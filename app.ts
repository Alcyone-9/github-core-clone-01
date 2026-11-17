// A GitHub-compatible git forge in one file: git smart HTTP (protocol v2 + v0), the REST v3
// resources, the GraphQL v4 surface gh and github-mcp-server speak, and an MCP streamable-HTTP
// endpoint — all over one in-memory store, no dependencies, Node built-ins only.
//
// Determinism: the suite replays a trial and compares the state export byte for byte, so nothing
// here reads the wall clock or a random source. Timestamps come from a logical clock that starts
// at the scenario epoch (2025-01-01T00:00:00Z) and advances one second per state-changing step;
// request ids and database ids are plain counters.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ------------------------------------------------------------------------------------------------
// Constants and the one store

const JSON_TYPE = 'application/json; charset=utf-8';
const ZERO_OID = '0'.repeat(40);
const EPOCH_SEC = 1_735_689_600; // 2025-01-01T00:00:00Z, the scenario epoch.
const MAX_BODY_BYTES = 256 * 1024 * 1024;

const VIEWER = { login: 'adaiversen', id: 1000, name: 'ada iversen', email: 'adaiversen@example.invalid' };
const SERVER_VERSION = '1.0.0';
const GIT_AGENT = 'git/github-core-clone-1.0';

interface GitObject {
  type: string;
  data: Buffer;
}

interface LabelRec {
  id: number;
  name: string;
  color: string;
  description: string | null;
}

interface IssueRec {
  kind: 'issue';
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  createdAt: string;
  updatedAt: string;
  closedAt: string | null;
}

interface PullRec {
  kind: 'pull';
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  headRef: string;
  baseRef: string;
  headSha: string;
  baseSha: string;
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  createdAt: string;
  updatedAt: string;
  closedAt: string | null;
}

interface CommentRec {
  id: number;
  body: string;
  createdAt: string;
  updatedAt: string;
}

interface Repo {
  id: number;
  owner: string;
  name: string;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  createdAt: string;
  updatedAt: string;
  objects: Map<string, GitObject>;
  refs: Map<string, string>;
  labels: Map<string, LabelRec>;
  issues: Map<number, IssueRec>;
  pulls: Map<number, PullRec>;
  comments: Map<number, CommentRec[]>;
  nextNumber: number;
}

const repos = new Map<string, Repo>();
let nextRepoId = 1;
let nextIssueId = 1;
let nextPullId = 1;
let nextCommentId = 1;
let nextLabelId = 1;
let requestCounter = 0;
let clockTick = 0;

/** The next logical timestamp: an ISO string and unix seconds, one second on from the last. */
function nextTime(): { iso: string; sec: number } {
  const sec = EPOCH_SEC + clockTick;
  clockTick += 1;
  return { iso: new Date(sec * 1000).toISOString(), sec };
}

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}

function findRepo(owner: string, name: string): Repo | null {
  return repos.get(repoKey(owner, name)) ?? null;
}

function createRepo(owner: string, name: string, description: string, isPrivate: boolean, defaultBranch: string): Repo {
  const t = nextTime();
  const repo: Repo = {
    id: nextRepoId++,
    owner,
    name,
    description,
    isPrivate,
    defaultBranch,
    createdAt: t.iso,
    updatedAt: t.iso,
    objects: new Map(),
    refs: new Map(),
    labels: new Map(),
    issues: new Map(),
    pulls: new Map(),
    comments: new Map(),
    nextNumber: 1,
  };
  repos.set(repoKey(owner, name), repo);
  return repo;
}

/** An opaque, stable global id (Relay style): base64 of `Type:key`. Never the bare database id. */
function globalId(type: string, key: string | number): string {
  return Buffer.from(`${type}:${key}`, 'utf8').toString('base64');
}

function decodeGlobalId(id: string): { type: string; key: string } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const colon = text.indexOf(':');
    if (colon < 0) return null;
    return { type: text.slice(0, colon), key: text.slice(colon + 1) };
  } catch {
    return null;
  }
}

function repoByGlobalId(id: string): Repo | null {
  const decoded = decodeGlobalId(id);
  if (decoded === null || decoded.type !== 'Repository') return null;
  const wanted = Number(decoded.key);
  for (const repo of repos.values()) if (repo.id === wanted) return repo;
  return null;
}

// ------------------------------------------------------------------------------------------------
// Git object primitives

function hashObject(type: string, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return createHash('sha1').update(header).update(data).digest('hex');
}

function storeObject(repo: Repo, type: string, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}

interface ParsedCommit {
  tree: string;
  parents: string[];
  author: string;
  committer: string;
  message: string;
}

/** Parse caches: a stored git object's bytes never change, so a parse keyed by its buffer stays valid. */
const commitParseCache = new WeakMap<Buffer, ParsedCommit>();
const treeParseCache = new WeakMap<Buffer, TreeEntry[]>();

function getCommit(repo: Repo, oid: string): ParsedCommit | null {
  const object = repo.objects.get(oid);
  if (object === undefined || object.type !== 'commit') return null;
  const cached = commitParseCache.get(object.data);
  if (cached !== undefined) return cached;
  const text = object.data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split < 0 ? text : text.slice(0, split);
  const message = split < 0 ? '' : text.slice(split + 2);
  let tree = '';
  let author = '';
  let committer = '';
  const parents: string[] = [];
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  const parsed: ParsedCommit = { tree, parents, author, committer, message };
  commitParseCache.set(object.data, parsed);
  return parsed;
}

function buildCommitData(tree: string, parents: readonly string[], author: string, committer: string, message: string): Buffer {
  let text = `tree ${tree}\n`;
  for (const parent of parents) text += `parent ${parent}\n`;
  text += `author ${author}\ncommitter ${committer}\n\n${message}`;
  return Buffer.from(text, 'utf8');
}

/** Make a commit in the viewer's name at the next logical second. */
function makeCommit(repo: Repo, tree: string, parents: readonly string[], message: string): string {
  const t = nextTime();
  const identity = `${VIEWER.name} <${VIEWER.email}> ${t.sec} +0000`;
  return storeObject(repo, 'commit', buildCommitData(tree, parents, identity, identity, message));
}

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function parseTree(data: Buffer): TreeEntry[] {
  const cached = treeParseCache.get(data);
  if (cached !== undefined) return cached;
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    const mode = data.toString('ascii', offset, space);
    const nul = data.indexOf(0x00, space + 1);
    const name = data.toString('utf8', space + 1, nul);
    const oid = data.toString('hex', nul + 1, nul + 21);
    entries.push({ mode, name, oid });
    offset = nul + 21;
  }
  treeParseCache.set(data, entries);
  return entries;
}

function isDirMode(mode: string): boolean {
  return mode === '40000' || mode === '040000';
}

/** Git's tree order: bytewise by name, directories as if the name ended in '/'. */
function sortTreeEntries(entries: TreeEntry[]): TreeEntry[] {
  return [...entries].sort((a, b) => {
    const ka = isDirMode(a.mode) ? `${a.name}/` : a.name;
    const kb = isDirMode(b.mode) ? `${b.name}/` : b.name;
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
}

function buildTreeData(entries: readonly TreeEntry[]): Buffer {
  const parts: Buffer[] = [];
  for (const entry of sortTreeEntries([...entries])) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

/** Flatten a tree into path -> blob oid (files only). */
function flattenTree(repo: Repo, treeOid: string | null, prefix: string, out: Map<string, string>): void {
  if (treeOid === null) return;
  const object = repo.objects.get(treeOid);
  if (object === undefined || object.type !== 'tree') return;
  for (const entry of parseTree(object.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (isDirMode(entry.mode)) flattenTree(repo, entry.oid, path, out);
    else if (entry.mode !== '160000') out.set(path, entry.oid);
  }
}

function flatTreeOf(repo: Repo, commitOid: string | null): Map<string, string> {
  const out = new Map<string, string>();
  if (commitOid === null) return out;
  const commit = getCommit(repo, commitOid);
  if (commit !== null) flattenTree(repo, commit.tree, '', out);
  return out;
}

/** Rebuild a root tree oid from a flat path -> blob oid map. */
function buildTreeFromFlat(repo: Repo, flat: ReadonlyMap<string, string>): string {
  const build = (items: ReadonlyArray<readonly [string, string]>): string => {
    const files: TreeEntry[] = [];
    const dirs = new Map<string, Array<readonly [string, string]>>();
    for (const [path, oid] of items) {
      const slash = path.indexOf('/');
      if (slash < 0) files.push({ mode: '100644', name: path, oid });
      else {
        const dir = path.slice(0, slash);
        const rest = path.slice(slash + 1);
        const list = dirs.get(dir) ?? [];
        list.push([rest, oid] as const);
        dirs.set(dir, list);
      }
    }
    const entries: TreeEntry[] = [...files];
    for (const [dir, list] of dirs) entries.push({ mode: '40000', name: dir, oid: build(list) });
    return storeObject(repo, 'tree', buildTreeData(entries));
  };
  return build([...flat.entries()]);
}

/** Walk a tree by path segments; answers the entry found, or null. */
function lookupPath(repo: Repo, treeOid: string, segments: readonly string[]): { type: 'blob' | 'tree'; oid: string; mode: string } | null {
  let current = treeOid;
  for (let i = 0; i < segments.length; i += 1) {
    const object = repo.objects.get(current);
    if (object === undefined || object.type !== 'tree') return null;
    const entry = parseTree(object.data).find((candidate) => candidate.name === segments[i]);
    if (entry === undefined) return null;
    if (i === segments.length - 1) {
      return { type: isDirMode(entry.mode) ? 'tree' : 'blob', oid: entry.oid, mode: entry.mode };
    }
    if (!isDirMode(entry.mode)) return null;
    current = entry.oid;
  }
  return { type: 'tree', oid: treeOid, mode: '40000' };
}

/** Every commit reachable from `tip` (itself included), tip first. */
function commitHistory(repo: Repo, tip: string): string[] {
  const order: string[] = [];
  const seen = new Set<string>();
  const stack = [tip];
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const commit = getCommit(repo, oid);
    if (commit === null) continue;
    order.push(oid);
    for (let i = commit.parents.length - 1; i >= 0; i -= 1) stack.push(commit.parents[i]);
  }
  return order;
}

function ancestorSet(repo: Repo, tip: string): Set<string> {
  return new Set(commitHistory(repo, tip));
}

function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  // Membership only: walk from the descendant and stop the moment the ancestor turns up,
  // instead of materialising the descendant's whole ancestor set first.
  const seen = new Set<string>();
  const stack = [descendant];
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (oid === ancestor) {
      const object = repo.objects.get(oid);
      if (object !== undefined && object.type === 'commit') return true;
      continue;
    }
    if (seen.has(oid)) continue;
    seen.add(oid);
    const commit = getCommit(repo, oid);
    if (commit === null) continue;
    for (const parent of commit.parents) stack.push(parent);
  }
  return false;
}

/** The nearest common ancestor of two commits, or null. */
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const ancestors = ancestorSet(repo, a);
  const seen = new Set<string>();
  const queue = [b];
  while (queue.length > 0) {
    const oid = queue.shift()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    if (ancestors.has(oid)) return oid;
    const commit = getCommit(repo, oid);
    if (commit !== null) queue.push(...commit.parents);
  }
  return null;
}

/** Peel a tag object to the commit it names (or return a commit oid unchanged). */
function peelToCommit(repo: Repo, oid: string): string | null {
  let current = oid;
  for (let depth = 0; depth < 16; depth += 1) {
    const object = repo.objects.get(current);
    if (object === undefined) return null;
    if (object.type === 'commit') return current;
    if (object.type !== 'tag') return null;
    const match = /^object ([0-9a-f]{40})$/m.exec(object.data.toString('utf8'));
    if (match === null) return null;
    current = match[1];
  }
  return null;
}

/** Resolve a REST `ref` value (branch name, full ref, tag or oid) to a commit oid. */
function resolveRef(repo: Repo, ref: string | null | undefined): string | null {
  if (ref === null || ref === undefined || ref === '') {
    const tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
    return tip === undefined ? null : peelToCommit(repo, tip);
  }
  const candidates = [
    repo.refs.get(ref),
    repo.refs.get(`refs/heads/${ref}`),
    repo.refs.get(`refs/tags/${ref}`),
    repo.refs.get(`refs/${ref}`),
  ];
  for (const candidate of candidates) {
    if (candidate !== undefined) return peelToCommit(repo, candidate);
  }
  if (/^[0-9a-f]{40}$/.test(ref) && repo.objects.has(ref)) return peelToCommit(repo, ref);
  return null;
}

function branchTip(repo: Repo, branch: string): string | null {
  const tip = repo.refs.get(`refs/heads/${branch}`);
  return tip === undefined ? null : tip;
}

// ------------------------------------------------------------------------------------------------
// Line diffs and three-way merges over flat trees

function splitLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (lines[lines.length - 1] === '') lines.pop();
  return lines;
}

/** Additions/deletions between two texts, by an LCS over lines (with a coarse fallback). */
function lineDiff(before: string, after: string): { additions: number; deletions: number } {
  const a = splitLines(before);
  const b = splitLines(after);
  if (a.length === 0) return { additions: b.length, deletions: 0 };
  if (b.length === 0) return { additions: 0, deletions: a.length };
  if (a.length > 4000 || b.length > 4000) return { additions: b.length, deletions: a.length };
  let prev = new Uint32Array(b.length + 1);
  let curr = new Uint32Array(b.length + 1);
  for (let i = a.length - 1; i >= 0; i -= 1) {
    for (let j = b.length - 1; j >= 0; j -= 1) {
      curr[j] = a[i] === b[j] ? prev[j + 1] + 1 : Math.max(prev[j], curr[j + 1]);
    }
    [prev, curr] = [curr, prev];
    curr.fill(0);
  }
  const common = prev[0];
  return { additions: b.length - common, deletions: a.length - common };
}

interface FileChange {
  path: string;
  status: 'added' | 'removed' | 'modified';
  baseOid: string | null;
  headOid: string | null;
  additions: number;
  deletions: number;
}

function blobText(repo: Repo, oid: string | null): string {
  if (oid === null) return '';
  const object = repo.objects.get(oid);
  return object === undefined ? '' : object.data.toString('utf8');
}

/** The file changes between two flat trees. */
function diffFlat(repo: Repo, base: ReadonlyMap<string, string>, head: ReadonlyMap<string, string>): FileChange[] {
  const changes: FileChange[] = [];
  const paths = new Set([...base.keys(), ...head.keys()]);
  for (const path of [...paths].sort()) {
    const baseOid = base.get(path) ?? null;
    const headOid = head.get(path) ?? null;
    if (baseOid === headOid) continue;
    const counts = lineDiff(blobText(repo, baseOid), blobText(repo, headOid));
    changes.push({
      path,
      status: baseOid === null ? 'added' : headOid === null ? 'removed' : 'modified',
      baseOid,
      headOid,
      additions: counts.additions,
      deletions: counts.deletions,
    });
  }
  return changes;
}

/** A three-way merge of flat trees; conflicts are paths both sides changed incompatibly. */
function mergeFlat(
  base: ReadonlyMap<string, string>,
  ours: ReadonlyMap<string, string>,
  theirs: ReadonlyMap<string, string>,
): { merged: Map<string, string>; conflicts: string[] } {
  const merged = new Map<string, string>();
  const conflicts: string[] = [];
  const paths = new Set([...base.keys(), ...ours.keys(), ...theirs.keys()]);
  for (const path of paths) {
    const b = base.get(path);
    const o = ours.get(path);
    const t = theirs.get(path);
    if (o === t) {
      if (o !== undefined) merged.set(path, o);
    } else if (b === o) {
      if (t !== undefined) merged.set(path, t);
    } else if (b === t) {
      if (o !== undefined) merged.set(path, o);
    } else {
      conflicts.push(path);
    }
  }
  return { merged, conflicts };
}

// ------------------------------------------------------------------------------------------------
// Packfiles and pkt-lines

const TYPE_CODES: Record<string, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPES: Record<number, string> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function packObjectHeader(type: string, size: number): Buffer {
  const code = TYPE_CODES[type];
  const bytes: number[] = [];
  let remaining = size;
  let first = (code << 4) | (remaining & 0x0f);
  remaining = Math.floor(remaining / 16);
  while (remaining > 0) {
    bytes.push(first | 0x80);
    first = remaining & 0x7f;
    remaining = Math.floor(remaining / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

function buildPack(objects: ReadonlyArray<{ type: string; data: Buffer }>): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const object of objects) {
    parts.push(packObjectHeader(object.type, object.data.length));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

/** Apply a git binary delta to a base object's bytes. */
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let offset = 0;
  const readVarint = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[offset++];
      value += (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if ((byte & 0x80) === 0) return value;
    }
  };
  const sourceSize = readVarint();
  if (sourceSize !== base.length) throw new Error(`delta base size ${sourceSize} != ${base.length}`);
  const targetSize = readVarint();
  const out = Buffer.alloc(targetSize);
  let written = 0;
  while (offset < delta.length) {
    const op = delta[offset++];
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      for (let bit = 0; bit < 4; bit += 1) if (op & (1 << bit)) copyOffset += delta[offset++] * 2 ** (8 * bit);
      for (let bit = 0; bit < 3; bit += 1) if (op & (0x10 << bit)) copySize += delta[offset++] * 2 ** (8 * bit);
      if (copySize === 0) copySize = 0x10000;
      base.copy(out, written, copyOffset, copyOffset + copySize);
      written += copySize;
    } else if (op > 0) {
      delta.copy(out, written, offset, offset + op);
      offset += op;
      written += op;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  if (written !== targetSize) throw new Error('delta size mismatch');
  return out;
}

interface PackEntry {
  offset: number;
  type: string;
  data: Buffer;
  baseOffset: number | null;
  baseOid: string | null;
}

/** Parse a pack, resolving ofs/ref deltas (a ref-delta base may live in `external`). */
function parsePack(pack: Buffer, external?: (oid: string) => GitObject | undefined): Array<{ type: string; data: Buffer }> {
  if (pack.length < 12 + 20 || pack.toString('ascii', 0, 4) !== 'PACK') throw new Error('not a packfile');
  const trailer = pack.subarray(pack.length - 20);
  const digest = createHash('sha1').update(pack.subarray(0, pack.length - 20)).digest();
  if (!trailer.equals(digest)) throw new Error('pack checksum mismatch');
  const count = pack.readUInt32BE(8);
  const entries: PackEntry[] = [];
  const byOffset = new Map<number, PackEntry>();
  let offset = 12;
  for (let i = 0; i < count; i += 1) {
    const entryOffset = offset;
    let byte = pack[offset++];
    const code = (byte >> 4) & 0x7;
    let size = byte & 0x0f;
    let shift = 4;
    while (byte & 0x80) {
      byte = pack[offset++];
      size += (byte & 0x7f) * 2 ** shift;
      shift += 7;
    }
    let baseOffset: number | null = null;
    let baseOid: string | null = null;
    if (code === 6) {
      let b = pack[offset++];
      let back = b & 0x7f;
      while (b & 0x80) {
        b = pack[offset++];
        back = ((back + 1) << 7) | (b & 0x7f);
      }
      baseOffset = entryOffset - back;
    } else if (code === 7) {
      baseOid = pack.toString('hex', offset, offset + 20);
      offset += 20;
    }
    const inflated = inflateSync(pack.subarray(offset), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
    offset += inflated.engine.bytesWritten;
    if (inflated.buffer.length !== size) throw new Error('pack entry size mismatch');
    const type = code === 6 || code === 7 ? '' : CODE_TYPES[code];
    if (type === undefined) throw new Error(`unknown pack type code ${code}`);
    const entry: PackEntry = { offset: entryOffset, type, data: inflated.buffer, baseOffset, baseOid };
    entries.push(entry);
    byOffset.set(entryOffset, entry);
  }
  const resolved = new Map<number, { type: string; data: Buffer }>();
  const resolve = (entry: PackEntry): { type: string; data: Buffer } => {
    const hit = resolved.get(entry.offset);
    if (hit !== undefined) return hit;
    let out: { type: string; data: Buffer };
    if (entry.baseOffset === null && entry.baseOid === null) {
      out = { type: entry.type, data: entry.data };
    } else {
      let base: { type: string; data: Buffer } | undefined;
      if (entry.baseOffset !== null) {
        const baseEntry = byOffset.get(entry.baseOffset);
        if (baseEntry === undefined) throw new Error('ofs-delta base missing');
        base = resolve(baseEntry);
      } else if (entry.baseOid !== null && external !== undefined) {
        base = external(entry.baseOid);
      }
      if (base === undefined) throw new Error('delta base missing');
      out = { type: base.type, data: applyDelta(base.data, entry.data) };
    }
    resolved.set(entry.offset, out);
    return out;
  };
  return entries.map((entry) => resolve(entry));
}

function pktLine(payload: Buffer | string): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const length = body.length + 4;
  const head = Buffer.from(length.toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([head, body]);
}

const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

interface Packet {
  kind: 'data' | 'flush' | 'delim' | 'end';
  payload: Buffer;
}

/** Split a pkt-line stream; `rest` is whatever follows the first flush (a pack, usually). */
function parsePackets(buffer: Buffer): { packets: Packet[]; rest: Buffer } {
  const packets: Packet[] = [];
  let offset = 0;
  while (offset + 4 <= buffer.length) {
    const head = buffer.toString('ascii', offset, offset + 4);
    if (!/^[0-9a-f]{4}$/.test(head)) break;
    const length = parseInt(head, 16);
    if (length === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      offset += 4;
      return { packets, rest: buffer.subarray(offset) };
    }
    if (length === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (length === 2) {
      packets.push({ kind: 'end', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (length < 4 || offset + length > buffer.length) break;
    packets.push({ kind: 'data', payload: buffer.subarray(offset + 4, offset + length) });
    offset += length;
  }
  return { packets, rest: buffer.subarray(offset) };
}

/** Frame pack bytes as sideband-1 pkt-lines (each packet well under the 65520-byte pkt limit). */
function sidebandChunks(pack: Buffer): Buffer[] {
  const chunks: Buffer[] = [];
  const SIZE = 65512;
  for (let offset = 0; offset < pack.length; offset += SIZE) {
    const slice = pack.subarray(offset, Math.min(pack.length, offset + SIZE));
    chunks.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  return chunks;
}

// ------------------------------------------------------------------------------------------------
// HTTP plumbing

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Readonly<Record<string, string>> = {}): void {
  const text = body === undefined ? '' : `${JSON.stringify(body)}\n`;
  res.writeHead(status, { 'content-type': JSON_TYPE, 'content-length': Buffer.byteLength(text), ...headers });
  res.end(text);
}

function sendJsonText(res: ServerResponse, status: number, text: string, bytes?: number): void {
  res.writeHead(status, { 'content-type': JSON_TYPE, 'content-length': bytes ?? Buffer.byteLength(text) });
  res.end(text);
}

function sendBuffer(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': body.length });
  res.end(body);
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (chunk: Buffer) => {
      total += chunk.length;
      if (total > MAX_BODY_BYTES) {
        reject(new Error('request body too large'));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function expectedToken(): string {
  return process.env.MAKEFUN_SHOP_TOKEN ?? '';
}

/** Bearer auth against the trial token; an unset token (local dev only) accepts everything. */
function authorized(req: IncomingMessage): boolean {
  const token = expectedToken();
  if (token === '') return true;
  const header = req.headers['authorization'];
  return typeof header === 'string' && header === `Bearer ${token}`;
}

function hasAnyAuth(req: IncomingMessage): boolean {
  return typeof req.headers['authorization'] === 'string';
}

class HttpError extends Error {
  status: number;
  constructor(status: number, message: string) {
    super(message);
    this.status = status;
  }
}

function notFound(): never {
  throw new HttpError(404, 'Not Found');
}

/** Parse a JSON request body: empty is {}, malformed is a 400 (the protocol checks require it). */
function jsonBody(raw: Buffer): Record<string, unknown> {
  const text = raw.toString('utf8').trim();
  if (text === '') return {};
  let parsed: unknown;
  try {
    parsed = JSON.parse(text);
  } catch {
    throw new HttpError(400, 'Problems parsing JSON');
  }
  if (typeof parsed !== 'object' || parsed === null || Array.isArray(parsed)) {
    throw new HttpError(400, 'Problems parsing JSON');
  }
  return parsed as Record<string, unknown>;
}

function str(value: unknown): string | null {
  return typeof value === 'string' ? value : null;
}

function bool(value: unknown): boolean | null {
  return typeof value === 'boolean' ? value : null;
}

function decodeSegment(segment: string): string {
  try {
    return decodeURIComponent(segment);
  } catch {
    return segment;
  }
}

// ------------------------------------------------------------------------------------------------
// REST serializers

/** The viewer's JSON is constant; one shared object is stringified into every response that embeds it. */
const VIEWER_JSON: Record<string, unknown> = {
  login: VIEWER.login,
  id: VIEWER.id,
  node_id: globalId('User', VIEWER.id),
  type: 'User',
  site_admin: false,
  name: VIEWER.name,
  email: VIEWER.email,
  avatar_url: '',
  url: `/api/v3/users/${VIEWER.login}`,
  html_url: `/${VIEWER.login}`,
};

function userJson(): Record<string, unknown> {
  return VIEWER_JSON;
}

function repoJson(repo: Repo): Record<string, unknown> {
  let openIssues = 0;
  for (const issue of repo.issues.values()) if (issue.state === 'open') openIssues += 1;
  for (const pull of repo.pulls.values()) if (pull.state === 'open') openIssues += 1;
  return {
    id: repo.id,
    node_id: globalId('Repository', repo.id),
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    private: repo.isPrivate,
    owner: userJson(),
    description: repo.description,
    fork: false,
    default_branch: repo.defaultBranch,
    created_at: repo.createdAt,
    updated_at: repo.updatedAt,
    pushed_at: repo.updatedAt,
    html_url: `/${repo.owner}/${repo.name}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    size: 0,
    stargazers_count: 0,
    watchers_count: 0,
    language: null,
    topics: [],
    visibility: repo.isPrivate ? 'private' : 'public',
    has_issues: true,
    has_projects: true,
    has_wiki: true,
    has_pages: false,
    has_downloads: true,
    archived: false,
    disabled: false,
    open_issues_count: openIssues,
    license: null,
    allow_forking: true,
    is_template: false,
  };
}

function labelJson(repo: Repo, name: string): Record<string, unknown> {
  const label = repo.labels.get(name);
  return {
    id: label?.id ?? 0,
    node_id: globalId('Label', `${repo.id}:${encodeURIComponent(name)}`),
    name,
    color: label?.color ?? 'ededed',
    description: label?.description ?? null,
    default: false,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/labels/${encodeURIComponent(name)}`,
  };
}

function issueJson(repo: Repo, issue: IssueRec): Record<string, unknown> {
  return {
    id: issue.id,
    node_id: globalId('Issue', `${repo.id}:${issue.number}`),
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => labelJson(repo, name)),
    user: userJson(),
    author_association: 'OWNER',
    comments: (repo.comments.get(issue.number) ?? []).length,
    created_at: issue.createdAt,
    updated_at: issue.updatedAt,
    closed_at: issue.closedAt,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
    html_url: `/${repo.owner}/${repo.name}/issues/${issue.number}`,
    repository_url: `/api/v3/repos/${repo.owner}/${repo.name}`,
  };
}

/**
 * Serialized issue bodies for the single-issue GET: an issue's JSON depends only on its own fields
 * (every mutation path bumps updatedAt), the repo's name, and its comment count (labels resolve to
 * immutable label records), so a body stamped with those three is safe to reuse verbatim.
 */
const issueTextCache = new WeakMap<IssueRec, { stamp: string; text: string; bytes: number }>();

function issueJsonText(repo: Repo, issue: IssueRec): { text: string; bytes: number } {
  const comments = (repo.comments.get(issue.number) ?? []).length;
  const stamp = `${repo.owner}/${repo.name}|${issue.updatedAt}|${comments}`;
  const hit = issueTextCache.get(issue);
  if (hit !== undefined && hit.stamp === stamp) return hit;
  const text = `${JSON.stringify(issueJson(repo, issue))}\n`;
  const entry = { stamp, text, bytes: Buffer.byteLength(text) };
  issueTextCache.set(issue, entry);
  return entry;
}

function pullJson(repo: Repo, pull: PullRec): Record<string, unknown> {
  const headTip = branchTip(repo, pull.headRef) ?? pull.headSha;
  const baseTip = branchTip(repo, pull.baseRef) ?? pull.baseSha;
  const side = (ref: string, sha: string): Record<string, unknown> => ({
    label: `${repo.owner}:${ref}`,
    ref,
    sha,
    user: userJson(),
    repo: repoJson(repo),
  });
  return {
    id: pull.id,
    node_id: globalId('PullRequest', `${repo.id}:${pull.number}`),
    number: pull.number,
    state: pull.state,
    title: pull.title,
    body: pull.body,
    user: userJson(),
    author_association: 'OWNER',
    head: side(pull.headRef, headTip),
    base: side(pull.baseRef, baseTip),
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    mergeable: pull.merged ? null : computeMergeable(repo, pull),
    mergeable_state: pull.merged ? 'clean' : 'unknown',
    merged_by: pull.merged ? userJson() : null,
    draft: false,
    comments: (repo.comments.get(pull.number) ?? []).length,
    created_at: pull.createdAt,
    updated_at: pull.updatedAt,
    closed_at: pull.closedAt,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pull.number}`,
    html_url: `/${repo.owner}/${repo.name}/pulls/${pull.number}`,
  };
}

function commentJson(repo: Repo, number: number, comment: CommentRec): Record<string, unknown> {
  return {
    id: comment.id,
    node_id: globalId('IssueComment', comment.id),
    body: comment.body,
    user: userJson(),
    author_association: 'OWNER',
    created_at: comment.createdAt,
    updated_at: comment.updatedAt,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/comments/${comment.id}`,
    html_url: `/${repo.owner}/${repo.name}/issues/${number}#issuecomment-${comment.id}`,
    issue_url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${number}`,
  };
}

function parseIdentity(line: string): { name: string; email: string; date: string } {
  const match = /^(.*?) <(.*?)> (\d+) [+-]\d{4}$/.exec(line);
  if (match === null) return { name: line, email: '', date: new Date(EPOCH_SEC * 1000).toISOString() };
  return { name: match[1], email: match[2], date: new Date(Number(match[3]) * 1000).toISOString() };
}

function commitJson(repo: Repo, oid: string): Record<string, unknown> {
  const commit = getCommit(repo, oid);
  if (commit === null) return { sha: oid };
  return {
    sha: oid,
    node_id: globalId('Commit', oid),
    commit: {
      author: parseIdentity(commit.author),
      committer: parseIdentity(commit.committer),
      message: commit.message,
      tree: { sha: commit.tree, url: `/api/v3/repos/${repo.owner}/${repo.name}/git/trees/${commit.tree}` },
      comment_count: 0,
    },
    parents: commit.parents.map((parent) => ({ sha: parent, url: `/api/v3/repos/${repo.owner}/${repo.name}/commits/${parent}` })),
    url: `/api/v3/repos/${repo.owner}/${repo.name}/commits/${oid}`,
    html_url: `/${repo.owner}/${repo.name}/commit/${oid}`,
  };
}

// ------------------------------------------------------------------------------------------------
// Shared domain operations (REST, GraphQL and MCP all act on these)

function createIssueRec(repo: Repo, title: string, body: string, labels: string[]): IssueRec {
  const t = nextTime();
  const issue: IssueRec = {
    kind: 'issue',
    id: nextIssueId++,
    number: repo.nextNumber++,
    title,
    body,
    state: 'open',
    labels: [...labels],
    createdAt: t.iso,
    updatedAt: t.iso,
    closedAt: null,
  };
  repo.issues.set(issue.number, issue);
  return issue;
}

function createPullRec(repo: Repo, title: string, body: string, headRef: string, baseRef: string): PullRec {
  const t = nextTime();
  const pull: PullRec = {
    kind: 'pull',
    id: nextPullId++,
    number: repo.nextNumber++,
    title,
    body,
    state: 'open',
    headRef,
    baseRef,
    headSha: branchTip(repo, headRef) ?? ZERO_OID,
    baseSha: branchTip(repo, baseRef) ?? ZERO_OID,
    merged: false,
    mergedAt: null,
    mergeCommitSha: null,
    createdAt: t.iso,
    updatedAt: t.iso,
    closedAt: null,
  };
  repo.pulls.set(pull.number, pull);
  return pull;
}

function addCommentRec(repo: Repo, number: number, body: string): CommentRec {
  const t = nextTime();
  const comment: CommentRec = { id: nextCommentId++, body, createdAt: t.iso, updatedAt: t.iso };
  const list = repo.comments.get(number) ?? [];
  list.push(comment);
  repo.comments.set(number, list);
  return comment;
}

/** The changed files of a pull request: merge-base tree versus head tree. */
function pullChanges(repo: Repo, pull: PullRec): FileChange[] {
  const headTip = branchTip(repo, pull.headRef);
  const baseTip = branchTip(repo, pull.baseRef);
  if (headTip === null || baseTip === null) return [];
  const base = mergeBase(repo, baseTip, headTip) ?? baseTip;
  return diffFlat(repo, flatTreeOf(repo, base), flatTreeOf(repo, headTip));
}

function computeMergeable(repo: Repo, pull: PullRec): boolean {
  if (pull.merged || pull.state !== 'open') return false;
  const headTip = branchTip(repo, pull.headRef);
  const baseTip = branchTip(repo, pull.baseRef);
  if (headTip === null || baseTip === null) return false;
  const base = mergeBase(repo, baseTip, headTip);
  const { conflicts } = mergeFlat(flatTreeOf(repo, base), flatTreeOf(repo, baseTip), flatTreeOf(repo, headTip));
  return conflicts.length === 0;
}

/** Squash-merge a pull request onto its base branch. Answers the merge commit sha, or null on conflict. */
function mergePullRec(repo: Repo, pull: PullRec, commitTitle?: string, commitMessage?: string): string | null {
  const headTip = branchTip(repo, pull.headRef);
  const baseTip = branchTip(repo, pull.baseRef);
  if (headTip === null || baseTip === null) return null;
  const base = mergeBase(repo, baseTip, headTip);
  const { merged, conflicts } = mergeFlat(flatTreeOf(repo, base), flatTreeOf(repo, baseTip), flatTreeOf(repo, headTip));
  if (conflicts.length > 0) return null;
  const tree = buildTreeFromFlat(repo, merged);
  const headline = commitTitle ?? `${pull.title} (#${pull.number})`;
  const message = commitMessage ? `${headline}\n\n${commitMessage}` : headline;
  const sha = makeCommit(repo, tree, [baseTip], message);
  repo.refs.set(`refs/heads/${pull.baseRef}`, sha);
  const t = nextTime();
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAt = t.iso;
  pull.closedAt = t.iso;
  pull.updatedAt = t.iso;
  pull.mergeCommitSha = sha;
  repo.updatedAt = t.iso;
  return sha;
}

/** Commit a flat tree onto a branch (created from the default tip when missing). */
function commitFlatToBranch(repo: Repo, branch: string, flat: ReadonlyMap<string, string>, message: string): string {
  let tip = branchTip(repo, branch);
  if (tip === null) {
    tip = branchTip(repo, repo.defaultBranch);
    if (tip === null && branch !== repo.defaultBranch) throw new HttpError(404, 'Branch not found');
  }
  const tree = buildTreeFromFlat(repo, flat);
  const sha = makeCommit(repo, tree, tip === null ? [] : [tip], message);
  repo.refs.set(`refs/heads/${branch}`, sha);
  repo.updatedAt = nextTime().iso;
  return sha;
}

// ------------------------------------------------------------------------------------------------
// REST v3

interface Page {
  perPage: number;
  page: number;
}

function pageOf(url: URL): Page {
  const perPageRaw = Number(url.searchParams.get('per_page') ?? '30');
  const pageRaw = Number(url.searchParams.get('page') ?? '1');
  const perPage = Number.isFinite(perPageRaw) && perPageRaw > 0 ? Math.min(100, Math.floor(perPageRaw)) : 30;
  const page = Number.isFinite(pageRaw) && pageRaw > 0 ? Math.floor(pageRaw) : 1;
  return { perPage, page };
}

/** Slice a list for the page and build the GitHub Link header for the rest. */
function paginate<T>(req: IncomingMessage, url: URL, items: readonly T[]): { slice: T[]; headers: Record<string, string> } {
  const { perPage, page } = pageOf(url);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const lastPage = Math.max(1, Math.ceil(items.length / perPage));
  const host = req.headers.host ?? 'localhost';
  const linkFor = (target: number): string => {
    const params = new URLSearchParams(url.searchParams);
    params.set('per_page', String(perPage));
    params.set('page', String(target));
    return `<http://${host}${url.pathname}?${params.toString()}>`;
  };
  const links: string[] = [];
  if (page < lastPage) {
    links.push(`${linkFor(page + 1)}; rel="next"`, `${linkFor(lastPage)}; rel="last"`);
  }
  if (page > 1) {
    links.push(`${linkFor(1)}; rel="first"`, `${linkFor(page - 1)}; rel="prev"`);
  }
  return { slice, headers: links.length > 0 ? { link: links.join(', ') } : {} };
}

function requireRepo(owner: string, name: string): Repo {
  const repo = findRepo(owner, name);
  if (repo === null) notFound();
  return repo as Repo;
}

function validateRepoName(name: string): void {
  if (name === '' || name === '.' || name === '..' || /[\s/\\]/.test(name) || name.length > 100) {
    throw new HttpError(422, 'Repository creation failed.');
  }
}

/** POST /user/repos and friends; answers the created repo or throws HttpError. */
function restCreateRepo(body: Record<string, unknown>): Repo {
  const name = str(body.name);
  if (name === null) throw new HttpError(422, 'Repository creation failed.');
  validateRepoName(name);
  if (findRepo(VIEWER.login, name) !== null) throw new HttpError(422, 'name already exists on this account');
  const description = str(body.description) ?? '';
  const isPrivate = bool(body.private) ?? false;
  const defaultBranch = str(body.default_branch) ?? 'main';
  return createRepo(VIEWER.login, name, description, isPrivate, defaultBranch === '' ? 'main' : defaultBranch);
}

async function handleRest(req: IncomingMessage, res: ServerResponse, url: URL, segments: string[], rawBody: Buffer): Promise<void> {
  const method = req.method ?? 'GET';
  if (!authorized(req)) {
    throw new HttpError(401, hasAnyAuth(req) ? 'Bad credentials' : 'Requires authentication');
  }
  const body = (): Record<string, unknown> => jsonBody(rawBody);

  // Root and meta.
  if (segments.length === 0) {
    if (method !== 'GET') notFound();
    sendJson(res, 200, {
      current_user_url: '/api/v3/user',
      current_user_repositories_url: '/api/v3/user/repos',
      repository_url: '/api/v3/repos/{owner}/{repo}',
      issue_search_url: '/api/v3/search/issues',
      rate_limit_url: '/api/v3/rate_limit',
    }, { 'x-oauth-scopes': 'repo, read:org' });
    return;
  }
  if (segments.length === 1 && segments[0] === 'meta') {
    if (method !== 'GET') notFound();
    sendJson(res, 200, { installed_version: SERVER_VERSION, git_executable: 'git', hooks: [] });
    return;
  }
  if (segments.length === 1 && segments[0] === 'user') {
    if (method !== 'GET') notFound();
    sendJson(res, 200, userJson());
    return;
  }
  if (segments.length === 2 && segments[0] === 'users') {
    if (method !== 'GET' || segments[1] !== VIEWER.login) notFound();
    sendJson(res, 200, userJson());
    return;
  }
  if (segments.length === 2 && segments[0] === 'user' && segments[1] === 'repos') {
    if (method === 'GET') {
      const mine = [...repos.values()].filter((repo) => repo.owner === VIEWER.login).sort((a, b) => a.id - b.id);
      const { slice, headers } = paginate(req, url, mine);
      sendJson(res, 200, slice.map(repoJson), headers);
      return;
    }
    if (method === 'POST') {
      const repo = restCreateRepo(body());
      sendJson(res, 201, repoJson(repo));
      return;
    }
    notFound();
  }

  if (segments[0] !== 'repos' || segments.length < 3) notFound();
  const owner = segments[1];
  const name = segments[2];
  const rest = segments.slice(3);
  const repo = requireRepo(owner, name);

  // The repository itself.
  if (rest.length === 0) {
    if (method === 'GET') {
      sendJson(res, 200, repoJson(repo));
      return;
    }
    if (method === 'PATCH') {
      const patch = body();
      const description = str(patch.description);
      if (description !== null) repo.description = description;
      const newName = str(patch.name);
      if (newName !== null && newName !== repo.name) {
        validateRepoName(newName);
        if (findRepo(repo.owner, newName) !== null) throw new HttpError(422, 'Repository creation failed.');
        repos.delete(repoKey(repo.owner, repo.name));
        repo.name = newName;
        repos.set(repoKey(repo.owner, repo.name), repo);
      }
      const isPrivate = bool(patch.private);
      if (isPrivate !== null) repo.isPrivate = isPrivate;
      const defaultBranch = str(patch.default_branch);
      if (defaultBranch !== null && defaultBranch !== '') repo.defaultBranch = defaultBranch;
      repo.updatedAt = nextTime().iso;
      sendJson(res, 200, repoJson(repo));
      return;
    }
    if (method === 'DELETE') {
      repos.delete(repoKey(repo.owner, repo.name));
      res.writeHead(204, { 'content-length': 0 });
      res.end();
      return;
    }
    notFound();
  }

  // Branches.
  if (rest[0] === 'branches') {
    if (rest.length === 1 && method === 'GET') {
      const branches = [...repo.refs.entries()]
        .filter(([ref]) => ref.startsWith('refs/heads/'))
        .map(([ref, sha]) => ({ name: ref.slice('refs/heads/'.length), commit: { sha, type: 'commit' }, protected: false }))
        .sort((a, b) => (a.name < b.name ? -1 : 1));
      const { slice, headers } = paginate(req, url, branches);
      sendJson(res, 200, slice, headers);
      return;
    }
    if (rest.length >= 2 && method === 'GET') {
      const branch = rest.slice(1).join('/');
      const tip = branchTip(repo, branch);
      if (tip === null) notFound();
      sendJson(res, 200, { name: branch, commit: { sha: tip, type: 'commit' }, protected: false });
      return;
    }
    notFound();
  }

  // Commits.
  if (rest[0] === 'commits' && rest.length === 1) {
    if (method !== 'GET') notFound();
    const start = resolveRef(repo, url.searchParams.get('sha'));
    if (start === null) {
      sendJson(res, 200, []);
      return;
    }
    const history = commitHistory(repo, start).map((oid) => commitJson(repo, oid));
    const { slice, headers } = paginate(req, url, history);
    sendJson(res, 200, slice, headers);
    return;
  }
  if (rest[0] === 'commits' && rest.length === 2 && method === 'GET') {
    if (!repo.objects.has(rest[1])) notFound();
    sendJson(res, 200, commitJson(repo, rest[1]));
    return;
  }

  // Git refs.
  if (rest[0] === 'git' && rest[1] === 'refs' && rest.length === 2 && method === 'POST') {
    const payload = body();
    const ref = str(payload.ref);
    const sha = str(payload.sha);
    if (ref === null || sha === null || !ref.startsWith('refs/')) throw new HttpError(422, 'Invalid ref or sha');
    if (!repo.objects.has(sha)) throw new HttpError(422, 'Object does not exist');
    if (repo.refs.has(ref)) throw new HttpError(422, 'Reference already exists');
    repo.refs.set(ref, sha);
    repo.updatedAt = nextTime().iso;
    const object = repo.objects.get(sha)!;
    sendJson(res, 201, { ref, node_id: globalId('Ref', `${repo.id}:${ref}`), object: { sha, type: object.type } });
    return;
  }
  if (rest[0] === 'git' && (rest[1] === 'ref' || rest[1] === 'refs') && rest.length >= 3) {
    const ref = rest.slice(2).join('/');
    const sha = repo.refs.get(ref);
    if (method === 'GET') {
      if (sha === undefined) notFound();
      const object = repo.objects.get(sha)!;
      sendJson(res, 200, { ref, node_id: globalId('Ref', `${repo.id}:${ref}`), object: { sha, type: object.type } });
      return;
    }
    if (method === 'DELETE') {
      if (sha === undefined) notFound();
      repo.refs.delete(ref);
      res.writeHead(204, { 'content-length': 0 });
      res.end();
      return;
    }
    notFound();
  }

  // Contents.
  if (rest[0] === 'contents') {
    const pathSegments = rest.slice(1);
    const path = pathSegments.join('/');
    if (method === 'GET') {
      const tip = resolveRef(repo, url.searchParams.get('ref'));
      if (tip === null) notFound();
      const commit = getCommit(repo, tip);
      if (commit === null) notFound();
      if (pathSegments.length === 0) {
        sendJson(res, 200, dirListing(repo, commit.tree, ''));
        return;
      }
      const found = lookupPath(repo, commit.tree, pathSegments);
      if (found === null) notFound();
      if (found.type === 'tree') {
        sendJson(res, 200, dirListing(repo, found.oid, path));
        return;
      }
      const blob = repo.objects.get(found.oid);
      if (blob === undefined) notFound();
      sendJson(res, 200, {
        type: 'file',
        encoding: 'base64',
        content: blob.data.toString('base64'),
        sha: found.oid,
        size: blob.data.length,
        name: pathSegments[pathSegments.length - 1],
        path,
        url: `/api/v3/repos/${owner}/${name}/contents/${path}`,
        html_url: `/${owner}/${name}/blob/${repo.defaultBranch}/${path}`,
        download_url: null,
      });
      return;
    }
    if (method === 'PUT') {
      const payload = body();
      const message = str(payload.message) ?? `Update ${path}`;
      const contentB64 = str(payload.content);
      if (contentB64 === null) throw new HttpError(422, 'content is required');
      const data = Buffer.from(contentB64.replace(/[\r\n\t ]+/g, ''), 'base64');
      const branch = str(payload.branch) ?? repo.defaultBranch;
      const tip = branchTip(repo, branch);
      const flat = flatTreeOf(repo, tip);
      const existing = flat.get(path);
      const givenSha = str(payload.sha);
      if (existing !== undefined) {
        if (givenSha === null) throw new HttpError(422, '"sha" wasn\'t supplied');
        if (givenSha.toLowerCase() !== existing.toLowerCase()) throw new HttpError(409, 'Conflict: the file has changed');
      }
      const blobSha = storeObject(repo, 'blob', data);
      flat.set(path, blobSha);
      const commitSha = commitFlatToBranch(repo, branch, flat, message);
      const commit = getCommit(repo, commitSha)!;
      sendJson(res, existing !== undefined ? 200 : 201, {
        content: {
          type: 'file',
          encoding: 'base64',
          sha: blobSha,
          size: data.length,
          name: pathSegments[pathSegments.length - 1],
          path,
        },
        commit: {
          sha: commitSha,
          message,
          author: parseIdentity(commit.author),
          committer: parseIdentity(commit.committer),
          tree: { sha: commit.tree },
          parents: commit.parents.map((parent) => ({ sha: parent })),
        },
      });
      return;
    }
    if (method === 'DELETE') {
      const payload = body();
      const message = str(payload.message) ?? `Delete ${path}`;
      const branch = str(payload.branch) ?? repo.defaultBranch;
      const tip = branchTip(repo, branch);
      const flat = flatTreeOf(repo, tip);
      const existing = flat.get(path);
      if (existing === undefined) notFound();
      const givenSha = str(payload.sha);
      if (givenSha !== null && givenSha.toLowerCase() !== existing.toLowerCase()) {
        throw new HttpError(409, 'Conflict: the file has changed');
      }
      flat.delete(path);
      const commitSha = commitFlatToBranch(repo, branch, flat, message);
      sendJson(res, 200, { content: null, commit: { sha: commitSha, message } });
      return;
    }
    notFound();
  }

  // Labels.
  if (rest[0] === 'labels' && rest.length === 1) {
    if (method === 'GET') {
      const labels = [...repo.labels.values()].sort((a, b) => (a.name < b.name ? -1 : 1)).map((label) => labelJson(repo, label.name));
      const { slice, headers } = paginate(req, url, labels);
      sendJson(res, 200, slice, headers);
      return;
    }
    if (method === 'POST') {
      const payload = body();
      const labelName = str(payload.name);
      if (labelName === null || labelName === '') throw new HttpError(422, 'Label name is required');
      const existing = repo.labels.get(labelName);
      if (existing !== undefined) {
        sendJson(res, 201, labelJson(repo, labelName));
        return;
      }
      const color = (str(payload.color) ?? 'ededed').replace(/^#/, '').toLowerCase();
      repo.labels.set(labelName, { id: nextLabelId++, name: labelName, color, description: str(payload.description) });
      sendJson(res, 201, labelJson(repo, labelName));
      return;
    }
    notFound();
  }

  // Issues and their comments.
  if (rest[0] === 'issues') {
    if (rest.length === 1) {
      if (method === 'GET') {
        const state = url.searchParams.get('state') ?? 'open';
        const sort = url.searchParams.get('sort') ?? 'created';
        const direction = url.searchParams.get('direction') ?? 'desc';
        const labelFilter = (url.searchParams.get('labels') ?? '').split(',').map((s) => s.trim()).filter((s) => s !== '');
        let list = [...repo.issues.values()];
        if (state === 'open' || state === 'closed') list = list.filter((issue) => issue.state === state);
        if (labelFilter.length > 0) list = list.filter((issue) => labelFilter.every((label) => issue.labels.includes(label)));
        const key = (issue: IssueRec): [string, number] => (sort === 'updated' ? [issue.updatedAt, issue.number] : [issue.createdAt, issue.number]);
        list.sort((a, b) => {
          const [ka, na] = key(a);
          const [kb, nb] = key(b);
          const cmp = ka === kb ? na - nb : ka < kb ? -1 : 1;
          return direction === 'asc' ? cmp : -cmp;
        });
        const { slice, headers } = paginate(req, url, list);
        sendJson(res, 200, slice.map((issue) => issueJson(repo, issue)), headers);
        return;
      }
      if (method === 'POST') {
        const payload = body();
        const title = str(payload.title);
        if (title === null) throw new HttpError(422, 'Title is required');
        const labels = readLabelNames(repo, payload.labels);
        const issue = createIssueRec(repo, title, str(payload.body) ?? '', labels);
        sendJson(res, 201, issueJson(repo, issue));
        return;
      }
      notFound();
    }
    const number = Number(rest[1]);
    if (rest.length === 2 && Number.isInteger(number)) {
      const issue = repo.issues.get(number);
      const pull = repo.pulls.get(number);
      if (method === 'GET') {
        if (issue !== undefined) {
          const body = issueJsonText(repo, issue);
          sendJsonText(res, 200, body.text, body.bytes);
          return;
        }
        if (pull !== undefined) {
          sendJson(res, 200, pullAsIssueJson(repo, pull));
          return;
        }
        notFound();
      }
      if (method === 'PATCH') {
        if (issue === undefined) notFound();
        const payload = body();
        const title = str(payload.title);
        if (title !== null) issue.title = title;
        const newBody = str(payload.body);
        if (newBody !== null) issue.body = newBody;
        if (payload.labels !== undefined) issue.labels = readLabelNames(repo, payload.labels);
        const state = str(payload.state);
        const t = nextTime();
        if (state === 'closed' && issue.state !== 'closed') {
          issue.state = 'closed';
          issue.closedAt = t.iso;
        } else if (state === 'open' && issue.state !== 'open') {
          issue.state = 'open';
          issue.closedAt = null;
        }
        issue.updatedAt = t.iso;
        sendJson(res, 200, issueJson(repo, issue));
        return;
      }
      notFound();
    }
    if (rest.length === 3 && rest[2] === 'comments' && Number.isInteger(number)) {
      if (repo.issues.get(number) === undefined && repo.pulls.get(number) === undefined) notFound();
      if (method === 'GET') {
        const list = (repo.comments.get(number) ?? []).map((comment) => commentJson(repo, number, comment));
        const { slice, headers } = paginate(req, url, list);
        sendJson(res, 200, slice, headers);
        return;
      }
      if (method === 'POST') {
        const payload = body();
        const text = str(payload.body);
        if (text === null) throw new HttpError(422, 'Body is required');
        const comment = addCommentRec(repo, number, text);
        sendJson(res, 201, commentJson(repo, number, comment));
        return;
      }
      notFound();
    }
    notFound();
  }

  // Pull requests.
  if (rest[0] === 'pulls') {
    if (rest.length === 1) {
      if (method === 'GET') {
        const state = url.searchParams.get('state') ?? 'open';
        let list = [...repo.pulls.values()];
        if (state === 'open') list = list.filter((pull) => pull.state === 'open');
        else if (state === 'closed') list = list.filter((pull) => pull.state === 'closed');
        list.sort((a, b) => (a.createdAt === b.createdAt ? b.number - a.number : a.createdAt < b.createdAt ? 1 : -1));
        const { slice, headers } = paginate(req, url, list);
        sendJson(res, 200, slice.map((pull) => pullJson(repo, pull)), headers);
        return;
      }
      if (method === 'POST') {
        const payload = body();
        const pull = restCreatePull(repo, payload);
        sendJson(res, 201, pullJson(repo, pull));
        return;
      }
      notFound();
    }
    const number = Number(rest[1]);
    if (!Number.isInteger(number)) notFound();
    const pull = repo.pulls.get(number);
    if (rest.length === 2) {
      if (method === 'GET') {
        if (pull === undefined) notFound();
        sendJson(res, 200, pullJson(repo, pull as PullRec));
        return;
      }
      if (method === 'PATCH') {
        if (pull === undefined) notFound();
        const payload = body();
        const title = str(payload.title);
        if (title !== null) (pull as PullRec).title = title;
        const newBody = str(payload.body);
        if (newBody !== null) (pull as PullRec).body = newBody;
        const state = str(payload.state);
        const t = nextTime();
        if (state === 'closed' && (pull as PullRec).state !== 'closed') {
          (pull as PullRec).state = 'closed';
          (pull as PullRec).closedAt = t.iso;
        } else if (state === 'open' && (pull as PullRec).state !== 'open' && !(pull as PullRec).merged) {
          (pull as PullRec).state = 'open';
          (pull as PullRec).closedAt = null;
        }
        (pull as PullRec).updatedAt = t.iso;
        sendJson(res, 200, pullJson(repo, pull as PullRec));
        return;
      }
      notFound();
    }
    if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
      if (pull === undefined) notFound();
      const files = pullChanges(repo, pull as PullRec).map((change) => ({
        sha: change.headOid ?? change.baseOid ?? ZERO_OID,
        filename: change.path,
        status: change.status === 'removed' ? 'removed' : change.status,
        additions: change.additions,
        deletions: change.deletions,
        changes: change.additions + change.deletions,
      }));
      const { slice, headers } = paginate(req, url, files);
      sendJson(res, 200, slice, headers);
      return;
    }
    if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
      if (pull === undefined) notFound();
      const target = pull as PullRec;
      if (target.merged || target.state !== 'open') throw new HttpError(405, 'Pull Request is not mergeable');
      const payload = body();
      const sha = mergePullRec(repo, target, str(payload.commit_title) ?? undefined, str(payload.commit_message) ?? undefined);
      if (sha === null) throw new HttpError(405, 'Pull Request is not mergeable');
      sendJson(res, 200, { sha, merged: true, message: 'Pull Request successfully merged' });
      return;
    }
    notFound();
  }

  notFound();
}

/** A directory listing for the contents API. */
function dirListing(repo: Repo, treeOid: string, prefix: string): Array<Record<string, unknown>> {
  const object = repo.objects.get(treeOid);
  if (object === undefined || object.type !== 'tree') return [];
  return sortTreeEntries(parseTree(object.data)).map((entry) => {
    const isDir = isDirMode(entry.mode);
    const blob = isDir ? undefined : repo.objects.get(entry.oid);
    return {
      type: isDir ? 'dir' : 'file',
      sha: entry.oid,
      size: isDir ? 0 : (blob?.data.length ?? 0),
      name: entry.name,
      path: prefix === '' ? entry.name : `${prefix}/${entry.name}`,
    };
  }).sort((a, b) => (String(a.name) < String(b.name) ? -1 : 1));
}

/** Validate a REST labels payload (names must already exist in the repo) and answer the names. */
function readLabelNames(repo: Repo, raw: unknown): string[] {
  if (raw === undefined || raw === null) return [];
  if (!Array.isArray(raw)) throw new HttpError(422, 'Invalid labels');
  const names: string[] = [];
  for (const entry of raw) {
    const name = typeof entry === 'string' ? entry : entry !== null && typeof entry === 'object' ? str((entry as Record<string, unknown>).name) : null;
    if (name === null) throw new HttpError(422, 'Invalid labels');
    if (!repo.labels.has(name)) throw new HttpError(422, `Label "${name}" does not exist`);
    names.push(name);
  }
  return names;
}

/** An issue-shaped view of a pull request (GitHub serves PRs under /issues/{n} too). */
function pullAsIssueJson(repo: Repo, pull: PullRec): Record<string, unknown> {
  return {
    id: pull.id,
    node_id: globalId('PullRequest', `${repo.id}:${pull.number}`),
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    labels: [],
    user: userJson(),
    comments: (repo.comments.get(pull.number) ?? []).length,
    created_at: pull.createdAt,
    updated_at: pull.updatedAt,
    closed_at: pull.closedAt,
    pull_request: { url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pull.number}`, merged_at: pull.mergedAt },
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${pull.number}`,
  };
}

/** POST /pulls validation shared by REST (GraphQL and MCP build their own payloads). */
function restCreatePull(repo: Repo, payload: Record<string, unknown>): PullRec {
  const title = str(payload.title);
  if (title === null) throw new HttpError(422, 'Title is required');
  const headRaw = str(payload.head);
  const baseRaw = str(payload.base);
  if (headRaw === null || baseRaw === null) throw new HttpError(422, 'Head and base are required');
  const head = headRaw.includes(':') ? headRaw.slice(headRaw.indexOf(':') + 1) : headRaw;
  const base = baseRaw.includes(':') ? baseRaw.slice(baseRaw.indexOf(':') + 1) : baseRaw;
  const headTip = branchTip(repo, head);
  const baseTip = branchTip(repo, base);
  if (headTip === null || baseTip === null) throw new HttpError(422, 'Head or base branch does not exist');
  if (head === base || headTip === baseTip) throw new HttpError(422, 'No commits between base and head');
  for (const existing of repo.pulls.values()) {
    if (existing.state === 'open' && existing.headRef === head && existing.baseRef === base) {
      throw new HttpError(422, 'A pull request already exists for this head and base');
    }
  }
  return createPullRec(repo, title, str(payload.body) ?? '', head, base);
}

// ------------------------------------------------------------------------------------------------
// Git smart HTTP

const UPLOAD_CAPS_V0 = `multi_ack_detailed side-band-64k thin-pack ofs-delta symref=HEAD:refs/heads/__DEFAULT__ agent=${GIT_AGENT}`;
const RECEIVE_CAPS = `report-status delete-refs side-band-64k ofs-delta agent=${GIT_AGENT}`;

/** The refs a v0 advertisement lists: HEAD first (carrying the capabilities), then refs by name. */
function advertisementRefs(repo: Repo, service: string): Buffer {
  const caps = (service === 'git-receive-pack' ? RECEIVE_CAPS : UPLOAD_CAPS_V0).replace('__DEFAULT__', repo.defaultBranch);
  const lines: Buffer[] = [];
  const headTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
  const names = [...repo.refs.keys()].sort();
  if (names.length === 0) {
    lines.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
    return Buffer.concat(lines);
  }
  lines.push(pktLine(`${headTip ?? ZERO_OID} HEAD\0${caps}\n`));
  for (const ref of names) {
    const oid = repo.refs.get(ref)!;
    lines.push(pktLine(`${oid} ${ref}\n`));
    const peeled = peelToCommit(repo, oid);
    if (peeled !== null && peeled !== oid) lines.push(pktLine(`${peeled} ${ref}^{}\n`));
  }
  return Buffer.concat(lines);
}

/** The protocol-v2 capability advertisement never changes; build it once. */
const V2_ADVERTISEMENT = Buffer.concat([
  pktLine('version 2\n'),
  pktLine(`agent=${GIT_AGENT}\n`),
  pktLine('ls-refs=unborn\n'),
  pktLine('fetch=shallow\n'),
  pktLine('object-format=sha1\n'),
  PKT_FLUSH,
]);

function handleInfoRefs(req: IncomingMessage, res: ServerResponse, repo: Repo, service: string): void {
  const protocol = req.headers['git-protocol'];
  if (service === 'git-upload-pack' && typeof protocol === 'string' && protocol.includes('version=2')) {
    sendBuffer(res, 200, V2_ADVERTISEMENT, 'application/x-git-upload-pack-advertisement');
    return;
  }
  const body = Buffer.concat([pktLine(`# service=${service}\n`), PKT_FLUSH, advertisementRefs(repo, service), PKT_FLUSH]);
  sendBuffer(res, 200, body, `application/x-git-${service === 'git-upload-pack' ? 'upload-pack' : 'receive-pack'}-advertisement`);
}

/** One ls-refs answer: HEAD (when it matches the prefixes), then matching refs in name order. */
function lsRefsLines(repo: Repo, args: { peel: boolean; symrefs: boolean; unborn: boolean; prefixes: string[] }): Buffer[] {
  const matches = (name: string): boolean => args.prefixes.length === 0 || args.prefixes.some((prefix) => name.startsWith(prefix));
  const lines: Buffer[] = [];
  const headRef = `refs/heads/${repo.defaultBranch}`;
  const headTip = repo.refs.get(headRef);
  if (matches('HEAD')) {
    if (headTip !== undefined) {
      lines.push(pktLine(`${headTip} HEAD${args.symrefs ? ` symref-target:${headRef}` : ''}\n`));
    } else if (args.unborn) {
      lines.push(pktLine(`unborn HEAD${args.symrefs ? ` symref-target:${headRef}` : ''}\n`));
    }
  }
  for (const ref of [...repo.refs.keys()].sort()) {
    if (!matches(ref)) continue;
    const oid = repo.refs.get(ref)!;
    let line = `${oid} ${ref}`;
    if (args.peel) {
      const peeled = peelToCommit(repo, oid);
      if (peeled !== null && peeled !== oid) line += ` peeled:${peeled}`;
    }
    lines.push(pktLine(`${line}\n`));
  }
  return lines;
}

interface FetchPlan {
  objects: Array<{ oid: string; type: string; data: Buffer }>;
  shallow: string[];
  unshallow: string[];
  knownHaves: string[];
}

/**
 * Choose the objects a fetch sends: everything reachable from the wants that the haves do not
 * already cover, with shallow depth honoured. A have the client marks shallow does not cover its
 * own parents — that is what makes deepen work.
 */
function planFetch(repo: Repo, wants: string[], haves: string[], depth: number | null, clientShallow: readonly string[]): FetchPlan {
  const shallowSet = new Set(clientShallow);
  // The have closure: full reachability, cut at the client's shallow boundary commits.
  const haveClosure = new Set<string>();
  const closureStack = [...haves];
  while (closureStack.length > 0) {
    const oid = closureStack.pop()!;
    if (haveClosure.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (object === undefined) continue;
    haveClosure.add(oid);
    if (object.type === 'commit') {
      const commit = getCommit(repo, oid);
      if (commit === null) continue;
      closureStack.push(commit.tree);
      if (!shallowSet.has(oid)) closureStack.push(...commit.parents);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) closureStack.push(entry.oid);
    } else if (object.type === 'tag') {
      const match = /^object ([0-9a-f]{40})$/m.exec(object.data.toString('utf8'));
      if (match !== null) closureStack.push(match[1]);
    }
  }

  // Breadth-first walk from the wants, generation by generation.
  const generations = new Map<string, number>();
  const included = new Set<string>();
  const queue: Array<{ oid: string; gen: number }> = [];
  const enqueue = (oid: string, gen: number): void => {
    const known = generations.get(oid);
    if (known !== undefined && known <= gen) return;
    generations.set(oid, gen);
    queue.push({ oid, gen });
  };
  for (const want of wants) {
    const object = repo.objects.get(want);
    if (object === undefined) continue;
    if (object.type === 'tag') {
      if (!haveClosure.has(want)) included.add(want);
      const target = peelToCommit(repo, want);
      if (target !== null) enqueue(target, 0);
    } else if (object.type === 'commit') {
      enqueue(want, 0);
    } else if (!haveClosure.has(want)) {
      included.add(want);
      if (object.type === 'tree') {
        for (const entry of parseTree(object.data)) enqueue(entry.oid, 0);
      }
    }
  }
  // A depth-bounded fetch with no haves and no client shallow boundary cannot include, unshallow
  // or acknowledge anything past generation depth-1, so the walk stops there instead of touring
  // the whole history. With haves or a shallow boundary the full walk still runs (deepen needs it).
  const maxGen = depth !== null && haves.length === 0 && clientShallow.length === 0 ? depth - 1 : Number.POSITIVE_INFINITY;
  const boundary = new Set<string>();
  let queueHead = 0;
  while (queueHead < queue.length) {
    const { oid, gen } = queue[queueHead++]!;
    if (generations.get(oid) !== gen) continue;
    const object = repo.objects.get(oid);
    if (object === undefined) continue;
    if (object.type === 'commit') {
      const commit = getCommit(repo, oid);
      if (commit === null) continue;
      const withinDepth = depth === null || gen < depth;
      if (withinDepth && !haveClosure.has(oid)) {
        included.add(oid);
        // The commit's tree closure rides along (minus what the client already has).
        const treeStack = [commit.tree];
        while (treeStack.length > 0) {
          const treeOid = treeStack.pop()!;
          if (haveClosure.has(treeOid) || included.has(treeOid)) continue;
          const treeObject = repo.objects.get(treeOid);
          if (treeObject === undefined || treeObject.type !== 'tree') continue;
          included.add(treeOid);
          for (const entry of parseTree(treeObject.data)) {
            if (isDirMode(entry.mode)) treeStack.push(entry.oid);
            else if (!haveClosure.has(entry.oid)) included.add(entry.oid);
          }
        }
        if (depth !== null && gen === depth - 1) {
          for (const parent of commit.parents) {
            if (repo.objects.has(parent) && !included.has(parent) && !haveClosure.has(parent)) boundary.add(oid);
          }
        }
      }
      // Parents are always traversed: depth is measured through haves too (deepen).
      for (const parent of commit.parents) {
        if (gen + 1 > maxGen) continue;
        enqueue(parent, gen + 1);
      }
    } else if (object.type === 'tree') {
      if (!haveClosure.has(oid) && !included.has(oid)) {
        included.add(oid);
        for (const entry of parseTree(object.data)) enqueue(entry.oid, gen);
      }
    }
  }

  const unshallow: string[] = [];
  for (const oid of clientShallow) {
    if (boundary.has(oid)) continue;
    const commit = getCommit(repo, oid);
    if (commit === null) continue;
    if (!generations.has(oid) && !included.has(oid)) continue;
    const covered = commit.parents.every((parent) => included.has(parent) || !repo.objects.has(parent));
    if (covered) unshallow.push(oid);
  }

  const objects: Array<{ oid: string; type: string; data: Buffer }> = [];
  for (const oid of included) {
    const object = repo.objects.get(oid);
    if (object !== undefined) objects.push({ oid, type: object.type, data: object.data });
  }
  // Commits first (newest generation first), then trees, then blobs, then tags: deterministic.
  const rank = (type: string): number => (type === 'commit' ? 0 : type === 'tree' ? 1 : type === 'blob' ? 2 : 3);
  objects.sort((a, b) => rank(a.type) - rank(b.type) || (a.oid < b.oid ? -1 : 1));
  return {
    objects,
    shallow: [...boundary].sort(),
    unshallow: unshallow.sort(),
    knownHaves: haves.filter((have) => repo.objects.has(have)),
  };
}

/** Pack bytes are a pure function of the object list (content-addressed), so repeat fetches reuse them. */
const packCache = new Map<string, Buffer>();

function packForObjects(objects: ReadonlyArray<{ oid: string; type: string; data: Buffer }>): Buffer {
  const key = objects.map((object) => object.oid).join(' ');
  const hit = packCache.get(key);
  if (hit !== undefined) return hit;
  const pack = buildPack(objects);
  if (packCache.size >= 32) packCache.clear();
  packCache.set(key, pack);
  return pack;
}

function fetchResponse(repo: Repo, wants: string[], haves: string[], depth: number | null, clientShallow: string[], done: boolean): Buffer {
  const parts: Buffer[] = [];
  const plan = planFetch(repo, wants, haves, depth, clientShallow);
  if (haves.length > 0) {
    parts.push(pktLine('acknowledgments\n'));
    if (plan.knownHaves.length > 0) {
      parts.push(pktLine(`ACK ${plan.knownHaves[0]}\n`));
      parts.push(pktLine('ready\n'));
    } else {
      parts.push(pktLine('NAK\n'));
    }
    parts.push(PKT_DELIM);
  }
  if (!done) return Buffer.concat(parts);
  if (plan.shallow.length > 0 || plan.unshallow.length > 0) {
    parts.push(pktLine('shallow-info\n'));
    for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
    for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
    parts.push(PKT_DELIM);
  }
  const pack = packForObjects(plan.objects);
  parts.push(pktLine('packfile\n'));
  parts.push(...sidebandChunks(pack));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function handleUploadPack(res: ServerResponse, repo: Repo, rawBody: Buffer): void {
  const { packets } = parsePackets(rawBody);
  const lines = packets.filter((packet) => packet.kind === 'data').map((packet) => packet.payload.toString('utf8').replace(/\n$/, ''));
  const first = lines[0] ?? '';

  if (first.startsWith('command=ls-refs')) {
    const args = { peel: false, symrefs: false, unborn: false, prefixes: [] as string[] };
    for (const line of lines.slice(1)) {
      if (line === 'peel') args.peel = true;
      else if (line === 'symrefs') args.symrefs = true;
      else if (line === 'unborn') args.unborn = true;
      else if (line.startsWith('ref-prefix ')) args.prefixes.push(line.slice('ref-prefix '.length));
    }
    sendBuffer(res, 200, Buffer.concat([...lsRefsLines(repo, args), PKT_FLUSH]), 'application/x-git-upload-pack-result');
    return;
  }

  if (first.startsWith('command=fetch')) {
    const wants: string[] = [];
    const haves: string[] = [];
    const clientShallow: string[] = [];
    let depth: number | null = null;
    let done = false;
    for (const line of lines.slice(1)) {
      if (line.startsWith('want ')) wants.push(line.slice(5).trim());
      else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
      else if (line.startsWith('shallow ')) clientShallow.push(line.slice(8).trim());
      else if (line.startsWith('deepen ')) depth = Number(line.slice(7).trim());
      else if (line.startsWith('deepen-since ')) depth = null;
      else if (line === 'done') done = true;
    }
    sendBuffer(res, 200, fetchResponse(repo, wants, haves, depth, clientShallow, done), 'application/x-git-upload-pack-result');
    return;
  }

  if (first.startsWith('want ')) {
    // Protocol v0 fetch: want/have lines, a flush, then `done`.
    const wants: string[] = [];
    const haves: string[] = [];
    let depth: number | null = null;
    for (const line of lines) {
      const clean = line.replace(/\0.*$/, '');
      if (clean.startsWith('want ')) wants.push(clean.slice(5).trim());
      else if (clean.startsWith('have ')) haves.push(clean.slice(5).trim());
      else if (clean.startsWith('deepen ')) depth = Number(clean.slice(7).trim());
    }
    const plan = planFetch(repo, wants, haves, depth, []);
    const pack = packForObjects(plan.objects);
    const body = Buffer.concat([pktLine('NAK\n'), ...sidebandChunks(pack), PKT_FLUSH]);
    sendBuffer(res, 200, body, 'application/x-git-upload-pack-result');
    return;
  }

  throw new HttpError(400, 'Unsupported git request');
}

interface PushCommand {
  oldOid: string;
  newOid: string;
  ref: string;
}

function handleReceivePack(res: ServerResponse, repo: Repo, rawBody: Buffer): void {
  const { packets, rest } = parsePackets(rawBody);
  const dataLines = packets.filter((packet) => packet.kind === 'data').map((packet) => packet.payload.toString('utf8').replace(/\n$/, ''));
  if (dataLines.length === 0 && rest.length === 0) throw new HttpError(400, 'Empty push');
  const commands: PushCommand[] = [];
  let capabilities = '';
  dataLines.forEach((line, index) => {
    let text = line;
    if (index === 0) {
      const nul = text.indexOf('\0');
      if (nul >= 0) {
        capabilities = text.slice(nul + 1);
        text = text.slice(0, nul);
      }
    }
    const parts = text.split(' ');
    if (parts.length === 3) commands.push({ oldOid: parts[0], newOid: parts[1], ref: parts[2] });
  });
  const sideband = capabilities.includes('side-band-64k');

  let unpackError: string | null = null;
  if (rest.length > 0) {
    try {
      const objects = parsePack(rest, (oid) => repo.objects.get(oid));
      for (const object of objects) storeObject(repo, object.type, object.data);
    } catch (err) {
      unpackError = err instanceof Error ? err.message : 'unpack error';
    }
  }

  const report: string[] = [`unpack ${unpackError === null ? 'ok' : `error: ${unpackError.replace(/[\r\n]+/g, ' ')}`}\n`];
  for (const command of commands) {
    if (unpackError !== null) {
      report.push(`ng ${command.ref} unpack failed\n`);
      continue;
    }
    const current = repo.refs.get(command.ref) ?? ZERO_OID;
    const fail = (reason: string): void => {
      report.push(`ng ${command.ref} ${reason}\n`);
    };
    if (command.oldOid !== current) {
      fail('reference mismatch');
      continue;
    }
    if (command.newOid === ZERO_OID) {
      if (command.ref === `refs/heads/${repo.defaultBranch}`) {
        fail('deletion of the current branch prohibited');
        continue;
      }
      repo.refs.delete(command.ref);
      report.push(`ok ${command.ref}\n`);
      continue;
    }
    if (!repo.objects.has(command.newOid)) {
      fail('missing object');
      continue;
    }
    if (command.oldOid !== ZERO_OID && command.ref.startsWith('refs/heads/')) {
      const newCommit = peelToCommit(repo, command.newOid);
      if (newCommit === null || !isAncestor(repo, command.oldOid, newCommit)) {
        fail('non-fast-forward');
        continue;
      }
    }
    repo.refs.set(command.ref, command.newOid);
    report.push(`ok ${command.ref}\n`);
  }
  if (unpackError === null && commands.some((command) => command.newOid !== ZERO_OID)) {
    repo.updatedAt = nextTime().iso;
  }

  const reportStream = Buffer.concat(report.map((line) => pktLine(line)));
  if (sideband) {
    const framed: Buffer[] = [];
    let offset = 0;
    const SIZE = 65512;
    while (offset < reportStream.length) {
      const slice = reportStream.subarray(offset, Math.min(reportStream.length, offset + SIZE));
      framed.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
      offset += SIZE;
    }
    framed.push(PKT_FLUSH);
    sendBuffer(res, 200, Buffer.concat(framed), 'application/x-git-receive-pack-result');
  } else {
    sendBuffer(res, 200, Buffer.concat([reportStream, PKT_FLUSH]), 'application/x-git-receive-pack-result');
  }
}

async function handleGit(req: IncomingMessage, res: ServerResponse, segments: string[], url: URL, rawBody: Buffer): Promise<void> {
  const method = req.method ?? 'GET';
  // segments: [owner, repo.git, ...tail]
  const owner = segments[0];
  const repoName = segments[1].replace(/\.git$/, '');
  const repo = findRepo(owner, repoName);
  if (repo === null) {
    sendJson(res, 404, { message: 'Not Found' });
    return;
  }
  const tail = segments.slice(2).join('/');
  if (method === 'GET' && tail === 'info/refs') {
    const service = url.searchParams.get('service') ?? '';
    if (service !== 'git-upload-pack' && service !== 'git-receive-pack') throw new HttpError(400, 'Missing service');
    handleInfoRefs(req, res, repo, service);
    return;
  }
  if (method === 'POST' && tail === 'git-upload-pack') {
    handleUploadPack(res, repo, rawBody);
    return;
  }
  if (method === 'POST' && tail === 'git-receive-pack') {
    handleReceivePack(res, repo, rawBody);
    return;
  }
  sendJson(res, 404, { message: 'Not Found' });
}

// ------------------------------------------------------------------------------------------------
// GraphQL v4: a small parser, a schema table, and an executor over the same store.

type GqlValue =
  | { kind: 'variable'; name: string }
  | { kind: 'int'; value: number }
  | { kind: 'float'; value: number }
  | { kind: 'string'; value: string }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; items: GqlValue[] }
  | { kind: 'object'; fields: Array<{ name: string; value: GqlValue }> };

interface GqlField {
  alias: string | null;
  name: string;
  args: Array<{ name: string; value: GqlValue }>;
  directives: Array<{ name: string; args: Array<{ name: string; value: GqlValue }> }>;
  selection: GqlSelection[] | null;
}

type GqlSelection =
  | { kind: 'field'; field: GqlField }
  | { kind: 'spread'; name: string; directives: GqlField['directives'] }
  | { kind: 'inline'; typeCondition: string | null; directives: GqlField['directives']; selection: GqlSelection[] };

interface GqlOperation {
  type: 'query' | 'mutation';
  name: string | null;
  variables: Array<{ name: string; type: string; defaultValue: GqlValue | null }>;
  selection: GqlSelection[];
}

interface GqlDocument {
  operations: GqlOperation[];
  fragments: Map<string, { typeCondition: string; selection: GqlSelection[] }>;
}

function gqlLex(source: string): Array<{ kind: string; value: string }> {
  const tokens: Array<{ kind: string; value: string }> = [];
  let i = 0;
  const isNameStart = (c: string): boolean => /[A-Za-z_]/.test(c);
  const isNameChar = (c: string): boolean => /[A-Za-z0-9_]/.test(c);
  while (i < source.length) {
    const c = source[i];
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r' || c === ',' || c === '\ufeff') {
      i += 1;
      continue;
    }
    if (c === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (source.startsWith('...', i)) {
      tokens.push({ kind: '...', value: '...' });
      i += 3;
      continue;
    }
    if ('!$():=@[]{}|'.includes(c)) {
      tokens.push({ kind: c, value: c });
      i += 1;
      continue;
    }
    if (c === '"') {
      if (source.startsWith('"""', i)) {
        const end = source.indexOf('"""', i + 3);
        if (end < 0) throw new Error('unterminated block string');
        tokens.push({ kind: 'string', value: source.slice(i + 3, end) });
        i = end + 3;
        continue;
      }
      let j = i + 1;
      let value = '';
      while (j < source.length && source[j] !== '"') {
        if (source[j] === '\\') {
          const esc = source[j + 1];
          if (esc === 'n') value += '\n';
          else if (esc === 't') value += '\t';
          else if (esc === 'r') value += '\r';
          else if (esc === 'b') value += '\b';
          else if (esc === 'f') value += '\f';
          else if (esc === '/') value += '/';
          else if (esc === '\\') value += '\\';
          else if (esc === '"') value += '"';
          else if (esc === 'u') {
            value += String.fromCharCode(parseInt(source.slice(j + 2, j + 6), 16));
            j += 4;
          } else value += esc;
          j += 2;
        } else {
          value += source[j];
          j += 1;
        }
      }
      if (j >= source.length) throw new Error('unterminated string');
      tokens.push({ kind: 'string', value });
      i = j + 1;
      continue;
    }
    if (isNameStart(c)) {
      let j = i;
      while (j < source.length && isNameChar(source[j])) j += 1;
      tokens.push({ kind: 'name', value: source.slice(i, j) });
      i = j;
      continue;
    }
    if (/[0-9-]/.test(c)) {
      let j = i;
      if (source[j] === '-') j += 1;
      while (j < source.length && /[0-9]/.test(source[j])) j += 1;
      let isFloat = false;
      if (source[j] === '.') {
        isFloat = true;
        j += 1;
        while (j < source.length && /[0-9]/.test(source[j])) j += 1;
      }
      if (source[j] === 'e' || source[j] === 'E') {
        isFloat = true;
        j += 1;
        if (source[j] === '+' || source[j] === '-') j += 1;
        while (j < source.length && /[0-9]/.test(source[j])) j += 1;
      }
      tokens.push({ kind: isFloat ? 'float' : 'int', value: source.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`unexpected character ${JSON.stringify(c)}`);
  }
  tokens.push({ kind: 'eof', value: '' });
  return tokens;
}

function gqlParse(source: string): GqlDocument {
  const tokens = gqlLex(source);
  let pos = 0;
  const peek = (): { kind: string; value: string } => tokens[pos];
  const next = (): { kind: string; value: string } => tokens[pos++];
  const expect = (kind: string): { kind: string; value: string } => {
    const token = next();
    if (token.kind !== kind) throw new Error(`expected ${kind}, got ${token.kind} ${token.value}`);
    return token;
  };
  const skip = (kind: string): boolean => {
    if (peek().kind === kind) {
      pos += 1;
      return true;
    }
    return false;
  };

  const parseValue = (): GqlValue => {
    const token = next();
    switch (token.kind) {
      case '$':
        return { kind: 'variable', name: expect('name').value };
      case 'int':
        return { kind: 'int', value: parseInt(token.value, 10) };
      case 'float':
        return { kind: 'float', value: parseFloat(token.value) };
      case 'string':
        return { kind: 'string', value: token.value };
      case 'name':
        if (token.value === 'true') return { kind: 'boolean', value: true };
        if (token.value === 'false') return { kind: 'boolean', value: false };
        if (token.value === 'null') return { kind: 'null' };
        return { kind: 'enum', value: token.value };
      case '[': {
        const items: GqlValue[] = [];
        while (peek().kind !== ']') items.push(parseValue());
        expect(']');
        return { kind: 'list', items };
      }
      case '{': {
        const fields: Array<{ name: string; value: GqlValue }> = [];
        while (peek().kind !== '}') {
          const name = expect('name').value;
          expect(':');
          fields.push({ name, value: parseValue() });
        }
        expect('}');
        return { kind: 'object', fields };
      }
      default:
        throw new Error(`unexpected value token ${token.kind}`);
    }
  };

  const parseType = (): string => {
    let text: string;
    if (skip('[')) {
      text = `[${parseType()}]`;
      expect(']');
    } else {
      text = expect('name').value;
    }
    if (skip('!')) text += '!';
    return text;
  };

  const parseArgs = (): Array<{ name: string; value: GqlValue }> => {
    const args: Array<{ name: string; value: GqlValue }> = [];
    if (!skip('(')) return args;
    while (peek().kind !== ')') {
      const name = expect('name').value;
      expect(':');
      args.push({ name, value: parseValue() });
    }
    expect(')');
    return args;
  };

  const parseDirectives = (): GqlField['directives'] => {
    const directives: GqlField['directives'] = [];
    while (skip('@')) {
      const name = expect('name').value;
      directives.push({ name, args: parseArgs() });
    }
    return directives;
  };

  const parseSelectionSet = (): GqlSelection[] => {
    expect('{');
    const selections: GqlSelection[] = [];
    while (peek().kind !== '}') selections.push(parseSelection());
    expect('}');
    return selections;
  };

  const parseSelection = (): GqlSelection => {
    if (skip('...')) {
      if (peek().kind === 'name' && peek().value === 'on') {
        next();
        const typeCondition = expect('name').value;
        const directives = parseDirectives();
        return { kind: 'inline', typeCondition, directives, selection: parseSelectionSet() };
      }
      const name = expect('name').value;
      return { kind: 'spread', name, directives: parseDirectives() };
    }
    let name = expect('name').value;
    let alias: string | null = null;
    if (skip(':')) {
      alias = name;
      name = expect('name').value;
    }
    const args = parseArgs();
    const directives = parseDirectives();
    const selection = peek().kind === '{' ? parseSelectionSet() : null;
    return { kind: 'field', field: { alias, name, args, directives, selection } };
  };

  const operations: GqlOperation[] = [];
  const fragments = new Map<string, { typeCondition: string; selection: GqlSelection[] }>();
  while (peek().kind !== 'eof') {
    if (peek().kind === '{') {
      operations.push({ type: 'query', name: null, variables: [], selection: parseSelectionSet() });
      continue;
    }
    const keyword = expect('name').value;
    if (keyword === 'fragment') {
      const fragName = expect('name').value;
      const on = expect('name').value;
      if (on !== 'on') throw new Error('fragment without type condition');
      const typeCondition = expect('name').value;
      parseDirectives();
      fragments.set(fragName, { typeCondition, selection: parseSelectionSet() });
      continue;
    }
    if (keyword === 'query' || keyword === 'mutation' || keyword === 'subscription') {
      let name: string | null = null;
      if (peek().kind === 'name') name = next().value;
      const variables: GqlOperation['variables'] = [];
      if (skip('(')) {
        while (peek().kind !== ')') {
          expect('$');
          const varName = expect('name').value;
          expect(':');
          const type = parseType();
          let defaultValue: GqlValue | null = null;
          if (skip('=')) defaultValue = parseValue();
          parseDirectives();
          variables.push({ name: varName, type, defaultValue });
        }
        expect(')');
      }
      parseDirectives();
      operations.push({ type: keyword === 'mutation' ? 'mutation' : 'query', name, variables, selection: parseSelectionSet() });
      continue;
    }
    throw new Error(`unexpected definition ${keyword}`);
  }
  return { operations, fragments };
}

// ------------------------------------------------------------------------------------------------
// The schema table (drives both execution and introspection)

type TypeRef = { kind: 'named'; name: string } | { kind: 'list'; of: TypeRef } | { kind: 'nonnull'; of: TypeRef };

function parseTypeRef(text: string): TypeRef {
  const trimmed = text.trim();
  if (trimmed.endsWith('!')) return { kind: 'nonnull', of: parseTypeRef(trimmed.slice(0, -1)) };
  if (trimmed.startsWith('[') && trimmed.endsWith(']')) return { kind: 'list', of: parseTypeRef(trimmed.slice(1, -1)) };
  return { kind: 'named', name: trimmed };
}

function namedTypeOf(ref: TypeRef): string {
  return ref.kind === 'named' ? ref.name : namedTypeOf(ref.of);
}

interface FieldDef {
  type: string;
  args?: Record<string, { type: string; default?: unknown }>;
}

interface TypeDef {
  kind: 'OBJECT' | 'INTERFACE' | 'ENUM' | 'INPUT_OBJECT' | 'SCALAR';
  fields?: Record<string, FieldDef>;
  enumValues?: string[];
  inputFields?: Record<string, { type: string; default?: unknown }>;
  possibleTypes?: string[];
}

const CONNECTION_ARGS: Record<string, { type: string }> = {
  first: { type: 'Int' },
  after: { type: 'String' },
  last: { type: 'Int' },
  before: { type: 'String' },
};

function connectionTypes(name: string, nodeType: string): Record<string, TypeDef> {
  return {
    [name]: {
      kind: 'OBJECT',
      fields: {
        nodes: { type: `[${nodeType}]` },
        edges: { type: `[${name}Edge]` },
        pageInfo: { type: 'PageInfo!' },
        totalCount: { type: 'Int!' },
      },
    },
    [`${name}Edge`]: {
      kind: 'OBJECT',
      fields: { node: { type: nodeType }, cursor: { type: 'String!' } },
    },
  };
}

const SCHEMA: Record<string, TypeDef> = {
  String: { kind: 'SCALAR' },
  Int: { kind: 'SCALAR' },
  Float: { kind: 'SCALAR' },
  Boolean: { kind: 'SCALAR' },
  ID: { kind: 'SCALAR' },
  DateTime: { kind: 'SCALAR' },
  GitObjectID: { kind: 'SCALAR' },
  URI: { kind: 'SCALAR' },
  Query: {
    kind: 'OBJECT',
    fields: {
      viewer: { type: 'User!' },
      repository: { type: 'Repository', args: { owner: { type: 'String!' }, name: { type: 'String!' } } },
      node: { type: 'Node', args: { id: { type: 'ID!' } } },
      rateLimit: { type: 'RateLimit', args: { dryRun: { type: 'Boolean' } } },
    },
  },
  Mutation: {
    kind: 'OBJECT',
    fields: {
      createIssue: { type: 'CreateIssuePayload', args: { input: { type: 'CreateIssueInput!' } } },
      closeIssue: { type: 'CloseIssuePayload', args: { input: { type: 'CloseIssueInput!' } } },
      reopenIssue: { type: 'ReopenIssuePayload', args: { input: { type: 'ReopenIssueInput!' } } },
      createPullRequest: { type: 'CreatePullRequestPayload', args: { input: { type: 'CreatePullRequestInput!' } } },
      mergePullRequest: { type: 'MergePullRequestPayload', args: { input: { type: 'MergePullRequestInput!' } } },
      addComment: { type: 'AddCommentPayload', args: { input: { type: 'AddCommentInput!' } } },
    },
  },
  RateLimit: {
    kind: 'OBJECT',
    fields: { cost: { type: 'Int!' }, limit: { type: 'Int!' }, remaining: { type: 'Int!' }, resetAt: { type: 'DateTime!' }, nodeCount: { type: 'Int!' }, used: { type: 'Int!' } },
  },
  Node: { kind: 'INTERFACE', fields: { id: { type: 'ID!' } }, possibleTypes: ['User', 'Organization', 'Repository', 'Issue', 'PullRequest', 'IssueComment', 'Label', 'Ref', 'Commit'] },
  RepositoryOwner: {
    kind: 'INTERFACE',
    fields: { id: { type: 'ID!' }, login: { type: 'String!' }, avatarUrl: { type: 'URI!' }, url: { type: 'URI!' } },
    possibleTypes: ['User', 'Organization'],
  },
  User: {
    kind: 'OBJECT',
    fields: {
      id: { type: 'ID!' },
      login: { type: 'String!' },
      name: { type: 'String' },
      email: { type: 'String' },
      databaseId: { type: 'Int' },
      avatarUrl: { type: 'URI!' },
      url: { type: 'URI!' },
      isViewer: { type: 'Boolean!' },
      createdAt: { type: 'DateTime!' },
      updatedAt: { type: 'DateTime!' },
    },
  },
  Organization: {
    kind: 'OBJECT',
    fields: {
      id: { type: 'ID!' },
      login: { type: 'String!' },
      name: { type: 'String' },
      databaseId: { type: 'Int' },
      avatarUrl: { type: 'URI!' },
      url: { type: 'URI!' },
    },
  },
  Repository: {
    kind: 'OBJECT',
    fields: {
      id: { type: 'ID!' },
      databaseId: { type: 'Int!' },
      name: { type: 'String!' },
      nameWithOwner: { type: 'String!' },
      owner: { type: 'RepositoryOwner!' },
      description: { type: 'String' },
      isPrivate: { type: 'Boolean!' },
      isArchived: { type: 'Boolean!' },
      isFork: { type: 'Boolean!' },
      defaultBranchRef: { type: 'Ref' },
      viewerPermission: { type: 'RepositoryPermission' },
      hasIssuesEnabled: { type: 'Boolean!' },
      hasWikiEnabled: { type: 'Boolean!' },
      url: { type: 'URI!' },
      createdAt: { type: 'DateTime!' },
      updatedAt: { type: 'DateTime!' },
      pushedAt: { type: 'DateTime' },
      issue: { type: 'Issue', args: { number: { type: 'Int!' } } },
      issues: {
        type: 'IssueConnection!',
        args: {
          ...CONNECTION_ARGS,
          states: { type: '[IssueState!]' },
          orderBy: { type: 'IssueOrder' },
          labels: { type: '[String!]' },
          filterBy: { type: 'IssueFilters' },
        },
      },
      pullRequest: { type: 'PullRequest', args: { number: { type: 'Int!' } } },
      pullRequests: {
        type: 'PullRequestConnection!',
        args: { ...CONNECTION_ARGS, states: { type: '[PullRequestState!]' }, orderBy: { type: 'PullRequestOrder' }, headRefName: { type: 'String' }, baseRefName: { type: 'String' } },
      },
      labels: { type: 'LabelConnection', args: { ...CONNECTION_ARGS, orderBy: { type: 'LabelOrder' } } },
      ref: { type: 'Ref', args: { qualifiedName: { type: 'String!' } } },
      refs: { type: 'RefConnection', args: { ...CONNECTION_ARGS, refPrefix: { type: 'String!' }, orderBy: { type: 'RefOrder' } } },
    },
  },
  Ref: {
    kind: 'OBJECT',
    fields: {
      id: { type: 'ID!' },
      name: { type: 'String!' },
      prefix: { type: 'String!' },
      target: { type: 'Commit' },
      repository: { type: 'Repository!' },
    },
  },
  Commit: {
    kind: 'OBJECT',
    fields: {
      id: { type: 'ID!' },
      oid: { type: 'GitObjectID!' },
      message: { type: 'String!' },
      messageHeadline: { type: 'String!' },
      tree: { type: 'Tree!' },
      committedDate: { type: 'DateTime!' },
      authoredDate: { type: 'DateTime!' },
      url: { type: 'URI!' },
    },
  },
  Tree: {
    kind: 'OBJECT',
    fields: { id: { type: 'ID!' }, oid: { type: 'GitObjectID!' } },
  },
  Issue: {
    kind: 'OBJECT',
    fields: {
      id: { type: 'ID!' },
      number: { type: 'Int!' },
      title: { type: 'String!' },
      body: { type: 'String' },
      bodyText: { type: 'String' },
      state: { type: 'IssueState!' },
      author: { type: 'User' },
      labels: { type: 'LabelConnection', args: { ...CONNECTION_ARGS, orderBy: { type: 'LabelOrder' } } },
      comments: { type: 'IssueCommentConnection!', args: CONNECTION_ARGS },
      repository: { type: 'Repository!' },
      createdAt: { type: 'DateTime!' },
      updatedAt: { type: 'DateTime!' },
      closedAt: { type: 'DateTime' },
      url: { type: 'URI!' },
    },
  },
  PullRequest: {
    kind: 'OBJECT',
    fields: {
      id: { type: 'ID!' },
      number: { type: 'Int!' },
      title: { type: 'String!' },
      body: { type: 'String' },
      state: { type: 'PullRequestState!' },
      merged: { type: 'Boolean!' },
      mergedAt: { type: 'DateTime' },
      mergeCommit: { type: 'Commit' },
      headRefName: { type: 'String!' },
      baseRefName: { type: 'String!' },
      headRef: { type: 'Ref' },
      baseRef: { type: 'Ref' },
      mergeable: { type: 'MergeableState!' },
      isDraft: { type: 'Boolean!' },
      author: { type: 'User' },
      files: { type: 'PullRequestChangedFileConnection', args: CONNECTION_ARGS },
      comments: { type: 'IssueCommentConnection!', args: CONNECTION_ARGS },
      repository: { type: 'Repository!' },
      createdAt: { type: 'DateTime!' },
      updatedAt: { type: 'DateTime!' },
      closedAt: { type: 'DateTime' },
      url: { type: 'URI!' },
    },
  },
  IssueComment: {
    kind: 'OBJECT',
    fields: {
      id: { type: 'ID!' },
      body: { type: 'String!' },
      bodyText: { type: 'String' },
      author: { type: 'User' },
      createdAt: { type: 'DateTime!' },
      updatedAt: { type: 'DateTime!' },
      url: { type: 'URI!' },
    },
  },
  Label: {
    kind: 'OBJECT',
    fields: {
      id: { type: 'ID!' },
      name: { type: 'String!' },
      color: { type: 'String!' },
      description: { type: 'String' },
      isDefault: { type: 'Boolean!' },
      url: { type: 'URI!' },
    },
  },
  PageInfo: {
    kind: 'OBJECT',
    fields: {
      hasNextPage: { type: 'Boolean!' },
      hasPreviousPage: { type: 'Boolean!' },
      startCursor: { type: 'String' },
      endCursor: { type: 'String' },
    },
  },
  ...connectionTypes('IssueConnection', 'Issue'),
  ...connectionTypes('PullRequestConnection', 'PullRequest'),
  ...connectionTypes('LabelConnection', 'Label'),
  ...connectionTypes('IssueCommentConnection', 'IssueComment'),
  ...connectionTypes('PullRequestChangedFileConnection', 'PullRequestChangedFile'),
  ...connectionTypes('RefConnection', 'Ref'),
  PullRequestChangedFile: {
    kind: 'OBJECT',
    fields: {
      path: { type: 'String!' },
      additions: { type: 'Int!' },
      deletions: { type: 'Int!' },
      changeType: { type: 'PatchStatus!' },
    },
  },
  IssueState: { kind: 'ENUM', enumValues: ['OPEN', 'CLOSED'] },
  PullRequestState: { kind: 'ENUM', enumValues: ['OPEN', 'CLOSED', 'MERGED'] },
  MergeableState: { kind: 'ENUM', enumValues: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] },
  OrderDirection: { kind: 'ENUM', enumValues: ['ASC', 'DESC'] },
  IssueOrderField: { kind: 'ENUM', enumValues: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'] },
  PullRequestOrderField: { kind: 'ENUM', enumValues: ['CREATED_AT', 'UPDATED_AT'] },
  LabelOrderField: { kind: 'ENUM', enumValues: ['NAME', 'CREATED_AT'] },
  RefOrderField: { kind: 'ENUM', enumValues: ['ALPHABETICAL', 'TAG_COMMIT_DATE'] },
  RepositoryPermission: { kind: 'ENUM', enumValues: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'] },
  SearchType: { kind: 'ENUM', enumValues: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'] },
  PullRequestMergeMethod: { kind: 'ENUM', enumValues: ['MERGE', 'SQUASH', 'REBASE'] },
  StateReason: { kind: 'ENUM', enumValues: ['COMPLETED', 'NOT_PLANNED', 'REOPENED'] },
  PatchStatus: { kind: 'ENUM', enumValues: ['ADDED', 'CHANGED', 'COPIED', 'DELETED', 'MODIFIED', 'RENAMED'] },
  IssueOrder: { kind: 'INPUT_OBJECT', inputFields: { field: { type: 'IssueOrderField!' }, direction: { type: 'OrderDirection!' } } },
  PullRequestOrder: { kind: 'INPUT_OBJECT', inputFields: { field: { type: 'PullRequestOrderField!' }, direction: { type: 'OrderDirection!' } } },
  LabelOrder: { kind: 'INPUT_OBJECT', inputFields: { field: { type: 'LabelOrderField' }, direction: { type: 'OrderDirection' } } },
  RefOrder: { kind: 'INPUT_OBJECT', inputFields: { field: { type: 'RefOrderField' }, direction: { type: 'OrderDirection' } } },
  IssueFilters: { kind: 'INPUT_OBJECT', inputFields: { assignee: { type: 'String' }, createdBy: { type: 'String' }, labels: { type: '[String!]' }, states: { type: '[IssueState!]' } } },
  CreateIssueInput: {
    kind: 'INPUT_OBJECT',
    inputFields: {
      repositoryId: { type: 'ID!' },
      title: { type: 'String!' },
      body: { type: 'String' },
      labelIds: { type: '[ID!]' },
      assigneeIds: { type: '[ID!]' },
      milestoneId: { type: 'ID' },
      issueTemplate: { type: 'String' },
      clientMutationId: { type: 'String' },
    },
  },
  CloseIssueInput: {
    kind: 'INPUT_OBJECT',
    inputFields: { issueId: { type: 'ID!' }, stateReason: { type: 'StateReason' }, clientMutationId: { type: 'String' } },
  },
  ReopenIssueInput: {
    kind: 'INPUT_OBJECT',
    inputFields: { issueId: { type: 'ID!' }, clientMutationId: { type: 'String' } },
  },
  CreatePullRequestInput: {
    kind: 'INPUT_OBJECT',
    inputFields: {
      repositoryId: { type: 'ID!' },
      baseRefName: { type: 'String!' },
      headRefName: { type: 'String!' },
      title: { type: 'String!' },
      body: { type: 'String' },
      draft: { type: 'Boolean' },
      maintainerCanModify: { type: 'Boolean' },
      clientMutationId: { type: 'String' },
    },
  },
  MergePullRequestInput: {
    kind: 'INPUT_OBJECT',
    inputFields: {
      pullRequestId: { type: 'ID!' },
      mergeMethod: { type: 'PullRequestMergeMethod' },
      commitHeadline: { type: 'String' },
      commitBody: { type: 'String' },
      expectedHeadOid: { type: 'GitObjectID' },
      authorEmail: { type: 'String' },
      clientMutationId: { type: 'String' },
    },
  },
  AddCommentInput: {
    kind: 'INPUT_OBJECT',
    inputFields: { subjectId: { type: 'ID!' }, body: { type: 'String!' }, clientMutationId: { type: 'String' } },
  },
  CreateIssuePayload: { kind: 'OBJECT', fields: { issue: { type: 'Issue' }, clientMutationId: { type: 'String' } } },
  CloseIssuePayload: { kind: 'OBJECT', fields: { issue: { type: 'Issue' }, clientMutationId: { type: 'String' } } },
  ReopenIssuePayload: { kind: 'OBJECT', fields: { issue: { type: 'Issue' }, clientMutationId: { type: 'String' } } },
  CreatePullRequestPayload: { kind: 'OBJECT', fields: { pullRequest: { type: 'PullRequest' }, clientMutationId: { type: 'String' } } },
  MergePullRequestPayload: { kind: 'OBJECT', fields: { pullRequest: { type: 'PullRequest' }, clientMutationId: { type: 'String' } } },
  AddCommentPayload: {
    kind: 'OBJECT',
    fields: { commentEdge: { type: 'IssueCommentConnectionEdge' }, subject: { type: 'Node' }, clientMutationId: { type: 'String' } },
  },
  __Schema: {
    kind: 'OBJECT',
    fields: {
      types: { type: '[__Type!]!' },
      queryType: { type: '__Type!' },
      mutationType: { type: '__Type' },
      subscriptionType: { type: '__Type' },
      directives: { type: '[__Directive!]!' },
    },
  },
  __Type: {
    kind: 'OBJECT',
    fields: {
      kind: { type: '__TypeKind!' },
      name: { type: 'String' },
      description: { type: 'String' },
      fields: { type: '[__Field!]', args: { includeDeprecated: { type: 'Boolean', default: false } } },
      interfaces: { type: '[__Type!]' },
      possibleTypes: { type: '[__Type!]' },
      enumValues: { type: '[__EnumValue!]', args: { includeDeprecated: { type: 'Boolean', default: false } } },
      inputFields: { type: '[__InputValue!]', args: { includeDeprecated: { type: 'Boolean', default: false } } },
      ofType: { type: '__Type' },
      specifiedByURL: { type: 'String' },
      isOneOf: { type: 'Boolean' },
    },
  },
  __Field: {
    kind: 'OBJECT',
    fields: {
      name: { type: 'String!' },
      description: { type: 'String' },
      args: { type: '[__InputValue!]!', args: { includeDeprecated: { type: 'Boolean', default: false } } },
      type: { type: '__Type!' },
      isDeprecated: { type: 'Boolean!' },
      deprecationReason: { type: 'String' },
    },
  },
  __InputValue: {
    kind: 'OBJECT',
    fields: {
      name: { type: 'String!' },
      description: { type: 'String' },
      type: { type: '__Type!' },
      defaultValue: { type: 'String' },
      isDeprecated: { type: 'Boolean!' },
      deprecationReason: { type: 'String' },
    },
  },
  __EnumValue: {
    kind: 'OBJECT',
    fields: {
      name: { type: 'String!' },
      description: { type: 'String' },
      isDeprecated: { type: 'Boolean!' },
      deprecationReason: { type: 'String' },
    },
  },
  __Directive: {
    kind: 'OBJECT',
    fields: {
      name: { type: 'String!' },
      description: { type: 'String' },
      locations: { type: '[__DirectiveLocation!]!' },
      args: { type: '[__InputValue!]!' },
      isRepeatable: { type: 'Boolean!' },
    },
  },
  __TypeKind: { kind: 'ENUM', enumValues: ['SCALAR', 'OBJECT', 'INTERFACE', 'UNION', 'ENUM', 'INPUT_OBJECT', 'LIST', 'NON_NULL'] },
  __DirectiveLocation: {
    kind: 'ENUM',
    enumValues: ['QUERY', 'MUTATION', 'SUBSCRIPTION', 'FIELD', 'FRAGMENT_DEFINITION', 'FRAGMENT_SPREAD', 'INLINE_FRAGMENT', 'VARIABLE_DEFINITION', 'SCHEMA', 'SCALAR', 'OBJECT', 'FIELD_DEFINITION', 'ARGUMENT_DEFINITION', 'INTERFACE', 'UNION', 'ENUM', 'ENUM_VALUE', 'INPUT_OBJECT', 'INPUT_FIELD_DEFINITION'],
  },
};

const TYPE_INTERFACES: Record<string, string[]> = {
  User: ['Node', 'RepositoryOwner'],
  Organization: ['Node', 'RepositoryOwner'],
  Repository: ['Node'],
  Issue: ['Node'],
  PullRequest: ['Node'],
  IssueComment: ['Node'],
  Label: ['Node'],
  Ref: ['Node'],
  Commit: ['Node'],
};

// ------------------------------------------------------------------------------------------------
// GraphQL execution

type GqlObj = { __type: string; [key: string]: unknown };

class GqlError extends Error {}

interface ExecCtx {
  doc: GqlDocument;
  variables: Record<string, unknown>;
  errors: Array<{ message: string }>;
}

function resolveValue(value: GqlValue, ctx: ExecCtx): unknown {
  switch (value.kind) {
    case 'variable':
      return ctx.variables[value.name];
    case 'int':
    case 'float':
    case 'string':
    case 'boolean':
    case 'enum':
      return value.value;
    case 'null':
      return null;
    case 'list':
      return value.items.map((item) => resolveValue(item, ctx));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const field of value.fields) out[field.name] = resolveValue(field.value, ctx);
      return out;
    }
  }
}

function argsOf(field: GqlField, ctx: ExecCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const arg of field.args) out[arg.name] = resolveValue(arg.value, ctx);
  return out;
}

function directivesAllow(directives: GqlField['directives'], ctx: ExecCtx): boolean {
  for (const directive of directives) {
    const args = argsOf({ alias: null, name: '', args: directive.args, directives: [], selection: null }, ctx);
    if (directive.name === 'skip' && args.if === true) return false;
    if (directive.name === 'include' && args.if === false) return false;
  }
  return true;
}

function typeMatches(condition: string | null, concrete: string): boolean {
  if (condition === null) return true;
  if (condition === concrete) return true;
  const interfaces = TYPE_INTERFACES[concrete] ?? [];
  return interfaces.includes(condition);
}

interface CollectedField {
  field: GqlField;
  parentType: string;
}

function collectFields(selections: readonly GqlSelection[], parentType: string, concrete: string, ctx: ExecCtx, out: Map<string, CollectedField>): void {
  for (const selection of selections) {
    if (!directivesAllow(selection.kind === 'field' ? selection.field.directives : selection.directives, ctx)) continue;
    if (selection.kind === 'field') {
      const key = selection.field.alias ?? selection.field.name;
      if (!out.has(key)) out.set(key, { field: selection.field, parentType });
    } else if (selection.kind === 'inline') {
      if (typeMatches(selection.typeCondition, concrete)) {
        collectFields(selection.selection, selection.typeCondition ?? parentType, concrete, ctx, out);
      }
    } else {
      const fragment = ctx.doc.fragments.get(selection.name);
      if (fragment !== undefined && typeMatches(fragment.typeCondition, concrete)) {
        collectFields(fragment.selection, fragment.typeCondition, concrete, ctx, out);
      }
    }
  }
}

function executeSelectionSet(selections: readonly GqlSelection[], parentType: string, obj: GqlObj | null, ctx: ExecCtx): Record<string, unknown> {
  const concrete = obj?.__type ?? parentType;
  const collected = new Map<string, CollectedField>();
  collectFields(selections, parentType, concrete, ctx, collected);
  const out: Record<string, unknown> = {};
  for (const [key, { field, parentType: fieldParent }] of collected) {
    out[key] = executeField(field, fieldParent, obj, ctx);
  }
  return out;
}

function executeField(field: GqlField, parentType: string, obj: GqlObj | null, ctx: ExecCtx): unknown {
  const name = field.name;
  if (name === '__typename') return obj?.__type ?? parentType;
  if (name === '__schema' && parentType === 'Query') {
    return completeValue(parseTypeRef('__Schema'), { __type: '__Schema' }, field, ctx);
  }
  if (name === '__type' && parentType === 'Query') {
    const args = argsOf(field, ctx);
    const typeName = typeof args.name === 'string' ? args.name : '';
    const value: GqlObj | null = SCHEMA[typeName] !== undefined ? { __type: '__Type', ref: { kind: 'named', name: typeName } as TypeRef } : null;
    return completeValue(parseTypeRef('__Type'), value, field, ctx);
  }
  const typeDef = SCHEMA[parentType];
  const fieldDef = typeDef?.fields?.[name];
  if (fieldDef === undefined) {
    ctx.errors.push({ message: `Field '${name}' doesn't exist on type '${parentType}'` });
    return null;
  }
  let raw: unknown;
  try {
    raw = resolveField(parentType, name, obj, argsOf(field, ctx), ctx);
  } catch (err) {
    ctx.errors.push({ message: err instanceof Error ? err.message : String(err) });
    return null;
  }
  return completeValue(parseTypeRef(fieldDef.type), raw, field, ctx);
}

function completeValue(ref: TypeRef, raw: unknown, field: GqlField, ctx: ExecCtx): unknown {
  if (ref.kind === 'nonnull') return completeValue(ref.of, raw, field, ctx);
  if (raw === null || raw === undefined) return null;
  if (ref.kind === 'list') {
    const items = Array.isArray(raw) ? raw : [raw];
    return items.map((item) => completeValue(ref.of, item, field, ctx));
  }
  const def = SCHEMA[ref.name];
  if (def === undefined || def.kind === 'SCALAR' || def.kind === 'ENUM') return raw;
  const gqlObj = raw as GqlObj;
  if (field.selection === null) return null;
  return executeSelectionSet(field.selection, ref.name, gqlObj, ctx);
}

// ------------------------------------------------------------------------------------------------
// Introspection values

function typeObj(ref: TypeRef): GqlObj {
  return { __type: '__Type', ref };
}

function inputValueObj(name: string, typeText: string, defaultValue: unknown): GqlObj {
  return {
    __type: '__InputValue',
    valueName: name,
    typeText,
    defaultText: defaultValue === undefined ? null : typeof defaultValue === 'string' ? JSON.stringify(defaultValue) : String(defaultValue),
  };
}

function fieldObj(name: string, def: FieldDef): GqlObj {
  return { __type: '__Field', fieldName: name, fieldDef: def };
}

const DIRECTIVES: GqlObj[] = [
  {
    __type: '__Directive',
    name: 'include',
    description: 'Directs the executor to include this field or fragment only when the `if` argument is true.',
    locations: ['FIELD', 'FRAGMENT_SPREAD', 'INLINE_FRAGMENT'],
    args: [inputValueObj('if', 'Boolean!', undefined)],
    isRepeatable: false,
  },
  {
    __type: '__Directive',
    name: 'skip',
    description: 'Directs the executor to skip this field or fragment when the `if` argument is true.',
    locations: ['FIELD', 'FRAGMENT_SPREAD', 'INLINE_FRAGMENT'],
    args: [inputValueObj('if', 'Boolean!', undefined)],
    isRepeatable: false,
  },
  {
    __type: '__Directive',
    name: 'deprecated',
    description: 'Marks an element of a GraphQL schema as no longer supported.',
    locations: ['FIELD_DEFINITION', 'ARGUMENT_DEFINITION', 'INPUT_FIELD_DEFINITION', 'ENUM_VALUE'],
    args: [inputValueObj('reason', 'String', 'No longer supported')],
    isRepeatable: false,
  },
  {
    __type: '__Directive',
    name: 'specifiedBy',
    description: 'Exposes a URL that specifies the behaviour of this scalar.',
    locations: ['SCALAR'],
    args: [inputValueObj('url', 'String!', undefined)],
    isRepeatable: false,
  },
];

// ------------------------------------------------------------------------------------------------
// Connections

function cursorFor(index: number): string {
  return Buffer.from(`cursor:${index}`, 'utf8').toString('base64');
}

function parseCursor(raw: unknown): number | null {
  if (typeof raw !== 'string') return null;
  try {
    const text = Buffer.from(raw, 'base64').toString('utf8');
    const match = /^cursor:(\d+)$/.exec(text);
    return match === null ? null : Number(match[1]);
  } catch {
    return null;
  }
}

interface ConnectionPage {
  items: GqlObj[];
  pageInfo: { hasNextPage: boolean; hasPreviousPage: boolean; startCursor: string | null; endCursor: string | null };
  edges: Array<{ node: GqlObj; cursor: string }>;
  totalCount: number;
}

function applyConnection(items: readonly GqlObj[], args: Record<string, unknown>): ConnectionPage {
  let start = 0;
  let end = items.length;
  const after = parseCursor(args.after);
  if (after !== null) start = Math.min(items.length, after + 1);
  const before = parseCursor(args.before);
  if (before !== null) end = Math.min(end, before);
  let indices = items.map((_, index) => index).slice(start, end);
  if (typeof args.first === 'number') indices = indices.slice(0, Math.max(0, args.first));
  if (typeof args.last === 'number') indices = indices.slice(Math.max(0, indices.length - Math.max(0, args.last)));
  const pageItems = indices.map((index) => items[index]);
  const edges = indices.map((index) => ({ node: items[index], cursor: cursorFor(index) }));
  return {
    items: pageItems,
    edges,
    totalCount: items.length,
    pageInfo: {
      hasNextPage: indices.length > 0 ? indices[indices.length - 1] + 1 < end : false,
      hasPreviousPage: indices.length > 0 ? indices[0] > start : false,
      startCursor: edges.length > 0 ? edges[0].cursor : null,
      endCursor: edges.length > 0 ? edges[edges.length - 1].cursor : null,
    },
  };
}

function connectionObj(type: string, items: readonly GqlObj[], args: Record<string, unknown>): GqlObj {
  return { __type: type, page: applyConnection(items, args) };
}

// ------------------------------------------------------------------------------------------------
// GraphQL domain objects and field resolution

function viewerObj(): GqlObj {
  return { __type: 'User' };
}

function repoObj(repo: Repo): GqlObj {
  return { __type: 'Repository', repo };
}

function issueObj(repo: Repo, issue: IssueRec): GqlObj {
  return { __type: 'Issue', repo, rec: issue };
}

function pullObj(repo: Repo, pull: PullRec): GqlObj {
  return { __type: 'PullRequest', repo, rec: pull };
}

function commentObj(repo: Repo, number: number, comment: CommentRec): GqlObj {
  return { __type: 'IssueComment', repo, number, rec: comment };
}

function labelObj(repo: Repo, name: string): GqlObj {
  return { __type: 'Label', repo, name };
}

function refObj(repo: Repo, branch: string): GqlObj | null {
  const tip = branchTip(repo, branch);
  if (tip === null) return null;
  return { __type: 'Ref', repo, name: branch, oid: tip };
}

function commitObj(repo: Repo, oid: string): GqlObj {
  return { __type: 'Commit', repo, oid };
}

function repoOf(obj: GqlObj): Repo {
  return obj.repo as Repo;
}

function nodeById(id: unknown): GqlObj | null {
  if (typeof id !== 'string') return null;
  const decoded = decodeGlobalId(id);
  if (decoded === null) return null;
  const { type, key } = decoded;
  if (type === 'User') return key === String(VIEWER.id) ? viewerObj() : null;
  if (type === 'Repository') {
    const repo = repoByGlobalId(id);
    return repo === null ? null : repoObj(repo);
  }
  if (type === 'Issue' || type === 'PullRequest') {
    const split = key.indexOf(':');
    if (split < 0) return null;
    const repoId = Number(key.slice(0, split));
    const number = Number(key.slice(split + 1));
    for (const repo of repos.values()) {
      if (repo.id !== repoId) continue;
      if (type === 'Issue') {
        const issue = repo.issues.get(number);
        return issue === undefined ? null : issueObj(repo, issue);
      }
      const pull = repo.pulls.get(number);
      return pull === undefined ? null : pullObj(repo, pull);
    }
    return null;
  }
  if (type === 'IssueComment') {
    const commentId = Number(key);
    for (const repo of repos.values()) {
      for (const [number, list] of repo.comments) {
        const found = list.find((comment) => comment.id === commentId);
        if (found !== undefined) return commentObj(repo, number, found);
      }
    }
    return null;
  }
  if (type === 'Label') {
    const split = key.indexOf(':');
    if (split < 0) return null;
    const repoId = Number(key.slice(0, split));
    const name = decodeURIComponent(key.slice(split + 1));
    for (const repo of repos.values()) {
      if (repo.id === repoId && repo.labels.has(name)) return labelObj(repo, name);
    }
    return null;
  }
  if (type === 'Commit') {
    for (const repo of repos.values()) if (repo.objects.get(key)?.type === 'commit') return commitObj(repo, key);
    return null;
  }
  return null;
}

function resolveIssueTarget(id: unknown): { repo: Repo; number: number; kind: 'issue' | 'pull' } | null {
  if (typeof id !== 'string') return null;
  const decoded = decodeGlobalId(id);
  if (decoded === null || (decoded.type !== 'Issue' && decoded.type !== 'PullRequest')) return null;
  const split = decoded.key.indexOf(':');
  if (split < 0) return null;
  const repoId = Number(decoded.key.slice(0, split));
  const number = Number(decoded.key.slice(split + 1));
  for (const repo of repos.values()) {
    if (repo.id !== repoId) continue;
    if (decoded.type === 'Issue' && repo.issues.has(number)) return { repo, number, kind: 'issue' };
    if (decoded.type === 'PullRequest' && repo.pulls.has(number)) return { repo, number, kind: 'pull' };
  }
  return null;
}

function sortedIssues(repo: Repo, args: Record<string, unknown>): IssueRec[] {
  const states = Array.isArray(args.states) ? (args.states as string[]) : ['OPEN'];
  let list = [...repo.issues.values()].filter((issue) => states.includes(issue.state.toUpperCase()));
  const labelFilter = Array.isArray(args.labels) ? (args.labels as string[]) : [];
  if (labelFilter.length > 0) list = list.filter((issue) => labelFilter.every((label) => issue.labels.includes(label)));
  const orderBy = (args.orderBy ?? null) as { field?: string; direction?: string } | null;
  const direction = orderBy?.direction === 'ASC' ? 'ASC' : 'DESC';
  const field = orderBy?.field ?? 'CREATED_AT';
  list.sort((a, b) => {
    const ka = field === 'UPDATED_AT' ? a.updatedAt : field === 'COMMENTS' ? String((repo.comments.get(a.number) ?? []).length).padStart(8, '0') : a.createdAt;
    const kb = field === 'UPDATED_AT' ? b.updatedAt : field === 'COMMENTS' ? String((repo.comments.get(b.number) ?? []).length).padStart(8, '0') : b.createdAt;
    const cmp = ka === kb ? a.number - b.number : ka < kb ? -1 : 1;
    return direction === 'ASC' ? cmp : -cmp;
  });
  return list;
}

function sortedPulls(repo: Repo, args: Record<string, unknown>): PullRec[] {
  const states = Array.isArray(args.states) ? (args.states as string[]) : ['OPEN'];
  let list = [...repo.pulls.values()].filter((pull) => {
    const state = pull.merged ? 'MERGED' : pull.state.toUpperCase();
    return states.includes(state);
  });
  if (typeof args.headRefName === 'string') list = list.filter((pull) => pull.headRef === args.headRefName);
  if (typeof args.baseRefName === 'string') list = list.filter((pull) => pull.baseRef === args.baseRefName);
  const orderBy = (args.orderBy ?? null) as { field?: string; direction?: string } | null;
  const direction = orderBy?.direction === 'ASC' ? 'ASC' : 'DESC';
  list.sort((a, b) => {
    const ka = orderBy?.field === 'UPDATED_AT' ? a.updatedAt : a.createdAt;
    const kb = orderBy?.field === 'UPDATED_AT' ? b.updatedAt : b.createdAt;
    const cmp = ka === kb ? a.number - b.number : ka < kb ? -1 : 1;
    return direction === 'ASC' ? cmp : -cmp;
  });
  return list;
}

function resolveField(parentType: string, name: string, obj: GqlObj | null, args: Record<string, unknown>, ctx: ExecCtx): unknown {
  // Introspection meta types resolve from their wrapper values.
  if (parentType === '__Schema') {
    switch (name) {
      case 'types':
        return Object.keys(SCHEMA).sort().map((typeName) => typeObj({ kind: 'named', name: typeName }));
      case 'queryType':
        return typeObj({ kind: 'named', name: 'Query' });
      case 'mutationType':
        return typeObj({ kind: 'named', name: 'Mutation' });
      case 'subscriptionType':
        return null;
      case 'directives':
        return DIRECTIVES;
    }
  }
  if (parentType === '__Type') {
    const ref = (obj as GqlObj).ref as TypeRef;
    switch (name) {
      case 'kind':
        return ref.kind === 'named' ? (SCHEMA[ref.name]?.kind ?? 'OBJECT') : ref.kind === 'list' ? 'LIST' : 'NON_NULL';
      case 'name':
        return ref.kind === 'named' ? ref.name : null;
      case 'description':
        return null;
      case 'fields': {
        if (ref.kind !== 'named') return null;
        const def = SCHEMA[ref.name];
        if (def === undefined || (def.kind !== 'OBJECT' && def.kind !== 'INTERFACE') || def.fields === undefined) return null;
        return Object.entries(def.fields).map(([fieldName, fieldDef]) => fieldObj(fieldName, fieldDef));
      }
      case 'interfaces': {
        if (ref.kind !== 'named') return null;
        const def = SCHEMA[ref.name];
        if (def === undefined || def.kind !== 'OBJECT') return null;
        return (TYPE_INTERFACES[ref.name] ?? []).map((iface) => typeObj({ kind: 'named', name: iface }));
      }
      case 'possibleTypes': {
        if (ref.kind !== 'named') return null;
        const def = SCHEMA[ref.name];
        if (def === undefined || def.kind !== 'INTERFACE' || def.possibleTypes === undefined) return null;
        return def.possibleTypes.map((typeName) => typeObj({ kind: 'named', name: typeName }));
      }
      case 'enumValues': {
        if (ref.kind !== 'named') return null;
        const def = SCHEMA[ref.name];
        if (def === undefined || def.kind !== 'ENUM' || def.enumValues === undefined) return null;
        return def.enumValues.map((value) => ({ __type: '__EnumValue', name: value }));
      }
      case 'inputFields': {
        if (ref.kind !== 'named') return null;
        const def = SCHEMA[ref.name];
        if (def === undefined || def.kind !== 'INPUT_OBJECT' || def.inputFields === undefined) return null;
        return Object.entries(def.inputFields).map(([inputName, inputDef]) => inputValueObj(inputName, inputDef.type, inputDef.default));
      }
      case 'ofType':
        return ref.kind === 'named' ? null : typeObj(ref.of);
      case 'specifiedByURL':
        return null;
      case 'isOneOf':
        return false;
    }
  }
  if (parentType === '__Field') {
    const wrapper = obj as GqlObj;
    const def = wrapper.fieldDef as FieldDef;
    switch (name) {
      case 'name':
        return wrapper.fieldName;
      case 'description':
        return null;
      case 'args':
        return Object.entries(def.args ?? {}).map(([argName, argDef]) => inputValueObj(argName, argDef.type, argDef.default));
      case 'type':
        return typeObj(parseTypeRef(def.type));
      case 'isDeprecated':
        return false;
      case 'deprecationReason':
        return null;
    }
  }
  if (parentType === '__InputValue') {
    const wrapper = obj as GqlObj;
    switch (name) {
      case 'name':
        return wrapper.valueName;
      case 'description':
        return null;
      case 'type':
        return typeObj(parseTypeRef(wrapper.typeText as string));
      case 'defaultValue':
        return wrapper.defaultText;
      case 'isDeprecated':
        return false;
      case 'deprecationReason':
        return null;
    }
  }
  if (parentType === '__EnumValue') return (obj as GqlObj)[name] === undefined ? (name === 'isDeprecated' ? false : null) : (obj as GqlObj)[name];
  if (parentType === '__Directive') {
    const wrapper = obj as GqlObj;
    if (wrapper[name] !== undefined) return wrapper[name];
    return name === 'description' ? null : null;
  }
  if (parentType === 'PageInfo' || parentType.endsWith('Payload')) {
    return (obj as GqlObj)?.[name] ?? null;
  }
  if (parentType.endsWith('Connection')) {
    const page = (obj as GqlObj).page as ConnectionPage;
    const edgeType = `${parentType}Edge`;
    switch (name) {
      case 'nodes':
        return page.items;
      case 'edges':
        return page.edges.map((edge) => ({ __type: edgeType, node: edge.node, cursor: edge.cursor }));
      case 'pageInfo':
        return { __type: 'PageInfo', ...page.pageInfo };
      case 'totalCount':
        return page.totalCount;
    }
  }
  if (parentType.endsWith('Edge')) {
    return (obj as GqlObj)?.[name] ?? null;
  }

  // Interface parents (Node, RepositoryOwner) resolve through the concrete type.
  const effectiveType = (parentType === 'Node' || parentType === 'RepositoryOwner') && obj !== null ? ((obj as GqlObj).__type ?? parentType) : parentType;
  switch (effectiveType) {
    case 'Query': {
      switch (name) {
        case 'viewer':
          return viewerObj();
        case 'repository': {
          const repo = typeof args.owner === 'string' && typeof args.name === 'string' ? findRepo(args.owner, args.name) : null;
          return repo === null ? null : repoObj(repo);
        }
        case 'node':
          return nodeById(args.id);
        case 'rateLimit':
          return {
            __type: 'RateLimit',
            cost: 1,
            limit: 5000,
            remaining: 4999,
            used: 1,
            nodeCount: 0,
            resetAt: new Date((EPOCH_SEC + 3600) * 1000).toISOString(),
          };
      }
      break;
    }
    case 'Mutation': {
      return resolveMutation(name, args);
    }
    case 'User': {
      switch (name) {
        case 'id':
          return globalId('User', VIEWER.id);
        case 'login':
          return VIEWER.login;
        case 'name':
          return VIEWER.name;
        case 'email':
          return VIEWER.email;
        case 'databaseId':
          return VIEWER.id;
        case 'avatarUrl':
          return '';
        case 'url':
          return '';
        case 'isViewer':
          return true;
        case 'createdAt':
        case 'updatedAt':
          return new Date(EPOCH_SEC * 1000).toISOString();
      }
      break;
    }
    case 'Repository': {
      const repo = repoOf(obj as GqlObj);
      switch (name) {
        case 'id':
          return globalId('Repository', repo.id);
        case 'databaseId':
          return repo.id;
        case 'name':
          return repo.name;
        case 'nameWithOwner':
          return `${repo.owner}/${repo.name}`;
        case 'owner':
          return viewerObj();
        case 'description':
          return repo.description === '' ? null : repo.description;
        case 'isPrivate':
          return repo.isPrivate;
        case 'isArchived':
          return false;
        case 'isFork':
          return false;
        case 'defaultBranchRef':
          return refObj(repo, repo.defaultBranch);
        case 'viewerPermission':
          return 'ADMIN';
        case 'hasIssuesEnabled':
          return true;
        case 'hasWikiEnabled':
          return true;
        case 'url':
          return '';
        case 'createdAt':
          return repo.createdAt;
        case 'updatedAt':
          return repo.updatedAt;
        case 'pushedAt':
          return repo.updatedAt;
        case 'issue': {
          const issue = typeof args.number === 'number' ? repo.issues.get(args.number) : undefined;
          return issue === undefined ? null : issueObj(repo, issue);
        }
        case 'issues':
          return connectionObj('IssueConnection', sortedIssues(repo, args).map((issue) => issueObj(repo, issue)), args);
        case 'pullRequest': {
          const pull = typeof args.number === 'number' ? repo.pulls.get(args.number) : undefined;
          return pull === undefined ? null : pullObj(repo, pull);
        }
        case 'pullRequests':
          return connectionObj('PullRequestConnection', sortedPulls(repo, args).map((pull) => pullObj(repo, pull)), args);
        case 'labels': {
          const names = [...repo.labels.keys()].sort();
          return connectionObj('LabelConnection', names.map((labelName) => labelObj(repo, labelName)), args);
        }
        case 'ref': {
          const qualified = typeof args.qualifiedName === 'string' ? args.qualifiedName : '';
          const branch = qualified.replace(/^refs\/heads\//, '');
          return refObj(repo, branch);
        }
        case 'refs': {
          const prefix = typeof args.refPrefix === 'string' ? args.refPrefix : 'refs/';
          const items: GqlObj[] = [];
          for (const ref of [...repo.refs.keys()].sort()) {
            if (!ref.startsWith(prefix) || !ref.startsWith('refs/heads/')) continue;
            const item = refObj(repo, ref.slice('refs/heads/'.length));
            if (item !== null) items.push(item);
          }
          return connectionObj('RefConnection', items, args);
        }
      }
      break;
    }
    case 'Issue': {
      const repo = repoOf(obj as GqlObj);
      const issue = (obj as GqlObj).rec as IssueRec;
      switch (name) {
        case 'id':
          return globalId('Issue', `${repo.id}:${issue.number}`);
        case 'number':
          return issue.number;
        case 'title':
          return issue.title;
        case 'body':
        case 'bodyText':
          return issue.body;
        case 'state':
          return issue.state.toUpperCase();
        case 'author':
          return viewerObj();
        case 'labels':
          return connectionObj('LabelConnection', issue.labels.map((labelName) => labelObj(repo, labelName)), args);
        case 'comments':
          return connectionObj('IssueCommentConnection', (repo.comments.get(issue.number) ?? []).map((comment) => commentObj(repo, issue.number, comment)), args);
        case 'repository':
          return repoObj(repo);
        case 'createdAt':
          return issue.createdAt;
        case 'updatedAt':
          return issue.updatedAt;
        case 'closedAt':
          return issue.closedAt;
        case 'url':
          return '';
      }
      break;
    }
    case 'PullRequest': {
      const repo = repoOf(obj as GqlObj);
      const pull = (obj as GqlObj).rec as PullRec;
      switch (name) {
        case 'id':
          return globalId('PullRequest', `${repo.id}:${pull.number}`);
        case 'number':
          return pull.number;
        case 'title':
          return pull.title;
        case 'body':
          return pull.body;
        case 'state':
          return pull.merged ? 'MERGED' : pull.state.toUpperCase();
        case 'merged':
          return pull.merged;
        case 'mergedAt':
          return pull.mergedAt;
        case 'mergeCommit':
          return pull.mergeCommitSha === null ? null : commitObj(repo, pull.mergeCommitSha);
        case 'headRefName':
          return pull.headRef;
        case 'baseRefName':
          return pull.baseRef;
        case 'headRef':
          return refObj(repo, pull.headRef);
        case 'baseRef':
          return refObj(repo, pull.baseRef);
        case 'mergeable':
          if (pull.merged || pull.state !== 'open') return 'UNKNOWN';
          return computeMergeable(repo, pull) ? 'MERGEABLE' : 'CONFLICTING';
        case 'isDraft':
          return false;
        case 'author':
          return viewerObj();
        case 'files': {
          const items = pullChanges(repo, pull).map((change) => ({
            __type: 'PullRequestChangedFile',
            path: change.path,
            additions: change.additions,
            deletions: change.deletions,
            changeType: change.status === 'added' ? 'ADDED' : change.status === 'removed' ? 'DELETED' : 'MODIFIED',
          }));
          return connectionObj('PullRequestChangedFileConnection', items, args);
        }
        case 'comments':
          return connectionObj('IssueCommentConnection', (repo.comments.get(pull.number) ?? []).map((comment) => commentObj(repo, pull.number, comment)), args);
        case 'repository':
          return repoObj(repo);
        case 'createdAt':
          return pull.createdAt;
        case 'updatedAt':
          return pull.updatedAt;
        case 'closedAt':
          return pull.closedAt;
        case 'url':
          return '';
      }
      break;
    }
    case 'IssueComment': {
      const comment = (obj as GqlObj).rec as CommentRec;
      switch (name) {
        case 'id':
          return globalId('IssueComment', comment.id);
        case 'body':
        case 'bodyText':
          return comment.body;
        case 'author':
          return viewerObj();
        case 'createdAt':
          return comment.createdAt;
        case 'updatedAt':
          return comment.updatedAt;
        case 'url':
          return '';
      }
      break;
    }
    case 'Label': {
      const repo = repoOf(obj as GqlObj);
      const labelName = (obj as GqlObj).name as string;
      const label = repo.labels.get(labelName);
      switch (name) {
        case 'id':
          return globalId('Label', `${repo.id}:${encodeURIComponent(labelName)}`);
        case 'name':
          return labelName;
        case 'color':
          return label?.color ?? 'ededed';
        case 'description':
          return label?.description ?? null;
        case 'isDefault':
          return false;
        case 'url':
          return '';
      }
      break;
    }
    case 'Ref': {
      const repo = repoOf(obj as GqlObj);
      switch (name) {
        case 'id':
          return globalId('Ref', `${repo.id}:refs/heads/${(obj as GqlObj).name as string}`);
        case 'name':
          return (obj as GqlObj).name;
        case 'prefix':
          return 'refs/heads/';
        case 'target': {
          const oid = (obj as GqlObj).oid as string;
          return commitObj(repo, oid);
        }
        case 'repository':
          return repoObj(repo);
      }
      break;
    }
    case 'Commit': {
      const repo = repoOf(obj as GqlObj);
      const oid = (obj as GqlObj).oid as string;
      const commit = getCommit(repo, oid);
      switch (name) {
        case 'id':
          return globalId('Commit', oid);
        case 'oid':
          return oid;
        case 'message':
          return commit?.message ?? '';
        case 'messageHeadline':
          return (commit?.message ?? '').split('\n')[0];
        case 'tree':
          return { __type: 'Tree', repo, oid: commit?.tree ?? ZERO_OID };
        case 'committedDate':
          return commit === null ? new Date(EPOCH_SEC * 1000).toISOString() : parseIdentity(commit.committer).date;
        case 'authoredDate':
          return commit === null ? new Date(EPOCH_SEC * 1000).toISOString() : parseIdentity(commit.author).date;
        case 'url':
          return '';
      }
      break;
    }
    case 'Tree': {
      switch (name) {
        case 'id':
          return globalId('Tree', (obj as GqlObj).oid as string);
        case 'oid':
          return (obj as GqlObj).oid;
      }
      break;
    }
  }
  return (obj as GqlObj)?.[name] ?? null;
}

function resolveMutation(name: string, args: Record<string, unknown>): unknown {
  const input = (args.input ?? {}) as Record<string, unknown>;
  const clientMutationId = typeof input.clientMutationId === 'string' ? input.clientMutationId : null;
  switch (name) {
    case 'createIssue': {
      const repo = typeof input.repositoryId === 'string' ? repoByGlobalId(input.repositoryId) : null;
      if (repo === null) throw new GqlError('Repository not found');
      const title = typeof input.title === 'string' ? input.title : '';
      const labels: string[] = [];
      if (Array.isArray(input.labelIds)) {
        for (const labelId of input.labelIds) {
          const decoded = decodeGlobalId(String(labelId));
          if (decoded !== null && decoded.type === 'Label') {
            const labelName = decodeURIComponent(decoded.key.slice(decoded.key.indexOf(':') + 1));
            if (repo.labels.has(labelName)) labels.push(labelName);
          }
        }
      }
      const issue = createIssueRec(repo, title, typeof input.body === 'string' ? input.body : '', labels);
      return { __type: 'CreateIssuePayload', issue: issueObj(repo, issue), clientMutationId };
    }
    case 'closeIssue':
    case 'reopenIssue': {
      const target = resolveIssueTarget(input.issueId);
      if (target === null || target.kind !== 'issue') throw new GqlError('Issue not found');
      const issue = target.repo.issues.get(target.number)!;
      const t = nextTime();
      if (name === 'closeIssue') {
        issue.state = 'closed';
        issue.closedAt = t.iso;
      } else {
        issue.state = 'open';
        issue.closedAt = null;
      }
      issue.updatedAt = t.iso;
      return { __type: name === 'closeIssue' ? 'CloseIssuePayload' : 'ReopenIssuePayload', issue: issueObj(target.repo, issue), clientMutationId };
    }
    case 'createPullRequest': {
      const repo = typeof input.repositoryId === 'string' ? repoByGlobalId(input.repositoryId) : null;
      if (repo === null) throw new GqlError('Repository not found');
      const head = typeof input.headRefName === 'string' ? input.headRefName : '';
      const base = typeof input.baseRefName === 'string' ? input.baseRefName : '';
      const headTip = branchTip(repo, head);
      const baseTip = branchTip(repo, base);
      if (headTip === null || baseTip === null) throw new GqlError('Head or base ref does not exist');
      if (head === base || headTip === baseTip) throw new GqlError('No commits between base and head');
      for (const existing of repo.pulls.values()) {
        if (existing.state === 'open' && existing.headRef === head && existing.baseRef === base) {
          throw new GqlError('A pull request already exists for this head and base');
        }
      }
      const pull = createPullRec(repo, typeof input.title === 'string' ? input.title : '', typeof input.body === 'string' ? input.body : '', head, base);
      return { __type: 'CreatePullRequestPayload', pullRequest: pullObj(repo, pull), clientMutationId };
    }
    case 'mergePullRequest': {
      const target = resolveIssueTarget(input.pullRequestId);
      if (target === null || target.kind !== 'pull') throw new GqlError('Pull request not found');
      const pull = target.repo.pulls.get(target.number)!;
      if (pull.merged || pull.state !== 'open') throw new GqlError('Pull request is not mergeable');
      const sha = mergePullRec(
        target.repo,
        pull,
        typeof input.commitHeadline === 'string' ? input.commitHeadline : undefined,
        typeof input.commitBody === 'string' ? input.commitBody : undefined,
      );
      if (sha === null) throw new GqlError('Pull request is not mergeable');
      return { __type: 'MergePullRequestPayload', pullRequest: pullObj(target.repo, pull), clientMutationId };
    }
    case 'addComment': {
      const target = resolveIssueTarget(input.subjectId);
      if (target === null) throw new GqlError('Subject not found');
      const comment = addCommentRec(target.repo, target.number, typeof input.body === 'string' ? input.body : '');
      const subject = target.kind === 'issue' ? issueObj(target.repo, target.repo.issues.get(target.number)!) : pullObj(target.repo, target.repo.pulls.get(target.number)!);
      return {
        __type: 'AddCommentPayload',
        commentEdge: { __type: 'IssueCommentConnectionEdge', node: commentObj(target.repo, target.number, comment), cursor: cursorFor(0) },
        subject,
        clientMutationId,
      };
    }
  }
  throw new GqlError(`Unknown mutation ${name}`);
}

function executeOperation(doc: GqlDocument, operation: GqlOperation, variablesIn: Record<string, unknown>): { data: Record<string, unknown>; errors: Array<{ message: string }> } {
  const ctx: ExecCtx = { doc, variables: {}, errors: [] };
  for (const variable of operation.variables) {
    if (variablesIn[variable.name] !== undefined) ctx.variables[variable.name] = variablesIn[variable.name];
    else if (variable.defaultValue !== null) ctx.variables[variable.name] = resolveValue(variable.defaultValue, ctx);
  }
  for (const [key, value] of Object.entries(variablesIn)) {
    if (ctx.variables[key] === undefined) ctx.variables[key] = value;
  }
  const rootType = operation.type === 'mutation' ? 'Mutation' : 'Query';
  const data = executeSelectionSet(operation.selection, rootType, { __type: rootType }, ctx);
  return { data, errors: ctx.errors };
}

function handleGraphQL(res: ServerResponse, rawBody: Buffer): void {
  let parsed: unknown;
  try {
    parsed = JSON.parse(rawBody.toString('utf8'));
  } catch {
    throw new HttpError(400, 'Problems parsing JSON');
  }
  const runOne = (entry: unknown): Record<string, unknown> => {
    if (typeof entry !== 'object' || entry === null) return { errors: [{ message: 'Invalid GraphQL request' }] };
    const request = entry as Record<string, unknown>;
    const query = typeof request.query === 'string' ? request.query : '';
    const variables = (typeof request.variables === 'object' && request.variables !== null ? request.variables : {}) as Record<string, unknown>;
    const operationName = typeof request.operationName === 'string' ? request.operationName : null;
    let doc: GqlDocument;
    try {
      doc = gqlParse(query);
    } catch (err) {
      return { errors: [{ message: err instanceof Error ? err.message : 'Parse error' }] };
    }
    const operation = operationName !== null ? doc.operations.find((op) => op.name === operationName) : doc.operations[0];
    if (operation === undefined) return { errors: [{ message: 'Operation not found' }] };
    const { data, errors } = executeOperation(doc, operation, variables);
    const out: Record<string, unknown> = { data };
    if (errors.length > 0) out.errors = errors;
    return out;
  };
  if (Array.isArray(parsed)) {
    sendJson(res, 200, parsed.map(runOne));
    return;
  }
  sendJson(res, 200, runOne(parsed));
}

// ------------------------------------------------------------------------------------------------
// MCP streamable HTTP

const MCP_REVISIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];
const MCP_SERVER_INFO = { name: 'github-core-clone', version: SERVER_VERSION };

interface McpToolDef {
  name: string;
  description: string;
  inputSchema: Record<string, unknown>;
}

function objectSchema(properties: Record<string, unknown>, required: string[]): Record<string, unknown> {
  return { type: 'object', properties, required };
}

const MCP_TOOLS: McpToolDef[] = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    inputSchema: objectSchema(
      {
        name: { type: 'string', description: 'The repository name.' },
        description: { type: 'string', description: 'A short description of the repository.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
        full_name: { type: 'string', description: 'The full name (owner/repo), when known.' },
      },
      ['name'],
    ),
  },
  {
    name: 'get_repo',
    description: 'Read one repository by owner and name.',
    inputSchema: objectSchema(
      {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        full_name: { type: 'string', description: 'The full name (owner/repo), when known.' },
      },
      ['owner', 'repo'],
    ),
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: objectSchema(
      {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
        full_name: { type: 'string', description: 'The full name (owner/repo), when known.' },
      },
      ['owner', 'repo', 'title'],
    ),
  },
  {
    name: 'list_issues',
    description: 'List the issues of a repository.',
    inputSchema: objectSchema(
      {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'Filter by state: open, closed or all.' },
        full_name: { type: 'string', description: 'The full name (owner/repo), when known.' },
      },
      ['owner', 'repo'],
    ),
  },
  {
    name: 'create_pull_request',
    description: 'Open a pull request from a head branch into a base branch.',
    inputSchema: objectSchema(
      {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        head: { type: 'string', description: 'The head branch name.' },
        base: { type: 'string', description: 'The base branch name.' },
        body: { type: 'string', description: 'The pull request body.' },
        full_name: { type: 'string', description: 'The full name (owner/repo), when known.' },
      },
      ['owner', 'repo', 'title', 'head', 'base'],
    ),
  },
  {
    name: 'merge_pull_request',
    description: 'Squash-merge a pull request into its base branch.',
    inputSchema: objectSchema(
      {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'number', description: 'The pull request number.' },
        full_name: { type: 'string', description: 'The full name (owner/repo), when known.' },
      },
      ['owner', 'repo', 'pull_number'],
    ),
  },
];

class RpcError extends Error {
  code: number;
  constructor(code: number, message: string) {
    super(message);
    this.code = code;
  }
}

function mcpResult(value: unknown): Record<string, unknown> {
  return { content: [{ type: 'text', text: JSON.stringify(value) }], structuredContent: value, isError: false };
}

function mcpToolFailure(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function mcpRepo(args: Record<string, unknown>): Repo {
  let owner = typeof args.owner === 'string' ? args.owner : null;
  let name = typeof args.repo === 'string' ? args.repo : null;
  if ((owner === null || name === null) && typeof args.full_name === 'string' && args.full_name.includes('/')) {
    const slash = args.full_name.indexOf('/');
    owner = args.full_name.slice(0, slash);
    name = args.full_name.slice(slash + 1);
  }
  if (owner === null || name === null) throw new RpcError(-32602, 'owner and repo are required');
  const repo = findRepo(owner, name);
  if (repo === null) throw new RpcError(-32602, `Repository ${owner}/${name} not found`);
  return repo;
}

function mcpRequire(args: Record<string, unknown>, names: string[]): void {
  for (const name of names) {
    if (args[name] === undefined || args[name] === null || args[name] === '') {
      throw new RpcError(-32602, `Missing required argument: ${name}`);
    }
  }
}

function callMcpTool(name: string, args: Record<string, unknown>): Record<string, unknown> {
  switch (name) {
    case 'create_repo': {
      mcpRequire(args, ['name']);
      const repoName = String(args.name);
      try {
        validateRepoName(repoName);
      } catch {
        return mcpToolFailure(`Invalid repository name: ${repoName}`);
      }
      if (findRepo(VIEWER.login, repoName) !== null) return mcpToolFailure(`Repository ${repoName} already exists`);
      const repo = createRepo(VIEWER.login, repoName, typeof args.description === 'string' ? args.description : '', args.private === true, 'main');
      return mcpResult(repoJson(repo));
    }
    case 'get_repo': {
      mcpRequire(args, ['owner', 'repo']);
      const repo = mcpRepo(args);
      return mcpResult(repoJson(repo));
    }
    case 'create_issue': {
      mcpRequire(args, ['owner', 'repo', 'title']);
      const repo = mcpRepo(args);
      const issue = createIssueRec(repo, String(args.title), typeof args.body === 'string' ? args.body : '', []);
      return mcpResult(issueJson(repo, issue));
    }
    case 'list_issues': {
      mcpRequire(args, ['owner', 'repo']);
      const repo = mcpRepo(args);
      const state = typeof args.state === 'string' ? args.state : 'open';
      const list = [...repo.issues.values()]
        .filter((issue) => state === 'all' || issue.state === state)
        .sort((a, b) => a.number - b.number);
      return mcpResult(list.map((issue) => issueJson(repo, issue)));
    }
    case 'create_pull_request': {
      mcpRequire(args, ['owner', 'repo', 'title', 'head', 'base']);
      const repo = mcpRepo(args);
      const head = String(args.head);
      const base = String(args.base);
      const headTip = branchTip(repo, head);
      const baseTip = branchTip(repo, base);
      if (headTip === null || baseTip === null) return mcpToolFailure('Head or base branch does not exist');
      if (head === base || headTip === baseTip) return mcpToolFailure('No commits between base and head');
      for (const existing of repo.pulls.values()) {
        if (existing.state === 'open' && existing.headRef === head && existing.baseRef === base) {
          return mcpToolFailure('A pull request already exists for this head and base');
        }
      }
      const pull = createPullRec(repo, String(args.title), typeof args.body === 'string' ? args.body : '', head, base);
      return mcpResult(pullJson(repo, pull));
    }
    case 'merge_pull_request': {
      mcpRequire(args, ['owner', 'repo', 'pull_number']);
      const repo = mcpRepo(args);
      const number = typeof args.pull_number === 'number' ? args.pull_number : Number(args.pull_number);
      const pull = repo.pulls.get(number);
      if (pull === undefined) return mcpToolFailure(`Pull request ${number} not found`);
      if (pull.merged || pull.state !== 'open') return mcpToolFailure('Pull request is not mergeable');
      const sha = mergePullRec(repo, pull);
      if (sha === null) return mcpToolFailure('Pull request is not mergeable');
      return mcpResult({ sha, merged: true, message: 'Pull Request successfully merged', pull_request: pullJson(repo, pull) });
    }
    default:
      throw new RpcError(-32602, `Unknown tool: ${name}`);
  }
}

function handleMcpMessage(message: unknown): Record<string, unknown> | null {
  if (typeof message !== 'object' || message === null || Array.isArray(message)) {
    return { jsonrpc: '2.0', id: null, error: { code: -32600, message: 'Invalid Request' } };
  }
  const request = message as Record<string, unknown>;
  const method = typeof request.method === 'string' ? request.method : '';
  const params = (typeof request.params === 'object' && request.params !== null ? request.params : {}) as Record<string, unknown>;
  const isNotification = request.id === undefined;
  const id = (request.id ?? null) as string | number | null;
  const respond = (result: unknown): Record<string, unknown> | null => (isNotification ? null : { jsonrpc: '2.0', id, result });
  const respondError = (code: number, text: string): Record<string, unknown> | null =>
    isNotification ? null : { jsonrpc: '2.0', id, error: { code, message: text } };

  switch (method) {
    case 'server/discover':
      return respond({
        supportedVersions: MCP_REVISIONS,
        capabilities: { tools: { listChanged: false } },
        serverInfo: MCP_SERVER_INFO,
        _meta: { 'io.modelcontextprotocol/serverInfo': MCP_SERVER_INFO, 'io.modelcontextprotocol/protocolVersion': '2026-07-28' },
      });
    case 'initialize': {
      const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '';
      const negotiated = MCP_REVISIONS.includes(requested) ? requested : '2025-03-26';
      return respond({ protocolVersion: negotiated, capabilities: { tools: { listChanged: false } }, serverInfo: MCP_SERVER_INFO });
    }
    case 'ping':
      return respond({});
    case 'tools/list':
      return respond({ tools: MCP_TOOLS });
    case 'tools/call': {
      const toolName = typeof params.name === 'string' ? params.name : '';
      const toolArgs = (typeof params.arguments === 'object' && params.arguments !== null ? params.arguments : {}) as Record<string, unknown>;
      try {
        return respond(callMcpTool(toolName, toolArgs));
      } catch (err) {
        if (err instanceof RpcError) return respondError(err.code, err.message);
        return respond(mcpToolFailure(err instanceof Error ? err.message : String(err)));
      }
    }
    case 'notifications/initialized':
    case 'notifications/cancelled':
      return null;
    default:
      if (method.startsWith('notifications/')) return null;
      return respondError(-32601, `Method not found: ${method}`);
  }
}

function handleMcp(req: IncomingMessage, res: ServerResponse, rawBody: Buffer): void {
  if (!hasAnyAuth(req) || !authorized(req)) {
    sendJson(res, 401, { message: 'Unauthorized' });
    return;
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(rawBody.toString('utf8'));
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (Array.isArray(parsed)) {
    const responses = parsed.map((entry) => handleMcpMessage(entry)).filter((entry) => entry !== null);
    if (responses.length === 0) {
      res.writeHead(202, { 'content-length': 0 });
      res.end();
      return;
    }
    sendJson(res, 200, responses);
    return;
  }
  const response = handleMcpMessage(parsed);
  if (response === null) {
    res.writeHead(202, { 'content-length': 0 });
    res.end();
    return;
  }
  sendJson(res, 200, response);
}

// ------------------------------------------------------------------------------------------------
// The router

export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void (async (): Promise<void> => {
      requestCounter += 1;
      res.setHeader('x-github-request-id', `ghcc-${requestCounter.toString(36)}-${(requestCounter * 7919).toString(36)}`);
      try {
        const url = new URL(req.url ?? '/', 'http://entry');
        let path = url.pathname;
        if (path.length > 1 && path.endsWith('/')) path = path.slice(0, -1);
        const segments = path.split('/').filter((segment) => segment !== '').map(decodeSegment);
        const method = req.method ?? 'GET';

        if (method === 'GET' && path === '/healthz') {
          sendJson(res, 200, { ok: true });
          return;
        }

        const rawBody = method === 'GET' || method === 'HEAD' ? Buffer.alloc(0) : await readBody(req);

        if (segments[0] === 'api' && segments[1] === 'v3') {
          await handleRest(req, res, url, segments.slice(2), rawBody);
          return;
        }
        if (path === '/api/graphql') {
          if (method !== 'POST') throw new HttpError(404, 'Not Found');
          if (!authorized(req)) throw new HttpError(401, hasAnyAuth(req) ? 'Bad credentials' : 'Requires authentication');
          handleGraphQL(res, rawBody);
          return;
        }
        if (path === '/mcp') {
          if (method !== 'POST') {
            sendJson(res, 405, { message: 'Method Not Allowed' });
            return;
          }
          handleMcp(req, res, rawBody);
          return;
        }
        if (segments.length >= 2 && segments[1].endsWith('.git')) {
          await handleGit(req, res, segments, url, rawBody);
          return;
        }
        sendJson(res, 404, { message: 'Not Found' });
      } catch (err) {
        if (res.headersSent) {
          res.end();
          return;
        }
        if (err instanceof HttpError) {
          sendJson(res, err.status, { message: err.message });
        } else {
          sendJson(res, 500, { message: 'Internal Server Error' });
        }
      }
    })();
  });
}
