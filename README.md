# github-core-clone-01 — a GitHub-compatible git forge

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/Alcyone-9/github-core-clone-01/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/Alcyone-9/github-core-clone-01/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

Built for the [make.fun "Build a GitHub-compatible git forge" bounty](https://make.fun/bounty/github-core-clone-01).

A complete GitHub-compatible forge in a single dependency-free TypeScript file
(`app.ts`), built for the make.fun `github-core-clone-01` bounty. It speaks the
four surfaces GitHub's own tooling speaks, all over one in-memory store:

- **Git smart HTTP** — protocol v2 (`ls-refs`, `fetch` with shallow/deepen and
  incremental haves) and v0 advertisements, plus v0 `git-receive-pack` with
  report-status in sideband frames, fast-forward enforcement and per-ref
  ok/ng reports. The object store, packfile reader/writer (including ofs/ref
  delta resolution) and pkt-line framing are implemented from scratch on
  `node:crypto` SHA-1 and `node:zlib`.
- **REST v3** — repositories (create/read/patch/delete, Link-header
  pagination), branches, commits, git refs, the contents API (create, update
  with stale-sha 409, delete, directory listings), labels, issues with
  comments, and pull requests with file diffs and squash merges (405 on
  conflict). Bearer-token auth: no token or a wrong token is a 401, another
  owner's name is a 404, every reply is JSON with an `X-GitHub-Request-Id`.
- **GraphQL v4** — a hand-written lexer/parser/executor and a schema table
  that also drives introspection (`__type`, `__schema`). Queries and
  mutations for viewer, repositories, issues, pull requests and comments,
  Relay global ids with `node(id:)` round-trips, cursor connections, and
  JSON-array operation batching. Everything written through GraphQL is the
  same object over REST and git, and vice versa.
- **MCP (streamable HTTP)** — `server/discover` (2026-07-28) plus the legacy
  `initialize` handshake, `tools/list` and `tools/call` for `create_repo`,
  `get_repo`, `create_issue`, `list_issues`, `create_pull_request` and
  `merge_pull_request`, acting on the same store as REST.

Issues and pull requests share one per-repository number counter, exactly
like GitHub. A squash merge is a three-way merge over flattened trees:
both-sides-changed paths conflict (405 / `CONFLICTING`), everything else
lands as a single-parent commit on the base branch.

## Determinism

The trial is replayed and the state export compared byte for byte, so the
server never reads the wall clock or a random source. Timestamps come from a
logical clock anchored at 2025-01-01T00:00:00Z that advances one second per
state-changing step; ids are plain counters.

## Running

```sh
node main.ts   # with MAKEFUN_ENV_URL set; see main.ts for the lifecycle
```

`main.ts` is the harness lifecycle (bind an ephemeral port, register, wait
for done) and stays as the kit shipped it; `app.ts` is the forge itself.
Node 22.18+ type stripping runs both files directly — no build step, no
dependencies, no network, no git binary.

## Layout

- `main.ts` — entry ↔ env lifecycle (unchanged from the kit).
- `app.ts` — the whole forge: store, git object/pack layer, smart HTTP,
  REST v3, GraphQL, MCP.
- `package.json`, `tsconfig.json` — project metadata.
- `LICENSE` — MIT.
