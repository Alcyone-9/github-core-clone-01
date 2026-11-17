// main.ts — the wire between this entry and the trial env.
//
// The env is a small HTTP server whose origin arrives in MAKEFUN_ENV_URL.
// My whole job here is mechanical:
//   1. start the forge from app.ts on an ephemeral port,
//   2. tell the env which port I landed on (POST /register, first one wins),
//   3. poll GET /done until the env says the trial is over,
//   4. close the server and exit 0.
// If MAKEFUN_ENV_URL is missing there is no env and nothing to do: exit 1.

import { createApp } from './app.ts';

const envOrigin = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');
if (envOrigin === '') {
  process.stderr.write('[main] MAKEFUN_ENV_URL is unset; exiting\n');
  process.exit(1);
}

const REQUEST_DEADLINE_MS = 30_000;
const FIRST_BACKOFF_MS = 250;
const LONGEST_BACKOFF_MS = 2_000;

function pause(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// Wait between retries: 250 ms, doubling, never longer than two seconds.
function backoffFor(failures: number): number {
  return Math.min(LONGEST_BACKOFF_MS, FIRST_BACKOFF_MS * 2 ** Math.min(failures, 8));
}

// POST /register until the env takes the port. A 409 only means an earlier
// register already won the slot, which is the env's business, not an error
// here. A 400 or 405 is a contract violation and is fatal. Anything else —
// the env still booting, a dropped connection — is worth another try.
async function announcePort(port: number): Promise<void> {
  for (let failures = 0; ; failures += 1) {
    let fatal: Error | null = null;
    try {
      const answer = await fetch(`${envOrigin}/register`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port }),
        signal: AbortSignal.timeout(REQUEST_DEADLINE_MS),
      });
      if (answer.status === 200 || answer.status === 409) return;
      if (answer.status === 400 || answer.status === 405) {
        fatal = new Error(`register refused with HTTP ${answer.status}: ${await answer.text()}`);
      }
    } catch {
      // Network trouble or a timeout: fall through and retry.
    }
    if (fatal !== null) throw fatal;
    await pause(backoffFor(failures));
  }
}

// GET /done answers immediately with {"done": false} while the suite runs,
// so this is a plain poll. It only returns once the body says done is true.
async function awaitDone(): Promise<void> {
  for (let failures = 0; ; failures += 1) {
    try {
      const answer = await fetch(`${envOrigin}/done`, {
        signal: AbortSignal.timeout(REQUEST_DEADLINE_MS),
      });
      if (answer.ok) {
        const body = (await answer.json()) as { done?: unknown };
        if (body.done === true) return;
      }
    } catch {
      // A failed poll just means "not done yet".
    }
    await pause(backoffFor(failures));
  }
}

async function run(): Promise<void> {
  const server = createApp();
  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, () => resolve());
  });
  const bound = server.address();
  if (bound === null || typeof bound === 'string') {
    throw new Error('server did not bind a TCP port');
  }
  process.stdout.write(`[main] forge listening on port ${bound.port}\n`);
  await announcePort(bound.port);
  process.stdout.write('[main] registered with the env; waiting for done\n');
  await awaitDone();
  server.close();
  process.stdout.write('[main] env said done; exiting\n');
}

try {
  await run();
  process.exit(0);
} catch (err) {
  process.stderr.write(`[main] ${err instanceof Error ? err.message : String(err)}\n`);
  process.exit(1);
}
