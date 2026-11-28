import { timingSafeEqual } from "node:crypto";
import { NextResponse } from "next/server";
import { verifyWorkflowToken } from "@/lib/ghoidc";
import { json } from "@/lib/desk";
import { normalizeEntry, readLedger, upsertLedger, type LedgerEntry } from "@/lib/ledger";

/**
 * The credit ledger (lib/ledger.ts): one entry per pull request merged into main that added one file under proofs/,
 * reductions/ or statements/ (or made a proof shorter). The merger (backlog.yml, trusted: it never runs pull request
 * code) appends an entry at each merge and posts them here every few minutes, { oidc, entries: [...] }, proved by its
 * GitHub OIDC token (or a maintainer, with x-oma-secret). Entries are upserted by pull request: posting the same ones
 * again changes nothing. The leaderboard and every credit page read the ledger next to the database.
 * GET: the ledger's size, or one entry (?pr=N).
 */
const MAX_ENTRIES = 2000;
const MAX_BYTES = 2_000_000;

function maintainer(req: Request) {
  const secret = process.env.OMA_VERDICT_SECRET ?? "";
  const got = req.headers.get("x-oma-secret") ?? "";
  return Boolean(secret && got && got.length === secret.length && timingSafeEqual(Buffer.from(got), Buffer.from(secret)));
}

export async function POST(req: Request) {
  const text = await req.text().catch(() => "");
  if (text.length > MAX_BYTES) return json({ error: "too_large", max_bytes: MAX_BYTES }, 413);
  let b: { oidc?: unknown; entries?: unknown } | null = null;
  try {
    b = JSON.parse(text);
  } catch {
    b = null;
  }
  if (!b || !Array.isArray(b.entries)) return json({ error: "bad_request", hint: "body {\"oidc\": <token>, \"entries\": [...]}" }, 400);
  if (!maintainer(req) && !(await verifyWorkflowToken(b.oidc))) return json({ error: "unauthorized" }, 401);
  if (b.entries.length > MAX_ENTRIES) return json({ error: "too_many_entries", max: MAX_ENTRIES }, 413);
  const valid: LedgerEntry[] = [];
  let rejected = 0;
  for (const x of b.entries) {
    const e = normalizeEntry(x);
    if (e) valid.push(e);
    else rejected++;
  }
  try {
    const r = valid.length ? await upsertLedger(valid) : { changed: 0, total: (await readLedger()).list.length };
    return json({ ok: true, accepted: valid.length, rejected, ...r });
  } catch (e) {
    console.error("api/ledger", e);
    return NextResponse.json({ error: "ledger_unavailable", hint: "Retry later; nothing was lost on your side." }, { status: 503, headers: { "Retry-After": "120", "Cache-Control": "no-store" } });
  }
}

export async function GET(req: Request) {
  const led = await readLedger();
  const pr = Number(new URL(req.url).searchParams.get("pr"));
  const headers = { "Cache-Control": "public, max-age=30", "Access-Control-Allow-Origin": "*" };
  if (Number.isInteger(pr) && pr > 0) {
    const entry = led.list.find((e) => e.pr === pr) ?? null;
    return NextResponse.json({ pr, entry }, { status: entry ? 200 : 404, headers });
  }
  const latest = led.list.reduce((a, e) => (e.merged_at > a ? e.merged_at : a), "");
  const kinds: Record<string, number> = {};
  for (const e of led.list) kinds[e.kind] = (kinds[e.kind] ?? 0) + 1;
  return NextResponse.json({ count: led.list.length, kinds, latest_merge: latest || null, live_updated: led.meta?.at ?? null }, { headers });
}
