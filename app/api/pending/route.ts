import { verifyWorkflowToken } from "@/lib/ghoidc";
import { json } from "@/lib/desk";
import { pendingKv, PENDING_KEY } from "@/lib/pendingprs";
import { PRS_KEY, submissionsOf, STATE_TEXT, type PublishedPr } from "@/lib/submissions";
import { getProfile } from "@/lib/db";
import { HANDLE_RE } from "@/lib/params";
import { NextResponse } from "next/server";

const ID_RE = /^[A-Za-z0-9_.'-]{1,200}$/;
const STATES = new Set(["checking", "verdict", "rejected", "review"]);

/**
 * The merger (backlog.yml, trusted: it never runs pull request code) posts the open pull requests here every 15 minutes:
 * { oidc, items: [{ id: problem id (the pull request title), pr, since }], prs?, queue? }. The desk then stops handing
 * those problems out (lib/pendingprs.ts). `prs` lists every open pull request with its author and the state the merger
 * knows (check running, waiting for its verdict, rejected with the reason, labelled for review), and `queue` the checks
 * running and waiting in GitHub's queue: the submission status of each contributor (lib/submissions.ts).
 * Only a request proved by the workflow's GitHub OIDC token is accepted.
 */
export async function POST(req: Request) {
  const b = (await req.json().catch(() => null)) as { oidc?: string; items?: unknown[]; prs?: unknown[]; queue?: { running?: unknown; queued?: unknown; perHour?: unknown } } | null;
  if (!b || !Array.isArray(b.items) || typeof b.oidc !== "string") return json({ error: "bad_request" }, 400);
  if (!(await verifyWorkflowToken(b.oidc))) return json({ error: "unauthorized" }, 401);
  const items = b.items
    .map((x) => x as { id?: unknown; pr?: unknown; since?: unknown })
    .filter((x) => typeof x.id === "string" && ID_RE.test(x.id) && Number.isInteger(x.pr))
    .slice(0, 20000)
    .map((x) => ({ id: x.id as string, pr: x.pr as number, since: typeof x.since === "string" ? x.since.slice(0, 25) : "" }));
  const kv = pendingKv();
  if (!kv) return json({ error: "kv_unavailable" }, 503);
  const at = new Date().toISOString();
  // kept two hours: if the merger stops posting, the list fades out instead of blocking problems forever
  await kv.put(PENDING_KEY, JSON.stringify({ at, items }), { expirationTtl: 7200 });
  let prs = 0;
  if (Array.isArray(b.prs)) {
    const list: PublishedPr[] = b.prs
      .map((x) => x as { pr?: unknown; id?: unknown; by?: unknown; since?: unknown; st?: unknown; reason?: unknown })
      .filter((x) => Number.isInteger(x.pr) && typeof x.id === "string" && ID_RE.test(x.id) && typeof x.by === "string" && HANDLE_RE.test(x.by.replace(/\[bot\]$/, "")))
      .slice(0, 20000)
      .map((x) => ({
        pr: x.pr as number, id: x.id as string, by: x.by as string, since: typeof x.since === "string" ? x.since.slice(0, 25) : "",
        ...(typeof x.st === "string" && STATES.has(x.st) ? { st: x.st } : {}),
        ...(typeof x.reason === "string" && x.reason ? { reason: x.reason.replace(/\s+/g, " ").slice(0, 300) } : {}),
      }));
    const n = (v: unknown) => (Number.isInteger(v) && (v as number) >= 0 ? (v as number) : null);
    const queue = { running: n(b.queue?.running) ?? 0, queued: n(b.queue?.queued), perHour: n(b.queue?.perHour) };
    await kv.put(PRS_KEY, JSON.stringify({ at, queue, prs: list }), { expirationTtl: 7200 });
    prs = list.length;
  }
  return json({ ok: true, items: items.length, prs });
}

/** GET ?handle=<GitHub handle>: where each recent submission of that person stands (also on /a/<handle>). */
export async function GET(req: Request) {
  const handle = new URL(req.url).searchParams.get("handle") ?? "";
  if (!HANDLE_RE.test(handle)) return json({ error: "bad_request", hint: "GET /api/pending?handle=<your GitHub handle>" }, 400);
  const { list, items, now } = await submissionsOf(handle, await getProfile(handle));
  return NextResponse.json(
    {
      handle,
      asOf: list?.at ?? null,
      queue: list ? { ...list.queue, note: "Checks start roughly in the order the pull requests were opened; waits are estimates at the pace of the last hour (perHour verdicts)." } : null,
      sentNow: now ? { waitingBefore: now.waiting, expectedMinutes: now.minutes } : null,
      submissions: items.map((s) => ({ ...s, meaning: STATE_TEXT[s.state] })),
    },
    { headers: { "Cache-Control": "public, s-maxage=60", "Access-Control-Allow-Origin": "*" } },
  );
}
