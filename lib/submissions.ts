import "server-only";
import { pendingKv } from "@/lib/pendingprs";
import { readLedger } from "@/lib/ledger";
import type { Profile } from "@/lib/db";
import { REPO } from "@/lib/site";

/**
 * Where each submission of one contributor stands, from data the site already has (no GitHub call from here):
 *  - the merger's list of open pull requests (tools/merger_loop.sh publish_pending, every 15 minutes, KV PRS_KEY): who
 *    opened each one, whether its check is running, done and waiting for the verdict, or rejected (with the reason);
 *  - the credit ledger (lib/ledger.ts): every merged pull request, that is every accepted submission;
 *  - the desk's own events: "submit" (sent, before the pull request is listed), "rejected" and "fault".
 * The wait is an estimate: checks start roughly in the order the pull requests were opened, at the pace of the last
 * hour (verdicts the merger gave, `perHour`), or else about `running` at a time, each taking about CHECK_MINUTES.
 */
export const PRS_KEY = "pending:prs:v1";
const CHECK_MINUTES = 2;

export type PublishedPr = { pr: number; id: string; by: string; since: string; st?: string; reason?: string };
export type PrList = { at: string; queue: { running: number; queued: number | null; perHour?: number | null }; prs: PublishedPr[] };
export type SubmissionState = "sent" | "queued" | "checking" | "verdict" | "review" | "accepted" | "rejected" | "checked" | "fault";
export type Submission = {
  state: SubmissionState;
  id: string;
  pr: number | null;
  url: string | null;
  at: string;
  /** Reason of a rejection, when the merger recorded it. */
  reason?: string;
  /** Queued: checks ahead of it (estimate) and the expected wait in minutes. */
  ahead?: number;
  waitMin?: number;
};

let mem: { at: number; list: PrList | null } | null = null;

/** The merger's latest list (cached 30 s per isolate), or null when none was published in the last two hours. */
export async function getPrList(): Promise<PrList | null> {
  if (mem && Date.now() - mem.at < 30_000) return mem.list;
  let list: PrList | null = null;
  try {
    list = ((await pendingKv()?.get(PRS_KEY, { type: "json", cacheTtl: 60 })) as PrList | null) ?? null;
  } catch { /* KV unavailable: the ledger and the desk's events still answer */ }
  mem = { at: Date.now(), list };
  return list;
}

const prUrl = (n: number) => `https://github.com/${REPO}/pull/${n}`;
const prOf = (detail: string | null) => Number(/\/pull\/(\d+)/.exec(detail ?? "")?.[1]) || null;

/** Checks per minute: the last hour's pace when it is known, else `running` checks every CHECK_MINUTES. */
const pace = (list: PrList) => ((list.queue.perHour ?? 0) >= 6 ? list.queue.perHour! / 60 : Math.max(1, list.queue.running || 1) / CHECK_MINUTES);

/** How long a submission sent now waits for its check (minutes, estimate), and how many are waiting before it. */
export function waitNow(states: Map<number, Submission>, list: PrList): { waiting: number; minutes: number } {
  const waiting = [...states.values()].filter((s) => s.state === "queued").length;
  return { waiting, minutes: Math.max(CHECK_MINUTES, Math.round((waiting + 1) / pace(list))) };
}

/** The open pull requests of the list with their state; queued ones with their place in the queue. */
export function openStates(list: PrList): Map<number, Submission & { by: string }> {
  const out = new Map<number, Submission & { by: string }>();
  // Checks start in the order the pull requests were opened: the ones being checked mark the head of the queue (their
  // median: a re-run of an old pull request does not move it). An open pull request older than that with no state of
  // its own was checked earlier (its verdict is a comment). With no check running (the batch checker), the last 3 hours.
  const running = list.prs.filter((p) => p.st === "checking").map((p) => p.since).sort();
  const head = running.length ? running[Math.floor(running.length / 2)] : new Date(Date.parse(list.at) - 3 * 3600_000).toISOString();
  const waiting = list.prs.filter((p) => !p.st && p.since >= head).sort((a, b) => a.since.localeCompare(b.since) || a.pr - b.pr);
  const place = new Map(waiting.map((p, i) => [p.pr, i]));
  const rate = pace(list);
  for (const p of list.prs) {
    const base = { id: p.id, pr: p.pr, url: prUrl(p.pr), at: p.since, by: p.by };
    if (p.st === "rejected") out.set(p.pr, { ...base, state: "rejected", ...(p.reason ? { reason: p.reason } : {}) });
    else if (p.st === "checking" || p.st === "verdict" || p.st === "review") out.set(p.pr, { ...base, state: p.st });
    else if (place.has(p.pr)) {
      const ahead = place.get(p.pr)!;
      out.set(p.pr, { ...base, state: "queued", ahead, waitMin: Math.max(CHECK_MINUTES, Math.round((ahead + 1) / rate)) });
    } else out.set(p.pr, { ...base, state: "checked" });
  }
  return out;
}

/** Every recent submission of `handle`, newest first. */
export async function submissionsOf(handle: string, profile: Profile | null, limit = 40): Promise<{ list: PrList | null; items: Submission[]; now: { waiting: number; minutes: number } | null }> {
  const h = handle.toLowerCase();
  const [list, ledger] = await Promise.all([getPrList(), readLedger().catch(() => null)]);
  const items: Submission[] = [];
  const seenPr = new Set<number>();
  const seenId = new Set<string>();
  const add = (s: Submission) => {
    if (s.pr) { if (seenPr.has(s.pr)) return; seenPr.add(s.pr); }
    seenId.add(s.id);
    items.push(s);
  };
  const states = list ? openStates(list) : null;
  if (states) for (const s of states.values()) if (s.by.toLowerCase() === h) add(s);
  // Accepted: merged pull requests, from the ledger (the latest ones; older ones are on the profile's proof list).
  const merged = (ledger?.list ?? []).filter((e) => e.handle.toLowerCase() === h).sort((a, b) => b.merged_at.localeCompare(a.merged_at)).slice(0, limit);
  for (const e of merged) add({ state: "accepted", id: e.id, pr: e.pr, url: prUrl(e.pr), at: e.merged_at });
  // The desk's events: verdicts it recorded, and proofs sent whose pull request is not listed yet.
  const recent = Date.now() - 12 * 3600_000;
  for (const e of profile?.events ?? []) {
    if (e.kind === "rejected" || e.kind === "fault") {
      const pr = prOf(e.detail);
      add({ state: e.kind, id: e.problem_id, pr, url: pr ? prUrl(pr) : null, at: e.created_at });
    } else if (e.kind === "submit" && Date.parse(e.created_at) >= recent && !seenId.has(e.problem_id)) {
      add({ state: "sent", id: e.problem_id, pr: null, url: null, at: e.created_at });
    }
  }
  items.sort((a, b) => b.at.localeCompare(a.at));
  return { list, items: items.slice(0, limit), now: list && states ? waitNow(states, list) : null };
}

export const STATE_TEXT: Record<SubmissionState, string> = {
  sent: "Sent from the desk: no open pull request for it in the checker's latest list (refreshed every 15 minutes)",
  queued: "Queued: waiting for a GitHub runner to check it",
  checking: "Being checked by Lean now",
  verdict: "Checked: waiting for the merger to write its verdict (merge or rejection), oldest pull requests first",
  review: "Accepted by Lean, waiting to be merged (older submissions labelled needs-human-review are merged in batches)",
  accepted: "Accepted: merged and credited",
  rejected: "Rejected: push a fixed file to the same pull request, or move on",
  checked: "Checked: the verdict is in a comment on the pull request",
  fault: "Checker fault (our side): re-run automatically",
};
