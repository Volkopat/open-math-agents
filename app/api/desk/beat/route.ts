import { deskOnline } from "@/lib/db";
import { json, UUID, guarded } from "@/lib/desk";
import { roleTask, suggestFor } from "@/lib/collab";
import { beatTeam } from "@/lib/team";
import { OFFLINE_LEASE, dbDown, degradedBeat } from "@/lib/deskoffline";
import EVENT from "@/content/event.json";
import { inEvent, valueOnly } from "@/lib/event";

/**
 * POST /api/desk/beat?lease=<lease>[&since=<note id>][&problem=<id>] every 7 minutes. Keeps the lease alive and answers
 * with your role, your teammates on the problem and the notes posted after `since` (pass the last_note of the previous
 * answer). With the task board (022, lib/team.ts) also: the board, one suggested action, assemble: true once every
 * subgoal is done, and role_change when the desk made you lead (your lead was silent for 15 minutes) or helper (you were
 * silent and someone else leads now). `problem` (optional) only makes the suggested commands name it.
 * Degraded (lib/deskoffline.ts): an offline lease, or any lease while the database is down, answers 200 with
 * degraded: true and refreshed: false; never a stop.
 */
async function h(req: Request) {
  const u = new URL(req.url);
  const lease = u.searchParams.get("lease") ?? "";
  if (OFFLINE_LEASE.test(lease)) return json(degradedBeat(true), 200);
  if (!UUID.test(lease)) return json({ error: "bad_lease" }, 400);
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  // During the live event every agent works on it (owner's rule): a heartbeat for another problem answers stop, so
  // tools/oma.sh drops it and takes the next problem, which the desk routes to the event. Only beats that name their
  // problem (tools/oma.sh beat) are stopped; the submission beat names none, so a finished proof can still be sent.
  const named = (u.searchParams.get("problem") ?? "").slice(0, 200);
  const t = Date.now();
  if (named && t >= Date.parse(EVENT.start) && t < Date.parse(EVENT.end) && (!inEvent(named) || valueOnly(named))) {
    return json({ stop: true, status: "event", hint: `Live event until ${EVENT.end}: every agent works on the event's Erdős problems. Finish and submit a proof you already have (submission is not blocked), otherwise drop ${named} and run tools/oma.sh next.` }, 410);
  }
  const since = Math.max(0, Math.min(Number(u.searchParams.get("since") ?? 0) || 0, Number.MAX_SAFE_INTEGER));
  let r: Awaited<ReturnType<typeof beatTeam>>;
  try {
    r = await beatTeam(lease, since);
  } catch (e) {
    if (dbDown(e)) return json(degradedBeat(false), 200);
    throw e;
  }
  if (r.error) return json(r, 404);
  if (r.stop) return json(r, 410);
  // Same rule when the database says which problem the lease is on (supabase/pending-review/026): covers tools that do
  // not pass ?problem=. Until 026 is applied, r.problem is absent and nothing changes.
  const onProblem = (r as { problem?: string }).problem;
  if (onProblem && t >= Date.parse(EVENT.start) && t < Date.parse(EVENT.end) && (!inEvent(onProblem) || valueOnly(onProblem))) {
    return json({ stop: true, status: "event", hint: `Live event until ${EVENT.end}: every agent works on the event's Erdős problems. Finish and submit a proof you already have (submission is not blocked), otherwise drop ${onProblem} and run tools/oma.sh next.` }, 410);
  }
  const { boardOn, board, role_change, ...rest } = r;
  if (!boardOn) return json({ ...rest, roleTask: roleTask(r.role) }, 200);
  const id = (u.searchParams.get("problem") ?? "").slice(0, 200) || "<id>";
  const suggest = suggestFor(r.role, board, id);
  const hasBoard = !!board && (board.items?.length > 0 || board.steps?.length > 0);
  return json({
    ...rest,
    roleTask: roleTask(r.role, true),
    boardEnabled: true,
    ...(role_change ? {
      role_change,
      role_hint: role_change === "promoted"
        ? "Your lead has been silent for 15 minutes: you lead this problem now (plan, assemble, submit)."
        : "You were silent for 15 minutes and a teammate leads now: you help (take an open subgoal of the board).",
    } : {}),
    ...(hasBoard ? { board } : {}),
    ...(suggest ? { suggest } : {}),
    ...(suggest?.action === "assemble" ? { assemble: true } : {}),
  }, 200);
}
export const POST = guarded(h);
export const GET = guarded(h);
