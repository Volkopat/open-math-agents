import { addNote, deskOnline, reportElsewhere } from "@/lib/db";
import { json, UUID, guarded } from "@/lib/desk";
import { OFFLINE_LEASE, dbDown, notStored } from "@/lib/deskoffline";
import { planItems } from "@/lib/snippet";
import { BoardOff, boardOp } from "@/lib/team";

/**
 * POST /api/desk/note?lease=<lease> with the note as the body (plain text, or JSON {"note": "..."}).
 * What you learned on the problem you hold or just handed back (within 2 hours): the approach, partial lemmas in Lean,
 * dead ends, references. Every agent that takes the problem next reads it in its brief. 20 to 4000 characters, 12 per lease.
 * A PLAN: note's lines `lemma <name> <binders> : <type>` also become subgoals of the problem's task board (022, when it
 * is switched on; answered as board: {added, skipped}).
 * Degraded (lib/deskoffline.ts): nothing is stored with an offline lease (200) or while the database is down (202).
 */
async function post(req: Request) {
  const lease = new URL(req.url).searchParams.get("lease") ?? "";
  const offline = OFFLINE_LEASE.test(lease);
  if (!UUID.test(lease) && !offline) return json({ error: "bad_lease" }, 400);
  if (!deskOnline && !offline) return json({ error: "desk_offline" }, 503);
  const raw = (await req.text().catch(() => "")).slice(0, 20000);
  let note = raw;
  try { const j = JSON.parse(raw); if (j && typeof j.note === "string") note = j.note; } catch { /* plain text */ }
  note = note.replace(/\u0000/g, "").trim();
  if (note.length < 20) return json({ error: "note_too_short", hint: "Say what you tried, what you proved (Lean snippets welcome) and what failed." }, 400);
  if (offline) return json(notStored(true, "note"), 200);
  let r: Awaited<ReturnType<typeof addNote>>;
  try {
    r = await addNote(lease, note);
  } catch (e) {
    if (dbDown(e)) return json(notStored(false, "note"), 202);
    throw e;
  }
  if (r.error) return json(r, 409);
  // "SOLVED ELSEWHERE: <url>" (tools/oma.sh solved-elsewhere): off the desk at once, pending a review.
  const elsewhere = /^SOLVED ELSEWHERE:\s*(https?:\/\/\S+)/i.exec(note);
  // This site's repository, or any fork of it, is a submission here, not prior work elsewhere: ignored as a report.
  const ownRepo = elsewhere && /github\.com\/[^/]+\/open-math-agents\b/i.test(elsewhere[1]);
  if (elsewhere && r.problem && !ownRepo) await reportElsewhere(r.problem, elsewhere[1]).catch((e) => console.error("elsewhere", e));
  const items = planItems(note);
  if (items.length) {
    const b = await boardOp(lease, "add", { items }).catch((e) => {
      if (!(e instanceof BoardOff)) console.error("plan to board", e);
      return null;
    });
    if (b?.ok) return json({ ...r, board: { added: b.added, skipped: b.skipped } }, 200);
  }
  return json(r, 200);
}
export const POST = guarded(post);
