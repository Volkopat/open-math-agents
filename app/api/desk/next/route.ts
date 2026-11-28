import { PROBLEMS, getProblem, getFull, skeleton, proofPath, statementSkeleton, type Problem } from "@/lib/catalog";
import CLEARED from "@/data/elsewhere_cleared.json";
import { deskDown, deskOnline, getElsewhereReports, getLiveMap, getStats, getSteps, hashIp, type Step } from "@/lib/db";
import { claimTeam, deadEnds } from "@/lib/team";
import { json, clientIp, guarded } from "@/lib/desk";
import { pointsFor } from "@/lib/points";
import { STEP_RE, stepSkeleton } from "@/lib/steps";
import { SITE, REPO } from "@/lib/site";
import { teamFields, type TeamNote } from "@/lib/collab";
import EVENT from "@/content/event.json";
import { guideFor, inEvent, isEventStep, valueOnly } from "@/lib/event";
import IMPACT from "@/content/impact.json";
import { getPending, pendingError } from "@/lib/pendingprs";
import { countHandout, dbDown, DEGRADED_NEXT, offlineLease, offlineScores } from "@/lib/deskoffline";

const IMPACT_IDS = IMPACT.groups.flatMap((g) => g.items.map((i) => i.id));
/** True while the live event runs (content/event.json): agents that ask for nothing specific work on its problems. */
const eventOn = (t = Date.now()) => t >= Date.parse(EVENT.start) && t < Date.parse(EVENT.end);

const LEVELS: Record<string, [number, number]> = { warmup: [0, 20], solid: [20, 55], hard: [55, 85], legendary: [85, 101] };
/** With this many live agents on a problem, a newcomer who asks for it by name is sent to one of its open steps instead
 * (proving every step closes it), unless they pass exact=1. */
const CROWDED = 6;

/** Least crowded first, random among ties, so agents spread out. */
function pick<T extends { id: string }>(cands: T[], live: Map<string, number>) {
  if (cands.length === 0) return null;
  const min = Math.min(...cands.map((p) => live.get(p.id) ?? 0));
  const pool = cands.filter((p) => (live.get(p.id) ?? 0) === min);
  return pool[Math.floor(Math.random() * pool.length)];
}

async function handle(req: Request) {
  const u = new URL(req.url);
  let body: Record<string, string> = {};
  if (req.method === "POST") {
    // a JSON null, array or number is no options object (null used to throw on body[k])
    const b: unknown = await req.json().catch(() => null);
    if (b && typeof b === "object" && !Array.isArray(b)) body = b as Record<string, string>;
  }
  const get = (k: string) => (body[k] ?? u.searchParams.get(k) ?? "").toString().trim();

  const handleName = get("handle");
  if (!/^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/.test(handleName)) {
    return json({ error: "bad_handle", hint: "Pass handle=<your owner's GitHub login>." }, 400);
  }
  if (!deskOnline) return json({ error: "desk_offline", hint: "Coordination is not configured yet; the catalogue is still at /api/problems." }, 503);

  const [live, stats, pending] = await Promise.all([getLiveMap(), getStats(), getPending()]);
  const solved = new Set(stats.solved.map((s) => s.problem_id));
  // Database down (breaker open): the recent offline handouts count as crowding too, so agents still spread out
  // (lib/deskoffline.ts). Up: the live map alone, as always.
  const crowd = deskDown() ? await offlineScores(live) : live;
  // a problem with a proof waiting for its verdict is not handed out (lib/pending.ts); asking for it by name answers
  // proof_pending unless force=1
  const force = get("force") === "1";
  // Reported solved elsewhere by an agent (a "SOLVED ELSEWHERE: <url>" note): not handed out until reviewed.
  const reported = await getElsewhereReports();
  const elsewhere: typeof reported = Object.fromEntries(Object.entries(reported).filter(([id]) => !(id in CLEARED.entries)));
  const free = (id: string) => !solved.has(id) && !pending.has(id) && !elsewhere[id];
  // One clock reading per request: routing and the exemptions below must agree at the event's start and end.
  const eventLive = eventOn();
  // During the live event its problems are never refused for a waiting pull request or a solved-elsewhere report
  // (see below); a step with a waiting pull request stays blocked (duplicates clog the merger).
  const eventExempt = (id: string) => eventLive && inEvent(id);
  const pendingBlocks = (id: string) => pending.has(id) && !eventExempt(id);
  let wanted = get("problem");
  let kind = get("kind") || "known";
  // kind=impact: the problems most useful beyond mathematics (content/impact.json). During the live event, agents that
  // ask for nothing specific (no problem, default or broad kind) are sent to the event's problems and their open steps;
  // event=0 opts out.
  let event: { title: string; end: string; models?: string; redirected?: string } | null = null;
  // Owner's rule for the event (28 Nov 2026): every agent works on the event only. A problem asked for by name that is
  // not part of the event, any kind, and event=0 are overridden while it runs; the answer says so (redirected).
  const routeEvent = eventLive;
  let redirected: string | null = null;
  if (routeEvent && wanted && (!inEvent(wanted) || valueOnly(wanted))) { redirected = wanted; wanted = ""; }
  if (routeEvent) kind = "known";
  // An event problem asked for by name gets the event note too.
  if (routeEvent && wanted) event = { title: EVENT.title, end: EVENT.end, models: EVENT.models?.note };
  if (!wanted && (kind === "impact" || routeEvent)) {
    // During the event its problems stay open to everyone even when a pull request is waiting on them: a submitted
    // attempt at a famous problem is usually partial or wrong, and must not send the whole event elsewhere.
    // Event: a step with a waiting pull request stays on offer (excluding them left only the two value problems, where
    // nothing can be accepted, and agents left the site); a step reported solved elsewhere does not.
    const freeHere = (id: string) => (kind === "impact" ? free(id) : !solved.has(id) && (EVENT.problems.includes(id) || !elsewhere[id]));
    const openOnly = (id: string) => freeHere(id) && ["open", "unformalized"].includes(getProblem(id)?.kind ?? "");
    let cands = (kind === "impact" ? IMPACT_IDS : EVENT.problems.filter((id) => !valueOnly(id))).filter(openOnly);
    if (kind !== "impact") {
      const st = (await getSteps(undefined, true)).filter((s) => !s.solved && freeHere(s.id) && isEventStep(s.id));
      // Open steps first: work there can be accepted and earns points. The event problems themselves (value problems:
      // a formula goes to a person) only when no step is open.
      if (st.length) cands = st.map((s) => s.id);
      event = { title: EVENT.title, end: EVENT.end, models: EVENT.models?.note, ...(redirected ? { redirected: `${redirected} is not handed out during the event: every agent works on its Erdős problems until ${EVENT.end}.` } : {}) };
    }
    const choice = pick(cands.map((id) => ({ id })), crowd);
    if (choice) wanted = choice.id;
    else if (routeEvent) return json({ error: "event_nothing_open", hint: `Every problem of the event is solved or taken; the event runs until ${EVENT.end}.`, event: { title: EVENT.title, end: EVENT.end, ...(redirected ? { redirected: `${redirected} is not handed out during the event.` } : {}) } }, 404);
    else if (kind === "impact") return json({ error: "nothing_matches", hint: "Every problem of the impact list is solved or taken; try --kind open." }, 404);
    if (kind === "impact") kind = "any";
  }
  const agent = get("agent") || "unknown";
  // A lease from the database; if it cannot answer, an offline lease for the same problem (lib/deskoffline.ts), but
  // only when the solved list is known (cached stats): without it the desk answers 503 as before.
  const take = async (id: string, points: number): Promise<Awaited<ReturnType<typeof claimTeam>> & { degraded?: true; deadEnds?: TeamNote[] }> => {
    try {
      const r = await claimTeam(id, handleName, agent, hashIp(clientIp(req)), points);
      // Dead ends of every team that worked on it before (plain notes, cached): shown to every newcomer.
      return r.lease ? { ...r, deadEnds: await deadEnds(id) } : r;
    } catch (e) {
      if (!dbDown(e) || solved.size === 0) throw e;
      await countHandout(id);
      return { lease: offlineLease(), degraded: true, boardOn: false };
    }
  };

  // A crowded problem asked for by name: its open steps need hands more than its main attack does.
  let steered: { from: string; agents: number; hint: string } | null = null;
  if (wanted && !STEP_RE.test(wanted) && get("exact") !== "1" && (crowd.get(wanted) ?? 0) >= CROWDED) {
    const open = (await getSteps(undefined, true)).filter((s) => s.parent === wanted && !s.solved && free(s.id));
    const st = pick(open, crowd);
    if (st && (crowd.get(st.id) ?? 0) < (crowd.get(wanted) ?? 0)) {
      const n = crowd.get(wanted) ?? 0;
      steered = {
        from: wanted, agents: n,
        hint: `${n} agents already work on ${wanted}; its step ${st.id} has ${crowd.get(st.id) ?? 0}. Proving every step of the ` +
          `reduction closes ${wanted}, so this is the same attack. To join the main attack instead: tools/oma.sh next --problem ${wanted} --exact (exact=1).`,
      };
      wanted = st.id;
    }
  }

  // Steps (hypotheses of accepted reductions) live in the database, not in the static catalogue.
  if (kind === "step" || STEP_RE.test(wanted)) {
    if (wanted && !force && pendingBlocks(wanted)) return json(pendingError(wanted, pending.get(wanted)!, REPO), 409);
    if (wanted && !force && elsewhere[wanted]) return json({ error: "reported_solved_elsewhere", url: elsewhere[wanted].url, hint: "An agent found this already settled in the literature; it is off the desk until reviewed. Pick another problem." }, 409);
    const steps = (await getSteps(undefined, true)).filter((s) => !s.solved && !solved.has(s.id) && (s.id === wanted || !pendingBlocks(s.id)));
    const picked: Step | null | undefined = wanted ? steps.find((x) => x.id === wanted) : pick(steps, crowd);
    // The full list carries no statements (size): read the chosen step's own record.
    const s: Step | null | undefined = picked ? ((await getSteps(picked.id, true)).find((x) => x.id === picked.id) ?? picked) : picked;
    if (!s) return json({ error: wanted ? "not_found_or_solved" : "nothing_matches", hint: "No open step right now. Try --kind known." }, 404);
    const r = await take(s.id, s.points);
    if (r.error) return json(r, r.error === "rate_limited" ? 429 : 409);
    const parent = getProblem(s.parent);
    return json({
      lease: r.lease,
      points: s.points,
      problem: {
        id: s.id, kind: "step", title: `Step H${s.k} of ${parent?.title ?? s.parent}`, parent: s.parent, reduction: s.reduction,
        statement: `Hypothesis H${s.k} of reduction ${s.reduction} (${s.reduction_pr}). Proving every hypothesis closes ${s.parent}.`,
        lean: `def H${s.k} : Prop := ${s.statement}`, module: s.module, page: `${SITE}/p/${encodeURIComponent(s.id)}`,
      },
      othersWorking: crowd.get(s.id) ?? 0,
      file: `proofs/${s.id}.lean`,
      skeleton: stepSkeleton(s, handleName),
      next: nextHints(r.lease!, `proofs/${s.id}.lean`, s.id),
      ...teamFields(r, { boardOn: r.boardOn, id: s.id, handle: handleName, deadEnds: r.deadEnds }),
      ...(steered ? { steered } : {}),
      ...(event ? { event } : {}),
      ...(eventLive && guideFor(s.id) ? { guide: guideFor(s.id) } : {}),
      ...(r.degraded ? DEGRADED_NEXT : {}),
    });
  }

  // Problems with no Lean statement yet: the task is to state them, not to prove them.
  const formalize = kind === "formalize" || kind === "unformalized" || (wanted && getProblem(wanted)?.kind === "unformalized");
  if (formalize) {
    if (wanted && !force && pending.has(wanted)) return json(pendingError(wanted, pending.get(wanted)!, REPO), 409);
    const cands = PROBLEMS.filter((x) => x.kind === "unformalized" && !x.claim && !pending.has(x.id) && !elsewhere[x.id] && (!get("source") || x.source === get("source")) && (!get("field") || x.fields.includes(get("field"))));
    // most famous first: among the least crowded, take from the 25 best known still waiting
    const minLive = Math.min(...cands.map((x) => crowd.get(x.id) ?? 0));
    const top = cands.filter((x) => (crowd.get(x.id) ?? 0) === minLive).sort((a, b) => b.fame - a.fame).slice(0, 25);
    const pick0 = wanted ? getProblem(wanted) : top[Math.floor(Math.random() * top.length)];
    const fp = pick0 ? await getFull(pick0.id) : undefined;
    if (!fp || fp.kind !== "unformalized") return json({ error: wanted ? "not_found_or_already_formalized" : "nothing_matches" }, 404);
    const r = await take(fp.id, 0);
    if (r.error) return json(r, r.error === "rate_limited" ? 429 : 409);
    return json({
      lease: r.lease,
      task: "formalize",
      points: 0,
      problem: {
        id: fp.id, title: fp.title, kind: fp.kind, source: fp.source, fields: fp.fields, ref: fp.ref,
        statement: fp.statement || "(read the statement at the source link)", license: fp.license, page: `${SITE}/p/${encodeURIComponent(fp.id)}`,
      },
      othersWorking: crowd.get(fp.id) ?? 0,
      file: `statements/${fp.id}.lean`,
      skeleton: statementSkeleton(fp, handleName),
      instructions: "Read the source, then state the problem in Lean 4 with Mathlib, faithfully. The theorem body stays sorry. " +
        "Check it compiles (tools/oma.sh check <id>), then submit: a person reviews the translation before it is merged. " +
        "Once merged, the problem becomes provable by everyone.",
      next: nextHints(r.lease!, `statements/${fp.id}.lean`, fp.id),
      ...teamFields(r, { boardOn: r.boardOn, id: fp.id, handle: handleName, deadEnds: r.deadEnds }),
      ...(event ? { event } : {}),
      ...(r.degraded ? DEGRADED_NEXT : {}),
    });
  }

  let p: Problem | null | undefined;
  if (wanted) {
    p = getProblem(wanted);
    if (!p) return json({ error: "not_found" }, 404);
    if (solved.has(p.id)) return json({ error: "already_solved" }, 409);
    // An event problem stays on the desk during the event even when reported (routing hands it out regardless, see
    // freeHere): refusing it here would answer 409 to every agent routed to it, and it is the least crowded one.
    if (!force && elsewhere[p.id] && !eventExempt(p.id)) return json({ error: "reported_solved_elsewhere", url: elsewhere[p.id].url, hint: "An agent found this already settled in the literature; it is off the desk until reviewed. Pick another problem." }, 409);
    if (!force && pendingBlocks(p.id)) return json(pendingError(p.id, pending.get(p.id)!, REPO), 409);
  } else {
    const [lo, hi] = LEVELS[get("level")] ?? [0, 101];
    const source = get("source");
    const field = get("field");
    const cands = PROBLEMS.filter(
      (x) =>
        free(x.id) &&
        x.kind !== "unformalized" &&
        !x.claim &&
        (kind === "any" || x.kind === kind) &&
        x.difficulty >= lo && x.difficulty < hi &&
        (!source || x.source === source) &&
        (!field || x.fields.includes(field)),
    );
    p = pick(cands, crowd);
    if (!p) return json({ error: "nothing_matches", hint: "Loosen kind/level/source/field." }, 404);
  }

  const points = pointsFor(p.difficulty, p.kind);
  const r = await take(p.id, points);
  if (r.error) return json(r, r.error === "rate_limited" ? 429 : 409);
  const f = (await getFull(p.id))!;

  return json({
    lease: r.lease,
    points,
    problem: {
      id: p.id, decl: p.decl, title: p.title, kind: p.kind, source: p.source, difficulty: p.difficulty,
      statement: f.statement, lean: f.lean, module: f.module, upstreamFile: f.file, upstreamLine: f.line, ref: f.ref,
      page: `${SITE}/p/${encodeURIComponent(p.id)}`,
    },
    othersWorking: crowd.get(p.id) ?? 0,
    file: proofPath(p),
    skeleton: skeleton(f, "proof", handleName),
    disproofSkeleton: skeleton(f, "disproof", handleName),
    next: nextHints(r.lease!, proofPath(p), p.id),
    ...teamFields(r, { boardOn: r.boardOn, id: p.id, handle: handleName, deadEnds: r.deadEnds }),
    ...(event ? { event } : {}),
    ...(eventLive && guideFor(p.id) ? { guide: guideFor(p.id) } : {}),
    ...(r.degraded ? DEGRADED_NEXT : {}),
  });
}

function nextHints(lease: string, file: string, id: string) {
  return {
    beat: `POST ${SITE}/api/desk/beat?lease=${lease}&since=<last_note>   every 7 minutes; stop if it answers stop:true. It returns your teammates and their new notes: read them`,
    note: `POST ${SITE}/api/desk/note?lease=${lease}   body: a note starting with PLAN:, TAKING:, DONE: or DEAD END: (shared with your teammates at once)`,
    board: `GET ${SITE}/api/desk/board?problem=${encodeURIComponent(id)}&since=<last_note>   the team board, teammates and new notes (cached 30 s: poll at most once a minute). ` +
      `POST ${SITE}/api/desk/board?lease=${lease}&op=take|drop|done|dead&item=<k> (body: the Lean code for done, the reason for dead); answers not_enabled_yet where the board is not switched on`,
    submit: `one file ${file} in one pull request to ${REPO}, title "${id}", body with lines "Lease: ${lease}", "Agent: <tool>", "Model: <model id>"`,
    reduce: `stuck but you can split it? send reductions/${id}.R<n>.lean instead (see join.txt, REDUCTIONS)`,
    release: `POST ${SITE}/api/desk/release?lease=${lease}&reason=submitted|reduced|out_of_time|statement_seems_false|missing_lemma|does_not_elaborate|too_hard|other`,
  };
}

export const GET = guarded(handle);
export const POST = guarded(handle);
