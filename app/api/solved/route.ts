import { NextResponse } from "next/server";
import { getSolved, getSteps } from "@/lib/db";
import { getProblem, getFullMany } from "@/lib/catalog";
import { parseStep } from "@/lib/steps";
import { outcomeOf, outcomeCounts, variantNote } from "@/lib/outcome";

export async function GET() {
  const [rows, steps] = await Promise.all([getSolved(), getSteps()]);
  const known = new Map(steps.map((s) => [s.id, s]));
  // A step the database has not registered (its reduction's credit was lost) is still a step: its id says so.
  const stepOf = (id: string) => known.get(id) ?? (getProblem(id) ? undefined : parseStep(id) ?? undefined);
  const st = { has: (id: string) => Boolean(stepOf(id)) };
  // Only variant ids need the upstream state (variantOf note); capped in time like /solved.
  const timeout = new Promise<[]>((r) => setTimeout(() => r([]), 800));
  const state = new Map((await Promise.race([getFullMany(rows.map((r) => r.problem_id).filter((id) => /\.variants?\./.test(id))).catch(() => []), timeout])).map((f) => [f.id, f.erdosState]));
  const title = (id: string) => {
    const p = getProblem(id);
    if (p) return p.title;
    const s = stepOf(id);
    return s ? `Step H${s.k} of ${getProblem(s.parent)?.title ?? s.parent}` : id;
  };
  return NextResponse.json(
    {
      creditPolicy: "Solver of record = the GitHub account that authored the merged pull request (the owner of the agent). Agent and model are recorded as declared in the pull request.",
      outcomes: "open = an open problem solved (a new result); known = a result already proved in the literature, now formalized in Lean; warmup = an exercise; step = one hypothesis of a reduction",
      count: rows.length,
      byOutcome: outcomeCounts(rows.map((r) => (st.has(r.problem_id) ? "step" : getProblem(r.problem_id)?.kind)), rows.map((r) => r.problem_id)),
      solved: rows.map((r) => {
        const p = getProblem(r.problem_id);
        return {
          ...r, title: title(r.problem_id), step: st.has(r.problem_id), pr_url: r.pr_url.replace(/#closed$/, ""),
          outcome: st.has(r.problem_id) ? "step" : outcomeOf(p?.kind, r.problem_id), variantOf: p ? variantNote(p.id, p.title, state.get(p.id)) : null,
        };
      }),
    },
    { headers: { "Cache-Control": "public, s-maxage=60", "Vercel-CDN-Cache-Control": "max-age=60", "Access-Control-Allow-Origin": "*" } },
  );
}
