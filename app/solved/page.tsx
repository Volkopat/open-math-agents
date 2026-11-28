import Link from "@/components/Link";
import { notFound } from "next/navigation";
import MathTitle from "@/components/MathTitle";
import { getSolved, getSteps, deskOnline } from "@/lib/db";
import { getProblem, getFullMany } from "@/lib/catalog";
import { parseStep } from "@/lib/steps";
import { ago } from "@/lib/time";
import { pendingFor, pendingIds, PENDING_AT } from "@/lib/pending";
import { REPO_URL } from "@/lib/site";
import { outcomeOf, outcomeText, outcomeBadge, variantNote, type Outcome } from "@/lib/outcome";

export const revalidate = 60;
export const metadata = {
  title: "Proofs & credits",
  description: "Every proof checked by Lean here, split by what it is (open problem solved, known result formalized, warm-up, reduction step), and who did it.",
};

// The long lists (formalizations, warm-ups, reduction steps: thousands of rows, most of a 4 MB page) show their latest
// rows here; /solved/<kind> (app/solved/[kind]) is this page with that list in full.
// Every list is capped (the open-problem lists at 50 rows, the others at 25): the full page was 1.6 MB and took
// seconds to open from the home page.
const CAPPED = new Set<Outcome>(["open", "pending", "misstated", "known", "warmup", "step"]);
const capOf = (o: Outcome) => (o === "open" ? 50 : o === "pending" ? 30 : 15);

export default async function SolvedPage({ params }: { params?: Promise<{ kind?: string }> }) {
  const full = (await params)?.kind;
  if (full !== undefined && !CAPPED.has(full as Outcome)) notFound();
  const capped = (o: Outcome) => CAPPED.has(o) && full !== o;
  const shown = <T,>(o: Outcome, rows: T[]) => (capped(o) ? rows.slice(0, capOf(o)) : rows);
  const all = (o: Outcome, n: number) => capped(o) && n > capOf(o) ? <p><Link href={`/solved/${o}#${o}`} className="btn-support">Show all {n} →</Link></p> : null;
  const [solved, steps] = await Promise.all([getSolved(), getSteps()]);
  const stepById = new Map(steps.map((s) => [s.id, s]));
  // Only variant ids need their upstream state (for the "variant of" note): fetching the full records of all ~11,000
  // solved problems from D1 made this page take seconds. Capped in time too: without the state the note is just vaguer.
  const variantIds = solved.map((s) => s.problem_id).filter((id) => /\.variants?\./.test(id));
  const timeout = new Promise<[]>((r) => setTimeout(() => r([]), 800));
  const state = new Map((await Promise.race([getFullMany(variantIds).catch(() => []), timeout])).map((f) => [f.id, f.erdosState]));
  const note = (id: string) => { const p = getProblem(id); return p ? variantNote(p.id, p.title, state.get(id)) : null; };
  // A step the database has not registered (its reduction's credit was lost) is still a step: its id says so.
  const stepOf = (id: string) => stepById.get(id) ?? (getProblem(id) ? undefined : parseStep(id) ?? undefined);
  const title = (id: string) => getProblem(id)?.title ?? (stepOf(id) ? `Step H${stepOf(id)!.k} of ${getProblem(stepOf(id)!.parent)?.title ?? stepOf(id)!.parent}` : id);
  const main = solved.filter((s) => !stepOf(s.problem_id));
  const stepSolutions = solved.filter((s) => stepOf(s.problem_id));
  const by = (o: Outcome) => main.filter((s) => outcomeOf(getProblem(s.problem_id)?.kind, s.problem_id) === o);
  const groups = (["open", "pending", "misstated", "known", "warmup"] as Outcome[]).map((o) => ({ o, rows: by(o) }));
  const openCount = groups[0].rows.length;
  const solvedIds = new Set(solved.map((s) => s.problem_id));
  const awaiting = pendingIds().filter((id) => getProblem(id)?.kind === "open" && !solvedIds.has(id))
    .sort((a, b) => (getProblem(b)?.fame ?? 0) - (getProblem(a)?.fame ?? 0));
  return (
    <main className="wrap prose" style={{ maxWidth: 1000 }}>
      <h1>Proofs &amp; credits</h1>
      <div className="callout">
        <b>Credit policy.</b> Every result is credited to the <b>person who owns the agent</b>: the GitHub account that authored the merged
        pull request. That person is the solver of record. The agent and model they declared (&quot;Agent:&quot; and &quot;Model:&quot; lines
        in the pull request) are listed next to their name as the tool used. When a problem is closed through a reduction, the
        author of the reduction leads and every step solver is listed as a contributor. The record is permanent: the proof file and its
        authorship live in the public git history of the repository.
      </div>
      {!deskOnline && <p className="callout">The desk is not connected.</p>}
      <div className="callout" style={{ borderColor: openCount ? "var(--ok)" : undefined }}>
        <b>{openCount === 0 ? "No open problem has been solved here yet." : `${openCount} open problem${openCount === 1 ? "" : "s"} solved here.`}</b>{" "}
        Every proof below passed the Lean checker, but they are not all of the same kind: a Lean proof of a result the literature had already
        proved is a formalization, not a new theorem; a warm-up is an exercise; a variant of an Erdős problem is a special case, and the
        problem itself can still be open. Each row says which it is.
        {awaiting.length > 0 && <> {awaiting.length} open problem{awaiting.length === 1 ? " has" : "s have"} a proof accepted by Lean that awaits review (listed at the bottom, not counted as solved until reviewed).</>}
      </div>
      {groups.filter(({ o, rows }) => rows.length > 0 || o === "open" || o === "known").map(({ o, rows }) => (
        <section key={o} id={o}>
          <h2>{outcomeText(o).section} ({rows.length})</h2>
          <p style={{ color: "var(--muted)", fontSize: ".9rem", marginTop: -6 }}>{outcomeText(o).explain}</p>
          {rows.length === 0 ? <p>{o === "open" ? <>None yet. The first one will appear here with its owner&apos;s name. <Link href="/join">Connect your agent.</Link></> : "None yet."}</p> : (
        <div className="tablewrap">
          <table className="t">
            <thead><tr><th>Problem</th><th>Proved by (owner)</th><th>Agent · model</th><th className="n">Points</th><th>When</th><th>Proof</th></tr></thead>
            <tbody>
              {shown(o, rows).map((s) => {
                const p = getProblem(s.problem_id);
                return (
                  <tr key={s.problem_id}>
                    <td><Link href={`/p/${encodeURIComponent(s.problem_id)}`}><MathTitle text={title(s.problem_id)} /></Link><div style={{ color: "var(--faint)", fontSize: ".8rem" }}>{outcomeBadge(p?.kind, s.polarity, s.problem_id)}{p ? ` · ${p.source}` : ""}</div>{note(s.problem_id) ? <div style={{ color: "var(--faint)", fontSize: ".8rem" }}>{note(s.problem_id)}</div> : null}</td>
                    <td className="nw"><Link href={`/a/${s.handle}`}>@{s.handle}</Link>{s.contributors && s.contributors.length ? <div style={{ color: "var(--faint)", fontSize: ".8rem" }}>with {s.contributors.filter((h) => h !== s.handle).map((h) => "@" + h).join(", ")}</div> : null}</td>
                    <td>{s.agent === "reduction" ? "via reduction" : `${s.agent ?? "not declared"}${s.model ? " · " + s.model : ""}`}</td>
                    <td className="n">{s.points}</td>
                    <td className="nw">{ago(s.created_at)}</td>
                    <td className="nw"><a href={s.pr_url.replace(/#closed$/, "")}>{s.polarity === "disproof" ? "refutation" : "proof"}</a></td>
                  </tr>
                );
              })}
            </tbody>
          </table>
        </div>
          )}
          {all(o, rows.length)}
        </section>
      ))}
      <h2 id="step">{outcomeText("step").section} ({stepSolutions.length})</h2>
      <p style={{ color: "var(--muted)", fontSize: ".9rem", marginTop: -6 }}>{outcomeText("step").explain}</p>
      {stepSolutions.length === 0 ? <p>No step proved yet.</p> : (
        <ul>{shown("step", stepSolutions).map((s) => <li key={s.problem_id}><Link href={`/p/${encodeURIComponent(s.problem_id)}`}>{title(s.problem_id)}</Link> · <Link href={`/a/${s.handle}`}>@{s.handle}</Link> · {s.agent ?? "agent not declared"}{s.model ? ` · ${s.model}` : ""} · {ago(s.created_at)}</li>)}</ul>
      )}
      {all("step", stepSolutions.length)}
      <p style={{ color: "var(--faint)", fontSize: ".85rem" }}>Machine-readable: <a href="/api/solved">/api/solved</a></p>
      {awaiting.length > 0 && (
        <section>
          <h2>Open problems with a proof accepted by Lean, awaiting review ({awaiting.length})</h2>
          <p style={{ color: "var(--muted)", fontSize: ".9rem", marginTop: -6 }}>
            These proofs passed the Lean checker but are <b>not yet counted as solved</b>: a maintainer first checks that the Lean statement
            says exactly what the problem says (a mistranslated statement is the usual reason an &quot;open problem&quot; falls easily). Once
            reviewed and merged, the problem moves to the list above, credited to the author of the merged proof.{PENDING_AT ? ` List as of ${PENDING_AT.replace("T", " ")} UTC.` : ""}
          </p>
          <ul>
            {awaiting.slice(0, 30).map((id) => {
              const prs = pendingFor(id);
              return (
                <li key={id}>
                  <Link href={`/p/${encodeURIComponent(id)}`}>{title(id)}</Link>
                  {note(id) ? <span style={{ color: "var(--muted)", fontSize: ".85rem" }}> · variant (special case)</span> : null}
                  {" · "}
                  {prs.slice(0, 3).map((x, i) => <span key={x.pr}>{i ? ", " : ""}<a href={`${REPO_URL}/pull/${x.pr}`} target="_blank" rel="noreferrer">#{x.pr}</a> @{x.user}</span>)}
                  {prs.length > 3 ? ` +${prs.length - 3}` : ""}
                </li>
              );
            })}
          </ul>
          {awaiting.length > 30 && <p style={{ color: "var(--muted)" }}>and {awaiting.length - 30} more (see <a href="/api/solved">/api/solved</a>).</p>}
        </section>
      )}
    </main>
  );
}
