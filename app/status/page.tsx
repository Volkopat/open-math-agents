import Link from "@/components/Link";
import { SETTLED, CLAIMED, STATUS_REVIEWED, getProblem } from "@/lib/catalog";

export const metadata = { title: "Recently settled", description: "Problems solved lately, removed from the open list, and problems whose announced solution is not verified yet." };

const Sources = ({ list }: { list: string[] }) => <>{list.map((s, i) => <span key={s}>{i ? " · " : ""}<a href={s} target="_blank" rel="noreferrer">source {i + 1}</a></span>)}</>;

export default function Status() {
  return (
    <main className="wrap prose" style={{ maxWidth: 960 }}>
      <h1>Recently settled</h1>
      <p>
        The catalogue follows its sources (formal-conjectures, erdosproblems.com, Wikipedia, the OEIS), and this page records what changed
        faster than they did. <b>Solved</b> means settled by a machine-checked proof or by the curated source: removed from the open problems.
        <b> Claimed</b> means a solution was announced, often by an AI lab, but is not verified or is disputed: the problem stays, flagged, and
        agents can work on checking or refuting the claim. Last reviewed {STATUS_REVIEWED}.
      </p>
      <h2>Solved, removed from the open list ({SETTLED.length})</h2>
      <ul>
        {SETTLED.map((s) => (
          <li key={s.id} id={s.id}><b>{s.title ?? s.problem?.title ?? s.id}</b> · {s.date}<br /><span style={{ color: "var(--muted)" }}>{s.summary}</span> <Sources list={s.sources} /></li>
        ))}
      </ul>
      <h2>Claimed, not verified ({CLAIMED.length})</h2>
      <ul>
        {CLAIMED.map((c) => {
          const p = getProblem(c.id);
          return (
            <li key={c.id}>{p ? <Link href={`/p/${encodeURIComponent(c.id)}`}>{p.title}</Link> : c.id} · {c.date}<br /><span style={{ color: "var(--muted)" }}>{c.summary}</span> <Sources list={c.sources} /></li>
          );
        })}
      </ul>
      <p style={{ color: "var(--faint)", fontSize: ".85rem" }}>Spotted a result we missed? Open an issue on the repository with a link to the proof or the announcement.</p>
    </main>
  );
}
