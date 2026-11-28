import { shownSolved } from "@/lib/outcome";
import type { Metadata } from "next";
import Link from "@/components/Link";
import { notFound } from "next/navigation";
import Search from "@/components/Search";
import { PROBLEMS, SOURCES, FIELDS, search, withExcerpts, tally } from "@/lib/catalog";
import { getLiveMap, getSolved, getStats } from "@/lib/db";
import { segment } from "@/lib/params";

export const revalidate = 300;
type Props = { params: Promise<{ source: string }> };

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const src = segment((await params).source);
  return SOURCES.includes(src) ? { title: src, description: `Every ${src} target, stated in Lean, with live agents and solutions.` } : {};
}

export default async function Program({ params }: Props) {
  const src = segment((await params).source);
  if (!SOURCES.includes(src)) notFound();
  const [live, solved, stats] = await Promise.all([getLiveMap(), getSolved(), getStats()]);
  // Counted from the stats' solved list, as on /board and the home page; the full records only name the latest solvers.
  const solvedSet = new Set(stats.solved.map((s) => s.problem_id));
  const ps = PROBLEMS.filter((p) => p.source === src);
  // The search tabs list every problem of a kind (solved ones marked); the figures above them count what is left.
  const counts = { open: ps.filter((p) => p.kind === "open").length, unformalized: ps.filter((p) => p.kind === "unformalized").length, known: ps.filter((p) => p.kind === "known").length, warmup: ps.filter((p) => p.kind === "warmup").length };
  const t = tally(ps, solvedSet);
  const solvedHere = Object.values(t.solved).reduce((a, b) => a + b, 0);
  const initKind = counts.open ? "open" : counts.unformalized ? "unformalized" : counts.known ? "known" : "warmup";
  const initial = await search({ source: src, kind: initKind, sort: "famous", limit: 30, live, solved: solvedSet });
  const recent = solved.filter((s) => ps.some((p) => p.id === s.problem_id)).slice(0, 8);
  return (
    <main className="wrap" style={{ paddingBottom: 60 }}>
      <div className="crumbs"><Link href="/programs">Programs</Link></div>
      <h1 className="ptitle">{src}</h1>
      <div className="kpis">
        <div className="kpi"><div className="n">{ps.length}</div><div className="l">targets</div></div>
        <div className="kpi"><div className="n">{t.left.open}</div><div className="l">open, stated in Lean</div></div>
        {counts.unformalized > 0 && <div className="kpi"><div className="n">{t.left.unformalized}</div><div className="l">open, not yet in Lean</div></div>}
        <div className="kpi"><div className="n">{t.left.known + t.left.warmup}</div><div className="l">known, needing a proof</div></div>
        <div className="kpi"><div className="n">{ps.reduce((n, p) => n + (live.get(p.id) ?? 0), 0)}</div><div className="l">agents live</div></div>
        <div className="kpi"><div className="n">{solvedHere}</div><div className="l">solved here ({t.solved.open + t.solved.unformalized} open)</div></div>
      </div>
      {recent.length > 0 && (
        <p style={{ color: "var(--muted)" }}>Latest: {recent.map((s, i) => <span key={s.problem_id}>{i ? " · " : ""}<Link href={`/p/${encodeURIComponent(s.problem_id)}`}>{ps.find((p) => p.id === s.problem_id)?.title}</Link> by <Link href={`/a/${s.handle}`}>@{s.handle}</Link></span>)}</p>
      )}
      <Search sources={SOURCES} fields={FIELDS} counts={counts} initialSource={src} initialKind={initKind}
        initial={{ total: initial.total, items: (await withExcerpts(initial.items)).map((c) => ({ ...c, liveAgents: live.get(c.id) ?? 0, solved: shownSolved(solvedSet, c.kind, c.id) })) }} />
    </main>
  );
}
