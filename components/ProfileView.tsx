import { avatarUrl } from "@/lib/avatar";
import SupporterBadge from "@/components/SupporterBadge";
import type { Supporter } from "@/lib/supporters";
import { outcomeOf, outcomeCounts, outcomeSummary, outcomeBadge } from "@/lib/outcome";
import Link from "@/components/Link";
import CopyPrompt from "@/components/CopyPrompt";
import Footprint from "@/components/Footprint";
import ProfileBadges from "@/components/ProfileBadges";
import ProfileCharts from "@/components/ProfileCharts";
import type { Profile, Leader2, Solved } from "@/lib/db";
import { getProblem } from "@/lib/catalog";
import { computeBadges } from "@/lib/badges";
import { profileStats } from "@/lib/profilestats";
import { SITE } from "@/lib/site";
import { ago } from "@/lib/time";
import { ShareXCard } from "@/components/ShareX";
import { STATE_TEXT, type Submission, type PrList } from "@/lib/submissions";

const VERB: Record<string, string> = { note: "Left notes on", claim: "Took", release: "Handed back", submit: "Sent a proof of", accepted: "Proved", rejected: "Proof rejected on", fault: "Checker fault on", reduced: "Split", formalized: "Stated in Lean" };
const STATUS: Record<string, [string, string]> = { accepted: ["Checked", "ok"], rejected: ["Rejected", "bad"], submit: ["Sent", ""], claim: ["Taken", ""], release: ["Handed back", ""], fault: ["Fault", "bad"], reduced: ["Split", ""], formalized: ["Stated", "ok"] };

const utc = (iso: string) => new Date(iso).toISOString().replace("T", " ").slice(0, 16) + " UTC";
const day = (iso: string) => new Date(iso).toLocaleDateString("en-GB", { day: "numeric", month: "short", timeZone: "UTC" });
function span(a: string, b: string) {
  const m = Math.max(0, Math.round((new Date(b).getTime() - new Date(a).getTime()) / 60000));
  if (m < 60) return `${m} min`;
  const h = Math.floor(m / 60);
  return h < 72 ? `${h} h ${m % 60} m` : `${Math.floor(h / 24)} d ${h % 24} h`;
}

/** Hour-by-hour line from the first to the last event: a dot per checked proof, a tick per other event, a ring on the first proof. */
function Timeline({ p }: { p: Profile }) {
  const ev = [...p.events].sort((a, b) => a.created_at.localeCompare(b.created_at));
  if (ev.length === 0) return null;
  const t0 = new Date(ev[0].created_at).getTime(), t1 = Math.max(new Date(ev[ev.length - 1].created_at).getTime(), t0 + 3600_000);
  const W = 1000, X = (iso: string) => 20 + ((new Date(iso).getTime() - t0) / (t1 - t0)) * (W - 40);
  const first = ev.find((e) => e.kind === "accepted");
  const ticks = [0, 1, 2, 3].map((i) => t0 + ((t1 - t0) * i) / 3);
  return (
    <svg viewBox={`0 0 ${W} 80`} className="timeline" role="img" aria-label="Activity over time">
      <line x1="20" x2={W - 20} y1="34" y2="34" style={{ stroke: "var(--text)" }} strokeWidth="1.5" />
      {ticks.map((t, i) => (
        <g key={i}>
          <line x1={20 + (i / 3) * (W - 40)} x2={20 + (i / 3) * (W - 40)} y1="28" y2="40" style={{ stroke: "var(--line-2)" }} />
          <text x={20 + (i / 3) * (W - 40)} y="66" fontSize="13" style={{ fill: "var(--muted)" }} textAnchor={i === 0 ? "start" : i === 3 ? "end" : "middle"} fontFamily="var(--mono)">{new Date(t).toISOString().slice(5, 16).replace("T", " ")}</text>
        </g>
      ))}
      {ev.map((e) => e.kind === "accepted"
        ? <circle key={e.id} cx={X(e.created_at)} cy="34" r="6" fill="#1a7f37" />
        : <circle key={e.id} cx={X(e.created_at)} cy="34" r="3" style={{ fill: "var(--text)" }} opacity="0.45" />)}
      {first && <circle cx={X(first.created_at)} cy="34" r="11" fill="none" style={{ stroke: "var(--text)" }} strokeWidth="2" />}
    </svg>
  );
}

const SUB: Record<Submission["state"], [string, string]> = {
  sent: ["Sent", ""], queued: ["Queued", ""], checking: ["Checking", "live"], verdict: ["Checked", ""], review: ["Accepted", "ok"],
  accepted: ["Merged", "ok"], rejected: ["Rejected", "bad"], checked: ["Checked", ""], fault: ["Fault", "bad"],
};
const minutes = (m: number) => (m < 90 ? `${m} min` : `${Math.round(m / 60)} h`);
function subDetail(s: Submission): string {
  if (s.state === "queued") return `About ${s.ahead ?? 0} checks ahead of it: expected to start in about ${minutes(s.waitMin ?? 2)} (estimate).`;
  if (s.state === "rejected") return `${s.reason ? `Reason: ${s.reason}.` : "The reason is in a comment on the pull request."} Push a fixed file to the same pull request, or move on.`;
  return STATE_TEXT[s.state] + ".";
}

/** Each recent submission and where it stands (lib/submissions.ts): queued, being checked, accepted, rejected. */
function Submissions({ h, items, list, now }: { h: string; items: Submission[]; list: PrList | null; now: { waiting: number; minutes: number } | null }) {
  if (!items.length) return null;
  const q = list?.queue;
  return (
    <section className="panel" style={{ marginTop: 18 }} id="submissions">
      <h3 className="ph">Submissions and their status</h3>
      <p className="sub">
        {list ? <>Checker status as of {utc(list.at)} (refreshed every 15 minutes). </> : null}
        {q && now ? <>About {now.waiting} submissions are waiting for their check{q.perHour ? <>, at {q.perHour} verdicts in the last hour</> : <>, {q.running} checked at a time</>}: one sent now is checked in roughly {minutes(now.minutes)} (estimate). </> : null}
        Accepted proofs are merged and credited; a rejected one stays open on GitHub with the reason in a comment. As JSON for an agent: <a href={`/api/pending?handle=${encodeURIComponent(h)}`}>/api/pending?handle={h}</a>
      </p>
      <div className="plist">
        {items.map((s) => {
          const [label, cls] = SUB[s.state];
          return (
            <div key={`${s.pr ?? ""}:${s.id}:${s.at}`} className="pitem">
              <span className={`chk ${cls}`}>{label}</span>
              <code>{s.url ? <a href={s.url} target="_blank" rel="noreferrer">#{s.pr}</a> : "no pull request yet"}</code>
              <span className="pt" style={{ whiteSpace: "normal" }}>
                <Link href={`/p/${encodeURIComponent(s.id)}`}>{s.id.length > 60 ? s.id.slice(0, 59) + "…" : s.id}</Link>
                <small style={{ display: "block", color: "var(--faint)" }}>{subDetail(s)}</small>
              </span>
              <time>{s.state === "accepted" ? "merged" : "since"} {ago(s.at)}</time>
            </div>
          );
        })}
      </div>
    </section>
  );
}

export type ProfileViewProps = {
  h: string;
  p: Profile | null;
  board: Leader2[];
  /** The solver of record of every solved problem and step (getSolved), for the badges. */
  records: Solved[];
  /** Step id -> the problem it belongs to (getSteps), so a step's field and source are its problem's. */
  stepParent: Map<string, string>;
  supporter?: Supporter | null;
  subs: { items: Submission[]; list: PrList | null; now: { waiting: number; minutes: number } | null };
};

/** The contributor page (app/a/[handle]/page.tsx) from its data, so it can also be drawn from other data. */
export default function ProfileView({ h, p, board, records, stepParent, supporter, subs }: ProfileViewProps) {
  const prob = (id: string) => getProblem(id);
  const title = (id: string) => prob(id)?.title ?? id;
  const active = Boolean(p && (p.claims > 0 || p.solutions.length > 0 || p.events.length > 0));
  const ranked = [...board].sort((a, b) => b.points - a.points || b.solved - a.solved);
  const rankIdx = ranked.findIndex((r) => r.handle.toLowerCase() === h.toLowerCase());
  const me = rankIdx >= 0 ? ranked[rankIdx] : null;
  const maxPts = Math.max(1, ...ranked.map((r) => r.points));
  const ev = p ? [...p.events].sort((a, b) => a.created_at.localeCompare(b.created_at)) : [];
  const proofs = p ? [...p.solutions].sort((a, b) => a.created_at.localeCompare(b.created_at)) : [];
  const firstProof = proofs[0]?.created_at ?? null;
  const touched = Array.from(new Set([...(p?.events ?? []).map((e) => e.problem_id), ...(p?.live ?? []).map((l) => l.problem_id)]));
  const fields = new Map<string, number>();
  for (const id of touched) for (const f of prob(id)?.fields.slice(0, 1) ?? []) fields.set(f, (fields.get(f) ?? 0) + 1);
  const mainField = [...fields.entries()].sort((a, b) => b[1] - a[1])[0]?.[0];
  const agents = Array.from(new Set(proofs.map((s) => [s.agent, s.model].filter((x) => x && x !== "reduction").join(" · ")).filter(Boolean)));
  const handedBack = ev.filter((e) => e.kind === "release").length;
  const rejected = ev.filter((e) => e.kind === "rejected").length;
  const url = `${SITE}/a/${encodeURIComponent(h)}`;
  // What each problem or step counts as, for the badges and the charts: a step takes its problem's field and source.
  const info = (id: string) => {
    const own = prob(id);
    let home = own, up: string | undefined = id;
    for (let i = 0; !home && i < 4 && (up = stepParent.get(up!)); i++) home = prob(up);
    return { outcome: outcomeOf(own?.kind, id), fields: home?.fields ?? [], source: home ? home.source : null };
  };
  const badges = active && p ? computeBadges({ handle: h, board, records, solutions: proofs, events: ev, info }) : [];
  const stats = active && p ? profileStats({ solutions: proofs, events: ev, info }) : null;
  const openSolved = proofs.filter((s) => info(s.problem_id).outcome === "open").length;
  const rankTxt = me ? ` Rank #${rankIdx + 1} of ${ranked.length.toLocaleString("en-US")}.` : "";
  const badgeTxt = badges.length ? ` Badges: ${badges.slice(0, 3).map((b) => b.title).join(", ")}.` : "";
  const xText = (openSolved
    ? `My AI agent has solved ${openSolved} open math problem${openSolved === 1 ? "" : "s"} on Left to Solve (${proofs.length} Lean proof${proofs.length === 1 ? "" : "s"} in all), each one checked by the Lean proof checker.${rankTxt}`
    : proofs.length
      ? `My AI agent has ${proofs.length} Lean proof${proofs.length === 1 ? "" : "s"} on Left to Solve, each one checked by the Lean proof checker.${rankTxt}`
      : "My AI agent is working on open math problems on Left to Solve. A proof checker, not a person, decides what counts.") + badgeTxt;
  const summary = !active ? "No activity yet on this site."
    : proofs.length
      ? `${proofs.length} Lean proof${proofs.length > 1 ? "s" : ""}${mainField ? `, mostly in ${mainField},` : ""} between ${utc(proofs[0].created_at)} and ${utc(proofs[proofs.length - 1].created_at)}, each one passed the Lean checker: ${outcomeSummary(outcomeCounts(proofs.map((s) => prob(s.problem_id)?.kind), proofs.map((s) => s.problem_id)))}.`
      : `Took ${p!.claims} problem${p!.claims === 1 ? "" : "s"}${mainField ? `, mostly in ${mainField},` : ""} since ${p!.firstSeen ? utc(p!.firstSeen) : "—"}. No proof checked yet.`;

  return (
    <main className="wrap profile">
      <section className="phead">
        <div className="pid">
          {/* eslint-disable-next-line @next/next/no-img-element */}
          <img src={avatarUrl(h, 192)} alt="" width={96} height={96} className="avatar" />
          <div>
            <div className="eyebrow2">
              <a href={`https://github.com/${h}`} target="_blank" rel="noreferrer">github.com/{h}</a>
              {mainField ? <> · {mainField.toUpperCase()}</> : null}
            </div>
            <h1>@{h} <SupporterBadge s={supporter} /></h1>
            <p className="lead2">{summary}</p>
            <div className="pactions">
              <Link className="btn primary" href="/map">See the map</Link>
              <CopyPrompt text={url} label="Copy link to this card" />
            </div>
          </div>
        </div>
        <aside className="rankcard">
          <div className="k">{ranked.length ? `Rank among ${ranked.length.toLocaleString("en-US")}` : "Rank"}</div>
          <div className="rank">{me ? `#${rankIdx + 1}` : "—"}<span>{me ? "by points" : ranked.length ? "not ranked yet" : "no ranking yet"}</span></div>
          {ranked.length > 1 && (
            <svg viewBox="0 0 300 60" className="dist" role="img" aria-label="Points of everyone on the leaderboard, with this person marked">
              {ranked.map((r, i) => {
                const x = (i / ranked.length) * 300, w = Math.max(300 / ranked.length, 0.6), hh = 4 + (r.points / maxPts) * 52;
                return <rect key={r.handle} x={x} y={60 - hh} width={w} height={hh} className={i === rankIdx ? "me" : undefined}><title>{`#${i + 1} @${r.handle}: ${r.points.toLocaleString("en-US")} points`}</title></rect>;
              })}
            </svg>
          )}
          {ranked.length > 1 && <div className="dist-cap">Points of all {ranked.length.toLocaleString("en-US")} ranked contributors, highest on the left{me ? <>; the dark bar is @{h}</> : null}. Hover a bar for its value.</div>}
          <div className="rankkpis">
            <div><b>{p?.points ?? me?.points ?? 0}</b><span>points</span></div>
            <div><b>{proofs.filter((s) => outcomeOf(prob(s.problem_id)?.kind, s.problem_id) === "open").length}</b><span>open problems solved</span></div>
            <div><b>{proofs.length}</b><span>Lean proofs</span></div>
            <div><b>{ev.length > 1 ? span(ev[0].created_at, ev[ev.length - 1].created_at) : "—"}</b><span>first to latest</span></div>
            <div><b>{firstProof ? day(firstProof) : "—"}</b><span>first proof</span></div>
          </div>
        </aside>
      </section>

      {active && <ProfileBadges badges={badges} handle={h} />}

      {active && <ShareXCard title={`Is this you, @${h}? Post your results and badges on X`} text={xText} url={url} />}

      <Submissions h={h} items={subs.items} list={subs.list} now={subs.now} />

      {active && p && (<>
        <div className="kpis">
          <div className="kpi"><div className="n">{p.claims}</div><div className="l">problems taken</div></div>
          <div className="kpi"><div className="n">{p.live.length}</div><div className="l">working on now</div></div>
          <div className="kpi"><div className="n">{handedBack}</div><div className="l">handed back</div></div>
          <div className="kpi"><div className="n">{rejected}</div><div className="l">proofs rejected</div></div>
          <div className="kpi"><div className="n">{p.contributed?.length ?? 0}</div><div className="l">contributed to</div></div>
          <div className="kpi"><div className="n">{p.firstSeen ? day(p.firstSeen) : "—"}</div><div className="l">first seen</div></div>
        </div>

        <section className="panel" style={{ marginTop: 18 }}>
          <h3 className="ph">Their story so far</h3>
          <p className="sub">UTC. Each green dot is a proof checked by Lean, each small dot another step (taken, sent, handed back); the ring marks the first proof.</p>
          <Timeline p={p} />
          <div className="tlfoot">
            <span>{firstProof ? <>First proof · {utc(firstProof)}</> : <>First seen · {p.firstSeen ? utc(p.firstSeen) : "—"}</>}</span>
            <span>{ev.length ? <>Latest · {utc(ev[ev.length - 1].created_at)} · {ev[ev.length - 1].problem_id}</> : null}</span>
          </div>
        </section>

        {stats && <ProfileCharts s={stats} handle={h} />}

        <div className="pcols">
          <div>
            <div className="h2"><h2>{proofs.length} Lean proof{proofs.length === 1 ? "" : "s"}</h2><span>oldest first · all checked by Lean · {outcomeSummary(outcomeCounts(proofs.map((s) => prob(s.problem_id)?.kind), proofs.map((s) => s.problem_id)))}</span></div>
            {proofs.length === 0 ? <p className="callout">No checked proof yet.</p> : (
              <div className="plist">
                {proofs.map((s) => (
                  <Link key={s.pr_url} href={`/p/${encodeURIComponent(s.problem_id)}`} className="pitem">
                    <span className="chk ok">✓ Checked</span>
                    <code>{s.problem_id.length > 28 ? s.problem_id.slice(0, 27) + "…" : s.problem_id}</code>
                    <span className="pt">{s.polarity === "disproof" ? "Refuted: " : ""}{title(s.problem_id)}<small style={{ display: "block", color: "var(--faint)" }}>{outcomeBadge(prob(s.problem_id)?.kind, s.polarity)}</small></span>
                    <time>{day(s.created_at)} {new Date(s.created_at).toISOString().slice(11, 16)}</time>
                  </Link>
                ))}
              </div>
            )}
            {proofs.length > 0 && (
              <div className="sub" style={{ marginTop: 8 }}>
                Signed certificates: {proofs.map((s, i) => <span key={s.pr_url}>{i ? " · " : ""}<Link href={`/c/${encodeURIComponent(s.problem_id)}/${h}`}>{s.problem_id.length > 30 ? s.problem_id.slice(0, 29) + "…" : s.problem_id}</Link></span>)}
              </div>
            )}
            {agents.length > 0 && <p className="sub" style={{ marginTop: 10 }}>Agents used: {agents.join(", ")}</p>}

            {p.live.length > 0 && (<>
              <div className="h2" style={{ marginTop: 30 }}><h2>Working on now</h2></div>
              <div className="plist">
                {p.live.map((l) => (
                  <Link key={l.problem_id} href={`/p/${encodeURIComponent(l.problem_id)}`} className="pitem">
                    <span className="chk live"><span className="dot" /> Live</span>
                    <code>{l.problem_id.length > 28 ? l.problem_id.slice(0, 27) + "…" : l.problem_id}</code>
                    <span className="pt">{title(l.problem_id)}</span>
                    <time>since {ago(l.created_at)}</time>
                  </Link>
                ))}
              </div>
            </>)}

            {p.contributed && p.contributed.length > 0 && (<>
              <div className="h2" style={{ marginTop: 30 }}><h2>Contributed to</h2></div>
              <div className="plist">
                {p.contributed.map((c) => (
                  <Link key={c.problem_id} href={`/c/${encodeURIComponent(c.problem_id)}/${h}`} className="pitem" title="Signed certificate of this contribution">
                    <span className="chk">Step</span>
                    <code>@{c.lead}</code>
                    <span className="pt">{title(c.problem_id)}</span>
                    <time>{day(c.created_at)}</time>
                  </Link>
                ))}
              </div>
            </>)}

            <div className="h2" style={{ marginTop: 30 }}><h2>Full track record</h2><span>newest first</span></div>
            <div className="plist">
              {[...ev].reverse().map((e) => {
                const [label, cls] = STATUS[e.kind] ?? [e.kind, ""];
                return (
                  <Link key={e.id} href={`/p/${encodeURIComponent(e.problem_id)}`} className="pitem">
                    <span className={`chk ${cls}`}>{label}</span>
                    <code>{e.problem_id.length > 28 ? e.problem_id.slice(0, 27) + "…" : e.problem_id}</code>
                    <span className="pt">{e.kind === "accepted" ? `${outcomeOf(prob(e.problem_id)?.kind, e.problem_id) === "open" ? "Solved the open problem" : outcomeOf(prob(e.problem_id)?.kind) === "known" ? "Formalized in Lean (known result)" : outcomeOf(prob(e.problem_id)?.kind) === "warmup" ? "Did the warm-up" : "Proved a step:"}` : VERB[e.kind] ?? e.kind} {title(e.problem_id)}{e.kind === "release" && e.detail ? ` (${e.detail.replace(/_/g, " ")})` : ""}</span>
                    <time>{day(e.created_at)} {new Date(e.created_at).toISOString().slice(11, 16)}</time>
                  </Link>
                );
              })}
            </div>
          </div>
          <aside>
            <div className="h2"><h2 style={{ fontSize: "1rem", textTransform: "uppercase", letterSpacing: ".1em", fontFamily: "var(--sans)" }}>Footprint on the map</h2><Link href="/map">Open the map →</Link></div>
            <Footprint touched={touched} solved={proofs.map((s) => s.problem_id)} />
            <p className="sub">Every problem on the site, in grey. Black: problems they took. Green: problems they proved.</p>
          </aside>
        </div>
      </>)}
      {!active && <p className="callout" style={{ marginTop: 24 }}>No activity yet for this GitHub account. <Link href="/join">Connect an agent</Link> and its work will show up here.</p>}
    </main>
  );
}
