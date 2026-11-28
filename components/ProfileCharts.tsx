import type { ProfileStats, Bar } from "@/lib/profilestats";

/**
 * The charts of a contributor page, inline SVG (no chart library), from lib/profilestats.ts. Hover any mark for its
 * value (SVG <title>). Each line and bar chart is drawn twice, at a desktop and a phone width, and CSS shows one:
 * an SVG scales as a whole, so one drawing could not keep its labels readable at both sizes.
 */
const n = (x: number) => x.toLocaleString("en-US");
const DAYMS = 86_400_000;
const dayLabel = (t: number) => new Date(t).toLocaleDateString("en-GB", { day: "numeric", month: "short", timeZone: "UTC" });
const hm = (t: number) => new Date(t).toISOString().slice(11, 16);

/** Round tick values from 0 to at least max. */
export function niceTicks(max: number, count = 4): number[] {
  if (max <= 0) return [0, 1];
  const raw = max / count, mag = 10 ** Math.floor(Math.log10(raw));
  const step = [1, 2, 2.5, 5, 10].map((m) => m * mag).find((s) => s >= raw) ?? 10 * mag;
  const top = Math.ceil(max / step) * step;
  return Array.from({ length: Math.round(top / step) + 1 }, (_, i) => +(i * step).toFixed(6));
}

function Axes({ W, H, m, ticks, y }: { W: number; H: number; m: { l: number; r: number; t: number; b: number }; ticks: number[]; y: (v: number) => number }) {
  return (
    <g className="axes">
      {ticks.map((v) => (
        <g key={v}>
          <line x1={m.l} x2={W - m.r} y1={y(v)} y2={y(v)} className={v === 0 ? "base" : "grid"} />
          <text x={m.l - 8} y={y(v) + 4} textAnchor="end">{n(v)}</text>
        </g>
      ))}
    </g>
  );
}

function CumulativeSvg({ s, W, H }: { s: ProfileStats["cumulative"]; W: number; H: number }) {
  const m = { l: W < 400 ? 44 : 52, r: 16, t: 16, b: 30 };
  const t0 = s[0].t, t1 = Math.max(s[s.length - 1].t, t0 + 3_600_000);
  const ticks = niceTicks(s[s.length - 1].total, 4);
  const yMax = ticks[ticks.length - 1];
  const x = (t: number) => m.l + ((t - t0) / (t1 - t0)) * (W - m.l - m.r);
  const y = (v: number) => H - m.b - (v / yMax) * (H - m.t - m.b);
  // A step line: the total only changes when a proof is checked.
  let d = `M${x(t0)},${y(0)}`;
  for (const p of s) d += `H${x(p.t).toFixed(1)}V${y(p.total).toFixed(1)}`;
  const area = `${d}V${y(0)}Z`;
  const nx = W < 400 ? 3 : 4;
  const short = t1 - t0 < 4 * DAYMS;
  const last = s[s.length - 1];
  return (
    <svg viewBox={`0 0 ${W} ${H}`} className="pchart-svg" role="img" aria-label={`Points over time, reaching ${n(last.total)}`}>
      <Axes W={W} H={H} m={m} ticks={ticks} y={y} />
      {Array.from({ length: nx }, (_, i) => t0 + ((t1 - t0) * i) / (nx - 1)).map((t, i) => (
        <text key={i} x={x(t)} y={H - 8} textAnchor={i === 0 ? "start" : i === nx - 1 ? "end" : "middle"} className="tick">{dayLabel(t)}{short ? ` ${hm(t)}` : ""}</text>
      ))}
      <path d={area} className="area" />
      <path d={d} className="line" />
      {s.map((p, i) => (
        <circle key={i} cx={x(p.t)} cy={y(p.total)} r={s.length > 60 ? 6 : 9} className="hit">
          <title>{`${dayLabel(p.t)} ${hm(p.t)} UTC · +${n(p.gained)} for ${p.id} · ${n(p.total)} points in all`}</title>
        </circle>
      ))}
      <circle cx={x(last.t)} cy={y(last.total)} r="4.5" className="end" />
      <text x={x(last.t) - 8} y={Math.max(m.t + 12, y(last.total) - 9)} textAnchor="end" className="direct">{n(last.total)}</text>
    </svg>
  );
}

function PerDaySvg({ s, bucket, W, H }: { s: ProfileStats["perDay"]; bucket: ProfileStats["bucket"]; W: number; H: number }) {
  const m = { l: W < 400 ? 36 : 44, r: 8, t: 18, b: 30 };
  const ticks = niceTicks(Math.max(...s.map((b) => b.value)), 4);
  const yMax = ticks[ticks.length - 1];
  const y = (v: number) => H - m.b - (v / yMax) * (H - m.t - m.b);
  const slot = (W - m.l - m.r) / s.length;
  const bw = Math.min(56, Math.max(1.5, slot - 2));
  const every = Math.ceil(s.length / (W < 400 ? 4 : 7));
  const labelled = s.length <= (W < 400 ? 7 : 14);
  return (
    <svg viewBox={`0 0 ${W} ${H}`} className="pchart-svg" role="img" aria-label={`Checked proofs per ${bucket}`}>
      <Axes W={W} H={H} m={m} ticks={ticks} y={y} />
      {s.map((b, i) => {
        const cx = m.l + slot * i + slot / 2, top = y(b.value), base = y(0), r = Math.min(4, bw / 2, base - top);
        const path = b.value ? `M${cx - bw / 2},${base}V${top + r}Q${cx - bw / 2},${top} ${cx - bw / 2 + r},${top}H${cx + bw / 2 - r}Q${cx + bw / 2},${top} ${cx + bw / 2},${top + r}V${base}Z` : "";
        const label = `${bucket === "week" ? "Week of " : ""}${dayLabel(Date.parse(b.start))}`;
        return (
          <g key={b.start}>
            {path && <path d={path} className="bar" />}
            {labelled && b.value > 0 && <text x={cx} y={top - 5} textAnchor="middle" className="direct">{n(b.value)}</text>}
            {i % every === 0 && <text x={cx} y={H - 8} textAnchor="middle" className="tick">{dayLabel(Date.parse(b.start))}</text>}
            <rect x={m.l + slot * i} y={m.t} width={slot} height={H - m.t - m.b} className="hitr"><title>{`${label}: ${n(b.value)} checked proof${b.value === 1 ? "" : "s"}`}</title></rect>
          </g>
        );
      })}
    </svg>
  );
}

function HeatSvg({ h, W, small }: { h: ProfileStats["heat"]; W: number; small: boolean }) {
  const lw = small ? 50 : 104, top = 4, ch = small ? 15 : 24, gap = small ? 1.5 : 3;
  const cw = (W - lw) / 24;
  const H = top + h.rows.length * ch + 22;
  const hours = small ? [0, 6, 12, 18] : [0, 3, 6, 9, 12, 15, 18, 21];
  return (
    <svg viewBox={`0 0 ${W} ${H}`} className="pchart-svg" role="img" aria-label="Activity by day and UTC hour">
      {h.rows.map((r, ri) => (
        <g key={ri}>
          <text x={lw - 8} y={top + ri * ch + ch / 2 + 4} textAnchor="end" className="tick">{small ? r.short : r.label}</text>
          {h.cells[ri].map((v, hi) => (
            <rect key={hi} x={lw + hi * cw + gap / 2} y={top + ri * ch + gap / 2} width={cw - gap} height={ch - gap} rx={small ? 2 : 3}
              className={v ? "cell" : "cell zero"} style={v ? { fillOpacity: 0.14 + 0.86 * (v / h.max) } : undefined}>
              <title>{`${r.label}, ${String(hi).padStart(2, "0")}:00–${String(hi).padStart(2, "0")}:59 UTC: ${n(v)} event${v === 1 ? "" : "s"}`}</title>
            </rect>
          ))}
        </g>
      ))}
      {hours.map((hr) => <text key={hr} x={lw + hr * cw + 1} y={H - 6} className="tick">{String(hr).padStart(2, "0")}h</text>)}
    </svg>
  );
}

function HBars({ bars, unit = "proof" }: { bars: Bar[]; unit?: string }) {
  const max = Math.max(1, ...bars.map((b) => b.value));
  const total = bars.reduce((s, b) => s + b.value, 0);
  return (
    <div className="hbars">
      {bars.map((b) => {
        const pct = total ? Math.round((b.value / total) * 100) : 0;
        const tip = `${b.label}: ${n(b.value)} ${unit}${b.value === 1 ? "" : "s"} (${pct}%)${b.note ? `, ${b.note}` : ""}`;
        return (
          <div key={b.label} className={b.rest ? "hbar rest" : "hbar"}>
            <span className="hl">{b.label}{b.note ? <small> · {b.note}</small> : null}</span>
            <svg viewBox="0 0 100 10" preserveAspectRatio="none" className="ht" role="img" aria-label={tip}>
              <rect x="0" y="0" width="100" height="10" className="track" />
              {b.value > 0 && <rect x="0" y="0" width={Math.max(1.2, (b.value / max) * 100)} height="10" className="fill" />}
              <title>{tip}</title>
            </svg>
            <b className="hv">{n(b.value)}</b>
          </div>
        );
      })}
    </div>
  );
}

function Both({ lg, sm }: { lg: React.ReactNode; sm: React.ReactNode }) {
  return <><div className="vw-lg">{lg}</div><div className="vw-sm">{sm}</div></>;
}

export default function ProfileCharts({ s, handle }: { s: ProfileStats; handle: string }) {
  const proofs = s.cumulative.length;
  if (!proofs && !s.heat.total) return null;
  const best = s.perDay.reduce((a, b) => (b.value > a.value ? b : a), { start: "", value: 0 });
  const peak = s.heat.cells.length ? s.heat.cells.reduce((acc, row) => row.map((v, i) => acc[i] + v), new Array<number>(24).fill(0)) : [];
  const peakHour = peak.indexOf(Math.max(...peak));
  const pts = s.cumulative[proofs - 1]?.total ?? 0;
  return (
    <section className="pdash" aria-label={`Charts of @${handle}'s activity`}>
      <div className="h2" style={{ marginBottom: 12 }}><h2>In numbers</h2><span>UTC · hover any mark for its value</span></div>
      {proofs > 0 && (
        <div className="pdash-2">
          <figure className="pchart">
            <figcaption><h3 className="ph">Points over time</h3><p className="sub">{n(pts)} points from {n(proofs)} checked proof{proofs === 1 ? "" : "s"}; the line steps up at each one{proofs > 1 ? `, ${(pts / proofs).toFixed(1)} points per proof on average` : ""}.</p></figcaption>
            <Both lg={<CumulativeSvg s={s.cumulative} W={520} H={230} />} sm={<CumulativeSvg s={s.cumulative} W={340} H={210} />} />
          </figure>
          <figure className="pchart">
            <figcaption><h3 className="ph">Checked proofs per {s.bucket}</h3><p className="sub">{s.perDay.length === 1 ? "All on one day" : <>Best {s.bucket}: {n(best.value)} on {dayLabel(Date.parse(best.start))}</>}; {s.bucket === "week" ? "weeks" : "days"} without a proof show as gaps.</p></figcaption>
            <Both lg={<PerDaySvg s={s.perDay} bucket={s.bucket} W={520} H={230} />} sm={<PerDaySvg s={s.perDay} bucket={s.bucket} W={340} H={210} />} />
          </figure>
        </div>
      )}
      {s.heat.total > 0 && (
        <figure className="pchart">
          <figcaption><h3 className="ph">When they work</h3><p className="sub">Every event (taken, sent, checked, handed back) by {s.heat.mode === "date" ? "day" : "day of the week"} and hour of the day, UTC; darker is busier. {n(s.heat.total)} events, busiest hour {String(peakHour).padStart(2, "0")}:00 UTC.</p></figcaption>
          <Both lg={<HeatSvg h={s.heat} W={1060} small={false} />} sm={<HeatSvg h={s.heat} W={340} small />} />
          <div className="heatkey" aria-hidden="true"><span>Fewer</span>{[0.14, 0.35, 0.57, 0.78, 1].map((o) => <i key={o} style={{ opacity: o }} />)}<span>More</span></div>
        </figure>
      )}
      {proofs > 0 && (
        <div className="pdash-3">
          <figure className="pchart">
            <figcaption><h3 className="ph">What the proofs are</h3><p className="sub">An open problem counts as solved only once its statement is confirmed by review.</p></figcaption>
            <HBars bars={s.byOutcome} />
          </figure>
          <figure className="pchart">
            <figcaption><h3 className="ph">By field</h3><p className="sub">Primary field of each problem (a step: its problem's).</p></figcaption>
            <HBars bars={s.byField} />
          </figure>
          <figure className="pchart">
            <figcaption><h3 className="ph">By source</h3><p className="sub">Where the problem was collected from.</p></figcaption>
            <HBars bars={s.bySource} />
          </figure>
        </div>
      )}
    </section>
  );
}
