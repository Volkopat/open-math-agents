/**
 * The series behind the charts of a contributor page (components/ProfileCharts.tsx). Pure: the caller passes `info`,
 * which says what each problem or step counts as (outcomeOf) and its fields and source. All dates are UTC.
 */
import type { Outcome } from "@/lib/outcome";

export type Info = { outcome: Outcome; fields: string[]; source: string | null };
export type StatsInput = {
  solutions: { problem_id: string; polarity: string; points: number; created_at: string }[];
  events: { kind: string; problem_id: string; created_at: string }[];
  info: (id: string) => Info | null;
};
/** A bar of a breakdown; `rest` marks the "Other" bar, which folds `note` more labels. */
export type Bar = { label: string; value: number; note?: string; rest?: boolean };
export type ProfileStats = {
  /** One point per checked proof, oldest first: time and points so far. */
  cumulative: { t: number; total: number; id: string; gained: number }[];
  /** Checked proofs per UTC day (or per week, from 90 days on), every bucket from the first to the last. */
  perDay: { start: string; value: number }[];
  bucket: "day" | "week";
  byOutcome: Bar[];
  byField: Bar[];
  bySource: Bar[];
  /** Events per (row, UTC hour): rows are dates when the activity spans at most 14 days, weekdays otherwise. */
  heat: { rows: { label: string; short: string }[]; cells: number[][]; mode: "date" | "weekday"; max: number; total: number };
};

const DAY = 86_400_000;
const OUTCOME_LABEL: [Outcome, string][] = [
  ["open", "Open problem solved"],
  ["pending", "Open problem, statement being verified"],
  ["misstated", "Mis-stated formal version"],
  ["known", "Known result formalized"],
  ["warmup", "Warm-up"],
  ["step", "Reduction step"],
];
const WEEKDAYS = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];

/** The largest `top` entries, the rest folded into one "Other" bar. */
export function topBars(counts: Map<string, number>, top = 7, other = "Other"): Bar[] {
  const all = [...counts.entries()].sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]));
  const head: Bar[] = all.slice(0, all.length > top + 1 ? top : top + 1).map(([label, value]) => ({ label, value }));
  const rest = all.slice(head.length);
  if (rest.length) head.push({ label: other, value: rest.reduce((s, [, v]) => s + v, 0), note: `${rest.length} more`, rest: true });
  return head;
}

export function profileStats(inp: StatsInput): ProfileStats {
  const sol = [...inp.solutions].sort((a, b) => a.created_at.localeCompare(b.created_at));
  let total = 0;
  const cumulative = sol.map((s) => ({ t: Date.parse(s.created_at), total: (total += s.points), id: s.problem_id, gained: s.points }));

  // Proofs per day (or week).
  let perDay: ProfileStats["perDay"] = [];
  let bucket: ProfileStats["bucket"] = "day";
  if (sol.length) {
    const d0 = Math.floor(Date.parse(sol[0].created_at) / DAY), d1 = Math.floor(Date.parse(sol[sol.length - 1].created_at) / DAY);
    bucket = d1 - d0 + 1 > 90 ? "week" : "day";
    const size = bucket === "week" ? 7 : 1;
    const counts = new Map<number, number>();
    for (const s of sol) { const k = Math.floor((Math.floor(Date.parse(s.created_at) / DAY) - d0) / size); counts.set(k, (counts.get(k) ?? 0) + 1); }
    const nb = Math.floor((d1 - d0) / size) + 1;
    perDay = Array.from({ length: nb }, (_, k) => ({ start: new Date((d0 + k * size) * DAY).toISOString().slice(0, 10), value: counts.get(k) ?? 0 }));
  }

  // Breakdowns.
  const oc = new Map<Outcome, number>(), fc = new Map<string, number>(), sc = new Map<string, number>();
  for (const s of sol) {
    const i = inp.info(s.problem_id);
    const o = i?.outcome ?? "step";
    oc.set(o, (oc.get(o) ?? 0) + 1);
    const f = i?.fields[0] ?? "No field listed";
    fc.set(f, (fc.get(f) ?? 0) + 1);
    const src = i?.source ?? "No source listed";
    sc.set(src, (sc.get(src) ?? 0) + 1);
  }
  const byOutcome = OUTCOME_LABEL.filter(([o]) => oc.get(o) || o === "open").map(([o, label]) => ({ label, value: oc.get(o) ?? 0 }));

  // Heatmap of every event (taken, sent, proved, handed back...) by UTC hour.
  const times = inp.events.map((e) => Date.parse(e.created_at)).filter(Number.isFinite).sort((a, b) => a - b);
  let heat: ProfileStats["heat"] = { rows: [], cells: [], mode: "date", max: 0, total: 0 };
  if (times.length) {
    const d0 = Math.floor(times[0] / DAY), d1 = Math.floor(times[times.length - 1] / DAY);
    const mode = d1 - d0 + 1 <= 14 ? "date" : "weekday";
    const fmt = (t: number, o: Intl.DateTimeFormatOptions) => new Date(t).toLocaleDateString("en-GB", { ...o, timeZone: "UTC" });
    const rows = mode === "date"
      ? Array.from({ length: d1 - d0 + 1 }, (_, k) => ({ label: fmt((d0 + k) * DAY, { weekday: "short", day: "numeric", month: "short" }), short: fmt((d0 + k) * DAY, { day: "numeric", month: "short" }) }))
      : WEEKDAYS.map((w) => ({ label: w, short: w }));
    const cells = rows.map(() => new Array<number>(24).fill(0));
    for (const t of times) {
      const d = new Date(t);
      const r = mode === "date" ? Math.floor(t / DAY) - d0 : (d.getUTCDay() + 6) % 7;
      cells[r][d.getUTCHours()]++;
    }
    heat = { rows, cells, mode, max: Math.max(...cells.flat()), total: times.length };
  }
  return { cumulative, perDay, bucket, byOutcome, byField: topBars(fc, 7, "Other fields"), bySource: topBars(sc, 6, "Other sources"), heat };
}
