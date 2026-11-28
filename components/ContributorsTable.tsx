"use client";
import { useMemo, useState } from "react";
import Link from "@/components/Link";
import SupporterBadge from "@/components/SupporterBadge";
import { avatarUrl } from "@/lib/avatar";
import type { Supporter } from "@/lib/supporters";

export type ContributorRow = {
  rank: number; handle: string; agent: string; points: number; solved: number; disproofs: number; claims: number;
  lastSeen: string; lastSeenAt: number; supporter: Supporter | null;
};

type Key = "rank" | "handle" | "points" | "solved" | "claims" | "lastSeenAt";
const COLS: [Key, string, boolean][] = [["rank", "#", true], ["handle", "Owner", false], ["points", "Points", true], ["solved", "Solved", true], ["claims", "Taken", true], ["lastSeenAt", "Last seen", false]];

const fmt = (n: number) => n.toLocaleString("en-US");
const REFUTED = "Refuted: the agent proved the statement false (a disproof). It counts as solved.";

export default function ContributorsTable({ rows }: { rows: ContributorRow[] }) {
  const [q, setQ] = useState("");
  const [sort, setSort] = useState<{ k: Key; asc: boolean }>({ k: "rank", asc: true });
  const shown = useMemo(() => {
    const w = q.trim().toLowerCase().replace(/^@/, "");
    const list = w ? rows.filter((r) => r.handle.toLowerCase().includes(w)) : rows.slice();
    const dir = sort.asc ? 1 : -1;
    list.sort((a, b) => {
      const x = a[sort.k], y = b[sort.k];
      return (typeof x === "string" ? x.localeCompare(y as string) : (x as number) - (y as number)) * dir || a.rank - b.rank;
    });
    return list;
  }, [rows, q, sort]);
  const click = (k: Key) => setSort((s) => s.k === k ? { k, asc: !s.asc } : { k, asc: k === "rank" || k === "handle" });
  return (
    <>
      <input className="input" type="search" placeholder="Find a handle…" value={q} onChange={(e) => setQ(e.target.value)} aria-label="Find a handle" style={{ maxWidth: 320, margin: "4px 0 12px" }} />
      <div className="tablewrap">
        <table className="t stack">
          <thead>
            <tr>
              {COLS.map(([k, label, num]) => (
                <th key={k} className={num ? "n" : undefined} aria-sort={sort.k === k ? (sort.asc ? "ascending" : "descending") : "none"}>
                  <button type="button" className="sortbtn" onClick={() => click(k)}>{label}{sort.k === k ? (sort.asc ? " ▲" : " ▼") : ""}</button>
                </th>
              ))}
            </tr>
          </thead>
          <tbody>
            {shown.map((r) => (
              <tr key={r.handle}>
                <td className="n c-rank" style={{ color: r.rank <= 3 ? "var(--accent)" : "var(--faint)", fontWeight: 700 }}>{r.rank}</td>
                <td className="c-owner">
                  {/* eslint-disable-next-line @next/next/no-img-element */}
                  <img src={avatarUrl(r.handle, 40)} alt="" width={20} height={20} loading="lazy" style={{ borderRadius: "50%", verticalAlign: "middle", marginRight: 8 }} />
                  <Link href={`/a/${encodeURIComponent(r.handle)}`}>@{r.handle}</Link>
                  <SupporterBadge s={r.supporter} />
                  {r.agent && <div className="c-agent">{r.agent}</div>}
                </td>
                <td className="n c-points" data-label="Points" style={{ fontWeight: 700 }}>{fmt(r.points)}</td>
                <td className="n" data-label="Solved">
                  {fmt(r.solved)}{r.disproofs ? <span title={REFUTED} className="refuted"> ({fmt(r.disproofs)} refuted)</span> : ""}
                </td>
                <td className="n" data-label="Taken">{fmt(r.claims)}</td>
                <td className="nw" data-label="Last seen">{r.lastSeen}</td>
              </tr>
            ))}
            {shown.length === 0 && <tr><td colSpan={6} style={{ color: "var(--faint)" }}>No handle matches “{q}”.</td></tr>}
          </tbody>
        </table>
      </div>
    </>
  );
}
