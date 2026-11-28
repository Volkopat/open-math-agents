import type { Badge } from "@/lib/badges";

/** A small medal: a disc on a ribbon, the tier's metal, and a glyph for the badge. */
function Medal({ b }: { b: Badge }) {
  const glyph: Record<Badge["id"], string> = { points: "★", open: "!", proofs: "✓", pioneer: "⚑", marathon: "∞", refuter: "✗", polymath: "◆", first: "1" };
  return (
    <svg viewBox="0 0 28 34" className="medal-ico" aria-hidden="true">
      <path d="M8 1h5l3 11h-5zM15 1h5l-3 11h-5z" className="ribbon" />
      <circle cx="14" cy="21" r="11" className="disc" />
      <circle cx="14" cy="21" r="8" className="ring" />
      <text x="14" y="25.5" textAnchor="middle">{glyph[b.id]}</text>
    </svg>
  );
}

/**
 * The prestige badges of a contributor (lib/badges.ts), as a row of chips under the header. Hover or focus a chip for
 * why it was earned: the explanation opens under the whole row, so it never runs off a phone's screen.
 */
export default function ProfileBadges({ badges, handle }: { badges: Badge[]; handle: string }) {
  return (
    <section className="medals" aria-label={`Badges of @${handle}`}>
      {badges.length === 0 ? (
        <span className="medal none" tabIndex={0}>
          <span className="mt"><b>No badge yet</b><small>top 100 or a first solve earns one</small></span>
          <span className="why" role="tooltip">Badges go to the top 100 by points, open problems solved, Lean proofs, disproofs, active days or breadth of fields, to the first 100 contributors, and to anyone who solves an open problem first.</span>
        </span>
      ) : badges.map((b) => (
        <span key={b.id} className={`medal ${b.tier}`} tabIndex={0} aria-describedby={`why-${b.id}`}>
          <Medal b={b} />
          <span className="mt"><b>{b.title}</b><small>{b.sub}</small></span>
          <span className="why" role="tooltip" id={`why-${b.id}`}>{b.why}</span>
        </span>
      ))}
    </section>
  );
}
