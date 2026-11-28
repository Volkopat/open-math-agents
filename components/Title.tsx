// Titles of Lean variants end in " — <the Lean name, humanized>" ("— conjecture 2", "— exact density", "— strongBSD").
// Shown as the problem's title plus a grey "Variant: …" tag, so that a list of variants reads as one problem
// with labelled forms instead of one title with a code word glued on.

const BSD: Record<string, string> = {
  "WeierstrassCurve.Affine.Rat.strongBSD": "strong form, over ℚ",
  "WeierstrassCurve.Affine.Rat.weakBSD": "rank only, over ℚ",
  "WeierstrassCurve.Affine.NumberField.strongBSD": "strong form, over a number field",
  "WeierstrassCurve.Affine.NumberField.weakBSD": "rank only, over a number field",
  "NavierStokes.navier_stokes_existence_and_smoothness_R3": "on ℝ³",
  "NavierStokes.navier_stokes_existence_and_smoothness_periodic": "periodic, on the torus",
};

export function splitTitle(id: string, title: string): { main: string; variant: string | null } {
  const m = /^(.*\S)\s+—\s+([^—$]{1,48})$/.exec(title);
  if (BSD[id]) return { main: m ? m[1] : title, variant: BSD[id] };
  // Only Lean declaration ids (they contain a dot) get the treatment: free-text titles from MathOverflow,
  // Wikipedia or arXiv may use a dash on purpose.
  if (!m || !id.includes(".") || /^(mo|mse|wp|arxiv)-/.test(id)) return { main: title, variant: null };
  const v = m[2].replace(/_/g, " ").replace(/([a-z])([A-Z])/g, "$1 $2").trim();
  return { main: m[1], variant: v };
}

export default function Title({ id, title }: { id: string; title: string }) {
  const { main, variant } = splitTitle(id, title);
  if (!variant) return <>{title}</>;
  return <>{main} <span className="variant">Variant: {variant}</span></>;
}
