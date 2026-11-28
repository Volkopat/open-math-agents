import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

namespace OMA.S_oeis_a058211

/-- Three points `p, q, r` in the plane `ℝ × ℝ` are collinear. -/
def collinear3 (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

/-- The number of distinct connecting lines of `S` passing through `p`, identified by their
point-sets `S ∩ ℓ` where `ℓ` is the line through `p` and some `q ∈ S \ {p}`. -/
noncomputable def numLinesThrough (S : Finset (ℝ × ℝ)) (p : ℝ × ℝ) : ℕ :=
  open Classical in
  ((S.erase p).image (fun q => S.filter (fun r => collinear3 p q r))).card

/-- Dirac's conjecture (OEIS A058211): for every finite non-collinear set `S` of points in the
Euclidean plane `ℝ × ℝ`, there exists a point `p ∈ S` lying on at least `|S| / 2` connecting
lines determined by `S` (i.e., `|S| ≤ 2 * numLinesThrough S p`). (Disproved; `|S| = 9` is the
smallest counterexample, the first term of A058211.) -/
theorem main : ∀ S : Finset (ℝ × ℝ),
    (∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, ¬ collinear3 p q r) →
    ∃ p ∈ S, S.card ≤ 2 * numLinesThrough S p := by
  sorry

end OMA.S_oeis_a058211
