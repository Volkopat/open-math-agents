import Mathlib

/-!
# A000769: no-three-in-line placements of `2n` points

Source: https://oeis.org/A000769
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A000769): `a(n) = 0` for all sufficiently large `n`, where `a(n)` is the
number of inequivalent ways of placing `2n` points on an `n × n` grid so that no 3 are in a line.

Conventions:
* `a(n) = 0` iff there is no such placement at all (equivalence under the grid's symmetries does
  not affect existence). "In a line": collinear in `ℝ²` (any direction).
* The grid is `{0, …, n-1}²`.
-/

namespace OMA.S_oeis_a000769

/-- Three grid points are collinear (zero cross product). -/
def Collinear3 (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

/-- `S` has no three collinear points. -/
def NoThreeInLine (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r → ¬ Collinear3 p q r

theorem main :
    ∀ᶠ n : ℕ in Filter.atTop, ¬ ∃ S : Finset (ℤ × ℤ),
      (∀ p ∈ S, 0 ≤ p.1 ∧ p.1 < n ∧ 0 ≤ p.2 ∧ p.2 < n) ∧ S.card = 2 * n ∧ NoThreeInLine S := by
  sorry

end OMA.S_oeis_a000769
