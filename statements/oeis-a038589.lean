import Mathlib

/-!
# A038589: Sizes of successive clusters in the hexagonal lattice A₂

Source: https://oeis.org/A038589
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of points of the hexagonal lattice `A₂` at squared distance `≤ n` from a
lattice point: `1, 7, 7, 13, 19, …` (offset `0`). Conjecture (Benoit Cloitre, OEIS, 2012):
`a(n) = (2π/√3) n + O(n^(1/4 + ε))`, as for the Gauss circle or Dirichlet divisor problems.

## Encoding

* In the basis of two unit vectors at `60°`, the squared norm is `x² + xy + y²`, so
  `a n = #{(x, y) ∈ ℤ² : x² + xy + y² ≤ n}` (values checked against the OEIS terms).
* For every `ε > 0`, `a(n) - (2π/√3) n = O(n^(1/4 + ε))` as `n → ∞` (`Asymptotics.IsBigO`).
-/

namespace OMA.S_oeis_a038589

open Asymptotics Filter

/-- `a n`: number of `A₂` lattice points of squared norm at most `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 ≤ n}

theorem main :
    ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ => (a n : ℝ) - 2 * Real.pi / Real.sqrt 3 * n) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

end OMA.S_oeis_a038589
