import Mathlib

/-!
# OEIS A014201: lattice points in `x² + xy + y² ≤ n`

Source: https://oeis.org/A014201
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of integer solutions of `x² + xy + y² ≤ n` other than `(0, 0)`. Conjecture
(Cloitre, 2012): `a(n) = 2 (π/√3) n + O(n^(1/4 + ε))` for every `ε > 0`.
-/

namespace OMA.S_oeis_a014201

open Asymptotics Filter

/-- Number of `(x, y) ≠ (0, 0)` with `x² + xy + y² ≤ n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {v : ℤ × ℤ | v ≠ (0, 0) ∧ v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2 ≤ n}.ncard

/-- `a(n) - (2π/√3) n = O(n^(1/4 + ε))` for every `ε > 0`. -/
theorem main : ∀ ε : ℝ, 0 < ε →
    (fun n : ℕ => (a n : ℝ) - 2 * (Real.pi / Real.sqrt 3) * n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

end OMA.S_oeis_a014201
