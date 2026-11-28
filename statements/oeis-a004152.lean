import Mathlib

/-!
# OEIS A004152: digit sum of n!

Source: https://oeis.org/A004152
`a n` is the sum of the decimal digits of `n!`. Conjecture (heuristic, from Stirling's
formula and A027868): `a(n) = c₁ n log n - (c₁ + 9/8) n + O(log n)` with
`c₁ = 9 / (2 log 10)`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a004152

open Filter Asymptotics Real

/-- Sum of the decimal digits of `n!`. -/
def a (n : ℕ) : ℕ := (Nat.digits 10 n.factorial).sum

/-- `c₁ = 9 / (2 log 10)`. -/
noncomputable def c₁ : ℝ := 9 / (2 * log 10)

theorem main :
    (fun n : ℕ => (a n : ℝ) - (c₁ * n * log n - (c₁ + 9 / 8) * n)) =O[atTop]
      fun n : ℕ => log (n : ℝ) := by
  sorry

end OMA.S_oeis_a004152
