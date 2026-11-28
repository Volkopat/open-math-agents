import Mathlib

/-!
# OEIS A007097: primeth recurrence, product of logarithms

Source: https://oeis.org/A007097
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(0) = 1`, `a(n+1) = ` the `a(n)`-th prime: `1, 2, 3, 5, 11, 31, 127, …`. Conjecture (OEIS
entry): `log(a(1)) · log(a(2)) ⋯ log(a(n)) ~ a(n)`.

Conventions:
* The `m`-th prime (`m ≥ 1`) is `Nat.nth Nat.Prime (m - 1)`.
* `~` is `Asymptotics.IsEquivalent` as `n → ∞`.
-/

namespace OMA.S_oeis_a007097

open Filter Asymptotics

/-- The primeth recurrence. -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.nth Nat.Prime (a n - 1)

/-- `∏_{i=1}^{n} log a(i) ~ a(n)`. -/
theorem main : IsEquivalent atTop
    (fun n : ℕ => ∏ i ∈ Finset.Icc 1 n, Real.log (a i)) (fun n => (a n : ℝ)) := by
  sorry

end OMA.S_oeis_a007097
