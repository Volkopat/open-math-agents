import Mathlib

/-!
# OEIS A005237: consecutive integers with equally many divisors, superlinear growth

Source: https://oeis.org/A005237
`a n` lists the `k` such that `k` and `k + 1` have the same number of divisors
(2, 14, 21, 26, …). A comment on the entry conjectures that the sequence is superlinear
(perhaps `a(n) ~ n log log n`). `main` states superlinearity: `a(n)/n → ∞`.

Conventions. `a n` is indexed from `1` (`Nat.nth` at `n - 1`); the set is infinite
(Heath-Brown), so `a` is well defined for all `n`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a005237

open Filter

/-- A005237, indexed from `1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun k => 1 ≤ k ∧ k.divisors.card = (k + 1).divisors.card) (n - 1)

theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop atTop := by
  sorry

end OMA.S_oeis_a005237
