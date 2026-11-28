import Mathlib

/-!
# Zeroes of a tricky function

Source: https://mathoverflow.net/questions/46445
Let `h(x) = ∑_{n=2}^{⌊√x⌋} (cot(xπ/n) + cot((x+2)π/n))/n`. The asker wants to show that there
is no `N` such that every open unit interval `(k, k+1)` with integer `k ≥ N` contains a zero
of `h`. `main` states this.

Conventions. `Real.cot` is used (it takes the value `0` at the poles of `cot`, where
`sin = 0`); a zero of `h` is a point `x` with `h x = 0`. `k` ranges over natural numbers.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_46445

open Real

/-- The function `h`. -/
noncomputable def h (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊√x⌋₊, (cot (x * π / n) + cot ((x + 2) * π / n)) / n

theorem main :
    ¬ ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∃ x : ℝ, (k : ℝ) < x ∧ x < k + 1 ∧ h x = 0 := by
  sorry

end OMA.S_mo_46445
