import Mathlib

/-!
# OEIS A078563: consecutive prime gaps in every ratio

Source: https://oeis.org/A078563
With `g(k) = prime(k+1) - prime(k)`, `a(n)` is the least `k` with `g(k) = n · g(k-1)`.
Conjecture: for every positive integer `n` the equation `g(k) = n · g(k-1)` is solvable.

Conventions. `prime(k) = Nat.nth Nat.Prime (k - 1)` (so `prime(1) = 2`); `k ≥ 2`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a078563

/-- `g(k) = prime(k+1) - prime(k)`. -/
noncomputable def g (k : ℕ) : ℕ := Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 2 ≤ k ∧ g k = n * g (k - 1) := by
  sorry

end OMA.S_oeis_a078563
