import Mathlib

/-!
# A233206: Number of ways to write n = k + m (0 < k <= m) with k! + prime(m) prime.

Source: https://oeis.org/A233206
Credit: @gblacher2

Formalizes the OEIS comment (Zhi-Wei Sun): "Conjecture: a(n) > 0 for all n > 3."

Conventions: `prime(m)` is the `m`-th prime, 1-indexed as in the OEIS (`prime(1) = 2`).
`a(n) > 0` means that some representation `n = k + m` with `0 < k ≤ m` has
`k! + prime(m)` prime.
-/

namespace OMA.S_oeis_a233206

/-- `prime m`: the `m`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- For every `n > 3`, `n = k + m` with `0 < k ≤ m` and `k! + prime(m)` prime. -/
theorem main : ∀ n : ℕ, 3 < n →
    ∃ k m : ℕ, 0 < k ∧ k ≤ m ∧ n = k + m ∧ (Nat.factorial k + prime m).Prime := by
  sorry

end OMA.S_oeis_a233206
