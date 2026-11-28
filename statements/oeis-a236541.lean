import Mathlib

/-!
# A236541: Number of ways to write 2*n = k + m with 0 < k <= m such that prime(k) + m and k + prime(m) are both prime.

Source: https://oeis.org/A236541
Credit: @eltociear

`a(n)` (offset 1) counts the ways to write `2n = k + m` with `0 < k ≤ m` such that `prime(k) + m`
and `k + prime(m)` are both prime. The entry conjectures (Zhi-Wei Sun), as part (i):

  a(n) > 0 for all n > 31.

`main` states that such `k`, `m` exist for every `n > 31`. `prime(k)` is the `k`-th prime, `Nat.nth Nat.Prime (k - 1)`.
-/

namespace OMA.S_oeis_a236541

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Part (i) of the conjecture in OEIS A236541: `a(n) > 0` for all `n > 31`. -/
theorem main : ∀ n : ℕ, 31 < n → ∃ k m : ℕ, 0 < k ∧ k ≤ m ∧ k + m = 2 * n ∧
      (prime k + m).Prime ∧ (k + prime m).Prime := by
  sorry

end OMA.S_oeis_a236541
