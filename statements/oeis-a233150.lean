import Mathlib

/-!
# A233150: Number of ways to write n = k + m (k, m > 0) with 2^k + prime(m) prime

Source: https://oeis.org/A233150
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A233150): a(n) > 0 except for n = 1, 2, 7.

Conventions:
* The sequence has offset 1. prime(m) is the m-th prime with prime(1) = 2
  (`Nat.nth Nat.Prime (m - 1)`).
* a(n) > 0 means that n = k + m with k, m > 0 and 2^k + prime(m) prime.
* "a(n) > 0 except for n = 1, 2, 7" is stated as: for n >= 1, a(n) > 0 if and only if n is not 1,
  2 or 7 (a(1) = a(2) = a(7) = 0 in the data).
-/

namespace OMA.S_oeis_a233150

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- Sun's conjecture on A233150: for `n >= 1`, `n = k + m` with `k, m > 0` and `2^k + prime(m)`
prime if and only if `n ∉ {1, 2, 7}`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((∃ k m : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧ (2 ^ k + prime m).Prime) ↔
      (n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 7)) := by
  sorry

end OMA.S_oeis_a233150
