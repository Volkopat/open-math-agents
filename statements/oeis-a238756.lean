import Mathlib

/-!
# A238756: Number of ordered ways to write n = k + m (k > 0 and m > 0) such that 2*k + 1, prime(prime(k)) - prime(k) + 1 and prime(prime(m)) - prime(m) + 1 are all prime.

Source: https://oeis.org/A238756
Credit: @luciusacarr

Data: 0, 1, 2, 3, 3, 2, 3, 3, 3, 4, 2, 5, 4, 3, 6, 4, 4, 3, 3, 6, ... (offset 1).

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 for all n > 1 (verified for n up to 10^7).
`main` states it.

Reading of the source:
* `prime(k)` is the k-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`; since
  `prime(prime(k)) ≥ prime(k)`, the subtraction is exact in ℕ.
* a(n) > 0 means some `k, m > 0` with `k + m = n` satisfy the three conditions. The first 25
  data values were recomputed from this definition.
-/

namespace OMA.S_oeis_a238756

/-- The k-th prime, 1-indexed: `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

theorem main :
    -- a(n) > 0 for all n > 1.
    ∀ n : ℕ, 1 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k + m ∧ (2 * k + 1).Prime ∧
      (prime (prime k) - prime k + 1).Prime ∧ (prime (prime m) - prime m + 1).Prime := by
  sorry

end OMA.S_oeis_a238756
