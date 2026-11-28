import Mathlib

/-!
# A236470: a(n) = |{0 < k < n: p = prime(k) + phi(n-k), p + 2 and prime(p) + 2 are all prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236470
Credit: @luciusacarr

Data: 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 2, 1, 2, 1, 1, 1, 1, ... (offset 1).

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 for all n > 948 (verified for n up to 50000).
`main` states it.

Reading of the source:
* `prime(k)` is the k-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`, and `phi`
  is `Nat.totient`.
* a(n) > 0 means some `0 < k < n` has `p = prime(k) + phi(n-k)`, `p + 2` and `prime(p) + 2` all
  prime. The first 30 data values were recomputed from this definition.
-/

namespace OMA.S_oeis_a236470

/-- The k-th prime, 1-indexed: `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

theorem main :
    -- a(n) > 0 for all n > 948.
    ∀ n : ℕ, 948 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧
      (prime k + Nat.totient (n - k)).Prime ∧ (prime k + Nat.totient (n - k) + 2).Prime ∧
      (prime (prime k + Nat.totient (n - k)) + 2).Prime := by
  sorry

end OMA.S_oeis_a236470
