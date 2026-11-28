import Mathlib

/-!
# A236619: a(n) = |{0 < k < n: prime(m)^3 + 2*m^3 and m^3 + 2*prime(m)^3 are both prime with m = 3*phi(k) + phi(n-k) - 1}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236619
Credit: @luciusacarr

Data: 0, 1, 2, 1, 0, 0, 0, ..., 0, 2, 1, 0, 0, 1, 2, ... (offset 1).

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 for every n = 90, 91, ... (verified for n up
to 100000). `main` states it.

Reading of the source:
* `prime(m)` is the m-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`, and `phi`
  is `Nat.totient`. For `0 < k < n`, `m = 3 phi(k) + phi(n-k) - 1 ≥ 3`, so the subtraction is
  exact in ℕ.
* a(n) > 0 means some `0 < k < n` makes both numbers prime. The first 7 data values were
  recomputed from this definition.
-/

namespace OMA.S_oeis_a236619

/-- The m-th prime, 1-indexed: `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

theorem main :
    -- a(n) > 0 for every n ≥ 90.
    ∀ n : ℕ, 90 ≤ n → ∃ k : ℕ, 0 < k ∧ k < n ∧
      let m := 3 * Nat.totient k + Nat.totient (n - k) - 1
      (prime m ^ 3 + 2 * m ^ 3).Prime ∧ (m ^ 3 + 2 * prime m ^ 3).Prime := by
  sorry

end OMA.S_oeis_a236619
