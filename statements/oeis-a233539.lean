import Mathlib

/-!
# A233539: a(n) = |{0 < k < n-2: m - 1, m + 1, prime(m) - m and prime(m) + m are all prime with m = phi(k) + phi(n-k)/2}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A233539
Credit: @luciusacarr

Data: 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 3, 2, 4, 2, 4, 4, 2, 4, 3, 5, ... (offset 1).

The entry's comment (Zhi-Wei Sun) states a two-part conjecture. `main` states both parts, as a
conjunction, in the order the source gives them.

Conjecture: (i) a(n) > 0 for all n > 794.
(ii) For any integer n > 59, there is a positive integer k < n such that m = phi(k) + phi(n-k)/4
is an integer with prime(m) - m and prime(m) + m both prime.

Reading of the source:
* `prime(m)` is the m-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`, and `phi`
  is `Nat.totient`. Since `prime(m) > m`, `prime(m) - m` is exact in ℕ.
* In (i), `k < n - 2` makes `n - k > 2`, so `phi(n-k)` is even and `phi(n-k)/2` is exact.
  The first 30 data values were recomputed from this definition.
* In (ii), "m is an integer" is the requirement `4 ∣ phi(n-k)`, and then `m = phi(k) + phi(n-k)/4`.
-/

namespace OMA.S_oeis_a233539

/-- The m-th prime, 1-indexed: `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

theorem main :
    -- (i) a(n) > 0 for all n > 794.
    (∀ n : ℕ, 794 < n → ∃ k : ℕ, 0 < k ∧ k + 2 < n ∧
      let m := Nat.totient k + Nat.totient (n - k) / 2
      (m - 1).Prime ∧ (m + 1).Prime ∧ (prime m - m).Prime ∧ (prime m + m).Prime) ∧
    -- (ii) for n > 59 some 0 < k < n has m = phi(k) + phi(n-k)/4 an integer with
    -- prime(m) - m and prime(m) + m prime.
    (∀ n : ℕ, 59 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ 4 ∣ Nat.totient (n - k) ∧
      let m := Nat.totient k + Nat.totient (n - k) / 4
      (prime m - m).Prime ∧ (prime m + m).Prime) := by
  sorry

end OMA.S_oeis_a233539
