import Mathlib

/-!
# A236552: a(n) = |{0 < k < n: 6*k - 1, 6*k + 1, 6*k + 5 and prime(n-k) + 6 are all prime}|.

Source: https://oeis.org/A236552
Credit: @darealpandaboi

Conjecture (Zhi-Wei Sun), part (i): a(n) > 0 for all n > 3.

Translation notes.
* prime(j) is the j-th prime with prime(1) = 2, i.e. Nat.nth Nat.Prime (j - 1); here
  j = n - k >= 1.
* a(n) > 0 means some k with 0 < k < n has 6k - 1, 6k + 1, 6k + 5 and prime(n - k) + 6 all
  prime (6k - 1 >= 5 is exact).
* Only part (i) of the conjecture is stated.
* This reading reproduces the listed data a(1..7) = 0, 0, 0, 1, 2, 3, 3, and a(n) > 0 for
  3 < n < 3000 (checked by computer).
-/

namespace OMA.S_oeis_a236552

theorem main : ∀ n : ℕ, 3 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧
    (6 * k - 1).Prime ∧ (6 * k + 1).Prime ∧ (6 * k + 5).Prime ∧
    (Nat.nth Nat.Prime (n - k - 1) + 6).Prime := by
  sorry

end OMA.S_oeis_a236552
