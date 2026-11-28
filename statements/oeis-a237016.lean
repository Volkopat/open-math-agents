import Mathlib

/-!
# A237016: a(n) = |{0 < k < n: phi(k)*sigma(n-k) is a square}|, where phi(.) is Euler's totient function and sigma(j) is the sum of all positive divisors of j.

Source: https://oeis.org/A237016
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 except for n = 1, 7, 17.
(ii) If n > 5, then phi(k)*sigma(n-k) + 1 is a square for some 0 < k < n.
(iii) If n > 309, then there is a positive integer k < n/2 such that sigma(k)*sigma(n-k) is a square.

Formalization notes:
* phi = `Nat.totient`, sigma = `ArithmeticFunction.sigma 1`, prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2). "x is a square" is `IsSquare x`.
* (i) is stated as: for n ≥ 1, a(n) = 0 iff n ∈ {1, 7, 17}. "k < n/2" is stated as 2k < n.
* Controls (computed): a(1..30) = 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 3, 1, 4, 2, 2, 1, 0, 1, 2, 2, 2, 2, 6,
  4, 2, 2, 4, 2, 2, 4, as in the entry; (i) and (ii) hold for n < 300, (iii) for 310 ≤ n < 700.
-/

namespace OMA.S_oeis_a237016

open ArithmeticFunction

/-- A237016(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k => IsSquare (Nat.totient k * sigma 1 (n - k))).card

/-- The conjecture of the entry (all parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n = 1 ∨ n = 7 ∨ n = 17)) ∧
      (∀ n : ℕ, 5 < n → ∃ k, 0 < k ∧ k < n ∧ IsSquare (Nat.totient k * sigma 1 (n - k) + 1)) ∧
      ∀ n : ℕ, 309 < n → ∃ k, 0 < k ∧ 2 * k < n ∧ IsSquare (sigma 1 k * sigma 1 (n - k)) := by
  sorry

end OMA.S_oeis_a237016
