import Mathlib

/-!
# A233547: a(n) = |{0 < k < n/2: phi(k)*phi(n-k) - 1 and phi(k)*phi(n-k) + 1 are both prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A233547
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 5.
(ii) For any n > 3, sigma(k)*phi(n-k) - 1 and sigma(k)*phi(n-k) + 1 are both prime for some
0 < k < n.
(iii) For any n > 5 not equal to 35, there is a positive integer k < n such that
phi(k)*phi(n-k) - 1 is a Sophie Germain prime.

Formalization notes:
* phi = `Nat.totient`, sigma = `ArithmeticFunction.sigma 1`, prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2). "x is a square" is `IsSquare x`.
* "k < n/2" is stated as 2k < n. A Sophie Germain prime is a prime q with 2q + 1 prime.
  Products that are 0 make "x - 1" equal 0 in ℕ, which is not prime, as -1 is not prime.
* Controls (computed): a(1..30) = 0, 0, 0, 0, 0, 1, 2, 1, 3, 4, 3, 2, 3, 2, 3, 1, 1, 2, 1, 5, 2, 3, 1,
  2, 1, 1, 3, 4, 5, 4, as in the entry; all three parts hold for n < 300.
-/

namespace OMA.S_oeis_a233547

open ArithmeticFunction

/-- A233547(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k => 2 * k < n ∧
    (Nat.totient k * Nat.totient (n - k) - 1).Prime ∧
    (Nat.totient k * Nat.totient (n - k) + 1).Prime).card

/-- The conjecture of the entry (all parts listed above). -/
theorem main :
    (∀ n : ℕ, 5 < n → 0 < a n) ∧
      (∀ n : ℕ, 3 < n → ∃ k, 0 < k ∧ k < n ∧ (sigma 1 k * Nat.totient (n - k) - 1).Prime ∧
        (sigma 1 k * Nat.totient (n - k) + 1).Prime) ∧
      ∀ n : ℕ, 5 < n → n ≠ 35 → ∃ k, 0 < k ∧ k < n ∧
        (Nat.totient k * Nat.totient (n - k) - 1).Prime ∧
        (2 * (Nat.totient k * Nat.totient (n - k) - 1) + 1).Prime := by
  sorry

end OMA.S_oeis_a233547
