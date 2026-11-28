import Mathlib

/-!
# A233918: a(n) = |{0 < k <= n/2: (phi(k) + phi(n-k))/2 is prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A233918
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 5.
(ii) If n > 5 is not equal to 19, then phi(k) + phi(n-k) - 1 and phi(k) + phi(n-k) + 1 are both
prime for some 0 < k < n.
(iii) If n > 5, then (phi(k)/2)^2 + (phi(n-k)/2)^2 is prime for some 0 < k < n.
(iv) If n > 8, then (sigma(k) + phi(n-k))/2 is prime for some 0 < k < n.

Formalization notes:
* phi = `Nat.totient`, sigma = `ArithmeticFunction.sigma 1`, prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2). "x is a square" is `IsSquare x`.
* A rational number such as (phi(k) + phi(n-k))/2 "is prime" only when it is an integer, so each
  halving is stated as: the quantity is even and its half is prime ((iii): both phi(k) and
  phi(n-k) even).
* "k <= n/2" is stated as 2k ≤ n.
* Controls (computed): a(1..30) = 0, 0, 0, 0, 0, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 4, 3, 2, 7, 1, 3, 3, 4,
  7, 2, 4, 5, 5, 5, 5, as in the entry; all four parts hold for n < 300.
-/

namespace OMA.S_oeis_a233918

open ArithmeticFunction

/-- A233918(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k => 2 * k ≤ n ∧ Even (Nat.totient k + Nat.totient (n - k)) ∧
    ((Nat.totient k + Nat.totient (n - k)) / 2).Prime).card

/-- The conjecture of the entry (all parts listed above). -/
theorem main :
    (∀ n : ℕ, 5 < n → 0 < a n) ∧
      (∀ n : ℕ, 5 < n → n ≠ 19 → ∃ k, 0 < k ∧ k < n ∧
        (Nat.totient k + Nat.totient (n - k) - 1).Prime ∧
        (Nat.totient k + Nat.totient (n - k) + 1).Prime) ∧
      (∀ n : ℕ, 5 < n → ∃ k, 0 < k ∧ k < n ∧ Even (Nat.totient k) ∧ Even (Nat.totient (n - k)) ∧
        ((Nat.totient k / 2) ^ 2 + (Nat.totient (n - k) / 2) ^ 2).Prime) ∧
      ∀ n : ℕ, 8 < n → ∃ k, 0 < k ∧ k < n ∧ Even (sigma 1 k + Nat.totient (n - k)) ∧
        ((sigma 1 k + Nat.totient (n - k)) / 2).Prime := by
  sorry

end OMA.S_oeis_a233918
