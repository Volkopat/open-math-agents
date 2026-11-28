import Mathlib

/-!
# A234200: a(n) = |{0 < k < n/2: k*phi(n-k) - 1 and k*phi(n-k) + 1 are both prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234200
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 4.
(ii) If n > 3 is different from 9 and 29, then k*sigma(n-k) - 1 and k*sigma(n-k) + 1 are both prime
for some 0 < k < n.

Formalization notes:
* phi = `Nat.totient`, sigma = `ArithmeticFunction.sigma 1`, prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2). "x is a square" is `IsSquare x`.
* "k < n/2" is stated as 2k < n. k*phi(n-k) - 1 is computed in ℕ; where k*phi(n-k) = 0 it gives
  0, which is not prime, matching -1 not being prime.
* Controls (computed): a(1..30) = 0, 0, 0, 0, 1, 2, 1, 3, 3, 2, 3, 2, 2, 3, 2, 2, 2, 1, 3, 2, 2, 2, 2,
  2, 4, 2, 2, 4, 4, 3, as in the entry; both parts hold for n < 300.
-/

namespace OMA.S_oeis_a234200

open ArithmeticFunction

/-- A234200(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k =>
    2 * k < n ∧ (k * Nat.totient (n - k) - 1).Prime ∧ (k * Nat.totient (n - k) + 1).Prime).card

/-- The conjecture of the entry (all parts listed above). -/
theorem main :
    (∀ n : ℕ, 4 < n → 0 < a n) ∧
      ∀ n : ℕ, 3 < n → n ≠ 9 → n ≠ 29 →
        ∃ k, 0 < k ∧ k < n ∧ (k * sigma 1 (n - k) - 1).Prime ∧ (k * sigma 1 (n - k) + 1).Prime := by
  sorry

end OMA.S_oeis_a234200
