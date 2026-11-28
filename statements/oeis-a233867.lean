import Mathlib

/-!
# A233867: a(n) = |{0 < m < 2*n: m is a square with 2*n - 1 - phi(m) prime}|, where phi(.) is Euler's totient function (A000010).

Source: https://oeis.org/A233867
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 1.
(ii) For any odd number 2*n - 1 > 4, there is a positive integer k < 2*n such that
2*n - 1 - phi(k) and 2*n - 1 + phi(k) are both prime.

Formalization notes:
* phi = `Nat.totient`, sigma = `ArithmeticFunction.sigma 1`, prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2). "x is a square" is `IsSquare x`.
* For 0 < m < 2n, phi(m) ≤ 2n - 1, so 2n - 1 - phi(m) does not truncate in ℕ. "2n - 1 > 4" is
  n ≥ 3.
* Controls (computed): a(1..30) = 0, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 3, 3, 1, 4, 2,
  1, 6, 2, 3, 4, 1, 3, as in the entry; both parts hold for n < 300.
-/

namespace OMA.S_oeis_a233867


/-- A233867(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 (2 * n)).filter fun m => IsSquare m ∧ (2 * n - 1 - Nat.totient m).Prime).card

/-- The conjecture of the entry (all parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
      ∀ n : ℕ, 3 ≤ n → ∃ k, 0 < k ∧ k < 2 * n ∧ (2 * n - 1 - Nat.totient k).Prime ∧
        (2 * n - 1 + Nat.totient k).Prime := by
  sorry

end OMA.S_oeis_a233867
