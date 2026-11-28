import Mathlib

/-!
# A233296: a(n) = |{0 < k < n: k*prime(n-k) + 1 is prime}|.

Source: https://oeis.org/A233296
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 1. Similarly, for any integer n > 2, k*prime(n-k) - 1 (or
k^2*prime(n-k) - 1) is prime for some 0 < k < n.
(ii) Let n > 3 be an integer. Then k + prime(n-k) is prime for some 0 < k < n. Also, if n is not
equal to 13, then k^2 + prime(n-k)^2 is prime for some 0 < k < n.

Formalization notes:
* phi = `Nat.totient`, sigma = `ArithmeticFunction.sigma 1`, prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2). "x is a square" is `IsSquare x`.
* The "or" in (i) is read as two separate claims (one with k, one with k^2), both stated.
* Controls (computed): a(1..30) = 0, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 4, 2, 2, 5, 4, 1, 6, 1, 2, 5, 4, 4,
  4, 3, 3, 2, 4, 6, 5, as in the entry; every claim holds for n < 300.
-/

namespace OMA.S_oeis_a233296


/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A233296(n). -/
noncomputable def a (n : ℕ) : ℕ := ((Finset.Ioo 0 n).filter fun k => (k * prime (n - k) + 1).Prime).card

/-- The conjecture of the entry (all parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
      (∀ n : ℕ, 2 < n → ∃ k, 0 < k ∧ k < n ∧ (k * prime (n - k) - 1).Prime) ∧
      (∀ n : ℕ, 2 < n → ∃ k, 0 < k ∧ k < n ∧ (k ^ 2 * prime (n - k) - 1).Prime) ∧
      (∀ n : ℕ, 3 < n → ∃ k, 0 < k ∧ k < n ∧ (k + prime (n - k)).Prime) ∧
      ∀ n : ℕ, 3 < n → n ≠ 13 → ∃ k, 0 < k ∧ k < n ∧ (k ^ 2 + prime (n - k) ^ 2).Prime := by
  sorry

end OMA.S_oeis_a233296
