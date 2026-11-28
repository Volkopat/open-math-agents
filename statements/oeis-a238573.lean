import Mathlib

/-!
# A238573: a(n) = |{0 < k <= n: prime(k*n) + 2 is prime}|.

Source: https://oeis.org/A238573
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 6, and a(n) = 1 only for n = 2, 3, 8, 11, 17. Moreover, for any n > 0
there exists a positive integer k < 3*sqrt(n) + 6 such that prime(k*n) + 2 is prime.
(ii) For any integer n > 6, prime(k^2*n) + 2 is prime for some k = 1, ..., n.
(iii) If n > 5, then prime(k^2*(n-k)) + 2 is prime for some 0 < k < n.

Formalization notes:
* phi = `Nat.totient`, sigma = `ArithmeticFunction.sigma 1`, prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2). "x is a square" is `IsSquare x`.
* "a(n) = 1 only for n in S" is stated as: a(n) = 1 iff n ∈ S. The bound 3*sqrt(n) + 6 is in ℝ.
* Controls (computed): a(1..30) = 0, 1, 1, 0, 3, 0, 4, 1, 2, 3, 1, 3, 4, 4, 4, 4, 1, 3, 6, 5, 3, 3, 4,
  6, 3, 8, 5, 6, 3, 4, as in the entry; for n < 150 every part holds.
-/

namespace OMA.S_oeis_a238573


/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A238573(n). -/
noncomputable def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => (prime (k * n) + 2).Prime).card

/-- The conjecture of the entry (all parts listed above). -/
theorem main :
    (∀ n : ℕ, 6 < n → 0 < a n) ∧
      (∀ n : ℕ, a n = 1 ↔ n = 2 ∨ n = 3 ∨ n = 8 ∨ n = 11 ∨ n = 17) ∧
      (∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt n + 6 ∧ (prime (k * n) + 2).Prime) ∧
      (∀ n : ℕ, 6 < n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ (prime (k ^ 2 * n) + 2).Prime) ∧
      ∀ n : ℕ, 5 < n → ∃ k, 0 < k ∧ k < n ∧ (prime (k ^ 2 * (n - k)) + 2).Prime := by
  sorry

end OMA.S_oeis_a238573
