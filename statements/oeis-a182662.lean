import Mathlib

/-!
# A182662: Number of ordered ways to write n = p + q with q > 0 such that p, 3*(p + prime(q)) - 1 and 3*(p + prime(q)) + 1 are all prime.

Source: https://oeis.org/A182662
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A182662 (Zhi-Wei Sun):
a(n) > 0 if n is not a divisor of 12.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 0, 1, 0, 1, 2, 1, 1, 1, 0, 3, ...), so n ranges over
  the positive integers. `a n` is the number of natural numbers p < n (so that q = n - p > 0)
  such that p, 3*(p + prime(n - p)) - 1 and 3*(p + prime(n - p)) + 1 are all prime.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed,
  prime(q) is `Nat.nth Nat.Prime (q - 1)`, here with q = n - p >= 1.
* The natural subtraction in 3*(p + prime(q)) - 1 is exact because 3*(p + prime(q)) >= 6.
* The conjecture is a one-way implication (a(3) = 1 although 3 divides 12), stated for every
  n >= 1 that does not divide 12.
-/

namespace OMA.S_oeis_a182662

/-- A182662: number of p < n with p, 3*(p + prime(n-p)) - 1 and 3*(p + prime(n-p)) + 1
all prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ | p < n ∧ p.Prime ∧
    (3 * (p + Nat.nth Nat.Prime (n - p - 1)) - 1).Prime ∧
    (3 * (p + Nat.nth Nat.Prime (n - p - 1)) + 1).Prime}

/-- The conjecture of Sun: a(n) > 0 if n is not a divisor of 12. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ¬ (n ∣ 12) → 0 < a n := by
  sorry

end OMA.S_oeis_a182662
