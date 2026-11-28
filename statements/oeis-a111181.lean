import Mathlib

/-!
# A111181: a(n) = prime(n) - pi(n).

Source: https://oeis.org/A111181
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A111181 (Cino Hilliard, Oct 22 2005): There will always
be an x such that a(x+1) - a(x) = k for k=1,2..

Conventions:
* The sequence has offset 1 (data 2, 2, 3, 5, 8, 10, 13, 15, 19, 25, 26, 32, ...).
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* `a n` = prime(n) - pi(n) as an integer; the difference a(x+1) - a(x) is computed in `ℤ`.
* x ranges over the indices of the sequence, x >= 1 (the offset); k ranges over the positive
  integers 1, 2, ....
* The remark `However, x becomes large when k > 70` is not part of the claim.
-/

namespace OMA.S_oeis_a111181

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A111181: a(n) = prime(n) - pi(n). -/
noncomputable def a (n : ℕ) : ℤ := (pr n : ℤ) - (Nat.primeCounting n : ℤ)

/-- The conjecture recorded in A111181. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∃ x : ℕ, 1 ≤ x ∧ a (x + 1) - a x = (k : ℤ) := by
  sorry

end OMA.S_oeis_a111181
