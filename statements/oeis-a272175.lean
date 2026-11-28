import Mathlib

/-!
# A272175: Least number k such that (k^2+1) mod s = prime(n) where s is the sum of the distinct primes dividing k^2+1, or 0 if no such k exists.

Source: https://oeis.org/A272175
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A272175 (Michel Lagneau, Apr 28 2016): a(n)> 0 for all
n > 0.

Conventions:
* The sequence has offset 1 (data 13, 3, 68, 182, 5, 32, 191, 333, 73, 70, 1068, 132, ...).
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* s is the sum of the distinct primes dividing k^2 + 1, the sum over `Nat.primeFactors (k^2 + 1)`.
  `a(n) > 0` means that some positive integer k with (k^2 + 1) mod s = prime(n) exists; it is
  stated directly as the existence of k.
-/

namespace OMA.S_oeis_a272175

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The conjecture recorded in A272175. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧
    (k ^ 2 + 1) % (∑ q ∈ (k ^ 2 + 1).primeFactors, q) = pr n := by
  sorry

end OMA.S_oeis_a272175
