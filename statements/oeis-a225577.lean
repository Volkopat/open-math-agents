import Mathlib

/-!
# A225577: Least integer m>1 such that 1^2,2^2,...,n^2 are pairwise incongruent modulo 2^m-1.

Source: https://oeis.org/A225577
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A225577 (Zhi-Wei Sun, May 10 2013): a(n) is the least
prime p such that 2^p-1 is a Mersenne prime greater than 2n-1.

Conventions:
* The sequence has offset 1 (data 2, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, ...).
* `Inc n M` says that 1^2, 2^2, ..., n^2 are pairwise incongruent modulo M. a(n) is the least
  integer m > 1 with `Inc n (2^m - 1)`.
* The conjecture is stated as: for every n >= 1 there is an m which is at the same time the least
  element of {m > 1 : Inc n (2^m - 1)} and the least prime p such that 2^p - 1 is prime and
  greater than 2n - 1. The natural subtractions 2^m - 1 and 2n - 1 (n >= 1) are exact.
-/

namespace OMA.S_oeis_a225577

/-- 1^2, 2^2, ..., n^2 are pairwise incongruent modulo M. -/
def Inc (n M : ℕ) : Prop := ∀ j k : ℕ, 0 < j → j < k → k ≤ n → j ^ 2 % M ≠ k ^ 2 % M

/-- The conjecture recorded in A225577. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ m : ℕ,
    IsLeast {m : ℕ | 1 < m ∧ Inc n (2 ^ m - 1)} m ∧
    IsLeast {p : ℕ | p.Prime ∧ (2 ^ p - 1).Prime ∧ 2 * n - 1 < 2 ^ p - 1} m := by
  sorry

end OMA.S_oeis_a225577
