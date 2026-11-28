import Mathlib

/-!
# A294307: Positive integers m with m^k - 1 (k = 1,...,13) all practical.

Source: https://oeis.org/A294307
Credit: @darealpandaboi

Conjecture (Zhi-Wei Sun): For any positive integer n, there are infinitely many positive integers
m with m^k - 1 (k = 1, ..., n) all practical.

Translation notes.
* A practical number (A005153) is a positive integer x such that every smaller nonnegative
  integer is a sum of distinct divisors of x (0 is the empty sum).
* Practical numbers are positive, so m >= 2 is forced by the condition at k = 1.
* With n = 13 this reproduces the listed data: the m < 1100 are 169, 625, 729, 1089
  (checked by computer).
-/

namespace OMA.S_oeis_a294307

/-- x is practical: every m < x is a sum of distinct divisors of x. -/
def IsPractical (x : ℕ) : Prop :=
  0 < x ∧ ∀ m : ℕ, m < x → ∃ s ⊆ x.divisors, ∑ d ∈ s, d = m

theorem main : ∀ n : ℕ, 0 < n →
    {m : ℕ | 0 < m ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n → IsPractical (m ^ k - 1)}.Infinite := by
  sorry

end OMA.S_oeis_a294307
