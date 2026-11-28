import Mathlib

/-!
# A373610: Positive integers that cannot be written as a sum of a practical number and an octagonal number.

Source: https://oeis.org/A373610
Credit: @darealpandaboi

Conjecture (Somu and Tran, 2024): there are finitely many such integers. It was also conjectured
that 4005819 is the largest such integer (checked up to 10^8).

Translation notes.
* A practical number (A005153) is a positive integer x such that every smaller nonnegative
  integer is a sum of distinct divisors of x (0 is the empty sum).
* The octagonal numbers are k(3k - 2) for k >= 0, so 0 is included. This reading reproduces the
  listed data (checked by computer against every listed term); with k >= 1 instead, 1 would be
  a term, contradicting the data.
* Both conjectures are stated: the set is finite, and 4005819 is its largest element (a
  computer check confirms that 4005819 is not such a sum).
-/

namespace OMA.S_oeis_a373610

/-- x is practical: every m < x is a sum of distinct divisors of x. -/
def IsPractical (x : ℕ) : Prop :=
  0 < x ∧ ∀ m : ℕ, m < x → ∃ s ⊆ x.divisors, ∑ d ∈ s, d = m

/-- The positive integers that are not a practical number plus an octagonal number. -/
def S : Set ℕ :=
  {n : ℕ | 0 < n ∧ ¬ ∃ p k : ℕ, IsPractical p ∧ n = p + k * (3 * k - 2)}

theorem main : S.Finite ∧ IsGreatest S 4005819 := by
  sorry

end OMA.S_oeis_a373610
