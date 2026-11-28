import Mathlib

/-!
# A373443: Positive integers that cannot be written as a sum of a practical number and a hexagonal number.

Source: https://oeis.org/A373443
Credit: @darealpandaboi

Conjecture (Somu and Tran, 2024): there are finitely many such integers. It was also conjectured
that 1332329 is the largest such integer (checked up to 10^8).

Translation notes.
* A practical number (A005153) is a positive integer x such that every smaller nonnegative
  integer is a sum of distinct divisors of x (0 is the empty sum).
* The hexagonal numbers are k(2k - 1) for k >= 0, so 0 is included. This reading reproduces the
  listed data (checked by computer against every listed term); with k >= 1 instead, 1 would be
  a term, contradicting the data.
* Both conjectures are stated: the set is finite, and 1332329 is its largest element (a
  computer check confirms that 1332329 is not such a sum).
-/

namespace OMA.S_oeis_a373443

/-- x is practical: every m < x is a sum of distinct divisors of x. -/
def IsPractical (x : ℕ) : Prop :=
  0 < x ∧ ∀ m : ℕ, m < x → ∃ s ⊆ x.divisors, ∑ d ∈ s, d = m

/-- The positive integers that are not a practical number plus a hexagonal number. -/
def S : Set ℕ :=
  {n : ℕ | 0 < n ∧ ¬ ∃ p k : ℕ, IsPractical p ∧ n = p + k * (2 * k - 1)}

theorem main : S.Finite ∧ IsGreatest S 1332329 := by
  sorry

end OMA.S_oeis_a373443
