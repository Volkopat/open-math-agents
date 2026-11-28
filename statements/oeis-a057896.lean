import Mathlib

/-!
# A057896: Nonnegative numbers that can be written as m^k - m (with m and k nonnegative) in more than one way.

Source: https://oeis.org/A057896
Credit: @azmiozgen

Conjecture (Bennett 2001, from the entry): the sequence is finite and complete, i.e. its terms are
exactly 0, 6, 30, 210, 240, 2184, 8190, 78120, 24299970.

Formalization notes:
* m^k - m is computed in ℤ (it can be negative, e.g. k = 0). A number n ≥ 0 is a term when two
  distinct pairs (m, k) of natural numbers give m^k - m = n.
* The conjecture is stated as equality of the set of terms with the listed finite set.
* Controls (computed): among m^k - m < 10^9 with m, k ≥ 2, the values with two or more
  representations are 6, 30, 210, 240, 2184, 8190, 78120, 24299970; 0 has infinitely many (k = 1).
-/

namespace OMA.S_oeis_a057896

/-- `n` is `m^k - m` for two distinct pairs `(m, k)`. -/
def IsTerm (n : ℕ) : Prop :=
  ∃ m₁ k₁ m₂ k₂ : ℕ, (m₁, k₁) ≠ (m₂, k₂) ∧
    (m₁ : ℤ) ^ k₁ - m₁ = n ∧ (m₂ : ℤ) ^ k₂ - m₂ = n

/-- Bennett's conjecture: the terms are exactly the nine known values. -/
theorem main :
    {n : ℕ | IsTerm n} = ({0, 6, 30, 210, 240, 2184, 8190, 78120, 24299970} : Set ℕ) := by
  sorry

end OMA.S_oeis_a057896
