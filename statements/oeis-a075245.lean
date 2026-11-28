import Mathlib

/-!
# The first denominator in a maximal Egyptian-fraction expansion (OEIS A075245)

For an integer n ≥ 3, select a strictly increasing triple of positive
denominators representing 4/n whose last denominator is as large as possible.
M. F. Hasler conjectured that its first denominator is one above the quotient
of n by four, with a possible increment of two when n is one modulo eight.
The existential choice permits any maximizing triple when there is a tie.
-/

namespace OMA.S_oeis_a075245

def Expansion (n x y z : ℤ) : Prop :=
  0 < x ∧ x < y ∧ y < z ∧ 4*x*y*z = n*(y*z + x*z + x*y)

def Maximizes (n x y z : ℤ) : Prop :=
  Expansion n x y z ∧ ∀ a b c : ℤ, Expansion n a b c → c ≤ z

theorem main : ∀ n : ℤ, 3 ≤ n → ∃ x y z : ℤ, Maximizes n x y z ∧
    (x = n/4+1 ∨ (n%8 = 1 ∧ x = n/4+2)) := by
  sorry

end OMA.S_oeis_a075245
