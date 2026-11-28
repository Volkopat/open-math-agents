import Mathlib

/-!
# A352057: triangular numbers whose nonzero decimal digits are all equal

Source: https://oeis.org/A352057
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A352/A352057.seq
Credit: @Bondyboy2001

The sequence contains the triangular number zero. The common nonzero digit is represented by an
existing nonzero decimal digit `d`; every digit of the term is then either zero or `d`.
-/

namespace OMA.S_oeis_a352057

/-- `m` is a triangular number. -/
def IsTriangular (m : ℕ) : Prop :=
  ∃ n : ℕ, m = n * (n + 1) / 2

/-- Every nonzero decimal digit of `m` is the digit `d`. -/
def NonzeroDigitsAre (m d : ℕ) : Prop :=
  ∀ x : ℕ, x ∈ Nat.digits 10 m → x = 0 ∨ x = d

/-- The conjecture: among terms whose common nonzero digit is not five, the largest is `600060`. -/
theorem main :
    IsGreatest {m : ℕ | IsTriangular m ∧
      ∃ d : ℕ, d ≠ 0 ∧ d ≠ 5 ∧ NonzeroDigitsAre m d} 600060 := by
  sorry

end OMA.S_oeis_a352057
