import Mathlib

/-!
# A360822: squares with at most two decimal digits below eight

Source: https://oeis.org/A360822
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A360/A360822.seq
Credit: @Bondyboy2001

The source sequence consists of positive integers. Zero is therefore not a term, even though
it vacuously satisfies the digit-count condition.
-/

namespace OMA.S_oeis_a360822

/-- At most two decimal digits of `n ^ 2` are strictly less than eight. -/
def HasSmallSquareDigitCount (n : ℕ) : Prop :=
  ((Nat.digits 10 (n ^ 2)).filter fun d => d < 8).length ≤ 2

/-- Membership in A360822. -/
def IsTerm (n : ℕ) : Prop := 0 < n ∧ HasSmallSquareDigitCount n

/-- Branicky's conjecture: there are exactly `72` terms, the largest of which is `940206833`. -/
theorem main :
    Set.ncard {n : ℕ | IsTerm n} = 72 ∧
      IsGreatest {n : ℕ | IsTerm n} 940206833 := by
  sorry

end OMA.S_oeis_a360822
