import Mathlib

/-!
# A108069: ordered positive pairs with `i! * j! = n`

Source: https://oeis.org/A108069

Kane's conjecture is that the maximum value of the sequence is `4`. The factorials are positive,
so for a fixed nonzero `n` every factor index in a solution is at most `n`; the finite search
below is therefore exact. For `n = 0` there are no solutions.
-/

namespace OMA.S_oeis_a108069

/-- `a n` is the number of ordered pairs `(i, j)` of positive integers with `i! * j! = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun p => Nat.factorial p.1 * Nat.factorial p.2 = n)).card

/-- Kane's conjecture: the maximum value of `a` is `4`. -/
theorem main : IsGreatest (Set.range a) 4 := by
  sorry

end OMA.S_oeis_a108069
