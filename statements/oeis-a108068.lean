import Mathlib

/-!
# A108068: ordered pairs with `i! * j! = n`

Source: https://oeis.org/A108068

Kane's conjecture is that the maximum value of the sequence is `6`. The factorials are positive,
so for a fixed nonzero `n` every factor index in a solution is at most `n`; the finite search
below is therefore exact. For `n = 0` there are no solutions.
-/

namespace OMA.S_oeis_a108068

/-- `a n` is the number of ordered pairs `(i, j)` of nonnegative integers with `i! * j! = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => Nat.factorial p.1 * Nat.factorial p.2 = n)).card

/-- Kane's conjecture: the maximum value of `a` is `6`. -/
theorem main : IsGreatest (Set.range a) 6 := by
  sorry

end OMA.S_oeis_a108068
