import Mathlib

/-!
# The silver ratio as a limit of consecutive terms of A179807

Sources:
* https://oeis.org/A014176 states the conjecture.
* https://oeis.org/A179807 defines the antidiagonal sums, starting at index 1.
* https://oeis.org/A175105 gives the triangle recurrence and zero padding.

Credit: @tkyjpy
-/

namespace OMA.S_oeis_a014176

/-- A175105 with rows and columns starting at 1 and zeros outside the triangle. -/
def triangle (n k : Nat) : Nat :=
  if n = 0 then 0
  else if k = 1 then 1
  else if 2 <= k /\ k <= n then
    (Finset.range (k - 1)).sum fun j =>
      triangle (n - (j + 1)) (k - 1) + triangle (n - (j + 1)) k
  else 0
termination_by n
decreasing_by all_goals omega

/-- A179807. At index n >= 1 the cells satisfy row + column = n + 1. -/
def a179807 (n : Nat) : Nat :=
  (Finset.range n).sum fun j => triangle (n - j) (j + 1)

/-- The shift starts the ratio at the first published index. -/
theorem main :
    Filter.Tendsto
      (fun n : Nat => (a179807 (n + 2) : Real) / (a179807 (n + 1) : Real))
      Filter.atTop (nhds (1 + Real.sqrt 2)) := by
  sorry

end OMA.S_oeis_a014176
