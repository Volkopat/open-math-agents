import Mathlib

/-!
# A restricted factorial-square problem

Source: https://math.stackexchange.com/questions/2749067/disprove-m-100x220x-using-an-estimation-for-factorial
Credit: @treybeathard-jpg

PintOfMilk asks whether the equation `m! = 100*x^2 + 20*x` has no solutions when
`m >= 20`, with `m` and `x` nonnegative integers. We use `Nat` for both variables
and retain the stated lower bound. The question's suggested factorial estimates
are proposed proof methods, not hypotheses.

This is a restricted instance of Brocard's problem: the equation is equivalent
to `m! + 1 = (10*x + 1)^2`. No assertion that this open problem has been proved
is intended; the single placeholder below is the statement contribution.
-/

namespace OMA.S_mse_2749067

/-- The equation from the question has no nonnegative integer solutions with `m >= 20`. -/
theorem main : ∀ m x : ℕ, 20 ≤ m → m.factorial ≠ 100 * x ^ 2 + 20 * x := by
  sorry

end OMA.S_mse_2749067

