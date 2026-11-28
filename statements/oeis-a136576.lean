import Mathlib

/-!
# Shifted Hankel determinants of A136576

Source: Paul Barry, https://oeis.org/A136576 and https://oeis.org/A136577
(OEIS Foundation, CC BY-SA 4.0). Credit: @connoranderson.

Write A for the A136576 generating function and B=1−2A. The explicit
square-root generating function in the entry gives B=1−2xB+2x²B², with
constant coefficient 1. Coefficient comparison determines B uniquely by
the recurrence below. Every Hankel entry has positive index, where the
coefficient of A is minus half the coefficient of B. We use Michael Somos's
integer residue-class expression for A136577 from its OEIS entry.
-/

namespace OMA.S_oeis_a136576

def moment : ℕ → ℚ
  | 0 => 1
  | 1 => -2
  | t+2 => -2 * moment (t+1) + 2 * ∑ i : Fin (t+1), moment i.val * moment (t-i.val)
termination_by t => t
decreasing_by all_goals omega

noncomputable def hankel (n : ℕ) : ℚ :=
  (Matrix.of fun i j : Fin (n+1) => -(moment (i.val+j.val+1))/2).det

def closedForm (n : ℕ) : ℚ :=
  if (n+2)%4=0 then 0 else 4^(n^2/4) * (-1)^((n+2)/4)

theorem main : ∀ n : ℕ, hankel n = closedForm n := by
  sorry

end OMA.S_oeis_a136576
