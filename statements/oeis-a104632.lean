import Mathlib

/-!
# A recurrence for normalized pentanomial coefficients

T. D. Noe defines A104632 by a coefficient of a pentanomial power.
R. J. Mathar conjectured the recurrence on July 23, 2017. The offset is one,
so all four terms belong to the sequence for `n ≥ 4`.
Source: https://oeis.org/A104632 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a104632
open Polynomial

noncomputable def pentanomial : ℚ[X] := 1 + X + X^2 + X^3 + X^4

/-- Divide the coefficient immediately above the center by `n`. -/
noncomputable def a (n : ℕ) : ℚ := (pentanomial^n).coeff (2*n+1) / n

theorem main : ∀ n : ℕ, 4 ≤ n → let x : ℚ := n
    2*x*(2*x+1)*(x-1)*a n - (x-1)*(19*x^2-19*x+2)*a (n-1)
      - 5*(x-2)*(2*x^2-3*x-1)*a (n-2) + 25*x*(x-2)*(x-3)*a (n-3) = 0 := by
  sorry

end OMA.S_oeis_a104632
