import Mathlib

/-!
# A190171: Mathar's recurrence

Source: https://oeis.org/A190171
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A190171 (offset 0): number of peakless Motzkin paths of length n having no UHD's starting at level 0; here U=(1,1), H=(1,0), and D=(1,-1);
data 1, 1, 1, 1, 2, 5, 12, 27, 60, 135, 309, 717, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
(n+2)*a(n) +(-n+1)*a(n-1) +2*(-2*n-1)*a(n-2) +9*a(n-3) +(-n+1)*a(n-4) -9*a(n-5) +2*(-2*n+5)*a(n-6)
+(-n+1)*a(n-7) +(n-4)*a(n-8) = 0.

Formalization: The entry gives the g.f. in closed form, 2/(1 + sqrt((1 + (-3 + x)*x)*(1 + x + x^2)) + x*(-1 + x + 2*x^2)),
and this closed form is used as the definition here. S is the formal power series over ℚ with
S^2 = (1-3*x+x^2)*(1+x+x^2) = 1-2*x-x^2-2*x^3+x^4 and constant term 1 (the constant term selects the branch
of the square root), and G is determined by (1 - x + x^2 + 2*x^3 + S)*G = 2;
a(n) = [x^n] G. The recurrence involves a(n-8), so it is stated for n ≥ 8; it is checked by the data, for
example at n = 8: (10)*(60) + (-7)*(27) + (-34)*(12) + (9)*(5) + (-7)*(2) + (-9)*(1) + (-22)*(1) + (-7)*(1) + (4)*(1) = 0.
-/

namespace OMA.S_oeis_a190171

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A190171, for n ≥ 8. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 →
    coeff 0 S = 1 →
    (1 - X + X ^ 2 + 2 * X ^ 3 + S) * G = 2 →
    ∀ n : ℕ, 8 ≤ n →
      (2 + (n : ℚ)) * coeff n G + (1 - (n : ℚ)) * coeff (n - 1) G +
        (-2 - 4 * (n : ℚ)) * coeff (n - 2) G + (9) * coeff (n - 3) G +
        (1 - (n : ℚ)) * coeff (n - 4) G + (-9) * coeff (n - 5) G +
        (10 - 4 * (n : ℚ)) * coeff (n - 6) G + (1 - (n : ℚ)) * coeff (n - 7) G +
        (-4 + (n : ℚ)) * coeff (n - 8) G = 0 := by
  sorry

end OMA.S_oeis_a190171
