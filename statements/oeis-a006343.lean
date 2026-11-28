import Mathlib

/-!
# A006343: Mathar's recurrence

Source: https://oeis.org/A006343
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A006343 (offset 0): arkons: number of elementary maps with n-1 nodes;
data 1, 0, 1, 1, 4, 10, 34, 112, 398, 1443, 5387, 20482, ...

Conjecture (R. J. Mathar, Feb 20 2020): D-finite with recurrence
-(n+3)*(n-1)*a(n) +(11*n^2-2*n-45)*a(n-1) -(37*n+29)*(n-3)*a(n-2) +(29*n^2-125*n+78)*a(n-3)
+(61*n-106)*(n-3)*a(n-4) -155*(n-3)*(n-4)*a(n-5) = 0.

Formalization: The entry gives the algebraic equation x^3*A^3 - (x-1)*A^2 + (x-2)*A + 1 = 0 for the o.g.f. (Peter Bala,
Jun 22 2015), and this is used as the definition here. G is the formal power series over ℚ satisfying
this equation with G = 1 + 0*x + ...; the equation has exactly two power series solutions, both with
constant term 1, and the coefficient of x (0 for A006343, 1 for the other solution) selects the g.f.;
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (-32)*(10) + (220)*(4) + (-428)*(1) + (178)*(1) + (398)*(0) + (-310)*(1) = 0.
-/

namespace OMA.S_oeis_a006343

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A006343, for n ≥ 5. -/
theorem main : ∀ G : ℚ⟦X⟧, X ^ 3 * G ^ 3 - (X - 1) * G ^ 2 + (X - 2) * G + 1 = 0 →
    coeff 0 G = 1 →
    coeff 1 G = 0 →
    ∀ n : ℕ, 5 ≤ n →
      (3 - 2 * (n : ℚ) - (n : ℚ) ^ 2) * coeff n G + (-45 - 2 * (n : ℚ) + 11 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (87 + 82 * (n : ℚ) - 37 * (n : ℚ) ^ 2) * coeff (n - 2) G + (78 - 125 * (n : ℚ) + 29 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (318 - 289 * (n : ℚ) + 61 * (n : ℚ) ^ 2) * coeff (n - 4) G + (-1860 + 1085 * (n : ℚ) - 155 * (n : ℚ) ^ 2) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a006343
