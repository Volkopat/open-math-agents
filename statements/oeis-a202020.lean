import Mathlib

/-!
# A202020: Mathar's recurrence

Source: https://oeis.org/A202020
Credit: @ivillar

Status: known result. The entry records that the recurrence was corrected and proved from the g.f.: the corresponding
differential operator applied to the g.f. gives 4*(3*x^2-3*x+1) (Eric Longstreet, Nov 27 2026). The catalogue
text of the conjecture, 2(n+2)*a(n) -4*(5n+4)*a(n-1) +3*(19n-2)*a(n-2) +4*(11-14n)*a(n-4) +12*(n-1)*a(n-4)=0, has
the misprint a(n-4) for a(n-3) in its fourth term; `main` is the recurrence of the entry, with a(n-3).

A202020 (offset 0): number of 4-colored Motzkin paths of length n with no peaks at level 1;
data 1, 4, 16, 68, 305, 1428, 6914, 34368, 174438, 900392, 4712034, 24944268, ...

Conjecture (R. J. Mathar, Dec 18 2011): D-finite with recurrence
2*(n+2)*a(n) -4*(5*n+4)*a(n-1) +3*(19*n-2)*a(n-2) +4*(11-14*n)*a(n-3) +12*(n-1)*a(n-4) = 0.

Formalization: The entry gives the g.f. (2*z^2-4*z+1 - sqrt(12*z^2-8*z+1))/(2*z^4-8*z^3+4*z^2), and this closed form is used
as the definition here. S is the formal power series over ℚ with S^2 = 1-8*x+12*x^2 and constant term 1
(the constant term selects the branch of the square root), and G is determined by
G*(2*x^4 - 8*x^3 + 4*x^2) = 2*x^2 - 4*x + 1 - S, the stated expression multiplied by its denominator (the
denominator is a nonzero power series, so this equation has exactly one solution G);
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (12)*(305) + (-96)*(68) + (222)*(16) + (-180)*(4) + (36)*(1) = 0.
-/

namespace OMA.S_oeis_a202020

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A202020, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 8 * X + 12 * X ^ 2 →
    coeff 0 S = 1 →
    G * (2 * X ^ 4 - 8 * X ^ 3 + 4 * X ^ 2) = 2 * X ^ 2 - 4 * X + 1 - S →
    ∀ n : ℕ, 4 ≤ n →
      (4 + 2 * (n : ℚ)) * coeff n G + (-16 - 20 * (n : ℚ)) * coeff (n - 1) G +
        (-6 + 57 * (n : ℚ)) * coeff (n - 2) G + (44 - 56 * (n : ℚ)) * coeff (n - 3) G +
        (-12 + 12 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a202020
