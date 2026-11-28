import Mathlib

/-!
# A182879: Mathar's recurrence

Source: https://oeis.org/A182879
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A182879 (offset 0): the sum of the lengths of all weighted lattice paths in L_n;
data 0, 1, 3, 11, 33, 96, 278, 787, 2205, 6133, 16941, 46554, ...

Conjecture (R. J. Mathar, Jun 14 2016):
(n-1)*(310*n-781)*a(n) + (-882*n^2+3845*n-3679)*a(n-1) + (214*n^2-2903*n+3751)*a(n-2)
+ (-358*n^2-459*n+1955)*a(n-3) + (834*n^2-3631*n+4065)*a(n-4) - (262*n-663)*(n-3)*a(n-5) = 0.

Formalization: the entry gives the g.f. in closed form, z*(1+2*z^2-z^3)/((1-3*z+z^2)*(1+z+z^2))^(3/2), and
this closed form is used as the definition here. S is the formal power series over ℚ with
S^2 = (1-3*x+x^2)*(1+x+x^2) = 1 - 2x - x^2 - 2x^3 + x^4 and constant term 1 (the constant term
selects the branch of the square root), so that the 3/2 power is (1-3x+x^2)*(1+x+x^2)*S, and the
g.f. G is determined by (1 - 3*x + x^2)*(1 + x + x^2)*S*G = x*(1 + 2*x^2 - x^3);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (3076)*(96) + (-6504)*(33) + (-5414)*(11) + (-9290)*(3) + (6760)*(1) + (-1294)*(0) = 0.
-/

namespace OMA.S_oeis_a182879

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A182879, for n ≥ 5. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 →
    coeff 0 S = 1 →
    (1 - 3 * X + X ^ 2) * (1 + X + X ^ 2) * S * G = X * (1 + 2 * X ^ 2 - X ^ 3) →
    ∀ n : ℕ, 5 ≤ n →
      (781 - 1091 * (n : ℚ) + 310 * (n : ℚ) ^ 2) * coeff n G + (-3679 + 3845 * (n : ℚ) - 882 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (3751 - 2903 * (n : ℚ) + 214 * (n : ℚ) ^ 2) * coeff (n - 2) G + (1955 - 459 * (n : ℚ) - 358 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (4065 - 3631 * (n : ℚ) + 834 * (n : ℚ) ^ 2) * coeff (n - 4) G + (-1989 + 1449 * (n : ℚ) - 262 * (n : ℚ) ^ 2) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a182879
