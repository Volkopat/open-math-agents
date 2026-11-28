import Mathlib

/-!
# A182887: Mathar's recurrence

Source: https://oeis.org/A182887
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A182887 (offset 0): number of (1,0)-steps in all weighted lattice paths in L_n;
data 0, 1, 3, 7, 21, 60, 166, 463, 1281, 3521, 9645, 26322, ...

Conjecture (R. J. Mathar, Jun 14 2016):
(n-1)*(182*n-279)*a(n) + (-230*n^2+11*n+643)*a(n-1) + (-450*n^2+1603*n-315)*a(n-2)
+ (-498*n^2+971*n+57)*a(n-3) + (-86*n^2+959*n-529)*a(n-4) + (134*n-59)*(n-3)*a(n-5) = 0.

Formalization: the entry gives the g.f. in closed form, z*(1+z)*(1-z-z^2)/((1-3*z+z^2)*(1+z+z^2))^(3/2), and
this closed form is used as the definition here. S is the formal power series over ℚ with
S^2 = (1-3*x+x^2)*(1+x+x^2) = 1 - 2x - x^2 - 2x^3 + x^4 and constant term 1 (the constant term
selects the branch of the square root), so that the 3/2 power is (1-3x+x^2)*(1+x+x^2)*S, and the
g.f. G is determined by (1 - 3*x + x^2)*(1 + x + x^2)*S*G = x*(1 + x)*(1 - x - x^2);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (2524)*(60) + (-5052)*(21) + (-3550)*(7) + (-7538)*(3) + (2116)*(1) + (1222)*(0) = 0.
-/

namespace OMA.S_oeis_a182887

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A182887, for n ≥ 5. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 →
    coeff 0 S = 1 →
    (1 - 3 * X + X ^ 2) * (1 + X + X ^ 2) * S * G = X * (1 + X) * (1 - X - X ^ 2) →
    ∀ n : ℕ, 5 ≤ n →
      (279 - 461 * (n : ℚ) + 182 * (n : ℚ) ^ 2) * coeff n G + (643 + 11 * (n : ℚ) - 230 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-315 + 1603 * (n : ℚ) - 450 * (n : ℚ) ^ 2) * coeff (n - 2) G + (57 + 971 * (n : ℚ) - 498 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-529 + 959 * (n : ℚ) - 86 * (n : ℚ) ^ 2) * coeff (n - 4) G + (177 - 461 * (n : ℚ) + 134 * (n : ℚ) ^ 2) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a182887
