import Mathlib

/-!
# A157021: Mathar's recurrence

Source: https://oeis.org/A157021
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A157021 (offset 0): a(n)=sum{k=0..floor(n/2), C(n,2k)*A000108(floor(k/2))}. Inverse binomial transform is aeration of doubled Catalan numbers;
data 1, 1, 2, 4, 8, 16, 32, 64, 129, 265, 558, 1200, ...

Conjecture (R. J. Mathar, Feb 05 2015):
(n+4)*a(n) +(-7*n-18)*a(n-1) +2*(11*n+12)*a(n-2) +8*(-5*n+2)*a(n-3) +(41*n-76)*a(n-4)
+(-19*n+62)*a(n-5) +4*(-n+6)*a(n-6) +6*(n-6)*a(n-7) = 0.

Formalization: The entry gives the g.f. ((1-2x+2x^2)/(1-x)^3)*c(x^4/(1-x)^4) with c(y) = (1 - sqrt(1-4y))/(2y) the Catalan
g.f. With y = x^4/(1-x)^4 one has sqrt(1-4y) = S/(1-x)^2 for S = sqrt((1-x)^4 - 4x^4), so
c(y) = ((1-x)^2 - S)*(1-x)^2/(2x^4) and the g.f. is (1-2x+2x^2)*((1-x)^2 - S)/(2*x^4*(1-x)). Accordingly S is
the formal power series over ℚ with S^2 = (1-x)^4 - 4*x^4 = 1-4*x+6*x^2-4*x^3-3*x^4 and constant term 1 (the
constant term selects the branch of the square root), and G is determined by
2*x^4*(1-x)*G = (1-2*x+2*x^2)*((1-x)^2 - S);
a(n) = [x^n] G. The recurrence involves a(n-7), so it is stated for n ≥ 7; it is checked by the data, for
example at n = 7: (11)*(64) + (-67)*(32) + (178)*(16) + (-264)*(8) + (211)*(4) + (-71)*(2) + (-4)*(1) + (6)*(1) = 0.
-/

namespace OMA.S_oeis_a157021

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A157021, for n ≥ 7. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 - 3 * X ^ 4 →
    coeff 0 S = 1 →
    2 * X ^ 4 * (1 - X) * G = (1 - 2 * X + 2 * X ^ 2) * ((1 - X) ^ 2 - S) →
    ∀ n : ℕ, 7 ≤ n →
      (4 + (n : ℚ)) * coeff n G + (-18 - 7 * (n : ℚ)) * coeff (n - 1) G +
        (24 + 22 * (n : ℚ)) * coeff (n - 2) G + (16 - 40 * (n : ℚ)) * coeff (n - 3) G +
        (-76 + 41 * (n : ℚ)) * coeff (n - 4) G + (62 - 19 * (n : ℚ)) * coeff (n - 5) G +
        (24 - 4 * (n : ℚ)) * coeff (n - 6) G + (-36 + 6 * (n : ℚ)) * coeff (n - 7) G = 0 := by
  sorry

end OMA.S_oeis_a157021
