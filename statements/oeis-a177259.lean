import Mathlib

/-!
# A177259: Mathar's recurrence

Source: https://oeis.org/A177259
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A177259 (offset 0): number of derangements of {1,2,...,n} having no adjacent 3-cycles (an adjacent 3-cycle is a cycle of the form (i,i+1,i+2));
data 1, 0, 1, 1, 9, 41, 258, 1809, 14575, 131660, 1320264, 14551987, ...

Conjecture (R. J. Mathar, Jul 26 2022): D-finite with recurrence
a(n) = (n-1)*a(n-1) + (n-1)*a(n-2) + a(n-3) + (n-1)*a(n-4) + 2*a(n-6).

Formalization: the entry gives the g.f. Sum_{k>=0} k! * x^k / (1+x+x^3)^(k+1) (Seiichi Manyama, Feb 22 2024), and this
is used as the definition here. Y is the formal power series over ℚ with Y*(1+x+x^3) = x, that is
Y = x/(1+x+x^3); it has zero constant term, so the composition E(Y) = Sum_{k>=0} k! * Y^k of the
series E = Sum_{k>=0} k! * x^k with Y is defined (`(PowerSeries.mk fun k => k!).subst Y`); and the
g.f. G is determined by G*(1+x+x^3) = E(Y);
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (1)*(258) + (-5)*(41) + (-5)*(9) + (-1)*(1) + (-5)*(1) + (-2)*(1) = 0.
-/

namespace OMA.S_oeis_a177259

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A177259, for n ≥ 6. -/
theorem main : ∀ Y G : ℚ⟦X⟧, Y * (1 + X + X ^ 3) = X →
    G * (1 + X + X ^ 3) = (PowerSeries.mk fun k : ℕ => (k.factorial : ℚ)).subst Y →
    ∀ n : ℕ, 6 ≤ n →
      (1) * coeff n G + (1 - (n : ℚ)) * coeff (n - 1) G +
        (1 - (n : ℚ)) * coeff (n - 2) G + (-1) * coeff (n - 3) G +
        (1 - (n : ℚ)) * coeff (n - 4) G + (-2) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a177259
