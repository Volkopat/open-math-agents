import Mathlib

/-!
# A220899: Mathar's recurrence

Source: https://oeis.org/A220899
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A220899 (offset 2): number of 2-face-free maps on n edges;
data 0, 2, 6, 23, 90, 372, 1594, 7042, 31888, 147402, 693298, 3309625, ...

Conjecture (R. J. Mathar, Jul 17 2014):
2*(n+1)*(2*n+1)*a(n) +(-23*n^2+31*n-6)*a(n-1) +2*(-4*n^2-9*n+25)*a(n-2) +2*(23*n^2-142*n+174)*a(n-3)
+4*(n+8)*(n-5)*a(n-4) -23*(n-5)*(n-6)*a(n-5) = 0.

Formalization: the entry gives the g.f. as P(x) - x*P(x), where P(x) = A(x/(1+x)) is the g.f. of A220898
and A(x) is the g.f. of A000139; and A000139 gives its o.g.f. as A(x) = T(x)*(3 - T(x)), where
T(x) = 1 + x*T(x)^3 is the o.g.f. of A001764. These formulas are used as the definition here. Y is the
formal power series over ℚ with Y*(1+x) = x, that is Y = x/(1+x); T is the formal power series with
T = 1 + x*T^3 (this equation has exactly one power series solution); P is the composition of
A = T*(3 - T) with Y (`(T * (3 - T)).subst Y`; Y has zero constant term, so the composition is defined);
and G = (1 - x)*P. Then a(n) = [x^n] G for n ≥ 2 (the coefficients 2 and -1 of x^0 and x^1 in G are
not terms of the sequence). The sequence has offset 2 and the recurrence involves a(n-5), so it is
stated for n ≥ 7, where every index is at least the offset, with the coefficients expanded; it is
checked by the data, for example at n = 7:
(240)*(372) + (-916)*(90) + (-468)*(23) + (614)*(6) + (120)*(2) + (-46)*(0) = 0.
-/

namespace OMA.S_oeis_a220899

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A220899, for n ≥ 7. -/
theorem main : ∀ Y T P G : ℚ⟦X⟧, Y * (1 + X) = X →
    T = 1 + X * T ^ 3 →
    P = (T * (3 - T)).subst Y →
    G = (1 - X) * P →
    ∀ n : ℕ, 7 ≤ n →
      (2 + 6 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff n G + (-6 + 31 * (n : ℚ) - 23 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (50 - 18 * (n : ℚ) - 8 * (n : ℚ) ^ 2) * coeff (n - 2) G + (348 - 284 * (n : ℚ) + 46 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-160 + 12 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff (n - 4) G + (-690 + 253 * (n : ℚ) - 23 * (n : ℚ) ^ 2) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a220899
