import Mathlib

/-!
# A228178: Mathar's recurrence

Source: https://oeis.org/A228178
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Aug 25 2013); the entry records it as a conjecture and notes no proof or
verification of it.

A228178 (offset 0): the number of boundary edges for all ordered trees with n edges;
data 1, 4, 14, 47, 157, 529, 1805, 6238, 21812, 77062, 274738, 987276, ...

Conjecture (R. J. Mathar, Aug 25 2013):
2*(n+3)*a(n) +2*(-7*n-11)*a(n-1) +(29*n+7)*a(n-2) +(-21*n+19)*a(n-3) +2*(2*n-5)*a(n-4) = 0.

Formalization: the entry gives the g.f. (x*C+2*x^2*C^4)/(1-x), where C is the g.f. for the Catalan numbers
A000108, and this closed form is used as the definition here. T is the series C: the formal power series
over ℚ with T = 1 + x*T^2 (this equation has exactly one power series solution, with constant term 1); and G
is determined by G*(1 - x) = x*T + 2*x^2*T^4, the stated expression multiplied by its denominator.
Index convention: the g.f. has no constant term, G = x + 4*x^2 + 14*x^3 + 47*x^4 + ..., while the entry lists
the data with offset 0 (a(0) = 1, a(1) = 4, a(2) = 14, ...). The data are therefore a(n) = [x^(n+1)] G
(the coefficient of x^m in G is the number for the trees with m edges, and the offset of the entry is one
less), and `main` is Mathar's recurrence in the indexing of the entry and of its data, with
a(k) = [x^(k+1)] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data,
for example at n = 4: (14)*(157) + (-78)*(47) + (123)*(14) + (-65)*(4) + (6)*(1) = 0, and at n = 5:
(16)*(529) + (-92)*(157) + (152)*(47) + (-86)*(14) + (10)*(4) = 0.
-/

namespace OMA.S_oeis_a228178

open PowerSeries

/-- Mathar's conjectured recurrence for A228178 in the indexing of the entry, a(k) = [x^(k+1)] G,
for n ≥ 4. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T ^ 2 →
    G * (1 - X) = X * T + 2 * X ^ 2 * T ^ 4 →
    ∀ n : ℕ, 4 ≤ n →
      2 * ((n : ℚ) + 3) * coeff (n + 1) G + 2 * (-7 * (n : ℚ) - 11) * coeff n G +
        (29 * (n : ℚ) + 7) * coeff (n - 1) G + (-21 * (n : ℚ) + 19) * coeff (n - 2) G +
        2 * (2 * (n : ℚ) - 5) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a228178
