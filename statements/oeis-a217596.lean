import Mathlib

/-!
# A217596: Expansion of g.f. x / reversion(x - x^2 - x^3).

Source: https://oeis.org/A217596 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (Vladimir Kruchinin, Mar 19 2013), offset 0: expansion of the g.f.
x / reversion(x - x^2 - x^3). Terms: 1, -1, -2, -5, -17, -64, -259, -1098, -4815, ...
The formula section states:

  Conjecture: 25*n*(n-1)*a(n) - 5*(n-1)*(25*n-42)*a(n-1) + 3*(-23*n^2 + 59*n + 4)*a(n-2)
  + 9*(3*n-10)*(3*n-11)*a(n-3)=0. - R. J. Mathar, May 23 2014

(A later line by Peter Bala, Feb 15 2015, derives a second-order recurrence with Maple's
sumrecursion and says that Mathar's recurrence follows from it.)

Range. The source gives no range. The recurrence mentions a(n-3), so every term exists from
n = 3 on; but at n = 3 the entry's own terms a(0..3) = 1, -1, -2, -5 give
25*6*(-5) - 5*2*33*(-2) + 3*(-26)*(-1) + 9*(-1)*(-2)*1 = -750 + 660 + 78 + 18 = 6, not 0.
For every n from 4 to 12 the left side is 0 on the entry's terms. The recurrence is therefore
stated for n ≥ 4, the range on which it holds on the data; read for n ≥ 3 it would be false at
n = 3.

Formalization notes:
* The reversion of x - x^2 - x^3 is its compositional inverse: the power series R over ℚ with
  zero constant coefficient and R - R^2 - R^3 = x (this is (x - x^2 - x^3) evaluated at R).
  It exists and is unique, because x - x^2 - x^3 has linear coefficient 1.
* The g.f. G = x / R is the power series with G * R = x (R = x * (unit), so G exists, and it is
  unique because ℚ⟦X⟧ is an integral domain and R ≠ 0); a(n) = [x^n] G.
* The statement quantifies over every such R and G, in the layout of the merged square-root
  statements (for example `oeis-a071715`). Coefficients of the recurrence are written in ℚ,
  with no natural-number subtraction in them.
-/

namespace OMA.S_oeis_a217596

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of x / reversion(x - x^2 - x^3),
for n ≥ 4 (see the range note above). -/
theorem main : ∀ R G : ℚ⟦X⟧, coeff 0 R = 0 →
    R - R ^ 2 - R ^ 3 = X →
    G * R = X →
    ∀ n : ℕ, 4 ≤ n →
      25 * (n : ℚ) * ((n : ℚ) - 1) * coeff n G
        - 5 * ((n : ℚ) - 1) * (25 * (n : ℚ) - 42) * coeff (n - 1) G
        + 3 * (-23 * (n : ℚ) ^ 2 + 59 * (n : ℚ) + 4) * coeff (n - 2) G
        + 9 * (3 * (n : ℚ) - 10) * (3 * (n : ℚ) - 11) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a217596
