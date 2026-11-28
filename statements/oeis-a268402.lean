import Mathlib

/-!
# A268402: Mathar's recurrence

Source: https://oeis.org/A268402
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Oct 07 2016); the entry records it as a conjecture and notes no proof or
verification of it.

A268402 (offset 5): number of North-East lattice paths from (0,0) to (n,n) that bounce off the diagonal y = x to the right exactly four times;
data 1, 7, 40, 204, 977, 4493, 20091, 88025, 379766, 1618898, 6835636, 28640302, ...

Conjecture (R. J. Mathar, Oct 07 2016):
-(n-3)*(n-5)*(55*n-618)*a(n) +(-55*n^3-840*n^2+6969*n-5742)*a(n-1) +(3135*n^3 -37532*n^2 +138815*n
-163614)*a(n-2) +(-7645*n^3 +93072*n^2 -343985*n +391386)*a(n-3)
-18*(n-3)*(55*n-126)*(2*n-5)*a(n-4) = 0.

Formalization: The entry gives the g.f. -((-1 + f(x))^5*x^3*(-1 + f(x) + 2*x))/(2*(1 - f(x) + (-5 + f(x))*x)^5) with
f(x) = sqrt(1 - 4*x), and this closed form is used as the definition here. S is the formal power series
over ℚ with S^2 = 1-4*x and constant term 1, that is S = f(x) (the constant term selects the branch of the
square root); and G is determined by G*2*(1 - S + (S - 5)*x)^5 = -(S - 1)^5*x^3*(S - 1 + 2*x), the stated
expression multiplied by its denominator (the denominator is a nonzero power series, so this equation has
exactly one solution G);
a(n) = [x^n] G. The sequence has offset 5, and [x^k] G = 0 for k < 5. The recurrence involves a(n-4); with
a(k) read as [x^k] G (so a(k) = 0 below the offset) it holds for n ≥ 4, and `main` is stated
for this range, which contains every n ≥ 9 (where all indices are at least the offset).
It is checked by the data, for example at n = 9:
(2952)*(977) + (-51156)*(204) + (331044)*(40) + (-738852)*(7) + (-518076)*(1) = 0.
-/

namespace OMA.S_oeis_a268402

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A268402, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    G * (2 * (1 - S + (S - 5) * X) ^ 5) = -((S - 1) ^ 5 * X ^ 3 * (S - 1 + 2 * X)) →
    ∀ n : ℕ, 4 ≤ n →
      (9270 - 5769 * (n : ℚ) + 1058 * (n : ℚ) ^ 2 - 55 * (n : ℚ) ^ 3) * coeff n G + (-5742 + 6969 * (n : ℚ) - 840 * (n : ℚ) ^ 2 - 55 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-163614 + 138815 * (n : ℚ) - 37532 * (n : ℚ) ^ 2 + 3135 * (n : ℚ) ^ 3) * coeff (n - 2) G + (391386 - 343985 * (n : ℚ) + 93072 * (n : ℚ) ^ 2 - 7645 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (34020 - 39798 * (n : ℚ) + 15426 * (n : ℚ) ^ 2 - 1980 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a268402
