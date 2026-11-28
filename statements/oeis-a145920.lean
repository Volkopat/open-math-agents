import Mathlib

/-!
# A145920: Mathar's recurrence and generating function

Source: https://oeis.org/A145920
Credit: @ivillar

Status: open conjectures (R. J. Mathar, Oct 29 2008); the entry records them as conjectures and notes no proof
or verification of them. They follow from the closed form a(n) = (27x^4 - 18x^3 - 3x^2 + 2x)/8,
x = floor(n/2)*(-1)^n, recorded in the entry (William A. Tedeschi, Aug 16 2010), which is used here as the
definition.

A145920 (offset 1): list of numbers that are both pentagonal (A000326) and binomial coefficients C(n,4)
(A000332); data 0, 1, 5, 35, 70, 210, 330, 715, 1001, 1820, 2380, 3876, 4845, 7315, 8855, 12650, ...

Conjectures (R. J. Mathar, Oct 29 2008):
a(n) = a(n-1) + 4a(n-2) - 4a(n-3) - 6a(n-4) + 6a(n-5) + 4a(n-6) - 4a(n-7) - a(n-8) + a(n-9);
G.f.: x^2(1 + 4x + 26x^2 + 19x^3 + 4x^5 + x^6 + 26x^4)/((1+x)^4(1-x)^5).

Formalization: the entry gives a(n+1) = A000326(A001318(n)) (the pentagonal number whose index is the n-th
generalized pentagonal number) and the equivalent closed form
  a(n) = (27x^4 - 18x^3 - 3x^2 + 2x)/8 where x = floor(n/2)*(-1)^n, for n ≥ 1
(with y = x(3x-1)/2 the generalized pentagonal number of index n-1, this is y(3y-1)/2); the closed form is
used as the definition here (`a` below, with values in ℚ; the values are the integers of the data). `main`
has two parts. The recurrence involves a(n-9) and the sequence has offset 1, so it is stated for n ≥ 10,
where every index is at least the offset; it is checked by the data, for example at n = 10:
1820 = 1001 + 4*715 - 4*330 - 6*210 + 6*70 + 4*35 - 4*5 - 1 + 0. The generating function is the formal power
series Sum_{n>=1} a(n) x^n (the closed form gives the value 0 at n = 0, so this is the series with
coefficients a(n) for all n ≥ 0), and the g.f. identity is stated multiplied by its denominator.
-/

namespace OMA.S_oeis_a145920

open PowerSeries

/-- The index x = floor(n/2) * (-1)^n: 0, 0, 1, -1, 2, -2, 3, -3, ... -/
def x (n : ℕ) : ℚ := ((n / 2 : ℕ) : ℚ) * (-1) ^ n

/-- A145920 through the closed form of the entry: a(n) = (27x^4 - 18x^3 - 3x^2 + 2x)/8 with
x = floor(n/2) * (-1)^n. -/
def a (n : ℕ) : ℚ := (27 * x n ^ 4 - 18 * x n ^ 3 - 3 * x n ^ 2 + 2 * x n) / 8

/-- Mathar's conjectured recurrence (for n ≥ 10) and generating function for A145920. -/
theorem main :
    (∀ n : ℕ, 10 ≤ n →
      a n = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3) - 6 * a (n - 4) + 6 * a (n - 5) + 4 * a (n - 6) -
        4 * a (n - 7) - a (n - 8) + a (n - 9)) ∧
    (PowerSeries.mk (fun n => a n) * ((1 + X) ^ 4 * (1 - X) ^ 5) =
      (X ^ 2 * (1 + 4 * X + 26 * X ^ 2 + 19 * X ^ 3 + 26 * X ^ 4 + 4 * X ^ 5 + X ^ 6) : ℚ⟦X⟧)) := by
  sorry

end OMA.S_oeis_a145920
