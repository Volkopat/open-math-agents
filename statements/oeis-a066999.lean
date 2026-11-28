import Mathlib

/-!
# A066999: Voznyy's generating function for 3^n * Sum_{i=1..n} i^3/3^i

Source: https://oeis.org/A066999
Credit: @ivillar

A066999 (offset 1) is a(n) = 3^n * Sum_{i=1..n} i^3/3^i, with data 1, 11, 60, 244, 857, ...
Conjecture (Maksym Voznyy, Jul 27 2009): g.f.: (-1-x^2-4*x)/((3*x-1)*(x-1)^4).
Peter Bala (Nov 29 2012) gives the recurrence a(n) = 3*a(n-1) + n^3 and the o.g.f.
x*(1 + 4*x + x^2)/((1 - 3*x)*(1 - x)^4) = Sum_{n>=1} a(n) x^n.

Formalization notes.
* a(n) is computed in ℚ exactly as defined (it is an integer).
* The conjectured g.f. has constant term 1 = a(1): it is the series whose coefficient of x^k
  is a(k+1), i.e. Sum_{n>=1} a(n) x^(n-1) (Bala's o.g.f. divided by x). It is stated over ℚ⟦X⟧,
  cross-multiplied by the denominator (3*x-1)*(x-1)^4, whose constant coefficient is -1.
-/

namespace OMA.S_oeis_a066999

open PowerSeries

/-- A066999: a(n) = 3^n * Sum_{i=1..n} i^3/3^i. -/
def a (n : ℕ) : ℚ := 3 ^ n * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ 3 / 3 ^ i

/-- Voznyy's g.f. (coefficient of x^k is a(k+1)), cross-multiplied by its denominator. -/
theorem main :
    PowerSeries.mk (fun k => a (k + 1)) * ((3 * X - 1) * (X - 1) ^ 4 : PowerSeries ℚ) =
      -1 - X ^ 2 - 4 * X := by
  sorry

end OMA.S_oeis_a066999
