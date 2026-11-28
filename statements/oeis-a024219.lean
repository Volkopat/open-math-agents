import Mathlib

/-!
# The recurrence and generating function recorded in OEIS A024219

Source: https://oeis.org/A024219
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A024/A024219.seq
Credit: @Heart-galaxy

A024219 has offset 1. It is the floor of the ratio of the second and first
elementary symmetric functions of {1,4,...,3*n+1}. We use Howroyd's explicit
source formula floor(n*(9*n^2+9*n-2)/(4*(3*n+2))). The value a(0)=0 supplied
by this formula agrees with the zero constant coefficient of the source
generating function and is used only to define that formal power series.

Mathar conjectured the order-five recurrence and ordinary generating
function on October 8, 2011. Howroyd confirmed both on August 12, 2018.
The recurrence starts at n>=6, so all five preceding indices are in the
original domain. Integer arithmetic retains the source's signed coefficients.

For F=Sum_{n>=0} a(n)*X^n, the source generating function is
X^2*(-3+2*X-3*X^2+X^3)/((X^2+1)*(X-1)^3).
We multiply through by the denominator and cancel both minus signs.
The resulting formal-series equality is equivalent: the denominator
(1+X^2)*(1-X)^3 has constant coefficient 1, hence is a unit.
-/

namespace OMA.S_oeis_a024219

def a (n : ℕ) : ℤ := ⌊(n : ℚ)*(9*(n : ℚ)^2+9*(n : ℚ)-2)/(4*(3*(n : ℚ)+2))⌋

def F : PowerSeries ℤ := PowerSeries.mk a

theorem main :
    (∀ n : ℕ, 6 ≤ n → a n - 3*a (n-1) + 4*a (n-2) -
      4*a (n-3) + 3*a (n-4) - a (n-5) = 0) ∧
    ((1 + PowerSeries.X^2) * (1-PowerSeries.X)^3 * F =
      (3 : PowerSeries ℤ)*PowerSeries.X^2 - 2*PowerSeries.X^3 +
        3*PowerSeries.X^4 - PowerSeries.X^5) := by
  sorry

end OMA.S_oeis_a024219
