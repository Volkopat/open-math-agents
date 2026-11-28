import Mathlib

/-!
# A290745: a conjectured generating function

Source: https://oeis.org/A290745
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the closed form recorded in the entry, which is used as the definition here.

A290745 (offset 1): maximum number of distinct Lyndon factors that can appear in words of length n over an alphabet of size 10;
data 10, 11, 13, 16, 20, 25, 31, 38, 46, 55, 64, 74, 85, 97, ...

Conjecture (Colin Barker, Oct 03 2017): G.f.:
x*(10 - 9*x + x^2 + x^3 + x^4 + x^5 + x^6 + x^7 + x^8 + x^9 - 10*x^10 + 10*x^11) /
((1 - x)^3*(1 + x)*(1 - x + x^2 - x^3 + x^4)*(1 + x + x^2 + x^3 + x^4)).

Formalization: the entry records the closed form
a(n) = binomial(n+1,2) - (s-p)*binomial(m+1,2) - p*binomial(m+2,2) + s where s=10, m=floor(n/s), p=n-m*s
(Andrew Howroyd, Aug 14 2017), and this formula, with values in ℤ, is the definition of a(n) used here
(p is the remainder n mod 10). The sequence has offset 1, so the g.f. is Sum_{n>=1} a(n) x^n; `b` below
is a(n) for n ≥ 1 and 0 for n = 0, and the g.f. conjecture is stated as the identity
(Sum_n b(n) x^n) * (denominator) = (numerator) of formal power series over ℚ.
-/

namespace OMA.S_oeis_a290745

open PowerSeries

/-- a(n) = binomial(n+1,2) - (s-p)*binomial(m+1,2) - p*binomial(m+2,2) + s with s = 10, m = floor(n/s),
p = n - m*s, the closed form recorded in the entry. -/
def a (n : ℕ) : ℤ :=
  ((n + 1).choose 2 : ℤ) - (10 - ((n % 10 : ℕ) : ℤ)) * ((n / 10 + 1).choose 2 : ℤ) -
    ((n % 10 : ℕ) : ℤ) * ((n / 10 + 2).choose 2 : ℤ) + 10

/-- The coefficients of the g.f. (offset 1): b(0) = 0 and b(n) = a(n) for n ≥ 1. -/
def b (n : ℕ) : ℤ := if n = 0 then 0 else a n

/-- The conjectured generating function of A290745. -/
theorem main :
    PowerSeries.mk (fun n => (b n : ℚ)) * ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2 - X ^ 3 + X ^ 4) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) =
      X * (10 - 9 * X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 9 - 10 * X ^ 10 + 10 * X ^ 11) := by
  sorry

end OMA.S_oeis_a290745
