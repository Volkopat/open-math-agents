import Mathlib

/-!
# A290744: two conjectured formulas

Source: https://oeis.org/A290744
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both statements follow
from the closed form recorded in the entry, which is used as the definition here.

A290744 (offset 1): maximum number of distinct Lyndon factors that can appear in words of length n over an alphabet of size 5;
data 5, 6, 8, 11, 15, 19, 24, 30, 37, 45, 53, 62, 72, 83, ...

Conjectures from Colin Barker, Oct 03 2017:
(1) G.f.: x*(5 - 4*x + x^2 + x^3 + x^4 - 5*x^5 + 5*x^6) / ((1 - x)^3*(1 + x + x^2 + x^3 + x^4)).
(2) a(n) = 2*a(n-1) - a(n-2) + a(n-5) - 2*a(n-6) + a(n-7) for n>6.

Formalization: the entry records the closed form
a(n) = binomial(n+1,2) - (s-p)*binomial(m+1,2) - p*binomial(m+2,2) + s where s=5, m=floor(n/s), p=n-m*s
(Andrew Howroyd, Aug 14 2017), and this formula, with values in ℤ, is the definition of a(n) used here
(p is the remainder n mod 5). The sequence has offset 1, so the g.f. is Sum_{n>=1} a(n) x^n; `b` below
is a(n) for n ≥ 1 and 0 for n = 0, and the g.f. conjecture is stated as the identity
(Sum_n b(n) x^n) * (denominator) = (numerator) of formal power series over ℚ. The recurrence (2) is stated
for n ≥ 7, which is the stated range n > 6; at n = 7 it involves a(0), which is taken from the closed
form (a(0) = 5). `main` is the conjunction of (1) and (2).
-/

namespace OMA.S_oeis_a290744

open PowerSeries

/-- a(n) = binomial(n+1,2) - (s-p)*binomial(m+1,2) - p*binomial(m+2,2) + s with s = 5, m = floor(n/s),
p = n - m*s, the closed form recorded in the entry. -/
def a (n : ℕ) : ℤ :=
  ((n + 1).choose 2 : ℤ) - (5 - ((n % 5 : ℕ) : ℤ)) * ((n / 5 + 1).choose 2 : ℤ) -
    ((n % 5 : ℕ) : ℤ) * ((n / 5 + 2).choose 2 : ℤ) + 5

/-- The coefficients of the g.f. (offset 1): b(0) = 0 and b(n) = a(n) for n ≥ 1. -/
def b (n : ℕ) : ℤ := if n = 0 then 0 else a n

/-- The two conjectures of Colin Barker for A290744. -/
theorem main :
    (PowerSeries.mk (fun n => (b n : ℚ)) * ((1 - X) ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) =
      X * (5 - 4 * X + X ^ 2 + X ^ 3 + X ^ 4 - 5 * X ^ 5 + 5 * X ^ 6)) ∧
    (∀ n : ℕ, 7 ≤ n → a n = 2 * a (n - 1) - a (n - 2) + a (n - 5) - 2 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a290744
