import Mathlib

/-!
# A122047: a conjectured recurrence and generating function

Source: https://oeis.org/A122047
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both
statements follow from the closed form recorded in the entry, which is used as the definition here.

A122047 (offset 0): degree of the polynomial P(n,x), defined by a Somos-6 type sequence:
P(n,x) = (x^(n-1)*P(n-1,x)*P(n-5,x) + P(n-2,x)*P(n-4,x))/P(n-6,x), initialized with P(n,x) = 1 at n < 0;
data 0, 0, 1, 3, 6, 10, 15, 22, 31, 42, 55, 70, 88, 109, 133, 160, 190, 224, 262, 304, 350, ...

Conjectures from R. J. Mathar, Jul 15 2008:
(1) a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) + a(n-5) - 3*a(n-6) + 3*a(n-7) - a(n-8);
(2) o.g.f.: x^2/((x^4+x^3+x^2+x+1)(x-1)^4).

Formalization: the entry records the closed form a(n) = floor((n^3 + 6*n^2 + 5*n)/30) (Allan Bickle,
Sep 15 2022), and this formula, with values in ℤ, is the definition of a(n) used here. The recurrence
involves a(n-8), so it is stated for n ≥ 8. The g.f. conjecture is stated as the identity
(Sum_n a(n) x^n) * (1 + x + x^2 + x^3 + x^4) * (1 - x)^4 = x^2 of formal power series over ℚ (note
(x-1)^4 = (1-x)^4). `main` is the conjunction of (1) and (2). The entry records one more conjecture
of the same date, a closed form through A000292 and A099443; it is not part of `main`.
-/

namespace OMA.S_oeis_a122047

open PowerSeries

/-- a(n) = floor((n^3 + 6n^2 + 5n)/30), the closed form recorded in the entry. -/
def a (n : ℕ) : ℤ := ((n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 5 * (n : ℤ)) / 30

/-- The conjectured recurrence and generating function of A122047. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n → a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) + a (n - 5) - 3 * a (n - 6) +
      3 * a (n - 7) - a (n - 8)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * (1 - X) ^ 4 = X ^ 2) := by
  sorry

end OMA.S_oeis_a122047
