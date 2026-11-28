import Mathlib

/-!
# A196279: Let r= (7n) mod 10 and x=floor(7n/10) be the last digit and leading part of 7n. Then a(n) = (x-2r)/7.

Source: https://oeis.org/A196279
Credit: @ShoQo

Conjecture (R. J. Mathar, Oct 04 2011): a(n)= +a(n-1) +a(n-10) -a(n-11) with G.f.
x*(-2 +x -2*x^3 +x^4 -2*x^6 +x^7 +x^9 +x^2 +x^5 +x^8) / ( (1+x) *(x^4+x^3+x^2+x+1)
*(x^4-x^3+x^2-x+1) *(x-1)^2 ). (Charles R Greathouse IV, Jan 04 2013: "The conjecture above
is correct.")

Formalization notes:
* Offset 0; `a n` is an integer (x - 2r is divisible by 7, since 7n = 10x + r).
* The recurrence is stated for `n ≥ 11`. The generating function claim is stated as an identity
  of formal power series over `ℤ`: (Sum a(n) x^n) * denominator = numerator.
-/

namespace OMA.S_oeis_a196279

open PowerSeries

/-- a(n) = (x - 2r)/7 with x = floor(7n/10) and r = 7n mod 10. -/
def a (n : ℕ) : ℤ := (((7 * n / 10 : ℕ) : ℤ) - 2 * ((7 * n % 10 : ℕ) : ℤ)) / 7

theorem main :
    (∀ n : ℕ, 11 ≤ n → a n = a (n - 1) + a (n - 10) - a (n - 11)) ∧
    PowerSeries.mk a * ((1 + X) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) *
      (X - 1) ^ 2) =
      X * (-2 + X - 2 * X ^ 3 + X ^ 4 - 2 * X ^ 6 + X ^ 7 + X ^ 9 + X ^ 2 + X ^ 5 + X ^ 8) := by
  sorry

end OMA.S_oeis_a196279
