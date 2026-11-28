import Mathlib

/-!
# A230089: Barker's closed form and g.f. for 4, 2 or n according to divisibility

Source: https://oeis.org/A230089
Credit: @ivillar

A230089 (offset 1): a(n) = 4 if n is divisible by 4, 2 if n is divisible by 2 (but not 4),
and n otherwise; data 1, 2, 3, 4, 5, 2, 7, 4, 9, 2, ...
Conjecture (Colin Barker, Oct 09 2013): a(n) = (3+3*(-1)^n+(-i)^n+i^n+n-(-1)^n*n)/2 where
i = sqrt(-1), and the g.f. is -x*(4*x^5-x^4-2*x^3-2*x^2-2*x-1) / ((x-1)^2*(x+1)^2*(x^2+1)).

Formalization notes.
* The closed form is an identity of complex numbers (i is `Complex.I`), claimed for n ≥ 1.
* The g.f. of the offset-1 sequence is Sum_{n >= 1} a(n) x^n, written as `PowerSeries.mk` of the
  function that is 0 at n = 0 and a(n) for n ≥ 1; the identity is stated over ℤ⟦X⟧,
  cross-multiplied by the denominator (x-1)^2*(x+1)^2*(x^2+1), whose constant coefficient is 1.
-/

namespace OMA.S_oeis_a230089

open PowerSeries

/-- A230089: 4 if 4 divides n, else 2 if 2 divides n, else n. -/
def a (n : ℕ) : ℤ := if 4 ∣ n then 4 else if 2 ∣ n then 2 else n

/-- Barker's conjecture: the closed form, and the g.f. cross-multiplied by its denominator. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ((a n : ℤ) : ℂ) =
      (3 + 3 * (-1) ^ n + (-Complex.I) ^ n + Complex.I ^ n + n - (-1) ^ n * n) / 2) ∧
      PowerSeries.mk (fun n => if n = 0 then 0 else a n) *
          ((X - 1) ^ 2 * (X + 1) ^ 2 * (X ^ 2 + 1) : PowerSeries ℤ) =
        -X * (4 * X ^ 5 - X ^ 4 - 2 * X ^ 3 - 2 * X ^ 2 - 2 * X - 1) := by
  sorry

end OMA.S_oeis_a230089
