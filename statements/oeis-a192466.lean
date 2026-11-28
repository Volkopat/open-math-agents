import Mathlib

/-!
# A192466: Coefficient of x in the reduction by x^2->x+2 of the polynomial p(n,x)=1+x^n+x^(2n)

Source: https://oeis.org/A192466
Credit: @ivillar

Clark Kimberling's sequence (offset 1): a(n) is the coefficient of x in the reduction of
p(n,x) = 1 + x^n + x^(2n) by the substitution x^2 -> x+2. Reducing by x^2 -> x+2 means
replacing x^2 by x + 2 repeatedly until the degree is at most 1 (see A192232); the result is the
remainder of p(n,x) on division by the monic polynomial x^2 - x - 2, i.e. `p %ₘ (X^2 - X - 2)`.

Conjectures from Colin Barker, Feb 14 2017:
  a(n) = (-1 - (-1)^n + 2^n + 4^n) / 3,
  a(n) = 6*a(n-1) - 7*a(n-2) - 6*a(n-3) + 8*a(n-4) for n > 4.
The closed form is stated over ℚ (with exact division by 3), for every n ≥ 1.
-/

namespace OMA.S_oeis_a192466

open Polynomial

/-- p(n,x) = 1 + x^n + x^(2n). -/
noncomputable def p (n : ℕ) : ℤ[X] := 1 + X ^ n + X ^ (2 * n)

/-- The reduction of a polynomial by x^2 -> x+2: its remainder modulo x^2 - x - 2. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 2)

/-- a(n): the coefficient of x in the reduction of p(n,x) by x^2 -> x+2. -/
noncomputable def a (n : ℕ) : ℤ := (reduce (p n)).coeff 1

/-- Barker's conjectures: the closed form for n ≥ 1 and the order-4 recurrence for n > 4. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-1 - (-1) ^ n + 2 ^ n + 4 ^ n) / 3) ∧
    (∀ n : ℕ, 4 < n → a n = 6 * a (n - 1) - 7 * a (n - 2) - 6 * a (n - 3) + 8 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a192466
