import Mathlib

/-!
# A192759: Coefficient of x in the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192759
Credit: @jagong-cmu

Formalizes the conjecture recorded in OEIS A192759 (R. J. Mathar, May 04 2014):
G.f.: `-x / ((x^2+x-1)*(x^4+x^3+x^2+x+1)*(x-1)^2)`, partial sums of A124502.

Conventions:
* The titular polynomial is defined recursively (COMMENTS section of the entry) by
  p(n,x) = x*p(n-1,x) + floor((n+5)/5) for n > 0, where p(0,x) = 1; it is `p n` below, in `ℤ[X]`.
  The floor is the division `/` on `ℕ`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 0 and a(n) is the coefficient of x of the reduction of p(n,x)
  (data 0, 1, 2, 4, 7, 12, 21, ...).
* The g.f. is stated in `PowerSeries ℤ` as an identity after the multiplication by the
  denominator, which is a unit (its constant term is -1).
* A124502 is defined from its OEIS name (offset 1): a(1) = a(2) = 1, and
  a(n+1) = a(n) + a(n-1) + 1 if n is a multiple of 5, otherwise a(n+1) = a(n) + a(n-1), for n >= 2.
  Its value at index 0 is outside the offset and is never used. Partial sums: for every `n >= 0`,
  `a(n) = Sum_{k=1..n} A124502(k)` (data 0 = empty sum, 1, 1+1 = 2, 1+1+2 = 4, ...).
-/

namespace OMA.S_oeis_a192759

open Polynomial

/-- p(0,x) = 1, p(n,x) = x*p(n-1,x) + floor((n+5)/5). -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C ((((n + 1) + 5) / 5 : ℕ) : ℤ)

/-- A192759 (offset 0): the coefficient of x of the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 1

/-- A124502 (offset 1): a(1) = a(2) = 1, a(n+1) = a(n) + a(n-1) + [5 ∣ n] for n >= 2. -/
def A124502 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => A124502 (n + 2) + A124502 (n + 1) + if (n + 2) % 5 = 0 then 1 else 0

/-- The g.f. of A192759 is `-x / ((x^2+x-1)*(x^4+x^3+x^2+x+1)*(x-1)^2)`, and A192759 is the
sequence of partial sums of A124502. -/
theorem main :
    (PowerSeries.mk a *
        ((PowerSeries.X ^ 2 + PowerSeries.X - 1) *
          (PowerSeries.X ^ 4 + PowerSeries.X ^ 3 + PowerSeries.X ^ 2 + PowerSeries.X + 1) *
          (PowerSeries.X - 1) ^ 2) = -PowerSeries.X) ∧
    ∀ n : ℕ, a n = ∑ k ∈ Finset.Icc 1 n, A124502 k := by
  sorry

end OMA.S_oeis_a192759
