import Mathlib

/-!
# A192344: Constant term of the reduction of n-th polynomial at A161516 by x^2->x+1

Source: https://oeis.org/A192344
Credit: @ivillar

Clark Kimberling's sequence (offset 1). The polynomials are those of the entry's Mathematica program
(which calls them the polynomials defined at A161516): p(n,x) = (1/2)((x+d)^n + (x-d)^n) with
d = sqrt(x+4). Since x+d and x-d are the two roots of t^2 - 2x*t + (x^2 - x - 4), these
polynomials (the odd powers of d cancel) are characterized by
  p(0,x) = 1, p(1,x) = x, p(n+2,x) = 2x*p(n+1,x) - (x^2 - x - 4)*p(n,x),
which is how `p` is defined below, in ℤ[x]. Reducing by x^2 -> x+1 means replacing x^2 by x + 1
repeatedly until the degree is at most 1 (see A192232); the result is the remainder modulo the monic
polynomial x^2 - x - 1. The entry's program tabulates p(0,x), p(1,x), ... and lists the constant
terms from the first one on, so a(n) is the constant term of the reduction of p(n-1,x)
(data 1, 0, 5, 4, 49, 108, ...).

Conjecture (Colin Barker): a(n) = 2*a(n-1)+10*a(n-2)-6*a(n-3)-9*a(n-4). G.f.: -(5*x^2+2*x-1) / (9*x^4+6*x^3-10*x^2-2*x+1). [Colin Barker, Nov 22 2012]
The recurrence is stated for n > 4 (all indices at least the offset 1). The g.f. has constant term
-(-1) = 1 = a(1), so it is the g.f. of the terms listed from the first one, Sum_{n ≥ 0} a(n+1) x^n,
taken as a power series over ℚ.
-/

namespace OMA.S_oeis_a192344

open Polynomial

/-- p(n,x) = (1/2)((x+d)^n + (x-d)^n) with d = sqrt(x+4), via its two-term recurrence. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * p (n + 1) - (X ^ 2 - X - 4) * p n

/-- The reduction by x^2 -> x+1: the remainder modulo x^2 - x - 1. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 1)

/-- a(n) (offset 1): the constant term of the reduction of p(n-1,x). -/
noncomputable def a (n : ℕ) : ℤ := (reduce (p (n - 1))).coeff 0

/-- The conjectured g.f. -(5 * x ^ 2 + 2 * x - 1) / (9 * x ^ 4 + 6 * x ^ 3 - 10 * x ^ 2 - 2 * x + 1). -/
noncomputable def G : PowerSeries ℚ :=
  (-(5 * PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1)) * (9 * PowerSeries.X ^ 4 + 6 * PowerSeries.X ^ 3 - 10 * PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1)⁻¹

/-- Barker's conjectures: the recurrence and the generating function of a(1), a(2), ... -/
theorem main :
    (∀ n : ℕ, 4 < n →
      a n = 2 * a (n - 1) + 10 * a (n - 2) - 6 * a (n - 3) - 9 * a (n - 4)) ∧
    PowerSeries.mk (fun n => (a (n + 1) : ℚ)) = G := by
  sorry

end OMA.S_oeis_a192344
