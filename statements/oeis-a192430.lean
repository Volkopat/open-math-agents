import Mathlib

/-!
# A192430: Constant term of the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments

Source: https://oeis.org/A192430
Credit: @ivillar

Clark Kimberling's sequence (offset 0, data 1, 1, 3, 9, 33, 113, 403, ...). The entry's program (and its
example p(2,x) = 2+3x+x^2, p(3,x) = 2+7x+6x^2+x^3) defines
p(n,x) = (u^n+v^n)/2 + (u^n-v^n)/(2d) with u = x+d, v = x-d, d = sqrt(x+2).
Since u and v are the two roots of t^2 - 2x*t + (x^2 - x - 2), both parts satisfy the same two-term
recurrence, so p is characterized by
  p(0,x) = 1, p(1,x) = x + 1, p(n+2,x) = 2x*p(n+1,x) - (x^2 - x - 2)*p(n,x),
which is how `p` is defined below, in ℤ[x]. Reducing by x^2 -> x+1 means replacing x^2 by x + 1
repeatedly until the degree is at most 1 (see A192232); the result is the remainder modulo the monic
polynomial x^2 - x - 1. The program lists the constant terms of the reductions of p(0,x), p(1,x), ...,
so a(n) is the constant term of the reduction of p(n,x).

Conjecture (Colin Barker, May 12 2014): a(n) = 2*a(n-1)+6*a(n-2)-2*a(n-3)-a(n-4).
G.f.: -(x^3+5*x^2+x-1) / (x^4+2*x^3-6*x^2-2*x+1).
The recurrence is stated for n ≥ 4 (all indices at least the offset 0); the g.f. is that of
Sum_{n ≥ 0} a(n) x^n, as a power series over ℚ.
-/

namespace OMA.S_oeis_a192430

open Polynomial

/-- p(n,x) = (u^n+v^n)/2 + (u^n-v^n)/(2d), u = x+d, v = x-d, d = sqrt(x+2), via its recurrence. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X + 1
  | n + 2 => 2 * X * p (n + 1) - (X ^ 2 - X - 2) * p n

/-- The reduction by x^2 -> x+1: the remainder modulo x^2 - x - 1. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 1)

/-- a(n) (offset 0): the constant term of the reduction of p(n,x). -/
noncomputable def a (n : ℕ) : ℤ := (reduce (p n)).coeff 0

/-- The conjectured g.f. -(x^3+5*x^2+x-1) / (x^4+2*x^3-6*x^2-2*x+1). -/
noncomputable def G : PowerSeries ℚ :=
  (-(PowerSeries.X ^ 3 + 5 * PowerSeries.X ^ 2 + PowerSeries.X - 1)) *
    (PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 3 - 6 * PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1)⁻¹

/-- Barker's conjectures: the recurrence and the generating function. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      a n = 2 * a (n - 1) + 6 * a (n - 2) - 2 * a (n - 3) - a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) = G := by
  sorry

end OMA.S_oeis_a192430
