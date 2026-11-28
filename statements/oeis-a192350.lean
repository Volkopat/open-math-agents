import Mathlib

/-!
# A192350: Constant term of the reduction (by x^2->x+1) of polynomial p(n,x) identified in Comments

Source: https://oeis.org/A192350
Credit: @ivillar

Clark Kimberling's sequence (offset 1). The comment defines p(n,x) = (1/2)((x+d)^n + (x-d)^n)
with d = sqrt(x+5). Since x+d and x-d are the two roots of t^2 - 2x*t + (x^2 - x - 5), these
polynomials (the odd powers of d cancel) are characterized by
  p(0,x) = 1, p(1,x) = x, p(n+2,x) = 2x*p(n+1,x) - (x^2 - x - 5)*p(n,x),
which is how `p` is defined below, in ℤ[x]. Reducing by x^2 -> x+1 means replacing x^2 by x + 1
repeatedly until the degree is at most 1 (see A192232); the result is the remainder modulo the monic
polynomial x^2 - x - 1. The entry's program tabulates p(0,x), p(1,x), ... and lists the constant
terms from the first one on, so a(n) is the constant term of the reduction of p(n-1,x)
(data 1, 0, 6, 4, 64, 128, ...).

Conjecture (Colin Barker): a(n) = 2*a(n-1)+12*a(n-2)-8*a(n-3)-16*a(n-4). G.f.: -x*(6*x^2+2*x-1) / (16*x^4+8*x^3-12*x^2-2*x+1). [Colin Barker, Jan 17 2013]
The recurrence is stated for n > 4 (all indices at least the offset 1); the g.f. is that of
Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ.
-/

namespace OMA.S_oeis_a192350

open Polynomial

/-- p(n,x) = (1/2)((x+d)^n + (x-d)^n) with d = sqrt(x+5), via its two-term recurrence. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * p (n + 1) - (X ^ 2 - X - 5) * p n

/-- The reduction by x^2 -> x+1: the remainder modulo x^2 - x - 1. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 1)

/-- a(n) (offset 1): the constant term of the reduction of p(n-1,x). -/
noncomputable def a (n : ℕ) : ℤ := (reduce (p (n - 1))).coeff 0

/-- The conjectured g.f. -x * (6 * x ^ 2 + 2 * x - 1) / (16 * x ^ 4 + 8 * x ^ 3 - 12 * x ^ 2 - 2 * x + 1). -/
noncomputable def G : PowerSeries ℚ :=
  (-PowerSeries.X * (6 * PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1)) * (16 * PowerSeries.X ^ 4 + 8 * PowerSeries.X ^ 3 - 12 * PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1)⁻¹

/-- Barker's conjectures: the recurrence and the generating function. -/
theorem main :
    (∀ n : ℕ, 4 < n →
      a n = 2 * a (n - 1) + 12 * a (n - 2) - 8 * a (n - 3) - 16 * a (n - 4)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) = G := by
  sorry

end OMA.S_oeis_a192350
