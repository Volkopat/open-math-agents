import Mathlib

/-!
# A192376: Constant term of the reduction by x^2->x+2 of the polynomial p(n,x) defined below in Comments

Source: https://oeis.org/A192376
Credit: @ivillar

Clark Kimberling's sequence (offset 1). The comment defines p(n,x) = ((x+d)^n - (x-d)^n)/(2d)
with d = sqrt(x+1). Since x+d and x-d are the two roots of t^2 - 2x*t + (x^2 - x - 1), these
polynomials (only even powers of d survive) are characterized by
  p(0,x) = 0, p(1,x) = 1, p(n+2,x) = 2x*p(n+1,x) - (x^2 - x - 1)*p(n,x),
which is how `p` is defined below, in ℤ[x]. Reducing by x^2 -> x+2 means replacing x^2 by x + 2
repeatedly until the degree is at most 1 (see A192232); the result is the remainder modulo the monic
polynomial x^2 - x - 2. The entry's program tabulates p(1,x), p(2,x), ..., so a(n) is the constant
term of the reduction of p(n,x) (data 1, 0, 7, 16, 73, ...).

Conjecture (Colin Barker, May 11 2014): a(n) = 2*a(n-1)+6*a(n-2)+2*a(n-3)-a(n-4).
G.f.: x*(x-1)^2 / ((x+1)^2*(x^2-4*x+1)).
The recurrence is stated for n > 4 (all indices at least the offset 1); the g.f. is that of
Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ.
-/

namespace OMA.S_oeis_a192376

open Polynomial

/-- p(n,x) = ((x+d)^n - (x-d)^n)/(2d) with d = sqrt(x+1), via its two-term recurrence. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * X * p (n + 1) - (X ^ 2 - X - 1) * p n

/-- The reduction by x^2 -> x+2: the remainder modulo x^2 - x - 2. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 2)

/-- a(n) (offset 1): the constant term of the reduction of p(n,x). -/
noncomputable def a (n : ℕ) : ℤ := (reduce (p n)).coeff 0

/-- The conjectured g.f. x*(x-1)^2 / ((x+1)^2*(x^2-4*x+1)), as a power series over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (PowerSeries.X - 1) ^ 2) *
    ((PowerSeries.X + 1) ^ 2 * (PowerSeries.X ^ 2 - 4 * PowerSeries.X + 1))⁻¹

/-- Barker's conjecture: the recurrence (for n > 4) and the g.f. of Sum_{n ≥ 1} a(n) x^n. -/
theorem main :
    (∀ n : ℕ, 4 < n →
      a n = 2 * a (n - 1) + 6 * a (n - 2) + 2 * a (n - 3) - a (n - 4)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) = G := by
  sorry

end OMA.S_oeis_a192376
