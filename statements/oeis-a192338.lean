import Mathlib

/-!
# A192338: Constant term of the reduction of n-th polynomial at A157751 by x^2->x+2

Source: https://oeis.org/A192338
Credit: @ivillar

Clark Kimberling's sequence (offset 1). The polynomials of A157751 are F(0,x) = 1 and
F(n,x) = (x+1)*F(n-1,x) + F(n-1,-x) for n > 0 (as in the Mathematica program of the entry).
Reducing by x^2 -> x+2 means replacing x^2 by x + 2 repeatedly until the degree is at most 1 (see
A192232); the result is the remainder modulo the monic polynomial x^2 - x - 2. The program tabulates
the reductions of F(0,x), F(1,x), ... and lists their constant terms from the first one on, so
a(n) is the constant term of the reduction of F(n-1,x) (data 1, 2, 6, 18, 54, ...).

Conjecture (Colin Barker, Nov 22 2012): a(n) = 4*a(n-1)+a(n-2)-10*a(n-3)-4*a(n-4).
G.f.: x*(2*x^3-3*x^2-2*x+1) / ((x^2+2*x-1)*(4*x^2+2*x-1)).
The recurrence is stated for n > 4 (all indices at least the offset 1); the g.f. is that of
Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ.
-/

namespace OMA.S_oeis_a192338

open Polynomial

/-- The polynomials F(n,x) of A157751: F(0,x) = 1, F(n,x) = (x+1)*F(n-1,x) + F(n-1,-x). -/
noncomputable def F : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => (X + 1) * F n + (F n).comp (-X)

/-- The reduction by x^2 -> x+2: the remainder modulo x^2 - x - 2. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 2)

/-- a(n) (offset 1): the constant term of the reduction of F(n-1,x). -/
noncomputable def a (n : ℕ) : ℤ := (reduce (F (n - 1))).coeff 0

/-- The conjectured g.f. x*(2*x^3-3*x^2-2*x+1) / ((x^2+2*x-1)*(4*x^2+2*x-1)) over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (2 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1)) *
    ((PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1) * (4 * PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1))⁻¹

/-- Barker's conjecture: the recurrence (for n > 4) and the g.f. of Sum_{n ≥ 1} a(n) x^n. -/
theorem main :
    (∀ n : ℕ, 4 < n →
      a n = 4 * a (n - 1) + a (n - 2) - 10 * a (n - 3) - 4 * a (n - 4)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) = G := by
  sorry

end OMA.S_oeis_a192338
