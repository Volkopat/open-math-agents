import Mathlib

/-!
# A192382: Coefficient of x in the reduction by x^2 -> x+2 of the polynomial p(n,x) defined below in Comments

Source: https://oeis.org/A192382
Credit: @ivillar

Clark Kimberling's sequence (offset 1). The comment defines p(n,x) = ((x+d)^n - (x-d)^n)/(2*d)
with d = sqrt(x+2). Since x+d and x-d are the two roots of t^2 - 2x*t + (x^2 - x - 2), these
polynomials (only even powers of d survive) are characterized by
  p(0,x) = 0, p(1,x) = 1, p(n+2,x) = 2x*p(n+1,x) - (x^2 - x - 2)*p(n,x),
which is how `p` is defined below, in ℤ[x]. Reducing by x^2 -> x+2 means replacing x^2 by x + 2
repeatedly until the degree is at most 1 (see A192232); the result is the remainder modulo the monic
polynomial x^2 - x - 2. a(n) is the coefficient of x in the reduction of p(n,x), n ≥ 1
(data 0, 2, 4, 24, 80, ...).

Conjectures from Colin Barker, May 12 2014:
  a(n) = 2^(n-2)*(2*(-1)^n + 2^n)/3 = 2*A003683(n-1).
  a(n) = 2*a(n-1) + 8*a(n-2).
  G.f.: 2*x^2 / ((1+2*x)*(1-4*x)).
Here A003683(m) = 2^(m-1)*(2^m - (-1)^m)/3. The closed forms are stated in ℚ for n ≥ 1 (with
integer powers of 2), the recurrence for n ≥ 3 (all indices at least the offset 1), and the g.f. is
that of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ.
-/

namespace OMA.S_oeis_a192382

open Polynomial

/-- p(n,x) = ((x+d)^n - (x-d)^n)/(2d) with d = sqrt(x+2), via its two-term recurrence. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * X * p (n + 1) - (X ^ 2 - X - 2) * p n

/-- The reduction by x^2 -> x+2: the remainder modulo x^2 - x - 2. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 2)

/-- a(n) (offset 1): the coefficient of x in the reduction of p(n,x). -/
noncomputable def a (n : ℕ) : ℤ := (reduce (p n)).coeff 1

/-- A003683(m) = 2^(m-1)*(2^m - (-1)^m)/3 (offset 0). -/
noncomputable def A003683 (m : ℕ) : ℚ := (2 : ℚ) ^ ((m : ℤ) - 1) * (2 ^ m - (-1) ^ m) / 3

/-- The conjectured g.f. 2*x^2 / ((1+2*x)*(1-4*x)), as a power series over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (2 * PowerSeries.X ^ 2) * ((1 + 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X))⁻¹

/-- Barker's conjectures: the closed form, a(n) = 2*A003683(n-1), the recurrence (for n ≥ 3) and the
g.f. of Sum_{n ≥ 1} a(n) x^n. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2 : ℚ) ^ ((n : ℤ) - 2) * (2 * (-1) ^ n + 2 ^ n) / 3) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 2 * A003683 (n - 1)) ∧
    (∀ n : ℕ, 3 ≤ n → a n = 2 * a (n - 1) + 8 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) = G := by
  sorry

end OMA.S_oeis_a192382
