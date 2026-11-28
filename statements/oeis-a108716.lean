import Mathlib

/-!
# A108716: a(n) = tan(Pi/14)^(-2n) + tan(3*Pi/14)^(-2n) + tan(5*Pi/14)^(-2n)

Source: https://oeis.org/A108716
Credit: @ivillar

Offset 0, data 3, 21, 371, 7077, 135779, 2606261, ... The terms are taken as real numbers, with
tan(x)^(-2n) the integer power (the inverse of tan(x)^(2n)).

Conjecture (Colin Barker, Jun 01 2013): a(n) = 21*a(n-1)-35*a(n-2)+7*a(n-3).
G.f.: -(35*x^2-42*x+3) / (7*x^3-35*x^2+21*x-1).
The recurrence is stated for n ≥ 3 (all indices at least the offset 0); the g.f. is that of
Sum_{n ≥ 0} a(n) x^n, as a power series over ℝ.

Status: known result. Robert Israel verified it in 2015 (see the OEIS entry): the numbers
1/tan(θ)^2 for θ = π/14, 3π/14, 5π/14 are the roots of t^3 - 21t^2 + 35t - 7, so their power
sums satisfy this recurrence with initial values 3, 21, 371, which also gives the g.f.
-/

namespace OMA.S_oeis_a108716

open Real

/-- a(n) = tan(Pi/14)^(-2n) + tan(3*Pi/14)^(-2n) + tan(5*Pi/14)^(-2n). -/
noncomputable def a (n : ℕ) : ℝ :=
  tan (π / 14) ^ (-(2 * n : ℤ)) + tan (3 * π / 14) ^ (-(2 * n : ℤ)) +
    tan (5 * π / 14) ^ (-(2 * n : ℤ))

/-- The conjectured g.f. -(35*x^2-42*x+3) / (7*x^3-35*x^2+21*x-1). -/
noncomputable def G : PowerSeries ℝ :=
  (-(35 * PowerSeries.X ^ 2 - 42 * PowerSeries.X + 3)) *
    (7 * PowerSeries.X ^ 3 - 35 * PowerSeries.X ^ 2 + 21 * PowerSeries.X - 1)⁻¹

/-- Barker's conjectures: the recurrence and the generating function. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 21 * a (n - 1) - 35 * a (n - 2) + 7 * a (n - 3)) ∧
    PowerSeries.mk a = G := by
  sorry

end OMA.S_oeis_a108716
