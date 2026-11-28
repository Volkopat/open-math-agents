import Mathlib

/-!
# A002660: a(n) = Sum_{d|n, d <= 3} d^2 + 3*Sum_{d|n, d>3} d

Source: https://oeis.org/A002660
Credit: @ivillar

The sequence (offset 1, N. J. A. Sloane) is a(n) = Σ_{d | n, d ≤ 3} d² + 3·Σ_{d | n, d > 3} d.

Conjecture (Sean A. Irvine, May 16 2014): a(n) is the inverse Möbius transform of the sequence
with g.f. (x + 2x^2 + 2x^3 - 2x^4)/(1 - x)^2, i.e. a(n) = Σ_{d | n} b(d) for n ≥ 1, where
Σ_{m ≥ 0} b(m) x^m = (x + 2x^2 + 2x^3 - 2x^4)/(1 - x)^2.

The generating function is taken as a formal power series over ℚ (where 1 - x is invertible),
and b(d) is its coefficient of x^d.
-/

namespace OMA.S_oeis_a002660

open PowerSeries

/-- a(n) = Sum_{d|n, d <= 3} d^2 + 3*Sum_{d|n, d>3} d. -/
def a (n : ℕ) : ℕ :=
  (∑ d ∈ n.divisors with d ≤ 3, d ^ 2) + 3 * ∑ d ∈ n.divisors with 3 < d, d

/-- The generating function (x + 2x^2 + 2x^3 - 2x^4) / (1 - x)^2, as a power series over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (X + 2 * X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4) * ((1 - X) ^ 2)⁻¹

/-- Irvine's conjecture: a(n) = Σ_{d | n} [x^d] G(x) for every n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = ∑ d ∈ n.divisors, coeff d G := by
  sorry

end OMA.S_oeis_a002660
