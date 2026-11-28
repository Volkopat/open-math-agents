import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Mathar's recurrence for OEIS A080894

Source: https://oeis.org/A080894 (R. J. Mathar, January 24, 2020).
Credit: @NOELOO6

The original exponential generating function is exp(x M(x)), where M is the
ordinary Motzkin series. Its defining equation M = 1 + x M + x² M² determines
all its coefficients recursively and forces M(0) = 1. The sequence term a(n)
is n! times the coefficient of degree n in this exponential generating function.
-/

namespace OMA.S_oeis_a080894

open PowerSeries

noncomputable def a (M : PowerSeries ℚ) (n : ℕ) : ℚ :=
  n.factorial * coeff n ((exp ℚ).subst (X*M))

theorem main : ∀ M : PowerSeries ℚ, M = 1 + X*M + X^2*M^2 →
    ∀ n : ℕ, 3 ≤ n →
    (-2*(n:ℚ)+3)*a M n + (-2*(n:ℚ)^3+9*(n:ℚ)^2-9*n+1)*a M (n-1) +
    ((n:ℚ)-1)*(n-2)*(4*(n:ℚ)^2-2*n-3)*a M (n-2) +
    3*((n:ℚ)-1)*(n-3)*(2*n-1)*(n-2)^2*a M (n-3) = 0 := by
  sorry

end OMA.S_oeis_a080894
