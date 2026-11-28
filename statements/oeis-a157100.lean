import Mathlib

/-!
# A157100: Transform of Catalan numbers whose Hankel transform satisfies the Somos-4 recurrence

Source: https://oeis.org/A157100 (conjecture by R. J. Mathar)

`a(n)` (offset 0) is the coefficient of `x^n` in the generating function `(1+x)*c(x*(1-x^2))` given in
the entry, where `c(x)` is the generating function of the Catalan numbers A000108 (Mathlib's
`catalanSeries`), taken over `ℚ`, and `c(x*(1-x^2))` is the substitution `PowerSeries.subst`.

The conjecture, stated for `n >= 4` (where every index is defined):
Conjecture: (n+1)*a(n) +(-5*n+1)*a(n-1) +2*(2*n-1)*a(n-2) +2*(2*n-7)*a(n-3) +2*(-2*n+7)*a(n-4) = 0.
-/

namespace OMA.S_oeis_a157100

open PowerSeries

/-- The generating function `(1+x)*c(x*(1-x^2))`. -/
noncomputable def A : PowerSeries ℚ :=
  (1 + X) * (catalanSeries.map (Nat.castRingHom ℚ)).subst (X * (1 - X ^ 2))

theorem main : ∀ n : ℕ, 4 ≤ n →
      ((n : ℚ) + 1) * coeff n A + (-5 * (n : ℚ) + 1) * coeff (n - 1) A +
        2 * (2 * (n : ℚ) - 1) * coeff (n - 2) A + 2 * (2 * (n : ℚ) - 7) * coeff (n - 3) A +
        2 * (-2 * (n : ℚ) + 7) * coeff (n - 4) A = 0 := by
  sorry

end OMA.S_oeis_a157100
