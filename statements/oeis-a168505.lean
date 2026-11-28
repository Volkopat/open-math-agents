import Mathlib

/-!
# A168505: Expansion of 1/(1-x/(1+x/(1-x/(1-x/(1+x/(1-x/(1-x/(1+x/(1-... (continued fraction).

Source: https://oeis.org/A168505 (conjecture by R. J. Mathar)

`a(n)` (offset 0) is the coefficient of `x^n` in the continued fraction `1/(1-x/(1+x/(1-x/(1-x/(1+x/(1-x/(1-...`.
Its partial numerators repeat with period 3, so the fraction is `A = 1/(1 - X * U(x))`,
`U = 1/(1 + X * V(x))`, `V = 1/(1 - X * A(x))`, where `U` and `V` are the tails starting at
the second and third levels. These equations are written without division, and they determine
`A, U, V` uniquely as power series over `ℚ` (each coefficient is fixed by the earlier ones). The
statement asserts that such `A, U, V` exist and that every such triple satisfies the recurrence.

The conjecture, stated for `n >= 4` (where every index is defined):
Conjecture: (n+1)*a(n) - 3*n*a(n-1) + 3*(n-1)*a(n-2) + 3*(n-4)*a(n-3) + 2*(-2*n+7)*a(n-4) = 0.
-/

namespace OMA.S_oeis_a168505

open PowerSeries

/-- `A`, `U`, `V` are the continued fraction and its two tails. -/
def CF (A U V : PowerSeries ℚ) : Prop :=
  A * (1 - X * U) = 1 ∧ U * (1 + X * V) = 1 ∧ V * (1 - X * A) = 1

theorem main : (∃ A U V : PowerSeries ℚ, CF A U V) ∧
    ∀ A U V : PowerSeries ℚ, CF A U V → ∀ n : ℕ, 4 ≤ n →
      (((n : ℚ)+1)) * coeff n A +
        (-3*(n : ℚ)) * coeff (n - 1) A +
        (3*((n : ℚ)-1)) * coeff (n - 2) A +
        (3*((n : ℚ)-4)) * coeff (n - 3) A +
        (2*(-2*(n : ℚ)+7)) * coeff (n - 4) A = 0 := by
  sorry

end OMA.S_oeis_a168505
