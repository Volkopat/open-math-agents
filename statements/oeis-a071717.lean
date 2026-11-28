import Mathlib

/-!
# A071717: Mathar's recurrence, corrected to n ≥ 4

Source: https://oeis.org/A071717
Credit: @ivillar

Status: false as stated at n = 3 (the left side is 3 at n = 3 on the OEIS data); `main` is the
corrected recurrence (n ≥ 4), which is proved.

A071717 (offset 0): expansion of (1 + x^2*C)*C^2, where C = (1 - sqrt(1-4*x))/(2*x) is g.f. for Catalan numbers, A000108;
data 1, 2, 6, 17, 51, 160, 519, 1727, 5863, 20228, 70720, 250002, ...

Conjecture (R. J. Mathar, Aug 25 2013):
(n+2)*a(n) +(-3*n-2)*a(n-1) +(-5*n+8)*a(n-2) +2*(2*n-7)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G = (1 + x^2*c)*c^2;
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 4): on the data the left side of the recurrence as
stated is 3 at n = 3, and it vanishes from n = 4 on.
-/

namespace OMA.S_oeis_a071717

open PowerSeries

/-- The corrected recurrence (n ≥ 4): Mathar's recurrence, which fails at n = 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G = (1 + X ^ 2 * c) * c ^ 2 →
    ∀ n : ℕ, 4 ≤ n →
      (2 + (n : ℚ)) * coeff n G + (-2 - 3 * (n : ℚ)) * coeff (n - 1) G +
        (8 - 5 * (n : ℚ)) * coeff (n - 2) G + (-14 + 4 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a071717
