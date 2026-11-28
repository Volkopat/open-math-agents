import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace OMA.S_oeis_a369083

/-!
OEIS A369083: Expansion of g.f. A(x) satisfying
  A(x) = 1 + x * (5 * A(x)^2 - A(-x)^2) / 4,
equivalently 4 * (A(x) - 1) = x * (5 * A(x)^2 - A(-x)^2) over Z[[x]], where A(-x) has
coefficients (-1)^n * a(n).
Conjecture: a(n) == binomial(4*n + 3, n) (mod 2) for all n >= 0.
-/

theorem main : ∀ (A : PowerSeries ℤ),
    4 * (A - 1) =
      PowerSeries.X *
        (5 * A ^ 2 - (PowerSeries.mk fun n => (-1 : ℤ) ^ n * PowerSeries.coeff n A) ^ 2) →
    ∀ n : ℕ, PowerSeries.coeff n A % 2 = (Nat.choose (4 * n + 3) n : ℤ) % 2 := by
  sorry

end OMA.S_oeis_a369083
