import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a363560

/-- Defining functional equation of OEIS A363560:
`A(0) = 1` and `A(x)^3 = 1 + x * (A(x) + A(x)^2 + A(x)^9)`. -/
def IsA363560 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 1 ∧
  A ^ 3 = 1 + PowerSeries.X * (A + A ^ 2 + A ^ 9)

/-- Conjecture on OEIS A363560: `a(n) ≡ 0 (mod 3)` for every `n > 0` with `n % 7 ≠ 1`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA363560 A →
      ∀ n : ℕ, 0 < n → n % 7 ≠ 1 → PowerSeries.coeff n A ≡ 0 [ZMOD 3] := by
  sorry

end OMA.S_oeis_a363560
