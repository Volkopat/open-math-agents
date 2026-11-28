import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a368628

/-- Sign-negated formal power series `A(-x)` for `A(x) = ∑ a(n) x^n`. -/
noncomputable def negArg (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (-1 : ℤ) ^ n * PowerSeries.coeff n A

/-- `IsA368628 A` asserts that `A(x) = ∑_{n≥0} a(n) x^n` is the generating function of
OEIS A368628, uniquely determined by
`2 * A(x) = 2 + x * (A(x)^2 - A(-x)^2) + x * (A(x)^4 + A(-x)^4)`. -/
def IsA368628 (A : PowerSeries ℤ) : Prop :=
  2 * A = 2 + PowerSeries.X * (A ^ 2 - negArg A ^ 2) + PowerSeries.X * (A ^ 4 + negArg A ^ 4)

/-- Conjecture on OEIS A368628:
`a(n)` is odd iff `n = (4^k - 1) / 3` for some `k : ℕ`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA368628 A →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, n = (4 ^ k - 1) / 3 := by
  sorry

end OMA.S_oeis_a368628
