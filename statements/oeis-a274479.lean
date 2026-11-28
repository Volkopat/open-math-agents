import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a274479

/-- Formal power series composition `F(G(x))` for `F, G ∈ ℤ[[x]]` with `G(0) = 0`. -/
noncomputable def psComp (F G : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

/-- Defining functional equation of OEIS A274479:
`A(0) = 0`, `A'(0) = 1`, and `A(x)^2 = A(x^2 / (1 - 2x - 4x^2))`,
expressed via `G * (1 - 2x - 4x^2) = x^2` and `A^2 = A(G)`. -/
def IsA274479 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  PowerSeries.coeff 1 A = 1 ∧
  ∃ G : PowerSeries ℤ,
    G * (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2) = PowerSeries.X ^ 2 ∧
    A ^ 2 = psComp A G

/-- Conjecture on OEIS A274479: `a(n) ≡ 1 (mod 3)` for all `n ≥ 1`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA274479 A →
      ∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n A ≡ 1 [ZMOD 3] := by
  sorry

end OMA.S_oeis_a274479
