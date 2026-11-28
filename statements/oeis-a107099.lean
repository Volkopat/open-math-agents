import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a107099

/-- Formal power series composition `F(G(x))` for `F, G ∈ ℤ[[x]]` with `G(0) = 0`. -/
noncomputable def psComp (F G : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

/-- Defining functional equation of OEIS A107099:
`A(0) = 0`, `A'(0) = 1`, and `A(A(x)) = x + 4 * x^3`. -/
def IsA107099 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  PowerSeries.coeff 1 A = 1 ∧
  psComp A A = PowerSeries.X + 4 * PowerSeries.X ^ 3

/-- Conjecture on OEIS A107099: for every `n` that is not a power of `3`,
`[x^n] A(x) ≡ 0 (mod 3)`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA107099 A →
      ∀ n : ℕ, (¬ ∃ k : ℕ, n = 3 ^ k) → PowerSeries.coeff n A ≡ 0 [ZMOD 3] := by
  sorry

end OMA.S_oeis_a107099
