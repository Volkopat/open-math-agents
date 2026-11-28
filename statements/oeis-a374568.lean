import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a374568

/-- Formal power series composition `F(G(x))` for `F, G ∈ ℤ[[x]]` with `G(0) = 0`. -/
noncomputable def psComp (F G : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

/-- Defining functional equation of OEIS A374568:
`A(0) = 0` and `x = A(x - x^2) - A(x + x^2)^2`. -/
def IsA374568 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  PowerSeries.X =
    psComp A (PowerSeries.X - PowerSeries.X ^ 2) -
      (psComp A (PowerSeries.X + PowerSeries.X ^ 2)) ^ 2

/-- Conjecture on OEIS A374568: `a(n)` is odd if and only if `n = 4^k` for some `k ≥ 0`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA374568 A →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, n = 4 ^ k := by
  sorry

end OMA.S_oeis_a374568
