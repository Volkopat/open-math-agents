import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a295762

/-- Formal power series composition `F(G(x))` for `F, G ∈ ℤ[[x]]` with `G(0) = 0`. -/
noncomputable def psComp (F G : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

/-- Formal power series substitution `F(x^m)` for `F ∈ ℤ[[x]]` and `m ≥ 1`. -/
noncomputable def psSubPow (F : PowerSeries ℤ) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if m ∣ n then PowerSeries.coeff (n / m) F else 0

/-- Defining functional equation of OEIS A295762:
`A(0) = 0` and `A(x - 2 * A(x^2)) = x + A(x^2)`. -/
def IsA295762 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  psComp A (PowerSeries.X - 2 * psSubPow A 2) = PowerSeries.X + psSubPow A 2

/-- Conjecture on OEIS A295762: `a(n)` is odd if and only if `n = 2^k` for some `k ≥ 0`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA295762 A →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  sorry

end OMA.S_oeis_a295762
