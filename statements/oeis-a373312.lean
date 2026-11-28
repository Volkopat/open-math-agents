import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a373312

/-- Formal power series composition `F(G(x))` for `F, G ∈ ℤ[[x]]` with `G(0) = 0`. -/
noncomputable def psComp (F G : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

/-- Defining functional equation of OEIS A373312:
`A(0) = 0`, `A'(0) = 1`, and `A(x)^2 = A(x * A(x) / (1 - A(x))^2)`,
expressed via `G * (1 - A)^2 = x * A` and `A^2 = A(G)`. -/
def IsA373312 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  PowerSeries.coeff 1 A = 1 ∧
  ∃ G : PowerSeries ℤ,
    G * (1 - A) ^ 2 = PowerSeries.X * A ∧
    A ^ 2 = psComp A G

/-- Conjecture on OEIS A373312: `a(n) ≡ 1 (mod 2)` if and only if `n = 2^k - 1` for some `k ≥ 1`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA373312 A →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k - 1 := by
  sorry

end OMA.S_oeis_a373312
