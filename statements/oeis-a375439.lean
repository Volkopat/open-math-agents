import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a375439

/-- Formal power series substitution `F(x^m)` for `F ∈ ℤ[[x]]` and `m ≥ 1`. -/
noncomputable def psSubPow (F : PowerSeries ℤ) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if m ∣ n then PowerSeries.coeff (n / m) F else 0

/-- Defining functional equation of OEIS A375439:
`A(0) = 0` and `3 * A(x) = 3 * (x + x^2) + 2 * A(x)^3 + A(x^3)`. -/
def IsA375439 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  3 * A = 3 * (PowerSeries.X + PowerSeries.X ^ 2) + 2 * A ^ 3 + psSubPow A 3

/-- Conjecture on OEIS A375439: `a(n)` is odd if and only if `n` has the form `3^k` or `2 * 3^k`
for some `k ≥ 0` (OEIS A038754). -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA375439 A →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k := by
  sorry

end OMA.S_oeis_a375439
