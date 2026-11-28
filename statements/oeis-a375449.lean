import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a375449

/-- Formal operator `x * d/dx` on `ℤ⟦x⟧`: `[x^n] (xDeriv F) = n * [x^n] F`. -/
noncomputable def xDeriv (F : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (n : ℤ) * PowerSeries.coeff n F

/-- Formal power series `A(x) ∈ ℤ⟦x⟧` with `A(0) = 0` satisfying the defining condition of
OEIS A375449: `[x^n] (x * A'(x) / (1 - n * A(x))) = n^(n + 1)` for all `n ≥ 1`. -/
def IsA375449 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  ∀ n : ℕ, 1 ≤ n →
    ∃ Q : PowerSeries ℤ,
      Q * (1 - PowerSeries.C (n : ℤ) * A) = xDeriv A ∧
      PowerSeries.coeff n Q = (n : ℤ) ^ (n + 1)

/-- OEIS A375449 conjecture: for `n > 1`, `a(n)` is odd if and only if `n` is of the form
`2^k - 2` or `2^k - 1` for some `k > 1`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA375449 A →
      ∀ n : ℕ, 1 < n →
        (Odd (PowerSeries.coeff n A) ↔ ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 2 ∨ n = 2 ^ k - 1)) := by
  sorry

end OMA.S_oeis_a375449
