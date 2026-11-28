import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a298689

/-- OEIS A298689 functional equation: for `A, R ∈ ℤ⟦X⟧` with `A * R = 1`,
`A(X) = ∑_{n ≥ 0} C(n^2, n) * X^n * R(X)^(n^2)`, written coefficientwise at `[X^m]`. -/
def SatisfiesA298689 (A R : PowerSeries ℤ) : Prop :=
  A * R = 1 ∧
  ∀ m : ℕ, PowerSeries.coeff m A =
    ∑ n ∈ Finset.range (m + 1),
      (Nat.choose (n ^ 2) n : ℤ) * PowerSeries.coeff (m - n) (R ^ (n ^ 2))

/-- Conjecture (Paul D. Hanna; OEIS A298689): For the integer power series `A(X) ∈ ℤ⟦X⟧`
satisfying `A(X) = ∑_{n ≥ 0} C(n^2, n) * X^n / A(X)^(n^2)`, for all `m ≥ 1`,
`a(m)` is odd if and only if `m = 2^k` for some `k ≥ 0`. -/
theorem main :
    ∀ A R : PowerSeries ℤ,
      SatisfiesA298689 A R →
      ∀ m : ℕ, 1 ≤ m →
        (Odd (PowerSeries.coeff m A) ↔ ∃ k : ℕ, m = 2 ^ k) := by
  sorry

end OMA.S_oeis_a298689
