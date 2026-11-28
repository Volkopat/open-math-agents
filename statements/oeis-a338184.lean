import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a338184

/-- The formal power series
`∑_{n≥0} (-1)^n * X^(n*(n+1)/2) * A^(n+1) / ∏_{k=1}^{n+1} (1 + X^k * A)`.
Since `n * (n + 1) / 2 ≥ n` for all `n ≥ 1`, only `n ≤ m` contributes to `[X^m]`. -/
noncomputable def rhsSeries (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.range (m + 1),
      PowerSeries.coeff m
        ((-1 : PowerSeries ℤ) ^ n * PowerSeries.X ^ (n * (n + 1) / 2) * A ^ (n + 1) *
          Ring.inverse (∏ k ∈ Finset.range (n + 1), (1 + PowerSeries.X ^ (k + 1) * A)))

/-- Generalized pentagonal numbers (OEIS A001318): integers of the form `k*(3*k - 1)/2` for `k : ℤ`. -/
def IsGenPentagonal (n : ℕ) : Prop :=
  ∃ k : ℤ, 2 * (n : ℤ) = k * (3 * k - 1)

/-- OEIS A338184: G.f. `A(x)` satisfies
`1 = ∑_{n≥0} (-1)^n * x^(n*(n+1)/2) * A(x)^(n+1) / ∏_{k=1}^{n+1} (1 + x^k * A(x))`.
Conjecture (Paul D. Hanna, 2020): For `n > 0`, `a(n) ≡ 2 (mod 4)` iff `n` is a generalized
pentagonal number (A001318), and `a(n) ≡ 0 (mod 4)` elsewhere. -/
theorem main :
    ∀ (A : PowerSeries ℤ),
      rhsSeries A = 1 →
      ∀ n : ℕ, 0 < n →
        (PowerSeries.coeff n A % 4 = 2 ↔ IsGenPentagonal n) ∧
        (PowerSeries.coeff n A % 4 = 0 ↔ ¬ IsGenPentagonal n) := by
  sorry

end OMA.S_oeis_a338184
