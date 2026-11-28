import Mathlib

namespace OMA.S_oeis_a246423

/-- Formal inverse of `1 - 3x` in `ℤ⟦X⟧`. -/
def inv1m3X : PowerSeries ℤ :=
  PowerSeries.mk fun k => (3 : ℤ) ^ k

/-- The `n`-th summand of the generating function of OEIS A246423:
`x^n / (1 - 3x)^(2n+1) * (∑_{k=0}^n C(n,k)^2 * 2^k * x^k) * (∑_{k=0}^n C(n,k)^2 * 3^k * x^k)`. -/
noncomputable def termA246423 (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ n * inv1m3X ^ (2 * n + 1) *
    (∑ k ∈ Finset.range (n + 1),
      PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * 2 ^ k) * PowerSeries.X ^ k) *
    (∑ k ∈ Finset.range (n + 1),
      PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * 3 ^ k) * PowerSeries.X ^ k)

/-- The `m`-th coefficient `a(m)` of OEIS A246423. -/
noncomputable def a246423 (m : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (m + 1), PowerSeries.coeff m (termA246423 n)

theorem main :
    a246423 0 = 1 ∧
    ∀ n : ℕ, 0 < n →
      ((∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k) → a246423 n % 4 = 2) ∧
      ((¬ ∃ k : ℕ, 2 ≤ k ∧ n = 2 ^ k) → a246423 n % 4 = 0) := by
  sorry

end OMA.S_oeis_a246423
