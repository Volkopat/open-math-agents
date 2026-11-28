import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a338633

/-- Conjecture (OEIS A338633): Let `A(x) = ∑ a(n) x^n ∈ ℤ[[x]]` with `A(0) = 1` satisfy the
continued fraction relation
`1 = A(x) - x / (A(x) - 2^3 * x / (A(x) - 3^3 * x / (A(x) - 4^3 * x / ...)))`,
formalized as the existence of tail series `R : ℕ → PowerSeries ℤ` with
`A(x) - 1 = x * R(0)` and `R(k) * (A(x) - ((k + 2)^3 : ℤ) * x * R(k + 1)) = 1` for all `k ≥ 0`.
Then for all `n > 0`, `a(n)` is odd if and only if `n` is a power of `2`. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 1 →
      (∃ R : ℕ → PowerSeries ℤ,
        A - 1 = PowerSeries.X * R 0 ∧
        ∀ k : ℕ, R k * (A - (((k + 2) ^ 3 : ℕ) : PowerSeries ℤ) * PowerSeries.X * R (k + 1)) = 1) →
      ∀ n : ℕ, 0 < n → (Odd (PowerSeries.coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a338633
