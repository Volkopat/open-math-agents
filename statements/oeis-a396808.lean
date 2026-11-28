import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a396808

/-- Conjecture (OEIS A396808): If `A(x) = ∑ a(n) x^n ∈ ℤ[[x]]` satisfies `A(0) = 1`, `A'(0) = 1`,
and `(n + 1) * [x^n] A(x)^(n + 1) = n * [x^n] A(x)^(n + 2)` for all `n > 1`, then for all `n > 0`,
`a(n)` is odd if and only if `n` is a power of `2`. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 1 →
      PowerSeries.coeff 1 A = 1 →
      (∀ n : ℕ, 1 < n →
        ((n + 1 : ℕ) : ℤ) * PowerSeries.coeff n (A ^ (n + 1)) =
          (n : ℤ) * PowerSeries.coeff n (A ^ (n + 2))) →
      ∀ n : ℕ, 0 < n → (Odd (PowerSeries.coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a396808
