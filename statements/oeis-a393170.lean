import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

namespace OMA.S_oeis_a393170

/-- Conjecture (OEIS A393170): let `A(x) = ∑_{n≥0} a(n) x^n ∈ ℤ⟦X⟧` satisfy `A(0) = 1` and
`[x^n] 1 / (A(x) - n * x) = 0` for all `n ≥ 1`. Then for all `n ≥ 1`, `a(n)` is odd if and
only if `n` is a power of `2`. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 1 →
      (∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff n (Ring.inverse (A - (n : PowerSeries ℤ) * PowerSeries.X)) = 0) →
      ∀ n : ℕ, 1 ≤ n → (Odd (PowerSeries.coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a393170
