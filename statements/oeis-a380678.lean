import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.GroupWithZero.Units.Basic

namespace OMA.S_oeis_a380678

/-- Conjecture (OEIS A380678): let `A(x) = ∑_{n≥1} a(n) x^n ∈ ℤ⟦X⟧` satisfy `A(0) = 0`,
`a(1) = 1`, and `A(x - A(x)^2 / (1 - A(x)^2)) = x`. Then for all `n ≥ 1`, `a(n)` is odd if
and only if `n = 3 * 2^m - 2` or `n = 4 * 2^m - 2` for some `m : ℕ` (OEIS A027383). -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.coeff 1 A = 1 →
      PowerSeries.subst (PowerSeries.X - A ^ 2 * Ring.inverse (1 - A ^ 2)) A = PowerSeries.X →
      ∀ n : ℕ, 1 ≤ n →
        (Odd (PowerSeries.coeff n A) ↔ ∃ m : ℕ, n = 3 * 2 ^ m - 2 ∨ n = 4 * 2 ^ m - 2) := by
  sorry

end OMA.S_oeis_a380678
