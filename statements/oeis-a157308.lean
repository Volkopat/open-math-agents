import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution

namespace OMA.S_oeis_a157308

open PowerSeries

/-- OEIS A157308 Conjecture: let `A(x), F(x) ∈ ℤ[[x]]` be formal power series with
`[x^0] A = [x^1] A = 1`, `[x^0] F = [x^1] F = 1`, `F(x) = A(x * F(x))`, and
`[x^(2k+1)] A = [x^(2k+1)] F = 0` for all `k ≥ 1`. Then for every `m : ℕ`,
`[x^m] A ≡ 1 (mod 2)` if and only if `m = 0` or `m = 2^k` for some `k : ℕ`. -/
theorem main :
    ∀ A F : PowerSeries ℤ,
      PowerSeries.coeff 0 A = 1 →
      PowerSeries.coeff 1 A = 1 →
      PowerSeries.coeff 0 F = 1 →
      PowerSeries.coeff 1 F = 1 →
      (∀ k : ℕ, 1 ≤ k → PowerSeries.coeff (2 * k + 1) A = 0) →
      (∀ k : ℕ, 1 ≤ k → PowerSeries.coeff (2 * k + 1) F = 0) →
      F = A.subst (PowerSeries.X * F) →
      ∀ m : ℕ, PowerSeries.coeff m A % 2 = 1 ↔ (m = 0 ∨ ∃ k : ℕ, m = 2 ^ k) := by
  sorry

end OMA.S_oeis_a157308
