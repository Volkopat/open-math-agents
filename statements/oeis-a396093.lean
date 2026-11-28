import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

namespace OMA.S_oeis_a396093

/-- Formal power series operator `B(F) = F / (1 - F)^2` over `ℤ⟦X⟧` (using `Ring.inverse`). -/
noncomputable def B_op (F : PowerSeries ℤ) : PowerSeries ℤ :=
  F * Ring.inverse ((1 - F) ^ 2)

/-- Generating function `A(x) = B(B(B(x)))` of OEIS A396093, the third iterate of
`B(x) = x / (1 - x)^2`. -/
noncomputable def A : PowerSeries ℤ :=
  B_op (B_op (B_op PowerSeries.X))

/-- `a(n)` (OEIS A396093): the coefficient of `x^n` in `A(x) = B(B(B(x)))`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n A

/-- Conjectures (OEIS A396093):
1. `a(2n)` is even for all `n ≥ 1`.
2. For all `n ≥ 1`, `a(2n - 1)` is even iff `n = 5k - 2` for some `k ≥ 1`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → Even (a (2 * n))) ∧
    (∀ n : ℕ, 1 ≤ n → (Even (a (2 * n - 1)) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 5 * k - 2)) := by
  sorry

end OMA.S_oeis_a396093
