import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Integer roots of Hanna's composed power series

Source: https://oeis.org/A363309
Credit: @anmolspace (Lean formalization).

Paul D. Hanna's 2023 entry gives the cubic example and conjectures the
integrality of the (2n−1)-st root for every positive integer n.
-/

namespace OMA.S_oeis_a363309

open PowerSeries

def Defines (n : ℕ) (F A B : PowerSeries ℤ) : Prop :=
  F = 1 + X*F^n ∧ A = F.subst (X*F^(2*n-1)) ∧ B = A.subst (X*B^(n-1))

/-- Writing B = 1 + X·R^(2n−1) expresses the claimed root without division by X. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (∃ F A B, Defines n F A B) ∧
    ∀ F A B, Defines n F A B → ∃ R : PowerSeries ℤ,
      R.constantCoeff = 1 ∧ B = 1 + X*R^(2*n-1) := by
  sorry

end OMA.S_oeis_a363309
