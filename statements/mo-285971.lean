import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Data.Real.Basic

/-! Source: https://mathoverflow.net/questions/285971 (question 2). -/

namespace OMA.S_mo_285971

def Atom {d : ℕ} (H : AddSubmonoid (Fin d → ℕ)) (v : Fin d → ℕ) : Prop :=
  v ∈ H ∧ v ≠ 0 ∧
    ∀ a b, a ∈ H → b ∈ H → a + b = v → a = 0 ∨ b = 0

/-- Every nonzero element meets the support of a nonzero pure power in the monoid. -/
def Simple {d : ℕ} (H : AddSubmonoid (Fin d → ℕ)) : Prop :=
  ∀ v ∈ H, v ≠ 0 → ∃ i : Fin d, 0 < v i ∧ ∃ k : ℕ, 0 < k ∧ Pi.single i k ∈ H

/-- The elasticity is the supremum of these ratios of factorization lengths.
Including 1 implements the convention for the zero element. -/
def ratios {d : ℕ} (H : AddSubmonoid (Fin d → ℕ)) : Set ℝ :=
  {r | r = 1 ∨ ∃ a b : List (Fin d → ℕ), 0 < a.length ∧ 0 < b.length ∧
    (∀ x ∈ a, Atom H x) ∧ (∀ x ∈ b, Atom H x) ∧ a.sum = b.sum ∧
    r = (a.length : ℝ) / (b.length : ℝ)}

/-- The rational-or-infinite assertion for simple submonoids (Question 2).
A counterexample also answers Question 1. -/
theorem main : ∀ (d : ℕ) (H : AddSubmonoid (Fin d → ℕ)), Simple H →
    ¬ BddAbove (ratios H) ∨ ∃ q : ℚ, IsLUB (ratios H) (q : ℝ) := by
  sorry

end OMA.S_mo_285971
