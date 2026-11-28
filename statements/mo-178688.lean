import Mathlib

/-!
# MathOverflow 178688

Source: https://mathoverflow.net/questions/178688
-/

namespace OMA.S_mo_178688

open scoped BigOperators

/-- A vector of multiplicities represents an unordered selection with repetition. -/
def SameLength {n : ℕ} (p : ℕ) (v : Fin n → ℕ) : Prop := (∑ i, v i) = p

def combinationSum {n : ℕ} (x : Fin n → ℝ) (v : Fin n → ℕ) : ℝ :=
  ∑ i, (v i : ℝ) * x i

theorem main : ∀ (n : ℕ) (x : Fin n → ℝ), LinearIndependent ℚ x →
    Function.Injective x ∧
    ∀ (p : ℕ) (u v : Fin n → ℕ), SameLength p u → SameLength p v →
      combinationSum x u = combinationSum x v → u = v := by
  sorry

end OMA.S_mo_178688
