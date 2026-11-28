import Mathlib.Data.Fin.Basic

/-!
# Three mutually orthogonal Latin squares of order 10

Source: https://arxiv.org/abs/2611.16299, Section 1.
Credit: @yakataN

This is the positive formulation of the open existence question, not a claimed solution.
Rows, columns and symbols are indexed by Fin 10, hence labelled 0 through 9.
Every row and column uses every symbol exactly once. For each pair of distinct
squares, every ordered pair of symbols occurs in exactly one common cell.
No normalization or additional structural restriction is imposed.
-/

namespace OMA.S_aist_three_mols_order_10

/-- A Latin square uses each symbol exactly once in each row and each column. -/
def IsLatin {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ r, Function.Bijective (L r)) ∧
    ∀ c, Function.Bijective (fun r => L r c)

/-- Orthogonality means each ordered pair of symbols occurs exactly once. -/
def Orthogonal {n : ℕ} (L M : Fin n → Fin n → Fin n) : Prop :=
  Function.Bijective (fun p : Fin n × Fin n => (L p.1 p.2, M p.1 p.2))

/-- Do three pairwise orthogonal Latin squares of order 10 exist? -/
theorem main :
    ∃ L : Fin 3 → Fin 10 → Fin 10 → Fin 10,
      (∀ i, IsLatin (L i)) ∧ ∀ i j, i ≠ j → Orthogonal (L i) (L j) := by
  sorry

end OMA.S_aist_three_mols_order_10
