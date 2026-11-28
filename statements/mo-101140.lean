import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Basic

/-! Source: https://mathoverflow.net/questions/101140 -/

namespace OMA.S_mo_101140

/-- An indexed family allows repetitions and counts each occurrence separately. -/
def IsRegular {n m : ℕ} (F : Fin m → Finset (Fin n)) : Prop :=
  (∀ i, (F i).Nonempty) ∧
    ∀ x : Fin n, (Finset.univ.filter fun i => x ∈ F i).card = n

/-- The symbols of a set are the union of the symbols of the specified intervals.
Empty intervals allow the use of fewer than b blocks. -/
def UsesBlocks {n l : ℕ} (word : Fin l → Fin n) (s : Finset (Fin n)) (b : ℕ) : Prop :=
  ∃ endpoints : Fin b → Fin (l + 1) × Fin (l + 1),
    ∀ x, x ∈ s ↔ ∃ i : Fin b, ∃ j : Fin l,
      ((endpoints i).1 : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < ((endpoints i).2 : ℕ) ∧ word j = x

/-- There are no uniform exponents giving both a subquadratic word length
and a sublinear number of blocks per set. -/
theorem main :
    ¬ ∃ α β : ℝ, α < 2 ∧ β < 1 ∧
      ∀ n m : ℕ, 0 < n → ∀ F : Fin m → Finset (Fin n), IsRegular F →
        ∃ (l b : ℕ) (word : Fin l → Fin n),
          (l : ℝ) ≤ (n : ℝ) ^ α ∧ (b : ℝ) ≤ (n : ℝ) ^ β ∧
            ∀ i, UsesBlocks word (F i) b := by
  sorry

end OMA.S_mo_101140
