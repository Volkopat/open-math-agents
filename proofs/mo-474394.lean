import OMAStatements.S_mo_474394
import Mathlib
open OMA.S_mo_474394

/-- Ian Wanless's balanced frequency square of order `6` on the symbols `0, 1, 2`. -/
def W : Fin 6 → Fin 6 → Fin 3 :=
  ![![0, 0, 1, 2, 1, 2],
    ![0, 0, 2, 1, 2, 1],
    ![1, 2, 1, 2, 0, 0],
    ![2, 1, 2, 1, 0, 0],
    ![1, 2, 0, 0, 1, 2],
    ![2, 1, 0, 0, 2, 1]]

lemma W_rows : ∀ i s, (Finset.univ.filter fun j => W i j = s).card = 2 := by decide

lemma W_cols : ∀ j s, (Finset.univ.filter fun i => W i j = s).card = 2 := by decide

lemma W_none : ¬ ∃ R C : Finset (Fin 6), R.card = 3 ∧ C.card = 3 ∧
    (∀ i ∈ R, ∀ s : Fin 3, ∃ j ∈ C, W i j = s) ∧
    (∀ j ∈ C, ∀ s : Fin 3, ∃ i ∈ R, W i j = s) := by
  decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_474394.main) := by
  intro h
  exact W_none (h 3 2 (by norm_num) (by norm_num) W W_rows W_cols)
