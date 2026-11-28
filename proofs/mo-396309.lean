import OMAStatements.S_mo_396309
import Mathlib

open OMA.S_mo_396309

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_396309.main) := by
  intro h
  have key := h 3 Nat.prime_three (by norm_num) 1 le_rfl 1
    (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) !![1, 0, 1; 0, 1, 0; 2, 0, 0]
    (by simp) (by rw [Matrix.det_fin_three]; decide)
  unfold isoCount at key
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype] at key
  revert key
  decide +kernel
