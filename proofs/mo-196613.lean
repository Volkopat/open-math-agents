import OMAStatements.S_mo_196613

/-!
At stretch one, the functional equation makes the difference vanish identically.
The zero at two lies off the critical line.
-/

open OMA.S_mo_196613

lemma xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_196613.main) := by
  intro h
  have hz : xi (2 : ℂ) - xi (1 - 2) = 0 := by rw [xi_one_sub, sub_self]
  have hline := h 1 one_ne_zero 2 (Or.inr (by simpa using hz))
  norm_num at hline
