import OMAStatements.S_mo_292809
import Mathlib

-- Problem: mo-292809, for a symmetric matrix with nonzero determinant and nonzero leading
-- principal minors, are the ratios of successive leading minors positive?
-- Credit: original one-dimensional counterexample by @ivillar (#26139).
-- Statement and earlier diagonal development by @etaubman (#20558).
--
-- No. For the 1 x 1 rational matrix [-1] the leading minors are 1 (order 0) and -1 (order 1),
-- so the ratio at k = 1 is -1.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_292809.main) := by
  intro h
  have hmin : ∀ k (hk : k ≤ 1), 0 < k →
      OMA.S_mo_292809.leadingMinor (-1 : Matrix (Fin 1) (Fin 1) ℚ) k hk ≠ 0 := by
    intro k hk hk0
    obtain rfl : k = 1 := by omega
    simp [OMA.S_mo_292809.leadingMinor]
  have key := h ℚ 1 (-1) Matrix.isSymm_one.neg (by simp) hmin 1 le_rfl one_pos
  unfold OMA.S_mo_292809.leadingMinor at key
  rw [Matrix.det_fin_one, Matrix.det_fin_zero] at key
  norm_num at key
