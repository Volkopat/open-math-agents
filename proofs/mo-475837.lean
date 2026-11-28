import OMAStatements.S_mo_475837
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_475837.main := by
  intro s hs hap L hL
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / (L - 1))
  rw [div_lt_iff₀ (by linarith)] at hj
  obtain ⟨a, d, hd, h⟩ := hap (j + 2)
  obtain ⟨k, hk⟩ := h j (by omega)
  obtain ⟨k', hk'⟩ := h (j + 1) (by omega)
  have := hs.monotone (hs.lt_iff_lt.1 (show s k < s k' by rw [hk, hk']; nlinarith))
  refine ⟨k, ?_⟩
  have : (s (k + 1) : ℝ) ≤ s k' := by exact_mod_cast this
  have hd : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hk'] at this; rw [hk]; push_cast at *
  nlinarith [mul_pos hd (sub_pos.2 hj), mul_nonneg (sub_pos.2 hL).le a.cast_nonneg]
