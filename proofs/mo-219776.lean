import OMAStatements.S_mo_219776
import Mathlib

-- Shorter disproof of mo-219776. First disproof: PR #12761. This version: @tylerpixel

open Set
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_219776.main) := by
  intro h
  obtain ⟨c, hc⟩ := h 1 one_pos (1 + ·) (fun x => x ^ 2 + 2 * x) (fun y => (1 + y) ^ 2) (by fun_prop)
    ⟨1, by norm_num⟩ (by fun_prop) (fun x hx y hy hxy => by
      have := mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx.1 hy.1); dsimp; nlinarith) (by norm_num)
    (by intros; ring)
  have h₁ := hc 1 (by norm_num)
  have h₂ := hc (1 / 2) (by norm_num)
  norm_num at h₁ h₂
  linarith
