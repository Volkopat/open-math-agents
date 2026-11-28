import OMAStatements.S_mse_3679252
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mse_3679252.main := fun _ _ F hF h =>
  ⟨Fᶜ, hF.isOpen_compl, by simp [hF.frontier_eq, hF.isNowhereDense_iff.1 h]⟩
