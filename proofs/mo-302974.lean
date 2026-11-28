import OMAStatements.S_mo_302974
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_302974.main := fun p hp => by
  have := charP_of_injective_ringHom (f := TrivSqZeroExt.inlHom (ZMod p) (ZMod p)) TrivSqZeroExt.inl_injective p
  have : (DualNumber.eps : DualNumber (ZMod p)) ^ p = 0 := pow_eq_zero_of_le hp.out.two_le (by simp [sq])
  refine ⟨DualNumber (ZMod p), inferInstance, WittVector.teichmuller p DualNumber.eps, fun h => ?_, ?_⟩
  · simpa using congrArg (fun w : WittVector p (DualNumber (ZMod p)) => (w.coeff 0).snd) h
  rw [mul_comm]
  ext (_ | _ | n) <;> simp [WittVector.mul_charP_coeff_succ, WittVector.mul_charP_coeff_zero, WittVector.teichmuller_coeff_pos, hp.out.ne_zero, *]
