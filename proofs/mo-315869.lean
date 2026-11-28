import OMAStatements.S_mo_315869
import Mathlib

open scoped TensorProduct in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_315869.main) := fun h => by
  have e := congrArg (TensorProduct.lid ℤ _) (h ℤ ℤ (ℤ × ZMod 2) ((2 : ℤ) • LinearMap.inl ℤ ℤ _)
    (fun a b e => by simpa using congrArg Prod.fst e) (a₁ := 1 ⊗ₜ (0, 1)) (a₂ := 0)
    (by rw [TensorProduct.map_tmul, map_zero, show ((2 : ℤ) • LinearMap.inl ℤ ℤ (ZMod 2)) 1 = (2 : ℤ) • (1, 0) from rfl,
      TensorProduct.smul_tmul, LinearMap.id_apply, show (2 : ℤ) • ((0, 1) : ℤ × ZMod 2) = 0 by decide]; exact TensorProduct.tmul_zero _ _))
  simp at e
