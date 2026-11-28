import OMAStatements.S_mo_211276
import Mathlib

open Equiv OMA.S_mo_211276

private theorem additiveEven :
    ∀ p q : Perm (Fin 3), (∀ i, label 1 i + label 1 (p i) = label 1 (q i)) →
      Perm.sign p = 1 := by
  decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_211276.main) := by
  intro h
  have hle : Subgroup.closure {p : Perm (Fin 3) | IsAdditive 1 p} ≤ Perm.sign.ker := by
    apply (Subgroup.closure_le _).mpr
    intro p hp
    obtain ⟨q, hq⟩ := hp
    exact MonoidHom.mem_ker.mpr (additiveEven p q hq)
  rw [h 1] at hle
  have hmem : swap (0 : Fin 3) 1 ∈ Perm.sign.ker := hle (by simp)
  have he := MonoidHom.mem_ker.mp hmem
  rw [Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) he