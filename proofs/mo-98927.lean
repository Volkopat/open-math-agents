import OMAStatements.S_mo_98927
import Mathlib

open Subgroup in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_98927.main) := fun h => by
  have N (x : DihedralGroup 3 × DihedralGroup 3) (hx : ∀ g, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹) : normalClosure {x} ≤ zpowers x :=
    @normalClosure_le_normal _ _ _ _ ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
      rw [← conj_zpow]; rcases hx g with e | e <;> rw [e] <;> simp [zpow_mem]⟩ (by simp)
  have a := N (DihedralGroup.r 1, 1) (by decide)
  have b := N (1, DihedralGroup.r 1) (by decide)
  have := h (DihedralGroup 3 × DihedralGroup 3) (.r 1, 1) (1, .r 1) (eq_bot_iff.2 fun g hg => ?_)
  · rw [relIndex_eq_one.2 a, relIndex_eq_one.2 b, one_mul, eq_comm, relIndex_eq_one] at this
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (this (normalClosure_normal.conj_mem _ (subset_normalClosure (Set.mem_singleton _)) (DihedralGroup.sr 0, 1)))
    have h1 := congrArg Prod.fst hk
    have h2 := congrArg Prod.snd hk
    simp at h1 h2
    rw [h2] at h1
    revert h1
    decide
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 (a hg.1)
  obtain ⟨j, e⟩ := mem_zpowers_iff.1 (b hg.2)
  have := congrArg Prod.fst e
  simp at this
  simp [Prod.ext_iff, ← this]
