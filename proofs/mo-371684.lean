import OMAStatements.S_mo_371684
import Mathlib

open OMA.S_mo_371684

abbrev E := EuclideanSpace ℂ (Fin 2)

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_371684.main) := by
  intro h
  set e1 : E := EuclideanSpace.single 0 1 with he1
  set e2 : E := EuclideanSpace.single 1 1 with he2
  set a : E →L[ℂ] E := (ℂ ∙ e1).starProjection with ha
  have h12 : inner ℂ e2 e1 = 0 := by simp [he1, he2, EuclideanSpace.inner_single_left]
  have r1 : Rel a ⊥ (ℂ ∙ e2) := by
    intro x
    rw [Submodule.starProjection_bot, ha, Submodule.starProjection_singleton,
      Submodule.starProjection_singleton, inner_smul_right, h12]
    simp
  have r2 : Rel a (ℂ ∙ (e1 + e2)) (ℂ ∙ (e1 + e2)) := fun x => rfl
  obtain ⟨hsup, _⟩ := h E a _ _ _ _ r1 r2
  have key := hsup e1
  have hae1 : a e1 = e1 :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self e1)
  rw [hae1, bot_sup_eq] at key
  have hmem : e1 ∈ (ℂ ∙ e2) ⊔ (ℂ ∙ (e1 + e2)) := by
    have : (e1 + e2) - e2 ∈ (ℂ ∙ e2) ⊔ (ℂ ∙ (e1 + e2)) :=
      Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
    simpa using this
  rw [Submodule.starProjection_eq_self_iff.mpr hmem] at key
  have hin : (ℂ ∙ (e1 + e2)).starProjection e1 ∈ (ℂ ∙ (e1 + e2)) :=
    Submodule.starProjection_apply_mem _ _
  rw [key, Submodule.mem_span_singleton] at hin
  obtain ⟨c, hc⟩ := hin
  have c1 := congrArg (fun v : E => v 1) hc
  have c0 := congrArg (fun v : E => v 0) hc
  simp [he1, he2] at c0 c1
  rw [c1] at c0
  simp at c0
