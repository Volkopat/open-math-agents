import OMAStatements.S_mo_252065
import Mathlib

open OMA.S_mo_252065

lemma mo252065_eq {A B₁ B₂ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))} (hA : 2 ≤ Module.finrank ℝ A)
    (h1 : 1 ≤ Module.finrank ℝ B₁) (h2 : 1 ≤ Module.finrank ℝ B₂)
    (o1 : A.IsOrtho B₁) (o2 : A.IsOrtho B₂) : B₁ = B₂ := by
  have hc := A.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at hc
  have hle : Module.finrank ℝ Aᗮ ≤ 1 := by omega
  have e1 : B₁ = Aᗮ := Submodule.eq_of_le_of_finrank_le
    (Submodule.isOrtho_iff_le.1 o1.symm) (by omega)
  have e2 : B₂ = Aᗮ := Submodule.eq_of_le_of_finrank_le
    (Submodule.isOrtho_iff_le.1 o2.symm) (by omega)
  rw [e1, e2]

lemma mo252065_le (A : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) : Module.finrank ℝ A ≤ 3 := by
  have := Submodule.finrank_le A
  rwa [finrank_euclideanSpace_fin] at this

lemma mo252065_rows : ∀ i : Fin 4, ∃ a b : Fin 4, M i a = 0 ∧ M i b = 0 ∧
    ∃ i' : Fin 4, M i' a = 0 ∧ M i' b ≠ 0 := by
  intro i; fin_cases i
  · exact ⟨1, 2, by simp [M], by simp [M], 1, by simp [M], by simp [M]⟩
  · exact ⟨1, 3, by simp [M], by simp [M], 0, by simp [M], by simp [M]⟩
  · exact ⟨0, 2, by simp [M], by simp [M], 3, by simp [M], by simp [M]⟩
  · exact ⟨0, 3, by simp [M], by simp [M], 2, by simp [M], by simp [M]⟩

lemma mo252065_cols : ∀ j : Fin 4, ∃ a b : Fin 4, M a j = 0 ∧ M b j = 0 ∧
    ∃ j' : Fin 4, M a j' = 0 ∧ M b j' ≠ 0 := by
  intro j; fin_cases j
  · exact ⟨2, 3, by simp [M], by simp [M], 2, by simp [M], by simp [M]⟩
  · exact ⟨0, 1, by simp [M], by simp [M], 2, by simp [M], by simp [M]⟩
  · exact ⟨0, 2, by simp [M], by simp [M], 1, by simp [M], by simp [M]⟩
  · exact ⟨1, 3, by simp [M], by simp [M], 1, by simp [M], by simp [M]⟩

theorem OMA.solution : type_of% @OMA.S_mo_252065.main := by
  intro S T hS hT hM
  constructor
  · intro i
    by_contra hne
    have h2 : 2 ≤ Module.finrank ℝ (S i) := by have := hS i; omega
    obtain ⟨a, b, ha, hb, i', hia, hib⟩ := mo252065_rows i
    have heq : T a = T b := mo252065_eq h2 (hT a) (hT b) ((hM i a).1 ha) ((hM i b).1 hb)
    have := (hM i' a).1 hia
    rw [heq] at this
    exact hib ((hM i' b).2 this)
  · intro j
    by_contra hne
    have h2 : 2 ≤ Module.finrank ℝ (T j) := by have := hT j; omega
    obtain ⟨a, b, ha, hb, j', hja, hjb⟩ := mo252065_cols j
    have heq : S a = S b := mo252065_eq h2 (hS a) (hS b) ((hM a j).1 ha).symm ((hM b j).1 hb).symm
    have := (hM a j').1 hja
    rw [heq] at this
    exact hjb ((hM b j').2 this)
