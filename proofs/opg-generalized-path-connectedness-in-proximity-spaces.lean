import OMAStatements.S_opg_generalized_path_connectedness_in_proximity_spaces
import Mathlib

open OMA.S_opg_generalized_path_connectedness_in_proximity_spaces in
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_generalized_path_connectedness_in_proximity_spaces.main) := by
  intro h
  -- A non-symmetric funcoid on `Bool`: `X` is related to `Y` iff `false ∈ X` and `true ∈ Y`.
  let μ : Funcoid Bool Bool :=
    { rel := fun X Y => false ∈ X ∧ true ∈ Y
      empty_left := by simp
      empty_right := by simp
      union_left := by intro I J Y; simp [or_and_right]
      union_right := by intro X I J; simp [and_or_left] }
  have hconn : ConnectedRegarding μ Set.univ := by
    intro X Y _ _ hU hI
    have hf : false ∈ X ∪ Y := hU ▸ Set.mem_univ _
    have ht : true ∈ X ∪ Y := hU ▸ Set.mem_univ _
    rcases hf with hf | hf <;> rcases ht with ht | ht
    · -- both in X: then Y is empty
      exfalso
      obtain ⟨y, hy⟩ := ‹Y.Nonempty›
      have hyX : y ∈ X := by cases y <;> assumption
      exact (Set.eq_empty_iff_forall_notMem.1 hI) y ⟨hyX, hy⟩
    · exact Or.inl ⟨hf, ht⟩
    · exact Or.inr ⟨hf, ht⟩
    · exfalso
      obtain ⟨x, hx⟩ := ‹X.Nonempty›
      have hxY : x ∈ Y := by cases x <;> assumption
      exact (Set.eq_empty_iff_forall_notMem.1 hI) x ⟨hx, hxY⟩
  have hpath := (h Bool μ Set.univ).1 hconn
  -- Going from `true` to `false` would need `{true}` related to `{false}`.
  obtain ⟨P, lt, -, -, haP, hbP, ha, -, hrel⟩ := hpath true trivial false trivial
  have hlt : lt true false := ha false hbP (by decide)
  have hPU : ({true} : Set Bool) ∪ {false} = P := by
    ext x; cases x <;> simp [haP, hbP]
  have := hrel {true} {false} (Set.singleton_nonempty _) (Set.singleton_nonempty _) hPU
    (by ext x; cases x <;> simp) (by simp [hlt])
  simp [μ] at this
