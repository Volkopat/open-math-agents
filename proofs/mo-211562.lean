import OMAStatements.S_mo_211562
import Mathlib

open FirstOrder FirstOrder.Language

open OMA.S_mo_211562

private def groupAutomorphismAsEquiv {G : Type} [Group G] (a : G ≃* G) :
    let _ := pureGroupStructure G
    G ≃[pureGroupLanguage] G := by
  let _ := pureGroupStructure G
  refine { a.toEquiv with map_fun' := ?_, map_rel' := ?_ }
  · intro n f args
    change PureGroupSymbol n at f
    cases f
    · change a 1 = 1
      exact map_one a
    · change a (args 0)⁻¹ = (a (args 0))⁻¹
      exact map_inv a (args 0)
    · change a (args 0 * args 1) = a (args 0) * a (args 1)
      exact map_mul a (args 0) (args 1)
  · intro _ r _
    exact Empty.elim r

theorem OMA.solution : type_of% @OMA.S_mo_211562.main := by
  intro G _ H h
  obtain ⟨φ,hφ⟩ := h
  let _ := pureGroupStructure G
  have hChar : H.Characteristic := by
    constructor
    intro a
    ext x
    change a x ∈ H ↔ x ∈ H
    rw [hφ (a x),hφ x]
    exact StrongHomClass.realize_formula (groupAutomorphismAsEquiv a) φ (v := fun _ => x)
  let _ : H.Characteristic := hChar
  exact ⟨hChar,inferInstance⟩
