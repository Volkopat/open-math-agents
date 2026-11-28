import OMAStatements.S_wp_cap_set

open Finset OMA.S_wp_cap_set

theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_cap_set.main) := by
  intro h
  obtain ⟨S, hS, hmax⟩ := (h 1).1
  have hcard : Fintype.card (CapSpace 1) = 3 := by
    simp [CapSpace]
  have hbound : BddAbove (capSetSizes 1) := by
    refine ⟨3, ?_⟩
    intro k hk
    rcases mem_image.mp hk with ⟨T, _, rfl⟩
    simpa [hcard] using card_le_univ T
  have hmem : 3 ∈ capSetSizes 1 := by
    exact mem_image.mpr ⟨univ, mem_univ _, by simp [hcard]⟩
  have hfull : S = univ := by
    apply eq_univ_of_card
    rw [hcard]
    exact le_antisymm (by simpa [hcard] using card_le_univ S)
      (hmax ▸ le_csSup hbound hmem)
  rw [hfull] at hS
  let x : CapSpace 1 := fun _ => 0
  let y : CapSpace 1 := fun _ => 1
  let z : CapSpace 1 := fun _ => 2
  have hsum : x + y + z = 0 := by
    funext i
    change (0 : ZMod 3) + 1 + 2 = 0
    decide
  rcases hS x (mem_univ _) y (mem_univ _) z (mem_univ _) hsum with hxy | hxz | hyz
  · exact (by decide : (0 : ZMod 3) ≠ 1) (congrFun hxy 0)
  · exact (by decide : (0 : ZMod 3) ≠ 2) (congrFun hxz 0)
  · exact (by decide : (1 : ZMod 3) ≠ 2) (congrFun hyz 0)