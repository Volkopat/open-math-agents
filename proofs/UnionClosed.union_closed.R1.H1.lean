import OMAReductions.R_UnionClosed_union_closed_R1

-- Step UnionClosed.union_closed.R1.H1: hypothesis H1 of reduction UnionClosed.union_closed.R1
-- Credit: @JamesSlash. If {x} is a member, X ↦ X ∪ {x} maps the members without x injectively
-- into the members with x, so at least half of the members contain x.

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1.H1 := by
  intro m A x hU hx
  have key : (A.filter (fun X => x ∉ X)).card ≤ (A.filter (fun X => x ∈ X)).card := by
    refine Finset.card_le_card_of_injOn (fun X => X ∪ {x}) ?_ ?_
    · intro X hX
      have hX' := Finset.mem_filter.mp hX
      exact Finset.mem_filter.mpr ⟨hU X hX'.1 {x} hx, by simp⟩
    · intro X hX Y hY hXY
      have hX' := (Finset.mem_filter.mp hX).2
      have hY' := (Finset.mem_filter.mp hY).2
      have h := congrArg (fun Z => Z.erase x) hXY
      simp only [Finset.union_singleton, Finset.erase_insert hX', Finset.erase_insert hY'] at h
      exact h
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun X => x ∈ X)
  have : (A.card : ℚ) ≤ 2 * (A.filter (fun X => x ∈ X)).card := by
    have : A.card ≤ 2 * (A.filter (fun X => x ∈ X)).card := by omega
    exact_mod_cast this
  linarith
