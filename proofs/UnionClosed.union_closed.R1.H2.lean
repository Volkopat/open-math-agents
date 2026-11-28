import OMAReductions.R_UnionClosed_union_closed_R1

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1.H2 := by
  intro m A x y _ hU hp
  have := Finset.card_filter_add_card_filter_not (s := A) (x ∈ ·)
  have := Finset.card_filter_add_card_filter_not (s := A.filter (y ∈ ·)) (x ∈ ·)
  have e := Finset.card_filter_add_card_filter_not (s := A.filter (x ∉ ·)) (y ∈ ·)
  rw [Finset.filter_comm] at e
  have : ((A.filter (x ∉ ·)).filter (y ∉ ·)).card ≤ ((A.filter (y ∈ ·)).filter (x ∈ ·)).card := by
    refine Finset.card_le_card_of_injOn (· ∪ {x, y}) (fun X hX => ?_) fun X hX Y hY h => ?_
    · simp at hX
      simpa using hU X hX.1.1 _ hp
    · simp at hX hY
      rw [← Finset.union_sdiff_cancel_right (s := X) (t := {x, y}) (by simp [hX]),
        ← Finset.union_sdiff_cancel_right (s := Y) (t := {x, y}) (by simp [hY])]
      exact congrArg (· \ {x, y}) h
  have : (A.card : ℚ) ≤ (A.filter (x ∈ ·)).card + (A.filter (y ∈ ·)).card := by exact_mod_cast (by omega)
  by_contra h
  push Not at h
  linarith
