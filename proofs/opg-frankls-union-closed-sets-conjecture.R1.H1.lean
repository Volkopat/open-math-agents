import OMAReductions.R_opg_frankls_union_closed_sets_conjecture_R1
import Mathlib

/-! Sarvate–Renaud: a union-closed family with a member `{x}` or `{x, y}` has a frequent element.
For `{x}`, `X ↦ X ∪ {x}` injects the members without `x` into the members with `x`. For `{x, y}`,
`X ↦ X ∪ {x, y}` injects the members with neither into the members with both, so
`|F| ≤ |F_x| + |F_y|` and the larger of the two works. -/

theorem OMA.solution : OMA.R_opg_frankls_union_closed_sets_conjecture_R1.H1 := by
  intro α _ F huc ⟨S, hS, hc⟩
  rcases hc with hc | hc
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc
    refine ⟨x, ?_⟩
    have := Finset.card_filter_add_card_filter_not (s := F) (x ∈ ·)
    have : (F.filter (x ∉ ·)).card ≤ (F.filter (x ∈ ·)).card := by
      refine Finset.card_le_card_of_injOn (· ∪ {x}) (fun X hX => ?_) fun X hX Y hY h => ?_
      · simpa using huc X (Finset.mem_filter.1 hX).1 {x} hS
      · simpa [Finset.erase_insert, (Finset.mem_filter.1 hX).2, (Finset.mem_filter.1 hY).2] using
          congrArg (Finset.erase · x) h
    omega
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
    have := Finset.card_filter_add_card_filter_not (s := F) (x ∈ ·)
    have := Finset.card_filter_add_card_filter_not (s := F.filter (y ∈ ·)) (x ∈ ·)
    have e := Finset.card_filter_add_card_filter_not (s := F.filter (x ∉ ·)) (y ∈ ·)
    rw [Finset.filter_comm] at e
    have : ((F.filter (x ∉ ·)).filter (y ∉ ·)).card ≤ ((F.filter (y ∈ ·)).filter (x ∈ ·)).card := by
      refine Finset.card_le_card_of_injOn (· ∪ {x, y}) (fun X hX => ?_) fun X hX Y hY h => ?_
      · simp at hX
        simpa using huc X hX.1.1 _ hS
      · simp at hX hY
        rw [← Finset.union_sdiff_cancel_right (s := X) (t := {x, y}) (by simp [hX]),
          ← Finset.union_sdiff_cancel_right (s := Y) (t := {x, y}) (by simp [hY])]
        exact congrArg (· \ {x, y}) h
    rcases le_total (F.filter (x ∈ ·)).card (F.filter (y ∈ ·)).card with h | h
    · exact ⟨y, by omega⟩
    · exact ⟨x, by omega⟩
