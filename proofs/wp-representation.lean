import OMAStatements.S_wp_representation

open OMA.S_wp_representation

theorem OMA.solution : type_of% @OMA.S_wp_representation.main := by
  refine ⟨2, ⊥, ⟨2, by decide, [0, 0, 1, 1], ?_⟩, ?_⟩
  · constructor
    · intro v
      fin_cases v <;> decide
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> first
        | exact (hxy rfl).elim
        | change False ↔ ([0, 0, 1, 1] : List (Fin 2)).IsChain (· ≠ ·)
          simp [List.isChain_cons_cons]
  · intro k hk w hw
    have hnodup : w.Nodup := List.nodup_iff_count_le_one.mpr fun v => by
      rw [hw.1 v]
      omega
    have hAlt : Alternate w 0 1 := List.Pairwise.isChain (hnodup.filter _)
    exact (hw.2 0 1 (by decide)).2 hAlt