import OMAStatements.S_opg_the_bermond_thomassen_conjecture

/-- The pointwise outdegree hypothesis also holds on the empty vertex type. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_the_bermond_thomassen_conjecture.main) := by
  intro h
  let G : Digraph Empty := ⟨fun _ _ => False⟩
  obtain ⟨m, c, cycles, _⟩ := h 1 (by decide) Empty G (fun v => v.elim) (fun v => v.elim)
  have hm : 2 ≤ m 0 := (cycles 0).1
  exact (c 0 ⟨0, by omega⟩).elim
