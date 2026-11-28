import FormalConjectures.ErdosProblems.«554»

/-! The original five-cycle proof was submitted by @eitanteperman.
This argument builds on the shorter proofs by @VestigeClub and @katiem08. -/

open SimpleGraph

theorem OMA.solution : type_of% @Erdos554.multicolourGraphRamsey_one_cycleGraph_five := by

  unfold multicolourGraphRamsey
  refine IsLeast.csInf_eq ⟨fun C ↦ ⟨0, .of_le fun _ _ h ↦ ?_⟩, ?_⟩
  · simp [h.ne, Fin.eq_zero]
  · intro n hn
    obtain ⟨_, ⟨f⟩⟩ := hn (fun _ ↦ 0)
    simpa using Fintype.card_le_of_embedding f.toEmbedding
