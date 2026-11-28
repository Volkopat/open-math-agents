import FormalConjectures.ErdosProblems.«602»

open Set Finset
-- Problem: Countable index set case.
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/602.lean:156 (declaration Erdos602.erdos_602.variants.countable_index)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Erdos602.erdos_602.variants.countable_index := by
  intro α A hA hfin _
  -- the part of `A i` outside all earlier sets is infinite
  have hinf : ∀ i, (A i \ ⋃ j ∈ range i, A j).Infinite := by
    intro i
    have overlap : (A i ∩ ⋃ j ∈ range i, A j).Finite := by
      simp only [inter_iUnion]
      exact Finite.biUnion (finite_toSet _) fun j hj =>
        hfin i j (mem_range.mp hj).ne'
    exact ((hA i).2.sdiff overlap).mono fun _ hx => ⟨hx.1, fun h => hx.2 ⟨hx.1, h⟩⟩
  choose a ha b hb hab using fun i => (hinf i).nontrivial
  have key : ∀ i j, a i ≠ b j := by
    intro i j h
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact (hb j).2 (mem_iUnion₂.2 ⟨i, mem_range.mpr hij, h ▸ (ha i).1⟩)
    · exact hab i h
    · exact (ha i).2 (mem_iUnion₂.2 ⟨j, mem_range.mpr hij, h.symm ▸ (hb j).1⟩)
  classical
  let f : α → Fin 2 := fun n => if ∃ i, n = b i then 1 else 0
  refine ⟨f, fun i hMono => ?_⟩
  simpa [f, key, show ∃ j, b i = b j from ⟨i, rfl⟩] using
    hMono (a i) (ha i).1 (b i) (hb i).1
