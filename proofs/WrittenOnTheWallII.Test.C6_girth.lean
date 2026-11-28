import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph Walk

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.C6_girth := by
  have h := cycleGraph.isCycle_cycle (n := 3)
  refine le_antisymm (by simpa using h.girth_le_length) ?_
  obtain ⟨a, p, hp, e⟩ := exists_girth_eq_length.2 (· _ h)
  rw [e]
  exact le_of_not_gt fun lt =>
    (by decide +kernel : ∀ a, ∀ p : {p : (cycleGraph 6).Walk a a // p.length < 6},
        ¬(p.1.tail.support.Nodup ∧ 3 ≤ p.1.length)) a ⟨p, lt⟩ ⟨hp.isPath_tail.2, hp.three_le_length⟩
