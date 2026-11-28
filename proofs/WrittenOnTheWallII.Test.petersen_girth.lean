import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph Walk

set_option maxHeartbeats 1000000 in
theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.petersen_girth := by
  let a : PetersenVertex := ⟨{0, 1}, by decide⟩
  obtain ⟨p, hp⟩ := (by decide +kernel :
    ∃ p : {p : petersenGraph.Walk a a // p.length = 5}, p.1.tail.support.Nodup)
  have h : p.1.IsCycle := isCycle_iff_isPath_tail_and_le_length.2
    ⟨p.1.tail.isPath_def.2 hp, by simp [p.2]⟩
  refine le_antisymm (by simpa [p.2] using h.girth_le_length) ?_
  obtain ⟨v, q, hq, e⟩ := exists_girth_eq_length.2 (· _ h)
  rw [e]
  exact le_of_not_gt fun lt =>
    (by decide +kernel : ∀ v, ∀ q : {q : petersenGraph.Walk v v // q.length < 5},
      ¬ (q.1.tail.support.Nodup ∧ 3 ≤ q.1.length)) v ⟨q, lt⟩
      ⟨hq.isPath_tail.2, hq.three_le_length⟩
