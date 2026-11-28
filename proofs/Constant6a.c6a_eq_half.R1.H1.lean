import OMAReductions.R_Constant6a_c6a_eq_half_R1

/-! The family `{∅, {0}}` is union-closed and every element lies in at most half of its sets
(the argument of the merged proof of `Constant6a.c6a_upper_bound`). -/

theorem OMA.solution : OMA.R_Constant6a_c6a_eq_half_R1.H1 := by
  unfold OMA.R_Constant6a_c6a_eq_half_R1.H1 Constant6a.C6a
  refine csSup_le ⟨0, fun _ _ _ => ⟨0, by simp⟩⟩ ?_
  intro c hc
  obtain ⟨i, hi⟩ := hc ({∅, {0}} : Finset (Finset ℕ)) (by decide) (by decide)
  by_cases h : i = 0 <;>
    simp [Finset.filter_insert, Finset.filter_singleton, h] at hi <;> linarith
