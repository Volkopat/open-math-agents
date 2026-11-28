import FormalConjectures.OptimizationConstants.«6a»

-- The empty set and one singleton give the upper bound.
theorem OMA.solution : type_of% @Constant6a.c6a_upper_bound := by
  unfold Constant6a.C6a
  refine csSup_le ⟨0, fun _ _ _ => ⟨0, by simp⟩⟩ ?_
  intro c hc
  obtain ⟨i, hi⟩ := hc ({∅, {0}} : Finset (Finset ℕ)) (by decide) (by decide)
  by_cases h : i = 0 <;>
    simp [Finset.filter_insert, Finset.filter_singleton, h] at hi <;> linarith
