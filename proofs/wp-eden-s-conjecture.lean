import OMAStatements.S_wp_eden_s_conjecture

open OMA.S_wp_eden_s_conjecture

theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_eden_s_conjecture.main) := by
  intro h
  let φ : ℝ → E 1 → E 1 := fun _ x => x
  have attractor : IsGlobalAttractor φ ∅ := by
    refine ⟨isCompact_empty, ?_, ?_⟩
    · intro t ht
      exact Set.image_empty _
    · intro B hB ε hε
      exact ⟨0, fun t ht y hy => by simpa only [Metric.infDist_empty] using hε⟩
  obtain ⟨x, hx, _⟩ := h 1 (fun _ => 0) φ ∅ contDiff_const
    (fun _ => rfl) (fun _ _ _ => rfl) (fun t x => hasDerivAt_const t x) attractor
  exact hx