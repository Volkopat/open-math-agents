import OMAStatements.S_opg_vertex_cover_integrality_gap

open OMA.S_opg_vertex_cover_integrality_gap

/-- Matching identical vertices is a winning strategy for every pebble count. -/
private theorem countingEquiv_self {n : ℕ} (k : ℕ) (G : SimpleGraph (Fin n)) :
    CountingEquiv k G G := by
  let W : Set (Position n k) := {p | ∀ i a b, p i = some (a, b) → a = b}
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i a b h
    cases h
  · intro p hp i j a b a' b' hi hj
    obtain rfl := hp i a b hi
    obtain rfl := hp j a' b' hj
    exact ⟨Iff.rfl, Iff.rfl⟩
  · intro p hp i
    refine ⟨Equiv.refl _, ?_⟩
    intro v j a b h
    by_cases hji : j = i
    · subst j
      have hab : v = a ∧ v = b := by simpa using h
      exact hab.1.symm.trans hab.2
    · exact hp j a b (by simpa [Function.update_of_ne hji] using h)

/-- The empty set covers every edge of the edgeless graph. -/
private theorem vc_bot (n : ℕ) : vc (⊥ : SimpleGraph (Fin n)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  exact ⟨∅, rfl, fun _ _ h => h.elim⟩

/-- The registered inequality allows both cover numbers to vanish. -/
theorem OMA.solution : type_of% @OMA.S_opg_vertex_cover_integrality_gap.main := by
  intro ε _
  refine ⟨1, zero_lt_one, 0, ?_⟩
  intro n _
  exact ⟨⊥, ⊥, countingEquiv_self _ _, by simp [vc_bot]⟩
