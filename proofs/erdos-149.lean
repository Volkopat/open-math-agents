import OMAStatements.S_erdos_149

-- Problem: Erdős Problem 149
-- Upstream: formal-conjectures statements/erdos-149.lean:0 (declaration OMA.S_erdos_149.main)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Counterexample: the empty graph on one vertex with Δ = 0. The bound forces k = 0, but a
-- colouring is a total function `Sym2 V → Fin k`, and `Sym2 Unit` is inhabited (the diagonal
-- element), so no map into `Fin 0` exists.
theorem OMA.disproof : ¬ (type_of% @OMA.S_erdos_149.main) := by
  intro h
  obtain ⟨k, ⟨c, _⟩, hk⟩ := h (V := Unit) (⊥ : SimpleGraph Unit) 0 (by
    intro v
    simp)
  have hk0 : k = 0 := by
    have : (k : ℝ) ≤ 0 := by simpa using hk
    exact_mod_cast le_antisymm this (Nat.cast_nonneg k)
  subst hk0
  exact (c (Sym2.diag ())).elim0
