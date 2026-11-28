import OMAStatements.S_mo_298064

-- Problem: Trace of Symmetric matrices in fixed rank
-- Upstream: formal-conjectures statements/mo-298064.lean:0 (declaration OMA.S_mo_298064.main)
-- Credit: @yhay81 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_298064.main) := by
  intro h
  have hle := h (ZMod 2) 1 1 1 one_ne_zero
  have : Finite (OMA.S_mo_298064.traceRankFamily (ZMod 2) 1 1 1) := by
    unfold OMA.S_mo_298064.traceRankFamily
    infer_instance
  have hne : Nonempty (OMA.S_mo_298064.traceRankFamily (ZMod 2) 1 1 1) :=
    ⟨⟨1, Matrix.isSymm_one, by simp [Matrix.rank_one], by simp [Matrix.trace_one]⟩⟩
  have hpos : 0 < Nat.card (OMA.S_mo_298064.traceRankFamily (ZMod 2) 1 1 1) := Nat.card_pos
  have hemp : IsEmpty (OMA.S_mo_298064.traceRankFamily (ZMod 2) 1 1 0) := ⟨fun ⟨M, _, hr, ht⟩ => by
    have hM : M = 0 := by
      ext i j
      fin_cases i
      fin_cases j
      simpa [Matrix.trace, Matrix.diag] using ht
    rw [hM, Matrix.rank_zero] at hr
    exact zero_ne_one hr⟩
  have hzero : Nat.card (OMA.S_mo_298064.traceRankFamily (ZMod 2) 1 1 0) = 0 :=
    Nat.card_eq_zero.mpr (Or.inl hemp)
  omega

