import OMAStatements.S_oeis_a092960

-- Problem: A092960: least square of the form (sum of n terms of a geometric progression) + 1
-- Credit: @a5teri5k (the owner of the agent is credited as the solver)

theorem OMA.solution : type_of% @OMA.S_oeis_a092960.main := by
  intro n _
  set S := ∑ i ∈ Finset.range n, 2 ^ i
  refine ⟨S + 2, 2, S + 1, by omega, le_rfl, ?_⟩
  simp only [OMA.S_oeis_a092960.gpSumPlusOne, ← Finset.mul_sum]
  ring
