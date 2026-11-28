import OMAStatements.S_oeis_a016813

-- Problem oeis-a016813: an odd m has (3m+1)/2 even exactly when m = 4n + 1 for some n.
-- Upstream: statements/oeis-a016813.lean (declaration OMA.S_oeis_a016813.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Write m = 2j + 1. Then (3m+1)/2 = 3j + 2, which is even exactly when j is even, that is, when m leaves
-- remainder 1 on division by 4. Linear arithmetic (omega) checks both directions.

theorem OMA.solution : type_of% @OMA.S_oeis_a016813.main := by
  intro m hm
  rw [Nat.odd_iff] at hm
  unfold OMA.S_oeis_a016813.a
  rw [Nat.even_iff]
  constructor
  · intro h
    exact ⟨m / 4, by omega⟩
  · rintro ⟨n, rfl⟩
    omega
