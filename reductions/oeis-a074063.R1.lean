import OMAStatements.S_oeis_a074063

namespace OMA.R_oeis_a074063_R1

/-- The finite interval with published arrangements. -/
def H1 : Prop :=
  ∀ n : ℕ, 58 ≤ n → n ≤ 200 → OMA.S_oeis_a074063.Exists n

/-- The remaining unbounded interval. -/
def H2 : Prop :=
  ∀ n : ℕ, 200 < n → OMA.S_oeis_a074063.Exists n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a074063.main := by
  intro small large n hn
  by_cases h : n ≤ 200
  · exact small n hn h
  · exact large n (Nat.lt_of_not_ge h)

end OMA.R_oeis_a074063_R1
