import OMAReductions.R_oeis_a027697_R1_H3_R1

/-!
Proof of `OMA.R_oeis_a027697_R1_H3_R1.H2`.
Counting up to `x + B` splits as the count up to `x` plus the count of the `B` integers
`x, x + 1, ..., x + B - 1`, and the latter is at most `B`.
-/

theorem OMA.solution : OMA.R_oeis_a027697_R1_H3_R1.H2 := by
  intro x B
  rw [Nat.count_add]
  exact Nat.add_le_add_left (Nat.count_le _) _
