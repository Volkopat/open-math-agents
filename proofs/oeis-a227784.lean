import OMAStatements.S_oeis_a227784

open OMA.S_oeis_a227784

-- The published residue nine already fails at modulus nine.
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a227784.main) := by
  intro h
  have upper : a 9 ≤ 2 := by
    apply csInf_le' (s := {k : ℕ | ∃ x : Fin k → ZMod 9, ∑ i, (x i)^4 = -1})
    exact ⟨![1, 2], by decide⟩
  have eq := (h 9 (by decide)).1 (by decide)
  omega
