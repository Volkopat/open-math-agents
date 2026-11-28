import OMAStatements.S_oeis_a191017

theorem OMA.solution : type_of% @OMA.S_oeis_a191017.main := by
  intro p _
  have h8 : ((p : ℤ) : ZMod 8) = (((p % 56 : ℕ) : ℤ) : ZMod 8) := by
    rw [ZMod.intCast_eq_intCast_iff']
    omega
  have h7 : jacobiSym (p : ℤ) 7 = jacobiSym ((p % 56 : ℕ) : ℤ) 7 := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left ((p % 56 : ℕ) : ℤ)]
    congr 1
    omega
  unfold OMA.S_oeis_a191017.kron14
  rw [h8, h7]
  have hr : p % 56 < 56 := Nat.mod_lt _ (by norm_num)
  generalize p % 56 = r at hr ⊢
  interval_cases r <;> simp [OMA.S_oeis_a191017.S] <;> norm_num
