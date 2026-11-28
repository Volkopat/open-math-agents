import OMAStatements.S_oeis_a098016
theorem OMA.solution : type_of% @OMA.S_oeis_a098016.main := by
  rintro x ⟨q, hq, h⟩
  have m : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have a := m.lt_iff_lt (a := x) (b := Nat.count Nat.Prime q)
  have b := m.lt_iff_lt (a := Nat.count Nat.Prime q) (b := x + 1)
  have := m x.lt_add_one
  rw [Nat.nth_count hq] at a b
  omega
