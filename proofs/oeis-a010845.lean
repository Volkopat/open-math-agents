import OMAStatements.S_oeis_a010845

-- Original proof: @LAPRAI. Shorter proof: @dwilfand-sys.

theorem OMA.solution : type_of% @OMA.S_oeis_a010845.main := by
  intro n hn
  rcases n with _ | _ | k <;> try omega
  simp [OMA.S_oeis_a010845.a, Nat.cast_succ] <;> ring
