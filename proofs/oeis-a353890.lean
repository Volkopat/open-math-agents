import OMAStatements.S_oeis_a353890

-- Credit: @MMexicann

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a353890.main) := by
  rintro ⟨a, h⟩
  have hEq := (h.2.1 29 (by decide) (by decide)).2
  have hTot : Nat.totient 177 = 116 := by decide
  have hJac : OMA.S_oeis_a353890.jacobsthal 29 = 178956971 := by decide
  have hFact : (2 : ℕ) ^ 29 + 1 = 177 * 3033169 := by decide
  rw [hFact, Nat.totient_mul (by decide : Nat.Coprime 177 3033169), hTot, hJac] at hEq
  have hBound := Nat.totient_le 3033169
  omega
