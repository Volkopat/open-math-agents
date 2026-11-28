import OMAStatements.S_oeis_a000695

-- Disproof at k = 3, n = 4. The written leaf rule gives the node counts 1, 3, 4, 8 at stages
-- 1, 2, 3, 4, while Nat.ofDigits 3 (Nat.digits 2 4) = 3 ^ 2 = 9. (For k = 4 the rule gives 14
-- nodes at stage 4 against 16, as the statement's docstring notes.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a000695.main) := by
  intro h
  have h4 := h 3 (by norm_num) 4
  have f2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  have f4 : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hd : Nat.digits 2 4 = [0, 0, 1] := by norm_num
  rw [hd] at h4
  simp [OMA.S_oeis_a000695.leafGrowth, f2, f4, Nat.ofDigits] at h4
