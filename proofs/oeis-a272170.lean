import OMAStatements.S_oeis_a272170

theorem bc_a272170_div (F X k : ℕ) (hX : 0 < X) (lo : k * X ≤ F) (hi : F < (k + 1) * X) :
    F / X = k := by
  first
  | exact Nat.div_eq_of_lt_le lo hi
  | exact le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hX).2 hi))
      ((Nat.le_div_iff_mul_le hX).2 lo)

theorem bc_a272170_term (F : ℕ) (hF : 2 ≤ F) : ∃ j : ℕ, 2 * 2 ^ j ≤ F ∧ F < 4 * 2 ^ j ∧
    (F / 2 ^ (Nat.log 2 F - 1)) % 2 = if 3 * 2 ^ j ≤ F then 1 else 0 := by
  have h1 : 2 ^ Nat.log 2 F ≤ F := Nat.pow_log_le_self 2 (by omega)
  have h2 : F < 2 ^ (Nat.log 2 F + 1) := Nat.lt_pow_succ_log_self (by norm_num) F
  obtain ⟨j, hj⟩ : ∃ j, Nat.log 2 F = j + 1 := by
    refine ⟨Nat.log 2 F - 1, ?_⟩
    by_contra hc
    have h0 : Nat.log 2 F = 0 := by omega
    rw [h0] at h2
    norm_num at h2
    omega
  rw [hj] at h1 h2
  rw [hj, Nat.add_sub_cancel]
  have e1 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have e2 : 2 ^ (j + 1 + 1) = 4 * 2 ^ j := by ring
  have hX : 0 < 2 ^ j := by positivity
  refine ⟨j, by omega, by omega, ?_⟩
  split_ifs with h
  · have hq : F / 2 ^ j = 3 := bc_a272170_div F (2 ^ j) 3 hX (by omega) (by omega)
    simp [hq]
  · have hq : F / 2 ^ j = 2 := bc_a272170_div F (2 ^ j) 2 hX (by omega) (by omega)
    simp [hq]

theorem bc_a272170_rel (A B ja jb : ℕ) (hA1 : 2 * 2 ^ ja ≤ A) (hA2 : A < 4 * 2 ^ ja)
    (hB1 : 2 * 2 ^ jb ≤ B) (hB2 : B < 4 * 2 ^ jb) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    2 ^ jb = 2 ^ ja ∨ 2 ^ jb = 2 * 2 ^ ja := by
  rcases Nat.lt_or_ge jb ja with h | h
  · exfalso
    have h1 : 2 ^ (jb + 1) ≤ 2 ^ ja := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (jb + 1) = 2 * 2 ^ jb := by ring
    omega
  · rcases Nat.lt_or_ge jb (ja + 2) with h' | h'
    · rcases Nat.lt_or_ge jb (ja + 1) with h'' | h''
      · left
        rw [show jb = ja by omega]
      · right
        rw [show jb = ja + 1 by omega]
        ring
    · exfalso
      have h1 : 2 ^ (ja + 2) ≤ 2 ^ jb := Nat.pow_le_pow_right (by norm_num) h'
      have h2 : 2 ^ (ja + 2) = 4 * 2 ^ ja := by ring
      omega

theorem OMA.solution : type_of% @OMA.S_oeis_a272170.main := by
  intro n hn h
  obtain ⟨hab, hbc⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hx : 0 < Nat.fib (m + 1) := Nat.fib_pos.2 (by omega)
  have hxy : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_le_fib_succ
  have hm : Nat.fib m ≤ Nat.fib (m + 1) := Nat.fib_le_fib_succ
  have e2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two (n := m)
  have e3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two (n := m + 1)
  have e4 : Nat.fib (m + 3 + 1) = Nat.fib (m + 2) + Nat.fib (m + 3) :=
    Nat.fib_add_two (n := m + 2)
  have e5 : Nat.fib (m + 3 + 2) = Nat.fib (m + 3) + Nat.fib (m + 3 + 1) :=
    Nat.fib_add_two (n := m + 3)
  obtain ⟨j0, h01, h02, hb0⟩ := bc_a272170_term (Nat.fib (m + 3)) (by omega)
  obtain ⟨j1, h11, h12, hb1⟩ := bc_a272170_term (Nat.fib (m + 3 + 1)) (by omega)
  obtain ⟨j2, h21, h22, hb2⟩ := bc_a272170_term (Nat.fib (m + 3 + 2)) (by omega)
  have r1 := bc_a272170_rel _ _ j0 j1 h01 h02 h11 h12 (by omega) (by omega)
  have r2 := bc_a272170_rel _ _ j1 j2 h11 h12 h21 h22 (by omega) (by omega)
  have p0 : 0 < 2 ^ j0 := by positivity
  have p1 : 0 < 2 ^ j1 := by positivity
  have p2 : 0 < 2 ^ j2 := by positivity
  have ha0 : OMA.S_oeis_a272170.a (m + 3) =
      if 3 * 2 ^ j0 ≤ Nat.fib (m + 3) then 1 else 0 := hb0
  have ha1 : OMA.S_oeis_a272170.a (m + 3 + 1) =
      if 3 * 2 ^ j1 ≤ Nat.fib (m + 3 + 1) then 1 else 0 := hb1
  have ha2 : OMA.S_oeis_a272170.a (m + 3 + 2) =
      if 3 * 2 ^ j2 ≤ Nat.fib (m + 3 + 2) then 1 else 0 := hb2
  rw [ha0, ha1] at hab
  rw [ha1, ha2] at hbc
  rcases r1 with r1 | r1 <;> rcases r2 with r2 | r2 <;> split_ifs at hab hbc <;> omega
