import OMAStatements.S_oeis_a295292

theorem A295292_sum_even (n : ℕ) (hn : n % 2 = 0) : ∀ t : ℕ, 2 * t ≤ n →
    3 * (∑ i ∈ Finset.Icc 1 (2 * t), i * (n - i) * ((n - i) % 2)) + 4 * t ^ 3 + 3 * t ^ 2
      = 3 * (n + 1) * t ^ 2 + t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro h
    have ih' := ih (by omega)
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring,
      Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have h1 : (n - (2 * t + 1)) % 2 = 1 := by omega
    have h2 : (n - (2 * t + 1 + 1)) % 2 = 0 := by omega
    rw [h1, h2]
    obtain ⟨d, rfl⟩ : ∃ d, n = d + (2 * t + 1) := ⟨n - (2 * t + 1), by omega⟩
    simp only [Nat.add_sub_cancel, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at ih' ⊢
    nlinarith [ih']

theorem A295292_sum_odd (n : ℕ) (hn : n % 2 = 1) : ∀ t : ℕ, 2 * t ≤ n →
    3 * (∑ i ∈ Finset.Icc 1 (2 * t), i * (n - i) * ((n - i) % 2)) + 2 * t * (t + 1) * (2 * t + 1)
      = 3 * n * t * (t + 1) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro h
    have ih' := ih (by omega)
    have e : ∑ i ∈ Finset.Icc 1 (2 * (t + 1)), i * (n - i) * ((n - i) % 2)
        = ∑ i ∈ Finset.Icc 1 (2 * t), i * (n - i) * ((n - i) % 2)
          + (2 * t + 1 + 1) * (n - (2 * t + 1 + 1)) := by
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring,
        Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have h1 : (n - (2 * t + 1)) % 2 = 0 := by omega
      have h2 : (n - (2 * t + 1 + 1)) % 2 = 1 := by omega
      rw [h1, h2]
      simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero]
    rw [e]
    obtain ⟨d, rfl⟩ : ∃ d, n = d + (2 * t + 1 + 1) := ⟨n - (2 * t + 1 + 1), by omega⟩
    simp only [Nat.add_sub_cancel] at ih' ⊢
    nlinarith [ih']

theorem A295292_z0 (n m : ℕ) (h : n = 4 * m) :
    3 * (OMA.S_oeis_a295292.a n : ℤ) = 8 * (m : ℤ) ^ 3 + m := by
  subst h
  have h := A295292_sum_even (4 * m) (by omega) m (by omega)
  have e : 4 * m / 2 = 2 * m := by omega
  have g : 3 * OMA.S_oeis_a295292.a (4 * m) + 4 * m ^ 3 + 3 * m ^ 2
      = 3 * (4 * m + 1) * m ^ 2 + m := by
    unfold OMA.S_oeis_a295292.a
    rw [e]
    exact h
  zify at g
  linarith

theorem A295292_z1 (n m : ℕ) (h : n = 4 * m + 1) :
    3 * (OMA.S_oeis_a295292.a n : ℤ) = (m : ℤ) * (m + 1) * (8 * m + 1) := by
  subst h
  have h := A295292_sum_odd (4 * m + 1) (by omega) m (by omega)
  have e : (4 * m + 1) / 2 = 2 * m := by omega
  have g : 3 * OMA.S_oeis_a295292.a (4 * m + 1) + 2 * m * (m + 1) * (2 * m + 1)
      = 3 * (4 * m + 1) * m * (m + 1) := by
    unfold OMA.S_oeis_a295292.a
    rw [e]
    exact h
  zify at g
  linarith

theorem A295292_z2 (n m : ℕ) (h : n = 4 * m + 2) :
    3 * (OMA.S_oeis_a295292.a n : ℤ) = 8 * (m : ℤ) ^ 3 + 18 * m ^ 2 + 13 * m + 3 := by
  subst h
  have h := A295292_sum_even (4 * m + 2) (by omega) m (by omega)
  have e : (4 * m + 2) / 2 = 2 * m + 1 := by omega
  have e1 : 4 * m + 2 - (2 * m + 1) = 2 * m + 1 := by omega
  have e2 : (2 * m + 1) % 2 = 1 := by omega
  have g : 3 * OMA.S_oeis_a295292.a (4 * m + 2) + 4 * m ^ 3 + 3 * m ^ 2
      = 3 * (4 * m + 2 + 1) * m ^ 2 + m + 3 * ((2 * m + 1) * (2 * m + 1)) := by
    unfold OMA.S_oeis_a295292.a
    rw [e, Finset.sum_Icc_succ_top (by omega), e1, e2, Nat.mul_one]
    linarith
  zify at g
  linarith

theorem A295292_z3 (n m : ℕ) (h : n = 4 * m + 3) :
    3 * (OMA.S_oeis_a295292.a n : ℤ) = (m : ℤ) * (m + 1) * (8 * m + 7) := by
  subst h
  have h := A295292_sum_odd (4 * m + 3) (by omega) m (by omega)
  have e : (4 * m + 3) / 2 = 2 * m + 1 := by omega
  have e1 : 4 * m + 3 - (2 * m + 1) = 2 * m + 2 := by omega
  have e2 : (2 * m + 2) % 2 = 0 := by omega
  have g : 3 * OMA.S_oeis_a295292.a (4 * m + 3) + 2 * m * (m + 1) * (2 * m + 1)
      = 3 * (4 * m + 3) * m * (m + 1) := by
    unfold OMA.S_oeis_a295292.a
    rw [e, Finset.sum_Icc_succ_top (by omega), e1, e2, Nat.mul_zero, Nat.add_zero]
    exact h
  zify at g
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a295292.main := by
  intro n hn
  obtain ⟨q, hq⟩ : ∃ q, n = 4 * q + 14 ∨ n = 4 * q + 15 ∨ n = 4 * q + 16 ∨ n = 4 * q + 17 :=
    ⟨(n - 14) / 4, by omega⟩
  rcases hq with h | h | h | h
  · have e0 : n = 4 * (q + 3) + 2 := by omega
    have e1 : n - 1 = 4 * (q + 3) + 1 := by omega
    have e4 : n - 4 = 4 * (q + 2) + 2 := by omega
    have e5 : n - 5 = 4 * (q + 2) + 1 := by omega
    have e8 : n - 8 = 4 * (q + 1) + 2 := by omega
    have e9 : n - 9 = 4 * (q + 1) + 1 := by omega
    have e12 : n - 12 = 4 * q + 2 := by omega
    have e13 : n - 13 = 4 * q + 1 := by omega
    have h0 := A295292_z2 n (q + 3) e0
    have h1 := A295292_z1 (n - 1) (q + 3) e1
    have h4 := A295292_z2 (n - 4) (q + 2) e4
    have h5 := A295292_z1 (n - 5) (q + 2) e5
    have h8 := A295292_z2 (n - 8) (q + 1) e8
    have h9 := A295292_z1 (n - 9) (q + 1) e9
    have h12 := A295292_z2 (n - 12) q e12
    have h13 := A295292_z1 (n - 13) q e13
    clear e0 e1 e4 e5 e8 e9 e12 e13 h hn
    push_cast at h0 h1 h4 h5 h8 h9 h12 h13
    linarith
  · have e0 : n = 4 * (q + 3) + 3 := by omega
    have e1 : n - 1 = 4 * (q + 3) + 2 := by omega
    have e4 : n - 4 = 4 * (q + 2) + 3 := by omega
    have e5 : n - 5 = 4 * (q + 2) + 2 := by omega
    have e8 : n - 8 = 4 * (q + 1) + 3 := by omega
    have e9 : n - 9 = 4 * (q + 1) + 2 := by omega
    have e12 : n - 12 = 4 * q + 3 := by omega
    have e13 : n - 13 = 4 * q + 2 := by omega
    have h0 := A295292_z3 n (q + 3) e0
    have h1 := A295292_z2 (n - 1) (q + 3) e1
    have h4 := A295292_z3 (n - 4) (q + 2) e4
    have h5 := A295292_z2 (n - 5) (q + 2) e5
    have h8 := A295292_z3 (n - 8) (q + 1) e8
    have h9 := A295292_z2 (n - 9) (q + 1) e9
    have h12 := A295292_z3 (n - 12) q e12
    have h13 := A295292_z2 (n - 13) q e13
    clear e0 e1 e4 e5 e8 e9 e12 e13 h hn
    push_cast at h0 h1 h4 h5 h8 h9 h12 h13
    linarith
  · have e0 : n = 4 * (q + 4) := by omega
    have e1 : n - 1 = 4 * (q + 3) + 3 := by omega
    have e4 : n - 4 = 4 * (q + 3) := by omega
    have e5 : n - 5 = 4 * (q + 2) + 3 := by omega
    have e8 : n - 8 = 4 * (q + 2) := by omega
    have e9 : n - 9 = 4 * (q + 1) + 3 := by omega
    have e12 : n - 12 = 4 * (q + 1) := by omega
    have e13 : n - 13 = 4 * q + 3 := by omega
    have h0 := A295292_z0 n (q + 4) e0
    have h1 := A295292_z3 (n - 1) (q + 3) e1
    have h4 := A295292_z0 (n - 4) (q + 3) e4
    have h5 := A295292_z3 (n - 5) (q + 2) e5
    have h8 := A295292_z0 (n - 8) (q + 2) e8
    have h9 := A295292_z3 (n - 9) (q + 1) e9
    have h12 := A295292_z0 (n - 12) (q + 1) e12
    have h13 := A295292_z3 (n - 13) q e13
    clear e0 e1 e4 e5 e8 e9 e12 e13 h hn
    push_cast at h0 h1 h4 h5 h8 h9 h12 h13
    linarith
  · have e0 : n = 4 * (q + 4) + 1 := by omega
    have e1 : n - 1 = 4 * (q + 4) := by omega
    have e4 : n - 4 = 4 * (q + 3) + 1 := by omega
    have e5 : n - 5 = 4 * (q + 3) := by omega
    have e8 : n - 8 = 4 * (q + 2) + 1 := by omega
    have e9 : n - 9 = 4 * (q + 2) := by omega
    have e12 : n - 12 = 4 * (q + 1) + 1 := by omega
    have e13 : n - 13 = 4 * (q + 1) := by omega
    have h0 := A295292_z1 n (q + 4) e0
    have h1 := A295292_z0 (n - 1) (q + 4) e1
    have h4 := A295292_z1 (n - 4) (q + 3) e4
    have h5 := A295292_z0 (n - 5) (q + 3) e5
    have h8 := A295292_z1 (n - 8) (q + 2) e8
    have h9 := A295292_z0 (n - 9) (q + 2) e9
    have h12 := A295292_z1 (n - 12) (q + 1) e12
    have h13 := A295292_z0 (n - 13) (q + 1) e13
    clear e0 e1 e4 e5 e8 e9 e12 e13 h hn
    push_cast at h0 h1 h4 h5 h8 h9 h12 h13
    linarith
