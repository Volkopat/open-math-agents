import OMAStatements.S_oeis_a295321

theorem A295321_evenCase (n N : ℕ) (hn : n = 2 * N) : ∀ k : ℕ, k ≤ n →
    3 * (∑ i ∈ Finset.Icc 1 k, i * (n - i) * ((n - i + 1) % 2))
      + 2 * (k / 2) * (k / 2 + 1) * (2 * (k / 2) + 1) = 6 * N * (k / 2) * (k / 2 + 1) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega)]
    rcases Nat.even_or_odd' k with ⟨J, rfl | rfl⟩
    · have h1 : (2 * J) / 2 = J := by omega
      have h2 : (2 * J + 1) / 2 = J := by omega
      have h3 : (n - (2 * J + 1) + 1) % 2 = 0 := by omega
      rw [h1] at ih
      rw [h2, h3]
      simp only [mul_zero, add_zero]
      exact ih
    · obtain ⟨d, hd⟩ : ∃ d, N = J + 1 + d := ⟨N - J - 1, by omega⟩
      subst hd
      have h1 : (2 * J + 1) / 2 = J := by omega
      have h2 : (2 * J + 1 + 1) / 2 = J + 1 := by omega
      have h3 : (n - (2 * J + 1 + 1) + 1) % 2 = 1 := by omega
      have h4 : n - (2 * J + 1 + 1) = 2 * d := by omega
      rw [h1] at ih
      rw [h2, h3, h4]
      linarith

theorem A295321_oddCase (n N : ℕ) (hn : n = 2 * N + 1) : ∀ k : ℕ, k ≤ n →
    3 * (∑ i ∈ Finset.Icc 1 k, i * (n - i) * ((n - i + 1) % 2))
      + 4 * ((k + 1) / 2) ^ 3
      = 6 * N * ((k + 1) / 2) ^ 2 + 3 * ((k + 1) / 2) ^ 2 + (k + 1) / 2 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega)]
    rcases Nat.even_or_odd' k with ⟨J, rfl | rfl⟩
    · obtain ⟨d, hd⟩ : ∃ d, N = J + d := ⟨N - J, by omega⟩
      subst hd
      have h1 : (2 * J + 1) / 2 = J := by omega
      have h2 : (2 * J + 1 + 1) / 2 = J + 1 := by omega
      have h3 : (n - (2 * J + 1) + 1) % 2 = 1 := by omega
      have h4 : n - (2 * J + 1) = 2 * d := by omega
      rw [h1] at ih
      rw [h2, h3, h4]
      linarith
    · have h1 : (2 * J + 1 + 1) / 2 = J + 1 := by omega
      have h2 : (2 * J + 1 + 1 + 1) / 2 = J + 1 := by omega
      have h3 : (n - (2 * J + 1 + 1) + 1) % 2 = 0 := by omega
      rw [h1] at ih
      rw [h2, h3]
      simp only [mul_zero, add_zero]
      exact ih

theorem A295321_c0 (n J : ℕ) (h : n = 4 * (J + 1)) :
    3 * (OMA.S_oeis_a295321.a n : ℤ) + 2 * (J : ℤ) * (J + 1) * (2 * J + 1)
      = 6 * (2 * ((J : ℤ) + 1)) * J * (J + 1) := by
  have key : 3 * OMA.S_oeis_a295321.a n + 2 * J * (J + 1) * (2 * J + 1)
      = 6 * (2 * (J + 1)) * J * (J + 1) := by
    have h0 := A295321_evenCase n (2 * (J + 1)) (by omega) (2 * J + 1) (by omega)
    have e1 : (n - 1) / 2 = 2 * J + 1 := by omega
    have e3 : (2 * J + 1) / 2 = J := by omega
    unfold OMA.S_oeis_a295321.a
    rw [e1]
    rw [e3] at h0
    exact h0
  exact_mod_cast key

theorem A295321_c2 (n m : ℕ) (h : n = 4 * m + 2) :
    3 * (OMA.S_oeis_a295321.a n : ℤ) + 2 * (m : ℤ) * (m + 1) * (2 * m + 1)
      = 6 * (2 * (m : ℤ) + 1) * m * (m + 1) := by
  have key : 3 * OMA.S_oeis_a295321.a n + 2 * m * (m + 1) * (2 * m + 1)
      = 6 * (2 * m + 1) * m * (m + 1) := by
    have h0 := A295321_evenCase n (2 * m + 1) (by omega) (2 * m) (by omega)
    have e1 : (n - 1) / 2 = 2 * m := by omega
    have e3 : (2 * m) / 2 = m := by omega
    unfold OMA.S_oeis_a295321.a
    rw [e1]
    rw [e3] at h0
    exact h0
  exact_mod_cast key

theorem A295321_c1 (n m : ℕ) (h : n = 4 * m + 1) :
    3 * (OMA.S_oeis_a295321.a n : ℤ) + 4 * (m : ℤ) ^ 3
      = 6 * (2 * (m : ℤ)) * m ^ 2 + 3 * (m : ℤ) ^ 2 + m := by
  have key : 3 * OMA.S_oeis_a295321.a n + 4 * m ^ 3
      = 6 * (2 * m) * m ^ 2 + 3 * m ^ 2 + m := by
    have h0 := A295321_oddCase n (2 * m) (by omega) (2 * m) (by omega)
    have e1 : (n - 1) / 2 = 2 * m := by omega
    have e3 : (2 * m + 1) / 2 = m := by omega
    unfold OMA.S_oeis_a295321.a
    rw [e1]
    rw [e3] at h0
    exact h0
  exact_mod_cast key

theorem A295321_c3 (n m : ℕ) (h : n = 4 * m + 3) :
    3 * (OMA.S_oeis_a295321.a n : ℤ) + 4 * ((m : ℤ) + 1) ^ 3
      = 6 * (2 * (m : ℤ) + 1) * (m + 1) ^ 2 + 3 * ((m : ℤ) + 1) ^ 2 + (m + 1) := by
  have key : 3 * OMA.S_oeis_a295321.a n + 4 * (m + 1) ^ 3
      = 6 * (2 * m + 1) * (m + 1) ^ 2 + 3 * (m + 1) ^ 2 + (m + 1) := by
    have h0 := A295321_oddCase n (2 * m + 1) (by omega) (2 * m + 1) (by omega)
    have e1 : (n - 1) / 2 = 2 * m + 1 := by omega
    have e3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    unfold OMA.S_oeis_a295321.a
    rw [e1]
    rw [e3] at h0
    exact h0
  exact_mod_cast key

theorem OMA.solution : type_of% @OMA.S_oeis_a295321.main := by
  intro n hn
  obtain ⟨q, s, hs, hq⟩ : ∃ q s, s < 4 ∧ n = 4 * q + s + 14 :=
    ⟨(n - 14) / 4, (n - 14) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases s
  · have h1 := A295321_c1 (n - 13) q (by omega)
    have h2 := A295321_c2 (n - 12) q (by omega)
    have h3 := A295321_c1 (n - 9) (q + 1) (by omega)
    have h4 := A295321_c2 (n - 8) (q + 1) (by omega)
    have h5 := A295321_c1 (n - 5) (q + 2) (by omega)
    have h6 := A295321_c2 (n - 4) (q + 2) (by omega)
    have h7 := A295321_c1 (n - 1) (q + 3) (by omega)
    have h8 := A295321_c2 n (q + 3) (by omega)
    push_cast at h1 h2 h3 h4 h5 h6 h7 h8
    linarith
  · have h1 := A295321_c2 (n - 13) q (by omega)
    have h2 := A295321_c3 (n - 12) q (by omega)
    have h3 := A295321_c2 (n - 9) (q + 1) (by omega)
    have h4 := A295321_c3 (n - 8) (q + 1) (by omega)
    have h5 := A295321_c2 (n - 5) (q + 2) (by omega)
    have h6 := A295321_c3 (n - 4) (q + 2) (by omega)
    have h7 := A295321_c2 (n - 1) (q + 3) (by omega)
    have h8 := A295321_c3 n (q + 3) (by omega)
    push_cast at h1 h2 h3 h4 h5 h6 h7 h8
    linarith
  · have h1 := A295321_c3 (n - 13) q (by omega)
    have h2 := A295321_c0 (n - 12) q (by omega)
    have h3 := A295321_c3 (n - 9) (q + 1) (by omega)
    have h4 := A295321_c0 (n - 8) (q + 1) (by omega)
    have h5 := A295321_c3 (n - 5) (q + 2) (by omega)
    have h6 := A295321_c0 (n - 4) (q + 2) (by omega)
    have h7 := A295321_c3 (n - 1) (q + 3) (by omega)
    have h8 := A295321_c0 n (q + 3) (by omega)
    push_cast at h1 h2 h3 h4 h5 h6 h7 h8
    linarith
  · have h1 := A295321_c0 (n - 13) q (by omega)
    have h2 := A295321_c1 (n - 12) (q + 1) (by omega)
    have h3 := A295321_c0 (n - 9) (q + 1) (by omega)
    have h4 := A295321_c1 (n - 8) (q + 2) (by omega)
    have h5 := A295321_c0 (n - 5) (q + 2) (by omega)
    have h6 := A295321_c1 (n - 4) (q + 3) (by omega)
    have h7 := A295321_c0 (n - 1) (q + 3) (by omega)
    have h8 := A295321_c1 n (q + 4) (by omega)
    push_cast at h1 h2 h3 h4 h5 h6 h7 h8
    linarith
