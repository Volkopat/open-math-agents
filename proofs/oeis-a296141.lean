import OMAStatements.S_oeis_a296141

open OMA.S_oeis_a296141

theorem OMA.A296141.a_step (n : ℕ) :
    a (n + 2) = a n + ((n + 1) / 2) * ((n + 3 - (n + 1) / 2) % 2) := by
  unfold OMA.S_oeis_a296141.a
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · have e1 : (n + 2 - 1) / 2 = (n - 1) / 2 + 1 := by omega
    rw [e1, Finset.sum_Icc_succ_top (by omega)]
    have e2 : (n - 1) / 2 + 1 = (n + 1) / 2 := by omega
    have e3 : (n + 2 - ((n - 1) / 2 + 1) + 1) % 2 = (n + 3 - (n + 1) / 2) % 2 := by omega
    rw [e3, e2]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    have e4 : (n + 2 - i + 1) % 2 = (n - i + 1) % 2 := by omega
    rw [e4]

theorem OMA.A296141.s0 (m : ℕ) : a (4 * m + 4) = a (4 * m + 2) := by
  have h := OMA.A296141.a_step (4 * m + 2)
  have t : (4 * m + 2 + 3 - (4 * m + 2 + 1) / 2) % 2 = 0 := by omega
  have e : 4 * m + 2 + 2 = 4 * m + 4 := by omega
  rw [t, e, Nat.mul_zero, Nat.add_zero] at h
  exact h

theorem OMA.A296141.s1 (m : ℕ) : a (4 * m + 5) = a (4 * m + 3) := by
  have h := OMA.A296141.a_step (4 * m + 3)
  have t : (4 * m + 3 + 3 - (4 * m + 3 + 1) / 2) % 2 = 0 := by omega
  have e : 4 * m + 3 + 2 = 4 * m + 5 := by omega
  rw [t, e, Nat.mul_zero, Nat.add_zero] at h
  exact h

theorem OMA.A296141.s2 (m : ℕ) : a (4 * m + 6) = a (4 * m + 4) + (2 * m + 2) := by
  have h := OMA.A296141.a_step (4 * m + 4)
  have t : (4 * m + 4 + 3 - (4 * m + 4 + 1) / 2) % 2 = 1 := by omega
  have u : (4 * m + 4 + 1) / 2 = 2 * m + 2 := by omega
  have e : 4 * m + 4 + 2 = 4 * m + 6 := by omega
  rw [t, u, e, Nat.mul_one] at h
  exact h

theorem OMA.A296141.s3 (m : ℕ) : a (4 * m + 7) = a (4 * m + 5) + (2 * m + 3) := by
  have h := OMA.A296141.a_step (4 * m + 5)
  have t : (4 * m + 5 + 3 - (4 * m + 5 + 1) / 2) % 2 = 1 := by omega
  have u : (4 * m + 5 + 1) / 2 = 2 * m + 3 := by omega
  have e : 4 * m + 5 + 2 = 4 * m + 7 := by omega
  rw [t, u, e, Nat.mul_one] at h
  exact h

theorem OMA.A296141.closed (m : ℕ) :
    a (4 * m) + m = m * m ∧ a (4 * m + 1) = m * m ∧ a (4 * m + 2) = m * m + m ∧
      a (4 * m + 3) = (m + 1) * (m + 1) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [OMA.S_oeis_a296141.a]
  | succ m ih =>
    obtain ⟨_, _, h2, h3⟩ := ih
    have e0 : 4 * (m + 1) = 4 * m + 4 := by ring
    have e1 : 4 * (m + 1) + 1 = 4 * m + 5 := by ring
    have e2 : 4 * (m + 1) + 2 = 4 * m + 6 := by ring
    have e3 : 4 * (m + 1) + 3 = 4 * m + 7 := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e0, OMA.A296141.s0, h2]; ring
    · rw [e1, OMA.A296141.s1, h3]
    · rw [e2, OMA.A296141.s2, OMA.A296141.s0, h2]; ring
    · rw [e3, OMA.A296141.s3, OMA.A296141.s1, h3]; ring

theorem OMA.A296141.c0 (m : ℕ) : (a (4 * m) : ℤ) = (m : ℤ) * m - m := by
  have h := (OMA.A296141.closed m).1
  have h' : ((a (4 * m) + m : ℕ) : ℤ) = ((m * m : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

theorem OMA.A296141.c1 (m : ℕ) : (a (4 * m + 1) : ℤ) = (m : ℤ) * m := by
  rw [(OMA.A296141.closed m).2.1]; push_cast; ring

theorem OMA.A296141.c2 (m : ℕ) : (a (4 * m + 2) : ℤ) = (m : ℤ) * m + m := by
  rw [(OMA.A296141.closed m).2.2.1]; push_cast; ring

theorem OMA.A296141.c3 (m : ℕ) : (a (4 * m + 3) : ℤ) = ((m : ℤ) + 1) * (m + 1) := by
  rw [(OMA.A296141.closed m).2.2.2]; push_cast; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a296141.main := by
  intro n hn
  obtain ⟨m, r, hr, hnm⟩ : ∃ m r, r < 4 ∧ n = 4 * m + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases r
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    have f0 : a n = a (4 * (k + 3)) := congrArg a (by omega)
    have f1 : a (n - 1) = a (4 * (k + 2) + 3) := congrArg a (by omega)
    have f4 : a (n - 4) = a (4 * (k + 2)) := congrArg a (by omega)
    have f5 : a (n - 5) = a (4 * (k + 1) + 3) := congrArg a (by omega)
    have f8 : a (n - 8) = a (4 * (k + 1)) := congrArg a (by omega)
    have f9 : a (n - 9) = a (4 * k + 3) := congrArg a (by omega)
    rw [f0, f1, f4, f5, f8, f9]
    simp only [OMA.A296141.c0, OMA.A296141.c3]
    push_cast
    ring
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    have f0 : a n = a (4 * (k + 3) + 1) := congrArg a (by omega)
    have f1 : a (n - 1) = a (4 * (k + 3)) := congrArg a (by omega)
    have f4 : a (n - 4) = a (4 * (k + 2) + 1) := congrArg a (by omega)
    have f5 : a (n - 5) = a (4 * (k + 2)) := congrArg a (by omega)
    have f8 : a (n - 8) = a (4 * (k + 1) + 1) := congrArg a (by omega)
    have f9 : a (n - 9) = a (4 * (k + 1)) := congrArg a (by omega)
    rw [f0, f1, f4, f5, f8, f9]
    simp only [OMA.A296141.c0, OMA.A296141.c1]
    push_cast
    ring
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have f0 : a n = a (4 * (k + 2) + 2) := congrArg a (by omega)
    have f1 : a (n - 1) = a (4 * (k + 2) + 1) := congrArg a (by omega)
    have f4 : a (n - 4) = a (4 * (k + 1) + 2) := congrArg a (by omega)
    have f5 : a (n - 5) = a (4 * (k + 1) + 1) := congrArg a (by omega)
    have f8 : a (n - 8) = a (4 * k + 2) := congrArg a (by omega)
    have f9 : a (n - 9) = a (4 * k + 1) := congrArg a (by omega)
    rw [f0, f1, f4, f5, f8, f9]
    simp only [OMA.A296141.c1, OMA.A296141.c2]
    push_cast
    ring
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have f0 : a n = a (4 * (k + 2) + 3) := congrArg a (by omega)
    have f1 : a (n - 1) = a (4 * (k + 2) + 2) := congrArg a (by omega)
    have f4 : a (n - 4) = a (4 * (k + 1) + 3) := congrArg a (by omega)
    have f5 : a (n - 5) = a (4 * (k + 1) + 2) := congrArg a (by omega)
    have f8 : a (n - 8) = a (4 * k + 3) := congrArg a (by omega)
    have f9 : a (n - 9) = a (4 * k + 2) := congrArg a (by omega)
    rw [f0, f1, f4, f5, f8, f9]
    simp only [OMA.A296141.c2, OMA.A296141.c3]
    push_cast
    ring
