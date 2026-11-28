import OMAStatements.S_oeis_a173693

open OMA.S_oeis_a173693

def OMA.w (n : ℕ) : Fin 5 → ℤ := (M ^ n).mulVec ![0, 0, 0, 0, 1]

theorem OMA.w_succ (n : ℕ) : OMA.w (n + 1) = M.mulVec (OMA.w n) := by
  unfold OMA.w
  rw [pow_succ', Matrix.mulVec_mulVec]

theorem OMA.c0 (n : ℕ) : OMA.w (n + 1) 0 = OMA.w n 1 := by
  rw [OMA.w_succ]; simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
theorem OMA.c1 (n : ℕ) : OMA.w (n + 1) 1 = OMA.w n 2 := by
  rw [OMA.w_succ]; simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
theorem OMA.c2 (n : ℕ) : OMA.w (n + 1) 2 = OMA.w n 3 := by
  rw [OMA.w_succ]; simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
theorem OMA.c3 (n : ℕ) : OMA.w (n + 1) 3 = OMA.w n 4 := by
  rw [OMA.w_succ]; simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
theorem OMA.c4 (n : ℕ) : OMA.w (n + 1) 4 = OMA.w n 0 - OMA.w n 2 + OMA.w n 3 + OMA.w n 4 := by
  rw [OMA.w_succ]; simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_five]; ring

theorem OMA.b_eq (n : ℕ) : b n = OMA.w n 0 := rfl

theorem OMA.rec (n : ℕ) : b (n + 5) = b (n + 4) + b (n + 3) - b (n + 2) + b n := by
  have h5 : b (n + 5) = OMA.w n 0 - OMA.w n 2 + OMA.w n 3 + OMA.w n 4 := by
    rw [OMA.b_eq, OMA.c0, OMA.c1, OMA.c2, OMA.c3, OMA.c4]
  have h4 : b (n + 4) = OMA.w n 4 := by
    rw [OMA.b_eq, OMA.c0, OMA.c1, OMA.c2, OMA.c3]
  have h3 : b (n + 3) = OMA.w n 3 := by
    rw [OMA.b_eq, OMA.c0, OMA.c1, OMA.c2]
  have h2 : b (n + 2) = OMA.w n 2 := by
    rw [OMA.b_eq, OMA.c0, OMA.c1]
  rw [h5, h4, h3, h2, OMA.b_eq]
  ring

theorem OMA.ceil_half (z : ℤ) : 2 * ⌈(z : ℚ) / 2⌉ = z + z % 2 := by
  rcases Int.emod_two_eq_zero_or_one z with h | h
  · obtain ⟨m, hm⟩ : ∃ m, z = 2 * m := ⟨z / 2, by omega⟩
    have : ⌈(z : ℚ) / 2⌉ = m := by
      rw [Int.ceil_eq_iff, hm]; push_cast; constructor <;> linarith
    rw [this]; omega
  · obtain ⟨m, hm⟩ : ∃ m, z = 2 * m + 1 := ⟨z / 2, by omega⟩
    have : ⌈(z : ℚ) / 2⌉ = m + 1 := by
      rw [Int.ceil_eq_iff, hm]; push_cast; constructor <;> linarith
    rw [this]; omega

theorem OMA.two_a (n : ℕ) : 2 * a n = b n + b n % 2 := OMA.ceil_half (b n)

theorem OMA.per (n : ℕ) : b (n + 31) % 2 = b n % 2 := by
  have r0 : b (n + 5) = b (n + 4) + b (n + 3) - b (n + 2) + b (n + 0) := OMA.rec (n + 0)
  have r1 : b (n + 6) = b (n + 5) + b (n + 4) - b (n + 3) + b (n + 1) := OMA.rec (n + 1)
  have r2 : b (n + 7) = b (n + 6) + b (n + 5) - b (n + 4) + b (n + 2) := OMA.rec (n + 2)
  have r3 : b (n + 8) = b (n + 7) + b (n + 6) - b (n + 5) + b (n + 3) := OMA.rec (n + 3)
  have r4 : b (n + 9) = b (n + 8) + b (n + 7) - b (n + 6) + b (n + 4) := OMA.rec (n + 4)
  have r5 : b (n + 10) = b (n + 9) + b (n + 8) - b (n + 7) + b (n + 5) := OMA.rec (n + 5)
  have r6 : b (n + 11) = b (n + 10) + b (n + 9) - b (n + 8) + b (n + 6) := OMA.rec (n + 6)
  have r7 : b (n + 12) = b (n + 11) + b (n + 10) - b (n + 9) + b (n + 7) := OMA.rec (n + 7)
  have r8 : b (n + 13) = b (n + 12) + b (n + 11) - b (n + 10) + b (n + 8) := OMA.rec (n + 8)
  have r9 : b (n + 14) = b (n + 13) + b (n + 12) - b (n + 11) + b (n + 9) := OMA.rec (n + 9)
  have r10 : b (n + 15) = b (n + 14) + b (n + 13) - b (n + 12) + b (n + 10) := OMA.rec (n + 10)
  have r11 : b (n + 16) = b (n + 15) + b (n + 14) - b (n + 13) + b (n + 11) := OMA.rec (n + 11)
  have r12 : b (n + 17) = b (n + 16) + b (n + 15) - b (n + 14) + b (n + 12) := OMA.rec (n + 12)
  have r13 : b (n + 18) = b (n + 17) + b (n + 16) - b (n + 15) + b (n + 13) := OMA.rec (n + 13)
  have r14 : b (n + 19) = b (n + 18) + b (n + 17) - b (n + 16) + b (n + 14) := OMA.rec (n + 14)
  have r15 : b (n + 20) = b (n + 19) + b (n + 18) - b (n + 17) + b (n + 15) := OMA.rec (n + 15)
  have r16 : b (n + 21) = b (n + 20) + b (n + 19) - b (n + 18) + b (n + 16) := OMA.rec (n + 16)
  have r17 : b (n + 22) = b (n + 21) + b (n + 20) - b (n + 19) + b (n + 17) := OMA.rec (n + 17)
  have r18 : b (n + 23) = b (n + 22) + b (n + 21) - b (n + 20) + b (n + 18) := OMA.rec (n + 18)
  have r19 : b (n + 24) = b (n + 23) + b (n + 22) - b (n + 21) + b (n + 19) := OMA.rec (n + 19)
  have r20 : b (n + 25) = b (n + 24) + b (n + 23) - b (n + 22) + b (n + 20) := OMA.rec (n + 20)
  have r21 : b (n + 26) = b (n + 25) + b (n + 24) - b (n + 23) + b (n + 21) := OMA.rec (n + 21)
  have r22 : b (n + 27) = b (n + 26) + b (n + 25) - b (n + 24) + b (n + 22) := OMA.rec (n + 22)
  have r23 : b (n + 28) = b (n + 27) + b (n + 26) - b (n + 25) + b (n + 23) := OMA.rec (n + 23)
  have r24 : b (n + 29) = b (n + 28) + b (n + 27) - b (n + 26) + b (n + 24) := OMA.rec (n + 24)
  have r25 : b (n + 30) = b (n + 29) + b (n + 28) - b (n + 27) + b (n + 25) := OMA.rec (n + 25)
  have r26 : b (n + 31) = b (n + 30) + b (n + 29) - b (n + 28) + b (n + 26) := OMA.rec (n + 26)
  have h : b (n + 31) = (9563) * b (n + 0) + (6626) * b (n + 1) + (-4972) * b (n + 2) + (6118) * b (n + 3) + (13802) * b (n + 4) := by
    linear_combination (9563) * r0 + (6626) * r1 + (4591) * r2 + (3181) * r3 + (2204) * r4 + (1527) * r5 + (1058) * r6 + (733) * r7 + (508) * r8 + (352) * r9 + (244) * r10 + (169) * r11 + (117) * r12 + (81) * r13 + (56) * r14 + (39) * r15 + (27) * r16 + (19) * r17 + (13) * r18 + (9) * r19 + (6) * r20 + (4) * r21 + (3) * r22 + (2) * r23 + (2) * r24 + (1) * r25 + (1) * r26
  have e0 : b (n + 0) = b n := rfl
  rw [e0] at h
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a173693.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 36 := ⟨n - 36, by omega⟩
  have e1 : m + 36 - 1 = m + 35 := rfl
  have e2 : m + 36 - 2 = m + 34 := rfl
  have e3 : m + 36 - 3 = m + 33 := rfl
  have e5 : m + 36 - 5 = m + 31 := rfl
  have e31 : m + 36 - 31 = m + 5 := rfl
  have e32 : m + 36 - 32 = m + 4 := rfl
  have e33 : m + 36 - 33 = m + 3 := rfl
  have e34 : m + 36 - 34 = m + 2 := rfl
  have e36 : m + 36 - 36 = m := by omega
  rw [e1, e2, e3, e5, e31, e32, e33, e34, e36]
  have t36 := OMA.two_a (m + 36)
  have t35 := OMA.two_a (m + 35)
  have t34 := OMA.two_a (m + 34)
  have t33 := OMA.two_a (m + 33)
  have t31 := OMA.two_a (m + 31)
  have t5 := OMA.two_a (m + 5)
  have t4 := OMA.two_a (m + 4)
  have t3 := OMA.two_a (m + 3)
  have t2 := OMA.two_a (m + 2)
  have t0 := OMA.two_a m
  have p5 : b (m + 36) % 2 = b (m + 5) % 2 := OMA.per (m + 5)
  have p4 : b (m + 35) % 2 = b (m + 4) % 2 := OMA.per (m + 4)
  have p3 : b (m + 34) % 2 = b (m + 3) % 2 := OMA.per (m + 3)
  have p2 : b (m + 33) % 2 = b (m + 2) % 2 := OMA.per (m + 2)
  have p0 : b (m + 31) % 2 = b m % 2 := OMA.per m
  have q31 : b (m + 36) = b (m + 35) + b (m + 34) - b (m + 33) + b (m + 31) := OMA.rec (m + 31)
  have q0 : b (m + 5) = b (m + 4) + b (m + 3) - b (m + 2) + b m := OMA.rec m
  linarith
