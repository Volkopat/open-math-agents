import OMAStatements.S_oeis_a192826
import Mathlib

open OMA.S_oeis_a192826

noncomputable def P192826.cc (m : ℕ) : ℚ := (m.choose (m / 2) : ℚ)

theorem P192826.codd (i : ℕ) : ((i : ℚ) + 1) * P192826.cc (2 * i + 1) = (2 * (i : ℚ) + 1) * P192826.cc (2 * i) := by
  unfold P192826.cc
  rw [show (2 * i + 1) / 2 = i by omega, show 2 * i / 2 = i by omega]
  have h := Nat.add_one_mul_choose_eq (2 * i) i
  have hs : (2 * i + 1).choose (i + 1) = (2 * i + 1).choose i := Nat.choose_symm_half i
  rw [hs] at h
  have h' : (((2 * i + 1) * (2 * i).choose i : ℕ) : ℚ) = (((2 * i + 1).choose i * (i + 1) : ℕ) : ℚ) := by rw [h]
  push_cast at h'
  linarith

theorem P192826.ceven (i : ℕ) : P192826.cc (2 * i + 2) = 2 * P192826.cc (2 * i + 1) := by
  unfold P192826.cc
  rw [show (2 * i + 2) / 2 = i + 1 by omega, show (2 * i + 1) / 2 = i by omega]
  rw [show 2 * i + 2 = (2 * i + 1) + 1 by ring, Nat.choose_succ_succ]
  have hs : (2 * i + 1).choose (i + 1) = (2 * i + 1).choose i := Nat.choose_symm_half i
  rw [hs]
  push_cast
  ring

theorem P192826.hA (k : ℕ) (hk : 3 ≤ k) :
    (a k : ℚ) = 2 ^ (k - 2) * (k : ℚ) ^ 2 * (2 + 2 ^ (k - 1) - P192826.cc (k - 1)) := by
  simp only [a, show k ≠ 2 by omega, if_false, P192826.cc]
  push_cast
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a192826.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  apply Int.cast_injective (α := ℚ)
  push_cast
  try simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · have e3 : (a (2 * j + 3) : ℚ) = 2 ^ (2 * j + 1) * ((2 * j : ℕ) + 3 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 2) - P192826.cc (2 * j + 2)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 3 - 2 = 2 * j + 1 by omega, show 2 * j + 3 - 1 = 2 * j + 2 by omega]
      push_cast
      ring
    have e4 : (a (2 * j + 4) : ℚ) = 2 ^ (2 * j + 2) * ((2 * j : ℕ) + 4 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 3) - P192826.cc (2 * j + 3)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 4 - 2 = 2 * j + 2 by omega, show 2 * j + 4 - 1 = 2 * j + 3 by omega]
      push_cast
      ring
    have e5 : (a (2 * j + 5) : ℚ) = 2 ^ (2 * j + 3) * ((2 * j : ℕ) + 5 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 4) - P192826.cc (2 * j + 4)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 5 - 2 = 2 * j + 3 by omega, show 2 * j + 5 - 1 = 2 * j + 4 by omega]
      push_cast
      ring
    have e6 : (a (2 * j + 6) : ℚ) = 2 ^ (2 * j + 4) * ((2 * j : ℕ) + 6 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 5) - P192826.cc (2 * j + 5)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 6 - 2 = 2 * j + 4 by omega, show 2 * j + 6 - 1 = 2 * j + 5 by omega]
      push_cast
      ring
    have e7 : (a (2 * j + 7) : ℚ) = 2 ^ (2 * j + 5) * ((2 * j : ℕ) + 7 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 6) - P192826.cc (2 * j + 6)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 7 - 2 = 2 * j + 5 by omega, show 2 * j + 7 - 1 = 2 * j + 6 by omega]
      push_cast
      ring
    have e8 : (a (2 * j + 8) : ℚ) = 2 ^ (2 * j + 6) * ((2 * j : ℕ) + 8 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 7) - P192826.cc (2 * j + 7)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 8 - 2 = 2 * j + 6 by omega, show 2 * j + 8 - 1 = 2 * j + 7 by omega]
      push_cast
      ring
    have e9 : (a (2 * j + 9) : ℚ) = 2 ^ (2 * j + 7) * ((2 * j : ℕ) + 9 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 8) - P192826.cc (2 * j + 8)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 9 - 2 = 2 * j + 7 by omega, show 2 * j + 9 - 1 = 2 * j + 8 by omega]
      push_cast
      ring
    have e10 : (a (2 * j + 10) : ℚ) = 2 ^ (2 * j + 8) * ((2 * j : ℕ) + 10 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 9) - P192826.cc (2 * j + 9)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 10 - 2 = 2 * j + 8 by omega, show 2 * j + 10 - 1 = 2 * j + 9 by omega]
      push_cast
      ring
    rw [e10, e9, e8, e7, e6, e5, e4, e3]
    try simp only [show 2 * j + 2 = 2 * j + 2 by omega, show 2 * j + 3 = 2 * j + 3 by omega, show 2 * j + 4 = 2 * j + 4 by omega, show 2 * j + 5 = 2 * j + 5 by omega, show 2 * j + 6 = 2 * j + 6 by omega, show 2 * j + 7 = 2 * j + 7 by omega, show 2 * j + 8 = 2 * j + 8 by omega, show 2 * j + 9 = 2 * j + 9 by omega]
    have c3 : P192826.cc (2 * j + 3) = (2 * (j : ℚ) + 3) / ((j : ℚ) + 2) * P192826.cc (2 * j + 2) := by
      have h := P192826.codd (j + 1)
      rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show 2 * (j + 1) = 2 * j + 2 by ring] at h
      push_cast at h
      field_simp
      linarith
    have c4 : P192826.cc (2 * j + 4) = 2 * P192826.cc (2 * j + 3) := by
      have h := P192826.ceven (j + 1)
      rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring] at h
      exact h
    have c5 : P192826.cc (2 * j + 5) = (2 * (j : ℚ) + 5) / ((j : ℚ) + 3) * P192826.cc (2 * j + 4) := by
      have h := P192826.codd (j + 2)
      rw [show 2 * (j + 2) + 1 = 2 * j + 5 by ring, show 2 * (j + 2) = 2 * j + 4 by ring] at h
      push_cast at h
      field_simp
      linarith
    have c6 : P192826.cc (2 * j + 6) = 2 * P192826.cc (2 * j + 5) := by
      have h := P192826.ceven (j + 2)
      rw [show 2 * (j + 2) + 2 = 2 * j + 6 by ring, show 2 * (j + 2) + 1 = 2 * j + 5 by ring] at h
      exact h
    have c7 : P192826.cc (2 * j + 7) = (2 * (j : ℚ) + 7) / ((j : ℚ) + 4) * P192826.cc (2 * j + 6) := by
      have h := P192826.codd (j + 3)
      rw [show 2 * (j + 3) + 1 = 2 * j + 7 by ring, show 2 * (j + 3) = 2 * j + 6 by ring] at h
      push_cast at h
      field_simp
      linarith
    have c8 : P192826.cc (2 * j + 8) = 2 * P192826.cc (2 * j + 7) := by
      have h := P192826.ceven (j + 3)
      rw [show 2 * (j + 3) + 2 = 2 * j + 8 by ring, show 2 * (j + 3) + 1 = 2 * j + 7 by ring] at h
      exact h
    have c9 : P192826.cc (2 * j + 9) = (2 * (j : ℚ) + 9) / ((j : ℚ) + 5) * P192826.cc (2 * j + 8) := by
      have h := P192826.codd (j + 4)
      rw [show 2 * (j + 4) + 1 = 2 * j + 9 by ring, show 2 * (j + 4) = 2 * j + 8 by ring] at h
      push_cast at h
      field_simp
      linarith
    rw [c9, c8, c7, c6, c5, c4, c3]
    field_simp
    push_cast
    ring
  · have e3 : (a (2 * j + 1 + 3) : ℚ) = 2 ^ (2 * j + 1 + 1) * ((2 * j + 1 : ℕ) + 3 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 1 + 2) - P192826.cc (2 * j + 1 + 2)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 1 + 3 - 2 = 2 * j + 1 + 1 by omega, show 2 * j + 1 + 3 - 1 = 2 * j + 1 + 2 by omega]
      push_cast
      ring
    have e4 : (a (2 * j + 1 + 4) : ℚ) = 2 ^ (2 * j + 1 + 2) * ((2 * j + 1 : ℕ) + 4 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 1 + 3) - P192826.cc (2 * j + 1 + 3)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 1 + 4 - 2 = 2 * j + 1 + 2 by omega, show 2 * j + 1 + 4 - 1 = 2 * j + 1 + 3 by omega]
      push_cast
      ring
    have e5 : (a (2 * j + 1 + 5) : ℚ) = 2 ^ (2 * j + 1 + 3) * ((2 * j + 1 : ℕ) + 5 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 1 + 4) - P192826.cc (2 * j + 1 + 4)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 1 + 5 - 2 = 2 * j + 1 + 3 by omega, show 2 * j + 1 + 5 - 1 = 2 * j + 1 + 4 by omega]
      push_cast
      ring
    have e6 : (a (2 * j + 1 + 6) : ℚ) = 2 ^ (2 * j + 1 + 4) * ((2 * j + 1 : ℕ) + 6 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 1 + 5) - P192826.cc (2 * j + 1 + 5)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 1 + 6 - 2 = 2 * j + 1 + 4 by omega, show 2 * j + 1 + 6 - 1 = 2 * j + 1 + 5 by omega]
      push_cast
      ring
    have e7 : (a (2 * j + 1 + 7) : ℚ) = 2 ^ (2 * j + 1 + 5) * ((2 * j + 1 : ℕ) + 7 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 1 + 6) - P192826.cc (2 * j + 1 + 6)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 1 + 7 - 2 = 2 * j + 1 + 5 by omega, show 2 * j + 1 + 7 - 1 = 2 * j + 1 + 6 by omega]
      push_cast
      ring
    have e8 : (a (2 * j + 1 + 8) : ℚ) = 2 ^ (2 * j + 1 + 6) * ((2 * j + 1 : ℕ) + 8 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 1 + 7) - P192826.cc (2 * j + 1 + 7)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 1 + 8 - 2 = 2 * j + 1 + 6 by omega, show 2 * j + 1 + 8 - 1 = 2 * j + 1 + 7 by omega]
      push_cast
      ring
    have e9 : (a (2 * j + 1 + 9) : ℚ) = 2 ^ (2 * j + 1 + 7) * ((2 * j + 1 : ℕ) + 9 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 1 + 8) - P192826.cc (2 * j + 1 + 8)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 1 + 9 - 2 = 2 * j + 1 + 7 by omega, show 2 * j + 1 + 9 - 1 = 2 * j + 1 + 8 by omega]
      push_cast
      ring
    have e10 : (a (2 * j + 1 + 10) : ℚ) = 2 ^ (2 * j + 1 + 8) * ((2 * j + 1 : ℕ) + 10 : ℚ) ^ 2 * (2 + 2 ^ (2 * j + 1 + 9) - P192826.cc (2 * j + 1 + 9)) := by
      rw [P192826.hA _ (by omega), show 2 * j + 1 + 10 - 2 = 2 * j + 1 + 8 by omega, show 2 * j + 1 + 10 - 1 = 2 * j + 1 + 9 by omega]
      push_cast
      ring
    rw [e10, e9, e8, e7, e6, e5, e4, e3]
    try simp only [show 2 * j + 1 + 2 = 2 * j + 3 by omega, show 2 * j + 1 + 3 = 2 * j + 4 by omega, show 2 * j + 1 + 4 = 2 * j + 5 by omega, show 2 * j + 1 + 5 = 2 * j + 6 by omega, show 2 * j + 1 + 6 = 2 * j + 7 by omega, show 2 * j + 1 + 7 = 2 * j + 8 by omega, show 2 * j + 1 + 8 = 2 * j + 9 by omega, show 2 * j + 1 + 9 = 2 * j + 10 by omega]
    have c4 : P192826.cc (2 * j + 4) = 2 * P192826.cc (2 * j + 3) := by
      have h := P192826.ceven (j + 1)
      rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring] at h
      exact h
    have c5 : P192826.cc (2 * j + 5) = (2 * (j : ℚ) + 5) / ((j : ℚ) + 3) * P192826.cc (2 * j + 4) := by
      have h := P192826.codd (j + 2)
      rw [show 2 * (j + 2) + 1 = 2 * j + 5 by ring, show 2 * (j + 2) = 2 * j + 4 by ring] at h
      push_cast at h
      field_simp
      linarith
    have c6 : P192826.cc (2 * j + 6) = 2 * P192826.cc (2 * j + 5) := by
      have h := P192826.ceven (j + 2)
      rw [show 2 * (j + 2) + 2 = 2 * j + 6 by ring, show 2 * (j + 2) + 1 = 2 * j + 5 by ring] at h
      exact h
    have c7 : P192826.cc (2 * j + 7) = (2 * (j : ℚ) + 7) / ((j : ℚ) + 4) * P192826.cc (2 * j + 6) := by
      have h := P192826.codd (j + 3)
      rw [show 2 * (j + 3) + 1 = 2 * j + 7 by ring, show 2 * (j + 3) = 2 * j + 6 by ring] at h
      push_cast at h
      field_simp
      linarith
    have c8 : P192826.cc (2 * j + 8) = 2 * P192826.cc (2 * j + 7) := by
      have h := P192826.ceven (j + 3)
      rw [show 2 * (j + 3) + 2 = 2 * j + 8 by ring, show 2 * (j + 3) + 1 = 2 * j + 7 by ring] at h
      exact h
    have c9 : P192826.cc (2 * j + 9) = (2 * (j : ℚ) + 9) / ((j : ℚ) + 5) * P192826.cc (2 * j + 8) := by
      have h := P192826.codd (j + 4)
      rw [show 2 * (j + 4) + 1 = 2 * j + 9 by ring, show 2 * (j + 4) = 2 * j + 8 by ring] at h
      push_cast at h
      field_simp
      linarith
    have c10 : P192826.cc (2 * j + 10) = 2 * P192826.cc (2 * j + 9) := by
      have h := P192826.ceven (j + 4)
      rw [show 2 * (j + 4) + 2 = 2 * j + 10 by ring, show 2 * (j + 4) + 1 = 2 * j + 9 by ring] at h
      exact h
    rw [c10, c9, c8, c7, c6, c5, c4]
    field_simp
    push_cast
    ring
