import OMAStatements.S_oeis_a005561
import Mathlib

open OMA.S_oeis_a005561

namespace P005561

noncomputable def B (i : ℕ) : ℚ := ((2 * i).factorial : ℚ) / (i.factorial * i.factorial)

theorem Bpos (i : ℕ) : B i ≠ 0 := by unfold B; positivity

theorem ch (N k : ℕ) (h : k ≤ N) : ((N.choose k : ℕ) : ℚ) = (N.factorial : ℚ) / (k.factorial * (N - k).factorial) :=
  Nat.cast_choose ℚ h

theorem b4_0 (i : ℕ) : ((Nat.choose (2 * i + 4) i : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4)) / (((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4)) := by
  rw [ch _ _ (by omega), show 2 * i + 4 - i = i + 4 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b5_0 (i : ℕ) : ((Nat.choose (2 * i + 5) i : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4) * (2 * (i : ℚ) + 5)) / (((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4) * ((i : ℚ) + 5)) := by
  rw [ch _ _ (by omega), show 2 * i + 5 - i = i + 5 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b5_1 (i : ℕ) : ((Nat.choose (2 * i + 5) (i + 1) : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4) * (2 * (i : ℚ) + 5)) / (((i : ℚ) + 1) * ((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4)) := by
  rw [ch _ _ (by omega), show 2 * i + 5 - (i + 1) = i + 4 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b6_1 (i : ℕ) : ((Nat.choose (2 * i + 6) (i + 1) : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4) * (2 * (i : ℚ) + 5) * (2 * (i : ℚ) + 6)) / (((i : ℚ) + 1) * ((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4) * ((i : ℚ) + 5)) := by
  rw [ch _ _ (by omega), show 2 * i + 6 - (i + 1) = i + 5 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b7_1 (i : ℕ) : ((Nat.choose (2 * i + 7) (i + 1) : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4) * (2 * (i : ℚ) + 5) * (2 * (i : ℚ) + 6) * (2 * (i : ℚ) + 7)) / (((i : ℚ) + 1) * ((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4) * ((i : ℚ) + 5) * ((i : ℚ) + 6)) := by
  rw [ch _ _ (by omega), show 2 * i + 7 - (i + 1) = i + 6 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b7_2 (i : ℕ) : ((Nat.choose (2 * i + 7) (i + 2) : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4) * (2 * (i : ℚ) + 5) * (2 * (i : ℚ) + 6) * (2 * (i : ℚ) + 7)) / (((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4) * ((i : ℚ) + 5)) := by
  rw [ch _ _ (by omega), show 2 * i + 7 - (i + 2) = i + 5 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem b8_2 (i : ℕ) : ((Nat.choose (2 * i + 8) (i + 2) : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4) * (2 * (i : ℚ) + 5) * (2 * (i : ℚ) + 6) * (2 * (i : ℚ) + 7) * (2 * (i : ℚ) + 8)) / (((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4) * ((i : ℚ) + 5) * ((i : ℚ) + 6)) := by
  rw [ch _ _ (by omega), show 2 * i + 8 - (i + 2) = i + 6 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem at_eq (t : ℕ) : (a (t + 4) : ℚ) = ((t + 5).choose ((t + 2) / 2) : ℚ) * (t + 4).choose ((t + 1) / 2) -
    ((t + 5).choose ((t + 1) / 2) : ℚ) * (t + 4).choose (t / 2) := by
  simp only [a, column]
  rw [show 3 + t + 1 + 1 = t + 5 by ring, show 3 + t + 1 = t + 4 by ring]

theorem A0 (i : ℕ) : (a (2 * i + 4) : ℚ) = (Nat.choose (2 * i + 5) (i + 1) : ℚ) * (Nat.choose (2 * i + 4) i : ℚ) - (Nat.choose (2 * i + 5) i : ℚ) * (Nat.choose (2 * i + 4) i : ℚ) := by
  rw [at_eq, show (2 * i + 2) / 2 = i + 1 by omega, show (2 * i + 1) / 2 = i by omega, show 2 * i / 2 = i by omega]

theorem A1 (i : ℕ) : (a (2 * i + 5) : ℚ) = (Nat.choose (2 * i + 6) (i + 1) : ℚ) * (Nat.choose (2 * i + 5) (i + 1) : ℚ) - (Nat.choose (2 * i + 6) (i + 1) : ℚ) * (Nat.choose (2 * i + 5) i : ℚ) := by
  rw [show 2 * i + 5 = 2 * i + 1 + 4 by ring, at_eq, show 2 * i + 1 + 5 = 2 * i + 6 by ring, show 2 * i + 1 + 4 = 2 * i + 5 by ring, show (2 * i + 1 + 2) / 2 = i + 1 by omega, show (2 * i + 1 + 1) / 2 = i + 1 by omega, show (2 * i + 1) / 2 = i by omega]

theorem A2 (i : ℕ) : (a (2 * i + 6) : ℚ) = (Nat.choose (2 * i + 7) (i + 2) : ℚ) * (Nat.choose (2 * i + 6) (i + 1) : ℚ) - (Nat.choose (2 * i + 7) (i + 1) : ℚ) * (Nat.choose (2 * i + 6) (i + 1) : ℚ) := by
  rw [show 2 * i + 6 = 2 * i + 2 + 4 by ring, at_eq, show 2 * i + 2 + 5 = 2 * i + 7 by ring, show 2 * i + 2 + 4 = 2 * i + 6 by ring, show (2 * i + 2 + 2) / 2 = i + 2 by omega, show (2 * i + 2 + 1) / 2 = i + 1 by omega, show (2 * i + 2) / 2 = i + 1 by omega]

theorem A3 (i : ℕ) : (a (2 * i + 7) : ℚ) = (Nat.choose (2 * i + 8) (i + 2) : ℚ) * (Nat.choose (2 * i + 7) (i + 2) : ℚ) - (Nat.choose (2 * i + 8) (i + 2) : ℚ) * (Nat.choose (2 * i + 7) (i + 1) : ℚ) := by
  rw [show 2 * i + 7 = 2 * i + 3 + 4 by ring, at_eq, show 2 * i + 3 + 5 = 2 * i + 8 by ring, show 2 * i + 3 + 4 = 2 * i + 7 by ring, show (2 * i + 3 + 2) / 2 = i + 2 by omega, show (2 * i + 3 + 1) / 2 = i + 2 by omega, show (2 * i + 3) / 2 = i + 1 by omega]

end P005561

theorem OMA.solution : type_of% @OMA.S_oeis_a005561.main := by
  intro n hn
  rcases Nat.lt_or_ge n 6 with h3 | h4
  · obtain rfl : n = 5 := by omega
    simp [a, column, Nat.choose]
    norm_num
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨i, rfl⟩ : ∃ i, m = i + 3 := ⟨m - 3, by omega⟩
    subst hm
    rw [show i + 3 + (i + 3) - 1 = 2 * i + 5 by omega, show i + 3 + (i + 3) - 2 = 2 * i + 4 by omega,
      show i + 3 + (i + 3) = 2 * i + 6 by omega, P005561.A0, P005561.A1, P005561.A2]
    have h := P005561.Bpos i
    simp only [P005561.b4_0, P005561.b5_0, P005561.b5_1, P005561.b6_1, P005561.b7_1, P005561.b7_2]
    push_cast
    field_simp
    ring
  · obtain ⟨i, rfl⟩ : ∃ i, m = i + 3 := ⟨m - 3, by omega⟩
    subst hm
    rw [show 2 * (i + 3) + 1 - 1 = 2 * i + 6 by omega, show 2 * (i + 3) + 1 - 2 = 2 * i + 5 by omega,
      show 2 * (i + 3) + 1 = 2 * i + 7 by omega, P005561.A1, P005561.A2, P005561.A3]
    have h := P005561.Bpos i
    simp only [P005561.b5_0, P005561.b5_1, P005561.b6_1, P005561.b7_1, P005561.b7_2, P005561.b8_2]
    push_cast
    field_simp
    ring
