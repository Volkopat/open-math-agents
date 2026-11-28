import OMAStatements.S_oeis_a005560
import Mathlib

open OMA.S_oeis_a005560

namespace P005560

noncomputable def B (i : ℕ) : ℚ := ((2 * i).factorial : ℚ) / (i.factorial * i.factorial)

theorem Bpos (i : ℕ) : B i ≠ 0 := by unfold B; positivity

theorem ch (N k : ℕ) (h : k ≤ N) : ((N.choose k : ℕ) : ℚ) = (N.factorial : ℚ) / (k.factorial * (N - k).factorial) :=
  Nat.cast_choose ℚ h

theorem b3_0 (i : ℕ) : ((Nat.choose (2 * i + 3) i : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3)) / (((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3)) := by
  rw [ch _ _ (by omega), show 2 * i + 3 - i = i + 3 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem b4_0 (i : ℕ) : ((Nat.choose (2 * i + 4) i : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4)) / (((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4)) := by
  rw [ch _ _ (by omega), show 2 * i + 4 - i = i + 4 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem b4_1 (i : ℕ) : ((Nat.choose (2 * i + 4) (i + 1) : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4)) / (((i : ℚ) + 1) * ((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3)) := by
  rw [ch _ _ (by omega), show 2 * i + 4 - (i + 1) = i + 3 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem b5_1 (i : ℕ) : ((Nat.choose (2 * i + 5) (i + 1) : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4) * (2 * (i : ℚ) + 5)) / (((i : ℚ) + 1) * ((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4)) := by
  rw [ch _ _ (by omega), show 2 * i + 5 - (i + 1) = i + 4 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem b6_1 (i : ℕ) : ((Nat.choose (2 * i + 6) (i + 1) : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4) * (2 * (i : ℚ) + 5) * (2 * (i : ℚ) + 6)) / (((i : ℚ) + 1) * ((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4) * ((i : ℚ) + 5)) := by
  rw [ch _ _ (by omega), show 2 * i + 6 - (i + 1) = i + 5 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem b6_2 (i : ℕ) : ((Nat.choose (2 * i + 6) (i + 2) : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4) * (2 * (i : ℚ) + 5) * (2 * (i : ℚ) + 6)) / (((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4)) := by
  rw [ch _ _ (by omega), show 2 * i + 6 - (i + 2) = i + 4 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem b7_2 (i : ℕ) : ((Nat.choose (2 * i + 7) (i + 2) : ℕ) : ℚ) = B i * ((2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 2) * (2 * (i : ℚ) + 3) * (2 * (i : ℚ) + 4) * (2 * (i : ℚ) + 5) * (2 * (i : ℚ) + 6) * (2 * (i : ℚ) + 7)) / (((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 1) * ((i : ℚ) + 2) * ((i : ℚ) + 3) * ((i : ℚ) + 4) * ((i : ℚ) + 5)) := by
  rw [ch _ _ (by omega), show 2 * i + 7 - (i + 2) = i + 5 by omega]
  unfold B
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem at_eq (t : ℕ) : (a (t + 3) : ℚ) = ((t + 4).choose ((t + 2) / 2) : ℚ) * (t + 3).choose ((t + 1) / 2) -
    ((t + 4).choose ((t + 1) / 2) : ℚ) * (t + 3).choose (t / 2) := by
  simp only [a, column]
  rw [show 2 + t + 1 + 1 = t + 4 by ring, show 2 + t + 1 = t + 3 by ring]

theorem A0 (i : ℕ) : (a (2 * i + 3) : ℚ) = (Nat.choose (2 * i + 4) (i + 1) : ℚ) * (Nat.choose (2 * i + 3) i : ℚ) - (Nat.choose (2 * i + 4) i : ℚ) * (Nat.choose (2 * i + 3) i : ℚ) := by
  rw [at_eq, show (2 * i + 2) / 2 = i + 1 by omega, show (2 * i + 1) / 2 = i by omega, show 2 * i / 2 = i by omega]

theorem A1 (i : ℕ) : (a (2 * i + 4) : ℚ) = (Nat.choose (2 * i + 5) (i + 1) : ℚ) * (Nat.choose (2 * i + 4) (i + 1) : ℚ) - (Nat.choose (2 * i + 5) (i + 1) : ℚ) * (Nat.choose (2 * i + 4) i : ℚ) := by
  rw [show 2 * i + 4 = 2 * i + 1 + 3 by ring, at_eq, show 2 * i + 1 + 4 = 2 * i + 5 by ring, show 2 * i + 1 + 3 = 2 * i + 4 by ring, show (2 * i + 1 + 2) / 2 = i + 1 by omega, show (2 * i + 1 + 1) / 2 = i + 1 by omega, show (2 * i + 1) / 2 = i by omega]

theorem A2 (i : ℕ) : (a (2 * i + 5) : ℚ) = (Nat.choose (2 * i + 6) (i + 2) : ℚ) * (Nat.choose (2 * i + 5) (i + 1) : ℚ) - (Nat.choose (2 * i + 6) (i + 1) : ℚ) * (Nat.choose (2 * i + 5) (i + 1) : ℚ) := by
  rw [show 2 * i + 5 = 2 * i + 2 + 3 by ring, at_eq, show 2 * i + 2 + 4 = 2 * i + 6 by ring, show 2 * i + 2 + 3 = 2 * i + 5 by ring, show (2 * i + 2 + 2) / 2 = i + 2 by omega, show (2 * i + 2 + 1) / 2 = i + 1 by omega, show (2 * i + 2) / 2 = i + 1 by omega]

theorem A3 (i : ℕ) : (a (2 * i + 6) : ℚ) = (Nat.choose (2 * i + 7) (i + 2) : ℚ) * (Nat.choose (2 * i + 6) (i + 2) : ℚ) - (Nat.choose (2 * i + 7) (i + 2) : ℚ) * (Nat.choose (2 * i + 6) (i + 1) : ℚ) := by
  rw [show 2 * i + 6 = 2 * i + 3 + 3 by ring, at_eq, show 2 * i + 3 + 4 = 2 * i + 7 by ring, show 2 * i + 3 + 3 = 2 * i + 6 by ring, show (2 * i + 3 + 2) / 2 = i + 2 by omega, show (2 * i + 3 + 1) / 2 = i + 2 by omega, show (2 * i + 3) / 2 = i + 1 by omega]

end P005560

theorem OMA.solution : type_of% @OMA.S_oeis_a005560.main := by
  intro n hn
  rcases Nat.lt_or_ge n 5 with h3 | h4
  · obtain rfl : n = 4 := by omega
    simp [a, column, Nat.choose]
    norm_num
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨i, rfl⟩ : ∃ i, m = i + 3 := ⟨m - 3, by omega⟩
    subst hm
    rw [show i + 3 + (i + 3) - 1 = 2 * i + 5 by omega, show i + 3 + (i + 3) - 2 = 2 * i + 4 by omega,
      show i + 3 + (i + 3) = 2 * i + 6 by omega, P005560.A1, P005560.A2, P005560.A3]
    have h := P005560.Bpos i
    simp only [P005560.b4_0, P005560.b4_1, P005560.b5_1, P005560.b6_1, P005560.b6_2, P005560.b7_2]
    push_cast
    field_simp
    ring
  · obtain ⟨i, rfl⟩ : ∃ i, m = i + 2 := ⟨m - 2, by omega⟩
    subst hm
    rw [show 2 * (i + 2) + 1 - 1 = 2 * i + 4 by omega, show 2 * (i + 2) + 1 - 2 = 2 * i + 3 by omega,
      show 2 * (i + 2) + 1 = 2 * i + 5 by omega, P005560.A0, P005560.A1, P005560.A2]
    have h := P005560.Bpos i
    simp only [P005560.b3_0, P005560.b4_0, P005560.b4_1, P005560.b5_1, P005560.b6_1, P005560.b6_2]
    push_cast
    field_simp
    ring
