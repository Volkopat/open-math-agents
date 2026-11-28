import OMAStatements.S_oeis_a081181
import Mathlib

open OMA.S_oeis_a081181

namespace P081181

noncomputable def E (j : ℕ) : ℚ := ((3 * j).factorial : ℚ) / ((2 * j).factorial * j.factorial)

theorem Epos (j : ℕ) : E j ≠ 0 := by unfold E; positivity

theorem ch (N k : ℕ) (h : k ≤ N) : ((N.choose k : ℕ) : ℚ) = (N.factorial : ℚ) / (k.factorial * (N - k).factorial) :=
  Nat.cast_choose ℚ h

theorem v0 (j : ℕ) : (a (2 * j) : ℚ) = E j * ((3 * (j : ℚ) + 1)) / (((j : ℚ) + 1)) := by
  unfold a E
  rw [show (2 * j + 1) / 2 + (2 * j + 1) = 3 * j + 1 by omega, ch _ _ (by omega),
    show 3 * j + 1 - (2 * j) = j + 1 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem v1 (j : ℕ) : (a (2 * j + 1) : ℚ) = E j * ((3 * (j : ℚ) + 1) * (3 * (j : ℚ) + 2) * (3 * (j : ℚ) + 3)) / ((2 * (j : ℚ) + 1) * ((j : ℚ) + 1) * ((j : ℚ) + 2)) := by
  unfold a E
  rw [show (2 * j + 1 + 1) / 2 + (2 * j + 1 + 1) = 3 * j + 3 by omega, ch _ _ (by omega),
    show 3 * j + 3 - (2 * j + 1) = j + 2 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem v2 (j : ℕ) : (a (2 * j + 2) : ℚ) = E j * ((3 * (j : ℚ) + 1) * (3 * (j : ℚ) + 2) * (3 * (j : ℚ) + 3) * (3 * (j : ℚ) + 4)) / ((2 * (j : ℚ) + 1) * (2 * (j : ℚ) + 2) * ((j : ℚ) + 1) * ((j : ℚ) + 2)) := by
  unfold a E
  rw [show (2 * j + 2 + 1) / 2 + (2 * j + 2 + 1) = 3 * j + 4 by omega, ch _ _ (by omega),
    show 3 * j + 4 - (2 * j + 2) = j + 2 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem v3 (j : ℕ) : (a (2 * j + 3) : ℚ) = E j * ((3 * (j : ℚ) + 1) * (3 * (j : ℚ) + 2) * (3 * (j : ℚ) + 3) * (3 * (j : ℚ) + 4) * (3 * (j : ℚ) + 5) * (3 * (j : ℚ) + 6)) / ((2 * (j : ℚ) + 1) * (2 * (j : ℚ) + 2) * (2 * (j : ℚ) + 3) * ((j : ℚ) + 1) * ((j : ℚ) + 2) * ((j : ℚ) + 3)) := by
  unfold a E
  rw [show (2 * j + 3 + 1) / 2 + (2 * j + 3 + 1) = 3 * j + 6 by omega, ch _ _ (by omega),
    show 3 * j + 6 - (2 * j + 3) = j + 3 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem v4 (j : ℕ) : (a (2 * j + 4) : ℚ) = E j * ((3 * (j : ℚ) + 1) * (3 * (j : ℚ) + 2) * (3 * (j : ℚ) + 3) * (3 * (j : ℚ) + 4) * (3 * (j : ℚ) + 5) * (3 * (j : ℚ) + 6) * (3 * (j : ℚ) + 7)) / ((2 * (j : ℚ) + 1) * (2 * (j : ℚ) + 2) * (2 * (j : ℚ) + 3) * (2 * (j : ℚ) + 4) * ((j : ℚ) + 1) * ((j : ℚ) + 2) * ((j : ℚ) + 3)) := by
  unfold a E
  rw [show (2 * j + 4 + 1) / 2 + (2 * j + 4 + 1) = 3 * j + 7 by omega, ch _ _ (by omega),
    show 3 * j + 7 - (2 * j + 4) = j + 3 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  try ring

end P081181

set_option maxRecDepth 100000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081181.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    subst hm
    rw [show j + 2 + (j + 2) = 2 * j + 4 by omega]
    have h := P081181.Epos j
    have e : (((8 * ((2 * j + 4 : ℕ) : ℤ) * (((2 * j + 4 : ℕ) : ℤ) + 3) * (1845 * ((2 * j + 4 : ℕ) : ℤ) - 2882) * a (2 * j + 4)
        + 4 * (-5097 * ((2 * j + 4 : ℕ) : ℤ) ^ 3 + 11143 * ((2 * j + 4 : ℕ) : ℤ) ^ 2 + 42110 * ((2 * j + 4 : ℕ) : ℤ) - 27416) * a (2 * j + 4 - 1)
        + 6 * (-16605 * ((2 * j + 4 : ℕ) : ℤ) ^ 3 - 7272 * ((2 * j + 4 : ℕ) : ℤ) ^ 2 - 16701 * ((2 * j + 4 : ℕ) : ℤ) + 9490) * a (2 * j + 4 - 2)
        + 3 * (3 * ((2 * j + 4 : ℕ) : ℤ) - 5) * (5097 * ((2 * j + 4 : ℕ) : ℤ) - 949) * (3 * ((2 * j + 4 : ℕ) : ℤ) - 4) * a (2 * j + 4 - 3)) : ℤ) : ℚ) = 0 := by
      rw [show 2 * j + 4 - 1 = 2 * j + 3 by omega, show 2 * j + 4 - 2 = 2 * j + 2 by omega,
        show 2 * j + 4 - 3 = 2 * j + 1 by omega]
      push_cast
      rw [P081181.v1, P081181.v2, P081181.v3, P081181.v4]
      field_simp
      ring
    exact_mod_cast e
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    subst hm
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
    have h := P081181.Epos j
    have e : (((8 * ((2 * j + 3 : ℕ) : ℤ) * (((2 * j + 3 : ℕ) : ℤ) + 3) * (1845 * ((2 * j + 3 : ℕ) : ℤ) - 2882) * a (2 * j + 3)
        + 4 * (-5097 * ((2 * j + 3 : ℕ) : ℤ) ^ 3 + 11143 * ((2 * j + 3 : ℕ) : ℤ) ^ 2 + 42110 * ((2 * j + 3 : ℕ) : ℤ) - 27416) * a (2 * j + 3 - 1)
        + 6 * (-16605 * ((2 * j + 3 : ℕ) : ℤ) ^ 3 - 7272 * ((2 * j + 3 : ℕ) : ℤ) ^ 2 - 16701 * ((2 * j + 3 : ℕ) : ℤ) + 9490) * a (2 * j + 3 - 2)
        + 3 * (3 * ((2 * j + 3 : ℕ) : ℤ) - 5) * (5097 * ((2 * j + 3 : ℕ) : ℤ) - 949) * (3 * ((2 * j + 3 : ℕ) : ℤ) - 4) * a (2 * j + 3 - 3)) : ℤ) : ℚ) = 0 := by
      rw [show 2 * j + 3 - 1 = 2 * j + 2 by omega, show 2 * j + 3 - 2 = 2 * j + 1 by omega,
        show 2 * j + 3 - 3 = 2 * j by omega]
      push_cast
      rw [P081181.v0, P081181.v1, P081181.v2, P081181.v3]
      field_simp
      ring
    exact_mod_cast e
