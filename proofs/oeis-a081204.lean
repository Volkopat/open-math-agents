import OMAStatements.S_oeis_a081204
import Mathlib

open OMA.S_oeis_a081204

namespace P081204

noncomputable def E (j : ℕ) : ℚ := ((3 * j).factorial : ℚ) / ((2 * j).factorial * j.factorial)

theorem Epos (j : ℕ) : E j ≠ 0 := by unfold E; positivity

theorem ch (N k : ℕ) (h : k ≤ N) : ((N.choose k : ℕ) : ℚ) = (N.factorial : ℚ) / (k.factorial * (N - k).factorial) :=
  Nat.cast_choose ℚ h

theorem v0 (j : ℕ) : (a (2 * j) : ℚ) = E j := by
  unfold a E
  rw [show (2 * j + 1) / 2 + 2 * j = 3 * j by omega, ch _ _ (by omega), show 3 * j - 2 * j = j by omega]

theorem v1 (j : ℕ) : (a (2 * j + 1) : ℚ) = E j * ((3 * j + 2) * (3 * j + 1) / ((2 * j + 1) * (j + 1))) := by
  unfold a E
  rw [show (2 * j + 1 + 1) / 2 + (2 * j + 1) = 3 * j + 2 by omega, ch _ _ (by omega),
    show 3 * j + 2 - (2 * j + 1) = j + 1 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem v2 (j : ℕ) : (a (2 * j + 2) : ℚ) =
    E j * ((3 * j + 3) * (3 * j + 2) * (3 * j + 1) / ((2 * j + 2) * (2 * j + 1) * (j + 1))) := by
  unfold a E
  rw [show (2 * j + 2 + 1) / 2 + (2 * j + 2) = 3 * j + 3 by omega, ch _ _ (by omega),
    show 3 * j + 3 - (2 * j + 2) = j + 1 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem v3 (j : ℕ) : (a (2 * j + 3) : ℚ) =
    E j * ((3 * j + 5) * (3 * j + 4) * (3 * j + 3) * (3 * j + 2) * (3 * j + 1) /
      ((2 * j + 3) * (2 * j + 2) * (2 * j + 1) * (j + 2) * (j + 1))) := by
  unfold a E
  rw [show (2 * j + 3 + 1) / 2 + (2 * j + 3) = 3 * j + 5 by omega, ch _ _ (by omega),
    show 3 * j + 5 - (2 * j + 3) = j + 2 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem v4 (j : ℕ) : (a (2 * j + 4) : ℚ) =
    E j * ((3 * j + 6) * (3 * j + 5) * (3 * j + 4) * (3 * j + 3) * (3 * j + 2) * (3 * j + 1) /
      ((2 * j + 4) * (2 * j + 3) * (2 * j + 2) * (2 * j + 1) * (j + 2) * (j + 1))) := by
  unfold a E
  rw [show (2 * j + 4 + 1) / 2 + (2 * j + 4) = 3 * j + 6 by omega, ch _ _ (by omega),
    show 3 * j + 6 - (2 * j + 4) = j + 2 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

end P081204

theorem OMA.solution : type_of% @OMA.S_oeis_a081204.main := by
  constructor
  · intro n hn
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      subst hm
      rw [show j + 1 + (j + 1) - 1 = 2 * j + 1 by omega, show j + 1 + (j + 1) - 2 = 2 * j by omega,
        show j + 1 + (j + 1) = 2 * j + 2 by omega]
      have h := P081204.Epos j
      have e : ((4 * ((2 * j + 2 : ℕ) : ℤ) * ((2 * j + 2 : ℕ) + 1) * (6 * (2 * j + 2 : ℕ) ^ 2 - 15 * (2 * j + 2 : ℕ) + 8) * a (2 * j + 2)
          + 6 * ((2 * j + 2 : ℕ) : ℤ) * (9 * (2 * j + 2 : ℕ) - 7) * a (2 * j + 1)
          - 3 * (3 * ((2 * j + 2 : ℕ) : ℤ) - 4) * (3 * (2 * j + 2 : ℕ) - 2) * (6 * (2 * j + 2 : ℕ) ^ 2 - 3 * (2 * j + 2 : ℕ) - 1) * a (2 * j) : ℤ) : ℚ) = 0 := by
        push_cast
        rw [P081204.v0, P081204.v1, P081204.v2]
        field_simp
        ring
      exact_mod_cast e
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      subst hm
      rw [show 2 * (j + 1) + 1 - 1 = 2 * j + 2 by omega, show 2 * (j + 1) + 1 - 2 = 2 * j + 1 by omega,
        show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
      have h := P081204.Epos j
      have e : ((4 * ((2 * j + 3 : ℕ) : ℤ) * ((2 * j + 3 : ℕ) + 1) * (6 * (2 * j + 3 : ℕ) ^ 2 - 15 * (2 * j + 3 : ℕ) + 8) * a (2 * j + 3)
          + 6 * ((2 * j + 3 : ℕ) : ℤ) * (9 * (2 * j + 3 : ℕ) - 7) * a (2 * j + 2)
          - 3 * (3 * ((2 * j + 3 : ℕ) : ℤ) - 4) * (3 * (2 * j + 3 : ℕ) - 2) * (6 * (2 * j + 3 : ℕ) ^ 2 - 3 * (2 * j + 3 : ℕ) - 1) * a (2 * j + 1) : ℤ) : ℚ) = 0 := by
        push_cast
        rw [P081204.v1, P081204.v2, P081204.v3]
        field_simp
        ring
      exact_mod_cast e
  · intro n hn
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
      subst hm
      rw [show j + 2 + (j + 2) - 1 = 2 * j + 3 by omega, show j + 2 + (j + 2) - 2 = 2 * j + 2 by omega,
        show j + 2 + (j + 2) - 3 = 2 * j + 1 by omega, show j + 2 + (j + 2) = 2 * j + 4 by omega]
      have h := P081204.Epos j
      have e : ((8 * ((2 * j + 4 : ℕ) : ℤ) ^ 2 * ((2 * j + 4 : ℕ) + 1) * a (2 * j + 4)
          - 12 * ((2 * j + 4 : ℕ) : ℤ) * (83 * (2 * j + 4 : ℕ) ^ 2 - 313 * (2 * j + 4 : ℕ) + 232) * a (2 * j + 3)
          + 6 * (-9 * ((2 * j + 4 : ℕ) : ℤ) ^ 3 - 377 * (2 * j + 4 : ℕ) + 384) * a (2 * j + 2)
          + 9 * (3 * ((2 * j + 4 : ℕ) : ℤ) - 5) * (83 * (2 * j + 4 : ℕ) - 64) * (3 * (2 * j + 4 : ℕ) - 7) * a (2 * j + 1) : ℤ) : ℚ) = 0 := by
        push_cast
        rw [P081204.v1, P081204.v2, P081204.v3, P081204.v4]
        field_simp
        ring
      exact_mod_cast e
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      subst hm
      rw [show 2 * (j + 1) + 1 - 1 = 2 * j + 2 by omega, show 2 * (j + 1) + 1 - 2 = 2 * j + 1 by omega,
        show 2 * (j + 1) + 1 - 3 = 2 * j by omega, show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
      have h := P081204.Epos j
      have e : ((8 * ((2 * j + 3 : ℕ) : ℤ) ^ 2 * ((2 * j + 3 : ℕ) + 1) * a (2 * j + 3)
          - 12 * ((2 * j + 3 : ℕ) : ℤ) * (83 * (2 * j + 3 : ℕ) ^ 2 - 313 * (2 * j + 3 : ℕ) + 232) * a (2 * j + 2)
          + 6 * (-9 * ((2 * j + 3 : ℕ) : ℤ) ^ 3 - 377 * (2 * j + 3 : ℕ) + 384) * a (2 * j + 1)
          + 9 * (3 * ((2 * j + 3 : ℕ) : ℤ) - 5) * (83 * (2 * j + 3 : ℕ) - 64) * (3 * (2 * j + 3 : ℕ) - 7) * a (2 * j) : ℤ) : ℚ) = 0 := by
        push_cast
        rw [P081204.v0, P081204.v1, P081204.v2, P081204.v3]
        field_simp
        ring
      exact_mod_cast e
