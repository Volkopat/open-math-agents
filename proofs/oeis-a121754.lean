import OMAStatements.S_oeis_a121754
import Mathlib

open OMA.S_oeis_a121754

namespace P121754

theorem fsucc (x : ℕ) : ((x + 1).factorial : ℚ) = ((x : ℚ) + 1) * (x.factorial : ℚ) := by
  rw [Nat.factorial_succ]; push_cast; ring

theorem Eo (j : ℕ) : a (2 * j + 3) = (-3 + 2 * (2 * (j : ℚ) + 3)) * a (2 * j + 2) - (3 - 4 * (2 * (j : ℚ) + 3) + (2 * (j : ℚ) + 3) ^ 2) * a (2 * j + 1) +
    ((2 * j + 1).factorial : ℚ) * (-3 + 2 * (2 * (j : ℚ) + 3)) := by
  rw [a]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one]
  push_cast
  ring

theorem Ee (j : ℕ) : a (2 * j + 4) = (-3 + 2 * (2 * (j : ℚ) + 4)) * a (2 * j + 3) - (3 - 4 * (2 * (j : ℚ) + 4) + (2 * (j : ℚ) + 4) ^ 2) * a (2 * j + 2) +
    ((2 * j + 2).factorial : ℚ) * (-2 + (2 * (j : ℚ) + 4)) := by
  rw [show 2 * j + 4 = (2 * j + 1) + 3 by ring, a]
  simp only [show 2 * j + 1 + 2 = 2 * j + 3 by ring, show 2 * j + 1 + 1 = 2 * j + 2 by ring, pow_add, pow_mul, neg_one_sq, one_pow, pow_one]
  push_cast
  ring

theorem FO : ∀ j : ℕ, ((4 - 2 * (2 * (j : ℚ) + 3)) * a (2 * j + 3) + (-4 * (2 * (j : ℚ) + 3) + 2 * (2 * (j : ℚ) + 3) ^ 2) * a (2 * j + 2) + (-(3 / 2) + 4 * (2 * (j : ℚ) + 3) - (7 / 2) * (2 * (j : ℚ) + 3) ^ 2 + (2 * (j : ℚ) + 3) ^ 3) * ((2 * j + 1).factorial : ℚ) = 0) ∧ ((-2) * a (2 * j + 4) + (2 * (2 * (j : ℚ) + 4)) * a (2 * j + 3) + (1 - (5 / 2) * (2 * (j : ℚ) + 4) + (2 * (j : ℚ) + 4) ^ 2) * ((2 * j + 2).factorial : ℚ) = 0)
  | 0 => by
    have e3 := Eo 0
    have e4 := Ee 0
    have h1 : a 1 = 0 := by simp [a]
    have h2 : a 2 = 1 := by simp [a]
    norm_num [Nat.factorial] at e3 e4 ⊢
    simp only [h1, h2] at e3 e4
    constructor <;> linarith
  | j + 1 => by
    obtain ⟨ho, he⟩ := FO j
    have e5 := Eo (j + 1)
    have e6 := Ee (j + 1)
    simp only [show 2 * (j + 1) + 3 = 2 * j + 5 by ring, show 2 * (j + 1) + 2 = 2 * j + 4 by ring,
      show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show 2 * (j + 1) + 4 = 2 * j + 6 by ring] at e5 e6 ⊢
    have f3 : ((2 * j + 3).factorial : ℚ) = (2 * (j : ℚ) + 3) * ((2 * j + 2).factorial : ℚ) := by
      rw [show 2 * j + 3 = (2 * j + 2) + 1 by ring, fsucc]; push_cast; ring
    have f4 : ((2 * j + 4).factorial : ℚ) = (2 * (j : ℚ) + 4) * (2 * (j : ℚ) + 3) * ((2 * j + 2).factorial : ℚ) := by
      rw [show 2 * j + 4 = (2 * j + 3) + 1 by ring, fsucc, f3]; push_cast; ring
    simp only [f4] at e6 ⊢
    simp only [f3] at e5 e6 ⊢
    push_cast at e5 e6 ⊢
    have ho1 : (4 - 2 * (2 * ((j : ℚ) + 1) + 3)) * a (2 * j + 5) + (-4 * (2 * ((j : ℚ) + 1) + 3) + 2 * (2 * ((j : ℚ) + 1) + 3) ^ 2) * a (2 * j + 4) + (-(3 / 2) + 4 * (2 * ((j : ℚ) + 1) + 3) - (7 / 2) * (2 * ((j : ℚ) + 1) + 3) ^ 2 + (2 * ((j : ℚ) + 1) + 3) ^ 3) * ((2 * (j : ℚ) + 3) * ((2 * j + 2).factorial : ℚ)) = 0 := by
      linear_combination ((2 - 2 * (2 * (j : ℚ) + 4))) * (e5) + ((2 - 3 * (2 * (j : ℚ) + 4) + (2 * (j : ℚ) + 4) ^ 2)) * he
    refine ⟨ho1, ?_⟩
    linear_combination ((-2)) * (e6) + ((1)) * ho1

end P121754

theorem OMA.solution : type_of% @OMA.S_oeis_a121754.main := by
  intro n hn
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 6 ∨ n = 2 * k + 7 := ⟨(n - 6) / 2, by omega⟩
  · simp only [show 2 * k + 6 - 1 = 2 * k + 5 by omega, show 2 * k + 6 - 2 = 2 * k + 4 by omega, show 2 * k + 6 - 3 = 2 * k + 3 by omega, show 2 * k + 6 - 4 = 2 * k + 2 by omega, show 2 * k + 6 - 5 = 2 * k + 1 by omega]
    have hf0 := (P121754.FO (k + 1)).2
    have he0 := P121754.Ee (k + 1)
    have hf1 := (P121754.FO (k + 1)).1
    have he1 := P121754.Eo (k + 1)
    have hf2 := (P121754.FO (k + 0)).2
    have he2 := P121754.Ee (k + 0)
    have hf3 := (P121754.FO (k + 0)).1
    have he3 := P121754.Eo (k + 0)
    simp only [show 2 * (k + 1) + 0 = 2 * k + 2 by ring, show 2 * (k + 1) + 1 = 2 * k + 3 by ring, show 2 * (k + 1) + 2 = 2 * k + 4 by ring, show 2 * (k + 1) + 3 = 2 * k + 5 by ring, show 2 * (k + 1) + 4 = 2 * k + 6 by ring, show 2 * (k + 2) + 0 = 2 * k + 4 by ring, show 2 * (k + 2) + 1 = 2 * k + 5 by ring, show 2 * (k + 2) + 2 = 2 * k + 6 by ring, show 2 * (k + 2) + 3 = 2 * k + 7 by ring, show 2 * (k + 2) + 4 = 2 * k + 8 by ring, show 2 * (k + 0) + 0 = 2 * k + 0 by ring, show 2 * (k + 0) + 1 = 2 * k + 1 by ring, show 2 * (k + 0) + 2 = 2 * k + 2 by ring, show 2 * (k + 0) + 3 = 2 * k + 3 by ring, show 2 * (k + 0) + 4 = 2 * k + 4 by ring] at hf0 hf1 hf2 hf3 he0 he1 he2 he3
    have f2 : ((2 * k + 2).factorial : ℚ) = (2 * (k : ℚ) + 2) * ((2 * k + 1).factorial : ℚ) := by
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, P121754.fsucc]; push_cast; ring
    have f3 : ((2 * k + 3).factorial : ℚ) = (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 2) * ((2 * k + 1).factorial : ℚ) := by
      rw [show 2 * k + 3 = (2 * k + 2) + 1 by ring, P121754.fsucc, show 2 * k + 2 = (2 * k + 1) + 1 by ring, P121754.fsucc]; push_cast; ring
    have f4 : ((2 * k + 4).factorial : ℚ) = (2 * (k : ℚ) + 4) * (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 2) * ((2 * k + 1).factorial : ℚ) := by
      rw [show 2 * k + 4 = (2 * k + 3) + 1 by ring, P121754.fsucc, show 2 * k + 3 = (2 * k + 2) + 1 by ring, P121754.fsucc, show 2 * k + 2 = (2 * k + 1) + 1 by ring, P121754.fsucc]; push_cast; ring
    simp only [f4, f3, f2] at hf0 hf1 hf2 hf3 he0 he1 he2 he3
    push_cast at hf0 hf1 hf2 hf3 he0 he1 he2 he3 ⊢
    linear_combination (-8 - 8 * (2 * (k : ℚ) + 6)) * hf0 + 0 * he0 + (105 + 8 * (2 * (k : ℚ) + 6)) * hf1 + (-99 + 16 * (2 * (k : ℚ) + 6) ^ 2) * he1 + ((645 / 2) - (201 / 2) * (2 * (k : ℚ) + 6) + 24 * (2 * (k : ℚ) + 6) ^ 2) * hf2 + 0 * he2 + (-(557 / 2) + (571 / 2) * (2 * (k : ℚ) + 6) - 73 * (2 * (k : ℚ) + 6) ^ 2) * hf3 + (1244 - 831 * (2 * (k : ℚ) + 6) + 130 * (2 * (k : ℚ) + 6) ^ 2) * he3
  · simp only [show 2 * k + 7 - 1 = 2 * k + 6 by omega, show 2 * k + 7 - 2 = 2 * k + 5 by omega, show 2 * k + 7 - 3 = 2 * k + 4 by omega, show 2 * k + 7 - 4 = 2 * k + 3 by omega, show 2 * k + 7 - 5 = 2 * k + 2 by omega]
    have hf0 := (P121754.FO (k + 2)).1
    have he0 := P121754.Eo (k + 2)
    have hf1 := (P121754.FO (k + 1)).2
    have he1 := P121754.Ee (k + 1)
    have hf2 := (P121754.FO (k + 1)).1
    have he2 := P121754.Eo (k + 1)
    have hf3 := (P121754.FO (k + 0)).2
    have he3 := P121754.Ee (k + 0)
    simp only [show 2 * (k + 1) + 0 = 2 * k + 2 by ring, show 2 * (k + 1) + 1 = 2 * k + 3 by ring, show 2 * (k + 1) + 2 = 2 * k + 4 by ring, show 2 * (k + 1) + 3 = 2 * k + 5 by ring, show 2 * (k + 1) + 4 = 2 * k + 6 by ring, show 2 * (k + 2) + 0 = 2 * k + 4 by ring, show 2 * (k + 2) + 1 = 2 * k + 5 by ring, show 2 * (k + 2) + 2 = 2 * k + 6 by ring, show 2 * (k + 2) + 3 = 2 * k + 7 by ring, show 2 * (k + 2) + 4 = 2 * k + 8 by ring, show 2 * (k + 0) + 0 = 2 * k + 0 by ring, show 2 * (k + 0) + 1 = 2 * k + 1 by ring, show 2 * (k + 0) + 2 = 2 * k + 2 by ring, show 2 * (k + 0) + 3 = 2 * k + 3 by ring, show 2 * (k + 0) + 4 = 2 * k + 4 by ring] at hf0 hf1 hf2 hf3 he0 he1 he2 he3
    have f3 : ((2 * k + 3).factorial : ℚ) = (2 * (k : ℚ) + 3) * ((2 * k + 2).factorial : ℚ) := by
      rw [show 2 * k + 3 = (2 * k + 2) + 1 by ring, P121754.fsucc]; push_cast; ring
    have f4 : ((2 * k + 4).factorial : ℚ) = (2 * (k : ℚ) + 4) * (2 * (k : ℚ) + 3) * ((2 * k + 2).factorial : ℚ) := by
      rw [show 2 * k + 4 = (2 * k + 3) + 1 by ring, P121754.fsucc, show 2 * k + 3 = (2 * k + 2) + 1 by ring, P121754.fsucc]; push_cast; ring
    have f5 : ((2 * k + 5).factorial : ℚ) = (2 * (k : ℚ) + 5) * (2 * (k : ℚ) + 4) * (2 * (k : ℚ) + 3) * ((2 * k + 2).factorial : ℚ) := by
      rw [show 2 * k + 5 = (2 * k + 4) + 1 by ring, P121754.fsucc, show 2 * k + 4 = (2 * k + 3) + 1 by ring, P121754.fsucc, show 2 * k + 3 = (2 * k + 2) + 1 by ring, P121754.fsucc]; push_cast; ring
    simp only [f5, f4, f3] at hf0 hf1 hf2 hf3 he0 he1 he2 he3
    push_cast at hf0 hf1 hf2 hf3 he0 he1 he2 he3 ⊢
    linear_combination (-8) * hf0 + (48) * he0 + (-(387 / 2) + 57 * (2 * (k : ℚ) + 7)) * hf1 + 0 * he1 + (-346 - 49 * (2 * (k : ℚ) + 7) + 8 * (2 * (k : ℚ) + 7) ^ 2) * hf2 + (1727 - 146 * (2 * (k : ℚ) + 7) ^ 2) * he2 + (5710 - (5139 / 2) * (2 * (k : ℚ) + 7) + (571 / 2) * (2 * (k : ℚ) + 7) ^ 2) * hf3 + (1244 - 831 * (2 * (k : ℚ) + 7) + 130 * (2 * (k : ℚ) + 7) ^ 2) * he3
