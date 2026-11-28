import OMAStatements.S_oeis_a184674
import Mathlib

lemma OMA.bnd (y : ℚ) (hy : 1 ≤ y) : 0 < 1 / (4 * y ^ 2) ∧ 1 / (4 * y ^ 2) ≤ 1 / 4 := by
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem OMA.solution : type_of% @OMA.S_oeis_a184674.main := by
  intro n hn
  simp only [OMA.S_oeis_a184674.a, OMA.S_oeis_a184674.b]
  have hy : (1 : ℚ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have e : ((n : ℚ) / 2 - 1 / (2 * (n : ℚ))) ^ 2 = (n : ℚ) ^ 2 / 4 - 1 / 2 + 1 / (4 * (n : ℚ) ^ 2) := by
    have : (n : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  rw [e]
  obtain ⟨b1, b2⟩ := OMA.bnd n hy
  rw [show n - 1 = n - 1 from rfl]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h1 : ⌊((2 * (k + 1) : ℕ) : ℚ) ^ 2 / 4 - 1 / 2 + 1 / (4 * ((2 * (k + 1) : ℕ) : ℚ) ^ 2)⌋ =
        ((k : ℤ) + 1) ^ 2 - 1 := by
      rw [Int.floor_eq_iff]
      push_cast at b1 b2 ⊢
      constructor <;> nlinarith
    have h2 : ⌊((((2 * (k + 1) - 1 : ℕ) : ℚ)) ^ 2 + 6 * (((2 * (k + 1) - 1 : ℕ) : ℚ)) + 1) / 4⌋ =
        ((k : ℤ) + 1) ^ 2 + 2 * ((k : ℤ) + 1) - 1 := by
      rw [Int.floor_eq_iff, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      push_cast
      constructor <;> nlinarith
    rw [h1, h2]
    push_cast
    ring
  · have hm : (1 : ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have b3 : 1 / (4 * (2 * (m : ℚ) + 1) ^ 2) < 1 / 4 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h1 : ⌊((2 * m + 1 : ℕ) : ℚ) ^ 2 / 4 - 1 / 2 + 1 / (4 * ((2 * m + 1 : ℕ) : ℚ) ^ 2)⌋ =
        (m : ℤ) ^ 2 + m - 1 := by
      rw [Int.floor_eq_iff]
      push_cast at b1 b2 ⊢
      constructor <;> nlinarith
    have h2 : ⌊((((2 * m + 1 - 1 : ℕ) : ℚ)) ^ 2 + 6 * (((2 * m + 1 - 1 : ℕ) : ℚ)) + 1) / 4⌋ =
        (m : ℤ) ^ 2 + 3 * m := by
      rw [Int.floor_eq_iff, show 2 * m + 1 - 1 = 2 * m by omega]
      push_cast
      constructor <;> nlinarith
    rw [h1, h2]
    push_cast
    ring
