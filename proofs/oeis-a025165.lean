import OMAStatements.S_oeis_a025165
import Mathlib

open OMA.S_oeis_a025165 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025165.main := by
  have hr : ∀ n : ℕ, hermiteOne (n + 2)
      = 2 * hermiteOne (n + 1) - 2 * ((n : ℤ) + 1) * hermiteOne n := by
    intro n
    first | rfl | rw [hermiteOne] | simp only [hermiteOne]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · -- k = 2m + 0
    obtain ⟨Q, hQ⟩ : ∃ Q : ℚ, Q = ((2 : ℚ) ^ m)⁻¹ := ⟨_, rfl⟩
    have ha0 : a (2 * m + 5) = (hermiteOne (2 * m + 5) : ℚ) * Q / 4 := by
      unfold a
      rw [show (2 * m + 5) / 2 = m + 2 by omega, hQ, pow_add]
      first | ring | (field_simp) | (field_simp; ring)
    have ha1 : a (2 * m + 5 - 1) = (hermiteOne (2 * m + 4) : ℚ) * Q / 4 := by
      rw [show 2 * m + 5 - 1 = 2 * m + 4 by omega]
      unfold a
      rw [show (2 * m + 4) / 2 = m + 2 by omega, hQ, pow_add]
      first | ring | (field_simp) | (field_simp; ring)
    have ha2 : a (2 * m + 5 - 2) = (hermiteOne (2 * m + 3) : ℚ) * Q / 2 := by
      rw [show 2 * m + 5 - 2 = 2 * m + 3 by omega]
      unfold a
      rw [show (2 * m + 3) / 2 = m + 1 by omega, hQ, pow_add]
      first | ring | (field_simp) | (field_simp; ring)
    have ha3 : a (2 * m + 5 - 3) = (hermiteOne (2 * m + 2) : ℚ) * Q / 2 := by
      rw [show 2 * m + 5 - 3 = 2 * m + 2 by omega]
      unfold a
      rw [show (2 * m + 2) / 2 = m + 1 by omega, hQ, pow_add]
      first | ring | (field_simp) | (field_simp; ring)
    have ha4 : a (2 * m + 5 - 4) = (hermiteOne (2 * m + 1) : ℚ) * Q / 1 := by
      rw [show 2 * m + 5 - 4 = 2 * m + 1 by omega]
      unfold a
      rw [show (2 * m + 1) / 2 = m by omega, hQ]
      first | ring | (field_simp) | (field_simp; ring)
    have ha5 : a (2 * m + 5 - 5) = (hermiteOne (2 * m) : ℚ) * Q / 1 := by
      rw [show 2 * m + 5 - 5 = 2 * m by omega]
      unfold a
      rw [show (2 * m) / 2 = m by omega, hQ]
      first | ring | (field_simp) | (field_simp; ring)
    have r0 : hermiteOne (2 * m + 2) = 2 * hermiteOne (2 * m + 1) - 2 * (((2 * m : ℕ) : ℤ) + 1) * hermiteOne (2 * m) := hr (2 * m)
    have r1 : hermiteOne (2 * m + 3) = 2 * hermiteOne (2 * m + 2) - 2 * (((2 * m + 1 : ℕ) : ℤ) + 1) * hermiteOne (2 * m + 1) := hr (2 * m + 1)
    have r2 : hermiteOne (2 * m + 4) = 2 * hermiteOne (2 * m + 3) - 2 * (((2 * m + 2 : ℕ) : ℤ) + 1) * hermiteOne (2 * m + 2) := hr (2 * m + 2)
    have r3 : hermiteOne (2 * m + 5) = 2 * hermiteOne (2 * m + 4) - 2 * (((2 * m + 3 : ℕ) : ℤ) + 1) * hermiteOne (2 * m + 3) := hr (2 * m + 3)
    have r0' := congrArg (Int.cast : ℤ → ℚ) r0
    have r1' := congrArg (Int.cast : ℤ → ℚ) r1
    have r2' := congrArg (Int.cast : ℤ → ℚ) r2
    have r3' := congrArg (Int.cast : ℤ → ℚ) r3
    push_cast at r0' r1' r2' r3'
    rw [ha0, ha1, ha2, ha3, ha4, ha5]
    push_cast
    linear_combination (1) / 4 * Q * r3' + (3) / 4 * Q * r2' + ((m : ℚ) + 2) / 1 * Q * r1' + ((m : ℚ) + 1) / 1 * Q * r0'
  · -- k = 2m + 1
    obtain ⟨Q, hQ⟩ : ∃ Q : ℚ, Q = ((2 : ℚ) ^ m)⁻¹ := ⟨_, rfl⟩
    have ha0 : a (2 * m + 1 + 5) = (hermiteOne (2 * m + 6) : ℚ) * Q / 8 := by
      rw [show 2 * m + 1 + 5 = 2 * m + 6 by omega]
      unfold a
      rw [show (2 * m + 6) / 2 = m + 3 by omega, hQ, pow_add]
      first | ring | (field_simp) | (field_simp; ring)
    have ha1 : a (2 * m + 1 + 5 - 1) = (hermiteOne (2 * m + 5) : ℚ) * Q / 4 := by
      rw [show 2 * m + 1 + 5 - 1 = 2 * m + 5 by omega]
      unfold a
      rw [show (2 * m + 5) / 2 = m + 2 by omega, hQ, pow_add]
      first | ring | (field_simp) | (field_simp; ring)
    have ha2 : a (2 * m + 1 + 5 - 2) = (hermiteOne (2 * m + 4) : ℚ) * Q / 4 := by
      rw [show 2 * m + 1 + 5 - 2 = 2 * m + 4 by omega]
      unfold a
      rw [show (2 * m + 4) / 2 = m + 2 by omega, hQ, pow_add]
      first | ring | (field_simp) | (field_simp; ring)
    have ha3 : a (2 * m + 1 + 5 - 3) = (hermiteOne (2 * m + 3) : ℚ) * Q / 2 := by
      rw [show 2 * m + 1 + 5 - 3 = 2 * m + 3 by omega]
      unfold a
      rw [show (2 * m + 3) / 2 = m + 1 by omega, hQ, pow_add]
      first | ring | (field_simp) | (field_simp; ring)
    have ha4 : a (2 * m + 1 + 5 - 4) = (hermiteOne (2 * m + 2) : ℚ) * Q / 2 := by
      rw [show 2 * m + 1 + 5 - 4 = 2 * m + 2 by omega]
      unfold a
      rw [show (2 * m + 2) / 2 = m + 1 by omega, hQ, pow_add]
      first | ring | (field_simp) | (field_simp; ring)
    have ha5 : a (2 * m + 1 + 5 - 5) = (hermiteOne (2 * m + 1) : ℚ) * Q / 1 := by
      rw [show 2 * m + 1 + 5 - 5 = 2 * m + 1 by omega]
      unfold a
      rw [show (2 * m + 1) / 2 = m by omega, hQ]
      first | ring | (field_simp) | (field_simp; ring)
    have r0 : hermiteOne (2 * m + 3) = 2 * hermiteOne (2 * m + 2) - 2 * (((2 * m + 1 : ℕ) : ℤ) + 1) * hermiteOne (2 * m + 1) := hr (2 * m + 1)
    have r1 : hermiteOne (2 * m + 4) = 2 * hermiteOne (2 * m + 3) - 2 * (((2 * m + 2 : ℕ) : ℤ) + 1) * hermiteOne (2 * m + 2) := hr (2 * m + 2)
    have r2 : hermiteOne (2 * m + 5) = 2 * hermiteOne (2 * m + 4) - 2 * (((2 * m + 3 : ℕ) : ℤ) + 1) * hermiteOne (2 * m + 3) := hr (2 * m + 3)
    have r3 : hermiteOne (2 * m + 6) = 2 * hermiteOne (2 * m + 5) - 2 * (((2 * m + 4 : ℕ) : ℤ) + 1) * hermiteOne (2 * m + 4) := hr (2 * m + 4)
    have r0' := congrArg (Int.cast : ℤ → ℚ) r0
    have r1' := congrArg (Int.cast : ℤ → ℚ) r1
    have r2' := congrArg (Int.cast : ℤ → ℚ) r2
    have r3' := congrArg (Int.cast : ℤ → ℚ) r3
    push_cast at r0' r1' r2' r3'
    rw [ha0, ha1, ha2, ha3, ha4, ha5]
    push_cast
    linear_combination (1) / 8 * Q * r3' + (1) / 2 * Q * r2' + ((m : ℚ) + 3) / 2 * Q * r1' + (2*(m : ℚ) + 3) / 2 * Q * r0'
