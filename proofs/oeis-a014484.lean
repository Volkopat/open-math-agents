import OMAStatements.S_oeis_a014484
import Mathlib

open OMA.S_oeis_a014484 in
theorem OMA.solution : type_of% @OMA.S_oeis_a014484.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h (j : ℕ) : (a j : ℤ) * 6 = (j+2).factorial * (2*j+3) * 2^j := by
    rcases j with _ | j
    · simp [a]
    · exact mod_cast Nat.div_mul_cancel
        (((Nat.factorial_dvd_factorial (by omega : 3 ≤ j+1+2)).mul_right _).mul_right _)
  have h2 := h (k+2)
  have h1 := h (k+1)
  have h0 := h k
  simp [Nat.factorial_succ, pow_succ, add_assoc] at h0 h1 h2 ⊢
  exact mul_right_cancel₀ (by norm_num : (6:ℤ) ≠ 0) (by
    linear_combination h2 + (-2*((k:ℤ)+2)-9)*h1 + 6*((k:ℤ)+3)*h0)
