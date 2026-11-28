import OMAStatements.S_oeis_a094047
import Mathlib

namespace OMA.S_oeis_a094047
end OMA.S_oeis_a094047

theorem OMA.solution : type_of% @OMA.S_oeis_a094047.main := by
  intro a _ _ _ h n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have h4 := h (k + 6) (by omega)
  have h3 := h (k + 5) (by omega)
  have h2 := h (k + 4) (by omega)
  have e1 : k + 6 - 1 = k + 5 := by omega
  have e2 : k + 6 - 2 = k + 4 := by omega
  have e3 : k + 6 - 3 = k + 3 := by omega
  have e4 : k + 6 - 4 = k + 2 := by omega
  have e5 : k + 5 - 1 = k + 4 := by omega
  have e6 : k + 5 - 2 = k + 3 := by omega
  have e7 : k + 5 - 3 = k + 2 := by omega
  have e8 : k + 4 - 1 = k + 3 := by omega
  have e9 : k + 4 - 2 = k + 2 := by omega
  have e10 : k + 4 - 3 = k + 1 := by omega
  rw [e1, e2, e3] at h4
  rw [e5, e6, e7] at h3
  rw [e8, e9, e10] at h2
  rw [e1, e2, e3, e4]
  have f2 : (((k + 2).factorial : ℕ) : ℚ) = ((k : ℚ) + 2) * ((k + 1).factorial : ℕ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f3 : (((k + 3).factorial : ℕ) : ℚ) = ((k : ℚ) + 3) * ((k + 2).factorial : ℕ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have p6 : (-1 : ℚ) ^ (k + 6) = (-1) ^ k := by rw [pow_add]; norm_num
  have p5 : (-1 : ℚ) ^ (k + 5) = -(-1) ^ k := by rw [pow_add]; norm_num
  have p4 : (-1 : ℚ) ^ (k + 4) = (-1) ^ k := by rw [pow_add]; norm_num
  rw [p6, f3, f2] at h4
  rw [p5, f2] at h3
  rw [p4] at h2
  push_cast at h4 h3 h2 ⊢
  linear_combination h4 + ((k : ℚ) + 3) * h3 + (-2 - (k : ℚ)) * h2
