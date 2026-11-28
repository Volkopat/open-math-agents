import OMAStatements.S_oeis_a007901

namespace OMA.S_oeis_a007901

private theorem s_rec (k : ℕ) :
    ((k : ℤ) + 2) * s (k + 2) = 2 * (2 * (k : ℤ) + 1) * s (k + 1) := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [← succ_mul_catalan_eq_centralBinom (k + 1),
    ← succ_mul_catalan_eq_centralBinom k] at h
  have hmul : (k + 1) * ((k + 2) * catalan (k + 1)) =
      (k + 1) * (2 * (2 * k + 1) * catalan k) := by
    calc
      _ = (k + 1) * ((k + 1 + 1) * catalan (k + 1)) := rfl
      _ = 2 * (2 * k + 1) * ((k + 1) * catalan k) := h
      _ = _ := by ring
  have hc := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) hmul
  have hz : ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) =
      2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by exact_mod_cast hc
  simp only [s, if_neg (by omega : k + 2 ≠ 0), if_neg (by omega : k + 1 ≠ 0),
    show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel]
  linear_combination -2 * hz

private theorem e_of_large (m : ℕ) (hm : 4 ≤ m) :
    e m = s m - 3 * s (m - 1) + s (m - 2) := by
  simp [e, show 1 ≤ m by omega, show 2 ≤ m by omega,
    show m ≠ 0 by omega, show m ≠ 1 by omega, show m ≠ 2 by omega, show m ≠ 3 by omega]

private theorem e_rec (k : ℕ) :
    ((k : ℤ) + 5) * (k : ℤ) * e (k + 5) =
      2 * ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) * e (k + 4) := by
  have h₁ := s_rec (k + 3)
  have h₂ := s_rec (k + 2)
  have h₃ := s_rec (k + 1)
  push_cast at h₁ h₂ h₃
  rw [e_of_large (k + 5) (by omega), e_of_large (k + 4) (by omega)]
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega]
  linear_combination (k : ℤ) * h₁ - 3 * ((k : ℤ) + 1) * h₂ + ((k : ℤ) + 2) * h₃

private theorem a_step (k : ℕ) :
    a (k + 4) = e (k + 1) + 7 * a (k + 3) - 14 * a (k + 2) + 9 * a (k + 1) := by
  rw [a]

end OMA.S_oeis_a007901

open OMA.S_oeis_a007901 in
theorem OMA.solution : type_of% @OMA.S_oeis_a007901.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 8 := ⟨n - 8, by omega⟩
  have h₁ := a_step (k + 4)
  have h₂ := a_step (k + 3)
  simp only [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega,
    show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega]
  push_cast
  linear_combination ((k : ℤ) + 5) * (k : ℤ) * h₁ -
    2 * ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) * h₂ + e_rec k
