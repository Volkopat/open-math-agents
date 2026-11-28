import OMAStatements.S_oeis_a192473

namespace OMA.P192473

open Polynomial OMA.S_oeis_a192473

/-- Coordinates of the reduction of `x^n` in the basis `1, x`. -/
def w : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((w n).2, (w n).1 + (w n).2)

lemma red (n : ℕ) : ∃ s : ℤ[X],
    (X : ℤ[X]) ^ n = (X ^ 2 - X - 1) * s + (C (w n).2 * X + C (w n).1) := by
  induction n with
  | zero => exact ⟨0, by simp [w]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨s * X + C (w n).2, ?_⟩
    rw [pow_succ, hs]
    simp only [w, map_add]
    ring

lemma q_monic : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have e : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + C 1) := by simp; ring
  rw [e]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  norm_num

lemma q_degree : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by
  have e : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + C 1) := by simp; ring
  rw [e, degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow] <;> try rfl
  rw [degree_X_add_C]
  norm_num

lemma rem (n : ℕ) : p n %ₘ (X ^ 2 - X - 1)
    = C ((w n).2 + (w (2 * n + 2)).2) * X + C (1 + (w n).1 + (w (2 * n + 2)).1) := by
  obtain ⟨s1, h1⟩ := red n
  obtain ⟨s2, h2⟩ := red (2 * n + 2)
  refine (div_modByMonic_unique (s1 + s2) _ q_monic ⟨?_, ?_⟩).2
  · unfold p
    rw [h1, h2]
    simp only [map_add, map_one]
    ring
  · rw [q_degree]
    exact lt_of_le_of_lt (degree_linear_le) (by norm_num)

lemma a_eq (n : ℕ) : a n = (w n).2 + (w (2 * n + 2)).2 := by
  unfold a
  rw [rem, coeff_add, coeff_C_mul, coeff_X_one, coeff_C_of_ne_zero one_ne_zero, mul_one, add_zero]

lemma fibrec (m : ℕ) : (w (m + 2)).2 = (w (m + 1)).2 + (w m).2 := by
  simp only [w]; ring

end OMA.P192473

open OMA.S_oeis_a192473 OMA.P192473 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192473.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have e1 : k + 5 - 1 = k + 4 := by omega
  have e2 : k + 5 - 2 = k + 3 := by omega
  have e3 : k + 5 - 3 = k + 2 := by omega
  have e4 : k + 5 - 4 = k + 1 := by omega
  rw [e1, e2, e3, e4]
  simp only [a_eq]
  have i5 : 2 * (k + 5) + 2 = 2 * k + 12 := by ring
  have i4 : 2 * (k + 4) + 2 = 2 * k + 10 := by ring
  have i3 : 2 * (k + 3) + 2 = 2 * k + 8 := by ring
  have i2 : 2 * (k + 2) + 2 = 2 * k + 6 := by ring
  have i1 : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
  rw [i5, i4, i3, i2, i1]
  have f1 := fibrec (k + 3)
  have f2 := fibrec (k + 2)
  have f3 := fibrec (k + 1)
  have g4 := fibrec (2 * k + 4)
  have g5 := fibrec (2 * k + 5)
  have g6 := fibrec (2 * k + 6)
  have g7 := fibrec (2 * k + 7)
  have g8 := fibrec (2 * k + 8)
  have g9 := fibrec (2 * k + 9)
  have g10 := fibrec (2 * k + 10)
  linarith
