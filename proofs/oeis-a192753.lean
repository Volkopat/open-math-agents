import OMAStatements.S_oeis_a192753

namespace OMA.P192753

open Polynomial OMA.S_oeis_a192753

/-- Coordinates of the reduction of `p n` in the basis `1, x`. -/
def w : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((w n).2 + (4 * ((n : ℤ) + 1) + 3), (w n).1 + (w n).2)

lemma red (n : ℕ) : ∃ s : ℤ[X],
    p n = (X ^ 2 - X - 1) * s + (C (w n).2 * X + C (w n).1) := by
  induction n with
  | zero => exact ⟨0, by simp [w, p]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨X * s + C (w n).2, ?_⟩
    rw [p, hs]
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

lemma rem (n : ℕ) : p n %ₘ (X ^ 2 - X - 1) = C (w n).2 * X + C (w n).1 := by
  obtain ⟨s, hs⟩ := red n
  refine (div_modByMonic_unique s _ q_monic ⟨?_, ?_⟩).2
  · rw [hs]; ring
  · rw [q_degree]
    exact lt_of_le_of_lt (degree_linear_le) (by norm_num)

lemma a_eq (n : ℕ) : a n = (w n).2 := by
  unfold a
  rw [rem, coeff_add, coeff_C_mul, coeff_X_one, coeff_C_of_ne_zero one_ne_zero, mul_one, add_zero]

lemma vrec (m : ℕ) : (w (m + 2)).2 = (w (m + 1)).2 + (w m).2 + (4 * ((m : ℤ) + 1) + 3) := by
  simp only [w]
  ring

lemma arec (k : ℕ) : a (k + 4) = 3 * a (k + 3) - 2 * a (k + 2) - a (k + 1) + a k := by
  simp only [a_eq]
  have h2 := vrec (k + 2)
  have h1 := vrec (k + 1)
  have h0 := vrec k
  push_cast at h2 h1 h0
  linarith

lemma a0 : a 0 = 0 := by rw [a_eq]; simp [w]
lemma a1 : a 1 = 1 := by rw [a_eq]; simp [w]
lemma a2 : a 2 = 8 := by rw [a_eq]; simp [w]
lemma a3 : a 3 = 20 := by rw [a_eq]; simp [w]

end OMA.P192753

open OMA.S_oeis_a192753 OMA.P192753 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a192753.main := by
  have hD : ∀ f : ℤ⟦X⟧, f * ((X ^ 2 + X - 1) * (X - 1) ^ 2)
      = f * X ^ 4 - f * X ^ 3 - (f * X ^ 2 + f * X ^ 2) + (f * X + f * X + f * X) - f := by
    intro f; ring
  have hN : ((X : ℤ⟦X⟧) * (-1 - 5 * X + 2 * X ^ 2)) = -(X : ℤ⟦X⟧) - (X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2) + (X ^ 3 + X ^ 3) := by ring
  show PowerSeries.mk a * ((X ^ 2 + X - 1) * (X - 1) ^ 2) = (X : ℤ⟦X⟧) * (-1 - 5 * X + 2 * X ^ 2)
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, map_neg, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  have hx : ∀ f : ℤ⟦X⟧, PowerSeries.coeff n (f * X) = if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
    intro f
    have := PowerSeries.coeff_mul_X_pow' (p := f) (n := 1) (d := n)
    simpa using this
  simp only [hx, PowerSeries.coeff_mk]
  rcases n with _ | _ | _ | _ | k
  · simp [a0]
  · simp [a0, a1]
  · simp [a0, a1, a2]
  · simp [a0, a1, a2, a3]
  · have h := arec k
    have e4 : k + 1 + 1 + 1 + 1 = k + 4 := rfl
    simp only [e4]
    have c4 : 4 ≤ k + 4 := by omega
    have c3 : 3 ≤ k + 4 := by omega
    have c2 : 2 ≤ k + 4 := by omega
    have c1 : 1 ≤ k + 4 := by omega
    have n1 : ¬ (k + 4 = 1) := by omega
    have n2 : ¬ (k + 4 = 2) := by omega
    have n3 : ¬ (k + 4 = 3) := by omega
    have s4 : k + 4 - 4 = k := by omega
    have s3 : k + 4 - 3 = k + 1 := by omega
    have s2 : k + 4 - 2 = k + 2 := by omega
    have s1 : k + 4 - 1 = k + 3 := by omega
    simp only [c4, c3, c2, c1, n1, n2, n3, s4, s3, s2, s1, if_true, if_false]
    linarith
