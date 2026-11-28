import OMAStatements.S_oeis_a192758

namespace OMA.P192758

open Polynomial OMA.S_oeis_a192758

/-- Coordinates of the reduction of `p n` in the basis `1, x`. -/
def w : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((w n).2 + (((n + 1 + 4) / 4 : ℕ) : ℤ), (w n).1 + (w n).2)

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

lemma b_eq (n : ℕ) : b n = (w n).2 := by
  unfold b
  rw [rem, coeff_add, coeff_C_mul, coeff_X_one, coeff_C_of_ne_zero one_ne_zero, mul_one, add_zero]

lemma vrec (m : ℕ) :
    (w (m + 2)).2 = (w (m + 1)).2 + (w m).2 + (((m + 1 + 4) / 4 : ℕ) : ℤ) := by
  simp only [w]
  ring

lemma brec (k : ℕ) :
    b (k + 7) = 2 * b (k + 6) - b (k + 4) + b (k + 3) - 2 * b (k + 2) + b k := by
  simp only [b_eq]
  have h5 := vrec (k + 5)
  have h4 := vrec (k + 4)
  have h1 := vrec (k + 1)
  have h0 := vrec k
  have hc : (((k + 5 + 1 + 4) / 4 : ℕ) : ℤ) + (((k + 1 + 4) / 4 : ℕ) : ℤ)
      = (((k + 4 + 1 + 4) / 4 : ℕ) : ℤ) + (((k + 1 + 1 + 4) / 4 : ℕ) : ℤ) := by
    have : (k + 5 + 1 + 4) / 4 + (k + 1 + 4) / 4 = (k + 4 + 1 + 4) / 4 + (k + 1 + 1 + 4) / 4 := by
      omega
    exact_mod_cast this
  linarith

lemma b0 : b 0 = 0 := by rw [b_eq]; simp [w]
lemma b1 : b 1 = 1 := by rw [b_eq]; simp [w]
lemma b2 : b 2 = 2 := by rw [b_eq]; simp [w]
lemma b3 : b 3 = 4 := by rw [b_eq]; simp [w]
lemma b4 : b 4 = 7 := by rw [b_eq]; simp [w]
lemma b5 : b 5 = 13 := by rw [b_eq]; simp [w]
lemma b6 : b 6 = 22 := by rw [b_eq]; simp [w]

end OMA.P192758

open OMA.S_oeis_a192758 OMA.P192758 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a192758.main := by
  have hD : ∀ f : ℤ⟦X⟧, f * ((1 + X) * (X ^ 2 + 1) * (X ^ 2 + X - 1) * (X - 1) ^ 2)
      = f * X ^ 7 - (f * X ^ 5 + f * X ^ 5) + f * X ^ 4 - f * X ^ 3 + (f * X + f * X) - f := by
    intro f; ring
  have core : PowerSeries.mk b * ((1 + X) * (X ^ 2 + 1) * (X ^ 2 + X - 1) * (X - 1) ^ 2)
      = -(X : ℤ⟦X⟧) := by
    rw [hD]
    ext n
    have hx : ∀ f : ℤ⟦X⟧,
        PowerSeries.coeff n (f * X) = if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
      intro f
      have := PowerSeries.coeff_mul_X_pow' (p := f) (n := 1) (d := n)
      simpa using this
    simp only [map_sub, map_add, map_neg, PowerSeries.coeff_mul_X_pow', hx, PowerSeries.coeff_mk,
      PowerSeries.coeff_X]
    rcases n with _ | _ | _ | _ | _ | _ | _ | k
    · simp [b0]
    · simp [b0, b1]
    · simp [b0, b1, b2]
    · simp [b0, b1, b2, b3]
    · simp [b0, b1, b2, b3, b4]
    · simp [b0, b1, b2, b3, b4, b5]
    · simp [b0, b1, b2, b3, b4, b5, b6]
    · have h := brec k
      have e7 : k + 1 + 1 + 1 + 1 + 1 + 1 + 1 = k + 7 := rfl
      simp only [e7]
      have c7 : 7 ≤ k + 7 := by omega
      have c5 : 5 ≤ k + 7 := by omega
      have c4 : 4 ≤ k + 7 := by omega
      have c3 : 3 ≤ k + 7 := by omega
      have c1 : 1 ≤ k + 7 := by omega
      have n1 : ¬ (k + 7 = 1) := by omega
      have s7 : k + 7 - 7 = k := by omega
      have s5 : k + 7 - 5 = k + 2 := by omega
      have s4 : k + 7 - 4 = k + 3 := by omega
      have s3 : k + 7 - 3 = k + 4 := by omega
      have s1 : k + 7 - 1 = k + 6 := by omega
      simp only [c7, c5, c4, c3, c1, n1, s7, s5, s4, s3, s1, if_true, if_false]
      linarith
  show (X * PowerSeries.mk b) * ((1 + X) * (X ^ 2 + 1) * (X ^ 2 + X - 1) * (X - 1) ^ 2)
    = -(X : ℤ⟦X⟧) ^ 2
  rw [mul_assoc, core]
  ring
