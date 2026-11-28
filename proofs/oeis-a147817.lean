import OMAStatements.S_oeis_a147817

-- Problem: A147817: Number of consistent sets of 4 irreflexive binary order relationships over n objects.
-- Upstream: formal-conjectures statements/oeis-a147817.lean:0 (declaration OMA.S_oeis_a147817.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The closed form is a polynomial of degree 8 in n, so its differences of order 9 vanish; this is
(2). For (1), the coefficient of x^n in (Sum a(k) x^k) (1 - x)^9 is the difference of order 9 of a at
n (with a(k) = 0 for k < 0), which is the corresponding coefficient of the numerator for n < 9 and 0
otherwise. -/

namespace A147817Aux

open OMA.S_oeis_a147817 PowerSeries

theorem c2 (n : ℕ) : 2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem c3 (n : ℕ) : 6 * (n.choose 3 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ']
    push_cast
    linear_combination ih + 3 * c2 k

theorem c4 (n : ℕ) : 24 * (n.choose 4 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ']
    push_cast
    linear_combination ih + 4 * c3 k

theorem rec (m : ℕ) : a (m + 9) = 9 * a (m + 8) - 36 * a (m + 7) + 84 * a (m + 6) - 126 * a (m + 5) + 126 * a (m + 4) - 84 * a (m + 3) + 36 * a (m + 2) - 9 * a (m + 1) + a (m) := by
  have key : 24 * (a (m + 9) - (9 * a (m + 8) - 36 * a (m + 7) + 84 * a (m + 6) - 126 * a (m + 5) + 126 * a (m + 4) - 84 * a (m + 3) + 36 * a (m + 2) - 9 * a (m + 1) + a (m))) = 0 := by
    simp only [a]
    have h9 := c4 (m + 9)
    have h8 := c4 (m + 8)
    have h7 := c4 (m + 7)
    have h6 := c4 (m + 6)
    have h5 := c4 (m + 5)
    have h4 := c4 (m + 4)
    have h3 := c4 (m + 3)
    have h2 := c4 (m + 2)
    have h1 := c4 (m + 1)
    have h0 := c4 (m)
    push_cast at h9 h8 h7 h6 h5 h4 h3 h2 h1 h0 ⊢
    linear_combination (1) * (((m : ℤ) + 9) ^ 4 + 2 * ((m : ℤ) + 9) ^ 3 - 5 * ((m : ℤ) + 9) ^ 2 - 22 * ((m : ℤ) + 9) - 30) * h9 +
      (-9) * (((m : ℤ) + 8) ^ 4 + 2 * ((m : ℤ) + 8) ^ 3 - 5 * ((m : ℤ) + 8) ^ 2 - 22 * ((m : ℤ) + 8) - 30) * h8 +
      (36) * (((m : ℤ) + 7) ^ 4 + 2 * ((m : ℤ) + 7) ^ 3 - 5 * ((m : ℤ) + 7) ^ 2 - 22 * ((m : ℤ) + 7) - 30) * h7 +
      (-84) * (((m : ℤ) + 6) ^ 4 + 2 * ((m : ℤ) + 6) ^ 3 - 5 * ((m : ℤ) + 6) ^ 2 - 22 * ((m : ℤ) + 6) - 30) * h6 +
      (126) * (((m : ℤ) + 5) ^ 4 + 2 * ((m : ℤ) + 5) ^ 3 - 5 * ((m : ℤ) + 5) ^ 2 - 22 * ((m : ℤ) + 5) - 30) * h5 +
      (-126) * (((m : ℤ) + 4) ^ 4 + 2 * ((m : ℤ) + 4) ^ 3 - 5 * ((m : ℤ) + 4) ^ 2 - 22 * ((m : ℤ) + 4) - 30) * h4 +
      (84) * (((m : ℤ) + 3) ^ 4 + 2 * ((m : ℤ) + 3) ^ 3 - 5 * ((m : ℤ) + 3) ^ 2 - 22 * ((m : ℤ) + 3) - 30) * h3 +
      (-36) * (((m : ℤ) + 2) ^ 4 + 2 * ((m : ℤ) + 2) ^ 3 - 5 * ((m : ℤ) + 2) ^ 2 - 22 * ((m : ℤ) + 2) - 30) * h2 +
      (9) * (((m : ℤ) + 1) ^ 4 + 2 * ((m : ℤ) + 1) ^ 3 - 5 * ((m : ℤ) + 1) ^ 2 - 22 * ((m : ℤ) + 1) - 30) * h1 +
      (-1) * ((m : ℤ) ^ 4 + 2 * (m : ℤ) ^ 3 - 5 * (m : ℤ) ^ 2 - 22 * (m : ℤ) - 30) * h0
  linarith

theorem a0 : a 0 = 0 := by norm_num [a, Nat.choose]
theorem a1 : a 1 = 0 := by norm_num [a, Nat.choose]
theorem a2 : a 2 = 0 := by norm_num [a, Nat.choose]
theorem a3 : a 3 = 0 := by norm_num [a, Nat.choose]
theorem a4 : a 4 = 186 := by norm_num [a, Nat.choose]
theorem a5 : a 5 = 3050 := by norm_num [a, Nat.choose]
theorem a6 : a 6 = 20790 := by norm_num [a, Nat.choose]
theorem a7 : a 7 = 93030 := by norm_num [a, Nat.choose]
theorem a8 : a 8 = 321580 := by norm_num [a, Nat.choose]

theorem gfC : PowerSeries.mk (fun n => (a n : ℚ)) * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * C (-9) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * C 36 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * C (-84) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * C 126 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * C (-126) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * C 84 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * X * C (-36) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * X * X * C 9 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * X * X * X * C (-1) =
    (1 : ℚ⟦X⟧) * X * X * X * X * C 186 + (1 : ℚ⟦X⟧) * X * X * X * X * X * C 1376 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * C 36 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * X * C 96 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * X * X * C (-14) := by
  ext n
  cases n with
  | zero =>
    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
    simp [a0]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
      simp [a0, a1]
    | succ n =>
      cases n with
      | zero =>
        simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
        simp [a0, a1, a2]
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
          simp [a0, a1, a2, a3]
        | succ n =>
          cases n with
          | zero =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
            simp [a0, a1, a2, a3, a4]
          | succ n =>
            cases n with
            | zero =>
              simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
              simp [a0, a1, a2, a3, a4, a5]
              norm_num
            | succ n =>
              cases n with
              | zero =>
                simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                simp [a0, a1, a2, a3, a4, a5, a6]
                norm_num
              | succ n =>
                cases n with
                | zero =>
                  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                  simp [a0, a1, a2, a3, a4, a5, a6, a7]
                  norm_num
                | succ n =>
                  cases n with
                  | zero =>
                    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                    simp [a0, a1, a2, a3, a4, a5, a6, a7, a8]
                    norm_num
                  | succ n =>
                    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
                    have h := rec n
                    have hq : ((a (n + 9) : ℤ) : ℚ) = 9 * ((a (n + 8) : ℤ) : ℚ) - 36 * ((a (n + 7) : ℤ) : ℚ) + 84 * ((a (n + 6) : ℤ) : ℚ) - 126 * ((a (n + 5) : ℤ) : ℚ) + 126 * ((a (n + 4) : ℤ) : ℚ) - 84 * ((a (n + 3) : ℤ) : ℚ) + 36 * ((a (n + 2) : ℤ) : ℚ) - 9 * ((a (n + 1) : ℤ) : ℚ) + ((a (n) : ℤ) : ℚ) := by
                      exact_mod_cast h
                    simp [PowerSeries.coeff_one]
                    linear_combination hq

end A147817Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a147817.main := by
  refine ⟨?_, ?_⟩
  · have h := A147817Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    exact A147817Aux.rec m
