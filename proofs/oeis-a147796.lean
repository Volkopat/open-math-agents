import OMAStatements.S_oeis_a147796

-- Problem: A147796: Number of consistent sets of 3 irreflexive binary order relationships over n objects.
-- Upstream: formal-conjectures statements/oeis-a147796.lean:0 (declaration OMA.S_oeis_a147796.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Since 6 binomial(n,3) = n (n-1) (n-2), the closed form is a polynomial of degree 6 in n, so its
seventh differences vanish; this is (2). For (1), the coefficient of x^n in
(Sum a(k) x^k) (1 - x)^7 is the seventh difference of a at n (with a(k) = 0 for k < 0), which is
6, 110, 2, 2 for n = 3, 4, 5, 6 and 0 otherwise. -/

namespace A147796Aux

open OMA.S_oeis_a147796 PowerSeries

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

theorem rec7 (m : ℕ) : a (m + 7) = 7 * a (m + 6) - 21 * a (m + 5) + 35 * a (m + 4) - 35 * a (m + 3) +
    21 * a (m + 2) - 7 * a (m + 1) + a m := by
  have key : 6 * (a (m + 7) - (7 * a (m + 6) - 21 * a (m + 5) + 35 * a (m + 4) - 35 * a (m + 3) +
      21 * a (m + 2) - 7 * a (m + 1) + a m)) = 0 := by
    simp only [a]
    have h7 := c3 (m + 7)
    have h6 := c3 (m + 6)
    have h5 := c3 (m + 5)
    have h4 := c3 (m + 4)
    have h3 := c3 (m + 3)
    have h2 := c3 (m + 2)
    have h1 := c3 (m + 1)
    have h0 := c3 (m)
    push_cast at h7 h6 h5 h4 h3 h2 h1 h0 ⊢
    linear_combination (1) * (((m : ℤ) + 7) ^ 3 - 5 * ((m : ℤ) + 7) - 6) * h7 +
      (-7) * (((m : ℤ) + 6) ^ 3 - 5 * ((m : ℤ) + 6) - 6) * h6 +
      (21) * (((m : ℤ) + 5) ^ 3 - 5 * ((m : ℤ) + 5) - 6) * h5 +
      (-35) * (((m : ℤ) + 4) ^ 3 - 5 * ((m : ℤ) + 4) - 6) * h4 +
      (35) * (((m : ℤ) + 3) ^ 3 - 5 * ((m : ℤ) + 3) - 6) * h3 +
      (-21) * (((m : ℤ) + 2) ^ 3 - 5 * ((m : ℤ) + 2) - 6) * h2 +
      (7) * (((m : ℤ) + 1) ^ 3 - 5 * ((m : ℤ) + 1) - 6) * h1 +
      (-1) * ((m : ℤ) ^ 3 - 5 * (m : ℤ) - 6) * h0
  linarith

theorem a0 : a 0 = 0 := by norm_num [a, Nat.choose]
theorem a1 : a 1 = 0 := by norm_num [a, Nat.choose]
theorem a2 : a 2 = 0 := by norm_num [a, Nat.choose]
theorem a3 : a 3 = 6 := by norm_num [a, Nat.choose]
theorem a4 : a 4 = 152 := by norm_num [a, Nat.choose]
theorem a5 : a 5 = 940 := by norm_num [a, Nat.choose]
theorem a6 : a 6 = 3600 := by norm_num [a, Nat.choose]

theorem gfC : PowerSeries.mk (fun n => (a n : ℚ)) * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * C (-7) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * C 21 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * C (-35) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * C 35 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * C (-21) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * C 7 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * X * C (-1) =
    (1 : ℚ⟦X⟧) * X * X * X * C 6 + (1 : ℚ⟦X⟧) * X * X * X * X * C 110 + (1 : ℚ⟦X⟧) * X * X * X * X * X * C 2 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * C 2 := by
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
            norm_num
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
                simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
                have h := rec7 n
                have hq : ((a (n + 7) : ℤ) : ℚ) = 7 * ((a (n + 6) : ℤ) : ℚ) - 21 * ((a (n + 5) : ℤ) : ℚ) + 35 * ((a (n + 4) : ℤ) : ℚ) -
                    35 * ((a (n + 3) : ℤ) : ℚ) + 21 * ((a (n + 2) : ℤ) : ℚ) - 7 * ((a (n + 1) : ℤ) : ℚ) + ((a n : ℤ) : ℚ) := by
                  exact_mod_cast h
                simp [PowerSeries.coeff_one]
                linear_combination hq

end A147796Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a147796.main := by
  refine ⟨?_, ?_⟩
  · have h := A147796Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    exact A147796Aux.rec7 m
