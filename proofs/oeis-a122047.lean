import OMAStatements.S_oeis_a122047

-- Problem: A122047: Degree of the polynomial P(n,x), defined by a Somos-6 type sequence.
-- Upstream: formal-conjectures statements/oeis-a122047.lean:0 (declaration OMA.S_oeis_a122047.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! With f(n) = n^3 + 6n^2 + 5n one has f(n+5) = f(n) + 30 binomial(n+5, 2), hence
a(n+5) = a(n) + binomial(n+5, 2). The recurrence says that the third difference of a(n) - a(n-5)
vanishes, which holds because binomial(n, 2) is quadratic. The denominator of the g.f. is
(1 - x)^3 (1 - x^5), so the coefficient of x^n in the product is the left side minus the right side
of the recurrence, which is 1 for n = 2 and 0 otherwise. -/

namespace A122047Aux

open OMA.S_oeis_a122047 PowerSeries

theorem c2 (n : ℕ) : 2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem step (n : ℕ) : a (n + 5) = a n + ((n + 5).choose 2 : ℤ) := by
  unfold a
  have h := c2 (n + 5)
  have e : ((n + 5 : ℕ) : ℤ) ^ 3 + 6 * ((n + 5 : ℕ) : ℤ) ^ 2 + 5 * ((n + 5 : ℕ) : ℤ) =
      ((n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 5 * (n : ℤ)) + 30 * ((n + 5).choose 2 : ℤ) := by
    push_cast at h ⊢
    linear_combination (-15) * h
  rw [e, Int.add_mul_ediv_left _ _ (by norm_num)]

theorem rec8 (m : ℕ) : a (m + 8) = 3 * a (m + 7) - 3 * a (m + 6) + a (m + 5) + a (m + 3) - 3 * a (m + 2) +
    3 * a (m + 1) - a m := by
  have s3 := step (m + 3)
  have s2 := step (m + 2)
  have s1 := step (m + 1)
  have s0 := step m
  have c8 := c2 (m + 3 + 5)
  have c7 := c2 (m + 2 + 5)
  have c6 := c2 (m + 1 + 5)
  have c5 := c2 (m + 5)
  push_cast at c8 c7 c6 c5
  have key : 2 * (a (m + 8) - (3 * a (m + 7) - 3 * a (m + 6) + a (m + 5) + a (m + 3) - 3 * a (m + 2) +
      3 * a (m + 1) - a m)) = 0 := by
    linear_combination 2 * s3 - 6 * s2 + 6 * s1 - 2 * s0 + c8 - 3 * c7 + 3 * c6 - c5
  linarith

theorem a0 : a 0 = 0 := by norm_num [a]
theorem a1 : a 1 = 0 := by norm_num [a]
theorem a2 : a 2 = 1 := by norm_num [a]
theorem a3 : a 3 = 3 := by norm_num [a]
theorem a4 : a 4 = 6 := by norm_num [a]
theorem a5 : a 5 = 10 := by norm_num [a]
theorem a6 : a 6 = 15 := by norm_num [a]
theorem a7 : a 7 = 22 := by norm_num [a]

theorem gfC : PowerSeries.mk (fun n => (a n : ℚ)) * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * C (-3) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * C 3 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * C (-1) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * C (-1) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * C 3 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * X * C (-3) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * X * X * C 1 =
    (1 : ℚ⟦X⟧) * X * X * C 1 := by
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
            simp [a1, a2, a3, a4]
            norm_num
          | succ n =>
            cases n with
            | zero =>
              simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
              simp [a0, a2, a3, a4, a5]
              norm_num
            | succ n =>
              cases n with
              | zero =>
                simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                simp [a0, a1, a3, a4, a5, a6]
                norm_num
              | succ n =>
                cases n with
                | zero =>
                  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                  simp [a0, a1, a2, a4, a5, a6, a7]
                  norm_num
                | succ n =>
                  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
                  have h := rec8 n
                  have hq : ((a (n + 8) : ℤ) : ℚ) = 3 * ((a (n + 7) : ℤ) : ℚ) - 3 * ((a (n + 6) : ℤ) : ℚ) + ((a (n + 5) : ℤ) : ℚ) +
                      ((a (n + 3) : ℤ) : ℚ) - 3 * ((a (n + 2) : ℤ) : ℚ) + 3 * ((a (n + 1) : ℤ) : ℚ) - ((a n : ℤ) : ℚ) := by
                    exact_mod_cast h
                  simp [PowerSeries.coeff_one]
                  linear_combination hq

end A122047Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a122047.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    exact A122047Aux.rec8 m
  · have h := A122047Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
