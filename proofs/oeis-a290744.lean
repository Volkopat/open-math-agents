import OMAStatements.S_oeis_a290744

-- Problem: A290744: Maximum number of distinct Lyndon factors that can appear in words of length n over an alphabet of size 5.
-- Upstream: formal-conjectures statements/oeis-a290744.lean:0 (declaration OMA.S_oeis_a290744.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Replacing n by n + 5 replaces m by m + 1 and keeps p, and the closed form gives
a(n+5) = a(n) + 4 n + 10. Hence the second difference of a(n) - a(n-5) vanishes. The denominator of
the g.f. is (1 - x)^2 (1 - x^5), so the coefficient of x^n in the product is that second difference
(with b(k) = 0 for k ≤ 0), which matches the numerator for n ≤ 7 and is 0 otherwise. -/

namespace A290744Aux

open OMA.S_oeis_a290744 PowerSeries

theorem c2 (n : ℕ) : 2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem step (n : ℕ) : a (n + 5) = a n + 4 * (n : ℤ) + 10 := by
  unfold a
  have e1 : (n + 5) / 5 = n / 5 + 1 := by omega
  have e2 : (n + 5) % 5 = n % 5 := by omega
  obtain ⟨M, P, hM, hP, hnat⟩ : ∃ M P : ℕ, n / 5 = M ∧ n % 5 = P ∧ n = 5 * M + P :=
    ⟨n / 5, n % 5, rfl, rfl, (Nat.div_add_mod n 5).symm⟩
  rw [e1, e2, hM, hP]
  have hn : (n : ℤ) = 5 * (M : ℤ) + (P : ℤ) := by exact_mod_cast hnat
  have ca := c2 (n + 5 + 1)
  have cb := c2 (n + 1)
  have cc := c2 (M + 1 + 1)
  have cd := c2 (M + 1)
  have ce := c2 (M + 1 + 2)
  have cf := c2 (M + 2)
  push_cast at ca cb cc cd ce cf ⊢
  refine mul_left_cancel₀ (a := (2 : ℤ)) (by norm_num) ?_
  linear_combination ca - cb - (5 - (P : ℤ)) * cc + (5 - (P : ℤ)) * cd - (P : ℤ) * ce + (P : ℤ) * cf + 2 * hn

theorem rec (m : ℕ) : a (m + 7) = 2 * a (m + 6) - a (m + 5) + a (m + 2) - 2 * a (m + 1) + a m := by
  have s2 := step (m + 2)
  have s1 := step (m + 1)
  have s0 := step m
  push_cast at s2 s1 s0
  linear_combination s2 - 2 * s1 + s0

theorem b0 : b 0 = 0 := by simp [b]
theorem b1 : b 1 = 5 := by norm_num [b, a, Nat.choose]
theorem b2 : b 2 = 6 := by norm_num [b, a, Nat.choose]
theorem b3 : b 3 = 8 := by norm_num [b, a, Nat.choose]
theorem b4 : b 4 = 11 := by norm_num [b, a, Nat.choose]
theorem b5 : b 5 = 15 := by norm_num [b, a, Nat.choose]
theorem b6 : b 6 = 19 := by norm_num [b, a, Nat.choose]
theorem b7 : b 7 = 24 := by norm_num [b, a, Nat.choose]

theorem recb (m : ℕ) : b (m + 8) = 2 * b (m + 7) - b (m + 6) + b (m + 3) - 2 * b (m + 2) + b (m + 1) := by
  unfold b
  have h0 : ¬ (m + 8 = 0) := by omega
  have h1 : ¬ (m + 7 = 0) := by omega
  have h2 : ¬ (m + 6 = 0) := by omega
  have h3 : ¬ (m + 3 = 0) := by omega
  have h4 : ¬ (m + 2 = 0) := by omega
  have h5 : ¬ (m + 1 = 0) := by omega
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  exact rec (m + 1)

theorem gfC : PowerSeries.mk (fun n => (b n : ℚ)) * C 1 +
    PowerSeries.mk (fun n => (b n : ℚ)) * X * C (-2) +
    PowerSeries.mk (fun n => (b n : ℚ)) * X * X * C 1 +
    PowerSeries.mk (fun n => (b n : ℚ)) * X * X * X * X * X * C (-1) +
    PowerSeries.mk (fun n => (b n : ℚ)) * X * X * X * X * X * X * C 2 +
    PowerSeries.mk (fun n => (b n : ℚ)) * X * X * X * X * X * X * X * C (-1) =
    (1 : ℚ⟦X⟧) * X * C 5 + (1 : ℚ⟦X⟧) * X * X * C (-4) + (1 : ℚ⟦X⟧) * X * X * X * C 1 + (1 : ℚ⟦X⟧) * X * X * X * X * C 1 + (1 : ℚ⟦X⟧) * X * X * X * X * X * C 1 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * C (-5) + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * X * C 5 := by
  ext n
  cases n with
  | zero =>
    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
    simp [b0]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
      simp [b0, b1]
    | succ n =>
      cases n with
      | zero =>
        simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
        simp [b0, b1, b2]
        norm_num
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
          simp [b1, b2, b3]
          norm_num
        | succ n =>
          cases n with
          | zero =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
            simp [b2, b3, b4]
            norm_num
          | succ n =>
            cases n with
            | zero =>
              simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
              simp [b0, b3, b4, b5]
              norm_num
            | succ n =>
              cases n with
              | zero =>
                simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
                simp [b0, b1, b4, b5, b6]
                norm_num
              | succ n =>
                cases n with
                | zero =>
                  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
                  simp [b0, b1, b2, b5, b6, b7]
                  norm_num
                | succ n =>
                  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
                  have h := recb n
                  have hq : ((b (n + 8) : ℤ) : ℚ) = 2 * ((b (n + 7) : ℤ) : ℚ) - ((b (n + 6) : ℤ) : ℚ) + ((b (n + 3) : ℤ) : ℚ) - 2 * ((b (n + 2) : ℤ) : ℚ) + ((b (n + 1) : ℤ) : ℚ) := by
                    exact_mod_cast h
                  simp [PowerSeries.coeff_one]
                  linear_combination hq

end A290744Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a290744.main := by
  refine ⟨?_, ?_⟩
  · have h := A290744Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    exact A290744Aux.rec m
