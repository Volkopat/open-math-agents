import OMAStatements.S_oeis_a335756

-- Problem: A335756: A cup filling problem starting with 2 empty cups of sizes 3 and n, where a(n) is the number of unreachable states.
-- Upstream: formal-conjectures statements/oeis-a335756.lean:0 (declaration OMA.S_oeis_a335756.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! One has a(n+3) = a(n) + 10 if 3 divides n and a(n+3) = a(n) + 6 otherwise, and n+3 is divisible by
3 exactly when n is; hence a(n+6) - a(n+3) = a(n+3) - a(n). The denominator of the g.f. is
(1 - x^3)^2, so the coefficient of x^n in the product is a(n) - 2 a(n-3) + a(n-6), which is
2, 0, 2, 8, 6, 4 for n = 0, ..., 5 and 0 otherwise. -/

namespace A335756Aux

open OMA.S_oeis_a335756 PowerSeries

theorem step (n : ℕ) : a (n + 3) = a n + (if n % 3 = 0 then 10 else 6) := by
  unfold a
  by_cases h : n % 3 = 0
  · have h' : (n + 3) % 3 = 0 := by omega
    have e : (n + 3) / 3 = n / 3 + 1 := by omega
    rw [if_pos h, if_pos h', if_pos h, e]
    push_cast
    ring
  · have h' : ¬ ((n + 3) % 3 = 0) := by omega
    rw [if_neg h, if_neg h', if_neg h]
    push_cast
    ring

theorem rec6 (m : ℕ) : a (m + 6) = 2 * a (m + 3) - a m := by
  have s1 := step (m + 3)
  have s0 := step m
  have hm : (m + 3) % 3 = m % 3 := by omega
  rw [hm] at s1
  linear_combination s1 - s0

theorem a0 : a 0 = 2 := by norm_num [a]

theorem a1 : a 1 = 0 := by norm_num [a]

theorem a2 : a 2 = 2 := by norm_num [a]

theorem a3 : a 3 = 12 := by norm_num [a]

theorem a4 : a 4 = 6 := by norm_num [a]

theorem a5 : a 5 = 8 := by norm_num [a]

theorem gfC : PowerSeries.mk (fun n => (a n : ℚ)) * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * C (-2) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * C 1 =
    (1 : ℚ⟦X⟧) * C 2 + (1 : ℚ⟦X⟧) * X * X * C 2 + (1 : ℚ⟦X⟧) * X * X * X * C 8 +
      (1 : ℚ⟦X⟧) * X * X * X * X * C 6 + (1 : ℚ⟦X⟧) * X * X * X * X * X * C 4 := by
  ext n
  cases n with
  | zero =>
    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
    simp [a0]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
        PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
      simp [a1]
    | succ n =>
      cases n with
      | zero =>
        simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
          PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
        simp [a2]
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
            PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
          simp [a0, a3]
          norm_num
        | succ n =>
          cases n with
          | zero =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
              PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
            simp [a1, a4]
          | succ n =>
            cases n with
            | zero =>
              simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
                PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
              simp [a2, a5]
              norm_num
            | succ m =>
              simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
                PowerSeries.coeff_mk]
              have h := rec6 m
              have hq : ((a (m + 6) : ℤ) : ℚ) = 2 * ((a (m + 3) : ℤ) : ℚ) - ((a m : ℤ) : ℚ) := by
                exact_mod_cast h
              simp [PowerSeries.coeff_one]
              linear_combination hq

end A335756Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a335756.main := by
  refine ⟨?_, ?_⟩
  · have h := A335756Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have e1 : m + 6 - 3 = m + 3 := rfl
    have e2 : m + 6 - 6 = m := rfl
    rw [e1, e2]
    exact A335756Aux.rec6 m
