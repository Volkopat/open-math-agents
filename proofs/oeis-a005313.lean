import OMAStatements.S_oeis_a005313

-- Problem: A005313: Maximal sum of inverse squares of the singular values of triangular anti-Hadamard matrices of order n.
-- Upstream: formal-conjectures statements/oeis-a005313.lean:0 (declaration OMA.S_oeis_a005313.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! With c(n) = F(n) F(n+1) one has a(n+1) = a(n) + 1 + c(n) and
c(n+3) = 2 c(n+2) + 2 c(n+1) - c(n). Hence a satisfies the recurrence with operator
(E - 1)^2 (E + 1) (E^2 - 3E + 1), and the g.f. identity is this recurrence read coefficientwise,
with the first five coefficients checked directly. -/

namespace A005313Aux

open OMA.S_oeis_a005313 PowerSeries

theorem astep (n : ℕ) : a (n + 1) = a n + 1 + (Nat.fib n : ℤ) * (Nat.fib (n + 1) : ℤ) := by
  unfold a
  rw [Finset.sum_range_succ]
  push_cast
  ring

theorem cstep (n : ℕ) : (Nat.fib (n + 3) : ℤ) * (Nat.fib (n + 4) : ℤ) =
    2 * ((Nat.fib (n + 2) : ℤ) * (Nat.fib (n + 3) : ℤ)) +
      2 * ((Nat.fib (n + 1) : ℤ) * (Nat.fib (n + 2) : ℤ)) - (Nat.fib n : ℤ) * (Nat.fib (n + 1) : ℤ) := by
  have g2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have g3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  have g4 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
  have h2 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by exact_mod_cast g2
  have h3 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by exact_mod_cast g3
  have h4 : (Nat.fib (n + 4) : ℤ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by exact_mod_cast g4
  rw [h4, h3, h2]
  ring

theorem rec (n : ℕ) : a (n + 5) = 4 * a (n + 4) - 3 * a (n + 3) - 3 * a (n + 2) + 4 * a (n + 1) - a n := by
  have s0 : a (n + 1) = a n + 1 + (Nat.fib n : ℤ) * (Nat.fib (n + 1) : ℤ) := astep n
  have s1 : a (n + 2) = a (n + 1) + 1 + (Nat.fib (n + 1) : ℤ) * (Nat.fib (n + 2) : ℤ) := astep (n + 1)
  have s2 : a (n + 3) = a (n + 2) + 1 + (Nat.fib (n + 2) : ℤ) * (Nat.fib (n + 3) : ℤ) := astep (n + 2)
  have s3 : a (n + 4) = a (n + 3) + 1 + (Nat.fib (n + 3) : ℤ) * (Nat.fib (n + 4) : ℤ) := astep (n + 3)
  have s4 : a (n + 5) = a (n + 4) + 1 + (Nat.fib (n + 4) : ℤ) * (Nat.fib (n + 5) : ℤ) := astep (n + 4)
  have c0 : (Nat.fib (n + 3) : ℤ) * (Nat.fib (n + 4) : ℤ) = 2 * ((Nat.fib (n + 2) : ℤ) * (Nat.fib (n + 3) : ℤ)) + 2 * ((Nat.fib (n + 1) : ℤ) * (Nat.fib (n + 2) : ℤ)) - (Nat.fib n : ℤ) * (Nat.fib (n + 1) : ℤ) := cstep n
  have c1 : (Nat.fib (n + 4) : ℤ) * (Nat.fib (n + 5) : ℤ) = 2 * ((Nat.fib (n + 3) : ℤ) * (Nat.fib (n + 4) : ℤ)) + 2 * ((Nat.fib (n + 2) : ℤ) * (Nat.fib (n + 3) : ℤ)) - (Nat.fib (n + 1) : ℤ) * (Nat.fib (n + 2) : ℤ) := cstep (n + 1)
  linear_combination (-1) * s0 + 3 * s1 - 3 * s3 + s4 + c1 - c0

theorem a0 : a 0 = 0 := by norm_num [a, Finset.sum_range_succ]
theorem a1 : a 1 = 1 := by norm_num [a, Finset.sum_range_succ]
theorem a2 : a 2 = 3 := by norm_num [a, Finset.sum_range_succ]
theorem a3 : a 3 = 6 := by norm_num [a, Finset.sum_range_succ]
theorem a4 : a 4 = 13 := by norm_num [a, Finset.sum_range_succ]

theorem gfC : PowerSeries.mk (fun n => (a n : ℚ)) * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * C (-4) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * C 3 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * C 3 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * C (-4) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * C 1 =
    (1 : ℚ⟦X⟧) * X * C 1 + (1 : ℚ⟦X⟧) * X * X * C (-1) + (1 : ℚ⟦X⟧) * X * X * X * C (-3) + (1 : ℚ⟦X⟧) * X * X * X * X * C 1 := by
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
        norm_num
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
          simp [a0, a1, a2, a3]
          norm_num
        | succ n =>
          cases n with
          | zero =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
            simp [a0, a1, a2, a3, a4]
            norm_num
          | succ n =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
            have h := rec n
            have hq : ((a (n + 5) : ℤ) : ℚ) = 4 * ((a (n + 4) : ℤ) : ℚ) - 3 * ((a (n + 3) : ℤ) : ℚ) - 3 * ((a (n + 2) : ℤ) : ℚ) + 4 * ((a (n + 1) : ℤ) : ℚ) - ((a n : ℤ) : ℚ) := by
              exact_mod_cast h
            simp [PowerSeries.coeff_one]
            linear_combination hq

end A005313Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a005313.main := by
  have h := A005313Aux.gfC
  simp only [map_ofNat, map_neg, map_one] at h
  linear_combination h
