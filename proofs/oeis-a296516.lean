import OMAStatements.S_oeis_a296516

-- Problem: A296516: a(n) is the number of terms in expanded form of bivariate polynomial Q_n, where (P_n, Q_n) is defined by: P_0 = x, Q_0 = y, P_(n+1) = P_n + Q_n, Q_(n+1) = P_n * Q_n.
-- Upstream: formal-conjectures statements/oeis-a296516.lean:0 (declaration OMA.S_oeis_a296516.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! F(2n+1) satisfies u(n+2) = 3 u(n+1) - u(n), F(n+2) satisfies v(n+2) = v(n+1) + v(n), and the
quadratic part is killed by the third difference. The operator of the recurrence is
(E - 1)^3 (E^2 - 3E + 1) (E^2 - E - 1), so it kills each part of the closed form. The g.f. identity is
the same recurrence read coefficientwise, with the first eight coefficients checked directly. -/

namespace A296516Aux

open OMA.S_oeis_a296516 PowerSeries

theorem pstep (j : ℕ) : (Nat.fib (2 * (j + 2) + 1) : ℚ) =
    3 * (Nat.fib (2 * (j + 1) + 1) : ℚ) - (Nat.fib (2 * j + 1) : ℚ) := by
  have h1 : Nat.fib (2 * j + 3 + 2) = Nat.fib (2 * j + 3) + Nat.fib (2 * j + 3 + 1) := Nat.fib_add_two
  have h2 : Nat.fib (2 * j + 2 + 2) = Nat.fib (2 * j + 2) + Nat.fib (2 * j + 2 + 1) := Nat.fib_add_two
  have h3 : Nat.fib (2 * j + 1 + 2) = Nat.fib (2 * j + 1) + Nat.fib (2 * j + 1 + 1) := Nat.fib_add_two
  have e5 : 2 * (j + 2) + 1 = 2 * j + 3 + 2 := by ring
  have e3 : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
  rw [e5, e3]
  have h1q : (Nat.fib (2 * j + 3 + 2) : ℚ) = Nat.fib (2 * j + 3) + Nat.fib (2 * j + 4) := by
    exact_mod_cast h1
  have h2q : (Nat.fib (2 * j + 4) : ℚ) = Nat.fib (2 * j + 2) + Nat.fib (2 * j + 3) := by
    exact_mod_cast h2
  have h3q : (Nat.fib (2 * j + 3) : ℚ) = Nat.fib (2 * j + 1) + Nat.fib (2 * j + 2) := by
    exact_mod_cast h3
  linear_combination h1q + h2q - h3q

theorem qstep (j : ℕ) : (Nat.fib (j + 2 + 2) : ℚ) =
    (Nat.fib (j + 2) : ℚ) + (Nat.fib (j + 1 + 2) : ℚ) := by
  have h : Nat.fib (j + 2 + 2) = Nat.fib (j + 2) + Nat.fib (j + 1 + 2) := Nat.fib_add_two
  exact_mod_cast h

/-- The closed form without the special value at 0. -/
def g (n : ℕ) : ℚ :=
  ((Nat.fib (2 * n + 1) : ℚ) + (Nat.fib (n + 2) : ℚ) - (n : ℚ) ^ 2 + (n : ℚ) - 2) / 2

theorem ag (k : ℕ) (hk : k ≠ 0) : a k = g k := by
  simp [a, g, hk]

theorem grec (n : ℕ) : g (n + 7) = 7 * g (n + 6) - 18 * g (n + 5) + 20 * g (n + 4) - 6 * g (n + 3) - 6 * g (n + 2) + 5 * g (n + 1) - g n := by
  have p0 : (Nat.fib (2 * (n + 2) + 1) : ℚ) = 3 * (Nat.fib (2 * (n + 1) + 1) : ℚ) - (Nat.fib (2 * n + 1) : ℚ) := pstep n
  have p1 : (Nat.fib (2 * (n + 3) + 1) : ℚ) = 3 * (Nat.fib (2 * (n + 2) + 1) : ℚ) - (Nat.fib (2 * (n + 1) + 1) : ℚ) := pstep (n + 1)
  have p2 : (Nat.fib (2 * (n + 4) + 1) : ℚ) = 3 * (Nat.fib (2 * (n + 3) + 1) : ℚ) - (Nat.fib (2 * (n + 2) + 1) : ℚ) := pstep (n + 2)
  have p3 : (Nat.fib (2 * (n + 5) + 1) : ℚ) = 3 * (Nat.fib (2 * (n + 4) + 1) : ℚ) - (Nat.fib (2 * (n + 3) + 1) : ℚ) := pstep (n + 3)
  have p4 : (Nat.fib (2 * (n + 6) + 1) : ℚ) = 3 * (Nat.fib (2 * (n + 5) + 1) : ℚ) - (Nat.fib (2 * (n + 4) + 1) : ℚ) := pstep (n + 4)
  have p5 : (Nat.fib (2 * (n + 7) + 1) : ℚ) = 3 * (Nat.fib (2 * (n + 6) + 1) : ℚ) - (Nat.fib (2 * (n + 5) + 1) : ℚ) := pstep (n + 5)
  have q0 : (Nat.fib (n + 2 + 2) : ℚ) = (Nat.fib (n + 2) : ℚ) + (Nat.fib (n + 1 + 2) : ℚ) := qstep n
  have q1 : (Nat.fib (n + 3 + 2) : ℚ) = (Nat.fib (n + 1 + 2) : ℚ) + (Nat.fib (n + 2 + 2) : ℚ) := qstep (n + 1)
  have q2 : (Nat.fib (n + 4 + 2) : ℚ) = (Nat.fib (n + 2 + 2) : ℚ) + (Nat.fib (n + 3 + 2) : ℚ) := qstep (n + 2)
  have q3 : (Nat.fib (n + 5 + 2) : ℚ) = (Nat.fib (n + 3 + 2) : ℚ) + (Nat.fib (n + 4 + 2) : ℚ) := qstep (n + 3)
  have q4 : (Nat.fib (n + 6 + 2) : ℚ) = (Nat.fib (n + 4 + 2) : ℚ) + (Nat.fib (n + 5 + 2) : ℚ) := qstep (n + 4)
  have q5 : (Nat.fib (n + 7 + 2) : ℚ) = (Nat.fib (n + 5 + 2) : ℚ) + (Nat.fib (n + 6 + 2) : ℚ) := qstep (n + 5)
  simp only [g]
  push_cast at p0 p1 p2 p3 p4 p5 q0 q1 q2 q3 q4 q5 ⊢
  linear_combination (1 / 2 : ℚ) * ((1) * p0 + (-2) * p1 + (-1) * p2 + (5) * p3 + (-4) * p4 + (1) * p5
    + (-1) * q0 + (6) * q1 + (-13) * q2 + (13) * q3 + (-6) * q4 + (1) * q5)

theorem rec (n : ℕ) : a (n + 8) = 7 * a (n + 7) - 18 * a (n + 6) + 20 * a (n + 5) - 6 * a (n + 4) - 6 * a (n + 3) + 5 * a (n + 2) - a (n + 1) := by
  rw [ag (n + 8) (by omega), ag (n + 7) (by omega), ag (n + 6) (by omega), ag (n + 5) (by omega), ag (n + 4) (by omega), ag (n + 3) (by omega), ag (n + 2) (by omega), ag (n + 1) (by omega)]
  exact grec (n + 1)

theorem a0 : a 0 = 1 := by simp [a]
theorem a1 : a 1 = 1 := by norm_num [a]
theorem a2 : a 2 = 2 := by norm_num [a]
theorem a3 : a 3 = 5 := by norm_num [a]
theorem a4 : a 4 = 14 := by norm_num [a]
theorem a5 : a 5 = 40 := by norm_num [a]
theorem a6 : a 6 = 111 := by norm_num [a]
theorem a7 : a 7 = 300 := by norm_num [a]

theorem gfC : PowerSeries.mk a * C 1 +
    PowerSeries.mk a * X * C (-7) +
    PowerSeries.mk a * X * X * C 18 +
    PowerSeries.mk a * X * X * X * C (-20) +
    PowerSeries.mk a * X * X * X * X * C 6 +
    PowerSeries.mk a * X * X * X * X * X * C 6 +
    PowerSeries.mk a * X * X * X * X * X * X * C (-5) +
    PowerSeries.mk a * X * X * X * X * X * X * X * C 1 =
    (1 : ℚ⟦X⟧) * C 1 + (1 : ℚ⟦X⟧) * X * C (-6) + (1 : ℚ⟦X⟧) * X * X * C 13 + (1 : ℚ⟦X⟧) * X * X * X * C (-11) + (1 : ℚ⟦X⟧) * X * X * X * X * C 1 + (1 : ℚ⟦X⟧) * X * X * X * X * X * C 4 + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * C (-4) + (1 : ℚ⟦X⟧) * X * X * X * X * X * X * X * C 1 := by
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
      norm_num
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
                  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
                  simp [a0, a1, a2, a3, a4, a5, a6, a7]
                  norm_num
                | succ n =>
                  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
                  have h := rec n
                  simp [PowerSeries.coeff_one]
                  linear_combination h

end A296516Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a296516.main := by
  refine ⟨?_, ?_⟩
  · have h := A296516Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    exact A296516Aux.rec m
