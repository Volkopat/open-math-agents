import OMAStatements.S_oeis_a006172

-- Problem: A006172: a(n) = 1 + F(2*n+1) + (-1)^n*L(n).
-- Upstream: formal-conjectures statements/oeis-a006172.lean:0 (declaration OMA.S_oeis_a006172.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(n) = 1 + f(n) + g(n) with f(n) = F(2n+1), g(n) = (-1)^n L(n). From the Fibonacci
-- and Lucas recurrences, f(n+2) = 3f(n+1) - f(n) and g(n+2) = g(n) - g(n+1); the constant 1, f and
-- g are annihilated by x - 1, x^2 - 3x + 1 and x^2 + x - 1, whose product is
-- x^5 - 3x^4 - x^3 + 7x^2 - 5x + 1, so a(n+5) = 3a(n+4) + a(n+3) - 7a(n+2) + 5a(n+1) - a(n).
-- The denominator is D = 1 - 3x - x^2 + 7x^3 - 5x^4 + x^5, so the coefficient of x^m in a * D is 0
-- for m >= 5, and for m < 5 it is 4, -10, -1, 9, -3 from a(0..4) = 4, 2, 9, 10, 42 (Berselli).
-- Plouffe's numerator has constant coefficient 2, while that of a * D is a(0) = 4.

open OMA.S_oeis_a006172 in
theorem OMA.solution : type_of% @OMA.S_oeis_a006172.main := by
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℤ, ∀ n, F n = (Nat.fib (2 * n + 1) : ℤ) := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℤ, ∀ n, G n = (-1) ^ n * L n := ⟨_, fun _ => rfl⟩
  have ha : ∀ n, a n = 1 + F n + G n := by
    intro n
    rw [hF n, hG n]
    rfl
  have hFr : ∀ n, F (n + 2) = 3 * F (n + 1) - F n := by
    intro n
    rw [hF (n + 2), hF (n + 1), hF n]
    rw [show 2 * (n + 2) + 1 = 2 * n + 5 by ring, show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    have e1 : Nat.fib (2 * n + 5) = Nat.fib (2 * n + 3) + Nat.fib (2 * n + 4) :=
      Nat.fib_add_two (n := 2 * n + 3)
    have e2 : Nat.fib (2 * n + 4) = Nat.fib (2 * n + 2) + Nat.fib (2 * n + 3) :=
      Nat.fib_add_two (n := 2 * n + 2)
    have e3 : Nat.fib (2 * n + 3) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) :=
      Nat.fib_add_two (n := 2 * n + 1)
    have e1' : (Nat.fib (2 * n + 5) : ℤ) = (Nat.fib (2 * n + 3) : ℤ) + (Nat.fib (2 * n + 4) : ℤ) := by
      exact_mod_cast e1
    have e2' : (Nat.fib (2 * n + 4) : ℤ) = (Nat.fib (2 * n + 2) : ℤ) + (Nat.fib (2 * n + 3) : ℤ) := by
      exact_mod_cast e2
    have e3' : (Nat.fib (2 * n + 3) : ℤ) = (Nat.fib (2 * n + 1) : ℤ) + (Nat.fib (2 * n + 2) : ℤ) := by
      exact_mod_cast e3
    linarith
  have hGr : ∀ n, G (n + 2) = G n - G (n + 1) := by
    intro n
    rw [hG (n + 2), hG (n + 1), hG n]
    have hL : L (n + 2) = L (n + 1) + L n := rfl
    rw [hL]
    ring
  have hrec : ∀ k, a (k + 5) = 3 * a (k + 4) + a (k + 3) - 7 * a (k + 2) + 5 * a (k + 1) - a k := by
    intro k
    simp only [ha]
    have f5 : F (k + 5) = 3 * F (k + 4) - F (k + 3) := hFr (k + 3)
    have f3 : F (k + 3) = 3 * F (k + 2) - F (k + 1) := hFr (k + 1)
    have f2 : F (k + 2) = 3 * F (k + 1) - F k := hFr k
    have g5 : G (k + 5) = G (k + 3) - G (k + 4) := hGr (k + 3)
    have g4 : G (k + 4) = G (k + 2) - G (k + 3) := hGr (k + 2)
    have g3 : G (k + 3) = G (k + 1) - G (k + 2) := hGr (k + 1)
    have g2 : G (k + 2) = G k - G (k + 1) := hGr k
    linear_combination f5 - 2 * f3 + f2 + g5 - 4 * g4 + 4 * g3 - g2
  have hq : ∀ m, 5 ≤ m → (a m : ℚ) = 3 * (a (m - 1) : ℚ) + (a (m - 2) : ℚ) - 7 * (a (m - 3) : ℚ) +
      5 * (a (m - 4) : ℚ) - (a (m - 5) : ℚ) := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
    rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
      show k + 5 - 5 = k by omega]
    exact_mod_cast hrec k
  have F0 : F 0 = 1 := by
    rw [hF]
    decide
  have F1 : F 1 = 2 := by
    rw [hF]
    decide
  have F2 : F 2 = 5 := by
    rw [hF]
    decide
  have F3 : F 3 = 13 := by
    rw [hF]
    decide
  have F4 : F 4 = 34 := by
    rw [hF]
    decide
  have G0 : G 0 = 2 := by
    rw [hG]
    decide
  have G1 : G 1 = -1 := by
    rw [hG]
    decide
  have G2 : G 2 = 3 := by
    rw [hG]
    decide
  have G3 : G 3 = -4 := by
    rw [hG]
    decide
  have G4 : G 4 = 7 := by
    rw [hG]
    decide
  have q0 : (a 0 : ℚ) = 4 := by
    have h : a 0 = 4 := by
      rw [ha, F0, G0]
      norm_num
    exact_mod_cast h
  have q1 : (a 1 : ℚ) = 2 := by
    have h : a 1 = 2 := by
      rw [ha, F1, G1]
      norm_num
    exact_mod_cast h
  have q2 : (a 2 : ℚ) = 9 := by
    have h : a 2 = 9 := by
      rw [ha, F2, G2]
      norm_num
    exact_mod_cast h
  have q3 : (a 3 : ℚ) = 10 := by
    have h : a 3 = 10 := by
      rw [ha, F3, G3]
      norm_num
    exact_mod_cast h
  have q4 : (a 4 : ℚ) = 42 := by
    have h : a 4 = 42 := by
      rw [ha, F4, G4]
      norm_num
    exact_mod_cast h
  have e : PowerSeries.mk (fun n => (a n : ℚ)) * ((PowerSeries.X - 1) *
      (PowerSeries.X ^ 2 - PowerSeries.X - 1) * (PowerSeries.X ^ 2 - 3 * PowerSeries.X + 1)) =
      PowerSeries.mk (fun n => (a n : ℚ))
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
        - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4)
        + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 5 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5]
    ring
  have e2 : (4 - 10 * PowerSeries.X - PowerSeries.X ^ 2 + 9 * PowerSeries.X ^ 3 -
      3 * PowerSeries.X ^ 4 : PowerSeries ℚ) =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * PowerSeries.X ^ 1
        - PowerSeries.X ^ 2
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9 * PowerSeries.X ^ 3
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * PowerSeries.X ^ 4 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3]
    ring
  have hB : PowerSeries.mk (fun n => (a n : ℚ)) * ((PowerSeries.X - 1) *
      (PowerSeries.X ^ 2 - PowerSeries.X - 1) * (PowerSeries.X ^ 2 - 3 * PowerSeries.X + 1)) =
      4 - 10 * PowerSeries.X - PowerSeries.X ^ 2 + 9 * PowerSeries.X ^ 3 -
        3 * PowerSeries.X ^ 4 := by
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 5 with hm | hm
    · interval_cases m
      · norm_num [q0]
      · norm_num [q0, q1]
      · norm_num [q0, q1, q2]
      · norm_num [q0, q1, q2, q3]
      · norm_num [q0, q1, q2, q3, q4]
    · simp (disch := omega) only [if_pos, if_neg]
      linarith [hq m hm]
  refine ⟨fun h => ?_, hB⟩
  have h2 : (4 - 10 * PowerSeries.X - PowerSeries.X ^ 2 + 9 * PowerSeries.X ^ 3 -
      3 * PowerSeries.X ^ 4 : PowerSeries ℚ) =
      -(-2 - 3 * PowerSeries.X + 19 * PowerSeries.X ^ 2 - 17 * PowerSeries.X ^ 3 +
        4 * PowerSeries.X ^ 4) := hB.symm.trans h
  have h0 : PowerSeries.coeff 0 (4 - 10 * PowerSeries.X - PowerSeries.X ^ 2 +
      9 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 4 : PowerSeries ℚ) =
      PowerSeries.coeff 0 (-(-2 - 3 * PowerSeries.X + 19 * PowerSeries.X ^ 2 -
        17 * PowerSeries.X ^ 3 + 4 * PowerSeries.X ^ 4) : PowerSeries ℚ) := by
    rw [h2]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
  have c4 : PowerSeries.constantCoeff (4 : PowerSeries ℚ) = 4 :=
    map_ofNat (PowerSeries.constantCoeff : PowerSeries ℚ →+* ℚ) 4
  have c2 : PowerSeries.constantCoeff (2 : PowerSeries ℚ) = 2 :=
    map_ofNat (PowerSeries.constantCoeff : PowerSeries ℚ →+* ℚ) 2
  norm_num [c4, c2] at h0
