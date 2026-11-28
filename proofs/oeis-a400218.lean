import OMAStatements.S_oeis_a400218

-- Problem: A400218: Scaled z-coordinates of the vertices of a Boerdijk-Coxeter helix starting at a tetrahedron with vertices (-1,-1,-1), (1, -1, 1), (-1, 1, 1), and (1, 1, -1).
-- Upstream: formal-conjectures statements/oeis-a400218.lean:0 (declaration OMA.S_oeis_a400218.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the z-coordinates satisfy z(n+4) = (2/3)(z(n+1) + z(n+2) + z(n+3)) - z(n), so
-- b(n) = 3^n z(n+3) = a(n+3) satisfies b(n+4) = 2b(n+3) + 6b(n+2) + 18b(n+1) - 81b(n), whose
-- polynomial is (x - 3)(x^3 + x^2 - 3x - 27). Hence e(n) = b(n+3) + b(n+2) - 3b(n+1) - 27b(n) has
-- e(n+1) = 3e(n), and e(0) = -13 + 1 - 15 + 27 = 0, so e = 0. That is the coefficient of x^m,
-- m >= 6, in the product; the coefficients for m < 6 come from a(0..5) = -1, 1, 1, -1, 5, 1.

open OMA.S_oeis_a400218 in
theorem OMA.solution : type_of% @OMA.S_oeis_a400218.main := by
  have hz : ∀ n, (v (n + 4)).2.2 =
      2 / 3 * ((v (n + 1)).2.2 + (v (n + 2)).2.2 + (v (n + 3)).2.2) - (v n).2.2 := fun n => rfl
  have z0 : (v 0).2.2 = -1 := rfl
  have z1 : (v 1).2.2 = 1 := rfl
  have z2 : (v 2).2.2 = 1 := rfl
  have z3 : (v 3).2.2 = -1 := rfl
  have z4 : (v 4).2.2 = 5 / 3 := by
    have h : (v 4).2.2 = 2 / 3 * ((v 1).2.2 + (v 2).2.2 + (v 3).2.2) - (v 0).2.2 := rfl
    rw [h, z0, z1, z2, z3]
    norm_num
  have z5 : (v 5).2.2 = 1 / 9 := by
    have h : (v 5).2.2 = 2 / 3 * ((v 2).2.2 + (v 3).2.2 + (v 4).2.2) - (v 1).2.2 := rfl
    rw [h, z1, z2, z3, z4]
    norm_num
  have z6 : (v 6).2.2 = -13 / 27 := by
    have h : (v 6).2.2 = 2 / 3 * ((v 3).2.2 + (v 4).2.2 + (v 5).2.2) - (v 2).2.2 := rfl
    rw [h, z2, z3, z4, z5]
    norm_num
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ n, b n = 3 ^ n * (v (n + 3)).2.2 := ⟨_, fun _ => rfl⟩
  have hbrec : ∀ n, b (n + 4) = 2 * b (n + 3) + 6 * b (n + 2) + 18 * b (n + 1) - 81 * b n := by
    intro n
    have e4 : b (n + 4) = 3 ^ (n + 4) * (v (n + 7)).2.2 := hb (n + 4)
    have e3 : b (n + 3) = 3 ^ (n + 3) * (v (n + 6)).2.2 := hb (n + 3)
    have e2 : b (n + 2) = 3 ^ (n + 2) * (v (n + 5)).2.2 := hb (n + 2)
    have e1 : b (n + 1) = 3 ^ (n + 1) * (v (n + 4)).2.2 := hb (n + 1)
    have e0 : b n = 3 ^ n * (v (n + 3)).2.2 := hb n
    have h7 : (v (n + 7)).2.2 =
        2 / 3 * ((v (n + 4)).2.2 + (v (n + 5)).2.2 + (v (n + 6)).2.2) - (v (n + 3)).2.2 :=
      hz (n + 3)
    rw [e4, e3, e2, e1, e0, h7]
    ring
  have hE : ∀ n, b (n + 3) + b (n + 2) - 3 * b (n + 1) - 27 * b n = 0 := by
    intro n
    induction n with
    | zero =>
      have f0 : b 0 = 3 ^ 0 * (v 3).2.2 := hb 0
      have f1 : b 1 = 3 ^ 1 * (v 4).2.2 := hb 1
      have f2 : b 2 = 3 ^ 2 * (v 5).2.2 := hb 2
      have f3 : b 3 = 3 ^ 3 * (v 6).2.2 := hb 3
      show b 3 + b 2 - 3 * b 1 - 27 * b 0 = 0
      rw [f3, f2, f1, f0, z6, z5, z4, z3]
      norm_num
    | succ k ih =>
      show b (k + 4) + b (k + 3) - 3 * b (k + 2) - 27 * b (k + 1) = 0
      linear_combination hbrec k + 3 * ih
  have hab : ∀ j, a (j + 3) = b j := by
    intro j
    rw [hb j]
    show (if j + 3 ≤ 3 then (1 : ℚ) else 3 ^ (j + 3 - 3)) * (v (j + 3)).2.2 =
      3 ^ j * (v (j + 3)).2.2
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [if_pos (show j + 3 ≤ 3 by omega), h, pow_zero]
    · rw [if_neg (show ¬ (j + 3 ≤ 3) by omega), show j + 3 - 3 = j by omega]
  have key : ∀ m, 6 ≤ m → a m + a (m - 1) - 3 * a (m - 2) - 27 * a (m - 3) = 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega]
    have h6 : a (k + 6) = b (k + 3) := hab (k + 3)
    have h5 : a (k + 5) = b (k + 2) := hab (k + 2)
    have h4 : a (k + 4) = b (k + 1) := hab (k + 1)
    have h3 : a (k + 3) = b k := hab k
    rw [h6, h5, h4, h3]
    exact hE k
  have a0 : a 0 = -1 := by
    show (if 0 ≤ 3 then (1 : ℚ) else 3 ^ (0 - 3)) * (v 0).2.2 = -1
    rw [z0]
    norm_num
  have a1 : a 1 = 1 := by
    show (if 1 ≤ 3 then (1 : ℚ) else 3 ^ (1 - 3)) * (v 1).2.2 = 1
    rw [z1]
    norm_num
  have a2 : a 2 = 1 := by
    show (if 2 ≤ 3 then (1 : ℚ) else 3 ^ (2 - 3)) * (v 2).2.2 = 1
    rw [z2]
    norm_num
  have a3 : a 3 = -1 := by
    show (if 3 ≤ 3 then (1 : ℚ) else 3 ^ (3 - 3)) * (v 3).2.2 = -1
    rw [z3]
    norm_num
  have a4 : a 4 = 5 := by
    show (if 4 ≤ 3 then (1 : ℚ) else 3 ^ (4 - 3)) * (v 4).2.2 = 5
    rw [z4]
    norm_num
  have a5 : a 5 = 1 := by
    show (if 5 ≤ 3 then (1 : ℚ) else 3 ^ (5 - 3)) * (v 5).2.2 = 1
    rw [z5]
    norm_num
  have e : PowerSeries.mk a *
      (27 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 - PowerSeries.X - 1) =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 27 * (PowerSeries.mk a * PowerSeries.X ^ 3)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * (PowerSeries.mk a * PowerSeries.X ^ 2)
        - PowerSeries.mk a * PowerSeries.X ^ 1 - PowerSeries.mk a := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 27,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3]
    ring
  have e2 : (18 * PowerSeries.X ^ 5 + 26 * PowerSeries.X ^ 4 - 24 * PowerSeries.X ^ 3 -
      5 * PowerSeries.X ^ 2 + 1 : PowerSeries ℚ) =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 18 * PowerSeries.X ^ 5
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 26 * PowerSeries.X ^ 4
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 24 * PowerSeries.X ^ 3
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * PowerSeries.X ^ 2 + PowerSeries.X ^ 0 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 18,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 26,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 24,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 6 with hm | hm
  · interval_cases m
    · norm_num [a0]
    · norm_num [a0, a1]
    · norm_num [a0, a1, a2]
    · norm_num [a0, a1, a2, a3]
    · norm_num [a1, a2, a3, a4]
    · norm_num [a2, a3, a4, a5]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [key m hm]
