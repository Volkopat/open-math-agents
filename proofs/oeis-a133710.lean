import OMAStatements.S_oeis_a133710

-- Problem: A133710: Column l=3 of irregular triangle in A133709.
-- Upstream: formal-conjectures statements/oeis-a133710.lean:0 (declaration OMA.S_oeis_a133710.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: unfolding the definition gives T(m,1) = 1, T(m,2) = C(m+2,m) - 3 and
-- T(m,3) = C(m+6,m) - 6 C(m+2,m) + 11, so 720 a(m) is the degree-6 polynomial
-- (m+1)(m+2)(m+3)(m+4)(m+5)(m+6) - 2160 (m+1)(m+2) + 7920. Its seventh difference vanishes,
-- which is the recurrence, and the g.f. follows by comparing coefficients.

namespace R06A133710

open OMA.S_oeis_a133710

theorem T_eq (m l : ℕ) : T m l = if l = 1 then 1
    else (∑ i ∈ Finset.range l, (-1) ^ i * (l.choose i : ℤ) *
        ((2 ^ (l - i) + m - 2).choose m : ℤ)) -
      ∑ i : Fin l, if (i : ℕ) = 0 then 0 else (Nat.stirlingSecond l i : ℤ) * T m i := by
  rw [T]

theorem fin_sum_eq (m l : ℕ) :
    (∑ i : Fin l, if (i : ℕ) = 0 then 0 else (Nat.stirlingSecond l i : ℤ) * T m i) =
      ∑ i ∈ Finset.range l, if i = 0 then 0 else (Nat.stirlingSecond l i : ℤ) * T m i :=
  Fin.sum_univ_eq_sum_range (fun i => if i = 0 then 0 else (Nat.stirlingSecond l i : ℤ) * T m i) l

theorem sum2 (f : ℕ → ℤ) : ∑ i ∈ Finset.range 2, f i = f 0 + f 1 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]

theorem sum3 (f : ℕ → ℤ) : ∑ i ∈ Finset.range 3, f i = f 0 + f 1 + f 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]

theorem T_one (m : ℕ) : T m 1 = 1 := by
  rw [T_eq, if_pos (rfl : (1 : ℕ) = 1)]

theorem T_two (m : ℕ) : T m 2 = ((m + 2).choose m : ℤ) - 3 := by
  rw [T_eq, if_neg (show ¬ (2 : ℕ) = 1 by norm_num), fin_sum_eq, sum2, sum2,
    if_pos (rfl : (0 : ℕ) = 0), if_neg (show ¬ (1 : ℕ) = 0 by norm_num), T_one]
  have p0 : (2 : ℕ) ^ (2 - 0) = 4 := by norm_num
  have p1 : (2 : ℕ) ^ (2 - 1) = 2 := by norm_num
  have e0 : 2 ^ (2 - 0) + m - 2 = m + 2 := by omega
  have e1 : 2 ^ (2 - 1) + m - 2 = m := by omega
  rw [e0, e1, Nat.choose_self, show Nat.choose 2 0 = 1 by decide,
    show Nat.choose 2 1 = 2 by decide, show Nat.stirlingSecond 2 1 = 1 by decide]
  push_cast
  ring

theorem T_three (m : ℕ) :
    T m 3 = ((m + 6).choose m : ℤ) - 6 * ((m + 2).choose m : ℤ) + 11 := by
  rw [T_eq, if_neg (show ¬ (3 : ℕ) = 1 by norm_num), fin_sum_eq, sum3, sum3,
    if_pos (rfl : (0 : ℕ) = 0), if_neg (show ¬ (1 : ℕ) = 0 by norm_num),
    if_neg (show ¬ (2 : ℕ) = 0 by norm_num), T_one, T_two]
  have p0 : (2 : ℕ) ^ (3 - 0) = 8 := by norm_num
  have p1 : (2 : ℕ) ^ (3 - 1) = 4 := by norm_num
  have p2 : (2 : ℕ) ^ (3 - 2) = 2 := by norm_num
  have e0 : 2 ^ (3 - 0) + m - 2 = m + 6 := by omega
  have e1 : 2 ^ (3 - 1) + m - 2 = m + 2 := by omega
  have e2 : 2 ^ (3 - 2) + m - 2 = m := by omega
  rw [e0, e1, e2, Nat.choose_self, show Nat.choose 3 0 = 1 by decide,
    show Nat.choose 3 1 = 3 by decide, show Nat.choose 3 2 = 3 by decide,
    show Nat.stirlingSecond 3 1 = 1 by decide, show Nat.stirlingSecond 3 2 = 3 by decide]
  push_cast
  ring

theorem c2 (m : ℕ) : ((m + 2).choose m : ℚ) * 2 = ((m : ℚ) + 1) * ((m : ℚ) + 2) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial m 2
  have g2 : Nat.factorial (m + 2) = (m + 2) * Nat.factorial (m + 1) := Nat.factorial_succ (m + 1)
  have g1 : Nat.factorial (m + 1) = (m + 1) * Nat.factorial m := Nat.factorial_succ m
  rw [← Nat.choose_symm_add, g2, g1, show Nat.factorial 2 = 2 by decide] at h
  have hq : ((m + 2).choose m : ℚ) * (Nat.factorial m : ℚ) * 2 =
      ((m : ℚ) + 2) * (((m : ℚ) + 1) * (Nat.factorial m : ℚ)) := by
    exact_mod_cast h
  have hf : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  apply mul_right_cancel₀ hf
  linear_combination hq

theorem c6 (m : ℕ) : ((m + 6).choose m : ℚ) * 720 =
    ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4) * ((m : ℚ) + 5) *
      ((m : ℚ) + 6) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial m 6
  have g6 : Nat.factorial (m + 6) = (m + 6) * Nat.factorial (m + 5) := Nat.factorial_succ (m + 5)
  have g5 : Nat.factorial (m + 5) = (m + 5) * Nat.factorial (m + 4) := Nat.factorial_succ (m + 4)
  have g4 : Nat.factorial (m + 4) = (m + 4) * Nat.factorial (m + 3) := Nat.factorial_succ (m + 3)
  have g3 : Nat.factorial (m + 3) = (m + 3) * Nat.factorial (m + 2) := Nat.factorial_succ (m + 2)
  have g2 : Nat.factorial (m + 2) = (m + 2) * Nat.factorial (m + 1) := Nat.factorial_succ (m + 1)
  have g1 : Nat.factorial (m + 1) = (m + 1) * Nat.factorial m := Nat.factorial_succ m
  rw [← Nat.choose_symm_add, g6, g5, g4, g3, g2, g1, show Nat.factorial 6 = 720 by decide] at h
  have hq : ((m + 6).choose m : ℚ) * (Nat.factorial m : ℚ) * 720 =
      ((m : ℚ) + 6) * (((m : ℚ) + 5) * (((m : ℚ) + 4) * (((m : ℚ) + 3) * (((m : ℚ) + 2) *
        (((m : ℚ) + 1) * (Nat.factorial m : ℚ)))))) := by
    exact_mod_cast h
  have hf : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  apply mul_right_cancel₀ hf
  linear_combination hq

theorem a_eq (m : ℕ) : a m = ((m + 6).choose m : ℤ) - 6 * ((m + 2).choose m : ℤ) + 11 :=
  T_three m

theorem hcf (m : ℕ) : (720 : ℚ) * (a m : ℚ) =
    ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4) * ((m : ℚ) + 5) *
      ((m : ℚ) + 6) - 2160 * ((m : ℚ) + 1) * ((m : ℚ) + 2) + 7920 := by
  have ha := congrArg (Int.cast : ℤ → ℚ) (a_eq m)
  push_cast at ha
  linear_combination 720 * ha + c6 m - 2160 * c2 m

end R06A133710

open OMA.S_oeis_a133710 R06A133710 in
theorem OMA.solution : type_of% @OMA.S_oeis_a133710.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    rw [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega,
      show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega,
      show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega,
      show k + 8 - 7 = k + 1 by omega]
    have h0 := hcf (k + 1)
    have h1 := hcf (k + 2)
    have h2 := hcf (k + 3)
    have h3 := hcf (k + 4)
    have h4 := hcf (k + 5)
    have h5 := hcf (k + 6)
    have h6 := hcf (k + 7)
    have h7 := hcf (k + 8)
    push_cast at h0 h1 h2 h3 h4 h5 h6 h7
    have hq : (a (k + 8) : ℚ) = 7 * (a (k + 7) : ℚ) - 21 * (a (k + 6) : ℚ) +
        35 * (a (k + 5) : ℚ) - 35 * (a (k + 4) : ℚ) + 21 * (a (k + 3) : ℚ) -
        7 * (a (k + 2) : ℚ) + (a (k + 1) : ℚ) := by
      linear_combination (h7 - 7 * h6 + 21 * h5 - 35 * h4 + 35 * h3 - 21 * h2 + 7 * h1 - h0) / 720
    exact_mod_cast hq
  · obtain ⟨A, hA⟩ : ∃ A : PowerSeries ℚ,
        A = PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ)) := ⟨_, rfl⟩
    rw [← hA]
    have cA : ∀ n, PowerSeries.coeff n A = if n = 0 then 0 else (a n : ℚ) := by
      intro n
      rw [hA, PowerSeries.coeff_mk]
    have hf : ∀ n, 1 ≤ n → PowerSeries.coeff n A = (a n : ℚ) := by
      intro n hn
      rw [cA, if_neg (show ¬ n = 0 by omega)]
    have v1 : (a 1 : ℚ) = 0 := by
      have h := hcf 1
      push_cast at h
      linear_combination h / 720
    have v2 : (a 2 : ℚ) = 3 := by
      have h := hcf 2
      push_cast at h
      linear_combination h / 720
    have v3 : (a 3 : ℚ) = 35 := by
      have h := hcf 3
      push_cast at h
      linear_combination h / 720
    have v4 : (a 4 : ℚ) = 131 := by
      have h := hcf 4
      push_cast at h
      linear_combination h / 720
    have v5 : (a 5 : ℚ) = 347 := by
      have h := hcf 5
      push_cast at h
      linear_combination h / 720
    have v6 : (a 6 : ℚ) = 767 := by
      have h := hcf 6
      push_cast at h
      linear_combination h / 720
    have v7 : (a 7 : ℚ) = 1511 := by
      have h := hcf 7
      push_cast at h
      linear_combination h / 720
    have k3 : (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat _ 3
    have k6 : (PowerSeries.C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat _ 6
    have k7 : (PowerSeries.C (7 : ℚ) : PowerSeries ℚ) = 7 := map_ofNat _ 7
    have k14 : (PowerSeries.C (14 : ℚ) : PowerSeries ℚ) = 14 := map_ofNat _ 14
    have k21 : (PowerSeries.C (21 : ℚ) : PowerSeries ℚ) = 21 := map_ofNat _ 21
    have k31 : (PowerSeries.C (31 : ℚ) : PowerSeries ℚ) = 31 := map_ofNat _ 31
    have k35 : (PowerSeries.C (35 : ℚ) : PowerSeries ℚ) = 35 := map_ofNat _ 35
    have k51 : (PowerSeries.C (51 : ℚ) : PowerSeries ℚ) = 51 := map_ofNat _ 51
    have k60 : (PowerSeries.C (60 : ℚ) : PowerSeries ℚ) = 60 := map_ofNat _ 60
    have e : A * (1 - PowerSeries.X) ^ 7 =
        A - A * PowerSeries.X ^ 1 * PowerSeries.C (7 : ℚ) +
          A * PowerSeries.X ^ 2 * PowerSeries.C (21 : ℚ) -
          A * PowerSeries.X ^ 3 * PowerSeries.C (35 : ℚ) +
          A * PowerSeries.X ^ 4 * PowerSeries.C (35 : ℚ) -
          A * PowerSeries.X ^ 5 * PowerSeries.C (21 : ℚ) +
          A * PowerSeries.X ^ 6 * PowerSeries.C (7 : ℚ) - A * PowerSeries.X ^ 7 := by
      rw [k7, k21, k35]
      ring
    have e2 : (PowerSeries.X ^ 2 * (3 + 14 * PowerSeries.X - 51 * PowerSeries.X ^ 2 +
        60 * PowerSeries.X ^ 3 - 31 * PowerSeries.X ^ 4 + 6 * PowerSeries.X ^ 5) :
          PowerSeries ℚ) =
        PowerSeries.X ^ 2 * PowerSeries.C (3 : ℚ) + PowerSeries.X ^ 3 * PowerSeries.C (14 : ℚ) -
          PowerSeries.X ^ 4 * PowerSeries.C (51 : ℚ) +
          PowerSeries.X ^ 5 * PowerSeries.C (60 : ℚ) -
          PowerSeries.X ^ 6 * PowerSeries.C (31 : ℚ) +
          PowerSeries.X ^ 7 * PowerSeries.C (6 : ℚ) := by
      rw [k3, k14, k51, k60, k31, k6]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 8 with hm | hm
    · interval_cases m <;> norm_num [cA, v1, v2, v3, v4, v5, v6, v7]
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 8 := ⟨m - 8, by omega⟩
      rw [if_pos (show 1 ≤ j + 8 by omega), if_pos (show 2 ≤ j + 8 by omega),
        if_pos (show 3 ≤ j + 8 by omega), if_pos (show 4 ≤ j + 8 by omega),
        if_pos (show 5 ≤ j + 8 by omega), if_pos (show 6 ≤ j + 8 by omega),
        if_pos (show 7 ≤ j + 8 by omega),
        if_neg (show ¬ (j + 8 = 2) by omega), if_neg (show ¬ (j + 8 = 3) by omega),
        if_neg (show ¬ (j + 8 = 4) by omega), if_neg (show ¬ (j + 8 = 5) by omega),
        if_neg (show ¬ (j + 8 = 6) by omega), if_neg (show ¬ (j + 8 = 7) by omega),
        show j + 8 - 1 = j + 7 by omega, show j + 8 - 2 = j + 6 by omega,
        show j + 8 - 3 = j + 5 by omega, show j + 8 - 4 = j + 4 by omega,
        show j + 8 - 5 = j + 3 by omega, show j + 8 - 6 = j + 2 by omega,
        show j + 8 - 7 = j + 1 by omega,
        hf (j + 8) (by omega), hf (j + 7) (by omega), hf (j + 6) (by omega),
        hf (j + 5) (by omega), hf (j + 4) (by omega), hf (j + 3) (by omega),
        hf (j + 2) (by omega), hf (j + 1) (by omega)]
      have h0 := hcf (j + 1)
      have h1 := hcf (j + 2)
      have h2 := hcf (j + 3)
      have h3 := hcf (j + 4)
      have h4 := hcf (j + 5)
      have h5 := hcf (j + 6)
      have h6 := hcf (j + 7)
      have h7 := hcf (j + 8)
      push_cast at h0 h1 h2 h3 h4 h5 h6 h7
      linear_combination (h7 - 7 * h6 + 21 * h5 - 35 * h4 + 35 * h3 - 21 * h2 + 7 * h1 - h0) / 720
