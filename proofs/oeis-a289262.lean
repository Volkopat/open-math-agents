import OMAStatements.S_oeis_a289262
import Mathlib

open PowerSeries OMA.S_oeis_a289262

private noncomputable def r : ℝ := 11/7

private noncomputable def deltaSeries := denominator r * (1+(X : ℚ⟦X⟧))

private theorem weight_period (n : ℕ) : weight r (n+7) = weight r n + 11 := by
  unfold weight r
  rw [show (((n+7 : ℕ) : ℝ)+1)*(11/7) =
    ((n : ℝ)+1)*(11/7)+(11 : ℤ) by push_cast; ring, Int.floor_add_intCast, Int.cast_add]
  norm_num

private theorem delta_step (n : ℕ) :
    coeff (n+1) deltaSeries = (-1 : ℚ)^(n+1)*weight r (n+1)+(-1 : ℚ)^n*weight r n := by
  simp [deltaSeries, denominator, mul_add, coeff_succ_mul_X]

private theorem delta_period (n : ℕ) : coeff (n+7) deltaSeries = -coeff n deltaSeries := by
  cases n with
  | zero =>
    rw [show 0+7=6+1 by decide, delta_step]
    norm_num [deltaSeries, denominator, mul_add, weight, r]
  | succ n =>
    rw [show n.succ+7=(n+7)+1 by omega, delta_step, delta_step,
      show n+7+1=n+1+7 by omega, weight_period, weight_period]
    rw [pow_add (-1 : ℚ) (n+1) 7, pow_add (-1 : ℚ) n 7, pow_succ (-1 : ℚ) n]
    ring

private theorem multiply_period :
    deltaSeries*(1+X^7) = 1-C 2*X^1+X^2-C 2*X^3+X^4-C 2*X^5+C 2*X^6 := by
  rw [mul_add,mul_one]
  ext n
  simp only [map_add, map_sub, coeff_C_mul_X_pow]
  simp only [coeff_one, coeff_X_pow, coeff_mul_X_pow']
  by_cases h : 7 ≤ n
  · have e := delta_period (n-7)
    rw [show n-7+7=n by omega] at e
    simp [h,show n≠0 by omega,show n≠1 by omega,show n≠2 by omega,show n≠3 by omega,
      show n≠4 by omega,show n≠5 by omega,show n≠6 by omega,e]
  · interval_cases n
    · norm_num [deltaSeries, denominator, mul_add, weight, r]
    all_goals rw [delta_step]; norm_num [weight,r]

private theorem cleared :
    (denominator r)⁻¹ * (1-C 2*X^1+X^6+C 2*X^7-C 2*X^8) =
    (1+X)*(1+X^7)*(1-X^2) := by
  have h0 : constantCoeff (denominator r) = 1 := by norm_num [denominator,weight,r]
  have he : denominator r*((1+X)*(1+X^7)*(1-X^2)) =
      1-C 2*X^1+X^6+C 2*X^7-C 2*X^8 := by
    calc
      _ = (deltaSeries*(1+X^7))*(1-X^2) := by unfold deltaSeries; ring
      _ = _ := by
        rw [multiply_period]
        have hc : C (2 : ℚ) = (2 : ℚ⟦X⟧) := by
          rw [show (2 : ℚ) = 1+1 by norm_num, map_add, map_one]
          norm_num
        simp only [hc]
        ring
  rw [← he, ← mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [h0]; norm_num), one_mul]

private def pulse (n : ℕ) : ℚ :=
  (if n=0 then 1 else 0) + (if n=1 then 1 else 0) - (if n=2 then 1 else 0) -
    (if n=3 then 1 else 0) + (if n=7 then 1 else 0) + (if n=8 then 1 else 0) -
    (if n=9 then 1 else 0) - (if n=10 then 1 else 0)

private noncomputable def shift (n k : ℕ) : ℚ := if k ≤ n then a r (n-k) else 0

private theorem coeff_recurrence (n : ℕ) :
    a r n-2*shift n 1+shift n 6+2*shift n 7-2*shift n 8 = pulse n := by
  have e := congrArg (coeff (R := ℚ) n) cleared
  rw [show ((1+X)*(1+X^7)*(1-X^2) : ℚ⟦X⟧) =
    1+X^1-X^2-X^3+X^7+X^8-X^9-X^10 by ring] at e
  rw [show (denominator r)⁻¹ * (1-C 2*X^1+X^6+C 2*X^7-C 2*X^8) =
    (denominator r)⁻¹ - C 2*((denominator r)⁻¹*X^1) + (denominator r)⁻¹*X^6 +
      C 2*((denominator r)⁻¹*X^7) - C 2*((denominator r)⁻¹*X^8) by simp; ring] at e
  simp only [map_add,map_sub,coeff_one,coeff_X_pow,coeff_C_mul,coeff_mul_X_pow',a,shift,pulse] at e ⊢
  exact e

private theorem small_values (n : ℕ) (hn : n < 11) :
    a r n = ([1, 3, 5, 9, 18, 36, 71, 138, 268, 522, 1017] : List ℚ)[n]?.getD 0 := by
  have h0 : a r 0 = 1 := by
    have e := coeff_recurrence 0
    norm_num [shift,pulse] at e
    linarith
  have h1 : a r 1 = 3 := by
    have e := coeff_recurrence 1
    norm_num [shift,pulse, h0] at e
    linarith
  have h2 : a r 2 = 5 := by
    have e := coeff_recurrence 2
    norm_num [shift,pulse, h1] at e
    linarith
  have h3 : a r 3 = 9 := by
    have e := coeff_recurrence 3
    norm_num [shift,pulse, h2] at e
    linarith
  have h4 : a r 4 = 18 := by
    have e := coeff_recurrence 4
    norm_num [shift,pulse, h3] at e
    linarith
  have h5 : a r 5 = 36 := by
    have e := coeff_recurrence 5
    norm_num [shift,pulse, h4] at e
    linarith
  have h6 : a r 6 = 71 := by
    have e := coeff_recurrence 6
    norm_num [shift,pulse, h5, h0] at e
    linarith
  have h7 : a r 7 = 138 := by
    have e := coeff_recurrence 7
    norm_num [shift,pulse, h6, h1, h0] at e
    linarith
  have h8 : a r 8 = 268 := by
    have e := coeff_recurrence 8
    norm_num [shift,pulse, h7, h2, h1, h0] at e
    linarith
  have h9 : a r 9 = 522 := by
    have e := coeff_recurrence 9
    norm_num [shift,pulse, h8, h3, h2, h1] at e
    linarith
  have h10 : a r 10 = 1017 := by
    have e := coeff_recurrence 10
    norm_num [shift,pulse, h9, h4, h3, h2] at e
    linarith
  interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem OMA.solution : type_of% @OMA.S_oeis_a289262.main := by
  change StrictMono (a r)
  have growth (n : ℕ) : 0 < a r n ∧ (0 < n → 3*a r (n-1) ≤ 2*a r n) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h : n < 11
      · have e := small_values n h
        constructor
        · rw [e]
          interval_cases n <;> norm_num
        · intro hpos
          rw [e, small_values (n-1) (by omega)]
          interval_cases n <;> norm_num
      · have e := coeff_recurrence n
        simp [shift,pulse, show 1 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
          show 8 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
          show n ≠ 3 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
          show n ≠ 9 by omega, show n ≠ 10 by omega] at e
        have h1 := (ih (n-1) (by omega)).2 (by omega)
        rw [show n-1-1=n-2 by omega] at h1
        have h2 := (ih (n-2) (by omega)).2 (by omega)
        rw [show n-2-1=n-3 by omega] at h2
        have h3 := (ih (n-3) (by omega)).2 (by omega)
        rw [show n-3-1=n-4 by omega] at h3
        have h4 := (ih (n-4) (by omega)).2 (by omega)
        rw [show n-4-1=n-5 by omega] at h4
        have h5 := (ih (n-5) (by omega)).2 (by omega)
        rw [show n-5-1=n-6 by omega] at h5
        have h6 := (ih (n-6) (by omega)).2 (by omega)
        rw [show n-6-1=n-7 by omega] at h6
        have hprev := (ih (n-1) (by omega)).1
        have htail := (ih (n-8) (by omega)).1
        constructor
        · linarith
        · intro _
          linarith
  apply strictMono_nat_of_lt_succ
  intro n
  have hp := (growth n).1
  have h := (growth (n+1)).2 (by omega)
  rw [Nat.add_sub_cancel] at h
  linarith