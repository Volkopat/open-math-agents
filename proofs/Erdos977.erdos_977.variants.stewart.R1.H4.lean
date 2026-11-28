import OMAReductions.R_Erdos977_erdos_977_variants_stewart_R1
import Mathlib

namespace OMA.Erdos977StewartH4

open Real Filter

private lemma pow_div_fact_le_exp (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    x ^ k / (k.factorial : ℝ) ≤ exp x := by
  exact Real.pow_div_factorial_le_exp x hx k

private lemma log_two_bounds : (0.69 : ℝ) < log 2 ∧ log 2 < 0.7 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> linarith

private lemma exp_small_bound (P : ℕ) (hP16 : P < 16) :
    (P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log P ≤ 150 := by
  have hlog2 := log_two_bounds
  by_cases hP0 : P = 0
  · subst hP0; simp
  by_cases hP1 : P = 1
  · subst hP1; simp
  have hP2 : 2 ≤ P := by omega
  have hPR : (P : ℝ) ≤ 15 := by exact_mod_cast (show P ≤ 15 by omega)
  have hlogP_nonneg : 0 ≤ log (P : ℝ) := log_natCast_nonneg P
  have hlogP_le : log (P : ℝ) ≤ 3 := by
    have h1 : (P : ℝ) ≤ 16 := by linarith
    have h2 : log (P : ℝ) ≤ log 16 := log_le_log (by positivity) h1
    have h16 : log (16 : ℝ) = 4 * log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
    linarith
  have hexp_le : exp (-log (P : ℝ) / (51.9 * log (log (P : ℝ)))) ≤ 3 := by
    by_cases hPeq2 : P = 2
    · subst hPeq2
      have hll : log (log (2 : ℝ)) ≤ -0.3 := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < log 2 by linarith)
        linarith
      have hden : 51.9 * log (log (2 : ℝ)) ≤ -15 := by linarith
      have hquot : -log (2 : ℝ) / (51.9 * log (log (2 : ℝ))) ≤ 1 := by
        rw [div_le_iff_of_neg (by linarith)]
        linarith
      have he1 : exp (1 : ℝ) < 3 := by
        have := Real.exp_one_lt_d9; linarith
      exact (exp_le_exp.mpr hquot).trans he1.le
    · have hP3 : (3 : ℝ) ≤ P := by exact_mod_cast (show 3 ≤ P by omega)
      have he1 : exp (1 : ℝ) < 3 := by
        have := Real.exp_one_lt_d9; linarith
      have hlP : 1 < log (P : ℝ) := by
        have := log_lt_log (exp_pos 1) (lt_of_lt_of_le he1 hP3)
        rwa [log_exp] at this
      have hll : 0 < log (log (P : ℝ)) := log_pos hlP
      have hquot : -log (P : ℝ) / (51.9 * log (log (P : ℝ))) ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      exact (exp_le_exp.mpr hquot).trans (by norm_num)
  have h1 : (P : ℝ) * exp (-log P / (51.9 * log (log P))) ≤ 15 * 3 :=
    mul_le_mul hPR hexp_le (by positivity) (by positivity)
  have h2 : (P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 ≤ 45 * 1 := by
    nlinarith [hlog2.1, hlog2.2]
  nlinarith

theorem main_proof : OMA.R_Erdos977_erdos_977_variants_stewart_R1.H4 := by
  refine ⟨1, by norm_num, ?_⟩
  let M : ℝ := 10 ^ 25
  filter_upwards [eventually_ge_atTop (Nat.ceil (exp (exp M)) + 16)] with n hn P hineq
  rw [one_mul]
  have hlog2 := log_two_bounds
  have hn_exp : exp (exp M) ≤ (n : ℝ) := by
    have h1 : (Nat.ceil (exp (exp M)) : ℝ) ≤ n := by exact_mod_cast (show Nat.ceil (exp (exp M)) ≤ n by omega)
    exact (Nat.le_ceil _).trans h1
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast (show 16 ≤ n by omega)
  have hn_pos : (0 : ℝ) < n := by linarith
  set L : ℝ := log (n : ℝ) with hL_def
  have hL_ge : exp M ≤ L := by
    have h := log_le_log (exp_pos (exp M)) hn_exp
    rwa [log_exp] at h
  have hL_pos : 0 < L := lt_of_lt_of_le (exp_pos M) hL_ge
  set ℓ : ℝ := log L with hℓ_def
  have hℓ_ge : M ≤ ℓ := by
    have h := log_le_log (exp_pos M) hL_ge
    rwa [log_exp] at h
  have hℓ_pos : 0 < ℓ := by
    have hMpos : (0 : ℝ) < M := by dsimp [M]; positivity
    linarith
  have hℓ_10 : (10 : ℝ) ≤ ℓ := by
    have hM10 : (10 : ℝ) ≤ M := by dsimp [M]; norm_num
    linarith
  have hℓ_huge : 48 * (60000 : ℝ) ^ 4 * 120 * 100 ≤ ℓ := by
    have hMhuge : 48 * (60000 : ℝ) ^ 4 * 120 * 100 ≤ M := by dsimp [M]; norm_num
    linarith
  -- Lower bounds from Taylor series of exp: L ≥ ℓ^5 / 120 and n ≥ L^3 / 6
  have hL_ge_poly : ℓ ^ 5 / 120 ≤ L := by
    have h := pow_div_fact_le_exp ℓ hℓ_pos.le 5
    have hfact : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num
    rw [hfact, exp_log hL_pos] at h
    exact h
  have hn_ge_poly : L ^ 3 / 6 ≤ n := by
    have h := pow_div_fact_le_exp L hL_pos.le 3
    have hfact : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
    rw [hfact, exp_log hn_pos] at h
    exact h
  have hL_big : (10 ^ 10 : ℝ) ≤ L := by
    have h1 : (10 ^ 4 : ℝ) ≤ ℓ := by
      have hM4 : (10 ^ 4 : ℝ) ≤ M := by dsimp [M]; norm_num
      linarith
    have h2 : (10 ^ 10 : ℝ) * 120 ≤ ℓ ^ 5 := by
      calc (10 ^ 10 : ℝ) * 120 ≤ (10 ^ 4 : ℝ) ^ 5 := by norm_num
        _ ≤ ℓ ^ 5 := pow_le_pow_left₀ (by norm_num) h1 5
    linarith
  -- LHS lower bound: (n / (Nat.log 2 n + 1)) * log 2 ≥ 0.2 * (n / L)
  have hlog2_pos : (0 : ℝ) < log 2 := by linarith only [hlog2.1]
  have hnatlog : (Nat.log 2 n : ℝ) ≤ L / log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    have hpow : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have hlog := log_le_log (by positivity) hpow
    rwa [log_pow] at hlog
  have hden_le : (Nat.log 2 n : ℝ) + 1 ≤ 2 * L / log 2 := by
    have h1 : 1 ≤ L / log 2 := by
      rw [le_div_iff₀ hlog2_pos]; linarith only [hL_big, hlog2.2]
    have h2L : 2 * L / log 2 = L / log 2 + L / log 2 := by ring
    linarith only [hnatlog, h1, h2L]
  have hlhs_ge : (0.2 : ℝ) * (n / L) ≤ (n : ℝ) / ((Nat.log 2 n : ℝ) + 1) * log 2 := by
    have h1 : (n : ℝ) / (2 * L / log 2) ≤ (n : ℝ) / ((Nat.log 2 n : ℝ) + 1) :=
      div_le_div_of_nonneg_left hn_pos.le (by positivity) hden_le
    have h2 : (n : ℝ) / (2 * L / log 2) * log 2 = (log 2 ^ 2 / 2) * (n / L) := by
      field_simp
    have h3 : (0.2 : ℝ) ≤ log 2 ^ 2 / 2 := by nlinarith [hlog2.1]
    have h4 : (0.2 : ℝ) * (n / L) ≤ (log 2 ^ 2 / 2) * (n / L) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    nlinarith [hlog2.1]
  -- log (4 * n) ≤ 0.01 * (n / L)
  have hlog4n : log (4 * (n : ℝ)) ≤ 0.01 * (n / L) := by
    have h4 : log (4 * (n : ℝ)) = 2 * log 2 + L := by
      rw [log_mul (by norm_num) hn_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; ring
    have h4le : log (4 * (n : ℝ)) ≤ 2 * L := by linarith [hlog2.2]
    have hL2 : 200 * L ^ 2 ≤ n := by nlinarith
    have hdiv : 2 * L ≤ 0.01 * (n / L) := by
      rw [mul_div_assoc', le_div_iff₀ hL_pos]
      linarith
    linarith
  -- Now prove Y ≤ P by contradiction
  by_contra! hPlt
  set Y : ℝ := (n : ℝ) ^ (1 + 1 / (104 * ℓ)) with hY_def
  by_cases hP16 : P < 16
  · have hsmall := exp_small_bound P hP16
    have hPR_le : (P : ℝ) ≤ 16 := by exact_mod_cast (show P ≤ 16 by omega)
    have hterm : (P : ℝ) / n *
        ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P) ≤
        2400 * L / n := by
      have heq : (P : ℝ) / n *
          ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P) =
          (P : ℝ) * ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log P) * (L / n) := by
        rw [hL_def]; ring
      rw [heq]
      have h1 : (P : ℝ) * ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log P) ≤ 16 * 150 := by
        have hnonneg : 0 ≤ (P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log P := by
          have : 0 ≤ log (P : ℝ) := log_natCast_nonneg P
          have : 0 ≤ log 2 := by linarith only [hlog2.1]
          positivity
        exact mul_le_mul hPR_le hsmall hnonneg (by norm_num)
      have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ L / n by positivity)
      have h3 : (16 * 150 : ℝ) * (L / n) = 2400 * L / n := by ring
      linarith only [h2, h3]
    have hsmall2 : 2400 * L / n ≤ 0.01 * (n / L) := by
      have hLn : 240000 * L ^ 2 ≤ (n : ℝ) := by
        have hL2 : 240000 * 6 ≤ L := by linarith only [hL_big]
        have hL3 : 240000 * 6 * L ^ 2 ≤ L ^ 3 := by
          have : L ^ 3 = L * L ^ 2 := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right hL2 (by positivity)
        linarith only [hL3, hn_ge_poly]
      have hsq : 240000 * L ^ 2 ≤ (n : ℝ) ^ 2 := by
        have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn16]
        linarith only [hLn, this]
      rw [div_le_iff₀ hn_pos, mul_div_assoc', mul_comm (0.01 * (n : ℝ) / L),
        mul_div_assoc', le_div_iff₀ hL_pos]
      nlinarith only [hsq]
    have : (0.2 : ℝ) * (n / L) ≤ 0.02 * (n / L) := by linarith only [hlhs_ge, hineq, hlog4n, hterm, hsmall2]
    have hpos_nL : 0 < (n : ℝ) / L := by positivity
    linarith only [this, hpos_nL]
  · have hPR16 : (16 : ℝ) ≤ P := by exact_mod_cast (show 16 ≤ P by omega)
    have h1_le_exp : (1 : ℝ) ≤ 1 + 1 / (104 * ℓ) := by
      have : (0 : ℝ) ≤ 1 / (104 * ℓ) := by positivity
      linarith
    have hY_ge_n : (n : ℝ) ≤ Y := by
      rw [hY_def]
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
        _ ≤ (n : ℝ) ^ (1 + 1 / (104 * ℓ)) :=
          rpow_le_rpow_of_exponent_le (by linarith only [hn16]) h1_le_exp
    have hY_pos : 0 < Y := by linarith only [hn_pos, hY_ge_n]
    have hlogY : log Y = (1 + 1 / (104 * ℓ)) * L := by
      rw [hY_def, log_rpow hn_pos, hL_def]
    have hlogY_le : log Y ≤ 2 * L := by
      have hdiv : 1 / (104 * ℓ) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith only [hℓ_10]
      nlinarith only [hlogY, hdiv, hL_pos]
    have hlogP_le : log (P : ℝ) ≤ 2 * L :=
      (log_le_log (by positivity) hPlt.le).trans hlogY_le
    have hmono := OMA.R_Erdos977_erdos_977_variants_stewart_R1.mono_aux hPR16 hPlt.le
    -- Upper bound on log (log Y)
    have hlogY_pos : 0 < log Y := by rw [hlogY]; positivity
    have hllY : log (log Y) ≤ (51.95 / 51.9) * ℓ := by
      rw [hlogY, log_mul (by positivity) hL_pos.ne', ← hℓ_def]
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (104 * ℓ) by positivity)
      have h2 : 1 / (104 * ℓ) ≤ (0.05 / 51.9) * ℓ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [hℓ_10]
      linarith only [h1, h2]
    have hllY_pos : 0 < log (log Y) := by
      have : 1 < log Y := by nlinarith only [hlogY, h1_le_exp, hL_big]
      exact log_pos this
    have hexp_arg : L / (51.95 * ℓ) ≤ log Y / (51.9 * log (log Y)) := by
      have hnum : L ≤ log Y := by nlinarith only [hlogY, h1_le_exp, hL_pos]
      have hden : 51.9 * log (log Y) ≤ 51.95 * ℓ := by linarith only [hllY]
      calc L / (51.95 * ℓ) ≤ log Y / (51.95 * ℓ) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ log Y / (51.9 * log (log Y)) :=
            div_le_div_of_nonneg_left hlogY_pos.le (by positivity) hden
    -- Combine (Y / n) * Y * exp(-log Y / (51.9 * log (log Y))) ≤ n * exp (-L / (60000 * ℓ))
    have hY2_div_n : Y / n * Y = n * exp (L / (52 * ℓ)) := by
      have hY_exp : Y = exp ((1 + 1 / (104 * ℓ)) * L) := by
        rw [← hlogY, exp_log hY_pos]
      have hn_exp2 : (n : ℝ) = exp L := (exp_log hn_pos).symm
      rw [hY_exp, hn_exp2]
      rw [div_mul_eq_mul_div, ← exp_add, ← exp_sub, ← exp_add]
      congr 1
      field_simp
      ring
    have hprod_bound : (P : ℝ) / n * ((P : ℝ) * exp (-log P / (51.9 * log (log P)))) ≤
        n * exp (-L / (60000 * ℓ)) := by
      have h1 : (P : ℝ) / n * ((P : ℝ) * exp (-log P / (51.9 * log (log P)))) ≤
          Y / n * (Y * exp (-log Y / (51.9 * log (log Y)))) := by
        apply mul_le_mul (div_le_div_of_nonneg_right hPlt.le hn_pos.le) hmono (by positivity) (by positivity)
      have h2 : Y / n * (Y * exp (-log Y / (51.9 * log (log Y)))) =
          n * exp (L / (52 * ℓ) - log Y / (51.9 * log (log Y))) := by
        rw [← mul_assoc, hY2_div_n, mul_assoc, ← exp_add]
        congr 2; ring
      have h3 : L / (52 * ℓ) - log Y / (51.9 * log (log Y)) ≤ -L / (60000 * ℓ) := by
        have hdiff : L / (52 * ℓ) - L / (51.95 * ℓ) = -(0.05 / (52 * 51.95)) * (L / ℓ) := by
          field_simp; ring
        have hconst : (1 / 60000 : ℝ) ≤ 0.05 / (52 * 51.95) := by norm_num
        have h4 : -(0.05 / (52 * 51.95)) * (L / ℓ) ≤ -(1 / 60000) * (L / ℓ) := by
          nlinarith only [hconst, show 0 < L / ℓ by positivity]
        have h5 : -(1 / 60000 : ℝ) * (L / ℓ) = -L / (60000 * ℓ) := by ring
        linarith only [hexp_arg, hdiff, h4, h5]
      calc (P : ℝ) / n * ((P : ℝ) * exp (-log P / (51.9 * log (log P))))
          ≤ n * exp (L / (52 * ℓ) - log Y / (51.9 * log (log Y))) := h2 ▸ h1
        _ ≤ n * exp (-L / (60000 * ℓ)) :=
          mul_le_mul_of_nonneg_left (exp_le_exp.mpr h3) hn_pos.le
    -- Bound exp(-L / (60000 * ℓ)) using x^4 / 24 ≤ exp x
    set x : ℝ := L / (60000 * ℓ) with hx_def
    have hx_pos : 0 < x := by positivity
    have hexp_neg : exp (-x) ≤ 24 / x ^ 4 := by
      have h := pow_div_fact_le_exp x hx_pos.le 4
      have hfact : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num
      rw [hfact] at h
      rw [exp_neg, le_div_iff₀ (by positivity)]
      have h1 := mul_le_mul_of_nonneg_left h (show 0 ≤ (exp x)⁻¹ by positivity)
      rw [inv_mul_cancel₀ (exp_pos x).ne'] at h1
      linarith only [h1]
    have hsecond : (P : ℝ) / n *
        ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P) ≤
        0.01 * (n / L) := by
      have hrew : (P : ℝ) / n *
          ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P) =
          ((P : ℝ) / n * ((P : ℝ) * exp (-log P / (51.9 * log (log P))))) *
            (log 2 * L * log P) := by
        rw [hL_def]; ring
      rw [hrew]
      have hfac_le : log 2 * L * log P ≤ 2 * L ^ 2 := by
        have h1 : log 2 * L ≤ L := by nlinarith only [hlog2.2, hL_pos]
        have h2 : 0 ≤ log (P : ℝ) := log_natCast_nonneg P
        nlinarith only [h1, h2, hlogP_le, hL_pos]
      have hstep1 : ((P : ℝ) / n * ((P : ℝ) * exp (-log P / (51.9 * log (log P))))) *
            (log 2 * L * log P) ≤ (n * exp (-x)) * (2 * L ^ 2) := by
        have hrew2 : -L / (60000 * ℓ) = -x := by rw [hx_def]; ring
        rw [hrew2] at hprod_bound
        exact mul_le_mul hprod_bound hfac_le (by positivity) (by positivity)
      have hstep2 : (n * exp (-x)) * (2 * L ^ 2) ≤ (n * (24 / x ^ 4)) * (2 * L ^ 2) := by
        gcongr
      have hstep3 : (n * (24 / x ^ 4)) * (2 * L ^ 2) =
          (48 * 60000 ^ 4 * ℓ ^ 4 / L) * (n / L) := by
        rw [hx_def]; field_simp; ring
      have hcoef : 48 * (60000 : ℝ) ^ 4 * ℓ ^ 4 / L ≤ 0.01 := by
        rw [div_le_iff₀ hL_pos]
        have h2 : 48 * (60000 : ℝ) ^ 4 * 120 * 100 * ℓ ^ 4 ≤ ℓ ^ 5 := by
          have : ℓ ^ 5 = ℓ * ℓ ^ 4 := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right hℓ_huge (by positivity)
        linarith only [h2, hL_ge_poly]
      have hstep4 : (48 * 60000 ^ 4 * ℓ ^ 4 / L) * (n / L) ≤ 0.01 * (n / L) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      linarith only [hstep1, hstep2, hstep3, hstep4]
    have : (0.2 : ℝ) * (n / L) ≤ 0.02 * (n / L) := by linarith only [hlhs_ge, hineq, hlog4n, hsecond]
    have hpos_nL : 0 < (n : ℝ) / L := by positivity
    linarith only [this, hpos_nL]

end OMA.Erdos977StewartH4

theorem OMA.solution : OMA.R_Erdos977_erdos_977_variants_stewart_R1.H4 :=
  OMA.Erdos977StewartH4.main_proof
