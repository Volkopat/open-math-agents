import OMAStatements.S_arxiv_2202_03713
import Mathlib

/-!
# Proof of Doumas monotonicity conjecture (arXiv:2202.03713, Conjecture 2.5)

Agent: antigravity
Model: Gemini 4 Neon
Credit: @Andyi955

We prove that `a_p = pi^2 / 6 + p * w_p - p^2 * c_p^2` is strictly decreasing for `p >= 1`.

## Proof Overview

1. For `p >= 1` and `u in (0, 1)`, define the quantile function of `log(max(E_1, ..., E_p))`:
   `h_p(u) = log (-log (1 - u ^ (1 / p)))`.
2. Changing variables `u = (1 - exp (-x)) ^ p` (`x > 0`), expanding `(1 - exp (-x)) ^ (p - 1)`
   binomially, and scaling `t = (j + 1) * x` yields
   `Var(h_p) = (I_2 - I_1^2) + p * w_p - p^2 * c_p^2`,
   where `I_m = int_{Ioi 0} (log x)^m * exp (-x) dx`.
   Hence `a_p - a_{p+1} = Var(h_p) - Var(h_{p+1})`, without needing to evaluate `I_2 - I_1^2`.
3. On `(0, 1)`, the derivative satisfies
   `h_p'(u) = Psi(1 - u ^ (1 / p)) / (u * (-log u))`,
   where `Psi(w) = ((1 - w) * (-log (1 - w))) / (w * (-log w))`.
   By `log x < x - 1` applied to `x = 1 / w` and `x = 1 / (1 - w)`, `(log Psi)'(w) > 0`,
   so `Psi` is strictly increasing on `(0, 1)`.
4. Since `1 - u ^ (1 / (p + 1)) < 1 - u ^ (1 / p)`, we get `0 < h_{p+1}'(u) < h_p'(u)` on `(0, 1)`.
   Thus both `f = h_{p+1}` and `d = h_p - h_{p+1}` are strictly increasing on `(0, 1)`.
5. By the intermediate value theorem, `f(u*) = mean(f)` for some `u* in (0, 1)`, whence
   `(f(u) - mean(f)) * (d(u) - d(u*)) >= 0` pointwise on `(0, 1)`, giving `Cov(f, d) >= 0`.
   Since `d` is strictly increasing and continuous, `Var(d) > 0`, and therefore
   `Var(h_p) = Var(f) + 2 * Cov(f, d) + Var(d) > Var(f) = Var(h_{p+1})`.
-/

open MeasureTheory Set Filter Real

namespace OMA.P_arxiv_2202_03713

/-- First log-exponential moment `I1 = int_0^infty log(x) exp(-x) dx`. -/
private noncomputable def I1 : ℝ := ∫ x in Ioi (0 : ℝ), Real.log x * Real.exp (-x)

/-- Second log-exponential moment `I2 = int_0^infty (log x)^2 exp(-x) dx`. -/
private noncomputable def I2 : ℝ := ∫ x in Ioi (0 : ℝ), Real.log x ^ 2 * Real.exp (-x)

/-- Change-of-variables map `phi_p(x) = (1 - exp(-x))^p` from `(0, infty)` onto `(0, 1)`. -/
private noncomputable def phi (p : ℕ) (x : ℝ) : ℝ := (1 - Real.exp (-x)) ^ p

/-- Derivative of `phi_p`. -/
private noncomputable def phi' (p : ℕ) (x : ℝ) : ℝ :=
  (p : ℝ) * (1 - Real.exp (-x)) ^ (p - 1) * Real.exp (-x)

/-- Quantile function `h_p(u) = log(-log(1 - u^(1/p)))` on `(0, 1)`. -/
private noncomputable def h (p : ℕ) (u : ℝ) : ℝ :=
  Real.log (-Real.log (1 - u ^ (1 / (p : ℝ))))

/-- Auxiliary function `Psi(w) = ((1 - w)(-log(1 - w))) / (w(-log w))`. -/
private noncomputable def Psi (w : ℝ) : ℝ :=
  ((1 - w) * (-Real.log (1 - w))) / (w * (-Real.log w))

/-- Logarithm of `Psi(w)` on `(0, 1)`. -/
private noncomputable def logPsi (w : ℝ) : ℝ :=
  Real.log (1 - w) + Real.log (-Real.log (1 - w)) - Real.log w - Real.log (-Real.log w)

/-- Variance of a function on `(0, 1)` under Lebesgue measure. -/
private noncomputable def var01 (f : ℝ → ℝ) : ℝ :=
  ∫ u in Ioo (0 : ℝ) 1, (f u - ∫ t in Ioo (0 : ℝ) 1, f t) ^ 2

/-! ### Step 1: Integrability and scaling of `(log x)^m * exp(-k * x)` on `Ioi 0` -/

private lemma integrableOn_log_pow_exp (m : ℕ) (hm : m ≤ 2) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun x : ℝ => Real.log x ^ m * Real.exp (-k * x)) (Ioi (0 : ℝ)) := by
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) :=
    (Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · -- Integrability on `(0, 1]`, dominated by `16 * x ^ (-1/2)`.
    have hdom : IntegrableOn (fun x : ℝ => (16 : ℝ) * x ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) := by
      have hr : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume (0 : ℝ) 1 :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hr
      exact hr.const_mul 16
    have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.log x ^ m * Real.exp (-k * x))
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine (ContinuousOn.pow ?_ m).mul ?_
      · exact continuousOn_log.mono (fun x hx => ne_of_gt hx.1)
      · exact (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hexp_le : Real.exp (-k * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hlog_nonpos : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx1
    have hr4_ge : (1 : ℝ) ≤ x ^ (-(1 / 4 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx1 (by norm_num)
    have hr2_eq : x ^ (-(1 / 4 : ℝ)) * x ^ (-(1 / 4 : ℝ)) = x ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hr2_ge : (1 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := by
      rw [← hr2_eq]
      nlinarith
    have hlog_bound : -Real.log x ≤ 4 * x ^ (-(1 / 4 : ℝ)) := by
      have hy : 0 < x ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hx0 _
      have h1 : Real.log (x ^ (-(1 / 4 : ℝ))) ≤ x ^ (-(1 / 4 : ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos hy
      rw [Real.log_rpow hx0] at h1
      linarith
    have habs_log : |Real.log x| ≤ 4 * x ^ (-(1 / 4 : ℝ)) := by
      rw [abs_of_nonpos hlog_nonpos]
      exact hlog_bound
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    have hpow_le : |Real.log x| ^ m ≤ 16 * x ^ (-(1 / 2 : ℝ)) := by
      interval_cases m
      · simp only [pow_zero]
        linarith
      · simp only [pow_one]
        have : x ^ (-(1 / 4 : ℝ)) ≤ x ^ (-(1 / 2 : ℝ)) := by
          rw [← hr2_eq]
          nlinarith
        linarith
      · calc |Real.log x| ^ 2
            ≤ (4 * x ^ (-(1 / 4 : ℝ))) ^ 2 := by
              nlinarith [abs_nonneg (Real.log x), habs_log]
          _ = 16 * (x ^ (-(1 / 4 : ℝ)) * x ^ (-(1 / 4 : ℝ))) := by ring
          _ = 16 * x ^ (-(1 / 2 : ℝ)) := by rw [hr2_eq]
    calc |Real.log x| ^ m * Real.exp (-k * x)
        ≤ |Real.log x| ^ m * 1 := mul_le_mul_of_nonneg_left hexp_le (pow_nonneg (abs_nonneg _) _)
      _ = |Real.log x| ^ m := mul_one _
      _ ≤ 16 * x ^ (-(1 / 2 : ℝ)) := hpow_le
  · -- Integrability on `(1, infty)`, dominated by `C * exp(-(k/2) * x)`.
    set C : ℝ := 1 + 2 / k + 8 / k ^ 2 with hC_def
    have hdom : IntegrableOn (fun x : ℝ => C * Real.exp (-(k / 2) * x)) (Ioi (1 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith : -(k / 2) < 0) 1).const_mul C
    have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.log x ^ m * Real.exp (-k * x))
        (volume.restrict (Ioi (1 : ℝ))) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine (ContinuousOn.pow ?_ m).mul ?_
      · exact continuousOn_log.mono (fun x hx => ne_of_gt (lt_trans zero_lt_one hx))
      · exact (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx1
    have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hlog_le : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
    set u : ℝ := k / 2 * x with hu_def
    have hu0 : 0 ≤ u := by positivity
    have hexp_split : Real.exp (-k * x) = Real.exp (-u) * Real.exp (-(k / 2) * x) := by
      rw [← Real.exp_add]
      congr 1
      rw [hu_def]
      ring
    have hexp_ge : 1 + u + u ^ 2 / 2 ≤ Real.exp u := by
      have h := Real.sum_le_exp_of_nonneg hu0 3
      simp [Finset.sum_range_succ, Nat.factorial] at h
      linarith
    have hexp_pos : 0 < Real.exp u := Real.exp_pos u
    have hpow_le : x ^ m * Real.exp (-u) ≤ C := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hexp_pos]
      have hk1 : 0 < 2 / k := by positivity
      have hk2 : 0 < 8 / k ^ 2 := by positivity
      have hC1 : 1 ≤ C := by rw [hC_def]; linarith
      have hC2 : 2 / k ≤ C := by rw [hC_def]; linarith
      have hC3 : 8 / k ^ 2 ≤ C := by rw [hC_def]; linarith
      interval_cases m
      · simp only [pow_zero]
        nlinarith [Real.one_le_exp hu0]
      · simp only [pow_one]
        have hxu : x = (2 / k) * u := by rw [hu_def]; field_simp
        have hu_le : u ≤ Real.exp u := by nlinarith [sq_nonneg u]
        calc x = (2 / k) * u := hxu
          _ ≤ (2 / k) * Real.exp u := mul_le_mul_of_nonneg_left hu_le (by positivity)
          _ ≤ C * Real.exp u := mul_le_mul_of_nonneg_right hC2 hexp_pos.le
      · have hx2u : x ^ 2 = (8 / k ^ 2) * (u ^ 2 / 2) := by rw [hu_def]; field_simp; ring
        have hu2_le : u ^ 2 / 2 ≤ Real.exp u := by linarith
        calc x ^ 2 = (8 / k ^ 2) * (u ^ 2 / 2) := hx2u
          _ ≤ (8 / k ^ 2) * Real.exp u := mul_le_mul_of_nonneg_left hu2_le (by positivity)
          _ ≤ C * Real.exp u := mul_le_mul_of_nonneg_right hC3 hexp_pos.le
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hlog_nn, abs_of_pos (Real.exp_pos _),
      hexp_split, ← mul_assoc]
    calc Real.log x ^ m * Real.exp (-u) * Real.exp (-(k / 2) * x)
        ≤ x ^ m * Real.exp (-u) * Real.exp (-(k / 2) * x) := by
          gcongr
      _ ≤ C * Real.exp (-(k / 2) * x) := by
          gcongr

private lemma integral_log_exp_mul {k : ℝ} (hk : 0 < k) :
    ∫ x in Ioi (0 : ℝ), Real.log x * Real.exp (-k * x) = (I1 - Real.log k) / k := by
  have hcongr : ∫ x in Ioi (0 : ℝ), Real.log x * Real.exp (-k * x) =
      ∫ x in Ioi (0 : ℝ), (Real.log (k * x) - Real.log k) * Real.exp (-(k * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    rw [Real.log_mul hk.ne' hx0.ne']
    ring_nf
  rw [hcongr]
  have hscale := integral_comp_mul_left_Ioi
    (fun t : ℝ => (Real.log t - Real.log k) * Real.exp (-t)) (0 : ℝ) hk
  simp only [mul_zero, smul_eq_mul] at hscale
  rw [hscale]
  have hint1 : IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioi (0 : ℝ)) := by
    simpa using integrableOn_log_pow_exp 1 (by omega) one_pos
  have hint0 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi (0 : ℝ)) := by
    simpa using integrableOn_log_pow_exp 0 (by omega) one_pos
  have hint0c : IntegrableOn (fun t : ℝ => Real.log k * Real.exp (-t)) (Ioi (0 : ℝ)) :=
    hint0.const_mul (Real.log k)
  have hsub : ∫ t in Ioi (0 : ℝ), (Real.log t - Real.log k) * Real.exp (-t) =
      I1 - Real.log k := by
    have heq : (fun t : ℝ => (Real.log t - Real.log k) * Real.exp (-t)) =
        (fun t : ℝ => Real.log t * Real.exp (-t) - Real.log k * Real.exp (-t)) := by
      ext t; ring
    rw [heq, integral_sub hint1 hint0c, integral_const_mul,
      integral_exp_neg_Ioi_zero, mul_one, I1]
  rw [hsub, div_eq_inv_mul]

private lemma integral_log_sq_exp_mul {k : ℝ} (hk : 0 < k) :
    ∫ x in Ioi (0 : ℝ), Real.log x ^ 2 * Real.exp (-k * x) =
      (I2 - 2 * Real.log k * I1 + Real.log k ^ 2) / k := by
  have hcongr : ∫ x in Ioi (0 : ℝ), Real.log x ^ 2 * Real.exp (-k * x) =
      ∫ x in Ioi (0 : ℝ), (Real.log (k * x) - Real.log k) ^ 2 * Real.exp (-(k * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    rw [Real.log_mul hk.ne' hx0.ne']
    ring_nf
  rw [hcongr]
  have hscale := integral_comp_mul_left_Ioi
    (fun t : ℝ => (Real.log t - Real.log k) ^ 2 * Real.exp (-t)) (0 : ℝ) hk
  simp only [mul_zero, smul_eq_mul] at hscale
  rw [hscale]
  have hint2 : IntegrableOn (fun t : ℝ => Real.log t ^ 2 * Real.exp (-t)) (Ioi (0 : ℝ)) := by
    simpa using integrableOn_log_pow_exp 2 (by omega) one_pos
  have hint1 : IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioi (0 : ℝ)) := by
    simpa using integrableOn_log_pow_exp 1 (by omega) one_pos
  have hint0 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi (0 : ℝ)) := by
    simpa using integrableOn_log_pow_exp 0 (by omega) one_pos
  have hint1c : IntegrableOn (fun t : ℝ => (2 * Real.log k) * (Real.log t * Real.exp (-t)))
      (Ioi (0 : ℝ)) := hint1.const_mul _
  have hint0c : IntegrableOn (fun t : ℝ => Real.log k ^ 2 * Real.exp (-t)) (Ioi (0 : ℝ)) :=
    hint0.const_mul _
  have hint12 : IntegrableOn (fun t : ℝ => Real.log t ^ 2 * Real.exp (-t) -
      (2 * Real.log k) * (Real.log t * Real.exp (-t))) (Ioi (0 : ℝ)) :=
    hint2.sub hint1c
  have hexp : ∫ t in Ioi (0 : ℝ), (Real.log t - Real.log k) ^ 2 * Real.exp (-t) =
      I2 - 2 * Real.log k * I1 + Real.log k ^ 2 := by
    have heq : (fun t : ℝ => (Real.log t - Real.log k) ^ 2 * Real.exp (-t)) =
        (fun t : ℝ => (Real.log t ^ 2 * Real.exp (-t) -
          (2 * Real.log k) * (Real.log t * Real.exp (-t))) +
          Real.log k ^ 2 * Real.exp (-t)) := by
      ext t; ring
    rw [heq, integral_add hint12 hint0c, integral_sub hint2 hint1c,
      integral_const_mul, integral_const_mul, integral_exp_neg_Ioi_zero, mul_one, I1, I2]
  rw [hexp, div_eq_inv_mul]

/-! ### Step 2: Combinatorial identity and binomial expansion of `phi'` integrals -/

private lemma alternating_choose_div_sum (p : ℕ) (hp : 1 ≤ p) :
    (p : ℝ) * ∑ j ∈ Finset.range p, (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ) / ((j : ℝ) + 1) = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  simp only [Nat.succ_eq_add_one, add_tsub_cancel_right]
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ((n + 1 : ℕ) : ℝ) * ((-1 : ℝ) ^ j * (n.choose j : ℝ) / ((j : ℝ) + 1)) =
        (-1 : ℝ) ^ j * (((n + 1).choose (j + 1) : ℕ) : ℝ) := by
    intro j _
    have hchoose : (j + 1) * (n + 1).choose (j + 1) = (n + 1) * n.choose j := by
      simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq n j).symm
    have hchooseR : ((j : ℝ) + 1) * (((n + 1).choose (j + 1) : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ) * (n.choose j : ℝ) := by
      exact_mod_cast hchoose
    have hj : (j : ℝ) + 1 ≠ 0 := by positivity
    rw [mul_div_assoc', div_eq_iff hj]
    linear_combination (-1 : ℝ) ^ j * hchooseR.symm
  rw [Finset.sum_congr rfl hterm]
  have hbinom : (0 : ℝ) = ∑ m ∈ Finset.range (n + 2),
      (-1 : ℝ) ^ m * ((n + 1).choose m : ℝ) := by
    have h := add_pow (-1 : ℝ) (1 : ℝ) (n + 1)
    simp only [neg_add_cancel, zero_pow (Nat.succ_ne_zero n), one_pow, mul_one] at h
    exact h
  rw [Finset.sum_range_succ'] at hbinom
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one] at hbinom
  have hneg : ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (j + 1) * ((n + 1).choose (j + 1) : ℝ) =
      -(∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * ((n + 1).choose (j + 1) : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
  rw [hneg] at hbinom
  linarith

private lemma phi'_mul_eq_sum (p : ℕ) (hp : 1 ≤ p) (x : ℝ) (g : ℝ) :
    phi' p x * g = ∑ j ∈ Finset.range p,
      ((p : ℝ) * (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ)) *
        (g * Real.exp (-((j : ℝ) + 1) * x)) := by
  unfold phi'
  have hbinom : (1 - Real.exp (-x)) ^ (p - 1) =
      ∑ j ∈ Finset.range p, (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ) * Real.exp (-(j : ℝ) * x) := by
    have h := add_pow (-Real.exp (-x)) (1 : ℝ) (p - 1)
    rw [show -Real.exp (-x) + 1 = 1 - Real.exp (-x) by ring] at h
    have hp1 : (p - 1) + 1 = p := by omega
    rw [hp1] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, neg_pow, ← Real.exp_nat_mul]
    have hexp : (j : ℝ) * (-x) = -(j : ℝ) * x := by ring
    rw [hexp]
    ring
  rw [hbinom, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hexp : Real.exp (-(j : ℝ) * x) * Real.exp (-x) = Real.exp (-((j : ℝ) + 1) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (p : ℝ) * ((-1 : ℝ) ^ j * ((p - 1).choose j : ℝ) * Real.exp (-(j : ℝ) * x)) *
        Real.exp (-x) * g
      = ((p : ℝ) * (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ)) *
          (g * (Real.exp (-(j : ℝ) * x) * Real.exp (-x))) := by ring
    _ = ((p : ℝ) * (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ)) *
          (g * Real.exp (-((j : ℝ) + 1) * x)) := by rw [hexp]

private lemma integrableOn_phi'_log_pow (p : ℕ) (hp : 1 ≤ p) (m : ℕ) (hm : m ≤ 2) :
    IntegrableOn (fun x : ℝ => phi' p x * Real.log x ^ m) (Ioi (0 : ℝ)) := by
  have heq : (fun x : ℝ => phi' p x * Real.log x ^ m) =
      (fun x : ℝ => ∑ j ∈ Finset.range p,
        ((p : ℝ) * (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ)) *
          (Real.log x ^ m * Real.exp (-((j : ℝ) + 1) * x))) := by
    ext x
    exact phi'_mul_eq_sum p hp x (Real.log x ^ m)
  rw [heq]
  exact integrable_finsetSum _ fun j _ =>
    (integrableOn_log_pow_exp m hm (by positivity : (0 : ℝ) < (j : ℝ) + 1)).const_mul _

private lemma integral_phi'_log (p : ℕ) (hp : 1 ≤ p) :
    ∫ x in Ioi (0 : ℝ), phi' p x * Real.log x = I1 - (p : ℝ) * OMA.S_arxiv_2202_03713.c p := by
  have heq : (fun x : ℝ => phi' p x * Real.log x) =
      (fun x : ℝ => ∑ j ∈ Finset.range p,
        ((p : ℝ) * (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ)) *
          (Real.log x * Real.exp (-((j : ℝ) + 1) * x))) := by
    ext x
    exact phi'_mul_eq_sum p hp x (Real.log x)
  have hint : ∀ j ∈ Finset.range p,
      IntegrableOn (fun x : ℝ => ((p : ℝ) * (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ)) *
        (Real.log x * Real.exp (-((j : ℝ) + 1) * x))) (Ioi (0 : ℝ)) := by
    intro j _
    have h1 : IntegrableOn (fun x : ℝ => Real.log x * Real.exp (-((j : ℝ) + 1) * x))
        (Ioi (0 : ℝ)) := by
      simpa using integrableOn_log_pow_exp 1 (by omega) (by positivity : (0 : ℝ) < (j : ℝ) + 1)
    exact h1.const_mul _
  rw [heq, integral_finsetSum _ hint]
  have hsum : ∑ j ∈ Finset.range p,
      ∫ x in Ioi (0 : ℝ), ((p : ℝ) * (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ)) *
        (Real.log x * Real.exp (-((j : ℝ) + 1) * x)) =
      I1 * ((p : ℝ) * ∑ j ∈ Finset.range p,
          (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ) / ((j : ℝ) + 1)) -
        (p : ℝ) * OMA.S_arxiv_2202_03713.c p := by
    unfold OMA.S_arxiv_2202_03713.c
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_log_exp_mul (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
    have hadd : (1 : ℝ) + (j : ℝ) = (j : ℝ) + 1 := add_comm 1 (j : ℝ)
    rw [hadd]
    ring
  rw [hsum, alternating_choose_div_sum p hp, mul_one]

private lemma integral_phi'_log_sq (p : ℕ) (hp : 1 ≤ p) :
    ∫ x in Ioi (0 : ℝ), phi' p x * Real.log x ^ 2 =
      I2 - 2 * I1 * ((p : ℝ) * OMA.S_arxiv_2202_03713.c p) +
        (p : ℝ) * OMA.S_arxiv_2202_03713.w p := by
  have heq : (fun x : ℝ => phi' p x * Real.log x ^ 2) =
      (fun x : ℝ => ∑ j ∈ Finset.range p,
        ((p : ℝ) * (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ)) *
          (Real.log x ^ 2 * Real.exp (-((j : ℝ) + 1) * x))) := by
    ext x
    exact phi'_mul_eq_sum p hp x (Real.log x ^ 2)
  have hint : ∀ j ∈ Finset.range p,
      IntegrableOn (fun x : ℝ => ((p : ℝ) * (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ)) *
        (Real.log x ^ 2 * Real.exp (-((j : ℝ) + 1) * x))) (Ioi (0 : ℝ)) := by
    intro j _
    exact (integrableOn_log_pow_exp 2 (by omega)
      (by positivity : (0 : ℝ) < (j : ℝ) + 1)).const_mul _
  rw [heq, integral_finsetSum _ hint]
  have hsum : ∑ j ∈ Finset.range p,
      ∫ x in Ioi (0 : ℝ), ((p : ℝ) * (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ)) *
        (Real.log x ^ 2 * Real.exp (-((j : ℝ) + 1) * x)) =
      I2 * ((p : ℝ) * ∑ j ∈ Finset.range p,
          (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ) / ((j : ℝ) + 1)) -
        2 * I1 * ((p : ℝ) * OMA.S_arxiv_2202_03713.c p) +
        (p : ℝ) * OMA.S_arxiv_2202_03713.w p := by
    unfold OMA.S_arxiv_2202_03713.c OMA.S_arxiv_2202_03713.w
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_log_sq_exp_mul (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
    have hadd : (1 : ℝ) + (j : ℝ) = (j : ℝ) + 1 := add_comm 1 (j : ℝ)
    rw [hadd]
    ring
  rw [hsum, alternating_choose_div_sum p hp, mul_one]

/-! ### Step 3: Change of variables `u = phi_p(x)` and variance representation of `a_p` -/

private lemma hasDerivAt_phi (p : ℕ) (_hp : 1 ≤ p) (x : ℝ) :
    HasDerivAt (phi p) (phi' p x) x := by
  unfold phi phi'
  have h1 : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-x)) x := by
    have hneg : HasDerivAt (fun t : ℝ => -t) (-1) x := (hasDerivAt_id x).fun_neg
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * (-1)) x :=
      hneg.exp
    simpa using hexp.const_sub (1 : ℝ)
  simpa [mul_assoc] using h1.fun_pow p

private lemma phi'_pos (p : ℕ) (hp : 1 ≤ p) {x : ℝ} (hx : 0 < x) : 0 < phi' p x := by
  unfold phi'
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : 0 < 1 - Real.exp (-x) := by
    have : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  positivity

private lemma phi_strictMonoOn (p : ℕ) (hp : 1 ≤ p) : StrictMonoOn (phi p) (Ioi (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · exact (fun x _ => (hasDerivAt_phi p hp x).continuousAt.continuousWithinAt)
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_phi p hp x).deriv]
    exact phi'_pos p hp hx

private lemma phi_image_Ioi (p : ℕ) (hp : 1 ≤ p) : phi p '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : 0 < x := hx
    have hlt1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hpos : 0 < 1 - Real.exp (-x) := by linarith
    have hlt : 1 - Real.exp (-x) < 1 := by linarith [Real.exp_pos (-x)]
    exact ⟨pow_pos hpos p, pow_lt_one₀ hpos.le hlt (by omega)⟩
  · rintro ⟨hu0, hu1⟩
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp
    have hu_rpow_pos : 0 < u ^ (1 / (p : ℝ)) := Real.rpow_pos_of_pos hu0 _
    have hu_rpow_lt1 : u ^ (1 / (p : ℝ)) < 1 :=
      Real.rpow_lt_one hu0.le hu1 (by positivity)
    have h1sub_pos : 0 < 1 - u ^ (1 / (p : ℝ)) := by linarith
    have h1sub_lt1 : 1 - u ^ (1 / (p : ℝ)) < 1 := by linarith
    refine ⟨-Real.log (1 - u ^ (1 / (p : ℝ))), ?_, ?_⟩
    · simp only [mem_Ioi, neg_pos]
      exact Real.log_neg h1sub_pos h1sub_lt1
    · unfold phi
      rw [neg_neg, Real.exp_log h1sub_pos, sub_sub_cancel, ← Real.rpow_natCast,
        ← Real.rpow_mul hu0.le]
      have hcancel : (1 / (p : ℝ)) * (p : ℝ) = 1 := one_div_mul_cancel hp_pos.ne'
      rw [hcancel, Real.rpow_one]

private lemma h_comp_phi (p : ℕ) (hp : 1 ≤ p) {x : ℝ} (hx : 0 < x) :
    h p (phi p x) = Real.log x := by
  unfold h phi
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp
  have h1sub : 0 < 1 - Real.exp (-x) := by
    have : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul h1sub.le]
  have hcancel : (p : ℝ) * (1 / (p : ℝ)) = 1 := mul_one_div_cancel hp_pos.ne'
  rw [hcancel, Real.rpow_one, sub_sub_cancel, Real.log_exp, neg_neg]

private lemma integrableOn_h (p : ℕ) (hp : 1 ≤ p) :
    IntegrableOn (h p) (Ioo (0 : ℝ) 1) := by
  rw [← phi_image_Ioi p hp,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_phi p hp x).hasDerivWithinAt)
      (phi_strictMonoOn p hp).injOn]
  have h1 : IntegrableOn (fun x : ℝ => phi' p x * Real.log x) (Ioi (0 : ℝ)) := by
    simpa using integrableOn_phi'_log_pow p hp 1 (by omega)
  refine h1.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul, abs_of_pos (phi'_pos p hp hx), h_comp_phi p hp hx]

private lemma integrableOn_h_sq (p : ℕ) (hp : 1 ≤ p) :
    IntegrableOn (fun u => h p u ^ 2) (Ioo (0 : ℝ) 1) := by
  rw [← phi_image_Ioi p hp,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_phi p hp x).hasDerivWithinAt)
      (phi_strictMonoOn p hp).injOn]
  refine (integrableOn_phi'_log_pow p hp 2 (by omega)).congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul, abs_of_pos (phi'_pos p hp hx), h_comp_phi p hp hx]

private lemma integral_h (p : ℕ) (hp : 1 ≤ p) :
    ∫ u in Ioo (0 : ℝ) 1, h p u = I1 - (p : ℝ) * OMA.S_arxiv_2202_03713.c p := by
  rw [← phi_image_Ioi p hp,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_phi p hp x).hasDerivWithinAt)
      (phi_strictMonoOn p hp).injOn]
  rw [← integral_phi'_log p hp]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [smul_eq_mul, abs_of_pos (phi'_pos p hp hx), h_comp_phi p hp hx]

private lemma integral_h_sq (p : ℕ) (hp : 1 ≤ p) :
    ∫ u in Ioo (0 : ℝ) 1, h p u ^ 2 =
      I2 - 2 * I1 * ((p : ℝ) * OMA.S_arxiv_2202_03713.c p) +
        (p : ℝ) * OMA.S_arxiv_2202_03713.w p := by
  rw [← phi_image_Ioi p hp,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_phi p hp x).hasDerivWithinAt)
      (phi_strictMonoOn p hp).injOn]
  rw [← integral_phi'_log_sq p hp]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [smul_eq_mul, abs_of_pos (phi'_pos p hp hx), h_comp_phi p hp hx]

private lemma integral_const_Ioo_zero_one (c : ℝ) :
    ∫ _u in Ioo (0 : ℝ) 1, c = c := by
  rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo]
  simp

private lemma var01_eq_sub_sq {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo (0 : ℝ) 1))
    (hf2 : IntegrableOn (fun u => f u ^ 2) (Ioo (0 : ℝ) 1)) :
    var01 f = (∫ u in Ioo (0 : ℝ) 1, f u ^ 2) - (∫ u in Ioo (0 : ℝ) 1, f u) ^ 2 := by
  unfold var01
  set μ := ∫ t in Ioo (0 : ℝ) 1, f t
  have hconst : IntegrableOn (fun _ : ℝ => μ ^ 2) (Ioo (0 : ℝ) 1) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top.ne)
  have hfc : IntegrableOn (fun u : ℝ => (2 * μ) * f u) (Ioo (0 : ℝ) 1) :=
    hf.const_mul (2 * μ)
  have hf2sub : IntegrableOn (fun u : ℝ => f u ^ 2 - (2 * μ) * f u) (Ioo (0 : ℝ) 1) :=
    hf2.sub hfc
  have heq : (fun u : ℝ => (f u - μ) ^ 2) =
      (fun u : ℝ => (f u ^ 2 - (2 * μ) * f u) + μ ^ 2) := by
    ext u; ring
  rw [heq, integral_add hf2sub hconst, integral_sub hf2 hfc,
    integral_const_mul, integral_const_Ioo_zero_one]
  ring

private lemma var01_h (p : ℕ) (hp : 1 ≤ p) :
    var01 (h p) = (I2 - I1 ^ 2) + (p : ℝ) * OMA.S_arxiv_2202_03713.w p -
      (p : ℝ) ^ 2 * OMA.S_arxiv_2202_03713.c p ^ 2 := by
  rw [var01_eq_sub_sq (integrableOn_h p hp) (integrableOn_h_sq p hp),
    integral_h p hp, integral_h_sq p hp]
  ring

/-! ### Step 4: Strict monotonicity of `Psi` and contraction `0 < h_{p+1}' < h_p'` -/

private lemma hasDerivAt_logPsi {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt logPsi
      ((1 / ((1 - w) * (-Real.log (1 - w))) - 1 / w) +
        (1 / (w * (-Real.log w)) - 1 / (1 - w))) w := by
  have hw0 : 0 < w := hw.1
  have hw1 : w < 1 := hw.2
  have h1w0 : 0 < 1 - w := by linarith
  have h1w1 : 1 - w < 1 := by linarith
  have hlogw_neg : Real.log w < 0 := Real.log_neg hw0 hw1
  have hlog1w_neg : Real.log (1 - w) < 0 := Real.log_neg h1w0 h1w1
  have h1 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - w)) w := by
    have ha : HasDerivAt (fun t : ℝ => 1 - t) (-1) w := by
      simpa using (hasDerivAt_id w).const_sub (1 : ℝ)
    simpa [div_eq_mul_inv] using ha.log h1w0.ne'
  have h2 : HasDerivAt (fun t : ℝ => Real.log (-Real.log (1 - t)))
      (1 / ((1 - w) * (-Real.log (1 - w)))) w := by
    have hb : HasDerivAt (fun t : ℝ => -Real.log (1 - t)) (1 / (1 - w)) w := by
      simpa [neg_div] using h1.fun_neg
    have hc := hb.log (by linarith : -Real.log (1 - w) ≠ 0)
    have heq : (1 / (1 - w)) / (-Real.log (1 - w)) = 1 / ((1 - w) * (-Real.log (1 - w))) := by
      field_simp [h1w0.ne', (by linarith : -Real.log (1 - w) ≠ 0)]
    rwa [heq] at hc
  have h3 : HasDerivAt (fun t : ℝ => Real.log t) (1 / w) w := by
    simpa [one_div] using Real.hasDerivAt_log hw0.ne'
  have h4 : HasDerivAt (fun t : ℝ => Real.log (-Real.log t))
      (-1 / (w * (-Real.log w))) w := by
    have hb : HasDerivAt (fun t : ℝ => -Real.log t) (-1 / w) w := by
      simpa [neg_div] using h3.fun_neg
    have hc := hb.log (by linarith : -Real.log w ≠ 0)
    have heq : (-1 / w) / (-Real.log w) = -1 / (w * (-Real.log w)) := by
      field_simp [hw0.ne', (by linarith : -Real.log w ≠ 0)]
    rwa [heq] at hc
  have htot : HasDerivAt logPsi
      (-1 / (1 - w) + 1 / ((1 - w) * (-Real.log (1 - w))) - 1 / w -
        (-1 / (w * (-Real.log w)))) w :=
    ((h1.fun_add h2).fun_sub h3).fun_sub h4
  have hring : -1 / (1 - w) + 1 / ((1 - w) * (-Real.log (1 - w))) - 1 / w -
      (-1 / (w * (-Real.log w))) =
      (1 / ((1 - w) * (-Real.log (1 - w))) - 1 / w) +
        (1 / (w * (-Real.log w)) - 1 / (1 - w)) := by ring
  rwa [hring] at htot

private lemma strictMonoOn_Psi : StrictMonoOn Psi (Ioo (0 : ℝ) 1) := by
  have hlog_mono : StrictMonoOn logPsi (Ioo (0 : ℝ) 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo 0 1) ?_ ?_
    · exact fun w hw => (hasDerivAt_logPsi hw).continuousAt.continuousWithinAt
    · intro w hw
      rw [interior_Ioo] at hw
      rw [(hasDerivAt_logPsi hw).deriv]
      have hw0 : 0 < w := hw.1
      have hw1 : w < 1 := hw.2
      have h1w0 : 0 < 1 - w := by linarith
      have h1w1 : 1 - w < 1 := by linarith
      have hlogw_pos : 0 < -Real.log w := neg_pos.mpr (Real.log_neg hw0 hw1)
      have hlog1w_pos : 0 < -Real.log (1 - w) := neg_pos.mpr (Real.log_neg h1w0 h1w1)
      -- Key 3-line bound: `log(1/t) < 1/t - 1` for `t in (0, 1)` applied to `1 - w` and `w`.
      have hA : (1 - w) * (-Real.log (1 - w)) < w := by
        have hne : 1 / (1 - w) ≠ 1 := fun h => by
          rw [div_eq_one_iff_eq h1w0.ne'] at h
          linarith
        have hlt : Real.log (1 / (1 - w)) < 1 / (1 - w) - 1 :=
          Real.log_lt_sub_one_of_pos (by positivity) hne
        rw [one_div, Real.log_inv] at hlt
        have hmul := mul_lt_mul_of_pos_left hlt h1w0
        have hrhs : (1 - w) * ((1 - w)⁻¹ - 1) = w := by field_simp [h1w0.ne']; ring
        linarith
      have hB : w * (-Real.log w) < 1 - w := by
        have hne : 1 / w ≠ 1 := fun h => by
          rw [div_eq_one_iff_eq hw0.ne'] at h
          linarith
        have hlt : Real.log (1 / w) < 1 / w - 1 :=
          Real.log_lt_sub_one_of_pos (by positivity) hne
        rw [one_div, Real.log_inv] at hlt
        have hmul := mul_lt_mul_of_pos_left hlt hw0
        have hrhs : w * (w⁻¹ - 1) = 1 - w := by field_simp [hw0.ne']
        linarith
      have h1 : 1 / w < 1 / ((1 - w) * (-Real.log (1 - w))) :=
        one_div_lt_one_div_of_lt (mul_pos h1w0 hlog1w_pos) hA
      have h2 : 1 / (1 - w) < 1 / (w * (-Real.log w)) :=
        one_div_lt_one_div_of_lt (mul_pos hw0 hlogw_pos) hB
      linarith
  have hexp_eq : ∀ w ∈ Ioo (0 : ℝ) 1, Real.exp (logPsi w) = Psi w := by
    intro w hw
    have hw0 : 0 < w := hw.1
    have hw1 : w < 1 := hw.2
    have h1w0 : 0 < 1 - w := by linarith
    have h1w1 : 1 - w < 1 := by linarith
    have hlogw_pos : 0 < -Real.log w := neg_pos.mpr (Real.log_neg hw0 hw1)
    have hlog1w_pos : 0 < -Real.log (1 - w) := neg_pos.mpr (Real.log_neg h1w0 h1w1)
    unfold logPsi Psi
    rw [Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log h1w0, Real.exp_log hlog1w_pos,
      Real.exp_log hw0, Real.exp_log hlogw_pos, div_div]
  intro x hx y hy hxy
  rw [← hexp_eq x hx, ← hexp_eq y hy]
  exact Real.exp_lt_exp.mpr (hlog_mono hx hy hxy)

private lemma hasDerivAt_h (p : ℕ) (hp : 1 ≤ p) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (h p) (Psi (1 - u ^ (1 / (p : ℝ))) / (u * (-Real.log u))) u := by
  have hu0 : 0 < u := hu.1
  have hu1 : u < 1 := hu.2
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp
  have hup_pos : 0 < u ^ (1 / (p : ℝ)) := Real.rpow_pos_of_pos hu0 _
  have hup_lt1 : u ^ (1 / (p : ℝ)) < 1 := Real.rpow_lt_one hu0.le hu1 (by positivity)
  have h1u_pos : 0 < 1 - u ^ (1 / (p : ℝ)) := by linarith
  have h1u_lt1 : 1 - u ^ (1 / (p : ℝ)) < 1 := by linarith
  have hlog_neg : Real.log (1 - u ^ (1 / (p : ℝ))) < 0 := Real.log_neg h1u_pos h1u_lt1
  have hlogu_neg : Real.log u < 0 := Real.log_neg hu0 hu1
  have h1 : HasDerivAt (fun t : ℝ => t ^ (1 / (p : ℝ)))
      ((1 / (p : ℝ)) * u ^ (1 / (p : ℝ) - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu0.ne')
  have h1' : HasDerivAt (fun t : ℝ => 1 - t ^ (1 / (p : ℝ)))
      (-(u ^ (1 / (p : ℝ)) / ((p : ℝ) * u))) u := by
    have hsub := h1.const_sub (1 : ℝ)
    have heq : -((1 / (p : ℝ)) * u ^ (1 / (p : ℝ) - 1)) =
        -(u ^ (1 / (p : ℝ)) / ((p : ℝ) * u)) := by
      rw [Real.rpow_sub hu0, Real.rpow_one]
      ring
    rwa [heq] at hsub
  have h2 : HasDerivAt (fun t : ℝ => -Real.log (1 - t ^ (1 / (p : ℝ))))
      (u ^ (1 / (p : ℝ)) / ((p : ℝ) * u * (1 - u ^ (1 / (p : ℝ))))) u := by
    have hlog := (h1'.log h1u_pos.ne').fun_neg
    have heq : -(-(u ^ (1 / (p : ℝ)) / ((p : ℝ) * u)) / (1 - u ^ (1 / (p : ℝ)))) =
        u ^ (1 / (p : ℝ)) / ((p : ℝ) * u * (1 - u ^ (1 / (p : ℝ)))) := by
      field_simp [hp_pos.ne', hu0.ne', h1u_pos.ne']
    rwa [heq] at hlog
  have h3 : HasDerivAt (h p)
      ((u ^ (1 / (p : ℝ)) / ((p : ℝ) * u * (1 - u ^ (1 / (p : ℝ))))) /
        (-Real.log (1 - u ^ (1 / (p : ℝ))))) u :=
    h2.log (by linarith : -Real.log (1 - u ^ (1 / (p : ℝ))) ≠ 0)
  have heq : (u ^ (1 / (p : ℝ)) / ((p : ℝ) * u * (1 - u ^ (1 / (p : ℝ))))) /
      (-Real.log (1 - u ^ (1 / (p : ℝ)))) =
      Psi (1 - u ^ (1 / (p : ℝ))) / (u * (-Real.log u)) := by
    unfold Psi
    rw [sub_sub_cancel, Real.log_rpow hu0]
    field_simp [hp_pos.ne', hu0.ne', h1u_pos.ne', hlogu_neg.ne, hlog_neg.ne]
  rwa [heq] at h3

private lemma strictMonoOn_h (p : ℕ) (hp : 1 ≤ p) : StrictMonoOn (h p) (Ioo (0 : ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 1) ?_ ?_
  · exact fun u hu => (hasDerivAt_h p hp hu).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioo] at hu
    rw [(hasDerivAt_h p hp hu).deriv]
    have hu0 : 0 < u := hu.1
    have hu1 : u < 1 := hu.2
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp
    have hup_pos : 0 < u ^ (1 / (p : ℝ)) := Real.rpow_pos_of_pos hu0 _
    have hup_lt1 : u ^ (1 / (p : ℝ)) < 1 := Real.rpow_lt_one hu0.le hu1 (by positivity)
    have h1u_pos : 0 < 1 - u ^ (1 / (p : ℝ)) := by linarith
    have h1u_lt1 : 1 - u ^ (1 / (p : ℝ)) < 1 := by linarith
    have hlogu_pos : 0 < -Real.log u := neg_pos.mpr (Real.log_neg hu0 hu1)
    have hPsi_pos : 0 < Psi (1 - u ^ (1 / (p : ℝ))) := by
      unfold Psi
      rw [sub_sub_cancel]
      have h1 : 0 < -Real.log (u ^ (1 / (p : ℝ))) := neg_pos.mpr (Real.log_neg hup_pos hup_lt1)
      have h2 : 0 < -Real.log (1 - u ^ (1 / (p : ℝ))) := neg_pos.mpr (Real.log_neg h1u_pos h1u_lt1)
      positivity
    exact div_pos hPsi_pos (mul_pos hu0 hlogu_pos)

private lemma strictMonoOn_h_sub_h_succ (p : ℕ) (hp : 1 ≤ p) :
    StrictMonoOn (fun u => h p u - h (p + 1) u) (Ioo (0 : ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 1) ?_ ?_
  · exact fun u hu =>
      ((hasDerivAt_h p hp hu).fun_sub
        (hasDerivAt_h (p + 1) (by omega) hu)).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioo] at hu
    have hderiv := (hasDerivAt_h p hp hu).fun_sub (hasDerivAt_h (p + 1) (by omega) hu)
    rw [hderiv.deriv, sub_pos]
    have hu0 : 0 < u := hu.1
    have hu1 : u < 1 := hu.2
    have hlogu_pos : 0 < -Real.log u := neg_pos.mpr (Real.log_neg hu0 hu1)
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp
    have hexp_lt : 1 / ((p + 1 : ℕ) : ℝ) < 1 / (p : ℝ) := by
      refine one_div_lt_one_div_of_lt hp_pos ?_
      exact_mod_cast Nat.lt_succ_self p
    have hrpow_lt : u ^ (1 / (p : ℝ)) < u ^ (1 / ((p + 1 : ℕ) : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_gt hu0 hu1 hexp_lt
    have hw_lt : 1 - u ^ (1 / ((p + 1 : ℕ) : ℝ)) < 1 - u ^ (1 / (p : ℝ)) := by linarith
    have hw1_mem : 1 - u ^ (1 / ((p + 1 : ℕ) : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
      have ha : 0 < u ^ (1 / ((p + 1 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hu0 _
      have hb : u ^ (1 / ((p + 1 : ℕ) : ℝ)) < 1 :=
        Real.rpow_lt_one hu0.le hu1 (by positivity)
      exact ⟨by linarith, by linarith⟩
    have hw2_mem : 1 - u ^ (1 / (p : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
      have ha : 0 < u ^ (1 / (p : ℝ)) := Real.rpow_pos_of_pos hu0 _
      have hb : u ^ (1 / (p : ℝ)) < 1 := Real.rpow_lt_one hu0.le hu1 (by positivity)
      exact ⟨by linarith, by linarith⟩
    exact div_lt_div_of_pos_right (strictMonoOn_Psi hw1_mem hw2_mem hw_lt)
      (mul_pos hu0 hlogu_pos)

/-! ### Step 5: One-variable Chebyshev variance comparison -/

private lemma integral_pos_of_continuousOn_nonneg_ne_zero {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ioo (0 : ℝ) 1))
    (hg_int : IntegrableOn g (Ioo (0 : ℝ) 1))
    (hg_nn : ∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ g u)
    {u0 : ℝ} (hu0 : u0 ∈ Ioo (0 : ℝ) 1) (hgu0 : g u0 ≠ 0) :
    0 < ∫ u in Ioo (0 : ℝ) 1, g u := by
  have hae : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hg_nn u hu
  rw [setIntegral_pos_iff_support_of_nonneg_ae hae hg_int]
  have hopen : IsOpen (Function.support g ∩ Ioo (0 : ℝ) 1) := by
    have hpre : Function.support g ∩ Ioo (0 : ℝ) 1 =
        (Ioo (0 : ℝ) 1) ∩ g ⁻¹' ({0}ᶜ) := by
      ext u
      simp [Function.mem_support, and_comm]
    rw [hpre]
    exact hg_cont.isOpen_inter_preimage isOpen_Ioo isClosed_singleton.isOpen_compl
  exact hopen.measure_pos volume ⟨u0, hgu0, hu0⟩

private lemma exists_eq_mean_of_strictMonoOn {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Ioo (0 : ℝ) 1))
    (hf_mono : StrictMonoOn f (Ioo (0 : ℝ) 1))
    (hf_int : IntegrableOn f (Ioo (0 : ℝ) 1)) :
    ∃ ustar ∈ Ioo (0 : ℝ) 1, f ustar = ∫ t in Ioo (0 : ℝ) 1, f t := by
  set μ := ∫ t in Ioo (0 : ℝ) 1, f t
  have hconst_int : IntegrableOn (fun _ : ℝ => μ) (Ioo (0 : ℝ) 1) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top.ne)
  have h13 : (1 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have h23 : (2 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hlt12 : f (1 / 3) < f (2 / 3) := hf_mono h13 h23 (by norm_num)
  have hex_lt : ∃ u1 ∈ Ioo (0 : ℝ) 1, f u1 < μ := by
    by_contra hall
    push Not at hall
    have hne : ∃ u0 ∈ Ioo (0 : ℝ) 1, f u0 - μ ≠ 0 := by
      by_cases h : f (1 / 3) = μ
      · exact ⟨2 / 3, h23, by linarith⟩
      · exact ⟨1 / 3, h13, sub_ne_zero.mpr h⟩
    obtain ⟨u0, hu0, hne0⟩ := hne
    have hsub_cont : ContinuousOn (fun u => f u - μ) (Ioo (0 : ℝ) 1) :=
      hf_cont.sub continuousOn_const
    have hsub_int : IntegrableOn (fun u => f u - μ) (Ioo (0 : ℝ) 1) :=
      hf_int.sub hconst_int
    have hpos := integral_pos_of_continuousOn_nonneg_ne_zero
      hsub_cont hsub_int (fun u hu => sub_nonneg.mpr (hall u hu)) hu0 hne0
    rw [integral_sub hf_int hconst_int, integral_const_Ioo_zero_one, sub_self] at hpos
    exact lt_irrefl 0 hpos
  have hex_gt : ∃ u2 ∈ Ioo (0 : ℝ) 1, μ < f u2 := by
    by_contra hall
    push Not at hall
    have hne : ∃ u0 ∈ Ioo (0 : ℝ) 1, μ - f u0 ≠ 0 := by
      by_cases h : f (1 / 3) = μ
      · exact ⟨2 / 3, h23, by linarith⟩
      · exact ⟨1 / 3, h13, fun heq => h (by linarith)⟩
    obtain ⟨u0, hu0, hne0⟩ := hne
    have hsub_cont : ContinuousOn (fun u => μ - f u) (Ioo (0 : ℝ) 1) :=
      continuousOn_const.sub hf_cont
    have hsub_int : IntegrableOn (fun u => μ - f u) (Ioo (0 : ℝ) 1) :=
      hconst_int.sub hf_int
    have hpos := integral_pos_of_continuousOn_nonneg_ne_zero
      hsub_cont hsub_int (fun u hu => sub_nonneg.mpr (hall u hu)) hu0 hne0
    rw [integral_sub hconst_int hf_int, integral_const_Ioo_zero_one, sub_self] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨u1, hu1, hfu1⟩ := hex_lt
  obtain ⟨u2, hu2, hfu2⟩ := hex_gt
  have hu12 : u1 ≤ u2 := by
    by_contra h
    push Not at h
    linarith [hf_mono hu2 hu1 h]
  have hsub : Icc u1 u2 ⊆ Ioo (0 : ℝ) 1 := fun u hu =>
    ⟨lt_of_lt_of_le hu1.1 hu.1, lt_of_le_of_lt hu.2 hu2.2⟩
  have hmem : μ ∈ Icc (f u1) (f u2) := ⟨hfu1.le, hfu2.le⟩
  obtain ⟨ustar, hustar, hfustar⟩ :=
    intermediate_value_Icc hu12 (hf_cont.mono hsub) hmem
  exact ⟨ustar, hsub hustar, hfustar⟩

private lemma var01_lt_var01_add {f d : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Ioo (0 : ℝ) 1))
    (hd_cont : ContinuousOn d (Ioo (0 : ℝ) 1))
    (hf_mono : StrictMonoOn f (Ioo (0 : ℝ) 1))
    (hd_mono : StrictMonoOn d (Ioo (0 : ℝ) 1))
    (hf_int : IntegrableOn f (Ioo (0 : ℝ) 1))
    (hf2_int : IntegrableOn (fun u => f u ^ 2) (Ioo (0 : ℝ) 1))
    (hd_int : IntegrableOn d (Ioo (0 : ℝ) 1))
    (hd2_int : IntegrableOn (fun u => d u ^ 2) (Ioo (0 : ℝ) 1)) :
    var01 f < var01 (fun u => f u + d u) := by
  set μf := ∫ t in Ioo (0 : ℝ) 1, f t
  set μd := ∫ t in Ioo (0 : ℝ) 1, d t
  have hconst_int : ∀ c : ℝ, IntegrableOn (fun _ : ℝ => c) (Ioo (0 : ℝ) 1) := fun _ =>
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top.ne)
  have hfd_int : IntegrableOn (fun u => f u * d u) (Ioo (0 : ℝ) 1) := by
    have hdom : IntegrableOn (fun u => (f u ^ 2 + d u ^ 2) / 2) (Ioo (0 : ℝ) 1) :=
      (hf2_int.add hd2_int).div_const 2
    refine hdom.mono' ((hf_cont.mul hd_cont).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u _
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|f u| - |d u|), sq_abs (f u), sq_abs (d u)]
  have hfc_int : IntegrableOn (fun u => (f u - μf) ^ 2) (Ioo (0 : ℝ) 1) := by
    have heq : (fun u => (f u - μf) ^ 2) = (fun u => f u ^ 2 - (2 * μf) * f u + μf ^ 2) := by
      ext u; ring
    rw [heq]
    exact (hf2_int.sub (hf_int.const_mul _)).add (hconst_int _)
  have hdc_int : IntegrableOn (fun u => (d u - μd) ^ 2) (Ioo (0 : ℝ) 1) := by
    have heq : (fun u => (d u - μd) ^ 2) = (fun u => d u ^ 2 - (2 * μd) * d u + μd ^ 2) := by
      ext u; ring
    rw [heq]
    exact (hd2_int.sub (hd_int.const_mul _)).add (hconst_int _)
  have hcov_int : IntegrableOn (fun u => (f u - μf) * (d u - μd)) (Ioo (0 : ℝ) 1) := by
    have heq : (fun u => (f u - μf) * (d u - μd)) =
        (fun u => f u * d u - μd * f u - μf * d u + μf * μd) := by
      ext u; ring
    rw [heq]
    exact ((hfd_int.sub (hf_int.const_mul _)).sub (hd_int.const_mul _)).add (hconst_int _)
  have hcov2_int : IntegrableOn (fun u => 2 * ((f u - μf) * (d u - μd))) (Ioo (0 : ℝ) 1) :=
    hcov_int.const_mul 2
  have hfc_cov2_int : IntegrableOn (fun u => (f u - μf) ^ 2 + 2 * ((f u - μf) * (d u - μd)))
      (Ioo (0 : ℝ) 1) :=
    hfc_int.add hcov2_int
  have hmean_add : ∫ t in Ioo (0 : ℝ) 1, (f t + d t) = μf + μd :=
    integral_add hf_int hd_int
  have hvar_expand : var01 (fun u => f u + d u) =
      var01 f + 2 * (∫ u in Ioo (0 : ℝ) 1, (f u - μf) * (d u - μd)) +
        ∫ u in Ioo (0 : ℝ) 1, (d u - μd) ^ 2 := by
    unfold var01
    rw [hmean_add]
    have heq : (fun u => (f u + d u - (μf + μd)) ^ 2) =
        (fun u => ((f u - μf) ^ 2 + 2 * ((f u - μf) * (d u - μd))) + (d u - μd) ^ 2) := by
      ext u; ring
    rw [heq, integral_add hfc_cov2_int hdc_int, integral_add hfc_int hcov2_int,
      integral_const_mul]
  -- Term 1: `Var(d) > 0` because `d` is strictly increasing and continuous.
  have hvard_pos : 0 < ∫ u in Ioo (0 : ℝ) 1, (d u - μd) ^ 2 := by
    have h13 : (1 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
    have h23 : (2 / 3 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
    have hlt : d (1 / 3) < d (2 / 3) := hd_mono h13 h23 (by norm_num)
    have hne : ∃ u0 ∈ Ioo (0 : ℝ) 1, (d u0 - μd) ^ 2 ≠ 0 := by
      by_cases h : d (1 / 3) = μd
      · exact ⟨2 / 3, h23, pow_ne_zero 2 (by linarith)⟩
      · exact ⟨1 / 3, h13, pow_ne_zero 2 (sub_ne_zero.mpr h)⟩
    obtain ⟨u0, hu0, hne0⟩ := hne
    exact integral_pos_of_continuousOn_nonneg_ne_zero
      ((hd_cont.sub continuousOn_const).pow 2) hdc_int
      (fun u _ => sq_nonneg _) hu0 hne0
  -- Term 2: `Cov(f, d) >= 0` via `f(u*) = mean(f)` and pointwise nonnegativity.
  have hcov_nn : 0 ≤ ∫ u in Ioo (0 : ℝ) 1, (f u - μf) * (d u - μd) := by
    obtain ⟨ustar, hustar, hfustar⟩ := exists_eq_mean_of_strictMonoOn hf_cont hf_mono hf_int
    have hshift : ∫ u in Ioo (0 : ℝ) 1, (f u - μf) * (d u - μd) =
        ∫ u in Ioo (0 : ℝ) 1, (f u - f ustar) * (d u - d ustar) := by
      have heq : (fun u => (f u - μf) * (d u - μd)) =
          (fun u => (f u - f ustar) * (d u - d ustar) +
            (d ustar - μd) * (f u - μf)) := by
        ext u; rw [hfustar]; ring
      have hterm1 : IntegrableOn (fun u => (f u - f ustar) * (d u - d ustar)) (Ioo (0 : ℝ) 1) := by
        have h1 : (fun u => (f u - f ustar) * (d u - d ustar)) =
            (fun u => f u * d u - d ustar * f u - f ustar * d u + f ustar * d ustar) := by
          ext u; ring
        rw [h1]
        exact ((hfd_int.sub (hf_int.const_mul _)).sub (hd_int.const_mul _)).add (hconst_int _)
      have hterm2 : IntegrableOn (fun u => (d ustar - μd) * (f u - μf)) (Ioo (0 : ℝ) 1) :=
        (hf_int.sub (hconst_int _)).const_mul _
      rw [heq, integral_add hterm1 hterm2, integral_const_mul,
        integral_sub hf_int (hconst_int _), integral_const_Ioo_zero_one, sub_self, mul_zero,
        add_zero]
    rw [hshift]
    refine setIntegral_nonneg measurableSet_Ioo fun u hu => ?_
    rcases le_total u ustar with hle | hle
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hf_mono.monotoneOn hu hustar hle))
        (sub_nonpos.mpr (hd_mono.monotoneOn hu hustar hle))
    · exact mul_nonneg
        (sub_nonneg.mpr (hf_mono.monotoneOn hustar hu hle))
        (sub_nonneg.mpr (hd_mono.monotoneOn hustar hu hle))
  linarith

end OMA.P_arxiv_2202_03713

/-- **Doumas, Conjecture 2.5.** The sequence `a_p = pi^2/6 + p w_p - p^2 c_p^2` is strictly
decreasing for all integers `p >= 1`. -/
theorem OMA.solution : type_of% @OMA.S_arxiv_2202_03713.main := by
  intro p hp
  open OMA.P_arxiv_2202_03713 in
  have hvar_lt : var01 (h (p + 1)) < var01 (h p) := by
    have hf_cont : ContinuousOn (h (p + 1)) (Ioo (0 : ℝ) 1) :=
      fun u hu => (hasDerivAt_h (p + 1) (by omega) hu).continuousAt.continuousWithinAt
    have hp_cont : ContinuousOn (h p) (Ioo (0 : ℝ) 1) :=
      fun u hu => (hasDerivAt_h p hp hu).continuousAt.continuousWithinAt
    have hd_cont : ContinuousOn (fun u => h p u - h (p + 1) u) (Ioo (0 : ℝ) 1) :=
      hp_cont.sub hf_cont
    have hf_int : IntegrableOn (h (p + 1)) (Ioo (0 : ℝ) 1) := integrableOn_h (p + 1) (by omega)
    have hf2_int : IntegrableOn (fun u => h (p + 1) u ^ 2) (Ioo (0 : ℝ) 1) :=
      integrableOn_h_sq (p + 1) (by omega)
    have hp_int : IntegrableOn (h p) (Ioo (0 : ℝ) 1) := integrableOn_h p hp
    have hp2_int : IntegrableOn (fun u => h p u ^ 2) (Ioo (0 : ℝ) 1) := integrableOn_h_sq p hp
    have hd_int : IntegrableOn (fun u => h p u - h (p + 1) u) (Ioo (0 : ℝ) 1) :=
      hp_int.sub hf_int
    have hd2_int : IntegrableOn (fun u => (h p u - h (p + 1) u) ^ 2) (Ioo (0 : ℝ) 1) := by
      have hdom : IntegrableOn (fun u => 2 * (h p u ^ 2 + h (p + 1) u ^ 2)) (Ioo (0 : ℝ) 1) :=
        (hp2_int.add hf2_int).const_mul 2
      refine hdom.mono' ((hd_cont.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (h p u + h (p + 1) u)]
    have hlt := var01_lt_var01_add hf_cont hd_cont
      (strictMonoOn_h (p + 1) (by omega)) (strictMonoOn_h_sub_h_succ p hp)
      hf_int hf2_int hd_int hd2_int
    have hsum : (fun u => h (p + 1) u + (h p u - h (p + 1) u)) = h p := by
      ext u; ring
    rwa [hsum] at hlt
  rw [OMA.P_arxiv_2202_03713.var01_h (p + 1) (by omega),
    OMA.P_arxiv_2202_03713.var01_h p hp] at hvar_lt
  unfold OMA.S_arxiv_2202_03713.a
  linarith
