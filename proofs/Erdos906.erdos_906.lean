import FormalConjectures.ErdosProblems.«906»
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! A square-supported factorial series for Erdős Problem 906. The use of
sparse Taylor support is inspired by ZhiJie He’s construction.
https://erdosproblems.ai/wiki/problems/analysis/E0906/claims/2026_09_17_he
-/

-- Credit: @MrSeizy

open Filter Set Metric
open scoped Topology BigOperators NNReal ENNReal

namespace OMA
noncomputable section

-- Entire convergence and differentiated coefficients
private def weight (m : ℕ) : ℝ := (m.factorial : ℝ) ^ (3 / 4 : ℝ)

private def rawCoeff (m : ℕ) : ℝ := (m.factorial : ℝ) ^ (-(1 / 4) : ℝ)

private def square (m : ℕ) : Prop := m.sqrt ^ 2 = m

private instance (m : ℕ) : Decidable (square m) := inferInstanceAs (Decidable (m.sqrt ^ 2 = m))

private def sparseCoeff (m : ℕ) : ℂ :=
  if square m then (rawCoeff m : ℂ) else 0

private lemma weight_pos (m : ℕ) : 0 < weight m := by
  unfold weight
  positivity

private lemma rawCoeff_pos (m : ℕ) : 0 < rawCoeff m := by
  unfold rawCoeff
  positivity

private lemma weight_succ (m : ℕ) :
    weight (m + 1) = ((m : ℝ) + 1) ^ (3 / 4 : ℝ) * weight m := by
  simp only [weight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [Real.mul_rpow (by positivity) (by positivity)]

private lemma rawCoeff_succ (m : ℕ) :
    rawCoeff (m + 1) = ((m : ℝ) + 1) ^ (-(1 / 4) : ℝ) * rawCoeff m := by
  simp only [rawCoeff, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [Real.mul_rpow (by positivity) (by positivity)]

private lemma factorial_mul_rawCoeff (m : ℕ) :
    (m.factorial : ℝ) * rawCoeff m = weight m := by
  have hp : 0 < (m.factorial : ℝ) := by positivity
  rw [rawCoeff, weight, mul_comm, ← Real.rpow_add_one hp.ne']
  norm_num

private lemma summable_rawCoeff_mul_pow {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun m : ℕ => rawCoeff m * r ^ m) := by
  by_cases h : r = 0
  · subst r
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp [zero_pow (by simpa using hk : k ≠ 0)]
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
  · exact Eventually.of_forall fun m => mul_ne_zero (rawCoeff_pos m).ne' (pow_ne_zero _ h)
  · have hlim : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
      by simpa [Function.comp_def] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    have hpow := (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp hlim
    have hratio : (fun m : ℕ => ‖rawCoeff (m + 1) * r ^ (m + 1)‖ / ‖rawCoeff m * r ^ m‖) =
        fun m : ℕ => ((m : ℝ) + 1) ^ (-(1 / 4) : ℝ) * r := by
      funext m
      have h₁ : 0 ≤ rawCoeff (m + 1) * r ^ (m + 1) :=
        mul_nonneg (rawCoeff_pos _).le (pow_nonneg hr _)
      have h₀ : 0 ≤ rawCoeff m * r ^ m := mul_nonneg (rawCoeff_pos _).le (pow_nonneg hr _)
      rw [Real.norm_of_nonneg h₁, Real.norm_of_nonneg h₀, rawCoeff_succ, pow_succ]
      have hm := (rawCoeff_pos m).ne'
      have hp := pow_ne_zero m h
      field_simp
    rw [hratio]
    simpa only [Function.comp_def, zero_mul] using hpow.mul_const r

private def sparseSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ sparseCoeff

private def sparseFunction : ℂ → ℂ := sparseSeries.sum

private lemma sparseSeries_radius : sparseSeries.radius = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  apply sparseSeries.le_radius_of_summable_norm
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_)
    (summable_rawCoeff_mul_pow r.coe_nonneg)
  rw [sparseSeries, FormalMultilinearSeries.ofScalars_norm]
  gcongr
  unfold sparseCoeff
  split_ifs
  · rw [Complex.norm_real, Real.norm_of_nonneg (rawCoeff_pos m).le]
  · simpa using (rawCoeff_pos m).le

private lemma sparseFunction_hasSeries :
    HasFPowerSeriesOnBall sparseFunction sparseSeries 0 ⊤ := by
  rw [← sparseSeries_radius]
  apply sparseSeries.hasFPowerSeriesOnBall
  rw [sparseSeries_radius]
  simp

private lemma sparseFunction_diff : Differentiable ℂ sparseFunction := by
  intro z
  apply (sparseFunction_hasSeries.analyticAt_of_mem ?_).differentiableAt
  exact edist_lt_top _ _

private lemma sparseFunction_iterated_at_zero (m : ℕ) :
    iteratedDeriv m sparseFunction 0 = (m.factorial : ℂ) * sparseCoeff m := by
  rw [iteratedDeriv_eq_iteratedFDeriv, ← sparseFunction_hasSeries.factorial_smul 1 m]
  simp [sparseSeries, nsmul_eq_mul]

private lemma sparseFunction_derivative_hasSum (n : ℕ) (z : ℂ) :
    HasSum (fun k : ℕ => if square (n + k) then
      ((weight (n + k) / (k.factorial : ℝ) : ℝ) : ℂ) * z ^ k else 0)
      (iteratedDeriv n sparseFunction z) := by
  classical
  have hd : Differentiable ℂ (iteratedDeriv n sparseFunction) :=
    (sparseFunction_diff.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by simp)
  refine (Complex.hasSum_taylorSeries_of_entire hd 0 z).congr_fun fun k => ?_
  have hiter : iteratedDeriv k (iteratedDeriv n sparseFunction) =
      iteratedDeriv (n + k) sparseFunction := by
    simp only [iteratedDeriv_eq_iterate]
    rw [Nat.add_comm, Function.iterate_add_apply]
  simp only [sub_zero, smul_eq_mul, hiter, sparseFunction_iterated_at_zero, sparseCoeff]
  split_ifs with h
  · have hm : (↑(n + k).factorial : ℂ) * (rawCoeff (n + k) : ℂ) =
        (weight (n + k) : ℂ) := by exact_mod_cast factorial_mul_rawCoeff (n + k)
    rw [hm]
    push_cast
    ring
  · simp

-- Crossings of adjacent square terms
private def scale (x : ℝ) : ℝ := x ^ (3 / 4 : ℝ)

private def stepRadius (n m : ℕ) : ℝ := ((m : ℝ) - n) / scale m

private def gap (j : ℕ) : ℕ := 2 * j + 1

private lemma square_succ_sub (j : ℕ) : (j + 1) ^ 2 - j ^ 2 = gap j := by
  have h : (j + 1) ^ 2 = j ^ 2 + gap j := by unfold gap; ring
  omega

private lemma square_pred_add_le {j : ℕ} (hj : 0 < j) : (j - 1) ^ 2 + j ≤ j ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  change (k + 1 - 1) ^ 2 + (k + 1) ≤ (k + 1) ^ 2
  rw [Nat.add_sub_cancel]
  nlinarith

private lemma scale_pos {x : ℝ} (hx : 0 < x) : 0 < scale x :=
  Real.rpow_pos_of_pos hx _

private lemma scale_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    scale a ≤ scale b :=
  Real.rpow_le_rpow ha hab (by norm_num)

private lemma scale_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    scale (a * b) = scale a * scale b := Real.mul_rpow ha hb

private lemma scale_le_self {a : ℝ} (ha : 1 ≤ a) : scale a ≤ a :=
  Real.rpow_le_self_of_one_le ha (by norm_num)

private lemma scale_square {a : ℝ} (ha : 0 < a) :
    scale (a ^ 2) = a * Real.sqrt a := by
  rw [scale, ← Real.rpow_natCast_mul ha.le, Real.sqrt_eq_rpow,
    show (2 : ℕ) * (3 / 4 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.rpow_add_one ha.ne', mul_comm]

private lemma stepRadius_pos {n a : ℕ} (h : n < a) : 0 < stepRadius n a := by
  exact div_pos (sub_pos.mpr (by exact_mod_cast h))
    (scale_pos (by exact_mod_cast (show 0 < a by omega)))

private lemma stepRadius_sub_le {n a b : ℕ} (ha : 0 < a) (hn : n ≤ a) (hab : a ≤ b) :
    stepRadius n b - stepRadius n a ≤ ((b : ℝ) - a) / scale a := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hn' : (n : ℝ) ≤ a := by exact_mod_cast hn
  have h := div_le_div_of_nonneg_left (show 0 ≤ (b : ℝ) - n by linarith)
    (scale_pos ha') (scale_le ha'.le hb')
  unfold stepRadius
  calc
    _ ≤ ((b : ℝ) - n) / scale a - ((a : ℝ) - n) / scale a := sub_le_sub_right h _
    _ = _ := by ring

private lemma stepRadius_sub_ge {n a b : ℕ} (ha : 0 < a) (hn : n ≤ a) (hab : a ≤ b) :
    (n : ℝ) / b * (((b : ℝ) - a) / scale a) ≤ stepRadius n b - stepRadius n a := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hb' : (0 : ℝ) < b := ha'.trans_le hab'
  have hn' : (n : ℝ) ≤ a := by exact_mod_cast hn
  have hs : scale (b : ℝ) ≤ scale a * ((b : ℝ) / a) := by
    calc
      scale (b : ℝ) = scale ((a : ℝ) * ((b : ℝ) / a)) := by
        congr 1
        field_simp
      _ = scale a * scale ((b : ℝ) / a) := scale_mul _ _ ha'.le (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (scale_le_self ((one_le_div ha').mpr hab'))
        (scale_pos ha').le
  have h := div_le_div_of_nonneg_left (show 0 ≤ (b : ℝ) - n by linarith)
    (scale_pos hb') hs
  unfold stepRadius
  refine le_trans (le_of_eq ?_) (sub_le_sub_right h _)
  field_simp
  ring

private lemma stepRadius_mono {n a b : ℕ} (ha : 0 < a) (hn : n ≤ a) (hab : a ≤ b) :
    stepRadius n a ≤ stepRadius n b := by
  have h : 0 ≤ (n : ℝ) / b * (((b : ℝ) - a) / scale a) := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact mul_nonneg (by positivity) (div_nonneg (sub_nonneg.mpr this) (scale_pos (by exact_mod_cast ha)).le)
  linarith [h.trans (stepRadius_sub_ge ha hn hab)]

private lemma exists_stepRadius_ge (n : ℕ) {r : ℝ} (_hr : 0 < r) :
    ∃ j : ℕ, n < j ^ 2 ∧ r ≤ stepRadius n (j ^ 2) := by
  have ht : Tendsto (fun x : ℝ => x ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨j, hj₁, hj₂⟩ : ∃ j : ℕ, 2 * (n + 1) ≤ j ∧
      2 * r ≤ ((j : ℝ) ^ 2) ^ (1 / 4 : ℝ) := by
    have ht' : Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (1 / 4 : ℝ)) atTop atTop :=
      ht.comp ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
    exact ((eventually_ge_atTop (2 * (n + 1))).and (ht'.eventually_ge_atTop _)).exists
  have hjle : j ≤ j ^ 2 := Nat.le_self_pow (by decide) j
  refine ⟨j, by omega, ?_⟩
  have h : (2 : ℝ) * n ≤ (j : ℝ) ^ 2 := by
    exact_mod_cast (show 2 * n ≤ j ^ 2 by omega)
  have hjpos : (0 : ℝ) < (j : ℝ) ^ 2 := by
    have : 0 < j := by omega
    positivity
  unfold stepRadius
  push_cast
  apply (le_div_iff₀ (scale_pos hjpos)).mpr
  have hp : ((j : ℝ) ^ 2) ^ (1 / 4 : ℝ) * scale ((j : ℝ) ^ 2) = (j : ℝ) ^ 2 := by
    rw [scale, ← Real.rpow_add hjpos, show (1 / 4 : ℝ) + 3 / 4 = 1 by norm_num,
      Real.rpow_one]
  nlinarith [mul_le_mul_of_nonneg_right hj₂ (scale_pos hjpos).le]

private def logCross (n j : ℕ) : ℝ :=
  (∑ m ∈ Finset.Ioc (j ^ 2) ((j + 1) ^ 2), Real.log (stepRadius n m)) / gap j

private def cross (n j : ℕ) : ℝ := Real.exp (logCross n j)

private lemma cross_pos (n j : ℕ) : 0 < cross n j := Real.exp_pos _

private lemma log_cross (n j : ℕ) : Real.log (cross n j) = logCross n j :=
  Real.log_exp _

private lemma cross_bounds {n j : ℕ} (hn : n < j ^ 2) :
    stepRadius n (j ^ 2) ≤ cross n j ∧ cross n j ≤ stepRadius n ((j + 1) ^ 2) := by
  have hjp : 0 < j ^ 2 := by omega
  have hjs : j ^ 2 ≤ (j + 1) ^ 2 := by gcongr; omega
  have hgap : (0 : ℝ) < gap j := by unfold gap; positivity
  have hcard : (Finset.Ioc (j ^ 2) ((j + 1) ^ 2)).card = gap j := by
    rw [Nat.card_Ioc, square_succ_sub]
  have h₁ := stepRadius_pos hn
  have h₂ := stepRadius_pos (hn.trans_le hjs)
  constructor
  · rw [← Real.log_le_log_iff h₁ (cross_pos n j), log_cross, logCross, le_div_iff₀ hgap]
    calc
      _ = ∑ _m ∈ Finset.Ioc (j ^ 2) ((j + 1) ^ 2), Real.log (stepRadius n (j ^ 2)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun m hm =>
        Real.log_le_log h₁ (stepRadius_mono hjp hn.le (Finset.mem_Ioc.mp hm).1.le)
  · rw [← Real.log_le_log_iff (cross_pos n j) h₂, log_cross, logCross, div_le_iff₀ hgap]
    calc
      _ ≤ ∑ _m ∈ Finset.Ioc (j ^ 2) ((j + 1) ^ 2), Real.log (stepRadius n ((j + 1) ^ 2)) := by
        apply Finset.sum_le_sum
        intro m hm
        have hh := Finset.mem_Ioc.mp hm
        exact Real.log_le_log (stepRadius_pos (hn.trans hh.1))
          (stepRadius_mono (hjp.trans hh.1) (hn.trans hh.1).le hh.2)
      _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_comm]

private lemma stepRadius_estimates {n j a b : ℕ} (hj : 8 ≤ j)
    (hn : j ^ 2 ≤ 2 * n) (hna : n < a) (ha : (j - 1) ^ 2 ≤ a)
    (hab : a ≤ b) (hb : b ≤ (j + 2) ^ 2) :
    ((b : ℝ) - a) / (32 * ((j : ℝ) * Real.sqrt j)) ≤ stepRadius n b - stepRadius n a ∧
    stepRadius n b - stepRadius n a ≤ 4 * (((b : ℝ) - a) / ((j : ℝ) * Real.sqrt j)) := by
  have hj' : (8 : ℝ) ≤ j := by exact_mod_cast hj
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hsa : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hsb : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hn' : (j : ℝ) ^ 2 ≤ 2 * n := by exact_mod_cast hn
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hminor : (j : ℝ) ^ 2 / 4 ≤ a := by
    have h : ((j : ℝ) - 1) ^ 2 ≤ a := by
      rw [← show ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 by rw [Nat.cast_sub (by omega)]; norm_num]
      exact_mod_cast ha
    nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) - 2 by linarith)
      (show 0 ≤ 3 * (j : ℝ) - 2 by linarith)]
  have hmajor : (b : ℝ) ≤ 4 * (j : ℝ) ^ 2 := by
    have h : (b : ℝ) ≤ ((j : ℝ) + 2) ^ 2 := by exact_mod_cast hb
    nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) - 2 by linarith)
      (show 0 ≤ 3 * (j : ℝ) + 2 by linarith)]
  have hfour : scale 4 ≤ 4 := scale_le_self (by norm_num)
  have hmin : ((j : ℝ) * Real.sqrt j) / 4 ≤ scale a := by
    have h := scale_le (show 0 ≤ (j : ℝ) ^ 2 / 4 by positivity) hminor
    rw [div_eq_inv_mul, scale_mul _ _ (by positivity) (by positivity),
      scale_square hjp] at h
    have hs : (1 / 4 : ℝ) ≤ scale 4⁻¹ := by
      unfold scale at *
      rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4)]
      simpa using inv_anti₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) _) hfour
    calc
      _ = (1 / 4 : ℝ) * ((j : ℝ) * Real.sqrt j) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hs (by positivity)).trans h
  have hmax : scale a ≤ 4 * ((j : ℝ) * Real.sqrt j) := by
    have h := scale_le hsa.le (hab'.trans hmajor)
    rw [scale_mul _ _ (by norm_num) (by positivity), scale_square hjp] at h
    exact h.trans (mul_le_mul_of_nonneg_right hfour (by positivity))
  have hfrac : (1 / 8 : ℝ) ≤ (n : ℝ) / b := by
    apply (le_div_iff₀ hsb).mpr
    linarith
  constructor
  · refine le_trans ?_ (stepRadius_sub_ge (by exact_mod_cast hsa) hna.le hab)
    calc
      _ = (1 / 8 : ℝ) * (((b : ℝ) - a) / (4 * ((j : ℝ) * Real.sqrt j))) := by ring
      _ ≤ _ := mul_le_mul hfrac
        (div_le_div_of_nonneg_left (sub_nonneg.mpr hab') (scale_pos hsa) hmax)
        (by positivity) (by positivity)
  · refine (stepRadius_sub_le (by exact_mod_cast hsa) hna.le hab).trans ?_
    calc
      _ ≤ ((b : ℝ) - a) / (((j : ℝ) * Real.sqrt j) / 4) :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hab') (by positivity) hmin
      _ = _ := by ring

private lemma log_sub_ge_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  rw [sub_div, div_self hb.ne']
  linarith

private lemma eventually_cross {r ε D : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ j : ℕ, 8 ≤ j ∧ D ≤ (gap j : ℝ) ∧
      n < (j - 1) ^ 2 ∧ |cross n j - r| < ε ∧
      Real.log (stepRadius n (j ^ 2 - j)) ≤ logCross n j - 100 / gap j ∧
      logCross n j + 100 / gap j ≤ Real.log (stepRadius n ((j + 1) ^ 2 + j)) := by
  classical
  let M := max (2 / r) (max (4 * r) (max (20 / min ε 1) (3200 * (r + 1))))
  have ht : Tendsto (fun j : ℕ => Real.sqrt (j : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (ht.eventually_gt_atTop M)
  obtain ⟨L, hL⟩ := exists_nat_gt D
  filter_upwards [eventually_ge_atTop ((max J (max L 8)) ^ 2)] with n hn
  let P := fun j : ℕ => n < j ^ 2 ∧ r ≤ stepRadius n (j ^ 2)
  have he : ∃ j, P j := exists_stepRadius_ge n hr
  let j := Nat.find he
  have hj : P j := Nat.find_spec he
  have hmono : StrictMono (fun k : ℕ => k ^ 2) := by
    intro a b hab
    exact Nat.pow_lt_pow_left hab (by decide)
  have hlarge : max J (max L 8) ≤ j := by
    by_contra! h
    exact (not_lt_of_ge hn) ((hmono h).trans' hj.1)
  have hj8 : 8 ≤ j := by omega
  have hjR : (8 : ℝ) ≤ j := by exact_mod_cast hj8
  have hjP : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hgapP : 0 < (gap j : ℝ) := by unfold gap; positivity
  have hgapj : (j : ℝ) ≤ gap j := by
    unfold gap
    push_cast
    linarith
  have hDj : D ≤ (gap j : ℝ) := hL.le.trans ((by exact_mod_cast (show L ≤ j by omega)
    : (L : ℝ) ≤ j).trans hgapj)
  have hS : M < Real.sqrt (j : ℝ) := hJ _ (by omega)
  have hSpos : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos_of_pos hjP
  have hSr : 2 / r < Real.sqrt (j : ℝ) := (le_max_left _ _).trans_lt hS
  have hSr' : 4 * r < Real.sqrt (j : ℝ) :=
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hS)
  have hSε : 20 / min ε 1 < Real.sqrt (j : ℝ) :=
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hS))
  have hSK : 3200 * (r + 1) < Real.sqrt (j : ℝ) :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hS))
  have hpred : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hprev : n < (j - 1) ^ 2 := by
    by_contra! hc
    have hc' : ((j : ℝ) - 1) ^ 2 ≤ n := by
      rw [← hpred]
      exact_mod_cast hc
    have h := hj.2
    change r ≤ (((j ^ 2 : ℕ) : ℝ) - n) / scale ((j ^ 2 : ℕ) : ℝ) at h
    rw [Nat.cast_pow, scale_square hjP, le_div_iff₀ (by positivity)] at h
    have hp := (div_lt_iff₀ hr).mp hSr
    nlinarith [mul_pos hjP (show 0 < Real.sqrt (j : ℝ) * r - 2 by linarith)]
  have hprev_lt : stepRadius n ((j - 1) ^ 2) < r := by
    refine lt_of_not_ge fun h => ?_
    exact (Nat.find_min he (show j - 1 < j by omega)) ⟨hprev, h⟩
  have hnj : j ^ 2 ≤ 2 * n := by
    have h := hprev_lt
    change (((((j - 1) ^ 2 : ℕ) : ℝ) - n) / scale (((j - 1) ^ 2 : ℕ) : ℝ)) < r at h
    have hpos : 0 < ((j : ℝ) - 1) ^ 2 := pow_pos (by linarith) _
    rw [Nat.cast_pow, hpred, div_lt_iff₀ (scale_pos hpos)] at h
    have hs : scale (((j : ℝ) - 1) ^ 2) ≤ (j : ℝ) * Real.sqrt j := by
      rw [← scale_square hjP]
      exact scale_le (by positivity) (by gcongr <;> linarith)
    have h₁ := mul_le_mul_of_nonneg_left hs hr.le
    have h₂ := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hSr' hSpos) hjP
    have h₃ : Real.sqrt (j : ℝ) * Real.sqrt j = j := Real.mul_self_sqrt hjP.le
    rw [h₃] at h₂
    have h₄ := mul_nonneg (show 0 ≤ (j : ℝ) - 8 by linarith) (show 0 ≤ (j : ℝ) by positivity)
    exact_mod_cast (show (j : ℝ) ^ 2 ≤ 2 * n by nlinarith)
  let a := (j - 1) ^ 2
  let b := (j + 1) ^ 2 + j
  let c := j ^ 2 - j
  have hc : c + j = j ^ 2 := by
    have hk := Nat.le_self_pow (by decide : 2 ≠ 0) j
    dsimp [c]; omega
  have hbudget : ∀ (u v : ℕ), a ≤ u → u ≤ v → v ≤ (j + 2) ^ 2 →
      ((v : ℝ) - u) / (32 * ((j : ℝ) * Real.sqrt j)) ≤ stepRadius n v - stepRadius n u ∧
      stepRadius n v - stepRadius n u ≤ 4 * (((v : ℝ) - u) / ((j : ℝ) * Real.sqrt j)) :=
    fun u v hu huv hv => stepRadius_estimates hj8 hnj (hprev.trans_le hu) hu huv hv
  have hac : a ≤ c := Nat.le_sub_of_add_le (square_pred_add_le (by omega))
  have hcj : c ≤ j ^ 2 := Nat.sub_le _ _
  have hjs : j ^ 2 ≤ (j + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ j) 2
  have hcb : c ≤ b := (hcj.trans hjs).trans (Nat.le_add_right _ _)
  have hbb : b ≤ (j + 2) ^ 2 := by
    dsimp [b]
    have h : (j + 2) ^ 2 = (j + 1) ^ 2 + 2 * j + 3 := by ring
    omega
  have hb_a : (b : ℝ) - a = 5 * j := by
    dsimp [a, b]
    push_cast
    rw [hpred]
    ring
  have htotal := (hbudget a b le_rfl (hac.trans hcb) hbb).2
  rw [hb_a] at htotal
  have htotal' : stepRadius n b - stepRadius n a < min ε 1 := by
    have hs : 4 * (5 * (j : ℝ) / ((j : ℝ) * Real.sqrt j)) = 20 / Real.sqrt j := by
      field_simp
      norm_num
    rw [hs] at htotal
    refine htotal.trans_lt ?_
    exact (div_lt_iff₀ hSpos).mpr (by
      have hh : 0 < min ε (1 : ℝ) := lt_min hε (by norm_num)
      linarith [(div_lt_iff₀ hh).mp hSε])
  have hcr := cross_bounds hj.1
  have hbpos : ((j + 1) ^ 2 : ℕ) ≤ b := by dsimp [b]; omega
  have hbr : stepRadius n ((j + 1) ^ 2) ≤ stepRadius n b :=
    stepRadius_mono (by have := hj.1; omega)
      (hj.1.le.trans (hmono.monotone (Nat.le_succ j))) hbpos
  have hcross_lo : r ≤ cross n j := hj.2.trans hcr.1
  have hcross_hi : cross n j ≤ stepRadius n b := hcr.2.trans hbr
  have hbr' : stepRadius n b < r + min ε 1 := by linarith
  have hca : n < c := hprev.trans_le hac
  have hcpos := stepRadius_pos hca
  have hbpos' := stepRadius_pos (hca.trans_le hcb)
  have hhalf : 100 * (r + 1) ≤ (gap j : ℝ) / (32 * Real.sqrt j) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hp := mul_lt_mul_of_pos_right hSK hSpos
    have hs : Real.sqrt (j : ℝ) * Real.sqrt j = j := Real.mul_self_sqrt hjP.le
    rw [hs] at hp
    linarith only [hgapj, hp]
  have lowerSep : 1 / (32 * Real.sqrt j) ≤ cross n j - stepRadius n c := by
    have hjb : j ^ 2 ≤ (j + 2) ^ 2 := hmono.monotone (by omega)
    have h := (hbudget c (j ^ 2) hac hcj hjb).1
    have hcast := congrArg (fun k : ℕ => (k : ℝ)) hc
    push_cast at hcast h
    have heq : ((j : ℝ) ^ 2 - c) / (32 * ((j : ℝ) * Real.sqrt j)) =
        1 / (32 * Real.sqrt j) := by
      rw [← hcast, add_sub_cancel_left]
      field_simp
    linarith [heq ▸ h, hcr.1]
  have upperSep : 1 / (32 * Real.sqrt j) ≤ stepRadius n b - cross n j := by
    have h := (hbudget ((j + 1) ^ 2) b (hac.trans (hcj.trans hjs)) hbpos hbb).1
    have heq : ((b : ℝ) - (((j + 1) ^ 2 : ℕ) : ℝ)) / (32 * ((j : ℝ) * Real.sqrt j)) =
        1 / (32 * Real.sqrt j) := by
      dsimp [b]
      push_cast
      rw [add_sub_cancel_left]
      field_simp
    linarith [heq ▸ h, hcr.2]
  have logSep {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hv' : v ≤ r + 1)
      (hsep : 1 / (32 * Real.sqrt j) ≤ v - u) :
      100 / (gap j : ℝ) ≤ Real.log v - Real.log u := by
    refine le_trans ?_ (log_sub_ge_div hu hv)
    apply (le_div_iff₀ hv).mpr
    rw [div_mul_eq_mul_div]
    have hh : 100 * (r + 1) ≤ (gap j : ℝ) * (1 / (32 * Real.sqrt j)) := by
      simpa [div_eq_mul_inv] using hhalf
    apply (div_le_iff₀ hgapP).mpr
    calc
      100 * v ≤ 100 * (r + 1) := by linarith
      _ ≤ _ := by
        rw [mul_comm (v - u) (gap j : ℝ)]
        exact hh.trans (mul_le_mul_of_nonneg_left hsep hgapP.le)
  refine ⟨j, hj8, hDj, hprev, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hcross_lo)]
    linarith [min_le_left ε (1 : ℝ)]
  · have h := logSep hcpos (cross_pos n j) (by linarith [min_le_right ε (1 : ℝ)]) lowerSep
    rw [log_cross] at h
    linarith
  · have h := logSep (cross_pos n j) hbpos' (by linarith [min_le_right ε (1 : ℝ)]) upperSep
    rw [log_cross] at h
    linarith

-- A nearby binomial root and the minimum modulus principle
private lemma exists_zero_of_norm_gap {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hcenter : ‖g 0‖ ≤ 1 / 16) (hbdry : ∀ v : ℂ, ‖v‖ = 1 / 2 → 1 / 8 ≤ ‖g v‖) :
    ∃ v : ℂ, ‖v‖ ≤ 1 / 2 ∧ g v = 0 := by
  by_contra! hn
  have hnon (v : ℂ) (hv : v ∈ closedBall (0 : ℂ) (1 / 2)) : g v ≠ 0 := by
    apply hn
    simpa [mem_closedBall, dist_zero_right] using hv
  have hd : DiffContOnCl ℂ (fun v => (g v)⁻¹) (ball 0 (1 / 2)) := by
    constructor
    · exact hg.differentiableOn.inv (fun v hv => hnon v (ball_subset_closedBall hv))
    · rw [closure_ball _ (by norm_num)]
      exact hg.continuous.continuousOn.inv₀ hnon
  have hz : (0 : ℂ) ∈ closure (ball 0 (1 / 2)) :=
    subset_closure (mem_ball_self (by norm_num))
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
    (C := 8) (fun v hv => ?_) hz
  · rw [norm_inv] at h
    have hp : 0 < ‖g 0‖ := norm_pos_iff.mpr (hn 0 (by simp))
    have := (inv_le_comm₀ hp (by positivity : 0 < (8 : ℝ))).mp h
    norm_num at this
    linarith
  · rw [frontier_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0), mem_sphere, dist_zero_right] at hv
    rw [norm_inv]
    have h := hbdry v hv
    apply (inv_le_comm₀ (by linarith : 0 < ‖g v‖) (by positivity : 0 < (8 : ℝ))).mpr
    norm_num
    exact h

private lemma exp_model_lower {v : ℂ} (hv : ‖v‖ = 1 / 2) : 1 / 4 ≤ ‖1 - Complex.exp v‖ := by
  have h := Complex.norm_exp_sub_one_sub_id_le (x := v) (by rw [hv]; norm_num)
  have ht := norm_sub_le (Complex.exp v - 1) (Complex.exp v - 1 - v)
  rw [sub_sub_cancel] at ht
  rw [norm_sub_rev 1 (Complex.exp v)]
  rw [hv] at h ht
  linarith

private lemma exists_zero_of_exp_model {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hclose : ∀ v : ℂ, ‖v‖ ≤ 1 / 2 → ‖g v - (1 - Complex.exp v)‖ ≤ 1 / 16) :
    ∃ v : ℂ, ‖v‖ ≤ 1 / 2 ∧ g v = 0 := by
  apply exists_zero_of_norm_gap hg
  · simpa using hclose 0 (by norm_num)
  · intro v hv
    have ha := exp_model_lower hv
    have hb := hclose v hv.le
    have hc := norm_sub_le (1 - Complex.exp v - g v) (-g v)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_sub_rev (1 - Complex.exp v) (g v)] at hc
    linarith

private lemma norm_exp_div (v : ℂ) {d : ℕ} (_hd : 0 < d) :
    ‖Complex.exp (v / (d : ℂ))‖ = Real.exp (v.re / d) := by
  rw [Complex.norm_exp, ← Complex.ofReal_natCast, Complex.div_ofReal_re]

private lemma exp_div_pow (v : ℂ) {d : ℕ} (hd : 0 < d) :
    Complex.exp (v / (d : ℂ)) ^ d = Complex.exp v := by
  rw [← Complex.exp_nat_mul]
  congr 1
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

private lemma nearby_phase_root {z : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r)
    {d : ℕ} (hd : Real.pi ≤ d) :
    ∃ w : ℂ, ‖w‖ = r ∧ w ^ d = - (r : ℂ) ^ d ∧
      ‖w - z‖ ≤ |r - ‖z‖| + 2 * r * Real.pi / d := by
  have hd' : 0 < (d : ℝ) := Real.pi_pos.trans_le hd
  have hd'' : 0 < d := by exact_mod_cast hd'
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u := ((r / ‖z‖ : ℝ) : ℂ) * z
  have hu : ‖u‖ = r := by
    rw [show u = ((r / ‖z‖ : ℝ) : ℂ) * z by rfl, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hzn.ne']
  have hun : u ≠ 0 := norm_pos_iff.mp (hu ▸ hr)
  let s := - (r : ℂ) ^ d / u ^ d
  have hs : ‖s‖ = 1 := by
    dsimp [s]
    rw [norm_div, norm_neg, norm_pow, norm_pow, hu, Complex.norm_real,
      Real.norm_of_nonneg hr.le, div_self (pow_ne_zero _ hr.ne')]
  let t : ℂ := (s.arg : ℂ) * Complex.I
  have ht : Complex.exp t = s := by
    simpa [t, hs] using Complex.norm_mul_exp_arg_mul_I s
  have ht_re : t.re = 0 := by
    simp [t, Complex.mul_re]
  have ht_norm : ‖t‖ ≤ Real.pi := by
    rw [show t = (s.arg : ℂ) * Complex.I by rfl, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg s).le, Complex.arg_le_pi s⟩
  let w := u * Complex.exp (t / (d : ℂ))
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [show w = u * Complex.exp (t / (d : ℂ)) by rfl, norm_mul,
      hu, norm_exp_div t hd'', ht_re, zero_div, Real.exp_zero, mul_one]
  · rw [show w = u * Complex.exp (t / (d : ℂ)) by rfl, mul_pow, exp_div_pow t hd'', ht]
    dsimp [s]
    field_simp
  · have htdiv : ‖t / (d : ℂ)‖ ≤ Real.pi / d := by
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right ht_norm hd'.le
    have hwdu : ‖w - u‖ ≤ 2 * r * Real.pi / d := by
      rw [show w - u = u * (Complex.exp (t / (d : ℂ)) - 1) by dsimp [w]; ring, norm_mul, hu]
      have hh := Complex.norm_exp_sub_one_le
        (htdiv.trans ((div_le_iff₀ hd').mpr (by simpa using hd)))
      calc
        _ ≤ r * (2 * ‖t / (d : ℂ)‖) := mul_le_mul_of_nonneg_left hh hr.le
        _ ≤ r * (2 * (Real.pi / d)) := by gcongr
        _ = _ := by ring
    have hud : ‖u - z‖ = |r - ‖z‖| := by
      rw [show u - z = (((r / ‖z‖ - 1 : ℝ) : ℂ)) * z by dsimp [u]; push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ = |(r / ‖z‖ - 1) * ‖z‖| := by rw [abs_mul, abs_of_nonneg (norm_nonneg z)]
        _ = _ := by congr 1; field_simp
    calc
      _ ≤ ‖w - u‖ + ‖u - z‖ := by
        simpa only [dist_eq_norm] using dist_triangle w u z
      _ ≤ _ := by linarith [hud]

-- Polynomial growth forced by an algebraic relation
private lemma polynomial_eval_bound (p : Polynomial ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖p.eval (x : ℂ)‖ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * x ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  gcongr
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)

private lemma polynomial_eval_eventually_lower (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop, c ≤ ‖p.eval (x : ℂ)‖ := by
  by_cases h : p.natDegree = 0
  · refine ⟨‖p.leadingCoeff‖, norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp),
      Eventually.of_forall fun x => ?_⟩
    rw [← Polynomial.coeff_natDegree, h]
    have he : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h
    nth_rw 2 [he]
    simp
  · refine ⟨1, zero_lt_one, ?_⟩
    apply (p.tendsto_norm_atTop (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero h))
      (z := fun x : ℝ => (x : ℂ)) ?_).eventually_ge_atTop
    simpa [Complex.norm_real, Real.norm_eq_abs] using tendsto_abs_atTop_atTop

private lemma algebraic_growth {f : ℂ → ℂ} (hf : IsAlgebraic (Polynomial ℂ) f) :
    ∃ (A : ℝ) (D : ℕ), ∀ᶠ x : ℝ in atTop, ‖f (x : ℂ)‖ ≤ A * x ^ D := by
  obtain ⟨P, hP, hPf⟩ := hf
  let B (i : ℕ) := ∑ k ∈ Finset.range ((P.coeff i).natDegree + 1), ‖(P.coeff i).coeff k‖
  let D := (Finset.range P.natDegree).sup (fun i => (P.coeff i).natDegree)
  let A := ∑ i ∈ Finset.range P.natDegree, B i
  have hB (i : ℕ) : 0 ≤ B i := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hB i
  obtain ⟨c, hc, hcl⟩ := polynomial_eval_eventually_lower P.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hP)
  refine ⟨A / c + 1, D, ?_⟩
  filter_upwards [hcl, eventually_ge_atTop (1 : ℝ)] with x hlead hx
  let e := Polynomial.evalRingHom (x : ℂ)
  let Q := P.map e
  have hln : e P.leadingCoeff ≠ 0 := norm_pos_iff.mp (hc.trans_le hlead)
  have hQd : Q.natDegree = P.natDegree := Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hln
  have hQl : Q.leadingCoeff = P.leadingCoeff.eval (x : ℂ) :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hln
  have hQ : Q ≠ 0 := by
    intro he
    change Q.leadingCoeff = e P.leadingCoeff at hQl
    exact hln (by rw [← hQl, he, Polynomial.leadingCoeff_zero])
  have hroot : Q.IsRoot (f (x : ℂ)) := by
    have h := congrFun hPf (x : ℂ)
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range] at h
    simpa only [Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply,
      Polynomial.algebraMap_algebraPi, Polynomial.coe_aeval_eq_eval, e,
      Polynomial.coe_evalRingHom] using h
  have hbound : (↑((Finset.range Q.natDegree).sup (‖Q.coeff ·‖₊)) : ℝ) ≤ A * x ^ D := by
    have hn : 0 ≤ A * x ^ D := mul_nonneg hA (by positivity)
    change ((Finset.range Q.natDegree).sup (‖Q.coeff ·‖₊) : ℝ≥0) ≤
      (⟨A * x ^ D, hn⟩ : ℝ≥0)
    refine Finset.sup_le fun i hi => ?_
    rw [hQd] at hi
    change ‖Q.coeff i‖ ≤ A * x ^ D
    rw [Polynomial.coeff_map]
    calc
      _ ≤ B i * x ^ (P.coeff i).natDegree := polynomial_eval_bound _ hx
      _ ≤ A * x ^ D := by
        gcongr
        · exact Finset.single_le_sum (fun k _ => hB k) hi
        · exact Finset.le_sup (f := fun k => (P.coeff k).natDegree) hi
  have hlt := hroot.norm_lt_cauchyBound hQ
  have hlt' : ‖f (x : ℂ)‖ <
      (↑((Finset.range Q.natDegree).sup (‖Q.coeff ·‖₊)) : ℝ) / ‖Q.leadingCoeff‖ + 1 := by
    exact_mod_cast hlt
  rw [hQl] at hlt'
  calc
    _ ≤ _ := hlt'.le
    _ ≤ (A * x ^ D) / c + 1 := by
      gcongr
    _ ≤ _ := by
      have hpow : 1 ≤ x ^ D := one_le_pow₀ hx
      calc
        _ ≤ A * x ^ D / c + x ^ D := add_le_add_right hpow _
        _ = _ := by ring

private lemma transcendental_of_real_growth {f : ℂ → ℂ}
    (hf : ∀ d : ℕ, ∃ b : ℝ, 0 < b ∧ ∀ x : ℝ, 1 ≤ x → b * x ^ (d + 1) ≤ ‖f (x : ℂ)‖) :
    Transcendental (Polynomial ℂ) f := by
  intro h
  obtain ⟨A, D, hA⟩ := algebraic_growth h
  obtain ⟨b, hb, hbd⟩ := hf D
  obtain ⟨x, hx, hAx⟩ := ((eventually_gt_atTop (max (1 : ℝ) (A / b))).and hA).exists
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx.le
  have hs := (hbd x hx1).trans hAx
  rw [pow_succ, ← show (b * x) * x ^ D = b * (x ^ D * x) by ring] at hs
  have hxp : 0 < x := zero_lt_one.trans_le hx1
  have hh := (mul_le_mul_iff_left₀ (pow_pos hxp D)).mp hs
  have hh' := (div_lt_iff₀ hb).mp ((le_max_right (1 : ℝ) (A / b)).trans_lt hx)
  exact (not_lt_of_ge hh) (by simpa [mul_comm] using hh')

-- Geometric estimates for the remaining terms
private def realTerm (n m : ℕ) (r : ℝ) : ℝ :=
  weight m / ((m - n).factorial : ℝ) * r ^ (m - n)

private def logTerm (n m : ℕ) (r : ℝ) : ℝ := Real.log (realTerm n m r)

private lemma realTerm_pos {n m : ℕ} {r : ℝ} (hr : 0 < r) :
    0 < realTerm n m r :=
  mul_pos (div_pos (weight_pos _) (by positivity)) (pow_pos hr _)

private lemma logTerm_succ {n m : ℕ} (hn : n ≤ m) {r : ℝ} (hr : 0 < r) :
    logTerm n (m + 1) r - logTerm n m r =
      Real.log r - Real.log (stepRadius n (m + 1)) := by
  have hs : m + 1 - n = (m - n) + 1 := by omega
  have hpos : 0 < stepRadius n (m + 1) := stepRadius_pos (by omega)
  have h : realTerm n (m + 1) r * stepRadius n (m + 1) =
      realTerm n m r * r := by
    unfold realTerm stepRadius scale
    rw [hs, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Nat.cast_succ, weight_succ,
      pow_succ, Nat.cast_sub hn]
    have ha : 0 < ((m : ℝ) + 1) ^ (3 / 4 : ℝ) := by positivity
    have hb : 0 < ((m - n).factorial : ℝ) := by positivity
    have hc : 0 < (m : ℝ) - n + 1 := by
      have : (n : ℝ) ≤ m := by exact_mod_cast hn
      linarith
    field_simp
    ring
  have hl := congrArg Real.log h
  rw [Real.log_mul (realTerm_pos hr).ne' hpos.ne',
    Real.log_mul (realTerm_pos hr).ne' hr.ne'] at hl
  unfold logTerm
  linarith

private lemma logTerm_sub {n a b : ℕ} (hna : n ≤ a) (hab : a ≤ b) {r : ℝ} (hr : 0 < r) :
    logTerm n b r - logTerm n a r =
      ∑ m ∈ Finset.Ioc a b, (Real.log r - Real.log (stepRadius n m)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ← ih, ← logTerm_succ (hna.trans hab) hr]
    ring

private lemma logTerm_upper {n a b : ℕ} (hna : n ≤ a) (hab : a ≤ b) {r C : ℝ} (hr : 0 < r)
    (h : ∀ m : ℕ, a < m → m ≤ b → Real.log r - Real.log (stepRadius n m) ≤ C) :
    logTerm n b r - logTerm n a r ≤ (↑(b - a) : ℝ) * C := by
  rw [logTerm_sub hna hab hr, ← Nat.card_Ioc, ← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun m hm => h m (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hm).2

private lemma logTerm_lower {n a b : ℕ} (hna : n ≤ a) (hab : a ≤ b) {r C : ℝ} (hr : 0 < r)
    (h : ∀ m : ℕ, a < m → m ≤ b → C ≤ Real.log r - Real.log (stepRadius n m)) :
    (↑(b - a) : ℝ) * C ≤ logTerm n b r - logTerm n a r := by
  rw [logTerm_sub hna hab hr, ← Nat.card_Ioc, ← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun m hm => h m (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hm).2

private lemma realTerm_cross {n j : ℕ} (hn : n ≤ j ^ 2) :
    realTerm n ((j + 1) ^ 2) (cross n j) = realTerm n (j ^ 2) (cross n j) := by
  have hjs : j ^ 2 ≤ (j + 1) ^ 2 := by gcongr; omega
  have hf := logTerm_sub hn hjs (cross_pos n j)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, square_succ_sub,
    nsmul_eq_mul, log_cross, logCross] at hf
  have hg : (gap j : ℝ) ≠ 0 := by unfold gap; positivity
  have hf' : logTerm n ((j + 1) ^ 2) (cross n j) -
      logTerm n (j ^ 2) (cross n j) = 0 := by
    rw [hf, mul_div_cancel₀ _ hg, sub_self]
  apply Real.log_injOn_pos (realTerm_pos (cross_pos n j)) (realTerm_pos (cross_pos n j))
  exact sub_eq_zero.mp hf'

private lemma log_tail_budget {d span strong j steps : ℝ}
    (hd : 0 < d) (hdj : d ≤ 3 * j) (hj : 0 ≤ j) (hs : 0 ≤ steps) (hspan : j * steps ≤ span)
    (hstrong : span ≤ 3 * strong) :
    span / d - 100 * strong / d ≤ -10 * steps := by
  rw [← sub_div, div_le_iff₀ hd]
  have hdstep := mul_le_mul_of_nonneg_right hdj hs
  have hsp : 0 ≤ span := (mul_nonneg hj hs).trans hspan
  linarith

private lemma lower_tail_log {n j k : ℕ} (hj : 8 ≤ j) (hn : n < (j - 1) ^ 2)
    (hk : k < j) (hnk : n ≤ k ^ 2) {r : ℝ} (hr : 0 < r)
    (hrlo : logCross n j - 1 / (gap j : ℝ) ≤ Real.log r)
    (hsep : Real.log (stepRadius n (j ^ 2 - j)) ≤ logCross n j - 100 / gap j) :
    logTerm n (k ^ 2) r - logTerm n (j ^ 2) r ≤ -10 * ((j : ℝ) - k) := by
  let a := k ^ 2
  let b := j ^ 2
  let c := b - j
  have hjs : j ≤ b := Nat.le_self_pow (by decide) j
  have hcb : c + j = b := by dsimp [c]; omega
  have hj2 : (j - 1) ^ 2 + j ≤ b := square_pred_add_le (by omega)
  have hac : a ≤ c := by
    have hh : a ≤ (j - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hcb' : c ≤ b := by omega
  have hnj : n < b := by omega
  have hcr := (cross_bounds hnj).1
  have hp := stepRadius_pos hnj
  have hcut : ∀ m, a < m → m ≤ c → (99 : ℝ) / gap j ≤ Real.log r - Real.log (stepRadius n m) := by
    intro m hm hmc
    have hnm : n < m := by omega
    have hs := Real.log_le_log (stepRadius_pos hnm)
      (stepRadius_mono (by omega) hnm.le hmc)
    change Real.log (stepRadius n c) ≤ _ at hsep
    calc
      _ = (logCross n j - 1 / gap j) - (logCross n j - 100 / gap j) := by ring
      _ ≤ _ := sub_le_sub hrlo (hs.trans hsep)
  have hrest : ∀ m, c < m → m ≤ b → -(1 : ℝ) / gap j ≤ Real.log r - Real.log (stepRadius n m) := by
    intro m hm hmb
    have hnm : n < m := by omega
    have hs := Real.log_le_log (stepRadius_pos hnm)
      (stepRadius_mono (by omega) hnm.le hmb)
    have h := Real.log_le_log hp hcr
    rw [log_cross] at h
    calc
      _ = (logCross n j - 1 / gap j) - logCross n j := by ring
      _ ≤ _ := sub_le_sub hrlo (hs.trans h)
  have h₁ := logTerm_lower hnk hac hr hcut
  have h₂ := logTerm_lower (hnk.trans hac) hcb' hr hrest
  rw [Nat.cast_sub hac] at h₁
  rw [Nat.cast_sub hcb'] at h₂
  have hsum : ((b : ℝ) - a) / gap j - 100 * ((c : ℝ) - a) / gap j ≥
      logTerm n a r - logTerm n b r := by
    linarith only [h₁, h₂, show ((b : ℝ) - a) / gap j - 100 * ((c : ℝ) - a) / gap j =
      -(((c : ℝ) - a) * (99 / gap j) + ((b : ℝ) - c) * (-1 / gap j)) by ring]
  refine hsum.trans (log_tail_budget (j := (j : ℝ)) (by unfold gap; positivity) ?_
    (by positivity) (sub_nonneg.mpr (by exact_mod_cast hk.le)) ?_ ?_)
  · unfold gap
    push_cast
    have : (8 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  · dsimp [a, b]
    push_cast
    have : 0 ≤ (k : ℝ) * ((j : ℝ) - k) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hk.le))
    nlinarith
  · have hpred : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hh : (a : ℝ) ≤ ((j : ℝ) - 1) ^ 2 := by
      rw [← hpred]
      exact_mod_cast (show a ≤ (j - 1) ^ 2 from Nat.pow_le_pow_left (by omega) 2)
    have hb' : (b : ℝ) = (j : ℝ) ^ 2 := by dsimp [b]; push_cast; rfl
    have heq := congrArg (fun x : ℕ => (x : ℝ)) hcb
    push_cast at heq
    have : (8 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith

private lemma upper_tail_log {n j k : ℕ} (hj : 8 ≤ j) (hn : n < j ^ 2)
    (hk : j + 1 < k) {r : ℝ} (hr : 0 < r)
    (hrhi : Real.log r ≤ logCross n j + 1 / (gap j : ℝ))
    (hsep : logCross n j + 100 / gap j ≤ Real.log (stepRadius n ((j + 1) ^ 2 + j))) :
    logTerm n (k ^ 2) r - logTerm n ((j + 1) ^ 2) r ≤ -10 * ((k : ℝ) - (j + 1)) := by
  let a := (j + 1) ^ 2
  let b := k ^ 2
  let c := a + j
  have hac : a ≤ c := Nat.le_add_right _ _
  have hcb : c ≤ b := by
    have hh : (j + 2) ^ 2 ≤ b := Nat.pow_le_pow_left (by omega) 2
    have he : (j + 2) ^ 2 = (j + 1) ^ 2 + 2 * j + 3 := by ring
    dsimp [c, a]
    omega
  have hna : n < a := hn.trans_le (Nat.pow_le_pow_left (Nat.le_succ j) 2)
  have hcr := (cross_bounds hn).2
  have hweak : ∀ m, a < m → m ≤ c → Real.log r - Real.log (stepRadius n m) ≤ 1 / (gap j : ℝ) := by
    intro m hm _
    have hs := Real.log_le_log (stepRadius_pos hna)
      (stepRadius_mono (by omega) hna.le hm.le)
    have h := Real.log_le_log (cross_pos n j) hcr
    rw [log_cross] at h
    calc
      _ ≤ (logCross n j + 1 / gap j) - logCross n j := sub_le_sub hrhi (h.trans hs)
      _ = _ := by ring
  have hstrong : ∀ m, c < m → m ≤ b → Real.log r - Real.log (stepRadius n m) ≤ -99 / (gap j : ℝ) := by
    intro m hm _
    have hnc : n < c := hna.trans_le hac
    have hs := Real.log_le_log (stepRadius_pos hnc)
      (stepRadius_mono (by omega) hnc.le hm.le)
    change _ ≤ Real.log (stepRadius n c) at hsep
    calc
      _ ≤ (logCross n j + 1 / gap j) - (logCross n j + 100 / gap j) :=
        sub_le_sub hrhi (hsep.trans hs)
      _ = _ := by ring
  have h₁ := logTerm_upper hna.le hac hr hweak
  have h₂ := logTerm_upper (hna.le.trans hac) hcb hr hstrong
  rw [Nat.cast_sub hac] at h₁
  rw [Nat.cast_sub hcb] at h₂
  have hsum : logTerm n b r - logTerm n a r ≤
      ((b : ℝ) - a) / gap j - 100 * ((b : ℝ) - c) / gap j := by
    linarith only [h₁, h₂, show ((b : ℝ) - a) / gap j - 100 * ((b : ℝ) - c) / gap j =
      ((c : ℝ) - a) * (1 / gap j) + ((b : ℝ) - c) * (-99 / gap j) by ring]
  refine hsum.trans (log_tail_budget (j := (j : ℝ)) (by unfold gap; positivity) ?_
    (by positivity) (sub_nonneg.mpr (by exact_mod_cast hk.le)) ?_ ?_)
  · unfold gap
    push_cast
    have : (8 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  · dsimp [a, b]
    push_cast
    have hk' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hk.le
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) - (j + 1) by linarith)
      (show 0 ≤ (k : ℝ) + 1 by positivity)]
  · have hk' : (j : ℝ) + 2 ≤ k := by exact_mod_cast (show j + 2 ≤ k by omega)
    dsimp [c, a, b]
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') (show 0 ≤ (k : ℝ) + (j + 2) by positivity)]

-- The normalized derivative and eventual zero-hitting
private def termCoeff (n m : ℕ) : ℝ := weight m / ((m - n).factorial : ℝ)

private def squareTerm (n j : ℕ) (z : ℂ) : ℂ :=
  if n ≤ j ^ 2 then (termCoeff n (j ^ 2) : ℂ) * z ^ (j ^ 2 - n) else 0

private lemma termCoeff_pos (n m : ℕ) : 0 < termCoeff n m :=
  div_pos (weight_pos m) (by positivity)

private lemma squareTerm_norm {n j : ℕ} {z : ℂ} (h : n ≤ j ^ 2) :
    ‖squareTerm n j z‖ = realTerm n (j ^ 2) ‖z‖ := by
  rw [squareTerm, if_pos h, norm_mul, Complex.norm_real, norm_pow,
    Real.norm_of_nonneg (termCoeff_pos _ _).le]
  rfl

private lemma squareTerm_hasSum (n : ℕ) (z : ℂ) :
    HasSum (fun j => squareTerm n j z) (iteratedDeriv n sparseFunction z) := by
  let F (m : ℕ) := if square m then
    if n ≤ m then (termCoeff n m : ℂ) * z ^ (m - n) else 0
    else 0
  have h₁ : HasSum (fun k => F (k + n)) (iteratedDeriv n sparseFunction z) := by
    refine (sparseFunction_derivative_hasSum n z).congr_fun fun k => ?_
    simp [F, termCoeff, Nat.add_comm k n]
  have hsum : ∑ k ∈ Finset.range n, F k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have : ¬ n ≤ k := by have := Finset.mem_range.mp hk; omega
    simp [F, this]
  have h₂ : HasSum F (iteratedDeriv n sparseFunction z) := by
    simpa [hsum] using (hasSum_nat_add_iff (f := F) n).1 h₁
  have hi : Function.Injective (fun j : ℕ => j ^ 2) := by
    exact (show StrictMono (fun j : ℕ => j ^ 2) from
      fun _ _ h => Nat.pow_lt_pow_left h (by decide)).injective
  have hzero (m : ℕ) (hm : m ∉ Set.range (fun j : ℕ => j ^ 2)) : F m = 0 := by
    have hm' : ¬ square m := fun h => hm ⟨m.sqrt, h⟩
    simp [F, hm']
  refine ((hi.hasSum_iff hzero).2 h₂).congr_fun fun j => ?_
  simp [F, squareTerm, square, Nat.sqrt_eq']

private lemma sparseFunction_growth (d : ℕ) :
    ∃ b : ℝ, 0 < b ∧ ∀ x : ℝ, 1 ≤ x → b * x ^ (d + 1) ≤ ‖sparseFunction (x : ℂ)‖ := by
  let j := d + 1
  refine ⟨termCoeff 0 (j ^ 2), termCoeff_pos _ _, fun x hx => ?_⟩
  let F (k : ℕ) := termCoeff 0 (k ^ 2) * x ^ (k ^ 2)
  have hF (k : ℕ) : 0 ≤ F k := mul_nonneg (termCoeff_pos _ _).le (by positivity)
  have h := squareTerm_hasSum 0 (x : ℂ)
  have hsum : HasSum F (sparseFunction (x : ℂ)).re := by
    refine (Complex.reCLM.hasSum h).congr_fun fun k => ?_
    simp [F, squareTerm, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  have hle : F j ≤ (sparseFunction (x : ℂ)).re := by
    rw [← hsum.tsum_eq]
    exact hsum.summable.le_tsum j (fun k _ => hF k)
  calc
    _ ≤ F j := by
      dsimp [F]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hx (Nat.le_self_pow (by decide : 2 ≠ 0) j))
        (termCoeff_pos _ _).le
    _ ≤ _ := hle.trans (Complex.re_le_norm _)

private lemma exp_tail_factor (k : ℕ) : Real.exp (-10 * (k : ℝ)) ≤ (1 / 128 : ℝ) ^ k := by
  have h : Real.exp (-10 : ℝ) ≤ 1 / 128 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have h₁ : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h₂ : (2 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h₁ _
    rw [← Real.exp_nat_mul] at h₂
    norm_num at h₂
    nlinarith
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h _

private lemma log_tail_to_norm {n a b : ℕ} {r : ℝ} (hr : 0 < r) {p : ℕ}
    (h : logTerm n a r - logTerm n b r ≤ -10 * (p : ℝ)) :
    realTerm n a r ≤ realTerm n b r * (1 / 128 : ℝ) ^ p := by
  unfold logTerm at h
  rw [← Real.log_div (realTerm_pos hr).ne' (realTerm_pos hr).ne'] at h
  have h' := Real.exp_le_exp.mpr h
  rw [Real.exp_log (div_pos (realTerm_pos hr) (realTerm_pos hr))] at h'
  rw [mul_comm]
  exact (div_le_iff₀ (realTerm_pos hr)).mp (h'.trans (exp_tail_factor p))

private lemma norm_two_tails {n j : ℕ} {z : ℂ}
    (hlo : ∀ k < j, ‖squareTerm n k z‖ ≤ ‖squareTerm n j z‖ * (1 / 128 : ℝ) ^ (j-k))
    (hhi : ∀ k, j+1 < k → ‖squareTerm n k z‖ ≤
        ‖squareTerm n (j+1) z‖ * (1 / 128 : ℝ) ^ (k-(j+1))) :
    ‖iteratedDeriv n sparseFunction z - (squareTerm n j z + squareTerm n (j+1) z)‖ ≤
      (‖squareTerm n j z‖ + ‖squareTerm n (j+1) z‖) / 127 := by
  let q : ℝ := 1 / 128
  have hgeo : HasSum (fun k : ℕ => q ^ (k + 1)) (1 / 127 : ℝ) := by
    have h := (hasSum_geometric_of_lt_one (show 0 ≤ q by positivity)
      (show q < 1 by norm_num [q])).mul_left q
    have hval : q * (1 - q)⁻¹ = (1 / 127 : ℝ) := by norm_num [q]
    rw [hval] at h
    exact h.congr_fun fun k => pow_succ' q k
  have hss := squareTerm_hasSum n z
  have hsplit := hss.summable.sum_add_tsum_nat_add (j+2)
  rw [hss.tsum_eq, Finset.sum_range_succ, Finset.sum_range_succ] at hsplit
  let a := ‖squareTerm n j z‖
  let b := ‖squareTerm n (j+1) z‖
  have hleft : ‖∑ k ∈ Finset.range j, squareTerm n k z‖ ≤ a / 127 := by
    calc
      _ ≤ ∑ k ∈ Finset.range j, a * q ^ (j - k) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => hlo k (Finset.mem_range.mp hk))
      _ = ∑ k ∈ Finset.range j, a * q ^ (k + 1) := by
        rw [← Finset.sum_range_reflect (fun k => a * q ^ (j - k)) j]
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        have := Finset.mem_range.mp hk
        omega
      _ ≤ _ := by
        have hh := (hgeo.mul_left a).summable.sum_le_tsum (Finset.range j)
          (fun k _ => by positivity)
        rw [(hgeo.mul_left a).tsum_eq] at hh
        simpa [div_eq_mul_inv] using hh
  have hright : ‖∑' k : ℕ, squareTerm n (k + (j+2)) z‖ ≤ b / 127 := by
    have hbound (k : ℕ) : ‖squareTerm n (k+(j+2)) z‖ ≤ b * q ^ (k+1) := by
      simpa [b, q, show k + (j + 2) - (j + 1) = k + 1 by omega] using
        hhi (k+(j+2)) (by omega)
    have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hgeo.mul_left b).summable
    calc
      _ ≤ ∑' k : ℕ, ‖squareTerm n (k + (j+2)) z‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' k : ℕ, b * q ^ (k+1) := hs.tsum_mono (hgeo.mul_left b).summable hbound
      _ = _ := by simpa [div_eq_mul_inv] using (hgeo.mul_left b).tsum_eq
  rw [← hsplit, show (∑ k ∈ Finset.range j, squareTerm n k z) + squareTerm n j z +
      squareTerm n (j+1) z + (∑' k : ℕ, squareTerm n (k+(j+2)) z) -
      (squareTerm n j z + squareTerm n (j+1) z) =
      (∑ k ∈ Finset.range j, squareTerm n k z) + (∑' k : ℕ, squareTerm n (k+(j+2)) z) by ring]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ a/127 + b/127 := add_le_add hleft hright
    _ = _ := by ring

private lemma local_zero {n j : ℕ} (hj : 8 ≤ j) (hn : n < (j - 1) ^ 2)
    (hlo : Real.log (stepRadius n (j ^ 2 - j)) ≤ logCross n j - 100 / gap j)
    (hhi : logCross n j + 100 / gap j ≤ Real.log (stepRadius n ((j + 1) ^ 2 + j)))
    {w : ℂ} (hw : ‖w‖ = cross n j) (hwp : w ^ gap j = - (cross n j : ℂ) ^ gap j) :
    ∃ v : ℂ, ‖v‖ ≤ 1 / 2 ∧
      iteratedDeriv n sparseFunction (w * Complex.exp (v / (gap j : ℂ))) = 0 := by
  let d := gap j
  let r := cross n j
  have hd : 0 < d := by unfold d gap; omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : 0 < r := cross_pos _ _
  have hw₀ : w ≠ 0 := norm_pos_iff.mp (hw ▸ hr)
  have hnj : n < j ^ 2 := hn.trans_le (Nat.pow_le_pow_left (by omega) 2)
  have hns : n ≤ (j+1) ^ 2 := hnj.le.trans (Nat.pow_le_pow_left (Nat.le_succ _) 2)
  let z (v : ℂ) := w * Complex.exp (v / (d : ℂ))
  have hz (v : ℂ) : z v ≠ 0 := mul_ne_zero hw₀ (Complex.exp_ne_zero _)
  let g (v : ℂ) := iteratedDeriv n sparseFunction (z v) / squareTerm n j (z v)
  have htz (v : ℂ) : squareTerm n j (z v) ≠ 0 := by
    rw [squareTerm, if_pos hnj.le]
    exact mul_ne_zero (by exact_mod_cast (termCoeff_pos n (j ^ 2)).ne') (pow_ne_zero _ (hz v))
  have hzd : Differentiable ℂ z := by
    dsimp [z]; fun_prop
  have hgd : Differentiable ℂ g := by
    apply Differentiable.div
    · exact ((sparseFunction_diff.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by simp)).comp hzd
    · simp only [squareTerm, if_pos hnj.le]
      fun_prop
    · exact htz
  have he := realTerm_cross hnj.le
  have hpow : (j+1) ^ 2 - n = (j ^ 2 - n) + d := by
    have hh := square_succ_sub j
    omega
  have hcratio : termCoeff n ((j+1) ^ 2) * r ^ d = termCoeff n (j ^ 2) := by
    change termCoeff n ((j+1)^2) * r ^ ((j+1)^2 - n) =
      termCoeff n (j^2) * r ^ (j^2-n) at he
    rw [hpow, pow_add, mul_comm (r ^ (j ^ 2 - n)) (r ^ d), ← mul_assoc] at he
    exact mul_right_cancel₀ (pow_ne_zero _ hr.ne') he
  have hpair (v : ℂ) : squareTerm n (j+1) (z v) =
      -(squareTerm n j (z v) * Complex.exp v) := by
    have hh : z v ^ d = - (r : ℂ) ^ d * Complex.exp v := by
      rw [show z v = w * Complex.exp (v/(d:ℂ)) by rfl, mul_pow, exp_div_pow v hd, hwp]
    rw [squareTerm, squareTerm, if_pos hns, if_pos hnj.le, hpow, pow_add, hh]
    have hC : (termCoeff n ((j+1)^2) : ℂ) * (r : ℂ)^d = (termCoeff n (j^2) : ℂ) := by
      exact_mod_cast hcratio
    linear_combination - (z v) ^ (j^2-n) * Complex.exp v * hC
  have hgclose (v : ℂ) (hv : ‖v‖ ≤ 1/2) : ‖g v - (1 - Complex.exp v)‖ ≤ 1/16 := by
    have hrz : 0 < ‖z v‖ := norm_pos_iff.mpr (hz v)
    have hrel : Real.log ‖z v‖ = logCross n j + v.re / d := by
      rw [show z v = w * Complex.exp (v/(d:ℂ)) by rfl, norm_mul, hw, norm_exp_div v hd,
        Real.log_mul hr.ne' (Real.exp_pos _).ne', log_cross, Real.log_exp]
    have hre := Complex.abs_re_le_norm v
    have hbr := abs_le.mp hre
    have hlo' : logCross n j - 1 / (d:ℝ) ≤ Real.log ‖z v‖ := by
      rw [hrel]
      have hh : -(1 : ℝ) ≤ v.re := by linarith only [hv, hbr.1]
      simpa only [neg_div, sub_eq_add_neg] using add_le_add_right (div_le_div_of_nonneg_right hh hdR.le) (logCross n j)
    have hhi' : Real.log ‖z v‖ ≤ logCross n j + 1 / (d:ℝ) := by
      rw [hrel]
      have hh : v.re ≤ (1 : ℝ) := by linarith only [hv, hbr.2]
      exact add_le_add_right (div_le_div_of_nonneg_right hh hdR.le) _
    have h_tail := norm_two_tails (z := z v)
      (n := n) (j := j) (fun k hk => ?_) (fun k hk => ?_)
    · have heq : g v - (1 - Complex.exp v) =
          (iteratedDeriv n sparseFunction (z v) -
            (squareTerm n j (z v) + squareTerm n (j+1) (z v))) / squareTerm n j (z v) := by
        dsimp [g]
        rw [hpair]
        field_simp [htz v]
        ring
      rw [heq, norm_div, div_le_iff₀ (norm_pos_iff.mpr (htz v))]
      have hp : ‖squareTerm n (j+1) (z v)‖ ≤ 3 * ‖squareTerm n j (z v)‖ := by
        rw [hpair, norm_neg, norm_mul, Complex.norm_exp]
        have hh : v.re ≤ 1 := by linarith only [hv, hbr.2]
        have hx : Real.exp v.re ≤ 3 :=
          (Real.exp_le_exp.mpr hh).trans Real.exp_one_lt_three.le
        nlinarith [mul_le_mul_of_nonneg_left hx (norm_nonneg (squareTerm n j (z v)))]
      linarith [norm_nonneg (squareTerm n j (z v))]
    · by_cases h : n ≤ k^2
      · rw [squareTerm_norm h, squareTerm_norm hnj.le]
        apply log_tail_to_norm hrz
        rw [Nat.cast_sub hk.le]
        exact lower_tail_log hj hn hk h hrz hlo' hlo
      · simp [squareTerm, h]
    · have hn' : n ≤ k^2 := hns.trans (Nat.pow_le_pow_left hk.le 2)
      rw [squareTerm_norm hn', squareTerm_norm hns]
      apply log_tail_to_norm hrz
      rw [Nat.cast_sub hk.le, Nat.cast_add, Nat.cast_one]
      exact upper_tail_log hj hnj hk hrz hhi' hhi
  obtain ⟨v, hv, hgv⟩ := exists_zero_of_exp_model hgd hgclose
  exact ⟨v, hv, (div_eq_zero_iff.mp hgv).resolve_right (htz v)⟩

private lemma eventually_zero_ball {c : ℂ} (hc : c ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ z ∈ ball c ε, iteratedDeriv n sparseFunction z = 0 := by
  let R := ‖c‖
  let K := (R+1) * (2 * Real.pi + 1)
  have hR : 0 < R := norm_pos_iff.mpr hc
  have hK : 0 < K := mul_pos (by positivity) (by linarith [Real.pi_pos])
  have he := eventually_cross (D := max Real.pi (2*K/ε)) hR
    (show 0 < min (ε/2) 1 by exact lt_min (by positivity) (by norm_num))
  filter_upwards [he] with n hn
  obtain ⟨j, hj, hd, hnj, hr, hlo, hhi⟩ := hn
  have hdp := (le_max_left _ _).trans hd
  have hdR : (0 : ℝ) < gap j := Real.pi_pos.trans_le hdp
  have hdN : 0 < gap j := by exact_mod_cast hdR
  obtain ⟨w, hw, hwp, hwc⟩ := nearby_phase_root hc (cross_pos n j) hdp
  obtain ⟨v, hv, hvzero⟩ := local_zero hj hnj hlo hhi hw hwp
  let z := w * Complex.exp (v / (gap j : ℂ))
  refine ⟨z, mem_ball.mpr ?_, hvzero⟩
  rw [dist_eq_norm]
  have hnorm : ‖v/(gap j : ℂ)‖ ≤ (1 / 2 : ℝ) / gap j := by
    rw [norm_div, Complex.norm_natCast]
    gcongr
  have h₁ := Complex.norm_exp_sub_one_le (hnorm.trans
    ((div_le_iff₀ hdR).mpr (by linarith [Real.pi_gt_three])))
  have hzw : ‖z - w‖ ≤ cross n j / gap j := by
    rw [show z-w = w * (Complex.exp (v/(gap j:ℂ)) - 1) by dsimp [z]; ring, norm_mul, hw]
    have heq : cross n j / (gap j:ℝ) =
        cross n j * (2 * ((1/2 : ℝ) / gap j)) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (h₁.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num)))
      (cross_pos n j).le
  have hrc : cross n j ≤ R+1 := by
    have h := (abs_lt.mp (hr.trans_le (min_le_right _ _))).2
    linarith
  have hshift : K / (gap j : ℝ) ≤ ε/2 := by
    have h := (le_max_right Real.pi (2*K/ε)).trans hd
    exact (div_le_iff₀ hdR).mpr (by
      have hh := (div_le_iff₀ hε).mp h
      linarith)
  calc
    _ ≤ ‖z - w‖ + ‖w - c‖ := by simpa only [dist_eq_norm] using dist_triangle z w c
    _ ≤ |cross n j - R| + cross n j * (2 * Real.pi + 1) / gap j := by
      linarith [hzw, hwc, show cross n j * (2 * Real.pi + 1) / (gap j : ℝ) =
        cross n j / gap j + 2 * cross n j * Real.pi / gap j by ring]
    _ ≤ |cross n j - R| + K / gap j := by
      dsimp [K]
      gcongr
    _ < ε := by linarith [hr.trans_le (min_le_left (ε/2) 1)]

/-- The square-supported factorial series has zeros in every disk for all high derivatives. -/
private theorem completeProof : ∃ f : ℂ → ℂ, Transcendental (Polynomial ℂ) f ∧
    Differentiable ℂ f ∧ ∀ n : ℕ → ℕ, StrictMono n →
    Dense { z | ∃ k, iteratedDeriv (n k) f z = 0 } := by
  refine ⟨sparseFunction, transcendental_of_real_growth sparseFunction_growth,
    sparseFunction_diff, fun n hn => ?_⟩
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨c, hcU, hc⟩ : ∃ c ∈ U, (c : ℂ) ≠ 0 := by
    by_contra! h
    have hsub : U ⊆ {(0 : ℂ)} := fun x hx => h x hx
    have : U = {(0 : ℂ)} := hsub.antisymm (Set.singleton_subset_iff.mpr (by
      obtain ⟨x, hx⟩ := hUne
      simpa [h x hx] using hx))
    exact (not_isOpen_singleton (x := (0 : ℂ))) (this ▸ hU)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hcU
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_zero_ball hc hε)
  have hnn : N ≤ n N := hn.id_le N
  obtain ⟨z, hzU, hz₀⟩ := hN (n N) hnn
  exact ⟨z, hball hzU, N, hz₀⟩

end
end OMA

theorem OMA.solution : type_of% @Erdos906.erdos_906 := OMA.completeProof
