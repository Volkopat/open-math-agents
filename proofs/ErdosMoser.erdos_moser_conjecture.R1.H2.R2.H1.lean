import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R2
import Mathlib

/-!
# Proof of Step H1 of ErdosMoser.erdos_moser_conjecture.R1.H2.R2 (Gallot-Moree-Zudilin 2010)

Proves Gallot-Moree-Zudilin (2010) Theorem 1 and Corollary 1:
for any positive even integer `k` and integer `m > 10 ^ 9` with `k + 2 < m`, `2 * m < 3 * (k + 1)`,
and `ErdosMoser.powerSum k m = m ^ k`, we have
  `0 < Real.log 2 - (2 * k : ℝ) / (2 * m - 3 : ℝ) < 1 / (90 * (2 * m - 3 : ℝ) ^ 2)`
and therefore `((2 * k : ℚ) / (2 * m - 3 : ℚ))` is a continued fraction convergent of `Real.log 2`.
-/

namespace OMA.ErdosMoserGMZ

open Finset

/- ### Section 1: Elementary exponential and binomial-series inequalities -/

lemma exp_neg_bounds {δ : ℝ} (hδ0 : 0 < δ) :
    1 - δ + δ ^ 2 / 2 - δ ^ 3 / 6 < Real.exp (-δ) ∧
    Real.exp (-δ) < 1 - δ + δ ^ 2 / 2 := by
  let g1 : ℝ → ℝ := fun t => -1 + t + Real.exp (-t)
  have hg1_deriv : ∀ t : ℝ, HasDerivAt g1 (1 - Real.exp (-t)) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => -1 + u) 1 t := (hasDerivAt_id t).const_add (-1)
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_id t).neg.exp
    exact (h1.add h2).congr_deriv (by ring)
  have hg1_pos : ∀ t : ℝ, 0 < t → 0 < g1 t := by
    intro t ht
    have hmono : StrictMonoOn g1 (Set.Icc 0 t) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 t)
        (fun x _ => (hg1_deriv x).continuousAt.continuousWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      rw [(hg1_deriv x).deriv]
      have : Real.exp (-x) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith [hx.1])
      rw [Real.exp_zero] at this
      linarith
    have h0 := hmono (Set.left_mem_Icc.mpr ht.le) (Set.right_mem_Icc.mpr ht.le) ht
    simp only [g1, add_zero, neg_zero, Real.exp_zero, neg_add_cancel] at h0
    exact h0
  let g2 : ℝ → ℝ := fun t => 1 - t + t ^ 2 / 2 - Real.exp (-t)
  have hg2_deriv : ∀ t : ℝ, HasDerivAt g2 (g1 t) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := (hasDerivAt_id t).const_sub 1
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t :=
      ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by simp)
    have h3 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_id t).neg.exp
    exact ((h1.add h2).sub h3).congr_deriv (by dsimp only [g1]; ring)
  have hg2_pos : ∀ t : ℝ, 0 < t → 0 < g2 t := by
    intro t ht
    have hmono : StrictMonoOn g2 (Set.Icc 0 t) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 t)
        (fun x _ => (hg2_deriv x).continuousAt.continuousWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      rw [(hg2_deriv x).deriv]
      exact hg1_pos x hx.1
    have h0 := hmono (Set.left_mem_Icc.mpr ht.le) (Set.right_mem_Icc.mpr ht.le) ht
    simp only [g2, sub_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero, neg_zero,
      Real.exp_zero, sub_self] at h0
    exact h0
  let g3 : ℝ → ℝ := fun t => Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6)
  have hg3_deriv : ∀ t : ℝ, HasDerivAt g3 (g2 t) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_id t).neg.exp
    have h2 : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := (hasDerivAt_id t).const_sub 1
    have h3 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t :=
      ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by simp)
    have h4 : HasDerivAt (fun u : ℝ => u ^ 3 / 6) (t ^ 2 / 2) t :=
      ((hasDerivAt_pow 3 t).div_const 6).congr_deriv (by simp; ring)
    exact (h1.sub (((h2.add h3).sub h4))).congr_deriv (by dsimp only [g2]; ring)
  have hg3_pos : 0 < g3 δ := by
    have hmono : StrictMonoOn g3 (Set.Icc 0 δ) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 δ)
        (fun x _ => (hg3_deriv x).continuousAt.continuousWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      rw [(hg3_deriv x).deriv]
      exact hg2_pos x hx.1
    have h0 := hmono (Set.left_mem_Icc.mpr hδ0.le) (Set.right_mem_Icc.mpr hδ0.le) hδ0
    simp only [g3, neg_zero, Real.exp_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_pow (by norm_num : 3 ≠ 0), zero_div, add_zero, sub_self] at h0
    exact h0
  exact ⟨by dsimp only [g3] at hg3_pos; linarith, by have := hg2_pos δ hδ0; dsimp only [g2] at this; linarith⟩

lemma one_sub_mul_exp_bounds {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    1 - y ^ 2 / 2 - y ^ 3 / 3 - y ^ 4 / 8 - y ^ 5 / 30 - y ^ 6 / 120 < (1 - y) * Real.exp y ∧
    (1 - y) * Real.exp y < 1 - y ^ 2 / 2 - y ^ 3 / 3 - y ^ 4 / 8 := by
  constructor
  · have hexp := Real.sum_le_exp_of_nonneg hy0.le 7
    simp only [sum_range_succ, sum_range_zero, zero_add, Nat.factorial] at hexp
    norm_num at hexp
    have hy6 : 0 < y ^ 6 / 720 := by positivity
    have hlt : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 < Real.exp y := by
      linarith
    have hmul : (1 - y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120) <
        (1 - y) * Real.exp y := mul_lt_mul_of_pos_left hlt (by linarith)
    have halg : (1 - y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120) =
        1 - y ^ 2 / 2 - y ^ 3 / 3 - y ^ 4 / 8 - y ^ 5 / 30 - y ^ 6 / 120 := by ring
    linarith
  · let f : ℝ → ℝ := fun t => (1 - t ^ 2 / 2 - t ^ 3 / 3 - t ^ 4 / 8) - (1 - t) * Real.exp t
    have hf_deriv : ∀ t : ℝ, HasDerivAt f (t * (Real.exp t - (1 + t + t ^ 2 / 2))) t := by
      intro t
      have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t :=
        ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by simp)
      have h3 : HasDerivAt (fun u : ℝ => u ^ 3 / 3) (t ^ 2) t :=
        ((hasDerivAt_pow 3 t).div_const 3).congr_deriv (by simp)
      have h4 : HasDerivAt (fun u : ℝ => u ^ 4 / 8) (t ^ 3 / 2) t :=
        ((hasDerivAt_pow 4 t).div_const 8).congr_deriv (by simp; ring)
      have hpoly : HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2 - u ^ 3 / 3 - u ^ 4 / 8)
          (-t - t ^ 2 - t ^ 3 / 2) t :=
        (((h2.const_sub 1).sub h3).sub h4).congr_deriv (by ring)
      have hprod : HasDerivAt (fun u : ℝ => (1 - u) * Real.exp u) (-t * Real.exp t) t :=
        (((hasDerivAt_id t).const_sub 1).mul (Real.hasDerivAt_exp t)).congr_deriv (by
          simp only [id_eq]; ring)
      exact (hpoly.sub hprod).congr_deriv (by ring)
    have hmono : StrictMonoOn f (Set.Icc 0 y) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 y)
        (fun t _ => (hf_deriv t).continuousAt.continuousWithinAt) ?_
      intro t ht
      rw [interior_Icc] at ht
      rw [(hf_deriv t).deriv]
      have hexp := Real.sum_le_exp_of_nonneg ht.1.le 4
      simp only [sum_range_succ, sum_range_zero, zero_add, Nat.factorial] at hexp
      norm_num at hexp
      have ht3 : 0 < t ^ 3 / 6 := by positivity [ht.1]
      exact mul_pos ht.1 (by linarith)
    have h0 := hmono (Set.left_mem_Icc.mpr hy0.le) (Set.right_mem_Icc.mpr hy0.le) hy0
    simp only [f, zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 3 ≠ 0),
      zero_pow (by norm_num : 4 ≠ 0), zero_div, sub_zero, Real.exp_zero, mul_one, sub_self] at h0
    linarith

lemma hasDerivAt_one_sub_rpow {x r : ℝ} (hx : x < 1) :
    HasDerivAt (fun t : ℝ => (1 - t) ^ r) (-r * (1 - x) ^ (r - 1)) x := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := (hasDerivAt_id x).const_sub 1
  have h2 := h1.rpow_const (p := r) (Or.inl (by linarith : 1 - x ≠ 0))
  exact h2.congr_deriv (by ring)

lemma one_sub_rpow_bounds {α x : ℝ} (hα : 3 < α) (hx0 : 0 < x) (hx1 : x < 1) :
    1 - α * x + α * (α - 1) / 2 * x ^ 2 - α * (α - 1) * (α - 2) / 6 * x ^ 3 < (1 - x) ^ α ∧
    (1 - x) ^ α < 1 - α * x + α * (α - 1) / 2 * x ^ 2 := by
  have hstep1 : ∀ r t : ℝ, 1 < r → 0 < t → t < 1 → 1 - r * t < (1 - t) ^ r := by
    intro r t hr ht0 ht1
    let f : ℝ → ℝ := fun u => (1 - u) ^ r - (1 - r * u)
    have hf_deriv : ∀ u : ℝ, u < 1 → HasDerivAt f (r * (1 - (1 - u) ^ (r - 1))) u := by
      intro u hu
      have h1 := hasDerivAt_one_sub_rpow (r := r) hu
      have h2 : HasDerivAt (fun v : ℝ => 1 - r * v) (-r) u :=
        ((hasDerivAt_id u).const_mul r).const_sub 1 |>.congr_deriv (by ring)
      exact (h1.sub h2).congr_deriv (by ring)
    have hmono : StrictMonoOn f (Set.Icc 0 t) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 t) ?_ ?_
      · intro u hu
        exact (hf_deriv u (by linarith [hu.2])).continuousAt.continuousWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hu1 : u < 1 := lt_trans hu.2 ht1
        rw [(hf_deriv u hu1).deriv]
        have hlt : (1 - u) ^ (r - 1) < 1 := Real.rpow_lt_one (by linarith) (by linarith [hu.1]) (by linarith)
        exact mul_pos (by linarith) (by linarith)
    have h0 := hmono (Set.left_mem_Icc.mpr ht0.le) (Set.right_mem_Icc.mpr ht0.le) ht0
    simp only [f, sub_zero, Real.one_rpow, mul_zero, sub_self] at h0
    linarith
  have hstep2 : ∀ r t : ℝ, 2 < r → 0 < t → t < 1 →
      (1 - t) ^ r < 1 - r * t + r * (r - 1) / 2 * t ^ 2 := by
    intro r t hr ht0 ht1
    let f : ℝ → ℝ := fun u => 1 - r * u + r * (r - 1) / 2 * u ^ 2 - (1 - u) ^ r
    have hf_deriv : ∀ u : ℝ, u < 1 →
        HasDerivAt f (r * ((1 - u) ^ (r - 1) - (1 - (r - 1) * u))) u := by
      intro u hu
      have h1 : HasDerivAt (fun v : ℝ => 1 - r * v) (-r) u :=
        ((hasDerivAt_id u).const_mul r).const_sub 1 |>.congr_deriv (by ring)
      have h2 : HasDerivAt (fun v : ℝ => r * (r - 1) / 2 * v ^ 2) (r * (r - 1) * u) u :=
        ((hasDerivAt_pow 2 u).const_mul (r * (r - 1) / 2)).congr_deriv (by simp; ring)
      have h3 := hasDerivAt_one_sub_rpow (r := r) hu
      exact ((h1.add h2).sub h3).congr_deriv (by ring)
    have hmono : StrictMonoOn f (Set.Icc 0 t) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 t) ?_ ?_
      · intro u hu
        exact (hf_deriv u (by linarith [hu.2])).continuousAt.continuousWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hu1 : u < 1 := lt_trans hu.2 ht1
        rw [(hf_deriv u hu1).deriv]
        have hlt := hstep1 (r - 1) u (by linarith) hu.1 hu1
        exact mul_pos (by linarith) (by linarith)
    have h0 := hmono (Set.left_mem_Icc.mpr ht0.le) (Set.right_mem_Icc.mpr ht0.le) ht0
    simp only [f, mul_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.one_rpow,
      sub_self] at h0
    linarith
  have hstep3 : 1 - α * x + α * (α - 1) / 2 * x ^ 2 - α * (α - 1) * (α - 2) / 6 * x ^ 3 <
      (1 - x) ^ α := by
    let f : ℝ → ℝ := fun u =>
      (1 - u) ^ α - (1 - α * u + α * (α - 1) / 2 * u ^ 2 - α * (α - 1) * (α - 2) / 6 * u ^ 3)
    have hf_deriv : ∀ u : ℝ, u < 1 →
        HasDerivAt f (α * (1 - (α - 1) * u + (α - 1) * (α - 2) / 2 * u ^ 2 - (1 - u) ^ (α - 1))) u := by
      intro u hu
      have h0 := hasDerivAt_one_sub_rpow (r := α) hu
      have h1 : HasDerivAt (fun v : ℝ => 1 - α * v) (-α) u :=
        ((hasDerivAt_id u).const_mul α).const_sub 1 |>.congr_deriv (by ring)
      have h2 : HasDerivAt (fun v : ℝ => α * (α - 1) / 2 * v ^ 2) (α * (α - 1) * u) u :=
        ((hasDerivAt_pow 2 u).const_mul (α * (α - 1) / 2)).congr_deriv (by simp; ring)
      have h3 : HasDerivAt (fun v : ℝ => α * (α - 1) * (α - 2) / 6 * v ^ 3)
          (α * (α - 1) * (α - 2) / 2 * u ^ 2) u :=
        ((hasDerivAt_pow 3 u).const_mul (α * (α - 1) * (α - 2) / 6)).congr_deriv (by simp; ring)
      exact (h0.sub ((h1.add h2).sub h3)).congr_deriv (by ring)
    have hmono : StrictMonoOn f (Set.Icc 0 x) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 x) ?_ ?_
      · intro u hu
        exact (hf_deriv u (by linarith [hu.2])).continuousAt.continuousWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hu1 : u < 1 := lt_trans hu.2 hx1
        rw [(hf_deriv u hu1).deriv]
        have hlt := hstep2 (α - 1) u (by linarith) hu.1 hu1
        have hrew : α - 1 - 1 = α - 2 := by ring
        rw [hrew] at hlt
        exact mul_pos (by linarith) (by linarith)
    have h0 := hmono (Set.left_mem_Icc.mpr hx0.le) (Set.right_mem_Icc.mpr hx0.le) hx0
    simp only [f, sub_zero, Real.one_rpow, mul_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_pow (by norm_num : 3 ≠ 0), add_zero, sub_self] at h0
    linarith
  exact ⟨hstep3, hstep2 α x (by linarith) hx0 hx1⟩

lemma gmz_term_bounds {α y : ℝ} (hα : 10 ≤ α) (hy0 : 0 < y) (hy1 : y < 1) :
    Real.exp (-α * y) * (1 - α / 2 * y ^ 2 - α / 3 * y ^ 3 + α * (α - 2) / 8 * y ^ 4 +
        α * (5 * α - 6) / 30 * y ^ 5 - α ^ 3 / 6 * y ^ 6) < (1 - y) ^ α ∧
    (1 - y) ^ α <
      Real.exp (-α * y) * (1 - α / 2 * y ^ 2 - α / 3 * y ^ 3 + α * (α - 2) / 8 * y ^ 4 +
        α ^ 2 / 2 * y ^ 5) := by
  set x1 := y ^ 2 / 2 + y ^ 3 / 3 + y ^ 4 / 8
  set x2 := y ^ 2 / 2 + y ^ 3 / 3 + y ^ 4 / 8 + y ^ 5 / 30 + y ^ 6 / 120
  have hx1_pos : 0 < x1 := by dsimp only [x1]; positivity
  have hx2_pos : 0 < x2 := by dsimp only [x2]; positivity
  have hy2 : y ^ 2 < 1 := pow_lt_one₀ hy0.le hy1 (by norm_num)
  have hy3 : y ^ 3 < y ^ 2 := pow_lt_pow_right_of_lt_one₀ hy0 hy1 (by norm_num)
  have hy4 : y ^ 4 < y ^ 2 := pow_lt_pow_right_of_lt_one₀ hy0 hy1 (by norm_num)
  have hy5 : y ^ 5 < y ^ 2 := pow_lt_pow_right_of_lt_one₀ hy0 hy1 (by norm_num)
  have hy6 : y ^ 6 < y ^ 2 := pow_lt_pow_right_of_lt_one₀ hy0 hy1 (by norm_num)
  have hy6_5 : y ^ 6 < y ^ 5 := pow_lt_pow_right_of_lt_one₀ hy0 hy1 (by norm_num)
  have hy7_5 : y ^ 7 < y ^ 5 := pow_lt_pow_right_of_lt_one₀ hy0 hy1 (by norm_num)
  have hy8_5 : y ^ 8 < y ^ 5 := pow_lt_pow_right_of_lt_one₀ hy0 hy1 (by norm_num)
  have hx2_le_y2 : x2 < y ^ 2 := by dsimp only [x2]; linarith
  have hx2_lt1 : x2 < 1 := lt_trans hx2_le_y2 hy2
  have hx1_lt1 : x1 < 1 := by
    have hpos : 0 < y ^ 5 / 30 + y ^ 6 / 120 := by positivity
    dsimp only [x1, x2] at *; linarith
  have ⟨h1_lo, h1_hi⟩ := one_sub_mul_exp_bounds hy0 hy1
  have hmul_eq : ((1 - y) * Real.exp y) ^ α = (1 - y) ^ α * Real.exp (α * y) := by
    rw [Real.mul_rpow (by linarith) (Real.exp_pos y).le, ← Real.exp_mul, mul_comm y α]
  have hexp_pos : 0 < Real.exp (-α * y) := Real.exp_pos _
  have hexp_cancel : Real.exp (-α * y) * Real.exp (α * y) = 1 := by
    rw [← Real.exp_add]; simp
  constructor
  · have hr1 : (1 - x2) ^ α < ((1 - y) * Real.exp y) ^ α :=
      Real.rpow_lt_rpow (by linarith) (by dsimp only [x2]; linarith) (by linarith)
    have hr2 := (one_sub_rpow_bounds (by linarith : 3 < α) hx2_pos hx2_lt1).1
    have hx2_sq : y ^ 4 / 4 + y ^ 5 / 3 + y ^ 6 / 5 ≤ x2 ^ 2 := by
      have hbase : x1 ≤ x2 := by
        dsimp only [x1, x2]; linarith [show 0 ≤ y ^ 5 / 30 + y ^ 6 / 120 by positivity]
      have hsq1 : x1 ^ 2 ≤ x2 ^ 2 := pow_le_pow_left₀ hx1_pos.le hbase 2
      have hexp2 : x1 ^ 2 =
          y ^ 4 / 4 + y ^ 5 / 3 + (17 / 72 : ℝ) * y ^ 6 + y ^ 7 / 12 + y ^ 8 / 64 := by
        dsimp only [x1]; ring
      have hpos78 : 0 ≤ y ^ 7 / 12 + y ^ 8 / 64 := by positivity
      have hy6nn : 0 ≤ y ^ 6 := by positivity
      linarith
    have hx2_cu : x2 ^ 3 ≤ y ^ 6 := by
      have h1 : x2 ^ 3 ≤ (y ^ 2) ^ 3 := pow_le_pow_left₀ hx2_pos.le hx2_le_y2.le 3
      simpa [← pow_mul] using h1
    have hpoly_lo : 1 - α / 2 * y ^ 2 - α / 3 * y ^ 3 + α * (α - 2) / 8 * y ^ 4 +
        α * (5 * α - 6) / 30 * y ^ 5 - α ^ 3 / 6 * y ^ 6 ≤
        1 - α * x2 + α * (α - 1) / 2 * x2 ^ 2 - α * (α - 1) * (α - 2) / 6 * x2 ^ 3 := by
      have hc2_nn : 0 ≤ α * (α - 1) / 2 := by nlinarith only [hα]
      have ht1 : α * (α - 1) / 2 * (y ^ 4 / 4 + y ^ 5 / 3 + y ^ 6 / 5) ≤
          α * (α - 1) / 2 * x2 ^ 2 := mul_le_mul_of_nonneg_left hx2_sq hc2_nn
      have hcoef3 : α * (α - 1) * (α - 2) / 6 ≤ α ^ 3 / 6 := by
        have h1 : α ^ 3 - α * (α - 1) * (α - 2) = 3 * α ^ 2 - 2 * α := by ring
        have h2 : 0 ≤ 3 * α ^ 2 - 2 * α := by nlinarith only [hα]
        linarith only [h1, h2]
      have ht2 : α * (α - 1) * (α - 2) / 6 * x2 ^ 3 ≤ α ^ 3 / 6 * y ^ 6 :=
        mul_le_mul hcoef3 hx2_cu (by positivity) (by positivity)
      have hrem : 0 ≤ (α * (α - 1) / 10 - α / 120) * y ^ 6 := by
        have hc : 0 ≤ α * (α - 1) / 10 - α / 120 := by nlinarith only [hα]
        exact mul_nonneg hc (by positivity)
      have hdiff_id :
          (1 - α * x2 + α * (α - 1) / 2 * (y ^ 4 / 4 + y ^ 5 / 3 + y ^ 6 / 5) - α ^ 3 / 6 * y ^ 6) -
          (1 - α / 2 * y ^ 2 - α / 3 * y ^ 3 + α * (α - 2) / 8 * y ^ 4 +
            α * (5 * α - 6) / 30 * y ^ 5 - α ^ 3 / 6 * y ^ 6) =
          (α * (α - 1) / 10 - α / 120) * y ^ 6 := by dsimp only [x2]; ring
      linarith only [ht1, ht2, hrem, hdiff_id]
    have hlt : 1 - α / 2 * y ^ 2 - α / 3 * y ^ 3 + α * (α - 2) / 8 * y ^ 4 +
        α * (5 * α - 6) / 30 * y ^ 5 - α ^ 3 / 6 * y ^ 6 < (1 - y) ^ α * Real.exp (α * y) := by
      rw [← hmul_eq]
      exact lt_of_le_of_lt hpoly_lo (lt_trans hr2 hr1)
    have hmul := mul_lt_mul_of_pos_left hlt hexp_pos
    have hrhs : Real.exp (-α * y) * ((1 - y) ^ α * Real.exp (α * y)) = (1 - y) ^ α := by
      rw [mul_left_comm, hexp_cancel, mul_one]
    linarith only [hmul, hrhs]
  · have hr1 : ((1 - y) * Real.exp y) ^ α < (1 - x1) ^ α :=
      Real.rpow_lt_rpow (mul_nonneg (by linarith) (Real.exp_pos y).le) (by dsimp only [x1]; linarith) (by linarith)
    have hr2 := (one_sub_rpow_bounds (by linarith : 3 < α) hx1_pos hx1_lt1).2
    have hx1_sq : x1 ^ 2 ≤ y ^ 4 / 4 + y ^ 5 := by
      have hexp1 : x1 ^ 2 = y ^ 4 / 4 + y ^ 5 / 3 + (17 / 72 : ℝ) * y ^ 6 + y ^ 7 / 12 + y ^ 8 / 64 := by
        dsimp only [x1]; ring
      have hy5_pos : 0 < y ^ 5 := pow_pos hy0 5
      linarith only [hexp1, hy6_5, hy7_5, hy8_5, hy5_pos]
    have hpoly_hi : 1 - α * x1 + α * (α - 1) / 2 * x1 ^ 2 ≤
        1 - α / 2 * y ^ 2 - α / 3 * y ^ 3 + α * (α - 2) / 8 * y ^ 4 + α ^ 2 / 2 * y ^ 5 := by
      have hc2_nn : 0 ≤ α * (α - 1) / 2 := by nlinarith only [hα]
      have ht1 : α * (α - 1) / 2 * x1 ^ 2 ≤ α * (α - 1) / 2 * (y ^ 4 / 4 + y ^ 5) :=
        mul_le_mul_of_nonneg_left hx1_sq hc2_nn
      have hid : 1 - α * x1 + α * (α - 1) / 2 * (y ^ 4 / 4 + y ^ 5) -
          (1 - α / 2 * y ^ 2 - α / 3 * y ^ 3 + α * (α - 2) / 8 * y ^ 4 + α ^ 2 / 2 * y ^ 5) =
          -(α / 2) * y ^ 5 := by dsimp only [x1]; ring
      have hneg : 0 ≤ (α / 2) * y ^ 5 := by positivity
      linarith only [ht1, hid, hneg]
    have hlt : (1 - y) ^ α * Real.exp (α * y) <
        1 - α / 2 * y ^ 2 - α / 3 * y ^ 3 + α * (α - 2) / 8 * y ^ 4 + α ^ 2 / 2 * y ^ 5 := by
      rw [← hmul_eq]
      exact lt_of_lt_of_le (lt_trans hr1 hr2) hpoly_hi
    have hmul := mul_lt_mul_of_pos_left hlt hexp_pos
    have hlhs : Real.exp (-α * y) * ((1 - y) ^ α * Real.exp (α * y)) = (1 - y) ^ α := by
      rw [mul_left_comm, hexp_cancel, mul_one]
    linarith only [hmul, hlhs]

lemma exp_neg_lt_inv_pow_five {α m : ℝ} (hm : (10 ^ 9 : ℝ) < m) (hα : (0.6 : ℝ) * m < α) :
    Real.exp (-α) < 1 / m ^ 5 := by
  have hm_pos : 0 < m := by linarith
  have hα_pos : 0 < α := by nlinarith
  rw [Real.exp_neg, inv_eq_one_div]
  refine one_div_lt_one_div_of_lt (by positivity) ?_
  have hexp6 := Real.sum_le_exp_of_nonneg hα_pos.le 7
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.factorial] at hexp6
  norm_num at hexp6
  have h1 : (0.6 * m) ^ 6 < α ^ 6 := pow_lt_pow_left₀ hα (by positivity) (by norm_num)
  have h2 : m ^ 5 < (0.6 * m) ^ 6 / 720 := by
    have : (0.6 * m) ^ 6 / 720 = (0.046656 / 720 : ℝ) * m ^ 6 := by ring
    rw [this]
    have hm5 : 0 < m ^ 5 := pow_pos hm_pos 5
    have h6 : m ^ 6 = m ^ 5 * m := by ring
    rw [h6]
    nlinarith
  have hnn : 0 ≤ 1 + α + α ^ 2 / 2 + α ^ 3 / 6 + α ^ 4 / 24 + α ^ 5 / 120 := by positivity
  linarith

/- ### Section 2: Finite geometric power-sum telescoping (no infinite series) -/

lemma geom_power_sum_step (n m : ℕ) (hm : 1 ≤ m) {w : ℝ} (hw : 0 < w) :
    (w - 1) * (∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-(j : ℤ))) =
      1 + (∑ j ∈ Ico 1 m, (((j + 1 : ℝ) ^ n - (j : ℝ) ^ n) * w ^ (-(j : ℤ)))) -
      (m : ℝ) ^ n * w ^ (-((m - 1 : ℕ) : ℤ)) := by
  have hw0 : w ≠ 0 := hw.ne'
  have hmul : w * (∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-(j : ℤ))) =
      ∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-((j - 1 : ℕ) : ℤ)) := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
    have hpow : w * w ^ (-(j : ℤ)) = w ^ (-((j - 1 : ℕ) : ℤ)) := by
      rw [← zpow_one_add₀ hw0]
      congr 1; omega
    rw [← mul_assoc, mul_comm w, mul_assoc, hpow]
  have hshift : ∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-((j - 1 : ℕ) : ℤ)) =
      ∑ j ∈ range (m - 1), ((j + 1 : ℝ) ^ n * w ^ (-(j : ℤ))) := by
    refine sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Ico, mem_range] at hj ⊢; omega
    · intro a ha b hb hab; simp only [mem_Ico] at ha hb; omega
    · intro r hr; simp only [mem_range] at hr
      exact ⟨r + 1, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj
      have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
      have hcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
        rw [Nat.cast_sub hj1, Nat.cast_one]; ring
      rw [hcast]
  have hsplit : (∑ j ∈ range (m - 1), ((j + 1 : ℝ) ^ n * w ^ (-(j : ℤ)))) +
      (m : ℝ) ^ n * w ^ (-((m - 1 : ℕ) : ℤ)) =
      1 + ∑ j ∈ Ico 1 m, ((j + 1 : ℝ) ^ n * w ^ (-(j : ℤ))) := by
    have h1 : (∑ j ∈ range (m - 1), ((j + 1 : ℝ) ^ n * w ^ (-(j : ℤ)))) +
        (m : ℝ) ^ n * w ^ (-((m - 1 : ℕ) : ℤ)) =
        ∑ j ∈ range m, ((j + 1 : ℝ) ^ n * w ^ (-(j : ℤ))) := by
      have hm_eq : m = (m - 1) + 1 := by omega
      conv_rhs => rw [hm_eq, sum_range_succ]
      have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
        rw [Nat.cast_sub hm, Nat.cast_one]; ring
      rw [hcast]
    rw [h1, range_eq_Ico, sum_eq_sum_Ico_succ_bot hm]
    simp
  have hsub : (∑ j ∈ Ico 1 m, ((j + 1 : ℝ) ^ n * w ^ (-(j : ℤ)))) -
      (∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-(j : ℤ))) =
      ∑ j ∈ Ico 1 m, (((j + 1 : ℝ) ^ n - (j : ℝ) ^ n) * w ^ (-(j : ℤ))) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => by ring
  have hdist : (w - 1) * (∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-(j : ℤ))) =
      w * (∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-(j : ℤ))) -
      (∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-(j : ℤ))) := by ring
  linarith

lemma geom_power_sum_bounds {m : ℕ} (hm : 10 ≤ m) {w : ℝ} (hw1 : (1.9 : ℝ) < w) (hw2 : w < 2.1) :
    let T : ℕ → ℝ := fun n => ∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-(j : ℤ))
    let wm : ℝ := w ^ (-(m : ℤ))
    (0 < 1 / (w - 1) - T 0 ∧ 1 / (w - 1) - T 0 < 3 * wm) ∧
    (0 < (w + w ^ 2) / (w - 1) ^ 3 - T 2 ∧ (w + w ^ 2) / (w - 1) ^ 3 - T 2 < 20 * (m : ℝ) ^ 2 * wm) ∧
    (0 < (w + 4 * w ^ 2 + w ^ 3) / (w - 1) ^ 4 - T 3 ∧
      (w + 4 * w ^ 2 + w ^ 3) / (w - 1) ^ 4 - T 3 < 100 * (m : ℝ) ^ 3 * wm) ∧
    (0 < (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) / (w - 1) ^ 5 - T 4 ∧
      (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) / (w - 1) ^ 5 - T 4 < 600 * (m : ℝ) ^ 4 * wm) ∧
    (0 < T 5 ∧ T 5 < (w + 26 * w ^ 2 + 66 * w ^ 3 + 26 * w ^ 4 + w ^ 5) / (w - 1) ^ 6) ∧
    (0 < T 6 ∧ T 6 < (w + 57 * w ^ 2 + 302 * w ^ 3 + 302 * w ^ 4 + 57 * w ^ 5 + w ^ 6) / (w - 1) ^ 7) := by
  intro T wm
  have hw0 : 0 < w := by linarith
  have hw_sub : (0.9 : ℝ) < w - 1 := by linarith
  have hmR : (10 : ℝ) ≤ m := by exact_mod_cast hm
  have hwm_pos : 0 < wm := zpow_pos hw0 _
  have hwm1 : w ^ (-((m - 1 : ℕ) : ℤ)) = w * wm := by
    dsimp only [wm]
    rw [← zpow_one_add₀ hw0.ne']
    congr 1; omega
  set P0 : ℝ := 1 / (w - 1)
  set P1 : ℝ := w / (w - 1) ^ 2
  set P2 : ℝ := (w + w ^ 2) / (w - 1) ^ 3
  set P3 : ℝ := (w + 4 * w ^ 2 + w ^ 3) / (w - 1) ^ 4
  set P4 : ℝ := (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) / (w - 1) ^ 5
  set P5 : ℝ := (w + 26 * w ^ 2 + 66 * w ^ 3 + 26 * w ^ 4 + w ^ 5) / (w - 1) ^ 6
  set P6 : ℝ := (w + 57 * w ^ 2 + 302 * w ^ 3 + 302 * w ^ 4 + 57 * w ^ 5 + w ^ 6) / (w - 1) ^ 7
  have hP0 : (w - 1) * P0 = 1 := by dsimp only [P0]; field_simp
  have hP1 : (w - 1) * P1 = 1 + P0 := by dsimp only [P1, P0]; field_simp; ring
  have hP2 : (w - 1) * P2 = 1 + 2 * P1 + P0 := by dsimp only [P2, P1, P0]; field_simp; ring
  have hP3 : (w - 1) * P3 = 1 + 3 * P2 + 3 * P1 + P0 := by dsimp only [P3, P2, P1, P0]; field_simp; ring
  have hP4 : (w - 1) * P4 = 1 + 4 * P3 + 6 * P2 + 4 * P1 + P0 := by
    dsimp only [P4, P3, P2, P1, P0]; field_simp; ring
  have hP5 : (w - 1) * P5 = 1 + 5 * P4 + 10 * P3 + 10 * P2 + 5 * P1 + P0 := by
    dsimp only [P5, P4, P3, P2, P1, P0]; field_simp; ring
  have hP6 : (w - 1) * P6 = 1 + 6 * P5 + 15 * P4 + 20 * P3 + 15 * P2 + 6 * P1 + P0 := by
    dsimp only [P6, P5, P4, P3, P2, P1, P0]; field_simp; ring
  have hT0 : (w - 1) * T 0 = 1 - w * wm := by
    have h := geom_power_sum_step 0 m (by omega) hw0
    simp only [pow_zero, sub_self, zero_mul, sum_const_zero, add_zero, one_mul, hwm1] at h
    dsimp only [T]
    simpa [pow_zero, one_mul] using h
  have hT1 : (w - 1) * T 1 = 1 + T 0 - (m : ℝ) * (w * wm) := by
    have h := geom_power_sum_step 1 m (by omega) hw0
    rw [hwm1] at h
    have hs : ∑ j ∈ Ico 1 m, (((j + 1 : ℝ) ^ 1 - (j : ℝ) ^ 1) * w ^ (-(j : ℤ))) = T 0 := by
      refine sum_congr rfl fun j _ => by ring
    rw [hs, pow_one] at h; exact h
  have hT2 : (w - 1) * T 2 = 1 + 2 * T 1 + T 0 - (m : ℝ) ^ 2 * (w * wm) := by
    have h := geom_power_sum_step 2 m (by omega) hw0
    rw [hwm1] at h
    have hs : ∑ j ∈ Ico 1 m, (((j + 1 : ℝ) ^ 2 - (j : ℝ) ^ 2) * w ^ (-(j : ℤ))) = 2 * T 1 + T 0 := by
      dsimp only [T]
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => by ring
    rw [hs] at h; linarith only [h]
  have hT3 : (w - 1) * T 3 = 1 + 3 * T 2 + 3 * T 1 + T 0 - (m : ℝ) ^ 3 * (w * wm) := by
    have h := geom_power_sum_step 3 m (by omega) hw0
    rw [hwm1] at h
    have hs : ∑ j ∈ Ico 1 m, (((j + 1 : ℝ) ^ 3 - (j : ℝ) ^ 3) * w ^ (-(j : ℤ))) =
        3 * T 2 + 3 * T 1 + T 0 := by
      dsimp only [T]
      rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => by ring
    rw [hs] at h; linarith only [h]
  have hT4 : (w - 1) * T 4 = 1 + 4 * T 3 + 6 * T 2 + 4 * T 1 + T 0 - (m : ℝ) ^ 4 * (w * wm) := by
    have h := geom_power_sum_step 4 m (by omega) hw0
    rw [hwm1] at h
    have hs : ∑ j ∈ Ico 1 m, (((j + 1 : ℝ) ^ 4 - (j : ℝ) ^ 4) * w ^ (-(j : ℤ))) =
        4 * T 3 + 6 * T 2 + 4 * T 1 + T 0 := by
      dsimp only [T]
      simp_rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => by ring
    rw [hs] at h; linarith only [h]
  have hT5 : (w - 1) * T 5 = 1 + 5 * T 4 + 10 * T 3 + 10 * T 2 + 5 * T 1 + T 0 - (m : ℝ) ^ 5 * (w * wm) := by
    have h := geom_power_sum_step 5 m (by omega) hw0
    rw [hwm1] at h
    have hs : ∑ j ∈ Ico 1 m, (((j + 1 : ℝ) ^ 5 - (j : ℝ) ^ 5) * w ^ (-(j : ℤ))) =
        5 * T 4 + 10 * T 3 + 10 * T 2 + 5 * T 1 + T 0 := by
      dsimp only [T]
      simp_rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => by ring
    rw [hs] at h; linarith only [h]
  have hT6 : (w - 1) * T 6 = 1 + 6 * T 5 + 15 * T 4 + 20 * T 3 + 15 * T 2 + 6 * T 1 + T 0 -
      (m : ℝ) ^ 6 * (w * wm) := by
    have h := geom_power_sum_step 6 m (by omega) hw0
    rw [hwm1] at h
    have hs : ∑ j ∈ Ico 1 m, (((j + 1 : ℝ) ^ 6 - (j : ℝ) ^ 6) * w ^ (-(j : ℤ))) =
        6 * T 5 + 15 * T 4 + 20 * T 3 + 15 * T 2 + 6 * T 1 + T 0 := by
      dsimp only [T]
      simp_rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => by ring
    rw [hs] at h; linarith only [h]
  -- Helper: if (w - 1) * e = rhs and rhs < (0.9) * bound then e < bound
  have hdiv_ub : ∀ e rhs bd : ℝ, (w - 1) * e = rhs → 0 < e → rhs < (0.9 : ℝ) * bd → e < bd := by
    intro e rhs bd heq hpos hlt
    have h1 : (0.9 : ℝ) * e < (w - 1) * e := mul_lt_mul_of_pos_right hw_sub hpos
    linarith only [heq, h1, hlt]
  have hpos_of : ∀ e rhs : ℝ, (w - 1) * e = rhs → 0 < rhs → 0 < e := by
    intro e rhs heq hpos
    by_contra hle; push Not at hle
    have : (w - 1) * e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hle
    linarith only [heq, hpos, this]
  have hwwm_lt : w * wm < 2.1 * wm := mul_lt_mul_of_pos_right hw2 hwm_pos
  have hwwm_pos : 0 < w * wm := mul_pos hw0 hwm_pos
  have hm1_le : (1 : ℝ) ≤ m := by linarith
  have hm2_le : (m : ℝ) ≤ (m : ℝ) ^ 2 / 10 := by nlinarith only [hmR]
  have hm02_le : (1 : ℝ) ≤ (m : ℝ) ^ 2 / 100 := by nlinarith only [hmR]
  have hm23_le : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 / 10 := by
    have : (m : ℝ) ^ 3 = (m : ℝ) ^ 2 * m := by ring
    nlinarith only [hmR, this, pow_pos (by linarith : (0 : ℝ) < m) 2]
  have hm13_le : (m : ℝ) ≤ (m : ℝ) ^ 3 / 100 := by linarith only [hm2_le, hm23_le]
  have hm03_le : (1 : ℝ) ≤ (m : ℝ) ^ 3 / 1000 := by linarith only [hm02_le, hm23_le]
  have hm34_le : (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 4 / 10 := by
    have : (m : ℝ) ^ 4 = (m : ℝ) ^ 3 * m := by ring
    nlinarith only [hmR, this, pow_pos (by linarith : (0 : ℝ) < m) 3]
  have hm24_le : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 / 100 := by linarith only [hm23_le, hm34_le]
  have hm14_le : (m : ℝ) ≤ (m : ℝ) ^ 4 / 1000 := by linarith only [hm13_le, hm34_le]
  have hm04_le : (1 : ℝ) ≤ (m : ℝ) ^ 4 / 10000 := by linarith only [hm03_le, hm34_le]
  have hE0_eq : (w - 1) * (P0 - T 0) = w * wm := by linarith only [hP0, hT0]
  have hE0_pos : 0 < P0 - T 0 := hpos_of _ _ hE0_eq hwwm_pos
  have hE0_ub : P0 - T 0 < 3 * wm := hdiv_ub _ _ _ hE0_eq hE0_pos (by linarith only [hwwm_lt, hwm_pos])
  have hE1_eq : (w - 1) * (P1 - T 1) = (P0 - T 0) + (m : ℝ) * (w * wm) := by linarith only [hP1, hT1]
  have hE1_pos : 0 < P1 - T 1 := hpos_of _ _ hE1_eq (by positivity)
  have hE1_ub : P1 - T 1 < 6 * (m : ℝ) * wm := by
    refine hdiv_ub _ _ _ hE1_eq hE1_pos ?_
    have h1 : (m : ℝ) * (w * wm) < 2.1 * (m : ℝ) * wm := by
      have := mul_lt_mul_of_pos_left hwwm_lt (by linarith : (0 : ℝ) < m)
      have hrew : (m : ℝ) * (2.1 * wm) = 2.1 * (m : ℝ) * wm := by ring
      linarith only [this, hrew]
    have h2 : 3 * wm ≤ 0.3 * (m : ℝ) * wm := by nlinarith only [hmR, hwm_pos]
    have hmw : 0 < (m : ℝ) * wm := by positivity
    linarith only [hE0_ub, h1, h2, hmw]
  have hE2_eq : (w - 1) * (P2 - T 2) = 2 * (P1 - T 1) + (P0 - T 0) + (m : ℝ) ^ 2 * (w * wm) := by
    linarith only [hP2, hT2]
  have hE2_pos : 0 < P2 - T 2 := hpos_of _ _ hE2_eq (by positivity)
  have hE2_ub : P2 - T 2 < 20 * (m : ℝ) ^ 2 * wm := by
    refine hdiv_ub _ _ _ hE2_eq hE2_pos ?_
    have h1 : (m : ℝ) ^ 2 * (w * wm) < (m : ℝ) ^ 2 * (2.1 * wm) :=
      mul_lt_mul_of_pos_left hwwm_lt (by positivity)
    have h2 : 2 * (6 * (m : ℝ) * wm) ≤ 1.2 * (m : ℝ) ^ 2 * wm := by
      have := mul_le_mul_of_nonneg_right hm2_le hwm_pos.le; linarith only [this]
    have h3 : 3 * wm ≤ 0.03 * (m : ℝ) ^ 2 * wm := by
      have := mul_le_mul_of_nonneg_right hm02_le hwm_pos.le; linarith only [this]
    have hm2wm : 0 < (m : ℝ) ^ 2 * wm := by positivity
    linarith only [hE1_ub, hE0_ub, h1, h2, h3, hm2wm]
  have hE3_eq : (w - 1) * (P3 - T 3) =
      3 * (P2 - T 2) + 3 * (P1 - T 1) + (P0 - T 0) + (m : ℝ) ^ 3 * (w * wm) := by
    linarith only [hP3, hT3]
  have hE3_pos : 0 < P3 - T 3 := hpos_of _ _ hE3_eq (by positivity)
  have hE3_ub : P3 - T 3 < 100 * (m : ℝ) ^ 3 * wm := by
    refine hdiv_ub _ _ _ hE3_eq hE3_pos ?_
    have h1 : (m : ℝ) ^ 3 * (w * wm) < (m : ℝ) ^ 3 * (2.1 * wm) :=
      mul_lt_mul_of_pos_left hwwm_lt (by positivity)
    have h2 : 3 * (20 * (m : ℝ) ^ 2 * wm) ≤ 6 * (m : ℝ) ^ 3 * wm := by
      have := mul_le_mul_of_nonneg_right hm23_le hwm_pos.le; linarith only [this]
    have h3 : 3 * (6 * (m : ℝ) * wm) ≤ 0.18 * (m : ℝ) ^ 3 * wm := by
      have := mul_le_mul_of_nonneg_right hm13_le hwm_pos.le; linarith only [this]
    have h4 : 3 * wm ≤ 0.003 * (m : ℝ) ^ 3 * wm := by
      have := mul_le_mul_of_nonneg_right hm03_le hwm_pos.le; linarith only [this]
    have hm3wm : 0 < (m : ℝ) ^ 3 * wm := by positivity
    linarith only [hE2_ub, hE1_ub, hE0_ub, h1, h2, h3, h4, hm3wm]
  have hE4_eq : (w - 1) * (P4 - T 4) =
      4 * (P3 - T 3) + 6 * (P2 - T 2) + 4 * (P1 - T 1) + (P0 - T 0) + (m : ℝ) ^ 4 * (w * wm) := by
    linarith only [hP4, hT4]
  have hE4_pos : 0 < P4 - T 4 := hpos_of _ _ hE4_eq (by positivity)
  have hE4_ub : P4 - T 4 < 600 * (m : ℝ) ^ 4 * wm := by
    refine hdiv_ub _ _ _ hE4_eq hE4_pos ?_
    have h1 : (m : ℝ) ^ 4 * (w * wm) < (m : ℝ) ^ 4 * (2.1 * wm) :=
      mul_lt_mul_of_pos_left hwwm_lt (by positivity)
    have h2 : 4 * (100 * (m : ℝ) ^ 3 * wm) ≤ 40 * (m : ℝ) ^ 4 * wm := by
      have := mul_le_mul_of_nonneg_right hm34_le hwm_pos.le; linarith only [this]
    have h3 : 6 * (20 * (m : ℝ) ^ 2 * wm) ≤ 1.2 * (m : ℝ) ^ 4 * wm := by
      have := mul_le_mul_of_nonneg_right hm24_le hwm_pos.le; linarith only [this]
    have h4 : 4 * (6 * (m : ℝ) * wm) ≤ 0.024 * (m : ℝ) ^ 4 * wm := by
      have := mul_le_mul_of_nonneg_right hm14_le hwm_pos.le; linarith only [this]
    have h5 : 3 * wm ≤ 0.0003 * (m : ℝ) ^ 4 * wm := by
      have := mul_le_mul_of_nonneg_right hm04_le hwm_pos.le; linarith only [this]
    have hm4wm : 0 < (m : ℝ) ^ 4 * wm := by positivity
    linarith only [hE3_ub, hE2_ub, hE1_ub, hE0_ub, h1, h2, h3, h4, h5, hm4wm]
  have hE5_eq : (w - 1) * (P5 - T 5) =
      5 * (P4 - T 4) + 10 * (P3 - T 3) + 10 * (P2 - T 2) + 5 * (P1 - T 1) + (P0 - T 0) +
      (m : ℝ) ^ 5 * (w * wm) := by linarith only [hP5, hT5]
  have hE5_pos : 0 < P5 - T 5 := hpos_of _ _ hE5_eq (by positivity)
  have hE6_eq : (w - 1) * (P6 - T 6) =
      6 * (P5 - T 5) + 15 * (P4 - T 4) + 20 * (P3 - T 3) + 15 * (P2 - T 2) + 6 * (P1 - T 1) +
      (P0 - T 0) + (m : ℝ) ^ 6 * (w * wm) := by linarith only [hP6, hT6]
  have hE6_pos : 0 < P6 - T 6 := hpos_of _ _ hE6_eq (by positivity)
  have hT_pos : ∀ n : ℕ, 0 < T n := fun n => by
    refine sum_pos (fun j hj => ?_) ⟨1, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    have hj1 : (0 : ℝ) < j := by exact_mod_cast (mem_Ico.mp hj).1
    positivity
  exact ⟨⟨hE0_pos, hE0_ub⟩, ⟨hE2_pos, hE2_ub⟩, ⟨hE3_pos, hE3_ub⟩, ⟨hE4_pos, hE4_ub⟩,
    ⟨hT_pos 5, by linarith only [hE5_pos]⟩, ⟨hT_pos 6, by linarith only [hE6_pos]⟩⟩

/- ### Section 3: Rational-function bounds at w = 2 - ε and evaluation at k_hi, k_lo -/

lemma rational_at_two_sub_eps {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 1000) :
    let w : ℝ := 2 - ε
    (1 / (w - 1) = 1 + ε + ε ^ 2 + ε ^ 3 / (1 - ε)) ∧
    (6 + 13 * ε < (w + w ^ 2) / (w - 1) ^ 3 ∧ (w + w ^ 2) / (w - 1) ^ 3 < 6 + 13 * ε + 25 * ε ^ 2) ∧
    (26 < (w + 4 * w ^ 2 + w ^ 3) / (w - 1) ^ 4 ∧
      (w + 4 * w ^ 2 + w ^ 3) / (w - 1) ^ 4 < 26 + 80 * ε) ∧
    (150 < (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) / (w - 1) ^ 5 ∧
      (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) / (w - 1) ^ 5 < 150 + 600 * ε) ∧
    ((w + 26 * w ^ 2 + 66 * w ^ 3 + 26 * w ^ 4 + w ^ 5) / (w - 1) ^ 6 < 1200) ∧
    ((w + 57 * w ^ 2 + 302 * w ^ 3 + 302 * w ^ 4 + 57 * w ^ 5 + w ^ 6) / (w - 1) ^ 7 < 10000) := by
  intro w
  have hw1 : w - 1 = 1 - ε := by dsimp only [w]; ring
  have h1e_pos : 0 < 1 - ε := by linarith
  have h1e_ge : (0.999 : ℝ) < 1 - ε := by linarith
  have hε2 : ε ^ 2 < ε / 1000 := by nlinarith
  have hε3 : ε ^ 3 < ε ^ 2 / 1000 := by nlinarith
  have hε4 : ε ^ 4 < ε ^ 3 / 1000 := by nlinarith
  have hε5 : ε ^ 5 < ε ^ 4 / 1000 := by nlinarith
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hw1]; field_simp; ring
  · rw [hw1, lt_div_iff₀ (pow_pos h1e_pos 3)]
    have hid : (w + w ^ 2) - (6 + 13 * ε) * (1 - ε) ^ 3 =
        ε ^ 2 * (22 - 33 * ε + 13 * ε ^ 2) := by dsimp only [w]; ring
    have hpos : 0 < ε ^ 2 * (22 - 33 * ε + 13 * ε ^ 2) := by nlinarith
    linarith
  · rw [hw1, div_lt_iff₀ (pow_pos h1e_pos 3)]
    have hid : (6 + 13 * ε + 25 * ε ^ 2) * (1 - ε) ^ 3 - (w + w ^ 2) =
        ε ^ 2 * (3 - 42 * ε + 62 * ε ^ 2 - 25 * ε ^ 3) := by dsimp only [w]; ring
    have hpos : 0 < ε ^ 2 * (3 - 42 * ε + 62 * ε ^ 2 - 25 * ε ^ 3) := by nlinarith
    linarith
  · rw [hw1, lt_div_iff₀ (pow_pos h1e_pos 4)]
    have hid : (w + 4 * w ^ 2 + w ^ 3) - 26 * (1 - ε) ^ 4 =
        ε * (75 - 146 * ε + 103 * ε ^ 2 - 26 * ε ^ 3) := by dsimp only [w]; ring
    have hpos : 0 < ε * (75 - 146 * ε + 103 * ε ^ 2 - 26 * ε ^ 3) := by nlinarith
    linarith
  · rw [hw1, div_lt_iff₀ (pow_pos h1e_pos 4)]
    have hid : (26 + 80 * ε) * (1 - ε) ^ 4 - (w + 4 * w ^ 2 + w ^ 3) =
        ε * (5 - 174 * ε + 377 * ε ^ 2 - 294 * ε ^ 3 + 80 * ε ^ 4) := by dsimp only [w]; ring
    have hpos : 0 < ε * (5 - 174 * ε + 377 * ε ^ 2 - 294 * ε ^ 3 + 80 * ε ^ 4) := by nlinarith
    linarith
  · rw [hw1, lt_div_iff₀ (pow_pos h1e_pos 5)]
    have hid : (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) - 150 * (1 - ε) ^ 5 =
        ε * (541 - 1399 * ε + 1481 * ε ^ 2 - 749 * ε ^ 3 + 150 * ε ^ 4) := by dsimp only [w]; ring
    have hpos : 0 < ε * (541 - 1399 * ε + 1481 * ε ^ 2 - 749 * ε ^ 3 + 150 * ε ^ 4) := by nlinarith
    linarith
  · rw [hw1, div_lt_iff₀ (pow_pos h1e_pos 5)]
    have hid : (150 + 600 * ε) * (1 - ε) ^ 5 - (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) =
        ε * (59 - 1601 * ε + 4519 * ε ^ 2 - 5251 * ε ^ 3 + 2850 * ε ^ 4 - 600 * ε ^ 5) := by
      dsimp only [w]; ring
    have hpos : 0 < ε * (59 - 1601 * ε + 4519 * ε ^ 2 - 5251 * ε ^ 3 + 2850 * ε ^ 4 - 600 * ε ^ 5) := by
      nlinarith
    linarith
  · rw [hw1, div_lt_iff₀ (pow_pos h1e_pos 6)]
    have hw_le : w < 2 := by dsimp only [w]; linarith
    have hw_nn : 0 < w := by dsimp only [w]; linarith
    have h2 : w ^ 2 ≤ 4 := by nlinarith
    have h3 : w ^ 3 ≤ 8 := by nlinarith
    have h4 : w ^ 4 ≤ 16 := by nlinarith
    have h5 : w ^ 5 ≤ 32 := by nlinarith
    have hnum : w + 26 * w ^ 2 + 66 * w ^ 3 + 26 * w ^ 4 + w ^ 5 < 1083 := by linarith
    have hden : (0.99 : ℝ) < (1 - ε) ^ 6 := by
      have : (0.999 : ℝ) ^ 6 ≤ (1 - ε) ^ 6 := pow_le_pow_left₀ (by norm_num) h1e_ge.le 6
      norm_num at this; linarith
    linarith
  · rw [hw1, div_lt_iff₀ (pow_pos h1e_pos 7)]
    have hw_le : w < 2 := by dsimp only [w]; linarith
    have hw_nn : 0 < w := by dsimp only [w]; linarith
    have h2 : w ^ 2 ≤ 4 := by nlinarith
    have h3 : w ^ 3 ≤ 8 := by nlinarith
    have h4 : w ^ 4 ≤ 16 := by nlinarith
    have h5 : w ^ 5 ≤ 32 := by nlinarith
    have h6 : w ^ 6 ≤ 64 := by nlinarith
    have hnum : w + 57 * w ^ 2 + 302 * w ^ 3 + 302 * w ^ 4 + 57 * w ^ 5 + w ^ 6 < 9367 := by
      linarith
    have hden : (0.99 : ℝ) < (1 - ε) ^ 7 := by
      have : (0.999 : ℝ) ^ 7 ≤ (1 - ε) ^ 7 := pow_le_pow_left₀ (by norm_num) h1e_ge.le 7
      norm_num at this; linarith
    linarith

lemma gmz_main_poly_hi (m L : ℝ) (hm : m ≠ 0) :
    let α : ℝ := ((2 * m - 3) / 2) * L
    let δ : ℝ := (3 / 2 : ℝ) * L / m
    (1 + 2 * δ + 3 * δ ^ 2) - α / (2 * m ^ 2) * (6 + 26 * δ) -
    α / (3 * m ^ 3) * 26 + α * (α - 2) / (8 * m ^ 4) * 150 =
    1 + (6 * L ^ 2 - 25 / 6 * L) / m ^ 2 +
    (-27 * L ^ 2 - 49 / 2 * L) / m ^ 3 +
    (675 / 16 * L ^ 2 + 225 / 4 * L) / m ^ 4 := by
  intro α δ
  dsimp only [α, δ]
  field_simp
  ring

lemma gmz_main_poly_lo (m L b : ℝ) (hm : m ≠ 0) :
    let α : ℝ := m * L - (3 / 2 : ℝ) * L - b / m
    let δ : ℝ := (3 / 2 : ℝ) * L / m + b / m ^ 2
    (1 + 2 * δ + 3 * δ ^ 2) - α / (2 * m ^ 2) * (6 + 26 * δ) -
    α / (3 * m ^ 3) * 26 + α * (α - 2) / (8 * m ^ 4) * 150 =
    1 + (2 * b + 6 * L ^ 2 - 25 / 6 * L) / m ^ 2 +
    (-4 * L * b - 27 * L ^ 2 - 49 / 2 * L + 3 * b) / m ^ 3 +
    (3 * b ^ 2 + 3 / 2 * L * b + 26 / 3 * b + 675 / 16 * L ^ 2 + 225 / 4 * L) / m ^ 4 +
    (13 * b ^ 2 + 225 / 4 * L * b + 75 / 2 * b) / m ^ 5 +
    (75 / 4 * b ^ 2) / m ^ 6 := by
  intro α δ
  dsimp only [α, δ]
  field_simp
  ring

lemma gmz_eval_hi {m : ℕ} (hm : 10 ^ 9 < m) :
    ∑ j ∈ Ico 1 m, (1 - (j : ℝ) / m) ^ (((2 * m - 3 : ℝ) / 2) * Real.log 2) < 1 := by
  have hmR : (10 ^ 9 : ℝ) < m := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < m := by linarith
  set L : ℝ := Real.log 2
  have hL_lo : (0.6931471803 : ℝ) < L := Real.log_two_gt_d9
  have hL_hi : L < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  set α : ℝ := ((2 * (m : ℝ) - 3) / 2) * L
  set lam : ℝ := α / m
  set δ : ℝ := (3 / 2 : ℝ) * L / m
  have hlam_eq : lam = L - δ := by dsimp only [lam, α, δ]; field_simp
  have hα_lb : (0.6 : ℝ) * m < α := by dsimp only [α]; nlinarith
  have hα_ge : (10 : ℝ) ≤ α := by linarith
  have hα_pos : 0 < α := by linarith
  have hα_lt : α < m := by dsimp only [α]; nlinarith
  have hδ_pos : 0 < δ := by dsimp only [δ]; positivity
  have hδ_lt : δ < (2 : ℝ) / m := by
    dsimp only [δ]; rw [div_lt_div_iff_of_pos_right hm_pos]; linarith
  have hδ_small : δ < (1 : ℝ) / 100000 := by
    have : (2 : ℝ) / m < 1 / 100000 := by rw [div_lt_div_iff₀ hm_pos (by norm_num)]; linarith
    linarith
  set w : ℝ := Real.exp lam
  have hw_eq : w = 2 * Real.exp (-δ) := by
    dsimp only [w]
    rw [hlam_eq, sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  set ε : ℝ := 2 - w
  have ⟨hexp_lo, hexp_hi⟩ := exp_neg_bounds hδ_pos
  have hε_lo : 2 * δ - δ ^ 2 < ε := by dsimp only [ε]; rw [hw_eq]; linarith
  have hε_hi : ε < 2 * δ - δ ^ 2 + δ ^ 3 / 3 := by dsimp only [ε]; rw [hw_eq]; linarith
  have hδ_sq_nn : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hδ_sq_lt : δ ^ 2 < δ := by nlinarith only [hδ_pos, hδ_small]
  have hδ_cu_lt : δ ^ 3 < δ := by nlinarith only [hδ_pos, hδ_small, hδ_sq_lt]
  have hε_pos : 0 < ε := by linarith only [hε_lo, hδ_sq_lt, hδ_pos]
  have hε_lt : ε < (1 : ℝ) / 1000 := by linarith only [hε_hi, hδ_sq_nn, hδ_cu_lt, hδ_small]
  have hε_lt_2δ : ε < 2 * δ := by
    have hcu : δ ^ 3 / 3 < δ ^ 2 := by nlinarith only [hδ_pos, hδ_small, hδ_sq_nn]
    linarith only [hε_hi, hcu]
  have hε_ub : ε < (4 : ℝ) / m := by
    have h2 : 2 * ((2 : ℝ) / m) = 4 / m := by ring
    linarith only [hε_lt_2δ, hδ_lt, h2]
  have hw1 : (1.9 : ℝ) < w := by dsimp only [ε] at hε_lt; linarith
  have hw2 : w < 2.1 := by dsimp only [ε] at hε_pos; linarith
  let T : ℕ → ℝ := fun n => ∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-(j : ℤ))
  have hterm_le : ∀ j ∈ Ico 1 m,
      (1 - (j : ℝ) / m) ^ α <
        w ^ (-(j : ℤ)) * (1 - α / (2 * (m : ℝ) ^ 2) * (j : ℝ) ^ 2 -
          α / (3 * (m : ℝ) ^ 3) * (j : ℝ) ^ 3 +
          α * (α - 2) / (8 * (m : ℝ) ^ 4) * (j : ℝ) ^ 4 +
          α ^ 2 / (2 * (m : ℝ) ^ 5) * (j : ℝ) ^ 5) := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
    have hjm : j < m := (mem_Ico.mp hj).2
    have hjR0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hjRm : (j : ℝ) < m := by exact_mod_cast hjm
    have hy0 : 0 < (j : ℝ) / m := div_pos hjR0 hm_pos
    have hy1 : (j : ℝ) / m < 1 := (div_lt_one hm_pos).mpr hjRm
    have htb := (gmz_term_bounds hα_ge hy0 hy1).2
    have hexp_w : Real.exp (-α * ((j : ℝ) / m)) = w ^ (-(j : ℤ)) := by
      dsimp only [w, lam]
      rw [zpow_neg, zpow_natCast, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1; ring
    rw [hexp_w] at htb
    convert htb using 2
    ring
  have hsum_lt : ∑ j ∈ Ico 1 m, (1 - (j : ℝ) / m) ^ α <
      T 0 - α / (2 * (m : ℝ) ^ 2) * T 2 - α / (3 * (m : ℝ) ^ 3) * T 3 +
      α * (α - 2) / (8 * (m : ℝ) ^ 4) * T 4 + α ^ 2 / (2 * (m : ℝ) ^ 5) * T 5 := by
    have hne : (Ico 1 m).Nonempty := ⟨1, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    have h1 := sum_lt_sum_of_nonempty hne hterm_le
    have hrhs : ∑ j ∈ Ico 1 m,
        w ^ (-(j : ℤ)) * (1 - α / (2 * (m : ℝ) ^ 2) * (j : ℝ) ^ 2 -
          α / (3 * (m : ℝ) ^ 3) * (j : ℝ) ^ 3 +
          α * (α - 2) / (8 * (m : ℝ) ^ 4) * (j : ℝ) ^ 4 +
          α ^ 2 / (2 * (m : ℝ) ^ 5) * (j : ℝ) ^ 5) =
        T 0 - α / (2 * (m : ℝ) ^ 2) * T 2 - α / (3 * (m : ℝ) ^ 3) * T 3 +
        α * (α - 2) / (8 * (m : ℝ) ^ 4) * T 4 + α ^ 2 / (2 * (m : ℝ) ^ 5) * T 5 := by
      dsimp only [T]
      rw [mul_sum, mul_sum, mul_sum, mul_sum,
        ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => by ring
    linarith only [h1, hrhs]
  have hg := geom_power_sum_bounds (m := m) (by omega) hw1 hw2
  change (0 < 1 / (w - 1) - T 0 ∧ 1 / (w - 1) - T 0 < 3 * w ^ (-(m : ℤ))) ∧
    (0 < (w + w ^ 2) / (w - 1) ^ 3 - T 2 ∧ (w + w ^ 2) / (w - 1) ^ 3 - T 2 < 20 * (m : ℝ) ^ 2 * w ^ (-(m : ℤ))) ∧
    (0 < (w + 4 * w ^ 2 + w ^ 3) / (w - 1) ^ 4 - T 3 ∧
      (w + 4 * w ^ 2 + w ^ 3) / (w - 1) ^ 4 - T 3 < 100 * (m : ℝ) ^ 3 * w ^ (-(m : ℤ))) ∧
    (0 < (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) / (w - 1) ^ 5 - T 4 ∧
      (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) / (w - 1) ^ 5 - T 4 < 600 * (m : ℝ) ^ 4 * w ^ (-(m : ℤ))) ∧
    (0 < T 5 ∧ T 5 < (w + 26 * w ^ 2 + 66 * w ^ 3 + 26 * w ^ 4 + w ^ 5) / (w - 1) ^ 6) ∧
    (0 < T 6 ∧ T 6 < (w + 57 * w ^ 2 + 302 * w ^ 3 + 302 * w ^ 4 + 57 * w ^ 5 + w ^ 6) / (w - 1) ^ 7) at hg
  obtain ⟨⟨hE0_pos, _⟩, ⟨_, hE2_ub⟩, ⟨_, hE3_ub⟩, ⟨hE4_pos, _⟩, ⟨_, hT5_ub⟩, _⟩ := hg
  have hrat := rational_at_two_sub_eps hε_pos hε_lt
  have hw_rew : 2 - ε = w := by dsimp only [ε]; ring
  dsimp only at hrat
  rw [hw_rew] at hrat
  obtain ⟨hP0_eq, ⟨hP2_lo, _⟩, ⟨hP3_lo, _⟩, ⟨_, hP4_hi⟩, hP5_hi, _⟩ := hrat
  have hwm_lt5 : w ^ (-(m : ℤ)) < 1 / (m : ℝ) ^ 5 := by
    have hwm_exp : w ^ (-(m : ℤ)) = Real.exp (-α) := by
      dsimp only [w, lam]
      rw [zpow_neg, zpow_natCast, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1; field_simp
    rw [hwm_exp]
    exact exp_neg_lt_inv_pow_five hmR hα_lb
  have hT0_ub : T 0 < 1 + 2 * δ + 3 * δ ^ 2 + 100 / (m : ℝ) ^ 3 := by
    have h1 : T 0 < 1 + ε + ε ^ 2 + ε ^ 3 / (1 - ε) := by linarith only [hE0_pos, hP0_eq]
    have hε3_div : ε ^ 3 / (1 - ε) < 70 / (m : ℝ) ^ 3 := by
      rw [div_lt_iff₀ (by linarith only [hε_lt])]
      have hcu : ε ^ 3 < (4 / (m : ℝ)) ^ 3 := pow_lt_pow_left₀ hε_ub hε_pos.le (by norm_num)
      have h64 : (4 / (m : ℝ)) ^ 3 = 64 * (1 / (m : ℝ) ^ 3) := by ring
      have h70 : (70 : ℝ) / (m : ℝ) ^ 3 = 70 * (1 / (m : ℝ) ^ 3) := by ring
      have hpos3 : (0 : ℝ) < 1 / (m : ℝ) ^ 3 := by positivity
      have h1e : (0.999 : ℝ) < 1 - ε := by linarith only [hε_lt]
      rw [h70]
      nlinarith only [hcu, h64, hpos3, h1e]
    have hε_sq_ub : ε ^ 2 < 4 * δ ^ 2 := by
      have h2 : ε ^ 2 < (2 * δ) ^ 2 := pow_lt_pow_left₀ hε_lt_2δ hε_pos.le (by norm_num)
      linarith only [h2, show (2 * δ) ^ 2 = 4 * δ ^ 2 by ring]
    have hδ3_ub : δ ^ 3 / 3 < 3 / (m : ℝ) ^ 3 := by
      have hcu : δ ^ 3 < (2 / (m : ℝ)) ^ 3 := pow_lt_pow_left₀ hδ_lt hδ_pos.le (by norm_num)
      have h8 : (2 / (m : ℝ)) ^ 3 = 8 / (m : ℝ) ^ 3 := by ring
      have h83 : (8 / (m : ℝ) ^ 3) / 3 = (8 / 3 : ℝ) * (1 / (m : ℝ) ^ 3) := by ring
      have h3 : (3 : ℝ) / (m : ℝ) ^ 3 = 3 * (1 / (m : ℝ) ^ 3) := by ring
      have hp : (0 : ℝ) < 1 / (m : ℝ) ^ 3 := by positivity
      linarith only [hcu, h8, h83, h3, hp]
    have hsum100 : (70 : ℝ) / (m : ℝ) ^ 3 + 3 / (m : ℝ) ^ 3 < 100 / (m : ℝ) ^ 3 := by
      rw [← add_div]; exact div_lt_div_of_pos_right (by norm_num) (by positivity)
    linarith only [h1, hε_hi, hε3_div, hε_sq_ub, hδ3_ub, hsum100]
  have hT2_lb : 6 + 26 * δ - 200 / (m : ℝ) ^ 2 < T 2 := by
    have h1 : 6 + 13 * ε - 20 * (m : ℝ) ^ 2 * w ^ (-(m : ℤ)) < T 2 := by linarith only [hP2_lo, hE2_ub]
    have h2 : 20 * (m : ℝ) ^ 2 * w ^ (-(m : ℤ)) < 20 / (m : ℝ) ^ 2 := by
      have hm5 : 1 / (m : ℝ) ^ 5 ≤ 1 / (m : ℝ) ^ 4 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
      have hlt4 := lt_of_lt_of_le hwm_lt5 hm5
      have := mul_lt_mul_of_pos_left hlt4 (by positivity : (0 : ℝ) < 20 * (m : ℝ) ^ 2)
      have hr : 20 * (m : ℝ) ^ 2 * (1 / (m : ℝ) ^ 4) = 20 / (m : ℝ) ^ 2 := by field_simp
      linarith only [this, hr]
    have h3 : 13 * δ ^ 2 < 52 / (m : ℝ) ^ 2 := by
      have hsq : δ ^ 2 < (2 / (m : ℝ)) ^ 2 := pow_lt_pow_left₀ hδ_lt hδ_pos.le (by norm_num)
      have h4 : 13 * (2 / (m : ℝ)) ^ 2 = 52 / (m : ℝ) ^ 2 := by ring
      linarith only [hsq, h4]
    have h200 : (20 : ℝ) / (m : ℝ) ^ 2 + 52 / (m : ℝ) ^ 2 < 200 / (m : ℝ) ^ 2 := by
      rw [← add_div]; exact div_lt_div_of_pos_right (by norm_num) (by positivity)
    linarith only [h1, hε_lo, h2, h3, h200]
  have hT3_lb : 26 - 100 / (m : ℝ) < T 3 := by
    have h1 : 26 - 100 * (m : ℝ) ^ 3 * w ^ (-(m : ℤ)) < T 3 := by linarith only [hP3_lo, hE3_ub]
    have h2 : 100 * (m : ℝ) ^ 3 * w ^ (-(m : ℤ)) < 100 / m := by
      have hm5 : 1 / (m : ℝ) ^ 5 ≤ 1 / (m : ℝ) ^ 4 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
      have hlt4 := lt_of_lt_of_le hwm_lt5 hm5
      have := mul_lt_mul_of_pos_left hlt4 (by positivity : (0 : ℝ) < 100 * (m : ℝ) ^ 3)
      have hr : 100 * (m : ℝ) ^ 3 * (1 / (m : ℝ) ^ 4) = 100 / m := by field_simp
      linarith only [this, hr]
    linarith only [h1, h2]
  have hT4_ub : T 4 < 150 + 2400 / m := by
    have h600 : 600 * (4 / (m : ℝ)) = 2400 / m := by ring
    linarith only [hE4_pos, hP4_hi, hε_ub, h600]
  have hterm2 : α / (2 * (m : ℝ) ^ 2) * (6 + 26 * δ - 200 / (m : ℝ) ^ 2) <
      α / (2 * (m : ℝ) ^ 2) * T 2 := mul_lt_mul_of_pos_left hT2_lb (by positivity)
  have hterm3 : α / (3 * (m : ℝ) ^ 3) * (26 - 100 / m) <
      α / (3 * (m : ℝ) ^ 3) * T 3 := mul_lt_mul_of_pos_left hT3_lb (by positivity)
  have hα2_pos : 0 < α - 2 := by linarith only [hα_ge]
  have hterm4 : α * (α - 2) / (8 * (m : ℝ) ^ 4) * T 4 <
      α * (α - 2) / (8 * (m : ℝ) ^ 4) * (150 + 2400 / m) :=
    mul_lt_mul_of_pos_left hT4_ub (by positivity)
  have hterm5 : α ^ 2 / (2 * (m : ℝ) ^ 5) * T 5 < 600 / (m : ℝ) ^ 3 := by
    have h1 : α ^ 2 / (2 * (m : ℝ) ^ 5) * T 5 < α ^ 2 / (2 * (m : ℝ) ^ 5) * 1200 :=
      mul_lt_mul_of_pos_left (lt_trans hT5_ub hP5_hi) (by positivity)
    have h2 : α ^ 2 / (2 * (m : ℝ) ^ 5) * 1200 < 600 / (m : ℝ) ^ 3 := by
      have hrew : α ^ 2 / (2 * (m : ℝ) ^ 5) * 1200 = 600 * α ^ 2 / (m : ℝ) ^ 5 := by ring
      rw [hrew, div_lt_div_iff₀ (by positivity) (by positivity)]
      have hsq : α ^ 2 < (m : ℝ) ^ 2 := pow_lt_pow_left₀ hα_lt (by linarith) (by norm_num)
      have hm3 : 0 < (m : ℝ) ^ 3 := pow_pos hm_pos 3
      have h53 : (m : ℝ) ^ 5 = (m : ℝ) ^ 2 * (m : ℝ) ^ 3 := by ring
      nlinarith only [hsq, hm3, h53]
    linarith only [h1, h2]
  have hmain_eq := gmz_main_poly_hi (m : ℝ) L hm_pos.ne'
  dsimp only at hmain_eq
  have hcoef2 : 6 * L ^ 2 - 25 / 6 * L < (-0.0053 : ℝ) := by nlinarith only [hL_lo, hL_hi]
  have hα2_lt : α * (α - 2) < (m : ℝ) ^ 2 := by nlinarith only [hα_lt, hα_ge]
  have ha1 : α / (2 * (m : ℝ) ^ 2) * (200 / (m : ℝ) ^ 2) < 100 / (m : ℝ) ^ 3 := by
    have : α / (2 * (m : ℝ) ^ 2) * (200 / (m : ℝ) ^ 2) = 100 * α / (m : ℝ) ^ 4 := by ring
    rw [this, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hm3 : 0 < (m : ℝ) ^ 3 := pow_pos hm_pos 3
    have h43 : (m : ℝ) ^ 4 = m * (m : ℝ) ^ 3 := by ring
    nlinarith only [hα_lt, hm3, h43]
  have ha2 : α / (3 * (m : ℝ) ^ 3) * (100 / m) < 40 / (m : ℝ) ^ 3 := by
    have : α / (3 * (m : ℝ) ^ 3) * (100 / m) = 100 * α / (3 * (m : ℝ) ^ 4) := by ring
    rw [this, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hm3 : 0 < (m : ℝ) ^ 3 := pow_pos hm_pos 3
    have h43 : (m : ℝ) ^ 4 = m * (m : ℝ) ^ 3 := by ring
    nlinarith only [hα_lt, hm3, h43]
  have ha3 : α * (α - 2) / (8 * (m : ℝ) ^ 4) * (2400 / m) < 300 / (m : ℝ) ^ 3 := by
    have : α * (α - 2) / (8 * (m : ℝ) ^ 4) * (2400 / m) = 300 * (α * (α - 2)) / (m : ℝ) ^ 5 := by ring
    rw [this, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hm3 : 0 < (m : ℝ) ^ 3 := pow_pos hm_pos 3
    have h53 : (m : ℝ) ^ 5 = (m : ℝ) ^ 2 * (m : ℝ) ^ 3 := by ring
    nlinarith only [hα2_lt, hm3, h53]
  have ha4 : (-27 * L ^ 2 - 49 / 2 * L) / (m : ℝ) ^ 3 < 0 :=
    div_neg_of_neg_of_pos (by nlinarith only [hL_lo, hL_hi]) (by positivity)
  have ha5 : (675 / 16 * L ^ 2 + 225 / 4 * L) / (m : ℝ) ^ 4 < 100 / (m : ℝ) ^ 3 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hc : 675 / 16 * L ^ 2 + 225 / 4 * L < 100 := by nlinarith only [hL_lo, hL_hi]
    have hm3 : 0 < (m : ℝ) ^ 3 := pow_pos hm_pos 3
    have h43 : (m : ℝ) ^ 4 = m * (m : ℝ) ^ 3 := by ring
    nlinarith only [hc, hmR, hm3, h43]
  have hsum_err : (100 : ℝ) / (m : ℝ) ^ 3 + 100 / (m : ℝ) ^ 3 + 40 / (m : ℝ) ^ 3 +
      300 / (m : ℝ) ^ 3 + 600 / (m : ℝ) ^ 3 + 100 / (m : ℝ) ^ 3 = 1240 / (m : ℝ) ^ 3 := by ring
  have h1240 : 1240 / (m : ℝ) ^ 3 < (0.001 : ℝ) / (m : ℝ) ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hm2 : 0 < (m : ℝ) ^ 2 := pow_pos hm_pos 2
    have h32 : (m : ℝ) ^ 3 = m * (m : ℝ) ^ 2 := by ring
    nlinarith only [hmR, hm2, h32]
  have hneg : (6 * L ^ 2 - 25 / 6 * L) / (m : ℝ) ^ 2 + (0.001 : ℝ) / (m : ℝ) ^ 2 < 0 := by
    rw [← add_div]
    exact div_neg_of_neg_of_pos (by linarith only [hcoef2]) (by positivity)
  have hexp_dist :
      (1 + 2 * δ + 3 * δ ^ 2 + 100 / (m : ℝ) ^ 3) -
      α / (2 * (m : ℝ) ^ 2) * (6 + 26 * δ - 200 / (m : ℝ) ^ 2) -
      α / (3 * (m : ℝ) ^ 3) * (26 - 100 / m) +
      α * (α - 2) / (8 * (m : ℝ) ^ 4) * (150 + 2400 / m) + 600 / (m : ℝ) ^ 3 =
      ((1 + 2 * δ + 3 * δ ^ 2) - α / (2 * (m : ℝ) ^ 2) * (6 + 26 * δ) -
        α / (3 * (m : ℝ) ^ 3) * 26 + α * (α - 2) / (8 * (m : ℝ) ^ 4) * 150) +
      100 / (m : ℝ) ^ 3 + α / (2 * (m : ℝ) ^ 2) * (200 / (m : ℝ) ^ 2) +
      α / (3 * (m : ℝ) ^ 3) * (100 / m) + α * (α - 2) / (8 * (m : ℝ) ^ 4) * (2400 / m) +
      600 / (m : ℝ) ^ 3 := by ring
  linarith only [hsum_lt, hT0_ub, hterm2, hterm3, hterm4, hterm5, hexp_dist, hmain_eq,
    ha1, ha2, ha3, ha4, ha5, hsum_err, h1240, hneg]

set_option maxHeartbeats 400000 in
lemma gmz_eval_lo {m : ℕ} (hm : 10 ^ 9 < m) :
    1 < ∑ j ∈ Ico 1 m,
      (1 - (j : ℝ) / m) ^ (((2 * m - 3 : ℝ) / 2) * (Real.log 2 - 1 / (90 * (2 * m - 3 : ℝ) ^ 2))) := by
  have hmR : (10 ^ 9 : ℝ) < m := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < m := by linarith
  set L : ℝ := Real.log 2
  have hL_lo : (0.6931471803 : ℝ) < L := Real.log_two_gt_d9
  have hL_hi : L < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  set α : ℝ := ((2 * (m : ℝ) - 3) / 2) * (L - 1 / (90 * (2 * (m : ℝ) - 3) ^ 2))
  set lam : ℝ := α / m
  set b : ℝ := (m : ℝ) / (180 * (2 * (m : ℝ) - 3))
  set δ : ℝ := (3 / 2 : ℝ) * L / m + b / (m : ℝ) ^ 2
  have hlam_eq : lam = L - δ := by
    dsimp only [lam, α, δ, b]
    have h2m3 : 2 * (m : ℝ) - 3 ≠ 0 := by linarith
    field_simp
    ring
  have hb_lo : (1 / 360 : ℝ) < b := by
    dsimp only [b]; rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith
  have hb_hi : b < (1 / 359 : ℝ) := by
    dsimp only [b]; rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hδ_pos : 0 < δ := by dsimp only [δ]; positivity
  have hδ_lt : δ < (2 : ℝ) / m := by
    dsimp only [δ]
    have h1 : b / (m : ℝ) ^ 2 < 1 / (100 * (m : ℝ)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hb_hi, hmR]
    have h2 : (3 / 2 : ℝ) * L / m < 1.1 / m := by
      rw [div_lt_div_iff_of_pos_right hm_pos]; linarith only [hL_hi]
    have h3 : (1.1 : ℝ) / m + 1 / (100 * m) < 2 / m := by
      rw [show (1.1 : ℝ) / m + 1 / (100 * m) = 1.11 / m by ring]
      exact div_lt_div_of_pos_right (by norm_num) hm_pos
    linarith only [h1, h2, h3]
  have hδ_small : δ < (1 : ℝ) / 100000 := by
    have : (2 : ℝ) / m < 1 / 100000 := by rw [div_lt_div_iff₀ hm_pos (by norm_num)]; linarith
    linarith only [hδ_lt, this]
  have hα_mul : α = (m : ℝ) * (L - δ) := by rw [← hlam_eq]; dsimp only [lam]; field_simp
  have hα_lb : (0.6 : ℝ) * m < α := by rw [hα_mul]; nlinarith only [hL_lo, hδ_small, hm_pos]
  have hα_ge : (10 : ℝ) ≤ α := by linarith only [hα_lb, hmR]
  have hα_pos : 0 < α := by linarith only [hα_ge]
  have hα_lt : α < m := by rw [hα_mul]; nlinarith only [hL_hi, hδ_pos, hm_pos]
  set w : ℝ := Real.exp lam
  have hw_eq : w = 2 * Real.exp (-δ) := by
    dsimp only [w]
    rw [hlam_eq, sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  set ε : ℝ := 2 - w
  have ⟨hexp_lo, hexp_hi⟩ := exp_neg_bounds hδ_pos
  have hε_lo : 2 * δ - δ ^ 2 < ε := by dsimp only [ε]; rw [hw_eq]; linarith
  have hε_hi : ε < 2 * δ - δ ^ 2 + δ ^ 3 / 3 := by dsimp only [ε]; rw [hw_eq]; linarith
  have hδ_sq_nn : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hδ_sq_lt : δ ^ 2 < δ := by nlinarith only [hδ_pos, hδ_small]
  have hδ_cu_lt : δ ^ 3 < δ := by nlinarith only [hδ_pos, hδ_small, hδ_sq_lt]
  have hε_pos : 0 < ε := by linarith only [hε_lo, hδ_sq_lt, hδ_pos]
  have hε_lt : ε < (1 : ℝ) / 1000 := by linarith only [hε_hi, hδ_sq_nn, hδ_cu_lt, hδ_small]
  have hε_lt_2δ : ε < 2 * δ := by
    have hcu : δ ^ 3 / 3 < δ ^ 2 := by nlinarith only [hδ_pos, hδ_small, hδ_sq_nn]
    linarith only [hε_hi, hcu]
  have hε_ub : ε < (4 : ℝ) / m := by
    have h2 : 2 * ((2 : ℝ) / m) = 4 / m := by ring
    linarith only [hε_lt_2δ, hδ_lt, h2]
  have hw1 : (1.9 : ℝ) < w := by dsimp only [ε] at hε_lt; linarith
  have hw2 : w < 2.1 := by dsimp only [ε] at hε_pos; linarith
  let T : ℕ → ℝ := fun n => ∑ j ∈ Ico 1 m, (j : ℝ) ^ n * w ^ (-(j : ℤ))
  have hterm_gt : ∀ j ∈ Ico 1 m,
      w ^ (-(j : ℤ)) * (1 - α / (2 * (m : ℝ) ^ 2) * (j : ℝ) ^ 2 -
        α / (3 * (m : ℝ) ^ 3) * (j : ℝ) ^ 3 +
        α * (α - 2) / (8 * (m : ℝ) ^ 4) * (j : ℝ) ^ 4 +
        α * (5 * α - 6) / (30 * (m : ℝ) ^ 5) * (j : ℝ) ^ 5 -
        α ^ 3 / (6 * (m : ℝ) ^ 6) * (j : ℝ) ^ 6) <
      (1 - (j : ℝ) / m) ^ α := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
    have hjm : j < m := (mem_Ico.mp hj).2
    have hjR0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hjRm : (j : ℝ) < m := by exact_mod_cast hjm
    have hy0 : 0 < (j : ℝ) / m := div_pos hjR0 hm_pos
    have hy1 : (j : ℝ) / m < 1 := (div_lt_one hm_pos).mpr hjRm
    have htb := (gmz_term_bounds hα_ge hy0 hy1).1
    have hexp_w : Real.exp (-α * ((j : ℝ) / m)) = w ^ (-(j : ℤ)) := by
      dsimp only [w, lam]
      rw [zpow_neg, zpow_natCast, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1; ring
    rw [hexp_w] at htb
    convert htb using 2
    ring
  have hsum_gt :
      T 0 - α / (2 * (m : ℝ) ^ 2) * T 2 - α / (3 * (m : ℝ) ^ 3) * T 3 +
      α * (α - 2) / (8 * (m : ℝ) ^ 4) * T 4 + α * (5 * α - 6) / (30 * (m : ℝ) ^ 5) * T 5 -
      α ^ 3 / (6 * (m : ℝ) ^ 6) * T 6 <
      ∑ j ∈ Ico 1 m, (1 - (j : ℝ) / m) ^ α := by
    have hne : (Ico 1 m).Nonempty := ⟨1, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    have h1 := sum_lt_sum_of_nonempty hne hterm_gt
    have hlhs : ∑ j ∈ Ico 1 m,
        w ^ (-(j : ℤ)) * (1 - α / (2 * (m : ℝ) ^ 2) * (j : ℝ) ^ 2 -
          α / (3 * (m : ℝ) ^ 3) * (j : ℝ) ^ 3 +
          α * (α - 2) / (8 * (m : ℝ) ^ 4) * (j : ℝ) ^ 4 +
          α * (5 * α - 6) / (30 * (m : ℝ) ^ 5) * (j : ℝ) ^ 5 -
          α ^ 3 / (6 * (m : ℝ) ^ 6) * (j : ℝ) ^ 6) =
        T 0 - α / (2 * (m : ℝ) ^ 2) * T 2 - α / (3 * (m : ℝ) ^ 3) * T 3 +
        α * (α - 2) / (8 * (m : ℝ) ^ 4) * T 4 + α * (5 * α - 6) / (30 * (m : ℝ) ^ 5) * T 5 -
        α ^ 3 / (6 * (m : ℝ) ^ 6) * T 6 := by
      dsimp only [T]
      rw [mul_sum, mul_sum, mul_sum, mul_sum, mul_sum,
        ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun j _ => by ring
    linarith only [h1, hlhs]
  have hg := geom_power_sum_bounds (m := m) (by omega) hw1 hw2
  change (0 < 1 / (w - 1) - T 0 ∧ 1 / (w - 1) - T 0 < 3 * w ^ (-(m : ℤ))) ∧
    (0 < (w + w ^ 2) / (w - 1) ^ 3 - T 2 ∧ (w + w ^ 2) / (w - 1) ^ 3 - T 2 < 20 * (m : ℝ) ^ 2 * w ^ (-(m : ℤ))) ∧
    (0 < (w + 4 * w ^ 2 + w ^ 3) / (w - 1) ^ 4 - T 3 ∧
      (w + 4 * w ^ 2 + w ^ 3) / (w - 1) ^ 4 - T 3 < 100 * (m : ℝ) ^ 3 * w ^ (-(m : ℤ))) ∧
    (0 < (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) / (w - 1) ^ 5 - T 4 ∧
      (w + 11 * w ^ 2 + 11 * w ^ 3 + w ^ 4) / (w - 1) ^ 5 - T 4 < 600 * (m : ℝ) ^ 4 * w ^ (-(m : ℤ))) ∧
    (0 < T 5 ∧ T 5 < (w + 26 * w ^ 2 + 66 * w ^ 3 + 26 * w ^ 4 + w ^ 5) / (w - 1) ^ 6) ∧
    (0 < T 6 ∧ T 6 < (w + 57 * w ^ 2 + 302 * w ^ 3 + 302 * w ^ 4 + 57 * w ^ 5 + w ^ 6) / (w - 1) ^ 7) at hg
  obtain ⟨⟨_, hE0_ub⟩, ⟨hE2_pos, _⟩, ⟨hE3_pos, _⟩, ⟨_, hE4_ub⟩, ⟨hT5_pos, _⟩, ⟨_, hT6_ub⟩⟩ := hg
  have hrat := rational_at_two_sub_eps hε_pos hε_lt
  have hw_rew : 2 - ε = w := by dsimp only [ε]; ring
  dsimp only at hrat
  rw [hw_rew] at hrat
  obtain ⟨hP0_eq, ⟨_, hP2_hi⟩, ⟨_, hP3_hi⟩, ⟨hP4_lo, _⟩, _, hP6_hi⟩ := hrat
  have hwm_lt5 : w ^ (-(m : ℤ)) < 1 / (m : ℝ) ^ 5 := by
    have hwm_exp : w ^ (-(m : ℤ)) = Real.exp (-α) := by
      dsimp only [w, lam]
      rw [zpow_neg, zpow_natCast, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1; field_simp
    rw [hwm_exp]
    exact exp_neg_lt_inv_pow_five hmR hα_lb
  have hT0_lb : 1 + 2 * δ + 3 * δ ^ 2 - 40 / (m : ℝ) ^ 3 < T 0 := by
    have h1 : 1 + ε + ε ^ 2 + ε ^ 3 / (1 - ε) - 3 * w ^ (-(m : ℤ)) < T 0 := by
      linarith only [hE0_ub, hP0_eq]
    have hε3_nn : 0 ≤ ε ^ 3 / (1 - ε) := by
      have : 0 < 1 - ε := by linarith only [hε_lt]
      positivity
    have hwm_small : 3 * w ^ (-(m : ℤ)) < 3 / (m : ℝ) ^ 3 := by
      have h53 : 1 / (m : ℝ) ^ 5 ≤ 1 / (m : ℝ) ^ 3 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
      have h3eq : 3 * (1 / (m : ℝ) ^ 3) = 3 / (m : ℝ) ^ 3 := by ring
      linarith only [hwm_lt5, h53, h3eq]
    have hε_sq_lb : 4 * δ ^ 2 - 32 / (m : ℝ) ^ 3 < ε ^ 2 := by
      have hpos_diff : 0 < 2 * δ - δ ^ 2 := by linarith only [hδ_pos, hδ_sq_lt]
      have hsq : (2 * δ - δ ^ 2) ^ 2 < ε ^ 2 := pow_lt_pow_left₀ hε_lo hpos_diff.le (by norm_num)
      have h2 : (2 * δ - δ ^ 2) ^ 2 = 4 * δ ^ 2 - 4 * δ ^ 3 + δ ^ 4 := by ring
      have h3 : 4 * δ ^ 3 < 32 / (m : ℝ) ^ 3 := by
        have hcu : δ ^ 3 < (2 / (m : ℝ)) ^ 3 := pow_lt_pow_left₀ hδ_lt hδ_pos.le (by norm_num)
        have h32 : 4 * (2 / (m : ℝ)) ^ 3 = 32 / (m : ℝ) ^ 3 := by ring
        linarith only [hcu, h32]
      have h4 : 0 ≤ δ ^ 4 := by positivity
      linarith only [hsq, h2, h3, h4]
    have h40 : (3 : ℝ) / (m : ℝ) ^ 3 + 32 / (m : ℝ) ^ 3 < 40 / (m : ℝ) ^ 3 := by
      rw [← add_div]; exact div_lt_div_of_pos_right (by norm_num) (by positivity)
    linarith only [h1, hε_lo, hε3_nn, hwm_small, hε_sq_lb, h40]
  have hT2_ub : T 2 < 6 + 26 * δ + 400 / (m : ℝ) ^ 2 := by
    have h1 : T 2 < 6 + 13 * ε + 25 * ε ^ 2 := by linarith only [hE2_pos, hP2_hi]
    have h3 : 25 * ε ^ 2 < 400 / (m : ℝ) ^ 2 := by
      have hsq : ε ^ 2 < (4 / (m : ℝ)) ^ 2 := pow_lt_pow_left₀ hε_ub hε_pos.le (by norm_num)
      have h400 : 25 * (4 / (m : ℝ)) ^ 2 = 400 / (m : ℝ) ^ 2 := by ring
      linarith only [hsq, h400]
    linarith only [h1, hε_lt_2δ, h3]
  have hT3_ub : T 3 < 26 + 320 / m := by
    have h320 : 80 * (4 / (m : ℝ)) = 320 / m := by ring
    linarith only [hE3_pos, hP3_hi, hε_ub, h320]
  have hT4_lb : 150 - 600 / m < T 4 := by
    have h1 : 150 - 600 * (m : ℝ) ^ 4 * w ^ (-(m : ℤ)) < T 4 := by linarith only [hP4_lo, hE4_ub]
    have h2 : 600 * (m : ℝ) ^ 4 * w ^ (-(m : ℤ)) < 600 / m := by
      have := mul_lt_mul_of_pos_left hwm_lt5 (by positivity : (0 : ℝ) < 600 * (m : ℝ) ^ 4)
      have hr : 600 * (m : ℝ) ^ 4 * (1 / (m : ℝ) ^ 5) = 600 / m := by field_simp
      linarith only [this, hr]
    linarith only [h1, h2]
  have hterm5_pos : 0 < α * (5 * α - 6) / (30 * (m : ℝ) ^ 5) * T 5 := by
    have : 0 < 5 * α - 6 := by linarith only [hα_ge]
    positivity
  have hterm6_ub : α ^ 3 / (6 * (m : ℝ) ^ 6) * T 6 < 1700 / (m : ℝ) ^ 3 := by
    have h1 : α ^ 3 / (6 * (m : ℝ) ^ 6) * T 6 < α ^ 3 / (6 * (m : ℝ) ^ 6) * 10000 :=
      mul_lt_mul_of_pos_left (lt_trans hT6_ub hP6_hi) (by positivity)
    have h2 : α ^ 3 / (6 * (m : ℝ) ^ 6) * 10000 < 1700 / (m : ℝ) ^ 3 := by
      have hrew : α ^ 3 / (6 * (m : ℝ) ^ 6) * 10000 = 10000 * α ^ 3 / (6 * (m : ℝ) ^ 6) := by ring
      rw [hrew, div_lt_div_iff₀ (by positivity) (by positivity)]
      have hcu : α ^ 3 < (m : ℝ) ^ 3 := pow_lt_pow_left₀ hα_lt (by linarith) (by norm_num)
      have hm3 : 0 < (m : ℝ) ^ 3 := pow_pos hm_pos 3
      have h63 : (m : ℝ) ^ 6 = (m : ℝ) ^ 3 * (m : ℝ) ^ 3 := by ring
      nlinarith only [hcu, hm3, h63]
    linarith only [h1, h2]
  have hterm2 : α / (2 * (m : ℝ) ^ 2) * T 2 < α / (2 * (m : ℝ) ^ 2) * (6 + 26 * δ + 400 / (m : ℝ) ^ 2) :=
    mul_lt_mul_of_pos_left hT2_ub (by positivity)
  have hterm3 : α / (3 * (m : ℝ) ^ 3) * T 3 < α / (3 * (m : ℝ) ^ 3) * (26 + 320 / m) :=
    mul_lt_mul_of_pos_left hT3_ub (by positivity)
  have hα2_pos : 0 < α - 2 := by linarith only [hα_ge]
  have hterm4 : α * (α - 2) / (8 * (m : ℝ) ^ 4) * (150 - 600 / m) <
      α * (α - 2) / (8 * (m : ℝ) ^ 4) * T 4 :=
    mul_lt_mul_of_pos_left hT4_lb (by positivity)
  have hα_eq : α = (m : ℝ) * L - (3 / 2 : ℝ) * L - b / m := by
    rw [hα_mul]; dsimp only [δ]; field_simp; ring
  have hmain_eq := gmz_main_poly_lo (m : ℝ) L b hm_pos.ne'
  dsimp only at hmain_eq
  rw [← hα_eq] at hmain_eq
  have hcoef2 : (0.00015 : ℝ) < 2 * b + 6 * L ^ 2 - 25 / 6 * L := by
    nlinarith only [hb_lo, hL_lo, hL_hi]
  have hα2_lt : α * (α - 2) < (m : ℝ) ^ 2 := by nlinarith only [hα_lt, hα_ge]
  have ha1 : α / (2 * (m : ℝ) ^ 2) * (400 / (m : ℝ) ^ 2) < 200 / (m : ℝ) ^ 3 := by
    have : α / (2 * (m : ℝ) ^ 2) * (400 / (m : ℝ) ^ 2) = 200 * α / (m : ℝ) ^ 4 := by ring
    rw [this, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hm3 : 0 < (m : ℝ) ^ 3 := pow_pos hm_pos 3
    have h43 : (m : ℝ) ^ 4 = m * (m : ℝ) ^ 3 := by ring
    nlinarith only [hα_lt, hm3, h43]
  have ha2 : α / (3 * (m : ℝ) ^ 3) * (320 / m) < 110 / (m : ℝ) ^ 3 := by
    have : α / (3 * (m : ℝ) ^ 3) * (320 / m) = 320 * α / (3 * (m : ℝ) ^ 4) := by ring
    rw [this, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hm3 : 0 < (m : ℝ) ^ 3 := pow_pos hm_pos 3
    have h43 : (m : ℝ) ^ 4 = m * (m : ℝ) ^ 3 := by ring
    nlinarith only [hα_lt, hm3, h43]
  have ha3 : α * (α - 2) / (8 * (m : ℝ) ^ 4) * (600 / m) < 100 / (m : ℝ) ^ 3 := by
    have : α * (α - 2) / (8 * (m : ℝ) ^ 4) * (600 / m) = 75 * (α * (α - 2)) / (m : ℝ) ^ 5 := by ring
    rw [this, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hm3 : 0 < (m : ℝ) ^ 3 := pow_pos hm_pos 3
    have h53 : (m : ℝ) ^ 5 = (m : ℝ) ^ 2 * (m : ℝ) ^ 3 := by ring
    nlinarith only [hα2_lt, hm3, h53]
  have ha4 : (-100 : ℝ) / (m : ℝ) ^ 3 <
      (-4 * L * b - 27 * L ^ 2 - 49 / 2 * L + 3 * b) / (m : ℝ) ^ 3 :=
    div_lt_div_of_pos_right (by nlinarith only [hb_lo, hb_hi, hL_lo, hL_hi]) (by positivity)
  have ha5 : (0 : ℝ) <
      (3 * b ^ 2 + 3 / 2 * L * b + 26 / 3 * b + 675 / 16 * L ^ 2 + 225 / 4 * L) / (m : ℝ) ^ 4 :=
    div_pos (by nlinarith only [hb_lo, hb_hi, hL_lo, hL_hi]) (by positivity)
  have ha6 : (0 : ℝ) < (13 * b ^ 2 + 225 / 4 * L * b + 75 / 2 * b) / (m : ℝ) ^ 5 :=
    div_pos (by positivity) (by positivity)
  have ha7 : (0 : ℝ) < (75 / 4 * b ^ 2) / (m : ℝ) ^ 6 :=
    div_pos (by positivity) (by positivity)
  have hsum_err : (40 : ℝ) / (m : ℝ) ^ 3 + 200 / (m : ℝ) ^ 3 + 110 / (m : ℝ) ^ 3 +
      100 / (m : ℝ) ^ 3 + 1700 / (m : ℝ) ^ 3 + 100 / (m : ℝ) ^ 3 = 2250 / (m : ℝ) ^ 3 := by ring
  have h2250 : 2250 / (m : ℝ) ^ 3 < (0.0001 : ℝ) / (m : ℝ) ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hm2 : 0 < (m : ℝ) ^ 2 := pow_pos hm_pos 2
    have h32 : (m : ℝ) ^ 3 = m * (m : ℝ) ^ 2 := by ring
    nlinarith only [hmR, hm2, h32]
  have hmain_pos : (0 : ℝ) < (2 * b + 6 * L ^ 2 - 25 / 6 * L) / (m : ℝ) ^ 2 -
      (0.0001 : ℝ) / (m : ℝ) ^ 2 := by
    rw [← sub_div]
    exact div_pos (by linarith only [hcoef2]) (by positivity)
  have hneg100 : (-100 : ℝ) / (m : ℝ) ^ 3 = -(100 / (m : ℝ) ^ 3) := by ring
  have hexp_dist :
      (1 + 2 * δ + 3 * δ ^ 2 - 40 / (m : ℝ) ^ 3) -
      α / (2 * (m : ℝ) ^ 2) * (6 + 26 * δ + 400 / (m : ℝ) ^ 2) -
      α / (3 * (m : ℝ) ^ 3) * (26 + 320 / m) +
      α * (α - 2) / (8 * (m : ℝ) ^ 4) * (150 - 600 / m) - 1700 / (m : ℝ) ^ 3 =
      ((1 + 2 * δ + 3 * δ ^ 2) - α / (2 * (m : ℝ) ^ 2) * (6 + 26 * δ) -
        α / (3 * (m : ℝ) ^ 3) * 26 + α * (α - 2) / (8 * (m : ℝ) ^ 4) * 150) -
      40 / (m : ℝ) ^ 3 - α / (2 * (m : ℝ) ^ 2) * (400 / (m : ℝ) ^ 2) -
      α / (3 * (m : ℝ) ^ 3) * (320 / m) - α * (α - 2) / (8 * (m : ℝ) ^ 4) * (600 / m) -
      1700 / (m : ℝ) ^ 3 := by ring
  linarith only [hsum_gt, hT0_lb, hterm2, hterm3, hterm4, hterm5_pos, hterm6_ub, hexp_dist,
    hmain_eq, ha1, ha2, ha3, ha4, ha5, ha6, ha7, hsum_err, h2250, hmain_pos, hneg100]

/- ### Section 4: Strict antitonicity and Legendre's continued fraction theorem -/

lemma powerSum_div_eq_sum_one_sub {k m : ℕ} (hm : 0 < m)
    (heq : ErdosMoser.powerSum k m = m ^ k) :
    ∑ j ∈ Ico 1 m, (1 - (j : ℝ) / m) ^ (k : ℝ) = 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk : ((m : ℝ) ^ k) ≠ 0 := pow_ne_zero k hmR.ne'
  have hcast : ∑ i ∈ Ico 1 m, (i : ℝ) ^ k = (m : ℝ) ^ k := by
    have h1 : ((ErdosMoser.powerSum k m : ℕ) : ℝ) = ((m ^ k : ℕ) : ℝ) := by exact_mod_cast heq
    unfold ErdosMoser.powerSum at h1
    push_cast at h1
    exact h1
  have hbij : ∑ j ∈ Ico 1 m, (1 - (j : ℝ) / m) ^ (k : ℝ) =
      (∑ i ∈ Ico 1 m, (i : ℝ) ^ k) / (m : ℝ) ^ k := by
    rw [sum_div]
    refine sum_bij (fun j _ => m - j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Ico] at hj ⊢; omega
    · intro a ha b hb hab; simp only [mem_Ico] at ha hb; omega
    · intro i hi; simp only [mem_Ico] at hi
      exact ⟨m - i, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj
      simp only [mem_Ico] at hj
      rw [Real.rpow_natCast, ← div_pow]
      congr 1
      rw [Nat.cast_sub (le_of_lt hj.2)]
      field_simp
  rw [hbij, hcast, div_self hmk]

lemma sum_one_sub_strictAnti {m : ℕ} (hm : 2 ≤ m) {α β : ℝ} (hab : α < β) :
    ∑ j ∈ Ico 1 m, (1 - (j : ℝ) / m) ^ β < ∑ j ∈ Ico 1 m, (1 - (j : ℝ) / m) ^ α := by
  have hne : (Ico 1 m).Nonempty := ⟨1, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine sum_lt_sum_of_nonempty hne fun j hj => ?_
  have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
  have hjm : j < m := (mem_Ico.mp hj).2
  have hjR0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjRm : (j : ℝ) < m := by exact_mod_cast hjm
  have hbase0 : 0 < 1 - (j : ℝ) / m := by
    have : (j : ℝ) / m < 1 := (div_lt_one hmR).mpr hjRm
    linarith
  have hbase1 : 1 - (j : ℝ) / m < 1 := by
    have : 0 < (j : ℝ) / m := div_pos hjR0 hmR
    linarith
  exact Real.rpow_lt_rpow_of_exponent_gt hbase0 hbase1 hab

lemma rat_den_le_of_div {a b : ℕ} (hb : 0 < b) :
    ((a : ℚ) / (b : ℚ)).den ≤ b := by
  have hq : ((a : ℚ) / (b : ℚ)) = Rat.divInt (a : ℤ) (b : ℤ) := by
    rw [Rat.divInt_eq_div]
    rfl
  rw [hq]
  have hdvd : ((Rat.divInt (a : ℤ) (b : ℤ)).den : ℤ) ∣ (b : ℤ) := Rat.den_dvd (a : ℤ) (b : ℤ)
  exact Nat.le_of_dvd hb (Int.ofNat_dvd.mp hdvd)

end OMA.ErdosMoserGMZ

theorem OMA.solution : OMA.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R2.H1 := by
  unfold OMA.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R2.H1
  intro k m _hk hm9 _heven _hklo _hkhi heq
  have hm_pos : 0 < m := by omega
  have hm2 : 2 ≤ m := by omega
  have h2m3_pos : (0 : ℝ) < 2 * (m : ℝ) - 3 := by
    have : (10 ^ 9 : ℝ) < m := by exact_mod_cast hm9
    linarith
  have hphi_k := OMA.ErdosMoserGMZ.powerSum_div_eq_sum_one_sub hm_pos heq
  have hhi := OMA.ErdosMoserGMZ.gmz_eval_hi hm9
  have hlo := OMA.ErdosMoserGMZ.gmz_eval_lo hm9
  set α_hi : ℝ := ((2 * (m : ℝ) - 3) / 2) * Real.log 2
  set α_lo : ℝ := ((2 * (m : ℝ) - 3) / 2) * (Real.log 2 - 1 / (90 * (2 * (m : ℝ) - 3) ^ 2))
  have hk_lt_hi : (k : ℝ) < α_hi := by
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with hEq | hLt
    · rw [hEq] at hhi; linarith
    · have := OMA.ErdosMoserGMZ.sum_one_sub_strictAnti hm2 hLt
      linarith
  have hk_gt_lo : α_lo < (k : ℝ) := by
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hle with hEq | hLt
    · rw [← hEq] at hlo; linarith
    · have := OMA.ErdosMoserGMZ.sum_one_sub_strictAnti hm2 hLt
      linarith
  have happrox_lo : 0 < Real.log 2 - (2 * (k : ℝ)) / (2 * (m : ℝ) - 3) := by
    rw [sub_pos, div_lt_iff₀ h2m3_pos]
    dsimp only [α_hi] at hk_lt_hi
    linarith
  have happrox_hi : Real.log 2 - (2 * (k : ℝ)) / (2 * (m : ℝ) - 3) <
      1 / (90 * (2 * (m : ℝ) - 3) ^ 2) := by
    have h1 : Real.log 2 - 1 / (90 * (2 * (m : ℝ) - 3) ^ 2) <
        (2 * (k : ℝ)) / (2 * (m : ℝ) - 3) := by
      rw [lt_div_iff₀ h2m3_pos]
      dsimp only [α_lo] at hk_gt_lo
      linarith
    linarith
  refine ⟨happrox_lo, happrox_hi, ?_⟩
  set q : ℚ := (2 * (k : ℚ)) / (2 * (m : ℚ) - 3)
  have hq_nat : q = (((2 * k : ℕ) : ℚ) / ((2 * m - 3 : ℕ) : ℚ)) := by
    dsimp only [q]
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 3 ≤ 2 * m),
      Nat.cast_mul, Nat.cast_ofNat]
    norm_num
  have hq_real : (q : ℝ) = (2 * (k : ℝ)) / (2 * (m : ℝ) - 3) := by
    dsimp only [q]; push_cast; rfl
  have hden_le : (q.den : ℝ) ≤ 2 * (m : ℝ) - 3 := by
    have hnat : q.den ≤ 2 * m - 3 := by
      rw [hq_nat]
      exact OMA.ErdosMoserGMZ.rat_den_le_of_div (by omega)
    have hcast : (q.den : ℝ) ≤ ((2 * m - 3 : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [Nat.cast_sub (by omega : 3 ≤ 2 * m), Nat.cast_mul, Nat.cast_ofNat] at hcast
    norm_num at hcast
    exact hcast
  have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have habs : |Real.log 2 - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2) := by
    rw [hq_real, abs_of_pos happrox_lo]
    have h1 : 1 / (90 * (2 * (m : ℝ) - 3) ^ 2) < 1 / (2 * (q.den : ℝ) ^ 2) := by
      refine one_div_lt_one_div_of_lt (by positivity) ?_
      have hsq : (q.den : ℝ) ^ 2 ≤ (2 * (m : ℝ) - 3) ^ 2 := by nlinarith
      nlinarith
    exact lt_trans happrox_hi h1
  exact Real.exists_rat_eq_convergent habs

