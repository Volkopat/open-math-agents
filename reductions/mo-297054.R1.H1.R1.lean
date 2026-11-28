import OMAReductions.R_mo_297054_R1
import Mathlib

/-!
# Krzyz conjecture, step mo-297054.R1.H1: the cases n = 2 and n = 3 are proved

Proved here: for f holomorphic, nonvanishing, |f| <= 1 on the unit disk,
|a_2| <= 2/e (`krzyz_n2`) and |a_3| <= 2/e (`krzyz_n3`), where a_n = f^(n)(0)/n!
(Hummel-Scheinberg-Zalcman 1977). Write f = exp L, a = L 0, sigma = 2 Re a = -2t.
F = (L - a)/(L + conj a) is a Schwarz function, G = dslope F 0, and
L - a = z G (L - a + sigma). Differentiating this identity at 0 gives
a_2 = f(0) sigma (G'(0) + G(0)^2 (1 - t)) and
a_3 = f(0) sigma (G''(0)/2 + G(0) G'(0) 2 (1 - t) + G(0)^3 (1 - 2t + 2t^2/3)).
Schwarz-Pick (`schwarz_pick0`) and Schur's second inequality (`schur2`) bound the
coefficients of G; the remaining real inequalities (`real_bound`, `real3`) are proved by
splitting t into intervals.
H1, H2: the remaining known cases n = 4 (Tan 1983), n = 5 (Samaris 2003).
-/

namespace OMA.R_mo_297054_R1_H1_R1

open Metric Complex
open OMA.R_mo_297054_R1 (holo_log mobius_le)


lemma QB (u P b c : ℝ) (hu : 0 ≤ u) (hb0 : 0 ≤ b) :
    ((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * u) + b ^ 3 * P ≤
      1 - b ^ 2 + u ^ 2 * b ^ 2 * (1 + b) + b ^ 3 * P := by
  have h1 : (0 : ℝ) < 1 + b := by linarith
  have key : b * c * (2 * u) - u ^ 2 * b ^ 2 * (1 + b) ≤ c ^ 2 / (1 + b) := by
    rw [le_div_iff₀ h1]
    nlinarith [sq_nonneg (c - u * b * (1 + b))]
  linarith

lemma QA (u P b c : ℝ) (hu : 0 ≤ u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1 - b ^ 2) (hA : 1 ≤ b * (1 + u)) :
    ((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * u) + b ^ 3 * P ≤
      b * (1 - b ^ 2) * (1 + 2 * u) + b ^ 3 * P := by
  have h1 : (0 : ℝ) < 1 + b := by linarith
  have e : c ^ 2 / (1 + b) = c ^ 2 * (1 + b)⁻¹ := div_eq_mul_inv _ _
  set s := 1 - b ^ 2 with hs
  have hs' : s = (1 - b) * (1 + b) := by rw [hs]; ring
  -- (s - c) (2 u b - (s + c)/(1+b)) ≥ 0
  have hsc : (s + c) / (1 + b) ≤ 2 * (1 - b) := by
    rw [div_le_iff₀ h1]; nlinarith
  have h2 : 0 ≤ (s - c) * (2 * u * b - (s + c) / (1 + b)) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have h3 : (s - c) * (2 * u * b - (s + c) / (1 + b)) =
      (2 * u * b * s - s ^ 2 / (1 + b)) - (2 * u * b * c - c ^ 2 / (1 + b)) := by
    field_simp; ring
  have h4 : s ^ 2 / (1 + b) = (1 - b) * s := by
    rw [div_eq_iff h1.ne', hs']; ring
  rw [h3, h4] at h2
  have : b * (1 - b ^ 2) * (1 + 2 * u) = s - (1 - b) * s + 2 * u * b * s := by rw [← hs]; ring
  rw [this]
  linarith

lemma piece (t0 t1 U0 U1 P1 W E0 : ℝ) (ht0 : 0 ≤ t0) (ht01 : t0 < t1) (hU0 : 0 ≤ U0) (hE0 : 0 ≤ E0)
    (hU : ∀ t : ℝ, t0 ≤ t → t ≤ t1 → U0 ≤ |1 - t| ∧ |1 - t| ≤ U1)
    (hP : ∀ t : ℝ, t0 ≤ t → t ≤ t1 → |1 - 2 * t + 2 * t ^ 2 / 3| ≤ P1)
    (hA : ∀ b : ℝ, 0 ≤ b → b ≤ 1 → 1 ≤ b * (1 + U1) →
      b * (1 - b ^ 2) * (1 + 2 * U1) + b ^ 3 * P1 ≤ W)
    (hB : ∀ b : ℝ, 0 ≤ b → b ≤ 1 → b * (1 + U0) ≤ 1 →
      1 - b ^ 2 + U1 ^ 2 * b ^ 2 * (1 + b) + b ^ 3 * P1 ≤ W)
    (hE : E0 ≤ Real.exp (t0 - 1)) (hW1 : t0 * W ≤ E0) (hW2 : t1 * W ≤ E0 * (1 + t1 - t0))
    (t b c : ℝ) (h0 : t0 ≤ t) (h1 : t ≤ t1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) := by
  obtain ⟨hu0, hu1⟩ := hU t h0 h1
  have hp := hP t h0 h1
  have hpn := abs_nonneg (1 - 2 * t + 2 * t ^ 2 / 3)
  set u := |1 - t|
  set P := |1 - 2 * t + 2 * t ^ 2 / 3|
  have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb0 3
  have hQ : ((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * u) + b ^ 3 * P ≤ W := by
    by_cases hc : 1 ≤ b * (1 + u)
    · refine (QA u P b c (by linarith) hb0 hb1 hc0 hc1 hc).trans ?_
      refine le_trans ?_ (hA b hb0 hb1 (by nlinarith))
      have hs : 0 ≤ b * (1 - b ^ 2) := mul_nonneg hb0 (by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_left hu1 hs, mul_le_mul_of_nonneg_left hp hb3]
    · push Not at hc
      refine (QB u P b c (by linarith) hb0).trans ?_
      refine le_trans ?_ (hB b hb0 hb1 (by nlinarith))
      have hs : 0 ≤ b ^ 2 * (1 + b) := by positivity
      have hu2 : u ^ 2 ≤ U1 ^ 2 := pow_le_pow_left₀ (by linarith) hu1 2
      nlinarith [mul_le_mul_of_nonneg_left hu2 hs, mul_le_mul_of_nonneg_left hp hb3]
  have hexp : E0 * (1 + (t - t0)) ≤ Real.exp (t - 1) := by
    have e : Real.exp (t - 1) = Real.exp (t0 - 1) * Real.exp (t - t0) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have := Real.add_one_le_exp (t - t0)
    have hpos : 0 ≤ 1 + (t - t0) := by linarith
    calc E0 * (1 + (t - t0)) ≤ Real.exp (t0 - 1) * (1 + (t - t0)) :=
          mul_le_mul_of_nonneg_right hE hpos
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have ht : 0 ≤ t := by linarith
  have hlin : t * W ≤ E0 * (1 + (t - t0)) := by
    have key : 0 ≤ (t1 - t0) * (E0 * (1 + (t - t0)) - t * W) := by
      nlinarith [mul_le_mul_of_nonneg_left hW1 (by linarith : (0 : ℝ) ≤ t1 - t),
        mul_le_mul_of_nonneg_left hW2 (by linarith : (0 : ℝ) ≤ t - t0)]
    have := (mul_nonneg_iff_of_pos_left (sub_pos.2 ht01)).mp key
    linarith
  calc _ ≤ t * W := mul_le_mul_of_nonneg_left hQ ht
    _ ≤ _ := hlin.trans hexp

lemma pc0 (t b c : ℝ) (h0 : (0:ℝ) ≤ t) (h1 : t ≤ (3/10:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (0:ℝ) (3/10:ℝ) (7/10:ℝ) (1:ℝ) (1:ℝ) (1419/1000:ℝ) (1839/5000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonneg (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.707)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.588)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (by
      rw [show (0:ℝ) - 1 = (0:ℝ) + (-1) by ring, Real.exp_add]
      nlinarith [Real.add_one_le_exp (0:ℝ), Real.exp_neg_one_gt_d9, Real.exp_pos (0:ℝ),
        Real.exp_pos (-1)])
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc1 (t b c : ℝ) (h0 : (3/10:ℝ) ≤ t) (h1 : t ≤ (1/2:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (3/10:ℝ) (1/2:ℝ) (1/2:ℝ) (7/10:ℝ) (23/50:ℝ) (529/500:ℝ) (2391/5000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonneg (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.642)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.667)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (by
      rw [show (3/10:ℝ) - 1 = (3/10:ℝ) + (-1) by ring, Real.exp_add]
      nlinarith [Real.add_one_le_exp (3/10:ℝ), Real.exp_neg_one_gt_d9, Real.exp_pos (3/10:ℝ),
        Real.exp_pos (-1)])
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc2 (t b c : ℝ) (h0 : (3/2:ℝ) ≤ t) (h1 : t ≤ (17/10:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (3/2:ℝ) (17/10:ℝ) (1/2:ℝ) (7/10:ℝ) (1/2:ℝ) (107/100:ℝ) (16487/10000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.649)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.667)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (3/2:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc3 (t b c : ℝ) (h0 : (17/10:ℝ) ≤ t) (h1 : t ≤ (37/20:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (17/10:ℝ) (37/20:ℝ) (7/10:ℝ) (17/20:ℝ) (71/150:ℝ) (1151/1000:ℝ) (20137/10000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.636)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.588)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (17/10:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc4 (t b c : ℝ) (h0 : (37/20:ℝ) ≤ t) (h1 : t ≤ (2:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (37/20:ℝ) (2:ℝ) (17/20:ℝ) (1:ℝ) (251/600:ℝ) (1249/1000:ℝ) (5849/2500:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.622)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.541)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (37/20:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc5 (t b c : ℝ) (h0 : (2:ℝ) ≤ t) (h1 : t ≤ (43/20:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (2:ℝ) (43/20:ℝ) (1:ℝ) (23/20:ℝ) (1/3:ℝ) (168/125:ℝ) (13591/5000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.609)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.500)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (2:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc6 (t b c : ℝ) (h0 : (43/20:ℝ) ≤ t) (h1 : t ≤ (23/10:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (43/20:ℝ) (23/10:ℝ) (23/20:ℝ) (13/10:ℝ) (131/600:ℝ) (717/500:ℝ) (31581/10000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.596)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.465)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (43/20:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc7 (t b c : ℝ) (h0 : (23/10:ℝ) ≤ t) (h1 : t ≤ (5/2:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (23/10:ℝ) (5/2:ℝ) (13/10:ℝ) (3/2:ℝ) (1/6:ℝ) (789/500:ℝ) (9173/2500:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.590)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.435)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (23/10:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc8 (t b c : ℝ) (h0 : (5/2:ℝ) ≤ t) (h1 : t ≤ (53/20:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (5/2:ℝ) (53/20:ℝ) (3/2:ℝ) (33/20:ℝ) (229/600:ℝ) (87/50:ℝ) (2801/625:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.605)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.400)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (5/2:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc9 (t b c : ℝ) (h0 : (53/20:ℝ) ≤ t) (h1 : t ≤ (14/5:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (53/20:ℝ) (14/5:ℝ) (33/20:ℝ) (9/5:ℝ) (47/75:ℝ) (1911/1000:ℝ) (52069/10000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.621)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.377)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (53/20:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc10 (t b c : ℝ) (h0 : (14/5:ℝ) ≤ t) (h1 : t ≤ (3:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (14/5:ℝ) (3:ℝ) (9/5:ℝ) (2:ℝ) (1:ℝ) (2159/1000:ℝ) (12099/2000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.645)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.357)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (14/5:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc11 (t b c : ℝ) (h0 : (3:ℝ) ≤ t) (h1 : t ≤ (16/5:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (3:ℝ) (16/5:ℝ) (2:ℝ) (11/5:ℝ) (107/75:ℝ) (2431/1000:ℝ) (73887/10000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.673)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.333)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (3:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc12 (t b c : ℝ) (h0 : (16/5:ℝ) ≤ t) (h1 : t ≤ (69/20:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (16/5:ℝ) (69/20:ℝ) (11/5:ℝ) (49/20:ℝ) (407/200:ℝ) (563/200:ℝ) (90241/10000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.713)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.312)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (16/5:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc13 (t b c : ℝ) (h0 : (69/20:ℝ) ≤ t) (h1 : t ≤ (37/10:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (69/20:ℝ) (37/10:ℝ) (49/20:ℝ) (27/10:ℝ) (409/150:ℝ) (1631/500:ℝ) (7241/625:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.762)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.290)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (69/20:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc14 (t b c : ℝ) (h0 : (37/10:ℝ) ≤ t) (h1 : t ≤ (4:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (37/10:ℝ) (4:ℝ) (27/10:ℝ) (3:ℝ) (11/3:ℝ) (3917/1000:ℝ) (74361/5000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.837)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.270)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (37/10:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc15 (t b c : ℝ) (h0 : (4:ℝ) ≤ t) (h1 : t ≤ (87/20:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (4:ℝ) (87/20:ℝ) (3:ℝ) (67/20:ℝ) (983/200:ℝ) (4943/1000:ℝ) (200633/10000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.960)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.250)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (4:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc16 (t b c : ℝ) (h0 : (87/20:ℝ) ≤ t) (h1 : t ≤ (47/10:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (87/20:ℝ) (47/10:ℝ) (67/20:ℝ) (37/10:ℝ) (949/150:ℝ) (3173/500:ℝ) (284331/10000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 1.000)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.230)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (87/20:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc17 (t b c : ℝ) (h0 : (47/10:ℝ) ≤ t) (h1 : t ≤ (103/20:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (47/10:ℝ) (103/20:ℝ) (37/10:ℝ) (83/20:ℝ) (5029/600:ℝ) (8407/1000:ℝ) (25157/625:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 1.000)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.213)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (47/10:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc18 (t b c : ℝ) (h0 : (103/20:ℝ) ≤ t) (h1 : t ≤ (117/20:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (103/20:ℝ) (117/20:ℝ) (83/20:ℝ) (97/20:ℝ) (2423/200:ℝ) (1519/125:ℝ) (627799/10000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 1.000)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.194)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (103/20:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pc19 (t b c : ℝ) (h0 : (117/20:ℝ) ≤ t) (h1 : t ≤ (7:ℝ)) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) :=
  piece (117/20:ℝ) (7:ℝ) (97/20:ℝ) (6:ℝ) (59/3:ℝ) (9863/500:ℝ) (621643/5000:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (fun t h0 h1 => by rw [abs_of_nonpos (by linarith)]; constructor <;> linarith)
    (fun t h0 h1 => by
      have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
      have q2 := sq_nonneg (t - 3 / 2)
      have q3 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h0)
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 1.000)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h1) h0
      have q6 := mul_nonneg (sub_nonneg.2 h1) q3
      have q7 := mul_nonneg (sub_nonneg.2 h2) h0
      nlinarith)
    (fun b h0 h1 h2 => by
      have q1 := mul_nonneg h0 h0
      have q2 := mul_nonneg q1 h0
      have q3 := sq_nonneg (b - 0.171)
      have q4 := mul_nonneg h0 q3
      have q5 := mul_nonneg (sub_nonneg.2 h2) h0
      have q6 := mul_nonneg (sub_nonneg.2 h2) q3
      have q7 := mul_nonneg (sub_nonneg.2 h1) h0
      nlinarith)
    (le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
      (Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (117/20:ℝ) - 1 by norm_num) 10))
    (by norm_num) (by norm_num) t b c h0 h1 hb0 hb1 hc0 hc1

lemma pmid (t b c : ℝ) (h0 : 1 / 2 ≤ t) (h1 : t ≤ 3 / 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) := by
  have hu0 := abs_nonneg (1 - t)
  have hQ := QB (|1 - t|) (|1 - 2 * t + 2 * t ^ 2 / 3|) b c hu0 hb0
  have hu2 : |1 - t| ^ 2 = (1 - t) ^ 2 := sq_abs _
  have hp : |1 - 2 * t + 2 * t ^ 2 / 3| ≤ 1 - 2 * (1 - t) ^ 2 := by
    have q1 := mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1)
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb0 3
  have hB : 1 - b ^ 2 + |1 - t| ^ 2 * b ^ 2 * (1 + b) + b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3| ≤ 1 := by
    rw [hu2]
    have h3 := mul_le_mul_of_nonneg_left hp hb3
    have hu1 : (1 - t) ^ 2 ≤ 1 := by nlinarith
    have h4 : 0 ≤ b ^ 2 * (1 - (1 - t) ^ 2) * (1 - b) :=
      mul_nonneg (mul_nonneg (sq_nonneg b) (by linarith)) (by linarith)
    nlinarith
  have ht : 0 ≤ t := by linarith
  have he : t ≤ Real.exp (t - 1) := by linarith [Real.add_one_le_exp (t - 1)]
  calc _ ≤ t * 1 := mul_le_mul_of_nonneg_left (hQ.trans hB) ht
    _ ≤ _ := by linarith

lemma pbig (t b c : ℝ) (h0 : 7 ≤ t) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) := by
  have hu : |1 - t| = t - 1 := by rw [abs_of_nonpos (by linarith)]; ring
  have hp : |1 - 2 * t + 2 * t ^ 2 / 3| = 1 - 2 * t + 2 * t ^ 2 / 3 := by
    rw [abs_of_nonneg (by nlinarith)]
  have hb3 : b ^ 3 ≤ 1 := pow_le_one₀ hb0 hb1
  have hP0 : 0 ≤ 1 - 2 * t + 2 * t ^ 2 / 3 := by nlinarith
  have hQ : ((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3| ≤ 3 + 4 / 5 * (t - 1) + (1 - 2 * t + 2 * t ^ 2 / 3) := by
    by_cases hc : 1 ≤ b * (1 + |1 - t|)
    · refine (QA _ _ b c (abs_nonneg _) hb0 hb1 hc0 hc1 hc).trans ?_
      rw [hu, hp]
      have hs : b * (1 - b ^ 2) ≤ 2 / 5 := by nlinarith [sq_nonneg (b - 577 / 1000)]
      have hs0 : 0 ≤ b * (1 - b ^ 2) := mul_nonneg hb0 (by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_right hs (by linarith : (0 : ℝ) ≤ 1 + 2 * (t - 1)),
        mul_le_mul_of_nonneg_right hb3 hP0]
    · push Not at hc
      refine (QB _ _ b c (abs_nonneg _) hb0).trans ?_
      rw [hu] at hc ⊢
      rw [hp]
      have hub : (t - 1) * b ≤ 1 := by nlinarith
      have hub0 : 0 ≤ (t - 1) * b := mul_nonneg (by linarith) hb0
      have h2 : (t - 1) ^ 2 * b ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ 1 + b),
        mul_le_mul_of_nonneg_right hb3 hP0, sq_nonneg b]
  have ht : 0 ≤ t := by linarith
  refine (mul_le_mul_of_nonneg_left hQ ht).trans ?_
  have hx : (0 : ℝ) ≤ t - 1 := by linarith
  have he := Real.sum_le_exp_of_nonneg hx 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at he
  push_cast at he
  have y0 : 0 ≤ t - 7 := by linarith
  nlinarith [pow_nonneg y0 2, pow_nonneg y0 3, pow_nonneg y0 4, pow_nonneg y0 5,
    pow_nonneg y0 6, pow_nonneg y0 7]

lemma tq (t b c : ℝ) (ht : 0 < t) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1 - b ^ 2) :
    t * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ Real.exp (t - 1) := by
  rcases le_or_gt t (3/10 : ℝ) with h1 | h1
  · exact pc0 t b c (by linarith) h1 hb0 hb1 hc0 hc1
  rcases le_or_gt t (1/2 : ℝ) with h3 | h3
  · exact pc1 t b c (by linarith) h3 hb0 hb1 hc0 hc1
  rcases le_or_gt t (3/2 : ℝ) with h5 | h5
  · exact pmid t b c (by linarith) (by linarith) hb0 hb1
  rcases le_or_gt t (17/10 : ℝ) with h7 | h7
  · exact pc2 t b c (by linarith) h7 hb0 hb1 hc0 hc1
  rcases le_or_gt t (37/20 : ℝ) with h9 | h9
  · exact pc3 t b c (by linarith) h9 hb0 hb1 hc0 hc1
  rcases le_or_gt t (2 : ℝ) with h11 | h11
  · exact pc4 t b c (by linarith) h11 hb0 hb1 hc0 hc1
  rcases le_or_gt t (43/20 : ℝ) with h13 | h13
  · exact pc5 t b c (by linarith) h13 hb0 hb1 hc0 hc1
  rcases le_or_gt t (23/10 : ℝ) with h15 | h15
  · exact pc6 t b c (by linarith) h15 hb0 hb1 hc0 hc1
  rcases le_or_gt t (5/2 : ℝ) with h17 | h17
  · exact pc7 t b c (by linarith) h17 hb0 hb1 hc0 hc1
  rcases le_or_gt t (53/20 : ℝ) with h19 | h19
  · exact pc8 t b c (by linarith) h19 hb0 hb1 hc0 hc1
  rcases le_or_gt t (14/5 : ℝ) with h21 | h21
  · exact pc9 t b c (by linarith) h21 hb0 hb1 hc0 hc1
  rcases le_or_gt t (3 : ℝ) with h23 | h23
  · exact pc10 t b c (by linarith) h23 hb0 hb1 hc0 hc1
  rcases le_or_gt t (16/5 : ℝ) with h25 | h25
  · exact pc11 t b c (by linarith) h25 hb0 hb1 hc0 hc1
  rcases le_or_gt t (69/20 : ℝ) with h27 | h27
  · exact pc12 t b c (by linarith) h27 hb0 hb1 hc0 hc1
  rcases le_or_gt t (37/10 : ℝ) with h29 | h29
  · exact pc13 t b c (by linarith) h29 hb0 hb1 hc0 hc1
  rcases le_or_gt t (4 : ℝ) with h31 | h31
  · exact pc14 t b c (by linarith) h31 hb0 hb1 hc0 hc1
  rcases le_or_gt t (87/20 : ℝ) with h33 | h33
  · exact pc15 t b c (by linarith) h33 hb0 hb1 hc0 hc1
  rcases le_or_gt t (47/10 : ℝ) with h35 | h35
  · exact pc16 t b c (by linarith) h35 hb0 hb1 hc0 hc1
  rcases le_or_gt t (103/20 : ℝ) with h37 | h37
  · exact pc17 t b c (by linarith) h37 hb0 hb1 hc0 hc1
  rcases le_or_gt t (117/20 : ℝ) with h39 | h39
  · exact pc18 t b c (by linarith) h39 hb0 hb1 hc0 hc1
  rcases le_or_gt t (7 : ℝ) with h41 | h41
  · exact pc19 t b c (by linarith) h41 hb0 hb1 hc0 hc1
  exact pbig t b c (by linarith) hb0 hb1 hc0 hc1

lemma real3 (t b c : ℝ) (ht : 0 < t) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1 - b ^ 2) :
    Real.exp (-t) * (2 * t) * (((1 - b ^ 2) - c ^ 2 / (1 + b)) + b * c * (2 * |1 - t|) +
      b ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) ≤ 2 / Real.exp 1 := by
  have h := tq t b c ht hb0 hb1 hc0 hc1
  have hm : Real.exp (-t) * Real.exp (t - 1) = Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  have hE : 2 / Real.exp 1 = 2 * Real.exp (-1) := by rw [Real.exp_neg]; ring
  rw [hE, ← hm]
  have hp := (Real.exp_pos (-t)).le
  nlinarith [mul_le_mul_of_nonneg_left h hp]

/-- Mobius map of the closed disk: `‖(w - c)/(1 - conj c * w)‖ ≤ 1`. -/
lemma mob_disk (c w : ℂ) (hc : ‖c‖ < 1) (hw : ‖w‖ ≤ 1) :
    ‖(w - c) / (1 - starRingEnd ℂ c * w)‖ ≤ 1 := by
  have hc2 : c.re * c.re + c.im * c.im < 1 := by
    have h := Complex.sq_norm c
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg c]
  have hw2 : w.re * w.re + w.im * w.im ≤ 1 := by
    have h := Complex.sq_norm w
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg w]
  have hd : 1 - starRingEnd ℂ c * w ≠ 0 := by
    intro h
    have h1 : starRingEnd ℂ c * w = 1 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, norm_one] at h2
    nlinarith [norm_nonneg c, norm_nonneg w]
  rw [norm_div, div_le_one (norm_pos_iff.mpr hd)]
  have key : ‖w - c‖ ^ 2 ≤ ‖1 - starRingEnd ℂ c * w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2.le) (sub_nonneg.mpr hw2)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp key

/-- Schwarz-Pick at the origin: `‖G'(0)‖ ≤ 1 - ‖G(0)‖^2`. -/
lemma schwarz_pick0 (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖G z‖ ≤ 1) : ‖deriv G 0‖ ≤ 1 - ‖G 0‖ ^ 2 := by
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have key : ∀ r : ℝ, 0 < r → r < 1 → r * ‖deriv G 0‖ ≤ 1 - r ^ 2 * ‖G 0‖ ^ 2 := by
    intro r hr0 hr1
    set c : ℂ := (r : ℂ) * G 0 with hc
    have hrn : ∀ z : ℂ, ‖(r : ℂ) * G z‖ = r * ‖G z‖ := by
      intro z
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    have hcn : ‖c‖ = r * ‖G 0‖ := hrn 0
    have hc1 : ‖c‖ < 1 := by rw [hcn]; nlinarith [hb 0 m0, norm_nonneg (G 0)]
    have hle : ∀ z ∈ ball (0 : ℂ) 1, ‖(r : ℂ) * G z‖ ≤ 1 := by
      intro z hz
      rw [hrn]; nlinarith [hb z hz, norm_nonneg (G z)]
    have hden : ∀ z ∈ ball (0 : ℂ) 1, 1 - starRingEnd ℂ c * ((r : ℂ) * G z) ≠ 0 := by
      intro z hz h
      have h1 : starRingEnd ℂ c * ((r : ℂ) * G z) = 1 := by linear_combination -h
      have h2 := congrArg norm h1
      rw [norm_mul, Complex.norm_conj, norm_one] at h2
      nlinarith [hle z hz, norm_nonneg ((r : ℂ) * G z), norm_nonneg c]
    set H : ℂ → ℂ := fun z => ((r : ℂ) * G z - c) / (1 - starRingEnd ℂ c * ((r : ℂ) * G z))
      with hH
    have hHd : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt H
        (((r : ℂ) * deriv G z * (1 - starRingEnd ℂ c * ((r : ℂ) * G z)) -
          ((r : ℂ) * G z - c) * (-(starRingEnd ℂ c * ((r : ℂ) * deriv G z)))) /
          (1 - starRingEnd ℂ c * ((r : ℂ) * G z)) ^ 2) z := by
      intro z hz
      have hGz : HasDerivAt G (deriv G z) z :=
        ((hG z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
      have h1 : HasDerivAt (fun w => (r : ℂ) * G w - c) ((r : ℂ) * deriv G z) z :=
        (hGz.const_mul _).sub_const c
      have h2 : HasDerivAt (fun w => 1 - starRingEnd ℂ c * ((r : ℂ) * G w))
          (-(starRingEnd ℂ c * ((r : ℂ) * deriv G z))) z :=
        ((hGz.const_mul _).const_mul _).const_sub 1
      exact h1.div h2 (hden z hz)
    have hHD : DifferentiableOn ℂ H (ball 0 1) :=
      fun z hz => (hHd z hz).differentiableAt.differentiableWithinAt
    have hH0 : H 0 = 0 := by simp [hH, hc]
    have hmaps : Set.MapsTo H (ball 0 1) (closedBall (H 0) 1) := by
      intro z hz
      rw [hH0, mem_closedBall, dist_zero_right]
      exact mob_disk c _ hc1 (hle z hz)
    have hS := Complex.norm_deriv_le_div_of_mapsTo_ball hHD hmaps one_pos
    rw [(hHd 0 m0).deriv, ← hc] at hS
    have hk : 1 - starRingEnd ℂ c * c = ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast; ring
    have hkpos : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
    have hk0 : ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
    have hsimp : ((r : ℂ) * deriv G 0 * (1 - starRingEnd ℂ c * c) -
          (c - c) * (-(starRingEnd ℂ c * ((r : ℂ) * deriv G 0)))) /
          (1 - starRingEnd ℂ c * c) ^ 2 = (r : ℂ) * deriv G 0 / ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [hk]; field_simp; ring
    rw [hsimp, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hr0, abs_of_pos hkpos, div_one,
      div_le_one hkpos, hcn] at hS
    nlinarith
  have X0 := norm_nonneg (deriv G 0)
  have Y0 := norm_nonneg (G 0)
  have Y1 : ‖G 0‖ ≤ 1 := hb 0 m0
  by_contra hcon
  push Not at hcon
  set Z := ‖deriv G 0‖ + ‖G 0‖ ^ 2 with hZ
  have hZ1 : 1 < Z := by linarith
  set r := (1 + Z) / (2 * Z) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by positivity)]; linarith
  have h := key r hr0 hr1
  have h2 : r ^ 2 * Z ≤ 1 := by
    have : r ^ 2 * ‖deriv G 0‖ ≤ r * ‖deriv G 0‖ := by
      have : r ^ 2 ≤ r := by nlinarith
      exact mul_le_mul_of_nonneg_right this X0
    rw [hZ]; nlinarith
  have h3 : r ^ 2 * Z = (1 + Z) ^ 2 / (4 * Z) := by
    rw [hr]; field_simp; ring
  rw [h3, div_le_one (by positivity)] at h2
  nlinarith

/-- `t (t - 1) ≤ e^(t-1)` for `t ≥ 2`. -/
lemma poly_exp (x : ℝ) (hx : 1 ≤ x) : x * (x + 1) ≤ Real.exp x := by
  have h := Real.quadratic_le_exp_of_nonneg (x := x / 2) (by linarith)
  have he : Real.exp x = Real.exp (x / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [he]
  have h0 : 0 ≤ 1 + x / 2 + (x / 2) ^ 2 / 2 := by positivity
  have h1 : (1 + x / 2 + (x / 2) ^ 2 / 2) ^ 2 ≤ Real.exp (x / 2) ^ 2 :=
    pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 1), mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (x - 2))]

/-- The final real estimate. -/
lemma real_bound (t b : ℝ) (ht : 0 < t) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.exp (-t) * (2 * t) * ((1 - b) + b * |1 - t|) ≤ 2 / Real.exp 1 := by
  have hE : 2 / Real.exp 1 = 2 * Real.exp (-1) := by rw [Real.exp_neg]; ring
  have hm : Real.exp (t - 1) * Real.exp (-t) = Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos (-t)
  have h1 : t ≤ Real.exp (t - 1) := by linarith [Real.add_one_le_exp (t - 1)]
  have h2 : t * |1 - t| ≤ Real.exp (t - 1) := by
    rcases le_or_gt t 2 with h | h
    · have : |1 - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg (1 - t)]
    · rw [abs_of_neg (by linarith : 1 - t < 0)]
      have := poly_exp (t - 1) (by linarith)
      nlinarith
  have k1 : t * Real.exp (-t) ≤ Real.exp (-1) := by
    rw [← hm]; exact mul_le_mul_of_nonneg_right h1 hpos.le
  have k2 : t * |1 - t| * Real.exp (-t) ≤ Real.exp (-1) := by
    rw [← hm]; exact mul_le_mul_of_nonneg_right h2 hpos.le
  rw [hE]
  have e1 : Real.exp (-t) * (2 * t) * ((1 - b) + b * |1 - t|) =
      2 * ((1 - b) * (t * Real.exp (-t)) + b * (t * |1 - t| * Real.exp (-t))) := by ring
  rw [e1]
  have := mul_le_mul_of_nonneg_left k1 (sub_nonneg.mpr hb1)
  have := mul_le_mul_of_nonneg_left k2 hb0
  nlinarith

/-- Core `n = 2` estimate when `‖g 0‖ < 1`. -/
theorem krzyz_two_strict (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0 ∧ ‖g z‖ ≤ 1) (h0 : ‖g 0‖ < 1) :
    ‖iteratedDeriv 2 g 0 / 2‖ ≤ 2 / Real.exp 1 := by
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hD : ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) := isOpen_ball.mem_nhds m0
  obtain ⟨L, hL0, hL, hexp⟩ := holo_log g hg (fun z hz => (hb z hz).1)
  have hg0 : g 0 ≠ 0 := (hb 0 m0).1
  have hre : ∀ z ∈ ball (0 : ℂ) 1, (L z).re ≤ 0 := by
    intro z hz
    have h := (hb z hz).2
    rw [hexp z hz, Complex.norm_exp] at h
    exact Real.exp_le_one_iff.mp h
  obtain ⟨a, ha_def⟩ : ∃ a, a = L 0 := ⟨_, rfl⟩
  have hare : a.re = Real.log ‖g 0‖ := by rw [ha_def, hL0, Complex.log_re]
  have hpos : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have ha : a.re < 0 := by rw [hare]; exact Real.log_neg hpos h0
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = a + starRingEnd ℂ a := ⟨_, rfl⟩
  have hden : ∀ z ∈ ball (0 : ℂ) 1, L z + starRingEnd ℂ a ≠ 0 := by
    intro z hz h
    have := congrArg Complex.re h
    simp at this
    linarith [hre z hz]
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ, F = fun z => (L z - a) / (L z + starRingEnd ℂ a) :=
    ⟨_, rfl⟩
  have hFd : DifferentiableOn ℂ F (ball 0 1) := by
    intro z hz
    rw [hFdef]
    exact (((hL z hz).sub_const a).div ((hL z hz).add_const _)
      (hden z hz)).differentiableAt.differentiableWithinAt
  have hF0 : F 0 = 0 := by
    rw [hFdef]
    show (L 0 - a) / _ = 0
    rw [← ha_def, sub_self, zero_div]
  have hmaps : Set.MapsTo F (ball 0 1) (closedBall (F 0) 1) := by
    intro z hz
    rw [hF0, mem_closedBall, dist_zero_right, hFdef]
    exact mobius_le a (L z) ha (hre z hz)
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = dslope F 0 := ⟨_, rfl⟩
  have hGd : DifferentiableOn ℂ G (ball 0 1) := by
    rw [hGdef]; exact (Complex.differentiableOn_dslope hD).2 hFd
  have hGb : ∀ z ∈ ball (0 : ℂ) 1, ‖G z‖ ≤ 1 := by
    intro z hz
    have := Complex.norm_dslope_le_div_of_mapsTo_ball hFd hmaps hz
    rw [hGdef]; simpa using this
  have hSP := schwarz_pick0 G hGd hGb
  have hFG : ∀ z, F z = z * G z := by
    intro z
    have := sub_smul_dslope F 0 z
    rw [hF0, sub_zero, sub_zero, smul_eq_mul, ← hGdef] at this
    exact this.symm
  have hid : ∀ z ∈ ball (0 : ℂ) 1, L z - a = z * G z * (L z - a + σ) := by
    intro z hz
    have h1 := hFG z
    rw [hFdef] at h1
    have e : L z - a + σ = L z + starRingEnd ℂ a := by rw [hσ]; ring
    rw [e, ← h1, div_mul_cancel₀ _ (hden z hz)]
  have hGda : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt G (deriv G z) z := fun z hz =>
    ((hGd z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hA : ∀ z ∈ ball (0 : ℂ) 1, deriv g z / g z =
      (1 * G z + z * deriv G z) * (L z - a + σ) + z * G z * (deriv g z / g z) := by
    intro z hz
    have h1 := ((hasDerivAt_id' z).mul (hGda z hz)).mul (((hL z hz).sub_const a).add_const σ)
    have h2 : HasDerivAt (fun w => L w - a) (deriv g z / g z) z := (hL z hz).sub_const a
    have heq : (fun w => L w - a) =ᶠ[nhds z] (fun w => w * G w * (L w - a + σ)) :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) (fun w hw => hid w hw)
    exact h2.unique (h1.congr_of_eventuallyEq heq)
  have hgd' : DifferentiableOn ℂ (deriv g) (ball 0 1) := hg.deriv isOpen_ball
  have hL'diff : DifferentiableAt ℂ (fun z => deriv g z / g z) 0 :=
    ((hgd' 0 m0).differentiableAt hD).div ((hg 0 m0).differentiableAt hD) hg0
  have hG'diff : DifferentiableAt ℂ (deriv G) 0 :=
    ((hGd.deriv isOpen_ball) 0 m0).differentiableAt hD
  have hl1 : deriv g 0 / g 0 = σ * G 0 := by
    have := hA 0 m0
    rw [← ha_def] at this
    rw [this]; ring
  have hB : deriv (fun z => deriv g z / g z) 0 =
      2 * σ * deriv G 0 + 2 * G 0 * (deriv g 0 / g 0) := by
    have hR := (((hGda 0 m0).const_mul (1 : ℂ)).add ((hasDerivAt_id' (0 : ℂ)).mul
      hG'diff.hasDerivAt)).mul (((hL 0 m0).sub_const a).add_const σ) |>.add
      (((hasDerivAt_id' (0 : ℂ)).mul (hGda 0 m0)).mul hL'diff.hasDerivAt)
    have heq : (fun z => deriv g z / g z) =ᶠ[nhds (0 : ℂ)]
        (fun w => (1 * G w + w * deriv G w) * (L w - a + σ) + w * G w * (deriv g w / g w)) :=
      Filter.eventually_of_mem hD (fun w hw => hA w hw)
    have key := hL'diff.hasDerivAt.unique (hR.congr_of_eventuallyEq heq)
    rw [key, ← ha_def]
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  have hderiv_eq : deriv g =ᶠ[nhds (0 : ℂ)] (fun z => (deriv g z / g z) * g z) :=
    Filter.eventually_of_mem hD (fun z hz => by
      show deriv g z = deriv g z / g z * g z
      rw [div_mul_cancel₀ _ (hb z hz).1])
  have hg0d : HasDerivAt g (deriv g 0) 0 := ((hg 0 m0).differentiableAt hD).hasDerivAt
  have hC : iteratedDeriv 2 g 0 = deriv (fun z => deriv g z / g z) 0 * g 0 +
      (deriv g 0 / g 0) * deriv g 0 := by
    show iteratedDeriv (1 + 1) g 0 = _
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv_eq.deriv_eq]
    exact (hL'diff.hasDerivAt.mul hg0d).deriv
  have e1 : deriv g 0 = σ * G 0 * g 0 := by rw [← hl1, div_mul_cancel₀ _ hg0]
  have hσr : σ = ((2 * a.re : ℝ) : ℂ) := by rw [hσ, Complex.add_conj]
  have hE : iteratedDeriv 2 g 0 / 2 =
      g 0 * ((2 * a.re : ℝ) : ℂ) * (deriv G 0 + G 0 ^ 2 * ((1 - (-a.re) : ℝ) : ℂ)) := by
    rw [hC, hB, hl1, e1, ← hσr]
    have : ((1 - (-a.re) : ℝ) : ℂ) = 1 + σ / 2 := by rw [hσr]; push_cast; ring
    rw [this]; ring
  have ht0 : 0 < -a.re := by linarith
  have hnorm : ‖iteratedDeriv 2 g 0 / 2‖ =
      ‖g 0‖ * (2 * (-a.re)) * ‖deriv G 0 + G 0 ^ 2 * ((1 - (-a.re) : ℝ) : ℂ)‖ := by
    rw [hE, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : 2 * a.re < 0)]
    ring
  have htri : ‖deriv G 0 + G 0 ^ 2 * ((1 - (-a.re) : ℝ) : ℂ)‖ ≤
      (1 - ‖G 0‖ ^ 2) + ‖G 0‖ ^ 2 * |1 - (-a.re)| := by
    calc _ ≤ ‖deriv G 0‖ + ‖G 0 ^ 2 * ((1 - (-a.re) : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖deriv G 0‖ + ‖G 0‖ ^ 2 * |1 - (-a.re)| := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by linarith [hSP]
  have hg0e : ‖g 0‖ = Real.exp (-(-a.re)) := by rw [neg_neg, hare, Real.exp_log hpos]
  have hbd := real_bound (-a.re) (‖G 0‖ ^ 2) ht0 (sq_nonneg _)
    (by nlinarith [hGb 0 m0, norm_nonneg (G 0)])
  rw [hnorm, hg0e]
  calc _ ≤ Real.exp (-(-a.re)) * (2 * (-a.re)) *
        ((1 - ‖G 0‖ ^ 2) + ‖G 0‖ ^ 2 * |1 - (-a.re)|) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ ≤ 2 / Real.exp 1 := hbd

/-- The case `n = 2` of the Krzyz conjecture: `|f''(0)/2| ≤ 2/e`. -/
theorem krzyz_n2 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 ∧ ‖f z‖ ≤ 1) :
    ‖iteratedDeriv 2 f 0 / 2‖ ≤ 2 / Real.exp 1 := by
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have key : ∀ r : ℝ, 0 < r → r < 1 → r * ‖iteratedDeriv 2 f 0 / 2‖ ≤ 2 / Real.exp 1 := by
    intro r hr0 hr1
    obtain ⟨g, hg_def⟩ : ∃ g : ℂ → ℂ, g = fun z => (r : ℂ) * f z := ⟨_, rfl⟩
    have hgd : DifferentiableOn ℂ g (ball 0 1) := by rw [hg_def]; exact hf.const_mul _
    have hgb : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0 ∧ ‖g z‖ ≤ 1 := by
      intro z hz
      rw [hg_def]
      refine ⟨mul_ne_zero (by exact_mod_cast hr0.ne') (hb z hz).1, ?_⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [(hb z hz).2, norm_nonneg (f z)]
    have hg0 : ‖g 0‖ < 1 := by
      rw [hg_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [(hb 0 m0).2, norm_nonneg (f 0)]
    have hder : iteratedDeriv 2 g 0 = (r : ℂ) * iteratedDeriv 2 f 0 := by
      show iteratedDeriv (1 + 1) g 0 = (r : ℂ) * iteratedDeriv (1 + 1) f 0
      rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one, hg_def,
        deriv_const_mul_field', deriv_const_mul_field']
    have h := krzyz_two_strict g hgd hgb hg0
    rw [hder, mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0] at h
    exact h
  by_contra hcon
  push Not at hcon
  set c := 2 / Real.exp 1 with hc
  have hc0 : 0 < c := by positivity
  set d := ‖iteratedDeriv 2 f 0 / 2‖
  have hd : 0 < d := lt_trans hc0 hcon
  have h := key ((c + d) / (2 * d)) (by positivity)
    (by rw [div_lt_one (by positivity)]; linarith)
  have : (c + d) / (2 * d) * d = (c + d) / 2 := by field_simp
  rw [this] at h
  linarith

/-- In the form of `H1` at `n = 2`. -/
theorem krzyz_H1_two (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0 ∧ ‖f z‖ ≤ 1) :
    ‖iteratedDeriv 2 f 0 / (Nat.factorial 2 : ℂ)‖ ≤ 2 / Real.exp 1 := by
  have h2 : (Nat.factorial 2 : ℂ) = 2 := by norm_num [Nat.factorial]
  rw [h2]; exact krzyz_n2 f hf hb

lemma dat {u : ℂ → ℂ} (hu : DifferentiableOn ℂ u (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) : DifferentiableAt ℂ u z :=
  hu.differentiableAt (isOpen_ball.mem_nhds hz)

lemma dcongr {u v : ℂ → ℂ} (h : Set.EqOn u v (ball (0 : ℂ) 1)) :
    Set.EqOn (deriv u) (deriv v) (ball (0 : ℂ) 1) := fun z hz =>
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) h)

lemma zbase {Y P : ℂ → ℂ} (hP : DifferentiableOn ℂ P (ball 0 1))
    (h : Set.EqOn Y (fun z => z * P z) (ball (0 : ℂ) 1)) :
    Set.EqOn (deriv Y) (fun z => 1 * P z + z * deriv P z) (ball (0 : ℂ) 1) := by
  intro z hz
  rw [dcongr h hz]
  have h1 : HasDerivAt (fun z => z * P z) (1 * P z + z * deriv P z) z :=
    (hasDerivAt_id' z).mul (dat hP hz).hasDerivAt
  exact h1.deriv

lemma zstep {W S : ℂ → ℂ} (k : ℂ) (hS : DifferentiableOn ℂ S (ball 0 1))
    (h : Set.EqOn W (fun z => k * S z + z * deriv S z) (ball (0 : ℂ) 1)) :
    Set.EqOn (deriv W) (fun z => (k + 1) * deriv S z + z * deriv (deriv S) z)
      (ball (0 : ℂ) 1) := by
  intro z hz
  rw [dcongr h hz]
  have h1 : HasDerivAt (fun z => k * S z + z * deriv S z)
      (k * deriv S z + (1 * deriv S z + z * deriv (deriv S) z)) z :=
    ((dat hS hz).hasDerivAt.const_mul k).add
      ((hasDerivAt_id' z).mul (dat (hS.deriv isOpen_ball) hz).hasDerivAt)
  rw [h1.deriv]; ring

lemma dmul {u v : ℂ → ℂ} (hu : DifferentiableOn ℂ u (ball 0 1))
    (hv : DifferentiableOn ℂ v (ball 0 1)) :
    Set.EqOn (deriv (fun z => u z * v z)) (fun z => deriv u z * v z + u z * deriv v z)
      (ball (0 : ℂ) 1) :=
  fun z hz => ((dat hu hz).hasDerivAt.mul (dat hv hz).hasDerivAt).deriv

lemma dmul2 {u v : ℂ → ℂ} (hu : DifferentiableOn ℂ u (ball 0 1))
    (hv : DifferentiableOn ℂ v (ball 0 1)) :
    deriv (deriv (fun z => u z * v z)) 0 = deriv (deriv u) 0 * v 0 +
      2 * (deriv u 0 * deriv v 0) + u 0 * deriv (deriv v) 0 := by
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  rw [dcongr (dmul hu hv) m0]
  have hu' := hu.deriv isOpen_ball
  have hv' := hv.deriv isOpen_ball
  have h : HasDerivAt (fun z => deriv u z * v z + u z * deriv v z)
      (deriv (deriv u) 0 * v 0 + deriv u 0 * deriv v 0 +
        (deriv u 0 * deriv v 0 + u 0 * deriv (deriv v) 0)) 0 :=
    ((dat hu' m0).hasDerivAt.mul (dat hv m0).hasDerivAt).add
      ((dat hu m0).hasDerivAt.mul (dat hv' m0).hasDerivAt)
  rw [h.deriv]; ring

lemma lim_one (A B : ℝ → ℝ) (hA : Continuous A) (hB : Continuous B)
    (h : ∀ r : ℝ, 0 < r → r < 1 → A r ≤ B r) : A 1 ≤ B 1 := by
  have hmem : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), A r ≤ B r := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact h r hr.1 hr.2
  exact le_of_tendsto_of_tendsto ((hA.tendsto 1).mono_left nhdsWithin_le_nhds)
    ((hB.tendsto 1).mono_left nhdsWithin_le_nhds) hmem

/-- Schur's second inequality when `‖G 0‖ < 1`. -/
lemma schur_strict (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖G z‖ ≤ 1) (h0 : ‖G 0‖ < 1) :
    ‖deriv (deriv G) 0‖ / 2 * (1 + ‖G 0‖) ≤
      (1 - ‖G 0‖ ^ 2) * (1 + ‖G 0‖) - ‖deriv G 0‖ ^ 2 := by
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hD : ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) := isOpen_ball.mem_nhds m0
  obtain ⟨β, hβ⟩ : ∃ β, β = G 0 := ⟨_, rfl⟩
  have hβ1 : ‖β‖ < 1 := by rw [hβ]; exact h0
  have hden : ∀ z ∈ ball (0 : ℂ) 1, 1 - starRingEnd ℂ β * G z ≠ 0 := by
    intro z hz h
    have h1 : starRingEnd ℂ β * G z = 1 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, norm_one] at h2
    nlinarith [hb z hz, norm_nonneg (G z), norm_nonneg β]
  have hQd : DifferentiableOn ℂ (fun z => 1 - starRingEnd ℂ β * G z) (ball 0 1) :=
    (hG.const_mul _).const_sub 1
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, H = fun z => (G z - β) / (1 - starRingEnd ℂ β * G z) :=
    ⟨_, rfl⟩
  have hHd : DifferentiableOn ℂ H (ball 0 1) := by
    rw [hH]; exact (hG.sub_const β).div hQd hden
  have hH0 : H 0 = 0 := by
    rw [hH]
    show (G 0 - β) / _ = 0
    rw [← hβ, sub_self, zero_div]
  have hmaps : Set.MapsTo H (ball 0 1) (closedBall (H 0) 1) := by
    intro z hz
    rw [hH0, mem_closedBall, dist_zero_right, hH]
    exact mob_disk β (G z) hβ1 (hb z hz)
  obtain ⟨K, hK⟩ : ∃ K : ℂ → ℂ, K = dslope H 0 := ⟨_, rfl⟩
  have hKd : DifferentiableOn ℂ K (ball 0 1) := by
    rw [hK]; exact (Complex.differentiableOn_dslope hD).2 hHd
  have hKb : ∀ z ∈ ball (0 : ℂ) 1, ‖K z‖ ≤ 1 := by
    intro z hz
    have := Complex.norm_dslope_le_div_of_mapsTo_ball hHd hmaps hz
    rw [hK]; simpa using this
  have hSP := schwarz_pick0 K hKd hKb
  have hHK : ∀ z, H z = z * K z := by
    intro z
    have := sub_smul_dslope H 0 z
    rw [hH0, sub_zero, sub_zero, smul_eq_mul, ← hK] at this
    exact this.symm
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun z => K z * (1 - starRingEnd ℂ β * G z) := ⟨_, rfl⟩
  have hPd : DifferentiableOn ℂ P (ball 0 1) := by rw [hP]; exact hKd.mul hQd
  have hid : Set.EqOn (fun z => G z - β) (fun z => z * P z) (ball (0 : ℂ) 1) := by
    intro z hz
    have h1 : (G z - β) / (1 - starRingEnd ℂ β * G z) = z * K z := by rw [← hHK z, hH]
    show G z - β = z * P z
    rw [hP, ← mul_assoc, ← h1, div_mul_cancel₀ _ (hden z hz)]
  have d1 := zbase hPd hid
  have d2 := zstep 1 hPd d1
  have eG : deriv (fun z => G z - β) = deriv G := by funext z; exact deriv_sub_const β
  rw [eG] at d1 d2
  have hγ : deriv G 0 = P 0 := by have := d1 m0; simp at this; exact this
  have hG2 : deriv (deriv G) 0 = 2 * deriv P 0 := by
    have := d2 m0; simp at this; rw [this]; ring
  have hP0 : P 0 = K 0 * (1 - starRingEnd ℂ β * β) := by rw [hP, hβ]
  have hP1 : deriv P 0 = deriv K 0 * (1 - starRingEnd ℂ β * β) +
      K 0 * (-(starRingEnd ℂ β * deriv G 0)) := by
    have h1 : HasDerivAt (fun z => K z * (1 - starRingEnd ℂ β * G z))
        (deriv K 0 * (1 - starRingEnd ℂ β * G 0) + K 0 * (-(starRingEnd ℂ β * deriv G 0))) 0 :=
      (dat hKd m0).hasDerivAt.mul (((dat hG m0).hasDerivAt.const_mul _).const_sub 1)
    rw [hP, h1.deriv, ← hβ]
  have hk : 1 - starRingEnd ℂ β * β = ((1 - ‖β‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hs : 0 < 1 - ‖β‖ ^ 2 := by nlinarith [norm_nonneg β]
  rw [hk] at hP0 hP1
  rw [← hβ]
  set s := 1 - ‖β‖ ^ 2 with hs_def
  have hc : ‖deriv G 0‖ = ‖K 0‖ * s := by
    rw [hγ, hP0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hX : ‖deriv (deriv G) 0‖ / 2 ≤ ‖deriv K 0‖ * s + ‖β‖ * (‖K 0‖ * ‖deriv G 0‖) := by
    have n2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hG2, hP1, norm_mul, n2]
    have := norm_add_le (deriv K 0 * ((s : ℝ) : ℂ)) (K 0 * (-(starRingEnd ℂ β * deriv G 0)))
    rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs] at this
    linarith
  have hK0 := norm_nonneg (K 0)
  have hb0 := norm_nonneg β
  have hK1 := norm_nonneg (deriv K 0)
  rw [hc]
  have e : s = (1 - ‖β‖) * (1 + ‖β‖) := by rw [hs_def]; ring
  have h3 : ‖deriv (deriv G) 0‖ / 2 ≤ s * (1 - ‖K 0‖ ^ 2 * (1 - ‖β‖)) := by
    rw [hc] at hX
    nlinarith [mul_le_mul_of_nonneg_right hSP hs.le]
  have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : (0 : ℝ) ≤ 1 + ‖β‖)
  calc _ ≤ s * (1 - ‖K 0‖ ^ 2 * (1 - ‖β‖)) * (1 + ‖β‖) := h4
    _ = _ := by rw [e]; ring

/-- Schur's second inequality: `|G''(0)/2| (1 + |G 0|) ≤ (1 - |G 0|^2)(1 + |G 0|) - |G'(0)|^2`. -/
lemma schur2 (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖G z‖ ≤ 1) :
    ‖deriv (deriv G) 0‖ / 2 * (1 + ‖G 0‖) ≤
      (1 - ‖G 0‖ ^ 2) * (1 + ‖G 0‖) - ‖deriv G 0‖ ^ 2 := by
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have key : ∀ r : ℝ, 0 < r → r < 1 →
      (fun r : ℝ => r * ‖deriv (deriv G) 0‖ / 2 * (1 + r * ‖G 0‖)) r ≤
      (fun r : ℝ => (1 - (r * ‖G 0‖) ^ 2) * (1 + r * ‖G 0‖) - (r * ‖deriv G 0‖) ^ 2) r := by
    intro r hr0 hr1
    obtain ⟨Gr, hGr⟩ : ∃ Gr : ℂ → ℂ, Gr = fun z => (r : ℂ) * G z := ⟨_, rfl⟩
    have hrn : ∀ w : ℂ, ‖(r : ℂ) * w‖ = r * ‖w‖ := fun w => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    have h1 : DifferentiableOn ℂ Gr (ball 0 1) := by rw [hGr]; exact hG.const_mul _
    have h2 : ∀ z ∈ ball (0 : ℂ) 1, ‖Gr z‖ ≤ 1 := by
      intro z hz
      rw [hGr]
      show ‖(r : ℂ) * G z‖ ≤ 1
      rw [hrn]; nlinarith [hb z hz, norm_nonneg (G z)]
    have h3 : ‖Gr 0‖ < 1 := by
      rw [hGr]
      show ‖(r : ℂ) * G 0‖ < 1
      rw [hrn]; nlinarith [hb 0 m0, norm_nonneg (G 0)]
    have e1 : deriv Gr = fun z => (r : ℂ) * deriv G z := by
      rw [hGr]; exact deriv_const_mul_field' _
    have e2 : deriv (deriv Gr) = fun z => (r : ℂ) * deriv (deriv G) z := by
      rw [e1]; exact deriv_const_mul_field' _
    have e0 : Gr 0 = (r : ℂ) * G 0 := by rw [hGr]
    have := schur_strict Gr h1 h2 h3
    rw [e2, e1, e0] at this
    beta_reduce at this
    rw [hrn, hrn, hrn] at this
    show r * ‖deriv (deriv G) 0‖ / 2 * (1 + r * ‖G 0‖) ≤ _
    linarith
  have := lim_one _ _ (by fun_prop) (by fun_prop) key
  simp only [one_mul] at this
  exact this

/-- Core `n = 3` estimate when `‖g 0‖ < 1`. -/
theorem krzyz_three_strict (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0 ∧ ‖g z‖ ≤ 1) (h0 : ‖g 0‖ < 1) :
    ‖iteratedDeriv 3 g 0 / 6‖ ≤ 2 / Real.exp 1 := by
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hD : ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) := isOpen_ball.mem_nhds m0
  obtain ⟨L, hL0, hL, hexp⟩ := holo_log g hg (fun z hz => (hb z hz).1)
  have hg0 : g 0 ≠ 0 := (hb 0 m0).1
  have hre : ∀ z ∈ ball (0 : ℂ) 1, (L z).re ≤ 0 := by
    intro z hz
    have h := (hb z hz).2
    rw [hexp z hz, Complex.norm_exp] at h
    exact Real.exp_le_one_iff.mp h
  obtain ⟨a, ha_def⟩ : ∃ a, a = L 0 := ⟨_, rfl⟩
  have hare : a.re = Real.log ‖g 0‖ := by rw [ha_def, hL0, Complex.log_re]
  have hpos : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have ha : a.re < 0 := by rw [hare]; exact Real.log_neg hpos h0
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = a + starRingEnd ℂ a := ⟨_, rfl⟩
  have hden : ∀ z ∈ ball (0 : ℂ) 1, L z + starRingEnd ℂ a ≠ 0 := by
    intro z hz h
    have := congrArg Complex.re h
    simp at this
    linarith [hre z hz]
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ, F = fun z => (L z - a) / (L z + starRingEnd ℂ a) :=
    ⟨_, rfl⟩
  have hFd : DifferentiableOn ℂ F (ball 0 1) := by
    intro z hz
    rw [hFdef]
    exact (((hL z hz).sub_const a).div ((hL z hz).add_const _)
      (hden z hz)).differentiableAt.differentiableWithinAt
  have hF0 : F 0 = 0 := by
    rw [hFdef]
    show (L 0 - a) / _ = 0
    rw [← ha_def, sub_self, zero_div]
  have hmaps : Set.MapsTo F (ball 0 1) (closedBall (F 0) 1) := by
    intro z hz
    rw [hF0, mem_closedBall, dist_zero_right, hFdef]
    exact mobius_le a (L z) ha (hre z hz)
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = dslope F 0 := ⟨_, rfl⟩
  have hGd : DifferentiableOn ℂ G (ball 0 1) := by
    rw [hGdef]; exact (Complex.differentiableOn_dslope hD).2 hFd
  have hGb : ∀ z ∈ ball (0 : ℂ) 1, ‖G z‖ ≤ 1 := by
    intro z hz
    have := Complex.norm_dslope_le_div_of_mapsTo_ball hFd hmaps hz
    rw [hGdef]; simpa using this
  have hSP := schwarz_pick0 G hGd hGb
  have hSc := schur2 G hGd hGb
  have hFG : ∀ z, F z = z * G z := by
    intro z
    have := sub_smul_dslope F 0 z
    rw [hF0, sub_zero, sub_zero, smul_eq_mul, ← hGdef] at this
    exact this.symm
  have hLd : DifferentiableOn ℂ L (ball 0 1) :=
    fun z hz => (hL z hz).differentiableAt.differentiableWithinAt
  obtain ⟨M, hM⟩ : ∃ M : ℂ → ℂ, M = fun z => L z - a := ⟨_, rfl⟩
  have hMd : DifferentiableOn ℂ M (ball 0 1) := by rw [hM]; exact hLd.sub_const a
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun z => G z * (M z + σ) := ⟨_, rfl⟩
  have hNd : DifferentiableOn ℂ (fun z => M z + σ) (ball 0 1) := hMd.add_const σ
  have hPd : DifferentiableOn ℂ P (ball 0 1) := by rw [hP]; exact hGd.mul hNd
  have hid : Set.EqOn M (fun z => z * P z) (ball (0 : ℂ) 1) := by
    intro z hz
    have h1 := hFG z
    rw [hFdef] at h1
    have e : L z - a + σ = L z + starRingEnd ℂ a := by rw [hσ]; ring
    show M z = z * P z
    rw [hP, hM]
    show L z - a = z * (G z * (L z - a + σ))
    rw [e, ← mul_assoc, ← h1, div_mul_cancel₀ _ (hden z hz)]
  have d1 := zbase hPd hid
  have d2 := zstep 1 hPd d1
  have d3 := zstep (1 + 1) (hPd.deriv isOpen_ball) d2
  have eM : deriv M = deriv L := by rw [hM]; funext z; exact deriv_sub_const a
  have eN : deriv (fun z => M z + σ) = deriv M := by funext z; exact deriv_add_const σ
  rw [eM] at d1 d2 d3 eN
  have hM0 : M 0 = 0 := by
    rw [hM]
    show L 0 - a = 0
    rw [← ha_def, sub_self]
  -- values at 0
  have l1 : deriv L 0 = P 0 := by have := d1 m0; simp at this; exact this
  have l2 : deriv (deriv L) 0 = 2 * deriv P 0 := by
    have := d2 m0; simp at this; rw [this]; ring
  have l3 : deriv (deriv (deriv L)) 0 = 3 * deriv (deriv P) 0 := by
    have := d3 m0; simp at this; rw [this]; ring
  have p0 : P 0 = G 0 * σ := by rw [hP]; simp [hM0]
  have p1 : deriv P 0 = deriv G 0 * σ + G 0 * deriv L 0 := by
    rw [hP, (dmul hGd hNd m0), eN]
    beta_reduce
    rw [hM0, zero_add]
  have p2 : deriv (deriv P) 0 = deriv (deriv G) 0 * σ + 2 * (deriv G 0 * deriv L 0) +
      G 0 * deriv (deriv L) 0 := by
    rw [hP, dmul2 hGd hNd, eN, hM0, zero_add]
  -- derivatives of g
  have hgexp : Set.EqOn g (fun z => Complex.exp (L z)) (ball (0 : ℂ) 1) := fun z hz => hexp z hz
  have hL1d := hLd.deriv isOpen_ball
  have g1 : Set.EqOn (deriv g) (fun z => g z * deriv L z) (ball (0 : ℂ) 1) := by
    intro z hz
    rw [dcongr hgexp hz, ((dat hLd hz).hasDerivAt.cexp).deriv, ← hexp z hz]
  have g2 : Set.EqOn (deriv (deriv g)) (fun z => deriv g z * deriv L z +
      g z * deriv (deriv L) z) (ball (0 : ℂ) 1) := by
    intro z hz
    rw [dcongr g1 hz, dmul hg hL1d hz]
  have hg1d := hg.deriv isOpen_ball
  have hL2d := hL1d.deriv isOpen_ball
  have g3 : deriv (deriv (deriv g)) 0 = deriv (deriv g) 0 * deriv L 0 +
      deriv g 0 * deriv (deriv L) 0 + (deriv g 0 * deriv (deriv L) 0 +
        g 0 * deriv (deriv (deriv L)) 0) := by
    rw [dcongr g2 m0]
    have h : HasDerivAt (fun z => deriv g z * deriv L z + g z * deriv (deriv L) z)
        (deriv (deriv g) 0 * deriv L 0 + deriv g 0 * deriv (deriv L) 0 +
          (deriv g 0 * deriv (deriv L) 0 + g 0 * deriv (deriv (deriv L)) 0)) 0 :=
      ((dat hg1d m0).hasDerivAt.mul (dat hL1d m0).hasDerivAt).add
        ((dat hg m0).hasDerivAt.mul (dat hL2d m0).hasDerivAt)
    exact h.deriv
  have g1' := g1 m0
  have g2' := g2 m0
  simp only at g1' g2'
  have hσr : σ = ((2 * a.re : ℝ) : ℂ) := by rw [hσ, Complex.add_conj]
  have hE : iteratedDeriv 3 g 0 / 6 = g 0 * ((2 * a.re : ℝ) : ℂ) *
      (deriv (deriv G) 0 / 2 + G 0 * deriv G 0 * ((2 * (1 - (-a.re)) : ℝ) : ℂ) +
        G 0 ^ 3 * ((1 - 2 * (-a.re) + 2 * (-a.re) ^ 2 / 3 : ℝ) : ℂ)) := by
    show iteratedDeriv (1 + 1 + 1) g 0 / 6 = _
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, g3, g2', g1', l3, p2, l2,
      p1, l1, p0, ← hσr]
    have e1 : ((2 * (1 - (-a.re)) : ℝ) : ℂ) = 2 + σ := by rw [hσr]; push_cast; ring
    have e2 : ((1 - 2 * (-a.re) + 2 * (-a.re) ^ 2 / 3 : ℝ) : ℂ) = 1 + σ + σ ^ 2 / 6 := by
      rw [hσr]; push_cast; ring
    rw [e1, e2]; ring
  have ht0 : 0 < -a.re := by linarith
  set t := -a.re with ht
  have hnorm : ‖iteratedDeriv 3 g 0 / 6‖ ≤ ‖g 0‖ * (2 * t) *
      ((‖deriv (deriv G) 0‖ / 2) + ‖G 0‖ * ‖deriv G 0‖ * (2 * |1 - t|) +
        ‖G 0‖ ^ 3 * |1 - 2 * t + 2 * t ^ 2 / 3|) := by
    rw [hE, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : 2 * a.re < 0)]
    have hn : -(2 * a.re) = 2 * t := by rw [ht]; ring
    rw [hn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_
    · rw [norm_div]; norm_num
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hg0e : ‖g 0‖ = Real.exp (-t) := by rw [ht, neg_neg, hare, Real.exp_log hpos]
  have hb0 := norm_nonneg (G 0)
  have hb1 : ‖G 0‖ ≤ 1 := hGb 0 m0
  have hδ : ‖deriv (deriv G) 0‖ / 2 ≤ (1 - ‖G 0‖ ^ 2) - ‖deriv G 0‖ ^ 2 / (1 + ‖G 0‖) := by
    have h1 : (0 : ℝ) < 1 + ‖G 0‖ := by linarith
    have key : (‖deriv (deriv G) 0‖ / 2) * (1 + ‖G 0‖) ≤
        ((1 - ‖G 0‖ ^ 2) - ‖deriv G 0‖ ^ 2 / (1 + ‖G 0‖)) * (1 + ‖G 0‖) := by
      rw [sub_mul, div_mul_cancel₀ _ h1.ne']; linarith [hSc]
    exact le_of_mul_le_mul_right key h1
  have hbd := real3 t (‖G 0‖) (‖deriv G 0‖) ht0 hb0 hb1 (norm_nonneg _) hSP
  rw [hg0e] at hnorm
  refine hnorm.trans (le_trans ?_ hbd)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith [hδ]



/-- The case `n = 3` of the Krzyz conjecture: `|f'''(0)/6| ≤ 2/e`. -/
theorem krzyz_n3 (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 ∧ ‖f z‖ ≤ 1) :
    ‖iteratedDeriv 3 f 0 / 6‖ ≤ 2 / Real.exp 1 := by
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have key : ∀ r : ℝ, 0 < r → r < 1 → r * ‖iteratedDeriv 3 f 0 / 6‖ ≤ 2 / Real.exp 1 := by
    intro r hr0 hr1
    obtain ⟨g, hg_def⟩ : ∃ g : ℂ → ℂ, g = fun z => (r : ℂ) * f z := ⟨_, rfl⟩
    have hgd : DifferentiableOn ℂ g (ball 0 1) := by rw [hg_def]; exact hf.const_mul _
    have hgb : ∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0 ∧ ‖g z‖ ≤ 1 := by
      intro z hz
      rw [hg_def]
      refine ⟨mul_ne_zero (by exact_mod_cast hr0.ne') (hb z hz).1, ?_⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [(hb z hz).2, norm_nonneg (f z)]
    have hg0 : ‖g 0‖ < 1 := by
      rw [hg_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [(hb 0 m0).2, norm_nonneg (f 0)]
    have hder : iteratedDeriv 3 g 0 = (r : ℂ) * iteratedDeriv 3 f 0 := by
      show iteratedDeriv (1 + 1 + 1) g 0 = (r : ℂ) * iteratedDeriv (1 + 1 + 1) f 0
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_one, hg_def, deriv_const_mul_field',
        deriv_const_mul_field', deriv_const_mul_field']
    have h := krzyz_three_strict g hgd hgb hg0
    rw [hder, mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0] at h
    exact h
  by_contra hcon
  push Not at hcon
  set c := 2 / Real.exp 1 with hc
  have hc0 : 0 < c := by positivity
  set d := ‖iteratedDeriv 3 f 0 / 6‖
  have hd : 0 < d := lt_trans hc0 hcon
  have h := key ((c + d) / (2 * d)) (by positivity)
    (by rw [div_lt_one (by positivity)]; linarith)
  have : (c + d) / (2 * d) * d = (c + d) / 2 := by field_simp
  rw [this] at h
  linarith

/-- In the form of `H1` at `n = 3`. -/
theorem krzyz_H1_three (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0 ∧ ‖f z‖ ≤ 1) :
    ‖iteratedDeriv 3 f 0 / (Nat.factorial 3 : ℂ)‖ ≤ 2 / Real.exp 1 := by
  have h3 : (Nat.factorial 3 : ℂ) = 6 := by norm_num [Nat.factorial]
  rw [h3]; exact krzyz_n3 f hf hb

/-- The case `n = 4` (Tan Delin 1983). -/
def H1 : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) →
    (∀ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0 ∧ ‖f z‖ ≤ 1) →
    ‖iteratedDeriv 4 f 0 / (Nat.factorial 4 : ℂ)‖ ≤ 2 / Real.exp 1

/-- The case `n = 5` (Samaris 2003). -/
def H2 : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) →
    (∀ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0 ∧ ‖f z‖ ≤ 1) →
    ‖iteratedDeriv 5 f 0 / (Nat.factorial 5 : ℂ)‖ ≤ 2 / Real.exp 1

theorem main : H1 → H2 → OMA.R_mo_297054_R1.H1 := by
  intro h4 h5 f hf hb n hn2 hn5
  interval_cases n
  · exact krzyz_H1_two f hf hb
  · exact krzyz_H1_three f hf hb
  · exact h4 f hf hb
  · exact h5 f hf hb

end OMA.R_mo_297054_R1_H1_R1
