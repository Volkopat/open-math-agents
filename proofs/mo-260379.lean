import OMAStatements.S_mo_260379
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic

namespace OMA.TetIter260379

noncomputable def v : ℕ → ℝ → ℝ
  | 0, l => l
  | n + 1, l => l * (1 - Real.exp (-v n l))

noncomputable def d : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, l => 1 - Real.exp (-v n l) + l * Real.exp (-v n l) * d n l

noncomputable def e : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, l => Real.exp (-v n l) * (2 * d n l + l * (e n l - (d n l) ^ 2))

theorem hasDerivAt_v (n : ℕ) (l : ℝ) : HasDerivAt (v n) (d n l) l := by
  induction n with
  | zero => exact hasDerivAt_id l
  | succ n ih =>
    have hExp : HasDerivAt (fun x : ℝ => Real.exp (-v n x))
        (Real.exp (-v n l) * -d n l) l := ih.neg.exp
    have h : HasDerivAt (fun x : ℝ => x * (1 - Real.exp (-v n x)))
        (1 * (1 - Real.exp (-v n l)) + l * (0 - Real.exp (-v n l) * -d n l)) l :=
      (hasDerivAt_id l).mul ((hasDerivAt_const l (1 : ℝ)).sub hExp)
    have hc : 1 * (1 - Real.exp (-v n l)) + l * (0 - Real.exp (-v n l) * -d n l) =
        d (n + 1) l := by
      rw [d]
      ring
    rw [hc] at h
    exact h

theorem hasDerivAt_d (n : ℕ) (l : ℝ) : HasDerivAt (d n) (e n l) l := by
  induction n with
  | zero => exact hasDerivAt_const l (1 : ℝ)
  | succ n ih =>
    have hExp : HasDerivAt (fun x : ℝ => Real.exp (-v n x))
        (Real.exp (-v n l) * -d n l) l := (hasDerivAt_v n l).neg.exp
    have h : HasDerivAt (fun x : ℝ => 1 - Real.exp (-v n x) + x * Real.exp (-v n x) * d n x)
        (0 - Real.exp (-v n l) * -d n l +
          ((1 * Real.exp (-v n l) + l * (Real.exp (-v n l) * -d n l)) * d n l +
            l * Real.exp (-v n l) * e n l)) l :=
      ((hasDerivAt_const l (1 : ℝ)).sub hExp).add (((hasDerivAt_id l).mul hExp).mul ih)
    have hc : 0 - Real.exp (-v n l) * -d n l +
        ((1 * Real.exp (-v n l) + l * (Real.exp (-v n l) * -d n l)) * d n l +
          l * Real.exp (-v n l) * e n l) = e (n + 1) l := by
      rw [e]
      ring
    rw [hc] at h
    exact h

theorem v_pos (n : ℕ) {l : ℝ} (hl : 0 < l) : 0 < v n l := by
  induction n with
  | zero => exact hl
  | succ n ih =>
    change 0 < l * (1 - Real.exp (-v n l))
    exact mul_pos hl (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ih)))

theorem v_step_le_mul (n : ℕ) {l : ℝ} (hl : 0 ≤ l) : v (n + 1) l ≤ l * v n l := by
  change l * (1 - Real.exp (-v n l)) ≤ l * v n l
  exact mul_le_mul_of_nonneg_left (by linarith [Real.one_sub_le_exp_neg (v n l)]) hl

private theorem exp_neg_ge_third {l : ℝ} (hl1 : l ≤ 1) : (1 : ℝ) / 3 ≤ Real.exp (-l) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos l)
    ((Real.exp_le_exp.mpr hl1).trans Real.exp_one_lt_three.le)

private theorem exp_two_thirds_lt_two : Real.exp (2 / 3 : ℝ) < 2 := by
  have hpow : (Real.exp (2 / 3 : ℝ)) ^ (3 : ℕ) = (Real.exp 1) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have hone : Real.exp 1 ≤ (11 / 4 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
  apply lt_of_pow_lt_pow_left₀ 3 (by norm_num)
  rw [hpow]
  calc
    (Real.exp 1) ^ (2 : ℕ) ≤ (11 / 4 : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 1).le hone 2
    _ < (2 : ℝ) ^ (3 : ℕ) := by norm_num

private theorem exp_neg_ge_half {x : ℝ} (hx : x ≤ 2 / 3) : (1 : ℝ) / 2 ≤ Real.exp (-x) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos x)
    ((Real.exp_le_exp.mpr hx).trans exp_two_thirds_lt_two.le)

theorem first_bounds (n : ℕ) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    0 < d n l ∧ d n l ≤ 1 ∧ v n l ≤ d n l := by
  induction n with
  | zero => exact ⟨zero_lt_one, le_rfl, hl1⟩
  | succ n ih =>
    rcases ih with ⟨hd, hd1, _⟩
    have hExp := Real.exp_pos (-v n l)
    have hgap : 0 < 1 - Real.exp (-v n l) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (v_pos n hl)))
    have hProd : 0 ≤ l * Real.exp (-v n l) * d n l :=
      mul_nonneg (mul_nonneg hl.le hExp.le) hd.le
    have hProdLe : l * Real.exp (-v n l) * d n l ≤ Real.exp (-v n l) :=
      (mul_le_of_le_one_right (mul_nonneg hl.le hExp.le) hd1).trans
        (mul_le_of_le_one_left hExp.le hl1)
    change 0 < 1 - Real.exp (-v n l) + l * Real.exp (-v n l) * d n l ∧
      1 - Real.exp (-v n l) + l * Real.exp (-v n l) * d n l ≤ 1 ∧
      l * (1 - Real.exp (-v n l)) ≤ 1 - Real.exp (-v n l) + l * Real.exp (-v n l) * d n l
    refine ⟨add_pos_of_pos_of_nonneg hgap hProd, by linarith, ?_⟩
    exact (mul_le_of_le_one_left hgap.le hl1).trans (le_add_of_nonneg_right hProd)

theorem v_le_two_thirds (n : ℕ) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    v (n + 1) l ≤ 2 / 3 := by
  induction n with
  | zero =>
    have hgap : 0 ≤ 1 - Real.exp (-l) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.le))
    change l * (1 - Real.exp (-l)) ≤ 2 / 3
    exact (mul_le_of_le_one_left hgap hl1).trans (by linarith [exp_neg_ge_third hl1])
  | succ n ih =>
    exact (v_step_le_mul (n + 1) hl.le).trans
      ((mul_le_of_le_one_left (v_pos (n + 1) hl).le hl1).trans ih)

private theorem d_step_le_two (n : ℕ) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    d (n + 1) l ≤ 2 * d n l := by
  obtain ⟨hd, _, hvd⟩ := first_bounds n hl hl1
  have hg : 1 - Real.exp (-v n l) ≤ d n l :=
    (show 1 - Real.exp (-v n l) ≤ v n l by linarith [Real.one_sub_le_exp_neg (v n l)]).trans hvd
  have hProd : l * Real.exp (-v n l) ≤ 1 :=
    (mul_le_of_le_one_left (Real.exp_pos _).le hl1).trans
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (v_pos n hl).le))
  change 1 - Real.exp (-v n l) + l * Real.exp (-v n l) * d n l ≤ 2 * d n l
  linarith only [hg, mul_le_of_le_one_left hd.le hProd]

theorem second_bound (n : ℕ) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    (d (n + 1) l) ^ 2 / 3 ≤ e (n + 1) l := by
  induction n with
  | zero =>
    obtain ⟨hd, hd1, _⟩ := first_bounds 1 hl hl1
    change (d 1 l) ^ 2 / 3 ≤ Real.exp (-l) * (2 * 1 + l * (0 - (1 : ℝ) ^ 2))
    calc
      (d 1 l) ^ 2 / 3 ≤ (1 : ℝ) / 3 := by
        have h := pow_le_pow_left₀ hd.le hd1 2
        linarith only [h]
      _ ≤ Real.exp (-l) := exp_neg_ge_third hl1
      _ ≤ Real.exp (-l) * (2 * 1 + l * (0 - (1 : ℝ) ^ 2)) :=
        le_mul_of_one_le_right (Real.exp_pos _).le (by linarith only [hl1])
  | succ n ih =>
    obtain ⟨hd, hd1, _⟩ := first_bounds (n + 1) hl hl1
    obtain ⟨hds, hds1, _⟩ := first_bounds (n + 2) hl hl1
    have hMul : l * (d (n + 1) l) ^ 2 ≤ d (n + 1) l := by
      rw [pow_two, ← mul_assoc]
      exact mul_le_of_le_one_left hd.le ((mul_le_of_le_one_left hd.le hl1).trans hd1)
    have hInner : (4 / 3 : ℝ) * d (n + 1) l ≤
        2 * d (n + 1) l + l * (e (n + 1) l - (d (n + 1) l) ^ 2) := by
      have hAux := mul_le_mul_of_nonneg_left
        (sub_le_sub_right ih ((d (n + 1) l) ^ 2)) hl.le
      nlinarith only [hMul, hAux]
    have hsquare : (d (n + 2) l) ^ 2 ≤ d (n + 2) l := by
      rw [pow_two]
      exact mul_le_of_le_one_left hds.le hds1
    calc
      (d (n + 2) l) ^ 2 / 3 ≤ (2 / 3 : ℝ) * d (n + 1) l := by
        linarith only [hsquare, d_step_le_two (n + 1) hl hl1]
      _ = (1 / 2 : ℝ) * ((4 / 3 : ℝ) * d (n + 1) l) := by ring
      _ ≤ Real.exp (-v (n + 1) l) * ((4 / 3 : ℝ) * d (n + 1) l) :=
        mul_le_mul_of_nonneg_right (exp_neg_ge_half (v_le_two_thirds n hl hl1)) (by positivity)
      _ ≤ e (n + 2) l := mul_le_mul_of_nonneg_left hInner (Real.exp_pos _).le

theorem iter_bounds (n : ℕ) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    0 < v (n + 1) l ∧ v (n + 1) l ≤ 2 / 3 ∧ 0 < d (n + 1) l ∧
      d (n + 1) l ≤ 1 ∧ (d (n + 1) l) ^ 2 / 3 ≤ e (n + 1) l :=
  ⟨v_pos (n + 1) hl, v_le_two_thirds n hl hl1, (first_bounds (n + 1) hl hl1).1,
    (first_bounds (n + 1) hl hl1).2.1, second_bound n hl hl1⟩

end OMA.TetIter260379

open Filter MeasureTheory Set
open scoped Interval Topology

namespace OMA.TetLog260379

noncomputable section

open Real intervalIntegral

private def moment (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (-t) ^ n * exp (-x * t)

def q (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, exp (-x * t)

def g (x : ℝ) : ℝ := log (q x)

def g1 (x : ℝ) : ℝ := moment 1 x / q x

def g2 (x : ℝ) : ℝ := moment 2 x / q x - (g1 x) ^ 2

private theorem hi {f : ℝ → ℝ} (hf : Continuous f) : IntervalIntegrable f volume 0 1 :=
  hf.intervalIntegrable _ _

private theorem hasDerivAt_moment (n : ℕ) (x : ℝ) :
    HasDerivAt (moment n) (moment (n + 1) x) x := by
  unfold moment
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun y t => (-t) ^ n * exp (-y * t))
    (F' := fun y t => (-t) ^ (n + 1) * exp (-y * t))
    (bound := fun _ => exp (|x| + 1)) (Metric.ball_mem_nhds x zero_lt_one)
    ?_ (hi (by fun_prop)) ?_ ?_ (hi continuous_const) ?_).2
  · exact Eventually.of_forall fun y => (show Continuous (fun t : ℝ =>
      (-t) ^ n * exp (-y * t)) by fun_prop).aestronglyMeasurable
  · exact (show Continuous (fun t : ℝ =>
      (-t) ^ (n + 1) * exp (-x * t)) by fun_prop).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht y hy => ?_
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Metric.mem_ball, Real.dist_eq] at hy
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_nonneg ht.1.le,
      abs_of_pos (exp_pos _)]
    have hy' : |y| ≤ |x| + 1 := by
      calc
        |y| = |(y - x) + x| := by rw [sub_add_cancel]
        _ ≤ |y - x| + |x| := abs_add_le _ _
        _ ≤ |x| + 1 := by linarith
    have hyt : -y * t ≤ |x| + 1 := by
      calc
        -y * t ≤ |y| * t := mul_le_mul_of_nonneg_right (neg_le_abs _) ht.1.le
        _ ≤ |y| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
        _ ≤ |x| + 1 := by simpa using hy'
    calc
      t ^ (n + 1) * exp (-y * t) ≤ 1 * exp (-y * t) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ ht.1.le ht.2) (exp_pos _).le
      _ ≤ exp (|x| + 1) := by rw [one_mul]; exact exp_le_exp.mpr hyt
  · refine Eventually.of_forall fun t _ y _ => ?_
    have h : HasDerivAt (fun z : ℝ => (-t) ^ n * exp (-z * t))
        ((-t) ^ n * (exp (-y * t) * (-1 * t))) y :=
      ((hasDerivAt_id y).neg.mul_const t).exp.const_mul ((-t) ^ n)
    have heq : (-t) ^ n * (exp (-y * t) * (-1 * t)) = (-t) ^ (n + 1) * exp (-y * t) := by
      rw [pow_succ]
      ring
    exact heq ▸ h

private theorem hasDerivAt_q (x : ℝ) : HasDerivAt q (moment 1 x) x := by
  have heq : moment 0 = q := by
    funext y
    simp [moment, q]
  rw [← heq]
  exact hasDerivAt_moment 0 x

theorem q_pos (x : ℝ) : 0 < q x := by
  calc
    0 < exp (-|x|) := exp_pos _
    _ = ∫ _t in (0 : ℝ)..1, exp (-|x|) := by simp
    _ ≤ q x := by
      apply integral_mono_on zero_le_one (hi continuous_const) (hi (by fun_prop))
      intro t ht
      apply exp_le_exp.mpr
      calc
        -|x| = -|x| * 1 := by rw [mul_one]
        _ ≤ -|x| * t := mul_le_mul_of_nonpos_left ht.2 (neg_nonpos.mpr (abs_nonneg _))
        _ ≤ -x * t := mul_le_mul_of_nonneg_right (neg_le_neg (le_abs_self x)) ht.1

theorem q_eq (x : ℝ) (hx : 0 < x) : q x = (1 - exp (-x)) / x := by
  have hd (t : ℝ) :
      HasDerivAt (fun t : ℝ => exp (-x * t) / -x) (exp (-x * t)) t := by
    have h : HasDerivAt (fun s : ℝ => exp (-x * s) / -x)
        (exp (-x * t) * (-x * 1) / -x) t :=
      ((hasDerivAt_id t).const_mul (-x)).exp.div_const (-x)
    rwa [mul_one, mul_div_cancel_right₀ _ (neg_ne_zero.mpr hx.ne')] at h
  rw [q, integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hi (by fun_prop))]
  simp only [mul_one, mul_zero, exp_zero]
  ring

theorem q_lower (x : ℝ) (_hx : 0 ≤ x) : 1 - x / 2 ≤ q x := by
  calc
    1 - x / 2 = ∫ t in (0 : ℝ)..1, 1 - x * t := by
      rw [integral_sub (hi continuous_const) (hi (by fun_prop)),
        intervalIntegral.integral_const_mul, integral_id]
      norm_num
      ring
    _ ≤ q x := by
      apply integral_mono_on zero_le_one (hi (by fun_prop)) (hi (by fun_prop))
      intro t _
      linarith [add_one_le_exp (-x * t)]

theorem hasDerivAt_g (x : ℝ) : HasDerivAt g (g1 x) x := by
  change HasDerivAt (fun y => log (q y)) (g1 x) x
  simpa [g1, div_eq_mul_inv, mul_comm] using
    (hasDerivAt_q x).log (q_pos x).ne'

theorem hasDerivAt_g1 (x : ℝ) : HasDerivAt g1 (g2 x) x := by
  have hq : q x ≠ 0 := (q_pos x).ne'
  have h : HasDerivAt g1
      ((moment 2 x * q x - moment 1 x * moment 1 x) / (q x) ^ 2) x :=
    (hasDerivAt_moment 1 x).div (hasDerivAt_q x) hq
  have hc : moment 2 x * q x / (q x) ^ 2 = moment 2 x / q x := by
    rw [pow_two, ← div_div, mul_div_cancel_right₀ _ hq]
  have heq : (moment 2 x * q x - moment 1 x * moment 1 x) / (q x) ^ 2 = g2 x := by
    rw [g2, g1, sub_div, hc, ← pow_two (moment 1 x), ← div_pow]
  exact heq ▸ h

private theorem centered_integral :
    (∫ t in (0 : ℝ)..1, (t - 1 / 2) ^ 2) = 1 / 12 := by
  calc
    _ = ∫ t in (0 : ℝ)..1, t ^ 2 - t + 1 / 4 := by
      apply integral_congr
      intro t _
      ring
    _ = _ := by
      rw [integral_add (hi (by fun_prop)) (hi continuous_const),
        integral_sub (hi (by fun_prop)) (hi (f := fun t : ℝ => t) (by fun_prop)),
        integral_pow, integral_id]
      norm_num

private theorem g2_le_div_q (x : ℝ) (hx : 0 ≤ x) : g2 x ≤ (1 / 12) / q x := by
  let c : ℝ := ∫ t in (0 : ℝ)..1, (t - 1 / 2) ^ 2 * exp (-x * t)
  have hc : c ≤ 1 / 12 := by
    rw [← centered_integral]
    apply integral_mono_on zero_le_one (hi (by fun_prop)) (hi (by fun_prop))
    intro t ht
    have he : exp (-x * t) ≤ 1 := by
      rw [← exp_zero]
      exact exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) ht.1)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (sq_nonneg (t - 1 / 2))
  have heq : c = moment 2 x + moment 1 x + q x / 4 := by
    calc
      c = ∫ t in (0 : ℝ)..1,
          ((-t) ^ 2 * exp (-x * t) + (-t) ^ 1 * exp (-x * t)) + exp (-x * t) / 4 := by
        apply integral_congr
        intro t _
        ring
      _ = _ := by
        rw [integral_add (hi (by fun_prop)) (hi (by fun_prop)),
          integral_add (hi (by fun_prop)) (hi (by fun_prop)), intervalIntegral.integral_div]
        rfl
  have hquot : c / q x = moment 2 x / q x + g1 x + 1 / 4 := by
    rw [heq, g1]
    field_simp [(q_pos x).ne']
  calc
    g2 x ≤ c / q x := by
      rw [hquot, g2]
      nlinarith [sq_nonneg (g1 x + 1 / 2)]
    _ ≤ (1 / 12) / q x := div_le_div_of_nonneg_right hc (q_pos x).le

theorem g2_le_eighth (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 2 / 3) : g2 x ≤ 1 / 8 := by
  refine (g2_le_div_q x hx).trans ((div_le_iff₀ (q_pos x)).2 ?_)
  linarith [q_lower x hx]

theorem g1_zero : g1 0 = -1 / 2 := by
  have hq : q 0 = 1 := by simp [q]
  have hm : moment 1 0 = -1 / 2 := by
    simp only [moment, pow_one, neg_zero, zero_mul, exp_zero, mul_one]
    rw [intervalIntegral.integral_neg (f := fun t : ℝ => t), integral_id]
    norm_num
  rw [g1, hm, hq, div_one]

theorem g1_le (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 2 / 3) : g1 x ≤ -5 / 12 := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, g1_zero]
    norm_num
  · obtain ⟨c, hc, ht⟩ := exists_hasDerivAt_eq_slope g1 g2 h
      (fun y _ => (hasDerivAt_g1 y).continuousAt.continuousWithinAt) (fun y _ => hasDerivAt_g1 y)
    have hle := g2_le_eighth c hc.1.le (hc.2.le.trans hx')
    rw [ht, sub_zero, g1_zero] at hle
    have hm := (div_le_iff₀ h).1 hle
    linarith

theorem min_le_of_concave_log {f : ℝ → ℝ} {s : Set ℝ}
    (h : ConcaveOn ℝ s (fun t => log (f t))) (hf : ∀ t ∈ s, 0 < f t)
    {x y z : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ Icc x y) :
    min (f x) (f y) ≤ f z := by
  have hz' : z ∈ s := h.1.segment_subset hx hy (by rwa [segment_eq_Icc (hz.1.trans hz.2)])
  have hmin := exp_monotone (h.min_le_of_mem_Icc hx hy hz)
  simpa only [exp_monotone.map_min, exp_log (hf x hx), exp_log (hf y hy), exp_log (hf z hz')]
    using hmin

end

end OMA.TetLog260379

namespace OMA.TetIter260379

open Filter Set
open scoped Topology

theorem tendsto_v_one : Tendsto (fun n => v n 1) atTop (𝓝 0) := by
  have hanti : Antitone (fun n => v n 1) := antitone_nat_of_succ_le fun n => by
    simpa only [one_mul] using v_step_le_mul n (l := 1) zero_le_one
  have hbdd : BddBelow (range fun n => v n 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (v_pos n zero_lt_one).le
  let a : ℝ := ⨅ n, v n 1
  have hlim : Tendsto (fun n => v n 1) atTop (𝓝 a) := tendsto_atTop_ciInf hanti hbdd
  have hstep : Tendsto (fun n => v (n + 1) 1) atTop (𝓝 a) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hcont : Continuous (fun x : ℝ => 1 - Real.exp (-x)) := by fun_prop
  have hnext : Tendsto (fun n => v (n + 1) 1) atTop (𝓝 (1 - Real.exp (-a))) := by
    have h := (hcont.continuousAt (x := a)).tendsto.comp hlim
    change Tendsto (fun n => 1 - Real.exp (-v n 1)) atTop (𝓝 (1 - Real.exp (-a))) at h
    simpa only [v, one_mul] using h
  have ha : a = 0 := by
    by_contra hn
    have hfix := tendsto_nhds_unique hstep hnext
    linarith only [hfix, Real.one_sub_lt_exp_neg hn]
  simpa only [ha] using hlim

private theorem v_le_geometric (n : ℕ) {l : ℝ} (hl : 0 ≤ l) :
    v n l ≤ l ^ (n + 1) := by
  induction n with
  | zero => simp [v]
  | succ n ih =>
    calc
      v (n + 1) l ≤ l * v n l := v_step_le_mul n hl
      _ ≤ l * l ^ (n + 1) := mul_le_mul_of_nonneg_left ih hl
      _ = l ^ (n + 1 + 1) := by rw [pow_succ l (n + 1), mul_comm]

private theorem v_step_ge_exp (n : ℕ) {l : ℝ} (hl : 0 ≤ l) :
    l * (v n l * Real.exp (-v n l)) ≤ v (n + 1) l := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (v n l))
    (Real.exp_pos (-v n l)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  change _ ≤ l * (1 - Real.exp (-v n l))
  exact mul_le_mul_of_nonneg_left (by linarith only [h]) hl

theorem v_ge_geometric_exp (n : ℕ) {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    l ^ (n + 1) * Real.exp (-(l / (1 - l))) ≤ v n l := by
  have hgeom : (∑ i ∈ Finset.range n, l ^ i) ≤ (1 - l)⁻¹ := by
    rw [← one_div, le_div_iff₀ (sub_pos.mpr hl1), geom_sum_mul_neg]
    linarith [pow_nonneg hl.le n]
  have hsum : (∑ i ∈ Finset.range n, v i l) ≤ l / (1 - l) := by
    calc
      (∑ i ∈ Finset.range n, v i l) ≤ ∑ i ∈ Finset.range n, l ^ (i + 1) :=
        Finset.sum_le_sum fun i _ => v_le_geometric i hl.le
      _ = (∑ i ∈ Finset.range n, l ^ i) * l := by simp only [Finset.sum_mul, pow_succ]
      _ ≤ (1 - l)⁻¹ * l := mul_le_mul_of_nonneg_right hgeom hl.le
      _ = l / (1 - l) := by rw [div_eq_mul_inv, mul_comm]
  have hprod (m : ℕ) :
      l ^ (m + 1) * Real.exp (-(∑ i ∈ Finset.range m, v i l)) ≤ v m l := by
    induction m with
    | zero => simp [v]
    | succ m ih =>
      rw [Finset.sum_range_succ, neg_add, Real.exp_add, pow_succ]
      calc
        l ^ (m + 1) * l *
              (Real.exp (-(∑ i ∈ Finset.range m, v i l)) * Real.exp (-v m l)) =
            l * ((l ^ (m + 1) * Real.exp (-(∑ i ∈ Finset.range m, v i l))) *
              Real.exp (-v m l)) := by ring
        _ ≤ l * (v m l * Real.exp (-v m l)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le) hl.le
        _ ≤ v (m + 1) l := v_step_ge_exp m hl.le
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hsum))
    (pow_nonneg hl.le _)).trans (hprod n)

end OMA.TetIter260379

namespace OMA.TetConcavity260379

open Set OMA.TetIter260379 OMA.TetLog260379

private theorem concaveOn_Ioo_of_hasDerivAt2 {a b : ℝ} {f f₁ f₂ : ℝ → ℝ}
    (h₁ : ∀ x ∈ Ioo a b, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Ioo a b, HasDerivAt f₁ (f₂ x) x)
    (h₂₀ : ∀ x ∈ Ioo a b, f₂ x ≤ 0) : ConcaveOn ℝ (Ioo a b) f := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := f₁) (f'' := f₂) (convex_Ioo a b) ?_ ?_ ?_ ?_
  · exact fun x hx => (h₁ x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (h₁ x (interior_subset hx)).hasDerivWithinAt
  · exact fun x hx => (h₂ x (interior_subset hx)).hasDerivWithinAt
  · exact fun x hx => h₂₀ x (interior_subset hx)

theorem log_exp_sub_one_concave :
    ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun x => Real.log (Real.exp x - 1)) := by
  have hpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < Real.exp x - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr hx.1)
  refine concaveOn_Ioo_of_hasDerivAt2
    (f₁ := fun x => Real.exp x / (Real.exp x - 1))
    (f₂ := fun x => -Real.exp x / (Real.exp x - 1) ^ 2) ?_ ?_ ?_
  · intro x hx
    exact ((Real.hasDerivAt_exp x).sub_const 1).log (hpos x hx).ne'
  · intro x hx
    have h := (Real.hasDerivAt_exp x).fun_div
      ((Real.hasDerivAt_exp x).sub_const 1) (hpos x hx).ne'
    have hnum : Real.exp x * (Real.exp x - 1) - Real.exp x * Real.exp x = -Real.exp x := by ring
    rwa [hnum] at h
  · intro x _
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos x).le) (sq_nonneg _)

theorem comp_iter_concave (n : ℕ) :
    ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun x => g (v (n + 1) x)) := by
  refine concaveOn_Ioo_of_hasDerivAt2
    (f₁ := fun x => g1 (v (n + 1) x) * d (n + 1) x)
    (f₂ := fun x => g2 (v (n + 1) x) * (d (n + 1) x) ^ 2 +
      g1 (v (n + 1) x) * e (n + 1) x) ?_ ?_ ?_
  · intro x _
    exact (hasDerivAt_g (v (n + 1) x)).comp x (hasDerivAt_v (n + 1) x)
  · intro x _
    have hh : HasDerivAt (fun y : ℝ => g1 (v (n + 1) y))
        (g2 (v (n + 1) x) * d (n + 1) x) x :=
      (hasDerivAt_g1 (v (n + 1) x)).comp x (hasDerivAt_v (n + 1) x)
    have h : HasDerivAt (fun y : ℝ => g1 (v (n + 1) y) * d (n + 1) y)
        (g2 (v (n + 1) x) * d (n + 1) x * d (n + 1) x +
          g1 (v (n + 1) x) * e (n + 1) x) x :=
      hh.fun_mul (hasDerivAt_d (n + 1) x)
    have hc : g2 (v (n + 1) x) * d (n + 1) x * d (n + 1) x +
        g1 (v (n + 1) x) * e (n + 1) x =
        g2 (v (n + 1) x) * (d (n + 1) x) ^ 2 + g1 (v (n + 1) x) * e (n + 1) x := by
      ring
    rwa [hc] at h
  · intro x hx
    obtain ⟨hv, hvbound, _, _, he⟩ := iter_bounds n hx.1 hx.2.le
    have he₀ : 0 ≤ e (n + 1) x := le_trans (by positivity) he
    have hd₂ : 0 ≤ (d (n + 1) x) ^ 2 := sq_nonneg _
    have hnonpos : (-5 / 12 : ℝ) ≤ 0 := by norm_num
    have hprod := mul_le_mul_of_nonpos_left he hnonpos
    calc
      g2 (v (n + 1) x) * (d (n + 1) x) ^ 2 + g1 (v (n + 1) x) * e (n + 1) x
          ≤ (1 / 8 : ℝ) * (d (n + 1) x) ^ 2 + (-5 / 12 : ℝ) * e (n + 1) x :=
        add_le_add (mul_le_mul_of_nonneg_right (g2_le_eighth _ hv.le hvbound) hd₂)
          (mul_le_mul_of_nonneg_right (g1_le _ hv.le hvbound) he₀)
      _ ≤ (1 / 8 : ℝ) * (d (n + 1) x) ^ 2 + (-5 / 12 : ℝ) * ((d (n + 1) x) ^ 2 / 3) :=
        add_le_add le_rfl hprod
      _ ≤ 0 := by linarith only [hd₂]

end OMA.TetConcavity260379

namespace OMA.Peak260379

open Filter Set
open scoped Topology

theorem peak_of_approx {c : ℝ → ℝ} {f : ℕ → ℝ → ℝ}
    (hcont : ∀ n, ContinuousOn (f n) (Ioo 0 1))
    (hle : ∀ n x, x ∈ Ioo 0 1 → c x ≤ f n x)
    (hconv : ∀ x ∈ Ioo 0 1, Tendsto (fun n => f n x) atTop (𝓝 (c x)))
    (hqc : ∀ n x y z, x ∈ Ioo 0 1 → y ∈ Ioo 0 1 → z ∈ Icc x y →
      min (f n x) (f n y) ≤ f n z)
    (hzero : ContinuousAt (f 0) 0) (hzval : f 0 0 = 0)
    (hone : ∀ n, ContinuousAt (f n) 1)
    (hoval : Tendsto (fun n => f n 1) atTop (𝓝 0))
    (hpos : ∃ x ∈ Ioo 0 1, 0 < c x) :
    ∃ μ ∈ Ioo 0 1, MonotoneOn c (Ioc 0 μ) ∧ AntitoneOn c (Ico μ 1) := by
  obtain ⟨x₀, hx₀, hpos⟩ := hpos
  have hbounded (x : ℝ) (hx : x ∈ Ioo 0 1) : BddBelow (range (fun n => f n x)) := by
    refine ⟨c x, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hle n x hx
  have hinf (x : ℝ) (hx : x ∈ Ioo 0 1) : (⨅ n, f n x) = c x := by
    apply le_antisymm
    · exact ge_of_tendsto' (hconv x hx) fun n => ciInf_le (hbounded x hx) n
    · exact le_ciInf fun n => hle n x hx
  have husc : UpperSemicontinuousOn c (Ioo 0 1) := by
    have h := upperSemicontinuousOn_ciInf hbounded fun n => (hcont n).upperSemicontinuousOn
    intro x hx
    exact UpperSemicontinuousWithinAt.congr_of_eventuallyEq (h x hx) hx
      (eventually_nhdsWithin_of_forall hinf)
  have hquasi {x y z : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1)
      (hz : z ∈ Icc x y) : min (c x) (c y) ≤ c z := by
    rw [← hinf z ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩]
    exact le_ciInf fun n => (min_le_min (hle n x hx) (hle n y hy)).trans (hqc n x y z hx hy hz)
  have hleft : ∀ᶠ x in 𝓝 (0 : ℝ), f 0 x < c x₀ := by
    have hlt : f 0 0 < c x₀ := by rwa [hzval]
    exact hzero.eventually (gt_mem_nhds hlt)
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.eventually_nhds_iff.mp hleft
  have hev : ∀ᶠ n in atTop, f n 1 < c x₀ := hoval.eventually (gt_mem_nhds hpos)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hright : ∀ᶠ x in 𝓝 (1 : ℝ), f N x < c x₀ :=
    (hone N).eventually (gt_mem_nhds (hN N le_rfl))
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.eventually_nhds_iff.mp hright
  let a : ℝ := min (x₀ / 2) (δ₀ / 2)
  let b : ℝ := max ((x₀ + 1) / 2) (1 - δ₁ / 2)
  have ha₀ : 0 < a := lt_min (by linarith [hx₀.1]) (by linarith)
  have hax : a ≤ x₀ := (min_le_left _ _).trans (by linarith [hx₀.1])
  have hxb : x₀ ≤ b := (show x₀ ≤ (x₀ + 1) / 2 by linarith [hx₀.2]).trans (le_max_left _ _)
  have hb₁ : b < 1 := max_lt (by linarith [hx₀.2]) (by linarith)
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 :=
    fun _ hx => ⟨ha₀.trans_le hx.1, hx.2.trans_lt hb₁⟩
  obtain ⟨μ, hμ, hmax⟩ :=
    UpperSemicontinuousOn.exists_isMaxOn (s := Icc a b) ⟨x₀, hax, hxb⟩
      isCompact_Icc (husc.mono hsub)
  have hμ' : μ ∈ Ioo 0 1 := hsub hμ
  have hdom (x : ℝ) (hx : x ∈ Ioo 0 1) : c x ≤ c μ := by
    by_cases ht : x ∈ Icc a b
    · exact hmax ht
    have hout : x < a ∨ b < x := by
      rcases lt_or_ge x a with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge fun h' => ht ⟨h, h'⟩)
    apply le_trans _ (hmax ⟨hax, hxb⟩)
    rcases hout with hlt | hgt
    · have hd : dist x 0 < δ₀ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
        have had : a ≤ δ₀ / 2 := min_le_right _ _
        linarith
      exact (hle 0 x hx).trans (hball₀ hd).le
    · have hd : dist x 1 < δ₁ := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hx.2)]
        have hbd : 1 - δ₁ / 2 ≤ b := le_max_right _ _
        linarith
      exact (hle N x hx).trans (hball₁ hd).le
  refine ⟨μ, hμ', ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : x ∈ Ioo 0 1 := ⟨hx.1, hx.2.trans_lt hμ'.2⟩
    simpa only [min_eq_left (hdom x hx')] using hquasi hx' hμ' ⟨hxy, hy.2⟩
  · intro x hx y hy hxy
    have hy' : y ∈ Ioo 0 1 := ⟨hμ'.1.trans_le hy.1, hy.2⟩
    simpa only [min_eq_right (hdom y hy')] using hquasi hμ' hy' ⟨hx.1, hxy⟩

end OMA.Peak260379

namespace OMA.TetCore260379

open Filter Set Topology
open OMA.S_mo_260379 OMA.TetIter260379

noncomputable def f (n : ℕ) (l : ℝ) : ℝ :=
  (Real.exp l - tet (base l) n) / l ^ n

theorem f_zero (l : ℝ) : f 0 l = Real.exp l - 1 := by
  simp [f, tet]

private theorem tet_succ (l : ℝ) (n : ℕ) :
    tet (base l) (n + 1) = Real.exp ((l * Real.exp (-l)) * tet (base l) n) := by
  rw [tet, base, ← Real.exp_mul]

-- The recurrence v measures the error after removing the factor exp l / l.
private theorem v_tet (n : ℕ) (l : ℝ) :
    v (n + 1) l = l * (1 - Real.exp (-l) * tet (base l) n) := by
  induction n with
  | zero =>
      simp [v, tet]
  | succ n ih =>
      rw [v, ih, tet_succ]
      congr 1
      rw [← Real.exp_add]
      congr 2
      ring

theorem f_eq (n : ℕ) {l : ℝ} (hl : 0 < l) :
    f n l = Real.exp l * v (n + 1) l / l ^ (n + 1) := by
  have hprod : Real.exp l * Real.exp (-l) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hnum : Real.exp l * (1 - Real.exp (-l) * tet (base l) n) =
      Real.exp l - tet (base l) n := by
    rw [mul_sub, ← mul_assoc, hprod, mul_one, one_mul]
  rw [f, v_tet, ← mul_left_comm, hnum, pow_succ]
  field_simp [hl.ne']

theorem f_pos (n : ℕ) {l : ℝ} (hl : 0 < l) : 0 < f n l := by
  rw [f_eq n hl]
  exact div_pos (mul_pos (Real.exp_pos _) (v_pos _ hl)) (pow_pos hl _)

theorem f_succ (n : ℕ) {l : ℝ} (hl : 0 < l) :
    f (n + 1) l = f n l * ((1 - Real.exp (-v (n + 1) l)) / v (n + 1) l) := by
  have hv := (v_pos (n + 1) hl).ne'
  rw [f_eq (n + 1) hl, f_eq n hl, v.eq_2, pow_succ l (n + 1)]
  field_simp [hl.ne', hv]

theorem f_antitone {l : ℝ} (hl : 0 < l) : Antitone (fun n => f n l) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [f_succ n hl]
  apply mul_le_of_le_one_right (f_pos n hl).le
  rw [div_le_one (v_pos _ hl)]
  linarith [Real.add_one_le_exp (-v (n + 1) l)]

private theorem f_bddBelow {l : ℝ} (hl : 0 < l) : BddBelow (range (fun n => f n l)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (f_pos n hl).le

theorem f_tendsto {l : ℝ} (hl : 0 < l) :
    Tendsto (fun n => f n l) atTop (𝓝 (c l)) := by
  have h := tendsto_atTop_ciInf (f_antitone hl) (f_bddBelow hl)
  have heq : c l = ⨅ n, f n l := h.limUnder_eq
  rw [heq]
  exact h

theorem c_le_f (n : ℕ) {l : ℝ} (hl : 0 < l) : c l ≤ f n l := by
  have h : ∀ᶠ m in atTop, f m l ≤ f n l :=
    (eventually_ge_atTop n).mono fun _ hm => f_antitone hl hm
  exact le_of_tendsto (f_tendsto hl) h

private theorem continuous_tet (n : ℕ) : Continuous (fun l : ℝ => tet (base l) n) := by
  induction n with
  | zero =>
      simpa only [tet] using (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))
  | succ n ih =>
      simp only [tet_succ]
      have hneg : Continuous (fun l : ℝ => -l) := continuous_id.neg
      exact Real.continuous_exp.comp
        ((continuous_id.mul (Real.continuous_exp.comp hneg)).mul ih)

theorem continuousAt_f (n : ℕ) {l : ℝ} (hl : l ≠ 0) : ContinuousAt (f n) l := by
  exact (Real.continuous_exp.sub (continuous_tet n)).continuousAt.div
    (continuous_id.pow n).continuousAt (pow_ne_zero n hl)

theorem continuous_f_zero : Continuous (f 0) := by
  rw [show f 0 = (fun l => Real.exp l - 1) from funext f_zero]
  exact Real.continuous_exp.sub continuous_const

end OMA.TetCore260379

namespace OMA.TetCore260379

open Filter Set Topology
open OMA.S_mo_260379 OMA.TetIter260379 OMA.TetLog260379 OMA.TetConcavity260379

-- Each recurrence step adds a concave logarithmic factor.
private theorem f_log_concave (n : ℕ) :
    ConcaveOn ℝ (Ioo 0 1) (fun l => Real.log (f n l)) := by
  induction n with
  | zero =>
      exact log_exp_sub_one_concave.congr fun l _ => by rw [f_zero]
  | succ n ih =>
      refine (ih.add (comp_iter_concave n)).congr fun l hl => ?_
      have hl0 : 0 < l := hl.1
      change Real.log (f n l) + g (v (n + 1) l) = Real.log (f (n + 1) l)
      rw [f_succ n hl0, ← q_eq _ (v_pos _ hl0),
        Real.log_mul (f_pos n hl0).ne' (q_pos _).ne']
      rfl

private theorem f_tendsto_one : Tendsto (fun n => f n 1) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ => v (n + 1) 1) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 tendsto_v_one
  have hscaled : Tendsto (fun n : ℕ => Real.exp 1 * v (n + 1) 1) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hshift
  have hfun : (fun n => f n 1) = (fun n => Real.exp 1 * v (n + 1) 1) := by
    funext n
    rw [f_eq n zero_lt_one, one_pow, div_one]
  rw [hfun]
  exact hscaled

private theorem c_pos {l : ℝ} (hl : 0 < l) (hl1 : l < 1) : 0 < c l := by
  let b := Real.exp l * (l * Real.exp (-(l / (1 - l))))
  have hbound (n : ℕ) : b ≤ f n l := by
    rw [f_eq n hl, le_div_iff₀ (pow_pos hl _)]
    calc
      b * l ^ (n + 1) =
          Real.exp l * (l ^ (n + 1 + 1) * Real.exp (-(l / (1 - l)))) := by
            dsimp [b]
            rw [pow_succ l (n + 1)]
            ring
      _ ≤ Real.exp l * v (n + 1) l :=
        mul_le_mul_of_nonneg_left (v_ge_geometric_exp (n + 1) hl hl1) (Real.exp_pos _).le
  exact (mul_pos (Real.exp_pos _) (mul_pos hl (Real.exp_pos _))).trans_le
    (ge_of_tendsto' (f_tendsto hl) hbound)

theorem unimodal : ∃ μ ∈ Ioo (0 : ℝ) 1, MonotoneOn c (Ioc 0 μ) ∧ AntitoneOn c (Ico μ 1) := by
  refine OMA.Peak260379.peak_of_approx
    (fun n l hl => (continuousAt_f n (ne_of_gt hl.1)).continuousWithinAt)
    (fun n _ hl => c_le_f n hl.1) (fun _ hl => f_tendsto hl.1)
    (fun n _ _ _ hx hy hz =>
      min_le_of_concave_log (f_log_concave n) (fun _ h => f_pos n h.1) hx hy hz)
    continuous_f_zero.continuousAt (by rw [f_zero, Real.exp_zero, sub_self])
    (fun n => continuousAt_f n one_ne_zero) f_tendsto_one ?_
  exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, c_pos (by norm_num) (by norm_num)⟩

end OMA.TetCore260379

theorem OMA.solution : type_of% @OMA.S_mo_260379.main :=
  OMA.TetCore260379.unimodal
