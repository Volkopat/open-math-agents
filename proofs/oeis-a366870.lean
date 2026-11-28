import OMAStatements.S_oeis_a366870
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
For a denominator d at least three, strong induction bounds the error
from the positive linear slope by 16√n. The recursive index is at most
n/d. The two-level continued-fraction map contracts the distance to
the same slope by at least a factor of two.
-/

open Filter Topology
open OMA.S_oeis_a366870

namespace NestedSlope

noncomputable def error (a : ℕ → ℕ) (c : ℝ) (n : ℕ) : ℝ := (a n : ℝ) - c*n

lemma square_root_error {a : ℕ → ℕ} {d : ℕ} {c : ℝ}
    (hd : 3 ≤ d) (hc : 0 < c) (hc1 : c < 1) (heq : c^2 + (d:ℝ)*c = d)
    (ha0 : a 0 = 0) (rec : ∀ n, a (n+1) = n+1 - a (a n / d)) (n : ℕ) :
    |error a c n| ≤ 16 * Real.sqrt n := by
  have hab : ∀ k, a k ≤ k := by
    intro k
    cases k with
    | zero => simp [ha0]
    | succ k => rw [rec]; exact Nat.sub_le _ _
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hflo : 0 ≤ c/(d:ℝ) := by positivity
  have hfhi : c/(d:ℝ) ≤ 1/3 := (div_le_iff₀ hdpos).2 (by linarith)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [error, ha0]
    | succ n =>
      let j := a n / d
      let r := a n % d
      have hj : j ≤ n := (Nat.div_le_self _ _).trans (hab n)
      have hj3 : 3*j ≤ n := calc
        _ ≤ d*j := Nat.mul_le_mul_right j hd
        _ ≤ a n := by simpa [j, Nat.mul_comm] using Nat.div_mul_le_self (a n) d
        _ ≤ _ := hab n
      have hjR : 3*(j:ℝ) ≤ n := by exact_mod_cast hj3
      have hr : (r:ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt (a n) (by omega : 0 < d)).le
      have hparts : (r:ℝ) + (d:ℝ)*j = (a n : ℝ) := by exact_mod_cast Nat.mod_add_div (a n) d
      have hrec : (a (n+1):ℝ) = (n:ℝ)+1 - (a j:ℝ) := by
        rw [rec, Nat.cast_sub ((hab j).trans (hj.trans (Nat.le_succ n)))]
        push_cast
        rfl
      have herr : error a c (n+1) =
          -error a c j - c/(d:ℝ)*error a c n + (1-c + c/(d:ℝ)*r) := by
        unfold error
        rw [hrec]
        push_cast
        field_simp [hdpos.ne']
        nlinarith only [congrArg (fun z : ℝ => (n:ℝ)*z) heq,
          congrArg (fun z : ℝ => c*z) hparts]
      have hoff : 0 ≤ 1-c + c/(d:ℝ)*r := by positivity
      have hoff' : 1-c + c/(d:ℝ)*r ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left hr hflo
        rw [div_mul_cancel₀ c hdpos.ne'] at h
        linarith
      have hroot : 5 * Real.sqrt j ≤ 3 * Real.sqrt ((n:ℝ)+1) := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).1
        nlinarith only [hjR, Real.sq_sqrt (Nat.cast_nonneg j),
          Real.sq_sqrt (show 0 ≤ (n:ℝ)+1 by positivity), Nat.cast_nonneg (α := ℝ) n]
      have hnroot : Real.sqrt (n:ℝ) ≤ Real.sqrt ((n:ℝ)+1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hone : 1 ≤ Real.sqrt ((n:ℝ)+1) :=
        Real.le_sqrt_of_sq_le (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
      have hprev : |c/(d:ℝ)*error a c n| ≤ (16 * Real.sqrt ((n:ℝ)+1))/3 := by
        rw [abs_mul, abs_of_nonneg hflo]
        calc
          _ ≤ (1/3:ℝ) * (16 * Real.sqrt n) :=
            mul_le_mul hfhi (ih n (Nat.lt_succ_self n)) (abs_nonneg _) (by norm_num)
          _ ≤ _ := by linarith
      have hjerr := abs_le.mp (ih j (Nat.lt_succ_of_le hj))
      have hnerr := abs_le.mp hprev
      rw [herr, abs_le]
      push_cast
      constructor <;> linarith

lemma ratio_limit {a : ℕ → ℕ} {c : ℝ}
    (bound : ∀ n, |error a c n| ≤ 16 * Real.sqrt n) :
    Tendsto (fun n : ℕ => (a n:ℝ)/(n:ℝ)) atTop (𝓝 c) := by
  have hh := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))).const_mul 16
  rw [mul_zero] at hh
  have hs : Tendsto (fun n : ℕ => 16 * Real.sqrt n/(n:ℝ)) atTop (𝓝 0) := by
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
    change 16 * (Real.sqrt n)⁻¹ = _
    field_simp [(Real.sqrt_pos.2 hn').ne']
    nlinarith [Real.sq_sqrt hn'.le]
  have he : Tendsto (fun n : ℕ => error a c n/(n:ℝ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hs.neg) hs
    · filter_upwards with n
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (abs_le.mp (bound n)).1 (Nat.cast_nonneg n)
    · filter_upwards with n
      exact div_le_div_of_nonneg_right (abs_le.mp (bound n)).2 (Nat.cast_nonneg n)
  have h := he.add_const c
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change ((a n:ℝ)-c*n)/(n:ℝ) + c = _
  field_simp
  <;> ring

lemma fraction_limit {f : ℕ → ℝ} {d c : ℝ} (hd : 3 ≤ d) (hc : 0 < c)
    (hc1 : c < 1) (heq : c^2+d*c=d) (base : f 0=0)
    (step : ∀ n, f (n+1) = 1/(1+1/(d+f n))) : Tendsto f atTop (𝓝 c) := by
  have hpos : ∀ n, 0 ≤ f n := by
    intro n
    induction n with
    | zero => simp [base]
    | succ n ih => rw [step]; have h : 0 < d+f n := by linarith
                   positivity
  have bound : ∀ n : ℕ, |f n-c| ≤ (1/2:ℝ)^n := by
    intro n
    induction n with
    | zero => simpa [base, abs_of_pos hc] using hc1.le
    | succ n ih =>
      have hx := hpos n
      have hdx : 0 < d + f n := by linarith
      have hden : 0 < 1+d+f n := by linarith
      have hden' : 0 < 1+1/(d+f n) := by positivity
      have identity : f (n+1)-c = (1-c)*(f n-c)/(1+d+f n) := by
        rw [step]
        field_simp [hdx.ne', hden.ne', hden'.ne']
        linear_combination -(d+f n+1)*heq
      rw [identity, abs_div, abs_mul, abs_of_nonneg (sub_nonneg.mpr hc1.le),
        abs_of_pos hden, pow_succ]
      calc
        _ ≤ |f n-c|/2 := by
          apply (div_le_div_iff₀ hden (by norm_num)).2
          nlinarith [mul_nonneg hc.le (abs_nonneg (f n-c)),
            mul_nonneg (by linarith : 0 ≤ d + f n - 1) (abs_nonneg (f n-c))]
        _ ≤ _ := by linarith
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num))
  · exact Filter.Eventually.of_forall fun n => abs_nonneg _
  · exact Filter.Eventually.of_forall bound

end NestedSlope

open NestedSlope

theorem OMA.solution : type_of% @OMA.S_oeis_a366870.main := by
  have h0 : value 0 = 0 := by rw [value, bounded]; rfl
  have hstep : ∀ n, value (n+1) = n+1 - value (value n / 4) := by
    intro n
    unfold value
    rw [bounded]
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg 2
  have hc : 0 < slope := by unfold slope; nlinarith
  have hc1 : slope < 1 := by unfold slope; nlinarith
  have heq : slope^2 + 4*slope = 4 := by unfold slope; nlinarith
  constructor
  · exact fraction_limit (d := 4) (by norm_num) hc hc1 heq rfl (fun _ => rfl)
  · exact ratio_limit (square_root_error (d := 4) (by norm_num) hc hc1
      (by simpa using heq) h0 hstep)
