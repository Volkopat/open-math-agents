import OMAStatements.S_mo_93323

/-!
# Disproof of mo-93323: Off-line zero of zeta^(8)(s) - zeta^(8)(1 - s)

We disprove the conjecture that all nonreal zeros of zeta^(k)(s) +- zeta^(k)(1 - s)
in the open critical strip lie on the critical line Re(s) = 1/2, by exhibiting a
rigorously certified zero of f(s) = zeta^(8)(s) - zeta^(8)(1 - s) inside the closed
disk of radius 10^(-5) centered at s0 = 0.76267016 + 5.79824402 * I.

The proof combines:
1. A Banach fixed-point / Newton-Kantorovich zero existence theorem on closed balls.
2. Order-12 Euler-Maclaurin summation for riemannZeta (cutoff M = 18) with analytic
   continuation to {Re(s) > 0, s != 1} and explicit integral remainder bounds.
3. Fixed-point complex ball arithmetic (scale 2^64) and Taylor jet propagation
   verified purely in the Lean kernel by decide.
-/

namespace OMA.Mo93323

open Complex Metric MeasureTheory Set Filter Topology
open scoped Polynomial

/-! ### Bernoulli polynomials scaled by 1/k! -/

noncomputable def bernPoly (k : ℕ) (x : ℝ) : ℝ :=
  ((Polynomial.bernoulli k).map (algebraMap ℚ ℝ)).eval x / (k.factorial : ℝ)

lemma bernPoly_zero (x : ℝ) : bernPoly 0 x = 1 := by
  simp [bernPoly, Polynomial.bernoulli_zero]

lemma bernPoly_one (x : ℝ) : bernPoly 1 x = x - 1 / 2 := by
  simp [bernPoly, Polynomial.bernoulli_one, one_div]

lemma bernPoly_eval_zero (k : ℕ) : bernPoly k 0 = (_root_.bernoulli k : ℝ) / (k.factorial : ℝ) := by
  rw [bernPoly]
  have h0 : ((Polynomial.bernoulli k).map (algebraMap ℚ ℝ)).eval 0 =
      (algebraMap ℚ ℝ) ((Polynomial.bernoulli k).eval 0) := by
    simpa using Polynomial.eval_map_apply (algebraMap ℚ ℝ) (0 : ℚ) (p := Polynomial.bernoulli k)
  rw [h0, Polynomial.bernoulli_eval_zero]
  simp

lemma bernPoly_eval_one (k : ℕ) (hk : 2 ≤ k) : bernPoly k 1 = bernPoly k 0 := by
  rw [bernPoly, bernPoly_eval_zero]
  have h1 : ((Polynomial.bernoulli k).map (algebraMap ℚ ℝ)).eval 1 =
      (algebraMap ℚ ℝ) ((Polynomial.bernoulli k).eval 1) := by
    simpa using Polynomial.eval_map_apply (algebraMap ℚ ℝ) (1 : ℚ) (p := Polynomial.bernoulli k)
  rw [h1, Polynomial.bernoulli_eval_one, ← bernoulli_eq_bernoulli'_of_ne_one (by omega : k ≠ 1)]
  simp

lemma hasDerivAt_bernPoly (k : ℕ) (x : ℝ) :
    HasDerivAt (bernPoly (k + 1)) (bernPoly k x) x := by
  unfold bernPoly
  have hd : HasDerivAt (fun y : ℝ => ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℝ)).eval y)
      (((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℝ)).derivative.eval x) x :=
    Polynomial.hasDerivAt _ x
  have hder : ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℝ)).derivative =
      ((k + 1 : ℕ) : ℝ[X]) * ((Polynomial.bernoulli k).map (algebraMap ℚ ℝ)) := by
    rw [Polynomial.derivative_map, Polynomial.derivative_bernoulli_add_one]
    simp [Polynomial.map_mul, Polynomial.map_natCast]
  rw [hder, Polynomial.eval_mul, Polynomial.eval_natCast] at hd
  have hdiv := hd.div_const (((k + 1).factorial : ℕ) : ℝ)
  refine hdiv.congr_deriv ?_
  rw [Nat.factorial_succ]
  push_cast
  have hk1 : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hk1]

lemma continuous_bernPoly (k : ℕ) : Continuous (bernPoly k) := by
  unfold bernPoly
  exact (Polynomial.continuous _).div_const _

lemma exists_bound_bernPoly (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, |bernPoly k t| ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := bernPoly k) (continuous_bernPoly k).continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

lemma bernoulli_val_2 : _root_.bernoulli 2 = 1 / 6 := by rw [bernoulli_two]; norm_num
lemma bernoulli_val_3 : _root_.bernoulli 3 = 0 := bernoulli_eq_zero_of_odd ⟨1, rfl⟩ (by omega)
lemma bernoulli_val_5 : _root_.bernoulli 5 = 0 := bernoulli_eq_zero_of_odd ⟨2, rfl⟩ (by omega)
lemma bernoulli_val_7 : _root_.bernoulli 7 = 0 := bernoulli_eq_zero_of_odd ⟨3, rfl⟩ (by omega)
lemma bernoulli_val_9 : _root_.bernoulli 9 = 0 := bernoulli_eq_zero_of_odd ⟨4, rfl⟩ (by omega)
lemma bernoulli_val_11 : _root_.bernoulli 11 = 0 := bernoulli_eq_zero_of_odd ⟨5, rfl⟩ (by omega)

lemma bernoulli_recur (n : ℕ) (hn : 1 ≤ n) :
    _root_.bernoulli n = -(1 / (n + 1 : ℚ)) * ∑ k ∈ Finset.range n, ((n + 1).choose k : ℚ) * _root_.bernoulli k := by
  have h := _root_.sum_bernoulli (n + 1)
  rw [Finset.sum_range_succ, Nat.choose_succ_self_right] at h
  have hne : (n + 1 : ℚ) ≠ 0 := by positivity
  have h0 : (if n + 1 = 1 then (1 : ℚ) else 0) = 0 := if_neg (by omega)
  rw [h0] at h
  have hmul : (n + 1 : ℚ) * _root_.bernoulli n =
      -(∑ k ∈ Finset.range n, ((n + 1).choose k : ℚ) * _root_.bernoulli k) := by
    push_cast at h; linarith
  field_simp [hne]
  linarith

lemma bernoulli_val_4 : _root_.bernoulli 4 = -1 / 30 := by
  rw [bernoulli_recur 4 (by omega)]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    _root_.bernoulli_zero, _root_.bernoulli_one, bernoulli_val_2, bernoulli_val_3]
  norm_num [Nat.choose]

lemma bernoulli_val_6 : _root_.bernoulli 6 = 1 / 42 := by
  rw [bernoulli_recur 6 (by omega)]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    _root_.bernoulli_zero, _root_.bernoulli_one, bernoulli_val_2, bernoulli_val_3, bernoulli_val_4, bernoulli_val_5]
  norm_num [Nat.choose]

lemma bernoulli_val_8 : _root_.bernoulli 8 = -1 / 30 := by
  rw [bernoulli_recur 8 (by omega)]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    _root_.bernoulli_zero, _root_.bernoulli_one, bernoulli_val_2, bernoulli_val_3, bernoulli_val_4,
    bernoulli_val_5, bernoulli_val_6, bernoulli_val_7]
  norm_num [Nat.choose]

lemma bernoulli_val_10 : _root_.bernoulli 10 = 5 / 66 := by
  rw [bernoulli_recur 10 (by omega)]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    _root_.bernoulli_zero, _root_.bernoulli_one, bernoulli_val_2, bernoulli_val_3, bernoulli_val_4,
    bernoulli_val_5, bernoulli_val_6, bernoulli_val_7, bernoulli_val_8, bernoulli_val_9]
  norm_num [Nat.choose]

lemma bernoulli_val_12 : _root_.bernoulli 12 = -691 / 2730 := by
  rw [bernoulli_recur 12 (by omega)]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    _root_.bernoulli_zero, _root_.bernoulli_one, bernoulli_val_2, bernoulli_val_3, bernoulli_val_4,
    bernoulli_val_5, bernoulli_val_6, bernoulli_val_7, bernoulli_val_8, bernoulli_val_9,
    bernoulli_val_10, bernoulli_val_11]
  norm_num [Nat.choose]

lemma bernoulli_poly_12_eval (t : ℝ) :
    ((Polynomial.bernoulli 12).map (algebraMap ℚ ℝ)).eval t =
      -691 / 2730 + 5 * (t * (1 - t)) ^ 2 + 10 * (t * (1 - t)) ^ 3 +
      17 / 2 * (t * (1 - t)) ^ 4 + 4 * (t * (1 - t)) ^ 5 + (t * (1 - t)) ^ 6 := by
  rw [Polynomial.bernoulli_def]
  simp only [Polynomial.map_sum, Polynomial.eval_finsetSum, Polynomial.map_monomial,
    Polynomial.eval_monomial, eq_ratCast]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [Nat.choose, _root_.bernoulli_zero, _root_.bernoulli_one, bernoulli_val_2, bernoulli_val_3,
    bernoulli_val_4, bernoulli_val_5, bernoulli_val_6, bernoulli_val_7, bernoulli_val_8,
    bernoulli_val_9, bernoulli_val_10, bernoulli_val_11, bernoulli_val_12]
  ring

lemma abs_bernPoly_12_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |bernPoly 12 t| ≤ (693 / 2730 : ℝ) / (Nat.factorial 12 : ℝ) := by
  rw [bernPoly, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (Nat.factorial 12 : ℝ))]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [bernoulli_poly_12_eval]
  set u := t * (1 - t)
  have hu0 : 0 ≤ u := mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hu4 : u ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have hu2 : u ^ 2 ≤ (1 / 4) ^ 2 := by nlinarith
  have hu3 : u ^ 3 ≤ (1 / 4) ^ 3 := by nlinarith
  have hu4' : u ^ 4 ≤ (1 / 4) ^ 4 := by nlinarith
  have hu5 : u ^ 5 ≤ (1 / 4) ^ 5 := by nlinarith
  have hu6 : u ^ 6 ≤ (1 / 4) ^ 6 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Rising factorial and cpow derivatives -/

def rising (s : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => rising s k * (s + k)

lemma differentiable_rising (k : ℕ) : Differentiable ℂ (fun s => rising s k) := by
  induction k with
  | zero => exact differentiable_const 1
  | succ k ih => exact ih.mul (differentiable_id.add (differentiable_const _))

lemma ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = Complex.exp ((Real.log x : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le]

lemma cpow_real_hasDerivAt {x : ℝ} (hx : 0 < x) (w : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ w) (w * (x : ℂ) ^ (w - 1)) x := by
  have heq : (fun y : ℝ => (y : ℂ) ^ w) =ᶠ[𝓝 x] (fun y : ℝ => Complex.exp ((Real.log y : ℂ) * w)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using ofReal_cpow_eq_exp hy w
  rw [heq.hasDerivAt_iff]
  have hlog : HasDerivAt (fun y : ℝ => (Real.log y : ℂ) * w) ((x⁻¹ : ℂ) * w) x := by
    simpa using ((Real.hasDerivAt_log hx.ne').ofReal_comp).mul_const w
  have hexp : HasDerivAt (fun y : ℝ => Complex.exp ((Real.log y : ℂ) * w))
      (Complex.exp ((Real.log x : ℂ) * w) * ((x⁻¹ : ℂ) * w)) x :=
    (Complex.hasDerivAt_exp _).comp x hlog
  refine hexp.congr_deriv ?_
  rw [← ofReal_cpow_eq_exp hx w, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_one]
  ring

lemma cpow_neg_real_hasDerivAt {x : ℝ} (hx : 0 < x) (w : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-w)) (-w * (x : ℂ) ^ (-(w + 1))) x := by
  refine (cpow_real_hasDerivAt hx (-w)).congr_deriv ?_
  have h : -w - 1 = -(w + 1) := by ring
  rw [h]

lemma cpow_exp_hasDerivAt {x : ℝ} (hx : 0 < x) (a s : ℂ) :
    HasDerivAt (fun z : ℂ => (x : ℂ) ^ (-(z + a)))
      (-(Real.log x : ℂ) * (x : ℂ) ^ (-(s + a))) s := by
  have heq : (fun z : ℂ => (x : ℂ) ^ (-(z + a))) = fun z => Complex.exp ((Real.log x : ℂ) * (-(z + a))) := by
    ext z; exact ofReal_cpow_eq_exp hx _
  rw [heq]
  have hlin : HasDerivAt (fun z : ℂ => (Real.log x : ℂ) * (-(z + a))) (-(Real.log x : ℂ)) s := by
    have h1 : HasDerivAt (fun z : ℂ => -(z + a)) (-1) s := ((hasDerivAt_id s).add_const a).neg
    simpa using h1.const_mul (Real.log x : ℂ)
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp ((Real.log x : ℂ) * (-(z + a))))
      (Complex.exp ((Real.log x : ℂ) * (-(s + a))) * (-(Real.log x : ℂ))) s :=
    (Complex.hasDerivAt_exp _).comp s hlin
  refine hexp.congr_deriv ?_
  rw [← ofReal_cpow_eq_exp hx (-(s + a))]
  ring

lemma measurable_fract_real : Measurable (Int.fract : ℝ → ℝ) := by
  have hfl : Measurable (fun x : ℝ => (⌊x⌋ : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (Monotone.measurable fun _ _ h => Int.floor_mono h)
  exact measurable_id.sub hfl

lemma intervalIntegral_fract_eq (n : ℕ) (f : ℝ → ℂ) (w : ℂ) :
    ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f (Int.fract x) * (x : ℂ) ^ w =
    ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f (x - n) * (x : ℂ) ^ w := by
  apply intervalIntegral.integral_congr_ae
  have hmeas : ∀ᵐ x : ℝ ∂volume, x ≠ (n : ℝ) ∧ x ≠ ((n + 1 : ℕ) : ℝ) := by
    have h1 : ∀ᵐ x : ℝ ∂volume, x ≠ (n : ℝ) := by rw [ae_iff]; simp
    have h2 : ∀ᵐ x : ℝ ∂volume, x ≠ ((n + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
    exact h1.and h2
  filter_upwards [hmeas] with x ⟨_, hxn1⟩ hx
  rw [uIoc_of_le (by exact_mod_cast Nat.le_succ n)] at hx
  have hlt : x < (n : ℝ) + 1 := by
    have : x ≤ (n : ℝ) + 1 := by simpa using hx.2
    exact lt_of_le_of_ne this (by simpa using hxn1)
  have hfl : ⌊x⌋ = (n : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast hx.1.le, by exact_mod_cast hlt⟩
  simp [Int.fract, hfl]

lemma ibp_unit_step {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (s : ℂ) :
    ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ),
      (bernPoly k (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + (k : ℂ))) =
    (bernPoly (k + 1) 0 : ℂ) * (((n + 1 : ℕ) : ℂ) ^ (-(s + (k : ℂ))) - (n : ℂ) ^ (-(s + (k : ℂ)))) +
    (s + (k : ℂ)) * ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ),
      (bernPoly (k + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((k + 1 : ℕ) : ℂ))) := by
  rw [intervalIntegral_fract_eq n (fun t => (bernPoly k t : ℂ)) (-(s + (k : ℂ))),
      intervalIntegral_fract_eq n (fun t => (bernPoly (k + 1) t : ℂ)) (-(s + ((k + 1 : ℕ) : ℂ)))]
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have hpos : ∀ x ∈ uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ), 0 < x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [hx.1]
  let u : ℝ → ℂ := fun x => (bernPoly (k + 1) (x - n) : ℂ)
  let u' : ℝ → ℂ := fun x => (bernPoly k (x - n) : ℂ)
  let v : ℝ → ℂ := fun x => (x : ℂ) ^ (-(s + (k : ℂ)))
  let v' : ℝ → ℂ := fun x => -(s + (k : ℂ)) * (x : ℂ) ^ (-(s + ((k + 1 : ℕ) : ℂ)))
  have hu : ∀ x ∈ uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ), HasDerivAt u (u' x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => bernPoly (k + 1) (y - n)) (bernPoly k (x - n)) x := by
      change HasDerivAt (bernPoly (k + 1) ∘ fun y : ℝ => id y - (n : ℝ)) (bernPoly k (x - n)) x
      exact ((hasDerivAt_bernPoly k (x - n)).comp x ((hasDerivAt_id x).sub_const (n : ℝ))).congr_deriv (mul_one _)
    exact h1.ofReal_comp
  have hv : ∀ x ∈ uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    refine (cpow_neg_real_hasDerivAt (hpos x hx) (s + (k : ℂ))).congr_deriv ?_
    simp only [v']
    have he : -(s + (k : ℂ) + 1) = -(s + ((k + 1 : ℕ) : ℂ)) := by push_cast; ring
    rw [he]
  have hu'_int : IntervalIntegrable u' volume (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
    (Complex.continuous_ofReal.comp ((continuous_bernPoly k).comp (continuous_id.sub continuous_const))).intervalIntegrable _ _
  have hv'_int : IntervalIntegrable v' volume (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
    refine (ContinuousOn.mul continuousOn_const fun x hx => ?_).intervalIntegrable
    exact (cpow_real_hasDerivAt (hpos x hx) (-(s + ((k + 1 : ℕ) : ℂ)))).continuousAt.continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'_int hv'_int
  have hu_n1 : u ((n + 1 : ℕ) : ℝ) = (bernPoly (k + 1) 0 : ℂ) := by
    simp only [u]; push_cast; rw [add_sub_cancel_left, bernPoly_eval_one (k + 1) (by omega)]
  have hu_n : u (n : ℝ) = (bernPoly (k + 1) 0 : ℂ) := by
    simp only [u, sub_self]
  have hmul_int : ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), u x * v' x =
      -(s + (k : ℂ)) * ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), u x * (x : ℂ) ^ (-(s + ((k + 1 : ℕ) : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext x; simp only [v']; ring
  rw [hu_n1, hu_n, hmul_int] at hibp
  have hv_n1 : v ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℂ) ^ (-(s + (k : ℂ))) := by simp [v]
  have hv_n : v (n : ℝ) = (n : ℂ) ^ (-(s + (k : ℂ))) := by simp [v]
  rw [hv_n1, hv_n] at hibp
  simp only [u, u', v] at hibp
  linear_combination hibp

lemma ibp_base_step {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : s ≠ 1) :
    (((n + 1 : ℕ) : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s) =
    (1 / 2 : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s) + (1 / 2 : ℂ) * (n : ℂ) ^ (-s) +
    s * ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ),
      (bernPoly 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((1 : ℕ) : ℂ))) := by
  rw [intervalIntegral_fract_eq n (fun t => (bernPoly 1 t : ℂ)) (-(s + ((1 : ℕ) : ℂ)))]
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have hpos : ∀ x ∈ uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ), 0 < x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [hx.1]
  have h1ms : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr hs.symm
  have hlhs : ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s) =
      (((n + 1 : ℕ) : ℂ) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s) := by
    have hd : ∀ x ∈ uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ),
        HasDerivAt (fun y : ℝ => (y : ℂ) ^ (1 - s) / (1 - s)) ((x : ℂ) ^ (-s)) x := by
      intro x hx
      refine ((cpow_real_hasDerivAt (hpos x hx) (1 - s)).div_const (1 - s)).congr_deriv ?_
      rw [show (1 - s) - 1 = -s by ring]
      field_simp [h1ms]
    have hint : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
      refine ContinuousOn.intervalIntegrable fun x hx => ?_
      exact (cpow_real_hasDerivAt (hpos x hx) (-s)).continuousAt.continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp [sub_div]
  rw [← hlhs]
  let u : ℝ → ℂ := fun x => (bernPoly 1 (x - n) : ℂ)
  let v : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  let v' : ℝ → ℂ := fun x => -s * (x : ℂ) ^ (-(s + ((1 : ℕ) : ℂ)))
  have hu : ∀ x ∈ uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ), HasDerivAt u 1 x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => bernPoly 1 (y - n)) 1 x := by
      change HasDerivAt (bernPoly 1 ∘ fun y : ℝ => id y - (n : ℝ)) 1 x
      exact ((hasDerivAt_bernPoly 0 (x - n)).comp x ((hasDerivAt_id x).sub_const (n : ℝ))).congr_deriv
        (by rw [bernPoly_zero, mul_one])
    simpa using h1.ofReal_comp
  have hv : ∀ x ∈ uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ), HasDerivAt v (v' x) x := fun x hx => by
    simpa only [v', Nat.cast_one] using cpow_neg_real_hasDerivAt (hpos x hx) s
  have hv'_int : IntervalIntegrable v' volume (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
    refine (ContinuousOn.mul continuousOn_const fun x hx => ?_).intervalIntegrable
    exact (cpow_real_hasDerivAt (hpos x hx) (-(s + ((1 : ℕ) : ℂ)))).continuousAt.continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv intervalIntegrable_const hv'_int
  have hu_n1 : u ((n + 1 : ℕ) : ℝ) = (1 / 2 : ℂ) := by
    simp only [u, bernPoly_one]; push_cast; ring
  have hu_n : u (n : ℝ) = -(1 / 2 : ℂ) := by
    simp only [u, bernPoly_one, sub_self]; push_cast; ring
  have hmul_int : ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), u x * v' x =
      -s * ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), u x * (x : ℂ) ^ (-(s + ((1 : ℕ) : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext x; simp only [v']; ring
  simp only [one_mul] at hibp
  rw [hu_n1, hu_n, hmul_int] at hibp
  have hv_n1 : v ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℂ) ^ (-s) := by simp [v]
  have hv_n : v (n : ℝ) = (n : ℂ) ^ (-s) := by simp [v]
  rw [hv_n1, hv_n] at hibp
  simp only [u, v] at hibp
  linear_combination hibp

/-! ### Improper integrals, Euler-Maclaurin for Re(s) > 1, and Analytic Continuation -/

noncomputable def I_em (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (18 : ℝ), (bernPoly k (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + k))

lemma integrableOn_I_em {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (bernPoly k (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + k))) (Ioi (18 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_bernPoly k
  have hlt : -(s.re + (k : ℝ)) < -1 := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
    linarith
  have hdom : IntegrableOn (fun x : ℝ => C * x ^ (-(s.re + (k : ℝ)))) (Ioi (18 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt hlt (by norm_num)).const_mul C
  refine hdom.mono' ?_ ?_
  · have hm1 : Measurable (fun x : ℝ => (bernPoly k (Int.fract x) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp ((continuous_bernPoly k).measurable.comp measurable_fract_real)
    have hm2 : Measurable (fun x : ℝ => (x : ℂ) ^ (-(s + k))) :=
      Complex.continuous_ofReal.measurable.pow_const _
    exact (hm1.mul hm2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := by linarith [mem_Ioi.mp hx]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have hre : (-(s + (k : ℂ))).re = -(s.re + k) := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩)
      (Real.rpow_nonneg hxpos.le _)

lemma sum_Ico_sub_succ (f : ℕ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ n ∈ Finset.Ico M N, (f (n + 1) - f n) = f N - f M := by
  induction N with
  | zero =>
    have hM : M = 0 := Nat.le_zero.mp hMN
    subst hM; simp
  | succ N ih =>
    rcases eq_or_lt_of_le hMN with rfl | hlt
    · simp
    · have hle : M ≤ N := by omega
      rw [Finset.sum_Ico_succ_top hle, ih hle]
      ring

lemma intervalIntegrable_Ico {f : ℝ → ℂ} {M N : ℕ} (hMN : M ≤ N)
    (hint : ∀ n ∈ Finset.Ico M N, IntervalIntegrable f volume (n : ℝ) ((n + 1 : ℕ) : ℝ)) :
    IntervalIntegrable f volume (M : ℝ) (N : ℝ) := by
  induction N with
  | zero =>
    have hM : M = 0 := Nat.le_zero.mp hMN
    subst hM; simp
  | succ N ih =>
    rcases eq_or_lt_of_le hMN with rfl | hlt
    · simp
    · have hle : M ≤ N := by omega
      exact (ih hle fun n hn => hint n (Finset.Ico_subset_Ico_right (Nat.le_succ N) hn)).trans
        (hint N (Finset.mem_Ico.mpr ⟨hle, Nat.lt_succ_self N⟩))

lemma intervalIntegral_sum_Ico {f : ℝ → ℂ} {M N : ℕ} (hMN : M ≤ N)
    (hint : ∀ n ∈ Finset.Ico M N, IntervalIntegrable f volume (n : ℝ) ((n + 1 : ℕ) : ℝ)) :
    ∑ n ∈ Finset.Ico M N, ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x =
      ∫ x in (M : ℝ)..(N : ℝ), f x := by
  induction N with
  | zero =>
    have hM : M = 0 := Nat.le_zero.mp hMN
    subst hM; simp
  | succ N ih =>
    rcases eq_or_lt_of_le hMN with rfl | hlt
    · simp
    · have hle : M ≤ N := by omega
      have hint' : ∀ n ∈ Finset.Ico M N, IntervalIntegrable f volume (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
        fun n hn => hint n (Finset.Ico_subset_Ico_right (Nat.le_succ N) hn)
      rw [Finset.sum_Ico_succ_top hle, ih hle hint']
      exact intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_Ico hle hint')
        (hint N (Finset.mem_Ico.mpr ⟨hle, Nat.lt_succ_self N⟩))

lemma tendsto_nat_cpow_zero {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (-w)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hev : (fun N : ℕ => ‖(N : ℂ) ^ (-w)‖) =ᶠ[atTop] (fun N : ℕ => (N : ℝ) ^ (-w.re)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    simpa [Complex.neg_re] using Complex.norm_cpow_eq_rpow_re_of_pos hpos (-w)
  rw [tendsto_congr' hev]
  exact (tendsto_rpow_neg_atTop hw).comp tendsto_natCast_atTop_atTop

lemma I_em_step {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    I_em k s = -(bernPoly (k + 1) 0 : ℂ) * (18 : ℂ) ^ (-(s + (k : ℂ))) + (s + (k : ℂ)) * I_em (k + 1) s := by
  have hint_k := integrableOn_I_em hk hs
  have hint_k1 := integrableOn_I_em (by omega : 1 ≤ k + 1) hs
  have hsum : ∀ N : ℕ, 18 ≤ N →
      ∫ x in (18 : ℝ)..(N : ℝ), (bernPoly k (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + (k : ℂ))) =
      (bernPoly (k + 1) 0 : ℂ) * ((N : ℂ) ^ (-(s + (k : ℂ))) - (18 : ℂ) ^ (-(s + (k : ℂ)))) +
      (s + (k : ℂ)) * ∫ x in (18 : ℝ)..(N : ℝ),
        (bernPoly (k + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((k + 1 : ℕ) : ℂ))) := by
    intro N hN
    have hstep := fun n (hn : n ∈ Finset.Ico 18 N) =>
      ibp_unit_step (n := n) (k := k) (by have := (Finset.mem_Ico.mp hn).1; omega) hk s
    have hsum_eq := Finset.sum_congr rfl hstep
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_eq
    have htel := sum_Ico_sub_succ (fun n : ℕ => (n : ℂ) ^ (-(s + (k : ℂ)))) hN
    rw [htel] at hsum_eq
    have hL : ∑ n ∈ Finset.Ico 18 N,
        ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), (bernPoly k (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + (k : ℂ))) =
        ∫ x in (18 : ℝ)..(N : ℝ), (bernPoly k (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + (k : ℂ))) := by
      refine intervalIntegral_sum_Ico hN fun n hn => ?_
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast Nat.le_succ n)]
      have h18n : (18 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      exact hint_k.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi h18n))
    have hR : ∑ n ∈ Finset.Ico 18 N,
        ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ),
          (bernPoly (k + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((k + 1 : ℕ) : ℂ))) =
        ∫ x in (18 : ℝ)..(N : ℝ),
          (bernPoly (k + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((k + 1 : ℕ) : ℂ))) := by
      refine intervalIntegral_sum_Ico hN fun n hn => ?_
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast Nat.le_succ n)]
      have h18n : (18 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      exact hint_k1.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi h18n))
    rw [hL, hR] at hsum_eq
    simpa only [Nat.cast_ofNat] using hsum_eq
  have hLimL : Tendsto (fun N : ℕ => ∫ x in (18 : ℝ)..(N : ℝ),
      (bernPoly k (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + (k : ℂ)))) atTop (𝓝 (I_em k s)) :=
    intervalIntegral_tendsto_integral_Ioi (18 : ℝ) hint_k tendsto_natCast_atTop_atTop
  have hLimR1 : Tendsto (fun N : ℕ => (N : ℂ) ^ (-(s + (k : ℂ)))) atTop (𝓝 0) :=
    tendsto_nat_cpow_zero (by simp; linarith)
  have hLimR2 : Tendsto (fun N : ℕ => ∫ x in (18 : ℝ)..(N : ℝ),
      (bernPoly (k + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((k + 1 : ℕ) : ℂ)))) atTop (𝓝 (I_em (k + 1) s)) :=
    intervalIntegral_tendsto_integral_Ioi (18 : ℝ) hint_k1 tendsto_natCast_atTop_atTop
  have hLimR : Tendsto (fun N : ℕ =>
      (bernPoly (k + 1) 0 : ℂ) * ((N : ℂ) ^ (-(s + (k : ℂ))) - (18 : ℂ) ^ (-(s + (k : ℂ)))) +
      (s + (k : ℂ)) * ∫ x in (18 : ℝ)..(N : ℝ),
        (bernPoly (k + 1) (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((k + 1 : ℕ) : ℂ)))) atTop
      (𝓝 ((bernPoly (k + 1) 0 : ℂ) * (0 - (18 : ℂ) ^ (-(s + (k : ℂ)))) + (s + (k : ℂ)) * I_em (k + 1) s)) :=
    ((hLimR1.sub tendsto_const_nhds).const_mul _).add (hLimR2.const_mul _)
  have hEq : I_em k s = (bernPoly (k + 1) 0 : ℂ) * (0 - (18 : ℂ) ^ (-(s + (k : ℂ)))) + (s + (k : ℂ)) * I_em (k + 1) s :=
    tendsto_nhds_unique hLimL (hLimR.congr' (by filter_upwards [eventually_ge_atTop 18] with N hN using (hsum N hN).symm))
  linear_combination hEq

lemma I_em_base_partial {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 18 ≤ N) :
    ((N : ℂ) ^ (1 - s) - (18 : ℂ) ^ (1 - s)) / (1 - s) =
    (∑ n ∈ Finset.Ico 18 N, (n : ℂ) ^ (-s)) + (1 / 2 : ℂ) * (N : ℂ) ^ (-s) -
    (1 / 2 : ℂ) * (18 : ℂ) ^ (-s) +
    s * ∫ x in (18 : ℝ)..(N : ℝ), (bernPoly 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((1 : ℕ) : ℂ))) := by
  have hint1 := integrableOn_I_em (k := 1) le_rfl hs0
  have hstep := fun n (hn : n ∈ Finset.Ico 18 N) =>
    ibp_base_step (n := n) (by have := (Finset.mem_Ico.mp hn).1; omega) hs1
  have heq := Finset.sum_congr rfl hstep
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at heq
  have htel1 := sum_Ico_sub_succ (fun n : ℕ => (n : ℂ) ^ (1 - s)) hN
  have htel2 := sum_Ico_sub_succ (fun n : ℕ => (n : ℂ) ^ (-s)) hN
  have hshift : ∑ n ∈ Finset.Ico 18 N, ((n + 1 : ℕ) : ℂ) ^ (-s) =
      (∑ n ∈ Finset.Ico 18 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (-s) - (18 : ℂ) ^ (-s) := by
    rw [Finset.sum_sub_distrib] at htel2
    have htel2' : ∑ n ∈ Finset.Ico 18 N, ((n + 1 : ℕ) : ℂ) ^ (-s) - ∑ n ∈ Finset.Ico 18 N, (n : ℂ) ^ (-s) =
        (N : ℂ) ^ (-s) - (18 : ℂ) ^ (-s) := by simpa only [Nat.cast_ofNat] using htel2
    linear_combination htel2'
  have hI : ∑ n ∈ Finset.Ico 18 N,
      ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ),
        (bernPoly 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((1 : ℕ) : ℂ))) =
      ∫ x in (18 : ℝ)..(N : ℝ),
        (bernPoly 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((1 : ℕ) : ℂ))) := by
    refine intervalIntegral_sum_Ico hN fun n hn => ?_
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast Nat.le_succ n)]
    have h18n : (18 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hn).1
    exact hint1.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi h18n))
  rw [htel1, hshift, hI] at heq
  simp only [Nat.cast_ofNat] at heq
  linear_combination heq

lemma I_em_base {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-s)) + (1 / 2 : ℂ) * (18 : ℂ) ^ (-s) +
      (18 : ℂ) ^ (1 - s) / (s - 1) - s * I_em 1 s := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hint1 := integrableOn_I_em (k := 1) le_rfl hs0
  have hzeta_sum : HasSum (fun n : ℕ => (n : ℂ) ^ (-s)) (riemannZeta s) := by
    have h1 := zeta_eq_tsum_one_div_nat_cpow hs
    have hsumm : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    rw [h1]
    have hfun : (fun n : ℕ => (n : ℂ) ^ (-s)) = (fun n : ℕ => 1 / (n : ℂ) ^ s) := by
      ext n; rw [one_div, Complex.cpow_neg]
    rw [hfun]; exact hsumm.hasSum
  have hLimZ : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s)) atTop (𝓝 (riemannZeta s)) :=
    hzeta_sum.tendsto_sum_nat
  have hrange_split : ∀ N : ℕ, 18 ≤ N →
      ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s) =
        (∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-s)) + ∑ n ∈ Finset.Ico 18 N, (n : ℂ) ^ (-s) := by
    intro N hN
    have h0 : ((0 : ℕ) : ℂ) ^ (-s) = 0 := by
      rw [Nat.cast_zero]
      exact Complex.zero_cpow (by intro h; rw [neg_eq_zero] at h; rw [h] at hs; simp at hs; norm_num at hs)
    have hsplit := (Finset.sum_range_add_sum_Ico (f := fun n : ℕ => (n : ℂ) ^ (-s)) hN).symm
    rw [hsplit]
    congr 1
    rw [show Finset.range 18 = insert 0 (Finset.Icc (1 : ℕ) 17) by decide,
      Finset.sum_insert (by decide), h0, zero_add]
  have hLimTail : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 18 N, (n : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s - ∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-s))) := by
    have h := hLimZ.sub (tendsto_const_nhds (x := ∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-s)))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 18] with N hN
    rw [hrange_split N hN]; ring
  have hLimN1 : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
    have h := tendsto_nat_cpow_zero (w := s - 1) (by simp; linarith)
    simpa [show -(s - 1) = 1 - s by ring] using h
  have hLimN0 : Tendsto (fun N : ℕ => (N : ℂ) ^ (-s)) atTop (𝓝 0) := tendsto_nat_cpow_zero hs0
  have hLimI : Tendsto (fun N : ℕ => ∫ x in (18 : ℝ)..(N : ℝ),
      (bernPoly 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((1 : ℕ) : ℂ)))) atTop (𝓝 (I_em 1 s)) :=
    intervalIntegral_tendsto_integral_Ioi (18 : ℝ) hint1 tendsto_natCast_atTop_atTop
  have hLimL : Tendsto (fun N : ℕ => ((N : ℂ) ^ (1 - s) - (18 : ℂ) ^ (1 - s)) / (1 - s)) atTop
      (𝓝 ((0 - (18 : ℂ) ^ (1 - s)) / (1 - s))) :=
    (hLimN1.sub tendsto_const_nhds).div_const _
  have hLimR : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Ico 18 N, (n : ℂ) ^ (-s)) + (1 / 2 : ℂ) * (N : ℂ) ^ (-s) -
      (1 / 2 : ℂ) * (18 : ℂ) ^ (-s) +
      s * ∫ x in (18 : ℝ)..(N : ℝ),
        (bernPoly 1 (Int.fract x) : ℂ) * (x : ℂ) ^ (-(s + ((1 : ℕ) : ℂ)))) atTop
      (𝓝 ((riemannZeta s - ∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-s)) + (1 / 2 : ℂ) * 0 -
        (1 / 2 : ℂ) * (18 : ℂ) ^ (-s) + s * I_em 1 s)) :=
    (((hLimTail.add (hLimN0.const_mul _)).sub tendsto_const_nhds).add (hLimI.const_mul _))
  have hEq := tendsto_nhds_unique hLimL
    (hLimR.congr' (by filter_upwards [eventually_ge_atTop 18] with N hN using (I_em_base_partial hs0 hs1 hN).symm))
  have hfrac : (0 - (18 : ℂ) ^ (1 - s)) / (1 - s) = (18 : ℂ) ^ (1 - s) / (s - 1) := by
    have h1ms : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr hs1.symm
    have hsm1 : (s - 1 : ℂ) ≠ 0 := sub_ne_zero.mpr hs1
    field_simp [h1ms, hsm1]; ring
  rw [hfrac] at hEq
  linear_combination -hEq

noncomputable def emMain (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-s)) + (1 / 2 : ℂ) * (18 : ℂ) ^ (-s) +
  (18 : ℂ) * (18 : ℂ) ^ (-s) * (s - 1)⁻¹ +
  (1 / 12 : ℂ) * (rising s 1 * (18 : ℂ) ^ (-s)) / (18 : ℂ) ^ 1 +
  (-(1 : ℂ) / 720) * (rising s 3 * (18 : ℂ) ^ (-s)) / (18 : ℂ) ^ 3 +
  (1 / 30240 : ℂ) * (rising s 5 * (18 : ℂ) ^ (-s)) / (18 : ℂ) ^ 5 +
  (-(1 : ℂ) / 1209600) * (rising s 7 * (18 : ℂ) ^ (-s)) / (18 : ℂ) ^ 7 +
  (1 / 47900160 : ℂ) * (rising s 9 * (18 : ℂ) ^ (-s)) / (18 : ℂ) ^ 9 +
  (-(691 : ℂ) / 1307674368000) * (rising s 11 * (18 : ℂ) ^ (-s)) / (18 : ℂ) ^ 11

lemma cpow_18_neg_add (s : ℂ) (j : ℕ) :
    (18 : ℂ) ^ (-(s + (j : ℂ))) = (18 : ℂ) ^ (-s) / (18 : ℂ) ^ j := by
  have h18 : (18 : ℂ) ≠ 0 := by norm_num
  rw [show -(s + (j : ℂ)) = -s - (j : ℂ) by ring, Complex.cpow_sub _ _ h18, Complex.cpow_natCast]

lemma cpow_18_one_sub (s : ℂ) : (18 : ℂ) ^ (1 - s) = (18 : ℂ) * (18 : ℂ) ^ (-s) := by
  have h18 : (18 : ℂ) ≠ 0 := by norm_num
  rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ h18, Complex.cpow_one]

lemma riemannZeta_eq_em_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = emMain s - rising s 12 * I_em 12 s := by
  have hs0 : 0 < s.re := by linarith
  have h0 := I_em_base hs
  have h1 := I_em_step (k := 1) (by omega) hs0
  have h2 := I_em_step (k := 2) (by omega) hs0
  have h3 := I_em_step (k := 3) (by omega) hs0
  have h4 := I_em_step (k := 4) (by omega) hs0
  have h5 := I_em_step (k := 5) (by omega) hs0
  have h6 := I_em_step (k := 6) (by omega) hs0
  have h7 := I_em_step (k := 7) (by omega) hs0
  have h8 := I_em_step (k := 8) (by omega) hs0
  have h9 := I_em_step (k := 9) (by omega) hs0
  have h10 := I_em_step (k := 10) (by omega) hs0
  have h11 := I_em_step (k := 11) (by omega) hs0
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] at h0
  simp only [bernPoly_eval_zero, cpow_18_neg_add, cpow_18_one_sub] at h0
  norm_num only [Nat.factorial, bernoulli_val_2, bernoulli_val_3, bernoulli_val_4,
    bernoulli_val_5, bernoulli_val_6, bernoulli_val_7, bernoulli_val_8, bernoulli_val_9,
    bernoulli_val_10, bernoulli_val_11, bernoulli_val_12] at h0
  rw [h0]
  unfold emMain
  simp only [rising]
  push_cast
  ring

/-! ### Derivatives of I_em 12 and Analytic Continuation to {Re(s) > 0, s ≠ 1} -/

noncomputable def I12_deriv (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (18 : ℝ), (bernPoly 12 (Int.fract x) : ℂ) * (-(Real.log x : ℂ)) ^ k * (x : ℂ) ^ (-(s + 12))

lemma log_le_four_rpow_quarter {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have h1 : Real.log (x ^ (1 / 4 : ℝ)) ≤ x ^ (1 / 4 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 _)
  rw [Real.log_rpow hx0] at h1
  linarith

lemma integrableOn_log_pow_rpow (k : ℕ) (hk : k ≤ 12) {α : ℝ} (hα : 12 ≤ α) :
    IntegrableOn (fun x : ℝ => (Real.log x) ^ k * x ^ (-α)) (Ioi (18 : ℝ)) := by
  have hlt : (k : ℝ) / 4 - α < -1 := by
    have hk' : (k : ℝ) ≤ 12 := by exact_mod_cast hk
    linarith
  have hdom : IntegrableOn (fun x : ℝ => (4 : ℝ) ^ k * x ^ ((k : ℝ) / 4 - α)) (Ioi (18 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt hlt (by norm_num)).const_mul _
  refine hdom.mono' ?_ ?_
  · exact ((Real.continuousOn_log.mono (fun x hx => (by linarith [mem_Ioi.mp hx] : x ≠ 0))).pow k |>.mul
      (ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (by linarith [mem_Ioi.mp hx] : x ≠ 0)))).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := by linarith [mem_Ioi.mp hx]
    have hx0 : 0 < x := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hlog0 k) (Real.rpow_nonneg hx0.le _))]
    calc (Real.log x) ^ k * x ^ (-α)
        ≤ (4 * x ^ (1 / 4 : ℝ)) ^ k * x ^ (-α) := by
          gcongr; exact log_le_four_rpow_quarter hx1
      _ = 4 ^ k * (x ^ (1 / 4 : ℝ)) ^ k * x ^ (-α) := by rw [mul_pow]
      _ = 4 ^ k * (x ^ ((k : ℝ) / 4) * x ^ (-α)) := by
          rw [← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) k, ← Real.rpow_mul hx0.le]; ring_nf
      _ = 4 ^ k * x ^ ((k : ℝ) / 4 - α) := by
          rw [← Real.rpow_add hx0]; ring_nf

lemma hasDerivAt_I12_deriv (k : ℕ) (hk : k ≤ 11) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (I12_deriv k) (I12_deriv (k + 1) s) s := by
  let F : ℂ → ℝ → ℂ := fun z x =>
    (bernPoly 12 (Int.fract x) : ℂ) * (-(Real.log x : ℂ)) ^ k * (x : ℂ) ^ (-(z + 12))
  let F' : ℂ → ℝ → ℂ := fun z x =>
    (bernPoly 12 (Int.fract x) : ℂ) * (-(Real.log x : ℂ)) ^ (k + 1) * (x : ℂ) ^ (-(z + 12))
  let bound : ℝ → ℝ := fun x => ((693 / 2730 : ℝ) / (Nat.factorial 12 : ℝ)) * ((Real.log x) ^ (k + 1) * x ^ (-(12 : ℝ)))
  have hε : 0 < s.re / 2 := by linarith
  have hball : Metric.ball s (s.re / 2) ∈ 𝓝 s := Metric.ball_mem_nhds s hε
  have hmeasF : ∀ z, AEStronglyMeasurable (F z) (volume.restrict (Ioi (18 : ℝ))) := by
    intro z
    have h1 : Measurable (fun x : ℝ => (bernPoly 12 (Int.fract x) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp ((continuous_bernPoly 12).measurable.comp measurable_fract_real)
    have h2 : Measurable (fun x : ℝ => (-(Real.log x : ℂ)) ^ k) :=
      ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg).pow_const k
    have h3 : Measurable (fun x : ℝ => (x : ℂ) ^ (-(z + 12))) :=
      Complex.continuous_ofReal.measurable.pow_const _
    exact ((h1.mul h2).mul h3).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable (F' s) (volume.restrict (Ioi (18 : ℝ))) := by
    have h1 : Measurable (fun x : ℝ => (bernPoly 12 (Int.fract x) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp ((continuous_bernPoly 12).measurable.comp measurable_fract_real)
    have h2 : Measurable (fun x : ℝ => (-(Real.log x : ℂ)) ^ (k + 1)) :=
      ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg).pow_const (k + 1)
    have h3 : Measurable (fun x : ℝ => (x : ℂ) ^ (-(s + 12))) :=
      Complex.continuous_ofReal.measurable.pow_const _
    exact ((h1.mul h2).mul h3).aestronglyMeasurable
  have hbound_int : Integrable bound (volume.restrict (Ioi (18 : ℝ))) :=
    (integrableOn_log_pow_rpow (k + 1) (by omega) le_rfl).const_mul _
  have hF_int : Integrable (F s) (volume.restrict (Ioi (18 : ℝ))) := by
    have hdom : Integrable (fun x : ℝ => ((693 / 2730 : ℝ) / (Nat.factorial 12 : ℝ)) * ((Real.log x) ^ k * x ^ (-(12 : ℝ))))
        (volume.restrict (Ioi (18 : ℝ))) :=
      (integrableOn_log_pow_rpow k (by omega) le_rfl).const_mul _
    refine hdom.mono' (hmeasF s) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := by linarith [mem_Ioi.mp hx]
    have hx0 : 0 < x := by linarith
    simp only [F, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    rw [abs_of_nonneg (Real.log_nonneg hx1)]
    have hre : (-(s + 12)).re = -(s.re + 12) := by simp
    rw [hre]
    have hpow : x ^ (-(s.re + 12)) ≤ x ^ (-(12 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [mul_assoc]
    exact mul_le_mul (abs_bernPoly_12_le (Int.fract_nonneg x) (Int.fract_lt_one x).le)
      (mul_le_mul_of_nonneg_left hpow (pow_nonneg (Real.log_nonneg hx1) k))
      (mul_nonneg (pow_nonneg (Real.log_nonneg hx1) k) (Real.rpow_nonneg hx0.le _)) (by positivity)
  have h_bound : ∀ᵐ x ∂volume.restrict (Ioi (18 : ℝ)), ∀ z ∈ Metric.ball s (s.re / 2), ‖F' z x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
    have hx1 : 1 ≤ x := by linarith [mem_Ioi.mp hx]
    have hx0 : 0 < x := by linarith
    have hzre : 0 < z.re := by
      have hdist : ‖z - s‖ < s.re / 2 := mem_ball_iff_norm.mp hz
      have hre : |z.re - s.re| ≤ ‖z - s‖ := by simpa using Complex.abs_re_le_norm (z - s)
      linarith [(abs_le.mp (hre.trans hdist.le)).1]
    simp only [F', bound, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    rw [abs_of_nonneg (Real.log_nonneg hx1)]
    have hre : (-(z + 12)).re = -(z.re + 12) := by simp
    rw [hre]
    have hpow : x ^ (-(z.re + 12)) ≤ x ^ (-(12 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [mul_assoc]
    exact mul_le_mul (abs_bernPoly_12_le (Int.fract_nonneg x) (Int.fract_lt_one x).le)
      (mul_le_mul_of_nonneg_left hpow (pow_nonneg (Real.log_nonneg hx1) (k + 1)))
      (mul_nonneg (pow_nonneg (Real.log_nonneg hx1) (k + 1)) (Real.rpow_nonneg hx0.le _)) (by positivity)
  have h_diff : ∀ᵐ x ∂volume.restrict (Ioi (18 : ℝ)), ∀ z ∈ Metric.ball s (s.re / 2),
      HasDerivAt (fun w => F w x) (F' z x) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
    have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
    have hd := (cpow_exp_hasDerivAt hx0 (12 : ℂ) z).const_mul ((bernPoly 12 (Int.fract x) : ℂ) * (-(Real.log x : ℂ)) ^ k)
    refine hd.congr_deriv ?_
    simp only [F']; ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball
    (Eventually.of_forall hmeasF) hF_int hmeasF' h_bound hbound_int h_diff).2

lemma iteratedDeriv_I12 (k : ℕ) (hk : k ≤ 12) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv k (I_em 12) s = I12_deriv k s := by
  have h0 : I_em 12 = I12_deriv 0 := by ext z; simp [I_em, I12_deriv]
  rw [h0]
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k (I12_deriv 0) =ᶠ[𝓝 s] I12_deriv k := by
      have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds hs] with z hz using ih (by omega) hz
    rw [heq.deriv_eq]
    exact (hasDerivAt_I12_deriv k (by omega) hs).deriv

lemma differentiableOn_emMain : DifferentiableOn ℂ emMain {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  intro s ⟨_, hs1⟩
  have hcpow : ∀ n : ℕ, 1 ≤ n → DifferentiableAt ℂ (fun z : ℂ => (n : ℂ) ^ (-z)) s := fun n hn => by
    have h := cpow_exp_hasDerivAt (x := (n : ℝ)) (by exact_mod_cast hn) 0 s
    simpa using h.differentiableAt
  have h18 := hcpow 18 (by omega)
  have hinv : DifferentiableAt ℂ (fun z : ℂ => (z - 1)⁻¹) s :=
    ((differentiableAt_id.sub (differentiableAt_const 1)).inv (sub_ne_zero.mpr hs1))
  have hsum : DifferentiableAt ℂ (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-z)) s :=
    DifferentiableAt.fun_sum fun n hn => hcpow n (Finset.mem_Icc.mp hn).1
  have hr : ∀ k, DifferentiableAt ℂ (fun z => rising z k) s := fun k => (differentiable_rising k).differentiableAt
  unfold emMain
  exact ((((((((hsum.add ((differentiableAt_const _).mul h18)).add
    (((differentiableAt_const _).mul h18).mul hinv)).add
    (((differentiableAt_const _).mul ((hr 1).mul h18)).div_const _)).add
    (((differentiableAt_const _).mul ((hr 3).mul h18)).div_const _)).add
    (((differentiableAt_const _).mul ((hr 5).mul h18)).div_const _)).add
    (((differentiableAt_const _).mul ((hr 7).mul h18)).div_const _)).add
    (((differentiableAt_const _).mul ((hr 9).mul h18)).div_const _)).add
    (((differentiableAt_const _).mul ((hr 11).mul h18)).div_const _)).differentiableWithinAt

lemma joinedIn_seg {U : Set ℂ} {a b : ℂ}
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → a + (t : ℂ) * (b - a) ∈ U) :
    JoinedIn U a b := by
  refine ⟨⟨⟨fun t : unitInterval => a + ((t : ℝ) : ℂ) * (b - a), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
  · simp
  · simp
  · intro t; exact hseg t.1 t.2.1 t.2.2

lemma isPreconnected_halfPlane_sub_one : IsPreconnected {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  set U : Set ℂ := {s : ℂ | 0 < s.re ∧ s ≠ 1}
  have hbase : (2 : ℂ) + I ∈ U := ⟨by simp, fun h => by have := congrArg Complex.im h; simp at this⟩
  have hpath : IsPathConnected U := by
    refine ⟨(2 : ℂ) + I, hbase, fun z hz => ?_⟩
    have hconn : ∀ w : ℂ, 0 < w.re → w.im ≠ 0 → JoinedIn U ((2 : ℂ) + I) w := by
      intro w hwre hwim
      have h1 : JoinedIn U ((2 : ℂ) + I) ((2 : ℂ) + (w.im : ℂ) * I) := by
        refine joinedIn_seg fun t ht0 ht1 => ⟨by simp, fun h => ?_⟩
        have := congrArg Complex.re h; simp at this
      have h2 : JoinedIn U ((2 : ℂ) + (w.im : ℂ) * I) w := by
        refine joinedIn_seg fun t ht0 ht1 => ⟨?_, fun h => ?_⟩
        · have hre : ((2 : ℂ) + (w.im : ℂ) * I + (t : ℂ) * (w - ((2 : ℂ) + (w.im : ℂ) * I))).re =
              2 * (1 - t) + t * w.re := by simp; ring
          rw [hre]
          rcases eq_or_lt_of_le ht0 with rfl | htpos
          · norm_num
          · have : 0 < t * w.re := mul_pos htpos hwre
            linarith
        · have him := congrArg Complex.im h
          simp at him; exact hwim him
      exact h1.trans h2
    by_cases hzim : z.im = 0
    · have h1 : JoinedIn U ((2 : ℂ) + I) ((z.re : ℂ) + I) :=
        hconn ((z.re : ℂ) + I) (by simp [hz.1]) (by simp)
      have h2 : JoinedIn U ((z.re : ℂ) + I) z := by
        have hzre1 : z.re ≠ 1 := by
          intro hre; apply hz.2; exact Complex.ext (by simp [hre]) (by simp [hzim])
        refine joinedIn_seg fun t ht0 ht1 => ⟨?_, fun h => ?_⟩
        · have hre : (((z.re : ℂ) + I) + (t : ℂ) * (z - ((z.re : ℂ) + I))).re = z.re := by simp
          rw [hre]; exact hz.1
        · have hre := congrArg Complex.re h
          simp at hre; exact hzre1 hre
      exact h1.trans h2
    · exact hconn z hz.1 hzim
  exact hpath.isConnected.isPreconnected

lemma riemannZeta_eq_em {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = emMain s - rising s 12 * I_em 12 s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  have hU_open : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hZ_diff : DifferentiableOn ℂ riemannZeta U := fun z hz =>
    (differentiableAt_riemannZeta hz.2).differentiableWithinAt
  have hR_diff : DifferentiableOn ℂ (fun z => emMain z - rising z 12 * I_em 12 z) U := by
    intro z hz
    have hI : DifferentiableAt ℂ (I_em 12) z := by
      have h0 : I_em 12 = I12_deriv 0 := by ext w; simp [I_em, I12_deriv]
      rw [h0]
      exact (hasDerivAt_I12_deriv 0 (by omega) hz.1).differentiableAt
    exact (differentiableOn_emMain z hz).sub
      (((differentiable_rising 12).differentiableAt.mul hI).differentiableWithinAt)
  have hZ_ana : AnalyticOnNhd ℂ riemannZeta U := hZ_diff.analyticOnNhd hU_open
  have hR_ana : AnalyticOnNhd ℂ (fun z => emMain z - rising z 12 * I_em 12 z) U := hR_diff.analyticOnNhd hU_open
  have h2_mem : (2 : ℂ) ∈ U := ⟨by simp, by norm_num⟩
  have hev : riemannZeta =ᶠ[𝓝 (2 : ℂ)] (fun z => emMain z - rising z 12 * I_em 12 z) := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen1.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact riemannZeta_eq_em_of_one_lt_re hz
  exact hZ_ana.eqOn_of_preconnected_of_eventuallyEq hR_ana isPreconnected_halfPlane_sub_one h2_mem hev ⟨hs0, hs1⟩

lemma iteratedDeriv_zeta_eq_em (k : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    iteratedDeriv k riemannZeta s =
      iteratedDeriv k emMain s - iteratedDeriv k (fun z => rising z 12 * I_em 12 z) s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  have hU_open : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hev : riemannZeta =ᶠ[𝓝 s] (fun z => emMain z - rising z 12 * I_em 12 z) := by
    filter_upwards [hU_open.mem_nhds ⟨hs0, hs1⟩] with z hz
    exact riemannZeta_eq_em hz.1 hz.2
  rw [hev.iteratedDeriv_eq]
  have hem_cd : ContDiffAt ℂ k emMain s :=
    ((differentiableOn_emMain.analyticOnNhd hU_open) s ⟨hs0, hs1⟩).contDiffAt.of_le le_top
  have hrem_diff : DifferentiableOn ℂ (fun z => rising z 12 * I_em 12 z) U := fun z hz => by
    have hI : DifferentiableAt ℂ (I_em 12) z := by
      have h0 : I_em 12 = I12_deriv 0 := by ext w; simp [I_em, I12_deriv]
      rw [h0]; exact (hasDerivAt_I12_deriv 0 (by omega) hz.1).differentiableAt
    exact ((differentiable_rising 12).differentiableAt.mul hI).differentiableWithinAt
  have hrem_cd : ContDiffAt ℂ k (fun z => rising z 12 * I_em 12 z) s :=
    ((hrem_diff.analyticOnNhd hU_open) s ⟨hs0, hs1⟩).contDiffAt.of_le le_top
  exact iteratedDeriv_sub hem_cd hrem_cd

/-! ### Section 3: Explicit Integral Remainder Bounds -/

noncomputable def I_log (k : ℕ) : ℝ :=
  ∫ x in Ioi (18 : ℝ), (Real.log x) ^ k * x ^ (-(12 : ℝ))

lemma norm_I12_deriv_le (k : ℕ) (hk : k ≤ 12) {s : ℂ} (hs : 0 < s.re) :
    ‖I12_deriv k s‖ ≤ ((693 / 2730 : ℝ) / (Nat.factorial 12 : ℝ)) * I_log k := by
  unfold I12_deriv I_log
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrableOn_log_pow_rpow k hk le_rfl).const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : 1 ≤ x := by linarith [mem_Ioi.mp hx]
  have hx0 : 0 < x := by linarith
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  rw [abs_of_nonneg (Real.log_nonneg hx1)]
  have hre : (-(s + 12)).re = -(s.re + 12) := by simp
  rw [hre]
  have hpow : x ^ (-(s.re + 12)) ≤ x ^ (-(12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  rw [mul_assoc]
  exact mul_le_mul (abs_bernPoly_12_le (Int.fract_nonneg x) (Int.fract_lt_one x).le)
    (mul_le_mul_of_nonneg_left hpow (pow_nonneg (Real.log_nonneg hx1) k))
    (mul_nonneg (pow_nonneg (Real.log_nonneg hx1) k) (Real.rpow_nonneg hx0.le _)) (by positivity)

lemma tendsto_log_pow_rpow_neg11 (k : ℕ) (hk : k ≤ 12) :
    Tendsto (fun x : ℝ => -(Real.log x) ^ k * x ^ (-(11 : ℝ)) / 11) atTop (𝓝 0) := by
  have hexp : 0 < 11 - (k : ℝ) / 4 := by
    have hk' : (k : ℝ) ≤ 12 := Nat.cast_le.mpr hk
    linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_
    (by simpa [neg_sub] using (tendsto_rpow_neg_atTop hexp).const_mul ((4 : ℝ) ^ k / 11))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx1
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg hlog0 k),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _), abs_of_pos (by norm_num : (0 : ℝ) < 11)]
  calc (Real.log x) ^ k * x ^ (-(11 : ℝ)) / 11
      ≤ (4 * x ^ (1 / 4 : ℝ)) ^ k * x ^ (-(11 : ℝ)) / 11 := by
        gcongr; exact log_le_four_rpow_quarter hx1
    _ = (4 : ℝ) ^ k / 11 * ((x ^ (1 / 4 : ℝ)) ^ k * x ^ (-(11 : ℝ))) := by rw [mul_pow]; ring
    _ = (4 : ℝ) ^ k / 11 * x ^ ((k : ℝ) / 4 - 11) := by
        rw [← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) k, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
        congr 2; ring

lemma I_log_zero : I_log 0 = 1 / (11 * (18 : ℝ) ^ 11) := by
  unfold I_log
  simp only [pow_zero, one_mul]
  rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
  rw [show -(12 : ℝ) + 1 = -(11 : ℝ) by norm_num, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 18),
    show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

lemma I_log_succ (k : ℕ) (hk : k ≤ 11) :
    I_log (k + 1) = (Real.log 18) ^ (k + 1) / (11 * (18 : ℝ) ^ 11) + ((k + 1 : ℝ) / 11) * I_log k := by
  let g : ℝ → ℝ := fun x => -(Real.log x) ^ (k + 1) * x ^ (-(11 : ℝ)) / 11
  let g' : ℝ → ℝ := fun x => (Real.log x) ^ (k + 1) * x ^ (-(12 : ℝ)) - ((k + 1 : ℝ) / 11) * ((Real.log x) ^ k * x ^ (-(12 : ℝ)))
  have hderiv : ∀ x ∈ Ici (18 : ℝ), HasDerivAt g (g' x) x := by
    intro x hx
    have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
    have hlog : HasDerivAt (fun y => (Real.log y) ^ (k + 1)) ((k + 1 : ℝ) * (Real.log x) ^ k * x⁻¹) x := by
      have h := ((Real.hasDerivAt_log hxpos.ne').pow (k + 1))
      refine h.congr_deriv ?_; push_cast; ring
    have hpow : HasDerivAt (fun y => y ^ (-(11 : ℝ))) (-(11 : ℝ) * x ^ (-(12 : ℝ))) x := by
      have h := Real.hasDerivAt_rpow_const (p := -(11 : ℝ)) (Or.inl hxpos.ne')
      refine h.congr_deriv ?_; norm_num
    have hprod := (hlog.neg.mul hpow).div_const 11
    refine hprod.congr_deriv ?_
    simp only [g', Pi.neg_apply]
    have hxmul : x⁻¹ * x ^ (-(11 : ℝ)) = x ^ (-(12 : ℝ)) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_add hxpos]; norm_num
    calc (-((↑k + 1) * Real.log x ^ k * x⁻¹) * x ^ (-11 : ℝ) + -Real.log x ^ (k + 1) * (-11 * x ^ (-12 : ℝ))) / 11
        = (-(↑k + 1) * Real.log x ^ k * (x⁻¹ * x ^ (-11 : ℝ)) + 11 * (Real.log x ^ (k + 1) * x ^ (-12 : ℝ))) / 11 := by ring
      _ = (-(↑k + 1) * Real.log x ^ k * x ^ (-12 : ℝ) + 11 * (Real.log x ^ (k + 1) * x ^ (-12 : ℝ))) / 11 := by rw [hxmul]
      _ = Real.log x ^ (k + 1) * x ^ (-12 : ℝ) - (↑k + 1) / 11 * (Real.log x ^ k * x ^ (-12 : ℝ)) := by ring
  have hint_g' : IntegrableOn g' (Ioi (18 : ℝ)) :=
    (integrableOn_log_pow_rpow (k + 1) (by omega) le_rfl).sub
      ((integrableOn_log_pow_rpow k (by omega) le_rfl).const_mul _)
  have htend : Tendsto g atTop (𝓝 0) := tendsto_log_pow_rpow_neg11 (k + 1) (by omega)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_g' htend
  have hsub : ∫ x in Ioi (18 : ℝ), g' x = I_log (k + 1) - ((k + 1 : ℝ) / 11) * I_log k := by
    unfold g' I_log
    rw [integral_sub (integrableOn_log_pow_rpow (k + 1) (by omega) le_rfl)
      ((integrableOn_log_pow_rpow k (by omega) le_rfl).const_mul _), integral_const_mul]
  rw [hsub] at hftc
  have hg18 : g 18 = -(Real.log 18) ^ (k + 1) / (11 * (18 : ℝ) ^ 11) := by
    simp only [g]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 18),
      show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hg18] at hftc
  linarith

def I_log_num : ℕ → ℕ
  | 0 => 1
  | k + 1 => 29 ^ (k + 1) * 11 ^ (k + 1) + (k + 1) * 10 * I_log_num k

lemma I_log_le_num (hlog18 : Real.log 18 ≤ 29 / 10) : ∀ k ≤ 12,
    I_log k ≤ (I_log_num k : ℝ) / ((11 : ℝ) ^ (k + 1) * (18 : ℝ) ^ 11 * (10 : ℝ) ^ k) := by
  intro k hk
  induction k with
  | zero =>
    rw [I_log_zero, I_log_num]
    push_cast; simp
  | succ k ih =>
    rw [I_log_succ k (by omega), I_log_num]
    have h1 : (Real.log 18) ^ (k + 1) ≤ (29 / 10 : ℝ) ^ (k + 1) :=
      pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) hlog18 (k + 1)
    have h2 : I_log k ≤ (I_log_num k : ℝ) / ((11 : ℝ) ^ (k + 1) * (18 : ℝ) ^ 11 * (10 : ℝ) ^ k) :=
      ih (by omega)
    have hpos1 : (0 : ℝ) < 11 * (18 : ℝ) ^ 11 := by positivity
    have hpos2 : (0 : ℝ) ≤ ((k : ℝ) + 1) / 11 := by positivity
    have hle := add_le_add (div_le_div_of_nonneg_right h1 hpos1.le) (mul_le_mul_of_nonneg_left h2 hpos2)
    refine hle.trans_eq ?_
    push_cast
    have hne11 : (11 : ℝ) ^ (k + 1) ≠ 0 := by positivity
    have hne10 : (10 : ℝ) ^ k ≠ 0 := by positivity
    have hne18 : (18 : ℝ) ^ 11 ≠ 0 := by positivity
    rw [div_pow, pow_succ (11 : ℝ) (k + 1), pow_succ (10 : ℝ) k]
    field_simp [hne11, hne10, hne18]



/-! ### Section 1: Banach Fixed-Point Zero Existence -/

lemma exists_zero_of_newton {f : ℂ → ℂ} {s₀ c : ℂ} {r M₂ : ℝ}
    (hr : 0 < r) (hc : c ≠ 0) (hM₂ : 0 ≤ M₂)
    (hf : ∀ z ∈ closedBall s₀ r, DifferentiableAt ℂ f z)
    (hf' : ∀ z ∈ closedBall s₀ r, DifferentiableAt ℂ (deriv f) z)
    (h0 : ‖f s₀‖ ≤ r / 2 * ‖c‖)
    (h1 : ‖deriv f s₀ - c‖ ≤ ‖c‖ / 4)
    (h2 : ∀ z ∈ closedBall s₀ r, ‖deriv (deriv f) z‖ ≤ M₂)
    (h3 : M₂ * r ≤ ‖c‖ / 4) :
    ∃ z ∈ closedBall s₀ r, f z = 0 := by
  let T : ℂ → ℂ := fun z => z - f z / c
  have hconv : Convex ℝ (closedBall s₀ r) := convex_closedBall s₀ r
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hT_deriv : ∀ z ∈ closedBall s₀ r, HasDerivAt T (1 - deriv f z / c) z := by
    intro z hz
    exact (hasDerivAt_id z).sub ((hf z hz).hasDerivAt.div_const c)
  have hT_norm : ∀ z ∈ closedBall s₀ r, ‖deriv T z‖ ≤ 1 / 2 := by
    intro z hz
    rw [(hT_deriv z hz).deriv]
    have hdiff_df : ‖deriv f z - deriv f s₀‖ ≤ M₂ * ‖z - s₀‖ :=
      hconv.norm_image_sub_le_of_norm_deriv_le (f := deriv f) hf' h2
        (mem_closedBall_self hr.le) hz
    have hz_dist : ‖z - s₀‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hz
    have hstep : ‖deriv f z - deriv f s₀‖ ≤ ‖c‖ / 4 :=
      hdiff_df.trans ((mul_le_mul_of_nonneg_left hz_dist hM₂).trans h3)
    have hsub : ‖c - deriv f z‖ ≤ ‖c‖ / 2 := by
      calc ‖c - deriv f z‖ = ‖(c - deriv f s₀) + (deriv f s₀ - deriv f z)‖ := by ring_nf
        _ ≤ ‖c - deriv f s₀‖ + ‖deriv f s₀ - deriv f z‖ := norm_add_le _ _
        _ = ‖deriv f s₀ - c‖ + ‖deriv f z - deriv f s₀‖ := by
            rw [norm_sub_rev c (deriv f s₀), norm_sub_rev (deriv f s₀) (deriv f z)]
        _ ≤ ‖c‖ / 4 + ‖c‖ / 4 := add_le_add h1 hstep
        _ = ‖c‖ / 2 := by ring
    have heq : (1 : ℂ) - deriv f z / c = (c - deriv f z) / c := by
      field_simp [hc]
    rw [heq, norm_div]
    exact (div_le_iff₀ hcpos).mpr (by linarith)
  have hT_dist : ∀ x ∈ closedBall s₀ r, ∀ y ∈ closedBall s₀ r,
      dist (T x) (T y) ≤ (1 / 2 : ℝ) * dist x y := by
    intro x hx y hy
    simpa [dist_eq_norm] using
      hconv.norm_image_sub_le_of_norm_deriv_le (f := T)
        (fun w hw => (hT_deriv w hw).differentiableAt) hT_norm hy hx
  have hT_maps : MapsTo T (closedBall s₀ r) (closedBall s₀ r) := by
    intro z hz
    rw [mem_closedBall]
    have h1' : dist (T z) (T s₀) ≤ (1 / 2 : ℝ) * dist z s₀ :=
      hT_dist z hz s₀ (mem_closedBall_self hr.le)
    have h2' : dist (T s₀) s₀ ≤ r / 2 := by
      rw [dist_eq_norm]
      have : T s₀ - s₀ = -(f s₀ / c) := by simp [T]
      rw [this, norm_neg, norm_div]
      exact (div_le_iff₀ hcpos).mpr h0
    have hz' : dist z s₀ ≤ r := mem_closedBall.mp hz
    calc dist (T z) s₀ ≤ dist (T z) (T s₀) + dist (T s₀) s₀ := dist_triangle _ _ _
      _ ≤ (1 / 2) * r + r / 2 := add_le_add (h1'.trans (by linarith)) h2'
      _ = r := by ring
  have hcontr : ContractingWith (1 / 2 : NNReal) (hT_maps.restrict T _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simpa [Subtype.dist_eq, MapsTo.val_restrict_apply] using hT_dist x.1 x.2 y.1 y.2
  obtain ⟨z, hz, hfix, _, _⟩ := hcontr.exists_fixedPoint'
    (isClosed_closedBall.isComplete) hT_maps (mem_closedBall_self hr.le) (edist_ne_top _ _)
  refine ⟨z, hz, ?_⟩
  have hTz : z - f z / c = z := hfix
  have hdiv : f z / c = 0 := by linear_combination -hTz
  exact (div_eq_zero_iff.mp hdiv).resolve_right hc

/-! ### Section 4: Fixed-Point Complex Ball Arithmetic (S = 2^64) -/

def SCALE : ℕ := 2 ^ 64

lemma scale_pos : (0 : ℝ) < (SCALE : ℝ) := by unfold SCALE; positivity

structure IBall where
  re : ℤ
  im : ℤ
  rad : ℕ
  deriving Repr, DecidableEq

noncomputable def IBall.center (a : IBall) : ℂ :=
  ((a.re : ℂ) + (a.im : ℂ) * I) / (SCALE : ℂ)

def IBall.Mem (a : IBall) (z : ℂ) : Prop :=
  ‖z - a.center‖ ≤ (a.rad : ℝ) / (SCALE : ℝ)

def IBall.absUb (a : IBall) : ℕ := a.re.natAbs + a.im.natAbs

lemma norm_ofReal_add_mul_I_le (x y : ℝ) : ‖(x : ℂ) + (y : ℂ) * I‖ ≤ |x| + |y| := by
  calc ‖(x : ℂ) + (y : ℂ) * I‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
    _ = |x| + |y| := by simp

lemma norm_re_im_le (x y : ℤ) : ‖(x : ℂ) + (y : ℂ) * I‖ ≤ (x.natAbs + y.natAbs : ℕ) := by
  calc ‖(x : ℂ) + (y : ℂ) * I‖ = ‖((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I‖ := by simp
    _ ≤ |(x : ℝ)| + |(y : ℝ)| := norm_ofReal_add_mul_I_le _ _
    _ = ((x.natAbs + y.natAbs : ℕ) : ℝ) := by simp [← Int.cast_abs]

lemma IBall.norm_center_le (a : IBall) : ‖a.center‖ ≤ (a.absUb : ℝ) / (SCALE : ℝ) := by
  rw [IBall.center, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_re_im_le a.re a.im) (scale_pos.le)

lemma IBall.norm_le {a : IBall} {z : ℂ} (h : a.Mem z) :
    ‖z‖ ≤ ((a.absUb + a.rad : ℕ) : ℝ) / (SCALE : ℝ) := by
  calc ‖z‖ = ‖(z - a.center) + a.center‖ := by ring_nf
    _ ≤ ‖z - a.center‖ + ‖a.center‖ := norm_add_le _ _
    _ ≤ (a.rad : ℝ) / SCALE + (a.absUb : ℝ) / SCALE := add_le_add h a.norm_center_le
    _ = ((a.absUb + a.rad : ℕ) : ℝ) / SCALE := by push_cast; ring

def ibZero : IBall := ⟨0, 0, 0⟩
def ibOne : IBall := ⟨(SCALE : ℤ), 0, 0⟩

lemma ibZero_mem : ibZero.Mem 0 := by simp [IBall.Mem, IBall.center, ibZero]

lemma ibOne_mem : ibOne.Mem 1 := by
  have hS : (SCALE : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by decide)
  simp [IBall.Mem, IBall.center, ibOne, div_self hS]

def ibConst (rn : ℤ) (rd : ℕ) (in_ : ℤ) (id_ : ℕ) : IBall :=
  ⟨(rn * (SCALE : ℤ)) / (rd : ℤ), (in_ * (SCALE : ℤ)) / (id_ : ℤ), 2⟩

lemma abs_ediv_sub_le (a : ℤ) (b : ℕ) (hb : 0 < b) :
    |(a : ℝ) / (b : ℝ) - ((a / (b : ℤ) : ℤ) : ℝ)| ≤ 1 := by
  have hb' : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hmod_nn : 0 ≤ a % (b : ℤ) := Int.emod_nonneg a (Int.natCast_ne_zero.mpr hb.ne')
  have hmod_lt : a % (b : ℤ) < (b : ℤ) := Int.emod_lt_of_pos a (Int.natCast_pos.mpr hb)
  have hdiv : (a : ℤ) = (b : ℤ) * (a / (b : ℤ)) + a % (b : ℤ) := (Int.mul_ediv_add_emod a b).symm
  have hdivR : (a : ℝ) = (b : ℝ) * ((a / (b : ℤ) : ℤ) : ℝ) + ((a % (b : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hdiv
  have hsub : (a : ℝ) / (b : ℝ) - ((a / (b : ℤ) : ℤ) : ℝ) = ((a % (b : ℤ) : ℤ) : ℝ) / (b : ℝ) := by
    field_simp [hb'.ne']
    linarith
  rw [hsub, abs_of_nonneg (div_nonneg (by exact_mod_cast hmod_nn) hb'.le)]
  exact (div_le_one hb').mpr (by exact_mod_cast hmod_lt.le)

lemma norm_ediv_err_le (a b : ℤ) (da db : ℕ) (hda : 0 < da) (hdb : 0 < db) :
    ‖(((a : ℂ) / (da : ℂ) - ((a / (da : ℤ) : ℤ) : ℂ)) +
      ((b : ℂ) / (db : ℂ) - ((b / (db : ℤ) : ℤ) : ℂ)) * I) / (SCALE : ℂ)‖ ≤
      2 / (SCALE : ℝ) := by
  rw [norm_div, Complex.norm_natCast]
  refine div_le_div_of_nonneg_right ?_ scale_pos.le
  have heq : ((a : ℂ) / (da : ℂ) - ((a / (da : ℤ) : ℤ) : ℂ)) +
      ((b : ℂ) / (db : ℂ) - ((b / (db : ℤ) : ℤ) : ℂ)) * I =
      (((a : ℝ) / (da : ℝ) - ((a / (da : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) +
      (((b : ℝ) / (db : ℝ) - ((b / (db : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) * I := by
    push_cast; rfl
  rw [heq]
  calc _ ≤ |(a : ℝ) / (da : ℝ) - ((a / (da : ℤ) : ℤ) : ℝ)| +
           |(b : ℝ) / (db : ℝ) - ((b / (db : ℤ) : ℤ) : ℝ)| :=
         norm_ofReal_add_mul_I_le _ _
    _ ≤ 1 + 1 := add_le_add (abs_ediv_sub_le a da hda) (abs_ediv_sub_le b db hdb)
    _ = 2 := by norm_num

lemma ibConst_mem {rn in_ : ℤ} {rd id_ : ℕ} (hrd : 0 < rd) (hid : 0 < id_) :
    (ibConst rn rd in_ id_).Mem ((rn : ℂ) / (rd : ℂ) + (in_ : ℂ) / (id_ : ℂ) * I) := by
  have hSC : (SCALE : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by decide)
  rw [IBall.Mem, IBall.center, ibConst]
  dsimp only
  have hdiff : (rn : ℂ) / (rd : ℂ) + (in_ : ℂ) / (id_ : ℂ) * I -
      (((rn * (SCALE : ℤ) / (rd : ℤ) : ℤ) : ℂ) + ((in_ * (SCALE : ℤ) / (id_ : ℤ) : ℤ) : ℂ) * I) / (SCALE : ℂ) =
      ((((rn * (SCALE : ℤ) : ℤ) : ℂ) / (rd : ℂ) - ((rn * (SCALE : ℤ) / (rd : ℤ) : ℤ) : ℂ)) +
       (((in_ * (SCALE : ℤ) : ℤ) : ℂ) / (id_ : ℂ) - ((in_ * (SCALE : ℤ) / (id_ : ℤ) : ℤ) : ℂ)) * I) / (SCALE : ℂ) := by
    push_cast; field_simp [hSC]; ring
  rw [hdiff]
  simpa using norm_ediv_err_le (rn * SCALE) (in_ * SCALE) rd id_ hrd hid

def ibAdd (a b : IBall) : IBall := ⟨a.re + b.re, a.im + b.im, a.rad + b.rad⟩
def ibNeg (a : IBall) : IBall := ⟨-a.re, -a.im, a.rad⟩
def ibSub (a b : IBall) : IBall := ⟨a.re - b.re, a.im - b.im, a.rad + b.rad⟩
def ibScaleInt (k : ℤ) (a : IBall) : IBall := ⟨k * a.re, k * a.im, k.natAbs * a.rad⟩

lemma ibAdd_mem {a b : IBall} {x y : ℂ} (hx : a.Mem x) (hy : b.Mem y) :
    (ibAdd a b).Mem (x + y) := by
  rw [IBall.Mem, IBall.center, ibAdd]
  have h1 : x + y - (((a.re + b.re : ℤ) : ℂ) + ((a.im + b.im : ℤ) : ℂ) * I) / (SCALE : ℂ) =
      (x - a.center) + (y - b.center) := by
    simp only [IBall.center]; push_cast; ring
  rw [h1]
  calc ‖(x - a.center) + (y - b.center)‖ ≤ ‖x - a.center‖ + ‖y - b.center‖ := norm_add_le _ _
    _ ≤ (a.rad : ℝ) / SCALE + (b.rad : ℝ) / SCALE := add_le_add hx hy
    _ = ((a.rad + b.rad : ℕ) : ℝ) / SCALE := by push_cast; ring

lemma ibNeg_mem {a : IBall} {x : ℂ} (hx : a.Mem x) : (ibNeg a).Mem (-x) := by
  rw [IBall.Mem, IBall.center, ibNeg]
  have h1 : -x - (((-a.re : ℤ) : ℂ) + ((-a.im : ℤ) : ℂ) * I) / (SCALE : ℂ) = -(x - a.center) := by
    simp only [IBall.center]; push_cast; ring
  rw [h1, norm_neg]; exact hx

lemma ibSub_mem {a b : IBall} {x y : ℂ} (hx : a.Mem x) (hy : b.Mem y) :
    (ibSub a b).Mem (x - y) := by
  simpa [ibSub, ibAdd, ibNeg, sub_eq_add_neg] using ibAdd_mem hx (ibNeg_mem hy)

lemma ibScaleInt_mem (k : ℤ) {a : IBall} {x : ℂ} (hx : a.Mem x) :
    (ibScaleInt k a).Mem ((k : ℂ) * x) := by
  rw [IBall.Mem, IBall.center, ibScaleInt]
  have h1 : (k : ℂ) * x - (((k * a.re : ℤ) : ℂ) + ((k * a.im : ℤ) : ℂ) * I) / (SCALE : ℂ) =
      (k : ℂ) * (x - a.center) := by
    simp only [IBall.center]; push_cast; ring
  rw [h1, norm_mul, Complex.norm_intCast]
  calc |(k : ℝ)| * ‖x - a.center‖ ≤ (k.natAbs : ℝ) * ((a.rad : ℝ) / SCALE) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
    _ = ((k.natAbs * a.rad : ℕ) : ℝ) / SCALE := by push_cast; ring

def ibDivNat (a : IBall) (d : ℕ) : IBall :=
  ⟨a.re / (d : ℤ), a.im / (d : ℤ), (a.rad + d - 1) / d + 2⟩

lemma nat_ceil_div_le (n d : ℕ) (hd : 0 < d) :
    (n : ℝ) / (d : ℝ) ≤ (((n + d - 1) / d : ℕ) : ℝ) := by
  have hd' : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  rw [div_le_iff₀ hd']
  have hnat : n ≤ (n + d - 1) / d * d := by
    have hdm := Nat.div_add_mod (n + d - 1) d
    have hlt := Nat.mod_lt (n + d - 1) hd
    rw [mul_comm] at hdm
    omega
  exact_mod_cast hnat

lemma ibDivNat_mem {a : IBall} {x : ℂ} {d : ℕ} (hd : 0 < d) (hx : a.Mem x) :
    (ibDivNat a d).Mem (x / (d : ℂ)) := by
  have hSC : (SCALE : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by decide)
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [IBall.Mem, IBall.center, ibDivNat]
  dsimp only
  have hsplit : x / (d : ℂ) - (((a.re / (d : ℤ) : ℤ) : ℂ) + ((a.im / (d : ℤ) : ℤ) : ℂ) * I) / (SCALE : ℂ) =
      (x - a.center) / (d : ℂ) +
      (((a.re : ℂ) / (d : ℂ) - ((a.re / (d : ℤ) : ℤ) : ℂ)) +
       ((a.im : ℂ) / (d : ℂ) - ((a.im / (d : ℤ) : ℤ) : ℂ)) * I) / (SCALE : ℂ) := by
    simp only [IBall.center]; field_simp [hSC, hdC]; ring
  rw [hsplit]
  have h1 : ‖(x - a.center) / (d : ℂ)‖ ≤ (((a.rad + d - 1) / d : ℕ) : ℝ) / SCALE := by
    rw [norm_div, Complex.norm_natCast]
    calc ‖x - a.center‖ / (d : ℝ) ≤ ((a.rad : ℝ) / SCALE) / (d : ℝ) :=
          div_le_div_of_nonneg_right hx hdR.le
      _ = ((a.rad : ℝ) / (d : ℝ)) / SCALE := by ring
      _ ≤ (((a.rad + d - 1) / d : ℕ) : ℝ) / SCALE :=
          div_le_div_of_nonneg_right (nat_ceil_div_le a.rad d hd) scale_pos.le
  calc ‖_ + _‖ ≤ ‖(x - a.center) / (d : ℂ)‖ + ‖_‖ := norm_add_le _ _
    _ ≤ (((a.rad + d - 1) / d : ℕ) : ℝ) / SCALE + 2 / SCALE :=
        add_le_add h1 (norm_ediv_err_le a.re a.im d d hd hd)
    _ = ((((a.rad + d - 1) / d + 2 : ℕ) : ℝ)) / SCALE := by push_cast; ring

def ibMul (a b : IBall) : IBall :=
  let reRaw := a.re * b.re - a.im * b.im
  let imRaw := a.re * b.im + a.im * b.re
  let num := a.absUb * b.rad + b.absUb * a.rad + a.rad * b.rad
  ⟨reRaw / (SCALE : ℤ), imRaw / (SCALE : ℤ), (num + SCALE - 1) / SCALE + 2⟩

lemma ibMul_mem {a b : IBall} {x y : ℂ} (hx : a.Mem x) (hy : b.Mem y) :
    (ibMul a b).Mem (x * y) := by
  have hSpos : 0 < SCALE := by decide
  have hSC : (SCALE : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hSpos.ne'
  rw [IBall.Mem, IBall.center, ibMul]
  dsimp only
  set reRaw := a.re * b.re - a.im * b.im
  set imRaw := a.re * b.im + a.im * b.re
  set num := a.absUb * b.rad + b.absUb * a.rad + a.rad * b.rad
  have hcenter_mul : a.center * b.center =
      (((reRaw : ℂ) / (SCALE : ℂ)) + ((imRaw : ℂ) / (SCALE : ℂ)) * I) / (SCALE : ℂ) := by
    simp only [IBall.center, reRaw, imRaw]
    push_cast
    field_simp [hSC]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hsplit : x * y - (((reRaw / (SCALE : ℤ) : ℤ) : ℂ) + ((imRaw / (SCALE : ℤ) : ℤ) : ℂ) * I) / (SCALE : ℂ) =
      (a.center * (y - b.center) + b.center * (x - a.center) + (x - a.center) * (y - b.center)) +
      (((reRaw : ℂ) / (SCALE : ℂ) - ((reRaw / (SCALE : ℤ) : ℤ) : ℂ)) +
       ((imRaw : ℂ) / (SCALE : ℂ) - ((imRaw / (SCALE : ℤ) : ℤ) : ℂ)) * I) / (SCALE : ℂ) := by
    have h1 : x * y - a.center * b.center =
        a.center * (y - b.center) + b.center * (x - a.center) + (x - a.center) * (y - b.center) := by ring
    rw [← h1, hcenter_mul]
    ring
  rw [hsplit]
  have hpart1 : ‖a.center * (y - b.center) + b.center * (x - a.center) + (x - a.center) * (y - b.center)‖ ≤
      (((num + SCALE - 1) / SCALE : ℕ) : ℝ) / SCALE := by
    calc _ ≤ ‖a.center * (y - b.center) + b.center * (x - a.center)‖ + ‖(x - a.center) * (y - b.center)‖ :=
          norm_add_le _ _
      _ ≤ (‖a.center * (y - b.center)‖ + ‖b.center * (x - a.center)‖) + ‖(x - a.center) * (y - b.center)‖ :=
          add_le_add_left (norm_add_le _ _) _
      _ = ‖a.center‖ * ‖y - b.center‖ + ‖b.center‖ * ‖x - a.center‖ + ‖x - a.center‖ * ‖y - b.center‖ := by
          simp
      _ ≤ ((a.absUb : ℝ) / SCALE) * ((b.rad : ℝ) / SCALE) +
          ((b.absUb : ℝ) / SCALE) * ((a.rad : ℝ) / SCALE) +
          ((a.rad : ℝ) / SCALE) * ((b.rad : ℝ) / SCALE) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul a.norm_center_le hy (norm_nonneg _) (by positivity)
          · exact mul_le_mul b.norm_center_le hx (norm_nonneg _) (by positivity)
          · exact mul_le_mul hx hy (norm_nonneg _) (by positivity)
      _ = ((num : ℝ) / SCALE) / SCALE := by simp only [num]; push_cast; ring
      _ ≤ (((num + SCALE - 1) / SCALE : ℕ) : ℝ) / SCALE :=
          div_le_div_of_nonneg_right (nat_ceil_div_le num SCALE hSpos) scale_pos.le
  calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
    _ ≤ (((num + SCALE - 1) / SCALE : ℕ) : ℝ) / SCALE + 2 / SCALE :=
        add_le_add hpart1 (norm_ediv_err_le reRaw imRaw SCALE SCALE hSpos hSpos)
    _ = ((((num + SCALE - 1) / SCALE + 2 : ℕ) : ℝ)) / SCALE := by push_cast; ring

def ibInv (a : IBall) : IBall :=
  let cLb := max a.re.natAbs a.im.natAbs
  let n2 : ℕ := a.re.natAbs * a.re.natAbs + a.im.natAbs * a.im.natAbs
  let re := (a.re * (SCALE : ℤ) * (SCALE : ℤ)) / (n2 : ℤ)
  let im := (-a.im * (SCALE : ℤ) * (SCALE : ℤ)) / (n2 : ℤ)
  let denom := cLb * (cLb - a.rad)
  ⟨re, im, (SCALE * SCALE * a.rad + denom - 1) / denom + 2⟩

lemma ibInv_mem {a : IBall} {x : ℂ} (hx : a.Mem x)
    (hpos : a.rad < max a.re.natAbs a.im.natAbs) :
    (ibInv a).Mem x⁻¹ := by
  have hSpos : 0 < SCALE := by decide
  have hSC : (SCALE : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hSpos.ne'
  set cLb := max a.re.natAbs a.im.natAbs
  set n2 : ℕ := a.re.natAbs * a.re.natAbs + a.im.natAbs * a.im.natAbs
  set denom := cLb * (cLb - a.rad)
  have hcLb_pos : 0 < cLb := lt_of_le_of_lt (Nat.zero_le _) hpos
  have hsub_pos : 0 < cLb - a.rad := Nat.sub_pos_of_lt hpos
  have hdenom_pos : 0 < denom := Nat.mul_pos hcLb_pos hsub_pos
  have hn2_pos : 0 < n2 := by
    have hle : cLb * cLb ≤ n2 := by
      dsimp only [cLb, n2]
      rcases le_total a.re.natAbs a.im.natAbs with h | h
      · rw [max_eq_right h]; exact Nat.le_add_left _ _
      · rw [max_eq_left h]; exact Nat.le_add_right _ _
    exact lt_of_lt_of_le (Nat.mul_pos hcLb_pos hcLb_pos) hle
  have hnorm_c : (cLb : ℝ) / SCALE ≤ ‖a.center‖ := by
    rw [IBall.center, norm_div, Complex.norm_natCast]
    refine div_le_div_of_nonneg_right ?_ scale_pos.le
    have hre : (a.re.natAbs : ℝ) ≤ ‖(a.re : ℂ) + (a.im : ℂ) * I‖ := by
      calc (a.re.natAbs : ℝ) = |(a.re : ℝ)| := by simp [← Int.cast_abs]
        _ = |((a.re : ℂ) + (a.im : ℂ) * I).re| := by simp
        _ ≤ ‖(a.re : ℂ) + (a.im : ℂ) * I‖ := Complex.abs_re_le_norm _
    have him : (a.im.natAbs : ℝ) ≤ ‖(a.re : ℂ) + (a.im : ℂ) * I‖ := by
      calc (a.im.natAbs : ℝ) = |(a.im : ℝ)| := by simp [← Int.cast_abs]
        _ = |((a.re : ℂ) + (a.im : ℂ) * I).im| := by simp
        _ ≤ ‖(a.re : ℂ) + (a.im : ℂ) * I‖ := Complex.abs_im_le_norm _
    exact_mod_cast max_le hre him
  have hc_ne : a.center ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm_c
    have : (0 : ℝ) < (cLb : ℝ) / SCALE := div_pos (Nat.cast_pos.mpr hcLb_pos) scale_pos
    linarith
  have hnorm_x : ((cLb - a.rad : ℕ) : ℝ) / SCALE ≤ ‖x‖ := by
    have h1 : ‖a.center‖ - ‖x - a.center‖ ≤ ‖x‖ := by
      have := norm_sub_norm_le a.center (a.center - x)
      simpa [norm_sub_rev] using this
    calc ((cLb - a.rad : ℕ) : ℝ) / SCALE = (cLb : ℝ) / SCALE - (a.rad : ℝ) / SCALE := by
          rw [Nat.cast_sub hpos.le]; ring
      _ ≤ ‖a.center‖ - ‖x - a.center‖ := sub_le_sub hnorm_c hx
      _ ≤ ‖x‖ := h1
  have hx_ne : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm_x
    have : (0 : ℝ) < ((cLb - a.rad : ℕ) : ℝ) / SCALE := div_pos (Nat.cast_pos.mpr hsub_pos) scale_pos
    linarith
  set reNum : ℤ := a.re * (SCALE : ℤ) * (SCALE : ℤ)
  set imNum : ℤ := -a.im * (SCALE : ℤ) * (SCALE : ℤ)
  have hc_inv : a.center⁻¹ =
      (((reNum : ℂ) / (n2 : ℂ)) + ((imNum : ℂ) / (n2 : ℂ)) * I) / (SCALE : ℂ) := by
    have hn2C : (n2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn2_pos.ne'
    have hne : (a.re : ℂ) + (a.im : ℂ) * I ≠ 0 := by
      intro h0; exact hc_ne (by simp [IBall.center, h0])
    have hsq : ((a.re : ℂ) + (a.im : ℂ) * I) * ((a.re : ℂ) - (a.im : ℂ) * I) = (n2 : ℂ) := by
      have hr : (a.re : ℂ) ^ 2 = ((a.re.natAbs * a.re.natAbs : ℕ) : ℂ) := by
        rw [Nat.cast_mul, ← sq]
        have hC := congrArg (Int.cast (R := ℂ)) (Int.natAbs_sq a.re).symm
        simp only [Int.cast_pow, Int.cast_natCast] at hC
        exact hC
      have hi : (a.im : ℂ) ^ 2 = ((a.im.natAbs * a.im.natAbs : ℕ) : ℂ) := by
        rw [Nat.cast_mul, ← sq]
        have hC := congrArg (Int.cast (R := ℂ)) (Int.natAbs_sq a.im).symm
        simp only [Int.cast_pow, Int.cast_natCast] at hC
        exact hC
      calc ((a.re : ℂ) + (a.im : ℂ) * I) * ((a.re : ℂ) - (a.im : ℂ) * I)
          = (a.re : ℂ) ^ 2 + (a.im : ℂ) ^ 2 := by ring_nf; simp [Complex.I_sq]
        _ = (n2 : ℂ) := by rw [hr, hi]; simp [n2]
    rw [IBall.center, inv_div]
    simp only [reNum, imNum]
    push_cast
    field_simp [hSC, hn2C, hne]
    rw [← hsq]; ring
  rw [IBall.Mem, IBall.center, ibInv]
  dsimp only
  have hsplit : x⁻¹ - (((reNum / (n2 : ℤ) : ℤ) : ℂ) + ((imNum / (n2 : ℤ) : ℤ) : ℂ) * I) / (SCALE : ℂ) =
      (a.center - x) / (x * a.center) +
      (((reNum : ℂ) / (n2 : ℂ) - ((reNum / (n2 : ℤ) : ℤ) : ℂ)) +
       ((imNum : ℂ) / (n2 : ℂ) - ((imNum / (n2 : ℤ) : ℤ) : ℂ)) * I) / (SCALE : ℂ) := by
    have h1 : x⁻¹ - a.center⁻¹ = (a.center - x) / (x * a.center) := by
      field_simp [hx_ne, hc_ne]
    rw [← h1, hc_inv]; ring
  change ‖x⁻¹ - (((reNum / (n2 : ℤ) : ℤ) : ℂ) + ((imNum / (n2 : ℤ) : ℤ) : ℂ) * I) / (SCALE : ℂ)‖ ≤ _
  rw [hsplit]
  have hpart1 : ‖(a.center - x) / (x * a.center)‖ ≤
      (((SCALE * SCALE * a.rad + denom - 1) / denom : ℕ) : ℝ) / SCALE := by
    rw [norm_div, norm_mul, norm_sub_rev]
    have hmul_lb : (denom : ℝ) / ((SCALE : ℝ) * (SCALE : ℝ)) ≤ ‖x‖ * ‖a.center‖ := by
      have : (denom : ℝ) / ((SCALE : ℝ) * (SCALE : ℝ)) =
          (((cLb - a.rad : ℕ) : ℝ) / SCALE) * ((cLb : ℝ) / SCALE) := by
        simp only [denom]; push_cast; ring
      rw [this]
      exact mul_le_mul hnorm_x hnorm_c (by positivity) (norm_nonneg _)
    calc ‖x - a.center‖ / (‖x‖ * ‖a.center‖)
        ≤ ((a.rad : ℝ) / SCALE) / ((denom : ℝ) / ((SCALE : ℝ) * (SCALE : ℝ))) :=
          div_le_div₀ (by positivity) hx (by positivity) hmul_lb
      _ = (((SCALE * SCALE * a.rad : ℕ) : ℝ) / (denom : ℝ)) / SCALE := by
          push_cast; field_simp [scale_pos.ne']
      _ ≤ (((SCALE * SCALE * a.rad + denom - 1) / denom : ℕ) : ℝ) / SCALE :=
          div_le_div_of_nonneg_right (nat_ceil_div_le _ _ hdenom_pos) scale_pos.le
  calc ‖_ + _‖ ≤ ‖(a.center - x) / (x * a.center)‖ + ‖_‖ := norm_add_le _ _
    _ ≤ (((SCALE * SCALE * a.rad + denom - 1) / denom : ℕ) : ℝ) / SCALE + 2 / SCALE :=
        add_le_add hpart1 (norm_ediv_err_le reNum imNum n2 n2 hn2_pos hn2_pos)
    _ = ((((SCALE * SCALE * a.rad + denom - 1) / denom + 2 : ℕ) : ℝ)) / SCALE := by push_cast; ring

def ibExpSmallAux (z : IBall) : ℕ → IBall × IBall × ℕ
  | 0 => (ibOne, ibOne, 1)
  | k + 1 =>
    let (acc, zp, fact) := ibExpSmallAux z k
    let zp' := ibMul zp z
    let fact' := fact * (k + 1)
    (ibAdd acc (ibDivNat zp' fact'), zp', fact')

def ibExpSmall (z : IBall) (D : ℕ) : IBall :=
  let (acc, _, _) := ibExpSmallAux z (D - 1)
  let denom := 2 ^ D * Nat.factorial D
  let tail := (2 * SCALE + denom - 1) / denom
  ⟨acc.re, acc.im, acc.rad + tail⟩

lemma ibExpSmallAux_spec {z : IBall} {w : ℂ} (hw : z.Mem w) :
    ∀ k : ℕ,
      (ibExpSmallAux z k).1.Mem (∑ m ∈ Finset.range (k + 1), w ^ m / (m.factorial : ℂ)) ∧
      (ibExpSmallAux z k).2.1.Mem (w ^ k) ∧
      (ibExpSmallAux z k).2.2 = k.factorial := by
  intro k
  induction k with
  | zero =>
    simp [ibExpSmallAux, ibOne_mem]
  | succ k ih =>
    obtain ⟨hacc, hzp, hfact⟩ := ih
    simp only [ibExpSmallAux]
    have hzp' : (ibMul (ibExpSmallAux z k).2.1 z).Mem (w ^ (k + 1)) := by
      rw [pow_succ]; exact ibMul_mem hzp hw
    have hfact' : (ibExpSmallAux z k).2.2 * (k + 1) = (k + 1).factorial := by
      rw [hfact, Nat.factorial_succ, mul_comm]
    refine ⟨?_, hzp', hfact'⟩
    rw [Finset.sum_range_succ, ← hfact']
    exact ibAdd_mem hacc (ibDivNat_mem (by rw [hfact']; exact Nat.factorial_pos _) hzp')

lemma ibExpSmall_mem {z : IBall} {w : ℂ} (hw : z.Mem w) {D : ℕ} (hD : 1 ≤ D)
    (hsmall : z.absUb + z.rad ≤ SCALE / 2) :
    (ibExpSmall z D).Mem (Complex.exp w) := by
  have hw_le : ‖w‖ ≤ 1 / 2 := by
    have h1 := z.norm_le hw
    have h2 : ((z.absUb + z.rad : ℕ) : ℝ) ≤ (SCALE : ℝ) / 2 := by
      have : (z.absUb + z.rad) * 2 ≤ SCALE := by omega
      have : ((z.absUb + z.rad : ℕ) : ℝ) * 2 ≤ (SCALE : ℝ) := by exact_mod_cast this
      linarith
    calc ‖w‖ ≤ ((z.absUb + z.rad : ℕ) : ℝ) / SCALE := h1
      _ ≤ ((SCALE : ℝ) / 2) / SCALE := div_le_div_of_nonneg_right h2 scale_pos.le
      _ = 1 / 2 := by field_simp [scale_pos.ne']
  have hcond : ‖w‖ / (D.succ : ℝ) ≤ 1 / 2 := by
    calc ‖w‖ / (D.succ : ℝ) ≤ ‖w‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) one_pos (by exact_mod_cast Nat.succ_pos D)
      _ = ‖w‖ := div_one _
      _ ≤ 1 / 2 := hw_le
  have hbound := Complex.exp_bound' (x := w) (n := D) hcond
  have htail_le : ‖w‖ ^ D / (D.factorial : ℝ) * 2 ≤
      (((2 * SCALE + 2 ^ D * D.factorial - 1) / (2 ^ D * D.factorial) : ℕ) : ℝ) / SCALE := by
    have hden_pos : 0 < 2 ^ D * D.factorial := Nat.mul_pos (by positivity) (Nat.factorial_pos D)
    have hwD : ‖w‖ ^ D ≤ (1 / 2 : ℝ) ^ D := pow_le_pow_left₀ (norm_nonneg _) hw_le D
    have hhalf : (1 / 2 : ℝ) ^ D * (2 : ℝ) ^ D = 1 := by rw [← mul_pow]; norm_num
    calc ‖w‖ ^ D / (D.factorial : ℝ) * 2
        ≤ (1 / 2 : ℝ) ^ D / (D.factorial : ℝ) * 2 := by gcongr
      _ = ((2 * SCALE : ℕ) : ℝ) / ((2 ^ D * D.factorial : ℕ) : ℝ) / SCALE := by
          push_cast; field_simp [scale_pos.ne']; linarith [hhalf]
      _ ≤ (((2 * SCALE + 2 ^ D * D.factorial - 1) / (2 ^ D * D.factorial) : ℕ) : ℝ) / SCALE :=
          div_le_div_of_nonneg_right (nat_ceil_div_le _ _ hden_pos) scale_pos.le
  have hacc := (ibExpSmallAux_spec hw (D - 1)).1
  rw [Nat.sub_add_cancel hD] at hacc
  rw [IBall.Mem, IBall.center, ibExpSmall]
  dsimp only
  set Ssum := ∑ m ∈ Finset.range D, w ^ m / (m.factorial : ℂ)
  have hsplit : Complex.exp w -
      (((ibExpSmallAux z (D - 1)).1.re : ℂ) + ((ibExpSmallAux z (D - 1)).1.im : ℂ) * I) / (SCALE : ℂ) =
      (Complex.exp w - Ssum) + (Ssum - (ibExpSmallAux z (D - 1)).1.center) := by
    simp only [IBall.center]; ring
  rw [hsplit]
  calc ‖(Complex.exp w - Ssum) + (Ssum - (ibExpSmallAux z (D - 1)).1.center)‖
      ≤ ‖Complex.exp w - Ssum‖ + ‖Ssum - (ibExpSmallAux z (D - 1)).1.center‖ := norm_add_le _ _
    _ ≤ (((2 * SCALE + 2 ^ D * D.factorial - 1) / (2 ^ D * D.factorial) : ℕ) : ℝ) / SCALE +
        ((ibExpSmallAux z (D - 1)).1.rad : ℝ) / SCALE := add_le_add (hbound.trans htail_le) hacc
    _ = ((((ibExpSmallAux z (D - 1)).1.rad + (2 * SCALE + 2 ^ D * D.factorial - 1) / (2 ^ D * D.factorial) : ℕ) : ℝ)) / SCALE := by
        push_cast; ring

def ibSqIter : ℕ → IBall → IBall
  | 0, a => a
  | k + 1, a => ibSqIter k (ibMul a a)

lemma ibSqIter_mem : ∀ (k : ℕ) {a : IBall} {x : ℂ}, a.Mem x →
    (ibSqIter k a).Mem (x ^ (2 ^ k))
  | 0, a, x, hx => by simpa [ibSqIter] using hx
  | k + 1, a, x, hx => by
    have hsq : (ibMul a a).Mem (x ^ 2) := by rw [sq]; exact ibMul_mem hx hx
    have h := ibSqIter_mem k hsq
    have hpow : (x ^ 2) ^ (2 ^ k) = x ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ']
    rw [hpow] at h
    exact h

def ibExp (z : IBall) (K D : ℕ) : IBall :=
  ibSqIter K (ibExpSmall (ibDivNat z (2 ^ K)) D)

lemma ibExp_mem {z : IBall} {w : ℂ} (hw : z.Mem w) {K D : ℕ} (hD : 1 ≤ D)
    (hsmall : (ibDivNat z (2 ^ K)).absUb + (ibDivNat z (2 ^ K)).rad ≤ SCALE / 2) :
    (ibExp z K D).Mem (Complex.exp w) := by
  have hdiv : (ibDivNat z (2 ^ K)).Mem (w / ((2 ^ K : ℕ) : ℂ)) :=
    ibDivNat_mem (by positivity) hw
  have hexp : (ibExpSmall (ibDivNat z (2 ^ K)) D).Mem (Complex.exp (w / ((2 ^ K : ℕ) : ℂ))) :=
    ibExpSmall_mem hdiv hD hsmall
  have hsq := ibSqIter_mem K hexp
  have heq : Complex.exp (w / ((2 ^ K : ℕ) : ℂ)) ^ (2 ^ K) = Complex.exp w := by
    rw [← Complex.exp_nat_mul]
    congr 1
    have hne : ((2 ^ K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
    field_simp [hne]
  rw [heq] at hsq
  exact hsq

/-! ### Section 4b: Strict List-based Jet Arithmetic & Kernel Verification -/

def logP_val : Fin 7 → ℤ
  | ⟨0, _⟩ => 12786308645202655232
  | ⟨1, _⟩ => 20265819725292941312
  | ⟨2, _⟩ => 29688889273197211648
  | ⟨3, _⟩ => 35895706510057369600
  | ⟨4, _⟩ => 44233360412869492736
  | ⟨5, _⟩ => 47314964359118725120
  | ⟨6, _⟩ => 52263561464023826432

def primeVal : Fin 7 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 7
  | ⟨4, _⟩ => 11
  | ⟨5, _⟩ => 13
  | ⟨6, _⟩ => 17

def logP_ball (i : Fin 7) : IBall := ⟨logP_val i, 0, 4096⟩

def checkLogP (i : Fin 7) : Bool :=
  let v := logP_val i
  let r : ℤ := 4096
  let bLo := ibExp ⟨v - r, 0, 0⟩ 3 22
  let bHi := ibExp ⟨v + r, 0, 0⟩ 3 22
  let pS : ℤ := (primeVal i : ℤ) * (SCALE : ℤ)
  decide ((ibDivNat ⟨v - r, 0, 0⟩ 8).absUb + (ibDivNat ⟨v - r, 0, 0⟩ 8).rad ≤ SCALE / 2) &&
  decide ((ibDivNat ⟨v + r, 0, 0⟩ 8).absUb + (ibDivNat ⟨v + r, 0, 0⟩ 8).rad ≤ SCALE / 2) &&
  decide (bLo.re + (bLo.rad : ℤ) ≤ pS) &&
  decide (pS ≤ bHi.re - (bHi.rad : ℤ))

lemma all_logs_ok : ∀ i : Fin 7, checkLogP i = true := by decide

-- Strict List-based Jet of length 11 (k = 0..10) so intermediate values are NEVER recomputed!
abbrev Jet := List IBall

def jetGet (J : Jet) (k : ℕ) : IBall := J.getD k ibZero
def jetZero : Jet := List.replicate 11 ibZero
def jetAdd (A B : Jet) : Jet := List.zipWith ibAdd A B
def jetScaleInt (c : ℤ) (A : Jet) : Jet := A.map (ibScaleInt c)
def jetDivNat (A : Jet) (d : ℕ) : Jet := A.map (fun x => ibDivNat x d)

def ibSumRange : ℕ → (ℕ → IBall) → IBall
  | 0, _ => ibZero
  | n + 1, f => ibAdd (ibSumRange n f) (f n)

def jetMul (A B : Jet) : Jet :=
  [ ibSumRange 1 (fun i => ibMul (jetGet A i) (jetGet B (0 - i)))
  , ibSumRange 2 (fun i => ibMul (jetGet A i) (jetGet B (1 - i)))
  , ibSumRange 3 (fun i => ibMul (jetGet A i) (jetGet B (2 - i)))
  , ibSumRange 4 (fun i => ibMul (jetGet A i) (jetGet B (3 - i)))
  , ibSumRange 5 (fun i => ibMul (jetGet A i) (jetGet B (4 - i)))
  , ibSumRange 6 (fun i => ibMul (jetGet A i) (jetGet B (5 - i)))
  , ibSumRange 7 (fun i => ibMul (jetGet A i) (jetGet B (6 - i)))
  , ibSumRange 8 (fun i => ibMul (jetGet A i) (jetGet B (7 - i)))
  , ibSumRange 9 (fun i => ibMul (jetGet A i) (jetGet B (8 - i)))
  , ibSumRange 10 (fun i => ibMul (jetGet A i) (jetGet B (9 - i)))
  , ibSumRange 11 (fun i => ibMul (jetGet A i) (jetGet B (10 - i))) ]

def jetMulLin (A : Jet) (a : IBall) : Jet :=
  [ ibMul a (jetGet A 0)
  , ibAdd (ibMul a (jetGet A 1)) (jetGet A 0)
  , ibAdd (ibMul a (jetGet A 2)) (jetGet A 1)
  , ibAdd (ibMul a (jetGet A 3)) (jetGet A 2)
  , ibAdd (ibMul a (jetGet A 4)) (jetGet A 3)
  , ibAdd (ibMul a (jetGet A 5)) (jetGet A 4)
  , ibAdd (ibMul a (jetGet A 6)) (jetGet A 5)
  , ibAdd (ibMul a (jetGet A 7)) (jetGet A 6)
  , ibAdd (ibMul a (jetGet A 8)) (jetGet A 7)
  , ibAdd (ibMul a (jetGet A 9)) (jetGet A 8)
  , ibAdd (ibMul a (jetGet A 10)) (jetGet A 9) ]

def logNatBall : ℕ → IBall
  | 1 => ibZero
  | 2 => logP_ball 0
  | 3 => logP_ball 1
  | 4 => ibScaleInt 2 (logP_ball 0)
  | 5 => logP_ball 2
  | 6 => ibAdd (logP_ball 0) (logP_ball 1)
  | 7 => logP_ball 3
  | 8 => ibScaleInt 3 (logP_ball 0)
  | 9 => ibScaleInt 2 (logP_ball 1)
  | 10 => ibAdd (logP_ball 0) (logP_ball 2)
  | 11 => logP_ball 4
  | 12 => ibAdd (ibScaleInt 2 (logP_ball 0)) (logP_ball 1)
  | 13 => logP_ball 5
  | 14 => ibAdd (logP_ball 0) (logP_ball 3)
  | 15 => ibAdd (logP_ball 1) (logP_ball 2)
  | 16 => ibScaleInt 4 (logP_ball 0)
  | 17 => logP_ball 6
  | 18 => ibAdd (logP_ball 0) (ibScaleInt 2 (logP_ball 1))
  | _ => ibZero

def cpowJetList (base negL : IBall) : Jet :=
  let rec go (k : ℕ) (cur : IBall) (fact : ℕ) : List IBall :=
    match k with
    | 0 => []
    | m + 1 =>
      let idx := 11 - (m + 1)
      let term := ibDivNat cur fact
      term :: go m (ibMul cur negL) (fact * (idx + 1))
  go 11 base 1

def invSubOneJetList (inv1 : IBall) : Jet :=
  let negInv1 := ibNeg inv1
  let rec go (k : ℕ) (cur : IBall) : List IBall :=
    match k with
    | 0 => []
    | m + 1 => cur :: go m (ibMul cur negInv1)
  go 11 inv1

def sum17Jet (cp : Fin 7 → IBall) : Jet :=
  let cp0 := cp 0; let cp1 := cp 1; let cp2 := cp 2; let cp3 := cp 3
  let cp4 := cp 4; let cp5 := cp 5; let cp6 := cp 6
  let c4 := ibMul cp0 cp0
  let c8 := ibMul c4 cp0
  let c9 := ibMul cp1 cp1
  let j1 := cpowJetList ibOne (ibNeg (logNatBall 1))
  let j2 := cpowJetList cp0 (ibNeg (logNatBall 2))
  let j3 := cpowJetList cp1 (ibNeg (logNatBall 3))
  let j4 := cpowJetList c4 (ibNeg (logNatBall 4))
  let j5 := cpowJetList cp2 (ibNeg (logNatBall 5))
  let j6 := cpowJetList (ibMul cp0 cp1) (ibNeg (logNatBall 6))
  let j7 := cpowJetList cp3 (ibNeg (logNatBall 7))
  let j8 := cpowJetList c8 (ibNeg (logNatBall 8))
  let j9 := cpowJetList c9 (ibNeg (logNatBall 9))
  let j10 := cpowJetList (ibMul cp0 cp2) (ibNeg (logNatBall 10))
  let j11 := cpowJetList cp4 (ibNeg (logNatBall 11))
  let j12 := cpowJetList (ibMul c4 cp1) (ibNeg (logNatBall 12))
  let j13 := cpowJetList cp5 (ibNeg (logNatBall 13))
  let j14 := cpowJetList (ibMul cp0 cp3) (ibNeg (logNatBall 14))
  let j15 := cpowJetList (ibMul cp1 cp2) (ibNeg (logNatBall 15))
  let j16 := cpowJetList (ibMul c4 c4) (ibNeg (logNatBall 16))
  let j17 := cpowJetList cp6 (ibNeg (logNatBall 17))
  [j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15, j16, j17].foldl jetAdd jetZero

def emMainJetOfCp (s : IBall) (cp : Fin 7 → IBall) : Jet :=
  let c18 := ibMul (cp 0) (ibMul (cp 1) (cp 1))
  let j18 := cpowJetList c18 (ibNeg (logNatBall 18))
  let sum17 := sum17Jet cp
  let half18 := jetDivNat j18 2
  let pole := jetMul (jetScaleInt 18 j18) (invSubOneJetList (ibInv (ibSub s ibOne)))
  let p0 : Jet := ibOne :: List.replicate 10 ibZero
  let p1 := jetMulLin p0 s
  let p2 := jetMulLin p1 (ibAdd s (ibConst 1 1 0 1))
  let p3 := jetMulLin p2 (ibAdd s (ibConst 2 1 0 1))
  let p4 := jetMulLin p3 (ibAdd s (ibConst 3 1 0 1))
  let p5 := jetMulLin p4 (ibAdd s (ibConst 4 1 0 1))
  let p6 := jetMulLin p5 (ibAdd s (ibConst 5 1 0 1))
  let p7 := jetMulLin p6 (ibAdd s (ibConst 6 1 0 1))
  let p8 := jetMulLin p7 (ibAdd s (ibConst 7 1 0 1))
  let p9 := jetMulLin p8 (ibAdd s (ibConst 8 1 0 1))
  let p10 := jetMulLin p9 (ibAdd s (ibConst 9 1 0 1))
  let p11 := jetMulLin p10 (ibAdd s (ibConst 10 1 0 1))
  let t2  := jetDivNat (jetMul p1 j18) (12 * 18 ^ 1)
  let t4  := jetDivNat (jetScaleInt (-1) (jetMul p3 j18)) (720 * 18 ^ 3)
  let t6  := jetDivNat (jetMul p5 j18) (30240 * 18 ^ 5)
  let t8  := jetDivNat (jetScaleInt (-1) (jetMul p7 j18)) (1209600 * 18 ^ 7)
  let t10 := jetDivNat (jetMul p9 j18) (47900160 * 18 ^ 9)
  let t12 := jetDivNat (jetScaleInt (-691) (jetMul p11 j18)) (1307674368000 * 18 ^ 11)
  [sum17, half18, pole, t2, t4, t6, t8, t10, t12].foldl jetAdd jetZero

def s0_ball : IBall := ibConst 76267016 100000000 579824402 100000000
def s0_refl_ball : IBall := ibSub ibOne s0_ball
def r_rad : ℕ := (SCALE + 99999) / 100000
def s_disk_ball : IBall := ⟨s0_ball.re, s0_ball.im, s0_ball.rad + r_rad⟩
def s_disk_refl_ball : IBall := ibSub ibOne s_disk_ball

def cp_s0 : Fin 7 → IBall
  | ⟨0, _⟩ => ⟨-6948882790686666690, 8362194959599224065, 71302⟩
  | ⟨1, _⟩ => ⟨7950493536652315786, -692136213535687480, 38514⟩
  | ⟨2, _⟩ => ⟨-5382212415734960341, -501256635967802409, 41021⟩
  | ⟨3, _⟩ => ⟨1184990855084638834, 4010647592662509736, 36815⟩
  | ⟨4, _⟩ => ⟨685755092039608143, -2882194480942867094, 29603⟩
  | ⟨5, _⟩ => ⟨-1749123894947201220, -1934814483773214101, 29527⟩
  | ⟨6, _⟩ => ⟨-1598502324198306057, 1401144202918619553, 26670⟩

def cp_s0_refl : Fin 7 → IBall
  | ⟨0, _⟩ => ⟨-10001339747358488831, -12035481867198994463, 94530⟩
  | ⟨1, _⟩ => ⟨14159408830084660270, 1232658019075016689, 62795⟩
  | ⟨2, _⟩ => ⟨-12535970442867072593, 1167500999108242919, 86743⟩
  | ⟨3, _⟩ => ⟨3293662336092068274, -11147528154001932159, 92387⟩
  | ⟨4, _⟩ => ⟨2416877327140732131, 10158014973950239797, 93178⟩
  | ⟨5, _⟩ => ⟨-6730075401289149508, 7444554042692977959, 101489⟩
  | ⟨6, _⟩ => ⟨-7081376773243630324, -6207078878968192041, 105067⟩

def cp_s_disk : Fin 7 → IBall
  | ⟨0, _⟩ => ⟨-6948882790686666690, 8362194959599224065, 293444067443388⟩
  | ⟨1, _⟩ => ⟨7950493536652315786, -692136213535687480, 252732747171710⟩
  | ⟨2, _⟩ => ⟨-5382212415734960341, -501256635967802409, 397204627191081⟩
  | ⟨3, _⟩ => ⟨1184990855084638834, 4010647592662509736, 433111086932138⟩
  | ⟨4, _⟩ => ⟨685755092039608143, -2882194480942867094, 429512380122147⟩
  | ⟨5, _⟩ => ⟨-1749123894947201220, -1934814483773214101, 460171447350892⟩
  | ⟨6, _⟩ => ⟨-1598502324198306057, 1401144202918619553, 460116798818377⟩

def cp_s_disk_refl : Fin 7 → IBall
  | ⟨0, _⟩ => ⟨-10001339747358488831, -12035481867198994463, 417575879830198⟩
  | ⟨1, _⟩ => ⟨14159408830084660270, 1232658019075016689, 442081012539248⟩
  | ⟨2, _⟩ => ⟨-12535970442867072593, 1167500999108242919, 901122528937077⟩
  | ⟨3, _⟩ => ⟨3293662336092068274, -11147528154001932159, 1166161302469526⟩
  | ⟨4, _⟩ => ⟨2416877327140732131, 10158014973950239797, 1455691825259262⟩
  | ⟨5, _⟩ => ⟨-6730075401289149508, 7444554042692977959, 1698052117142352⟩
  | ⟨6, _⟩ => ⟨-7081376773243630324, -6207078878968192041, 1946335886599264⟩

lemma cp_s0_eq : ∀ i : Fin 7, ibExp (ibNeg (ibMul s0_ball (logP_ball i))) 6 22 = cp_s0 i := by decide
lemma cp_s0_refl_eq : ∀ i : Fin 7, ibExp (ibNeg (ibMul s0_refl_ball (logP_ball i))) 6 22 = cp_s0_refl i := by decide
lemma cp_s_disk_eq : ∀ i : Fin 7, ibExp (ibNeg (ibMul s_disk_ball (logP_ball i))) 6 22 = cp_s_disk i := by decide
lemma cp_s_disk_refl_eq : ∀ i : Fin 7, ibExp (ibNeg (ibMul s_disk_refl_ball (logP_ball i))) 6 22 = cp_s_disk_refl i := by decide

def checkBanach : Bool :=
  let d1 := emMainJetOfCp s0_ball cp_s0
  let d2 := emMainJetOfCp s0_refl_ball cp_s0_refl
  let dd1 := emMainJetOfCp s_disk_ball cp_s_disk
  let dd2 := emMainJetOfCp s_disk_refl_ball cp_s_disk_refl
  let f0 := ibScaleInt (Nat.factorial 8) (ibSub (jetGet d1 8) (jetGet d2 8))
  let f1 := ibScaleInt (Nat.factorial 9) (ibAdd (jetGet d1 9) (jetGet d2 9))
  let f2 := ibScaleInt (Nat.factorial 10) (ibSub (jetGet dd1 10) (jetGet dd2 10))
  let cLb := max f1.re.natAbs f1.im.natAbs
  let f0Ub := f0.absUb + f0.rad + 600000000000
  let f1Err := f1.rad + 2500000000000
  let M2Ub := f2.absUb + f2.rad + 9000000000000
  decide (200000 * f0Ub ≤ cLb) &&
  decide (4 * f1Err ≤ cLb) &&
  decide (4 * M2Ub ≤ 100000 * cLb)

lemma banach_ok : checkBanach = true := by decide

/-! ### Section 4c: Soundness of Logs, Jets, and Remainder Bounds -/

lemma primeVal_pos (i : Fin 7) : 0 < primeVal i := by
  fin_cases i <;> decide

lemma logP_mem (i : Fin 7) : (logP_ball i).Mem (Real.log (primeVal i) : ℂ) := by
  have hok := all_logs_ok i
  unfold checkLogP at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hsmLo, hsmHi⟩, hLo⟩, hHi⟩ := hok
  set v := logP_val i
  set r : ℤ := 4096
  set bLo := ibExp ⟨v - r, 0, 0⟩ 3 22
  set bHi := ibExp ⟨v + r, 0, 0⟩ 3 22
  have hmemLo : (⟨v - r, 0, 0⟩ : IBall).Mem ((((v - r : ℤ) : ℝ) / (SCALE : ℝ) : ℝ) : ℂ) := by
    rw [IBall.Mem, IBall.center]
    have : ((((v - r : ℤ) : ℝ) / (SCALE : ℝ) : ℝ) : ℂ) = (((v - r : ℤ) : ℂ) + (0 : ℤ) * I) / (SCALE : ℂ) := by
      push_cast; simp
    rw [this, sub_self, norm_zero]; positivity
  have hmemHi : (⟨v + r, 0, 0⟩ : IBall).Mem ((((v + r : ℤ) : ℝ) / (SCALE : ℝ) : ℝ) : ℂ) := by
    rw [IBall.Mem, IBall.center]
    have : ((((v + r : ℤ) : ℝ) / (SCALE : ℝ) : ℝ) : ℂ) = (((v + r : ℤ) : ℂ) + (0 : ℤ) * I) / (SCALE : ℂ) := by
      push_cast; simp
    rw [this, sub_self, norm_zero]; positivity
  have hexpLo : bLo.Mem (Complex.exp ((((v - r : ℤ) : ℝ) / (SCALE : ℝ) : ℝ) : ℂ)) :=
    ibExp_mem hmemLo (K := 3) (D := 22) (by omega) hsmLo
  have hexpHi : bHi.Mem (Complex.exp ((((v + r : ℤ) : ℝ) / (SCALE : ℝ) : ℝ) : ℂ)) :=
    ibExp_mem hmemHi (K := 3) (D := 22) (by omega) hsmHi
  rw [← Complex.ofReal_exp] at hexpLo hexpHi
  have hre_le : ∀ (b : IBall) (y : ℝ), b.Mem (y : ℂ) →
      ((b.re - (b.rad : ℤ) : ℤ) : ℝ) / SCALE ≤ y ∧ y ≤ ((b.re + (b.rad : ℤ) : ℤ) : ℝ) / SCALE := by
    intro b y hb
    have h1 : |y - (b.re : ℝ) / SCALE| ≤ (b.rad : ℝ) / SCALE := by
      have hre : ((y : ℂ) - b.center).re = y - (b.re : ℝ) / SCALE := by
        rw [Complex.sub_re, Complex.ofReal_re]; simp [IBall.center]
      rw [← hre]
      exact (Complex.abs_re_le_norm _).trans hb
    have ⟨hl, hu⟩ := abs_le.mp h1
    push_cast
    constructor <;> linarith [sub_div (b.re : ℝ) (b.rad : ℝ) SCALE, add_div (b.re : ℝ) (b.rad : ℝ) SCALE]
  have hSpos : (0 : ℝ) < (SCALE : ℝ) := scale_pos
  have hexp_le_p : Real.exp (((v - r : ℤ) : ℝ) / SCALE) ≤ (primeVal i : ℝ) := by
    have h1 := (hre_le bLo _ hexpLo).2
    have h2 : ((bLo.re + (bLo.rad : ℤ) : ℤ) : ℝ) ≤ (primeVal i : ℝ) * (SCALE : ℝ) := by exact_mod_cast hLo
    calc Real.exp (((v - r : ℤ) : ℝ) / SCALE)
        ≤ ((bLo.re + (bLo.rad : ℤ) : ℤ) : ℝ) / SCALE := h1
      _ ≤ ((primeVal i : ℝ) * (SCALE : ℝ)) / SCALE := div_le_div_of_nonneg_right h2 hSpos.le
      _ = (primeVal i : ℝ) := by field_simp [hSpos.ne']
  have hp_le_exp : (primeVal i : ℝ) ≤ Real.exp (((v + r : ℤ) : ℝ) / SCALE) := by
    have h1 := (hre_le bHi _ hexpHi).1
    have h2 : (primeVal i : ℝ) * (SCALE : ℝ) ≤ ((bHi.re - (bHi.rad : ℤ) : ℤ) : ℝ) := by exact_mod_cast hHi
    calc (primeVal i : ℝ)
        = ((primeVal i : ℝ) * (SCALE : ℝ)) / SCALE := by field_simp [hSpos.ne']
      _ ≤ ((bHi.re - (bHi.rad : ℤ) : ℤ) : ℝ) / SCALE := div_le_div_of_nonneg_right h2 hSpos.le
      _ ≤ Real.exp (((v + r : ℤ) : ℝ) / SCALE) := h1
  have hp_pos : (0 : ℝ) < (primeVal i : ℝ) := Nat.cast_pos.mpr (primeVal_pos i)
  have hlog_lo : ((v - r : ℤ) : ℝ) / SCALE ≤ Real.log (primeVal i) := by
    have h := Real.log_le_log (Real.exp_pos _) hexp_le_p
    rwa [Real.log_exp] at h
  have hlog_hi : Real.log (primeVal i) ≤ ((v + r : ℤ) : ℝ) / SCALE := by
    have h := Real.log_le_log hp_pos hp_le_exp
    rwa [Real.log_exp] at h
  rw [IBall.Mem, IBall.center, logP_ball]
  dsimp only
  have hsub : (Real.log (primeVal i) : ℂ) - ((v : ℂ) + (0 : ℤ) * I) / (SCALE : ℂ) =
      ((Real.log (primeVal i) - (v : ℝ) / SCALE : ℝ) : ℂ) := by
    push_cast; simp
  rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  push_cast at hlog_lo hlog_hi
  constructor
  · have : ((v : ℝ) - (r : ℝ)) / SCALE = (v : ℝ) / SCALE - (4096 : ℝ) / SCALE := by simp [r, sub_div]
    linarith
  · have : ((v : ℝ) + (r : ℝ)) / SCALE = (v : ℝ) / SCALE + (4096 : ℝ) / SCALE := by simp [r, add_div]
    linarith

lemma log_18_le : Real.log 18 ≤ 29 / 10 := by
  have hbound : ∀ i : Fin 7, Real.log (primeVal i) ≤ ((logP_val i : ℝ) + 4096) / (SCALE : ℝ) := by
    intro i
    have hi := logP_mem i
    have hre : ((Real.log (primeVal i) : ℂ) - (logP_ball i).center).re =
        Real.log (primeVal i) - (logP_val i : ℝ) / SCALE := by
      rw [Complex.sub_re, Complex.ofReal_re]
      simp [IBall.center, logP_ball]
    have h1 : |Real.log (primeVal i) - (logP_val i : ℝ) / SCALE| ≤ (4096 : ℝ) / SCALE := by
      rw [← hre]; exact (Complex.abs_re_le_norm _).trans hi
    linarith [(abs_le.mp h1).2, add_div (logP_val i : ℝ) 4096 SCALE]
  have h2 : Real.log 2 ≤ ((logP_val 0 : ℝ) + 4096) / SCALE := by simpa [primeVal] using hbound 0
  have h3 : Real.log 3 ≤ ((logP_val 1 : ℝ) + 4096) / SCALE := by simpa [primeVal] using hbound 1
  have h18 : Real.log 18 = Real.log 2 + Real.log 3 + Real.log 3 := by
    have : (18 : ℝ) = (2 * 3) * 3 := by norm_num
    rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  rw [h18]
  have hnum : ((logP_val 0 : ℝ) + 4096) / SCALE + ((logP_val 1 : ℝ) + 4096) / SCALE +
      ((logP_val 1 : ℝ) + 4096) / SCALE ≤ 29 / 10 := by
    norm_num [logP_val, SCALE]
  linarith

lemma logNatBall_mem : ∀ n : ℕ, 1 ≤ n → n ≤ 18 → (logNatBall n).Mem (Real.log n : ℂ) := by
  intro n hn1 hn18
  have h0 : (logP_ball 0).Mem (Real.log 2 : ℂ) := by simpa [primeVal] using logP_mem 0
  have h1 : (logP_ball 1).Mem (Real.log 3 : ℂ) := by simpa [primeVal] using logP_mem 1
  have h2 : (logP_ball 2).Mem (Real.log 5 : ℂ) := by simpa [primeVal] using logP_mem 2
  have h3 : (logP_ball 3).Mem (Real.log 7 : ℂ) := by simpa [primeVal] using logP_mem 3
  have h4 : (logP_ball 4).Mem (Real.log 11 : ℂ) := by simpa [primeVal] using logP_mem 4
  have h5 : (logP_ball 5).Mem (Real.log 13 : ℂ) := by simpa [primeVal] using logP_mem 5
  have h6 : (logP_ball 6).Mem (Real.log 17 : ℂ) := by simpa [primeVal] using logP_mem 6
  interval_cases n <;> simp only [logNatBall]
  · simpa using ibZero_mem
  · exact h0
  · exact h1
  · have : (Real.log (4 : ℕ) : ℂ) = (2 : ℤ) * (Real.log 2 : ℂ) := by
      have : (4 : ℝ) = 2 * 2 := by norm_num
      push_cast; rw [this, Real.log_mul (by norm_num) (by norm_num)]; push_cast; ring
    rw [this]; exact ibScaleInt_mem 2 h0
  · exact h2
  · have : (Real.log (6 : ℕ) : ℂ) = (Real.log 2 : ℂ) + (Real.log 3 : ℂ) := by
      have : (6 : ℝ) = 2 * 3 := by norm_num
      push_cast; rw [this, Real.log_mul (by norm_num) (by norm_num)]; push_cast; ring
    rw [this]; exact ibAdd_mem h0 h1
  · exact h3
  · have : (Real.log (8 : ℕ) : ℂ) = (3 : ℤ) * (Real.log 2 : ℂ) := by
      have : (8 : ℝ) = (2 * 2) * 2 := by norm_num
      push_cast; rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]; push_cast; ring
    rw [this]; exact ibScaleInt_mem 3 h0
  · have : (Real.log (9 : ℕ) : ℂ) = (2 : ℤ) * (Real.log 3 : ℂ) := by
      have : (9 : ℝ) = 3 * 3 := by norm_num
      push_cast; rw [this, Real.log_mul (by norm_num) (by norm_num)]; push_cast; ring
    rw [this]; exact ibScaleInt_mem 2 h1
  · have : (Real.log (10 : ℕ) : ℂ) = (Real.log 2 : ℂ) + (Real.log 5 : ℂ) := by
      have : (10 : ℝ) = 2 * 5 := by norm_num
      push_cast; rw [this, Real.log_mul (by norm_num) (by norm_num)]; push_cast; ring
    rw [this]; exact ibAdd_mem h0 h2
  · exact h4
  · have : (Real.log (12 : ℕ) : ℂ) = (2 : ℤ) * (Real.log 2 : ℂ) + (Real.log 3 : ℂ) := by
      have : (12 : ℝ) = (2 * 2) * 3 := by norm_num
      push_cast; rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]; push_cast; ring
    rw [this]; exact ibAdd_mem (ibScaleInt_mem 2 h0) h1
  · exact h5
  · have : (Real.log (14 : ℕ) : ℂ) = (Real.log 2 : ℂ) + (Real.log 7 : ℂ) := by
      have : (14 : ℝ) = 2 * 7 := by norm_num
      push_cast; rw [this, Real.log_mul (by norm_num) (by norm_num)]; push_cast; ring
    rw [this]; exact ibAdd_mem h0 h3
  · have : (Real.log (15 : ℕ) : ℂ) = (Real.log 3 : ℂ) + (Real.log 5 : ℂ) := by
      have : (15 : ℝ) = 3 * 5 := by norm_num
      push_cast; rw [this, Real.log_mul (by norm_num) (by norm_num)]; push_cast; ring
    rw [this]; exact ibAdd_mem h1 h2
  · have : (Real.log (16 : ℕ) : ℂ) = (4 : ℤ) * (Real.log 2 : ℂ) := by
      have : (16 : ℝ) = ((2 * 2) * 2) * 2 := by norm_num
      push_cast
      rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
      push_cast; ring
    rw [this]; exact ibScaleInt_mem 4 h0
  · exact h6
  · have : (Real.log (18 : ℕ) : ℂ) = (Real.log 2 : ℂ) + (2 : ℤ) * (Real.log 3 : ℂ) := by
      have : (18 : ℝ) = 2 * (3 * 3) := by norm_num
      push_cast; rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]; push_cast; ring
    rw [this]; exact ibAdd_mem h0 (ibScaleInt_mem 2 h1)

/-! ### Jet Soundness -/

def Jet.Mem (J : Jet) (f : ℂ → ℂ) (s : ℂ) : Prop :=
  J.length = 11 ∧ ∀ k : ℕ, k < 11 → (jetGet J k).Mem (iteratedDeriv k f s / (k.factorial : ℂ))

lemma ibSumRange_mem (n : ℕ) (f : ℕ → IBall) (g : ℕ → ℂ) (h : ∀ i < n, (f i).Mem (g i)) :
    (ibSumRange n f).Mem (∑ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simpa [ibSumRange] using ibZero_mem
  | succ n ih =>
    rw [ibSumRange, Finset.sum_range_succ]
    exact ibAdd_mem (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

lemma jetGet_jetZero (k : ℕ) : jetGet jetZero k = ibZero := by
  simp only [jetGet, jetZero, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

lemma jetGet_jetAdd {A B : Jet} (hA : A.length = 11) (hB : B.length = 11) {k : ℕ} (hk : k < 11) :
    jetGet (jetAdd A B) k = ibAdd (jetGet A k) (jetGet B k) := by
  unfold jetGet jetAdd
  simp [List.getD_eq_getElem?_getD, hA, hB, hk]

lemma jetGet_jetScaleInt (c : ℤ) {A : Jet} (hA : A.length = 11) {k : ℕ} (hk : k < 11) :
    jetGet (jetScaleInt c A) k = ibScaleInt c (jetGet A k) := by
  unfold jetGet jetScaleInt
  simp [List.getD_eq_getElem?_getD, hA, hk]

lemma jetGet_jetDivNat {A : Jet} (d : ℕ) (hA : A.length = 11) {k : ℕ} (hk : k < 11) :
    jetGet (jetDivNat A d) k = ibDivNat (jetGet A k) d := by
  unfold jetGet jetDivNat
  simp [List.getD_eq_getElem?_getD, hA, hk]

lemma jetGet_jetMul (A B : Jet) {k : ℕ} (hk : k < 11) :
    jetGet (jetMul A B) k = ibSumRange (k + 1) (fun i => ibMul (jetGet A i) (jetGet B (k - i))) := by
  interval_cases k <;> rfl

lemma jetGet_jetMulLin_zero (A : Jet) (a : IBall) :
    jetGet (jetMulLin A a) 0 = ibMul a (jetGet A 0) := rfl

lemma jetGet_jetMulLin_succ (A : Jet) (a : IBall) {k : ℕ} (hk : k < 10) :
    jetGet (jetMulLin A a) (k + 1) = ibAdd (ibMul a (jetGet A (k + 1))) (jetGet A k) := by
  interval_cases k <;> rfl

lemma iteratedDeriv_const_mul_field (k : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    iteratedDeriv k (fun z => c * f z) = fun z => c * iteratedDeriv k f z := by
  induction k with
  | zero => ext z; simp
  | succ k ih =>
    ext z
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, iteratedDeriv_succ]

lemma iteratedDeriv_div_const_field (k : ℕ) (f : ℂ → ℂ) (c : ℂ) :
    iteratedDeriv k (fun z => f z / c) = fun z => iteratedDeriv k f z / c := by
  have h : (fun z => f z / c) = (fun z => c⁻¹ * f z) := by ext z; ring
  rw [h, iteratedDeriv_const_mul_field]
  ext z; ring

lemma iteratedDeriv_cpow_neg {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun z : ℂ => (n : ℂ) ^ (-z)) s = (-(Real.log n : ℂ)) ^ k * (n : ℂ) ^ (-s) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv k (fun z : ℂ => (n : ℂ) ^ (-z)) =
        fun z => (-(Real.log n : ℂ)) ^ k * (n : ℂ) ^ (-z) := funext ih
    rw [hfun, deriv_const_mul_field]
    have hd := cpow_exp_hasDerivAt (x := (n : ℝ)) (by exact_mod_cast hn) 0 s
    simp only [Complex.ofReal_natCast, add_zero] at hd
    rw [hd.deriv]; ring

lemma iteratedDeriv_inv_sub_one (k : ℕ) {s : ℂ} (hs : s ≠ 1) :
    iteratedDeriv k (fun z : ℂ => (z - 1)⁻¹) s =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) * (s - 1)⁻¹ ^ (k + 1) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun z : ℂ => (z - 1)⁻¹) =ᶠ[𝓝 s]
        (fun z : ℂ => (-1 : ℂ) ^ k * (k.factorial : ℂ) * (z - 1)⁻¹ ^ (k + 1)) := by
      filter_upwards [isOpen_ne.mem_nhds hs] with z hz using ih hz
    rw [hev.deriv_eq, deriv_const_mul_field]
    have hinv : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-(s - 1)⁻¹ ^ 2) s := by
      have h := ((hasDerivAt_id s).sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hs)
      refine h.congr_deriv ?_; simp only [id_eq]; field_simp [sub_ne_zero.mpr hs]
    have hpow : HasDerivAt (fun z : ℂ => (z - 1)⁻¹ ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * (s - 1)⁻¹ ^ k * (-(s - 1)⁻¹ ^ 2)) s :=
      hinv.pow (k + 1)
    rw [hpow.deriv, Nat.factorial_succ]
    push_cast
    ring

lemma iteratedDeriv_mul_div_factorial {f g : ℂ → ℂ} {s : ℂ} {k : ℕ}
    (hf : ContDiffAt ℂ k f s) (hg : ContDiffAt ℂ k g s) :
    iteratedDeriv k (fun z => f z * g z) s / (k.factorial : ℂ) =
      ∑ i ∈ Finset.range (k + 1),
        (iteratedDeriv i f s / (i.factorial : ℂ)) *
        (iteratedDeriv (k - i) g s / ((k - i).factorial : ℂ)) := by
  change iteratedDeriv k (f * g) s / (k.factorial : ℂ) = _
  rw [iteratedDeriv_mul hf hg, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hcomb : ((k.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((k - i).factorial : ℂ) = (k.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
  have h1 : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have h2 : ((k - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - i))
  have h3 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hch : ((k.choose i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hik).ne'
  rw [← hcomb]
  field_simp [h1, h2, h3, hch]

lemma analyticAt_iteratedDeriv {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f s) :
    ∀ k : ℕ, AnalyticAt ℂ (iteratedDeriv k f) s
  | 0 => by simpa using hf
  | k + 1 => by
    have h := (analyticAt_iteratedDeriv hf k).deriv
    have heq : deriv (iteratedDeriv k f) = iteratedDeriv (k + 1) f := by
      ext z; rw [iteratedDeriv_succ]
    rwa [heq] at h

lemma iteratedDeriv_mul_lin_succ {f : ℂ → ℂ} {s c : ℂ} (hf : AnalyticAt ℂ f s) :
    ∀ k : ℕ, ∀ᶠ z in 𝓝 s,
      iteratedDeriv (k + 1) (fun w => f w * (w + c)) z =
        (z + c) * iteratedDeriv (k + 1) f z + ((k + 1 : ℕ) : ℂ) * iteratedDeriv k f z := by
  intro k
  induction k with
  | zero =>
    have hana : ∀ᶠ z in 𝓝 s, AnalyticAt ℂ f z := hf.eventually_analyticAt
    filter_upwards [hana] with z hz
    rw [iteratedDeriv_one, iteratedDeriv_one, iteratedDeriv_zero]
    have hd : HasDerivAt (fun w => f w * (w + c)) (deriv f z * (z + c) + f z * 1) z :=
      hz.differentiableAt.hasDerivAt.mul ((hasDerivAt_id z).add_const c)
    rw [hd.deriv]; simp; ring
  | succ k ih =>
    have hana : ∀ᶠ z in 𝓝 s, AnalyticAt ℂ f z := hf.eventually_analyticAt
    have hopen := eventually_eventually_nhds.mpr (ih.and hana)
    filter_upwards [hopen] with z hz
    have heq : iteratedDeriv (k + 1) (fun w => f w * (w + c)) =ᶠ[𝓝 z]
        fun w => (w + c) * iteratedDeriv (k + 1) f w + ((k + 1 : ℕ) : ℂ) * iteratedDeriv k f w :=
      hz.mono fun w hw => hw.1
    have hfz : AnalyticAt ℂ f z := hz.self_of_nhds.2
    have hd1 : HasDerivAt (fun w => iteratedDeriv (k + 1) f w) (iteratedDeriv (k + 2) f z) z := by
      rw [iteratedDeriv_succ (n := k + 1)]
      exact (analyticAt_iteratedDeriv hfz (k + 1)).differentiableAt.hasDerivAt
    have hd0 : HasDerivAt (fun w => iteratedDeriv k f w) (iteratedDeriv (k + 1) f z) z := by
      rw [iteratedDeriv_succ (n := k)]
      exact (analyticAt_iteratedDeriv hfz k).differentiableAt.hasDerivAt
    have hd : HasDerivAt (fun w => (w + c) * iteratedDeriv (k + 1) f w + ((k + 1 : ℕ) : ℂ) * iteratedDeriv k f w)
        ((1 * iteratedDeriv (k + 1) f z + (z + c) * iteratedDeriv (k + 2) f z) +
         ((k + 1 : ℕ) : ℂ) * iteratedDeriv (k + 1) f z) z :=
      (((hasDerivAt_id z).add_const c).mul hd1).add (hd0.const_mul ((k + 1 : ℕ) : ℂ))
    rw [iteratedDeriv_succ, heq.deriv_eq, hd.deriv]
    push_cast; ring

lemma jetZero_mem (s : ℂ) : Jet.Mem jetZero (fun _ => 0) s := by
  refine ⟨by rfl, fun k _ => ?_⟩
  rw [jetGet_jetZero]
  have h0 : iteratedDeriv k (fun _ : ℂ => (0 : ℂ)) s = 0 := by
    cases k with
    | zero => simp
    | succ k => simp
  rw [h0, zero_div]
  exact ibZero_mem

lemma jetAdd_mem {A B : Jet} {f g : ℂ → ℂ} {s : ℂ}
    (hf : ContDiffAt ℂ 10 f s) (hg : ContDiffAt ℂ 10 g s)
    (hA : Jet.Mem A f s) (hB : Jet.Mem B g s) :
    Jet.Mem (jetAdd A B) (fun z => f z + g z) s := by
  refine ⟨by simp [jetAdd, hA.1, hB.1], fun k hk => ?_⟩
  rw [jetGet_jetAdd hA.1 hB.1 hk]
  have hle : (k : WithTop ℕ∞) ≤ 10 := by exact_mod_cast Nat.le_of_lt_succ hk
  change (ibAdd (jetGet A k) (jetGet B k)).Mem (iteratedDeriv k (f + g) s / (k.factorial : ℂ))
  rw [iteratedDeriv_add (hf.of_le hle) (hg.of_le hle), add_div]
  exact ibAdd_mem (hA.2 k hk) (hB.2 k hk)

lemma jetScaleInt_mem (c : ℤ) {A : Jet} {f : ℂ → ℂ} {s : ℂ} (hA : Jet.Mem A f s) :
    Jet.Mem (jetScaleInt c A) (fun z => (c : ℂ) * f z) s := by
  refine ⟨by simp [jetScaleInt, hA.1], fun k hk => ?_⟩
  rw [jetGet_jetScaleInt c hA.1 hk, iteratedDeriv_const_mul_field, mul_div_assoc]
  exact ibScaleInt_mem c (hA.2 k hk)

lemma jetDivNat_mem {d : ℕ} (hd : 0 < d) {A : Jet} {f : ℂ → ℂ} {s : ℂ} (hA : Jet.Mem A f s) :
    Jet.Mem (jetDivNat A d) (fun z => f z / (d : ℂ)) s := by
  refine ⟨by simp [jetDivNat, hA.1], fun k hk => ?_⟩
  rw [jetGet_jetDivNat d hA.1 hk, iteratedDeriv_div_const_field, div_right_comm]
  exact ibDivNat_mem hd (hA.2 k hk)

lemma jetMul_mem {A B : Jet} {f g : ℂ → ℂ} {s : ℂ}
    (hf : ContDiffAt ℂ 10 f s) (hg : ContDiffAt ℂ 10 g s)
    (hA : Jet.Mem A f s) (hB : Jet.Mem B g s) :
    Jet.Mem (jetMul A B) (fun z => f z * g z) s := by
  refine ⟨rfl, fun k hk => ?_⟩
  rw [jetGet_jetMul A B hk]
  have hle : (k : WithTop ℕ∞) ≤ 10 := by exact_mod_cast Nat.le_of_lt_succ hk
  rw [iteratedDeriv_mul_div_factorial (hf.of_le hle) (hg.of_le hle)]
  exact ibSumRange_mem (k + 1) _ _ fun i hi =>
    ibMul_mem (hA.2 i (by omega)) (hB.2 (k - i) (by omega))

lemma jetMulLin_mem {A : Jet} {a : IBall} {f : ℂ → ℂ} {s c : ℂ}
    (ha : a.Mem (s + c)) (hf : AnalyticAt ℂ f s) (hA : Jet.Mem A f s) :
    Jet.Mem (jetMulLin A a) (fun z => f z * (z + c)) s := by
  refine ⟨rfl, fun k hk => ?_⟩
  cases k with
  | zero =>
    rw [jetGet_jetMulLin_zero]
    have h0 := hA.2 0 (by omega)
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h0 ⊢
    rw [mul_comm]
    exact ibMul_mem ha h0
  | succ k =>
    rw [jetGet_jetMulLin_succ A a (by omega)]
    have hrec := (iteratedDeriv_mul_lin_succ (c := c) hf k).self_of_nhds
    rw [hrec, add_div, mul_div_assoc]
    have hsimp : ((k + 1 : ℕ) : ℂ) * iteratedDeriv k f s / ((k + 1).factorial : ℂ) =
        iteratedDeriv k f s / (k.factorial : ℂ) := by
      rw [Nat.factorial_succ]; push_cast
      have hk1 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      field_simp [hk1]
    rw [hsimp]
    exact ibAdd_mem (ibMul_mem ha (hA.2 (k + 1) hk)) (hA.2 k (by omega))

lemma cpowJetList_go_spec (negL : IBall) (b L : ℂ) :
    ∀ m k : ℕ, ∀ cur : IBall, ∀ fact : ℕ,
      m + k = 11 → fact = k.factorial → cur.Mem (b * L ^ k) → negL.Mem L →
      (cpowJetList.go negL m cur fact).length = m ∧
      ∀ j < m, (cpowJetList.go negL m cur fact).getD j ibZero |>.Mem (L ^ (k + j) * b / ((k + j).factorial : ℂ)) := by
  intro m
  induction m with
  | zero => intro k cur fact _ _ _ _; exact ⟨rfl, fun j hj => by omega⟩
  | succ m ih =>
    intro k cur fact hmk hfact hcur hL
    have hidx : 11 - (m + 1) = k := by omega
    unfold cpowJetList.go
    rw [hidx]
    have hcur' : (ibMul cur negL).Mem (b * L ^ (k + 1)) := by
      rw [pow_succ, ← mul_assoc]; exact ibMul_mem hcur hL
    have hfact' : fact * (k + 1) = (k + 1).factorial := by
      rw [hfact, Nat.factorial_succ, mul_comm]
    obtain ⟨hlen, hget⟩ := ih (k + 1) (ibMul cur negL) (fact * (k + 1)) (by omega) hfact' hcur' hL
    refine ⟨by simp [hlen], fun j hj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getD_cons_zero, add_zero]
      rw [hfact, mul_comm (L ^ k) b]
      exact ibDivNat_mem (Nat.factorial_pos k) hcur
    | succ j =>
      simp only [List.getD_cons_succ]
      have heq : k + (j + 1) = k + 1 + j := by omega
      rw [heq]
      exact hget j (by omega)

lemma cpowJetList_mem {n : ℕ} (hn : 1 ≤ n) {base negL : IBall} {s : ℂ}
    (hbase : base.Mem ((n : ℂ) ^ (-s))) (hnegL : negL.Mem (-(Real.log n : ℂ))) :
    Jet.Mem (cpowJetList base negL) (fun z : ℂ => (n : ℂ) ^ (-z)) s := by
  obtain ⟨hlen, hget⟩ := cpowJetList_go_spec negL ((n : ℂ) ^ (-s)) (-(Real.log n : ℂ))
    11 0 base 1 rfl rfl (by simpa using hbase) hnegL
  refine ⟨hlen, fun k hk => ?_⟩
  rw [iteratedDeriv_cpow_neg hn k s]
  simpa [jetGet, cpowJetList] using hget k hk

lemma invSubOneJetList_go_spec (inv1 : IBall) (u : ℂ) (hu : inv1.Mem u) :
    ∀ m k : ℕ, ∀ cur : IBall,
      cur.Mem (u * (-u) ^ k) →
      (invSubOneJetList.go (ibNeg inv1) m cur).length = m ∧
      ∀ j < m, (invSubOneJetList.go (ibNeg inv1) m cur).getD j ibZero |>.Mem (u * (-u) ^ (k + j)) := by
  intro m
  induction m with
  | zero => intro k cur _; exact ⟨rfl, fun j hj => by omega⟩
  | succ m ih =>
    intro k cur hcur
    unfold invSubOneJetList.go
    have hcur' : (ibMul cur (ibNeg inv1)).Mem (u * (-u) ^ (k + 1)) := by
      rw [pow_succ, ← mul_assoc]; exact ibMul_mem hcur (ibNeg_mem hu)
    obtain ⟨hlen, hget⟩ := ih (k + 1) (ibMul cur (ibNeg inv1)) hcur'
    refine ⟨by simp [hlen], fun j hj => ?_⟩
    cases j with
    | zero => simpa using hcur
    | succ j =>
      simp only [List.getD_cons_succ]
      have heq : k + (j + 1) = k + 1 + j := by omega
      rw [heq]
      exact hget j (by omega)

lemma invSubOneJetList_mem {inv1 : IBall} {s : ℂ} (hs : s ≠ 1) (hinv : inv1.Mem (s - 1)⁻¹) :
    Jet.Mem (invSubOneJetList inv1) (fun z : ℂ => (z - 1)⁻¹) s := by
  obtain ⟨hlen, hget⟩ := invSubOneJetList_go_spec inv1 (s - 1)⁻¹ hinv 11 0 inv1 (by simpa using hinv)
  refine ⟨hlen, fun k hk => ?_⟩
  rw [iteratedDeriv_inv_sub_one k hs]
  have hsimp : (-1 : ℂ) ^ k * (k.factorial : ℂ) * (s - 1)⁻¹ ^ (k + 1) / (k.factorial : ℂ) =
      (s - 1)⁻¹ * (-(s - 1)⁻¹) ^ k := by
    have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    rw [neg_eq_neg_one_mul, mul_pow, pow_succ']
    field_simp [hk0]
    rw [one_pow, mul_one, ← mul_pow]
    simp
  rw [hsimp]
  simpa [jetGet, invSubOneJetList] using hget k hk

lemma foldl_jetAdd_mem (s : ℂ) :
    ∀ (L : List (Jet × (ℂ → ℂ))) (accJ : Jet) (accF : ℂ → ℂ),
      ContDiffAt ℂ 10 accF s → Jet.Mem accJ accF s →
      (∀ p ∈ L, ContDiffAt ℂ 10 p.2 s ∧ Jet.Mem p.1 p.2 s) →
      Jet.Mem ((L.map Prod.fst).foldl jetAdd accJ) (fun z => accF z + (L.map (fun p => p.2 z)).sum) s := by
  intro L
  induction L with
  | nil =>
    intro accJ accF _ hacc _
    simpa using hacc
  | cons p ps ih =>
    intro accJ accF hacc_cd hacc_m hall
    have hp := hall p List.mem_cons_self
    have hps : ∀ q ∈ ps, ContDiffAt ℂ 10 q.2 s ∧ Jet.Mem q.1 q.2 s :=
      fun q hq => hall q (List.mem_cons_of_mem p hq)
    have hstep := ih (jetAdd accJ p.1) (fun z => accF z + p.2 z)
      (hacc_cd.add hp.1) (jetAdd_mem hacc_cd hp.1 hacc_m hp.2) hps
    have hfun : (fun z => accF z + (List.map (fun p => p.2 z) (p :: ps)).sum) =
        (fun z => (accF z + p.2 z) + (List.map (fun q => q.2 z) ps).sum) := by
      ext z; simp [add_assoc]
    rw [hfun]
    simpa [List.map_cons, List.foldl_cons] using hstep

lemma cpow_mul_nat {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (s : ℂ) :
    ((a * b : ℕ) : ℂ) ^ (-s) = (a : ℂ) ^ (-s) * (b : ℂ) ^ (-s) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hab0 : (0 : ℝ) < (a * b : ℕ) := by exact_mod_cast Nat.mul_pos ha hb
  rw [← Complex.ofReal_natCast (a * b), ← Complex.ofReal_natCast a, ← Complex.ofReal_natCast b,
    ofReal_cpow_eq_exp hab0, ofReal_cpow_eq_exp ha0, ofReal_cpow_eq_exp hb0, ← Complex.exp_add]
  congr 1
  push_cast
  rw [Real.log_mul ha0.ne' hb0.ne']
  push_cast; ring

lemma analyticAt_cpow_neg {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (n : ℂ) ^ (-z)) s := by
  have hdiff : Differentiable ℂ (fun z : ℂ => (n : ℂ) ^ (-z)) := fun z => by
    have hd := cpow_exp_hasDerivAt (x := (n : ℝ)) (by exact_mod_cast hn) 0 z
    simp only [Complex.ofReal_natCast, add_zero] at hd
    exact hd.differentiableAt
  exact (hdiff.differentiableOn.analyticOnNhd isOpen_univ) s (mem_univ s)

lemma analyticAt_rising (k : ℕ) (s : ℂ) : AnalyticAt ℂ (fun z => rising z k) s :=
  ((differentiable_rising k).differentiableOn.analyticOnNhd isOpen_univ) s (mem_univ s)

lemma p0_jet_mem (z : ℂ) :
    Jet.Mem (ibOne :: List.replicate 10 ibZero) (fun w : ℂ => rising w 0) z := by
  refine ⟨rfl, fun k hk => ?_⟩
  cases k with
  | zero => simpa [jetGet, rising] using ibOne_mem
  | succ k =>
    have hk10 : k < 10 := by omega
    have hget : jetGet (ibOne :: List.replicate 10 ibZero) (k + 1) = ibZero := by
      simp only [jetGet, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_replicate, hk10, ↓reduceIte, Option.getD_some]
    rw [hget]
    have h0 : iteratedDeriv (k + 1) (fun w : ℂ => rising w 0) z = 0 := by
      rw [iteratedDeriv_succ']; simp [rising, deriv_const']
    rw [h0, zero_div]; exact ibZero_mem

lemma rising_step_jet_mem {sb : IBall} {z : ℂ} (hz : sb.Mem z) (k : ℕ) {P : Jet}
    (hP : Jet.Mem P (fun w => rising w k) z) :
    Jet.Mem (jetMulLin P (ibAdd sb (ibConst k 1 0 1))) (fun w => rising w (k + 1)) z := by
  have hconst : (ibConst k 1 0 1).Mem (k : ℂ) := by
    simpa using ibConst_mem (rn := (k : ℤ)) (rd := 1) (in_ := 0) (id_ := 1) (by omega) (by omega)
  exact jetMulLin_mem (ibAdd_mem hz hconst) (analyticAt_rising k z) hP

lemma sum17_jet_mem {cp : Fin 7 → IBall} {z : ℂ}
    (hcp : ∀ i : Fin 7, (cp i).Mem ((primeVal i : ℂ) ^ (-z))) :
    Jet.Mem (sum17Jet cp)
      (fun w : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-w)) z := by
  have hc2 : (cp 0).Mem ((2 : ℂ) ^ (-z)) := by simpa [primeVal] using hcp 0
  have hc3 : (cp 1).Mem ((3 : ℂ) ^ (-z)) := by simpa [primeVal] using hcp 1
  have hc5 : (cp 2).Mem ((5 : ℂ) ^ (-z)) := by simpa [primeVal] using hcp 2
  have hc7 : (cp 3).Mem ((7 : ℂ) ^ (-z)) := by simpa [primeVal] using hcp 3
  have hc11 : (cp 4).Mem ((11 : ℂ) ^ (-z)) := by simpa [primeVal] using hcp 4
  have hc13 : (cp 5).Mem ((13 : ℂ) ^ (-z)) := by simpa [primeVal] using hcp 5
  have hc17 : (cp 6).Mem ((17 : ℂ) ^ (-z)) := by simpa [primeVal] using hcp 6
  have hc1 : ibOne.Mem (((1 : ℕ) : ℂ) ^ (-z)) := by simpa using ibOne_mem
  have hc4 : (ibMul (cp 0) (cp 0)).Mem ((4 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 2) (b := 2) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc2 hc2
  have hc6 : (ibMul (cp 0) (cp 1)).Mem ((6 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 2) (b := 3) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc2 hc3
  have hc8 : (ibMul (ibMul (cp 0) (cp 0)) (cp 0)).Mem ((8 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 4) (b := 2) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc4 hc2
  have hc9 : (ibMul (cp 1) (cp 1)).Mem ((9 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 3) (b := 3) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc3 hc3
  have hc10 : (ibMul (cp 0) (cp 2)).Mem ((10 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 2) (b := 5) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc2 hc5
  have hc12 : (ibMul (ibMul (cp 0) (cp 0)) (cp 1)).Mem ((12 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 4) (b := 3) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc4 hc3
  have hc14 : (ibMul (cp 0) (cp 3)).Mem ((14 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 2) (b := 7) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc2 hc7
  have hc15 : (ibMul (cp 1) (cp 2)).Mem ((15 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 3) (b := 5) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc3 hc5
  have hc16 : (ibMul (ibMul (cp 0) (cp 0)) (ibMul (cp 0) (cp 0))).Mem ((16 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 4) (b := 4) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc4 hc4
  have hJ : ∀ n : ℕ, 1 ≤ n → n ≤ 18 → ∀ b : IBall, b.Mem ((n : ℂ) ^ (-z)) →
      (cpowJetList b (ibNeg (logNatBall n))).Mem (fun w : ℂ => (n : ℂ) ^ (-w)) z :=
    fun n hn1 hn18 b hb => cpowJetList_mem hn1 hb (ibNeg_mem (logNatBall_mem n hn1 hn18))
  have hcd : ∀ n : ℕ, 1 ≤ n → ContDiffAt ℂ 10 (fun w : ℂ => (n : ℂ) ^ (-w)) z :=
    fun n hn => (analyticAt_cpow_neg hn z).contDiffAt.of_le le_top
  let c4 := ibMul (cp 0) (cp 0)
  let pairs : List (Jet × (ℂ → ℂ)) :=
    [(cpowJetList ibOne (ibNeg (logNatBall 1)), fun w => (1 : ℂ) ^ (-w)),
     (cpowJetList (cp 0) (ibNeg (logNatBall 2)), fun w => (2 : ℂ) ^ (-w)),
     (cpowJetList (cp 1) (ibNeg (logNatBall 3)), fun w => (3 : ℂ) ^ (-w)),
     (cpowJetList c4 (ibNeg (logNatBall 4)), fun w => (4 : ℂ) ^ (-w)),
     (cpowJetList (cp 2) (ibNeg (logNatBall 5)), fun w => (5 : ℂ) ^ (-w)),
     (cpowJetList (ibMul (cp 0) (cp 1)) (ibNeg (logNatBall 6)), fun w => (6 : ℂ) ^ (-w)),
     (cpowJetList (cp 3) (ibNeg (logNatBall 7)), fun w => (7 : ℂ) ^ (-w)),
     (cpowJetList (ibMul c4 (cp 0)) (ibNeg (logNatBall 8)), fun w => (8 : ℂ) ^ (-w)),
     (cpowJetList (ibMul (cp 1) (cp 1)) (ibNeg (logNatBall 9)), fun w => (9 : ℂ) ^ (-w)),
     (cpowJetList (ibMul (cp 0) (cp 2)) (ibNeg (logNatBall 10)), fun w => (10 : ℂ) ^ (-w)),
     (cpowJetList (cp 4) (ibNeg (logNatBall 11)), fun w => (11 : ℂ) ^ (-w)),
     (cpowJetList (ibMul c4 (cp 1)) (ibNeg (logNatBall 12)), fun w => (12 : ℂ) ^ (-w)),
     (cpowJetList (cp 5) (ibNeg (logNatBall 13)), fun w => (13 : ℂ) ^ (-w)),
     (cpowJetList (ibMul (cp 0) (cp 3)) (ibNeg (logNatBall 14)), fun w => (14 : ℂ) ^ (-w)),
     (cpowJetList (ibMul (cp 1) (cp 2)) (ibNeg (logNatBall 15)), fun w => (15 : ℂ) ^ (-w)),
     (cpowJetList (ibMul c4 c4) (ibNeg (logNatBall 16)), fun w => (16 : ℂ) ^ (-w)),
     (cpowJetList (cp 6) (ibNeg (logNatBall 17)), fun w => (17 : ℂ) ^ (-w))]
  have hfold := foldl_jetAdd_mem z pairs jetZero (fun _ => 0) contDiffAt_const (jetZero_mem z) (by
    intro p hp
    simp only [pairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by simpa using hcd 1 (by omega), by simpa using hJ 1 (by omega) (by omega) _ hc1⟩
    · exact ⟨by simpa using hcd 2 (by omega), by simpa using hJ 2 (by omega) (by omega) _ hc2⟩
    · exact ⟨by simpa using hcd 3 (by omega), by simpa using hJ 3 (by omega) (by omega) _ hc3⟩
    · exact ⟨by simpa using hcd 4 (by omega), by simpa using hJ 4 (by omega) (by omega) _ hc4⟩
    · exact ⟨by simpa using hcd 5 (by omega), by simpa using hJ 5 (by omega) (by omega) _ hc5⟩
    · exact ⟨by simpa using hcd 6 (by omega), by simpa using hJ 6 (by omega) (by omega) _ hc6⟩
    · exact ⟨by simpa using hcd 7 (by omega), by simpa using hJ 7 (by omega) (by omega) _ hc7⟩
    · exact ⟨by simpa using hcd 8 (by omega), by simpa using hJ 8 (by omega) (by omega) _ hc8⟩
    · exact ⟨by simpa using hcd 9 (by omega), by simpa using hJ 9 (by omega) (by omega) _ hc9⟩
    · exact ⟨by simpa using hcd 10 (by omega), by simpa using hJ 10 (by omega) (by omega) _ hc10⟩
    · exact ⟨by simpa using hcd 11 (by omega), by simpa using hJ 11 (by omega) (by omega) _ hc11⟩
    · exact ⟨by simpa using hcd 12 (by omega), by simpa using hJ 12 (by omega) (by omega) _ hc12⟩
    · exact ⟨by simpa using hcd 13 (by omega), by simpa using hJ 13 (by omega) (by omega) _ hc13⟩
    · exact ⟨by simpa using hcd 14 (by omega), by simpa using hJ 14 (by omega) (by omega) _ hc14⟩
    · exact ⟨by simpa using hcd 15 (by omega), by simpa using hJ 15 (by omega) (by omega) _ hc15⟩
    · exact ⟨by simpa using hcd 16 (by omega), by simpa using hJ 16 (by omega) (by omega) _ hc16⟩
    · exact ⟨by simpa using hcd 17 (by omega), by simpa using hJ 17 (by omega) (by omega) _ hc17⟩)
  have hfun : (fun w : ℂ => (0 : ℂ) + (List.map (fun p => p.2 w) pairs).sum) =
      (fun w : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-w)) := by
    ext w
    rw [show Finset.Icc (1 : ℕ) 17 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} by decide]
    simp [pairs]
  rw [hfun] at hfold
  exact hfold

lemma bernoulli_term_jet_mem {P j18 : Jet} {z : ℂ} {k d : ℕ} (c : ℤ) (hd : 0 < d)
    (hP : Jet.Mem P (fun w => rising w k) z)
    (hj18 : Jet.Mem j18 (fun w : ℂ => (18 : ℂ) ^ (-w)) z) :
    Jet.Mem (jetDivNat (jetScaleInt c (jetMul P j18)) d)
      (fun w => (c : ℂ) * (rising w k * (18 : ℂ) ^ (-w)) / (d : ℂ)) z := by
  have hr : ContDiffAt ℂ 10 (fun w => rising w k) z := (analyticAt_rising k z).contDiffAt.of_le le_top
  have h18 : ContDiffAt ℂ 10 (fun w : ℂ => (18 : ℂ) ^ (-w)) z := by
    simpa using (analyticAt_cpow_neg (n := 18) (by omega) z).contDiffAt.of_le le_top
  exact jetDivNat_mem hd (jetScaleInt_mem c (jetMul_mem hr h18 hP hj18))

lemma bernoulli_term_pos_jet_mem {P j18 : Jet} {z : ℂ} {k d : ℕ} (hd : 0 < d)
    (hP : Jet.Mem P (fun w => rising w k) z)
    (hj18 : Jet.Mem j18 (fun w : ℂ => (18 : ℂ) ^ (-w)) z) :
    Jet.Mem (jetDivNat (jetMul P j18) d)
      (fun w => (rising w k * (18 : ℂ) ^ (-w)) / (d : ℂ)) z := by
  have hr : ContDiffAt ℂ 10 (fun w => rising w k) z := (analyticAt_rising k z).contDiffAt.of_le le_top
  have h18 : ContDiffAt ℂ 10 (fun w : ℂ => (18 : ℂ) ^ (-w)) z := by
    simpa using (analyticAt_cpow_neg (n := 18) (by omega) z).contDiffAt.of_le le_top
  exact jetDivNat_mem hd (jetMul_mem hr h18 hP hj18)

lemma emMain_combine_mem {z : ℂ} {jSum17 jHalf jPole j2 j4 j6 j8 j10 j12 : Jet}
    (hz1 : z ≠ 1)
    (hsum17 : jSum17.Mem (fun w => ∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-w)) z)
    (hhalf : jHalf.Mem (fun w => (1 / 2 : ℂ) * (18 : ℂ) ^ (-w)) z)
    (hpole : jPole.Mem (fun w => (18 : ℂ) * (18 : ℂ) ^ (-w) * (w - 1)⁻¹) z)
    (ht2 : j2.Mem (fun w => (rising w 1 * (18 : ℂ) ^ (-w)) / ((12 * 18 ^ 1 : ℕ) : ℂ)) z)
    (ht4 : j4.Mem (fun w => ((-1 : ℤ) : ℂ) * (rising w 3 * (18 : ℂ) ^ (-w)) / ((720 * 18 ^ 3 : ℕ) : ℂ)) z)
    (ht6 : j6.Mem (fun w => (rising w 5 * (18 : ℂ) ^ (-w)) / ((30240 * 18 ^ 5 : ℕ) : ℂ)) z)
    (ht8 : j8.Mem (fun w => ((-1 : ℤ) : ℂ) * (rising w 7 * (18 : ℂ) ^ (-w)) / ((1209600 * 18 ^ 7 : ℕ) : ℂ)) z)
    (ht10 : j10.Mem (fun w => (rising w 9 * (18 : ℂ) ^ (-w)) / ((47900160 * 18 ^ 9 : ℕ) : ℂ)) z)
    (ht12 : j12.Mem (fun w => ((-691 : ℤ) : ℂ) * (rising w 11 * (18 : ℂ) ^ (-w)) / ((1307674368000 * 18 ^ 11 : ℕ) : ℂ)) z) :
    ([jSum17, jHalf, jPole, j2, j4, j6, j8, j10, j12].foldl jetAdd jetZero).Mem emMain z := by
  have h18_cd : ContDiffAt ℂ 10 (fun w : ℂ => (18 : ℂ) ^ (-w)) z := by
    simpa using (analyticAt_cpow_neg (n := 18) (by omega) z).contDiffAt.of_le le_top
  have hr_cd : ∀ k, ContDiffAt ℂ 10 (fun w => rising w k) z :=
    fun k => (analyticAt_rising k z).contDiffAt.of_le le_top
  have hinv_ana : AnalyticAt ℂ (fun w : ℂ => (w - 1)⁻¹) z := by
    have hdiff : DifferentiableOn ℂ (fun w : ℂ => (w - 1)⁻¹) {w : ℂ | w ≠ 1} := fun w hw =>
      ((differentiableAt_id.sub (differentiableAt_const (1 : ℂ))).inv (sub_ne_zero.mpr hw)).differentiableWithinAt
    exact (hdiff.analyticOnNhd isOpen_ne) z hz1
  let fsum17 : ℂ → ℂ := fun w => ∑ n ∈ Finset.Icc (1 : ℕ) 17, (n : ℂ) ^ (-w)
  let fhalf : ℂ → ℂ := fun w => (1 / 2 : ℂ) * (18 : ℂ) ^ (-w)
  let fpole : ℂ → ℂ := fun w => (18 : ℂ) * (18 : ℂ) ^ (-w) * (w - 1)⁻¹
  let ft2 : ℂ → ℂ := fun w => (rising w 1 * (18 : ℂ) ^ (-w)) / ((12 * 18 ^ 1 : ℕ) : ℂ)
  let ft4 : ℂ → ℂ := fun w => ((-1 : ℤ) : ℂ) * (rising w 3 * (18 : ℂ) ^ (-w)) / ((720 * 18 ^ 3 : ℕ) : ℂ)
  let ft6 : ℂ → ℂ := fun w => (rising w 5 * (18 : ℂ) ^ (-w)) / ((30240 * 18 ^ 5 : ℕ) : ℂ)
  let ft8 : ℂ → ℂ := fun w => ((-1 : ℤ) : ℂ) * (rising w 7 * (18 : ℂ) ^ (-w)) / ((1209600 * 18 ^ 7 : ℕ) : ℂ)
  let ft10 : ℂ → ℂ := fun w => (rising w 9 * (18 : ℂ) ^ (-w)) / ((47900160 * 18 ^ 9 : ℕ) : ℂ)
  let ft12 : ℂ → ℂ := fun w => ((-691 : ℤ) : ℂ) * (rising w 11 * (18 : ℂ) ^ (-w)) / ((1307674368000 * 18 ^ 11 : ℕ) : ℂ)
  let parts : List (Jet × (ℂ → ℂ)) :=
    [(jSum17, fsum17), (jHalf, fhalf), (jPole, fpole), (j2, ft2), (j4, ft4),
     (j6, ft6), (j8, ft8), (j10, ft10), (j12, ft12)]
  have hfold := foldl_jetAdd_mem z parts jetZero (fun _ => 0) contDiffAt_const (jetZero_mem z) (by
    intro p hp
    simp only [parts, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ContDiffAt.sum fun n hn => (analyticAt_cpow_neg (Finset.mem_Icc.mp hn).1 z).contDiffAt.of_le le_top, hsum17⟩
    · exact ⟨contDiffAt_const.mul h18_cd, hhalf⟩
    · exact ⟨(contDiffAt_const.mul h18_cd).mul (hinv_ana.contDiffAt.of_le le_top), hpole⟩
    · exact ⟨((hr_cd 1).mul h18_cd).div_const _, ht2⟩
    · exact ⟨(contDiffAt_const.mul ((hr_cd 3).mul h18_cd)).div_const _, ht4⟩
    · exact ⟨((hr_cd 5).mul h18_cd).div_const _, ht6⟩
    · exact ⟨(contDiffAt_const.mul ((hr_cd 7).mul h18_cd)).div_const _, ht8⟩
    · exact ⟨((hr_cd 9).mul h18_cd).div_const _, ht10⟩
    · exact ⟨(contDiffAt_const.mul ((hr_cd 11).mul h18_cd)).div_const _, ht12⟩)
  have hfun : (fun w : ℂ => (0 : ℂ) + (List.map (fun p => p.2 w) parts).sum) = emMain := by
    ext w
    simp only [parts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add]
    simp only [fsum17, fhalf, fpole, ft2, ft4, ft6, ft8, ft10, ft12, emMain]
    push_cast
    ring
  rw [hfun] at hfold
  exact hfold

lemma emMainJetOfCp_mem {sb : IBall} {cp : Fin 7 → IBall} {z : ℂ}
    (hz : sb.Mem z) (hz1 : z ≠ 1)
    (hinv_ok : (ibSub sb ibOne).rad < max (ibSub sb ibOne).re.natAbs (ibSub sb ibOne).im.natAbs)
    (hcp : ∀ i : Fin 7, (cp i).Mem ((primeVal i : ℂ) ^ (-z))) :
    (emMainJetOfCp sb cp).Mem emMain z := by
  unfold emMainJetOfCp
  extract_lets c18 j18 sum17 half18 pole p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 t2 t4 t6 t8 t10 t12
  have hc2 : (cp 0).Mem ((2 : ℂ) ^ (-z)) := by simpa [primeVal] using hcp 0
  have hc3 : (cp 1).Mem ((3 : ℂ) ^ (-z)) := by simpa [primeVal] using hcp 1
  have hc9 : (ibMul (cp 1) (cp 1)).Mem ((9 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 3) (b := 3) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc3 hc3
  have hc18 : c18.Mem ((18 : ℂ) ^ (-z)) := by
    have h := cpow_mul_nat (a := 2) (b := 9) (by omega) (by omega) z; norm_num at h; rw [h]; exact ibMul_mem hc2 hc9
  have hj18 : Jet.Mem j18 (fun w : ℂ => (18 : ℂ) ^ (-w)) z := by
    simpa using cpowJetList_mem (n := 18) (by omega) (by simpa using hc18)
      (ibNeg_mem (logNatBall_mem 18 (by omega) (by omega)))
  have h18_cd : ContDiffAt ℂ 10 (fun w : ℂ => (18 : ℂ) ^ (-w)) z := by
    simpa using (analyticAt_cpow_neg (n := 18) (by omega) z).contDiffAt.of_le le_top
  have hhalf18 : Jet.Mem half18 (fun w : ℂ => (1 / 2 : ℂ) * (18 : ℂ) ^ (-w)) z := by
    have h := jetDivNat_mem (d := 2) (by omega) hj18
    have hfun : (fun w : ℂ => (18 : ℂ) ^ (-w) / ((2 : ℕ) : ℂ)) = (fun w : ℂ => (1 / 2 : ℂ) * (18 : ℂ) ^ (-w)) := by
      ext w; push_cast; ring
    rwa [hfun] at h
  have hinv_ana : AnalyticAt ℂ (fun w : ℂ => (w - 1)⁻¹) z := by
    have hdiff : DifferentiableOn ℂ (fun w : ℂ => (w - 1)⁻¹) {w : ℂ | w ≠ 1} := fun w hw =>
      ((differentiableAt_id.sub (differentiableAt_const (1 : ℂ))).inv (sub_ne_zero.mpr hw)).differentiableWithinAt
    exact (hdiff.analyticOnNhd isOpen_ne) z hz1
  have hpole : Jet.Mem pole (fun w : ℂ => (18 : ℂ) * (18 : ℂ) ^ (-w) * (w - 1)⁻¹) z := by
    have h1 := jetScaleInt_mem 18 hj18
    have h2 := invSubOneJetList_mem hz1 (ibInv_mem (ibSub_mem hz ibOne_mem) hinv_ok)
    simpa using jetMul_mem (contDiffAt_const.mul h18_cd) (hinv_ana.contDiffAt.of_le le_top) h1 h2
  have hp1 : Jet.Mem p1 (fun w => rising w 1) z := by
    have h := jetMulLin_mem (c := 0) (by simpa using hz) (analyticAt_rising 0 z) (p0_jet_mem z)
    have hfun : (fun w : ℂ => rising w 0 * (w + 0)) = (fun w => rising w 1) := by ext w; simp [rising]
    rwa [hfun] at h
  have hp2 : Jet.Mem p2 (fun w => rising w 2) z := rising_step_jet_mem hz 1 hp1
  have hp3 : Jet.Mem p3 (fun w => rising w 3) z := rising_step_jet_mem hz 2 hp2
  have hp4 : Jet.Mem p4 (fun w => rising w 4) z := rising_step_jet_mem hz 3 hp3
  have hp5 : Jet.Mem p5 (fun w => rising w 5) z := rising_step_jet_mem hz 4 hp4
  have hp6 : Jet.Mem p6 (fun w => rising w 6) z := rising_step_jet_mem hz 5 hp5
  have hp7 : Jet.Mem p7 (fun w => rising w 7) z := rising_step_jet_mem hz 6 hp6
  have hp8 : Jet.Mem p8 (fun w => rising w 8) z := rising_step_jet_mem hz 7 hp7
  have hp9 : Jet.Mem p9 (fun w => rising w 9) z := rising_step_jet_mem hz 8 hp8
  have hp10 : Jet.Mem p10 (fun w => rising w 10) z := rising_step_jet_mem hz 9 hp9
  have hp11 : Jet.Mem p11 (fun w => rising w 11) z := rising_step_jet_mem hz 10 hp10
  exact emMain_combine_mem hz1 (sum17_jet_mem hcp) hhalf18 hpole
    (bernoulli_term_pos_jet_mem (d := 12 * 18 ^ 1) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) hp1 hj18)
    (bernoulli_term_jet_mem (d := 720 * 18 ^ 3) (-1) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) hp3 hj18)
    (bernoulli_term_pos_jet_mem (d := 30240 * 18 ^ 5) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) hp5 hj18)
    (bernoulli_term_jet_mem (d := 1209600 * 18 ^ 7) (-1) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) hp7 hj18)
    (bernoulli_term_pos_jet_mem (d := 47900160 * 18 ^ 9) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) hp9 hj18)
    (bernoulli_term_jet_mem (d := 1307674368000 * 18 ^ 11) (-691) (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))) hp11 hj18)

/-! ### Remainder Bound Verification -/

def rising12Jet (s : IBall) : Jet :=
  let p0 : Jet := ibOne :: List.replicate 10 ibZero
  let p1 := jetMulLin p0 s
  let p2 := jetMulLin p1 (ibAdd s (ibConst 1 1 0 1))
  let p3 := jetMulLin p2 (ibAdd s (ibConst 2 1 0 1))
  let p4 := jetMulLin p3 (ibAdd s (ibConst 3 1 0 1))
  let p5 := jetMulLin p4 (ibAdd s (ibConst 4 1 0 1))
  let p6 := jetMulLin p5 (ibAdd s (ibConst 5 1 0 1))
  let p7 := jetMulLin p6 (ibAdd s (ibConst 6 1 0 1))
  let p8 := jetMulLin p7 (ibAdd s (ibConst 7 1 0 1))
  let p9 := jetMulLin p8 (ibAdd s (ibConst 8 1 0 1))
  let p10 := jetMulLin p9 (ibAdd s (ibConst 9 1 0 1))
  let p11 := jetMulLin p10 (ibAdd s (ibConst 10 1 0 1))
  jetMulLin p11 (ibAdd s (ibConst 11 1 0 1))

lemma rising12Jet_mem {sb : IBall} {z : ℂ} (hz : sb.Mem z) :
    (rising12Jet sb).Mem (fun w => rising w 12) z := by
  have hp1 : Jet.Mem (jetMulLin (ibOne :: List.replicate 10 ibZero) sb) (fun w => rising w 1) z := by
    simpa [rising] using jetMulLin_mem (c := 0) (by simpa using hz) (analyticAt_rising 0 z) (p0_jet_mem z)
  exact rising_step_jet_mem hz 11 (rising_step_jet_mem hz 10 (rising_step_jet_mem hz 9
    (rising_step_jet_mem hz 8 (rising_step_jet_mem hz 7 (rising_step_jet_mem hz 6
    (rising_step_jet_mem hz 5 (rising_step_jet_mem hz 4 (rising_step_jet_mem hz 3
    (rising_step_jet_mem hz 2 (rising_step_jet_mem hz 1 hp1))))))))))

def natSumRange : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => natSumRange n f + f n

lemma natSumRange_eq_sum (n : ℕ) (f : ℕ → ℕ) :
    natSumRange n f = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [natSumRange, Finset.sum_range_succ, ih]

def D_rem : ℕ := 2730 * Nat.factorial 12 * 11 ^ 11 * 18 ^ 11 * 10 ^ 10

def remBoundNum (sb : IBall) (k : ℕ) : ℕ :=
  let p12 := rising12Jet sb
  natSumRange (k + 1) fun j =>
    ((jetGet p12 j).absUb + (jetGet p12 j).rad) *
    (k.factorial / (k - j).factorial) * 693 * I_log_num (k - j) *
    11 ^ (10 - (k - j)) * 10 ^ (10 - (k - j))

lemma rem_bounds_ok :
    remBoundNum s0_ball 8 + remBoundNum s0_refl_ball 8 ≤ 600000000000 * D_rem ∧
    remBoundNum s0_ball 9 + remBoundNum s0_refl_ball 9 ≤ 2500000000000 * D_rem ∧
    remBoundNum s_disk_ball 10 + remBoundNum s_disk_refl_ball 10 ≤ 9000000000000 * D_rem := by
  decide

lemma norm_rem_deriv_le (k : ℕ) (hk : k ≤ 10) {sb : IBall} {z : ℂ}
    (hz : sb.Mem z) (hzre : 0 < z.re) :
    ‖iteratedDeriv k (fun w => rising w 12 * I_em 12 w) z‖ ≤
      (remBoundNum sb k : ℝ) / ((D_rem : ℝ) * (SCALE : ℝ)) := by
  have hI_ana : AnalyticAt ℂ (I_em 12) z := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ (I_em 12) {w : ℂ | 0 < w.re} := fun w hw => by
      have h0 : I_em 12 = I12_deriv 0 := by ext u; simp [I_em, I12_deriv]
      rw [h0]; exact (hasDerivAt_I12_deriv 0 (by omega) hw).differentiableAt.differentiableWithinAt
    exact (hdiff.analyticOnNhd hopen) z hzre
  have hdiv := iteratedDeriv_mul_div_factorial
    ((analyticAt_rising 12 z).contDiffAt.of_le le_top) (hI_ana.contDiffAt.of_le le_top) (k := k)
  have hkpos : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have heq : iteratedDeriv k (fun w => rising w 12 * I_em 12 w) z =
      (k.factorial : ℂ) * ∑ j ∈ Finset.range (k + 1),
        (iteratedDeriv j (fun w => rising w 12) z / (j.factorial : ℂ)) *
        (iteratedDeriv (k - j) (I_em 12) z / ((k - j).factorial : ℂ)) := by
    rw [← hdiv]; field_simp [hkpos]
  rw [heq, norm_mul, Complex.norm_natCast]
  have hp12 := rising12Jet_mem hz
  have hsum_eq : (remBoundNum sb k : ℝ) =
      ∑ j ∈ Finset.range (k + 1),
        (((jetGet (rising12Jet sb) j).absUb + (jetGet (rising12Jet sb) j).rad : ℕ) : ℝ) *
        ((k.factorial / (k - j).factorial : ℕ) : ℝ) * 693 * (I_log_num (k - j) : ℝ) *
        (11 : ℝ) ^ (10 - (k - j)) * (10 : ℝ) ^ (10 - (k - j)) := by
    unfold remBoundNum
    dsimp only
    rw [natSumRange_eq_sum]
    push_cast
    rfl
  rw [hsum_eq, Finset.sum_div]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Nat.cast_nonneg _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [norm_mul]
  have h1 : ‖iteratedDeriv j (fun w => rising w 12) z / (j.factorial : ℂ)‖ ≤
      (((jetGet (rising12Jet sb) j).absUb + (jetGet (rising12Jet sb) j).rad : ℕ) : ℝ) / (SCALE : ℝ) :=
    (jetGet (rising12Jet sb) j).norm_le (hp12.2 j (by omega))
  have h2 : ‖iteratedDeriv (k - j) (I_em 12) z / ((k - j).factorial : ℂ)‖ ≤
      ((693 / 2730 : ℝ) / (Nat.factorial 12 : ℝ)) *
      ((I_log_num (k - j) : ℝ) / ((11 : ℝ) ^ (k - j + 1) * (18 : ℝ) ^ 11 * (10 : ℝ) ^ (k - j))) /
      ((k - j).factorial : ℝ) := by
    rw [norm_div, Complex.norm_natCast, iteratedDeriv_I12 (k - j) (by omega) hzre]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact (norm_I12_deriv_le (k - j) (by omega) hzre).trans
      (mul_le_mul_of_nonneg_left (I_log_le_num log_18_le (k - j) (by omega)) (by positivity))
  have hprod := mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (Nat.cast_nonneg k.factorial)
  refine hprod.trans_eq ?_
  have hdvd : (k - j).factorial ∣ k.factorial := Nat.factorial_dvd_factorial (by omega)
  have hdiv_cast : ((k.factorial / (k - j).factorial : ℕ) : ℝ) = (k.factorial : ℝ) / ((k - j).factorial : ℝ) := by
    rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
  have hpow11 : (11 : ℝ) ^ (k - j + 1) * (11 : ℝ) ^ (10 - (k - j)) = (11 : ℝ) ^ 11 := by
    rw [← pow_add]; congr 1; omega
  have hpow10 : (10 : ℝ) ^ (k - j) * (10 : ℝ) ^ (10 - (k - j)) = (10 : ℝ) ^ 10 := by
    rw [← pow_add]; congr 1; omega
  have hD : (D_rem : ℝ) = 2730 * (Nat.factorial 12 : ℝ) * (11 : ℝ) ^ 11 * (18 : ℝ) ^ 11 * (10 : ℝ) ^ 10 := by
    unfold D_rem; push_cast; norm_num
  rw [hdiv_cast, hD, ← hpow11, ← hpow10]
  have hne1 : (SCALE : ℝ) ≠ 0 := scale_pos.ne'
  have hne2 : ((k - j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hne3 : (Nat.factorial 12 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 12)
  have hne4 : (11 : ℝ) ^ (k - j + 1) ≠ 0 := by positivity
  have hne5 : (11 : ℝ) ^ (10 - (k - j)) ≠ 0 := by positivity
  have hne6 : (18 : ℝ) ^ 11 ≠ 0 := by positivity
  have hne7 : (10 : ℝ) ^ (k - j) ≠ 0 := by positivity
  have hne8 : (10 : ℝ) ^ (10 - (k - j)) ≠ 0 := by positivity
  field_simp [hne1, hne2, hne3, hne4, hne5, hne6, hne7, hne8]

/-! ### Section 5: Preconditions, Off-Line Zero Existence, and Disproof -/

noncomputable def s0_val : ℂ :=
  (76267016 : ℂ) / 100000000 + (579824402 : ℂ) / 100000000 * I

lemma s0_ball_mem : s0_ball.Mem s0_val := by
  simpa [s0_ball, s0_val] using
    ibConst_mem (rn := 76267016) (rd := 100000000) (in_ := 579824402) (id_ := 100000000)
      (by omega) (by omega)

lemma s0_refl_ball_mem : s0_refl_ball.Mem (1 - s0_val) :=
  ibSub_mem ibOne_mem s0_ball_mem

lemma s_disk_ball_mem {z : ℂ} (hz : z ∈ closedBall s0_val (1 / 100000 : ℝ)) :
    s_disk_ball.Mem z := by
  rw [IBall.Mem, s_disk_ball]
  have hdist : ‖z - s0_val‖ ≤ (1 / 100000 : ℝ) := by simpa [dist_eq_norm] using mem_closedBall.mp hz
  have hrad : (1 / 100000 : ℝ) ≤ (r_rad : ℝ) / (SCALE : ℝ) := by
    have h1 : (SCALE : ℝ) / 100000 ≤ (r_rad : ℝ) := by
      unfold r_rad
      exact nat_ceil_div_le SCALE 100000 (by omega)
    calc (1 / 100000 : ℝ) = ((SCALE : ℝ) / 100000) / SCALE := by field_simp [scale_pos.ne']
      _ ≤ (r_rad : ℝ) / SCALE := div_le_div_of_nonneg_right h1 scale_pos.le
  have hsplit : z - ({ re := s0_ball.re, im := s0_ball.im, rad := s0_ball.rad + r_rad } : IBall).center =
      (z - s0_val) + (s0_val - s0_ball.center) := by simp [IBall.center]
  rw [hsplit]
  calc ‖(z - s0_val) + (s0_val - s0_ball.center)‖
      ≤ ‖z - s0_val‖ + ‖s0_val - s0_ball.center‖ := norm_add_le _ _
    _ ≤ (r_rad : ℝ) / SCALE + (s0_ball.rad : ℝ) / SCALE := add_le_add (hdist.trans hrad) s0_ball_mem
    _ = ((s0_ball.rad + r_rad : ℕ) : ℝ) / SCALE := by push_cast; ring

lemma s_disk_refl_ball_mem {z : ℂ} (hz : z ∈ closedBall s0_val (1 / 100000 : ℝ)) :
    s_disk_refl_ball.Mem (1 - z) :=
  ibSub_mem ibOne_mem (s_disk_ball_mem hz)

lemma cp_small_ok :
    (∀ i : Fin 7,
      (ibDivNat (ibNeg (ibMul s0_ball (logP_ball i))) 64).absUb +
        (ibDivNat (ibNeg (ibMul s0_ball (logP_ball i))) 64).rad ≤ SCALE / 2) ∧
    (∀ i : Fin 7,
      (ibDivNat (ibNeg (ibMul s0_refl_ball (logP_ball i))) 64).absUb +
        (ibDivNat (ibNeg (ibMul s0_refl_ball (logP_ball i))) 64).rad ≤ SCALE / 2) ∧
    (∀ i : Fin 7,
      (ibDivNat (ibNeg (ibMul s_disk_ball (logP_ball i))) 64).absUb +
        (ibDivNat (ibNeg (ibMul s_disk_ball (logP_ball i))) 64).rad ≤ SCALE / 2) ∧
    (∀ i : Fin 7,
      (ibDivNat (ibNeg (ibMul s_disk_refl_ball (logP_ball i))) 64).absUb +
        (ibDivNat (ibNeg (ibMul s_disk_refl_ball (logP_ball i))) 64).rad ≤ SCALE / 2) := by
  decide

lemma inv_preconds_ok :
    (ibSub s0_ball ibOne).rad < max (ibSub s0_ball ibOne).re.natAbs (ibSub s0_ball ibOne).im.natAbs ∧
    (ibSub s0_refl_ball ibOne).rad < max (ibSub s0_refl_ball ibOne).re.natAbs (ibSub s0_refl_ball ibOne).im.natAbs ∧
    (ibSub s_disk_ball ibOne).rad < max (ibSub s_disk_ball ibOne).re.natAbs (ibSub s_disk_ball ibOne).im.natAbs ∧
    (ibSub s_disk_refl_ball ibOne).rad < max (ibSub s_disk_refl_ball ibOne).re.natAbs (ibSub s_disk_refl_ball ibOne).im.natAbs := by
  decide

lemma cp_mem_of_eq {sb : IBall} {cp : Fin 7 → IBall} {z : ℂ} (hz : sb.Mem z)
    (heq : ∀ i : Fin 7, ibExp (ibNeg (ibMul sb (logP_ball i))) 6 22 = cp i)
    (hsm : ∀ i : Fin 7,
      (ibDivNat (ibNeg (ibMul sb (logP_ball i))) 64).absUb +
        (ibDivNat (ibNeg (ibMul sb (logP_ball i))) 64).rad ≤ SCALE / 2) :
    ∀ i : Fin 7, (cp i).Mem ((primeVal i : ℂ) ^ (-z)) := by
  intro i
  rw [← heq i, ← Complex.ofReal_natCast (primeVal i),
    ofReal_cpow_eq_exp (Nat.cast_pos.mpr (primeVal_pos i))]
  have harg : (ibNeg (ibMul sb (logP_ball i))).Mem ((Real.log (primeVal i) : ℂ) * (-z)) := by
    have h := ibNeg_mem (ibMul_mem hz (logP_mem i))
    have : -(z * (Real.log (primeVal i) : ℂ)) = (Real.log (primeVal i) : ℂ) * (-z) := by ring
    rwa [this] at h
  exact ibExp_mem harg (K := 6) (D := 22) (by omega) (hsm i)

lemma disk_props {z : ℂ} (hz : z ∈ closedBall s0_val (1 / 100000 : ℝ)) :
    0 < z.re ∧ z.re < 1 ∧ z.im ≠ 0 ∧ z.re ≠ 1 / 2 ∧ z ≠ 1 ∧ 0 < (1 - z).re ∧ 1 - z ≠ 1 := by
  have hdist : ‖z - s0_val‖ ≤ (1 / 100000 : ℝ) := by simpa [dist_eq_norm] using mem_closedBall.mp hz
  have hre_diff : |z.re - s0_val.re| ≤ 1 / 100000 := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (z - s0_val)).trans hdist
  have him_diff : |z.im - s0_val.im| ≤ 1 / 100000 := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z - s0_val)).trans hdist
  have hs0re : s0_val.re = 76267016 / 100000000 := by simp [s0_val]
  have hs0im : s0_val.im = 579824402 / 100000000 := by simp [s0_val]
  rw [hs0re, abs_le] at hre_diff
  rw [hs0im, abs_le] at him_diff
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_, by simp; linarith, ?_⟩
  · intro h; rw [h] at hre_diff; simp at hre_diff; norm_num at hre_diff
  · intro h; have : z = 0 := sub_eq_self.mp h; rw [this] at hre_diff; simp at hre_diff; norm_num at hre_diff

lemma target_derivs {z : ℂ} (hz : z ∈ closedBall s0_val (1 / 100000 : ℝ)) :
    let f : ℂ → ℂ := fun w => iteratedDeriv 8 riemannZeta w - iteratedDeriv 8 riemannZeta (1 - w)
    DifferentiableAt ℂ f z ∧ DifferentiableAt ℂ (deriv f) z ∧
    deriv f z = iteratedDeriv 9 riemannZeta z + iteratedDeriv 9 riemannZeta (1 - z) ∧
    deriv (deriv f) z = iteratedDeriv 10 riemannZeta z - iteratedDeriv 10 riemannZeta (1 - z) := by
  intro f
  obtain ⟨_, _, _, _, hz1, _, h1z1⟩ := disk_props hz
  have hzeta_diff : DifferentiableOn ℂ riemannZeta {u : ℂ | u ≠ 1} := fun u hu =>
    (differentiableAt_riemannZeta hu).differentiableWithinAt
  have hana_zeta : ∀ w : ℂ, w ≠ 1 → AnalyticAt ℂ riemannZeta w := fun w hw =>
    (hzeta_diff.analyticOnNhd isOpen_ne) w hw
  have hopen : IsOpen {w : ℂ | w ≠ 1 ∧ 1 - w ≠ 1} :=
    isOpen_ne.inter (isOpen_ne.preimage (continuous_const.sub continuous_id))
  have hnhds : {w : ℂ | w ≠ 1 ∧ 1 - w ≠ 1} ∈ 𝓝 z := hopen.mem_nhds ⟨hz1, h1z1⟩
  have hana8 : ∀ w, w ≠ 1 → AnalyticAt ℂ (iteratedDeriv 8 riemannZeta) w :=
    fun w hw => analyticAt_iteratedDeriv (hana_zeta w hw) 8
  have hana9 : ∀ w, w ≠ 1 → AnalyticAt ℂ (iteratedDeriv 9 riemannZeta) w :=
    fun w hw => analyticAt_iteratedDeriv (hana_zeta w hw) 9
  have hana2 : AnalyticAt ℂ (fun w => iteratedDeriv 8 riemannZeta (1 - w)) z :=
    (hana8 (1 - z) h1z1).comp (analyticAt_const.sub analyticAt_id)
  have hf_ana : AnalyticAt ℂ f z := (hana8 z hz1).sub hana2
  have hfd : deriv f =ᶠ[𝓝 z]
      (fun w => iteratedDeriv 9 riemannZeta w + iteratedDeriv 9 riemannZeta (1 - w)) := by
    filter_upwards [hnhds] with w ⟨hw1, h1w1⟩
    have hd1 : HasDerivAt (iteratedDeriv 8 riemannZeta) (iteratedDeriv 9 riemannZeta w) w := by
      rw [iteratedDeriv_succ (n := 8)]
      exact (hana8 w hw1).differentiableAt.hasDerivAt
    have hd2 : HasDerivAt (fun u => iteratedDeriv 8 riemannZeta (1 - u))
        (iteratedDeriv 9 riemannZeta (1 - w) * (-1)) w := by
      have h1 : HasDerivAt (iteratedDeriv 8 riemannZeta) (iteratedDeriv 9 riemannZeta (1 - w)) (1 - w) := by
        rw [iteratedDeriv_succ (n := 8)]
        exact (hana8 (1 - w) h1w1).differentiableAt.hasDerivAt
      exact h1.comp w ((hasDerivAt_id w).const_sub (1 : ℂ))
    have hsub : HasDerivAt f (iteratedDeriv 9 riemannZeta w - iteratedDeriv 9 riemannZeta (1 - w) * (-1)) w :=
      hd1.sub hd2
    rw [hsub.deriv]; ring
  have hfdd : deriv (deriv f) z =
      iteratedDeriv 10 riemannZeta z - iteratedDeriv 10 riemannZeta (1 - z) := by
    rw [hfd.deriv_eq]
    have hd1 : HasDerivAt (iteratedDeriv 9 riemannZeta) (iteratedDeriv 10 riemannZeta z) z := by
      rw [iteratedDeriv_succ (n := 9)]
      exact (hana9 z hz1).differentiableAt.hasDerivAt
    have hd2 : HasDerivAt (fun u => iteratedDeriv 9 riemannZeta (1 - u))
        (iteratedDeriv 10 riemannZeta (1 - z) * (-1)) z := by
      have h1 : HasDerivAt (iteratedDeriv 9 riemannZeta) (iteratedDeriv 10 riemannZeta (1 - z)) (1 - z) := by
        rw [iteratedDeriv_succ (n := 9)]
        exact (hana9 (1 - z) h1z1).differentiableAt.hasDerivAt
      exact h1.comp z ((hasDerivAt_id z).const_sub (1 : ℂ))
    have hadd : HasDerivAt (fun w => iteratedDeriv 9 riemannZeta w + iteratedDeriv 9 riemannZeta (1 - w))
        (iteratedDeriv 10 riemannZeta z + iteratedDeriv 10 riemannZeta (1 - z) * (-1)) z :=
      hd1.add hd2
    rw [hadd.deriv]; ring
  exact ⟨hf_ana.differentiableAt, (AnalyticAt.deriv hf_ana).differentiableAt, hfd.self_of_nhds, hfdd⟩

lemma exists_off_line_zero :
    ∃ z ∈ closedBall s0_val (1 / 100000 : ℝ),
      iteratedDeriv 8 riemannZeta z - iteratedDeriv 8 riemannZeta (1 - z) = 0 := by
  let f : ℂ → ℂ := fun z => iteratedDeriv 8 riemannZeta z - iteratedDeriv 8 riemannZeta (1 - z)
  have hban := banach_ok
  unfold checkBanach at hban
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hban
  obtain ⟨⟨hcond1, hcond2⟩, hcond3⟩ := hban
  obtain ⟨hrem8, hrem9, hrem10⟩ := rem_bounds_ok
  have hDpos : (0 : ℝ) < (D_rem : ℝ) := by unfold D_rem; positivity
  let d1 := emMainJetOfCp s0_ball cp_s0
  let d2 := emMainJetOfCp s0_refl_ball cp_s0_refl
  let dd1 := emMainJetOfCp s_disk_ball cp_s_disk
  let dd2 := emMainJetOfCp s_disk_refl_ball cp_s_disk_refl
  let f0 := ibScaleInt (Nat.factorial 8) (ibSub (jetGet d1 8) (jetGet d2 8))
  let f1 := ibScaleInt (Nat.factorial 9) (ibAdd (jetGet d1 9) (jetGet d2 9))
  let f2 := ibScaleInt (Nat.factorial 10) (ibSub (jetGet dd1 10) (jetGet dd2 10))
  let cLb := max f1.re.natAbs f1.im.natAbs
  let f0Ub := f0.absUb + f0.rad + 600000000000
  let f1Err := f1.rad + 2500000000000
  let M2Ub := f2.absUb + f2.rad + 9000000000000
  change 200000 * f0Ub ≤ cLb at hcond1
  change 4 * f1Err ≤ cLb at hcond2
  change 4 * M2Ub ≤ 100000 * cLb at hcond3
  have hs0_mem_disk : s0_val ∈ closedBall s0_val (1 / 100000 : ℝ) := mem_closedBall_self (by norm_num)
  obtain ⟨hs0_re, _, _, _, hs0_1, h1s0_re, h1s0_1⟩ := disk_props hs0_mem_disk
  have hd1_mem : d1.Mem emMain s0_val :=
    emMainJetOfCp_mem s0_ball_mem hs0_1 inv_preconds_ok.1 (cp_mem_of_eq s0_ball_mem cp_s0_eq cp_small_ok.1)
  have hd2_mem : d2.Mem emMain (1 - s0_val) :=
    emMainJetOfCp_mem s0_refl_ball_mem h1s0_1 inv_preconds_ok.2.1 (cp_mem_of_eq s0_refl_ball_mem cp_s0_refl_eq cp_small_ok.2.1)
  have hc_lb : (cLb : ℝ) / (SCALE : ℝ) ≤ ‖f1.center‖ := by
    have hre : (f1.re.natAbs : ℝ) / SCALE ≤ ‖f1.center‖ := by
      have h1 : |f1.center.re| = (f1.re.natAbs : ℝ) / SCALE := by
        simp [IBall.center, abs_div, abs_of_pos scale_pos]
      rw [← h1]; exact Complex.abs_re_le_norm _
    have him : (f1.im.natAbs : ℝ) / SCALE ≤ ‖f1.center‖ := by
      have h1 : |f1.center.im| = (f1.im.natAbs : ℝ) / SCALE := by
        simp [IBall.center, abs_div, abs_of_pos scale_pos]
      rw [← h1]; exact Complex.abs_im_le_norm _
    change ((max f1.re.natAbs f1.im.natAbs : ℕ) : ℝ) / SCALE ≤ ‖f1.center‖
    rcases max_choice f1.re.natAbs f1.im.natAbs with h | h <;> rw [h]
    · exact hre
    · exact him
  have hcLb_pos : 0 < cLb := by
    have : 0 < f1Err := by simp only [f1Err]; omega
    omega
  have hc_ne : f1.center ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hc_lb
    have : (0 : ℝ) < (cLb : ℝ) / SCALE := div_pos (Nat.cast_pos.mpr hcLb_pos) scale_pos
    linarith
  have hrem_div : ∀ (a b c : ℕ), a + b ≤ c * D_rem →
      (a : ℝ) / ((D_rem : ℝ) * (SCALE : ℝ)) + (b : ℝ) / ((D_rem : ℝ) * (SCALE : ℝ)) ≤ (c : ℝ) / (SCALE : ℝ) := by
    intro a b c hab
    have h1 : (a : ℝ) + (b : ℝ) ≤ (c : ℝ) * (D_rem : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hab
    rw [← add_div, div_le_div_iff₀ (mul_pos hDpos scale_pos) scale_pos]
    calc ((a : ℝ) + (b : ℝ)) * (SCALE : ℝ)
        ≤ ((c : ℝ) * (D_rem : ℝ)) * (SCALE : ℝ) := mul_le_mul_of_nonneg_right h1 scale_pos.le
      _ = (c : ℝ) * ((D_rem : ℝ) * (SCALE : ℝ)) := by ring
  have hf0_main : f0.Mem (iteratedDeriv 8 emMain s0_val - iteratedDeriv 8 emMain (1 - s0_val)) := by
    have hsub := ibSub_mem (hd1_mem.2 8 (by omega)) (hd2_mem.2 8 (by omega))
    have hsc := ibScaleInt_mem (Nat.factorial 8) hsub
    have heq : ((Nat.factorial 8 : ℤ) : ℂ) * (iteratedDeriv 8 emMain s0_val / (Nat.factorial 8 : ℂ) -
        iteratedDeriv 8 emMain (1 - s0_val) / (Nat.factorial 8 : ℂ)) =
        iteratedDeriv 8 emMain s0_val - iteratedDeriv 8 emMain (1 - s0_val) := by
      have hne : (Nat.factorial 8 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 8)
      push_cast; field_simp [hne]
    rwa [heq] at hsc
  have h0_bound : ‖f s0_val‖ ≤ (1 / 100000 : ℝ) / 2 * ‖f1.center‖ := by
    have hsplit : f s0_val =
        (iteratedDeriv 8 emMain s0_val - iteratedDeriv 8 emMain (1 - s0_val)) -
        iteratedDeriv 8 (fun w => rising w 12 * I_em 12 w) s0_val +
        iteratedDeriv 8 (fun w => rising w 12 * I_em 12 w) (1 - s0_val) := by
      simp only [f, iteratedDeriv_zeta_eq_em 8 hs0_re hs0_1, iteratedDeriv_zeta_eq_em 8 h1s0_re h1s0_1]; ring
    have hrem_r := hrem_div _ _ 600000000000 hrem8
    have hb1 := f0.norm_le hf0_main
    have hb2 := norm_rem_deriv_le 8 (by omega) s0_ball_mem hs0_re
    have hb3 := norm_rem_deriv_le 8 (by omega) s0_refl_ball_mem h1s0_re
    have hnorm : ‖f s0_val‖ ≤ (f0Ub : ℝ) / SCALE := by
      rw [hsplit]
      have ht1 := norm_add_le
        ((iteratedDeriv 8 emMain s0_val - iteratedDeriv 8 emMain (1 - s0_val)) -
          iteratedDeriv 8 (fun w => rising w 12 * I_em 12 w) s0_val)
        (iteratedDeriv 8 (fun w => rising w 12 * I_em 12 w) (1 - s0_val))
      have ht2 := norm_sub_le
        (iteratedDeriv 8 emMain s0_val - iteratedDeriv 8 emMain (1 - s0_val))
        (iteratedDeriv 8 (fun w => rising w 12 * I_em 12 w) s0_val)
      have hcast : ((f0.absUb + f0.rad : ℕ) : ℝ) / SCALE + (600000000000 : ℝ) / SCALE = (f0Ub : ℝ) / SCALE := by
        simp only [f0Ub, Nat.cast_add]; ring
      linarith
    have hc1 : (200000 : ℝ) * (f0Ub : ℝ) ≤ (cLb : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hcond1
    have hc1' := div_le_div_of_nonneg_right hc1 scale_pos.le
    rw [mul_div_assoc] at hc1'
    linarith
  have hf1_main : f1.Mem (iteratedDeriv 9 emMain s0_val + iteratedDeriv 9 emMain (1 - s0_val)) := by
    have hadd := ibAdd_mem (hd1_mem.2 9 (by omega)) (hd2_mem.2 9 (by omega))
    have hsc := ibScaleInt_mem (Nat.factorial 9) hadd
    have heq : ((Nat.factorial 9 : ℤ) : ℂ) * (iteratedDeriv 9 emMain s0_val / (Nat.factorial 9 : ℂ) +
        iteratedDeriv 9 emMain (1 - s0_val) / (Nat.factorial 9 : ℂ)) =
        iteratedDeriv 9 emMain s0_val + iteratedDeriv 9 emMain (1 - s0_val) := by
      have hne : (Nat.factorial 9 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 9)
      push_cast; field_simp [hne]
    rwa [heq] at hsc
  have h1_bound : ‖deriv f s0_val - f1.center‖ ≤ ‖f1.center‖ / 4 := by
    have hdf := (target_derivs hs0_mem_disk).2.2.1
    have hsplit : deriv f s0_val - f1.center =
        ((iteratedDeriv 9 emMain s0_val + iteratedDeriv 9 emMain (1 - s0_val)) - f1.center) -
        iteratedDeriv 9 (fun w => rising w 12 * I_em 12 w) s0_val -
        iteratedDeriv 9 (fun w => rising w 12 * I_em 12 w) (1 - s0_val) := by
      rw [hdf, iteratedDeriv_zeta_eq_em 9 hs0_re hs0_1, iteratedDeriv_zeta_eq_em 9 h1s0_re h1s0_1]; ring
    have hrem_r := hrem_div _ _ 2500000000000 hrem9
    have hb2 := norm_rem_deriv_le 9 (by omega) s0_ball_mem hs0_re
    have hb3 := norm_rem_deriv_le 9 (by omega) s0_refl_ball_mem h1s0_re
    have hnorm : ‖deriv f s0_val - f1.center‖ ≤ (f1Err : ℝ) / SCALE := by
      rw [hsplit]
      have ht1 := norm_sub_le
        (((iteratedDeriv 9 emMain s0_val + iteratedDeriv 9 emMain (1 - s0_val)) - f1.center) -
          iteratedDeriv 9 (fun w => rising w 12 * I_em 12 w) s0_val)
        (iteratedDeriv 9 (fun w => rising w 12 * I_em 12 w) (1 - s0_val))
      have ht2 := norm_sub_le
        ((iteratedDeriv 9 emMain s0_val + iteratedDeriv 9 emMain (1 - s0_val)) - f1.center)
        (iteratedDeriv 9 (fun w => rising w 12 * I_em 12 w) s0_val)
      have hb1 : ‖(iteratedDeriv 9 emMain s0_val + iteratedDeriv 9 emMain (1 - s0_val)) - f1.center‖ ≤
          (f1.rad : ℝ) / SCALE := hf1_main
      have hcast : (f1.rad : ℝ) / SCALE + (2500000000000 : ℝ) / SCALE = (f1Err : ℝ) / SCALE := by
        simp only [f1Err, Nat.cast_add]; ring
      linarith
    have hc2 : (4 : ℝ) * (f1Err : ℝ) ≤ (cLb : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hcond2
    have hc2' := div_le_div_of_nonneg_right hc2 scale_pos.le
    rw [mul_div_assoc] at hc2'
    linarith
  have h2_bound : ∀ z ∈ closedBall s0_val (1 / 100000 : ℝ), ‖deriv (deriv f) z‖ ≤ (M2Ub : ℝ) / SCALE := by
    intro z hz
    obtain ⟨hz_re, _, _, _, hz1, h1z_re, h1z1⟩ := disk_props hz
    have hdd1_mem : dd1.Mem emMain z :=
      emMainJetOfCp_mem (s_disk_ball_mem hz) hz1 inv_preconds_ok.2.2.1
        (cp_mem_of_eq (s_disk_ball_mem hz) cp_s_disk_eq cp_small_ok.2.2.1)
    have hdd2_mem : dd2.Mem emMain (1 - z) :=
      emMainJetOfCp_mem (s_disk_refl_ball_mem hz) h1z1 inv_preconds_ok.2.2.2
        (cp_mem_of_eq (s_disk_refl_ball_mem hz) cp_s_disk_refl_eq cp_small_ok.2.2.2)
    have hf2_main : f2.Mem (iteratedDeriv 10 emMain z - iteratedDeriv 10 emMain (1 - z)) := by
      have hsub := ibSub_mem (hdd1_mem.2 10 (by omega)) (hdd2_mem.2 10 (by omega))
      have hsc := ibScaleInt_mem (Nat.factorial 10) hsub
      have heq : ((Nat.factorial 10 : ℤ) : ℂ) * (iteratedDeriv 10 emMain z / (Nat.factorial 10 : ℂ) -
          iteratedDeriv 10 emMain (1 - z) / (Nat.factorial 10 : ℂ)) =
          iteratedDeriv 10 emMain z - iteratedDeriv 10 emMain (1 - z) := by
        have hne : (Nat.factorial 10 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 10)
        push_cast; field_simp [hne]
      rwa [heq] at hsc
    have hddf := (target_derivs hz).2.2.2
    have hsplit : deriv (deriv f) z =
        (iteratedDeriv 10 emMain z - iteratedDeriv 10 emMain (1 - z)) -
        iteratedDeriv 10 (fun w => rising w 12 * I_em 12 w) z +
        iteratedDeriv 10 (fun w => rising w 12 * I_em 12 w) (1 - z) := by
      rw [hddf, iteratedDeriv_zeta_eq_em 10 hz_re hz1, iteratedDeriv_zeta_eq_em 10 h1z_re h1z1]; ring
    have hrem_r := hrem_div _ _ 9000000000000 hrem10
    have hb1 := f2.norm_le hf2_main
    have hb2 := norm_rem_deriv_le 10 (by omega) (s_disk_ball_mem hz) hz_re
    have hb3 := norm_rem_deriv_le 10 (by omega) (s_disk_refl_ball_mem hz) h1z_re
    rw [hsplit]
    have ht1 := norm_add_le
      ((iteratedDeriv 10 emMain z - iteratedDeriv 10 emMain (1 - z)) -
        iteratedDeriv 10 (fun w => rising w 12 * I_em 12 w) z)
      (iteratedDeriv 10 (fun w => rising w 12 * I_em 12 w) (1 - z))
    have ht2 := norm_sub_le
      (iteratedDeriv 10 emMain z - iteratedDeriv 10 emMain (1 - z))
      (iteratedDeriv 10 (fun w => rising w 12 * I_em 12 w) z)
    have hcast : ((f2.absUb + f2.rad : ℕ) : ℝ) / SCALE + (9000000000000 : ℝ) / SCALE = (M2Ub : ℝ) / SCALE := by
      simp only [M2Ub, Nat.cast_add]; ring
    linarith
  have h3_bound : ((M2Ub : ℝ) / SCALE) * (1 / 100000 : ℝ) ≤ ‖f1.center‖ / 4 := by
    have hc3 : (4 : ℝ) * (M2Ub : ℝ) ≤ (100000 : ℝ) * (cLb : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hcond3
    have hc3' := div_le_div_of_nonneg_right hc3 scale_pos.le
    rw [mul_div_assoc, mul_div_assoc] at hc3'
    linarith
  exact exists_zero_of_newton (by norm_num) hc_ne (div_nonneg (Nat.cast_nonneg _) scale_pos.le)
    (fun z hz => (target_derivs hz).1) (fun z hz => (target_derivs hz).2.1)
    h0_bound h1_bound h2_bound h3_bound

end OMA.Mo93323

/-- Disproof of `OMA.S_mo_93323.main`: the 8th derivative difference
`iteratedDeriv 8 riemannZeta z - iteratedDeriv 8 riemannZeta (1 - z)`
has a nonreal zero in the open critical strip with `z.re != 1/2`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_93323.main) := by
  intro hmain
  obtain ⟨z, hz_ball, hfz⟩ := OMA.Mo93323.exists_off_line_zero
  obtain ⟨hre0, hre1, him, hne_half, _, _, _⟩ := OMA.Mo93323.disk_props hz_ball
  exact hne_half (hmain 8 (by norm_num) z hre0 hre1 him (Or.inr hfz))
