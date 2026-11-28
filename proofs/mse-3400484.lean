import OMAStatements.S_mse_3400484
import Mathlib

-- Credit: @rpinho
-- Both tails are log-concave. The right squared-survival integral controls the
-- target by the left integrated CDF. For small CDF at the mean, its exponential
-- tangent controls both sides. Otherwise use the reflected left survival bound.

namespace LogConcaveTail

open MeasureTheory Set
open scoped Interval

private lemma continuous_one : Continuous (fun _ : ℝ => (1 : ℝ)) := continuous_const

private noncomputable def cdf (f : ℝ → ℝ) (l x : ℝ) : ℝ := ∫ t in l..x, f t

private noncomputable def survival (f : ℝ → ℝ) (l x : ℝ) : ℝ := 1 - cdf f l x

private lemma cdf_deriv {f : ℝ → ℝ} (hc : Continuous f) (l x : ℝ) :
    HasDerivAt (cdf f l) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable l x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

private lemma cdf_cont {f : ℝ → ℝ} (hc : Continuous f) (l : ℝ) : Continuous (cdf f l) :=
  continuous_iff_continuousAt.2 (fun x => (cdf_deriv hc l x).continuousAt)

private lemma surv_cont {f : ℝ → ℝ} (hc : Continuous f) (l : ℝ) : Continuous (survival f l) :=
  continuous_const.sub (cdf_cont hc l)

private lemma surv_integral {f : ℝ → ℝ} (hc : Continuous f) {l u : ℝ}
    (mass : (∫ x in l..u, f x) = 1) (t : ℝ) : survival f l t = ∫ x in t..u, f x := by
  have adjacent := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable l t) (hc.intervalIntegrable t u)
  change (∫ x in l..t, f x) + (∫ x in t..u, f x) = (∫ x in l..u, f x) at adjacent
  rw [mass] at adjacent
  unfold survival cdf
  linarith

private lemma positive_integral {f : ℝ → ℝ} {l u : ℝ} (hlt : l < u)
    (hc : Continuous f) (nn : ∀ x ∈ Icc l u, 0 ≤ f x) (pos : ∀ x ∈ Ioo l u, 0 < f x) :
    0 < ∫ x in l..u, f x := by
  refine intervalIntegral.integral_pos hlt hc.continuousOn (fun x hx => nn x (Ioc_subset_Icc_self hx)) ?_
  let mid := (l+u)/2
  have inside : mid ∈ Ioo l u := ⟨by dsimp [mid]; linarith, by dsimp [mid]; linarith⟩
  exact ⟨mid, Ioo_subset_Icc_self inside, pos mid inside⟩

private lemma cdf_pos {f : ℝ → ℝ} {l u : ℝ} (hc : Continuous f)
    (nn : ∀ x ∈ Icc l u, 0 ≤ f x) (pos : ∀ x ∈ Ioo l u, 0 < f x) {x : ℝ} (hx : x ∈ Ioc l u) :
    0 < cdf f l x :=
  positive_integral hx.1 hc (fun y hy => nn y ⟨hy.1, hy.2.trans hx.2⟩)
    (fun y hy => pos y ⟨hy.1, hy.2.trans_le hx.2⟩)

private lemma surv_pos {f : ℝ → ℝ} {l u : ℝ} (hc : Continuous f)
    (nn : ∀ x ∈ Icc l u, 0 ≤ f x) (pos : ∀ x ∈ Ioo l u, 0 < f x)
    (mass : (∫ x in l..u, f x) = 1) {x : ℝ} (hx : x ∈ Ico l u) :
    0 < survival f l x := by
  rw [surv_integral hc mass]
  exact positive_integral hx.2 hc (fun y hy => nn y ⟨hx.1.trans hy.1, hy.2⟩)
    (fun y hy => pos y ⟨hx.1.trans_lt hy.1, hy.2⟩)

private lemma tangent {D : Set ℝ} {g : ℝ → ℝ} {x y b : ℝ}
    (hg : ConcaveOn ℝ D g) (hx : x ∈ D) (hy : y ∈ D) (h : HasDerivAt g b x) :
    g y ≤ g x + b*(y-x) := by
  rcases lt_trichotomy x y with lt | rfl | gt
  · have m := hg.slope_le_of_hasDerivAt hx hy lt h
    rw [slope_def_field] at m
    linarith [(div_le_iff₀ (sub_pos.mpr lt)).1 m]
  · simp
  · have m := hg.le_slope_of_hasDerivAt hy hx gt h
    rw [slope_def_field] at m
    linarith [(le_div_iff₀ (sub_pos.mpr gt)).1 m]

private lemma exp_envelope {D : Set ℝ} {g : ℝ → ℝ} {x y b : ℝ}
    (hg : ConcaveOn ℝ D (fun t => Real.log (g t))) (hx : x ∈ D) (hy : y ∈ D)
    (px : 0 < g x) (py : 0 < g y) (h : HasDerivAt (fun t => Real.log (g t)) b x) :
    g y ≤ g x * Real.exp (b*(y-x)) := by
  have h' := Real.exp_le_exp.mpr (tangent hg hx hy h)
  simpa only [Real.exp_add, Real.exp_log px, Real.exp_log py] using h'

private lemma int_exp_affine (a b c x : ℝ) (hc : c ≠ 0) :
    (∫ t in a..b, Real.exp (c*(t-x))) =
      (Real.exp (c*(b-x)) - Real.exp (c*(a-x))) / c := by
  simp_rw [mul_sub]
  simp only [sub_eq_add_neg]
  rw [intervalIntegral.integral_comp_mul_add Real.exp hc, integral_exp]
  rw [smul_eq_mul, div_eq_inv_mul]
  ring

private lemma log_deriv_bounds {f : ℝ → ℝ} {l u : ℝ} (hc : Continuous f)
    (hd : ∀ x ∈ Ioo l u, DifferentiableAt ℝ f x)
    (pos : ∀ x ∈ Ioo l u, 0 < f x)
    (hlc : ConcaveOn ℝ (Ioo l u) (fun x => Real.log (f x)))
    (mass : (∫ x in l..u, f x) = 1) {x : ℝ} (hx : x ∈ Ioo l u)
    (hF : 0 ≤ cdf f l x) (hS : 0 ≤ survival f l x) :
    deriv f x * cdf f l x ≤ (f x)^2 ∧ -deriv f x * survival f l x ≤ (f x)^2 := by
  have px := pos x hx
  let β := deriv f x / f x
  have bForm : β * f x = deriv f x := div_mul_cancel₀ _ px.ne'
  have hlog : HasDerivAt (fun y => Real.log (f y)) β x := (hd x hx).hasDerivAt.log px.ne'
  have env (y : ℝ) (hy : y ∈ Ioo l u) : f y ≤ f x * Real.exp (β*(y-x)) :=
    exp_envelope hlc hx hy px (pos y hy) hlog
  have EL (a b : ℝ) : IntervalIntegrable (fun t => f x * Real.exp (β*(t-x))) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← bForm, ← neg_mul]
  constructor
  · have bound : β * cdf f l x ≤ f x := by
      by_cases bp : 0 < β
      · have hle := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hx.1.le
          (hc.intervalIntegrable l x) (EL l x) (fun y hy => env y ⟨hy.1, hy.2.trans hx.2⟩)
        rw [intervalIntegral.integral_const_mul, int_exp_affine _ _ _ _ bp.ne',
          sub_self, mul_zero, Real.exp_zero] at hle
        have b := (le_div_iff₀ bp).1 (by simpa only [mul_div_assoc, cdf] using hle :
          cdf f l x ≤ f x*(1-Real.exp (β*(l-x)))/β)
        nlinarith only [b, mul_nonneg px.le (Real.exp_pos (β*(l-x))).le]
      · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt bp) hF).trans px.le
    nlinarith only [mul_le_mul_of_nonneg_right bound px.le]
  · have bound : -β * survival f l x ≤ f x := by
      by_cases bn : β < 0
      · have hle := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hx.2.le
          (hc.intervalIntegrable x u) (EL x u) (fun y hy => env y ⟨hx.1.trans hy.1, hy.2⟩)
        rw [intervalIntegral.integral_const_mul, int_exp_affine _ _ _ _ bn.ne,
          sub_self, mul_zero, Real.exp_zero] at hle
        have factor :
            (Real.exp (β*(u-x))-1)/β = (1-Real.exp (β*(u-x)))/(-β) := by
          field_simp
          ring
        rw [factor, ← mul_div_assoc, ← surv_integral hc mass] at hle
        have b := (le_div_iff₀ (neg_pos.mpr bn)).1 hle
        nlinarith only [b, mul_nonneg px.le (Real.exp_pos (β*(u-x))).le]
      · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hS).trans px.le
    nlinarith only [mul_le_mul_of_nonneg_right bound px.le]

private lemma log_distributions {f : ℝ → ℝ} {l u : ℝ} (hc : Continuous f)
    (hd : ∀ x ∈ Ioo l u, DifferentiableAt ℝ f x)
    (nn : ∀ x ∈ Icc l u, 0 ≤ f x) (pos : ∀ x ∈ Ioo l u, 0 < f x)
    (hlc : ConcaveOn ℝ (Ioo l u) (fun x => Real.log (f x)))
    (mass : (∫ x in l..u, f x) = 1) :
    ConcaveOn ℝ (Ioc l u) (fun x => Real.log (cdf f l x)) ∧
      ConcaveOn ℝ (Ico l u) (fun x => Real.log (survival f l x)) := by
  let F := cdf f l
  let S := survival f l
  have Hc : ∀ x ∈ Ioc l u, 0 < F x := fun x h => cdf_pos hc nn pos h
  have Hs : ∀ x ∈ Ico l u, 0 < S x := fun x h => surv_pos hc nn pos mass h
  have fd (x : ℝ) : HasDerivAt F (f x) x := cdf_deriv hc l x
  have sd (x : ℝ) : HasDerivAt S (-f x) x := by
    exact (fd x).const_sub 1
  constructor
  · apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun x => f x/F x)
      (f'' := fun x => (deriv f x * F x - f x*f x)/(F x)^2) (convex_Ioc l u)
    · exact (cdf_cont hc l).continuousOn.log (fun x hx => (Hc x hx).ne')
    · rw [interior_Ioc]
      exact fun x hx => ((fd x).log (Hc x ⟨hx.1,hx.2.le⟩).ne').hasDerivWithinAt
    · rw [interior_Ioc]
      exact fun x hx => ((hd x hx).hasDerivAt.div (fd x) (Hc x ⟨hx.1,hx.2.le⟩).ne').hasDerivWithinAt
    · rw [interior_Ioc]
      intro x hx
      have b := (log_deriv_bounds hc hd pos hlc mass hx
        (Hc x ⟨hx.1,hx.2.le⟩).le (Hs x ⟨hx.1.le,hx.2⟩).le).1
      exact div_nonpos_of_nonpos_of_nonneg (by change deriv f x * cdf f l x - f x*f x ≤ 0; nlinarith only [b]) (sq_nonneg _)
  · apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun x => -f x/S x)
      (f'' := fun x => (-deriv f x * S x - (-f x)*(-f x))/(S x)^2) (convex_Ico l u)
    · exact (surv_cont hc l).continuousOn.log (fun x hx => (Hs x hx).ne')
    · rw [interior_Ico]
      exact fun x hx => ((sd x).log (Hs x ⟨hx.1.le,hx.2⟩).ne').hasDerivWithinAt
    · rw [interior_Ico]
      exact fun x hx => ((hd x hx).hasDerivAt.neg.div (sd x) (Hs x ⟨hx.1.le,hx.2⟩).ne').hasDerivWithinAt
    · rw [interior_Ico]
      intro x hx
      have b := (log_deriv_bounds hc hd pos hlc mass hx
        (Hc x ⟨hx.1,hx.2.le⟩).le (Hs x ⟨hx.1.le,hx.2⟩).le).2
      exact div_nonpos_of_nonpos_of_nonneg
        (by change -deriv f x * survival f l x - (-f x)*(-f x) ≤ 0; nlinarith only [b]) (sq_nonneg _)

private lemma mean_inside {f : ℝ → ℝ} {l u : ℝ} (bounds : l < u) (hc : Continuous f)
    (nn : ∀ x ∈ Icc l u, 0 ≤ f x) (pos : ∀ x ∈ Ioo l u, 0 < f x)
    (mass : (∫ x in l..u, f x) = 1) :
    (∫ x in l..u, x*f x) ∈ Ioo l u := by
  have inf : 0 < ∫ x in l..u, (x-l)*f x := by
    apply positive_integral bounds (by fun_prop)
    · exact fun x hx => mul_nonneg (sub_nonneg.mpr hx.1) (nn x hx)
    · exact fun x hx => mul_pos (sub_pos.mpr hx.1) (pos x hx)
  have sup : 0 < ∫ x in l..u, (u-x)*f x := by
    apply positive_integral bounds (by fun_prop)
    · exact fun x hx => mul_nonneg (sub_nonneg.mpr hx.2) (nn x hx)
    · exact fun x hx => mul_pos (sub_pos.mpr hx.2) (pos x hx)
  have ii : IntervalIntegrable (fun x => x*f x) volume l u := (continuous_id.mul hc).intervalIntegrable l u
  have mulI (a : ℝ) : IntervalIntegrable (fun x => a*f x) volume l u := (continuous_const.mul hc : Continuous (fun x => a*f x)).intervalIntegrable l u
  simp only [sub_mul] at inf sup
  rw [intervalIntegral.integral_sub ii (mulI l), intervalIntegral.integral_const_mul, mass, mul_one] at inf
  rw [intervalIntegral.integral_sub (mulI u) ii, intervalIntegral.integral_const_mul, mass, mul_one] at sup
  exact ⟨by linarith,by linarith⟩

private lemma cdf_mean_balance {f : ℝ → ℝ} {l u m : ℝ} (hc : Continuous f)
    (hm : m = ∫ x in l..u, x*f x)
    (mass : (∫ x in l..u, f x) = 1) :
    (∫ x in l..m, cdf f l x) = ∫ x in m..u, survival f l x := by
  let F := cdf f l
  let S := survival f l
  have fc : Continuous F := cdf_cont hc l
  have part := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := l) (b := u) (u := fun x : ℝ => x) (v := F)
    continuous_id.continuousOn fc.continuousOn
    (fun x _ => hasDerivAt_id x) (fun x _ => cdf_deriv hc l x)
    (continuous_const.intervalIntegrable l u) (hc.intervalIntegrable l u)
  have Fl : F l = 0 := intervalIntegral.integral_same
  have Fu : F u = 1 := mass
  simp only [Fu, Fl, mul_one, mul_zero, sub_zero, one_mul] at part
  rw [← hm] at part
  have add := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (fc.intervalIntegrable l m) (fc.intervalIntegrable m u)
  change (∫ x in l..m,F x) + (∫ x in m..u,F x) = (∫ x in l..u,F x) at add
  change (∫ x in l..m,F x) = ∫ x in m..u, 1-F x
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable m u) (fc.intervalIntegrable m u),
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  linarith

private lemma midpoint_product {D : Set ℝ} {G : ℝ → ℝ} {x y : ℝ}
    (hc : ConcaveOn ℝ D (fun t => Real.log (G t)))
    (hp : ∀ t ∈ D, 0 < G t) (hx : x ∈ D) (hy : y ∈ D) :
    G x * G y ≤ G ((x+y)/2)^2 := by
  have mix : (1/2 : ℝ) • x + (1/2 : ℝ) • y = (x+y)/2 := by simp [smul_eq_mul]; ring
  have xm : (x+y)/2 ∈ D := by
    rw [← mix]
    exact hc.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have mid : (1/2:ℝ) • Real.log (G x) + (1/2:ℝ) • Real.log (G y) ≤
      Real.log (G ((1/2:ℝ) • x + (1/2:ℝ) • y)) :=
    hc.2 hx hy (by norm_num) (by norm_num) (by norm_num)
  rw [mix] at mid
  simp only [smul_eq_mul] at mid
  have logbound : Real.log (G x) + Real.log (G y) ≤
      Real.log (G ((x+y)/2)) + Real.log (G ((x+y)/2)) := by linarith
  have E := Real.exp_le_exp.mpr logbound
  simpa only [Real.exp_add, Real.exp_log (hp x hx), Real.exp_log (hp y hy),
    Real.exp_log (hp _ xm), pow_two] using E

private lemma square_tail {S : ℝ → ℝ} {l m u : ℝ}
    (hmu : m ∈ Ioo l u) (ct : Continuous S)
    (Spos : ∀ x ∈ Ico l u, 0 < S x)
    (logS : ConcaveOn ℝ (Ico l u) (fun t => Real.log (S t))) :
    S m /2 * (∫ x in m..u, S x) ≤ ∫ x in m..u, S x^2 := by
  let p := (m+u)/2
  have mp : m ≤ p := by dsimp [p]; linarith [hmu.2]
  have pu : p ≤ u := by dsimp [p]; linarith [hmu.2]
  have hc : Continuous (fun x => S m*S (2*x-m)) := by fun_prop
  have hd : Continuous (fun x => S x^2) := ct.pow 2
  have main := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) mp
    (hc.intervalIntegrable m p) (hd.intervalIntegrable m p) (fun x hx => by
      have a : m ∈ Ico l u := ⟨hmu.1.le,hmu.2⟩
      have b : 2*x-m ∈ Ico l u := ⟨by linarith [hmu.1,hx.1], by dsimp [p] at hx; linarith [hx.2]⟩
      have bound := midpoint_product logS Spos a b
      have eq : (m+(2*x-m))/2=x := by ring
      rwa [eq] at bound)
  have int := intervalIntegral.integral_comp_mul_add (a:=m) (b:=p) S (by norm_num : (2:ℝ) ≠ 0) (-m)
  have eq1 : (2:ℝ)*m + -m = m := by ring
  have eq2 : (2:ℝ)*p + -m = u := by dsimp [p]; ring
  simp only [eq1, eq2, smul_eq_mul] at int
  simp only [sub_eq_add_neg, intervalIntegral.integral_const_mul] at main
  rw [int] at main
  have step := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hd.intervalIntegrable m p) (hd.intervalIntegrable p u)
  have nonneg := intervalIntegral.integral_nonneg (μ:=volume) pu (f:=fun x => S x^2) (fun x _ => sq_nonneg _)
  change (∫ x in m..p, S x^2) + (∫ x in p..u, S x^2) = (∫ x in m..u, S x^2) at step
  nlinarith only [main,step,nonneg]

private lemma reflect_survival {S : ℝ → ℝ} {l m u : ℝ} (hm : m ∈ Ioo l u)
    (hc : Continuous S) (left : S l = 1) (Spos : ∀ x ∈ Ico l u, 0 < S x)
    (logS : ConcaveOn ℝ (Ico l u) (fun x => Real.log (S x))) :
    (m-l) * Real.sqrt (S m) ≤ ∫ x in l..m, S x := by
  have leftMem : l ∈ Ico l u := ⟨le_rfl,hm.1.trans hm.2⟩
  have middleMem : m ∈ Ico l u := ⟨hm.1.le,hm.2⟩
  have pair (x : ℝ) (hx : x ∈ Icc l m) : 2*Real.sqrt (S m) ≤ S x + S (l+m-x) := by
    let t := (x-l)/(m-l)
    have t0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hm.1).le
    have t1 : t ≤ 1 := (div_le_iff₀ (sub_pos.mpr hm.1)).mpr (by linarith [hx.2])
    have hg : t*(m-l)=x-l := div_mul_cancel₀ _ (sub_ne_zero.mpr hm.1.ne')
    have aeq : (1-t) • l + t • m = x := by simp only [smul_eq_mul]; linarith only [hg]
    have beq : t • l + (1-t) • m = l+m-x := by simp only [smul_eq_mul]; linarith only [hg]
    have Ax : (1-t) • Real.log (S l) + t • Real.log (S m) ≤ Real.log (S ((1-t) • l + t • m)) :=
      logS.2 leftMem middleMem (by linarith) t0 (by ring)
    have Bx : t • Real.log (S l) + (1-t) • Real.log (S m) ≤ Real.log (S (t • l + (1-t) • m)) :=
      logS.2 leftMem middleMem t0 (by linarith) (by ring)
    rw [aeq] at Ax
    rw [beq] at Bx
    simp only [smul_eq_mul] at Ax Bx
    have lie : Real.log (S l) + Real.log (S m) ≤ Real.log (S x) + Real.log (S (l+m-x)) :=
      by linarith only [Ax,Bx]
    have px : x ∈ Ico l u := ⟨hx.1,hx.2.trans_lt hm.2⟩
    have py : l+m-x ∈ Ico l u := ⟨by linarith [hx.2],by linarith [hx.1,hm.2]⟩
    have exp := Real.exp_le_exp.mpr lie
    simp only [Real.exp_add, Real.exp_log (Spos _ middleMem),
      Real.exp_log (Spos _ px), Real.exp_log (Spos _ py), left, Real.log_one, Real.exp_zero, one_mul] at exp
    have sm := Real.sq_sqrt (Spos _ middleMem).le
    have rt := Real.sqrt_nonneg (S m)
    have hsq : (2*Real.sqrt (S m))^2 ≤ (S x + S (l+m-x))^2 :=
      by nlinarith only [sm, exp, sq_nonneg (S x - S (l+m-x))]
    by_contra! contra
    have suma : 0 < (2*Real.sqrt (S m))+(S x+S (l+m-x)) := by linarith [Spos _ px, Spos _ py]
    have cross := mul_pos (sub_pos.mpr contra) suma
    nlinarith only [cross,hsq]
  have flux : Continuous (fun x => S (l+m-x)) := hc.comp (by fun_prop)
  have h := intervalIntegral.integral_mono_on (μ := volume) hm.1.le (continuous_const.intervalIntegrable l m)
    ((hc.add flux).intervalIntegrable l m) pair
  change (∫ _ in l..m, 2*Real.sqrt (S m)) ≤ ∫ x in l..m, S x + S (l+m-x) at h
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_add (hc.intervalIntegrable l m) (flux.intervalIntegrable l m),
    intervalIntegral.integral_comp_sub_left S (l+m)] at h
  have eq1 : l+m-m=l := by ring
  have eq2 : l+m-l=m := by ring
  rw [eq1,eq2] at h
  nlinarith only [h]

private lemma elementary_exp_bounds :
    (4/11 : ℝ) < Real.exp (-1) ∧ (1/5 : ℝ) < Real.exp (-(3/2)) ∧
      (25/64 : ℝ) < Real.exp (-(93/100)) := by
  have e : Real.exp 1 < 68/25 := Real.exp_one_lt_d9.trans (by norm_num)
  have one : (4/11 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg, ← one_div]
    exact (lt_div_iff₀ (Real.exp_pos 1)).2 (by linarith)
  have cube : Real.exp 1 ^ (3:ℕ) ≤ (68/25 : ℝ)^3 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le e.le _
  have power : Real.exp (3/2)^2 = Real.exp 1 ^ (3:ℕ) := by
    rw [pow_two, ← Real.exp_add, Real.exp_one_pow]
    norm_num
  have p : Real.exp (3/2) < 5 := by
    by_contra! no
    have small := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) no 2
    linarith only [cube,power,small]
  have two : (1/5 : ℝ) < Real.exp (-(3/2)) := by
    rw [Real.exp_neg, ← one_div]
    exact (lt_div_iff₀ (Real.exp_pos _)).2 (by linarith)
  have eform : Real.exp 1 = Real.exp (93/100) * Real.exp (7/100) := by
    rw [← Real.exp_add]
    norm_num
  have lower := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (7/100))
    (Real.exp_pos (93/100)).le
  have h : Real.exp (93/100) < 64/25 := by nlinarith only [lower,eform,e]
  have three : (25/64 : ℝ) < Real.exp (-(93/100)) := by
    rw [Real.exp_neg, ← one_div]
    exact (lt_div_iff₀ (Real.exp_pos _)).2 (by linarith)
  exact ⟨one,two,three⟩

private lemma small_quantile {F : ℝ → ℝ} {l m u d : ℝ}
    (hm : m ∈ Ioo l u) (fc : Continuous F) (Fu : F u = 1)
    (fp : ∀ x ∈ Ioc l u, 0 < F x) (fmax : ∀ x ∈ Icc l u, F x ≤ 1)
    (logF : ConcaveOn ℝ (Ioc l u) (fun x => Real.log (F x)))
    (dh : HasDerivAt F d m) (dp : 0 < d)
    (balance : (∫ x in l..m, F x) = ∫ x in m..u, 1-F x)
    (small : F m < 25/64) :
    (4/11 : ℝ) < F m ∧ (∫ x in l..m,F x) ≤ (8/15) * F m * (m-l) := by
  let A := F m
  let D := m-l
  let h := d/A
  have dm : m ∈ Ioc l u := ⟨hm.1, hm.2.le⟩
  have ap : 0 < A := fp m dm
  have a1 : A < 1 := lt_trans small (by norm_num)
  have hp : 0 < h := div_pos dp ap
  have Dp : 0 < D := sub_pos.mpr hm.1
  have tang (t : ℝ) (ht : t ∈ Ioc l u) : F t ≤ A * Real.exp (h*(t-m)) :=
    exp_envelope logF dm ht ap (fp t ht) (dh.log ap.ne')
  have cExp (k : ℝ) : Continuous (fun t => A*Real.exp (k*(t-m))) := by fun_prop
  have left := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hm.1.le
    (fc.intervalIntegrable l m) ((cExp h).intervalIntegrable l m)
    (fun x hx => tang x ⟨hx.1, hx.2.trans hm.2 |>.le⟩)
  rw [intervalIntegral.integral_const_mul, int_exp_affine _ _ h _ hp.ne',
    sub_self, mul_zero, Real.exp_zero, ← mul_div_assoc] at left
  have neglog := Real.log_neg ap a1
  let b := m + (-Real.log A)/h
  have mb : m < b := by
    dsimp [b]
    have p := div_pos (neg_pos.mpr neglog) hp
    linarith
  have bu : b ≤ u := by
    have eu := tang u ⟨hm.1.trans hm.2,le_rfl⟩
    rw [Fu] at eu
    have e : Real.exp (-Real.log A) ≤ Real.exp (h*(u-m)) := by
      rw [Real.exp_neg, Real.exp_log ap, ← one_div]
      exact (div_le_iff₀ ap).2 (by simpa only [mul_comm] using eu)
    have le := (div_le_iff₀ hp).2 (by
      simpa only [mul_comm] using Real.exp_le_exp.mp e : -Real.log A ≤ (u-m)*h)
    dsimp [b]
    linarith
  have right : (∫ x in m..b, 1-A*Real.exp (h*(x-m))) ≤ ∫ x in m..b, 1-F x :=
    intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) mb.le
    ((continuous_one.sub (cExp h)).intervalIntegrable m b)
    ((continuous_one.sub fc).intervalIntegrable m b) (fun x hx => by
      have le := tang x ⟨hm.1.trans hx.1,hx.2.le.trans bu⟩
      change 1-A*Real.exp (h*(x-m)) ≤ 1-F x
      linarith)
  have ex : h*(b-m) = -Real.log A := by
    dsimp [b]
    field_simp
    ring
  rw [intervalIntegral.integral_sub (continuous_one.intervalIntegrable m b)
    ((cExp h).intervalIntegrable m b), intervalIntegral.integral_const, smul_eq_mul, mul_one,
    intervalIntegral.integral_const_mul, int_exp_affine _ _ h _ hp.ne', ex, sub_self, mul_zero,
    Real.exp_zero, Real.exp_neg, Real.exp_log ap] at right
  have expand : b-m-A*((A⁻¹-1)/h) = (-Real.log A-1+A)/h := by
    dsimp [b]
    field_simp
    ring
  rw [expand] at right
  have add := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    ((continuous_one.sub fc).intervalIntegrable m b) ((continuous_one.sub fc).intervalIntegrable b u)
  change (∫ x in m..b, (1-F x)) + (∫ x in b..u, (1-F x)) = (∫ x in m..u, (1-F x)) at add
  have posRight : 0 ≤ ∫ x in b..u, 1-F x :=
    intervalIntegral.integral_nonneg bu (fun x hx => sub_nonneg.mpr
      (fmax x ⟨hm.1.le.trans (mb.le.trans hx.1),hx.2⟩))
  have both : (-Real.log A-1+A)/h ≤ A*(1-Real.exp (h*(l-m)))/h :=
    right.trans (by linarith only [left,balance,add,posRight])
  have cmp := (div_le_div_iff_of_pos_right hp).mp both
  have e₀ : A*Real.exp (-h*D) ≤ 1+Real.log A := by
    have form : -h*D = h*(l-m) := by dsimp [D]; ring
    rw [form]
    linarith only [cmp]
  obtain ⟨low,elow,ec⟩ := elementary_exp_bounds
  have logLower : -1 < Real.log A := by
    have := mul_pos ap (Real.exp_pos (-h*D))
    linarith only [e₀,this]
  have Agt : (4/11 : ℝ) < A :=
    low.trans (by simpa only [Real.exp_log ap] using Real.exp_lt_exp.mpr logLower)
  have logUpper : Real.log A < -(93/100) :=
    (Real.log_lt_iff_lt_exp ap).2 (small.trans ec)
  have fast : (3/2 : ℝ) ≤ h*D := by
    by_contra! slow
    have ee := Real.exp_le_exp.mpr (show -(3/2 : ℝ) ≤ -h*D by linarith)
    have lower := mul_le_mul_of_nonneg_left (elow.le.trans ee) ap.le
    linarith only [lower,e₀,Agt,logUpper]
  let k := (3/2 : ℝ)/D
  have kp : 0 < k := div_pos (by norm_num) Dp
  have kh : k ≤ h := (div_le_iff₀ Dp).2 fast
  have left' := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hm.1.le
    (fc.intervalIntegrable l m) ((cExp k).intervalIntegrable l m)
    (fun x hx => (tang x ⟨hx.1,hx.2.trans hm.2 |>.le⟩).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_right kh (sub_nonpos.mpr hx.2.le))) ap.le))
  have expPoint : k*(l-m) = -(3/2) := by
    dsimp [k,D]
    field_simp [sub_ne_zero.mpr hm.1.ne']
    ring
  rw [intervalIntegral.integral_const_mul, int_exp_affine _ _ k _ kp.ne',
    sub_self, mul_zero, Real.exp_zero, expPoint] at left'
  refine ⟨Agt,left'.trans ?_⟩
  have kest : (1-Real.exp (-(3/2)))/k ≤ (8/15)*D := by
    apply (div_le_iff₀ kp).2
    have eq : (8/15 : ℝ)*D*k = 4/5 := by
      dsimp [k]
      field_simp
      ring
    rw [eq]
    linarith only [elow]
  have out := mul_le_mul_of_nonneg_left kest ap.le
  nlinarith only [out]

private lemma analyze_tail {f : ℝ → ℝ} {l u : ℝ} (hl : 0 ≤ l) (bounds : l < u)
    (hc : Continuous f) (hd : ∀ x ∈ Ioo l u, DifferentiableAt ℝ f x)
    (nn : ∀ x ∈ Icc l u, 0 ≤ f x) (pos : ∀ x ∈ Ioo l u, 0 < f x)
    (lc : ConcaveOn ℝ (Ioo l u) (fun x => Real.log (f x)))
    (mass : (∫ x in l..u,f x)=1) :
    let m := ∫ x in l..u, x*f x
    (∫ x in m..u, cdf f l x * survival f l x) ≤ m*(cdf f l m)^2 := by
  let m := ∫ x in l..u, x*f x
  let F := cdf f l
  let S := survival f l
  let A := F m
  let D := m-l
  let L := ∫ x in l..m, F x
  change (∫ x in m..u,F x*S x) ≤ m*A^2
  have mu : m ∈ Ioo l u := mean_inside bounds hc nn pos mass
  have Dp : 0 < D := sub_pos.mpr mu.1
  have fc : Continuous F := cdf_cont hc l
  have sc : Continuous S := surv_cont hc l
  have Fl : F l = 0 := intervalIntegral.integral_same
  have Fu : F u = 1 := mass
  have Sl : S l = 1 := by change 1 - F l = 1; rw [Fl,sub_zero]
  have sDef (x : ℝ) : S x = 1 - F x := rfl
  have FP : ∀ x ∈ Ioc l u, 0 < F x := fun _ h => cdf_pos hc nn pos h
  have SP : ∀ x ∈ Ico l u, 0 < S x := fun _ h => surv_pos hc nn pos mass h
  have ap : 0 < A := FP m ⟨mu.1,mu.2.le⟩
  have smp : 0 < S m := SP m ⟨mu.1.le,mu.2⟩
  have a1 : A < 1 := by
    change 0 < (1:ℝ)-A at smp
    linarith
  have SN (x : ℝ) (hx : x ∈ Icc l u) : 0 ≤ S x := by
    change 0 ≤ survival f l x
    rw [surv_integral hc mass]
    exact intervalIntegral.integral_nonneg hx.2 (fun y hy => nn y ⟨hx.1.trans hy.1,hy.2⟩)
  have Fmax (x : ℝ) (hx : x ∈ Icc l u) : F x ≤ 1 := by
    have h := SN x hx
    rw [sDef] at h
    linarith
  have bal : L = ∫ x in m..u, S x := cdf_mean_balance hc rfl mass
  obtain ⟨logF,logS⟩ := log_distributions hc hd nn pos lc mass
  have sq := square_tail mu sc SP logS
  change S m / 2 * (∫ x in m..u,S x) ≤ (∫ x in m..u,S x ^ 2) at sq
  rw [← bal] at sq
  have eq (x : ℝ) : F x*S x = S x - S x^2 := by rw [sDef]; ring
  simp_rw [eq]
  have sc2 : Continuous (fun x => S x^2) := sc.pow 2
  rw [intervalIntegral.integral_sub (sc.intervalIntegrable m u) (sc2.intervalIntegrable m u), ← bal]
  have estimate : L - (∫ x in m..u,S x^2) ≤ (1+A)/2*L := by
    change (1-A)/2*L ≤ _ at sq
    linarith only [sq]
  apply estimate.trans
  have mult : 0 ≤ (1+A)/2 := by positivity
  have target : (1+A)/2*L ≤ D*A^2 := by
    by_cases large : 25/64 ≤ A
    · have reflect := reflect_survival mu sc Sl SP logS
      have intS : (∫ x in l..m,S x) = D-L := by
        simp_rw [sDef]
        rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable l m)
          (fc.intervalIntegrable l m), intervalIntegral.integral_const,smul_eq_mul,mul_one]
      rw [intS] at reflect
      let r := Real.sqrt (1-A)
      have r0 : 0 ≤ r := Real.sqrt_nonneg _
      have rSq : r^2 = 1-A := Real.sq_sqrt (by linarith only [a1])
      have left : L ≤ D*(1-r) := by
        change D*r ≤ D-L at reflect
        linarith
      have rb : r ≤ 2*A := Real.sqrt_le_iff.2 ⟨by positivity,by
        nlinarith only [large, sq_nonneg (A-25/64)]⟩
      have rcmp := mul_le_mul_of_nonneg_left rb r0
      have combine : (1-r)*(1+r)=A := by nlinarith only [rSq]
      have am : (1+A)/2 ≤ A*(1+r) := by nlinarith only [rcmp,rSq]
      have result : (1+A)/2*(1-r) ≤ A^2 := by
        apply (mul_le_mul_iff_right₀ (by positivity : 0 < 1+r)).1
        have reorg : (1+r)*((1+A)/2*(1-r)) = ((1+A)/2)*A := by
          calc
            _ = ((1+A)/2)*((1-r)*(1+r)) := by ring
            _ = _ := by rw [combine]
        rw [reorg]
        nlinarith only [mul_le_mul_of_nonneg_right am ap.le]
      have est := mul_le_mul_of_nonneg_left left mult
      nlinarith only [est,mul_le_mul_of_nonneg_left result Dp.le]
    · have desc : HasDerivAt F (f m) m := cdf_deriv hc l m
      have ⟨amin,inactive⟩ := small_quantile mu fc Fu FP Fmax logF desc (pos m mu) bal (lt_of_not_ge large)
      change (4/11 : ℝ) < A at amin
      change L ≤ (8/15)*A*D at inactive
      have factor : (1+A)/2*(8/15) ≤ A := by linarith only [amin]
      have est := mul_le_mul_of_nonneg_left inactive mult
      have gap := mul_le_mul_of_nonneg_right factor (mul_nonneg ap.le Dp.le)
      nlinarith only [est,gap]
  exact target.trans (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (sq_nonneg _))

end LogConcaveTail

open LogConcaveTail MeasureTheory Set
open scoped Interval Topology

theorem OMA.solution : type_of% @OMA.S_mse_3400484.main := by
  intro l u f hl ulu hd nn pos lc mass
  let cap (x : ℝ) := max l (min x u)
  let g := f ∘ cap
  have caprange (x : ℝ) : cap x ∈ Icc l u := ⟨le_max_left _ _, max_le ulu.le (min_le_right _ _)⟩
  have gcont : Continuous g :=
    hd.continuousOn.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) caprange
  have g_eq (x : ℝ) (hx : x ∈ Icc l u) : g x=f x := by
    simp only [g,Function.comp_apply, cap,min_eq_left hx.2,max_eq_right hx.1]
  have dd (x : ℝ) (hx : x ∈ Ioo l u) : DifferentiableAt ℝ g x := by
    have neigh := Icc_mem_nhds hx.1 hx.2
    have ev : g =ᶠ[𝓝 x] f := Filter.eventually_of_mem neigh g_eq
    exact ev.differentiableAt_iff.mpr ((hd x (Ioo_subset_Icc_self hx)).differentiableAt neigh)
  have gn (x : ℝ) (hx : x ∈ Icc l u) : 0 ≤ g x := by rw [g_eq x hx]; exact nn x hx
  have gp (x : ℝ) (hx : x ∈ Ioo l u) : 0 < g x := by
    rw [g_eq x (Ioo_subset_Icc_self hx)]
    exact pos x hx
  have gc : ConcaveOn ℝ (Ioo l u) (fun x => Real.log (g x)) := by
    refine ⟨convex_Ioo l u, ?_⟩
    intro x hx y hy a b ha hb hab
    have mix : a • x + b • y ∈ Ioo l u := (convex_Ioo l u) hx hy ha hb hab
    simp only [g_eq x (Ioo_subset_Icc_self hx),g_eq y (Ioo_subset_Icc_self hy),
      g_eq _ (Ioo_subset_Icc_self mix)]
    exact lc.2 hx hy ha hb hab
  have mass_eq : (∫ x in l..u,g x) = ∫ x in l..u,f x := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ulu.le]
    exact g_eq
  have gmass := mass_eq.trans mass
  have meanEq : (∫ x in l..u,x*g x) = OMA.S_mse_3400484.mean f l u := by
    unfold OMA.S_mse_3400484.mean
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ulu.le]
    exact fun x hx => congrArg (fun y => x*y) (g_eq x hx)
  have mu := mean_inside ulu gcont gn gp gmass
  have hb := analyze_tail hl ulu gcont dd gn gp gc gmass
  dsimp only at hb
  rw [meanEq] at hb mu
  let m := OMA.S_mse_3400484.mean f l u
  change (∫ x in m..u,cdf g l x*survival g l x) ≤ m*(cdf g l m)^2 at hb
  change (∫ x in m..u,OMA.S_mse_3400484.cdf f l x * (1-OMA.S_mse_3400484.cdf f l x)) ≤
    m*(OMA.S_mse_3400484.cdf f l m)^2
  have cdfEq (x : ℝ) (hx : x ∈ Icc l u) : cdf g l x = OMA.S_mse_3400484.cdf f l x := by
    unfold cdf OMA.S_mse_3400484.cdf
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hx.1]
    exact fun y hy => g_eq y ⟨hy.1,hy.2.trans hx.2⟩
  have matchTail : (∫ x in m..u,cdf g l x*survival g l x) =
      ∫ x in m..u, OMA.S_mse_3400484.cdf f l x*(1-OMA.S_mse_3400484.cdf f l x) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le mu.2.le]
    intro x hx
    dsimp only [survival]
    rw [cdfEq x ⟨mu.1.le.trans hx.1,hx.2⟩]
  rwa [matchTail, cdfEq m (Ioo_subset_Icc_self mu)] at hb
