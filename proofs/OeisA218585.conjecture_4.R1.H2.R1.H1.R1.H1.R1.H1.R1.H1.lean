import OMAReductions.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1
import Mathlib

-- Credit: @JaviSoto
/-! The nontrivial angular character on the Eisenstein lattice. H1 is an
archimedean lattice cancellation statement; H2 is the Euler factorization in
the region of absolute convergence. Removing the ramified factor at 3 gives
zero logarithmic-derivative coefficient there, as the parent requires. -/
namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1
open OeisA218585 Real Filter ArithmeticFunction LSeries
open scoped Topology

/-- Holomorphic continuation of the lattice sum in each nonzero angular mode. -/
def H1 : Prop :=
  let z (u : ℤ × ℤ) : ℂ := u.1 + u.2 * ((1+Complex.I*(Real.sqrt 3 : ℂ))/2)
  let S (m : ℕ) (s : ℂ) := ∑' u : ℤ × ℤ, if z u=0 then (0:ℂ) else
    (z u/(‖z u‖:ℂ))^m*(‖z u‖:ℂ)^(-2*s)
  ∀ m : ℕ, m ≠ 0 → ∃ (F : ℂ → ℂ), (∀ s : ℂ, 1 ≤ s.re → AnalyticAt ℂ F s) ∧
    ∀ s : ℂ, 1<s.re → F s = S m s

/-- Euler factorization into split conjugate primes and norm-square inert primes.
The six units account for the division by six; the factor at three is removed. -/
def H2 : Prop :=
  let z (u : ℤ × ℤ) : ℂ := u.1 + u.2 * ((1+Complex.I*(Real.sqrt 3 : ℂ))/2)
  let S (m : ℕ) (s : ℂ) := ∑' u : ℤ × ℤ, if z u=0 then (0:ℂ) else
    (z u/(‖z u‖:ℂ))^m*(‖z u‖:ℂ)^(-2*s)
  let θ (k p : ℕ) := (k:ℝ)*(6*(⟨(xp p:ℝ)+(yp p:ℝ)/2,√3*(yp p:ℝ)/2⟩:ℂ).arg)
  let phase (k n : ℕ) : ℝ :=
    let p := n.minFac
    let j := n.factorization p
    if p%3=1 then cos (j*θ k p) else if p%3=2 ∧ Even j then 1 else 0
  let a (k n : ℕ) : ℂ := ((Λ n*phase k n : ℝ):ℂ)
  let b (k n : ℕ) : ℂ := a k n/(Real.log n:ℝ)
  ∀ k : ℕ, k≠0 → ∀ s : ℂ, 1<s.re →
    (1-(-1:ℂ)^k*(3:ℂ)^(-s))*(S (6*k) s/6) = Complex.exp (2*LSeries (b k) s)

theorem main : H1 → H2 → OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro lattice factors k hk
  let z (u : ℤ × ℤ) : ℂ := u.1 + u.2 * ((1+Complex.I*(Real.sqrt 3 : ℂ))/2)
  let S (m : ℕ) (s : ℂ) := ∑' u : ℤ × ℤ, if z u=0 then (0:ℂ) else
    (z u/(‖z u‖:ℂ))^m*(‖z u‖:ℂ)^(-2*s)
  let θ (k p : ℕ) := (k:ℝ)*(6*(⟨(xp p:ℝ)+(yp p:ℝ)/2,√3*(yp p:ℝ)/2⟩:ℂ).arg)
  let phase (k n : ℕ) : ℝ :=
    let p := n.minFac
    let j := n.factorization p
    if p%3=1 then cos (j*θ k p) else if p%3=2 ∧ Even j then 1 else 0
  let a (k n : ℕ) : ℂ := ((Λ n*phase k n : ℝ):ℂ)
  let b (k n : ℕ) : ℂ := a k n/(Real.log n:ℝ)
  obtain ⟨F,an,agree⟩ := lattice (6*k) (Nat.mul_ne_zero (by decide) hk)
  let L (s : ℂ) := (1-(-1:ℂ)^k*(3:ℂ)^(-s))*(F s/6)
  let E (s : ℂ) := Complex.exp (2*LSeries (b k) s)
  have cont (s : ℂ) (hs : 1<s.re) : L s=E s := by
    dsimp only [L,E]; rw [agree s hs]; exact factors k hk s hs
  have ba (n : ℕ) : ‖a k n‖ ≤ Λ n := by
    have h : |phase k n| ≤ 1 := by dsimp [phase]; split_ifs <;> simp [abs_cos_le_one]
    simpa [a,abs_mul,abs_of_nonneg vonMangoldt_nonneg] using
      mul_le_mul_of_nonneg_left h (vonMangoldt_nonneg (n:=n))
  have bb (n : ℕ) : ‖b k n‖ ≤ 1 := by
    by_cases hn : n ≤ 1
    · interval_cases n <;> simp [b,a]
    · have pos := Real.log_pos (by exact_mod_cast (show 1<n by omega) : (1:ℝ)<n)
      change ‖a k n / ((Real.log n : ℝ) : ℂ)‖ ≤ 1
      have nlog : ‖((Real.log n:ℝ):ℂ)‖ = Real.log n := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos]
      rw [norm_div,nlog,div_le_one pos]
      exact (ba n).trans vonMangoldt_le_log
  have logb : LSeries.logMul (b k)=a k := by
    funext n
    by_cases hn : n≤1
    · interval_cases n <;> simp [LSeries.logMul,b,a]
    · have pos := Real.log_pos (by exact_mod_cast (show 1<n by omega) : (1:ℝ)<n)
      have nz : ((Real.log n:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pos.ne'
      simp only [LSeries.logMul,b,←Complex.natCast_log]
      field_simp
  refine ⟨L,a k,?_,fun s hs => (cont s hs) ▸ Complex.exp_ne_zero _,ba,?_,?_⟩
  · intro s hs
    have d := an s hs
    dsimp only [L]
    rw [show (fun z : ℂ => (1-(-1:ℂ)^k*(3:ℂ)^(-z))*(F z/6)) =
      (fun z : ℂ => (1-(-1:ℂ)^k*Complex.exp (Complex.log 3*(-z)))*(F z/6)) by
      funext z; rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]]
    fun_prop
  · intro p hp; simp [a,phase,θ,hp.minFac_eq,hp.factorization_self]
  · intro s hs
    have ac : abscissaOfAbsConv (b k) ≤ (1:ℝ) :=
      abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
        LSeriesSummable_of_bounded_of_one_lt_re (m:=1) (fun n _ => bb n) (by simpa using hy)
    have hd := @LSeries_hasDerivAt (b k) s (ac.trans_lt (by exact_mod_cast hs))
    rw [logb] at hd
    have d := ((hd.const_mul (2:ℂ)).cexp).deriv
    have e : L =ᶠ[𝓝 s] E := by
      filter_upwards [(isOpen_lt (continuous_const (X:=ℂ)) Complex.continuous_re).mem_nhds hs] with z hz
      exact cont z hz
    rw [e.deriv_eq,cont s hs]
    dsimp only [E]
    rw [d]; field_simp [Complex.exp_ne_zero]

end OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1

section
/- Absolute convergence and locally uniform convergence for angular characters
on translates of the Eisenstein lattice. -/

open Complex Real Filter Finset Set
open scoped Topology
namespace OMA.AngularTail

noncomputable def z (u : ℤ × ℤ) : ℂ :=
  (u.1 : ℂ) + u.2 * ((1 + I * (Real.sqrt 3 : ℂ))/2)

noncomputable def g (m : ℕ) (s x : ℂ) : ℂ :=
  if x = 0 then 0 else (x/(‖x‖:ℂ))^m * (‖x‖:ℂ)^(-2*s)

theorem norm_g (m : ℕ) (s x : ℂ) (hx : x ≠ 0) :
    ‖g m s x‖ = ‖x‖^(-2*s.re) := by
  simp [g,hx,norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hx),
    Complex.mul_re, norm_ne_zero_iff.mpr hx]

theorem differentiable_g (m : ℕ) (x : ℂ) : Differentiable ℂ (fun s => g m s x) := by
  by_cases h : x=0
  · simp [g,h]
  · simp only [g,if_neg h]
    apply Differentiable.const_mul
    exact (differentiable_id.const_mul (-2:ℂ)).const_cpow
      (Or.inl (by exact_mod_cast norm_ne_zero_iff.mpr h))

theorem lattice_norm (u : ℤ × ℤ) : ‖u‖ ≤ 2*‖z u‖ := by
  have re : (z u).re = (u.1:ℝ) + u.2 / 2 := by
    simp [z,Complex.add_re,Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im]; ring
  have im : (z u).im = (u.2:ℝ)*Real.sqrt 3 / 2 := by
    simp [z,Complex.add_im,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im]; ring
  have hr := Complex.abs_re_le_norm (z u)
  have hi := Complex.abs_im_le_norm (z u)
  rw [re] at hr
  rw [im,abs_div,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] at hi
  norm_num at hi
  have hs : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  have hb : |(u.2:ℝ)| ≤ 2*‖z u‖ := by nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg (u.2:ℝ))]
  change max ‖u.1‖ ‖u.2‖ ≤ _
  simp only [Int.norm_eq_abs, max_le_iff]
  refine ⟨?_,hb⟩
  rw [abs_le] at hr hb ⊢
  constructor <;> linarith [hr.1,hr.2,hb.1,hb.2]

theorem lattice_summable (w : ℂ) (hw : w ≠ 0) (b : ℝ) (hb : 2 < b) :
    Summable (fun u : ℤ × ℤ => ‖w*z u‖^(-b)) := by
  have base : Summable (fun u : ℤ×ℤ => ‖u‖^(-b)) := by
    let eqv := (finTwoArrowEquiv ℤ).symm
    have h := eqv.summable_iff.mpr (EisensteinSeries.summable_one_div_norm_rpow hb)
    apply h.congr
    intro u
    change ‖![u.1,u.2]‖^(-b) = ‖u‖^(-b)
    congr 1
    rw [EisensteinSeries.norm_eq_max_natAbs,Prod.norm_def]
    simp [Int.norm_eq_abs]
  apply (base.mul_left ((‖w‖/2)^(-b))).of_nonneg_of_le (fun u => Real.rpow_nonneg (norm_nonneg _) _)
  intro u
  by_cases hu : u=0
  · simp [hu,z,Real.zero_rpow (by linarith : -b≠0)]
  rw [←Real.mul_rpow (by positivity) (norm_nonneg u),norm_mul]
  apply Real.rpow_le_rpow_of_nonpos (mul_pos (by positivity) (norm_pos_iff.mpr hu)) _ (by linarith)
  have h := mul_le_mul_of_nonneg_left (lattice_norm u) (norm_nonneg w)
  linarith

theorem original_scaled (m : ℕ) (w s : ℂ) (hw : w≠0) (hs : 1 < s.re) :
    Summable (fun u : ℤ×ℤ => ‖g m s (w*z u)‖) := by
  have h := lattice_summable w hw (2*s.re) (by linarith)
  apply h.congr
  intro u
  by_cases hz : w*z u=0
  · simp [hz,g,Real.zero_rpow (by linarith : -(2*s.re)≠0)]
  · rw [norm_g _ _ _ hz]; ring_nf

theorem original (m : ℕ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun u : ℤ×ℤ => ‖g m s (z u)‖) := by
  simpa only [one_mul] using original_scaled m 1 s one_ne_zero hs

private theorem powers (u v : ℂ) (hu : ‖u‖=1) (hv : ‖v‖=1) (m : ℕ) :
    ‖u^m-v^m‖ ≤ m*‖u-v‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show u^(m+1)-v^(m+1) = (u^m-v^m)*u+v^m*(u-v) by ring]
    have h := norm_add_le ((u^m-v^m)*u) (v^m*(u-v))
    simp only [norm_mul,norm_pow,hu,hv,one_pow,mul_one,one_mul] at h
    push_cast
    linarith

private theorem dir_diff (x j : ℂ) (hx : x≠0) (hx' : x+j≠0) :
    ‖(x+j)/(‖x+j‖:ℂ)-x/(‖x‖:ℂ)‖*‖x‖ ≤ 2*‖j‖ := by
  let u := (x+j)/(‖x+j‖:ℂ)
  let v := x/(‖x‖:ℂ)
  have hu : ‖u‖=1 := by simp [u,norm_ne_zero_iff.mpr hx']
  have ua : u*(‖x+j‖:ℂ)=x+j := div_mul_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.mpr hx')
  have va : v*(‖x‖:ℂ)=x := div_mul_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.mpr hx)
  have eq : (u-v)*(‖x‖:ℂ)=j+u*((‖x‖:ℂ)-‖x+j‖) := by linear_combination ua - va
  have e := norm_add_le j (u*((‖x‖:ℂ)-‖x+j‖))
  rw [←eq,norm_mul,norm_mul,hu,one_mul,←Complex.ofReal_sub] at e
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] at e
  have d := abs_norm_sub_norm_le x (x+j)
  simp only [sub_add_cancel_left,norm_neg] at d
  change ‖u-v‖*‖x‖ ≤ _
  linarith

/-- Uniform translation estimate on an open half-plane, with an absolute
majorant of order |x|^(-5/2) away from the origin. -/
theorem tail (m : ℕ) (s x j : ℂ) (hs : 3/4 ≤ s.re)
    (hr : 2 ≤ ‖x‖) (hj : 2*‖j‖ ≤ ‖x‖) :
    ‖g m s (x+j)-g m s x‖ ≤ (2*‖s‖+m)*‖j‖*(‖x‖/2)^(-(5/2:ℝ)) := by
  let R := ‖x‖/2
  let h := -2*s
  have R1 : 1 ≤ R := by dsimp [R]; linarith
  have Rp : 0 < R := by linarith
  have re : h.re = -2*s.re := by simp [h,Complex.mul_re]
  have hn : h≠0 := by intro e; rw [e] at re; simp at re; linarith
  have rx : R≤‖x‖ := by dsimp [R]; linarith
  have rj : R≤‖x+j‖ := by
    have hh := norm_sub_le (x+j) j
    rw [add_sub_cancel_right] at hh
    dsimp [R]; linarith
  have xpos : x≠0 := norm_pos_iff.mp (Rp.trans_le rx)
  have xjpos : x+j≠0 := norm_pos_iff.mp (Rp.trans_le rj)
  have nh : ‖h‖=2*‖s‖ := by simp [h]
  have derivAt (t : ℝ) (ht : t∈Ici R) := hasDerivAt_ofReal_cpow_const (Rp.trans_le ht).ne' hn
  have bound (t : ℝ) (ht : t∈Ici R) :
      ‖deriv (fun a : ℝ => (a:ℂ)^h) t‖ ≤ 2*‖s‖ * R^(-(5/2:ℝ)) := by
    rw [(derivAt t ht).deriv, norm_mul,nh,Complex.norm_cpow_eq_rpow_re_of_pos (Rp.trans_le ht)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (Real.rpow_le_rpow_of_exponent_le (R1.trans ht) (by simp [re]; linarith : (h-1).re≤-(5/2:ℝ))).trans
      (Real.rpow_le_rpow_of_nonpos Rp ht (by norm_num))
  have radial := (convex_Ici R).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (derivAt t ht).differentiableAt) bound rx rj
  have distnorm := abs_norm_sub_norm_le (x+j) x
  simp only [add_sub_cancel_left] at distnorm
  rw [Real.norm_eq_abs] at radial
  have radial' := radial.trans (mul_le_mul_of_nonneg_left distnorm (by positivity))
  let u := (x+j)/(‖x+j‖:ℂ)
  let v := x/(‖x‖:ℂ)
  have hu : ‖u‖=1 := by simp [u,norm_ne_zero_iff.mpr xjpos]
  have hv : ‖v‖=1 := by simp [v,norm_ne_zero_iff.mpr xpos]
  have dw := dir_diff x j xpos xjpos
  change ‖u-v‖*‖x‖ ≤ _ at dw
  have rad0 : ‖(‖x‖:ℂ)^h‖ ≤ R^(-(5/2:ℝ))*R := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Rp.trans_le rx), ←Real.rpow_add_one Rp.ne',
      show -(5/2:ℝ)+1=-(3/2:ℝ) by norm_num]
    exact (Real.rpow_le_rpow_of_exponent_le (R1.trans rx) (by rw [re]; linarith)).trans
      (Real.rpow_le_rpow_of_nonpos Rp rx (by norm_num))
  have w := mul_le_mul_of_nonneg_right (powers u v hu hv m) (norm_nonneg ((‖x‖:ℂ)^h))
  have angle := w.trans (mul_le_mul_of_nonneg_left rad0 (by positivity))
  have ar : ‖u-v‖*R ≤ ‖j‖ := by dsimp [R]; linarith
  have ang : ‖u^m-v^m‖*‖(‖x‖:ℂ)^h‖ ≤ (m:ℝ)*‖j‖*R^(-(5/2:ℝ)) := by
    nlinarith only [angle,mul_le_mul_of_nonneg_right ar (by positivity : (0:ℝ) ≤ m*R^(-(5/2:ℝ)))]
  rw [g,if_neg xjpos,g,if_neg xpos]
  change ‖u^m*(‖x+j‖:ℂ)^h-v^m*(‖x‖:ℂ)^h‖ ≤ _
  rw [show u^m*(‖x+j‖:ℂ)^h-v^m*(‖x‖:ℂ)^h =
      u^m*((‖x+j‖:ℂ)^h-(‖x‖:ℂ)^h)+(u^m-v^m)*(‖x‖:ℂ)^h by ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_mul,norm_pow,hu,one_pow,one_mul]
  change _ ≤ (2*‖s‖+m)*‖j‖*R^(-(5/2:ℝ))
  nlinarith only [radial',ang]

/-- A single summable majorant works for all complex arguments in the ball
of radius 1/8 about a point on or to the right of Re(s)=1. -/
theorem majorant (m : ℕ) (w j s : ℂ) (hw : w≠0) (hs : 1 ≤ s.re) :
    ∃ M : ℤ×ℤ → ℝ, Summable M ∧ ∀ u t, t∈Metric.ball s (1/8) →
      ‖g m t (w*z u+j)-g m t (w*z u)‖ ≤ M u := by
  classical
  let cut := max 2 (2*‖j‖)
  let G (u : ℤ×ℤ) := cut ≤ ‖w*z u‖
  let F (u : ℤ×ℤ) (t : ℂ) := g m t (w*z u+j)-g m t (w*z u)
  let B := (2*(‖s‖+1)+m)*‖j‖
  let Q (u : ℤ×ℤ) := B*(‖w*z u‖/2)^(-(5/2:ℝ))
  have summ : Summable Q := by
    have hh := (lattice_summable w hw (5/2) (by norm_num)).mul_right ((2:ℝ)^(-(5/2:ℝ)))⁻¹
    apply (hh.mul_left B).congr
    intro u
    change B*(_*_) = B*((‖w*z u‖/2)^(-(5/2:ℝ)))
    rw [Real.div_rpow (norm_nonneg _) (by norm_num : (0:ℝ)≤2),div_eq_mul_inv (‖w*z u‖^_)]
  have ultimately : ∀ᶠ u : ℤ×ℤ in cofinite, G u := by
    have hn : Tendsto (fun u : ℤ×ℤ => ‖u‖) cofinite atTop :=
      tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Topology.IsClosedEmbedding.id
    filter_upwards [hn.eventually_ge_atTop (2*cut/‖w‖)] with u hu
    have h := (div_le_iff₀ (norm_pos_iff.mpr hw)).mp hu
    have h' := mul_le_mul_of_nonneg_right (lattice_norm u) (norm_nonneg w)
    change cut≤‖w*z u‖
    rw [norm_mul]; linarith
  have small (u : ℤ×ℤ) : ∃ c : ℝ, ∀ t ∈ Metric.closedBall s (1/8), ‖F u t‖≤c :=
    (isCompact_closedBall _ _).exists_bound_of_continuousOn
      (((differentiable_g m (w*z u+j)).sub (differentiable_g m (w*z u))).continuous.continuousOn)
  choose c hc using small
  refine ⟨fun u => if G u then Q u else c u,summ.congr_cofinite ?_,?_⟩
  · filter_upwards [ultimately] with u hu; simp [hu]
  intro u t ht
  change _ ≤ if G u then Q u else c u
  by_cases good : G u
  · rw [if_pos good]
    have dist := Metric.mem_ball.mp ht
    rw [dist_eq_norm] at dist
    have nr := norm_sub_le (t-s) (-s)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at nr
    have hre := Complex.abs_re_le_norm (t-s)
    rw [Complex.sub_re,abs_le] at hre
    have h := tail m t (w*z u) j (by linarith [hre.1]) ((le_max_left ..).trans good)
      ((le_max_right ..).trans good)
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg j)
    linarith
  · rw [if_neg good]
    exact hc u t (Metric.ball_subset_closedBall ht)

theorem translated_abs (m : ℕ) (w j s : ℂ) (hw : w≠0) (hs : 1 ≤ s.re) :
    Summable (fun u : ℤ×ℤ => ‖g m s (w*z u+j)-g m s (w*z u)‖) := by
  obtain ⟨M,hM,bound⟩ := majorant m w j s hw hs
  exact hM.of_nonneg_of_le (fun _ => norm_nonneg _) (fun u => bound u s (Metric.mem_ball_self (by norm_num)))

theorem translated (m : ℕ) (w j s : ℂ) (hw : w≠0) (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (fun t => ∑' u : ℤ×ℤ, (g m t (w*z u+j)-g m t (w*z u))) s := by
  obtain ⟨M,hM,bound⟩ := majorant m w j s hw hs
  exact (Complex.differentiableOn_tsum_of_summable_norm hM (fun u =>
    ((differentiable_g m (w*z u+j)).sub (differentiable_g m (w*z u))).differentiableOn)
    Metric.isOpen_ball bound).analyticAt (Metric.ball_mem_nhds _ (by norm_num))

theorem shifted (m : ℕ) (w j s : ℂ) (hw : w≠0) (hs : 1 < s.re) :
    Summable (fun u : ℤ×ℤ => ‖g m s (w*z u+j)‖) :=
  ((translated_abs m w j s hw hs.le).add (original_scaled m w s hw hs)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun u => by
      simpa only [sub_add_cancel] using norm_add_le
        (g m s (w*z u+j)-g m s (w*z u)) (g m s (w*z u)))

end OMA.AngularTail

/- Two different index-seven similarities of the triangular lattice generate
the same coset-cancellation identity but have different angular factors. -/
namespace OMA.AngularSeven
open Complex
abbrev Pair := ℤ × ℤ

def A (u : Pair) : Pair := (2*u.1-u.2,u.1+3*u.2)
def B (u : Pair) : Pair := (3*u.1+u.2,-u.1+2*u.2)
def shift (u : Pair) (j : ℤ) : Pair := (u.1+j,u.2)

def cosA : Fin 7 × Pair ≃ Pair where
  toFun q := shift (A q.2) q.1
  invFun u := let j := (u.1-2*u.2)%7
              let b := (2*u.2-(u.1-j))/7
              (⟨j.toNat,by dsimp [j]; omega⟩,u.2-3*b,b)
  left_inv := by
    rintro ⟨⟨j,hj⟩,a,b⟩
    apply Prod.ext
    · apply Fin.ext; dsimp [shift,A]; omega
    · apply Prod.ext <;> dsimp [shift,A] <;> omega
  right_inv := by
    rintro ⟨x,y⟩
    apply Prod.ext <;> dsimp [shift,A] <;> omega

def cosB : Fin 7 × Pair ≃ Pair where
  toFun q := shift (B q.2) q.1
  invFun u := let j := (u.1+3*u.2)%7
              let b := (u.1-j+3*u.2)/7
              (⟨j.toNat,by dsimp [j]; omega⟩,-u.2+2*b,b)
  left_inv := by
    rintro ⟨⟨j,hj⟩,a,b⟩
    apply Prod.ext
    · apply Fin.ext; dsimp [shift,B]; omega
    · apply Prod.ext <;> dsimp [shift,B] <;> omega
  right_inv := by
    rintro ⟨x,y⟩
    apply Prod.ext <;> dsimp [shift,B] <;> omega

noncomputable def eta : ℂ := (1+I*(Real.sqrt 3 : ℂ))/2
noncomputable def val (u : Pair) : ℂ := u.1 + u.2 * eta

lemma eta_sq : eta^2 = eta-1 := by
  have h : (Real.sqrt 3 : ℂ)^2=3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  unfold eta
  linear_combination (Real.sqrt 3 : ℂ)^2/4*Complex.I_sq - h/4

lemma val_A (u : Pair) : val (A u) = (2+eta)*val u := by
  dsimp [A,val]; push_cast
  linear_combination -(u.2:ℂ)*eta_sq

lemma val_B (u : Pair) : val (B u) = (3-eta)*val u := by
  dsimp [B,val]; push_cast
  linear_combination (u.2:ℂ)*eta_sq

lemma val_shift (u : Pair) (j : ℤ) : val (shift u j)=val u+j := by
  simp [val,shift]; ring

lemma val_injective : Function.Injective val := by
  rintro ⟨a,b⟩ ⟨c,d⟩ eq
  have im := congrArg Complex.im eq
  have re := congrArg Complex.re eq
  simp [val,eta,Complex.mul_im,Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im] at im re
  subst d
  have ac : (a:ℝ) = c := by linarith
  exact Prod.ext (by exact_mod_cast ac) rfl

def residue (u : Pair) : ZMod 7 := (u.1:ZMod 7)+5*(u.2:ZMod 7)

lemma residue_A (u : Pair) : residue (A u)=0 := by
  have h : (7:ZMod 7)=0 := by decide
  dsimp [residue,A]; push_cast; linear_combination ((u.1:ZMod 7)+2*u.2)*h

lemma residue_B (u : Pair) : residue (B u)=5*residue u := by
  have h : (7:ZMod 7)=0 := by decide
  dsimp [residue,B]; push_cast; linear_combination -((u.1:ZMod 7)+2*u.2)*h

lemma distinguish {m : ℕ} (hm : m ≠ 0) : (2+eta)^m ≠ (3-eta)^m := by
  let x : Pair := (1,0)
  have vx (f : Pair → Pair) (c : ℂ) (h : ∀ u, val (f u)=c*val u) (n : ℕ) :
      val ((f^[n]) x) = c^n := by
    induction n with
    | zero => simp [val,x]
    | succ n ih => rw [Function.iterate_succ_apply',h,ih,pow_succ']
  have rb (n : ℕ) : residue ((B^[n]) x)=5^n := by
    induction n with
    | zero => simp [residue,x]
    | succ n ih => rw [Function.iterate_succ_apply',residue_B,ih,pow_succ']
  intro eq
  have same := val_injective ((vx A _ val_A m).trans (eq.trans (vx B _ val_B m).symm))
  have bad := congrArg residue same
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [rb,Function.iterate_succ_apply',residue_A] at bad
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact (pow_ne_zero _ (by decide : (5:ZMod 7)≠0)) bad.symm

end OMA.AngularSeven

namespace OMA.AngularSeven
open Complex
open scoped BigOperators ComplexConjugate

lemma coset_sum (E : Fin 7 × Pair ≃ Pair) (F : Pair → ℂ) (c : ℂ)
    (h : Summable F) (h0 : ∀ u, F (E (0,u)) = c * F u) :
    (∑' u, F u) = (∑ j : Fin 7, ∑' u, (F (E (j,u))-F (E (0,u)))) + 7*c*(∑' u, F u) := by
  have s : Summable (fun q => F (E q)) := E.summable_iff.mpr h
  have eqj (j : Fin 7) : ∑' u, (F (E (j,u))-F (E (0,u))) =
      (∑' u, F (E (j,u))) - c*(∑' u, F u) := by
    rw [(s.prod_factor j).tsum_sub (s.prod_factor 0),←tsum_mul_left]
    simp_rw [h0]
  have tot : (∑' u, F u) = ∑ j : Fin 7, ∑' u, F (E (j,u)) := by
    rw [←E.tsum_eq F,s.tsum_prod,tsum_fintype]
  simp_rw [eqj]
  rw [Finset.sum_sub_distrib,←tot]
  simp; ring

noncomputable def g (m : ℕ) (s z : ℂ) : ℂ :=
  if z=0 then 0 else (z/(‖z‖:ℂ))^m*(‖z‖:ℂ)^(-2*s)

lemma g_mul (m : ℕ) (s z w : ℂ) : g m s (z*w)=g m s z*g m s w := by
  by_cases hz : z=0
  · simp [hz,g]
  by_cases hw : w=0
  · simp [hw,g]
  simp only [g,if_neg (mul_ne_zero hz hw),if_neg hz,if_neg hw,norm_mul,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg z) (norm_nonneg w)]
  rw [mul_div_mul_comm,mul_pow]
  ring

lemma conjugate_factors : star (2+eta) = (3-eta) := by
  rw [show star (2+eta) = conj (2+eta) by rfl]
  have t : conj (2:ℂ)=2 := by exact map_ofNat _ 2
  simp [eta,t]; ring

lemma radius_eq : ‖2+eta‖=‖3-eta‖ := by rw [←conjugate_factors]; exact (Complex.norm_conj _).symm

lemma nonzero_w : 2+eta≠0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [eta,Complex.div_ofNat_re] at this

lemma g_distinguish {m : ℕ} (hm : m≠0) (s : ℂ) : g m s (2+eta) ≠ g m s (3-eta) := by
  have ha := nonzero_w
  have hb : 3-eta≠0 := by
    rw [←conjugate_factors]
    exact (map_ne_zero (starRingEnd ℂ)).mpr ha
  have hn : (‖3-eta‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hb
  simp only [g,if_neg ha,if_neg hb,div_pow,radius_eq]
  intro he
  have eq := mul_right_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hn)) he
  exact distinguish hm ((div_left_inj' (pow_ne_zero m hn)).mp eq)

lemma g_analytic (m : ℕ) (w s : ℂ) : AnalyticAt ℂ (fun t => g m t w) s := by
  by_cases hw : w=0
  · simp only [hw,g,if_true]; exact analyticAt_const
  have hn : (‖w‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  simp only [g,if_neg hw,Complex.cpow_def_of_ne_zero hn]
  fun_prop

end OMA.AngularSeven

namespace OMA.AngularSeven
open Complex
open scoped BigOperators

noncomputable def S (m : ℕ) (s : ℂ) := ∑' u : Pair, g m s (val u)
noncomputable def T (m : ℕ) (w s : ℂ) :=
  ∑ j : Fin 7, ∑' u : Pair, (g m s (w*val u+j)-g m s (w*val u))
noncomputable def extension (m : ℕ) (s : ℂ) :=
  (T m (3-eta) s-T m (2+eta) s)/(7*(g m s (2+eta)-g m s (3-eta)))

lemma coset_A (m : ℕ) (s : ℂ) (h : Summable (fun u : Pair => g m s (val u))) :
    S m s = T m (2+eta) s + 7*g m s (2+eta)*S m s := by
  have e (j : Fin 7) (u : Pair) : val (cosA (j,u)) = (2+eta)*val u+j := by
    change val (shift (A u) j) = _
    rw [val_shift,val_A]; simp
  have e0 (u : Pair) : val (cosA (0,u)) = (2+eta)*val u := by rw [e]; simp
  have total := coset_sum cosA _ _ h (fun u => by rw [e0,g_mul])
  simpa only [S,T,e0,e] using total

lemma coset_B (m : ℕ) (s : ℂ) (h : Summable (fun u : Pair => g m s (val u))) :
    S m s = T m (3-eta) s + 7*g m s (3-eta)*S m s := by
  have e (j : Fin 7) (u : Pair) : val (cosB (j,u)) = (3-eta)*val u+j := by
    change val (shift (B u) j) = _
    rw [val_shift,val_B]; simp
  have e0 (u : Pair) : val (cosB (0,u)) = (3-eta)*val u := by rw [e]; simp
  have total := coset_sum cosB _ _ h (fun u => by rw [e0,g_mul])
  simpa only [S,T,e0,e] using total

lemma equals_original {m : ℕ} (hm : m≠0) (s : ℂ)
    (h : Summable (fun u : Pair => g m s (val u))) : extension m s = S m s := by
  apply (div_eq_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (g_distinguish hm s)))).mpr
  linear_combination coset_A m s h - coset_B m s h

lemma extension_analytic {m : ℕ} (hm : m≠0) (s : ℂ)
    (H : ∀ w : ℂ, w≠0 → ∀ j : Fin 7, AnalyticAt ℂ
      (fun t => ∑' u : Pair, (g m t (w*val u+j)-g m t (w*val u))) s) :
    AnalyticAt ℂ (extension m) s := by
  have hT (w : ℂ) (hw : w≠0) : AnalyticAt ℂ (T m w) s := by
    apply Finset.analyticAt_fun_sum
    exact fun i _ => H w hw i
  have b : 3-eta≠0 := by
    rw [←conjugate_factors]; exact (map_ne_zero (starRingEnd ℂ)).mpr nonzero_w
  have nn := sub_ne_zero.mpr (g_distinguish hm s)
  exact ((hT _ b).sub (hT _ nonzero_w)).div
    (analyticAt_const.mul ((g_analytic m _ s).sub (g_analytic m _ s))) (mul_ne_zero (by norm_num) nn)

end OMA.AngularSeven
theorem OMA.AngularDeep.analytic : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro m hm
  refine ⟨OMA.AngularSeven.extension m,fun s hs => ?_,fun s hs => ?_⟩
  · apply OMA.AngularSeven.extension_analytic hm
    intro w hw j
    exact OMA.AngularTail.translated m w j s hw hs
  · exact OMA.AngularSeven.equals_original hm s (OMA.AngularTail.original m s hs).of_norm
end

section
/- The Euler logarithm for an Eisenstein angular character. Split primes occur
in conjugate pairs, inert primes have norm p², and the ramified prime is omitted. -/
namespace OMA.AngularEuler
open Real Filter ArithmeticFunction LSeries
open scoped Topology

noncomputable def phase (angle : ℕ → ℝ) (n : ℕ) : ℝ :=
  let p := n.minFac
  let j := n.factorization p
  if p%3 = 1 then cos (j*angle p) else if p%3 = 2 ∧ Even j then 1 else 0

noncomputable def a (angle : ℕ → ℝ) (n : ℕ) : ℂ := ((Λ n * phase angle n : ℝ):ℂ)
noncomputable def b (angle : ℕ → ℝ) (n : ℕ) : ℂ := a angle n / (Real.log n : ℝ)
noncomputable def euler (angle : ℕ → ℝ) (s : ℂ) : ℂ := Complex.exp (2*LSeries (b angle) s)


end OMA.AngularEuler
end

section
/- Euler logarithms for bounded completely multiplicative coefficients.
The prime-power logarithm expansion adapts Mathlib's
`DirichletCharacter.eulerProduct_log_eq_LSeries`,
Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean, copyright (c) 2023
Michael Stoll, released under the Apache License 2.0. Here the coefficients
need not be periodic, and the two factors differ on inert primes. -/

namespace OMA.AngularLog
open Complex Nat Filter ArithmeticFunction EulerProduct
open scoped Topology

noncomputable def lift (v : ℕ→ℂ) : ℕ →*₀ ℂ where
  toFun n := if n=0 then 0 else n.factorization.prod (fun p e => (v p)^e)
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a=0
    · simp [ha]
    by_cases hb : b=0
    · simp [hb]
    simp [ha,hb,Nat.factorization_mul,Finsupp.prod_add_index',pow_add]

@[simp] theorem lift_prime (v : ℕ→ℂ) {p : ℕ} (hp : p.Prime) : lift v p = v p := by
  simp [lift,hp.ne_zero,hp.factorization]

theorem lift_norm (v : ℕ→ℂ) (hv : ∀ p, ‖v p‖≤1) (n : ℕ) : ‖lift v n‖≤1 := by
  by_cases h : n=0
  · simp [h]
  simp only [lift,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,if_neg h,Finsupp.prod,norm_prod,norm_pow]
  exact Finset.prod_le_one (fun _ _ => by positivity) (fun p _ => pow_le_one₀ (norm_nonneg _) (hv p))

noncomputable def left (angle : ℕ→ℝ) (p : ℕ) : ℂ :=
  if p%3=1 then exp ((angle p:ℂ)*I) else if p%3=2 then 1 else 0

noncomputable def right (angle : ℕ→ℝ) (p : ℕ) : ℂ :=
  if p%3=1 then exp (-((angle p:ℂ)*I)) else if p%3=2 then -1 else 0

theorem left_norm (angle : ℕ→ℝ) (p : ℕ) : ‖left angle p‖≤1 := by
  unfold left; split_ifs <;> simp [Complex.norm_exp]

theorem right_norm (angle : ℕ→ℝ) (p : ℕ) : ‖right angle p‖≤1 := by
  unfold right; split_ifs <;> simp [Complex.norm_exp]

noncomputable def coeff (χ : ℕ →*₀ ℂ) (n : ℕ) : ℂ := χ n*Λ n/Real.log n

theorem coeff_norm (χ : ℕ →*₀ ℂ) (hc : ∀ n, ‖χ n‖≤1) (n : ℕ) : ‖coeff χ n‖≤1 := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp [coeff]
  have hn' := Real.log_pos (by exact_mod_cast (show 1 < n by omega) : (1:ℝ)<n)
  simp only [coeff,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldt_nonneg (n:=n)),abs_of_pos hn',div_le_one hn']
  exact (mul_le_of_le_one_left vonMangoldt_nonneg (hc n)).trans vonMangoldt_le_log

theorem exp_series (χ : ℕ →*₀ ℂ) (hc : ∀ n, ‖χ n‖≤1) {s : ℂ} (hs : 1 < s.re) :
    exp (LSeries (coeff χ) s) = LSeries (χ : ℕ→ℂ) s := by
  let f := χ * riemannZetaSummandHom (ne_zero_of_one_lt_re hs)
  have val (n : ℕ) : f n = χ n*(n:ℂ)^(-s) := rfl
  have hf : Summable (fun n => ‖f n‖) := (summable_riemannZetaSummand hs).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => by
      rw [val,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc n))
  have eul := exp_tsum_primes_log_eq_tsum (f:=f) hf
  have logs : ∑' p : Primes, -log (1-f p) = LSeries (coeff χ) s := by
    have hlt (p : Primes) : ‖f p‖ < 1 := hf.of_norm.norm_lt_one (f:=f.toMonoidHom) p.prop.one_lt
    rw [tsum_congr (fun p => (hasSum_taylorSeries_neg_log' (hlt p)).tsum_eq.symm),
      LSeries_def₀ (by simp [coeff])]
    let A (n : ℕ) := coeff χ n * (n:ℂ)^(-s)
    have hA : Summable A := by
      apply (summable_riemannZetaSummand hs).of_norm_bounded
      intro n
      change ‖coeff χ n*(n:ℂ)^(-s)‖ ≤ ‖(n:ℂ)^(-s)‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (coeff_norm χ hc n)
    calc
      _ = ∑' (p : Primes) (k : ℕ), A (p^(k+1)) := by
        refine tsum_congr fun p => tsum_congr fun k => ?_
        have hlog : Complex.log p ≠ 0 := mod_cast p.prop.log_ne_zero
        simp [A,coeff,val,mul_pow,←cpow_nat_mul,←natCast_cpow_natCast_mul,
          vonMangoldt_apply_pow,vonMangoldt_apply_prime p.2,field]
        have he := congrArg Complex.ofReal (Real.log_pow (p:ℝ) (k+1))
        push_cast at he
        rw [Complex.ofReal_log (by positivity),Complex.ofReal_pow,Complex.ofReal_natCast] at he
        rw [he]
        field_simp [hlog]
      _ = ∑' n : {n : ℕ // IsPrimePow n}, A n :=
        tsum_primes_pow_eq (hA.subtype _)
      _ = _ := by
        simp only [div_eq_mul_inv _ (_ ^ _),←cpow_neg]
        apply tsum_subtype_eq_of_support_subset
        intro n hn
        contrapose! hn
        simp [A,coeff,vonMangoldt_eq_zero_iff.mpr hn]
  rw [←logs,eul,LSeries_def₀ (by simp)]
  exact tsum_congr fun n => by rw [val,cpow_neg,div_eq_mul_inv]

theorem trace_power (angle : ℕ→ℝ) (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : j≠0) :
    (left angle p)^j+(right angle p)^j = 2*(AngularEuler.phase angle (p^j):ℂ) := by
  simp only [AngularEuler.phase,hp.pow_minFac hj,Nat.factorization_pow_self hp,left,right]
  by_cases s : p%3=1
  · simp only [if_pos s,←Complex.exp_nat_mul]
    have e : ((j:ℂ)*((angle p:ℂ)*I))=(((j:ℝ)*angle p:ℝ):ℂ)*I := by push_cast; ring
    have e' : ((j:ℂ)* -((angle p:ℂ)*I))=((-(j:ℝ)*angle p:ℝ):ℂ)*I := by push_cast; ring
    rw [e,e',Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I]
    simp [neg_mul,Real.cos_neg,Real.sin_neg]; ring
  · simp only [if_neg s]
    by_cases inert : p%3=2
    · by_cases ev : Even j <;> simp [inert,ev,neg_one_pow_eq_ite]; norm_num
    · simp [inert,zero_pow hj]

theorem coeffs (angle : ℕ→ℝ) :
    coeff (lift (left angle)) + coeff (lift (right angle)) = (2:ℂ) • AngularEuler.b angle := by
  funext n
  by_cases pp : IsPrimePow n
  · obtain ⟨p,j,prime,hj,rfl⟩ := (isPrimePow_def _).mp pp
    have hp := Nat.prime_iff.mpr prime
    have hh := trace_power angle p hp j hj.ne'
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,coeff,map_pow,lift_prime _ hp,
      AngularEuler.b,AngularEuler.a,Complex.ofReal_mul,←add_div,←add_mul,hh]
    ring
  · simp [coeff,AngularEuler.b,AngularEuler.a,vonMangoldt_eq_zero_iff.mpr pp]

theorem product (angle : ℕ→ℝ) (s : ℂ) (hs : 1 < s.re) :
    LSeries (lift (left angle) : ℕ→ℂ) s * LSeries (lift (right angle) : ℕ→ℂ) s =
      AngularEuler.euler angle s := by
  have su (χ : ℕ →*₀ ℂ) (hc : ∀n, ‖χ n‖≤1) :
      LSeriesSummable (coeff χ) s := LSeriesSummable_of_bounded_of_one_lt_re
        (m:=1) (fun n _ => coeff_norm χ hc n) hs
  have hl := lift_norm _ (left_norm angle)
  have hr := lift_norm _ (right_norm angle)
  rw [←exp_series _ hl hs,←exp_series _ hr hs,←exp_add,←LSeries_add (su _ hl) (su _ hr),
    coeffs,LSeries_smul,AngularEuler.euler]

noncomputable def arithmetic (v : ℕ→ℂ) : ArithmeticFunction ℂ := ⟨lift v, map_zero _⟩

theorem convolution (angle : ℕ→ℝ) (s : ℂ) (hs : 1 < s.re) :
    LSeries ((arithmetic (left angle)*arithmetic (right angle) : ArithmeticFunction ℂ) : ℕ→ℂ) s =
      AngularEuler.euler angle s := by
  apply (ArithmeticFunction.LSeries_mul' ?_ ?_).trans (product angle s hs)
  · exact LSeriesSummable_of_bounded_of_one_lt_re (m:=1) (fun n _ => lift_norm _ (left_norm angle) n) hs
  · exact LSeriesSummable_of_bounded_of_one_lt_re (m:=1) (fun n _ => lift_norm _ (right_norm angle) n) hs

end OMA.AngularLog
end

section
/- The lattice-coordinate model of the Eisenstein integers. Balanced integer
division rounds both coordinates of x/y; its norm error is at most 3/4. -/
namespace OMA.AngularRing
abbrev R := QuadraticAlgebra ℤ (-1) 1
open QuadraticAlgebra

lemma norm_formula (x : R) : x.norm=x.re^2+x.re*x.im+x.im^2 := by
  rw [norm_def]; ring

lemma norm_nonneg (x : R) : 0≤x.norm := by rw [norm_formula]; nlinarith [sq_nonneg (x.re+x.im),sq_nonneg x.re,sq_nonneg x.im]

lemma norm_pos {x : R} (hx : x≠0) : 0<x.norm := by
  by_contra! hn
  rw [norm_formula] at hn
  have h := sq_nonneg (x.re+x.im)
  apply hx
  ext <;> simp <;> nlinarith [sq_nonneg x.re,sq_nonneg x.im]

def N (x : R) : ℕ := x.norm.toNat
lemma cast_N (x : R) : (N x:ℤ)=x.norm := Int.toNat_of_nonneg (norm_nonneg x)
lemma N_pos {x : R} (hx : x≠0) : 0<N x := by have := norm_pos hx; unfold N; omega
lemma N_mul (x y : R) : N (x*y)=N x*N y := by
  exact Int.ofNat_inj.mp (by simp [cast_N])

def quot (x y : R) : R :=
  let v := x*star y
  ⟨v.re.bdiv (N y), v.im.bdiv (N y)⟩

lemma balanced (t : ℤ) {d : ℕ} (hd : 0<d) : -(d:ℤ) ≤ 2*t.bmod d ∧ 2*t.bmod d ≤ d := by
  have lo := @Int.le_bmod t d hd
  have hi := @Int.bmod_lt t d hd
  omega

lemma norm_rem (x y : R) (hy : y≠0) : N (x-y*quot x y)<N y := by
  let d := N y
  let v := x*star y
  let a := v.re.bmod d
  let b := v.im.bmod d
  have hd : 0<d := N_pos hy
  obtain ⟨al,ah⟩ := balanced v.re hd
  obtain ⟨bl,bh⟩ := balanced v.im hd
  change -(d:ℤ) ≤ 2*a at al
  change 2*a ≤ (d:ℤ) at ah
  change -(d:ℤ) ≤ 2*b at bl
  change 2*b ≤ (d:ℤ) at bh
  have sm : a^2+a*b+b^2 < (d:ℤ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ah) (by linarith : 0≤(d:ℤ)+2*a),
      mul_nonneg (sub_nonneg.mpr bh) (by linarith : 0≤(d:ℤ)+2*b),
      sq_nonneg (a-b),sq_pos_of_pos (by exact_mod_cast hd : (0:ℤ)<d)]
  have he : (x-y*quot x y)*star y = (⟨a,b⟩ : R) := by
    rw [sub_mul,show y*quot x y*star y=(y*star y)*quot x y by ring,
      ←QuadraticAlgebra.algebraMap_norm_eq_mul_star,←cast_N]
    change v-algebraMap ℤ R (d:ℤ)*quot x y=_
    ext
    · simp [quot,v,d,a,Int.bmod_eq_self_sub_mul_bdiv]
    · simp [quot,v,d,b,Int.bmod_eq_self_sub_mul_bdiv]
  have hnr := congrArg QuadraticAlgebra.norm he
  rw [map_mul,QuadraticAlgebra.norm_star,norm_formula (⟨a,b⟩:R)] at hnr
  change (x-y*quot x y).norm*y.norm = a^2+a*b+b^2 at hnr
  have dn : (d:ℤ)=y.norm := cast_N y
  rw [dn,←hnr] at sm
  rw [pow_two] at sm
  have := lt_of_mul_lt_mul_right sm (norm_nonneg y)
  exact_mod_cast (show (N (x-y*quot x y):ℤ)<N y by simpa [cast_N] using this)

instance euclidean : EuclideanDomain R where
  quotient := quot
  remainder x y := x-y*quot x y
  quotient_zero x := by ext <;> simp [quot,N]
  quotient_mul_add_remainder_eq x y := by ring
  r x y := N x<N y
  r_wellFounded := (measure N).wf
  remainder_lt := fun x _ hy => norm_rem x _ hy
  mul_left_not_lt := fun x y hy => not_lt_of_ge (by
    change N x ≤ N (x*y); rw [N_mul]
    exact Nat.le_mul_of_pos_right _ (N_pos hy))

lemma unit_iff (x : R) : IsUnit x ↔ N x=1 := by
  constructor
  · rintro ⟨u,rfl⟩
    have h := N_mul (u:R) (↑(u⁻¹):R)
    simp [N] at h
    exact (mul_eq_one.mp h.symm).1
  · intro h
    apply isUnit_iff_dvd_one.mpr
    refine ⟨star x,?_⟩
    rw [←QuadraticAlgebra.algebraMap_norm_eq_mul_star,←cast_N,h]
    simp

@[simp] theorem N_one : N 1=1 := rfl
@[simp] theorem N_zero : N 0=0 := rfl
@[simp] theorem N_star (x : R) : N (star x)=N x := by simp [N]

lemma N_nat (n : ℕ) : N (n : R)=n^2 := by
  apply Int.ofNat_inj.mp
  rw [cast_N,norm_formula]
  simp

lemma mul_conj (x : R) : x*star x=(N x:R) := by
  rw [←QuadraticAlgebra.algebraMap_norm_eq_mul_star,←cast_N]
  simp

lemma norm_prime {x : R} (hp : (N x).Prime) : Prime x := by
  apply irreducible_iff_prime.mp
  refine ⟨fun hu => hp.ne_one ((unit_iff x).mp hu),fun a b h => ?_⟩
  rw [unit_iff,unit_iff]
  rw [h,N_mul] at hp
  exact ((Nat.prime_mul_iff.mp hp).imp And.right And.right).symm

lemma N_mod_three (x : R) : N x % 3 ≠ 2 := by
  intro h
  have hh : ((N x : ℕ) : ZMod 3)=2 := by rw [←ZMod.natCast_mod,h]; decide
  have he := congrArg (fun z : ℤ => (z : ZMod 3)) (cast_N x)
  rw [norm_formula] at he
  push_cast at he
  rw [hh] at he
  exact (show ∀ a b : ZMod 3, a^2+a*b+b^2 ≠ 2 by decide) _ _ he.symm

lemma inert_prime (p : ℕ) (hp : p.Prime) (hi : p%3=2) : Prime (p:R) := by
  apply irreducible_iff_prime.mp
  refine ⟨?_,fun a b he => ?_⟩
  · rw [unit_iff,N_nat]
    exact ne_of_gt (one_lt_pow₀ hp.one_lt (by decide))
  · by_contra! hn
    have h := congrArg N he
    rw [N_nat,N_mul] at h
    have ab := (hp.mul_eq_prime_sq_iff (mt (unit_iff a).mpr hn.1)
      (mt (unit_iff b).mpr hn.2)).mp h.symm
    exact N_mod_three a (ab.1 ▸ hi)

abbrev ram : R := ⟨1,1⟩
lemma ram_norm : N ram=3 := by decide
lemma ram_prime : Prime ram := norm_prime (ram_norm ▸ (by decide : Nat.Prime 3))

/-- There are precisely six units, represented by the sixth roots of unity. -/
def units : Finset R := {⟨1,0⟩,⟨0,1⟩,⟨-1,1⟩,⟨-1,0⟩,⟨0,-1⟩,⟨1,-1⟩}
lemma card_units : units.card=6 := by decide

lemma mem_units (x : R) : x∈units ↔ IsUnit x := by
  rw [unit_iff]
  constructor
  · intro h
    simp only [units,Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro h
    obtain ⟨a,b⟩ := x
    have hn := cast_N (⟨a,b⟩ : R)
    rw [h,norm_formula] at hn
    change (1:ℤ)=a^2+a*b+b^2 at hn
    have ha : a^2≤1 := by nlinarith [sq_nonneg (a+2*b)]
    have hb : b^2≤1 := by nlinarith [sq_nonneg (2*a+b)]
    have ha' : -1≤a ∧ a≤1 := by constructor <;> nlinarith
    have hb' : -1≤b ∧ b≤1 := by constructor <;> nlinarith
    obtain ⟨ha₁,ha₂⟩ := ha'
    obtain ⟨hb₁,hb₂⟩ := hb'
    interval_cases a <;> interval_cases b <;> first | decide | norm_num at hn

lemma dvd_star_iff (x y : R) : x ∣ star y ↔ star x ∣ y := by
  constructor
  · rintro ⟨k,h⟩; exact ⟨star k,by simpa [mul_comm] using congrArg star h⟩
  · rintro ⟨k,h⟩; exact ⟨star k,by simpa [mul_comm] using congrArg star h⟩

lemma lift_norm_dvd {q : R} {p : ℕ} (hp : N q=p) {x : R} (h : p∣N x) :
    q∣x*star x := by
  rw [mul_conj]
  apply dvd_trans (b:=(p:R))
  · rw [←hp,←mul_conj]; exact dvd_mul_right _ _
  · obtain ⟨k,hk⟩ := h; exact ⟨(k:R),by simp [hk]⟩

lemma split_divides {q : R} {p : ℕ} (hp : p.Prime) (hq : N q=p) {x : R} (h : p∣N x) :
    q ∣ x ∨ star q ∣ x := by
  exact ((norm_prime (hq ▸ hp)).dvd_mul.mp (lift_norm_dvd hq h)).imp id (dvd_star_iff q x).mp

lemma inert_divides {p : ℕ} (hp : p.Prime) (hi : p%3=2) {x : R} (h : p ∣ N x) :
    (p : R) ∣ x := by
  have d : (p : R) ∣ x*star x := by
    rw [mul_conj]; obtain ⟨k,hk⟩ := h; exact ⟨(k:R),by simp [hk]⟩
  rcases (inert_prime p hp hi).dvd_mul.mp d with h|h
  · exact h
  · simpa using (dvd_star_iff _ _).mp h

lemma ram_divides {x : R} (h : 3 ∣ N x) : ram ∣ x := by
  obtain h|h := split_divides (by decide) ram_norm h
  · exact h
  · exact dvd_trans (b:=star ram) ⟨(⟨1,-1⟩:R),by decide⟩ h

lemma split_distinct {q : R} {p : ℕ} (hp : p.Prime) (hs : p%3=1) (hq : N q=p) :
    ¬ q ∣ star q := by
  intro hh
  have nq : q.norm=(p:ℤ) := by rw [←cast_N,hq]
  obtain ⟨u,hu⟩ := dvd_sub hh (dvd_refl q)
  have diff := congrArg QuadraticAlgebra.norm hu
  rw [map_mul,nq,norm_formula] at diff
  simp only [QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
    QuadraticAlgebra.re_star,QuadraticAlgebra.im_star] at diff
  let : Fact p.Prime := ⟨hp⟩
  have mod_d := congrArg (fun z : ℤ => (z:ZMod p)) diff
  have mod_q := congrArg (fun z : ℤ => (z:ZMod p)) nq
  rw [norm_formula] at mod_q
  push_cast at mod_q mod_d
  simp only [ZMod.natCast_self,zero_mul] at mod_q mod_d
  have h3 : (3:ZMod p) ≠ 0 := by
    change (↑(3:ℕ):ZMod p)≠0
    rw [Ne,ZMod.natCast_eq_zero_iff]
    intro hd
    have := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd
    exact this.elim hp.ne_one (fun h => by omega)
  have hbi : (3:ZMod p)*(q.im:ZMod p)^2=0 := by linear_combination mod_d
  have hb : (q.im:ZMod p)=0 := by simpa using (mul_eq_zero.mp hbi).resolve_left h3
  have ha : (q.re:ZMod p)=0 := by simpa [hb] using mod_q
  obtain ⟨a,ha'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha
  obtain ⟨b,hb'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  have div : (p:R) ∣ q := ⟨⟨a,b⟩,by ext <;> simp [ha',hb']⟩
  obtain ⟨v,hv⟩ := div
  have d := congrArg N hv
  rw [hq,N_mul,N_nat,pow_two,mul_assoc] at d
  have u : 1=p*N v := Nat.eq_of_mul_eq_mul_left hp.pos (by simpa using d)
  exact hp.not_dvd_one ⟨_,u⟩

end OMA.AngularRing
end

section
/- Identification of the split factors with the problem's two finite searches.
Reducing the Eisenstein norm modulo a split prime makes the rational prime
reducible; its two nonunit factors must both have norm p. The six units then
give uniqueness of the representative in the ordered sector. -/
namespace OMA.AngularSplit
open AngularRing QuadraticAlgebra OeisA218585

lemma split_norm {p : ℕ} (hp : p.Prime) (hs : p%3=1) : ∃ q : R, N q=p := by
  let : Fact p.Prime := ⟨hp⟩
  have d : 3∣Fintype.card (ZMod p)ˣ := by
    simp [ZMod.card_units_eq_totient,Nat.totient_prime hp]; omega
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card (G:=(ZMod p)ˣ) 3 d
  let a := (v : ZMod p).val
  have av : (a : ZMod p)=v := ZMod.natCast_zmod_val _
  have cube : (v:ZMod p)^3=1 := by
    exact congrArg Units.val (show v^3=1 by rw [←hv,pow_orderOf_eq_one])
  have nv : (v:ZMod p)≠1 := by
    intro he
    have he' : v=1 := Units.ext he
    simp [he'] at hv
  have F : (a:ZMod p)^2+a+1=0 := by
    rw [av]
    apply (mul_eq_zero.mp (show ((v:ZMod p)-1)*(v^2+v+1)=0 by linear_combination cube)).resolve_left
      (sub_ne_zero.mpr nv)
  let u : R := ⟨(a:ℤ),1⟩
  have div : (p:ℤ)∣u.norm := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa [norm_formula,u] using F
  have np : ¬Prime (p:R) := by
    intro prime
    have h : (p:R)∣u*star u := by
      rw [←QuadraticAlgebra.algebraMap_norm_eq_mul_star]
      obtain ⟨m,h⟩ := div
      exact ⟨(m:R),by simp [h]⟩
    have no (x : R) (hx : x.im=1 ∨ x.im= -1) : ¬(p:R)∣x := by
      rintro ⟨y,hy⟩
      have im := congrArg QuadraticAlgebra.im hy
      simp at im
      have hd : (p:ℤ)∣x.im := ⟨_,im⟩
      have no1 : ¬(p:ℤ)∣1 := by exact_mod_cast hp.not_dvd_one
      rcases hx with he|he <;> rw [he] at hd
      · exact no1 hd
      · exact no1 (Int.dvd_neg.mp hd)
    exact (prime.dvd_mul.mp h).elim (no _ (Or.inl rfl)) (no _ (Or.inr rfl))
  have notu : ¬IsUnit (p:R) := by
    rw [unit_iff,N_nat]; exact ne_of_gt (one_lt_pow₀ hp.one_lt (by decide))
  by_contra! nex
  apply np
  apply irreducible_iff_prime.mp
  refine ⟨notu,fun x y he => ?_⟩
  by_contra! nu
  have h := congrArg N he
  rw [N_nat,N_mul] at h
  exact nex _ ((hp.mul_eq_prime_sq_iff (mt (unit_iff _).mpr nu.1)
    (mt (unit_iff _).mpr nu.2)).mp h.symm).1

private lemma chamber (a b : ℤ) :
    ∃ u v : ℤ, 0 ≤ v ∧ v ≤ u ∧ u^2+u*v+v^2=a^2+a*b+b^2 := by
  have choice : (0≤b ∧ b≤a) ∨ (0≤a ∧ a≤b) ∨
      (0≤ -b ∧ -b≤ -a) ∨ (0≤ -a ∧ -a≤ -b) ∨
      (0≤ -a-b ∧ -a-b≤a) ∨ (0≤a ∧ a≤ -a-b) ∨
      (0≤ -a-b ∧ -a-b≤b) ∨ (0≤b ∧ b≤ -a-b) ∨
      (0≤a+b ∧ a+b≤ -a) ∨ (0≤ -a ∧ -a≤a+b) ∨
      (0≤a+b ∧ a+b≤ -b) ∨ (0≤ -b ∧ -b≤a+b) := by omega
  rcases choice with h|h|h|h|h|h|h|h|h|h|h|h
  all_goals exact ⟨_,_,h.1,h.2,by ring⟩

lemma sector {p : ℕ} (hp : p.Prime) (hs : p%3=1) :
    ∃ a b : ℕ, 0<b ∧ b<a ∧ a<p ∧ a^2+a*b+b^2=p := by
  obtain ⟨q,hq⟩ := split_norm hp hs
  obtain ⟨u,v,hv,hu,h⟩ := chamber q.re q.im
  rw [←norm_formula,←cast_N,hq] at h
  have hu0 := hv.trans hu
  lift v to ℕ using hv
  lift u to ℕ using hu0
  have eq : u^2+u*v+v^2=p := by exact_mod_cast h
  have hl : v≤u := by exact_mod_cast hu
  have pos : 0<v := by
    by_contra! hz
    have h₀ : v=0 := by omega
    exact hp.prime.not_isSquare ⟨u,by simpa [h₀,pow_two] using eq.symm⟩
  have lt : v<u := by
    by_contra! hh
    have e : v=u := le_antisymm hl hh
    have h3 : 3∣p := ⟨u^2,by rw [←eq,e]; ring⟩
    omega
  refine ⟨u,v,pos,lt,?_,eq⟩
  nlinarith [Nat.le_self_pow (by decide : 2≠0) u,pow_pos pos 2]

lemma unique_sector {p : ℕ} (hp : p.Prime) (x y : R) (hx : N x=p) (hy : N y=p)
    (xp : 0<x.im) (xo : x.im<x.re) (yp : 0<y.im) (yo : y.im<y.re) : x=y := by
  obtain ⟨a,b⟩ := x
  obtain ⟨c,d⟩ := y
  change 0<b at xp; change b<a at xo; change 0<d at yp; change d<c at yo
  have cases (z : R) (hz : N z=p) (div : z ∣ (⟨c,d⟩:R)) :
      ∃ v∈units, (⟨c,d⟩:R)=z*v := by
    obtain ⟨v,e⟩ := div
    have h := congrArg N e
    rw [hy,N_mul,hz] at h
    exact ⟨v,(mem_units _).mpr ((unit_iff _).mpr
      (Nat.eq_of_mul_eq_mul_left hp.pos (by simpa using h.symm))),e⟩
  rcases split_divides hp hx (x:=(⟨c,d⟩:R)) (by rw [hy]) with div|div
  · obtain ⟨v,hv,e⟩ := cases _ hx div
    simp only [units,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals have A := congrArg QuadraticAlgebra.re e; have B := congrArg QuadraticAlgebra.im e
    all_goals simp at A B; ext <;> simp <;> omega
  · obtain ⟨v,hv,e⟩ := cases _ ((N_star _).trans hx) div
    simp only [units,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals have A := congrArg QuadraticAlgebra.re e; have B := congrArg QuadraticAlgebra.im e
    all_goals simp at A B; ext <;> simp <;> omega

def pair (a b : ℕ) : R := ⟨(a:ℤ),(b:ℤ)⟩

@[simp] lemma N_pair (a b : ℕ) : N (pair a b)=a^2+a*b+b^2 := by
  apply Int.ofNat_inj.mp
  rw [cast_N,norm_formula]; simp [pair]

lemma nat_unique {p a b u v : ℕ} (hp : p.Prime) (hb : 0<b) (ha : b<a)
    (hv : 0<v) (hu : v<u) (e : a^2+a*b+b^2=p) (d : u^2+u*v+v^2=p) :
    a=u ∧ b=v := by
  have h := unique_sector hp (pair a b) (pair u v) (by simpa using e) (by simpa using d)
    (by simpa [pair]) (by simpa [pair]) (by simpa [pair]) (by simpa [pair])
  exact ⟨Int.ofNat_inj.mp (congrArg QuadraticAlgebra.re h),
    Int.ofNat_inj.mp (congrArg QuadraticAlgebra.im h)⟩

private lemma find_unique (n c : ℕ) (hc : c<n) (f : ℕ→Bool) (fc : f c)
    (only : ∀ t, f t → t=c) : ((List.range n).find? f).getD 0=c := by
  have some := List.find?_isSome.mpr ⟨c,List.mem_range.mpr hc,fc⟩
  obtain ⟨t,et⟩ := Option.isSome_iff_exists.mp some
  rw [et]; exact only t (List.find?_some et)

theorem specified {p : ℕ} (hp : p.Prime) (hs : p%3=1) :
    N (pair (xp p) (yp p))=p := by
  obtain ⟨u,v,hv,hu,up,e⟩ := sector hp hs
  have X : xp p=u := by
    apply find_unique p u up
    · simp; exact ⟨v,hu,hv,e⟩
    · intro t ht; simp at ht
      obtain ⟨b,bt,bp,hb⟩ := ht
      exact (nat_unique hp bp bt hv hu hb e).1
  have Y : yp p=v := by
    apply find_unique p v (hu.trans up)
    · simp; exact ⟨hv,u,⟨hu,up⟩,e⟩
    · intro t ht; simp at ht
      obtain ⟨tp,a,⟨ta,_⟩,h⟩ := ht
      exact (nat_unique hp tp ta hv hu h e).2
  simpa [X,Y] using e

end OMA.AngularSplit
end

section
/- Finite shells of the Eisenstein lattice and the local counting rules.
All sums carry a multiplicative weight; conjugate split primes overlap precisely
on the shell of multiples of their product. -/
namespace OMA.AngularShell
open AngularRing

def coords : ℤ × ℤ ≃ R where
  toFun x := ⟨x.1,x.2⟩
  invFun z := (z.re,z.im)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def shell (n : ℕ) : Finset R :=
  (((Finset.Icc (-(n:ℤ)) n) ×ˢ (Finset.Icc (-(n:ℤ)) n)).map coords.toEmbedding).filter
    (fun x => N x=n)

@[simp] lemma mem_shell (x : R) (n : ℕ) : x∈shell n ↔ N x=n := by
  refine ⟨fun h => (Finset.mem_filter.mp h).2,fun h => ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨(x.re,x.im),?_,rfl⟩,h⟩
  have e := cast_N x
  rw [h,norm_formula] at e
  have bound (a b : ℤ) (he : (n:ℤ)=a^2+a*b+b^2) : -(n:ℤ)≤a ∧ a≤n := by
    have w := sq_nonneg (2*b+a)
    by_cases hn : n=0
    · subst n
      constructor <;> nlinarith [sq_nonneg a]
    have pos : (1:ℤ) ≤ n := by omega
    constructor <;> by_contra! h
    · nlinarith [mul_nonneg (by omega : 0≤ -a-2) (by omega : 0≤ -a)]
    · nlinarith [mul_nonneg (by omega : 0≤a-2) (by omega : 0≤a)]
  have ha := bound x.re x.im e
  have hb := bound x.im x.re (by linarith)
  simpa using And.intro ha hb

def mult (u : R) (h : u≠0) : R ↪ R := ⟨(u*·),mul_right_injective₀ h⟩

lemma mem_mult (u : R) (h : u≠0) (n : ℕ) (x : R) :
    x ∈ (shell n).map (mult u h) ↔ u∣x ∧ N x=N u*n := by
  constructor
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
    exact ⟨⟨y,rfl⟩,by simpa [mult,N_mul] using congrArg (N u*·) ((mem_shell y n).mp hy)⟩
  · rintro ⟨⟨y,rfl⟩,hN⟩
    rw [N_mul] at hN
    exact Finset.mem_map.mpr ⟨y,(mem_shell _ _).mpr (Nat.eq_of_mul_eq_mul_left (N_pos h) hN),rfl⟩

noncomputable def S (w : R →*₀ ℂ) (n : ℕ) : ℂ := ∑ x ∈ shell n,w x

lemma map_sum (w : R →*₀ ℂ) (u : R) (h : u≠0) (n : ℕ) :
    ∑ x ∈ (shell n).map (mult u h), w x = w u*S w n := by
  simp [S,Finset.sum_map,mult,Finset.mul_sum]

lemma split_union {p : ℕ} (hp : p.Prime) {q : R} (hq : N q=p) (n : ℕ) :
    shell (p*n) = (shell n).map (mult q (norm_prime (hq ▸ hp)).ne_zero) ∪
      (shell n).map (mult (star q) (norm_prime ((N_star q).trans hq ▸ hp)).ne_zero) := by
  ext x
  simp only [Finset.mem_union,mem_mult,mem_shell,N_star,hq]
  constructor
  · intro hx
    exact ((split_divides hp hq (hx ▸ dvd_mul_right p n)).imp (⟨·,hx⟩) (⟨·,hx⟩))
  · exact fun h => h.elim And.right And.right

lemma split_empty {p : ℕ} (hp : p.Prime) (hs : p%3=1) {q : R} (hq : N q=p)
    (n : ℕ) (hn : ¬p∣n) :
    Disjoint ((shell n).map (mult q (norm_prime (hq ▸ hp)).ne_zero))
      ((shell n).map (mult (star q) (norm_prime ((N_star q).trans hq ▸ hp)).ne_zero)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
  have hq' := (mem_mult _ _ _ _).mp hx
  have hd := ((norm_prime (hq ▸ hp)).dvd_mul.mp hq'.1).resolve_left (split_distinct hp hs hq)
  obtain ⟨z,rfl⟩ := hd
  have hn' := (mem_shell _ _).mp hv
  exact hn ⟨_,by rw [←hn',N_mul,hq]⟩

lemma split_inter {p : ℕ} (hp : p.Prime) (hs : p%3=1) {q : R} (hq : N q=p)
    (n : ℕ) :
    (shell (p*n)).map (mult q (norm_prime (hq ▸ hp)).ne_zero) ∩
      (shell (p*n)).map (mult (star q) (norm_prime ((N_star q).trans hq ▸ hp)).ne_zero) =
    (shell n).map (mult (q*star q) (mul_ne_zero (norm_prime (hq ▸ hp)).ne_zero
      (norm_prime ((N_star q).trans hq ▸ hp)).ne_zero)) := by
  ext x
  simp only [Finset.mem_inter,mem_mult,N_mul,N_star,hq,mul_assoc]
  constructor
  · rintro ⟨⟨hd,hN⟩,⟨⟨y,hy⟩,_⟩⟩
    rw [hy] at hd
    obtain ⟨v,rfl⟩ := ((norm_prime (hq ▸ hp)).dvd_mul.mp hd).resolve_left (split_distinct hp hs hq)
    exact ⟨⟨v,hy.trans (by ring)⟩,hN⟩
  · rintro ⟨h,hN⟩
    exact ⟨⟨dvd_trans (dvd_mul_right _ _) h,hN⟩,⟨dvd_trans (dvd_mul_left _ _) h,hN⟩⟩

lemma split_first (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hs : p%3=1) {q : R}
    (hq : N q=p) (n : ℕ) (hn : ¬p∣n) :
    S w (p*n)=(w q+w (star q))*S w n := by
  unfold S
  rw [split_union hp hq,Finset.sum_union (split_empty hp hs hq n hn),map_sum,map_sum]
  exact (add_mul ..).symm

lemma split_next (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hs : p%3=1) {q : R}
    (hq : N q=p) (n : ℕ) :
    S w (p*(p*n))+w q*w (star q)*S w n=(w q+w (star q))*S w (p*n) := by
  let l := (shell (p*n)).map (mult q (norm_prime (hq ▸ hp)).ne_zero)
  let r := (shell (p*n)).map (mult (star q) (norm_prime ((N_star q).trans hq ▸ hp)).ne_zero)
  have h := Finset.sum_union_inter (s₁:=l) (s₂:=r) (f:=fun x => w x)
  unfold l r at h
  rw [←split_union,split_inter hp hs hq,map_sum,map_sum,map_sum,map_mul] at h
  · exact h.trans (add_mul ..).symm
  all_goals assumption

lemma all_mult (u : R) (hu : u≠0) (n : ℕ) (D : ∀ x : R, N x=N u*n → u∣x) :
    shell (N u*n) = (shell n).map (mult u hu) := by
  ext x
  simp only [mem_shell,mem_mult]
  exact ⟨fun e => ⟨D _ e,e⟩,And.right⟩

lemma inert_first (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hi : p%3=2) (n : ℕ)
    (hn : ¬p∣n) : S w (p*n)=0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have h := (mem_shell _ _).mp hx
  obtain ⟨y,hy⟩ := inert_divides hp hi (h ▸ dvd_mul_right p n)
  rw [hy,N_mul,N_nat,pow_two,mul_assoc] at h
  exact False.elim (hn ⟨_,(Nat.eq_of_mul_eq_mul_left hp.pos h).symm⟩)

lemma inert_next (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hi : p%3=2) (n : ℕ) :
    S w (p*(p*n))=w (p:R)*S w n := by
  have h := all_mult (p:R) (inert_prime p hp hi).ne_zero n fun x h =>
    inert_divides hp hi (by rw [h,N_nat,pow_two,mul_assoc]; exact dvd_mul_right _ _)
  rw [N_nat,pow_two,mul_assoc] at h
  unfold S; rw [h,map_sum]; rfl

lemma ram_step (w : R →*₀ ℂ) (n : ℕ) : S w (3*n)=w ram*S w n := by
  have h := all_mult ram ram_prime.ne_zero n fun x h =>
    ram_divides (by rw [h,ram_norm]; exact dvd_mul_right _ _)
  rw [ram_norm] at h
  unfold S; rw [h,map_sum]; rfl

def geom (x y : ℂ) (k : ℕ) : ℂ := ∑ j ∈ Finset.range (k+1), x^(k-j)*y^j

lemma geom_zero (x y : ℂ) : geom x y 0=1 := by simp [geom]

lemma geom_succ (x y : ℂ) (k : ℕ) : geom x y (k+1)=x*geom x y k+y^(k+1) := by
  unfold geom
  rw [Finset.sum_range_succ,Finset.mul_sum]
  simp only [Nat.sub_self,pow_zero,one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [show k+1-j=k-j+1 by have := Finset.mem_range.mp hj; omega,pow_succ]
  ring

lemma geom_rec (x y : ℂ) (k : ℕ) :
    geom x y (k+2)+x*y*geom x y k=(x+y)*geom x y (k+1) := by
  rw [geom_succ x y (k+1),geom_succ x y k,pow_succ y (k+1)]
  ring

lemma arith_mult (v : ℕ→ℂ) : (AngularLog.arithmetic v).IsMultiplicative :=
  ⟨map_one (AngularLog.lift v),fun {_ _} _ => map_mul (AngularLog.lift v) ..⟩

lemma arith_power (a b : ℕ→ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (AngularLog.arithmetic a * AngularLog.arithmetic b) (p^k) = geom (a p) (b p) k := by
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal' (fun u v =>
    AngularLog.arithmetic a u*AngularLog.arithmetic b v),Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj => ?_
  have le : j ≤ k := by simpa using Finset.mem_range.mp hj
  have div : p^k/p^j=p^(k-j) := by
    conv_lhs => rw [←Nat.sub_add_cancel le,pow_add]
    exact Nat.mul_div_cancel _ (pow_pos hp.pos _)
  simp [div,AngularLog.arithmetic,AngularLog.lift_prime _ hp]

lemma split_pow (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hs : p%3=1) {q : R}
    (hq : N q=p) (n : ℕ) (hn : ¬p∣n) (k : ℕ) :
    S w (p^k*n)=geom (w q) (w (star q)) k*S w n := by
  induction k using Nat.twoStepInduction with
  | zero => simp [geom_zero]
  | one => simpa [geom_succ,geom_zero] using split_first w hp hs hq n hn
  | more k ha hb =>
    have h := split_next w hp hs hq (p^k*n)
    rw [show p*(p^k*n)=p^(k+1)*n by rw [pow_succ',mul_assoc],
      show p*(p^(k+1)*n)=p^(k+2)*n by rw [pow_succ' p (k+1),mul_assoc],ha,hb] at h
    linear_combination h - S w n*geom_rec (w q) (w (star q)) k

lemma inert_pow (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hi : p%3=2) (hw : w (p:R)=1)
    (n : ℕ) (hn : ¬p∣n) (k : ℕ) : S w (p^k*n)=geom 1 (-1) k*S w n := by
  induction k using Nat.twoStepInduction with
  | zero => simp [geom_zero]
  | one => simpa [geom_succ,geom_zero] using inert_first w hp hi n hn
  | more k ha hb =>
    have h := inert_next w hp hi (p^k*n)
    rw [show p*(p^k*n)=p^(k+1)*n by rw [pow_succ',mul_assoc],
      show p*(p^(k+1)*n)=p^(k+2)*n by rw [pow_succ' p (k+1),mul_assoc],ha,hw,one_mul] at h
    linear_combination h - S w n*geom_rec 1 (-1) k

lemma shell_coeff (w : R →*₀ ℂ) (a b : ℕ→ℂ) (hunit : ∀ u∈units, w u=1)
    (h3 : w ram=0 ∧ a 3=0 ∧ b 3=0)
    (hs : ∀ p : ℕ, p.Prime → p%3=1 → ∃ q : R, N q=p ∧ a p=w q ∧ b p=w (star q))
    (hi : ∀ p : ℕ, p.Prime → p%3=2 → w (p:R)=1 ∧ a p=1 ∧ b p= -1) (n : ℕ) :
    S w n=6*((AngularLog.arithmetic a*AngularLog.arithmetic b) n) := by
  let c := AngularLog.arithmetic a*AngularLog.arithmetic b
  have cm := (arith_mult a).mul (arith_mult b)
  induction n using Nat.recOnPrimePow with
  | zero =>
    rw [ArithmeticFunction.map_zero,mul_zero]
    apply Finset.sum_eq_zero
    intro x hx
    have e := (mem_shell _ _).mp hx
    by_cases h : x=0
    · simp [h]
    · exact False.elim ((N_pos h).ne' e)
  | one =>
    have un : shell 1=units := by ext x; rw [mem_shell,mem_units,unit_iff]
    simp [S,un,Finset.sum_congr rfl hunit,card_units,cm.map_one]
  | prime_pow_mul n p k hp hn hk ih =>
    have cop : (p^k).Coprime n := (hp.coprime_iff_not_dvd.mpr hn).pow_left _
    rw [cm.map_mul_of_coprime cop,arith_power a b hp]
    suffices H : S w (p^k*n)=geom (a p) (b p) k*S w n by rw [H,ih]; ring
    rcases show p=3 ∨ p%3=1 ∨ p%3=2 by
      by_cases h : p%3=0
      · exact Or.inl (((Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h)).resolve_left (by decide)).symm
      · omega with h|h|h
    · subst p
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simp [pow_succ',mul_assoc,ram_step,h3.1,h3.2.1,h3.2.2,geom_succ]
    · obtain ⟨q,hq,ha,hb⟩ := hs p hp h
      rw [ha,hb]; exact split_pow w hp h hq n hn k
    · obtain ⟨hw,ha,hb⟩ := hi p hp h
      rw [ha,hb]; exact inert_pow w hp h hw n hn k

end OMA.AngularShell
end

section
/- The angular character on the lattice, its values at units and the ramified
prime, and the character with its ramified factor deleted. -/
namespace OMA.AngularWeight
open AngularRing AngularShell Complex
open scoped ComplexConjugate

noncomputable def place : R →+* ℂ :=
  (QuadraticAlgebra.lift ⟨AngularSeven.eta,by
    simp only [neg_one_zsmul,one_zsmul]; linear_combination AngularSeven.eta_sq⟩).toRingHom

lemma place_def (x : R) : place x=(x.re:ℂ)+x.im*AngularSeven.eta := by
  change x.re • (1:ℂ) + x.im • AngularSeven.eta=_
  simp

lemma place_star (x : R) : place (star x)=conj (place x) := by
  have e : conj AngularSeven.eta=1-AngularSeven.eta := by
    unfold AngularSeven.eta
    simp only [map_div₀,map_add,map_one,map_mul,Complex.conj_I,Complex.conj_ofReal,
      show conj (2:ℂ)=2 from map_ofNat _ _]
    ring
  simp [place_def,e]; ring

lemma norm_place (x : R) : ‖place x‖^2=(N x:ℝ) := by
  have h := congrArg place (mul_conj x)
  rw [map_mul,place_star,Complex.mul_conj,map_natCast] at h
  rw [←Complex.normSq_eq_norm_sq]
  exact_mod_cast (show (Complex.normSq (place x):ℂ)=(N x:ℂ) from h)

noncomputable def W (m : ℕ) (hm : m≠0) : R →*₀ ℂ where
  toFun x := (place x / (‖place x‖:ℂ))^m
  map_zero' := by simp [hm]
  map_one' := by simp
  map_mul' x y := by simp [mul_div_mul_comm,mul_pow]

lemma W_posNat (m : ℕ) (hm : m≠0) (n : ℕ) (hn : n≠0) : W m hm (n:R)=1 := by
  simp [W,hn]

lemma W_units (k : ℕ) (hk : k≠0) {u : R} (hu : u∈units) :
    W (6*k) (by positivity) u=1 := by
  have hn := (unit_iff _).mp ((mem_units _).mp hu)
  have norm : ‖place u‖=1 := by nlinarith [norm_place u,norm_nonneg (place u),show (N u:ℝ)=1 by simp [hn]]
  have power : u^6=1 := by
    simp only [units,Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simp [W,norm,pow_mul,←map_pow,power]

lemma W_ram (k : ℕ) (hk : k≠0) : W (6*k) (by positivity) ram=(-1:ℂ)^k := by
  have r6 : ram^6=(-27:R) := by decide
  have n3 : ((‖place ram‖:ℝ):ℂ)^2=3 := by exact_mod_cast (by simpa [ram_norm] using norm_place ram : ‖place ram‖^2=3)
  have n27 : ((‖place ram‖:ℝ):ℂ)^6=27 := by
    rw [show (6:ℕ)=2*3 by decide,pow_mul,n3]; norm_num
  change (place ram / (‖place ram‖:ℂ))^(6*k)=_
  rw [pow_mul,div_pow,←map_pow,r6,n27]
  rw [map_neg,show place (27:R)=27 from map_ofNat _ _]; norm_num

noncomputable def unram (w : R →*₀ ℂ) : R →*₀ ℂ where
  toFun x := if 3∣N x then 0 else w x
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by
    simp only [N_mul,Nat.prime_three.dvd_mul,map_mul]
    split_ifs <;> simp_all

lemma W_arg (m : ℕ) (hm : m≠0) (x : R) (hx : place x ≠ 0) :
    W m hm x=exp (((m:ℂ)*(place x).arg)*I) := by
  have hn : (‖place x‖:ℂ)≠0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have h : place x/(‖place x‖:ℂ)=exp ((place x).arg*I) :=
    (div_eq_iff hn).mpr (by rw [mul_comm,norm_mul_exp_arg_mul_I])
  simp only [W,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,h,←Complex.exp_nat_mul,mul_assoc]

lemma W_star (m : ℕ) (hm : m≠0) (x : R) : W m hm (star x)=conj (W m hm x) := by
  simp [W,place_star]

end OMA.AngularWeight
end

section
/- Regroup the absolutely convergent lattice series by norm, remove the
ramified prime, and identify the resulting Euler factors. -/
namespace OMA.AngularArithmetic
open Complex AngularRing AngularShell AngularWeight OeisA218585
open scoped ComplexConjugate

noncomputable def E (w : R →*₀ ℂ) (s : ℂ) (x : R) := w x * (N x:ℂ)^(-s)

lemma E_mul (w : R →*₀ ℂ) (s : ℂ) (x y : R) : E w s (x*y)=E w s x*E w s y := by
  simp [E,N_mul,Complex.natCast_mul_natCast_cpow]; ring

lemma place_coords (u : ℤ×ℤ) : place (coords u)=AngularTail.z u := by rw [place_def]; rfl

lemma E_eq_g (m : ℕ) (hm : m≠0) (s : ℂ) (x : R) :
    E (W m hm) s x=AngularTail.g m s (place x) := by
  by_cases h : place x=0
  · simp [E,W,AngularTail.g,h,hm]
  simp only [E,W,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,AngularTail.g,if_neg h]
  congr 1
  have n : (N x:ℂ)=(‖place x‖:ℂ)^2 := by exact_mod_cast (norm_place x).symm
  rw [n,show -2*s=(2:ℕ)*(-s) by push_cast; ring]
  symm
  apply Complex.cpow_nat_mul'
  all_goals simp [Complex.arg_ofReal_of_nonneg (norm_nonneg _),Real.pi_pos.le,Real.pi_pos]

lemma E_summable (m : ℕ) (hm : m≠0) {s : ℂ} (hs : 1<s.re) :
    Summable (E (W m hm) s) := by
  apply coords.summable_iff.mp
  simpa only [Function.comp_def,E_eq_g,place_coords] using (AngularTail.original m s hs).of_norm

lemma E_unram (w : R →*₀ ℂ) (s : ℂ) (x : R) :
    E (unram w) s x=(if 3∣N x then 0 else E w s x) := by
  by_cases h : 3∣N x <;> simp [unram,h,E]

lemma unram_sum (w : R →*₀ ℂ) (s : ℂ) (su : Summable (E w s)) :
    (∑' x, E (unram w) s x)=(1-E w s ram)*(∑' x, E w s x) := by
  let bad : Set R := {x | 3∣N x}
  have rs : Summable (bad.indicator (E w s)) := su.indicator _
  have difference : ∀ x, E (unram w) s x = E w s x - bad.indicator (E w s) x := by
    intro x; rw [E_unram]; by_cases h : 3∣N x <;> simp [bad,h,Set.indicator]
  have support : Function.support (bad.indicator (E w s)) ⊆ Set.range (ram*·) := by
    intro x hx
    have h : x∈bad := Set.support_indicator_subset hx
    obtain ⟨v,e⟩ := ram_divides h
    exact ⟨v,e.symm⟩
  have eq := (mul_right_injective₀ ram_prime.ne_zero).tsum_eq support
  have scale (x : R) : bad.indicator (E w s) (ram*x)=E w s ram*E w s x := by
    rw [Set.indicator_of_mem (by simp [bad,N_mul,ram_norm] : ram*x∈bad),E_mul]
  rw [tsum_congr difference,su.tsum_sub rs,←eq,tsum_congr scale,tsum_mul_left]
  ring

lemma by_shell (w : R →*₀ ℂ) (s : ℂ) (su : Summable (E w s)) :
    ∑' x, E w s x = ∑' n : ℕ, S w n*(n:ℂ)^(-s) := by
  rw [←(su.hasSum.tsum_fiberwise N).tsum_eq]
  refine tsum_congr fun n => ?_
  have seteq : N ⁻¹' ({n}:Set ℕ)=(shell n : Set R) := by ext x; simp
  rw [seteq,Finset.tsum_subtype']
  unfold S
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x hx => by rw [E,(mem_shell _ _).mp hx]

noncomputable def fac (p : ℕ) := AngularSplit.pair (xp p) (yp p)
noncomputable def angle (k p : ℕ) : ℝ := (k:ℝ)*(6*(place (fac p)).arg)

lemma specified_coeff (k : ℕ) (hk : k≠0) (n : ℕ) :
    S (unram (W (6*k) (by positivity))) n =
      6*((AngularLog.arithmetic (AngularLog.left (angle k)) *
        AngularLog.arithmetic (AngularLog.right (angle k))) n) := by
  apply shell_coeff
  · intro u hu
    have hn := (unit_iff _).mp ((mem_units _).mp hu)
    simp [unram,hn,W_units k hk hu]
  · norm_num [unram,ram_norm,AngularLog.left,AngularLog.right]
  · intro p hp hs
    let x := fac p
    have hx : N x=p := AngularSplit.specified hp hs
    have hn : ¬3∣p := by omega
    have non : place x≠0 := by
      intro e
      have h := norm_place x
      rw [hx,e,norm_zero] at h
      have := hp.pos; norm_cast at h; omega
    have v := W_arg (6*k) (by positivity) x non
    have hφ : (((6*k:ℕ):ℂ)*(place x).arg)*I=(angle k p:ℂ)*I := by
      simp [angle,x]; ring
    rw [hφ] at v
    refine ⟨x,hx,?_,?_⟩
    · simpa [unram,hx,hn,AngularLog.left,hs] using v.symm
    · simp [unram,N_star,hx,hn,AngularLog.right,hs,W_star,v,←Complex.exp_conj]
  · intro p hp hi
    have hn : ¬3∣p^2 := by
      intro d
      have := Nat.prime_three.dvd_of_dvd_pow d
      omega
    simp [unram,N_nat,hn,W_posNat _ _ _ hp.ne_zero,AngularLog.left,AngularLog.right,hi]

lemma place_fac (p : ℕ) : place (fac p)=
    (⟨(xp p:ℝ)+(yp p:ℝ)/2,Real.sqrt 3*(yp p:ℝ)/2⟩:ℂ) := by
  apply Complex.ext <;> simp [place_def,fac,AngularSplit.pair,AngularSeven.eta,
    Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.div_ofNat_re,Complex.div_ofNat_im] <;> ring

theorem factorization (k : ℕ) (hk : k≠0) (s : ℂ) (hs : 1<s.re) :
    (1-(-1:ℂ)^k*(3:ℂ)^(-s))*((∑' u : ℤ×ℤ, AngularTail.g (6*k) s (AngularTail.z u))/6) =
      AngularEuler.euler (angle k) s := by
  let w := W (6*k) (Nat.mul_ne_zero (by decide) hk)
  let c := AngularLog.arithmetic (AngularLog.left (angle k))*AngularLog.arithmetic (AngularLog.right (angle k))
  have su : Summable (E w s) := E_summable _ _ hs
  have ru : Summable (E (unram w) s) := by
    apply (su.indicator {x | ¬3∣N x}).congr
    intro x; rw [E_unram]; by_cases h : 3∣N x <;> simp [h,Set.indicator]
  have sum := unram_sum w s su
  have lattice : ∑' x, E w s x = ∑' u : ℤ×ℤ, AngularTail.g (6*k) s (AngularTail.z u) := by
    rw [←coords.tsum_eq (E w s)]
    exact tsum_congr fun x => by rw [show E w s (coords x)=_ from E_eq_g _ _ _ _,place_coords]
  have ramv : E w s ram=(-1:ℂ)^k*(3:ℂ)^(-s) := by
    simp [E,w,W_ram k hk,ram_norm]
  rw [ramv,lattice,by_shell _ _ ru] at sum
  have coeff : ∀ n, S (unram w) n=6*c n := specified_coeff k hk
  simp_rw [coeff,mul_assoc] at sum
  rw [tsum_mul_left] at sum
  have Eul : (∑' n : ℕ, c n*(n:ℂ)^(-s))=AngularEuler.euler (angle k) s := by
    rw [←AngularLog.convolution _ _ hs,LSeries_def₀ (show c 0=0 by simp)]
    exact tsum_congr fun n => by simp only [cpow_neg,div_eq_mul_inv]
  rw [Eul] at sum
  linear_combination -sum/6

end OMA.AngularArithmetic
end

theorem OMA.AngularDeep.arithmetic : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1.H2 := by
  intro k hk s hs
  have h := OMA.AngularArithmetic.factorization k hk s hs
  have he : OMA.AngularArithmetic.angle k =
      fun p => (k:ℝ)*(6*(⟨(OeisA218585.xp p:ℝ)+(OeisA218585.yp p:ℝ)/2,
        Real.sqrt 3*(OeisA218585.yp p:ℝ)/2⟩:ℂ).arg) := by
    funext p; rw [OMA.AngularArithmetic.angle,OMA.AngularArithmetic.place_fac]
  rw [he] at h
  exact h

theorem OMA.solution : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1.H1 :=
  OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1.main OMA.AngularDeep.analytic OMA.AngularDeep.arithmetic
