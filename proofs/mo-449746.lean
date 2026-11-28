import OMAStatements.S_mo_449746

/- The conditional theorem of J. B. Conrey (1983) on derivatives of ξ, in the classical Laguerre–Pólya theory of real zeros associated with Pólya and Speiser. -/


open Complex
namespace XiZeros

/-- Difference of the squared distances to the zero and its reflection across the circle. -/
theorem reflected_distance {R a x y : ℝ} (ha : a ≠ 0) :
    a^2 * ((x^2 + (y-R^2/a)^2) - (x^2 + (y-a)^2)) =
      (R^2-a^2)*((y-a)^2+R^2-y^2) := by
  field_simp
  ring

/-- Strictly positive real part of the logarithmic derivative of each disk factor
to the right of the imaginary axis. -/
theorem factor_pos {R a : ℝ} {z : ℂ} (ha : a ≠ 0) (haR : a^2 < R^2)
    (hy : z.im^2 < R^2) (hx : 0 < z.re) :
    0 < ((z - a * I)⁻¹ - (z - (R^2/a : ℝ) * I)⁻¹).re := by
  have hdiff := reflected_distance (R := R) (x := z.re) (y := z.im) ha
  have hmul : 0 < (R^2-a^2)*((z.im-a)^2+R^2-z.im^2) :=
    mul_pos (by linarith) (by nlinarith [sq_nonneg (z.im-a)])
  have hd : z.re^2 + (z.im-a)^2 < z.re^2 + (z.im-R^2/a)^2 := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) (sub_nonpos.mpr h)
    linarith
  have hpos : 0 < z.re^2 + (z.im-a)^2 := by positivity
  simp only [sub_re, inv_re, normSq_apply, sub_im, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]
  simp only [← sq]
  exact sub_pos.mpr (div_lt_div_of_pos_left hx hpos hd)


/-- The unnormalized linear factor with zero ia and pole iA. -/
noncomputable def ratio (a A : ℝ) (z : ℂ) := (z-a*I)/(z-A*I)

theorem ratio_logDeriv {a A : ℝ} {z : ℂ} (hx : z.re ≠ 0) :
    logDeriv (ratio a A) z = (z-a*I)⁻¹ - (z-A*I)⁻¹ := by
  have nz (b : ℝ) : z-b*I ≠ 0 := by
    intro h
    have H := congrArg Complex.re h
    simp at H
    exact hx H
  unfold ratio
  rw [logDeriv_div (f := fun w : ℂ => w-a*I) (g := fun w : ℂ => w-A*I) z (nz a) (nz A) (by fun_prop) (by fun_prop)]
  simp [logDeriv_apply, one_div]

/-- Norm identity on the boundary circle, in squared real coordinates. -/
theorem boundary_reflection {x y a R : ℝ} (ha : a ≠ 0) (h : x^2+y^2 = R^2) :
    a^2 * (x^2+(y-R^2/a)^2) = R^2 * (x^2+(y-a)^2) := by
  field_simp
  linear_combination (norm := ring_nf) (a^2 - R^2) * h

/-- Reflected evaluation in the other half-plane reverses the sign. -/
theorem factor_neg {R a : ℝ} {z : ℂ} (ha : a ≠ 0) (haR : a^2 < R^2)
    (hy : z.im^2 < R^2) (hx : z.re < 0) :
    ((z - a * I)⁻¹ - (z - (R^2/a : ℝ) * I)⁻¹).re < 0 := by
  have P := factor_pos (a := -a) (z := -z) (R := R) (neg_ne_zero.mpr ha)
    (by simpa using haR) (by simpa using hy) (by simpa using hx)
  rw [div_neg] at P
  simp only [Complex.ofReal_neg, neg_mul, sub_neg_eq_add] at P
  rw [show -z+↑a*I = -(z-↑a*I) by ring,
    show -z+(↑(R^2/a : ℝ):ℂ)*I = -(z-(↑(R^2/a : ℝ):ℂ)*I) by ring] at P
  simp only [inv_neg, sub_re, neg_re] at P ⊢
  linarith

end XiZeros

open Complex Filter Topology
namespace XiZeros

/-- The constant slope of the zero-free logarithm drops out when the same
disk decomposition is evaluated at opposite points. -/
theorem opposite_comparison {f g p q L₁ L₂ : ℂ}
    (h₁ : f = p + L₁) (h₂ : g = q + L₂) (hopp : g = -f)
    (hp : 0 ≤ p.re) (hq : q.re ≤ 0) :
    -(‖L₁-L₂‖) ≤ 2*f.re := by
  have h₃ := (abs_le.mp (Complex.abs_re_le_norm (L₁-L₂))).1
  have heq : f-g = p-q+(L₁-L₂) := by rw [h₁,h₂]; ring
  rw [hopp] at heq
  have hh := congrArg Complex.re heq
  simp only [sub_re, neg_re, add_re] at hh h₃
  linarith

/-- Sign-changing symmetry in all derivatives yields odd logarithmic derivative. -/
theorem opposite_logDeriv {F : ℂ → ℂ} {b : ℂ}
    (hb : b ≠ 0) (hs : ∀ z, F (-z) = b*F z) (z : ℂ) :
    logDeriv F (-z) = -logDeriv F z := by
  have heq : (fun w => F (-w)) = fun w => b*F w := funext hs
  have h := congrArg (fun f : ℂ → ℂ => deriv f z) heq
  change deriv (fun w => F (-w)) z = deriv (fun w => b*F w) z at h
  rw [deriv_comp_neg, deriv_const_mul_field] at h
  simp only [logDeriv_apply, hs]
  rw [show deriv F (-z) = -(b*deriv F z) by linear_combination -h]
  rw [neg_div, mul_div_mul_left _ _ hb]

end XiZeros


open Set Metric Complex
namespace XiZeros

/-- Derivatives of a normalized logarithm are nearly constant well inside a disk.
The real part is the only quantity that needs an upper bound. -/
theorem disk_log_deriv_difference {g : ℂ → ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hd : DifferentiableOn ℂ g (ball 0 (4*r))) (hzero : g 0 = 0)
    (hb : ∀ w ∈ ball 0 (4*r), (g w).re ≤ M)
    {z v : ℂ} (hz : ‖z‖ < r) (hv : ‖v‖ < r) :
    ‖deriv g z - deriv g v‖ ≤ (4*M / r^2) * ‖z-v‖ := by
  have span (x w : ℂ) (hx : ‖x‖ < r) (hw : ‖w-x‖ ≤ r) : ‖w‖ ≤ 2*r := by
    have ht := norm_add_le (w-x) x
    rw [sub_add_cancel] at ht
    linarith
  have small {x : ℂ} (hx : x ∈ ball 0 r) : closedBall x r ⊆ ball 0 (4*r) := by
    intro w hw
    rw [mem_ball_zero_iff]
    have := span x w (mem_ball_zero_iff.mp hx) (mem_closedBall_iff_norm.mp hw)
    linarith
  have g2 (x : ℂ) (hx : x ∈ ball 0 r) : ‖deriv (deriv g) x‖ ≤ 4*M / r^2 := by
    have bound (w : ℂ) (hw : w ∈ sphere x r) : ‖g w‖ ≤ 2*M := by
      have h2 := span x w (mem_ball_zero_iff.mp hx) (mem_sphere_iff_norm.mp hw).le
      have h4 : ‖w‖ < 4*r := by linarith
      have H := Complex.borelCaratheodory_zero hM hd hb (by positivity)
        (mem_ball_zero_iff.mpr h4) hzero
      refine H.trans ((div_le_iff₀ (by linarith)).mpr ?_)
      nlinarith [mul_nonneg hM.le (sub_nonneg.mpr h2)]
    have H := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr
      (hd.diffContOnCl_ball (small hx)) bound
    norm_num [iteratedDeriv_succ, Nat.factorial, ← mul_assoc] at H
    exact H
  have hsub : ball (0:ℂ) r ⊆ ball 0 (4*r) := ball_subset_ball (by linarith)
  have hdiff := (hd.deriv isOpen_ball).mono hsub
  have H := (convex_ball (0:ℂ) r).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => hdiff.differentiableAt (isOpen_ball.mem_nhds hx)) g2
    (mem_ball_zero_iff.mpr hv) (mem_ball_zero_iff.mpr hz)
  exact H

end XiZeros


open Set Metric Complex
namespace XiZeros

theorem normalized_log {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ F (ball 0 r)) (hn : ∀ x ∈ ball 0 r, F x ≠ 0) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧ ∀ x ∈ ball 0 r,
      HasDerivAt L (logDeriv F x) x ∧ F x = F 0 * exp (L x) := by
  have hdl : DifferentiableOn ℂ (logDeriv F) (ball 0 r) :=
    (hd.deriv isOpen_ball).div hd hn
  obtain ⟨L, hL0, hL⟩ := hdl.isExactOn_ball.with_val_at 0 0
  have hde (x : ℂ) (hx : x ∈ ball 0 r) :
      HasDerivAt (fun w => exp (L w)) (exp (L x) * logDeriv F x) x :=
    (hL x hx).cexp
  have heq : EqOn (logDeriv F) (logDeriv (fun w => exp (L w))) (ball 0 r) := by
    intro x hx
    conv_rhs => rw [logDeriv_apply, (hde x hx).deriv]
    field_simp
  obtain ⟨c, _, hc⟩ := (logDeriv_eqOn_iff hd
    (fun x hx => (hde x hx).differentiableAt.differentiableWithinAt) isOpen_ball
    (convex_ball (0:ℂ) r).isPreconnected (fun x _ => exp_ne_zero _) hn).mp heq
  have hc0 := hc (mem_ball_self hr)
  simp only [Pi.smul_apply, smul_eq_mul, hL0, Complex.exp_zero, mul_one] at hc0
  refine ⟨L, hL0, fun x hx => ⟨hL x hx, ?_⟩⟩
  simpa [hc0] using hc hx

end XiZeros

open Complex Filter Metric Set Topology
namespace XiZeros

/-- A holomorphic logarithmic derivative with nonnegative real part cannot vanish
at an interior point unless the original entire function is constant. -/
theorem strict_of_half_plane {F : ℂ → ℂ} (hd : Differentiable ℂ F)
    (hne : ∃ u v, F u ≠ F v)
    (hn : ∀ w : ℂ, 0 < w.re → F w ≠ 0)
    (hsign : ∀ w : ℂ, 0 < w.re → 0 ≤ (logDeriv F w).re) :
    ∀ z : ℂ, 0 < z.re → deriv F z ≠ 0 := by
  intro z hz hzero
  let U := {w : ℂ | 0 < w.re}
  have ho : IsOpen U := isOpen_lt continuous_const continuous_re
  have nh : U ∈ 𝓝 z := ho.mem_nhds hz
  have hld : DifferentiableOn ℂ (logDeriv F) U :=
    hd.deriv.differentiableOn.div hd.differentiableOn hn
  have hv : logDeriv F z = 0 := by simp [logDeriv_apply,hzero]
  have hl : ∀ᶠ w in 𝓝 z, logDeriv F w = 0 := by
    rcases (hld.analyticOnNhd ho z hz).eventually_constant_or_nhds_le_map_nhds with h | h
    · simpa [hv] using h
    · rw [hv] at h
      have hb : {v : ℂ | 0 ≤ v.re} ∈ Filter.map (logDeriv F) (𝓝 z) := by
        apply Filter.mem_map.mpr
        exact Filter.mem_of_superset nh fun w hw => hsign w hw
      obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (h hb)
      have hm : (-((r/2 : ℝ) : ℂ)) ∈ ball 0 r := by
        simp [abs_of_pos hr]
        linarith
      have hf := hsub hm
      change 0 ≤ (-((r/2 : ℝ) : ℂ)).re at hf
      simp at hf
      linarith
  have hlocal : deriv F =ᶠ[𝓝 z] (0 : ℂ → ℂ) := by
    filter_upwards [hl, nh] with w hw hwu
    exact (div_eq_zero_iff.mp (show deriv F w / F w = 0 from hw)).resolve_right (hn w hwu)
  have hglobal := (hd.deriv.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq analyticOnNhd_const hlocal
  obtain ⟨u,v,huv⟩ := hne
  exact huv (is_const_of_deriv_eq_zero hd (fun w => congrFun hglobal w) u v)

end XiZeros


namespace XiZeros

noncomputable def xi (s : ℂ) : ℂ := (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

theorem xi_entire : Differentiable ℂ xi := by
  unfold xi
  have hd := differentiable_completedZeta₀
  fun_prop

theorem xi_symm (s : ℂ) : xi (1-s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

theorem xi_eq_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s-1) * completedRiemannZeta s / 2 := by
  rw [xi, completedRiemannZeta_eq]
  field_simp [h0, sub_ne_zero.mpr (Ne.symm h1)]
  ring

theorem xi_half_of_rh (h : RiemannHypothesis) {s : ℂ} (hz : xi s = 0) :
    s.re = 1/2 := by
  suffices hor : ∀ z : ℂ, 0 < z.re → xi z = 0 → z.re = 1/2 by
    by_cases hp : 0 < s.re
    · exact hor s hp hz
    · have hs := hor (1-s) (by simp; linarith) ((xi_symm s).trans hz)
      simp at hs
      linarith
  intro z hp hzero
  have h0 : z ≠ 0 := by rintro rfl; simp at hp
  have h1 : z ≠ 1 := by rintro rfl; norm_num [xi] at hzero
  rw [xi_eq_completed h0 h1] at hzero
  have hΛ : completedRiemannZeta z = 0 := by
    rcases (mul_eq_zero.mp ((div_eq_zero_iff.mp hzero).resolve_right (by norm_num))).resolve_left
        (mul_ne_zero h0 (sub_ne_zero.mpr h1)) with h'
    exact h'
  apply h z _ _ h1
  · simp [riemannZeta_def_of_ne_zero h0, hΛ]
  · rintro ⟨k, hk⟩
    rw [hk] at hp
    simp at hp
    linarith [Nat.cast_nonneg (α := ℝ) k]

noncomputable def centered (z : ℂ) : ℂ := xi (1/2 + z)

theorem centered_even (z : ℂ) : centered (-z) = centered z := by
  unfold centered
  convert xi_symm (1/2+z) using 2
  ring

theorem centered_parity (n : ℕ) (z : ℂ) :
    iteratedDeriv n centered z = (-1 : ℂ)^n * iteratedDeriv n centered (-z) := by
  have heq : (fun t => centered (-t)) = centered := funext centered_even
  simpa only [heq, smul_eq_mul] using iteratedDeriv_comp_neg n centered z

theorem centered_to_root (h : ∀ m : ℕ, 0 < m → ∀ z : ℂ,
    iteratedDeriv m centered z = 0 → z.re = 0) :
    ∀ m : ℕ, 0 < m → ∀ s : ℂ, iteratedDeriv m xi s = 0 → s.re = 1/2 := by
  intro m hm s hs
  have h₁ : (1/2 : ℂ) + (s-1/2) = s := by ring
  have hh := h m hm (s-1/2) (by
    change iteratedDeriv m (fun z : ℂ => xi (1/2 + z)) (s-1/2) = 0
    simp only [iteratedDeriv_comp_const_add, h₁]
    exact hs)
  simp at hh
  linarith

end XiZeros

open Complex Real BigOperators
namespace XiZeros

theorem one_le_zeta_nat_re {k : ℕ} (hk : 1 < k) : 1 ≤ (riemannZeta k).re := by
  let Z := ∑' j : ℕ, 1/(j:ℝ)^k
  have hS : riemannZeta k = (Z : ℂ) := by
    rw [zeta_nat_eq_tsum_of_gt_one hk, Complex.ofReal_tsum]
    push_cast
    rfl
  rw [hS, Complex.ofReal_re]
  have H := (Real.summable_one_div_nat_pow.mpr hk).le_tsum (1:ℕ) (fun j _ => by positivity)
  simpa [Z] using H

theorem lower_even_completed (n : ℕ) :
    let k := 2*(n+1)
    (n.factorial:ℝ) / Real.pi^(n+1) ≤
      (((k:ℂ) * (k-1) * completedRiemannZeta k)/2).re := by
  let k := 2*(n+1)
  change (n.factorial:ℝ) / Real.pi^(n+1) ≤ (((k:ℂ) * ((k:ℂ)-1) * completedRiemannZeta k)/2).re
  have hk : 1 < k := by dsimp [k]; omega
  have h0 : (k:ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have half : (k:ℂ)/2 = n+1 := by simp [k]
  have gammaEq : Gammaℝ (k:ℂ) = ((((n.factorial:ℝ) / Real.pi^(n+1)):ℝ):ℂ) := by
    rw [Gammaℝ_def, neg_div, half, Complex.Gamma_nat_eq_factorial,
      show (n:ℂ)+1 = ((n+1 : ℕ):ℂ) by push_cast; rfl,
      Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    ring
  have hn : 0 < (n.factorial:ℝ)/Real.pi^(n+1) := by positivity
  have hg : Gammaℝ (k:ℂ) ≠ 0 := by rw [gammaEq]; exact_mod_cast hn.ne'
  have hΛ := (div_eq_iff hg).mp (riemannZeta_def_of_ne_zero h0).symm
  rw [hΛ, gammaEq]
  set b := (n.factorial:ℝ)/Real.pi^(n+1)
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have h := one_le_zeta_nat_re hk
  simp [Complex.div_ofNat_re, Complex.mul_re, Complex.mul_im]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hn.le,
    mul_nonneg (show 0 ≤ (k:ℝ) * (k-1) - 2 by nlinarith [sq_nonneg ((k:ℝ)-2)])
      (mul_nonneg (by linarith : 0 ≤ (riemannZeta k).re) hn.le)]

end XiZeros


namespace XiZeros
open Complex MeromorphicOn Metric Set Filter Function
open scoped Topology

lemma boundary_divisor_zero {h : ℂ → ℂ} {R : ℝ}
    (ha : AnalyticOnNhd ℂ h (closedBall 0 R))
    (hb : ∀ w ∈ sphere 0 R, h w ≠ 0) : divisor h (sphere 0 R) = 0 := by
  ext w
  by_cases hw : w ∈ sphere 0 R
  · rw [divisor_apply (ha.mono sphere_subset_closedBall).meromorphicOn hw]
    have hm := ((ha w (sphere_subset_closedBall hw)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr (hb w hw)
    simp [hm]
  · exact (divisor h (sphere 0 R)).apply_eq_zero_of_notMem hw

-- Values on the boundary, at the center, and locally at each nonreal evaluation point.
lemma finite_factor {h H : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (ha : AnalyticOnNhd ℂ h (closedBall 0 R)) (hb : ∀ w ∈ sphere 0 R, h w ≠ 0)
    (D : ECanonicalDecomp h H R) {w : ℂ} (hw : w ∈ closedBall 0 R) (hn : h w ≠ 0) :
    H w = (∏ a ∈ D.meromorphicOn.divisor_ball_support_finite.toFinset,
      canonicalFactor R a w ^ (divisor h (ball 0 R) a)) * h w := by
  have hm : meromorphicOrderAt h w = 0 :=
    ((ha w hw).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr hn
  rw [D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt hw hm hR,
    boundary_divisor_zero ha hb, (ha w hw).meromorphicTrailingCoeffAt_of_ne_zero hn]
  simp only [locallyFinsuppWithin.coe_zero, Pi.zero_apply, neg_zero, zpow_zero, finprod_one, mul_one, smul_eq_mul]
  congr 1
  apply finprod_eq_prod_of_mulSupport_subset
  intro a ha'
  apply D.meromorphicOn.divisor_ball_support_finite.mem_toFinset.mpr
  change divisor h (ball 0 R) a ≠ 0
  intro he
  exact ha' (by simp [he])
end XiZeros

namespace XiZeros
open Complex Filter Metric Set MeromorphicOn Function
open scoped Topology

lemma canonical_log {R a : ℝ} {z : ℂ} (hr : 0 < R) (ha : a ≠ 0) (hz : z.re ≠ 0) :
    logDeriv (canonicalFactor R (a*I)) z =
      -((z-a*I)⁻¹ - (z-(R^2/a : ℝ)*I)⁻¹) := by
  have A : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have C : (a:ℂ)*I/(R:ℂ) ≠ 0 := div_ne_zero (mul_ne_zero A I_ne_zero) (ofReal_ne_zero.mpr hr.ne')
  have eq : canonicalFactor R (a*I) =
      fun w : ℂ => ((a:ℂ)*I/R) * (ratio a (R^2/a) w) ^ (-1:ℤ) := by
    funext w
    simp only [canonicalFactor_apply, map_mul, conj_ofReal, conj_I, ratio,
      zpow_neg_one, inv_div, ofReal_div, ofReal_pow]
    rw [show (R:ℂ)^2 - ↑a * -I * w = (↑a * I) * (w-((R:ℂ)^2/↑a)*I) by
      field_simp; linear_combination (norm := ring_nf) (R:ℂ)^2 * I_sq]
    simp only [div_eq_mul_inv, mul_inv_rev]; ring
  have nz (b : ℝ) : z-b*I ≠ 0 := by
    intro he
    exact hz (by simpa using congrArg re he)
  rw [eq, logDeriv_const_mul _ _ C, logDeriv_fun_zpow, ratio_logDeriv hz]
  · simp
  · unfold ratio
    exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w-a*I) z).div
      (by fun_prop) (nz _)

lemma nowhere_flat {f : ℂ → ℂ} (hf : Differentiable ℂ f) {p : ℂ} (hp : f p ≠ 0) :
    ∀ w, meromorphicOrderAt f w ≠ ⊤ := by
  have hm : Meromorphic f := fun w => (hf.analyticAt w).meromorphicAt
  apply hm.exists_meromorphicOrderAt_ne_top_iff_forall.mp
  exact ⟨p, by rw [((hf.analyticAt p).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr hp]; simp⟩

lemma good_radius {f : ℂ → ℂ} (hf : Differentiable ℂ f) {p : ℂ} (hp : f p ≠ 0)
    {T : ℝ} : ∃ R ∈ Ioo T (T+1), ∀ w ∈ sphere 0 R, f w ≠ 0 := by
  let K := closedBall (0:ℂ) (T+1)
  have hm : MeromorphicOn f K := fun z _ => (hf.analyticAt z).meromorphicAt
  have hfinit := (isCompact_closedBall (0:ℂ) (T+1)).finite_sdiff_of_mem_codiscreteWithin
    (hm.eventually_codiscreteWithin_apply_ne_zero (fun w _ => nowhere_flat hf hp w))
  obtain ⟨R, hR, h⟩ := (Set.Ioo_infinite (show T < T+1 by linarith)).exists_notMem_finset
    (hfinit.image (fun w : ℂ => ‖w‖)).toFinset
  refine ⟨R,hR,fun w hw hz => h ?_⟩
  apply (hfinit.image (fun w : ℂ => ‖w‖)).mem_toFinset.mpr
  refine ⟨w,⟨mem_closedBall_zero_iff.mpr ?_, ?_⟩,mem_sphere_zero_iff_norm.mp hw⟩
  · rw [mem_sphere_zero_iff_norm.mp hw]; exact hR.2.le
  · simp [hz]


lemma disk_comparison {f : ℂ → ℂ} {R B : ℝ} (hr : 0 < R) (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (axis : ∀ a, f a = 0 → a.re = 0)
    (clean : ∀ w ∈ sphere 0 R, f w ≠ 0)
    (hb : ∀ w ∈ sphere 0 R, ‖f w‖ ≤ Real.exp B)
    (hM : 0 < B - Real.log ‖f 0‖)
    {w v : ℂ} (hw : ‖w‖ < R/4) (hv : ‖v‖ < R/4)
    (hw' : 0 < w.re) (hv' : v.re < 0)
    (opp : logDeriv f v = - logDeriv f w) :
    -(4*(B - Real.log ‖f 0‖)/(R/4)^2 * ‖w-v‖) ≤ 2*(logDeriv f w).re := by
  classical
  have A : AnalyticOnNhd ℂ f (closedBall 0 R) := fun z _ => hf.analyticAt z
  obtain ⟨H,D⟩ := A.meromorphicOn.exists_ecanonicalDecomp (fun u => nowhere_flat hf h0 u)
  let d := divisor f (ball 0 R)
  let S := D.meromorphicOn.divisor_ball_support_finite.toFinset
  have ds {a} (ha : a ∈ S) : d a ≠ 0 := D.meromorphicOn.divisor_ball_support_finite.mem_toFinset.mp ha
  have inside {a} (ha : a ∈ S) : a ∈ ball 0 R := d.supportWithinDomain (ds ha)
  have dz {a} (ha : a ∈ S) : f a = 0 := by
    by_contra h
    apply ds ha
    have := ((hf.analyticAt a).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr h
    simp [d, divisor_apply (A.meromorphicOn.mono_set ball_subset_closedBall) (inside ha), this]
  have dpos (a : ℂ) : 0 ≤ d a := (A.mono ball_subset_closedBall).divisor_nonneg a
  let P := fun z : ℂ => ∏ a ∈ S, canonicalFactor R a z ^ (d a)
  have HP {z} (hz : z ∈ closedBall 0 R) (hn : f z ≠ 0) : H z = P z * f z :=
    finite_factor hr A clean D hz hn
  have bH (z) (hz : z ∈ sphere (0:ℂ) R) : ‖H z‖ ≤ Real.exp B := by
    rw [HP (sphere_subset_closedBall hz) (clean z hz), norm_mul]
    have : ‖P z‖ = 1 := by
      simp only [P, norm_prod, norm_zpow]
      exact Finset.prod_eq_one fun a ha => by rw [norm_canonicalFactor_eval_circle_eq_one (inside ha) hz, one_zpow]
    simpa [this] using hb z hz
  have center : ‖f 0‖ ≤ ‖H 0‖ := by
    rw [HP (mem_closedBall_self hr.le) h0, norm_mul]
    apply le_mul_of_one_le_left (norm_nonneg _) 
    simp only [P,norm_prod,norm_zpow]
    apply Finset.one_le_prod
    intro a ha
    apply one_le_zpow₀ _ (dpos a)
    have an : a ≠ 0 := by rintro rfl; exact h0 (dz ha)
    have ar := mem_ball_zero_iff.mp (inside ha)
    simp [canonicalFactor_apply, norm_pow, abs_of_pos hr]
    apply (one_le_div (mul_pos hr (norm_pos_iff.mpr an))).mpr
    nlinarith [mul_le_mul_of_nonneg_left ar.le hr.le]
  have Hdiff := D.analyticOnNhd.differentiableOn
  have small : ball (0:ℂ) R ⊆ closedBall 0 R := ball_subset_closedBall
  obtain ⟨L,L0,hL⟩ := normalized_log hr (Hdiff.mono small) (fun z hz => D.ne_zero z (small hz))
  have Ldiff : DifferentiableOn ℂ L (ball 0 R) := fun z hz => (hL z hz).1.differentiableAt.differentiableWithinAt
  have Lbound : ∀ z ∈ ball 0 R, (L z).re ≤ B - Real.log ‖f 0‖ := by
    intro z hz
    have HH := Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0:ℂ) R)
      (isBounded_ball) (Hdiff.diffContOnCl_ball (by intro x hx; exact hx))
      (fun u hu => bH u (by rwa [frontier_ball _ hr.ne'] at hu)) (subset_closure hz)
    rw [(hL z hz).2, norm_mul, Complex.norm_exp] at HH
    have : ‖f 0‖ * Real.exp (L z).re ≤ Real.exp B :=
      (mul_le_mul_of_nonneg_right center (Real.exp_pos _).le).trans HH
    rw [← Real.exp_log (norm_pos_iff.mpr h0), ← Real.exp_add, Real.exp_le_exp] at this
    linarith
  let Q := fun z : ℂ => ∑ a ∈ S, (d a : ℂ) * logDeriv (canonicalFactor R a) z
  have ld {z : ℂ} (hz : z ∈ ball 0 R) (hn : z.re ≠ 0) :
      logDeriv f z = -Q z + deriv L z := by
    have fnz : f z ≠ 0 := fun e => hn (axis _ e)
    have za {a} (ha : a ∈ S) : z ≠ a := fun he => hn (he ▸ axis _ (dz ha))
    have nd (a) (ha : a ∈ S) := canonicalFactor_ne_zero (inside ha) (small hz) (za ha)
    have ad (a) (ha : a ∈ S) := (analyticOnNhd_canonicalFactor R a z (za ha)).differentiableAt
    have dp (a) (ha : a ∈ S) : DifferentiableAt ℂ (fun x => canonicalFactor R a x ^ d a) z :=
      (differentiableAt_zpow.2 (Or.inl (nd a ha))).comp z (ad a ha)
    have eh : H =ᶠ[𝓝 z] fun x => P x * f x := by
      filter_upwards [isOpen_ball.mem_nhds hz, hf.continuous.continuousAt.eventually_ne fnz] with x hx hnx
      exact HP (small hx) hnx
    have l := (logDeriv_congr_nhds eh).eq_of_nhds
    rw [logDeriv_mul (f := P) (g := f) z (Finset.prod_ne_zero_iff.mpr fun a ha => zpow_ne_zero _ (nd a ha))
      fnz (.fun_finsetProd dp) (hf z)] at l
    have lP : logDeriv P z = Q z := by
      rw [show P = (fun x => ∏ a ∈ S, (fun u => canonicalFactor R a u ^ d a) x) from rfl,
        logDeriv_prod (f := fun a x => canonicalFactor R a x ^ d a) (fun a ha => zpow_ne_zero _ (nd a ha)) dp]
      exact Finset.sum_congr rfl fun a ha => logDeriv_fun_zpow (ad a ha) _
    rw [(hL z hz).1.deriv, ← lP, l]; ring
  have sign {z : ℂ} (hz : ‖z‖ < R/4) (hn : z.re ≠ 0) :
      (0 < z.re → (Q z).re ≤ 0) ∧ (z.re < 0 → 0 ≤ (Q z).re) := by
    have one (a) (ha : a ∈ S) :
        (0 < z.re → ((d a : ℂ) * logDeriv (canonicalFactor R a) z).re ≤ 0) ∧
        (z.re < 0 → 0 ≤ ((d a : ℂ) * logDeriv (canonicalFactor R a) z).re) := by
      have ax := axis a (dz ha)
      have ai : a = (a.im:ℂ)*I := by apply Complex.ext <;> simp [ax]
      have an : a.im ≠ 0 := by
        intro e; have az : a = 0 := by rw [ai,e]; simp
        exact h0 (az ▸ dz ha)
      have ar := mem_ball_zero_iff.mp (inside ha)
      have aim := Complex.abs_im_le_norm a
      have zim := Complex.abs_im_le_norm z
      have a2 : a.im^2 < R^2 := by nlinarith [sq_abs a.im, sq_lt_sq' (show -R < |a.im| by linarith [abs_nonneg a.im]) (show |a.im| < R by linarith)]
      have z2 : z.im^2 < R^2 := by nlinarith [sq_abs z.im, sq_lt_sq' (show -R < |z.im| by linarith [abs_nonneg z.im]) (show |z.im| < R by linarith)]
      rw [show canonicalFactor R a = canonicalFactor R ((a.im:ℂ)*I) from congrArg _ ai,
        canonical_log hr an hn]
      simp only [mul_re, intCast_re, intCast_im, zero_mul, sub_zero, neg_re]
      have dn : 0 ≤ (d a : ℝ) := by exact_mod_cast dpos a
      exact ⟨fun e => mul_nonpos_of_nonneg_of_nonpos dn (neg_nonpos.mpr (factor_pos an a2 z2 e).le),
        fun e => mul_nonneg dn (neg_nonneg.mpr (factor_neg an a2 z2 e).le)⟩
    simp only [Q, re_sum]
    exact ⟨fun e => Finset.sum_nonpos fun a ha => (one a ha).1 e,
      fun e => Finset.sum_nonneg fun a ha => (one a ha).2 e⟩
  have atW := ld (mem_ball_zero_iff.mpr (show ‖w‖ < R by linarith)) hw'.ne'
  have atV := ld (mem_ball_zero_iff.mpr (show ‖v‖ < R by linarith)) hv'.ne
  have cmp := opposite_comparison atW atV opp (by simpa using (sign hw hw'.ne').1 hw')
    (by simpa using (sign hv hv'.ne).2 hv')
  have err := disk_log_deriv_difference (r := R/4) (by positivity) hM
    (by rwa [show 4*(R/4)=R by ring]) L0 (by rwa [show 4*(R/4)=R by ring]) hw hv
  exact (neg_le_neg err).trans cmp


def Subquadratic (F : ℂ → ℂ) : Prop := ∀ (c : ℂ) (C : ℝ), ∃ B : ℝ → ℝ,
    Tendsto (fun R => (B R - C)/R^2) atTop (𝓝 0) ∧
    ∀ᶠ R in atTop, C < B R ∧ ∀ w ∈ sphere (0:ℂ) R, ‖F (c+w)‖ ≤ Real.exp (B R)

lemma sign_of_growth {F : ℂ → ℂ} (hd : Differentiable ℂ F) (hne : ∃ u v, F u ≠ F v)
    (hg : Subquadratic F) (axis : ∀ z, F z = 0 → z.re = 0) {b : ℂ} (hb : b ≠ 0)
    (symm : ∀ z, F (-z) = b*F z) {z : ℂ} (hz : 0 < z.re) : 0 ≤ (logDeriv F z).re := by
  obtain ⟨p,hp⟩ : ∃ p, F p ≠ 0 := by
    by_contra! h
    obtain ⟨u,v,hu⟩ := hne
    exact hu ((h u).trans (h v).symm)
  obtain ⟨t,ht,clean⟩ := good_radius hd hp (T := 1)
  let c : ℂ := (t:ℂ)*I
  have hc : c.re = 0 := by simp [c]
  have hfc : F c ≠ 0 := clean c (by simp [c,abs_of_pos (show 0<t by linarith [ht.1])])
  let f := fun x : ℂ => F (c+x)
  have fd : Differentiable ℂ f := hd.comp (show Differentiable ℂ (fun x : ℂ => c+x) by fun_prop)
  have f0 : f 0 ≠ 0 := by simpa [f] using hfc
  have fa (a : ℂ) (h : f a = 0) : a.re = 0 := by simpa [hc] using axis (c+a) h
  let w := z-c
  let v := -z-c
  have link (x : ℂ) : logDeriv f x = logDeriv F (c+x) := by
    simp only [logDeriv_apply, f, deriv_comp_const_add]
  have W : logDeriv f w = logDeriv F z := by simp [link,w]
  have V : logDeriv f v = -logDeriv F z := by simpa [link,v] using opposite_logDeriv hb symm z
  obtain ⟨B,lim,maj⟩ := hg c (Real.log ‖f 0‖)
  have E : Tendsto (fun R => -(4*(B R - Real.log ‖f 0‖)/(R/4)^2 * ‖w-v‖)) atTop (𝓝 0) := by
    convert ((lim.const_mul 64).mul_const ‖w-v‖).neg using 1
    · funext R; ring
    · simp
  have often : ∃ᶠ R in atTop, ∀ u ∈ sphere 0 R, f u ≠ 0 := by
    apply frequently_atTop.mpr
    intro a
    obtain ⟨R,hR,h⟩ := good_radius fd f0 (T := max 0 a)
    exact ⟨R,(le_max_right ..).trans hR.1.le,h⟩
  have ev := (maj.and (eventually_gt_atTop (4 * (‖w‖+‖v‖+1))))
  have res : 0 ≤ 2*(logDeriv F z).re := le_of_tendsto_of_frequently E <|
    (often.and_eventually ev).mono (by
      intro R ⟨cleanR,⟨hm,majR⟩,hR⟩
      rw [← W]
      apply disk_comparison (by linarith [norm_nonneg w,norm_nonneg v]) fd f0 fa cleanR majR (sub_pos.mpr hm)
        (by linarith [norm_nonneg v]) (by linarith [norm_nonneg w])
        (by simpa [w,hc] using hz) (by simpa [v,hc] using hz)
      exact V.trans (congrArg Neg.neg W.symm))
  linarith


end XiZeros

/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

-- Adapted to Lean 4.33.1 for Wave 10C. See the accompanying LICENSE.
namespace LiCriterion
noncomputable def riemannXi (s : ℂ) : ℂ := (1/2 : ℂ) * s * (s-1) * completedRiemannZeta₀ s + 1/2
end LiCriterion

/-!
# A global bound on the completed ξ-function

Adapted from Parts A–G of Nicholas Bulka's `Lc/LiCriterion/XiGrowth.lean`
at commit `35df682f3b709ffe5fbcfdd452dfa964bd622b87` of
`nicholasbulka/li-criterion-rh-equivalence-lean`, under Apache 2.0.
This extract supplies the same definition of ξ, uses Mathlib alone, and ends
at `exists_xi_bound`. The modified theta kernel decays exponentially at
both Mellin endpoints after inversion, giving the bound at all complex arguments.
-/

namespace LiCriterion.XiGrowth

open Complex Real Set Filter MeasureTheory HurwitzZeta
open scoped Topology


/-! ## Part A: an elementary majorant -/

/-- The elementary bound `u ^ A * exp (-(p * u)) ≤ exp (A * log (A / p))`, valid for all
`u > 0`, `A ≥ 0`, `p > 0`.  This replaces any appeal to Stirling: it is just `log t ≤ t - 1`. -/
lemma rpow_mul_exp_neg_le {u A p : ℝ} (hu : 0 < u) (hA : 0 ≤ A) (hp : 0 < p) :
    u ^ A * rexp (-(p * u)) ≤ rexp (A * Real.log (A / p)) := by
  rcases eq_or_lt_of_le hA with rfl | hA'
  · have : rexp (-(p * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith : -(p * u) ≤ 0)
    simpa using this
  -- `A > 0`: take logarithms.
  have hAp : 0 < A / p := div_pos hA' hp
  have hkey : A * Real.log u - p * u ≤ A * Real.log (A / p) := by
    -- `log (u * p / A) ≤ u * p / A - 1`
    have h := Real.log_le_sub_one_of_pos (x := u * p / A) (by positivity)
    have hlog : Real.log (u * p / A) = Real.log u - Real.log (A / p) := by
      rw [Real.log_div (by positivity) (ne_of_gt hA'), Real.log_div (ne_of_gt hA') (ne_of_gt hp),
        Real.log_mul (ne_of_gt hu) (ne_of_gt hp)]
      ring
    rw [hlog] at h
    have hmul := mul_le_mul_of_nonneg_left h hA
    have : A * (u * p / A - 1) = p * u - A := by field_simp
    nlinarith [hA'.le]
  calc u ^ A * rexp (-(p * u))
      = rexp (A * Real.log u) * rexp (-(p * u)) := by
        rw [Real.rpow_def_of_pos hu]; ring_nf
    _ = rexp (A * Real.log u - p * u) := by rw [← Real.exp_add]; ring_nf
    _ ≤ rexp (A * Real.log (A / p)) := Real.exp_le_exp.2 hkey

/-! ## Part B: exponential decay of the theta kernel -/

/-- The even kernel at `a = 0` decays exponentially: there are `C, p > 0` with
`|Θ(x) - 1| ≤ C exp (-p x)` for every `x ≥ 1`.  Mathlib supplies the asymptotic; the content
here is upgrading it from `atTop` to all of `[1, ∞)` by compactness. -/
lemma exists_kernel_bound :
    ∃ C p : ℝ, 0 < C ∧ 0 < p ∧ ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub 0
  obtain ⟨c, hc⟩ := hO.bound
  obtain ⟨R, hR⟩ := eventually_atTop.1 hc
  set R' : ℝ := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  -- bound on the compact piece `[1, R']`
  have hcompact : IsCompact (Icc (1:ℝ) R') := isCompact_Icc
  have hcont : ContinuousOn (fun x : ℝ => evenKernel 0 x - 1) (Icc (1:ℝ) R') := by
    refine ContinuousOn.sub ?_ continuousOn_const
    exact (continuousOn_evenKernel 0).mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1)
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max (max c 0) (max (M * rexp (p * R')) 0) + 1, p, by positivity, hp, ?_⟩
  intro x hx1
  set C := max (max c 0) (max (M * rexp (p * R')) 0) + 1 with hC
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  rcases le_or_gt x R' with hle | hgt
  · -- compact range: use the sup bound, paying `exp (p R')`
    have h1 : |evenKernel 0 x - 1| ≤ M := by simpa using hM x ⟨hx1, hle⟩
    have h2 : M * rexp (p * R') * rexp (-(p * x)) ≤ C * rexp (-(p * x)) := by
      have : M * rexp (p * R') ≤ C := by
        have := le_max_left (M * rexp (p * R')) 0
        have h' := le_max_right (max c 0) (max (M * rexp (p * R')) 0)
        simp only [hC]; linarith [le_trans this h']
      exact mul_le_mul_of_nonneg_right this (le_of_lt (Real.exp_pos _))
    refine le_trans (le_trans h1 ?_) h2
    have hexp : (1:ℝ) ≤ rexp (p * R') * rexp (-(p * x)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    nlinarith [le_trans (abs_nonneg _) h1, Real.exp_pos (p * R'), Real.exp_pos (-(p*x))]
  · -- tail: use the `atTop` bound
    have hxR : R ≤ x := le_trans (le_max_left R 1) (le_of_lt hgt)
    have h1 : ‖evenKernel 0 x - 1‖ ≤ c * ‖rexp (-p * x)‖ := by simpa using hR x hxR
    have h2 : c ≤ C := by
      have := le_max_left c 0
      have h' := le_max_left (max c 0) (max (M * rexp (p * R')) 0)
      simp only [hC]; linarith [le_trans this h']
    have hnorm : ‖rexp (-p * x)‖ = rexp (-(p * x)) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; ring_nf
    rw [Real.norm_eq_abs, hnorm] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos _)))

/-! ## Part C: the modified kernel `f_modif` of the Riemann FE-pair -/

/-- The Riemann functional-equation pair, whose `Λ₀` is the completed zeta. -/
noncomputable abbrev PR : WeakFEPair ℂ := hurwitzEvenFEPair 0

lemma completedRiemannZeta₀_eq_mellin (s : ℂ) :
    completedRiemannZeta₀ s = (mellin PR.f_modif (s / 2)) / 2 := rfl

lemma f_modif_eq_of_one_lt {x : ℝ} (hx : 1 < x) :
    PR.f_modif x = (evenKernel 0 x : ℂ) - 1 := by
  simp [WeakFEPair.f_modif, hurwitzEvenFEPair, hx, not_lt.2 hx.le, Set.mem_Ioi, Set.mem_Ioo]

lemma f_modif_eq_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    PR.f_modif x = (evenKernel 0 x : ℂ) - ((x ^ (-(1/2) : ℝ) : ℝ) : ℂ) := by
  have hnot : ¬ (1 < x) := not_lt.2 hx1.le
  simp [WeakFEPair.f_modif, hurwitzEvenFEPair, hnot, hx0, hx1, Set.mem_Ioi, Set.mem_Ioo]

/-- On `(1, ∞)` the modified kernel inherits the exponential decay of the theta kernel. -/
lemma norm_f_modif_of_one_lt {C p : ℝ}
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)))
    {x : ℝ} (hx : 1 < x) : ‖PR.f_modif x‖ ≤ C * rexp (-(p * x)) := by
  rw [f_modif_eq_of_one_lt hx]
  have : ‖((evenKernel 0 x : ℂ) - 1)‖ = |evenKernel 0 x - 1| := by
    rw [show ((evenKernel 0 x : ℂ) - 1) = ((evenKernel 0 x - 1 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.norm_real _
  rw [this]
  exact hker x hx.le

/-- On `(0, 1)` the functional equation of the theta kernel converts the decay at `∞` into
decay at `0`: `‖f_modif x‖ ≤ C x^(-1/2) exp (-p/x)`. -/
lemma norm_f_modif_of_lt_one {C p : ℝ}
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)))
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖PR.f_modif x‖ ≤ x ^ (-(1/2) : ℝ) * (C * rexp (-(p / x))) := by
  have hinv : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
  -- the functional equation, at `a = 0`
  have hFE : evenKernel 0 x = x ^ (-(1/2) : ℝ) * evenKernel 0 (1 / x) := by
    rw [evenKernel_functional_equation 0 x, evenKernel_eq_cosKernel_of_zero,
      Real.rpow_neg hx0.le]
    ring
  have hval : PR.f_modif x = ((x ^ (-(1/2) : ℝ) * (evenKernel 0 (1 / x) - 1) : ℝ) : ℂ) := by
    rw [f_modif_eq_of_lt_one hx0 hx1, hFE]
    push_cast
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have hb := hker (1 / x) hinv
  have hpx : p * (1 / x) = p / x := by ring
  rw [hpx] at hb
  exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx0.le _)

/-! ## Part D: the Mellin integral estimate -/

/-- Pointwise bound for the Mellin integrand on `(0, 1]`. -/
lemma integrand_le_of_mem_Ioc {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)))
    (w : ℂ) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    ‖(x : ℂ) ^ (w - 1) • PR.f_modif x‖ ≤
      C * rexp (max (3/2 - w.re) 0 * Real.log (max (3/2 - w.re) 0 / p)) := by
  obtain ⟨hx0, hx1⟩ := hx
  set A := max (3/2 - w.re) 0 with hAdef
  have hA0 : 0 ≤ A := le_max_right _ _
  rcases eq_or_lt_of_le hx1 with rfl | hlt
  · -- at `x = 1` the modified kernel vanishes
    have h1 : PR.f_modif 1 = 0 := by
      simp [WeakFEPair.f_modif, Set.mem_Ioi, Set.mem_Ioo]
    simp only [h1, smul_zero, norm_zero]
    positivity
  · -- `0 < x < 1`
    have hnorm : ‖(x : ℂ) ^ (w - 1) • PR.f_modif x‖ = x ^ (w.re - 1) * ‖PR.f_modif x‖ := by
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp
    rw [hnorm]
    have hfb := norm_f_modif_of_lt_one hker hx0 hlt
    have hstep : x ^ (w.re - 1) * ‖PR.f_modif x‖
        ≤ x ^ (w.re - 1) * (x ^ (-(1/2) : ℝ) * (C * rexp (-(p / x)))) :=
      mul_le_mul_of_nonneg_left hfb (Real.rpow_nonneg hx0.le _)
    refine le_trans hstep ?_
    -- collect the powers of `x`
    have hxx : x ^ (w.re - 1) * x ^ (-(1/2) : ℝ) = x ^ (w.re - 3/2) := by
      rw [← Real.rpow_add hx0]; ring_nf
    have hcollect : x ^ (w.re - 1) * (x ^ (-(1/2) : ℝ) * (C * rexp (-(p / x))))
        = C * (x ^ (w.re - 3/2) * rexp (-(p / x))) := by
      rw [← hxx]; ring
    rw [hcollect]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    -- `x ^ (σ - 3/2) ≤ x ^ (-A)` because `x ≤ 1` and `-A ≤ σ - 3/2`
    have hmono : x ^ (w.re - 3/2) ≤ x ^ (-A) := by
      apply Real.rpow_le_rpow_of_exponent_ge hx0 hlt.le
      have : -A ≤ w.re - 3/2 := by
        simp only [hAdef, neg_le, le_max_iff]
        left; linarith
      linarith
    refine le_trans (mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le) ?_
    -- now apply the elementary majorant with `u = 1/x`
    have hu : (0:ℝ) < 1 / x := by positivity
    have hkey := rpow_mul_exp_neg_le (u := 1/x) (A := A) (p := p) hu hA0 hp
    have h1 : x ^ (-A) = (1/x) ^ A := by
      rw [one_div, Real.inv_rpow hx0.le, Real.rpow_neg hx0.le]
    have h2 : -(p / x) = -(p * (1/x)) := by ring
    rw [h1, h2]
    exact hkey

/-- Pointwise bound for the Mellin integrand on `(1, ∞)`. -/
lemma integrand_le_of_mem_Ioi {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)))
    (w : ℂ) {x : ℝ} (hx : x ∈ Ioi (1:ℝ)) :
    ‖(x : ℂ) ^ (w - 1) • PR.f_modif x‖ ≤
      C * rexp (max (w.re - 1) 0 * Real.log (max (w.re - 1) 0 / (p/2))) * rexp (-(p/2 * x)) := by
  have hx1 : (1:ℝ) < x := hx
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx1
  set B := max (w.re - 1) 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hnorm : ‖(x : ℂ) ^ (w - 1) • PR.f_modif x‖ = x ^ (w.re - 1) * ‖PR.f_modif x‖ := by
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp
  rw [hnorm]
  have hfb := norm_f_modif_of_one_lt hker hx1
  have hstep : x ^ (w.re - 1) * ‖PR.f_modif x‖ ≤ x ^ (w.re - 1) * (C * rexp (-(p * x))) :=
    mul_le_mul_of_nonneg_left hfb (Real.rpow_nonneg hx0.le _)
  refine le_trans hstep ?_
  -- `x ^ (σ - 1) ≤ x ^ B` because `x ≥ 1`
  have hmono : x ^ (w.re - 1) ≤ x ^ B :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (le_max_left _ _)
  have hstep2 : x ^ (w.re - 1) * (C * rexp (-(p * x))) ≤ x ^ B * (C * rexp (-(p * x))) := by
    have : (0:ℝ) ≤ C * rexp (-(p * x)) := by positivity
    exact mul_le_mul_of_nonneg_right hmono this
  refine le_trans hstep2 ?_
  -- split the exponential and apply the elementary majorant at rate `p/2`
  have hsplit : rexp (-(p * x)) = rexp (-(p/2 * x)) * rexp (-(p/2 * x)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have hkey := rpow_mul_exp_neg_le (u := x) (A := B) (p := p/2) hx0 hB0 (by positivity)
  calc x ^ B * (C * (rexp (-(p/2 * x)) * rexp (-(p/2 * x))))
      = C * (x ^ B * rexp (-(p/2 * x))) * rexp (-(p/2 * x)) := by ring
    _ ≤ C * rexp (B * Real.log (B / (p/2))) * rexp (-(p/2 * x)) := by
        have hxB : x ^ B * rexp (-(p/2 * x)) ≤ rexp (B * Real.log (B / (p/2))) := by
          have : -(p / 2 * x) = -(p/2 * x) := rfl
          exact hkey
        have hnn : (0:ℝ) ≤ rexp (-(p/2 * x)) := (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxB hC.le) hnn

/-- **The Mellin bound.**  The Mellin transform of the modified theta kernel is bounded by an
explicit expression in `Re w` alone.  No growth bound for `ζ` enters: the decay of the theta
kernel at `∞`, transported to `0` by the functional equation, is the whole input. -/
lemma norm_mellin_f_modif_le {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x))) (w : ℂ) :
    ‖mellin PR.f_modif w‖ ≤
      C * rexp (max (3/2 - w.re) 0 * Real.log (max (3/2 - w.re) 0 / p))
      + C * rexp (max (w.re - 1) 0 * Real.log (max (w.re - 1) 0 / (p/2))) * (2/p) := by
  have hp2 : (0:ℝ) < p/2 := by positivity
  set K₁ := C * rexp (max (3/2 - w.re) 0 * Real.log (max (3/2 - w.re) 0 / p)) with hK1
  set K₂ := C * rexp (max (w.re - 1) 0 * Real.log (max (w.re - 1) 0 / (p/2))) with hK2
  have hK1nn : 0 ≤ K₁ := by rw [hK1]; positivity
  have hK2nn : 0 ≤ K₂ := by rw [hK2]; positivity
  -- integrability of the Mellin integrand, for free from the FE-pair machinery
  have hint : IntegrableOn (fun t : ℝ => (t:ℂ) ^ (w - 1) • PR.f_modif t) (Ioi 0) :=
    (PR.isStrongFEPair_toStrongFEPair.hasMellin w).1
  set F : ℝ → ℝ := fun x => ‖(x:ℂ) ^ (w - 1) • PR.f_modif x‖ with hFdef
  have hFint : IntegrableOn F (Ioi 0) := hint.norm
  have hFint1 : IntegrableOn F (Ioc 0 1) := hFint.mono_set Ioc_subset_Ioi_self
  have hFint2 : IntegrableOn F (Ioi 1) := hFint.mono_set (Ioi_subset_Ioi zero_le_one)
  -- ‖∫‖ ≤ ∫ ‖·‖, then split at 1
  have hstep1 : ‖mellin PR.f_modif w‖ ≤ ∫ x in Ioi (0:ℝ), F x :=
    norm_integral_le_integral_norm _
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi (1:ℝ)) := by
    rw [Set.disjoint_left]
    intro a ha ha'
    exact absurd (mem_Ioi.1 ha') (not_lt.2 ha.2)
  have hsplit : ∫ x in Ioi (0:ℝ), F x = (∫ x in Ioc (0:ℝ) 1, F x) + ∫ x in Ioi (1:ℝ), F x := by
    rw [← setIntegral_union hdisj measurableSet_Ioi hFint1 hFint2,
      Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  -- the piece over `(0, 1]`
  have hb1 : (∫ x in Ioc (0:ℝ) 1, F x) ≤ K₁ := by
    have hconst : IntegrableOn (fun _ : ℝ => K₁) (Ioc (0:ℝ) 1) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have hmono : (∫ x in Ioc (0:ℝ) 1, F x) ≤ ∫ _x in Ioc (0:ℝ) 1, K₁ :=
      setIntegral_mono_on hFint1 hconst measurableSet_Ioc
        (fun x hx => integrand_le_of_mem_Ioc hC hp hker w hx)
    simpa using hmono
  -- the piece over `(1, ∞)`
  have hb2 : (∫ x in Ioi (1:ℝ), F x) ≤ K₂ * (2/p) := by
    have hexpint : IntegrableOn (fun x : ℝ => rexp (-(p/2 * x))) (Ioi 1) := by
      have := (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => rexp (-u)) 1 hp2).2
        (integrableOn_exp_neg_Ioi (p/2 * 1))
      simpa using this
    have hgint : IntegrableOn (fun x : ℝ => K₂ * rexp (-(p/2 * x))) (Ioi 1) :=
      hexpint.const_mul K₂
    have hmono : (∫ x in Ioi (1:ℝ), F x) ≤ ∫ x in Ioi (1:ℝ), K₂ * rexp (-(p/2 * x)) :=
      setIntegral_mono_on hFint2 hgint measurableSet_Ioi
        (fun x hx => integrand_le_of_mem_Ioi hC hp hker w hx)
    have hcomp : (∫ x in Ioi (1:ℝ), K₂ * rexp (-(p/2 * x))) = K₂ * ((p/2)⁻¹ * rexp (-(p/2))) := by
      rw [integral_const_mul]
      congr 1
      have h := integral_comp_mul_left_Ioi (fun u : ℝ => rexp (-u)) 1 hp2
      rw [mul_one, integral_exp_neg_Ioi, smul_eq_mul] at h
      exact h
    rw [hcomp] at hmono
    refine le_trans hmono ?_
    have hfac : (p/2)⁻¹ * rexp (-(p/2)) ≤ 2/p := by
      have h1 : rexp (-(p/2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have h2 : (0:ℝ) < (p/2)⁻¹ := by positivity
      have h3 : (p/2)⁻¹ * rexp (-(p/2)) ≤ (p/2)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h1 h2.le
      have h4 : (p/2)⁻¹ = 2/p := by field_simp
      linarith [h3, h4 ▸ h3]
    exact mul_le_mul_of_nonneg_left hfac hK2nn
  calc ‖mellin PR.f_modif w‖ ≤ ∫ x in Ioi (0:ℝ), F x := hstep1
    _ = (∫ x in Ioc (0:ℝ) 1, F x) + ∫ x in Ioi (1:ℝ), F x := hsplit
    _ ≤ K₁ + K₂ * (2/p) := add_le_add hb1 hb2

/-! ## Part E: from the Mellin bound to a bound on `Λ₀` and `ξ` -/

/-- Monotonicity bookkeeping: `a log (a/q)` is dominated by its value at the upper end,
after clipping the logarithm at `0`. -/
lemma term_le {a M q : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) (hq : 0 < q) :
    a * Real.log (a / q) ≤ M * max (Real.log (M / q)) 0 := by
  have hM : 0 ≤ M := le_trans ha haM
  have hmaxnn : 0 ≤ max (Real.log (M / q)) 0 := le_max_right _ _
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp [mul_nonneg hM hmaxnn]
  rcases le_or_gt (Real.log (a / q)) 0 with hlog | hlog
  · have : a * Real.log (a / q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hlog
    exact le_trans this (mul_nonneg hM hmaxnn)
  · have hle : Real.log (a / q) ≤ Real.log (M / q) :=
      Real.log_le_log (by positivity) (by gcongr)
    calc a * Real.log (a / q) ≤ M * Real.log (a / q) :=
          mul_le_mul_of_nonneg_right haM hlog.le
      _ ≤ M * Real.log (M / q) := mul_le_mul_of_nonneg_left hle hM
      _ ≤ M * max (Real.log (M / q)) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hM

/-- The explicit majorant, as a function of the radius. -/
noncomputable def bnd (C p r : ℝ) : ℝ :=
  C * rexp ((3/2 + r) * max (Real.log ((3/2 + r) / p)) 0)
  + C * rexp (r * max (Real.log (r / (p/2))) 0) * (2/p)

/-- `r ↦ max (log (r/q)) 0` is monotone on `[0, ∞)`, including at `r = 0`. -/
lemma maxlog_mono {q : ℝ} (hq : 0 < q) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    max (Real.log (a / q)) 0 ≤ max (Real.log (b / q)) 0 := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  · exact max_le_max_right 0 (Real.log_le_log (by positivity) (by gcongr))

/-- The majorant is monotone in the radius. -/
lemma bnd_mono {C p : ℝ} (hC : 0 < C) (hp : 0 < p) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    bnd C p a ≤ bnd C p b := by
  have hq : (0:ℝ) < p/2 := by positivity
  have h1 : (3/2 + a) * max (Real.log ((3/2 + a) / p)) 0
      ≤ (3/2 + b) * max (Real.log ((3/2 + b) / p)) 0 := by
    refine mul_le_mul (by linarith) (maxlog_mono hp (by linarith) (by linarith))
      (le_max_right _ _) (by linarith)
  have h2 : a * max (Real.log (a / (p/2))) 0 ≤ b * max (Real.log (b / (p/2))) 0 :=
    mul_le_mul hab (maxlog_mono hq ha hab) (le_max_right _ _) (le_trans ha hab)
  unfold bnd
  refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hC.le) ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) hC.le) (by positivity)

/-- The Mellin transform of the modified kernel, bounded in terms of `‖w‖` alone. -/
lemma norm_mellin_le_bnd {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x))) (w : ℂ) :
    ‖mellin PR.f_modif w‖ ≤ bnd C p ‖w‖ := by
  refine le_trans (norm_mellin_f_modif_le hC hp hker w) ?_
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hre1 : w.re ≤ ‖w‖ := le_trans (le_abs_self _) hre
  have hre2 : -‖w‖ ≤ w.re := neg_le_of_abs_le hre
  have hA : max (3/2 - w.re) 0 ≤ 3/2 + ‖w‖ := by
    apply max_le <;> [linarith; positivity]
  have hB : max (w.re - 1) 0 ≤ ‖w‖ := by
    apply max_le <;> [linarith; positivity]
  have h1 := term_le (le_max_right (3/2 - w.re) 0) hA hp
  have h2 := term_le (le_max_right (w.re - 1) 0) hB (by positivity : (0:ℝ) < p/2)
  unfold bnd
  refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hC.le) ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) hC.le) (by positivity)

/-- The completed zeta `Λ₀`, bounded on the circle of radius `r`. -/
lemma norm_completedRiemannZeta₀_le {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x))) (z : ℂ) :
    ‖completedRiemannZeta₀ z‖ ≤ bnd C p ‖z‖ := by
  rw [completedRiemannZeta₀_eq_mellin, norm_div]
  have h := norm_mellin_le_bnd hC hp hker (z / 2)
  have hnorm : ‖z / 2‖ = ‖z‖ / 2 := by simp
  rw [hnorm] at h
  have hmono : bnd C p (‖z‖ / 2) ≤ bnd C p ‖z‖ :=
    bnd_mono hC hp (by positivity) (by linarith [norm_nonneg z])
  have h2 : ‖(2:ℂ)‖ = 2 := by simp
  rw [h2]
  have : ‖mellin PR.f_modif (z/2)‖ / 2 ≤ bnd C p ‖z‖ / 2 := by
    apply div_le_div_of_nonneg_right (le_trans h hmono) (by norm_num)
  refine le_trans this ?_
  have hb : 0 ≤ bnd C p ‖z‖ := by unfold bnd; positivity
  linarith

/-! ## Part F: the bound on `ξ`, and the two order facts -/

/-- The constant collecting the `p`-dependence of the logarithms. -/
noncomputable def cst (p : ℝ) : ℝ := |Real.log p| + |Real.log (2/p)| + Real.log 3 + 1

lemma cst_pos (p : ℝ) : 0 < cst p := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold cst; positivity

/-- The majorant, collapsed into a single exponential, for radii `≥ 1`. -/
lemma bnd_le_exp {C p r : ℝ} (hC : 0 < C) (hp : 0 < p) (hr : 1 ≤ r) :
    bnd C p r ≤ (C * (1 + 2/p)) * rexp (4 * r * (Real.log r + cst p)) := by
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hc := cst_pos p
  have hsum : 0 ≤ Real.log r + cst p := by linarith
  -- the two exponents
  set X := (3/2 + r) * max (Real.log ((3/2 + r) / p)) 0 with hX
  set Y := r * max (Real.log (r / (p/2))) 0 with hY
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  -- `X ≤ 3 r (log r + c)`
  have hXle : X ≤ 3 * r * (Real.log r + cst p) := by
    have h1 : max (Real.log ((3/2 + r) / p)) 0 ≤ Real.log r + cst p := by
      apply max_le _ hsum
      have hle : (3/2 + r) / p ≤ 3 * r / p := by
        apply div_le_div_of_nonneg_right _ hp.le
        linarith
      have h2 : Real.log ((3/2 + r) / p) ≤ Real.log (3 * r / p) :=
        Real.log_le_log (by positivity) hle
      have h3 : Real.log (3 * r / p) = Real.log 3 + Real.log r - Real.log p := by
        rw [Real.log_div (by positivity) (ne_of_gt hp), Real.log_mul (by norm_num) (ne_of_gt hr0)]
      have h4 : -Real.log p ≤ |Real.log p| := neg_le_abs _
      unfold cst
      have h5 : 0 ≤ |Real.log (2/p)| := abs_nonneg _
      linarith [h2, h3.le, h3.ge]
    have h2 : (3/2 + r) ≤ 3 * r := by linarith
    rw [hX]
    calc (3/2 + r) * max (Real.log ((3/2 + r) / p)) 0
        ≤ (3 * r) * max (Real.log ((3/2 + r) / p)) 0 :=
          mul_le_mul_of_nonneg_right h2 (le_max_right _ _)
      _ ≤ (3 * r) * (Real.log r + cst p) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 3 * r * (Real.log r + cst p) := by ring
  -- `Y ≤ r (log r + c)`
  have hYle : Y ≤ r * (Real.log r + cst p) := by
    have h1 : max (Real.log (r / (p/2))) 0 ≤ Real.log r + cst p := by
      apply max_le _ hsum
      have h3 : Real.log (r / (p/2)) = Real.log r - Real.log (p/2) := by
        rw [Real.log_div (ne_of_gt hr0) (by positivity)]
      have h4 : Real.log (p/2) = -Real.log (2/p) := by
        rw [← Real.log_inv]; congr 1; field_simp
      have h5 : Real.log (2/p) ≤ |Real.log (2/p)| := le_abs_self _
      unfold cst
      have h6 : 0 ≤ |Real.log p| := abs_nonneg _
      have h7 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      linarith [h3.le, h3.ge, h4.le, h4.ge]
    rw [hY]
    exact mul_le_mul_of_nonneg_left h1 hr0.le
  -- collapse the sum of two exponentials
  have hkey : rexp X + rexp Y * (2/p) ≤ (1 + 2/p) * rexp (X + Y) := by
    have h1 : rexp X ≤ rexp (X + Y) := Real.exp_le_exp.2 (by linarith)
    have h2 : rexp Y ≤ rexp (X + Y) := Real.exp_le_exp.2 (by linarith)
    have hpp : (0:ℝ) < 2/p := by positivity
    nlinarith [Real.exp_pos (X + Y), h1, h2]
  have hXY : X + Y ≤ 4 * r * (Real.log r + cst p) := by linarith
  calc bnd C p r = C * rexp X + C * rexp Y * (2/p) := rfl
    _ = C * (rexp X + rexp Y * (2/p)) := by ring
    _ ≤ C * ((1 + 2/p) * rexp (X + Y)) := mul_le_mul_of_nonneg_left hkey hC.le
    _ ≤ C * ((1 + 2/p) * rexp (4 * r * (Real.log r + cst p))) := by
        have : rexp (X + Y) ≤ rexp (4 * r * (Real.log r + cst p)) := Real.exp_le_exp.2 hXY
        have hnn : (0:ℝ) ≤ 1 + 2/p := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hnn) hC.le
    _ = (C * (1 + 2/p)) * rexp (4 * r * (Real.log r + cst p)) := by ring

/-- **The growth bound for `ξ`.**  For every `z` with `‖z‖ ≥ 1`,
`‖ξ z‖ ≤ exp (‖z‖ * (4 log ‖z‖ + K))` for a constant `K` depending only on the kernel data. -/
lemma norm_riemannXi_le_exp {C p : ℝ} (hC : 0 < C) (hp : 0 < p)
    (hker : ∀ x : ℝ, 1 ≤ x → |evenKernel 0 x - 1| ≤ C * rexp (-(p * x)))
    {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖riemannXi z‖
      ≤ rexp (‖z‖ * (4 * Real.log ‖z‖ +
          (max (Real.log (C * (1 + 2/p) + 1)) 0 + 2 + 4 * cst p))) := by
  set r := ‖z‖ with hrdef
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hz
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hz
  have hc := cst_pos p
  set D := C * (1 + 2/p) with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  -- pointwise bound on ξ
  have hΛ : ‖completedRiemannZeta₀ z‖ ≤ bnd C p r := norm_completedRiemannZeta₀_le hC hp hker z
  have hxi : ‖riemannXi z‖ ≤ (1/2) * r * (r + 1) * bnd C p r + 1/2 := by
    have hdef : riemannXi z = (1/2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z + (1/2 : ℂ) := rfl
    rw [hdef]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖(1/2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z‖
        = (1/2) * r * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ := by
      simp [hrdef]
    have h2 : ‖z - 1‖ ≤ r + 1 := le_trans (norm_sub_le _ _) (by simp [hrdef])
    have h3 : ‖(1/2 : ℂ)‖ = 1/2 := by simp
    rw [h1, h3]
    have hbn : 0 ≤ bnd C p r := by unfold bnd; positivity
    have hstep : (1/2) * r * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖
        ≤ (1/2) * r * (r + 1) * bnd C p r := by
      apply mul_le_mul _ hΛ (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  -- collapse the majorant
  have hb := bnd_le_exp (C := C) (p := p) hC hp hz
  have hmul : (1/2) * r * (r + 1) * bnd C p r + 1/2
      ≤ (D + 1) * r ^ 2 * rexp (4 * r * (Real.log r + cst p)) := by
    have he1 : (1:ℝ) ≤ rexp (4 * r * (Real.log r + cst p)) :=
      Real.one_le_exp (by positivity)
    have hpoly : (1/2) * r * (r + 1) ≤ r ^ 2 := by nlinarith
    have hbn : 0 ≤ bnd C p r := by unfold bnd; positivity
    have h1 : (1/2) * r * (r + 1) * bnd C p r
        ≤ r ^ 2 * (D * rexp (4 * r * (Real.log r + cst p))) := by
      apply mul_le_mul hpoly hb hbn (by positivity)
    have h2 : (1:ℝ)/2 ≤ 1 * r ^ 2 * rexp (4 * r * (Real.log r + cst p)) := by
      nlinarith [sq_nonneg (r - 1), hz, Real.exp_pos (4 * r * (Real.log r + cst p))]
    nlinarith [h1, h2, Real.exp_pos (4 * r * (Real.log r + cst p))]
  -- turn the polynomial prefactor into an exponential
  have hr2 : rexp (2 * Real.log r) = r ^ 2 := by
    rw [show (2:ℝ) * Real.log r = Real.log r + Real.log r by ring, Real.exp_add,
      Real.exp_log hr0]
    ring
  have hpre : (D + 1) * r ^ 2 = rexp (Real.log (D + 1) + 2 * Real.log r) := by
    rw [Real.exp_add, Real.exp_log (by positivity), hr2]
  have hfinal : Real.log (D + 1) + 2 * Real.log r + 4 * r * (Real.log r + cst p)
      ≤ r * (4 * Real.log r + (max (Real.log (D + 1)) 0 + 2 + 4 * cst p)) := by
    have h1 : Real.log (D + 1) ≤ max (Real.log (D + 1)) 0 * r := by
      have hm : 0 ≤ max (Real.log (D + 1)) 0 := le_max_right _ _
      nlinarith [le_max_left (Real.log (D + 1)) 0]
    have h2 : 2 * Real.log r ≤ 2 * r := by
      nlinarith [Real.log_le_sub_one_of_pos hr0]
    nlinarith [hc.le]
  calc ‖riemannXi z‖ ≤ (1/2) * r * (r + 1) * bnd C p r + 1/2 := hxi
    _ ≤ (D + 1) * r ^ 2 * rexp (4 * r * (Real.log r + cst p)) := hmul
    _ = rexp (Real.log (D + 1) + 2 * Real.log r) * rexp (4 * r * (Real.log r + cst p)) := by
        rw [hpre]
    _ = rexp (Real.log (D + 1) + 2 * Real.log r + 4 * r * (Real.log r + cst p)) := by
        rw [← Real.exp_add]
    _ ≤ rexp (r * (4 * Real.log r + (max (Real.log (D + 1)) 0 + 2 + 4 * cst p))) :=
        Real.exp_le_exp.2 hfinal

/-! ## Part G: the two order facts -/

/-- The growth bound, with the kernel data packaged away. -/
lemma exists_xi_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 1 ≤ ‖z‖ →
    ‖riemannXi z‖ ≤ rexp (‖z‖ * (4 * Real.log ‖z‖ + K)) := by
  obtain ⟨C, p, hC, hp, hker⟩ := exists_kernel_bound
  refine ⟨max (Real.log (C * (1 + 2/p) + 1)) 0 + 2 + 4 * cst p, ?_, ?_⟩
  · have h1 : 0 ≤ max (Real.log (C * (1 + 2/p) + 1)) 0 := le_max_right _ _
    have h2 := (cst_pos p).le
    linarith
  · intro z hz
    exact norm_riemannXi_le_exp hC hp hker hz


end LiCriterion.XiGrowth
namespace XiZeros

lemma diff_centered : Differentiable ℂ centered :=
  xi_entire.comp (show Differentiable ℂ (fun z : ℂ => 1/2 + z) by fun_prop)

lemma subquadratic_derivative (m : ℕ) : Subquadratic (iteratedDeriv m centered) := by
  obtain ⟨K,K0,hK⟩ := LiCriterion.XiGrowth.exists_xi_bound
  have xiEq : xi = LiCriterion.riemannXi := by ext z : 1; unfold xi LiCriterion.riemannXi; ring
  intro c C
  let A := Real.log (m.factorial:ℝ) + |C| + 1
  let D := 8*Real.log 2 + 2*K
  let B := fun R : ℝ => A + R*(8*Real.log R + D)
  have f1 : 1 ≤ (m.factorial:ℝ) := by exact_mod_cast m.factorial_pos
  have hA : C < A := by dsimp [A]; linarith [le_abs_self C,Real.log_nonneg f1]
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨B, ?_, ?_⟩
  · have invR := (tendsto_inv_atTop_zero (𝕜 := ℝ))
    have hlog : Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have lim := (((invR.pow 2).const_mul (A-C)).add (hlog.const_mul 8)).add (invR.const_mul D)
    apply (show Tendsto _ atTop (𝓝 (0:ℝ)) by simpa using lim).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    dsimp [B]; field_simp; ring
  · filter_upwards [eventually_gt_atTop (‖(1/2:ℂ)+c‖+2)] with R hR
    have r1 : 1 ≤ R := by linarith [norm_nonneg ((1/2:ℂ)+c)]
    have r0 : 0 < R := by linarith
    have lR := Real.log_nonneg r1
    refine ⟨hA.trans_le (le_add_of_nonneg_right (mul_nonneg r0.le (by positivity))), ?_⟩
    intro w hw
    have wR := mem_sphere_zero_iff_norm.mp hw
    let U := R*(8*Real.log R + D)
    have bound (u : ℂ) (hu : u ∈ sphere (c+w) 1) : ‖centered u‖ ≤ Real.exp U := by
      have hδ := mem_sphere_iff_norm.mp hu
      let q : ℂ := 1/2+u
      have hqw : ‖q-w‖ ≤ ‖(1/2:ℂ)+c‖+1 := by
        rw [show q-w = ((1/2:ℂ)+c) + (u-(c+w)) by dsimp [q]; ring, ← hδ]
        apply norm_add_le
      have hab := abs_le.mp ((abs_norm_sub_norm_le q w).trans hqw)
      have q1 : 1 ≤ ‖q‖ := by linarith
      have q2 : ‖q‖ ≤ 2*R := by linarith
      change ‖xi q‖ ≤ _
      rw [xiEq]
      apply (hK q q1).trans
      apply Real.exp_le_exp.mpr
      calc ‖q‖ * (4 * Real.log ‖q‖ + K) ≤ (2*R)*(4*Real.log (2*R)+K) := by
             gcongr
             · linarith [Real.log_nonneg q1]
         _ = U := by rw [Real.log_mul (by norm_num) r0.ne']; dsimp [U,D]; ring
    have est := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m (by norm_num : (0:ℝ)<1)
      (diff_centered.differentiableOn.diffContOnCl_ball (Set.subset_univ _)) bound
    simp only [one_pow,div_one] at est
    apply est.trans
    change _ ≤ Real.exp (A + U)
    rw [Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    rw [← Real.log_le_iff_le_exp (by positivity)]
    dsimp [A]; linarith [abs_nonneg C]


lemma derivative_nonconstant (m : ℕ) : ∃ u v, iteratedDeriv m centered u ≠ iteratedDeriv m centered v := by
  by_contra! h
  have eq : iteratedDeriv m centered = fun _ => iteratedDeriv m centered 0 := funext (fun x => h x 0)
  have tail (j : ℕ) (hj : m < j) : iteratedDeriv j centered 0 = 0 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show m+1 ≤ j by omega)
    rw [show m+1+k = (k+1)+m by omega, iteratedDeriv_eq_iterate, Function.iterate_add_apply,
      ← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate, eq, iteratedDeriv_const]
    simp
  let S := Finset.range (m+1)
  let A := ∑ j ∈ S, ‖iteratedDeriv j centered 0‖
  have A0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have bound (z : ℂ) : ‖centered z‖ ≤ A * Real.exp ‖z‖ := by
    have series := Complex.taylorSeries_eq_of_entire' (c := 0) (z := z) diff_centered
    simp only [sub_zero] at series
    rw [tsum_eq_sum (s := S) (fun j hj => by
      have lt : m < j := by simpa [S] using hj
      simp [tail j lt])] at series
    rw [← series]
    refine (norm_sum_le _ _).trans ?_
    rw [show A * Real.exp ‖z‖ = ∑ j ∈ S, ‖iteratedDeriv j centered 0‖ * Real.exp ‖z‖
      by simp [A,Finset.sum_mul]]
    apply Finset.sum_le_sum
    intro j _
    simp only [norm_mul,norm_pow,norm_inv,Complex.norm_natCast]
    calc _ = ‖iteratedDeriv j centered 0‖ * (‖z‖^j / j.factorial) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg _) _) (norm_nonneg _)
  let q := Real.pi * Real.exp 2
  obtain ⟨n,hn⟩ := (FloorSemiring.eventually_mul_pow_lt_factorial_sub (A*q) q 0).exists
  simp only [Nat.sub_zero] at hn
  let k := 2*(n+1)
  have hk : 1 < k := by dsimp [k]; omega
  have h0 : (k:ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have h1 : (k:ℂ) ≠ 1 := by exact_mod_cast (show k ≠ 1 by omega)
  have low := lower_even_completed n
  change (n.factorial:ℝ)/Real.pi^(n+1) ≤ (((k:ℂ)*(k-1)*completedRiemannZeta k)/2).re at low
  rw [← xi_eq_completed h0 h1] at low
  let z : ℂ := (k:ℂ)-1/2
  have bz := bound z
  have cz : centered z = xi k := by unfold centered z; congr 1; ring
  have zn : ‖z‖ ≤ ((n+1:ℕ):ℝ)*2 := by
    have kr : (1:ℝ) < k := by exact_mod_cast hk
    have Z : z = (((k:ℝ)-1/2 : ℝ):ℂ) := by simp [z]
    rw [Z,Complex.norm_of_nonneg (by linarith)]
    simp [k]; linarith
  rw [cz] at bz
  have upper := (low.trans (Complex.re_le_norm _)).trans
    (bz.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr zn) A0))
  rw [Real.exp_nat_mul] at upper
  have lim := (div_le_iff₀ (pow_pos Real.pi_pos (n+1))).mp upper
  apply (not_lt_of_ge lim) 
  convert hn using 1
  dsimp [q]; rw [mul_pow]; ring

lemma entire_derivative (n : ℕ) : Differentiable ℂ (iteratedDeriv n centered) := by
  induction n with
  | zero => simpa using diff_centered
  | succ n hn => simpa only [iteratedDeriv_succ] using hn.deriv

lemma centered_critical (rh : RiemannHypothesis) (m : ℕ) :
    ∀ z, iteratedDeriv m centered z = 0 → z.re = 0 := by
  induction m with
  | zero =>
    intro z h
    have hz := xi_half_of_rh rh (s := 1/2+z) (by simpa [centered] using h)
    simp at hz
    linarith
  | succ n ih =>
    let F := iteratedDeriv n centered
    have hd : Differentiable ℂ F := entire_derivative n
    have parity (x : ℂ) : F (-x) = (-1:ℂ)^n * F x := by simpa [F] using centered_parity n (-x)
    have hr := strict_of_half_plane hd (derivative_nonconstant n) (fun w hw h => hw.ne' (ih w h))
      (fun w hw => sign_of_growth hd (derivative_nonconstant n) (subquadratic_derivative n) ih
        (pow_ne_zero n (by norm_num)) parity hw)
    intro z hz
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hder : iteratedDeriv (n+1) centered (-z) = 0 := by
        simpa [hz] using centered_parity (n+1) (-z)
      exact hr (-z) (by simpa using h) (by simpa only [iteratedDeriv_succ] using hder)
    · exact hr z h (by simpa only [iteratedDeriv_succ] using hz)

end XiZeros


theorem OMA.solution : type_of% @OMA.S_mo_449746.main := by
  intro rh
  exact XiZeros.centered_to_root (fun m _ => XiZeros.centered_critical rh m)

