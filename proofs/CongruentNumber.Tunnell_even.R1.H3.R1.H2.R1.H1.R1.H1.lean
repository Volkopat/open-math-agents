import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1
import Mathlib

/-! Rankin–Selberg evaluation of the level-32 theta-product moment. -/

section
/- Disk primitive and level-two Fricke transformation for the conductor-32 eta product. -/

namespace TunnellFricke

open Complex hiding eta
open Function ModularForm Set Filter Metric
open UpperHalfPlane hiding I
open scoped Real Topology

noncomputable def h (z : ℂ) := eta z ^2 * eta (2*z)^2
noncomputable def W (z : ℂ) := -1/(2*z)
noncomputable def disk (q : ℂ) := (∏' n : ℕ, (1-(q^4)^(n+1)))^2 *
  (∏' n : ℕ, (1-(q^8)^(n+1)))^2

lemma disk_hol : DifferentiableOn ℂ disk (ball 0 1) := by
  have hc (a : ℕ) (ha : 0<a) : MapsTo (fun q : ℂ => q^a) (ball 0 1) (ball 0 1) := by
    intro q hq
    simpa [mem_ball,norm_pow] using pow_lt_one₀ (norm_nonneg q) (by simpa using hq) ha.ne'
  have hf (a : ℕ) (ha : 0<a) := differentiableOn_tprod_one_sub_pow.comp
    (show DifferentiableOn ℂ (fun q : ℂ => q^a) (ball 0 1) by fun_prop) (hc a ha)
  exact ((hf 4 (by decide)).pow 2).mul ((hf 8 (by decide)).pow 2)

lemma disk_rot (q : ℂ) : disk (I*q) = disk q := by
  simp [disk,mul_pow,I_pow_four,show Complex.I^8=1 by rw [show 8=4*2 by decide,pow_mul,I_pow_four,one_pow]]

lemma present (z : ℂ) : h z = Periodic.qParam 4 z * disk (Periodic.qParam 4 z) := by
  have h1 : Periodic.qParam 1 z = Periodic.qParam 4 z ^4 := by
    simp only [Periodic.qParam,← Complex.exp_nat_mul]; push_cast; congr 1; ring
  have h2 : Periodic.qParam 1 (2*z) = Periodic.qParam 4 z ^8 := by
    simp only [Periodic.qParam,← Complex.exp_nat_mul]; push_cast; congr 1; ring
  have h0 : Periodic.qParam 24 z ^2 * Periodic.qParam 24 (2*z)^2 = Periodic.qParam 4 z := by
    simp only [Periodic.qParam,← Complex.exp_nat_mul,← Complex.exp_add]; push_cast; congr 1; ring
  simp only [h,eta,eta_q,h1,h2,mul_pow,disk]
  linear_combination (∏' k : ℕ, (1-(Periodic.qParam 4 z ^ 4)^(k+1)))^2 *
    (∏' k : ℕ, (1-(Periodic.qParam 4 z ^ 8)^(k+1)))^2 * h0

lemma sq_csqrt (z : ℂ) (hz : z ≠ 0) : sqrt z ^ 2 = z := by
  rw [sqrt_eq_exp hz,← exp_nat_mul]
  convert Complex.exp_log hz using 2 <;> ring

lemma eta_S_sq (z : ℂ) (hz : 0<z.im) : eta (-1/z)^2 = (-I)*z*eta z^2 := by
  have e : eta (-1/z) = (sqrt I)⁻¹*(sqrt z * eta z) := eta_comp_eq_csqrt_I_inv hz
  rw [e,mul_pow,mul_pow,inv_pow,sq_csqrt I I_ne_zero,sq_csqrt z (ne_zero (⟨z,hz⟩:ℍ)),inv_I]
  ring

lemma h_fricke (z : ℂ) (hz : 0<z.im) : h (W z) = -2*z^2*h z := by
  have hz' : 0<(2*z).im := by simpa [mul_im] using hz
  have hz0 := ne_zero (⟨z,hz⟩:ℍ)
  simp only [h,W,eta_S_sq _ hz',show 2*(-1/(2*z)) = -1/z by field_simp,eta_S_sq _ hz]
  linear_combination 2*z^2*eta z^2*eta (2*z)^2*I_sq

lemma W_mem {z : ℂ} (hz : 0<z.im) : 0<(W z).im := by
  have h2 : 0<(2*z).im := by simpa [mul_im] using hz
  simpa [W,neg_div] using (⟨2*z,h2⟩:ℍ).im_inv_neg_coe_pos

noncomputable def c : ℂ := 2*(Real.pi:ℂ)*I/4

lemma hasDeriv_q (z : ℂ) : HasDerivAt (Periodic.qParam 4) (c*Periodic.qParam 4 z) z := by
  have e : Periodic.qParam 4 = fun z => exp (c*z) := by
    ext z
    simp only [Periodic.qParam,c]
    push_cast
    congr 1
    ring
  rw [e]
  simpa [mul_comm] using ((hasDerivAt_id z).const_mul c).cexp

lemma q_T (z : ℂ) : Periodic.qParam 4 (z+1) = I*Periodic.qParam 4 z := by
  simp only [Periodic.qParam]
  push_cast
  rw [show 2*(Real.pi:ℂ)*I*(z+1)/4 = Real.pi/2*I + 2*Real.pi*I*z/4 by ring,
    exp_add,exp_pi_div_two_mul_I]

theorem primitive :
    ∃ J : ℂ → ℂ, (∀ z, 0<z.im → HasDerivAt J (c*h z) z) ∧
      Tendsto J (comap Complex.im atTop) (𝓝 0) ∧
      (∀ z, 0<z.im → J (z+1) = I*J z) ∧
      ∃ C : ℂ, ∀ z, 0<z.im → J (W z) = C-J z := by
  obtain ⟨G,hG0,hG⟩ := disk_hol.isExactOn_ball.with_val_at 0 0
  let J (z : ℂ) := G (Periodic.qParam 4 z)
  have qmem {z : ℂ} (hz : 0<z.im) : Periodic.qParam 4 z ∈ ball 0 1 := by
    simpa using Periodic.norm_qParam_lt_one (by norm_num : (0:ℝ)<4) hz
  have hJ (z : ℂ) (hz : 0<z.im) : HasDerivAt J (c*h z) z := by
    rw [show c*h z = disk (Periodic.qParam 4 z)*(c*Periodic.qParam 4 z) by rw [present]; ring]
    exact (hG _ (qmem hz)).comp z (hasDeriv_q z)
  have h0 : Tendsto J (comap Complex.im atTop) (𝓝 0) := by
    have hh := (hG 0 (mem_ball_self (by norm_num))).continuousAt.tendsto
    rw [hG0] at hh
    exact hh.comp ((Periodic.qParam_tendsto (by norm_num : (0:ℝ)<4)).mono_right nhdsWithin_le_nhds)
  have hA {q : ℂ} (hq : q ∈ ball 0 1) : I*q ∈ ball 0 1 := by simpa [mem_ball] using hq
  have da {q : ℂ} (hq : q ∈ ball 0 1) : HasDerivAt (fun w => G (I*w)) (I*disk q) q := by
    simpa only [Function.comp_def,id_eq, mul_one,disk_rot, mul_comm (disk q) I] using (hG _ (hA hq)).comp q ((hasDerivAt_id q).const_mul I)
  have db {q : ℂ} (hq : q ∈ ball 0 1) : HasDerivAt (fun w => I*G w) (I*disk q) q := (hG _ hq).const_mul I
  have rot : (ball 0 1).EqOn (fun w => G (I*w)) (fun w => I*G w) := by
    refine isOpen_ball.eqOn_of_deriv_eq (convex_ball (0:ℂ) 1).isPreconnected
      (fun q hq => (da hq).differentiableAt.differentiableWithinAt)
      (fun q hq => (db hq).differentiableAt.differentiableWithinAt)
      (fun q hq => (da hq).deriv.trans (db hq).deriv.symm) (x:=0) (by simp) ?_
    simp [hG0]
  refine ⟨J,hJ,h0,fun z hz => ?_,?_⟩
  · simpa [J,q_T] using rot (qmem hz)
  · have dW (z : ℂ) (hz : 0<z.im) : HasDerivAt W (1/(2*z^2)) z := by
      have hz0 := ne_zero (⟨z,hz⟩:ℍ)
      have hh := (hasDerivAt_const z (-1:ℂ)).div ((hasDerivAt_id z).const_mul 2) (mul_ne_zero two_ne_zero hz0)
      change HasDerivAt W ((0*(2*z)-(-1)*(2*1))/(2*z)^2) z at hh
      rwa [show (0*(2*z)-(-1)*(2*1))/(2*z)^2 = 1/(2*z^2) by field_simp; ring] at hh
    have da (z : ℂ) (hz : 0<z.im) : HasDerivAt (fun w => J (W w)) (-(c*h z)) z := by
      have hz0 := ne_zero (⟨z,hz⟩:ℍ)
      rw [show -(c*h z) = c*h (W z)*(1/(2*z^2)) by rw [h_fricke z hz]; field_simp]
      exact (hJ (W z) (W_mem hz)).comp z (dW z hz)
    have db (z : ℂ) (hz : 0<z.im) := (hJ z hz).neg
    obtain ⟨C,hC⟩ := isOpen_upperHalfPlaneSet.exists_eq_add_of_deriv_eq
      (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => (da z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (db z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (da z hz).deriv.trans (db z hz).deriv.symm)
    exact ⟨C,fun z hz => by simpa [sub_eq_add_neg,add_comm] using hC hz⟩

end TunnellFricke
end

section
/-
# The base cusp form for the congruent-number curves

The twelfth power of the eta product is a product of two rational dilates of
the modular discriminant. Its multiplier therefore has finite image, and on
the kernel the eta product is a weight-two cusp form. Its period is one.
Uniform convergence of the truncated products on compact subsets of the disk
identifies the Fourier coefficients with the prescribed integer coefficients.
-/

namespace TunnellRoot

open Complex UpperHalfPlane Matrix MatrixGroups ModularForm
open scoped Manifold Topology

lemma pow_slash (f : ℍ → ℂ) (g : SL(2, ℤ)) (k n : ℕ) :
    (f ^ n) ∣[((n*k : ℕ) : ℤ)] g = (f ∣[(k:ℤ)] g) ^ n := by
  induction n with
  | zero =>
    ext z
    simp [SL_slash_apply]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul, Nat.cast_add, mul_slash_SL2, ih, pow_succ]

lemma zero_of_twelfth_power {f : ℍ → ℂ} (h : IsZeroAtImInfty (f ^ 12)) : IsZeroAtImInfty f := by
  rw [isZeroAtImInfty_iff] at h ⊢
  intro ε hε
  obtain ⟨b,hb⟩ := h (ε^12) (by positivity)
  refine ⟨b, fun z hz => ?_⟩
  have ht := hb z hz
  simp only [Pi.pow_apply, norm_pow] at ht
  exact le_of_pow_le_pow_left₀ (by decide : 12 ≠ 0) hε.le ht

lemma constant_of_twelfth_power (q : ℍ → ℂ) (hq : Continuous q) (hp : ∀ z, q z ^ 12 = 1)
    (x y : ℍ) : q x = q y := by
  let Z := Polynomial.nthRootsFinset 12 (1:ℂ)
  apply isPreconnected_univ.constant_of_mapsTo (T := (Z : Set ℂ)) Z.finite_toSet.isDiscrete
    hq.continuousOn _ (Set.mem_univ x) (Set.mem_univ y)
  exact fun z _ => (Polynomial.mem_nthRootsFinset (by decide : 0 < 12) 1).mpr (hp z)

theorem exists_cusp_root {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (f : ℍ → ℂ) (hhol : MDiff f) (hf : ∀ z, f z ≠ 0)
    (hperiod : f ∣[(2 : ℤ)] ModularGroup.T = f)
    (F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 24) (hpow : ⇑F = f ^ 12) :
    ∃ H : Subgroup SL(2, ℤ), H.FiniteIndex ∧ ModularGroup.T ∈ H ∧
      ∃ G : CuspForm (H : Subgroup (GL (Fin 2) ℝ)) 2, ⇑G = f := by
  classical
  let base : ℍ := UpperHalfPlane.I
  let ratio (g : Γ) (z : ℍ) := (f ∣[(2 : ℤ)] (g.val)) z / f z
  have hpowg (g : Γ) : (f ∣[(2 : ℤ)] (g.val)) ^ 12 = f^12 := by
    have hh : (f^12) ∣[(24:ℤ)] g.val = (f∣[(2:ℤ)]g.val)^12 := pow_slash f g.val 2 12
    rw [← hh, ← hpow]
    exact F.slash_action_eq' _ ⟨g.val,g.property,rfl⟩
  have hrpow (g : Γ) (z : ℍ) : ratio g z ^ 12 = 1 := by
    have ht := congrFun (hpowg g) z
    change ((f ∣[(2 : ℤ)] (g.val)) z)^12 = f z ^12 at ht
    dsimp only [ratio]
    rw [div_pow, ht, div_self (pow_ne_zero _ (hf z))]
  have hrc (g : Γ) (z : ℍ) : ratio g z = ratio g base := by
    apply constant_of_twelfth_power _ _ (hrpow g)
    exact (hhol.slash 2 (g.val : GL (Fin 2) ℝ)).continuous.div hhol.continuous hf
  have hslash (g : Γ) : f ∣[(2 : ℤ)] g.val = ratio g base • f := by
    funext z
    exact (div_eq_iff (hf z)).mp (hrc g z)
  let χ : Γ →* ℂ := {
    toFun := fun g => ratio g base
    map_one' := by simp [ratio, hf]
    map_mul' := by
      intro g h
      have heq : (f ∣[(2 : ℤ)] ((g*h).val)) = (ratio g base * ratio h base) • f := by
        rw [Subgroup.coe_mul, SlashAction.slash_mul, hslash g, SL_slash,
          smul_slash, ← SL_slash, hslash h]
        simp [σ, smul_smul]
      exact (div_eq_iff (hf base)).mpr (congrFun heq base) }
  let χ' : Γ →* rootsOfUnity 12 ℂ := χ.toHomUnits.codRestrict _ (fun g => by
    change χ.toHomUnits g ^ 12 = 1
    ext
    exact hrpow g base)
  let H := χ'.ker.map Γ.subtype
  have hH : H.FiniteIndex := by
    constructor
    rw [Subgroup.index_map_subtype]
    exact Nat.mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := χ'.ker)) (Subgroup.FiniteIndex.index_ne_zero (H := Γ))
  have hker (g : Γ) : g ∈ χ'.ker ↔ ratio g base = 1 := by
    change χ' g = 1 ↔ _
    simp only [Subtype.ext_iff, Units.ext_iff]
    rfl
  have hsH (γ : SL(2, ℤ)) (hγ : γ ∈ H) : f ∣[(2 : ℤ)] γ = f := by
    obtain ⟨g,hg,rfl⟩ := hγ
    change f ∣[(2:ℤ)] g.val = f
    rw [hslash g, hker g |>.mp hg, one_smul]
  have hT' : ModularGroup.T ∈ H := by
    refine ⟨⟨_,hT⟩, (hker _).mpr ?_, rfl⟩
    simp [ratio, hperiod, hf]
  refine ⟨H,hH,hT', { toFun := f, slash_action_eq' := ?_, holo' := hhol, zero_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨γ,hγ,rfl⟩
    exact hsH γ hγ
  · intro c hc
    have hsub : (H : Subgroup (GL (Fin 2) ℝ)) ≤ (Γ : Subgroup (GL (Fin 2) ℝ)) := by
      apply Subgroup.map_mono
      rintro γ ⟨g,-,rfl⟩
      exact g.property
    have hcSL : IsCusp c 𝒮ℒ := hc.mono (Subgroup.map_le_range _ _)
    apply (OnePoint.isZeroAt_iff_forall_SL2Z hcSL).mpr
    intro γ hγ
    apply zero_of_twelfth_power
    have hh : (f^12) ∣[(24:ℤ)] γ = (f∣[(2:ℤ)]γ)^12 := pow_slash f γ 2 12
    rw [← hh, ← hpow]
    exact ((OnePoint.isZeroAt_iff_forall_SL2Z hcSL).mp (F.zero_at_cusps' (hc.mono hsub))) γ hγ

end TunnellRoot

namespace TunnellRoot

open Complex UpperHalfPlane Matrix MatrixGroups ModularForm
open Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup ConjAct Pointwise
open scoped Manifold

noncomputable def dilation (d : ℕ) (hd : 0 < d) : GL (Fin 2) ℚ :=
  mkOfDetNeZero !![(d:ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two, hd.ne'])

noncomputable def dilR (d : ℕ) (hd : 0 < d) : GL (Fin 2) ℝ :=
  (dilation d hd).map (Rat.castHom ℝ)

lemma val_dilR (d : ℕ) (hd : 0 < d) : ((dilR d hd : GL (Fin 2) ℝ) : Matrix _ _ _) =
    !![(d:ℝ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dilR, dilation, mkOfDetNeZero]

lemma det_dilR (d : ℕ) (hd : 0 < d) : (dilR d hd).det.val = d := by
  rw [val_det_apply, val_dilR, Matrix.det_fin_two]
  simp

lemma delta_dilate_slash (d : ℕ) (hd : 0 < d) (τ : ℍ) :
    CuspForm.translate CuspForm.discriminant (dilR d hd) τ =
    ModularForm.eta ((d:ℂ) * (τ : ℂ)) ^ 24 * (d : ℂ)^11 := by
  let g := dilR d hd
  have hdet : g.det.val = (d : ℝ) := det_dilR d hd
  have hpos : 0 < g.det.val := hdet ▸ (by exact_mod_cast hd)
  have hz : ↑(g • τ) = (d : ℂ) * (τ : ℂ) := by
    simp [UpperHalfPlane.coe_smul_of_det_pos hpos, num, denom, g,
      val_dilR]
  change (⇑CuspForm.discriminant ∣[(12:ℤ)] g) τ = _
  simp only [slash_apply, σ, hdet,
    CuspForm.coe_discriminant, ModularForm.discriminant, hz]
  simp [denom, g, val_dilR]
  norm_num [hd]

noncomputable def dilConj (d : ℕ) (hd : 0 < d) : Subgroup (GL (Fin 2) ℝ) :=
  toConjAct (dilR d hd)⁻¹ • 𝒮ℒ

lemma arith_dilConj (d : ℕ) (hd : 0 < d) : (dilConj d hd).IsArithmetic := by
  simpa only [map_inv, dilConj, dilR] using Subgroup.IsArithmetic.conj 𝒮ℒ (dilation d hd)⁻¹

lemma T_mem_dilConj (d : ℕ) (hd : 0 < d) : mapGL ℝ ModularGroup.T ∈ dilConj d hd := by
  change _ ∈ toConjAct (dilR d hd)⁻¹ • 𝒮ℒ
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  refine ⟨ModularGroup.T ^ (d:ℤ), ?_⟩
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Units.ext
  change (mapGL ℝ (ModularGroup.T ^ (d:ℤ))).val * (dilR d hd).val = (dilR d hd).val * (mapGL ℝ ModularGroup.T).val
  simp only [val_dilR, mapGL_coe_matrix, map_apply_coe, ModularGroup.coe_T_zpow, ModularGroup.coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private def restrictCusp {H Γ : Subgroup (GL (Fin 2) ℝ)} (h : H ≤ Γ) {k : ℤ}
    (F : CuspForm Γ k) : CuspForm H k where
  toFun := F
  slash_action_eq' g hg := F.slash_action_eq' g (h hg)
  holo' := F.holo'
  zero_at_cusps' hc := F.zero_at_cusps' (hc.mono h)

theorem exists_eta_base_cusp (f : ℍ → ℂ) (hhol : MDiff f) (hf : ∀ z, f z ≠ 0)
    (hperiod : f ∣[(2:ℤ)] ModularGroup.T = f)
    (hpow : ∀ z : ℍ, f z ^ 12 =
      ModularForm.eta (4 * (z : ℂ))^24 * ModularForm.eta (8 * (z : ℂ))^24) :
    ∃ H : Subgroup (GL (Fin 2) ℝ), H.IsArithmetic ∧ H.strictWidthInfty = 1 ∧
      ∃ G : CuspForm H 2, ⇑G = f := by
  let A := dilConj 4 (by decide)
  let B := dilConj 8 (by decide)
  have : A.IsArithmetic := arith_dilConj _ _
  have : B.IsArithmetic := arith_dilConj _ _
  let Γ := (A ⊓ B).comap (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
  have : Γ.FiniteIndex := Subgroup.IsArithmetic.finiteIndex_comap _
  have hT : ModularGroup.T ∈ Γ := ⟨T_mem_dilConj _ _, T_mem_dilConj _ _⟩
  have hsub : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ A ⊓ B := Subgroup.map_comap_le _ _
  let Fa := restrictCusp (hsub.trans inf_le_left)
    (CuspForm.translate CuspForm.discriminant (dilR 4 (by decide)))
  let Fb := restrictCusp (hsub.trans inf_le_right)
    (CuspForm.translate CuspForm.discriminant (dilR 8 (by decide)))
  let F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 24 :=
    (((4:ℝ)^11 * 8^11)⁻¹) • Fa.mulModularForm (CuspForm.toModularFormₗ Fb)
  have hF : ⇑F = f^12 := by
    funext τ
    change (((4:ℝ)^11 * 8^11)⁻¹) •
      (CuspForm.translate CuspForm.discriminant (dilR 4 (by decide)) τ *
       CuspForm.translate CuspForm.discriminant (dilR 8 (by decide)) τ) = f τ ^ 12
    rw [delta_dilate_slash, delta_dilate_slash, hpow]
    norm_num [Complex.real_smul]
    ring
  obtain ⟨H,hH,hHT,G,hG⟩ := exists_cusp_root hT f hhol hf hperiod F hF
  let : H.FiniteIndex := hH
  exact ⟨H, inferInstance, Subgroup.strictWidthInfty_eq_one_of_T_mem hHT, G, hG⟩

end TunnellRoot

namespace TunnellEtaUniform

open Filter Finset Polynomial
open scoped Topology

lemma eval_base_partial (D : ℕ) (q : ℂ) :
    (X * ∏ k ∈ Icc 1 D, ((1 - (X : ℂ[X])^(4*k))^2 * (1-X^(8*k))^2)).eval q =
      q * (∏ k ∈ range D, (1-(q^4)^(k+1)))^2 * (∏ k ∈ range D, (1-(q^8)^(k+1)))^2 := by
  simp only [eval_mul, eval_X, eval_prod, eval_pow, eval_sub, eval_one]
  induction D with
  | zero => simp
  | succ d ih =>
    rw [prod_Icc_succ_top (by omega : 1 ≤ d+1), prod_range_succ, prod_range_succ,
      ← mul_assoc, ih]
    simp only [← pow_mul]
    ring

theorem base_locallyUniform :
    TendstoLocallyUniformlyOn
      (fun (D : ℕ) (q : ℂ) =>
        (X * ∏ k ∈ Icc 1 D, ((1 - (X : ℂ[X])^(4*k))^2 * (1-X^(8*k))^2)).eval q)
      (fun q => q * (∏' k : ℕ, (1 - (q^4)^(k+1)))^2 * (∏' k : ℕ, (1 - (q^8)^(k+1)))^2)
      atTop (Metric.ball 0 1) := by
  let U := Metric.ball (0 : ℂ) 1
  let E (a : ℕ) (q : ℂ) : ℂ := ∏' k : ℕ, (1 - (q^a)^(k+1))
  let P (a D : ℕ) (q : ℂ) : ℂ := ∏ k ∈ range D, (1 - (q^a)^(k+1))
  have maps (a : ℕ) (ha : 0 < a) : Set.MapsTo (fun q : ℂ => q^a) U U := by
    intro q hq
    simp only [U, Metric.mem_ball, dist_zero_right, norm_pow] at hq ⊢
    exact pow_lt_one₀ (norm_nonneg _) hq ha.ne'
  have h (a : ℕ) (ha : 0 < a) : TendstoLocallyUniformlyOn (P a) (E a) atTop U := by
    dsimp only [P, E]
    exact (ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.comp _ (maps a ha)
      (by fun_prop)).hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  have hc (a : ℕ) (ha : 0 < a) : ContinuousOn (E a) U := by
    dsimp only [E]
    exact ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn.comp (by fun_prop) (maps a ha)
  have hi : TendstoLocallyUniformlyOn (fun (_ : ℕ) (q : ℂ) => q) id atTop U := by
    intro u hu x _
    exact ⟨Set.univ, univ_mem, .of_forall fun _ y _ => refl_mem_uniformity hu⟩
  have hs (a : ℕ) (ha : 0 < a) := (h a ha).mul₀ (h a ha) (hc a ha) (hc a ha)
  have hu := (hi.mul₀ (hs 4 (by decide)) continuousOn_id ((hc 4 (by decide)).mul (hc 4 (by decide)))).mul₀
    (hs 8 (by decide)) (continuousOn_id.mul ((hc 4 (by decide)).mul (hc 4 (by decide))))
    ((hc 8 (by decide)).mul (hc 8 (by decide)))
  simp_rw [eval_base_partial]
  simp only [pow_two]
  exact hu

end TunnellEtaUniform

namespace TunnellTaylor

open Filter Polynomial Finset
open scoped Topology

lemma deriv_eval (p : ℂ[X]) :
    deriv (fun z => p.eval z) = fun z => p.derivative.eval z :=
  funext fun z => (p.hasDerivAt z).deriv

lemma taylor_of_convergent_polynomials (P : ℕ → ℂ[X]) (f : ℂ → ℂ)
    (h : TendstoLocallyUniformlyOn (fun D z => (P D).eval z) f atTop (Metric.ball 0 1))
    (m : ℕ) (b : ℂ) (hst : ∀ D ≥ m, (P D).coeff m = b) :
    (m.factorial : ℂ)⁻¹ * iteratedDeriv m f 0 = b := by
  have iter (j : ℕ) : TendstoLocallyUniformlyOn
      (fun D z => (derivative^[j] (P D)).eval z) (iteratedDeriv j f)
      atTop (Metric.ball 0 1) := by
    induction j with
    | zero => simpa using h
    | succ j ih =>
      have h' := ih.deriv (Eventually.of_forall fun D => (derivative^[j] (P D)).differentiableOn)
        Metric.isOpen_ball
      simpa only [iteratedDeriv_succ, Function.comp_def, deriv_eval, Function.iterate_succ_apply'] using h'
  have ht := (iter m).tendsto_at (show (0 : ℂ) ∈ Metric.ball 0 1 by simp)
  have hconst : ∀ᶠ D in atTop, (derivative^[m] (P D)).eval 0 = (m.factorial : ℂ) * b := by
    filter_upwards [eventually_ge_atTop m] with D hD
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp [hst D hD, mul_comm, Nat.descFactorial_self]
  have hev : iteratedDeriv m f 0 = (m.factorial : ℂ) * b :=
    tendsto_nhds_unique ht (tendsto_nhds_of_eventually_eq hconst)
  rw [hev]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m), one_mul]

lemma coeff_mul_one_sub_pow {R : Type*} [CommRing R] (p : R[X]) {m k : ℕ} (hk : m < k) :
    (p * (1 - X ^ k)).coeff m = p.coeff m := by
  simp only [mul_sub, mul_one, coeff_sub, coeff_mul_X_pow', if_neg (by omega : ¬k ≤ m), sub_zero]

lemma base_stable {R : Type*} [CommRing R] (m D : ℕ) (hD : m ≤ D) :
    (X * ∏ k ∈ Icc 1 D, ((1 - (X : R[X])^(4*k))^2 * (1-X^(8*k))^2)).coeff m =
    (X * ∏ k ∈ Icc 1 m, ((1 - (X : R[X])^(4*k))^2 * (1-X^(8*k))^2)).coeff m := by
  induction D, hD using Nat.le_induction with
  | base => rfl
  | succ D hD ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ D+1)]
    simp only [pow_two, ← mul_assoc]
    rw [coeff_mul_one_sub_pow _ (by omega : m < 8*(D+1)),
      coeff_mul_one_sub_pow _ (by omega : m < 8*(D+1)),
      coeff_mul_one_sub_pow _ (by omega : m < 4*(D+1)),
      coeff_mul_one_sub_pow _ (by omega : m < 4*(D+1))]
    simpa only [pow_two, ← mul_assoc] using ih

lemma base_taylor (f : ℂ → ℂ)
    (h : TendstoLocallyUniformlyOn
      (fun (D : ℕ) (z : ℂ) => z * ∏ k ∈ Icc 1 D, ((1-z^(4*k))^2 * (1-z^(8*k))^2))
      f atTop (Metric.ball 0 1)) (m : ℕ) :
    (m.factorial : ℂ)⁻¹ * iteratedDeriv m f 0 =
      (((X * ∏ k ∈ Icc 1 m, ((1-(X : ℤ[X])^(4*k))^2 * (1-X^(8*k))^2)).coeff m : ℤ) : ℂ) := by
  let P (D : ℕ) : ℤ[X] := X * ∏ k ∈ Icc 1 D, ((1-X^(4*k))^2 * (1-X^(8*k))^2)
  apply taylor_of_convergent_polynomials (fun D => (P D).map (Int.castRingHom ℂ))
  · simpa only [P, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_mul,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_one,
      Polynomial.eval_X] using h
  · intro D hD
    rw [Polynomial.coeff_map]
    exact congrArg (fun z : ℤ => (z : ℂ)) (base_stable (R := ℤ) m D hD)

end TunnellTaylor

namespace TunnellEtaValue
open UpperHalfPlane Function MatrixGroups ModularForm
open scoped Manifold Real Topology

noncomputable def etaValue (z : ℍ) : ℂ :=
  eta (4*(z:ℂ))^2 * eta (8*(z:ℂ))^2

noncomputable def diskValue (q : ℂ) : ℂ :=
  q * (∏' k : ℕ, (1-(q^4)^(k+1)))^2 * (∏' k : ℕ, (1-(q^8)^(k+1)))^2

lemma etaValue_hol : MDiff etaValue := by
  have h (a : ℕ) (ha : 0 < a) : MDiff (fun z : ℍ => eta ((a:ℂ)*z)) := by
    intro z
    have hz : (a:ℂ)*(z:ℂ) ∈ upperHalfPlaneSet := by
      change 0 < ((a:ℂ)*(z:ℂ)).im
      simpa [Complex.mul_im] using mul_pos (Nat.cast_pos.mpr ha : 0 < (a : ℝ)) z.im_pos
    exact (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).mdifferentiableAt.comp z
      (mdifferentiableAt_const.mul (UpperHalfPlane.mdifferentiable_coe z))
  exact ((h 4 (by decide)).pow 2).mul ((h 8 (by decide)).pow 2)

lemma etaValue_ne (z : ℍ) : etaValue z ≠ 0 := by
  have h (a : ℕ) (ha : 0 < a) : eta ((a:ℂ)*z) ≠ 0 := by
    apply eta_ne_zero
    change 0 < ((a:ℂ)*(z:ℂ)).im
    simpa [Complex.mul_im] using mul_pos (Nat.cast_pos.mpr ha : 0 < (a:ℝ)) z.im_pos
  exact mul_ne_zero (pow_ne_zero 2 (h 4 (by decide))) (pow_ne_zero 2 (h 8 (by decide)))

lemma etaValue_pow (z : ℍ) :
    etaValue z ^ 12 = eta (4*(z:ℂ)) ^ 24 * eta (8*(z:ℂ)) ^ 24 := by
  simp only [etaValue, mul_pow, ← pow_mul]

lemma qparam_dilate (a : ℕ) (z : ℂ) :
    Periodic.qParam 1 ((a:ℂ)*z) = (Periodic.qParam 1 z)^a := by
  simp only [Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
  congr 1
  ring

lemma etaValue_eq (z : ℍ) : etaValue z = diskValue (Periodic.qParam 1 z) := by
  have hlead : Periodic.qParam 24 (4*(z:ℂ))^2 * Periodic.qParam 24 (8*(z:ℂ))^2 =
      Periodic.qParam 1 z := by
    simp only [Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
    push_cast
    congr 1
    ring
  unfold etaValue diskValue eta eta_q
  rw [show (4:ℂ) = (4:ℕ) by norm_num, qparam_dilate,
    show (8:ℂ) = (8:ℕ) by norm_num, qparam_dilate]
  rw [mul_pow, mul_pow]
  linear_combination (∏' k : ℕ, (1-(Periodic.qParam 1 z ^ 4)^(k+1)))^2 *
    (∏' k : ℕ, (1-(Periodic.qParam 1 z ^ 8)^(k+1)))^2 * hlead

lemma etaValue_period : etaValue ∣[(2:ℤ)] ModularGroup.T = etaValue := by
  funext z
  have hd : denom (ModularGroup.T : GL (Fin 2) ℝ) z = 1 := by
    simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_T]
  rw [SL_slash_apply, hd, one_zpow, mul_one, modular_T_smul]
  simp only [etaValue_eq]
  have h : Periodic.qParam 1 (1+(z:ℂ)) = Periodic.qParam 1 z := by
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one, Complex.exp_add]
    rw [show 2*(Real.pi:ℂ)*Complex.I = (2*Real.pi:ℝ)*Complex.I by push_cast; rfl]
    simp
  change diskValue (Periodic.qParam 1 (1+(z:ℂ))) = _
  rw [h]

lemma cusp_disk_near_zero {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (hwidth : Γ.strictWidthInfty = 1) (G : CuspForm Γ 2) (hg : ⇑G = etaValue) :
    UpperHalfPlane.cuspFunction 1 G =ᶠ[𝓝 0] diskValue := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : 0 < (1:ℝ))] with q hq
  by_cases h0 : q=0
  · subst q
    rw [CuspFormClass.cuspFunction_apply_zero G one_pos (hwidth ▸ Γ.strictWidthInfty_mem_strictPeriods)]
    simp [diskValue]
  have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos (by simpa using hq : ‖q‖ < 1) h0
  let z : ℍ := ⟨Periodic.invQParam 1 q, him⟩
  have hqz : Periodic.qParam 1 (z:ℂ) = q := Periodic.qParam_right_inv one_ne_zero h0
  rw [← hqz, SlashInvariantFormClass.eq_cuspFunction G z
    (hwidth ▸ Γ.strictWidthInfty_mem_strictPeriods) one_ne_zero, hg, etaValue_eq]

end TunnellEtaValue

open UpperHalfPlane MatrixGroups
open TunnellEtaValue

theorem TunnellEtaValue.actual_form :
    ∃ (H : Subgroup (GL (Fin 2) ℝ)) (hH : H.IsArithmetic) (_ : H.strictWidthInfty = 1)
      (F : CuspForm H 2), (∀ z : ℍ, F z = TunnellFricke.h (4*(z:ℂ))) ∧
      ∀ m : ℕ, (qExpansion 1 F).coeff m = (((Polynomial.X *
        ∏ i ∈ Finset.Icc 1 m, ((1-(Polynomial.X:Polynomial ℤ)^(4*i))^2*(1-Polynomial.X^(8*i))^2)).coeff m:ℤ):ℂ) := by
  obtain ⟨H, hH, hw, G, hg⟩ := TunnellRoot.exists_eta_base_cusp etaValue
    etaValue_hol etaValue_ne etaValue_period etaValue_pow
  let _ := hH
  refine ⟨H, hH, hw, G, ?_, ?_⟩
  · intro z
    rw [hg]
    simp only [etaValue,TunnellFricke.h,show 2*(4*(z:ℂ)) = 8*z by ring]
  intro m
  rw [qExpansion_coeff, (cusp_disk_near_zero hw G hg).iteratedDeriv_eq]
  apply TunnellTaylor.base_taylor
  unfold diskValue
  convert TunnellEtaUniform.base_locallyUniform using 1
  funext D z
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_X]
end

section
/-
# The base curve and its eta product

The coefficients of η(4z)²η(8z)² are sums of primary Gaussian integers of
fixed norm. Finite Gaussian binomial identities prove the theta expansion,
including Jacobi's cubic identity by differentiation. Coprime factorization
and prime-power recurrences on the Gaussian integers give the Hecke relations.
For split primes the quartic Jacobi sum has norm p, and the rational subgroup
of order eight determines the primary generator giving the Frobenius trace.
-/

/- Primary generators in the Gaussian coefficient formula for η(4τ)²η(8τ)². -/

namespace TunnellGaussian

open GaussianInt

def Primary (z : GaussianInt) : Prop := (⟨2,2⟩ : GaussianInt) ∣ z-1

lemma primary_iff (z : GaussianInt) :
    Primary z ↔ z.im % 2 = 0 ∧ (z.re + z.im) % 4 = 1 := by
  constructor
  · rintro ⟨⟨u,v⟩,h⟩
    have ha := congrArg Zsqrtd.re h
    have hb := congrArg Zsqrtd.im h
    change z.re - 1 = 2*u + -1*2*v at ha
    change z.im - 0 = 2*v + 2*u at hb
    omega
  · rintro ⟨h₁,h₂⟩
    refine ⟨⟨(z.re + z.im - 1)/4, (z.im - z.re + 1)/4⟩, ?_⟩
    ext
    · change z.re - 1 = 2*((z.re + z.im - 1)/4) + -1*2*((z.im - z.re + 1)/4)
      omega
    · change z.im - 0 = 2*((z.im - z.re + 1)/4) + 2*((z.re + z.im - 1)/4)
      omega

lemma primary_mul_iff {z w : GaussianInt} (hz : Primary z) : Primary (z*w) ↔ Primary w := by
  have h : (⟨2,2⟩ : GaussianInt) ∣ (z-1)*w := dvd_mul_of_dvd_left hz _
  unfold Primary
  rw [show z*w - 1 = (z-1)*w + (w-1) by ring, dvd_add_right h]

lemma primary_star {z : GaussianInt} (hz : Primary z) : Primary (star z) := by
  rw [primary_iff] at hz ⊢
  change (-z.im) % 2 = 0 ∧ (z.re - z.im) % 4 = 1
  omega

lemma norm_sq (z : GaussianInt) : z.norm = z.re^2 + z.im^2 := by rw [Zsqrtd.norm_def]; ring

lemma units_cases {u : GaussianInt} (hu : IsUnit u) :
    (u.re = 1 ∧ u.im = 0) ∨ (u.re = -1 ∧ u.im = 0) ∨
    (u.re = 0 ∧ u.im = 1) ∨ (u.re = 0 ∧ u.im = -1) := by
  have h := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) u).mpr hu
  rw [norm_sq] at h
  have hr : -1 ≤ u.re ∧ u.re ≤ 1 := by constructor <;> nlinarith [sq_nonneg (u.re+1), sq_nonneg (u.re-1), sq_nonneg u.im]
  have hi : -1 ≤ u.im ∧ u.im ≤ 1 := by constructor <;> nlinarith [sq_nonneg (u.im+1), sq_nonneg (u.im-1), sq_nonneg u.re]
  obtain ⟨hr₁, hr₂⟩ := hr
  obtain ⟨hi₁, hi₂⟩ := hi
  interval_cases h₁ : u.re <;> interval_cases h₂ : u.im <;> simp_all

lemma primary_unit_eq_one {u : GaussianInt} (h : Primary u) (hu : IsUnit u) : u = 1 := by
  have h' := (primary_iff _).mp h
  rcases units_cases hu with h | h | h | h <;> rcases h with ⟨hr, hi⟩ <;> simp [hr,hi] at h'
  ext <;> assumption

lemma primary_associated_eq {z w : GaussianInt} (hz : Primary z) (hw : Primary w) (h : Associated z w) :
    z = w := by
  obtain ⟨u,rfl⟩ := h
  rw [primary_unit_eq_one ((primary_mul_iff hz).mp hw) u.isUnit, mul_one]

lemma square_mod_two (a : ℤ) : a^2 % 2 = a % 2 := by
  rw [sq, Int.mul_emod]
  rcases (show a%2 = 0 ∨ a%2 = 1 by omega) with h | h <;> rw [h] <;> decide

lemma exists_primary_associate (z : GaussianInt) (ho : z.norm % 2 = 1) :
    ∃ w : GaussianInt, Primary w ∧ Associated w z := by
  rw [norm_sq, Int.add_emod, square_mod_two, square_mod_two] at ho
  have orient (v : GaussianInt) (hi : v.im % 2 = 0) (hr : v.re % 2 = 1) :
      ∃ w : GaussianInt, Primary w ∧ Associated w v := by
    by_cases hs : (v.re + v.im) % 4 = 1
    · exact ⟨v, (primary_iff _).mpr ⟨hi,hs⟩, Associated.refl _⟩
    · refine ⟨-v, (primary_iff _).mpr ?_, ?_⟩
      · change (-v.im)%2 = 0 ∧ (-v.re + -v.im)%4 = 1
        omega
      · simpa using associated_mul_unit_left v (-1) (isUnit_neg.mpr isUnit_one)
  by_cases he : z.im % 2 = 0
  · exact orient _ he (by omega)
  · let i : GaussianInt := ⟨0,1⟩
    have hu : IsUnit i := (Zsqrtd.norm_eq_one_iff' (by decide : (-1:ℤ) ≤ 0) i).mp (by decide)
    obtain ⟨w,hw,hwz⟩ := orient (z*i)
      (by change (z.re * 1 + z.im * 0)%2 = 0; omega)
      (by change (z.re * 0 + -1*z.im*1)%2 = 1; omega)
    exact ⟨w,hw,hwz.trans (associated_mul_unit_left z i hu)⟩

lemma primary_odd_norm {z : GaussianInt} (h : Primary z) : z.norm % 2 = 1 := by
  rw [norm_sq, Int.add_emod, square_mod_two, square_mod_two]
  have := (primary_iff _).mp h
  omega

lemma coprime_of_norms {z w : GaussianInt} (hc : Nat.Coprime z.norm.natAbs w.norm.natAbs) :
    IsCoprime z w := by
  have h := hc.isCoprime.map (Int.castRingHom GaussianInt)
  have hz : z ∣ (z.norm.natAbs : GaussianInt) := by
    rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  have hw : w ∣ (w.norm.natAbs : GaussianInt) := by
    rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  apply IsCoprime.of_isCoprime_of_dvd_right _ hw
  apply IsCoprime.of_isCoprime_of_dvd_left _ hz
  simpa using h

lemma norm_dvd_sq {z : GaussianInt} {m : ℕ} (h : z ∣ (m : GaussianInt)) :
    z.norm.natAbs ∣ m^2 := by
  obtain ⟨w,hw⟩ := h
  refine ⟨w.norm.natAbs, ?_⟩
  have he := congrArg (fun t : GaussianInt => t.norm.natAbs) hw
  simpa [sq, Int.natAbs_mul] using he

lemma scalar_split {a b m n : ℕ} (h : m.Coprime n) (ha : a ∣ m^2) (hb : b ∣ n^2)
    (he : a*b = m*n) : a = m := by
  apply Nat.dvd_antisymm
  · apply ((h.pow_left 2).coprime_dvd_left ha).dvd_of_dvd_mul_right
    rw [← he]
    exact dvd_mul_right _ _
  · apply ((h.pow_right 2).coprime_dvd_right hb).dvd_of_dvd_mul_right
    rw [he]
    exact dvd_mul_right _ _

lemma primary_factor {z : GaussianInt} {m n : ℕ} (hz : Primary z) (hc : m.Coprime n)
    (hn : z.norm.natAbs = m*n) :
    ∃ v w : GaussianInt, Primary v ∧ Primary w ∧ v.norm.natAbs = m ∧ w.norm.natAbs = n ∧ z = v*w := by
  have hd : z ∣ (m : GaussianInt)*(n : GaussianInt) := by
    rw [← Nat.cast_mul, ← hn, GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  obtain ⟨v,w,hv,hw,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  simp only [Zsqrtd.norm_mul, Int.natAbs_mul] at hn
  have hvm := scalar_split hc (norm_dvd_sq hv) (norm_dvd_sq hw) hn
  have hwn := scalar_split hc.symm (norm_dvd_sq hw) (norm_dvd_sq hv)
    (by simpa only [mul_comm] using hn)
  have ho := primary_odd_norm hz
  rw [Zsqrtd.norm_mul, Int.mul_emod] at ho
  have hvodd : v.norm % 2 = 1 := by
    by_contra he
    have e : v.norm % 2 = 0 := by omega
    simp [e] at ho
  obtain ⟨t,ht,htv⟩ := exists_primary_associate v hvodd
  have htvn := Zsqrtd.norm_eq_of_associated (by decide : (-1:ℤ) ≤ 0) htv
  obtain ⟨u,hu⟩ := htv
  have he : v*w = t*(u*w) := by rw [← hu, mul_assoc]
  have hwu := (primary_mul_iff ht).mp (he ▸ hz)
  have hun := (Zsqrtd.norm_eq_one_iff' (by decide : (-1:ℤ) ≤ 0) (u:GaussianInt)).mpr u.isUnit
  refine ⟨t, u*w, ht, hwu, by simpa only [htvn] using hvm, ?_, he⟩
  simpa only [Zsqrtd.norm_mul, hun, one_mul] using hwn

lemma primary_factor_unique {v w v' w' : GaussianInt} (hv : Primary v) (hv' : Primary v')
    (hc : Nat.Coprime v.norm.natAbs w.norm.natAbs) (hvm : v.norm.natAbs = v'.norm.natAbs)
    (hwn : w.norm.natAbs = w'.norm.natAbs) (he : v*w = v'*w') : v = v' ∧ w = w' := by
  have h₁ : v ∣ v' := (coprime_of_norms (hwn ▸ hc)).dvd_of_dvd_mul_right
    (he ▸ dvd_mul_right v w)
  have h₂ : v' ∣ v := (coprime_of_norms (hvm ▸ hc)).dvd_of_dvd_mul_right
    (he.symm ▸ dvd_mul_right v' w')
  have h := primary_associated_eq hv hv' (associated_of_dvd_dvd h₁ h₂)
  subst v'
  have h0 : v ≠ 0 := by intro e; simp [e] at hv; have := primary_odd_norm hv; simp at this
  exact ⟨rfl,mul_left_cancel₀ h0 he⟩

lemma shell_finite (n : ℕ) :
    {z : GaussianInt | Primary z ∧ z.norm.natAbs = n}.Finite := by
  let box := Set.Icc (-((n:ℤ)+1)) ((n:ℤ)+1)
  have hf : box.Finite := Set.finite_Icc _ _
  apply ((hf.prod hf).image (fun ab : ℤ × ℤ => (⟨ab.1, ab.2⟩ : GaussianInt))).subset
  rintro ⟨a,b⟩ ⟨-, hn⟩
  have h := GaussianInt.abs_natCast_norm (⟨a,b⟩ : GaussianInt)
  rw [hn, norm_sq] at h
  change (n:ℤ) = a^2 + b^2 at h
  refine ⟨(a,b), ⟨?_,?_⟩,rfl⟩
  · constructor <;> nlinarith [sq_nonneg (a-1),sq_nonneg (a+1),sq_nonneg b,sq_nonneg a]
  · constructor <;> nlinarith [sq_nonneg (b-1),sq_nonneg (b+1),sq_nonneg b,sq_nonneg a]

noncomputable def shell (n : ℕ) : Finset GaussianInt := (shell_finite n).toFinset

lemma mem_shell {z : GaussianInt} {n : ℕ} : z ∈ shell n ↔ Primary z ∧ z.norm.natAbs = n :=
  (shell_finite n).mem_toFinset

noncomputable def mass (n : ℕ) : GaussianInt := ∑ z ∈ shell n, z

theorem mass_mul {m n : ℕ} (hc : m.Coprime n) : mass (m*n) = mass m * mass n := by
  classical
  unfold mass
  simp only [Finset.sum_mul, Finset.mul_sum]
  symm
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun p _ => p.1*p.2)
  · rintro ⟨v,w⟩ hvw
    obtain ⟨hv,hw⟩ := Finset.mem_product.mp hvw
    obtain ⟨hvp,hvn⟩ := mem_shell.mp hv
    obtain ⟨hwp,hwn⟩ := mem_shell.mp hw
    exact mem_shell.mpr ⟨(primary_mul_iff hvp).mpr hwp, by simp [hvn,hwn,Int.natAbs_mul,mul_comm]⟩
  · rintro ⟨v,w⟩ hvw ⟨v',w'⟩ hvw' he
    simp only [Finset.mem_product,mem_shell] at hvw hvw'
    have h := primary_factor_unique hvw.1.1 hvw'.1.1 (by simpa only [hvw.1.2,hvw.2.2] using hc.symm)
      (hvw.1.2.trans hvw'.1.2.symm) (hvw.2.2.trans hvw'.2.2.symm) he
    exact Prod.ext h.1 h.2
  · intro z hz
    obtain ⟨hP, hn⟩ := mem_shell.mp hz
    obtain ⟨v,w,hv,hw,hvm,hwn,he⟩ := primary_factor hP hc.symm (by simpa only [mul_comm] using hn)
    exact ⟨(v,w),Finset.mem_product.mpr ⟨mem_shell.mpr ⟨hv,hvm⟩,mem_shell.mpr ⟨hw,hwn⟩⟩,he.symm⟩
  · intro p _
    exact mul_comm _ _

theorem mass_real (n : ℕ) : (mass n).im = 0 := by
  have hs : star (mass n) = mass n := by
    unfold mass
    rw [star_sum]
    apply Finset.sum_bij (fun z _ => star z)
    · intro z hz
      obtain ⟨hP,hn⟩ := mem_shell.mp hz
      exact mem_shell.mpr ⟨primary_star hP, by simpa using hn⟩
    · intro _ _ _ _ h
      exact star_injective h
    · intro z hz
      obtain ⟨hP,hn⟩ := mem_shell.mp hz
      exact ⟨star z,mem_shell.mpr ⟨primary_star hP,by simpa using hn⟩,star_star _⟩
    · intro _ _; rfl
  have := congrArg Zsqrtd.im hs
  change -(mass n).im = (mass n).im at this
  omega

theorem coefficient_mul {m n : ℕ} (hc : m.Coprime n) :
    (mass (m*n)).re = (mass m).re * (mass n).re := by simp [mass_mul hc,mass_real]

end TunnellGaussian

namespace TunnellGaussian

open GaussianInt Finset

lemma norm_product (z : GaussianInt) : z * star z = (z.norm.natAbs : GaussianInt) := by
  rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]

lemma unit_of_norm_one {z : GaussianInt} (h : z.norm.natAbs = 1) : IsUnit z := by
  apply (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) z).mp
  have h' := GaussianInt.abs_natCast_norm z
  simpa [h] using h'.symm

lemma norm_prime {z : GaussianInt} {p : ℕ} (hp : p.Prime) (h : z.norm.natAbs = p) : Prime z := by
  apply Irreducible.prime
  constructor
  · intro hu
    have hn := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) z).mpr hu
    simp [hn] at h
    exact hp.ne_one h.symm
  · intro a b hab
    rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul] at h
    rcases hp.eq_one_or_self_of_dvd _ (h ▸ dvd_mul_right _ _) with hh | hh
    · exact Or.inl (unit_of_norm_one hh)
    · exact Or.inr (unit_of_norm_one (Nat.eq_of_mul_eq_mul_left hp.pos (by simpa [hh] using h)))

lemma mem_shell_image {r : GaussianInt} {p n : ℕ} (hr : Primary r) (hrn : r.norm.natAbs = p)
    (hp : 0 < p) (z : GaussianInt) :
    z ∈ (shell n).image (r * ·) ↔ z ∈ shell (p*n) ∧ r ∣ z := by
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hw, hwn⟩ := mem_shell.mp hw
    exact ⟨mem_shell.mpr ⟨(primary_mul_iff hr).mpr hw, by simp [Int.natAbs_mul, hrn, hwn]⟩,
      dvd_mul_right _ _⟩
  · rintro ⟨hz, w, rfl⟩
    obtain ⟨hz, hn⟩ := mem_shell.mp hz
    simp only [Zsqrtd.norm_mul, Int.natAbs_mul, hrn] at hn
    exact Finset.mem_image.mpr ⟨w, mem_shell.mpr ⟨(primary_mul_iff hr).mp hz,
      Nat.eq_of_mul_eq_mul_left hp hn⟩, rfl⟩

lemma shell_sum_image (r : GaussianInt) (hr : r ≠ 0) (n : ℕ) :
    ∑ z ∈ (shell n).image (r * ·), z = r * mass n := by
  rw [Finset.sum_image (by intro a _ b _ h; exact mul_left_cancel₀ hr h)]
  exact (Finset.mul_sum ..).symm

lemma norm_dvd_by_prime {p : ℕ} {r z : GaussianInt} (hr : Prime r) (hrp : r ∣ (p : GaussianInt))
    (hz : p ∣ z.norm.natAbs) : r ∣ z ∨ star r ∣ z := by
  have h : r ∣ z * star z := (norm_product z).symm ▸ hrp.trans (Nat.cast_dvd_cast hz)
  rcases hr.dvd_mul.mp h with h | h
  · exact Or.inl h
  · obtain ⟨a, ha⟩ := h
    right
    exact ⟨star a, by simpa [mul_comm] using congrArg star ha⟩

lemma split_recurrence {r : GaussianInt} {p : ℕ} (hp : p.Prime) (hr : r ∈ shell p)
    (hne : r ≠ star r) (hsm : mass p = r + star r) (k : ℕ) :
    mass (p^(k+2)) = mass p * mass (p^(k+1)) - (p : GaussianInt)*mass (p^k) := by
  classical
  obtain ⟨hP,hn⟩ := mem_shell.mp hr
  have hPs := primary_star hP
  have hns : (star r).norm.natAbs = p := by simpa using hn
  have hprime := norm_prime hp hn
  have hsprime := norm_prime hp hns
  have fact : r * star r = (p : GaussianInt) := by rw [norm_product,hn]
  have hno : ¬star r ∣ r := fun h => hne (primary_associated_eq hPs hP
    (hsprime.associated_of_dvd hprime h)).symm
  let B := (shell (p^(k+1))).image (r * ·)
  let C := (shell (p^(k+1))).image (star r * ·)
  have hmB (z : GaussianInt) : z ∈ B ↔ z ∈ shell (p^(k+2)) ∧ r ∣ z := by
    simpa only [B, pow_succ' p (k+1)] using mem_shell_image hP hn hp.pos z (n := p^(k+1))
  have hmC (z : GaussianInt) : z ∈ C ↔ z ∈ shell (p^(k+2)) ∧ star r ∣ z := by
    simpa only [C, pow_succ' p (k+1)] using mem_shell_image hPs hns hp.pos z (n := p^(k+1))
  have hUnion : B ∪ C = shell (p^(k+2)) := by
    ext z
    rw [mem_union,hmB,hmC]
    constructor
    · rintro (h|h) <;> exact h.1
    · intro hz
      have hnz := (mem_shell.mp hz).2
      rcases norm_dvd_by_prime hprime (fact ▸ dvd_mul_right r (star r)) (z := z)
          (by rw [hnz]; exact dvd_pow_self p (by omega)) with hv | hv
      · exact Or.inl ⟨hz,hv⟩
      · exact Or.inr ⟨hz,hv⟩
  have hInt : B ∩ C = (shell (p^k)).image ((p : GaussianInt) * ·) := by
    have hpP : Primary (p : GaussianInt) := fact ▸ (primary_mul_iff hP).mpr hPs
    have hpn : (p : GaussianInt).norm.natAbs = p^2 := by simp [sq, Int.natAbs_mul]
    ext z
    rw [mem_inter,hmB,hmC,mem_shell_image hpP hpn (pow_pos hp.pos 2), ← pow_add,
        add_comm 2 k]
    constructor
    · rintro ⟨⟨hz, a, rfl⟩, _, h⟩
      obtain ⟨w, rfl⟩ := (hsprime.dvd_mul.mp h).resolve_left hno
      exact ⟨hz, w, by rw [← fact, mul_assoc]⟩
    · rintro ⟨hz, h⟩
      rw [← fact] at h
      exact ⟨⟨hz,(dvd_mul_right _ _).trans h⟩,hz,(dvd_mul_left _ _).trans h⟩
  have eqn := Finset.sum_union_inter (s₁ := B) (s₂ := C) (f := fun z => z)
  rw [hUnion, hInt, shell_sum_image _ (Nat.cast_ne_zero.mpr hp.ne_zero)] at eqn
  change mass _ + _ = _ + _ at eqn
  dsimp only [B,C] at eqn
  rw [shell_sum_image _ hprime.ne_zero, shell_sum_image _ hsprime.ne_zero] at eqn
  rw [hsm, add_mul]
  exact eq_sub_of_add_eq eqn

lemma inert_recurrence (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (k : ℕ) :
    mass (p^(k+2)) = mass p * mass (p^(k+1)) - (p : GaussianInt)*mass (p^k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hprime := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr h3
  have hall (z : GaussianInt) (h : p ∣ z.norm.natAbs) : (p : GaussianInt) ∣ z := by
    rcases norm_dvd_by_prime hprime dvd_rfl h with h' | h'
    · exact h'
    · simpa using h'
  have hP : Primary (-(p : GaussianInt)) := by
    rw [primary_iff]
    change (-(0 : ℤ)) % 2 = 0 ∧ (-(p:ℤ) + -0) % 4 = 1
    omega
  have hN : (-(p : GaussianInt)).norm.natAbs = p^2 := by simp [sq, Int.natAbs_mul]
  have h0 : shell p = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨_,hn⟩ := mem_shell.mp hz
    obtain ⟨a,ha⟩ := hall z (hn ▸ dvd_rfl)
    have h : p^2 ∣ p := by
      refine ⟨a.norm.natAbs, ?_⟩
      rw [ha] at hn
      simpa [sq, Int.natAbs_mul] using hn.symm
    have := Nat.le_of_dvd hp.pos h
    nlinarith [hp.two_le]
  have hi : shell (p^(k+2)) = (shell (p^k)).image ((-(p : GaussianInt)) * ·) := by
    ext z
    rw [mem_shell_image hP hN (pow_pos hp.pos 2), ← pow_add, add_comm 2 k]
    refine ⟨fun hz => ⟨hz,?_⟩, And.left⟩
    apply neg_dvd.mpr
    apply hall
    rw [(mem_shell.mp hz).2]
    exact dvd_pow_self p (by omega)
  have hem : mass p = 0 := by simp [mass,h0]
  have hmass : mass (p^(k+2)) = -(p : GaussianInt) * mass (p^k) := by
    unfold mass at *
    rw [hi, shell_sum_image _ (by exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.ne_zero))]
    rfl
  simp [hmass,hem]

lemma shell_split_prime {p : ℕ} (hp : p.Prime) {z : GaussianInt} (hz : z ∈ shell p) :
    shell p = {z, star z} := by
  have ⟨hzP,hn⟩ := mem_shell.mp hz
  have hstar : star z ∈ shell p := mem_shell.mpr ⟨primary_star hzP, by simpa using hn⟩
  ext w
  constructor
  · intro hw
    obtain ⟨hwP,hwn⟩ := mem_shell.mp hw
    have hwprim := norm_prime hp hwn
    have hzprim := norm_prime hp hn
    have hstprim := norm_prime hp (mem_shell.mp hstar).2
    have H : w ∣ z * star z := by
      rw [← Zsqrtd.norm_eq_mul_conj, ← GaussianInt.natCast_natAbs_norm, hn, ← hwn,
        GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
      exact dvd_mul_right _ _
    rcases hwprim.dvd_or_dvd H with h | h
    · have := primary_associated_eq hwP hzP (hwprim.associated_of_dvd hzprim h)
      simp [this]
    · have := primary_associated_eq hwP (primary_star hzP)
        (hwprim.associated_of_dvd hstprim h)
      simp [this]
  · simp only [mem_insert,mem_singleton]
    rintro (rfl|rfl) <;> assumption

lemma distinct_star_of_prime {p : ℕ} (hp : p.Prime) {z : GaussianInt} (hn : z.norm.natAbs = p) :
    z ≠ star z := by
  intro e
  have h := congrArg Zsqrtd.im e
  change z.im = -z.im at h
  have hi : z.im = 0 := by omega
  rw [norm_sq, hi, zero_pow (by decide : 2 ≠ 0), add_zero, Int.natAbs_pow] at hn
  exact Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) (show (z.re.natAbs ^ 2).Prime by rwa [hn])

theorem mass_prime_power (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ) :
    mass (p^(k+2)) = mass p * mass (p^(k+1)) - (p : GaussianInt)*mass (p^k) := by
  by_cases h3 : p % 4 = 3
  · exact inert_recurrence p hp h3 k
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,b,hab⟩ := Nat.Prime.sq_add_sq h3
  let w : GaussianInt := ⟨a,b⟩
  have hw : w.norm = p := by
    rw [norm_sq]
    change (a : ℤ)^2 + (b : ℤ)^2 = p
    exact_mod_cast hab
  obtain ⟨r, hr, he⟩ := exists_primary_associate w (by
    rw [hw]; exact_mod_cast hp.eq_two_or_odd.resolve_left hodd)
  have hn : r.norm.natAbs = p := by
    rw [Zsqrtd.norm_eq_of_associated (by decide : (-1 : ℤ) ≤ 0) he,hw,Int.natAbs_natCast]
  have hr' := mem_shell.mpr (And.intro hr hn)
  have hne := distinct_star_of_prime hp hn
  apply split_recurrence hp hr' hne _ k
  simp [mass, shell_split_prime hp hr', hne]

theorem coefficient_prime_power (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ) :
    (mass (p^(k+2))).re =
      (mass p).re * (mass (p^(k+1))).re - (p : ℤ) * (mass (p^k)).re := by
  rw [mass_prime_power p hp hodd k]
  simp [mass_real]

end TunnellGaussian

/-
# Local properties of the congruent-number curves
-/

namespace TunnellCoates

open WeierstrassCurve WeierstrassCurve.Affine

def E {K : Type*} [CommRing K] (n : K) : WeierstrassCurve K := ⟨0,0,0,-n^2,0⟩

lemma E_discriminant {K : Type*} [CommRing K] (n : K) : (E n).Δ = 64*n^6 := by
  simp [E, Δ, b₂,b₄,b₆,b₈]
  ring

lemma E_equation {K : Type*} [CommRing K] (n x y : K) :
    (E n).toAffine.Equation x y ↔ y^2 = x^3-n^2*x := by
  simp [Affine.equation_iff, E, sub_eq_add_neg]

lemma E_elliptic {K : Type*} [Field K] {n : K} (h2 : (2:K) ≠ 0) (hn : n ≠ 0) :
    (E n).IsElliptic := by
  constructor
  rw [E_discriminant, show (64:K)=(2:K)^6 by norm_num, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hn)

lemma card_points {K : Type*} [Field K] [Fintype K] [DecidableEq K] (n : K)
    [(E n).IsElliptic] : Nat.card (E n).toAffine.Point =
    (Finset.univ.filter (fun xy : K × K => xy.2^2 = xy.1^3-n^2*xy.1)).card + 1 := by
  classical
  have eqv := (E n).toAffine.pointEquiv.trans
    ((Equiv.subtypeEquivRight (fun xy : K×K => E_equation n xy.1 xy.2)).optionCongr)
  calc
    _ = Nat.card (Option {xy : K×K // xy.2^2 = xy.1^3-n^2*xy.1}) := Nat.card_congr eqv
    _ = _ := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma eight_dvd_of_four_two {G : Type*} [AddCommGroup G] (P Q : G)
    (h4 : (4:ℕ) • P = 0) (hp : (2:ℕ) • P ≠ 0) (hq : (2:ℕ) • Q = 0)
    (hq0 : Q ≠ 0) (hdiff : Q ≠ (2:ℕ) • P) : 8 ∣ Nat.card G := by
  have hord : addOrderOf P = 4 := by
    apply addOrderOf_eq_of_nsmul_and_div_prime_nsmul (by decide) h4
    intro p hp' hdiv
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp
      (hp'.dvd_of_dvd_pow (by simpa using hdiv : p ∣ 2^2))
    subst p
    exact hp
  let H := AddSubgroup.zmultiples P
  have hnon : Q ∉ H := by
    rintro ⟨m,hm⟩
    have hred : (m % 4) • P = Q := by
      simpa [hord, hm] using (mod_addOrderOf_zsmul P m)
    have hlo := Int.emod_nonneg m (by decide : (4:ℤ) ≠ 0)
    have hhi := Int.emod_lt_of_pos m (by decide : 0 < (4:ℤ))
    generalize hr : m % 4 = a at hred hlo hhi
    interval_cases a
    · exact hq0 (by simpa using hred.symm)
    · have hPQ : P = Q := by simpa using hred
      exact hp (hPQ ▸ hq)
    · exact hdiff (by exact_mod_cast hred.symm)
    · have h6 : (6:ℕ) • P = 0 := by
        calc _ = (2:ℕ) • ((3:ℕ) • P) := by rw [← mul_smul]; rfl
             _ = (2:ℕ) • Q := by rw [show (3:ℕ) • P = Q by exact_mod_cast hred]
             _ = 0 := hq
      change (4+2:ℕ) • P = 0 at h6
      rw [add_smul, h4, zero_add] at h6
      exact hp h6
  have hco : addOrderOf (Q : G ⧸ H) = 2 :=
    addOrderOf_eq_prime (by simpa only [← QuotientAddGroup.mk_nsmul, hq, QuotientAddGroup.mk_zero])
      (fun h => hnon ((QuotientAddGroup.eq_zero_iff _).mp h))
  have hdiv := addOrderOf_dvd_natCard (Q : G ⧸ H)
  rw [hco] at hdiv
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H, Nat.card_zmultiples, hord]
  omega

lemma eight_dvd_points_base (p : ℕ) [Fact p.Prime] (hp : p%4=1) :
    8 ∣ ((Finset.univ.filter (fun xy : ZMod p × ZMod p =>
      xy.2^2 = xy.1^3-xy.1)).card + 1) := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2:ZMod p) ≠ 0 := by
    change ((2:ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
  let W := E (1 : ZMod p)
  have : W.IsElliptic := E_elliptic h2 one_ne_zero
  obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  have hi2 : i^2 = -1 := by simpa [pow_two] using hi.symm
  have hy : (1-i : ZMod p) ≠ 0 := by
    intro h
    have hii : i=1 := (sub_eq_zero.mp h).symm
    rw [hii, one_pow] at hi2
    apply h2
    linear_combination hi2
  have H0 : W.toAffine.Equation 0 0 := by simp [W, E]
  have HQ : W.toAffine.Equation 1 0 := by simp [W, E_equation]
  have HP : W.toAffine.Equation i (1-i) := by
    rw [E_equation]; linear_combination -(i-1)*hi2
  let R := Affine.Point.mk H0
  let Q := Affine.Point.mk HQ
  let P := Affine.Point.mk HP
  have hR : R ≠ 0 := Affine.Point.some_ne_zero _
  have hQ : Q ≠ 0 := Affine.Point.some_ne_zero _
  have hQR : Q ≠ R := by
    change Affine.Point.some _ _ _ ≠ Affine.Point.some _ _ _
    simp
  have r2 : (2:ℕ) • R=0 := by
    rw [two_nsmul]; apply Affine.Point.add_self_of_Y_eq; simp [W, E, Affine.negY]
  have q2 : (2:ℕ) • Q=0 := by
    rw [two_nsmul]; apply Affine.Point.add_self_of_Y_eq; simp [W, E, Affine.negY]
  have hneg : 1-i ≠ W.toAffine.negY i (1-i) := by
    simp only [W,E,Affine.negY,zero_mul,sub_zero]
    intro h
    apply (mul_ne_zero h2 hy)
    linear_combination h
  have hs : W.toAffine.slope i i (1-i) (1-i) = -(1+i) := by
    rw [Affine.slope_of_Y_ne rfl hneg]
    apply (div_eq_iff (sub_ne_zero.mpr hneg)).mpr
    simp only [W,E,Affine.negY,zero_mul,mul_zero,add_zero,sub_zero,one_pow]
    linear_combination hi2
  have hx : W.toAffine.addX i i (-(1+i)) = 0 := by
    simp only [W,E,Affine.addX,zero_mul,add_zero,sub_zero]
    linear_combination hi2
  have hh : (2:ℕ) • P = R := by
    rw [two_nsmul]
    change Affine.Point.some _ _ _ + Affine.Point.some _ _ _ = Affine.Point.some _ _ _
    rw [Affine.Point.add_self_of_Y_ne hneg]
    simp only [Affine.Point.some.injEq, hs, hx, true_and]
    simp only [Affine.addY, Affine.negAddY, hx]
    simp only [W,E,Affine.negY,zero_mul,sub_zero]
    linear_combination -hi2
  have h4 : (4:ℕ) • P = 0 := by simpa only [show (4:ℕ)=2*2 by decide, mul_smul, hh] using r2
  have he := eight_dvd_of_four_two P Q h4 (hh ▸ hR) q2 hQ (hh ▸ hQR)
  rw [card_points] at he
  simpa using he

end TunnellCoates

/- The quartic Jacobi sum for the split primes of the congruent-number base curve. -/

namespace TunnellSplit

open Finset
open scoped ComplexConjugate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def phi (F : Type*) [Field F] [Fintype F] [DecidableEq F] : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

@[simp] lemma phi_apply (a : F) : phi F a = (quadraticChar F a : ℂ) := rfl

lemma phi_square : phi F ^ 2 = 1 := by
  ext x
  rw [MulChar.pow_apply_coe, phi_apply, MulChar.one_apply x.isUnit]
  exact_mod_cast quadraticChar_sq_one x.ne_zero

lemma quadratic_unique {χ ψ : MulChar F ℂ}
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) (hc : χ ≠ 1) (hd : ψ ≠ 1) : χ = ψ := by
  let e := MulChar.equiv_rootsOfUnity F ℂ
  let h : MulChar F ℂ →* ℂ := (Units.coeHom ℂ).comp
    ((rootsOfUnity (Fintype.card Fˣ) ℂ).subtype.comp e.toMonoidHom)
  have hi : Function.Injective h := Units.val_injective.comp (Subtype.val_injective.comp e.injective)
  have hn (a : MulChar F ℂ) (ha : a^2 = 1) (hb : a ≠ 1) : h a = -1 := by
    apply (sq_eq_one_iff.mp (show (h a)^2 = 1 by rw [← map_pow, ha, map_one])).resolve_left
    exact fun he => hb (hi (he.trans h.map_one.symm))
  exact hi ((hn χ hχ hc).trans (hn ψ hψ hd).symm)

theorem quartic_exists (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ χ : MulChar (ZMod p) ℂ, orderOf χ = 4 ∧ χ ^ 2 = phi (ZMod p) := by
  have hd : 4 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hd Complex.isPrimitiveRoot_I
  refine ⟨χ, hχ, quadratic_unique ?_ phi_square ?_ ?_⟩
  · rw [← pow_mul, show 2 * 2 = 4 by decide, ← hχ, pow_orderOf_eq_one]
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hχ] at this
    omega
  · apply (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr
    apply quadraticChar_ne_one
    rw [ZMod.ringChar_zmod_n]; omega

lemma square_grouping (hc : ringChar F ≠ 2) (f : F → ℂ) :
    ∑ x : F, f (x^2) = ∑ y : F, (1 + phi F y) * f y := by
  classical
  calc
    _ = ∑ y : F, ∑ x ∈ univ.filter (fun x : F => x^2 = y), f (x^2) := by
      rw [sum_fiberwise_of_maps_to (fun x _ => mem_univ (x^2))]
    _ = _ := by
      apply sum_congr rfl
      intro y _
      have he : ∑ x ∈ univ.filter (fun x : F => x^2 = y), f (x^2) =
          ∑ _x ∈ univ.filter (fun x : F => x^2 = y), f y :=
        sum_congr rfl (fun x hx => congrArg f (mem_filter.mp hx).2)
      rw [he, sum_const, nsmul_eq_mul]
      have h := quadraticChar_card_sqrts hc y
      rw [Set.toFinset_ofPred] at h
      have hc' : ((univ.filter (fun x : F => x^2 = y)).card : ℂ) = phi F y + 1 := by
        rw [phi_apply]; exact_mod_cast h
      rw [hc', add_comm]

theorem trace_jacobi (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val % 4 = 1)
    (χ : MulChar (ZMod p.val) ℂ) (hχ : χ ^ 2 = phi (ZMod p.val)) :
    let a : ℤ := (p.val : ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - xy.1)).card
    (a : ℂ) = -(jacobiSum χ (phi (ZMod p.val)) + jacobiSum (χ^3) (phi (ZMod p.val))) := by
  let F := ZMod p.val
  have hp2 : p.val ≠ 2 := by omega
  have hc : ringChar (ZMod p.val) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  have hn : quadraticChar (ZMod p.val) (-1) = 1 := by
    simpa only [legendreSym, Int.cast_neg, Int.cast_one] using
      (legendreSym.at_neg_one hp2).trans (ZMod.χ₄_nat_one_mod_four hp)
  have hφ (x : ZMod p.val) : phi (ZMod p.val) x = χ x ^ 2 := by
    rw [← hχ, MulChar.pow_apply' _ (by decide : 2 ≠ 0)]
  have hf (x : ZMod p.val) : (quadraticChar (ZMod p.val) (x^3 - x) : ℂ) =
      χ (x^2) * phi (ZMod p.val) (1-x^2) := by
    rw [show x^3 - x = (-1) * x * (1-x^2) by ring, map_mul, map_mul, hn, one_mul, Int.cast_mul,
      ← phi_apply, ← phi_apply, hφ x, map_pow]
  have ht := OMA.R_CongruentNumber_Tunnell_even_R1.trace_eq_neg_sum 1 p hp2
  simp only [Nat.cast_one, one_pow, one_mul] at ht
  dsimp only
  rw [ht, Int.cast_neg, Int.cast_sum]
  simp_rw [hf]
  rw [square_grouping hc (fun x => χ x * phi (ZMod p.val) (1-x))]
  congr 1
  rw [jacobiSum, jacobiSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro y _
  rw [hφ y, MulChar.pow_apply' _ (by decide : 3 ≠ 0)]
  ring

open GaussianInt in
lemma jacobi_is_gaussian {χ : MulChar F ℂ} (hχ : χ ^ 4 = 1) :
    ∃ g : GaussianInt, (g : ℂ) = jacobiSum χ (phi F) := by
  have hφ : (phi F) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, phi_square, one_pow]
  have hm := jacobiSum_mem_algebraAdjoin_of_pow_eq_one hχ hφ Complex.isPrimitiveRoot_I
  let e := GaussianInt.toComplex.toIntAlgHom
  have H : Algebra.adjoin ℤ ({Complex.I} : Set ℂ) ≤ e.range := by
    apply Algebra.adjoin_le
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    refine ⟨⟨0, 1⟩, ?_⟩
    change ((⟨0, 1⟩ : GaussianInt) : ℂ) = Complex.I
    simp [GaussianInt.toComplex_def']
  exact H hm

omit [DecidableEq F] in
lemma conj_jacobi (χ ψ : MulChar F ℂ) :
    conj (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
  unfold jacobiSum
  rw [map_sum]
  apply sum_congr rfl
  intro x _
  rw [map_mul]
  exact congrArg₂ (· * ·) (χ.star_apply' _) (ψ.star_apply' _)

theorem split_trace_norm (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val % 4 = 1) :
    let t : ℤ := (p.val : ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - xy.1)).card
    ∃ a b : ℤ, t = 2 * a ∧ a^2 + b^2 = p.val := by
  dsimp only
  obtain ⟨χ, ho, hχ⟩ := quartic_exists p.val hp
  let ψ := phi (ZMod p.val)
  have h4 : χ ^ 4 = 1 := ho ▸ pow_orderOf_eq_one χ
  have h3 : χ ^ 3 = χ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact h4
  have hψ : ψ⁻¹ = ψ := by
    symm; apply eq_inv_of_mul_eq_one_left
    rw [← pow_two]; exact phi_square
  have hne {k : ℕ} (hk : ¬ 4 ∣ k) : χ ^ k ≠ 1 := by
    intro h
    exact hk (ho ▸ orderOf_dvd_of_pow_eq_one h)
  have hc : ringChar ℂ ≠ ringChar (ZMod p.val) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
    exact p.property.ne_zero.symm
  have hn := jacobiSum_mul_jacobiSum_inv (F' := ℂ) hc
    (χ := χ) (φ := ψ) (by simpa using hne (k := 1) (by decide))
    (by simpa only [ψ, ← hχ] using hne (k := 2) (by decide))
    (by change χ * phi (ZMod p.val) ≠ 1; rw [← hχ, ← pow_succ']; exact hne (by decide))
  rw [← conj_jacobi, ZMod.card] at hn
  have ht := trace_jacobi p hp χ hχ
  change _ = -(jacobiSum χ ψ + jacobiSum (χ^3) ψ) at ht
  have hh : jacobiSum χ⁻¹ ψ = conj (jacobiSum χ ψ) := by rw [conj_jacobi, hψ]
  rw [h3, hh] at ht
  obtain ⟨g, hg⟩ := jacobi_is_gaussian h4
  change (g : ℂ) = jacobiSum χ ψ at hg
  rw [← hg, GaussianInt.toComplex_def₂] at hn ht
  refine ⟨-g.re, g.im, ?_, ?_⟩
  · have ht' := congrArg Complex.re ht
    simp only [Complex.intCast_re, Complex.neg_re, Complex.add_re, Complex.conj_re] at ht'
    norm_cast at ht'
    rw [Int.subNatNat_eq_coe] at ht'
    linarith
  · have hn' := congrArg Complex.re hn
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.natCast_re] at hn'
    norm_cast at hn'
    nlinarith

end TunnellSplit

/- The Frobenius trace of every congruent-number twist vanishes at primes 3 modulo 4. -/

namespace TunnellInert

open Finset Polynomial

theorem eta_zero_of_mod_four {m : ℕ} (hm : m % 4 ≠ 1) :
    (X * ∏ k ∈ Icc 1 m, ((1 - (X : ℤ[X])^(4*k))^2 * (1-X^(8*k))^2)).coeff m = 0 := by
  cases m with
  | zero => simp
  | succ d =>
    let P : ℤ[X] := ∏ k ∈ Icc 1 (d+1), ((1-X^k)^2 * (1-X^(2*k))^2)
    have hP : (expand ℤ 4) P =
        ∏ k ∈ Icc 1 (d+1), ((1-(X : ℤ[X])^(4*k))^2 * (1-X^(8*k))^2) := by
      dsimp only [P]
      simp only [map_prod, map_mul, map_pow, map_sub, map_one, expand_X, ← pow_mul,
        ← Nat.mul_assoc]
    rw [← hP, Polynomial.coeff_X_mul, Polynomial.coeff_expand (by decide : 0 < 4)]
    exact if_neg (by omega)

theorem inert_trace_zero (n : ℕ) (p : Nat.Primes) (hp : p.val % 4 = 3) :
    letI : NeZero p.val := ⟨p.property.ne_zero⟩
    (p.val : ℤ) - (Finset.univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - (n : ZMod p.val)^2 * xy.1)).card = 0 := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have hp' : p.val ≠ 2 := by omega
  let f (x : ZMod p.val) := quadraticChar (ZMod p.val) (x^3 - (n : ZMod p.val)^2*x)
  have hchi : quadraticChar (ZMod p.val) (-1) = -1 := by
    simpa only [legendreSym, Int.cast_neg, Int.cast_one] using
      ((legendreSym.at_neg_one hp').trans (ZMod.χ₄_nat_three_mod_four hp))
  have hf (x : ZMod p.val) : f (-x) = - f x := by
    dsimp only [f]
    rw [show (-x)^3-(n : ZMod p.val)^2 * (-x) = (-1)*(x^3-(n : ZMod p.val)^2*x) by ring,
      map_mul, hchi, neg_one_mul]
  have hsum := Equiv.sum_comp (Equiv.neg (ZMod p.val)) f
  change (∑ x : ZMod p.val, f (-x)) = ∑ x : ZMod p.val, f x at hsum
  simp_rw [hf, Finset.sum_neg_distrib] at hsum
  have ht := OMA.R_CongruentNumber_Tunnell_even_R1.trace_eq_neg_sum n p hp'
  change _ = - ∑ x : ZMod p.val, f x at ht
  omega

end TunnellInert

/- Identification of the coefficient of the Gaussian Hecke theta series at every odd prime. -/

namespace TunnellSplitMass

open Finset TunnellGaussian

lemma trace_primary {a b : ℤ} (h : (8 : ℤ) ∣ a^2 + b^2 + 1 - 2*a) :
    Primary (⟨a,b⟩ : GaussianInt) := by
  rw [primary_iff]
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h
  push_cast at hh
  have finite_check : ∀ x y : ZMod 8, x^2 + y^2 + 1 - 2*x = 0 →
      y.val % 2 = 0 ∧ (x.val + y.val) % 4 = 1 := by decide
  obtain ⟨he,hr⟩ := finite_check _ _ hh
  have ha := ZMod.val_intCast (n := 8) a
  have hb := ZMod.val_intCast (n := 8) b
  change b%2 = 0 ∧ (a+b)%4 = 1
  omega

lemma primary_trace_exists (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val % 4 = 1) :
    ∃ z ∈ shell p.val,
      (p.val : ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
        xy.2^2 = xy.1^3 - xy.1)).card = 2 * z.re := by
  obtain ⟨a,b,ht,hn⟩ := TunnellSplit.split_trace_norm p hp
  have hd := TunnellCoates.eight_dvd_points_base p.val hp
  have h : (8 : ℤ) ∣ a^2 + b^2 + 1 - 2*a := by
    obtain ⟨k,hk⟩ := hd
    refine ⟨k, ?_⟩
    rw [hn, ← ht]
    omega
  have hz : (⟨a,b⟩ : GaussianInt).norm = p.val := by rw [norm_sq]; exact hn
  exact ⟨⟨a,b⟩, mem_shell.mpr ⟨trace_primary h, by simp [hz]⟩, ht⟩

theorem trace_mass_split (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val % 4 = 1) :
    (mass p.val).re = (p.val : ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - xy.1)).card := by
  classical
  obtain ⟨z,hz,ht⟩ := primary_trace_exists p hp
  unfold mass
  rw [shell_split_prime p.property hz, sum_pair (distinct_star_of_prime p.property (mem_shell.mp hz).2), ht]
  change z.re + z.re = 2 * z.re
  ring

lemma shell_mod_four {n : ℕ} (hn : n % 4 = 3) : shell n = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hh := GaussianInt.abs_natCast_norm z
  rw [(mem_shell.mp hz).2, norm_sq] at hh
  have h : ((n : ℕ) : ZMod 4) = 3 := by
    apply ZMod.val_injective 4
    rw [ZMod.val_natCast, hn]
    decide
  have hx := congrArg (fun k : ℤ => (k : ZMod 4)) hh
  push_cast at hx
  rw [h] at hx
  have no_three : ∀ a b : ZMod 4, (3 : ZMod 4) ≠ a^2 + b^2 := by decide
  exact no_three _ _ hx

theorem trace_mass_odd (p : Nat.Primes) (hp : p.val ≠ 2) :
    letI : NeZero p.val := ⟨p.property.ne_zero⟩
    (mass p.val).re = (p.val : ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
      xy.2^2 = xy.1^3 - xy.1)).card := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have ho := p.property.odd_of_ne_two hp
  rcases (show p.val % 4 = 1 ∨ p.val % 4 = 3 by obtain ⟨k,hk⟩ := ho; omega) with h|h
  · exact trace_mass_split p h
  · have ht := TunnellInert.inert_trace_zero 1 p h
    simp only [Nat.cast_one, one_pow, one_mul] at ht
    simp [mass, shell_mod_four h, ht]

end TunnellSplitMass

/- Truncated unary theta identities imply the signed two-dimensional lattice expansion. -/

namespace TunnellJacobiFiniteBridge

open Polynomial Finset

def H1 : Prop := ∀ d : ℕ,
  (X : ℤ[X])^(d+1) ∣
    (∏ t ∈ Icc 1 d, (1-X^(8*t)))^3 -
    ∑ k ∈ range (d+1), C ((-1:ℤ)^k * (2*k+1)) * X^(8*(k+1).choose 2)

def H2 : Prop := ∀ d : ℕ,
  (X : ℤ[X])^(d+1) ∣
    (∏ t ∈ Icc 1 d, (1-X^(4*t)))^2 -
    (∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), C (j.negOnePow:ℤ) * X^(4*j.natAbs^2)) *
    ∏ t ∈ Icc 1 d, (1-X^(8*t))

lemma exponent_eq (k : ℕ) : 1+8*(k+1).choose 2 = (2*k+1)^2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

lemma unary_to_lattice (h₁ : H1) (h₂ : H2) (d : ℕ) :
    (X * ∏ t ∈ Icc 1 d, ((1-(X:ℤ[X])^(4*t))^2 * (1-X^(8*t))^2)).coeff d =
      ∑ k ∈ range (d+1), ∑ j ∈ Icc (-(d:ℤ)) (d:ℤ),
        if (2*k+1)^2 + 4*j.natAbs^2 = d then
            (((k:ℤ)+j).negOnePow : ℤ) * (2*k+1) else 0 := by
  let f (a : ℕ) : ℤ[X] := ∏ t ∈ Icc 1 d, (1-X^(a*t))
  let c (k : ℕ) : ℤ[X] := C ((-1:ℤ)^k*(2*k+1))*X^(8*(k+1).choose 2)
  let g (j : ℤ) : ℤ[X] := C (j.negOnePow:ℤ)*X^(4*j.natAbs^2)
  let S := ∑ k ∈ range (d+1), c k
  let T := ∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), g j
  have hc : X^(d+1) ∣ f 8 ^ 3 - S := h₁ d
  have ht : X^(d+1) ∣ f 4 ^ 2 - T * f 8 := h₂ d
  have hd : X^(d+1) ∣ X*f 4^2*f 8^2 - X*S*T := by
    have h := dvd_add (ht.mul_left (X * f 8 ^2)) (hc.mul_left (X*T))
    convert h using 1
    ring
  have he := X_pow_dvd_iff.1 hd d (by omega)
  rw [coeff_sub,sub_eq_zero] at he
  have hf : (∏ t ∈ Icc 1 d, ((1-(X:ℤ[X])^(4*t))^2 * (1-X^(8*t))^2)) =
      f 4^2 * f 8^2 := by simp only [f, prod_mul_distrib, prod_pow]
  rw [hf, ←mul_assoc, he]
  have hm (k : ℕ) (j : ℤ) : (X*c k*g j).coeff d =
    if (2*k+1)^2+4*j.natAbs^2=d then (((k:ℤ)+j).negOnePow:ℤ)*(2*k+1) else 0 := by
    have hp : X*c k*g j = C (((-1:ℤ)^k*(2*k+1))*(j.negOnePow:ℤ)) *
      X^(1+8*(k+1).choose 2+4*j.natAbs^2) := by
      simp only [c,g,map_mul,pow_add,pow_one]
      ring
    rw [hp,exponent_eq,coeff_C_mul_X_pow]
    simp only [Int.negOnePow_add, Units.val_mul, Int.coe_negOnePow_natCast]
    split_ifs <;> first | contradiction | (exfalso; solve_by_elim [Eq.symm]) | ring
  simp only [S,T,mul_sum,sum_mul,finsetSum_coeff,hm]
  exact Finset.sum_comm

end TunnellJacobiFiniteBridge

/- The signed lattice parametrization of the primary Gaussian integers of a fixed norm. -/

namespace TunnellEtaLattice

open Finset TunnellGaussian

def weight (k : ℕ) (j : ℤ) : ℤ := (Int.negOnePow ((k:ℤ)+j) : ℤ) * (2*(k:ℤ)+1)

def encode (k : ℕ) (j : ℤ) : GaussianInt := ⟨weight k j, 2*j⟩

lemma weight_cases (k : ℕ) (j : ℤ) :
    (weight k j = 2*(k:ℤ)+1 ∧ ((k:ℤ)+j)%2=0) ∨
    (weight k j = -(2*(k:ℤ)+1) ∧ ((k:ℤ)+j)%2=1) := by
  rcases Int.even_or_odd ((k:ℤ)+j) with h|h
  · left; rw [weight, Int.negOnePow_even _ h]; simp only [Units.val_one,one_mul,true_and]
    obtain ⟨v,hv⟩ := h; omega
  · right; rw [weight, Int.negOnePow_odd _ h]; simp only [Units.val_one,one_mul,Units.val_neg,neg_mul,true_and]
    obtain ⟨v,hv⟩ := h; omega

lemma primary_encode (k : ℕ) (j : ℤ) : Primary (encode k j) := by
  rw [primary_iff]
  change (2*j)%2=0 ∧ (weight k j+2*j)%4=1
  rcases weight_cases k j with ⟨h,he⟩|⟨h,he⟩ <;> omega

lemma norm_encode (k : ℕ) (j : ℤ) :
    (encode k j).norm = (2*(k:ℤ)+1)^2 + 4*j^2 := by
  rw [norm_sq]
  change (weight k j)^2+(2*j)^2 = _
  rcases weight_cases k j with ⟨h,-⟩|⟨h,-⟩ <;> rw [h] <;> ring

lemma abs_encode (k : ℕ) (j : ℤ) : (encode k j).re.natAbs = 2*k+1 := by
  change (weight k j).natAbs = _
  have hc : 2*(k:ℤ)+1 = ((2*k+1:ℕ):ℤ) := by push_cast; ring
  rcases weight_cases k j with ⟨h,-⟩|⟨h,-⟩ <;> rw [h,hc] <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

lemma encode_injective {k l : ℕ} {j h : ℤ} (e : encode k j = encode l h) : k=l ∧ j=h := by
  have a := congrArg (fun z : GaussianInt => z.re.natAbs) e
  simp only [abs_encode] at a
  have b := congrArg Zsqrtd.im e
  change 2*j=2*h at b
  omega

lemma encode_surjective {z : GaussianInt} (hz : Primary z) :
    ∃ k : ℕ, ∃ j : ℤ, encode k j = z := by
  obtain ⟨hi,hr⟩ := (primary_iff _).mp hz
  let k := z.re.natAbs/2
  let j := z.im/2
  have hj : 2*j = z.im := by dsimp [j]; omega
  have habs : z.re = (z.re.natAbs : ℤ) ∨ z.re = -(z.re.natAbs : ℤ) := Int.natAbs_eq z.re
  have hk : z.re.natAbs = 2*k+1 := by dsimp [k]; omega
  refine ⟨k,j, ?_⟩
  have hp := (primary_iff _).mp (primary_encode k j)
  change _ ∧ (weight k j + 2*j)%4=1 at hp
  ext
  · change weight k j = z.re
    rcases weight_cases k j with ⟨he,-⟩|⟨he,-⟩ <;> omega
  · exact hj

def indices (n : ℕ) : Finset (ℕ × ℤ) :=
  ((range (n+1)) ×ˢ (Icc (-(n:ℤ)) (n:ℤ))).filter (fun kj =>
    (2*(kj.1:ℤ)+1)^2+4*kj.2^2 = n)

lemma indices_iff (n k : ℕ) (j : ℤ) :
    (k,j) ∈ indices n ↔ (2*(k:ℤ)+1)^2+4*j^2 = n := by
  simp only [indices,mem_filter,mem_product,mem_range,mem_Icc]
  refine ⟨And.right, fun h => ⟨⟨?_,?_,?_⟩,h⟩⟩
  · have hk : (k:ℤ) ≤ n := by nlinarith [sq_nonneg (k:ℤ),sq_nonneg j]
    omega
  · nlinarith [sq_nonneg (2*(k:ℤ)+1),sq_nonneg (2*j+1)]
  · nlinarith [sq_nonneg (2*(k:ℤ)+1),sq_nonneg (2*j-1)]

theorem mass_eq_lattice (n : ℕ) :
    (mass n).re = ∑ kj ∈ indices n, weight kj.1 kj.2 := by
  let re : GaussianInt →+ ℤ := { toFun := Zsqrtd.re, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change re (∑ z ∈ shell n, z) = _
  rw [map_sum]
  symm
  apply sum_bij (fun kj _ => encode kj.1 kj.2)
  · rintro ⟨k,j⟩ h
    have hn := (indices_iff _ _ _).mp h
    exact mem_shell.mpr ⟨primary_encode k j, by simp [norm_encode,hn]⟩
  · rintro ⟨k,j⟩ _ ⟨l,h⟩ _ e
    exact Prod.ext (encode_injective e).1 (encode_injective e).2
  · intro z h
    obtain ⟨hz,hn⟩ := mem_shell.mp h
    obtain ⟨k,j,e⟩ := encode_surjective hz
    have h := GaussianInt.abs_natCast_norm z
    rw [hn, ← e, norm_encode] at h
    exact ⟨(k,j),(indices_iff _ _ _).mpr h.symm,e⟩
  · intro _ _; rfl

end TunnellEtaLattice

/- Finite Gaussian binomials and their stabilized coefficients. -/

namespace TunnellQBin

open Polynomial Finset

variable {R : Type*} [CommRing R]

def choose (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => choose q n (k+1) + q^(n-k)*choose q n k

def fac (q : R) (n : ℕ) : R := ∏ i ∈ range n, (1-q^(i+1))

lemma choose_zero (q : R) (n : ℕ) : choose q n 0 = 1 := by cases n <;> rfl

lemma choose_above (q : R) {n k : ℕ} (h : n < k) : choose q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> first | rfl | omega
  | succ n ih =>
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [choose, ih (by omega), ih (by omega), mul_zero, add_zero]

lemma choose_self (q : R) (n : ℕ) : choose q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choose, choose_above _ (by omega), Nat.sub_self, pow_zero, one_mul, ih, zero_add]

lemma fac_succ (q : R) (n : ℕ) : fac q (n+1) = fac q n * (1-q^(n+1)) := prod_range_succ ..

theorem factorial_formula (q : R) (n k : ℕ) (hk : k ≤ n) :
    choose q n k * fac q k * fac q (n-k) = fac q n := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k=0 := Nat.eq_zero_of_le_zero hk
    simp [choose,fac]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [choose_zero,fac]
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    by_cases h : l=n
    · subst l; simp [choose_self,fac]
    have hl : l+1 ≤ n := by omega
    have ha := ih (l+1) hl
    have hb := ih l (by omega)
    have step : n - l = n - (l+1) + 1 := by omega
    have ep : n-l + (l+1) = n+1 := by omega
    rw [choose, Nat.succ_sub_succ_eq_sub]
    calc
      _ = (choose q n (l+1)*fac q (l+1)*fac q (n-(l+1))) * (1-q^(n-l)) +
          q^(n-l) * (choose q n l*fac q l*fac q (n-l)) * (1-q^(l+1)) := by
          have hfac : fac q (n-l) = fac q (n-(l+1))*(1-q^(n-l)) := by
            simpa only [← step] using fac_succ q (n-(l+1))
          rw [hfac,fac_succ q l]
          ring
      _ = _ := by rw [ha,hb,fac_succ,← ep,pow_add]; ring

noncomputable def product (q : R) (n : ℕ) : R[X] :=
  ∏ i ∈ range n, (1 + C (q^i) * X)

lemma product_coeff (q : R) (n k : ℕ) :
    (product q n).coeff k = q^(k.choose 2)*choose q n k := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp [product,choose,Polynomial.coeff_one]
  | succ n ih =>
    have e : product q (n+1) = product q n + C (q^n)*(product q n*X) := by
      rw [product,prod_range_succ]
      change product q n*(1+C (q^n)*X) = _
      ring
    rw [e,coeff_add,coeff_C_mul]
    cases k with
    | zero => simp [choose_zero,ih]
    | succ k =>
      rw [Polynomial.coeff_mul_X,ih,ih,choose]
      by_cases h : k ≤ n
      · have htri : (k+1).choose 2 = k.choose 2 + k := by rw [Nat.choose_succ_succ]; simp [add_comm]
        have hexp : n + k.choose 2 = (k+1).choose 2 + (n-k) := by omega
        rw [mul_add]
        congr 1
        rw [← mul_assoc,← pow_add,hexp,pow_add,mul_assoc]
      · rw [choose_above _ (by omega : n < k)]
        simp

theorem expansion (q : R) (n : ℕ) :
    (∏ j ∈ range n, (1 + C (q^j)*X)) =
      ∑ k ∈ range (n+1), C (q^(k.choose 2)*choose q n k) * X^k := by
  ext k
  change (product q n).coeff k = _
  rw [product_coeff, finsetSum_coeff]
  simp only [coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero]
  by_cases hk : k < n+1
  · simp [hk]
  · simp [hk, choose_above q (show n < k by omega)]

lemma fac_unit (q : R) (hq : IsNilpotent q) (n : ℕ) : IsUnit (fac q n) := by
  induction n with
  | zero => simp [fac]
  | succ n ih =>
    rw [fac_succ]
    exact ih.mul ((hq.pow_of_pos (by omega : n+1 ≠ 0)).isUnit_one_sub)

lemma fac_stable (q : R) {d : ℕ} (hq : q^(d+1) = 0) {n : ℕ} (hn : d ≤ n) :
    fac q n = fac q d := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc,fac_succ,show d+k+1 = d+1+k by omega,pow_add,hq,zero_mul,
      sub_zero,mul_one,ih (by omega)]

theorem choose_stable (q : R) {d : ℕ} (hq : q^(d+1) = 0) (n k : ℕ)
    (hk : k ≤ n) (hd : d ≤ k) (ht : d ≤ n-k) : choose q n k * fac q d = 1 := by
  apply (fac_unit q ⟨_,hq⟩ d).mul_left_injective
  have h := factorial_formula q n k hk
  rw [fac_stable q hq hd,fac_stable q hq ht,fac_stable q hq (hd.trans hk)] at h
  simpa only [one_mul] using h

theorem map_choose {S : Type*} [CommRing S] (f : R →+* S) (q : R) (n k : ℕ) :
    f (choose q n k) = choose (f q) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [choose]
  | succ n ih => cases k <;> simp [choose,ih]

theorem expansion_eval (q t : R) (n : ℕ) :
    (∏ j ∈ range n, (1 + q^j*t)) =
      ∑ k ∈ range (n+1), (q^(k.choose 2)*choose q n k)*t^k := by
  have h := congrArg (Polynomial.evalRingHom t) (expansion q n)
  simpa only [map_prod,map_sum,map_add,map_one,map_mul,map_pow,coe_evalRingHom,eval_C,eval_X] using h

end TunnellQBin

/- A finite balanced specialization of the Gaussian binomial theorem. -/

namespace TunnellBalanced

open Finset
variable {K : Type*} [Field K]

private lemma normalizer (t : K) (N : ℕ) :
    ∏ i ∈ range N, (-t^(2*i+1)) = (-1 : K)^N * t^(N^2) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, show (n+1)^2 = n^2 + (2*n+1) by ring, pow_add, pow_succ (-1 : K)]
    ring

private lemma product_side (t : K) (ht : t ≠ 0) (N : ℕ) :
    ((-1 : K)^N * t^(N^2)) *
        (∏ j ∈ range (2*N), (1+(t^2)^j * (-t^(1-2*(N:ℤ))))) =
      ∏ i ∈ range N, (1-t^(2*i+1))^2 := by
  let F (j : ℕ) := 1 - t^(2*(j:ℤ)+1-2*(N:ℤ))
  have he (j : ℕ) : 1+(t^2)^j*(-t^(1-2*(N:ℤ))) = F j := by
    dsimp [F]
    rw [← pow_mul, ← zpow_natCast t (2*j), mul_neg, ← zpow_add₀ ht, ← sub_eq_add_neg]
    congr 2
    push_cast
    ring
  have hs : (∏ j ∈ range (2*N), F j) =
      (∏ j ∈ range N, F (N-1-j)) * ∏ j ∈ range N, F (N+j) := by
    rw [Finset.prod_range_reflect, ←prod_range_add, two_mul]
  simp only [he]
  rw [hs, ←normalizer, ←mul_assoc, ←prod_mul_distrib, ←prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  have hneg : (2*((N-1-i:ℕ):ℤ)+1-2*(N:ℤ)) = -((2*i+1:ℕ):ℤ) := by omega
  have hpos : (2*((N+i:ℕ):ℤ)+1-2*(N:ℤ)) = ((2*i+1:ℕ):ℤ) := by omega
  dsimp only [F]
  rw [hneg, hpos, zpow_neg, zpow_natCast]
  field_simp
  ring

private lemma triangular (k : ℕ) : 2*k.choose 2 + k = k^2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

private lemma power_side (t : K) (ht : t ≠ 0) (N k : ℕ) :
    t^(N^2) * (t^2)^k.choose 2 * (t^(1-2*(N:ℤ)))^k
      = t^(((k:ℤ)-(N:ℤ)).natAbs^2) := by
  rw [← pow_mul, ← zpow_natCast t (N^2), ← zpow_natCast t (2*k.choose 2),
      ← zpow_natCast (t^(1-2*(N:ℤ))) k, ← zpow_mul, ← zpow_add₀ ht, ← zpow_add₀ ht,
      ← zpow_natCast t (((k:ℤ)-(N:ℤ)).natAbs^2)]
  congr 1
  push_cast
  rw [sq_abs]
  have h : (2:ℤ)*(k.choose 2:ℕ) + (k:ℤ) = (k:ℤ)^2 := by exact_mod_cast triangular k
  linarith only [h]

private theorem balanced_field (t : K) (ht : t ≠ 0) (N : ℕ) :
    (∏ i ∈ range N, (1-t^(2*i+1))^2) =
    ∑ k ∈ range (2*N+1), ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : K) *
        t ^ (((k:ℤ)-(N:ℤ)).natAbs ^ 2) * TunnellQBin.choose (t^2) (2*N) k := by
  rw [←product_side t ht N, TunnellQBin.expansion_eval, Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  have hs : ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : K) =
      (-1:K)^k * (-1:K)^N := by
    rw [Int.negOnePow_sub, Units.val_mul, Int.cast_mul, Int.cast_negOnePow_natCast,
      Int.cast_negOnePow_natCast]
  rw [hs, ← power_side t ht, neg_eq_neg_one_mul (t^(1-2*(N:ℤ))), mul_pow]
  ring

open Polynomial in
theorem balanced {R : Type*} [CommRing R] (t : R) (N : ℕ) :
    (∏ i ∈ range N, (1-t^(2*i+1))^2) =
    ∑ k ∈ range (2*N+1), ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : R) *
        t ^ (((k:ℤ)-(N:ℤ)).natAbs^2) * TunnellQBin.choose (t^2) (2*N) k := by
  let x : ℤ[X] := X
  let f := algebraMap ℤ[X] (FractionRing ℤ[X])
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have hx : f x ≠ 0 := by
    rw [← map_zero f]
    exact fun h ↦ Polynomial.X_ne_zero (hf h)
  have hpoly : (∏ i ∈ range N, (1-x^(2*i+1))^2) =
      ∑ k ∈ range (2*N+1), ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : ℤ[X]) *
        x ^ (((k:ℤ)-(N:ℤ)).natAbs^2) * TunnellQBin.choose (x^2) (2*N) k := by
    apply hf
    simpa only [map_prod, map_sum, map_pow, map_sub, map_one, map_mul, map_intCast,
      TunnellQBin.map_choose] using balanced_field (f x) hx N
  let g := Polynomial.eval₂RingHom (Int.castRingHom R) t
  have hxt : g x = t := by simp [g,x]
  simpa only [map_prod, map_sum, map_pow, map_sub, map_one, map_mul, map_intCast,
    TunnellQBin.map_choose,hxt] using congrArg g hpoly

end TunnellBalanced

/- Finite Jacobi cubic identity by differentiating the Gaussian binomial theorem. -/

namespace TunnellCubicFinite

open Finset Polynomial TunnellQBin
open LaurentPolynomial hiding C

abbrev L := LaurentPolynomial ℤ
noncomputable abbrev q : L := T 1

lemma fac_ne (n : ℕ) : fac q n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj he
  have e : (1 : ℤ[X]) = X^(j+1) := by
    apply Polynomial.toLaurent_injective
    simpa only [map_one,map_pow,toLaurent_X,q] using sub_eq_zero.mp he
  have c := congrArg (fun p : ℤ[X] => p.coeff 0) e
  simp at c

lemma choose_symm (m k : ℕ) (hk : k ≤ m) :
    choose q m k = choose q m (m-k) := by
  have a := factorial_formula q m k hk
  have b := factorial_formula q m (m-k) (by omega)
  rw [Nat.sub_sub_self hk, mul_right_comm] at b
  exact mul_right_cancel₀ (fac_ne k) (mul_right_cancel₀ (fac_ne (m-k)) (a.trans b.symm))

lemma derivative_monom {S : Type*} [CommRing S] (t a : S) (k : ℕ) :
    t * (derivative (C a * X^k)).eval t = (k:S)*a*t^k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [derivative_C_mul, derivative_X_pow_succ]
    simp only [eval_mul,eval_C,eval_pow,eval_X,pow_succ,Nat.cast_succ]
    ring

lemma weighted_expansion (n : ℕ) (t : L) :
    t * ((∏ j ∈ range n, (1 + C (q^j)*X)).derivative.eval t) =
      ∑ k ∈ range (n+1), (k:L)*(q^(k.choose 2)*choose q n k)*t^k := by
  rw [expansion, map_sum, eval_finsetSum, mul_sum]
  exact sum_congr rfl fun k _ => derivative_monom _ _ _

lemma reflected_fac (n : ℕ) :
    ∏ i ∈ range n, (1 - (T (-((i:ℤ)+1)) : L)) =
      (-1)^n * T (-((n+1).choose 2 : ℤ)) * fac q n := by
  induction n with
  | zero => simp [fac]
  | succ n ih =>
    rw [prod_range_succ, ih, fac_succ, pow_succ]
    have hp : (1 - (T (-((n:ℤ)+1)) : L)) =
      -T (-((n:ℤ)+1))*(1-q^(n+1)) := by
      simp only [q,T_pow,mul_one,Nat.cast_add,Nat.cast_one,mul_sub,neg_mul,← T_add,neg_add_cancel,T_zero]
      ring
    rw [hp]
    have he : ((n+1+1).choose 2 : ℤ) = ((n+1).choose 2 : ℤ) + (n+1:ℕ) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
      ring
    have ht : (T (-((n+1+1).choose 2:ℤ)) : L) =
        T (-((n+1).choose 2:ℤ)) * T (-((n:ℤ)+1)) := by
      rw [← T_add,he,Nat.cast_add,Nat.cast_one]
      congr 1
      ring
    rw [ht]
    ring

lemma weighted_root (n : ℕ) :
    let t : L := -T (-(n:ℤ))
    t * ((∏ j ∈ range (2*n+1), (1 + C (q^j)*X)).derivative.eval t) =
      (-1)^(n+1) * T (-((n+1).choose 2 : ℤ)) * fac q n ^ 2 := by
  dsimp only
  let t : L := -T (-(n:ℤ))
  let f (j : ℕ) : L[X] := 1+C (q^j)*X
  change t*((∏ j ∈ range (2*n+1), f j).derivative.eval t) = _
  have ev (j : ℕ) : (f j).eval t = 1-T ((j:ℤ)-n) := by
    simp only [f,t,q,eval_add,eval_one,eval_mul,eval_C,eval_X,T_pow,mul_one,mul_neg,← T_add,sub_eq_add_neg]
  have ht : t*q^n = -1 := by
    simp only [t,q,T_pow,mul_one,neg_mul,← T_add,neg_add_cancel,T_zero]
  have center : (f n).eval t = 0 := by simp [ev]
  have dc : (f n).derivative.eval t = q^n := by simp [f]
  have left : ∏ j ∈ range n, (f j).eval t =
      (-1)^n*T (-((n+1).choose 2 : ℤ))*fac q n := by
    have hr := prod_range_reflect (fun j => (f j).eval t) n
    rw [← hr]
    convert reflected_fac n using 1
    apply prod_congr rfl
    intro i hi
    rw [ev]
    congr 2
    have := mem_range.mp hi
    omega
  have right : ∏ j ∈ range n, (f (n+1+j)).eval t = fac q n := by
    apply prod_congr rfl
    intro j _
    rw [ev]
    simp [q,T_pow]
    congr 1
    omega
  rw [show 2*n+1=n+1+n by omega, prod_range_add,prod_range_succ,derivative_mul,derivative_mul]
  simp only [eval_add,eval_mul,eval_prod,center,mul_zero,zero_mul,zero_add,add_zero,dc,left,right]
  calc _ = (t*q^n)*((-1)^n*T (-((n+1).choose 2 : ℤ)) * fac q n ^ 2) := by ring
       _ = _ := by rw [ht,pow_succ]; ring

lemma double_choose (m : ℕ) : 2*(m.choose 2 : ℤ) = (m:ℤ)*(m-1:ℤ) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    nlinarith

noncomputable def weight (n r : ℕ) : L :=
  (-1)^(n+1)*T ((n+1).choose 2 : ℤ) *
    ((r:L)*(q^(r.choose 2)*choose q (2*n+1) r)*(-T (-(n:ℤ)))^r)

lemma weight_clean (n r : ℕ) : weight n r =
    (-1)^(n+1+r)*T (((n+1).choose 2 : ℤ) + (r.choose 2:ℤ) - (n:ℤ)*r) *
      (r:L) * choose q (2*n+1) r := by
  simp only [weight,q,neg_pow (T (-(n:ℤ)) : L),T_pow,mul_one,pow_add,sub_eq_add_neg,T_add,
    mul_neg, mul_comm (r:ℤ) (n:ℤ)]
  ring

lemma weight_pair (n k : ℕ) (hk : k ≤ n) :
    weight n (n-k) + weight n (n+1+k) =
      (-1)^k*(2*k+1:L)*q^((k+1).choose 2)*choose q (2*n+1) (n+1+k) := by
  have hc := choose_symm (2*n+1) (n-k) (by omega)
  rw [show 2*n+1-(n-k)=n+1+k by omega] at hc
  have hsub : ((n-k:ℕ):ℤ) = (n:ℤ)-k := Nat.cast_sub hk
  have eL : ((n+1).choose 2:ℤ) + ((n-k).choose 2:ℤ) - n*(n-k:ℕ) = ((k+1).choose 2:ℤ) := by
    have a := double_choose (n+1)
    have b := double_choose (n-k)
    have c := double_choose (k+1)
    rw [hsub] at b ⊢
    push_cast at a c
    nlinarith
  have eR : ((n+1).choose 2:ℤ) + ((n+1+k).choose 2:ℤ) - n*(n+1+k:ℕ) = ((k+1).choose 2:ℤ) := by
    have a := double_choose (n+1)
    have b := double_choose (n+1+k)
    have c := double_choose (k+1)
    push_cast at a b c ⊢
    nlinarith
  have sign (a b : ℕ) : (-1:L)^(a+a+b) = (-1)^b := by
    rw [← two_mul, pow_add,pow_mul]
    norm_num
  rw [weight_clean,weight_clean,eL,eR, hc,
    show n+1+(n-k)=(n-k)+(n-k)+(k+1) by omega, sign,
    show n+1+(n+1+k)=(n+1)+(n+1)+k by omega,sign,pow_succ]
  rw [show (q^((k+1).choose 2):L)=T ((k+1).choose 2:ℤ) by simp only [q,T_pow,mul_one]]
  rw [Nat.cast_sub hk]
  push_cast
  ring

theorem cubic_laurent (n : ℕ) : fac q n ^ 2 =
    ∑ k ∈ range (n+1), (-1)^k * (2*k+1:L) * q^((k+1).choose 2) *
      choose q (2*n+1) (n+1+k) := by
  have h := (weighted_root n).symm.trans (weighted_expansion (2*n+1) (-T (-(n:ℤ))))
  have h' := congrArg (fun u:L => (-1)^(n+1)*T ((n+1).choose 2:ℤ) * u) h
  rw [mul_sum] at h'
  change _ = ∑ r ∈ range (2*n+1+1), weight n r at h'
  have hunit (a:ℕ) (b:ℤ) : ((-1)^a * T b:L) * ((-1)^a * T (-b)*fac q n^2) = fac q n^2 := by
    calc _ = (-1)^(a+a) * (T b*T (-b)) * fac q n^2 := by rw [pow_add]; ring
         _ = _ := by rw [← two_mul,pow_mul,← T_add,add_neg_cancel,T_zero]; norm_num
  rw [hunit,show 2*n+1+1=(n+1)+(n+1) by omega,sum_range_add] at h'
  rw [h',← sum_range_reflect (weight n) (n+1), ←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  have hk' := mem_range.mp hk
  simpa only [Nat.add_sub_cancel] using weight_pair n k (by omega)

end TunnellCubicFinite

/- Specialize the finite Jacobi identity from the universal Laurent polynomial. -/

namespace TunnellCubicFinite

open Polynomial Finset TunnellQBin

theorem cubic {R : Type*} [CommRing R] (q : R) (N : ℕ) :
    fac q N ^ 2 = ∑ k ∈ range (N+1), (-1)^k * (2*k+1:R) *
      q^((k+1).choose 2) * TunnellQBin.choose q (2*N+1) (N+1+k) := by
  have hp : fac (X : ℤ[X]) N ^ 2 = ∑ k ∈ range (N+1), (-1)^k * (2*k+1:ℤ[X]) *
      X^((k+1).choose 2) * TunnellQBin.choose (X : ℤ[X]) (2*N+1) (N+1+k) := by
    apply Polynomial.toLaurent_injective
    simpa only [fac, map_pow, map_prod, map_sub, map_one, map_sum, map_mul, map_add,
      map_neg, map_ofNat, map_natCast, map_choose, toLaurent_X] using cubic_laurent N
  let g := Polynomial.eval₂RingHom (Int.castRingHom R) q
  have hx : g X = q := by simp [g]
  simpa only [fac, map_pow, map_prod, map_sub, map_one, map_sum, map_mul, map_add,
    map_neg, map_ofNat, map_natCast, map_choose, hx] using congrArg g hp

end TunnellCubicFinite

/- Truncate the centered finite Jacobi identities at arbitrary degree. -/

namespace TunnellTruncated

open TunnellQBin Polynomial Finset

variable {R : Type*} [CommRing R]

lemma triangle_ge (k : ℕ) : k ≤ (k+1).choose 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ,Nat.choose_one_right]; omega

theorem cubic_stabilized (q : R) (d N : ℕ) (hN : 2*d ≤ N) (hq : q^(d+1)=0)
    (h : fac q N ^ 2 = ∑ k ∈ range (N+1),
      ((-1:R)^k * (2*(k:R)+1)) * q^((k+1).choose 2) * choose q (2*N+1) (N+1+k)) :
    fac q d ^ 3 = ∑ k ∈ range (d+1), ((-1:R)^k * (2*(k:R)+1)) * q^((k+1).choose 2) := by
  let f (k : ℕ) := ((-1:R)^k*(2*(k:R)+1))*q^((k+1).choose 2)
  change _ = ∑ k ∈ range (d+1), f k
  change fac q N ^ 2 = ∑ k ∈ range (N+1), f k * choose q (2*N+1) (N+1+k) at h
  have htail (k : ℕ) (hk : d < k) : f k = 0 := by
    have hpow := pow_eq_zero_of_le (show d+1 ≤ (k+1).choose 2 by have := triangle_ge k; omega) hq
    simp [f,hpow]
  have hs : ∑ k ∈ range (N+1), (f k * choose q (2*N+1) (N+1+k))*fac q d =
      ∑ k ∈ range (d+1), (f k * choose q (2*N+1) (N+1+k))*fac q d := by
    symm
    apply sum_subset (range_mono (by omega))
    intro k _ hk
    simp only [mem_range,not_lt] at hk
    rw [htail k (by omega),zero_mul,zero_mul]
  rw [fac_stable q hq (n:=N) (by omega)] at h
  calc
    _ = (fac q d)^2 * fac q d := by ring
    _ = _ := by
      rw [h,sum_mul,hs]
      apply sum_congr rfl
      intro k hk
      rw [mem_range] at hk
      rw [mul_assoc,choose_stable q hq _ _ (by omega) (by omega) (by omega),mul_one]

lemma map_fac {S : Type*} [CommRing S] (f : R →+* S) (q : R) (n : ℕ) :
    f (fac q n) = fac (f q) n := by simp [fac]

lemma poly_fac (s n : ℕ) :
    fac ((X : ℤ[X])^s) n = ∏ t ∈ Icc 1 n, (1-X^(s*t)) := by
  induction n with
  | zero => simp [fac]
  | succ n ih =>
    rw [fac_succ,ih,prod_Icc_succ_top (by omega : 1 ≤ n+1),← pow_mul]

noncomputable def trunc (d : ℕ) := AdjoinRoot.mk ((X : ℤ[X])^(d+1))

lemma nilpotent_trunc (d : ℕ) : (trunc d X)^(d+1)=0 := by
  rw [← map_pow]
  exact AdjoinRoot.mk_self

lemma trunc_pow (d s : ℕ) (hs : s ≠ 0) : (trunc d (X^s))^(d+1)=0 := by
  rw [map_pow,← pow_mul,mul_comm,pow_mul,nilpotent_trunc,zero_pow hs]

theorem cubic_congruence
    (hc : ∀ N : ℕ, let q := (X:ℤ[X])^8
      fac q N ^ 2 = ∑ k ∈ range (N+1),
        ((-1:ℤ[X])^k * (2*(k:ℤ[X])+1)) * q^((k+1).choose 2) * choose q (2*N+1) (N+1+k)) :
    TunnellJacobiFiniteBridge.H1 := by
  intro d
  let t := trunc d
  let q := (X:ℤ[X])^8
  apply (AdjoinRoot.mk_eq_mk).mp
  change t _ = t _
  have he := congrArg t (hc (2*d))
  change t (fac q (2*d)^2) = t (∑ k ∈ range (2*d+1),
    ((-1:ℤ[X])^k * (2*(k:ℤ[X])+1)) * q^((k+1).choose 2)*choose q (2*(2*d)+1) (2*d+1+k)) at he
  simp only [map_pow,map_fac,map_sum,map_mul,map_add,map_neg,map_one,map_ofNat,map_natCast,map_choose] at he
  have hh := cubic_stabilized (t q) d (2*d) (by omega) (trunc_pow d 8 (by decide)) he
  rw [← poly_fac]
  simp only [map_pow,map_fac,map_sum,map_mul]
  apply hh.trans
  apply sum_congr rfl
  intro k _
  have hcst (a : ℤ) : t (C a) = (a : _) := by
    rw [show C a = (a : ℤ[X]) by simp, map_intCast]
  simp only [hcst]
  push_cast
  dsimp only [q]
  rw [map_pow,← pow_mul]

lemma fac_even_odd (t : R) (N : ℕ) :
    fac t (2*N) = fac (t^2) N * (∏ i ∈ range N, (1-t^(2*i+1))) := by
  induction N with
  | zero => simp [fac]
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega,fac_succ,fac_succ,ih,fac_succ,prod_range_succ,
      ← pow_mul,show 2*(n+1) = 2*n+1+1 by omega]
    ring

lemma centered_sum (N : ℕ) (f : ℤ → R) :
    ∑ k ∈ range (2*N+1), f ((k:ℤ)-(N:ℤ)) = ∑ j ∈ Icc (-(N:ℤ)) (N:ℤ), f j := by
  apply sum_bij (fun (k : ℕ) _ => (k:ℤ)-(N:ℤ))
  · intro k hk
    simp only [mem_range] at hk
    rw [mem_Icc]; omega
  · intro k _ l _ he; omega
  · intro j hj
    rw [mem_Icc] at hj
    refine ⟨(j+N).toNat,mem_range.mpr (by omega),by omega⟩
  · intro _ _; rfl

theorem theta_stabilized (t : R) (d N : ℕ) (hN : 2*d ≤ N) (ht : t^(d+1)=0)
    (h : (∏ i ∈ range N, (1-t^(2*i+1))^2) = ∑ k ∈ range (2*N+1),
      (((((k:ℤ)-(N:ℤ)).negOnePow : ℤ) : R) * t^(((k:ℤ)-(N:ℤ)).natAbs^2)) *
        choose (t^2) (2*N) k) :
    fac t d ^ 2 = (∑ j ∈ Icc (-(d:ℤ)) (d:ℤ),
      ((j.negOnePow : ℤ) : R) * t^(j.natAbs^2)) * fac (t^2) d := by
  let f (j : ℤ) := ((j.negOnePow : ℤ) : R) * t^(j.natAbs^2)
  change fac t d ^ 2 = (∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), f j) * fac (t^2) d
  have hq : (t^2)^(d+1)=0 := by rw [← pow_mul,mul_comm,pow_mul,ht,zero_pow (by decide : 2≠0)]
  have htail (j : ℤ) (hj : ¬ j ∈ Icc (-(d:ℤ)) (d:ℤ)) : f j = 0 := by
    have habs := Int.natAbs_eq j
    simp only [mem_Icc,not_and_or,not_le] at hj
    have hjd : d+1 ≤ j.natAbs := by omega
    have hd : d+1 ≤ j.natAbs^2 := by nlinarith [Nat.le_mul_self j.natAbs]
    simp [f,pow_eq_zero_of_le hd ht]
  have hside : fac t d ^ 2 = (∏ i ∈ range N, (1-t^(2*i+1))^2) * fac (t^2) d ^ 2 := by
    have hfac := fac_even_odd t N
    rw [fac_stable t ht (n:=2*N) (by omega),fac_stable (t^2) hq (n:=N) (by omega)] at hfac
    rw [hfac,prod_pow]; ring
  rw [hside,h,pow_two (fac (t^2) d),← mul_assoc]
  congr 1
  rw [sum_mul]
  calc
    _ = ∑ k ∈ range (2*N+1), f ((k:ℤ)-(N:ℤ)) := by
      apply sum_congr rfl
      intro k hk
      change f ((k:ℤ)-N) * _ * _ = _
      by_cases hj : ((k:ℤ)-N) ∈ Icc (-(d:ℤ)) (d:ℤ)
      · rw [mem_Icc] at hj
        rw [mul_assoc,choose_stable (t^2) hq _ _ (by omega) (by omega) (by omega),mul_one]
      · rw [htail _ hj,zero_mul,zero_mul]
    _ = _ := by
      rw [centered_sum]
      symm
      apply sum_subset (fun j hj => ?_) (fun j _ hj => htail j hj)
      simp only [mem_Icc] at hj ⊢
      omega

theorem theta_congruence
    (hc : ∀ (d N : ℕ), let t := trunc d (X^4)
      (∏ i ∈ range N, (1-t^(2*i+1))^2) = ∑ k ∈ range (2*N+1),
        (((((k:ℤ)-(N:ℤ)).negOnePow : ℤ) : _) * t^(((k:ℤ)-(N:ℤ)).natAbs^2)) *
          choose (t^2) (2*N) k) : TunnellJacobiFiniteBridge.H2 := by
  intro d
  apply (AdjoinRoot.mk_eq_mk).mp
  change trunc d _ = trunc d _
  have he := theta_stabilized (trunc d (X^4)) d (2*d) (by omega) (trunc_pow d 4 (by decide)) (hc d (2*d))
  rw [← poly_fac,← poly_fac]
  have hh : trunc d (X^8) = (trunc d (X^4))^2 := by rw [← map_pow,← pow_mul]
  simp only [map_pow,map_mul,map_sum,map_fac] at he ⊢
  rw [he]
  congr 1
  · apply sum_congr rfl
    intro j _
    have hC : trunc d (C (j.negOnePow : ℤ)) = ((j.negOnePow:ℤ) : _) := by
      rw [show C (j.negOnePow:ℤ) = ((j.negOnePow:ℤ):ℤ[X]) by simp, map_intCast]
    rw [hC,← pow_mul]
  · rw [← pow_mul]

end TunnellTruncated

/- The arithmetic of the base congruent-number cusp form. -/

namespace TunnellArithmetic

open Polynomial Finset TunnellGaussian TunnellEtaLattice

theorem eta_eq_mass (h₁ : TunnellJacobiFiniteBridge.H1) (h₂ : TunnellJacobiFiniteBridge.H2) (n : ℕ) :
    (X * ∏ i ∈ Icc 1 n, ((1-(X:ℤ[X])^(4*i))^2*(1-X^(8*i))^2)).coeff n = (mass n).re := by
  rw [TunnellJacobiFiniteBridge.unary_to_lattice h₁ h₂, mass_eq_lattice]
  unfold indices
  rw [sum_filter,sum_product]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro j _
  have hsq : ((j.natAbs : ℤ)^2) = j^2 := by
    rcases Int.natAbs_eq j with h|h <;> nlinarith [congrArg (fun x : ℤ => x^2) h]
  have hiff : (2*k+1)^2+4*j.natAbs^2 = n ↔ (2*(k:ℤ)+1)^2+4*j^2 = n := by
    rw [← hsq]
    exact_mod_cast Iff.rfl
  simp only [hiff,weight]

end TunnellArithmetic

/- The absolutely convergent Gaussian lattice expansion of the twisted L-series. -/

namespace TunnellCMLSeries

open Finset TunnellGaussian

noncomputable def gaussianTerm (s : ℝ) (z : GaussianInt) : ℂ :=
  (z:ℂ) / (((z.norm.natAbs:ℝ)^s : ℝ):ℂ)

lemma norm_sq_real (z : GaussianInt) : (z.norm.natAbs:ℝ) = ‖(z:ℂ)‖^2 := by
  have h := congrArg Complex.re (GaussianInt.intCast_complex_norm z)
  simp only [Complex.intCast_re,Complex.ofReal_re,Complex.normSq_eq_norm_sq] at h
  rw [GaussianInt.natCast_natAbs_norm]
  exact h

lemma norm_term (s : ℝ) (hs : 3/2 < s) (z : GaussianInt) :
    ‖gaussianTerm s z‖ = ‖(z:ℂ)‖^(-(2*s-1)) := by
  rw [gaussianTerm,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _),norm_sq_real]
  by_cases h : z=0
  · subst z; simp [Real.zero_rpow (by linarith : 1-2*s≠0)]
  have hz := norm_pos_iff.mpr (GaussianInt.toComplex_eq_zero.not.mpr h)
  rw [← Real.rpow_natCast,← Real.rpow_mul hz.le,
    show -(2*s-1) = 1-(2:ℝ)*s by ring,Real.rpow_sub hz,Real.rpow_one]
  rfl

lemma summable_gaussianTerm (s : ℝ) (hs : 3/2 < s) : Summable (gaussianTerm s) := by
  let coords (z : GaussianInt) : Fin 2 → ℤ := ![z.re,z.im]
  have hi : Function.Injective coords := by
    intro z w h
    exact Zsqrtd.ext (congrFun h 0) (congrFun h 1)
  have h := (EisensteinSeries.summable_one_div_norm_rpow (show 2 < 2*s-1 by linarith)).comp_injective hi
  apply Summable.of_norm
  apply h.of_nonneg_of_le (fun z => norm_nonneg _)
  intro z
  rw [norm_term s hs]
  change _ ≤ ‖coords z‖^(-(2*s-1))
  have hc0 : coords 0 = 0 := by funext i; fin_cases i <;> rfl
  by_cases hz : z=0
  · subst z; rw [hc0]; simp
  have hpos : 0 < ‖coords z‖ := by
    apply norm_pos_iff.mpr
    exact fun he => hz (hi (he.trans hc0.symm))
  apply Real.rpow_le_rpow_of_nonpos hpos _ (by linarith)
  rw [EisensteinSeries.norm_eq_max_natAbs, Nat.cast_max,max_le_iff]
  constructor
  · have h := Complex.abs_re_le_norm (z:ℂ)
    simpa only [coords,Matrix.cons_val_zero,Nat.cast_max,← GaussianInt.intCast_re,
      Nat.cast_natAbs,Int.cast_abs] using h
  · have h := Complex.abs_im_le_norm (z:ℂ)
    simpa only [coords,Matrix.cons_val_one,Matrix.cons_val_zero,Nat.cast_max,← GaussianInt.intCast_im,
      Nat.cast_natAbs,Int.cast_abs] using h

noncomputable def twistSign (n m : ℕ) : ℤ := if Odd m then jacobiSym n m else 0

lemma norm_twist_le (n m : ℕ) : ‖((twistSign n m : ℤ):ℂ)‖ ≤ 1 := by
  unfold twistSign
  split
  · rcases jacobiSym.trichotomy (n:ℤ) m with h|h|h <;> simp [h]
  · simp

noncomputable def term (n : ℕ) (s : ℝ) (z : GaussianInt) : ℂ :=
  by classical exact if Primary z then (twistSign n z.norm.natAbs : ℂ) * gaussianTerm s z else 0

theorem summable_lattice (n : ℕ) (s : ℝ) (hs : 3/2<s) : Summable (term n s) := by
  classical
  apply Summable.of_norm
  apply (summable_gaussianTerm s hs).norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro z
  unfold term
  split
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_twist_le _ _)
  · simp

noncomputable def shellEquiv : (Σ n : ℕ, ↥(shell n)) ≃ {z : GaussianInt // Primary z} where
  toFun x := ⟨x.2.val,(mem_shell.mp x.2.property).1⟩
  invFun z := ⟨z.val.norm.natAbs, z.val, mem_shell.mpr ⟨z.property,rfl⟩⟩
  left_inv := by rintro ⟨n,z,hz⟩; obtain rfl := (mem_shell.mp hz).2; rfl
  right_inv := by intro z; rfl

noncomputable def latticeValue (n : ℕ) (s : ℝ) : ℂ :=
  ∑' z : {z : GaussianInt // Primary z},
    (twistSign n z.val.norm.natAbs : ℂ) * gaussianTerm s z.val

theorem shell_expansion (n : ℕ) (s : ℝ) (hs : 3/2<s) :
    HasSum (fun m : ℕ => (twistSign n m : ℂ) * ((mass m).re : ℂ) / ((m:ℂ)^(s:ℂ)))
      (latticeValue n s) := by
  classical
  let f (z : {z : GaussianInt // Primary z}) : ℂ :=
    (twistSign n z.val.norm.natAbs : ℂ) * gaussianTerm s z.val
  have hf : Summable f := by
    simpa only [Function.comp_def,f,term,Subtype.property,if_true] using (summable_lattice n s hs).subtype Primary
  have hsum : HasSum (fun c => f (shellEquiv c)) (latticeValue n s) :=
    shellEquiv.hasSum_iff.mpr hf.hasSum
  apply hsum.sigma
  intro m
  convert hasSum_fintype (fun v : ↥(shell m) => f (shellEquiv ⟨m,v⟩)) using 1
  have cst (v : ↥(shell m)) : f (shellEquiv ⟨m,v⟩) =
      (twistSign n m : ℂ) * ((v.val : GaussianInt) : ℂ) / (m:ℂ)^(s:ℂ) := by
    change _ * (_ / _) = _
    dsimp [f,shellEquiv,gaussianTerm]
    rw [(mem_shell.mp v.property).2,Complex.ofReal_cpow (Nat.cast_nonneg m)]
    push_cast
    ring
  simp only [cst,← Finset.sum_div,← Finset.mul_sum]
  have hc := (map_sum GaussianInt.toComplex (fun z => z) (shell m))
  change (↑(mass m) : ℂ) = ∑ z ∈ shell m, (z : ℂ) at hc
  have hre : (↑(mass m) : ℂ) = ((mass m).re : ℂ) := by simp [GaussianInt.toComplex_def,mass_real]
  rw [← hre,hc,← Finset.sum_attach (shell m) (fun z => (z : ℂ))]
  rfl

end TunnellCMLSeries

/- Euler product of the Gaussian Hecke L-series for the congruent-number twists. -/

namespace TunnellCMLSeries

open TunnellGaussian OMA.R_CongruentNumber_Tunnell_even_R1 Finset

lemma mass_one : mass 1 = 1 := by
  have e : shell 1 = {1} := by
    ext z
    rw [mem_shell,mem_singleton]
    constructor
    · rintro ⟨hz,hn⟩
      exact primary_unit_eq_one hz (Zsqrtd.norm_eq_one_iff.mp hn)
    · rintro rfl
      exact ⟨(primary_iff _).mpr (by decide),by simp⟩
  simp [mass,e]

lemma twistSign_one (n : ℕ) : twistSign n 1 = 1 := by simp [twistSign]

lemma twistSign_mul (n a b : ℕ) : twistSign n (a*b) = twistSign n a * twistSign n b := by
  by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [twistSign, Nat.odd_mul, ha, hb]
  exact jacobiSym.mul_right' _ (fun e => by simp [e] at ha) (fun e => by simp [e] at hb)

lemma twistSign_pow (n a k : ℕ) : twistSign n (a^k) = twistSign n a ^ k := by
  induction k with
  | zero => simp [twistSign_one]
  | succ k ih => rw [pow_succ,twistSign_mul,ih,pow_succ]

lemma twistSign_prime (n : ℕ) (p : Nat.Primes) [Fact p.val.Prime] (hp : p.val ≠ 2) :
    twistSign n p.val = quadraticChar (ZMod p.val) (n : ZMod p.val) := by
  have ho : Odd p.val := Nat.odd_iff.mpr (p.property.eq_two_or_odd.resolve_left hp)
  dsimp only [twistSign]
  rw [if_pos ho, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
  simp

lemma twistSign_bad (n : ℕ) (p : Nat.Primes) (hp : p.val ∣ 2*n) : twistSign n p.val = 0 := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  by_cases h : p.val = 2
  · simp [twistSign,h]
  · have hd : p.val ∣ n := (p.property.dvd_mul.mp hp).resolve_left
      (fun e => h ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp e))
    rw [twistSign_prime n p h, (ZMod.natCast_eq_zero_iff n _).mpr hd, quadraticChar_zero]

noncomputable def gaussCoeff (n m : ℕ) : ℂ := (twistSign n m:ℂ) * ((mass m).re : ℂ)

noncomputable def curveTrace (n : ℕ) (p : Nat.Primes) : ℤ :=
  letI : NeZero p.val := ⟨p.property.ne_zero⟩
  (p.val:ℤ) - (univ.filter (fun xy : ZMod p.val × ZMod p.val =>
    xy.2^2 = xy.1^3 - (n : ZMod p.val)^2 * xy.1)).card

lemma gaussCoeff_prime (n : ℕ) (p : Nat.Primes) (hp : ¬ p.val ∣ 2*n) :
    gaussCoeff n p.val = (curveTrace n p : ℂ) := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have hp2 : p.val ≠ 2 := fun h => hp (h ▸ dvd_mul_right _ _)
  have hpn : ¬ p.val ∣ n := fun h => hp (dvd_mul_of_dvd_right h 2)
  rw [gaussCoeff,twistSign_prime n p hp2,TunnellSplitMass.trace_mass_odd p hp2]
  simpa only [curveTrace,Int.cast_mul,Nat.cast_one,one_pow,one_mul] using congrArg (fun z : ℤ => (z:ℂ)) (traceOfFrobenius_twist n p hp2 hpn).symm

lemma gaussCoeff_rec (n : ℕ) (p : Nat.Primes) (hp : ¬ p.val ∣ 2*n) (k : ℕ) :
    gaussCoeff n (p.val^(k+2)) = gaussCoeff n p.val * gaussCoeff n (p.val^(k+1)) -
      (p.val : ℂ)*gaussCoeff n (p.val^k) := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have hp2 : p.val ≠ 2 := fun h => hp (h ▸ dvd_mul_right _ _)
  have hpn : ¬ p.val ∣ n := fun h => hp (dvd_mul_of_dvd_right h 2)
  have hs : ((twistSign n p.val : ℤ):ℂ)^2 = 1 := by
    rw [twistSign_prime n p hp2]; exact_mod_cast quadraticChar_sq_one ((ZMod.natCast_eq_zero_iff n p.val).not.mpr hpn)
  simp only [gaussCoeff,twistSign_pow,Int.cast_pow,coefficient_prime_power p.val p.property hp2 k,
    Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  linear_combination -((twistSign n p.val:ℂ)^k*p.val*((mass (p.val^k)).re:ℂ))*hs

theorem lattice_euler (n : ℕ) (s : ℝ) (hs : 3/2 < s) :
    HasProd (fun p : Nat.Primes => if p.val ∣ 2*n then (1:ℂ) else
      let T : ℂ := (p.val : ℂ)^(-(s:ℂ))
      (1-(curveTrace n p:ℂ)*T+(p.val:ℂ)*T^2)⁻¹) (latticeValue n s) := by
  classical
  let g (m : ℕ) := gaussCoeff n m / (m:ℂ)^(s:ℂ)
  have hsum : HasSum g (latticeValue n s) := shell_expansion n s hs
  have hfirst : gaussCoeff n 1 = 1 := by simp [gaussCoeff,mass_one,twistSign_one]
  have hf : g 1 = 1 := by simp [g,hfirst]
  have hz : g 0 = 0 := by simp [g, Complex.zero_cpow (by exact_mod_cast (by linarith : s≠0) : (s:ℂ)≠0)]
  have hm {a b : ℕ} (hc : a.Coprime b) : g (a*b) = g a * g b := by
    dsimp only [g,gaussCoeff]
    rw [twistSign_mul,coefficient_mul hc,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
    push_cast
    ring
  have h := EulerProduct.eulerProduct_hasProd hf (fun {_ _} h => hm h) hsum.summable.norm hz
  rw [hsum.tsum_eq] at h
  convert h using 2 with p
  let T := (p.val:ℂ)^(-(s:ℂ))
  let c (e : ℕ) := gaussCoeff n (p.val^e)*T^e
  have he (e : ℕ) : g (p.val^e) = c e := weight_prime_power p s e (gaussCoeff n (p.val^e))
  simp_rw [he]
  have hc0 : c 0 = 1 := by simp [c,hfirst]
  by_cases hp : p.val ∣ 2*n
  · rw [if_pos hp]
    symm
    apply (hasSum_single (0 : ℕ) ?_).tsum_eq.trans hc0
    rintro (_|e) he0
    · exact False.elim (he0 rfl)
    · simp [c,gaussCoeff,twistSign_pow,twistSign_bad n p hp]
  · rw [if_neg hp]
    symm
    have hc : Summable c := by
      simpa only [Function.comp_def,he] using hsum.summable.comp_injective (Nat.pow_right_injective p.property.one_lt)
    refine (tsum_of_euler_recurrence c ((curveTrace n p:ℂ)*T) ((p.val:ℂ)*T^2) hc hc0 ?_ ?_).tsum_eq
    · simp [c,gaussCoeff_prime n p hp]
    · intro r
      simp only [c,gaussCoeff_rec n p hp r,gaussCoeff_prime n p hp]
      ring

end TunnellCMLSeries
end

section
/- The weight-one Eisenstein kernel with the integer Euler factor applied before summation. -/

namespace TunnellCMRegularized

open Complex Filter Set
open scoped Topology

noncomputable def kernel (s w : ℂ) := w * exp (-2*s*(Real.log ‖w‖ : ℂ))

lemma kernel_mul (s w u : ℂ) : kernel s (w*u) = kernel s w * kernel s u := by
  by_cases hw : w=0
  · simp [hw,kernel]
  by_cases hu : u=0
  · simp [hu,kernel]
  rw [kernel,kernel,kernel,norm_mul,Real.log_mul (norm_ne_zero_iff.mpr hw) (norm_ne_zero_iff.mpr hu),
    ofReal_add,mul_add,exp_add]
  ring

lemma norm_kernel (s w : ℂ) (hw : w≠0) : ‖kernel s w‖ = ‖w‖^(1-2*s.re) := by
  have hp := norm_pos_iff.mpr hw
  rw [kernel,norm_mul,norm_exp,Real.rpow_def_of_pos hp]
  nth_rw 1 [← Real.exp_log hp]
  rw [← Real.exp_add]
  congr 1
  simp [Complex.mul_re]
  ring

lemma kernel_differentiable (w : ℂ) : Differentiable ℂ (kernel · w) := by
  unfold kernel
  fun_prop

lemma norm_log_error {u : ℂ} (hu : ‖u‖ ≤ 1/2) :
    |Real.log ‖1+u‖-u.re| ≤ ‖u‖^2 := by
  have hi : (1-‖u‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div,div_le_iff₀ (by linarith)]
    linarith
  calc
    _ ≤ ‖log (1+u)-u‖ := by simpa only [sub_re, log_re] using abs_re_le_norm (log (1+u)-u)
    _ ≤ ‖u‖^2 * (1-‖u‖)⁻¹ / 2 := norm_log_one_add_sub_self_le (by linarith)
    _ ≤ ‖u‖^2 * 2 / 2 := by gcongr
    _ = _ := by ring

noncomputable def linearPart (s u : ℂ) := u - 2*s*(u.re : ℂ)

lemma local_error {s u : ℂ} {R : ℝ} (hs : ‖s‖ ≤ R) (hu : ‖u‖ ≤ 1/2)
    (hsmall : 3*R*‖u‖ ≤ 1) :
    ‖kernel s (1+u) - 1 - linearPart s u‖ ≤ (9*R^2+8*R)*‖u‖^2 := by
  have hR := (norm_nonneg s).trans hs
  have hu0 := norm_nonneg u
  let A : ℂ := -2*s*(Real.log ‖1+u‖ : ℂ)
  let B : ℂ := -2*s*(u.re : ℂ)
  have ha : ‖A‖ ≤ 3*R*‖u‖ := by
    have hl : |Real.log ‖1+u‖| ≤ 3/2*‖u‖ :=
      by simpa only [log_re] using (abs_re_le_norm (log (1+u))).trans (norm_log_one_add_half_le_self hu)
    dsimp [A]
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ 2*R*(3/2*‖u‖) := by gcongr
      _ = _ := by ring
  have hAB : ‖A-B‖ ≤ 2*R*‖u‖^2 := by
    dsimp [A,B]
    rw [← mul_sub, ← ofReal_sub]
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    gcongr
    exact norm_log_error hu
  have e : kernel s (1+u) - 1 - linearPart s u =
      (exp A-1-A) + (A-B) + u*(exp A-1) := by
    unfold kernel linearPart
    dsimp [A,B]
    ring
  rw [e]
  calc
    _ ≤ (‖exp A-1-A‖+‖A-B‖) + ‖u‖*‖exp A-1‖ := by
      rw [← norm_mul]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((3*R*‖u‖)^2+2*R*‖u‖^2) + ‖u‖*(2*(3*R*‖u‖)) := by
      gcongr
      · exact (norm_exp_sub_one_sub_id_le (ha.trans hsmall)).trans (pow_le_pow_left₀ (norm_nonneg _) ha 2)
      · exact (norm_exp_sub_one_le (ha.trans hsmall)).trans (by gcongr)
    _ = _ := by ring

noncomputable def difference (a : ℕ) (z w s : ℂ) :=
  (a:ℂ)^2 * (kernel s (w+z)-kernel s w) -
    (a:ℂ) * (kernel s (w+(a:ℂ)*z)-kernel s w)

lemma linear_nat (a : ℕ) (s u : ℂ) :
    linearPart s ((a:ℂ)*u) = (a:ℂ)*linearPart s u := by
  simp [linearPart, Complex.mul_re]
  ring

lemma difference_bound {s z w : ℂ} (hw : w≠0) {R : ℝ} (hs : ‖s‖ ≤ R) (a : ℕ)
    (hu : ‖z/w‖ ≤ 1/2) (hv : ‖(a:ℂ)*(z/w)‖ ≤ 1/2)
    (hsu : 3*R*‖z/w‖ ≤ 1) (hsv : 3*R*‖(a:ℂ)*(z/w)‖ ≤ 1) :
    ‖difference a z w s‖ ≤ (((a:ℝ)^2+(a:ℝ)^3)*(9*R^2+8*R)*‖z‖^2) *
      ‖w‖^(-1-2*s.re) := by
  let u := z/w
  let err (v : ℂ) := kernel s (1+v) - 1 - linearPart s v
  have e : difference a z w s = kernel s w * ((a:ℂ)^2*err u-(a:ℂ)*err ((a:ℂ)*u)) := by
    have e₁ : w+z = w*(1+u) := by dsimp [u]; field_simp
    have e₂ : w+(a:ℂ)*z = w*(1+(a:ℂ)*u) := by dsimp [u]; field_simp
    unfold difference
    rw [e₁,e₂,kernel_mul,kernel_mul]
    dsimp [err]
    rw [linear_nat]
    ring
  have h₁ := local_error hs hu hsu
  have h₂ := local_error hs hv hsv
  rw [e,norm_mul,norm_kernel _ _ hw]
  calc
    _ ≤ ‖w‖^(1-2*s.re) * ((a:ℝ)^2 * ((9*R^2+8*R)*‖u‖^2) +
        (a:ℝ) * ((9*R^2+8*R)*‖(a:ℂ)*u‖^2)) := by
      gcongr
      apply (norm_sub_le _ _).trans
      simp only [norm_mul,norm_pow,Complex.norm_natCast]
      gcongr
      simpa only [norm_mul,Complex.norm_natCast] using h₂
    _ = _ := by
      have hp := norm_pos_iff.mpr hw
      have he : (-1-2*s.re)=(1-2*s.re)-2 := by ring
      simp only [u,norm_div,norm_mul,Complex.norm_natCast]
      rw [he,Real.rpow_sub hp (1-2*s.re) 2,Real.rpow_ofNat]
      ring

def domain : Set ℂ := {s | 3/4 < s.re}

lemma domain_open : IsOpen domain := isOpen_lt continuous_const continuous_re

theorem regularized_summable (L : PeriodPair) (a : ℕ) (z : ℂ) :
    SummableLocallyUniformlyOn (fun (w : L.lattice) => difference a z w) domain := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually domain_open
  intro K hK hc
  obtain ⟨R₀,hR₀⟩ := hc.exists_bound_of_continuousOn (continuous_id (X := ℂ)).continuousOn
  let R := max R₀ 1
  have hR : 0 ≤ R := le_trans (by norm_num : (0:ℝ)≤1) (le_max_right _ _)
  let C := ((a:ℝ)^2+(a:ℝ)^3)*(9*R^2+8*R)*‖z‖^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨fun w => C*‖(w:ℂ)‖^(-5/2:ℝ),
    (ZLattice.summable_norm_rpow L.lattice _ (by simp; norm_num)).mul_left _, ?_⟩
  have htop : Tendsto (fun w : L.lattice => ‖(w:ℂ)‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding L.isClosed_lattice.isClosedEmbedding_subtypeVal
  have ht : Tendsto (fun w : L.lattice => ‖z/(w:ℂ)‖) cofinite (𝓝 0) := by
    simp only [norm_div]
    exact tendsto_const_nhds.div_atTop htop
  have ht' : Tendsto (fun w : L.lattice => ‖(a:ℂ)*(z/(w:ℂ))‖) cofinite (𝓝 0) := by
    simpa only [norm_mul,mul_zero] using ht.const_mul ‖(a:ℂ)‖
  have hu := ht.eventually_le_const (by norm_num : (0:ℝ)<1/2)
  have hv := ht'.eventually_le_const (by norm_num : (0:ℝ)<1/2)
  have hsu : ∀ᶠ w : L.lattice in cofinite, 3*R*‖z/(w:ℂ)‖ ≤ 1 :=
    ((ht.const_mul (3*R)).eventually_le_const (by simp))
  have hsv : ∀ᶠ w : L.lattice in cofinite, 3*R*‖(a:ℂ)*(z/(w:ℂ))‖ ≤ 1 :=
    ((ht'.const_mul (3*R)).eventually_le_const (by simp))
  filter_upwards [hu,hv,hsu,hsv,htop.eventually_ge_atTop 1] with w h1 h2 h3 h4 hw
  intro s hs
  have hsR : ‖s‖ ≤ R := (hR₀ s hs).trans (le_max_left _ _)
  apply (difference_bound (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hw)) hsR a h1 h2 h3 h4).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le hw (by have := hK hs; change 3/4 < s.re at this; linarith)

noncomputable def regularized (L : PeriodPair) (a : ℕ) (z s : ℂ) :=
  ∑' w : L.lattice, difference a z w s

theorem regularized_holomorphic (L : PeriodPair) (a : ℕ) (z : ℂ) :
    DifferentiableOn ℂ (regularized L a z) domain := by
  apply (regularized_summable L a z).differentiableOn domain_open
  intro w s _
  unfold difference kernel
  fun_prop

open scoped ComplexConjugate

lemma kernel_one (w : ℂ) : kernel 1 w = conj (w⁻¹) := by
  by_cases hw : w = 0
  · simp [hw,kernel]
  have hp := norm_pos_iff.mpr hw
  have e : (-2:ℂ)*1*(Real.log ‖w‖ : ℂ) = (↑(-2*Real.log ‖w‖ : ℝ):ℂ) := by push_cast; ring
  rw [kernel,e,← Complex.ofReal_exp,show (-2:ℝ)*Real.log ‖w‖ = -(Real.log ‖w‖ * 2) by ring,
    Real.exp_neg,Real.exp_mul,Real.exp_log hp,Real.rpow_ofNat,← normSq_eq_norm_sq,Complex.inv_def]
  simp

lemma shifted_summable (L : PeriodPair) (z s : ℂ) (hs : 3/2<s.re) :
    Summable (fun w : L.lattice => kernel s (w+z)) := by
  have he : 1-2*s.re < -2 := by linarith
  apply Summable.of_norm
  apply (ZLattice.summable_norm_sub_rpow L.lattice (1-2*s.re) (by simpa using he) (-z)).congr
  intro w
  simp only [sub_neg_eq_add]
  by_cases h : (w:ℂ)+z=0
  · rw [h]
    simp [kernel,Real.zero_rpow (show 1-2*s.re≠0 by linarith)]
  · exact (norm_kernel _ _ h).symm

lemma unshifted_zero (L : PeriodPair) (s : ℂ) : ∑' w : L.lattice, kernel s w = 0 := by
  have h := (Equiv.neg L.lattice).tsum_eq (fun w : L.lattice => kernel s w)
  simp only [Equiv.neg_apply,Submodule.coe_neg] at h
  have hneg (w : ℂ) : kernel s (-w) = -(kernel s w) := by simp [kernel]
  simp only [hneg,tsum_neg] at h
  linear_combination -h/2

lemma shifted_period (L : PeriodPair) (z s : ℂ) (l : L.lattice) :
    (∑' w : L.lattice, kernel s (w+(z+l))) = ∑' w : L.lattice, kernel s (w+z) := by
  convert (Equiv.addRight l).tsum_eq (fun w : L.lattice => kernel s (w+z)) using 2 with w
  congr 1
  simp [add_left_comm,add_comm,add_assoc]

theorem regularized_large (L : PeriodPair) (a : ℕ) (z s : ℂ) (hs : 3/2<s.re)
    (hz : ((a:ℂ)-1)*z ∈ L.lattice) :
    regularized L a z s = ((a:ℂ)^2-(a:ℂ)) * ∑' w : L.lattice, kernel s (w+z) := by
  let l : L.lattice := ⟨((a:ℂ)-1)*z,hz⟩
  have he : (a:ℂ)*z=z+l := by dsimp [l]; ring
  have h₀ : Summable fun w : L.lattice => kernel s w := by
    simpa using shifted_summable L 0 s hs
  have h := (((shifted_summable L z s hs).hasSum.sub h₀.hasSum).mul_left ((a:ℂ)^2)).sub
    (((shifted_summable L ((a:ℂ)*z) s hs).hasSum.sub h₀.hasSum).mul_left (a:ℂ))
  rw [show regularized L a z s = _ from h.tsum_eq,unshifted_zero,he,shifted_period]
  ring

end TunnellCMRegularized
end

section
/- The negative quadratic twist and the coefficients of the trivial class-character theta series. -/

namespace TunnellRankin
open Finset TunnellCMLSeries TunnellGaussian

def negWeight (d m : ℕ) : ℤ := if Odd m then jacobiSym (-((2*d:ℕ):ℤ)) m else 0

lemma negWeight_one (d : ℕ) : negWeight d 1=1 := by simp [negWeight]

lemma negWeight_mul (d a b : ℕ) : negWeight d (a*b)=negWeight d a*negWeight d b := by
  by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [negWeight,Nat.odd_mul,ha,hb]
  exact jacobiSym.mul_right' _ (fun h => by simp [h] at ha) (fun h => by simp [h] at hb)

lemma negWeight_pow (d a k : ℕ) : negWeight d (a^k)=(negWeight d a)^k := by
  induction k with
  | zero => simp [negWeight_one]
  | succ k ih => rw [pow_succ,negWeight_mul,ih,pow_succ]

lemma norm_weight (d m : ℕ) : ‖(negWeight d m:ℂ)‖≤1 := by
  unfold negWeight
  split
  · rcases jacobiSym.trichotomy (-((2*d:ℕ):ℤ)) m with h|h|h <;> rw [h] <;> norm_num
  · simp

lemma twist_by_negative (d m : ℕ) : gaussCoeff (2*d) m=(negWeight d m:ℂ)*gaussCoeff 1 m := by
  by_cases hm : Odd m
  · by_cases h : m%4=1
    · simp only [gaussCoeff,twistSign,negWeight,if_pos hm,Nat.cast_one,jacobiSym.one_left,
        Int.cast_one,one_mul]
      rw [show (-((2*d:ℕ):ℤ))=(-1)*((2*d:ℕ):ℤ) by ring,jacobiSym.mul_left,jacobiSym.at_neg_one hm,
        ZMod.χ₄_nat_one_mod_four h,one_mul]
    · have h3 : m%4=3 := by have := Nat.odd_iff.mp hm; omega
      simp [gaussCoeff,mass,TunnellSplitMass.shell_mod_four h3]
  · simp [gaussCoeff,twistSign,negWeight,hm]

def chi (d : ℕ) : ArithmeticFunction ℤ := ⟨negWeight d,by simp [negWeight]⟩

lemma chi_mult (d : ℕ) : (chi d).IsMultiplicative :=
  ⟨negWeight_one d,fun _ => negWeight_mul d _ _⟩

def idealCoeff (d m : ℕ) : ℤ := ∑ e∈m.divisors,negWeight d e

lemma idealCoeff_mul (d : ℕ) {a b : ℕ} (h : a.Coprime b) :
    idealCoeff d (a*b)=idealCoeff d a*idealCoeff d b := by
  let z := (ArithmeticFunction.zeta : ArithmeticFunction ℤ)
  have he (m : ℕ) : (chi d*z) m = idealCoeff d m := by
    rw [show z=(ArithmeticFunction.zeta : ArithmeticFunction ℤ) by rfl,ArithmeticFunction.coe_mul_zeta_apply]
    rfl
  rw [←he,←he,←he]
  exact ((chi_mult d).mul ArithmeticFunction.isMultiplicative_zeta.natCast).map_mul_of_coprime h

lemma idealCoeff_one (d : ℕ) : idealCoeff d 1=1 := by simp [idealCoeff,negWeight_one]

lemma idealCoeff_prime_pow (d p k : ℕ) (hp : p.Prime) :
    idealCoeff d (p^k)=∑ j∈range (k+1),(negWeight d p)^j := by
  rw [idealCoeff,Nat.sum_divisors_prime_pow hp]
  simp_rw [negWeight_pow]

lemma norm_idealCoeff (d m : ℕ) : ‖(idealCoeff d m:ℂ)‖≤(m:ℝ) := by
  rw [idealCoeff,Int.cast_sum]
  calc
    _ ≤ ∑ e∈m.divisors,‖(negWeight d e:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _e∈m.divisors,(1:ℝ) := sum_le_sum (fun e _ => norm_weight d e)
    _ = m.divisors.card := by simp
    _ ≤ m := by
      exact_mod_cast (show m.divisors.card ≤ m by
        have h : m.divisors ⊆ Icc 1 m := by
          intro e he
          obtain ⟨hdiv,hm⟩ := Nat.mem_divisors.mp he
          exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdiv (Nat.pos_of_ne_zero hm),
            Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdiv⟩
        simpa using card_le_card h)

end TunnellRankin
end

section
/- Local Rankin–Selberg convolution for an unramified degree-two sequence and a binary ideal-count theta series. -/

namespace TunnellRankin
open Finset

lemma hecke_pair {R : Type*} [CommRing R] {b : ℕ → R} {a p : R} (h0 : b 0=1)
    (h1 : b 1=a) (hr : ∀ k, b (k+2)=a*b (k+1)-p*b k) (i j : ℕ) :
    b (i+1)*b (j+1) - p*b i*b j = b (i+j+2) := by
  induction i using Nat.twoStepInduction with
  | zero => simpa [h0,h1] using (hr j).symm
  | one =>
    rw [hr 0,h0,h1,show 1+j+2=(j+1)+2 by omega,hr (j+1),hr j]
    ring
  | more k h₁ h₂ =>
    rw [show k+2+1=(k+1)+2 by omega,hr (k+1),hr k,
      show k+2+j+2=(k+j+2)+2 by omega,hr (k+j+2)]
    rw [show k+j+2+1=k+1+j+2 by omega,←h₂,←h₁,show k+1+1=k+2 by omega,hr k]
    ring

def eulerConvolution {R : Type*} [CommRing R] (b : ℕ→R) (u : R) (k : ℕ) : R :=
  ∑ j∈range (k+1), u^j*b j*b (k-j)

lemma local_convolution {R : Type*} [CommRing R] {b : ℕ → R} {a p : R} (h0 : b 0=1)
    (h1 : b 1=a) (hr : ∀ k, b (k+2)=a*b (k+1)-p*b k) (u : R) (k : ℕ) :
    eulerConvolution b u (k+2) - p*u*eulerConvolution b u k =
      b (k+2)*∑ j∈range (k+3),u^j := by
  have shift (j : ℕ) (hj : j < k+1) :
      u^(j+1)*b (j+1)*b (k+2-(j+1)) - p*u*(u^j*b j*b (k-j)) = b (k+2)*u^(j+1) := by
    have hx := hecke_pair h0 h1 hr j (k-j)
    rw [show j+(k-j)+2=k+2 by omega] at hx
    rw [show k+2-(j+1)=k-j+1 by omega,pow_succ]
    linear_combination (u^j*u)*hx
  unfold eulerConvolution
  rw [sum_range_succ, sum_range_succ' (f:=fun j => u^j*b j*b (k+2-j)) (n:=k+1)]
  rw [sum_range_succ (f:=fun j => u^j) (n:=k+2), sum_range_succ' (f:=fun j => u^j) (n:=k+1)]
  simp only [pow_zero,h0,mul_one,one_mul,Nat.sub_zero,Nat.sub_self]
  rw [mul_sum]
  have hs := sum_congr (s₁:=range (k+1)) (s₂:=range (k+1)) rfl (fun j hj => shift j (mem_range.mp hj))
  rw [sum_sub_distrib] at hs
  rw [mul_add,mul_add,mul_sum]
  linear_combination hs

end TunnellRankin
end

section
/- The analytic Euler factor of the Rankin convolution, including all ramification signs. -/

namespace TunnellRankin
open Finset

theorem rankin_local_hasSum {b : ℕ→ℂ} {a p : ℂ} (h0 : b 0=1) (h1 : b 1=a)
    (hr : ∀ k, b (k+2)=a*b (k+1)-p*b k) (u T : ℂ) {F G : ℂ}
    (hf : HasSum (fun k : ℕ => b k*T^k) F) (hg : HasSum (fun k : ℕ => b k*(u*T)^k) G) :
    HasSum (fun k : ℕ => b k*(∑ j∈range (k+1),u^j)*T^k) ((1-p*u*T^2)*F*G) := by
  let H (k : ℕ) := eulerConvolution b u k*T^k
  let U (k : ℕ) := if 2≤k then H (k-2) else 0
  have hH : HasSum H (G*F) := by
    have h := hasSum_sum_range_mul_of_summable_norm hg.summable.norm hf.summable.norm
    rw [hg.tsum_eq,hf.tsum_eq] at h
    apply h.congr_fun
    intro k
    simp only [H,eulerConvolution,sum_mul]
    apply sum_congr rfl
    intro j hj
    have hj' : j+(k-j)=k := by have := mem_range.mp hj; omega
    rw [mul_pow,show T^k=T^j*T^(k-j) by rw [←pow_add,hj']]
    ring
  have hU : HasSum U (G*F) := by
    apply (hasSum_nat_add_iff' 2).mp
    simpa [U,sum_range_succ] using hH
  have hsub := hH.sub (hU.mul_left (p*u*T^2))
  rw [show G*F-(p*u*T^2)*(G*F)=(1-p*u*T^2)*F*G by ring] at hsub
  apply hsub.congr_fun
  intro k
  rcases k with _|(_|k)
  · simp [H,U,eulerConvolution,h0]
  · norm_num [H,U,eulerConvolution,h0,sum_range_succ] <;> ring_nf <;> tauto
  · change b (k+2)*(∑ j∈range (k+3),u^j)*T^(k+2) = H (k+2)-p*u*T^2*U (k+2)
    simp only [H,U,show 2≤k+2 by omega,if_true,show k+2-2=k by omega]
    rw [pow_add]
    linear_combination -(T^k*T^2)*local_convolution h0 h1 hr u k

end TunnellRankin
end

section
/- The complete Rankin–Selberg Euler product for the base congruent-number form
and the trivial quadratic ideal-class character of discriminant −8d. -/

namespace TunnellRankin
open Finset TunnellGaussian TunnellCMLSeries
open OMA.R_CongruentNumber_Tunnell_even_R1

noncomputable def dir (f : ℕ→ℂ) (s : ℝ) (m : ℕ) : ℂ := f m/(m:ℂ)^(s:ℂ)
noncomputable def twistA (n : ℕ) := gaussCoeff n
noncomputable def rankinA (d m : ℕ) : ℂ := twistA 1 m*(idealCoeff d m:ℂ)
noncomputable def localSum (f : ℕ→ℂ) (s : ℝ) (p : Nat.Primes) : ℂ := ∑' k : ℕ, dir f s (p.val^k)

lemma twistA_one (n : ℕ) : twistA n 1=1 := by simp [twistA,gaussCoeff,mass_one,twistSign_one]
lemma twistA_mul (n : ℕ) {a b : ℕ} (h : a.Coprime b) : twistA n (a*b)=twistA n a*twistA n b := by
  simp only [twistA,gaussCoeff,twistSign_mul,coefficient_mul h,Int.cast_mul]
  ring

lemma euler {f : ℕ→ℂ} {s : ℝ} (hs : 0<s) (h1 : f 1=1)
    (hm : ∀ {a b : ℕ}, a.Coprime b → f (a*b)=f a*f b) (hf : Summable (dir f s)) :
    HasProd (localSum f s) (∑' k,dir f s k) := by
  apply EulerProduct.eulerProduct_hasProd
  · simp [dir,h1]
  · intro a b hc
    simp [dir,hm hc,Nat.cast_mul,Complex.natCast_mul_natCast_cpow,div_mul_div_comm]
  · exact hf.norm
  · simp [dir,Complex.zero_cpow (by exact_mod_cast hs.ne' : (s:ℂ)≠0)]

lemma summable_rankin (d : ℕ) (s : ℝ) (hs : 5/2<s) : Summable (dir (rankinA d) s) := by
  have hf := (shell_expansion 1 (s-1) (by linarith)).summable.norm
  apply Summable.of_norm
  apply hf.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro m
  by_cases h : m=0
  · subst m
    rw [show dir (rankinA d) s 0=0 by simp [dir,Complex.zero_cpow (by exact_mod_cast (by linarith : s≠0) : (s:ℂ)≠0)],norm_zero]
    exact norm_nonneg _
  · have hp : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero h
    change ‖twistA 1 m*(idealCoeff d m:ℂ)/(m:ℂ)^(s:ℂ)‖≤ ‖twistA 1 m/(m:ℂ)^((s-1:ℝ):ℂ)‖
    simp only [norm_div,norm_mul,Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h),Complex.ofReal_re,
      Real.rpow_sub hp,Real.rpow_one]
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_idealCoeff d m) (norm_nonneg _)) (Real.rpow_nonneg hp.le _)

lemma local_hasSum {f : ℕ→ℂ} {s : ℝ} (hf : Summable (dir f s)) (p : Nat.Primes) :
    HasSum (fun k : ℕ => f (p.val^k)*((p.val:ℂ)^(-(s:ℂ)))^k) (localSum f s p) := by
  have h : Summable (fun k : ℕ => dir f s (p.val^k)) :=
    hf.comp_injective (Nat.pow_right_injective p.property.one_lt)
  apply h.hasSum.congr_fun
  intro k
  exact (weight_prime_power p s k _).symm

private lemma single_at_zero {f : ℕ→ℂ} (h0 : f 0=1) (h : ∀ k, k≠0 → f k=0) : HasSum f 1 :=
  h0 ▸ hasSum_single 0 h

lemma local_rankin (d : ℕ) (s : ℝ) (hs : 5/2<s) (p : Nat.Primes) :
    localSum (rankinA d) s p =
      (1-(p.val:ℂ)*(negWeight d p.val:ℂ)*((p.val:ℂ)^(-(s:ℂ)))^2) *
        localSum (twistA 1) s p * localSum (twistA (2*d)) s p := by
  let T := (p.val:ℂ)^(-(s:ℂ))
  let u : ℂ := negWeight d p.val
  let b (k : ℕ) := twistA 1 (p.val^k)
  have hf := local_hasSum (f:=twistA 1) (s:=s) (shell_expansion 1 s (by linarith)).summable p
  have hg := local_hasSum (f:=twistA (2*d)) (s:=s) (shell_expansion (2*d) s (by linarith)).summable p
  have hz := local_hasSum (summable_rankin d s hs) p
  have hg' : HasSum (fun k => b k*(u*T)^k) (localSum (twistA (2*d)) s p) := by
    apply hg.congr_fun
    intro k
    simp only [b,twistA,twist_by_negative,negWeight_pow,Int.cast_pow,mul_pow,u,T]
    ring
  have hr : HasSum (fun k => b k*(∑ j∈range (k+1),u^j)*T^k) (localSum (rankinA d) s p) := by
    apply hz.congr_fun
    intro k
    simp only [rankinA,idealCoeff_prime_pow d _ _ p.property,Int.cast_sum,Int.cast_pow,u,b,T]
  by_cases hp : p.val=2
  · have hu : u=0 := by simp [u,hp,negWeight]
    have hb : ∀ k, 0<k → b k=0 := by
      intro k hk
      change (twistSign 1 (p.val^k):ℂ)*_=0
      rw [twistSign_pow,hp,show twistSign 1 2=0 by decide,zero_pow hk.ne',Int.cast_zero,zero_mul]
    have hb0 : b 0=1 := by simp [b,twistA_one]
    have f1 : localSum (twistA 1) s p=1 := by
      apply hf.unique
      change HasSum (fun k => b k*T^k) 1
      apply single_at_zero (by simp [hb0])
      exact fun k hk => by rw [hb k (Nat.pos_of_ne_zero hk),zero_mul]
    have g1 : localSum (twistA (2*d)) s p=1 := by
      apply hg'.unique
      apply single_at_zero (by simp [hb0])
      exact fun k hk => by rw [hb k (Nat.pos_of_ne_zero hk),zero_mul]
    have r1 : localSum (rankinA d) s p=1 := by
      apply hr.unique
      apply single_at_zero (by simp [hb0])
      exact fun k hk => by rw [hb k (Nat.pos_of_ne_zero hk),zero_mul,zero_mul]
    change _=(1-(p.val:ℂ)*u*T^2)*_*_
    simp [r1,f1,g1,hu]
  · have hpg : ¬p.val∣2*1 := by simpa [Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two] using hp
    have hb0 : b 0=1 := by simp [b,twistA_one]
    have hrec (k : ℕ) : b (k+2)=b 1*b (k+1)-(p.val:ℂ)*b k := by
      simpa only [b,twistA,pow_one] using gaussCoeff_rec 1 p hpg k
    exact hr.unique (rankin_local_hasSum hb0 rfl hrec u T hf hg')

end TunnellRankin
end

section
/- Factorization of the central Rankin convolution in the half-plane of absolute convergence. -/

namespace TunnellRankin
open TunnellCMLSeries

noncomputable def quadraticCoeff (d m : ℕ) : ℂ := negWeight d m

lemma summable_quadratic (d : ℕ) {s : ℝ} (hs : 1<s) : Summable (dir (quadraticCoeff d) s) := by
  apply Summable.of_norm
  apply (Real.summable_nat_rpow_inv.mpr hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro m
  by_cases hm : m=0
  · subst m
    simp [dir,quadraticCoeff,negWeight,Real.zero_rpow (by linarith : s≠0)]
  · rw [dir,norm_div,Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm),Complex.ofReal_re]
    rw [←one_div]
    exact div_le_div_of_nonneg_right (norm_weight d m) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma quadratic_factor (d : ℕ) (s : ℝ) (hs : 5/2<s) (p : Nat.Primes) :
    localSum (quadraticCoeff d) (2*s-1) p *
      (1-(p.val:ℂ)*(negWeight d p.val:ℂ)*((p.val:ℂ)^(-(s:ℂ)))^2)=1 := by
  let u : ℂ := negWeight d p.val
  let q : ℂ := (p.val:ℂ)^(-((2*s-1:ℝ):ℂ))
  have he : q=(p.val:ℂ)*((p.val:ℂ)^(-(s:ℂ)))^2 := by
    dsimp [q]
    rw [show -((2*s-1:ℝ):ℂ)=1+(2:ℕ)*(-(s:ℂ)) by push_cast; ring,
      Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.property.ne_zero),Complex.cpow_one,Complex.cpow_nat_mul]
  have hq : ‖q‖<1 := by
    dsimp only [q]
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos,Complex.neg_re,Complex.ofReal_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by linarith)
  have hnorm : ‖u*q‖<1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_weight d p.val)).trans_lt hq
  have hseries := local_hasSum (summable_quadratic d (s:=2*s-1) (by linarith)) p
  have hloc : localSum (quadraticCoeff d) (2*s-1) p=(1-u*q)⁻¹ := by
    apply hseries.unique
    apply (hasSum_geometric_of_norm_lt_one hnorm).congr_fun
    intro k
    simp only [quadraticCoeff,negWeight_pow,Int.cast_pow,mul_pow,u,q]
  rw [hloc,show (p.val:ℂ)*(negWeight d p.val:ℂ)*((p.val:ℂ)^(-(s:ℂ)))^2=u*q by rw [he]; ring]
  apply inv_mul_cancel₀
  intro h
  rw [←sub_eq_zero.mp h,norm_one] at hnorm
  exact (lt_irrefl _ hnorm)

theorem rankin_factorization (d : ℕ) (s : ℝ) (hs : 5/2<s) :
    latticeValue 1 s*latticeValue (2*d) s =
      (∑' m : ℕ, (negWeight d m:ℂ)/(m:ℂ)^((2*s-1:ℝ):ℂ))*
      ∑' m : ℕ, gaussCoeff 1 m*(idealCoeff d m:ℂ)/(m:ℂ)^(s:ℂ) := by
  have hbase (n : ℕ) : HasProd (localSum (twistA n) s) (latticeValue n s) := by
    have ha : HasSum (dir (twistA n) s) (latticeValue n s) := shell_expansion n s (by linarith)
    rw [←ha.tsum_eq]
    exact euler (by linarith) (twistA_one n) (twistA_mul n) ha.summable
  have hL := euler (f:=quadraticCoeff d) (s:=2*s-1) (by linarith) (by simp [quadraticCoeff,negWeight_one])
    (fun {a b} _ => by simp [quadraticCoeff,negWeight_mul]) (summable_quadratic d (by linarith))
  have hR := euler (f:=rankinA d) (s:=s) (by linarith) (by simp [rankinA,idealCoeff_one,twistA_one])
    (fun {a b} h => by simp only [rankinA,idealCoeff_mul d h,twistA_mul 1 h,Int.cast_mul]; ring)
    (summable_rankin d s hs)
  apply ((hbase 1).mul (hbase (2*d))).unique
  apply (hL.mul hR).congr_fun
  intro p
  change _ = localSum (quadraticCoeff d) (2*s-1) p * localSum (rankinA d) s p
  rw [local_rankin d s hs p,←mul_assoc,←mul_assoc,quadratic_factor d s hs p,one_mul]

end TunnellRankin
end

section
/- Polarized Parseval on horizontal lines for the weight-two and weight-one factors. -/

namespace TunnellRankin
open AddCircle MeasureTheory Complex
open scoped ComplexConjugate InnerProductSpace

noncomputable def circleSeries (a : ℕ→ℂ) : C(AddCircle (1:ℝ),ℂ) := ∑' n : ℕ,a n • fourier (T:=1) (n:ℤ)

lemma circle_hasSum {a : ℕ→ℂ} (ha : Summable a) :
    HasSum (fun n : ℕ => a n • fourier (T:=1) (n:ℤ)) (circleSeries a) := by
  apply Summable.hasSum
  apply Summable.of_norm
  simpa [norm_smul,fourier_norm] using ha.norm

lemma circle_parseval {a b : ℕ→ℂ} (ha : Summable a) (hb : Summable b) :
    HasSum (fun n : ℕ => a n*conj (b n)) (∫ x : AddCircle (1:ℝ),
      conj (circleSeries b x)*circleSeries a x ∂haarAddCircle) := by
  let μ := @haarAddCircle (1:ℝ) (by exact ⟨by norm_num⟩)
  let v (k : ℕ) : Lp ℂ 2 μ := fourierLp 2 (T:=1) (k:ℤ)
  let A := ContinuousMap.toLp 2 μ ℂ (circleSeries a)
  let B := ContinuousMap.toLp 2 μ ℂ (circleSeries b)
  have ha' : HasSum (fun n : ℕ => a n • v n) A := by
    simpa only [A,v,map_smul] using (circle_hasSum ha).mapL (ContinuousMap.toLp 2 μ ℂ)
  have hb' : HasSum (fun n : ℕ => b n • v n) B := by
    simpa only [B,v,map_smul] using (circle_hasSum hb).mapL (ContinuousMap.toLp 2 μ ℂ)
  have hi (k : ℕ) : inner ℂ (v k) B=b k := by
    have hh := hb'.mapL (innerSL ℂ (v k))
    simp only [innerSL_apply_apply,inner_smul_right] at hh
    apply hh.unique
    have vv (n : ℕ) : inner ℂ (v k) (v n) = if k=n then 1 else 0 := by
      simpa only [v,Nat.cast_inj] using (orthonormal_iff_ite.mp (orthonormal_fourier (T:=1)) (k:ℤ) (n:ℤ))
    simp only [vv,mul_ite,mul_one,mul_zero]
    simpa using (hasSum_single (f:=fun n => if k=n then b n else 0) k (by intro n hn; simp [Ne.symm hn]))
  have sum := ha'.mapL (innerSL ℂ B)
  simp only [innerSL_apply_apply] at sum
  rw [show inner ℂ B A = ∫ x : AddCircle (1:ℝ),conj (circleSeries b x)*circleSeries a x ∂haarAddCircle by
    simpa only [A,B,μ,RCLike.inner_apply,mul_comm] using
      ContinuousMap.inner_toLp μ (circleSeries b) (circleSeries a)] at sum
  apply sum.congr_fun
  intro n
  simp only [innerSL_apply_apply,inner_smul_right,←hi n]
  rw [inner_conj_symm]

end TunnellRankin
end

section
/- The archimedean unfolded Rankin period as a Mellin transform of the horizontal Fourier pairing. -/

namespace TunnellRankin
open Complex MeasureTheory Set AddCircle TunnellCMLSeries
open scoped ComplexConjugate

noncomputable def mode (a : ℕ→ℂ) (t : ℝ) (k : ℕ) : ℂ :=
  a k*(Real.exp (-(t/2)*k):ℝ)

lemma summable_mode {a : ℕ→ℂ} {C : ℝ} {k : ℕ} (h : ∀ m : ℕ, ‖a m‖≤C*(m:ℝ)^k)
    {t : ℝ} (ht : 0<t) : Summable (mode a t) := by
  apply ((Real.summable_pow_mul_exp_neg_nat_mul k (show 0<t/2 by linarith)).mul_left C).of_norm_bounded
  intro m
  rw [mode,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),←mul_assoc]
  exact mul_le_mul_of_nonneg_right (h m) (Real.exp_pos _).le

lemma base_growth : ∃ C : ℝ, ∀ m : ℕ, ‖twistA 1 m‖≤C*(m:ℝ)^3 := by
  have hf : Summable (dir (twistA 1) 3) := (shell_expansion 1 3 (by norm_num)).summable
  refine ⟨∑' m,‖dir (twistA 1) 3 m‖,fun m => ?_⟩
  by_cases h : m=0
  · subst m
    simp [twistA,gaussCoeff,twistSign]
  · have hterm : ‖dir (twistA 1) 3 m‖≤∑' n, ‖dir (twistA 1) 3 n‖ :=
      hf.norm.le_tsum m (fun _ _ => norm_nonneg _)
    rw [dir,norm_div,Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h),Complex.ofReal_re,
      show (3:ℝ)=(3:ℕ) by norm_num,Real.rpow_natCast] at hterm
    exact (div_le_iff₀ (by positivity : 0<(m:ℝ)^3)).mp hterm

/- The horizontal average at height t/(4π), with period one. -/
noncomputable def strip (d : ℕ) (t : ℝ) : ℂ :=
  ∫ x : AddCircle (1:ℝ), conj (circleSeries (mode (fun m => (idealCoeff d m:ℂ)) t) x)*
    circleSeries (mode (twistA 1) t) x ∂haarAddCircle

lemma strip_expansion (d : ℕ) {t : ℝ} (ht : 0<t) :
    HasSum (fun m : ℕ => rankinA d m*(Real.exp (-(m:ℝ)*t):ℝ)) (strip d t) := by
  obtain ⟨C,hC⟩ := base_growth
  have hc : Summable (mode (fun m => (idealCoeff d m:ℂ)) t) :=
    summable_mode (C:=1) (k:=1) (fun n => by simpa using norm_idealCoeff d n) ht
  apply (circle_parseval (summable_mode hC ht) hc).congr_fun
  intro m
  simp only [rankinA,mode,map_mul,Complex.conj_ofReal,map_intCast]
  rw [show -(m:ℝ)*t=-(t/2)*m+(-(t/2)*m) by ring,Real.exp_add,Complex.ofReal_mul]
  ring

theorem mellin_strip (d : ℕ) {s : ℝ} (hs : 5/2<s) :
    mellin (strip d) (s:ℂ) = Complex.Gamma s*∑' m, dir (rankinA d) s m := by
  have pos : ∀ m : ℕ, rankinA d m=0 ∨ 0<(m:ℝ) := by
    intro m
    by_cases h : m=0
    · subst m; simp [rankinA,idealCoeff]
    · exact Or.inr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))
  have hsum : Summable (fun m : ℕ => ‖rankinA d m‖/(m:ℝ)^s) := by
    convert (summable_rankin d s hs).norm using 1
    ext m
    by_cases h : m=0
    · subst m; simp [dir,rankinA,idealCoeff]
    · rw [dir,norm_div,Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h),Complex.ofReal_re]
  have hm := hasSum_mellin (s:=(s:ℂ)) pos (by simpa using (show 0<s by linarith))
    (fun _ ht => strip_expansion d ht) (by simpa using hsum)
  have hv := (summable_rankin d s hs).hasSum.mul_left (Complex.Gamma s)
  apply hm.unique
  apply hv.congr_fun
  intro m
  simp only [dir,Complex.ofReal_natCast,mul_div_assoc]

end TunnellRankin
end

section
/- Identification of the archimedean strip pairing with the eta newform and its binary theta partner. -/

namespace TunnellRankin
open Complex Set Function ModularForm TunnellCMLSeries MeasureTheory AddCircle
open UpperHalfPlane hiding I
open scoped ComplexConjugate

noncomputable def point (x t : ℝ) (ht : 0<t) : ℍ := ⟨(x:ℂ)+I*(t/(4*Real.pi):ℝ),by
  simp only [add_im,ofReal_im,I_mul_im,ofReal_re,zero_add]
  exact div_pos ht (by positivity)⟩

lemma mode_qParam (a : ℕ→ℂ) (x t : ℝ) (ht : 0<t) (m : ℕ) :
    mode a t m * fourier (T:=1) (m:ℤ) (x:AddCircle (1:ℝ)) =
      a m * Periodic.qParam 1 (point x t ht)^m := by
  rw [mode,fourier_coe_apply,Periodic.qParam,←exp_nat_mul,ofReal_exp,mul_assoc,←exp_add]
  congr 2
  change _ = (m:ℂ)*(2*↑Real.pi*I*((x:ℂ)+I*↑(t/(4*Real.pi):ℝ))/↑(1:ℝ))
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [I_sq]
  ring

lemma circle_eta (x t : ℝ) (ht : 0<t) :
    circleSeries (mode (twistA 1) t) (x : AddCircle (1:ℝ)) =
      TunnellFricke.h (4*(point x t ht:ℂ)) := by
  obtain ⟨H,hH,hw,F,hF,hfc⟩ := TunnellEtaValue.actual_form
  letI : H.IsArithmetic := hH
  have per : (1:ℝ)∈H.strictPeriods := hw ▸ H.strictWidthInfty_mem_strictPeriods
  have hb (m : ℕ) : (qExpansion 1 F).coeff m=twistA 1 m := by
    have he := TunnellArithmetic.eta_eq_mass
      (TunnellTruncated.cubic_congruence (fun N => TunnellCubicFinite.cubic _ N))
      (TunnellTruncated.theta_congruence (fun _ N => TunnellBalanced.balanced _ N)) m
    rw [hfc]
    by_cases ho : Odd m
    · simp [twistA,gaussCoeff,twistSign,ho,he]
    · have hmod : m%4 ≠ 1 := by have := Nat.odd_iff.not.mp ho; omega
      simp [twistA,gaussCoeff,twistSign,ho,TunnellInert.eta_zero_of_mod_four hmod]
  obtain ⟨C,hC⟩ := base_growth
  have ha := (circle_hasSum (summable_mode hC ht)).mapL (ContinuousMap.evalCLM ℂ (x:AddCircle (1:ℝ)))
  have hf := ModularForm.hasSum_qExpansion F one_pos per (point x t ht)
  simp only [hb,hF] at hf
  apply ha.unique
  apply hf.congr_fun
  intro m
  change mode (twistA 1) t m * fourier (T:=1) (m:ℤ) (x:AddCircle (1:ℝ)) = _
  exact mode_qParam _ _ _ _ _

noncomputable def theta (d : ℕ) (z : ℍ) : ℂ :=
  ∑' m : ℕ,(idealCoeff d m:ℂ)*Periodic.qParam 1 z^m

lemma circle_theta (d : ℕ) (x t : ℝ) (ht : 0<t) :
    circleSeries (mode (fun m => (idealCoeff d m:ℂ)) t) (x:AddCircle (1:ℝ))=theta d (point x t ht) := by
  have hc : Summable (mode (fun m => (idealCoeff d m:ℂ)) t) :=
    summable_mode (C:=1) (k:=1) (fun n => by simpa using norm_idealCoeff d n) ht
  have ha := (circle_hasSum hc).mapL (ContinuousMap.evalCLM ℂ (x:AddCircle (1:ℝ)))
  symm
  apply HasSum.tsum_eq
  apply ha.congr_fun
  intro m
  change (idealCoeff d m:ℂ)*Periodic.qParam 1 (point x t ht)^m =
    mode (fun m => (idealCoeff d m:ℂ)) t m*fourier (T:=1) (m:ℤ) (x:AddCircle (1:ℝ))
  exact (mode_qParam (fun j => (idealCoeff d j:ℂ)) x t ht m).symm

end TunnellRankin
end

section
namespace TunnellTwistCharacter

def weight (n m : ℕ) : ℤ := if Odd m then jacobiSym n m else 0

lemma weight_one (n : ℕ) : weight n 1 = 1 := by simp [weight]

lemma weight_mul (n a b : ℕ) : weight n (a*b) = weight n a * weight n b := by
  by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [weight, Nat.odd_mul, ha, hb]
  exact jacobiSym.mul_right' _ (fun e => by simp [e] at ha) (fun e => by simp [e] at hb)

lemma weight_mod (n m : ℕ) : weight n (m % (4*n)) = weight n m := by
  have he : Even (4*n) := Even.mul_right (by decide) _
  have h : Odd (m % (4*n)) ↔ Odd m := by
    simp only [Nat.odd_iff, Nat.mod_mod_of_dvd _ he.two_dvd]
  by_cases hm : Odd m
  · simpa [weight, h, hm] using (jacobiSym.mod_right' n hm).symm
  · simp [weight, h, hm]

lemma weight_zero_of_not_coprime (n m : ℕ) (h : ¬m.Coprime (4*n)) :
    weight n m = 0 := by
  by_cases hm : Odd m
  · letI : NeZero m := ⟨fun e => by simp [e] at hm⟩
    rw [weight, if_pos hm, jacobiSym.eq_zero_iff_not_coprime]
    intro h'
    apply h
    apply Nat.coprime_mul_iff_right.mpr
    constructor
    · exact hm.coprime_two_right.pow_right 2
    · apply Nat.Coprime.symm
      simpa [Nat.coprime_iff_gcd_eq_one, Int.gcd_eq_natAbs] using h'
  · simp [weight, hm]

noncomputable def character (n : ℕ) (hn : n ≠ 0) : DirichletCharacter ℂ (4*n) where
  toFun z := (weight n z.val : ℂ)
  map_one' := by rw [ZMod.val_one_eq_one_mod, weight_mod, weight_one]; norm_num
  map_mul' a b := by rw [ZMod.val_mul, weight_mod, weight_mul]; push_cast; rfl
  map_nonunit' a ha := by
    letI : NeZero (4*n) := ⟨Nat.mul_ne_zero (by decide) hn⟩
    have h : ¬a.val.Coprime (4*n) := fun hc => ha (by
      simpa [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime _ _).mpr hc)
    rw [weight_zero_of_not_coprime n a.val h]
    norm_num

lemma character_apply_nat (n : ℕ) (hn : n ≠ 0) (m : ℕ) :
    character n hn (m : ZMod (4*n)) = (weight n m : ℂ) := by
  change (weight n (m : ZMod (4*n)).val : ℂ) = _
  rw [ZMod.val_natCast, weight_mod]

end TunnellTwistCharacter
end

section
/- The Jacobi character of conductor 8d, for squarefree d congruent to one modulo four. -/

namespace TunnellTwistCharacter

lemma character_quadratic (n : ℕ) (hn : n ≠ 0) : (character n hn).IsQuadratic := by
  intro a
  change (weight n a.val : ℂ) = 0 ∨ (weight n a.val : ℂ) = 1 ∨ (weight n a.val : ℂ) = -1
  by_cases ha : Odd a.val
  · rw [weight, if_pos ha]
    exact_mod_cast jacobiSym.trichotomy n a.val
  · simp [weight,ha]

lemma weight_two_mul {d a : ℕ} (hd : d%4=1) (ha : Odd a) :
    weight (2*d) a = ZMod.χ₈ a * jacobiSym a d := by
  rw [weight,if_pos ha,Nat.cast_mul,Nat.cast_ofNat,jacobiSym.mul_left,jacobiSym.at_two ha,
    jacobiSym.quadratic_reciprocity_one_mod_four hd ha]

lemma character_even {d : ℕ} (hd : d%4=1) :
    (character (2*d) (by omega)).Even := by
  let a := 8*d - 1
  have hz : (-1 : ZMod (4*(2*d))) = (a : ℕ) := by
    dsimp [a]
    rw [Nat.cast_sub (by omega), show 8*d = 4*(2*d) by ring]
    simp
  change character (2*d) _ (-1) = 1
  rw [hz, character_apply_nat, weight_two_mul hd (Nat.odd_iff.mpr (by dsimp [a]; omega))]
  have hj : jacobiSym (a:ℤ) d = jacobiSym (-1) d := by
    apply jacobiSym.mod_left'
    dsimp [a]
    rw [Nat.cast_sub (by omega)]
    push_cast
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-8,by ring⟩
  rw [hj,jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),ZMod.χ₄_nat_mod_four,hd,
    ZMod.χ₈_nat_mod_eight, show a%8 = 7 by dsimp [a]; omega]
  exact_mod_cast (by decide : ZMod.χ₈ (7:ℕ) * ZMod.χ₄ (1:ℕ) = 1)

lemma primitive_of_witness {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hw : ∀ p : ℕ, p.Prime → p ∣ N → ∃ a : ℕ, a ≡ 1 [MOD N/p] ∧ χ a = -1) :
    χ.IsPrimitive := by
  change χ.conductor = N
  by_contra h
  obtain ⟨q,heq⟩ := χ.conductor_dvd_level
  have hq : q ≠ 1 := by rintro rfl; simp_all
  obtain ⟨p,hp,r,hr⟩ := Nat.exists_prime_and_dvd hq
  have hn : N = (χ.conductor*r)*p := heq.trans (by rw [hr]; ring)
  have hdiv : N/p = χ.conductor*r := (congrArg (· / p) hn).trans (Nat.mul_div_cancel _ hp.pos)
  obtain ⟨a,ha,hval⟩ := hw p hp (hn ▸ dvd_mul_left _ _)
  have hunit : IsUnit (a : ZMod N) := by
    by_contra hu
    rw [χ.map_nonunit hu] at hval
    norm_num at hval
  have hsmall : (a : ZMod χ.conductor) = 1 := by
    have h := ha.of_dvd (show χ.conductor ∣ N/p by rw [hdiv]; exact dvd_mul_right _ _)
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have hc := ((ZMod.isUnit_iff_coprime a N).mp hunit).isCoprime
  have hv := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level hc
  rw [χ.changeLevel_primitiveCharacter] at hv
  simp only [Int.cast_natCast] at hv
  rw [hsmall,map_one,hval] at hv
  norm_num at hv

lemma jacobi_congr {a b d : ℕ} (h : a ≡ b [MOD d]) : jacobiSym a d = jacobiSym b d := by
  apply jacobiSym.mod_left'
  exact_mod_cast h

lemma primitive_witness {d : ℕ} (hd : d%4=1) (hs : Squarefree d)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ 4*(2*d)) :
    ∃ a : ℕ, a ≡ 1 [MOD 4*(2*d)/p] ∧ weight (2*d) a = -1 := by
  have hd0 : 0 < d := by omega
  by_cases ht : p = 2
  · subst p
    refine ⟨4*d+1, ?_, ?_⟩
    · rw [show 4*(2*d)/2 = 4*d by omega]
      simp [Nat.ModEq]
    · rw [weight_two_mul hd (Nat.odd_iff.mpr (by omega)),ZMod.χ₈_nat_mod_eight,
        show (4*d+1)%8=5 by omega, jacobi_congr (b:=1) (by simp [Nat.ModEq]),
        Nat.cast_one,jacobiSym.one_left,mul_one]
      decide
  have h8 : p.Coprime 8 := by
    have hc := hp.coprime_iff_not_dvd.mpr (fun h => ht ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
    exact hc.pow_right 3
  have hpd : p ∣ d := (hp.dvd_mul.mp (show p ∣ 8*d by rwa [show 8*d = 4*(2*d) by ring])).resolve_left
    (hp.coprime_iff_not_dvd.mp h8)
  obtain ⟨v,hv⟩ := hpd
  have hpv : p.Coprime v := Nat.coprime_of_squarefree_mul (hv ▸ hs)
  have hv0 : v ≠ 0 := by rintro rfl; simp_all
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b,hb⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using ht)
  obtain ⟨a,hab,ha1⟩ := Nat.chineseRemainder (Nat.coprime_mul_iff_right.mpr ⟨h8,hpv⟩) b.val 1
  have ht8 : a ≡ 1 [MOD 8] := ha1.of_dvd (dvd_mul_right ..)
  have hv1 : a ≡ 1 [MOD v] := ha1.of_dvd (dvd_mul_left ..)
  have ha : Odd a := Nat.odd_iff.mpr (ht8.of_dvd (by decide : 2 ∣ 8))
  have hj : jacobiSym a p = -1 := by
    rw [←jacobiSym.legendreSym.to_jacobiSym,legendreSym]
    simpa only [ZMod.natCast_eq_natCast_iff, Int.cast_natCast,
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hab,ZMod.natCast_zmod_val] using hb
  refine ⟨a, ?_, ?_⟩
  · convert ha1 using 1
    rw [hv,show 4*(2*(p*v)) = (8*v)*p by ring, Nat.mul_div_cancel _ hp.pos]
  · rw [weight_two_mul hd ha,ZMod.χ₈_nat_mod_eight,show a%8=1 from ht8,hv,
      jacobiSym.mul_right' _ hp.ne_zero hv0,hj,jacobi_congr hv1]
    simp

theorem character_primitive {d : ℕ} (hd : d%4=1) (hs : Squarefree d) :
    (character (2*d) (by omega)).IsPrimitive := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  apply primitive_of_witness
  intro p hp hpn
  obtain ⟨a,ha,hw⟩ := primitive_witness hd hs hp hpn
  refine ⟨a,ha,?_⟩
  rw [character_apply_nat,hw]
  norm_num

end TunnellTwistCharacter
end

section
/- The distinguished continuation of the unfolded Rankin integral at its central point. -/

namespace TunnellRankin
open TunnellTwistCharacter TunnellCMLSeries Complex Set

lemma negWeight_decompose (d m : ℕ) : negWeight d m=ZMod.χ₄ m*weight (2*d) m := by
  by_cases h : Odd m
  · simp [negWeight,weight,h,jacobiSym.neg _ h]
  · simp [negWeight,weight,h]

lemma negWeight_mod (d m : ℕ) : negWeight d (m%(4*(2*d))) = negWeight d m := by
  rw [negWeight_decompose,negWeight_decompose,weight_mod,ZMod.χ₄_nat_mod_four (m%(4*(2*d))),
    Nat.mod_mod_of_dvd _ (dvd_mul_right _ _),←ZMod.χ₄_nat_mod_four]

noncomputable def negCharacter (d : ℕ) (hd : 0<d) : DirichletCharacter ℂ (4*(2*d)) where
  toFun z := (negWeight d z.val:ℂ)
  map_one' := by rw [ZMod.val_one_eq_one_mod,negWeight_mod,negWeight_one]; norm_num
  map_mul' a b := by rw [ZMod.val_mul,negWeight_mod,negWeight_mul]; push_cast; rfl
  map_nonunit' a ha := by
    letI : NeZero (4*(2*d)) := ⟨by omega⟩
    have h : ¬a.val.Coprime (4*(2*d)) := fun hc => ha (by
      simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime _ _).mpr hc)
    simp [negWeight_decompose,weight_zero_of_not_coprime (2*d) a.val h]

lemma negCharacter_nat {d : ℕ} (hd : 0<d) (j : ℕ) :
    negCharacter d hd (j:ZMod (4*(2*d)))=(negWeight d j:ℂ) := by
  change (negWeight d (j:ZMod (4*(2*d))).val:ℂ)=_
  rw [ZMod.val_natCast,negWeight_mod]

lemma negCharacter_odd {d : ℕ} (hd : d%4=1) : (negCharacter d (by omega)).Odd := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  have he := character_even hd
  change (weight (2*d) (-1:ZMod (4*(2*d))).val:ℂ)=1 at he
  change (negWeight d (-1:ZMod (4*(2*d))).val:ℂ)= -1
  rw [negWeight_decompose,Int.cast_mul,he,mul_one]
  have hnat : (-1:ZMod (4*(2*d))).val%4=3 := by
    have hz : (-1:ZMod (4*(2*d)))=((4*(2*d)-1:ℕ):ZMod (4*(2*d))) := by rw [Nat.cast_sub (by omega)]; simp
    rw [hz,ZMod.val_natCast,Nat.mod_eq_of_lt (show 4*(2*d)-1<4*(2*d) by omega)]; omega
  rw [ZMod.χ₄_nat_three_mod_four hnat]; norm_num

noncomputable def negativeL (d : ℕ) (hd : 0<d) (s : ℂ) : ℂ :=
  haveI : NeZero (4*(2*d)) := ⟨by omega⟩
  DirichletCharacter.LFunction (negCharacter d hd) s

lemma negative_lseries (d : ℕ) (hd : 0<d) (s : ℝ) (hs : 1<s) :
    negativeL d hd (s:ℂ)=∑' m,dir (quadraticCoeff d) s m := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  rw [negativeL,DirichletCharacter.LFunction_eq_LSeries _ (by simpa using hs),LSeries]
  congr 1
  funext m
  rw [LSeries.term_of_ne_zero' (by exact_mod_cast (by linarith : s≠0) : (s:ℂ)≠0),negCharacter_nat]
  rfl

noncomputable def continued (d : ℕ) (hd : 0<d) (F L : ℂ→ℂ) (s : ℂ) : ℂ :=
  Gamma s*F s*L s / negativeL d hd (2*s-1)

lemma continued_eq {d : ℕ} (hd : 0<d) (F L : ℂ→ℂ) (s : ℝ) (hs : 5/2<s)
    (hF : F s=latticeValue 1 s) (hL : L s=latticeValue (2*d) s) :
    continued d hd F L s=mellin (strip d) (s:ℂ) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  have hχ := negative_lseries d hd (2*s-1) (by linarith)
  have hne := DirichletCharacter.LFunction_ne_zero_of_one_le_re (negCharacter d hd)
    (s:=((2*s-1:ℝ):ℂ)) (Or.inr (by exact_mod_cast (by linarith : 2*s-1≠1))) (by simpa using (show 1≤2*s-1 by linarith))
  change negativeL d hd _ =
    ∑' m : ℕ, (negWeight d m:ℂ)/(m:ℂ)^((2*s-1:ℝ):ℂ) at hχ
  change negativeL d hd ((2*s-1:ℝ):ℂ)≠0 at hne
  unfold continued
  rw [hF,hL,show (2:ℂ)*(s:ℂ)-1=((2*s-1:ℝ):ℂ) by push_cast; rfl,mellin_strip d hs]
  apply (div_eq_iff hne).mpr
  rw [mul_assoc,rankin_factorization d s hs,←hχ]
  change _=Complex.Gamma s*(∑' m : ℕ,gaussCoeff 1 m*(idealCoeff d m:ℂ)/(m:ℂ)^(s:ℂ))*negativeL d hd _
  ring

lemma continued_center {d : ℕ} (hd : d%4=1) {F L : ℂ→ℂ}
    (hF : AnalyticAt ℂ F 1) (hL : AnalyticAt ℂ L 1) :
    AnalyticAt ℂ (continued d (by omega) F L) 1 ∧
      (continued d (by omega) F L 1)*negativeL d (by omega) 1 =
      F 1*L 1 := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  have hχ : negCharacter d (by omega)≠1 := by
    intro hz
    have eq := negCharacter_odd hd
    rw [DirichletCharacter.Odd,hz,MulChar.one_apply (by simp)] at eq
    norm_num at eq
  have hne := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  change negativeL d (by omega) 1 ≠ 0 at hne
  have hg : AnalyticAt ℂ Complex.Gamma 1 := by
    let V := {s : ℂ | 0<s.re}
    have hV : DifferentiableOn ℂ Complex.Gamma V := by
      intro z hz
      apply (Complex.differentiableAt_Gamma z _).differentiableWithinAt
      intro n he
      change 0<z.re at hz
      rw [he,Complex.neg_re,Complex.natCast_re] at hz
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    exact hV.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (0:ℝ)<(1:ℂ).re))
  constructor
  · unfold continued
    apply AnalyticAt.div
    · exact (hg.mul hF).mul hL
    · unfold negativeL
      apply ((DirichletCharacter.differentiable_LFunction hχ).analyticAt _).comp
      fun_prop
    · simpa only [show (2:ℂ)*1-1=1 by norm_num] using hne
  · simp only [continued,show (2:ℂ)*1-1=1 by norm_num,Gamma_one,one_mul,div_mul_cancel₀ _ hne]

end TunnellRankin
end

section
/- A weight-one Eisenstein lattice sum for the Rankin integral. Its auxiliary finite
difference removes the convergence restriction at the central point. -/

namespace TunnellRankinEisenstein

open Complex TunnellCMRegularized TunnellRankin TunnellTwistCharacter Set Finset
open UpperHalfPlane hiding I
open scoped ComplexConjugate Topology

lemma negative_quadratic {d : ℕ} (hd : 0<d) : (negCharacter d hd).IsQuadratic := by
  intro r
  change (negWeight d r.val : ℂ)=0 ∨ (negWeight d r.val : ℂ)=1 ∨ (negWeight d r.val : ℂ)= -1
  by_cases h : Odd r.val
  · simp only [negWeight,if_pos h]
    exact_mod_cast jacobiSym.trichotomy (-((2*d:ℕ):ℤ)) r.val
  · simp [negWeight,h]

lemma negative_primitive {d : ℕ} (hd : d%4=1) (hs : Squarefree d) :
    (negCharacter d (by omega)).IsPrimitive := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  apply primitive_of_witness
  intro p hp hpN
  obtain ⟨a,ha,he⟩ := primitive_witness hd hs hp hpN
  have hfour : 4∣4*(2*d)/p := by
    by_cases h : p=2
    · subst p; rw [show 4*(2*d)/2=4*d by omega]; exact dvd_mul_right _ _
    · have hnot : ¬p∣4 := by
        intro H
        have h' := hp.dvd_of_dvd_pow (n:=2) (by simpa using H : p∣2^2)
        exact h ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      have hp' := (hp.dvd_mul.mp hpN).resolve_left hnot
      obtain ⟨t,ht⟩ := hp'
      rw [ht,←mul_assoc,mul_comm 4 p,mul_assoc,Nat.mul_div_cancel_left _ hp.pos]
      exact dvd_mul_right _ _
  refine ⟨a,ha,?_⟩
  rw [negCharacter_nat,negWeight_decompose,ZMod.χ₄_nat_one_mod_four (ha.of_dvd hfour),he]
  norm_num

/- The physical lattice coordinates have horizontal period N and vertical period N·kz.
The conjugate periods allow the regularized holomorphic parameter s to retain the
denominator cz+t at s=1. -/
def periods (k : ℕ) [NeZero k] (z : ℍ) : PeriodPair where
  ω₁ := 1
  ω₂ := (k:ℂ)*conj (z:ℂ)
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro x y h
    have hi := congrArg Complex.im h
    have hr := congrArg Complex.re h
    have hk : (k:ℝ)≠0 := by exact_mod_cast NeZero.ne k
    simp [Complex.mul_im,Complex.mul_re,hk,z.im_pos.ne'] at hi
    simp_all

def aux (N : ℕ) := N+1

lemma aux_ne (N : ℕ) [NeZero N] : (aux N:ℂ)^2-(aux N:ℂ)≠0 := by
  have h : 0 < N := NeZero.pos N
  unfold aux
  push_cast
  have hn : (N:ℂ)≠0 := by exact_mod_cast h.ne'
  rw [show ((N:ℂ)+1)^2-((N:ℂ)+1)=(N:ℂ)*((N:ℂ)+1) by ring]
  exact mul_ne_zero hn (by exact_mod_cast Nat.succ_ne_zero N)

noncomputable def regular (N k : ℕ) [NeZero N] [NeZero k] (χ : ZMod N → ℂ) (z : ℍ) (s : ℂ) : ℂ :=
  (∑ r : ZMod N, χ r*regularized (periods k z) (aux N) ((r.val:ℂ)/N) s) /
    ((aux N:ℂ)^2-(aux N:ℂ))

theorem regular_analytic (N k : ℕ) [NeZero N] [NeZero k] (χ : ZMod N → ℂ) (z : ℍ) :
    AnalyticOnNhd ℂ (regular N k χ z) domain := by
  apply DifferentiableOn.analyticOnNhd _ domain_open
  apply DifferentiableOn.div_const
  apply DifferentiableOn.fun_sum
  intro r _
  exact (regularized_holomorphic _ _ _).const_mul _

theorem regular_large (N k : ℕ) [NeZero N] [NeZero k] (χ : ZMod N → ℂ) (z : ℍ)
    {s : ℂ} (hs : 3/2<s.re) :
    regular N k χ z s=∑ r : ZMod N, χ r * ∑' j:ℤ×ℤ,
      kernel s ((j.1:ℂ)+(j.2:ℂ)*((k:ℂ)*conj (z:ℂ))+(r.val:ℂ)/N) := by
  classical
  rw [regular,div_eq_iff (aux_ne N),sum_mul]
  apply sum_congr rfl
  intro r _
  have he : ((aux N:ℂ)-1)*((r.val:ℂ)/N)∈(periods k z).lattice := by
    apply PeriodPair.mem_lattice.mpr
    refine ⟨(r.val:ℤ),0,?_⟩
    simp only [periods,aux,Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Int.cast_natCast,Int.cast_zero,zero_mul,mul_one,add_zero]
    have hN : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
    field_simp [hN]
  rw [regularized_large _ _ _ _ hs he]
  have es := (periods k z).latticeEquivProd.symm.toEquiv.tsum_eq
    (fun w : (periods k z).lattice => kernel s ((w:ℂ)+(r.val:ℂ)/N))
  have eh (j : ℤ×ℤ) : ((periods k z).latticeEquivProd.symm.toEquiv j:ℂ)=
      (j.1:ℂ)+(j.2:ℂ)*((k:ℂ)*conj (z:ℂ)) := by
    change ((periods k z).latticeEquivProd.symm j:ℂ)=_
    rw [PeriodPair.latticeEquiv_symm_apply]
    simp [periods]
  rw [←es]
  simp only [eh]
  ring

end TunnellRankinEisenstein
end

section
/- Discrete Fourier transformation of the horizontal rows of the central Eisenstein series. -/
namespace TunnellRankinCotangent
open Complex Finset TunnellRankin UpperHalfPlane
open scoped Real
noncomputable section

def q (z : ℂ) := Complex.exp (2*Real.pi*Complex.I*z)

def row {N : ℕ} [NeZero N] (χ : ZMod N→ℂ) (z : ℂ) :=
  ∑ r : ZMod N,χ r*((Real.pi:ℂ)*Complex.cot (Real.pi*(z+(r.val:ℂ)/N)))

lemma exp_mul_char {N : ℕ} [NeZero N] (r : ZMod N) (k : ℕ) (z : ℂ) :
    (q (z+(r.val:ℂ)/N))^k = ZMod.stdAddChar (r*(k:ZMod N))*(q z)^k := by
  rw [show r*(k:ZMod N)=(((r.val:ℤ)*(k:ℤ):ℤ):ZMod N) by push_cast; simp,ZMod.stdAddChar_coe]
  simp only [q,←Complex.exp_nat_mul,Int.cast_mul,Int.cast_natCast,←Complex.exp_add]
  congr 1
  ring

lemma finite_dft {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (k : ℕ) :
    ∑ r : ZMod N,χ r*ZMod.stdAddChar (r*(k:ZMod N))=χ k*gaussSum χ ZMod.stdAddChar := by
  simpa only [ZMod.dft_apply,mul_neg,neg_neg,smul_eq_mul,hq.inv,mul_comm] using
    hχ.fourierTransform_eq_inv_mul_gaussSum (-(k:ZMod N))

lemma row_qExpansion {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hq : χ.IsQuadratic) (hnt : χ≠1) (z : ℍ) :
    row χ z = (-2*Real.pi*Complex.I*gaussSum χ ZMod.stdAddChar) * ∑' k : ℕ,χ k*(q z)^k := by
  classical
  let e (r : ZMod N) : ℍ := ⟨(z:ℂ)+(r.val:ℂ)/N,by
    change 0 < ((z:ℂ) + ((r.val:ℕ):ℂ)/(N:ℂ)).im
    simp only [Complex.add_im,Complex.div_im,Complex.natCast_im,mul_zero,zero_mul,sub_zero,zero_div,add_zero]
    exact z.im_pos⟩
  have es (r : ZMod N) : ‖q (e r)‖<1 := norm_exp_two_pi_I_lt_one _
  have eg (r : ZMod N) := (hasSum_geometric_of_norm_lt_one (es r)).summable
  have hgeom (r : ZMod N) : Summable (fun k : ℕ => χ r*(q (e r))^k) := (eg r).mul_left _
  have he (r : ZMod N) : (Real.pi:ℂ)*Complex.cot (Real.pi*(e r:ℂ)) =
      Real.pi*Complex.I-2*Real.pi*Complex.I*∑' k : ℕ,(q (e r))^k := pi_mul_cot_pi_q_exp _
  change ∑ r, χ r*((Real.pi:ℂ)*Complex.cot (Real.pi*(e r:ℂ))) = _
  simp only [he,mul_sub,sum_sub_distrib,←sum_mul,χ.sum_eq_zero_of_ne_one hnt,zero_mul,zero_sub]
  have e1 (r : ZMod N) : χ r*(2*Real.pi*Complex.I*∑' k : ℕ,q (e r)^k) =
      (2*Real.pi*Complex.I)*∑' k : ℕ,χ r*q (e r)^k := by rw [tsum_mul_left]; ring
  simp only [e1,←mul_sum]
  rw [←Summable.tsum_finsetSum (fun r _ => hgeom r)]
  have hk (k : ℕ) : ∑ r,χ r*q (e r)^k=gaussSum χ ZMod.stdAddChar*(χ (k:ZMod N)*(q z)^k) := by
    simp only [e,exp_mul_char,←mul_assoc,←sum_mul,finite_dft hχ hq]
    ring
  simp only [hk,tsum_mul_left]
  ring

end
end TunnellRankinCotangent
end

section
/- Evaluation of the horizontal fibers of the regularization at the critical point. -/
namespace TunnellRankinEisenstein
open Complex TunnellCMRegularized Finset Set TunnellRankinCotangent
open scoped ComplexConjugate Topology
noncomputable section

def cotValue (x : ℂ) : ℂ := Real.pi * cot (Real.pi * x)

lemma cotValue_add_nat (x : ℂ) (m : ℕ) : cotValue (x+m) = cotValue x := by
  have he (w : ℂ) : cot w = (tan w)⁻¹ := by simp [Complex.cot,Complex.tan]
  simp only [cotValue,he,show (Real.pi:ℂ)*(x+(m:ℂ))=Real.pi*x+(m:ℂ)*Real.pi by ring,
    Complex.tan_add_nat_mul_pi]

lemma cotPairs {x : ℂ} (hx : x=0 ∨ x∈integerComplement) :
    HasSum (fun n : ℕ+ => (x-(n.val:ℂ))⁻¹+(x+(n.val:ℂ))⁻¹) (cotValue x-x⁻¹) := by
  rcases hx with rfl | hx
  · simpa [cotValue,Complex.cot] using (hasSum_zero (ι:=ℕ+) (M:=ℂ))
  have hs : Summable (fun n : ℕ+ => (x-(n.val:ℂ))⁻¹+(x+(n.val:ℂ))⁻¹) := by
    rw [summable_pnat_iff_summable_succ (f:=fun n : ℕ => (x-(n:ℂ))⁻¹+(x+(n:ℂ))⁻¹)]
    simpa [cotTerm] using summable_cotTerm hx
  apply hs.hasSum_iff.mpr
  have h := cot_series_rep hx
  simp only [one_div] at h
  exact eq_sub_iff_add_eq.mpr (by simpa only [cotValue,add_comm] using h.symm)

def centralFiber (a : ℕ) (t x : ℂ) (j : ℤ) : ℂ :=
  (a:ℂ)^2 * ((t+x+j)⁻¹ - (t+j)⁻¹) -
    (a:ℂ) * ((t+(a:ℂ)*x+j)⁻¹ - (t+j)⁻¹)

lemma tsum_symmetric (F : ℤ→ℂ) (hF : Summable F) :
    ∑' j, F j = F 0 + ∑' n : ℕ+, (F (-(n.val:ℤ))+F (n.val:ℤ)) := by
  have hp : Summable (fun n : ℕ+ => F (n.val:ℤ)) := hF.comp_injective (Nat.cast_injective.comp PNat.coe_injective)
  have hn : Summable (fun n : ℕ+ => F (-(n.val:ℤ))) := hF.comp_injective (neg_injective.comp (Nat.cast_injective.comp PNat.coe_injective))
  rw [tsum_int_eq_zero_add_tsum_pnat hF, Summable.tsum_add hn hp]
  ring

lemma critical_fiber (a : ℕ) (t x : ℂ) (ht : t=0 ∨ t∈integerComplement)
    (hx : t+x=0 ∨ t+x∈integerComplement) (hax : t+(a:ℂ)*x=0 ∨ t+(a:ℂ)*x∈integerComplement)
    (hs : Summable (centralFiber a t x)) :
    ∑' j, centralFiber a t x j =
      (a:ℂ)^2*(cotValue (t+x)-cotValue t) -
        (a:ℂ)*(cotValue (t+(a:ℂ)*x)-cotValue t) := by
  have h := (((cotPairs hx).sub (cotPairs ht)).mul_left ((a:ℂ)^2)).sub
    (((cotPairs hax).sub (cotPairs ht)).mul_left (a:ℂ))
  rw [tsum_symmetric _ hs]
  have hh : (∑' n : ℕ+, (centralFiber a t x (-(n.val:ℤ))+centralFiber a t x (n.val:ℤ))) = _ :=
    (h.congr_fun (g:=fun n : ℕ+ => centralFiber a t x (-(n.val:ℤ))+centralFiber a t x (n.val:ℤ)) (by
      intro n
      simp only [centralFiber,Int.cast_neg,Int.cast_natCast,sub_eq_add_neg]
      <;> ring)).tsum_eq
  rw [hh]
  simp [centralFiber]
  ring

end
end TunnellRankinEisenstein
end

section
/- The cotangent value of the odd Hurwitz zeta function at s = 1. -/
namespace TunnellRankinEisenstein
open Complex TunnellCMRegularized Filter Set HurwitzZeta
open scoped Topology ComplexConjugate
noncomputable section

lemma horizontal_locally (a : ℕ) (z : ℂ) :
    SummableLocallyUniformlyOn (fun (w : ℤ) => difference a z w) domain := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually domain_open
  intro K hK hc
  obtain ⟨R₀,hR₀⟩ := hc.exists_bound_of_continuousOn (continuous_id (X := ℂ)).continuousOn
  let R := max R₀ 1
  have hR : 0 ≤ R := le_trans (by norm_num : (0:ℝ)≤1) (le_max_right _ _)
  let C := ((a:ℝ)^2+(a:ℝ)^3)*(9*R^2+8*R)*‖z‖^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨fun w => C*|(w:ℝ)|^(-5/2:ℝ),
    (by simpa only [neg_div] using (Real.summable_abs_int_rpow (b:=5/2) (by norm_num)).mul_left C), ?_⟩
  have htop : Tendsto (fun w : ℤ => ‖(w:ℂ)‖) cofinite atTop := by
    exact tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Complex.isClosedEmbedding_intCast
  have ht : Tendsto (fun w : ℤ => ‖z/(w:ℂ)‖) cofinite (𝓝 0) := by
    simp only [norm_div]
    exact tendsto_const_nhds.div_atTop htop
  have ht' : Tendsto (fun w : ℤ => ‖(a:ℂ)*(z/(w:ℂ))‖) cofinite (𝓝 0) := by
    simpa only [norm_mul,mul_zero] using ht.const_mul ‖(a:ℂ)‖
  have hu := ht.eventually_le_const (by norm_num : (0:ℝ)<1/2)
  have hv := ht'.eventually_le_const (by norm_num : (0:ℝ)<1/2)
  have hsu : ∀ᶠ w : ℤ in cofinite, 3*R*‖z/(w:ℂ)‖ ≤ 1 :=
    ((ht.const_mul (3*R)).eventually_le_const (by simp))
  have hsv : ∀ᶠ w : ℤ in cofinite, 3*R*‖(a:ℂ)*(z/(w:ℂ))‖ ≤ 1 :=
    ((ht'.const_mul (3*R)).eventually_le_const (by simp))
  filter_upwards [hu,hv,hsu,hsv,htop.eventually_ge_atTop 1] with w h1 h2 h3 h4 hw
  intro s hs
  have hsR : ‖s‖ ≤ R := (hR₀ s hs).trans (le_max_left _ _)
  rw [← Complex.norm_intCast]
  apply (difference_bound (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hw)) hsR a h1 h2 h3 h4).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le hw (by have := hK hs; change 3/4 < s.re at this; linarith)

def horizontal (a : ℕ) (z s : ℂ) := ∑' j : ℤ, difference a z j s

lemma horizontal_analytic (a : ℕ) (z : ℂ) : AnalyticOnNhd ℂ (horizontal a z) domain := by
  apply DifferentiableOn.analyticOnNhd _ domain_open
  apply (horizontal_locally a z).differentiableOn domain_open
  intro w s _
  unfold difference kernel
  fun_prop

lemma kernel_real (s : ℂ) (w : ℝ) :
    kernel s (w:ℂ)=(SignType.sign w:ℂ)/((|w|:ℝ):ℂ)^(2*s-1) := by
  rcases lt_trichotomy w 0 with hw | rfl | hw
  · have hp : 0 < -w := neg_pos.mpr hw
    rw [kernel,abs_of_neg hw,sign_neg hw,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hw,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'),←Complex.ofReal_log hp.le,
      div_eq_mul_inv,←Complex.exp_neg]
    simp only [SignType.coe_neg,SignType.coe_one]
    rw [show -((Real.log (-w):ℂ)*(2*s-1)) = -2*s*(Real.log (-w):ℂ)+(Real.log (-w):ℂ) by ring,
      Complex.exp_add,←Complex.ofReal_exp,Real.exp_log hp]
    push_cast
    ring
  · simp [kernel]
  · rw [kernel,abs_of_pos hw,sign_pos hw,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hw.ne'),←Complex.ofReal_log hw.le,
      div_eq_mul_inv,←Complex.exp_neg]
    simp only [SignType.coe_one]
    rw [show -((Real.log w:ℂ)*(2*s-1)) = -2*s*(Real.log w:ℂ)+(Real.log w:ℂ) by ring,
      Complex.exp_add,←Complex.ofReal_exp,Real.exp_log hw]
    ring

lemma shifted_hurwitz (x : ℝ) {s : ℂ} (hs : 1<s.re) :
    HasSum (fun j : ℤ => kernel s ((j:ℂ)+(x:ℂ))) (2*hurwitzZetaOdd x (2*s-1)) := by
  have h := (hasSum_int_hurwitzZetaOdd x (s:=2*s-1) (by simp [Complex.mul_re]; linarith)).mul_left (2:ℂ)
  apply h.congr_fun
  intro j
  rw [show (j:ℂ)+(x:ℂ)=((j+x:ℝ):ℂ) by push_cast; rfl,kernel_real]
  ring

end
end TunnellRankinEisenstein
end

section
/- The positive vertical rows of the central Rankin Eisenstein series recover the
quadratic ideal-counting theta series. -/
namespace TunnellRankinCotangent
open Complex Finset TunnellRankin UpperHalfPlane
noncomputable section

lemma lambert (d : ℕ) {r : ℂ} (hr : ‖r‖ < 1) :
    (∑' a : ℕ+, ∑' b : ℕ+, (negWeight d b : ℂ)*r^((a:ℕ)*(b:ℕ))) =
      ∑' m : ℕ, (idealCoeff d m : ℂ)*r^m := by
  let F (x : ℕ+×ℕ+) := (negWeight d x.2:ℂ)*r^((x.1:ℕ)*(x.2:ℕ))
  have hsum : Summable F := by
    have h : Summable (fun x : ℕ+×ℕ+ => ‖r‖^((x.1:ℕ)*(x.2:ℕ))) := by
      simpa using (summable_prod_mul_pow 0 (r:=‖r‖) (by simpa using hr))
    apply h.of_norm_bounded
    intro x
    exact (norm_mul _ _).trans_le (by rw [norm_pow]; exact mul_le_of_le_one_left (by positivity) (norm_weight d _))
  change (∑' a : ℕ+, ∑' b : ℕ+, F (a,b)) = _
  have hS : Summable (fun x => F (sigmaAntidiagonalEquivProd x)) := sigmaAntidiagonalEquivProd.summable_iff.mpr hsum
  rw [← hsum.tsum_prod, ←sigmaAntidiagonalEquivProd.tsum_eq F, hS.tsum_sigma,
    ←tsum_pnat_eq_tsum_of_eq_zero (f:=fun m : ℕ => (idealCoeff d m:ℂ)*r^m) (by simp [idealCoeff])]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  simp only [sigmaAntidiagonalEquivProd,F,Equiv.coe_fn_mk,divisorsAntidiagonalFactors,PNat.mk_coe,
    Nat.mem_divisorsAntidiagonal,Finset.univ_eq_attach,idealCoeff,Int.cast_sum,Finset.sum_mul]
  rw [Finset.sum_attach _ (fun p : ℕ×ℕ => (negWeight d p.2:ℂ)*r^(p.1*p.2)),
    Nat.sum_divisorsAntidiagonal' (fun x y => (negWeight d y:ℂ)*r^(x*y))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hi)]

def multiple (a : ℕ+) (z : ℍ) : ℍ :=
  ⟨(a.val:ℂ)*(z:ℂ), by simpa [Complex.mul_im] using z.im_pos⟩

lemma sum_positive_rows {d : ℕ} (hd : d%4=1) (hs : Squarefree d) (z : ℍ) :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    (∑' a : ℕ+, row (negCharacter d (by omega)) (multiple a z)) =
      (-2*Real.pi*Complex.I*gaussSum (negCharacter d (by omega)) ZMod.stdAddChar) * theta d z := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  have hnt : negCharacter d (by omega)≠1 := by
    intro hz
    have he := negCharacter_odd hd
    rw [DirichletCharacter.Odd,hz,MulChar.one_apply (by simp)] at he
    norm_num at he
  have he (a : ℕ+) := row_qExpansion (TunnellRankinEisenstein.negative_primitive hd hs)
    (TunnellRankinEisenstein.negative_quadratic (by omega)) hnt (multiple a z)
  simp only [he,tsum_mul_left,negCharacter_nat]
  congr 1
  rw [theta,show Function.Periodic.qParam 1 z=q (z:ℂ) by simp [q,Function.Periodic.qParam],
    ←lambert d (show ‖q z‖<1 from norm_exp_two_pi_I_lt_one _)]
  apply tsum_congr
  intro a
  rw [←tsum_pnat_eq_tsum_of_eq_zero (f:=fun b : ℕ => (negWeight d b:ℂ)*q (multiple a z)^b) (by simp [negWeight])]
  apply tsum_congr
  intro b
  congr 1
  change (exp (_*((a.val:ℂ)*(z:ℂ))))^b.val = (exp (_*(z:ℂ)))^(a.val*b.val)
  simp only [← Complex.exp_nat_mul,Nat.cast_mul]
  congr 1
  ring

end
end TunnellRankinCotangent
end

section
/- The explicit central specialization of the Rankin Eisenstein lattice. -/
namespace TunnellRankinEisenstein
open Complex TunnellCMRegularized TunnellRankin TunnellRankinCotangent Finset Set
open UpperHalfPlane hiding I
open scoped ComplexConjugate Topology

noncomputable section

def coord (k : ℕ) (z : ℍ) (c : ℤ) : ℂ := (c:ℂ)*((k:ℂ)*(z:ℂ))
def offset {N : ℕ} (r : ZMod N) : ℂ := (r.val:ℂ)/N

def centralIndex (k : ℕ) [NeZero k] (z : ℍ) : ℤ×ℤ ≃ (periods k z).lattice :=
  (Equiv.prodComm ℤ ℤ).trans (periods k z).latticeEquivProd.symm.toEquiv

lemma centralIndex_val (k : ℕ) [NeZero k] (z : ℍ) (p : ℤ×ℤ) :
    (centralIndex k z p:ℂ)=(p.2:ℂ)+(p.1:ℂ)*((k:ℂ)*conj (z:ℂ)) := by
  change ((periods k z).latticeEquivProd.symm (p.2,p.1):ℂ)=_
  rw [PeriodPair.latticeEquiv_symm_apply]
  simp [periods]

lemma difference_index {N k : ℕ} [NeZero N] [NeZero k] (z : ℍ) (r : ZMod N) (p : ℤ×ℤ) :
    difference (aux N) (offset r) (centralIndex k z p) 1 =
      centralFiber (aux N) (coord k z p.1) (offset r) p.2 := by
  rw [centralIndex_val]
  simp only [difference,kernel_one,centralFiber,coord,offset,map_inv₀,map_add,map_mul,map_div₀,
    map_intCast,map_natCast,Complex.conj_conj]
  abel_nf

lemma indexed_hasSum {N k : ℕ} [NeZero N] [NeZero k] (z : ℍ) (r : ZMod N) :
    HasSum (fun p : ℤ×ℤ => centralFiber (aux N) (coord k z p.1) (offset r) p.2)
      (regularized (periods k z) (aux N) (offset r) 1) := by
  have h := (centralIndex k z).hasSum_iff.mpr
    ((regularized_summable (periods k z) (aux N) (offset r)).summable
      (show (1:ℂ)∈domain by norm_num [domain])).hasSum
  exact h.congr_fun (fun p => (difference_index z r p).symm)

lemma aux_offset {N : ℕ} [NeZero N] (r : ZMod N) :
    (aux N:ℂ)*offset r=offset r+(r.val:ℂ) := by
  have hN : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  unfold aux offset
  push_cast
  field_simp [hN]
  ring

lemma coord_im {k : ℕ} [NeZero k] (z : ℍ) {c : ℤ} (hc : c≠0) :
    (coord k z c).im≠0 := by
  simp [coord,Complex.mul_im,hc,NeZero.ne k,z.im_pos.ne']

lemma offset_im {N : ℕ} (r : ZMod N) : (offset r).im=0 := by
  simp only [offset,Complex.div_im,Complex.natCast_im,mul_zero,zero_mul,sub_zero,zero_div]

lemma offset_mem {N : ℕ} [NeZero N] (r : ZMod N) (hr : r≠0) : offset r∈integerComplement := by
  rintro ⟨b,hb⟩
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  unfold offset at hb
  have h : (b:ℝ)=(r.val:ℝ)/N := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_intCast,Complex.ofReal_div,Complex.ofReal_natCast] using hb
  have h1 : (0:ℝ)<(b:ℝ) := by rw [h]; exact div_pos (Nat.cast_pos.mpr (ZMod.val_pos.mpr hr)) hN
  have h2 : (b:ℝ)<1 := by rw [h,div_lt_one hN]; exact_mod_cast r.val_lt
  have e1 : 0<b := by exact_mod_cast h1
  have e2 : b<1 := by exact_mod_cast h2
  omega

lemma critical_fiber_row {N k : ℕ} [NeZero N] [NeZero k] (z : ℍ) (r : ZMod N) (c : ℤ) :
    ∑' j : ℤ, centralFiber (aux N) (coord k z c) (offset r) j =
      ((aux N:ℂ)^2-(aux N:ℂ))*(cotValue (coord k z c+offset r)-cotValue (coord k z c)) := by
  by_cases hr : r=0
  · subst r
    simp [offset,centralFiber]
  let t := coord k z c
  have ht : t=0 ∨ t∈integerComplement := by
    by_cases hc : c=0
    · simp [t,coord,hc]
    · right; rintro ⟨b,hb⟩
      exact coord_im z hc (by simpa using (congrArg Complex.im hb).symm)
  have hx : t+offset r∈integerComplement := by
    by_cases hc : c=0
    · simpa [t,coord,hc] using offset_mem r hr
    · rintro ⟨b,hb⟩; exact coord_im z hc (by simpa [t,offset_im] using (congrArg Complex.im hb).symm)
  have hx' : t+(aux N:ℂ)*offset r∈integerComplement := by
    rw [aux_offset,←add_assoc]
    simpa using (add_intCast_mem_integerComplement (r.val:ℤ)).mpr hx
  change (∑' j : ℤ, centralFiber (aux N) t (offset r) j) = _
  rw [critical_fiber _ _ _ ht (.inr hx) (.inr hx') ((indexed_hasSum z r).summable.prod_factor c),
    aux_offset,←add_assoc,cotValue_add_nat]
  ring

theorem regular_rows {N k : ℕ} [NeZero N] [NeZero k] {χ : DirichletCharacter ℂ N} (hnt : χ≠1) (z : ℍ) :
    HasSum (fun c : ℤ => row χ (coord k z c)) (regular N k χ z 1) := by
  classical
  let A := (aux N:ℂ)^2-(aux N:ℂ)
  have hA : A≠0 := aux_ne N
  have hh (r : ZMod N) := (indexed_hasSum (k:=k) z r).prod_fiberwise
    (fun c => ((indexed_hasSum (k:=k) z r).summable.prod_factor c).hasSum)
  have he := hasSum_sum (fun r (_ : r∈(univ:Finset (ZMod N))) => (hh r).mul_left (χ r))
  have h := he.mul_right A⁻¹
  change HasSum _ ((∑ r : ZMod N, χ r * regularized (periods k z) (aux N) (offset r) 1)*A⁻¹)
  apply h.congr_fun
  intro c
  simp only [critical_fiber_row]
  have h0 := χ.sum_eq_zero_of_ne_one hnt
  change (∑ r,χ r*cotValue (coord k z c+offset r))=
    (∑ r,χ r*(A*(cotValue (coord k z c+offset r)-cotValue (coord k z c))))*A⁻¹
  simp_rw [show ∀ b u v : ℂ,b*(A*(u-v))=A*(b*u-b*v) by intros; ring]
  rw [←mul_sum,sum_sub_distrib,←sum_mul,h0,zero_mul,sub_zero]
  field_simp
lemma row_neg {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) (x : ℂ) :
    row χ (-x)=row χ x := by
  classical
  have hc (y : ℂ) : cotValue (-y)= -cotValue y := by simp [cotValue,Complex.cot,div_neg]
  change (∑ r,χ r*cotValue (-x+offset r))=∑ r,χ r*cotValue (x+offset r)
  apply Fintype.sum_equiv (Equiv.neg _) _ _
  intro r
  simp only [Equiv.neg_apply,hχ.eval_neg]
  by_cases hr : r=0
  · subst r; simp [offset,hc]
  · haveI : NeZero r := ⟨hr⟩
    have hN : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
    have he : x+offset (-r) = -(-x+offset r)+(1:ℕ) := by
      simp only [offset,ZMod.val_neg_of_ne_zero,Nat.cast_sub r.val_lt.le,Nat.cast_one]
      field_simp
      ring
    rw [he,cotValue_add_nat,hc,neg_mul_neg]

/- The normalized Eisenstein lattice specializes at the central point to the quadratic
ideal-counting theta series, with an explicit finite cotangent constant. -/
theorem regular_one {d k : ℕ} [NeZero k] (hd : d%4=1) (hs : Squarefree d) (z : ℍ) :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    let χ := negCharacter d (by omega)
    regular (4*(2*d)) k χ z 1 = row χ 0 +
      (-4*Real.pi*Complex.I*gaussSum χ ZMod.stdAddChar)*theta d (multiple ⟨k,NeZero.pos k⟩ z) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let χ := negCharacter d (by omega)
  have hodd : χ.Odd := negCharacter_odd hd
  have hnt : χ≠1 := by
    intro h
    rw [DirichletCharacter.Odd,h,MulChar.one_apply (by simp)] at hodd
    norm_num at hodd
  have h := regular_rows (k:=k) hnt z
  have he : Function.Even (fun c : ℤ => row χ (coord k z c)) := by
    intro c
    simp only [coord,Int.cast_neg,neg_mul,row_neg hodd]
  change regular _ k χ z 1 = row χ 0 + (-4*Real.pi*Complex.I*gaussSum χ ZMod.stdAddChar)*theta d (multiple (⟨k,NeZero.pos k⟩ : ℕ+) z)
  rw [←h.tsum_eq,tsum_int_eq_zero_add_two_mul_tsum_pnat he h.summable]
  have hz (n : ℕ+) : coord k z n.val=(multiple n (multiple ⟨k,NeZero.pos k⟩ z):ℂ) := by simp [coord,multiple]
  have hh : (∑' n : ℕ+,row χ (coord k z (n.val:ℤ))) = _ := (tsum_congr (fun n : ℕ+ => congrArg (row χ) (hz n))).trans (sum_positive_rows hd hs (multiple (⟨k,NeZero.pos k⟩ : ℕ+) z))
  rw [hh]
  simp only [coord,Int.cast_zero,zero_mul,χ]
  ring

end
end TunnellRankinEisenstein
end

section
/- The exact Dirichlet L-value of the constant term of the Rankin Eisenstein family. -/
namespace TunnellRankinEisenstein
open Complex TunnellCMRegularized TunnellRankinCotangent HurwitzZeta Filter Set Finset
open scoped ComplexConjugate Topology

noncomputable section

lemma horizontal_large {a : ℕ} {x : ℝ} {m : ℤ} (hx : (a:ℝ)*x=x+(m:ℝ)) {s : ℂ} (hs : 1<s.re) :
    horizontal a x s=((a:ℂ)^2-(a:ℂ))*(2*hurwitzZetaOdd x (2*s-1)) := by
  have hh := shifted_hurwitz x hs
  have h0 : HasSum (fun j : ℤ => kernel s j) 0 := by
    have hz : hurwitzZetaOdd 0 (2*s-1)=0 := by
      have h := hurwitzZetaOdd_neg 0 (2*s-1)
      simp only [neg_zero] at h
      linear_combination h/2
    simpa [hz] using shifted_hurwitz 0 hs
  have hax : (a:ℂ)*(x:ℂ)=(x:ℂ)+(m:ℂ) := by exact_mod_cast hx
  have hh' := (Equiv.addRight m).hasSum_iff.mpr hh
  have hm : HasSum (fun j : ℤ => kernel s ((j:ℂ)+(a:ℂ)*(x:ℂ))) (2*hurwitzZetaOdd x (2*s-1)) := by
    apply hh'.congr_fun
    intro j
    rw [hax]
    simp [add_comm,add_assoc,add_left_comm]
  have H := (((hh.sub h0).mul_left ((a:ℂ)^2)).sub ((hm.sub h0).mul_left (a:ℂ))).tsum_eq
  unfold horizontal
  simpa only [difference,sub_zero,sub_mul] using H

lemma horizontal_eq {a : ℕ} {x : ℝ} {m : ℤ} (hx : (a:ℝ)*x=x+(m:ℝ)) :
    horizontal a x 1=((a:ℂ)^2-(a:ℂ))*(2*hurwitzZetaOdd x 1) := by
  let G (s : ℂ) := ((a:ℂ)^2-(a:ℂ))*(2*hurwitzZetaOdd x (2*s-1))
  have hG : AnalyticOnNhd ℂ G domain := by
    apply analyticOnNhd_const.mul
    apply analyticOnNhd_const.mul
    intro s _
    exact ((differentiable_hurwitzZetaOdd x).analyticAt _).comp (by fun_prop)
  have he : EqOn (horizontal a x) G domain :=
    (horizontal_analytic _ _).eqOn_of_preconnected_of_eventuallyEq hG
      (convex_halfSpace_re_gt _).isPreconnected (by norm_num [domain] : (2:ℂ)∈domain) (by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (show (1:ℝ)<(2:ℂ).re by norm_num)] with s hs
        exact horizontal_large hx hs)
  convert he (by norm_num [domain] : (1:ℂ)∈domain) using 1
  dsimp [G]
  norm_num

lemma cot_offset {N : ℕ} [NeZero N] (r : ZMod N) :
    cotValue (offset r)=2*hurwitzZetaOdd (ZMod.toAddCircle r) 1 := by
  let x : ℝ := (r.val:ℝ)/N
  have hx : (aux N:ℝ)*x=x+(r.val:ℤ) := by
    have hN : (N:ℝ)≠0 := by exact_mod_cast NeZero.ne N
    dsimp [aux,x]
    push_cast
    field_simp
    ring
  have H := horizontal_eq hx
  have he : (x:ℂ)=offset r := by simp only [x,offset,Complex.ofReal_div,Complex.ofReal_natCast]
  rw [he] at H
  have t := critical_fiber_row (k:=1) UpperHalfPlane.I r 0
  have h (j : ℤ) : difference (aux N) (offset r) j 1=centralFiber (aux N) 0 (offset r) j := by
    simpa [centralIndex_val,coord] using difference_index (k:=1) UpperHalfPlane.I r (0,j)
  simp only [horizontal,h] at H
  have h0 : cotValue 0=0 := by simp [cotValue,Complex.cot]
  simp only [coord,Int.cast_zero,zero_mul,zero_add,h0,sub_zero] at t
  rw [t] at H
  rw [ZMod.toAddCircle_apply]
  exact mul_left_cancel₀ (aux_ne N) H

lemma constant_L {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (ho : χ.Odd) :
    row χ 0=2*(N:ℂ)*χ.LFunction 1 := by
  have hN : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  change (∑ r,χ r*cotValue (0+offset r))=_
  simp only [zero_add,cot_offset,DirichletCharacter.LFunction,ZMod.LFunction_def_odd ho.to_fun,
    Complex.cpow_neg_one]
  simp_rw [show ∀ a b : ℂ,a*(2*b)=2*(a*b) by intros; ring,←mul_sum]
  field_simp

theorem regular_central {d k : ℕ} [NeZero k] (hd : d%4=1) (hs : Squarefree d) (z : UpperHalfPlane) :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    let χ := TunnellRankin.negCharacter d (by omega)
    regular (4*(2*d)) k χ z 1 =
      2*((4*(2*d):ℕ):ℂ)*χ.LFunction 1 +
      (-4*Real.pi*Complex.I*gaussSum χ ZMod.stdAddChar)*TunnellRankin.theta d (multiple ⟨k,NeZero.pos k⟩ z) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  exact (regular_one hd hs z).trans (congrArg (·+_) (constant_L (TunnellRankin.negCharacter_odd hd)))

end
end TunnellRankinEisenstein
end

section
/- The class-group theta Dirichlet series factors as ζ(s)L(χ,s) on Re(s)>1. -/
namespace TunnellClassThetaMellin
open Complex TunnellRankin DirichletCharacter
noncomputable section

lemma class_hasSum {d : ℕ} (hd : 0<d) {s : ℂ} (hs : 1<s.re) :
    HasSum (fun m : ℕ => (idealCoeff d m:ℂ)/(m:ℂ)^s) (riemannZeta s*negativeL d hd s) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let χ := negCharacter d hd
  have hc : LSeriesHasSum (fun n : ℕ => χ n) s (negativeL d hd s) := by
    rw [negativeL,DirichletCharacter.LFunction_eq_LSeries _ hs]
    exact (χ.LSeriesSummable_of_one_lt_re hs).LSeriesHasSum
  apply ((LSeriesHasSum_one hs).convolution hc).congr_fun
  intro m
  rw [LSeries.term_of_ne_zero' (by intro e; simp [e] at hs; linarith)]
  congr 1
  simp only [LSeries.convolution_def,Pi.one_apply,one_mul,χ,negCharacter_nat,
    idealCoeff,Int.cast_sum,Nat.sum_divisorsAntidiagonal' (fun _ b => (negWeight d b:ℂ))]
end
end TunnellClassThetaMellin
end

section
/- Hermite normal forms for the ideals of the imaginary quadratic order ℤ[√−n]. -/
namespace TunnellIdealHNF
abbrev R (n : ℕ) := Zsqrtd (-(n:ℤ))

structure Data (n : ℕ) where
  c : ℕ
  a : ℕ
  b : ℕ
  pos_c : 0<c
  pos_a : 0<a
  lt_b : b<a
  divides : (a:ℤ)∣(b:ℤ)^2+n

def ideal {n : ℕ} (s : Data n) : Ideal (R n) where
  carrier := {x | (s.c:ℤ)∣x.im ∧ (s.c:ℤ)*s.a∣x.re-s.b*x.im}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx,hx'⟩ ⟨hy,hy'⟩
    refine ⟨dvd_add hx hy,?_⟩
    change _ ∣ x.re+y.re-_* (x.im+y.im)
    rw [show x.re+y.re-(s.b:ℤ)*(x.im+y.im)=(x.re-s.b*x.im)+(y.re-s.b*y.im) by ring]
    exact dvd_add hx' hy'
  smul_mem' := by
    rintro x y ⟨⟨u,hu⟩,⟨t,ht⟩⟩
    obtain ⟨C,hC⟩ := s.divides
    change _ ∣ (x*y).im ∧ _ ∣ (x*y).re - _ * (x*y).im
    rw [Zsqrtd.re_mul,Zsqrtd.im_mul]
    constructor
    · exact ⟨x.re*u+(s.a*t+s.b*u)*x.im,by linear_combination (x.re+s.b*x.im)*hu+x.im*ht⟩
    · exact ⟨(x.re-s.b*x.im)*t-x.im*C*u,by linear_combination (x.re-s.b*x.im)*ht-
        x.im*((s.b:ℤ)^2+n)*hu-x.im*(s.c:ℤ)*u*hC⟩

lemma mem_ideal {n : ℕ} (s : Data n) (x : R n) : x∈ideal s ↔
    (s.c:ℤ)∣x.im ∧ (s.c:ℤ)*s.a∣x.re-s.b*x.im := Iff.rfl

lemma real_slice {n : ℕ} (s : Data n) (x : ℤ) : (⟨x,0⟩:R n)∈ideal s ↔ (s.c:ℤ)*s.a∣x := by simp [mem_ideal]
lemma lift_basis {n : ℕ} (s : Data n) : (⟨s.c*s.b,s.c⟩:R n)∈ideal s := by simp [mem_ideal,mul_comm]
lemma real_basis {n : ℕ} (s : Data n) : (⟨s.c*s.a,0⟩:R n)∈ideal s := (real_slice _ _).mpr dvd_rfl

lemma positive_generator (S : Ideal ℤ) {x : ℤ} (hx : x∈S) (hx0 : x≠0) :
    ∃ c : ℕ, 0<c ∧ ∀ y : ℤ, y∈S ↔ (c:ℤ)∣y := by
  let a := Submodule.IsPrincipal.generator S
  have h (y : ℤ) : y∈S ↔ a∣y := Submodule.IsPrincipal.mem_iff_generator_dvd S
  have h0 : a≠0 := by intro he; have := (h x).mp hx; simp [he,hx0] at this
  exact ⟨a.natAbs,Int.natAbs_pos.mpr h0,fun y => (h y).trans Int.natAbs_dvd.symm⟩

def imHom (n : ℕ) : R n →+ ℤ where
  toFun := Zsqrtd.im
  map_zero' := rfl
  map_add' _ _ := rfl

lemma cast_int {n : ℕ} (a : ℤ) : (a:R n)=⟨a,0⟩ := rfl

lemma normal_form {n : ℕ} (hn : 0<n) {I : Ideal (R n)} (hI : I≠⊥) :
    ∃ s : Data n, I=ideal s := by
  obtain ⟨z,hz,hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hnorm : (z.norm:R n)∈I := by rw [Zsqrtd.norm_eq_mul_conj]; exact I.mul_mem_right _ hz
  have hnorm0 : z.norm≠0 := by
    intro h; apply hz0
    change z.re*z.re- -(n:ℤ)*z.im*z.im=0 at h
    have ha : z.im=0 := by
      by_contra ha
      have hsq : 0<z.im*z.im := mul_self_pos.mpr ha
      have e := mul_pos (show 0<(n:ℤ) by exact_mod_cast hn) hsq
      nlinarith [mul_self_nonneg z.re]
    have hb : z.re=0 := by rw [ha] at h; simpa using h
    exact Zsqrtd.ext hb ha
  let S := I.comap (Int.castRingHom (R n))
  obtain ⟨A,hA,real_iff⟩ := positive_generator S hnorm hnorm0
  change ∀ y : ℤ, (y:R n)∈I ↔ (A:ℤ)∣y at real_iff
  have hR := (real_iff A).mpr dvd_rfl
  let T := (I.toAddSubgroup.map (imHom n)).toIntSubmodule
  have hT : ∀ y : ℤ, y∈T ↔ ∃ x∈I, x.im=y := fun _ => Iff.rfl
  have hroot (x : R n) (h : x∈I) : x.re∈T := (hT _).mpr ⟨Zsqrtd.sqrtd*x,I.mul_mem_left _ h,by simp [Zsqrtd.im_mul]⟩
  obtain ⟨c,hc,imag_iff⟩ := positive_generator T (hroot _ hR) (show ((A:R n).re:ℤ)≠0 by simpa using hA.ne')
  have ca : (c:ℤ)∣A := (imag_iff _).mp (hroot _ hR)
  obtain ⟨a,haa⟩ := (Int.natCast_dvd_natCast.mp ca)
  have hap : 0<a := by by_contra! h; have := Nat.eq_zero_of_le_zero h; simp [this] at haa; omega
  have eA : (A:ℤ)=c*a := by exact_mod_cast haa
  obtain ⟨v,hv,he⟩ := (hT _).mp ((imag_iff c).mpr dvd_rfl)
  obtain ⟨b₀,hb₀⟩ := (imag_iff v.re).mp (hroot v hv)
  let b := b₀%(a:ℤ)
  have hbpos : 0≤b := Int.emod_nonneg _ (by exact_mod_cast hap.ne')
  have hblt : b<(a:ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hap)
  have hlin : (⟨c*b,c⟩:R n)∈I := by
    have hh := I.sub_mem hv (I.mul_mem_left ((b₀/(a:ℤ):ℤ):R n) hR)
    convert hh using 1
    apply Zsqrtd.ext
    · simp only [Zsqrtd.re_sub,Zsqrtd.re_mul,cast_int,mul_zero,add_zero]
      change (c:ℤ)*b = v.re - b₀/a*A
      rw [eA,hb₀]
      dsimp [b]
      linear_combination (c:ℤ)*(Int.emod_add_mul_ediv b₀ a)
    · simp only [Zsqrtd.im_sub,Zsqrtd.im_mul,cast_int,mul_zero,zero_mul,zero_add,sub_zero]; exact he.symm
  have mem (x : R n) : x∈I ↔ (c:ℤ)∣x.im ∧ (A:ℤ)∣x.re-b*x.im := by
    constructor
    · intro hx
      obtain ⟨t,ht⟩ := (imag_iff x.im).mp ((hT _).mpr ⟨x,hx,rfl⟩)
      refine ⟨⟨t,ht⟩,(real_iff _).mp ?_⟩
      have hh := I.sub_mem hx (I.mul_mem_left (t:R n) hlin)
      convert hh using 1; apply Zsqrtd.ext
      · change x.re-b*x.im=x.re-(t*(c*b)+ -(n:ℤ)*0*c); rw [ht]; ring
      · change (0:ℤ)=x.im-(t*c+0*(c*b)); rw [ht]; ring
    · rintro ⟨⟨t,ht⟩,hA'⟩
      have hh := I.add_mem ((real_iff _).mpr hA') (I.mul_mem_left (t:R n) hlin)
      convert hh using 1; apply Zsqrtd.ext
      · change x.re=x.re-b*x.im+(t*(c*b)+ -(n:ℤ)*0*c); rw [ht]; ring
      · change x.im=0+(t*c+0*(c*b)); rw [ht]; ring
  have hmultiple := ((mem _).mp (I.mul_mem_left Zsqrtd.sqrtd hlin)).2
  rw [Zsqrtd.re_mul,Zsqrtd.im_mul] at hmultiple
  simp only [Zsqrtd.re_sqrtd,Zsqrtd.im_sqrtd,zero_mul,mul_one,one_mul,zero_add] at hmultiple
  obtain ⟨t,ht⟩ := hmultiple
  have e : (b^2+(n:ℤ))=(a:ℤ)*(-t) := by
    apply mul_left_cancel₀ (show (c:ℤ)≠0 by exact_mod_cast hc.ne')
    rw [eA] at ht
    linear_combination -ht
  let s : Data n := ⟨c,a,b.toNat,hc,hap,by omega,by exact ⟨-t,by simpa [Int.toNat_of_nonneg hbpos] using e⟩⟩
  refine ⟨s,?_⟩
  ext x
  rw [mem,mem_ideal]
  change _ ↔ (c:ℤ)∣x.im ∧ (c:ℤ)*a∣x.re-b.toNat*x.im
  rw [←eA,Int.toNat_of_nonneg hbpos]

lemma ideal_ne_bot {n : ℕ} (s : Data n) : ideal s≠⊥ := by
  intro h
  have he := real_basis s
  rw [h] at he
  have hh := congrArg Zsqrtd.re (show (⟨(s.c:ℤ)*s.a,0⟩:R n)=0 from he)
  change (s.c:ℤ)*s.a=0 at hh
  exact (mul_ne_zero (by exact_mod_cast s.pos_c.ne') (by exact_mod_cast s.pos_a.ne')) hh

lemma ideal_injective {n : ℕ} : Function.Injective (@ideal n) := by
  intro s t h
  have mono {s t : Data n} (h : ideal s ≤ ideal t) : t.c∣s.c ∧ t.c*t.a∣s.c*s.a ∧ (t.c:ℤ)*t.a∣s.c*s.b-t.b*s.c := by
    have e := (mem_ideal _ _).mp (h (lift_basis s))
    have e' := (real_slice _ _).mp (h (real_basis s))
    exact ⟨Int.natCast_dvd_natCast.mp (show (t.c:ℤ)∣(s.c:ℤ) from e.1),by exact_mod_cast e',e.2⟩
  obtain ⟨c₁,a₁,b₁⟩ := mono h.le
  obtain ⟨c₂,a₂,_⟩ := mono h.ge
  have c := Nat.dvd_antisymm c₂ c₁
  have ca := Nat.dvd_antisymm a₂ a₁
  have a : s.a=t.a := by rw [←c] at ca; exact Nat.eq_of_mul_eq_mul_left s.pos_c ca
  rw [←c,←a] at b₁
  obtain ⟨k,hk⟩ := b₁
  have he : (s.b:ℤ)-(t.b:ℤ)=s.a*k := by
    apply mul_left_cancel₀ (show (s.c:ℤ)≠0 by exact_mod_cast s.pos_c.ne')
    linear_combination hk
  have hm : (t.b:ℤ) ≡ (s.b:ℤ) [ZMOD s.a] := Int.modEq_iff_dvd.mpr ⟨k,he⟩
  have eb : t.b=s.b := by
    change (t.b:ℤ)%s.a=(s.b:ℤ)%s.a at hm
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast a ▸ t.lt_b),Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.lt_b)] at hm
    exact_mod_cast hm
  cases s; cases t; dsimp only at c a eb; congr; exact eb.symm

def residues {n : ℕ} (s : Data n) : R n →+ (ZMod s.c × ZMod (s.c*s.a)) where
  toFun x := (x.im,(x.re:ZMod (s.c*s.a))-s.b*x.im)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]; abel

lemma residues_surj {n : ℕ} (s : Data n) : Function.Surjective (residues s) := by
  rintro ⟨u,t⟩
  letI : NeZero s.c := ⟨s.pos_c.ne'⟩
  letI : NeZero (s.c*s.a) := ⟨mul_ne_zero s.pos_c.ne' s.pos_a.ne'⟩
  exact ⟨⟨(t.val:ℤ)+s.b*u.val,u.val⟩,by simp [residues]⟩

lemma residues_ker {n : ℕ} (s : Data n) : (residues s).ker=(ideal s).toAddSubgroup := by
  ext x
  change ((x.im:ZMod s.c),(x.re:ZMod (s.c*s.a))-s.b*x.im)=(0,0) ↔ _
  simp only [Prod.mk.injEq,mem_ideal,ZMod.intCast_zmod_eq_zero_iff_dvd]
  have he : ((x.re:ZMod (s.c*s.a))-s.b*x.im) = ((x.re-s.b*x.im:ℤ):ZMod (s.c*s.a)) := by push_cast; rfl
  rw [he,ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_mul]
  rfl

theorem quotient_card {n : ℕ} (s : Data n) : Nat.card (R n ⧸ ideal s)=s.c^2*s.a := by
  letI : NeZero s.c := ⟨s.pos_c.ne'⟩
  letI : NeZero (s.c*s.a) := ⟨mul_ne_zero s.pos_c.ne' s.pos_a.ne'⟩
  let e := (AddSubgroup.quotientEquivOfEq (residues_ker s).symm).trans (QuotientAddGroup.quotientKerEquivOfSurjective (residues s) (residues_surj s)).toEquiv
  have h := Nat.card_congr e
  change Nat.card (R n ⧸ ideal s)=_ at h
  simpa [Nat.card_prod,Nat.card_zmod,pow_two,mul_assoc] using h

end TunnellIdealHNF
end

section
/- The ideal times its conjugate is the principal ideal generated by its index. -/
namespace TunnellIdealHNF

def conjugate {n : ℕ} (I : Ideal (R n)) := I.comap (starRingEnd _)
lemma mem_conjugate {n : ℕ} (I : Ideal (R n)) (x : R n) : x∈conjugate I ↔ star x∈I := Iff.rfl
def idx {n : ℕ} (s : Data n) : ℕ := s.c^2*s.a

lemma basis_expansion {n : ℕ} (s : Data n) {x : R n} (hx : x∈ideal s) :
    ∃ u v : ℤ, x=⟨s.c*(s.a*u+s.b*v),s.c*v⟩ := by
  obtain ⟨⟨v,hv⟩,⟨u,hu⟩⟩ := (mem_ideal s x).mp hx
  exact ⟨u,v,Zsqrtd.ext (by dsimp only; linear_combination hu+(s.b:ℤ)*hv) hv⟩

lemma primitive_coeffs {n : ℕ} (hn : Squarefree n) (h₂ : n%4=2) (s : Data n) {C : ℤ}
    (hC : (s.b:ℤ)^2+n=s.a*C) : ∃ x y z : ℤ, (s.a:ℤ)*x+(2*s.b)*y+C*z=1 := by
  let a : ℤ := s.a
  let b : ℤ := s.b
  let g := Int.gcd a (2*b)
  let h := Int.gcd (g:ℤ) C
  have h₁ : (h:ℤ) ∣ a := (Int.gcd_dvd_left (g:ℤ) C).trans (Int.gcd_dvd_left a (2*b))
  have h₂' : (h:ℤ) ∣ 2*b := (Int.gcd_dvd_left (g:ℤ) C).trans (Int.gcd_dvd_right a (2*b))
  have h₃ : (h:ℤ) ∣ C := Int.gcd_dvd_right (g:ℤ) C
  have hh : h=1 := by
    by_contra e
    obtain ⟨p,hp,hp'⟩ := Nat.exists_prime_and_dvd e
    have hpz := Int.natCast_dvd_natCast.mpr hp'
    obtain ⟨A,hA⟩ := hpz.trans h₁
    obtain ⟨D,hD⟩ := hpz.trans h₃
    change b^2+n=a*C at hC
    by_cases hp2 : p=2
    · subst p
      have he : (b:ZMod 4)^2+2=0 := by
        have hh := congrArg (fun t:ℤ => (t:ZMod 4)) hC
        rw [hA,hD] at hh; push_cast at hh
        have hn₂ : (n:ZMod 4)=2 := by apply ZMod.val_injective 4; rw [ZMod.val_natCast,h₂]; decide
        rw [hn₂] at hh
        calc _=2*(A:ZMod 4)*(2*(D:ZMod 4)) := hh
             _=(4:ZMod 4)*(A*D) := by ring
             _=0 := by rw [show (4:ZMod 4)=0 by decide,zero_mul]
      exact (show ∀ z : ZMod 4, z^2+2≠0 by decide) _ he
    · have hpn : ¬(p:ℤ)∣2 := by
        intro h; have ht : p∣2 := by exact_mod_cast h
        rcases (Nat.dvd_prime Nat.prime_two).mp ht with h|h
        · exact hp.ne_one h
        · exact hp2 h
      obtain ⟨B,hB⟩ := ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp (hpz.trans h₂')).resolve_left hpn
      have he : (p:ℤ)*p∣n := ⟨A*D-B^2,by rw [hA,hD,hB] at hC; linear_combination hC⟩
      have ht : p*p∣n := by exact_mod_cast he
      exact hp.ne_one (Nat.isUnit_iff.mp (hn p ht))
  have hf := Int.gcd_eq_gcd_ab a (2*b)
  have hf' := Int.gcd_eq_gcd_ab (g:ℤ) C
  change (g:ℤ)=_ at hf
  change (h:ℤ)=_ at hf'
  rw [hh] at hf'; norm_cast at hf'
  refine ⟨Int.gcdA a (2*b)*Int.gcdA (g:ℤ) C,Int.gcdB a (2*b)*Int.gcdA (g:ℤ) C,Int.gcdB (g:ℤ) C,?_⟩
  change a*_+(2*b)*_+C*_=1
  linear_combination -hf' - Int.gcdA (g:ℤ) C*hf

theorem times_conj {n : ℕ} (hn : Squarefree n) (h₂ : n%4=2) (s : Data n) :
    ideal s*conjugate (ideal s)=Ideal.span {((idx s:ℕ):R n)} := by
  let N : ℤ := idx s
  have Ne : N=(s.c:ℤ)^2*s.a := by simp [N,idx]
  obtain ⟨C,hC⟩ := s.divides
  let P := ideal s*conjugate (ideal s)
  change P=Ideal.span {(N:R n)}
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro x hx y hy
    obtain ⟨u,v,hx'⟩ := basis_expansion s hx
    obtain ⟨t,w,hy'⟩ := basis_expansion s ((mem_conjugate _ _).mp hy)
    apply Ideal.mem_span_singleton.mpr
    refine ⟨⟨s.a*u*t+s.b*(u*w+v*t)+C*v*w,v*t-u*w⟩,?_⟩
    have e : y=star (⟨s.c*(s.a*t+s.b*w),s.c*w⟩:R n) := by rw [←hy',star_star]
    rw [hx',e]
    apply Zsqrtd.ext <;> simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.re_star,Zsqrtd.im_star,cast_int,Ne]
    · linear_combination (s.c:ℤ)^2*v*w*hC
    · ring
  · rw [Ideal.span_singleton_le_iff_mem]
    let g : R n := ⟨s.c*s.a,0⟩
    let u : R n := ⟨s.c*s.b,s.c⟩
    have g₁ : g∈ideal s := real_basis s
    have u₁ : u∈ideal s := lift_basis s
    have g₂ : g∈conjugate (ideal s) := by apply (mem_conjugate _ _).mpr; simpa [g,Zsqrtd.star_mk] using g₁
    have u₂ : star u∈conjugate (ideal s) := (mem_conjugate _ _).mpr (by simpa using u₁)
    have hA : ((N*(s.a:ℤ):ℤ):R n)∈P := by
      have hh : g*g=((N*(s.a:ℤ):ℤ):R n) := by
        change g*g=⟨N*(s.a:ℤ),0⟩
        apply Zsqrtd.ext <;> simp only [g,Ne,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring
      rw [←hh]; exact Ideal.mul_mem_mul g₁ g₂
    have hB : ((N*(2*s.b:ℤ):ℤ):R n)∈P := by
      have hh : u*g+g*star u=((N*(2*s.b:ℤ):ℤ):R n) := by
        change u*g+g*star u=⟨N*(2*s.b:ℤ),0⟩
        apply Zsqrtd.ext <;> simp only [g,u,Ne,Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.star_mk] <;> ring
      rw [←hh]; exact P.add_mem (Ideal.mul_mem_mul u₁ g₂) (Ideal.mul_mem_mul g₁ u₂)
    have hD : ((N*C:ℤ):R n)∈P := by
      have hh : u*star u=((N*C:ℤ):R n) := by
        rw [←Zsqrtd.norm_eq_mul_conj]; congr 1
        dsimp [u,Zsqrtd.norm]; rw [Ne]; linear_combination (s.c:ℤ)^2*hC
      rw [←hh]; exact Ideal.mul_mem_mul u₁ u₂
    obtain ⟨x,y,z,h⟩ := primitive_coeffs hn h₂ s hC
    have hh := P.add_mem (P.add_mem (P.mul_mem_left (x:R n) hA) (P.mul_mem_left (y:R n) hB)) (P.mul_mem_left (z:R n) hD)
    have he : N=x*(N*s.a)+y*(N*(2*s.b))+z*(N*C) := by linear_combination -N*h
    simpa only [←Int.cast_mul,←Int.cast_add,←he] using hh

end TunnellIdealHNF
end

section
/- The local double cosets of the Hurwitz order at 2 and the order
ℤ[i+j] + 4 O. Coordinates use the integral Hurwitz basis 1, i, j,
u=(1+i+j+ij)/2. -/

namespace TunnellHurwitzFour
open Finset

abbrev H (R : Type*) := R × R × R × R

def prod {R : Type*} [CommRing R] (x y : H R) : H R :=
  let (a,b,c,d) := x
  let (u,v,w,t) := y
  (a*u-b*v-c*w-d*t-b*w+c*v-b*t-d*w,
   a*v+b*u-b*w+c*v+d*v+c*t-d*w,
   a*w+c*u-b*w+c*v-b*t+d*v+c*t,
   a*t+d*u+2*b*w-2*c*v+b*t-d*v-c*t+d*w+d*t)

def nr {R : Type*} [CommRing R] (x : H R) : R :=
  let (a,b,c,d) := x
  a^2+b^2+c^2+d^2+(a+b+c)*d

def ham (x : H ℚ) : Quaternion ℚ :=
  let (a,b,c,d) := x
  ⟨a+d/2,b+d/2,c+d/2,d/2⟩

lemma ham_prod (x y : H ℚ) : ham (prod x y)=ham x * ham y := by
  obtain ⟨a,b,c,d⟩ := x
  obtain ⟨u,v,w,t⟩ := y
  apply QuaternionAlgebra.ext
  · rw [Quaternion.re_mul]; dsimp [ham,prod]; ring
  · rw [Quaternion.imI_mul]; dsimp [ham,prod]; ring
  · rw [Quaternion.imJ_mul]; dsimp [ham,prod]; ring
  · rw [Quaternion.imK_mul]; dsimp [ham,prod]; ring

lemma ham_norm (x : H ℚ) : Quaternion.normSq (ham x) = nr x := by
  rw [Quaternion.normSq_def']; dsimp [ham,nr]; ring

noncomputable def box : Finset (H ℤ) :=
  let I := Icc (-2:ℤ) 2
  I ×ˢ (I ×ˢ (I ×ˢ I))

lemma norm_one_mem (x : H ℤ) (hx : nr x=1) : x∈box := by
  obtain ⟨a,b,c,d⟩ := x
  change a^2+b^2+c^2+d^2+(a+b+c)*d=1 at hx
  have he : (2*a+d)^2+(2*b+d)^2+(2*c+d)^2+d^2=4 := by linear_combination 4*hx
  have bound (z : ℤ) (h : z^2≤4) : -2≤z ∧ z≤2 := by
    constructor <;> by_contra! hh <;> nlinarith
  have ha := bound (2*a+d) (by nlinarith [sq_nonneg (2*b+d),sq_nonneg (2*c+d),sq_nonneg d])
  have hb := bound (2*b+d) (by nlinarith [sq_nonneg (2*a+d),sq_nonneg (2*c+d),sq_nonneg d])
  have hc := bound (2*c+d) (by nlinarith [sq_nonneg (2*a+d),sq_nonneg (2*b+d),sq_nonneg d])
  have hd := bound d (by nlinarith [sq_nonneg (2*a+d),sq_nonneg (2*b+d),sq_nonneg (2*c+d)])
  simp [box]
  omega

end TunnellHurwitzFour
end

section
/- The global Hurwitz order and its one-sided ideal class number. -/

namespace TunnellHurwitz
open TunnellHurwitzFour Quaternion
abbrev Q := Quaternion ℚ

def hamZ (x : H ℤ) : Q := ham ((x.1:ℚ),(x.2.1:ℚ),(x.2.2.1:ℚ),(x.2.2.2:ℚ))

lemma hamZ_mul (x y : H ℤ) : hamZ (prod x y) = hamZ x * hamZ y := by
  unfold hamZ
  rw [←ham_prod]
  congr 1
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨e,f,g,h⟩
  simp [prod]

lemma hamZ_add (x y : H ℤ) : hamZ (x+y)=hamZ x+hamZ y := by
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add] <;> simp [hamZ,ham,add_div] <;> ring

lemma hamZ_neg (x : H ℤ) : hamZ (-x)=-(hamZ x) := by
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg] <;> simp [hamZ,ham] <;> ring

def order : Subring Q where
  carrier := Set.range hamZ
  zero_mem' := ⟨0,by apply QuaternionAlgebra.ext <;> norm_num [hamZ,ham]⟩
  one_mem' := ⟨(1,0,0,0),by apply QuaternionAlgebra.ext <;> norm_num [hamZ,ham]⟩
  add_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,hamZ_add a b⟩
  neg_mem' := by rintro _ ⟨a,rfl⟩; exact ⟨-a,hamZ_neg _⟩
  mul_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨prod a b,hamZ_mul _ _⟩

lemma integer_coords (a b c d : ℤ) : (⟨a,b,c,d⟩:Q)∈order := by
  refine ⟨(a-d,b-d,c-d,2*d),?_⟩
  apply QuaternionAlgebra.ext <;> dsimp [hamZ,ham] <;> push_cast <;> ring

lemma half_mem : (⟨1/2,1/2,1/2,1/2⟩:Q)∈order := by
  refine ⟨(0,0,0,1),?_⟩
  apply QuaternionAlgebra.ext <;> norm_num [hamZ,ham]

lemma norm_int {q : Q} (hq : q∈order) : ∃ n : ℕ, normSq q=n := by
  obtain ⟨⟨a,b,c,d⟩,rfl⟩ := hq
  let N := nr (a,b,c,d)
  have hh : normSq (hamZ (a,b,c,d))=(N:ℚ) := by simp [hamZ,ham_norm,N,nr]
  have hN : 0≤N := by exact_mod_cast (hh ▸ normSq_nonneg : 0≤(N:ℚ))
  refine ⟨N.toNat,hh.trans ?_⟩
  exact_mod_cast (Int.toNat_of_nonneg hN).symm

/- Rounding into the Lipschitz suborder suffices unless all four entries are half-integers. -/
lemma approximate (q : Q) : ∃ r∈order, normSq (q-r)<1 := by
  let r : Q := ⟨round q.re,round q.imI,round q.imJ,round q.imK⟩
  have hr : r∈order := integer_coords _ _ _ _
  by_cases h : normSq (q-r)<1
  · exact ⟨r,hr,h⟩
  let err (t : ℚ) := t-round t
  have bound (t : ℚ) : err t ^ 2 ≤ 1/4 := by
    have hl := round_le_add_half t
    have hh := sub_half_lt_round t
    dsimp [err]
    nlinarith [mul_nonneg (show 0≤t-round t+1/2 by linarith) (show 0≤1/2-(t-round t) by linarith)]
  have eqn (t : ℚ) (ht : 1/4 ≤ err t^2) : err t = -1/2 := by
    have he := le_antisymm (bound t) ht
    have hlt : err t<1/2 := by dsimp [err]; linarith [sub_half_lt_round t]
    have hf : (err t-1/2)*(err t+1/2)=0 := by nlinarith
    rcases mul_eq_zero.mp hf with ha|ha <;> linarith
  have he : ¬err q.re^2+err q.imI^2+err q.imJ^2+err q.imK^2<1 := by
    rw [normSq_def'] at h
    exact h
  have a := eqn q.re (by linarith [bound q.imI,bound q.imJ,bound q.imK])
  have b := eqn q.imI (by linarith [bound q.re,bound q.imJ,bound q.imK])
  have c := eqn q.imJ (by linarith [bound q.re,bound q.imI,bound q.imK])
  have d := eqn q.imK (by linarith [bound q.re,bound q.imI,bound q.imJ])
  let u : Q := ⟨1/2,1/2,1/2,1/2⟩
  have heq : q=r-u := by
    dsimp only [err] at a b c d
    apply QuaternionAlgebra.ext
    · change q.re=(round q.re:ℚ)-1/2; linarith
    · change q.imI=(round q.imI:ℚ)-1/2; linarith
    · change q.imJ=(round q.imJ:ℚ)-1/2; linarith
    · change q.imK=(round q.imK:ℚ)-1/2; linarith
  refine ⟨q,?_,by simp⟩
  rw [heq]
  exact order.sub_mem hr half_mem

/- Every nonzero integral right ideal of the maximal Hurwitz order is principal. -/
theorem integral_class_number_one (S : Set Q) (hin : S⊆order)
    (hsub : ∀ a∈S, ∀ b∈S, a-b∈S) (hmul : ∀ a∈S, ∀ b∈order, a*b∈S)
    (hne : ∃ a∈S, a≠0) :
    ∃ a∈S, a≠0 ∧ S={x | ∃ b∈order, x=a*b} := by
  classical
  let P (n : ℕ) := ∃ a∈S, a≠0 ∧ normSq a = n
  obtain ⟨q,hq,hq0⟩ := hne
  obtain ⟨n,hn⟩ := norm_int (hin hq)
  have hP : ∃ n, P n := ⟨n,q,hq,hq0,hn⟩
  obtain ⟨a,ha,ha0,han⟩ := Nat.find_spec hP
  refine ⟨a,ha,ha0,Set.ext fun x => ⟨?_,?_⟩⟩
  · intro hx
    obtain ⟨r,hr,ht⟩ := approximate (a⁻¹*x)
    have hv : x-a*r∈S := hsub x hx _ (hmul a ha r hr)
    have he : x-a*r=a*(a⁻¹*x-r) := by rw [mul_sub,←mul_assoc,mul_inv_cancel₀ ha0,one_mul]
    have ha' : 0<normSq a := lt_of_le_of_ne normSq_nonneg (normSq_ne_zero.mpr ha0).symm
    have hlt : normSq (x-a*r)<normSq a := by
      rw [he,map_mul]; simpa using mul_lt_mul_of_pos_left ht ha'
    have hzero : x-a*r=0 := by
      by_contra h0
      obtain ⟨k,hk⟩ := norm_int (hin hv)
      have hmin := Nat.find_min' hP (show P k from ⟨x-a*r,hv,h0,hk⟩)
      rw [hk,han] at hlt
      exact (not_lt_of_ge hmin) (by exact_mod_cast hlt)
    exact ⟨r,hr,sub_eq_zero.mp hzero⟩
  · rintro ⟨r,hr,rfl⟩; exact hmul a ha r hr

end TunnellHurwitz
end

section
/- # The ternary square shell for the weight-three-halves coefficients -/

namespace TunnellShell

open OMA.R_CongruentNumber_Tunnell_even_R1 CongruentNumber Finset
open scoped PowerSeries.WithPiTopology

abbrev Triple := ℤ × ℤ × ℤ

def normSq (v : Triple) : ℤ := v.1^2+v.2.1^2+v.2.2^2

def shell (N : ℕ) : Finset Triple :=
  let I := Finset.Icc (-(N:ℤ)-1) (N+1:ℤ)
  (I ×ˢ (I ×ˢ I)).filter (fun v => normSq v=N)

@[simp] lemma mem_shell {N : ℕ} {v : Triple} : v ∈ shell N ↔ normSq v=N := by
  obtain ⟨x,y,z⟩ := v
  simp only [shell,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  change x^2+y^2+z^2=(N:ℤ) at h
  have hbound (a:ℤ) (ha:a^2≤N) : -(N:ℤ)-1 ≤ a ∧ a ≤ N+1 :=
    ⟨by nlinarith [sq_nonneg (a+1)],by nlinarith [sq_nonneg (a-1)]⟩
  exact ⟨hbound x (by nlinarith [sq_nonneg y,sq_nonneg z]), hbound y (by nlinarith [sq_nonneg x,sq_nonneg z]),
    hbound z (by nlinarith [sq_nonneg x,sq_nonneg y])⟩

def rot (v : Triple) : Triple := (v.2.1,v.2.2,v.1)

end TunnellShell
end

section
/- Trace-zero Hurwitz elements and embeddings of the imaginary quadratic order. -/

namespace TunnellHurwitz
open Quaternion TunnellShell

def pure (v : Triple) : Q := ⟨0,v.1,v.2.1,v.2.2⟩

lemma pure_mem (v : Triple) : pure v∈order := integer_coords 0 _ _ _

lemma pure_injective : Function.Injective pure := by
  intro v w h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  dsimp [pure] at hi hj hk
  exact Prod.ext (by exact_mod_cast hi) (Prod.ext (by exact_mod_cast hj) (by exact_mod_cast hk))

lemma trace_zero_integral {q : Q} (hq : q∈order) (hr : q.re=0) : ∃ v, q=pure v := by
  obtain ⟨⟨a,b,c,d⟩,rfl⟩ := hq
  change (a:ℚ)+d/2=0 at hr
  refine ⟨(b-a,c-a,-a),?_⟩
  apply QuaternionAlgebra.ext <;> dsimp [hamZ,TunnellHurwitzFour.ham,pure] <;> push_cast <;> linarith

lemma pure_norm (v : Triple) : Quaternion.normSq (pure v)=(TunnellShell.normSq v:ℚ) := by
  rw [Quaternion.normSq_def']
  simp [pure,TunnellShell.normSq]

def quadraticValue (d : ℕ) (v : Triple) (z : Zsqrtd (-(d:ℤ))) : Q :=
  ⟨z.re,z.im*v.1,z.im*v.2.1,z.im*v.2.2⟩

def embed (d : ℕ) (v : Triple) (hv : v∈shell d) : Zsqrtd (-(d:ℤ)) →+* Q where
  toFun := quadraticValue d v
  map_one' := by
    apply QuaternionAlgebra.ext <;> dsimp [quadraticValue] <;> simp
  map_zero' := by
    apply QuaternionAlgebra.ext <;> dsimp [quadraticValue] <;> simp
  map_add' x y := by
    apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add]
    all_goals dsimp [quadraticValue]; push_cast; ring
  map_mul' x y := by
    have hn := mem_shell.mp hv
    change _^2+_^2+_^2=(d:ℤ) at hn
    have hq : (v.1:ℚ)^2+(v.2.1:ℚ)^2+(v.2.2:ℚ)^2=d := by exact_mod_cast hn
    apply QuaternionAlgebra.ext
    · rw [Quaternion.re_mul]
      dsimp [quadraticValue]; push_cast
      linear_combination (x.im:ℚ)*y.im*hq
    · rw [Quaternion.imI_mul]; dsimp [quadraticValue]; push_cast; ring
    · rw [Quaternion.imJ_mul]; dsimp [quadraticValue]; push_cast; ring
    · rw [Quaternion.imK_mul]; dsimp [quadraticValue]; push_cast; ring

lemma embed_root (d : ℕ) (v : Triple) (hv : v∈shell d) : embed d v hv Zsqrtd.sqrtd=pure v := by
  change quadraticValue d v _=_
  apply QuaternionAlgebra.ext <;> simp [quadraticValue,pure]

lemma embed_integral (d : ℕ) (v : Triple) (hv : v∈shell d) (z) : embed d v hv z ∈ order := by
  have he : embed d v hv z = (⟨z.re,(z.im*v.1:ℤ),(z.im*v.2.1:ℤ),(z.im*v.2.2:ℤ)⟩ : Q) := by
    change quadraticValue d v z=_
    apply QuaternionAlgebra.ext <;> simp [quadraticValue]
  rw [he]
  exact integer_coords _ _ _ _

lemma negative_root {d : ℕ} (hd : 0<d) (q : Q) (h : q*q= -(d:Q)) :
    q.re=0 ∧ Quaternion.normSq q=d := by
  have h₀ := congrArg QuaternionAlgebra.re h
  have h₁ := congrArg QuaternionAlgebra.imI h
  have h₂ := congrArg QuaternionAlgebra.imJ h
  have h₃ := congrArg QuaternionAlgebra.imK h
  simp only [Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,
    Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg,
    Quaternion.re_natCast,Quaternion.imI_natCast,Quaternion.imJ_natCast,Quaternion.imK_natCast,neg_zero] at h₀ h₁ h₂ h₃
  have hr : q.re=0 := by
    by_contra hr
    have hI : q.imI=0 := (mul_eq_zero.mp (show q.re*q.imI=0 by nlinarith [h₁])).resolve_left hr
    have hJ : q.imJ=0 := (mul_eq_zero.mp (show q.re*q.imJ=0 by nlinarith [h₂])).resolve_left hr
    have hK : q.imK=0 := (mul_eq_zero.mp (show q.re*q.imK=0 by nlinarith [h₃])).resolve_left hr
    rw [hI,hJ,hK] at h₀
    have hp : (0:ℚ)<d := by exact_mod_cast hd
    nlinarith [sq_nonneg q.re]
  exact ⟨hr,by rw [normSq_def',hr]; rw [hr] at h₀; nlinarith⟩

end TunnellHurwitz
end

section
/- Optimal embeddings of ℤ[√−n] into the Hurwitz order for n squarefree and 2 modulo 4. -/

namespace TunnellHurwitz
open Quaternion TunnellShell TunnellHurwitzFour

lemma primitive {n : ℕ} (hs : Squarefree n) {v : Triple} (hv : v∈shell n) :
    ∃ a b c : ℤ, v.1*a+v.2.1*b+v.2.2*c=1 := by
  obtain ⟨x,y,z⟩ := v
  let g := Int.gcd x y
  let h := Int.gcd (g:ℤ) z
  have hg (u : ℤ) (hu : (g:ℤ) ∣ u) : (h:ℤ) ∣ u := (Int.gcd_dvd_left (g:ℤ) z).trans hu
  obtain ⟨a,ha⟩ := hg x (Int.gcd_dvd_left x y)
  obtain ⟨b,hb⟩ := hg y (Int.gcd_dvd_right x y)
  obtain ⟨c,hc⟩ := Int.gcd_dvd_right (g:ℤ) z
  have hn := mem_shell.mp hv
  change x^2+y^2+z^2=(n:ℤ) at hn
  have hdiv : (h:ℤ)*(h:ℤ) ∣ n := by
    refine ⟨a^2+b^2+c^2,?_⟩
    rw [←hn,ha,hb,hc]; ring
  have hd : h*h ∣ n := by exact_mod_cast hdiv
  have h1 := Nat.isUnit_iff.mp (hs h hd)
  let u := Int.gcdA (g:ℤ) z
  let w := Int.gcdB (g:ℤ) z
  refine ⟨Int.gcdA x y*u,Int.gcdB x y*u,w,?_⟩
  have hg' := Int.gcd_eq_gcd_ab x y
  have hh := Int.gcd_eq_gcd_ab (g:ℤ) z
  change (g:ℤ)=_ at hg'
  change (h:ℤ)=g*u+z*w at hh
  dsimp only
  rw [h1] at hh
  norm_cast at hh
  linear_combination -hh - u*hg'

def evalRat (v : Triple) (a b : ℚ) : Q := ⟨a,b*v.1,b*v.2.1,b*v.2.2⟩

lemma eval_norm {n : ℕ} {v : Triple} (hv : v∈shell n) (a b : ℚ) :
    normSq (evalRat v a b)=a^2+n*b^2 := by
  have h := mem_shell.mp hv
  change v.1^2+v.2.1^2+v.2.2^2=(n:ℤ) at h
  have hh : (v.1:ℚ)^2+(v.2.1:ℚ)^2+(v.2.2:ℚ)^2=n := by exact_mod_cast h
  rw [normSq_def']; dsimp [evalRat]; linear_combination b^2*hh

lemma doubled_coords {q : Q} (hq : q∈order) :
    ∃ A B C D : ℤ, (A:ℚ)=2*q.re ∧ (B:ℚ)=2*q.imI ∧ (C:ℚ)=2*q.imJ ∧ (D:ℚ)=2*q.imK := by
  obtain ⟨⟨a,b,c,d⟩,rfl⟩ := hq
  refine ⟨2*a+d,2*b+d,2*c+d,d,?_⟩
  refine ⟨?_,?_,?_,?_⟩ <;> dsimp [hamZ,ham] <;> push_cast <;> ring

lemma optimal {n : ℕ} (hs : Squarefree n) (h2 : n%4=2) {v : Triple} (hv : v∈shell n) (a b : ℚ) :
    evalRat v a b∈order ↔ (∃ x : ℤ, a=x) ∧ (∃ y : ℤ, b=y) := by
  constructor
  · intro h
    obtain ⟨i,j,k,hi⟩ := primitive hs hv
    obtain ⟨A,B,C,D,hA,hB,hC,hD⟩ := doubled_coords h
    dsimp only [evalRat] at hA hB hC hD
    let E := i*B+j*C+k*D
    have hE : (E:ℚ)=2*b := by
      have hi' : (v.1:ℚ)*i+(v.2.1:ℚ)*j+(v.2.2:ℚ)*k=1 := by exact_mod_cast hi
      dsimp [E]; push_cast
      linear_combination (i:ℚ)*hB+(j:ℚ)*hC+(k:ℚ)*hD+2*b*hi'
    obtain ⟨N,hN⟩ := norm_int h
    rw [eval_norm hv] at hN
    have eqn : A^2+(n:ℤ)*E^2=4*(N:ℤ) := by
      have ee : (A:ℚ)^2+(n:ℚ)*(E:ℚ)^2=4*N := by
        rw [hA,hE]; linear_combination 4*hN
      exact_mod_cast ee
    have chk : ∀ x y : ZMod 4, x^2+2*y^2=0 → x.val%2=0 ∧ y.val%2=0 := by decide
    have hn : (n:ZMod 4)=2 := by apply ZMod.val_injective 4; rw [ZMod.val_natCast,h2]; decide
    have heq := congrArg (fun u:ℤ => (u:ZMod 4)) eqn
    push_cast at heq
    rw [hn] at heq
    have hh := chk (A:ZMod 4) (E:ZMod 4) (by simpa only [show (4:ZMod 4)=0 by decide,zero_mul] using heq)
    have hAv := ZMod.val_intCast (n:=4) A
    have hEv := ZMod.val_intCast (n:=4) E
    have ha : (A/2:ℤ)*2=A := by omega
    have hb : (E/2:ℤ)*2=E := by omega
    refine ⟨⟨A/2,?_⟩,⟨E/2,?_⟩⟩
    · have h' : ((A/2:ℤ):ℚ)*2=A := by exact_mod_cast ha
      linarith
    · have h' : ((E/2:ℤ):ℚ)*2=E := by exact_mod_cast hb
      linarith
  · rintro ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩
    exact embed_integral n v hv ⟨a,b⟩

lemma centralizer {n : ℕ} (hs : Squarefree n) {v : Triple} (hv : v∈shell n) (q : Q)
    (h : q*pure v=pure v*q) : ∃ b : ℚ, q=evalRat v q.re b := by
  obtain ⟨i,j,k,hi⟩ := primitive hs hv
  have hi' : (v.1:ℚ)*i+(v.2.1:ℚ)*j+(v.2.2:ℚ)*k=1 := by exact_mod_cast hi
  have e₁ := congrArg QuaternionAlgebra.imI h
  have e₂ := congrArg QuaternionAlgebra.imJ h
  have e₃ := congrArg QuaternionAlgebra.imK h
  rw [Quaternion.imI_mul,Quaternion.imI_mul] at e₁
  rw [Quaternion.imJ_mul,Quaternion.imJ_mul] at e₂
  rw [Quaternion.imK_mul,Quaternion.imK_mul] at e₃
  dsimp [pure] at e₁ e₂ e₃
  refine ⟨i*q.imI+j*q.imJ+k*q.imK,?_⟩
  apply QuaternionAlgebra.ext
  · rfl
  · dsimp [evalRat]; linear_combination -q.imI*hi'+(j:ℚ)/2*e₃-(k:ℚ)/2*e₂
  · dsimp [evalRat]; linear_combination -q.imJ*hi'-(i:ℚ)/2*e₃+(k:ℚ)/2*e₁
  · dsimp [evalRat]; linear_combination -q.imK*hi'+(i:ℚ)/2*e₂-(j:ℚ)/2*e₁

lemma integral_centralizer {n : ℕ} (hs : Squarefree n) (h2 : n%4=2) {v : Triple}
    (hv : v∈shell n) {q : Q} (hq : q∈order) (h : q*pure v=pure v*q) :
    ∃ z, q=embed n v hv z := by
  obtain ⟨b,hb⟩ := centralizer hs hv q h
  have hl : evalRat v q.re b ∈ order := hb ▸ hq
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := (optimal hs h2 hv q.re b).mp hl
  refine ⟨⟨x,y⟩,?_⟩
  calc q = evalRat v q.re b := hb
       _ = _ := by rw [hx,hy]; rfl

end TunnellHurwitz
end

section
/- Rational conjugacy of the embeddings and their integral intertwiner lattices. -/

namespace TunnellHurwitz

open TunnellShell Quaternion

lemma pure_square {n : ℕ} {v : Triple} (hv : v∈shell n) : pure v*pure v=-(n:Q) := by
  have h := congrArg (embed n v hv) (Zsqrtd.dmuld (d:=-(n:ℤ)))
  simpa only [map_mul,embed_root,map_intCast,map_neg,map_natCast,Int.cast_neg,Int.cast_natCast] using h

lemma intertwine {n : ℕ} (v w : Triple) (hv : v∈shell n) (hw : w∈shell n) :
    ∃ q∈order, q≠0 ∧ pure w*q=q*pure v := by
  by_cases h : pure w+pure v=0
  · have hw' : pure w= -pure v := eq_neg_of_add_eq_zero_left h
    obtain ⟨a,b,c⟩ := v
    by_cases hab : a=0 ∧ b=0
    · obtain ⟨rfl,rfl⟩ := hab
      let q : Q := pure (1,0,0)
      refine ⟨q,pure_mem _,fun he => ?_,?_⟩
      · have t := congrArg QuaternionAlgebra.imI he
        norm_num [q,pure] at t
      · rw [hw',neg_mul]
        apply QuaternionAlgebra.ext <;>
          simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg,
          Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul]
        all_goals simp [pure,q]
    · let q : Q := pure (-b,a,0)
      refine ⟨q,pure_mem _,fun he => ?_,?_⟩
      · apply hab
        have h1 := congrArg QuaternionAlgebra.imI he
        have h2 := congrArg QuaternionAlgebra.imJ he
        simp [q,pure] at h1 h2
        exact ⟨h2,h1⟩
      · rw [hw',neg_mul]
        apply QuaternionAlgebra.ext <;>
          simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg,
          Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul]
        all_goals simp [pure,q] <;> ring
  · exact ⟨pure w+pure v,order.add_mem (pure_mem _) (pure_mem _),h,
      by rw [mul_add,add_mul,pure_square hw,pure_square hv,add_comm]⟩

def intertwiner (v w : Triple) : AddSubgroup Q where
  carrier := {q | q∈order ∧ pure w*q=q*pure v}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,hea⟩ ⟨hb,heb⟩
    exact ⟨order.add_mem ha hb,by rw [mul_add,add_mul,hea,heb]⟩
  neg_mem' := by rintro a ⟨ha,he⟩; exact ⟨order.neg_mem ha,by rw [mul_neg,neg_mul,he]⟩

lemma intertwiner_comp {u v w : Triple} {a b : Q} (ha : a∈intertwiner v w) (hb : b∈intertwiner u v) :
    a*b∈intertwiner u w := by
  exact ⟨order.mul_mem ha.1 hb.1,by rw [←mul_assoc,ha.2,mul_assoc,hb.2,mul_assoc]⟩

end TunnellHurwitz
end

section
/- Explicit splitting of the Hamilton quaternion algebra at odd primes. -/

namespace TunnellQuaternion

open Matrix Quaternion

variable {K : Type*} [Field K]

def matrixOf (a b : K) (x : Quaternion K) : Matrix (Fin 2) (Fin 2) K :=
  !![x.re + a*x.imJ + b*x.imK, x.imI+b*x.imJ-a*x.imK;
     -x.imI+b*x.imJ-a*x.imK, x.re-a*x.imJ-b*x.imK]

def splitHom (a b : K) (hab : a^2+b^2 = -1) : Quaternion K →+* Matrix (Fin 2) (Fin 2) K where
  toFun := matrixOf a b
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf]
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring
  map_mul' x y := by
    have hb : b^2= -1-a^2 := by linear_combination hab
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixOf,Matrix.mul_apply,Fin.sum_univ_two] <;> ring_nf <;> rw [hb] <;> ring

lemma split_det (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    (splitHom a b hab x).det = normSq x := by
  change (matrixOf a b x).det = _
  simp [Matrix.det_fin_two,matrixOf,normSq_def']
  linear_combination -(x.imJ^2+x.imK^2)*hab

lemma split_trace (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    (splitHom a b hab x).trace = 2*x.re := by
  change (matrixOf a b x).trace = _
  simp [Matrix.trace_fin_two,matrixOf]
  ring

lemma split_star (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    splitHom a b hab (star x) = (splitHom a b hab x).adjugate := by
  change matrixOf a b (star x) = (matrixOf a b x).adjugate
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring

def quaternionOf (a b : K) (m : Matrix (Fin 2) (Fin 2) K) : Quaternion K :=
  ⟨(m 0 0+m 1 1)/2,(m 0 1-m 1 0)/2,
    -(a*(m 0 0-m 1 1) + b*(m 0 1+m 1 0))/2,
    -(b*(m 0 0-m 1 1) - a*(m 0 1+m 1 0))/2⟩

lemma split_iso (a b : K) (hab : a^2+b^2 = -1) (htwo : (2:K) ≠ 0) :
    Function.Bijective (splitHom a b hab) := by
  have hb : b^2 = -1-a^2 := by linear_combination hab
  have left : Function.LeftInverse (quaternionOf a b) (splitHom a b hab) := by
    intro x
    change quaternionOf a b (matrixOf a b x) = x
    ext <;> dsimp [matrixOf,quaternionOf] <;> field_simp <;> ring_nf <;> rw [hb] <;> ring
  have right : Function.RightInverse (quaternionOf a b) (splitHom a b hab) := by
    intro M
    change matrixOf a b (quaternionOf a b M) = M
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp [matrixOf,quaternionOf] <;> field_simp <;> ring_nf <;> rw [hb] <;> ring
  exact ⟨left.injective,right.surjective⟩

lemma exists_splitting (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ a b : ZMod p, a^2+b^2 = -1 ∧ (2:ZMod p) ≠ 0 := by
  obtain ⟨a,b,ha,hb,h⟩ := Nat.sq_add_sq_zmodEq p (-1)
  refine ⟨a,b,?_,?_⟩
  · exact_mod_cast ((ZMod.intCast_eq_intCast_iff _ _ _).mpr h)
  · intro he
    have hh := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using he)
    have := (Nat.dvd_prime Nat.prime_two).mp hh
    have := (Fact.out : p.Prime).ne_one
    tauto

end TunnellQuaternion
end

section
/- Projective lines and rank-one quaternion reductions modulo an odd prime. -/

namespace TunnellQuaternion

open Matrix

variable {K : Type*} [Field K]
abbrev M2 (K : Type*) := Matrix (Fin 2) (Fin 2) K

end TunnellQuaternion
end

section
/- Descent of integral Hamilton quaternions inside specified right ideals modulo an odd prime. -/

namespace TunnellQuaternion

open Quaternion

def redFun (p : ℕ) (q : Quaternion ℤ) : Quaternion (ZMod p) := ⟨q.re,q.imI,q.imJ,q.imK⟩

def red (p : ℕ) : Quaternion ℤ →+* Quaternion (ZMod p) where
  toFun := redFun p
  map_add' x y := by apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add] <;> simp [redFun]
  map_mul' x y := by
    apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul] <;> simp [redFun]
  map_zero' := by ext <;> simp [redFun]
  map_one' := by ext <;> simp [redFun]

lemma red_apply (p : ℕ) (x : Quaternion ℤ) : red p x = redFun p x := rfl

lemma red_norm (p : ℕ) (x : Quaternion ℤ) : ((normSq x:ℤ) : ZMod p) = normSq (red p x) := by
  rw [normSq_def',normSq_def']
  simp [red_apply,redFun]

def lift (m : ℕ) (x : Quaternion (ZMod m)) : Quaternion ℤ :=
  ⟨x.re.valMinAbs,x.imI.valMinAbs,x.imJ.valMinAbs,x.imK.valMinAbs⟩

@[simp] lemma red_lift (m : ℕ) (x : Quaternion (ZMod m)) : red m (lift m x)=x := by
  change redFun m (lift m x)=x
  apply QuaternionAlgebra.ext <;> dsimp only [redFun,lift] <;> simp

end TunnellQuaternion
end

section
/- Norm-prime right divisors parameterized by the projective line at an odd prime. -/

namespace TunnellQuaternion

open Matrix Quaternion

variable {p : ℕ} [Fact p.Prime]

structure Model (p : ℕ) where
  f : Quaternion (ZMod p) ≃+* M2 (ZMod p)
  det (x) : (f x).det=normSq x
  trace (x) : (f x).trace=2*x.re
  bar (x) : f (star x) = (f x).adjugate
  smul (t : ZMod p) (x) : f (t • x)=t • f x

noncomputable def localModel (hp : p≠2) : Model p := Classical.choice <| by
  classical
  obtain ⟨a,b,hab,h2⟩ := exists_splitting p hp
  refine ⟨?_⟩
  exact ⟨RingEquiv.ofBijective (splitHom a b hab) (split_iso a b hab h2),split_det a b hab,
    split_trace a b hab,split_star a b hab,fun t x => by
      change matrixOf a b (t • x) = t • matrixOf a b x
      ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring⟩

variable (M : Model p)

def residue : Quaternion ℤ →+* M2 (ZMod p) := M.f.toRingHom.comp (red p)

lemma residue_zero (x : Quaternion ℤ) : residue M x = 0 ↔ red p x = 0 :=
  M.f.map_eq_zero_iff

lemma residue_det (x : Quaternion ℤ) : (residue M x).det = (normSq x : ℤ) :=
  (M.det _).trans (red_norm p x).symm

end TunnellQuaternion
end

section
/- Integral quaternion norm shells, rotations, and the weight on a coordinate. -/

namespace TunnellQuaternion

open Finset Quaternion TunnellShell

abbrev QInt := Quaternion ℤ

def pure (v : Triple) : QInt := ⟨0,v.1,v.2.1,v.2.2⟩
def vec (q : QInt) : Triple := (q.imI,q.imJ,q.imK)
def rotate (q : QInt) (v : Triple) : Triple := vec (q*pure v*star q)

lemma rotate_apply (a b c d x y z : ℤ) :
    rotate ⟨a,b,c,d⟩ (x,y,z) =
      ((a^2+b^2-c^2-d^2)*x+2*(b*c-a*d)*y+2*(b*d+a*c)*z,
       2*(b*c+a*d)*x+(a^2-b^2+c^2-d^2)*y+2*(c*d-a*b)*z,
       2*(b*d-a*c)*x+2*(c*d+a*b)*y+(a^2-b^2-c^2+d^2)*z) := by
  suffices h : ∀ (q : QInt) (v : Triple), rotate q v =
      ((q.re^2+q.imI^2-q.imJ^2-q.imK^2)*v.1+2*(q.imI*q.imJ-q.re*q.imK)*v.2.1+2*(q.imI*q.imK+q.re*q.imJ)*v.2.2,
       2*(q.imI*q.imJ+q.re*q.imK)*v.1+(q.re^2-q.imI^2+q.imJ^2-q.imK^2)*v.2.1+2*(q.imJ*q.imK-q.re*q.imI)*v.2.2,
       2*(q.imI*q.imK-q.re*q.imJ)*v.1+2*(q.imJ*q.imK+q.re*q.imI)*v.2.1+(q.re^2-q.imI^2-q.imJ^2+q.imK^2)*v.2.2) from h _ _
  intro q v
  ext <;> simp only [rotate,vec,Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star] <;> simp [pure] <;> ring

end TunnellQuaternion
end

section
/- Weighted finite fibers on ternary quadratic shells and the resulting Hecke relation. -/

namespace TunnellShellFibers

open Finset TunnellShell

def divisible (p : ℕ) (v : Triple) : Prop := (p:ℤ) ∣ v.1 ∧ (p:ℤ) ∣ v.2.1 ∧ (p:ℤ) ∣ v.2.2

end TunnellShellFibers
end

section
/- Integral inverse images of a rotation by a prime-norm quaternion. -/

namespace TunnellQuaternion
open Quaternion Finset TunnellShell

lemma norm_pure (v : Triple) : Quaternion.normSq (pure v)=TunnellShell.normSq v := by
  rw [Quaternion.normSq_def']
  change (0:ℤ)^2+v.1^2+v.2.1^2+v.2.2^2=_
  simp [TunnellShell.normSq]

variable {p : ℕ} [Fact p.Prime] (M : Model p)

lemma residue_trace (w : QInt) : (residue M w).trace=2*(w.re:ZMod p) :=
  M.trace _

lemma residue_pure_zero (v : Triple) :
    residue M (pure v)=0 ↔ TunnellShellFibers.divisible p v := by
  rw [residue_zero]
  constructor
  · intro h
    refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrArg QuaternionAlgebra.imI h),
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrArg QuaternionAlgebra.imJ h),
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrArg QuaternionAlgebra.imK h)⟩
  · rintro ⟨a,b,c⟩
    apply QuaternionAlgebra.ext
    · exact Int.cast_zero
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr a
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr b
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr c

end TunnellQuaternion
end

section
/- Every odd local prime admits an integral unit intertwining two primitive embeddings. -/

namespace TunnellToricLocal
open Matrix TunnellQuaternion
variable {K : Type*} [Field K]

def cyclicBasis (x y : K) (A : M2 K) : M2 K :=
  !![x,A 0 0*x+A 0 1*y;y,A 1 0*x+A 1 1*y]

lemma cyclic_exists (A : M2 K) (h2 : (2:K)≠0) (hn : A≠0) (ht : A.trace=0) :
    ∃ x y : K, (cyclicBasis x y A).det ≠ 0 := by
  by_contra! h
  have h1 := h 1 0
  have h2' := h 0 1
  have h3 := h 1 1
  simp only [cyclicBasis,det_fin_two,of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,one_mul,mul_one,zero_mul,mul_zero,zero_add,add_zero,sub_zero,zero_sub,neg_eq_zero] at h1 h2' h3
  have htt : A 0 0+A 1 1=0 := by simpa [Matrix.trace,Fin.sum_univ_two] using ht
  have hd : A 0 0=0 := (mul_eq_zero.mp (show 2*A 0 0=0 by linear_combination htt - h3 - h2' + h1)).resolve_left h2
  apply hn
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

lemma cyclic_action (A : M2 K) (ht : A.trace=0) (x y : K) :
    A*cyclicBasis x y A = cyclicBasis x y A*!![0,-A.det;1,0] := by
  have htt : A 0 0+A 1 1=0 := by simpa [Matrix.trace,Fin.sum_univ_two] using ht
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [cyclicBasis,det_fin_two,mul_apply,Fin.sum_univ_two]
  all_goals first | linear_combination (A 0 0*x+A 0 1*y)*htt | linear_combination (A 1 0*x+A 1 1*y)*htt

lemma matrix_intertwiner (V W : M2 K) (h2 : (2:K)≠0) (hv : V≠0) (hw : W≠0)
    (htv : V.trace=0) (htw : W.trace=0) (hd : V.det=W.det) :
    ∃ S : M2 K, (W*S+S*V).det≠0 := by
  obtain ⟨x,y,hb⟩ := cyclic_exists V h2 hv htv
  obtain ⟨u,v,hc⟩ := cyclic_exists W h2 hw htw
  let B := cyclicBasis x y V
  let C := cyclicBasis u v W
  let J : M2 K := !![0,-V.det;1,0]
  let T : M2 K := !![0,1;0,0]
  have heB : V*B=B*J := cyclic_action V htv _ _
  have heC : W*C=C*J := by simpa [C,J,hd] using cyclic_action W htw u v
  have hIB : J*B⁻¹=B⁻¹*V := by
    have hu := (isUnit_iff_ne_zero.mpr hb : IsUnit B.det)
    calc J*B⁻¹ = B⁻¹*(B*J)*B⁻¹ := by simp [←mul_assoc,Matrix.nonsing_inv_mul B hu]
         _ = _ := by rw [←heB]; simp [mul_assoc,Matrix.mul_nonsing_inv B hu]
  have hJT : J*T+T*J=1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [J,T,mul_apply,Fin.sum_univ_two]
  refine ⟨C*T*B⁻¹,?_⟩
  have h : W*(C*T*B⁻¹)+C*T*B⁻¹*V=C*B⁻¹ := by
    calc _=C*(J*T+T*J)*B⁻¹ := by
           rw [mul_add,add_mul]
           simp only [mul_assoc]
           rw [←hIB]
           simp only [←mul_assoc,heC]
         _=_ := by rw [hJT,mul_one]
  rw [h,det_mul,det_nonsing_inv,Ring.inverse_eq_inv]
  exact mul_ne_zero hc (inv_ne_zero hb)

variable {p : ℕ} [Fact p.Prime]

lemma residue_surj (M : Model p) (S : M2 (ZMod p)) :
    residue M (lift p (M.f.symm S))=S := by
  change M.f (red p (lift p (M.f.symm S)))=S
  rw [red_lift,M.f.apply_symm_apply]

lemma residue_nonzero (M : Model p) {n : ℕ} (hs : Squarefree n) {v : TunnellShell.Triple}
    (hv : v∈TunnellShell.shell n) : residue M (TunnellQuaternion.pure v)≠0 := by
  intro hz
  obtain ⟨hx,hy,hz⟩ := (residue_pure_zero M v).mp hz
  obtain ⟨a,b,c,he⟩ := TunnellHurwitz.primitive hs hv
  have hdiv : (p:ℤ)∣1 := he ▸ dvd_add (dvd_add (dvd_mul_of_dvd_left hx a) (dvd_mul_of_dvd_left hy b)) (dvd_mul_of_dvd_left hz c)
  exact (Fact.out : p.Prime).not_dvd_one (by exact_mod_cast hdiv)

lemma coprime_intertwiner (hp : p≠2) {n : ℕ} (hs : Squarefree n) (v w : TunnellShell.Triple)
    (hv : v∈TunnellShell.shell n) (hw : w∈TunnellShell.shell n) :
    ∃ q : Quaternion ℤ, TunnellQuaternion.pure w*q=q*TunnellQuaternion.pure v ∧ ¬ (p:ℤ) ∣ Quaternion.normSq q := by
  let M := localModel hp
  let V := residue M (TunnellQuaternion.pure v)
  let W := residue M (TunnellQuaternion.pure w)
  have ht (u : TunnellShell.Triple) : (residue M (TunnellQuaternion.pure u)).trace=0 := by
    rw [residue_trace]; simp [TunnellQuaternion.pure]
  have hd : V.det=W.det := by
    change (residue M _).det=(residue M _).det
    rw [residue_det,residue_det,norm_pure,norm_pure,TunnellShell.mem_shell.mp hv,TunnellShell.mem_shell.mp hw]
  have h2 : (2:ZMod p)≠0 := by
    intro hh
    have hp2 : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hh)
    exact hp ((Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left (Fact.out : p.Prime).ne_one)
  obtain ⟨S,hS⟩ := matrix_intertwiner V W h2 (residue_nonzero M hs hv) (residue_nonzero M hs hw) (ht v) (ht w) hd
  let s := lift p (M.f.symm S)
  let q := TunnellQuaternion.pure w*s+s*TunnellQuaternion.pure v
  have he (u : TunnellShell.Triple) (hu : u∈TunnellShell.shell n) : TunnellQuaternion.pure u*TunnellQuaternion.pure u=-(n:Quaternion ℤ) := by
    have hm : star (TunnellQuaternion.pure u) = -TunnellQuaternion.pure u := by
      apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg,
        Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star] <;> simp [TunnellQuaternion.pure]
    have hn := Quaternion.self_mul_star (TunnellQuaternion.pure u)
    rw [hm,mul_neg,norm_pure,TunnellShell.mem_shell.mp hu] at hn
    simpa only [neg_neg,Quaternion.coe_natCast] using congrArg Neg.neg hn
  refine ⟨q,?_,?_⟩
  · dsimp only [q]
    rw [mul_add,add_mul,←mul_assoc,he w hw,mul_assoc s,he v hv,mul_assoc,neg_mul,mul_neg]
    rw [Nat.cast_comm,add_comm]
  · intro h
    apply hS
    have hq : residue M q=W*S+S*V := by simp only [q,map_add,map_mul,s,residue_surj,W,V]
    rw [←hq,residue_det]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h

end TunnellToricLocal
end

section
/- At the ramified prime 2, division by the quadratic uniformizer preserves the intertwiner lattice. -/

namespace TunnellToricLocal

open TunnellHurwitz TunnellHurwitzFour TunnellShell Quaternion

def modTwo (u : H ℤ) : H (ZMod 2) := (u.1,u.2.1,u.2.2.1,u.2.2.2)

lemma modTwo_prod (x y : H ℤ) : modTwo (prod x y)=prod (modTwo x) (modTwo y) := by
  rcases x with ⟨a,b,c,d⟩; rcases y with ⟨e,f,g,h⟩
  simp [modTwo,prod]

lemma modTwo_nr (x : H ℤ) : ((nr x:ℤ):ZMod 2)=nr (modTwo x) := by
  rcases x with ⟨a,b,c,d⟩
  simp [modTwo,nr]

lemma norm_raw (u : H ℤ) : Quaternion.normSq (hamZ u)=((nr u:ℤ):ℚ) := by simp [hamZ,ham_norm,nr]

lemma half_integral {a b : Q} (ha : a∈order) (hb : b∈order) {A B : ℕ} (hA : Quaternion.normSq a=A)
    (hB : Quaternion.normSq b=B) (heA : Even A) (heB : Even B) : ∃ r∈order, a*b=(2:ℚ) • r := by
  obtain ⟨u,rfl⟩ := ha; obtain ⟨v,rfl⟩ := hb
  have ht : ∀ x y : H (ZMod 2), nr x=0 → nr y=0 → prod x y=0 := by decide
  have hz (u : H ℤ) (N : ℕ) (hh : Quaternion.normSq (hamZ u)=N) (he : Even N) : nr (modTwo u)=0 := by
    rw [norm_raw] at hh
    have hn : nr u=(N:ℤ) := by exact_mod_cast hh
    rw [←modTwo_nr,hn]; exact_mod_cast (ZMod.natCast_eq_zero_iff N 2).mpr he.two_dvd
  have h := ht _ _ (hz u A hA heA) (hz v B hB heB)
  rw [←modTwo_prod] at h
  rw [←hamZ_mul]
  generalize prod u v=z at *
  obtain ⟨a,b,c,d⟩ := z
  have hh (x : ℤ) (hx : (x:ZMod 2)=0) : x=2*(x/2) :=
    (Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx)).symm
  have ha := hh a (congrArg Prod.fst h)
  have hb := hh b (congrArg (fun x : H (ZMod 2) => x.2.1) h)
  have hc := hh c (congrArg (fun x : H (ZMod 2) => x.2.2.1) h)
  have hd := hh d (congrArg (fun x : H (ZMod 2) => x.2.2.2) h)
  let w : H ℤ := (a/2,b/2,c/2,d/2)
  refine ⟨hamZ w,⟨w,rfl⟩,?_⟩
  change hamZ (a,b,c,d) = (2:ℚ) • hamZ w
  have hvec : (a,b,c,d)=w+w := by apply Prod.ext <;> simp [w,Prod.ext_iff] <;> omega
  rw [hvec,hamZ_add,←two_smul ℚ]

theorem odd_intertwiner {n : ℕ} (hn : n%4=2) (v w : Triple) (hv : v∈shell n) (hw : w∈shell n) :
    ∃ q∈intertwiner v w, ∃ N : ℕ, Quaternion.normSq q=N ∧ Odd N := by
  classical
  let P (k : ℕ) := ∃ q∈intertwiner v w, ∃ N : ℕ, 0<N ∧ Quaternion.normSq q=N ∧ padicValNat 2 N=k
  obtain ⟨q,hq,hne,hi⟩ := intertwine v w hv hw
  obtain ⟨N,hN⟩ := norm_int hq
  have hNz : N≠0 := by rintro rfl; exact hne (Quaternion.normSq_eq_zero.mp (by simpa using hN))
  have hEx : ∃ k, P k := ⟨_,q,⟨hq,hi⟩,N,Nat.pos_of_ne_zero hNz,hN,rfl⟩
  obtain ⟨r,hr,m,hm,hnr,hval⟩ := Nat.find_spec hEx
  refine ⟨r,hr,m,hnr,?_⟩
  by_contra hodd
  obtain ⟨t,ht,htr⟩ := half_integral hr.1 (pure_mem v) hnr
    (by rw [pure_norm,TunnellShell.mem_shell.mp hv]; simp) (Nat.not_odd_iff_even.mp hodd)
    (Nat.even_iff.mpr (by omega : n%2=0))
  have he : t∈intertwiner v w := by
    refine ⟨ht,?_⟩
    apply smul_right_injective Q (by norm_num : (2:ℚ)≠0)
    change (2:ℚ) • (TunnellHurwitz.pure w*t)=(2:ℚ) • (t*TunnellHurwitz.pure v)
    calc _ = TunnellHurwitz.pure w * ((2:ℚ) • t) := (Algebra.mul_smul_comm _ _ _).symm
         _ = ((2:ℚ) • t)*TunnellHurwitz.pure v := by rw [←htr,←mul_assoc,hr.2]
         _ = _ := smul_mul_assoc _ _ _
  obtain ⟨T,hT⟩ := norm_int ht
  have hprod := congrArg Quaternion.normSq htr
  rw [map_mul,hnr,pure_norm,TunnellShell.mem_shell.mp hv,←Quaternion.coe_mul_eq_smul,map_mul,Quaternion.normSq_coe,hT] at hprod
  have heN : m*n=4*T := by exact_mod_cast (show (m:ℚ)*n=4*T by push_cast at hprod; linarith)
  have hTp : 0<T := Nat.pos_of_ne_zero (by rintro rfl; simp at heN; omega)
  have hval' := congrArg (padicValNat 2) heN
  let K := n/2
  have hnK : n=2*K := by dsimp [K]; omega
  have hK : 0<K := by dsimp [K]; omega
  have hK₂ : ¬2∣K := by dsimp [K]; omega
  rw [hnK,padicValNat.mul (by omega) (by positivity),padicValNat.mul (by decide) hK.ne',
    padicValNat.mul (by decide) hTp.ne',padicValNat.eq_zero_of_not_dvd hK₂,
    padicValNat_self,show padicValNat 2 4=2 by rw [show 4=2*2 by decide,padicValNat.mul (by decide) (by decide),padicValNat_self]] at hval'
  have hle := Nat.find_min' hEx (show P (padicValNat 2 T) from ⟨t,he,T,hTp,hT,rfl⟩)
  omega

end TunnellToricLocal
end

section
/- Local-to-global invertibility and composition of the quadratic intertwiner ideals. -/

namespace TunnellToricLocal
open TunnellHurwitz TunnellHurwitzFour TunnellShell Quaternion

def rat (a : Quaternion ℤ) : Q := ⟨a.re,a.imI,a.imJ,a.imK⟩

lemma rat_mul (a b : Quaternion ℤ) : rat (a*b)=rat a*rat b := by
  apply QuaternionAlgebra.ext
  all_goals
    first | rw [Quaternion.re_mul] | rw [Quaternion.imI_mul] | rw [Quaternion.imJ_mul] | rw [Quaternion.imK_mul]
    dsimp only [rat]
    simp only [Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,Int.cast_sub,Int.cast_mul,Int.cast_add]

lemma rat_norm (a : Quaternion ℤ) : Quaternion.normSq (rat a)=((Quaternion.normSq a:ℤ):ℚ) := by
  rw [Quaternion.normSq_def',Quaternion.normSq_def']; simp [rat]

lemma local_prime (p n : ℕ) (hp : p.Prime) (hn : Squarefree n) (h2 : n%4=2)
    (v w : Triple) (hv : v∈shell n) (hw : w∈shell n) :
    ∃ q∈intertwiner v w, ∃ N : ℤ, Quaternion.normSq q=(N:ℚ) ∧ ¬(p:ℤ)∣N := by
  by_cases hp2 : p=2
  · subst p
    obtain ⟨q,hq,N,hN,ho⟩ := odd_intertwiner h2 v w hv hw
    exact ⟨q,hq,N,by simpa using hN,by exact_mod_cast (Nat.not_even_iff_odd.mpr ho : ¬Even N) ∘ (fun h : (2:ℕ)∣N => even_iff_two_dvd.mpr h)⟩
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨q,he,hd⟩ := coprime_intertwiner hp2 hn v w hv hw
    refine ⟨rat q,⟨integer_coords _ _ _ _,?_⟩,_,rat_norm _,hd⟩
    have h := congrArg rat he
    simp only [rat_mul] at h
    exact h

def norms (v w : Triple) : Set ℤ := {N | ∃ q∈intertwiner v w, Quaternion.normSq q=(N:ℚ)}

lemma norm_ideal_top {n : ℕ} (hn : Squarefree n) (h2 : n%4=2)
    (v w : Triple) (hv : v∈shell n) (hw : w∈shell n) : Ideal.span (norms v w)=⊤ := by
  let I := Ideal.span (norms v w)
  let g := Submodule.IsPrincipal.generator I
  suffices h : IsUnit g from I.eq_top_of_isUnit_mem (Submodule.IsPrincipal.generator_mem I) h
  by_contra h
  have hg : g.natAbs ≠ 1 := by intro hh; exact h (by simpa [Int.isUnit_iff_natAbs_eq] using hh)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hg
  obtain ⟨q,hq,N,hN,he⟩ := local_prime p n hp hn h2 v w hv hw
  have him : N∈I := Ideal.subset_span (show N∈norms v w from ⟨q,hq,hN⟩)
  exact he ((Int.natCast_dvd.mpr hd).trans ((Submodule.IsPrincipal.mem_iff_generator_dvd I).mp him))

lemma star_order {q : Q} (hq : q∈order) : star q∈order := by
  obtain ⟨⟨a,b,c,d⟩,rfl⟩ := hq
  refine ⟨(a+d,-b,-c,-d),?_⟩
  apply QuaternionAlgebra.ext
  all_goals simp only [Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star] <;> simp [hamZ,ham] <;> ring

lemma pure_star (v : Triple) : star (TunnellHurwitz.pure v)= -TunnellHurwitz.pure v := by
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg,
    Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star] <;> simp [TunnellHurwitz.pure]

lemma star_intertwines {v w : Triple} {q : Q} (hq : q∈intertwiner v w) : star q∈intertwiner w v := by
  have he := congrArg star hq.2
  simp only [star_mul,pure_star,mul_neg,neg_mul,neg_inj] at he
  exact ⟨star_order hq.1,he.symm⟩

def idealProd (A B : AddSubgroup Q) : Submodule ℤ Q := Submodule.span ℤ {x | ∃ a∈A, ∃ b∈B, x=a*b}

lemma idealProd_mem {A B : AddSubgroup Q} {a b : Q} (ha : a∈A) (hb : b∈B) :
    a*b∈idealProd A B := Submodule.subset_span ⟨a,ha,b,hb,rfl⟩

lemma idealProd_one {n : ℕ} (hn : Squarefree n) (h2 : n%4=2)
    (v w : Triple) (hv : v∈shell n) (hw : w∈shell n) : (1:Q)∈idealProd (intertwiner w v) (intertwiner v w) := by
  let f : ℤ →ₗ[ℤ] Q := (Int.castRingHom Q).toAddMonoidHom.toIntLinearMap
  let I := idealProd (intertwiner w v) (intertwiner v w)
  have hle : Ideal.span (norms v w) ≤ I.comap f := by
    apply Submodule.span_le.mpr
    rintro N ⟨q,hq,hn⟩
    change (N:Q)∈I
    have he : star q*q=(N:Q) := by rw [star_mul_self,hn]; rfl
    rw [←he]
    exact idealProd_mem (star_intertwines hq) hq
  have h := hle (show (1:ℤ) ∈ Ideal.span (norms v w) by rw [norm_ideal_top hn h2 v w hv hw]; exact Submodule.mem_top)
  change ((1:ℤ):Q)∈I at h
  simpa using h

lemma compose_ideals {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) (u v w : Triple)
    (hu : u∈shell n) (hv : v∈shell n) :
    idealProd (intertwiner v w) (intertwiner u v)=(intertwiner u w).toIntSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,b,hb,rfl⟩
    exact intertwiner_comp ha hb
  · intro x hx
    let f : Q →ₗ[ℤ] Q := (AddMonoidHom.mulLeft x).toIntLinearMap
    let I := idealProd (intertwiner v w) (intertwiner u v)
    have hle : idealProd (intertwiner v u) (intertwiner u v) ≤ I.comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,ha,b,hb,rfl⟩
      change x*(a*b)∈I
      rw [←mul_assoc]
      exact idealProd_mem (intertwiner_comp hx ha) hb
    have he := hle (idealProd_one hn h2 u v hu hv)
    change x*1∈I at he
    simpa using he

end TunnellToricLocal
end

section
/- The twelve effective conjugations of the Hurwitz units and a fundamental domain. -/

namespace TunnellToric
open TunnellShell TunnellHurwitz TunnellHurwitzFour Finset Quaternion

def cyc (k : Fin 3) (v : Triple) : Triple := ![v,rot v,rot (rot v)] k
def signs (s : Fin 4) (v : Triple) : Triple :=
  ![v, (v.1,-v.2.1,-v.2.2),(-v.1,v.2.1,-v.2.2),(-v.1,-v.2.1,v.2.2)] s
def move (k : Fin 3) (s : Fin 4) (v : Triple) : Triple := signs s (cyc k v)
def basis (i : Fin 3) : Triple := ![(1,0,0),(0,1,0),(0,0,1)] i

def act (q : Q) (v : Triple) : Q := q*pure v*star q

def lin (v : Triple) (a b c : Q) : Q := (v.1:ℚ) • a+(v.2.1:ℚ) • b+(v.2.2:ℚ) • c

lemma pure_lin (v : Triple) : pure v=lin v (pure (basis 0)) (pure (basis 1)) (pure (basis 2)) := by
  apply QuaternionAlgebra.ext
  · change 0=(v.1:ℚ)*0+v.2.1*0+v.2.2*0; ring
  · change (v.1:ℚ)=(v.1:ℚ)*1+v.2.1*0+v.2.2*0; ring
  · change (v.2.1:ℚ)=(v.1:ℚ)*0+v.2.1*1+v.2.2*0; ring
  · change (v.2.2:ℚ)=(v.1:ℚ)*0+v.2.1*0+v.2.2*1; ring

lemma move_lin (k : Fin 3) (s : Fin 4) (v : Triple) :
    pure (move k s v)=lin v (pure (move k s (basis 0))) (pure (move k s (basis 1))) (pure (move k s (basis 2))) := by
  unfold lin
  apply QuaternionAlgebra.ext
  all_goals
    simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add,
      Quaternion.re_smul,Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul]
    fin_cases k <;> fin_cases s <;> simp [TunnellHurwitz.pure,move,cyc,rot,signs,basis]

lemma act_lin (q : Q) (v : Triple) :
    act q v=lin v (act q (basis 0)) (act q (basis 1)) (act q (basis 2)) := by
  unfold act
  rw [pure_lin v]
  simp only [lin,mul_add,add_mul,Algebra.mul_smul_comm,smul_mul_assoc]

noncomputable def integralUnits : Finset (H ℤ) := (Icc (-2:ℤ) 2 ×ˢ (Icc (-2:ℤ) 2 ×ˢ (Icc (-2:ℤ) 2 ×ˢ Icc (-2:ℤ) 2))).filter fun u => nr u = 1

def twice (u : H ℤ) : Quaternion ℤ := ⟨2*u.1+u.2.2.2,2*u.2.1+u.2.2.2,2*u.2.2.1+u.2.2.2,u.2.2.2⟩

def rot4 (u : H ℤ) (v : Triple) : Triple := TunnellQuaternion.rotate (twice u) v

lemma rot4_eq (u : H ℤ) (v : Triple) : pure (rot4 u v)=(4:ℚ) • act (hamZ u) v := by
  obtain ⟨a,b,c,d⟩ := u
  obtain ⟨x,y,z⟩ := v
  unfold rot4 twice
  rw [TunnellQuaternion.rotate_apply]
  apply QuaternionAlgebra.ext
  all_goals
    simp only [Quaternion.re_smul,Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul,
      act,Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,
      Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star]
    dsimp [TunnellHurwitz.pure,hamZ,ham]
    push_cast
    ring

lemma pure_four (v : Triple) : pure ((4:ℤ) • v)=(4:ℚ) • pure v := by
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_smul,Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul] <;> simp [TunnellHurwitz.pure]

def agrees (u : H ℤ) (k : Fin 3) (s : Fin 4) : Prop := ∀ i : Fin 3, rot4 u (basis i) = (4:ℤ) • move k s (basis i)
instance (u k s) : Decidable (agrees u k s) := by unfold agrees; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma rotations_table : (∀ u ∈ integralUnits, ∃ (k:Fin 3) (s:Fin 4), agrees u k s) ∧
    (∀ (k:Fin 3) (s:Fin 4), ∃ u ∈ integralUnits, agrees u k s) := by
  decide

lemma agrees_all {u k s} (h : agrees u k s) (v : Triple) : act (hamZ u) v = pure (move k s v) := by
  have hi (i : Fin 3) : act (hamZ u) (basis i)=pure (move k s (basis i)) := by
    have he := congrArg TunnellHurwitz.pure (h i)
    rw [rot4_eq,pure_four] at he
    exact (smul_right_injective Q (by norm_num : (4:ℚ)≠0)) he
  rw [act_lin,move_lin,hi 0,hi 1,hi 2]

lemma mem_units (u : H ℤ) : u∈integralUnits ↔ nr u=1 := by
  exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨norm_one_mem u h,h⟩⟩

lemma norm_ham (u : H ℤ) : Quaternion.normSq (hamZ u)=((nr u:ℤ):ℚ) := by simp [hamZ,ham_norm,nr]

lemma conjugate_iff (v w : Triple) :
    (∃ q∈order, Quaternion.normSq q=1 ∧ act q v=pure w) ↔ ∃ k s, move k s v=w := by
  constructor
  · rintro ⟨_,⟨u,rfl⟩,hn,hq⟩
    rw [norm_ham] at hn
    obtain ⟨k,s,h⟩ := rotations_table.1 u ((mem_units u).mpr (by exact_mod_cast hn))
    exact ⟨k,s,pure_injective ((agrees_all h v).symm.trans hq)⟩
  · rintro ⟨k,s,rfl⟩
    obtain ⟨u,hu,h⟩ := rotations_table.2 k s
    exact ⟨hamZ u,⟨u,rfl⟩,by rw [norm_ham,(mem_units u).mp hu]; simp,agrees_all h v⟩

end TunnellToric
end

section
/- Signed sums over representatives for optimal embeddings modulo the norm-one Hurwitz units. -/

namespace TunnellToric

open TunnellShell TunnellHurwitz Finset
open scoped Classical

def isRep (v : Triple) : Prop := Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1

noncomputable def representatives (n : ℕ) : Finset Triple := (shell n).filter isRep

lemma parity_type {n : ℕ} (hn : n%4=2) {v : Triple} (hv : v∈shell n) :
    (Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2) ∨ (Odd v.2.1 ∧ Odd v.2.2 ∧ Even v.1) ∨
    (Odd v.2.2 ∧ Odd v.1 ∧ Even v.2.1) := by
  have small : ∀ a b c : ZMod 4, a^2+b^2+c^2=2 →
      (a.val%2=1 ∧ b.val%2=1 ∧ c.val%2=0) ∨ (b.val%2=1 ∧ c.val%2=1 ∧ a.val%2=0) ∨
        (c.val%2=1 ∧ a.val%2=1 ∧ b.val%2=0) := by decide
  have hn' : (n:ZMod 4)=2 := by apply ZMod.val_injective 4; rw [ZMod.val_natCast,hn]; decide
  have he := congrArg (fun t:ℤ => (t:ZMod 4)) (mem_shell.mp hv)
  simp only [normSq,Int.cast_add,Int.cast_pow,Int.cast_natCast,hn'] at he
  have hh := small _ _ _ he
  have ha := ZMod.val_intCast (n:=4) v.1
  have hb := ZMod.val_intCast (n:=4) v.2.1
  have hc := ZMod.val_intCast (n:=4) v.2.2
  simp only [Int.odd_iff,Int.even_iff]
  omega

lemma sign_section {v : Triple} (h : Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2) : ∃ s, isRep (signs s v) := by
  obtain ⟨a,b,c⟩ := v
  change Odd a ∧ Odd b ∧ Even c at h
  have ha := Int.odd_iff.mp h.1
  have hb := Int.odd_iff.mp h.2.1
  by_cases hA : 0<a <;> by_cases hB : 0<b
  · exact ⟨0,by simpa [isRep,signs] using And.intro h.1 ⟨h.2.1,h.2.2,hA,hB⟩⟩
  · exact ⟨1,by simp [isRep,signs,h.1,h.2.1,h.2.2,hA]; omega⟩
  · exact ⟨2,by simp [isRep,signs,h.1,h.2.1,h.2.2,hB]; omega⟩
  · exact ⟨3,by simp [isRep,signs,h.1,h.2.1,h.2.2]; omega⟩

lemma exists_rep {n : ℕ} (hn : n%4=2) {v : Triple} (hv : v∈shell n) :
    ∃ k s, isRep (move k s v) := by
  rcases parity_type hn hv with h|h|h
  · exact ⟨0,sign_section h⟩
  · exact ⟨1,sign_section h⟩
  · exact ⟨2,sign_section h⟩

lemma represents_once {v : Triple} (hv : isRep v) (k : Fin 3) (s : Fin 4) :
    isRep (move k s v) ↔ k=0 ∧ s=0 := by
  rcases v with ⟨a,b,c⟩
  obtain ⟨ha,hb,hc,hp,hq⟩ := hv
  dsimp only at ha hb hc hp hq
  have hca : ¬Odd c := Int.not_odd_iff_even.mpr hc
  fin_cases k <;> fin_cases s <;> simp [isRep,move,cyc,signs,rot,ha,hb,hc,hp,hq,hca] <;> omega

lemma move_shell (k : Fin 3) (s : Fin 4) {n : ℕ} {v : Triple} (hv : v∈shell n) : move k s v∈shell n := by
  rw [mem_shell] at hv ⊢
  obtain ⟨a,b,c⟩ := v
  fin_cases k <;> fin_cases s <;> simp [normSq,move,cyc,signs,rot] at * <;> linarith

lemma rep_unique {n : ℕ} {v w : Triple} (hv : v∈representatives n) (hw : w∈representatives n)
    (he : ∃ q∈order, Quaternion.normSq q=1 ∧ act q v=pure w) : v=w := by
  obtain ⟨k,s,h⟩ := (conjugate_iff v w).mp he
  have hm : isRep (move k s v) := h ▸ (mem_filter.mp hw).2
  obtain ⟨rfl,rfl⟩ := (represents_once (mem_filter.mp hv).2 k s).mp hm
  exact h

lemma rep_exists {n : ℕ} (hn : n%4=2) {v : Triple} (hv : v∈shell n) :
    ∃ w∈representatives n, ∃ q∈order, Quaternion.normSq q=1 ∧ act q v=pure w := by
  obtain ⟨k,s,he⟩ := exists_rep hn hv
  exact ⟨move k s v,mem_filter.mpr ⟨move_shell k s hv,he⟩,
    (conjugate_iff v _).mpr ⟨k,s,rfl⟩⟩

end TunnellToric
end

section
/- Extension and contraction of invertible imaginary-quadratic ideals in the Hurwitz order. -/
namespace TunnellToricClass
open TunnellShell TunnellHurwitz TunnellToricLocal
open scoped Pointwise
abbrev Lattice := Submodule ℤ Q
abbrev O : Lattice := order.toAddSubgroup.toIntSubmodule
abbrev J (v w : Triple) : Lattice := (intertwiner v w).toIntSubmodule
abbrev line (a : Q) : Lattice := Submodule.span ℤ {a}

def C (v : Triple) : Lattice := LinearMap.ker ((AddMonoidHom.mulLeft (TunnellHurwitz.pure v)).toIntLinearMap - (AddMonoidHom.mulRight (TunnellHurwitz.pure v)).toIntLinearMap)
lemma mem_C {v : Triple} {a : Q} : a∈C v ↔ TunnellHurwitz.pure v*a=a*TunnellHurwitz.pure v := sub_eq_zero
lemma mem_J {v w : Triple} {a : Q} : a∈J v w ↔ a∈O ∧ TunnellHurwitz.pure w*a=a*TunnellHurwitz.pure v := Iff.rfl
lemma order_commutant (v : Triple) : O ⊓ C v = J v v := by ext x; rw [Submodule.mem_inf,mem_C,mem_J]
lemma one_O : (1:Q)∈O := order.one_mem
lemma one_J (v : Triple) : (1:Q)∈J v v := ⟨one_O,by simp⟩
lemma mul_O : O*O=O := by
  apply le_antisymm (Submodule.mul_le.mpr fun _ ha _ hb => order.mul_mem ha hb)
  intro a ha; simpa using Submodule.mul_mem_mul ha one_O
lemma mul_C (v : Triple) : C v * C v ≤ C v := by
  apply Submodule.mul_le.mpr
  intro a ha b hb
  apply mem_C.mpr
  rw [←mul_assoc,mem_C.mp ha,mul_assoc,mem_C.mp hb,mul_assoc]
lemma central_comm {n : ℕ} (hn : Squarefree n) {v : Triple} (hv : v∈shell n) {a b : Q} (ha : a∈C v) (hb : b∈C v) : a*b=b*a := by
  obtain ⟨r,er⟩ := centralizer hn hv a (mem_C.mp ha).symm
  obtain ⟨s,es⟩ := centralizer hn hv b (mem_C.mp hb).symm
  conv_lhs => rw [er,es]
  conv_rhs => rw [es,er]
  apply QuaternionAlgebra.ext
  all_goals first | rw [Quaternion.re_mul,Quaternion.re_mul] | rw [Quaternion.imI_mul,Quaternion.imI_mul] | rw [Quaternion.imJ_mul,Quaternion.imJ_mul] | rw [Quaternion.imK_mul,Quaternion.imK_mul]
  all_goals dsimp only [evalRat]; ring
lemma ideals_comm {n : ℕ} (hn : Squarefree n) {v : Triple} (hv : v∈shell n) {A B : Lattice} (ha : A≤C v) (hb : B≤C v) : A*B=B*A := by
  apply le_antisymm <;> apply Submodule.mul_le.mpr
  · intro a h₁ b h₂; rw [central_comm hn hv (ha h₁) (hb h₂)]; exact Submodule.mul_mem_mul h₂ h₁
  · intro a h₁ b h₂; rw [central_comm hn hv (hb h₁) (ha h₂)]; exact Submodule.mul_mem_mul h₂ h₁
lemma J_comp {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {u v w : Triple} (hu : u∈shell n) (hv : v∈shell n) : J v w * J u v = J u w := by
  refine Eq.trans ?_ (compose_ideals hn h2 u v w hu hv)
  apply le_antisymm (Submodule.mul_le.mpr fun _ ha _ hb => idealProd_mem ha hb)
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,b,hb,rfl⟩
  exact Submodule.mul_mem_mul ha hb
lemma J_extends {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {u v : Triple} (hu : u∈shell n) (hv : v∈shell n) : J u v*O=O := by
  have h₁ : 1 ≤ J u v*J v u := by rw [J_comp hn h2 hv hu]; exact Submodule.one_le.mpr (one_J v)
  have h₂ : 1 ≤ J u v*O := h₁.trans (mul_le_mul_right (show J v u ≤ O from fun _ h => h.1) _)
  apply le_antisymm
  · exact (mul_le_mul_left (show J u v ≤ O from fun _ h => h.1) _).trans mul_O.le
  · calc O = 1*O := (one_mul _).symm
         _ ≤ (J u v*O)*O := mul_le_mul_left h₂ _
         _ = _ := by rw [mul_assoc,mul_O]

/- An invertible ideal is recovered by intersecting its extension with the quadratic field. -/
lemma contract {v : Triple} {A B : Lattice} (hA : A≤C v) (hB : B≤C v)
    (hAB : A*B=J v v) (hBA : B*A=J v v) (hR : A*J v v=A) : A*O ⊓ C v=A := by
  let D := A*O ⊓ C v
  have hBD : B*D ≤ J v v := by
    rw [←order_commutant]
    apply le_inf
    · calc B*D ≤ B*(A*O) := mul_le_mul_right inf_le_left _
           _ = J v v*O := by rw [←mul_assoc,hBA]
           _ ≤ O*O := mul_le_mul_left (show J v v ≤ O from fun _ h => h.1) _
           _ = O := mul_O
    · exact (mul_le_mul' hB (show D≤C v from inf_le_right)).trans (mul_C v)
  apply le_antisymm
  · calc D = 1*D := (one_mul _).symm
         _ ≤ J v v*D := mul_le_mul_left (Submodule.one_le.mpr (one_J v)) _
         _ = A*(B*D) := by rw [←mul_assoc,hAB]
         _ ≤ A*J v v := mul_le_mul_right hBD _
         _ = A := hR
  · apply le_inf _ hA
    intro a ha; simpa using Submodule.mul_mem_mul ha one_O

lemma principal_extension {A : Lattice} (ha : A≤O) (hne : A≠⊥) :
    ∃ a∈A*O, a≠0 ∧ A*O=line a*O := by
  let D := A*O
  have hm : D*O=D := by change (A*O)*O=A*O; rw [mul_assoc,mul_O]
  have hi : D≤O := (mul_le_mul_left ha _).trans mul_O.le
  obtain ⟨b,hb,hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨a,h₁,h₂,h₃⟩ := integral_class_number_one (D:Set Q) hi
    (fun x hx y hy => D.sub_mem hx hy)
    (fun x hx y hy => hm ▸ Submodule.mul_mem_mul hx (show y∈O from hy))
    ⟨b,by simpa using Submodule.mul_mem_mul hb one_O,hb0⟩
  refine ⟨a,h₁,h₂,?_⟩
  ext x
  change x∈(D:Set Q) ↔ _
  rw [h₃,Submodule.mem_span_singleton_mul]
  constructor <;> rintro ⟨z,hz,h⟩ <;> exact ⟨z,hz,h.symm⟩

lemma J_right {u v : Triple} {a : Q} (ha : a≠0) (he : TunnellHurwitz.pure v*a=a*TunnellHurwitz.pure u) :
    line a*O ⊓ C v = line a*J v u := by
  ext x
  simp only [Submodule.mem_inf,Submodule.mem_span_singleton_mul,mem_C]
  constructor
  · rintro ⟨⟨y,hy,rfl⟩,hh⟩
    refine ⟨y,⟨hy,mul_left_cancel₀ ha ?_⟩,rfl⟩
    rw [←mul_assoc,←he,mul_assoc,hh,mul_assoc]
  · rintro ⟨y,hy,rfl⟩
    refine ⟨⟨y,hy.1,rfl⟩,?_⟩
    rw [←mul_assoc,he,mul_assoc,hy.2,mul_assoc]

/- Every invertible integral ideal in the quadratic field is a scalar multiple of the
intertwiner lattice for an optimal embedding of that field into the Hurwitz order. -/
lemma classify_ideal {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple} (hv : v∈shell n)
    {A B : Lattice} (ha : A≤O) (hA : A≤C v) (hB : B≤C v) (hAB : A*B=J v v) (hR : A*J v v=A) :
    ∃ w∈shell n, ∃ a∈J w v, a≠0 ∧ A=line a*J v w := by
  have hBA := (ideals_comm hs hv hB hA).trans hAB
  have hh := contract hA hB hAB hBA hR
  have hne : A≠⊥ := by
    rintro rfl; rw [Submodule.bot_mul] at hAB
    have h₁ := one_J v; rw [←hAB] at h₁; exact one_ne_zero h₁
  obtain ⟨a,haD,ha0,he⟩ := principal_extension ha hne
  have hO : a∈O := (mul_le_mul_left ha _).trans mul_O.le haD
  have hco : J v v ≤ C v := fun _ h => mem_C.mpr h.2
  have hra : J v v*A=A := (ideals_comm hs hv hco hA).trans hR
  have hp : TunnellHurwitz.pure v∈J v v := ⟨pure_mem _,rfl⟩
  have hm := Submodule.mul_mem_mul hp haD
  rw [←mul_assoc,hra,he,Submodule.mem_span_singleton_mul] at hm
  obtain ⟨t,ht,heq⟩ := hm
  have ht2 : t*t= -(n:Q) := by
    apply mul_left_cancel₀ ha0
    calc a*(t*t)=(TunnellHurwitz.pure v*TunnellHurwitz.pure v)*a := by rw [←mul_assoc,heq,mul_assoc,heq,←mul_assoc]
         _=a* -(n:Q) := by rw [pure_square hv,neg_mul,mul_neg,Nat.cast_comm]
  obtain ⟨hr,hN⟩ := negative_root (show 0<n by omega) t ht2
  obtain ⟨w,rfl⟩ := trace_zero_integral ht hr
  have hw : w∈shell n := by rw [mem_shell]; rw [pure_norm] at hN; exact_mod_cast hN
  exact ⟨w,hw,a,⟨hO,heq.symm⟩,ha0,by rw [←hh,he,J_right ha0 heq.symm]⟩

lemma line_mul (a b : Q) : line a * line b = line (a*b) := by rw [line,line,Submodule.span_mul_span,Set.singleton_mul_singleton]
lemma line_one : line 1=1 := (Submodule.one_eq_span).symm
lemma two_sided_inverse {a : Q} (ha : a≠0) : line a⁻¹*line a=1 := by rw [line_mul,inv_mul_cancel₀ ha,line_one]

/- Invertible integral ideals in the centralizer order; the inverse may be fractional. -/
def isIdeal (v : Triple) (A : Lattice) : Prop :=
  A≤O ∧ A≤C v ∧ A*J v v=A ∧ ∃ B≤C v, A*B=J v v

lemma from_embedding {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v w : Triple}
    (hv : v∈shell n) (hw : w∈shell n) {a : Q} (ha : a∈J w v) (ha0 : a≠0) :
    isIdeal v (line a*J v w) := by
  let A := line a*J v w
  let B := J w v*line a⁻¹
  have hi : A ≤ O := by
    intro z hz; obtain ⟨q,hq,rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
    exact order.mul_mem ha.1 hq.1
  have hA : A≤C v := by change line a*J v w≤_; rw [←J_right ha0 ha.2]; exact inf_le_right
  have hB : B≤C v := by
    intro z hz; obtain ⟨q,hq,rfl⟩ := Submodule.mem_mul_span_singleton.mp hz
    apply mem_C.mpr
    apply mul_right_cancel₀ ha0
    calc (TunnellHurwitz.pure v * (q*a⁻¹))*a = TunnellHurwitz.pure v*q := by simp [mul_assoc,ha0]
         _=q*TunnellHurwitz.pure w := hq.2
         _=(q*a⁻¹*TunnellHurwitz.pure v)*a := by rw [mul_assoc,ha.2]; simp [mul_assoc,ha0]
  have hBA : B*A=J v v := by
    change (J w v*line a⁻¹)*(line a*J v w)=_
    rw [mul_assoc,←mul_assoc (line a⁻¹),two_sided_inverse ha0,one_mul,J_comp hs hn hv hw]
  refine ⟨hi,hA,?_,B,hB,(ideals_comm hs hv hA hB).trans hBA⟩
  rw [mul_assoc,J_comp hs hn hv hv]

end TunnellToricClass
end

section
/- Optimal embeddings and proper invertible quadratic ideal classes. -/
namespace TunnellToricClass
open TunnellShell TunnellHurwitz TunnellToricLocal TunnellToric
open scoped Pointwise

lemma line_O {q : Q} (hq : q∈O) (hq' : q⁻¹∈O) (h0 : q≠0) : line q*O=O := by
  apply le_antisymm
  · intro z hz; obtain ⟨x,hx,rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
    exact order.mul_mem hq hx
  · intro x hx; exact Submodule.mem_span_singleton_mul.mpr ⟨q⁻¹*x,order.mul_mem hq' hx,by simp [h0]⟩

lemma line_O_equal {a b : Q} (_ha : a≠0) (hb : b≠0) (h : line a*O=line b*O) :
    ∃ q∈O, Quaternion.normSq q=1 ∧ a=b*q := by
  have owned (t : Q) : t∈line t*O := Submodule.mem_span_singleton_mul.mpr ⟨1,one_O,mul_one _⟩
  obtain ⟨q,hq,e₁⟩ := Submodule.mem_span_singleton_mul.mp (h ▸ owned a)
  obtain ⟨r,hr,e₂⟩ := Submodule.mem_span_singleton_mul.mp (h.symm ▸ owned b)
  have e : q*r=1 := mul_left_cancel₀ hb (by rw [←mul_assoc,e₁,e₂,mul_one])
  obtain ⟨N,hN⟩ := norm_int hq
  obtain ⟨M,hM⟩ := norm_int hr
  have hn := congrArg Quaternion.normSq e
  rw [map_mul,map_one,hN,hM] at hn
  have hnm : N*M=1 := by exact_mod_cast hn
  rw [Nat.eq_one_of_dvd_one (show N∣1 from ⟨M,hnm.symm⟩)] at hN
  exact ⟨q,hq,by simpa using hN,e₁.symm⟩

lemma inv_eq_star_of_unit {q : Q} (hq : Quaternion.normSq q=1) : q⁻¹=star q := by
  have hq0 : q≠0 := by intro h; simp [h] at hq
  apply mul_right_cancel₀ hq0
  rw [inv_mul_cancel₀ hq0,Quaternion.star_mul_self,hq,Quaternion.coe_one]

lemma unit_frame {n : ℕ} (hn : n%4=2) {v w : Triple} (hw : w∈shell n)
    {a : Q} (ha : a∈J w v) (h0 : a≠0) :
    ∃ z∈representatives n, ∃ b∈J z v, b≠0 ∧ line a*J v w=line b*J v z := by
  obtain ⟨z,hz,q,hq,hN,hact⟩ := rep_exists hn hw
  have hq0 : q≠0 := by intro h; simp [h] at hN
  have hi : q⁻¹∈O := inv_eq_star_of_unit hN ▸ star_order hq
  have he' : TunnellHurwitz.pure z=q*TunnellHurwitz.pure w*q⁻¹ := hact.symm.trans (by rw [inv_eq_star_of_unit hN]; rfl)
  have he : TunnellHurwitz.pure v*(a*q⁻¹)=(a*q⁻¹)*TunnellHurwitz.pure z := by
    rw [←mul_assoc,ha.2,he']; simp [mul_assoc,hq0]
  have hqO : line q⁻¹*O=O := line_O hi (by rw [inv_inv]; exact hq) (inv_ne_zero hq0)
  have heO : line (a*q⁻¹)*O=line a*O := by rw [←line_mul,mul_assoc,hqO]
  refine ⟨z,hz,a*q⁻¹,⟨order.mul_mem ha.1 hi,he⟩,mul_ne_zero h0 (inv_ne_zero hq0),?_⟩
  rw [←J_right h0 ha.2,←J_right (mul_ne_zero h0 (inv_ne_zero hq0)) he,heO]

lemma classify_rep {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple} (hv : v∈shell n)
    {A : Lattice} (h : isIdeal v A) :
    ∃ w∈representatives n, ∃ a∈J w v, a≠0 ∧ A=line a*J v w := by
  obtain ⟨ho,hA,hR,B,hB,hAB⟩ := h
  obtain ⟨w,hw,a,ha,h₀,e⟩ := classify_ideal hs hn hv ho hA hB hAB hR
  obtain ⟨z,hz,b,hb,hb0,hh⟩ := unit_frame hn hw ha h₀
  exact ⟨z,hz,b,hb,hb0,e.trans hh⟩

def homothetic (v : Triple) (A B : Lattice) : Prop := ∃ c∈C v, c≠0 ∧ line c*A=B

lemma frame_unique {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v w z : Triple} (hv : v∈shell n)
    (hw : w∈representatives n) (hz : z∈representatives n) {a b : Q} (ha : a∈J w v) (hb : b∈J z v)
    (ha0 : a≠0) (hb0 : b≠0) :
    homothetic v (line a*J v w) (line b*J v z) ↔ w=z := by
  classical
  constructor
  · rintro ⟨c,hc,hc0,he⟩
    have e := congrArg (fun I:Lattice => I*O) he
    change (line c*(line a*J v w))*O=(line b*J v z)*O at e
    rw [←mul_assoc (line c), line_mul] at e
    rw [mul_assoc,J_extends hs hn hv (Finset.mem_filter.mp hw).1,mul_assoc,J_extends hs hn hv (Finset.mem_filter.mp hz).1] at e
    obtain ⟨q,hq,hnq,e'⟩ := line_O_equal (mul_ne_zero hc0 ha0) hb0 e
    have hq0 : q≠0 := by intro h; simp [h] at hnq
    have ht : q*TunnellHurwitz.pure w=TunnellHurwitz.pure z*q := by
      apply mul_left_cancel₀ hb0
      calc b*(q*TunnellHurwitz.pure w)=(c*a)*TunnellHurwitz.pure w := by rw [←mul_assoc,←e']
           _=TunnellHurwitz.pure v*(c*a) := by rw [←mul_assoc (TunnellHurwitz.pure v),mem_C.mp hc,mul_assoc c (TunnellHurwitz.pure v),ha.2,mul_assoc]
           _=b*(TunnellHurwitz.pure z*q) := by rw [e',←mul_assoc,hb.2,mul_assoc]
    apply rep_unique hw hz
    refine ⟨q,hq,hnq,?_⟩
    change q*TunnellHurwitz.pure w*star q=TunnellHurwitz.pure z
    rw [ht,←inv_eq_star_of_unit hnq,mul_assoc,mul_inv_cancel₀ hq0,mul_one]
  · rintro rfl
    refine ⟨b*a⁻¹,mem_C.mpr ?_,mul_ne_zero hb0 (inv_ne_zero ha0),?_⟩
    · apply mul_right_cancel₀ ha0
      calc (TunnellHurwitz.pure v*(b*a⁻¹))*a=TunnellHurwitz.pure v*b := by simp [mul_assoc,ha0]
           _=b*TunnellHurwitz.pure w := hb.2
           _=(b*a⁻¹*TunnellHurwitz.pure v)*a := by rw [mul_assoc,ha.2]; simp [mul_assoc,ha0]
    · rw [←mul_assoc,line_mul,mul_assoc,inv_mul_cancel₀ ha0,mul_one]

abbrev IntegralIdeal (v : Triple) := {A : Lattice // isIdeal v A}

def idealSetoid (v : Triple) : Setoid (IntegralIdeal v) where
  r A B := homothetic v A.val B.val
  iseqv := {
    refl := fun _ => ⟨1,mem_C.mpr (by simp),one_ne_zero,by rw [line_one,one_mul]⟩
    symm := by
      rintro A B ⟨c,hc,h₀,he⟩
      refine ⟨c⁻¹,mem_C.mpr ((show Commute (TunnellHurwitz.pure v) c from mem_C.mp hc).inv_right₀),inv_ne_zero h₀,?_⟩
      rw [←he,←mul_assoc,two_sided_inverse h₀,one_mul]
    trans := by
      rintro A B D ⟨c,hc,hc₀,he⟩ ⟨d,hd,hd₀,he'⟩
      refine ⟨d*c,(mul_C v) (Submodule.mul_mem_mul hd hc),mul_ne_zero hd₀ hc₀,?_⟩
      rw [←line_mul,mul_assoc,he,he'] }

abbrev ProperIdealClass (v : Triple) := Quotient (idealSetoid v)

noncomputable def representative {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple}
    (hv : v∈shell n) (A : IntegralIdeal v) : ↥(representatives n) :=
  ⟨(classify_rep hs hn hv A.property).choose,(classify_rep hs hn hv A.property).choose_spec.1⟩

lemma representative_frame {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple}
    (hv : v∈shell n) (A : IntegralIdeal v) :
    ∃ a∈J (representative hs hn hv A).val v, a≠0 ∧ A.val=line a*J v (representative hs hn hv A).val :=
  (classify_rep hs hn hv A.property).choose_spec.2

lemma class_iff_same_rep {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple}
    (hv : v∈shell n) (A B : IntegralIdeal v) : homothetic v A B ↔ representative hs hn hv A=representative hs hn hv B := by
  obtain ⟨a,ha,h₀,he⟩ := representative_frame hs hn hv A
  obtain ⟨b,hb,h₁,he'⟩ := representative_frame hs hn hv B
  exact (show homothetic v A B ↔ (representative hs hn hv A).val=(representative hs hn hv B).val by
    conv_lhs => rw [he,he']
    exact frame_unique hs hn hv (representative hs hn hv A).property (representative hs hn hv B).property ha hb h₀ h₁).trans Subtype.ext_iff.symm

/- Hurwitz embedding classes are parametrized by invertible quadratic ideals modulo field homotheties. -/
noncomputable def idealEquiv {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple}
    (hv : v∈shell n) : ProperIdealClass v ≃ ↥(representatives n) := by
  classical
  let f : ProperIdealClass v → ↥(representatives n) := Quotient.lift (representative hs hn hv)
    (fun a b h => (class_iff_same_rep hs hn hv a b).mp h)
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b
    induction a using Quotient.inductionOn with | _ A =>
      induction b using Quotient.inductionOn with | _ B =>
        intro h
        exact Quotient.sound ((class_iff_same_rep hs hn hv A B).mpr h)
  · intro w
    have hw := (Finset.mem_filter.mp w.property).1
    obtain ⟨a,ha,ha0,he⟩ := intertwine w.val v hw hv
    have haJ : a∈J w.val v := ⟨ha,he⟩
    let A : IntegralIdeal v := ⟨line a*J v w.val,from_embedding hs hn hv hw haJ ha0⟩
    refine ⟨Quotient.mk (idealSetoid v) A,Subtype.ext ?_⟩
    obtain ⟨b,hb,hb0,he'⟩ := representative_frame hs hn hv A
    apply (frame_unique hs hn hv (representative hs hn hv A).property w.property hb haJ hb0 ha0).mp
    rw [←he']; exact (idealSetoid v).refl A

end TunnellToricClass
end

section
/- The proper quadratic ideals of the toric period are the images of ordinary ring ideals. -/
namespace TunnellEmbeddedIdeals
open TunnellIdealHNF TunnellShell TunnellHurwitz TunnellToricClass

def image {n : ℕ} {v : Triple} (hv : v∈shell n) (I : Ideal (TunnellIdealHNF.R n)) : Lattice :=
  I.toAddSubgroup.toIntSubmodule.map ((embed n v hv).toAddMonoidHom.toIntLinearMap)

lemma mem_image {n : ℕ} {v : Triple} (hv : v∈shell n) {I : Ideal (TunnellIdealHNF.R n)} {q : Q} :
    q∈image hv I ↔ ∃ z∈I, embed n v hv z=q := Iff.rfl

lemma embed_inj {n : ℕ} {v : Triple} (hn : Squarefree n) (hv : v∈shell n) : Function.Injective (embed n v hv) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  obtain ⟨x,y,z,he⟩ := primitive hn hv
  have e₁ := congrArg QuaternionAlgebra.re h
  have e₂ := congrArg QuaternionAlgebra.imI h
  have e₃ := congrArg QuaternionAlgebra.imJ h
  have e₄ := congrArg QuaternionAlgebra.imK h
  change (a:ℚ)=c at e₁
  change (b:ℚ)*v.1=d*v.1 at e₂
  change (b:ℚ)*v.2.1=d*v.2.1 at e₃
  change (b:ℚ)*v.2.2=d*v.2.2 at e₄
  apply Zsqrtd.ext (by exact_mod_cast e₁)
  have h' : (v.1:ℚ)*x+v.2.1*y+v.2.2*z=1 := by exact_mod_cast he
  have H : (b:ℚ)=d := by linear_combination x*e₂+y*e₃+z*e₄-(b-d)*h'
  exact_mod_cast H

lemma image_injective {n : ℕ} {v : Triple} (hn : Squarefree n) (hv : v∈shell n) : Function.Injective (image hv) := by
  intro I K he; ext z
  have h (J : Ideal _) : (embed n v hv z)∈image hv J ↔ z∈J := by
    constructor
    · rintro ⟨y,hy,ey⟩; exact embed_inj hn hv ey ▸ hy
    · intro hz; exact ⟨z,hz,rfl⟩
  rw [←h,he,h]

lemma image_order {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) :
    image hv ⊤=J v v := by
  ext q
  constructor
  · rw [mem_image]; rintro ⟨z,_,rfl⟩
    exact ⟨embed_integral _ _ _ _,by rw [←embed_root n v hv,←map_mul,←map_mul,mul_comm]⟩
  · rintro ⟨hq,he⟩; obtain ⟨z,ez⟩ := integral_centralizer hn h2 hv hq he.symm
    exact ⟨z,Submodule.mem_top,ez.symm⟩

lemma image_mul {n : ℕ} {v : Triple} (hv : v∈shell n) (A B : Ideal (R n)) :
    image hv (A*B)=image hv A*image hv B := by
  apply le_antisymm
  · intro q hq; obtain ⟨z,hz,rfl⟩ := (mem_image _).mp hq
    apply Submodule.mul_induction_on (C := fun a => embed n v hv a ∈ image hv A*image hv B) hz
    · intro a ha b hb
      rw [map_mul]
      exact Submodule.mul_mem_mul ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    · intro a b ha hb
      rw [map_add]; exact add_mem ha hb
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    obtain ⟨a,ha,rfl⟩ := (mem_image _).mp hx
    obtain ⟨b,hb,rfl⟩ := (mem_image _).mp hy
    exact ⟨a*b,Ideal.mul_mem_mul ha hb,map_mul (embed n v hv) a b⟩

lemma image_principal {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) (a : R n) :
    image hv (Ideal.span {a})=line (embed n v hv a)*J v v := by
  rw [←image_order hn h2 hv]
  ext q
  constructor
  · rintro ⟨z,hz,rfl⟩; obtain ⟨b,rfl⟩ := Ideal.mem_span_singleton.mp hz
    exact Submodule.mem_span_singleton_mul.mpr ⟨_,⟨b,Submodule.mem_top,rfl⟩,(map_mul ..).symm⟩
  · intro h
    obtain ⟨t,ht,rfl⟩ := Submodule.mem_span_singleton_mul.mp h
    obtain ⟨b,_,rfl⟩ := (mem_image _).mp ht
    exact ⟨a*b,Ideal.mem_span_singleton.mpr (dvd_mul_right _ _),map_mul (embed n v hv) a b⟩

lemma center_image {n : ℕ} {v : Triple} (hv : v∈shell n) (I : Ideal (R n)) : image hv I≤C v := by
  intro q hq; obtain ⟨a,_,rfl⟩ := (mem_image _).mp hq; apply mem_C.mpr; rw [←embed_root n v hv,←map_mul,←map_mul,mul_comm]

lemma image_isIdeal {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) (I : Ideal (R n)) (hI : I≠⊥) :
    isIdeal v (image hv I) := by
  obtain ⟨s,rfl⟩ := normal_form (show 0<n by omega) hI
  let N : Q := idx s
  have hN : N≠0 := by intro h; have H := congrArg QuaternionAlgebra.re h; change ((idx s:ℕ):ℚ)=0 at H; exact (show idx s≠0 from mul_ne_zero (pow_ne_zero _ s.pos_c.ne') s.pos_a.ne') (by exact_mod_cast H)
  have his : ∀ x : Q, x*N=N*x := fun x => (Nat.cast_comm (idx s) x).symm
  have hN' : N⁻¹∈C v := mem_C.mpr (show Commute (TunnellHurwitz.pure v) N from his _).inv_right₀
  let K := image hv (conjugate (ideal s))*line N⁻¹
  have hline : line N⁻¹ ≤ C v := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hN')
  have hK : K≤C v := (mul_le_mul' (center_image hv _) hline).trans (mul_C v)
  refine ⟨fun q hq => by obtain ⟨x,_,rfl⟩ := (mem_image _).mp hq; exact embed_integral _ _ _ _,center_image hv _,?_,K,hK,?_⟩
  · rw [←image_order hn h2 hv,←image_mul,Ideal.mul_top]
  · change image hv (ideal s)*(image hv (conjugate (ideal s))*line N⁻¹)=_
    rw [←mul_assoc,←image_mul,times_conj hn h2,image_principal hn h2 hv,map_natCast]
    change line N * J v v * line N⁻¹ = _
    rw [mul_assoc,ideals_comm hn hv (show J v v ≤ C v from fun _ h => mem_C.mpr h.2) hline,
      ←mul_assoc,line_mul,mul_inv_cancel₀ hN,line_one,one_mul]

def preimage {n : ℕ} {v : Triple} (hv : v∈shell n) (A : IntegralIdeal v) : Ideal (R n) where
  carrier := {x | embed n v hv x∈A.val}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; change embed n v hv (x+y)∈A.val; rw [map_add]; exact A.val.add_mem hx hy
  smul_mem' := by
    intro x y hy
    have hx : embed n v hv x∈J v v := ⟨embed_integral _ _ _ _,by rw [←embed_root n v hv,←map_mul,←map_mul,mul_comm]⟩
    change embed n v hv (x*y)∈A.val
    rw [mul_comm,map_mul,←A.property.2.2.1]
    exact Submodule.mul_mem_mul hy hx

lemma image_preimage {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) (A : IntegralIdeal v) :
    image hv (preimage hv A)=A.val := by
  ext q; constructor
  · rintro ⟨a,ha,rfl⟩; exact ha
  · intro hq
    obtain ⟨z,he⟩ := integral_centralizer hn h2 hv (A.property.1 hq) (mem_C.mp (A.property.2.1 hq)).symm
    refine (mem_image _).mpr ⟨z,?_,he.symm⟩
    change embed n v hv z∈A.val; rwa [←he]

lemma preimage_ne_bot {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) (A : IntegralIdeal v) :
    preimage hv A≠⊥ := by
  intro h
  have he := image_preimage hn h2 hv A
  rw [h] at he
  have hbot : image hv ⊥=⊥ := by apply le_antisymm _ bot_le; rintro _ ⟨x,hx,rfl⟩; rw [show x=0 from hx,map_zero]; exact Submodule.zero_mem _
  obtain ⟨B,_,hB⟩ := A.property.2.2.2
  rw [←he,hbot,Submodule.bot_mul] at hB
  have h₁ := one_J v; rw [←hB] at h₁
  exact one_ne_zero h₁

noncomputable def integralEquiv {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) :
    {I : Ideal (R n) // I≠⊥} ≃ IntegralIdeal v where
  toFun I := ⟨image hv I.val,image_isIdeal hn h2 hv I.val I.property⟩
  invFun A := ⟨preimage hv A,preimage_ne_bot hn h2 hv A⟩
  left_inv I := Subtype.ext (image_injective hn hv (image_preimage hn h2 hv _))
  right_inv A := Subtype.ext (image_preimage hn h2 hv A)

end TunnellEmbeddedIdeals
end

section
/- Multiplicative norm on the integral ideals of a squarefree imaginary quadratic order. -/
namespace TunnellIdealHNF
noncomputable def normI {n : ℕ} (I : Ideal (R n)) := Nat.card (R n ⧸ I)
def principal {n : ℕ} (x : R n) := Ideal.span {x}

lemma normI_positive {n : ℕ} (hn : 0<n) (I : Ideal (R n)) (hI : I≠⊥) : 0<normI I := by
  obtain ⟨s,rfl⟩ := normal_form hn hI
  rw [normI,quotient_card]; exact mul_pos (pow_pos s.pos_c _) s.pos_a
lemma int_pos_mem {n : ℕ} (hn : 0<n) (I : Ideal (R n)) (hI : I≠⊥) : ∃ A : ℕ, 0<A ∧ (A:R n)∈I := by
  obtain ⟨s,rfl⟩ := normal_form hn hI
  exact ⟨s.c*s.a,mul_pos s.pos_c s.pos_a,by
    have he : ((s.c*s.a:ℕ):R n)=⟨(s.c:ℤ)*s.a,0⟩ := by
      change (⟨((s.c*s.a:ℕ):ℤ),0⟩ : R n)=_; rw [Nat.cast_mul]
    rw [he]; exact real_basis s⟩

lemma mul_ne_bot {n : ℕ} (hn : 0<n) {I J : Ideal (R n)} (hI : I≠⊥) (hJ : J≠⊥) : I*J≠⊥ := by
  obtain ⟨a,ha,hi⟩ := int_pos_mem hn I hI; obtain ⟨b,hb,hj⟩ := int_pos_mem hn J hJ
  intro h; have hh := Ideal.mul_mem_mul hi hj; rw [h,←Nat.cast_mul] at hh
  exact Nat.cast_ne_zero.mpr (mul_ne_zero ha.ne' hb.ne') (show ((a*b:ℕ):R n)=0 from hh)

lemma conj_mem {n : ℕ} (I : Ideal (R n)) {x : R n} (h : x∈I) : star x∈conjugate I := by simpa [mem_conjugate] using h

lemma conjugate_mul {n : ℕ} (I J : Ideal (R n)) : conjugate (I*J)=conjugate I*conjugate J := by
  apply le_antisymm
  · intro x hx
    change star x∈I*J at hx
    have h (y : R n) (hy : y∈I*J) : star y∈conjugate I*conjugate J := by
      apply Submodule.mul_induction_on (C := fun y => star y∈conjugate I*conjugate J) hy
      · intro a ha b hb; rw [star_mul']; exact Ideal.mul_mem_mul (conj_mem _ ha) (conj_mem _ hb)
      · intro a b ha hb; rw [star_add]; exact add_mem ha hb
    simpa using h (star x) hx
  · apply Ideal.mul_le.mpr
    intro a ha b hb; change star (a*b)∈I*J
    rw [star_mul']; exact Ideal.mul_mem_mul ha hb

lemma norm_conjugate {n : ℕ} (hn : Squarefree n) (h₂ : n%4=2) (I : Ideal (R n)) (hI : I≠⊥) :
    I*conjugate I=principal (normI I:R n) := by
  obtain ⟨s,rfl⟩ := normal_form (show 0<n by omega) hI
  rw [normI,quotient_card]; exact times_conj hn h₂ s

lemma principal_injective_nat {n a b : ℕ} (h : principal (a:R n)=principal b) : a=b := by
  have mono {x y : ℕ} (h : principal (x:R n) ≤ principal y) : y∣x := by
    obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp (h (Ideal.mem_span_singleton_self _))
    have he := congrArg Zsqrtd.re hz
    change (x:ℤ)=y*z.re+ -(n:ℤ)*0*z.im at he
    exact Int.natCast_dvd_natCast.mp ⟨z.re,by simpa using he⟩
  exact Nat.dvd_antisymm (mono h.ge) (mono h.le)

lemma principal_mul {n : ℕ} (x y : R n) : principal (x*y)=principal x*principal y := (Ideal.span_singleton_mul_span_singleton x y).symm

lemma normI_mul {n : ℕ} (hn : Squarefree n) (h₂ : n%4=2) {I J : Ideal (R n)} (hI : I≠⊥) (hJ : J≠⊥) :
    normI (I*J)=normI I*normI J := by
  apply principal_injective_nat (n:=n)
  rw [←norm_conjugate hn h₂ _ (mul_ne_bot (by omega) hI hJ),Nat.cast_mul,principal_mul,←norm_conjugate hn h₂ _ hI,
    ←norm_conjugate hn h₂ _ hJ,conjugate_mul]; ac_rfl

lemma principal_star {n : ℕ} (x : R n) : conjugate (principal x)=principal (star x) := by
  ext y
  change star y∈Ideal.span {x} ↔ _
  change star y∈Ideal.span {x} ↔ y∈Ideal.span {star x}
  rw [Ideal.mem_span_singleton,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z,he⟩; exact ⟨star z,by rw [←star_mul',←he,star_star]⟩
  · rintro ⟨z,rfl⟩; exact ⟨star z,by rw [star_mul',star_star]⟩

lemma positive_norm {n : ℕ} (hn : 0<n) {z : R n} (hz : z≠0) : 0<z.norm := by
  change 0<z.re*z.re- -(n:ℤ)*z.im*z.im
  by_cases h : z.im=0
  · have he : z.re≠0 := fun he => hz (Zsqrtd.ext he h)
    rw [h]; simpa using mul_self_pos.mpr he
  · nlinarith [mul_self_nonneg z.re,mul_pos (show 0<(n:ℤ) by exact_mod_cast hn) (mul_self_pos.mpr h)]

lemma normI_principal {n : ℕ} (hn : Squarefree n) (h₂ : n%4=2) {x : R n} (hx : x≠0) :
    normI (principal x)=x.norm.toNat := by
  have hI : principal x≠⊥ := fun h => hx (by have H : x∈principal x := Ideal.mem_span_singleton_self x; rwa [h] at H)
  apply principal_injective_nat (n:=n)
  rw [←norm_conjugate hn h₂ _ hI,principal_star,←principal_mul,←Zsqrtd.norm_eq_mul_conj]
  congr 1
  rw [←Int.cast_natCast (R:=R n),Int.toNat_of_nonneg (positive_norm (by omega) hx).le]

end TunnellIdealHNF
end

section
/- The Dirichlet coefficients enumerating integral quadratic ideals by norm. -/
namespace TunnellIdealHNF
open Finset
def roots (n a : ℕ) : Finset ℕ := (range a).filter (fun b => (a:ℤ)∣(b:ℤ)^2+n)
noncomputable def divisors (m : ℕ) : Finset ℕ := m.divisors.filter (fun a => IsSquare (m/a))
abbrev indexed (n m : ℕ) := {s : Data n // s.c^2*s.a=m}
abbrev finiteRoot (n m : ℕ) := ↥((divisors m).sigma (roots n))

lemma quotient_by_a {n m : ℕ} (s : indexed n m) : m/s.val.a=s.val.c^2 := by
  exact (congrArg (·/s.val.a) s.property.symm).trans (Nat.mul_div_cancel _ s.val.pos_a)

noncomputable def divisorEquiv {n m : ℕ} (hm : 0 < m) : indexed n m ≃ finiteRoot n m := by
  classical
  let f : indexed n m → finiteRoot n m := fun s => ⟨⟨s.val.a,s.val.b⟩,mem_sigma.mpr ⟨mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨⟨s.val.c^2,s.property.symm.trans (mul_comm _ _)⟩,hm.ne'⟩,
      ⟨s.val.c,by rw [quotient_by_a s,pow_two]⟩⟩,mem_filter.mpr ⟨mem_range.mpr s.val.lt_b,s.val.divides⟩⟩⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro s t h
    have ha : s.val.a=t.val.a := congrArg (fun x : finiteRoot n m => x.val.fst) h
    have hb : s.val.b=t.val.b := congrArg (fun x : finiteRoot n m => x.val.snd) h
    have hc : s.val.c^2=t.val.c^2 := by rw [←quotient_by_a s,←quotient_by_a t,ha]
    have hc' : s.val.c=t.val.c := by nlinarith
    apply Subtype.ext
    cases s with | mk S _ =>
      cases t with | mk T _ =>
        cases S; cases T; dsimp only at ha hb hc'; congr
  · rintro ⟨⟨a,b⟩,h⟩
    obtain ⟨ha,hb⟩ := mem_sigma.mp h
    obtain ⟨hdiv,c,hc⟩ := mem_filter.mp ha
    have ha0 : 0<a := Nat.pos_of_mem_divisors hdiv
    have hd : a∣m := Nat.dvd_of_mem_divisors hdiv
    have he : c^2*a=m := by rw [pow_two,←hc,Nat.div_mul_cancel hd]
    have hc0 : 0<c := by by_contra! h; have := Nat.eq_zero_of_le_zero h; simp [this] at he; omega
    obtain ⟨hb',hbn⟩ := mem_filter.mp hb
    exact ⟨⟨⟨c,a,b,hc0,ha0,mem_range.mp hb',hbn⟩,he⟩,rfl⟩

abbrev NormIdeals (n m : ℕ) := {I : Ideal (R n) // I≠⊥ ∧ Nat.card (R n ⧸ I)=m}

noncomputable def indexedEquiv {n m : ℕ} (hn : 0<n) : indexed n m ≃ NormIdeals n m := by
  let f : indexed n m → NormIdeals n m := fun s => ⟨ideal s.val,ideal_ne_bot _,(quotient_card _).trans s.property⟩
  refine Equiv.ofBijective f ⟨fun _ _ h => Subtype.ext (ideal_injective (congrArg Subtype.val h)),?_⟩
  rintro ⟨I,hI,hm⟩
  obtain ⟨s,rfl⟩ := normal_form hn hI
  exact ⟨⟨s,(quotient_card _).symm.trans hm⟩,rfl⟩

theorem ideal_count {n m : ℕ} (hn : 0<n) (hm : 0 < m) :
    Nat.card (NormIdeals n m)=∑ a∈divisors m,(roots n a).card := by
  classical
  have e : NormIdeals n m ≃ finiteRoot n m := (indexedEquiv hn).symm.trans (divisorEquiv hm)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,card_sigma]

/- Reduction modulo a identifies the integral HNF roots with field-theoretic square roots. -/
theorem roots_zmod (n a : ℕ) (ha : 0<a) : letI : NeZero a := ⟨ha.ne'⟩
    (roots n a).card=((univ : Finset (ZMod a)).filter (fun x => x^2= -(n:ZMod a))).card := by
  letI : NeZero a := ⟨ha.ne'⟩
  apply card_nbij' (fun b:ℕ => (b:ZMod a)) (fun x:ZMod a => x.val)
  · intro b hb; obtain ⟨_,h⟩ := mem_filter.mp hb
    apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
    have e := (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).mpr h
    push_cast at e; exact eq_neg_of_add_eq_zero_left e
  · intro z hz; refine mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt z),?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).mp
    push_cast; rw [ZMod.natCast_zmod_val,(mem_filter.mp hz).2,neg_add_cancel]
  · intro b hb; change (b:ZMod a).val=b; rw [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hb).1)]
  · intro x _; exact ZMod.natCast_zmod_val _

end TunnellIdealHNF
end

section
/- Counts of primitive quadratic congruence roots and their behavior at prime powers. -/

namespace TunnellRankin
open Finset

private abbrev rootSet (d a : ℕ) := {x : ZMod a // x^2 = -((2*d:ℕ) : ZMod a)}

noncomputable def rho (d a : ℕ) : ℕ := if a = 0 then 0 else Nat.card (rootSet d a)

lemma rho_eq_card (d a : ℕ) [NeZero a] : rho d a =
    Fintype.card {x : ZMod a // x^2 = -((2*d:ℕ) : ZMod a)} := by
  simp only [rho,if_neg (NeZero.ne a),Nat.card_eq_fintype_card]

lemma rho_zero (d : ℕ) : rho d 0 = 0 := by simp [rho]

lemma rho_one (d : ℕ) : rho d 1 = 1 := by
  rw [rho_eq_card]
  have : Unique (rootSet d 1) := ⟨⟨⟨0,Subsingleton.elim _ _⟩⟩,fun _ => Subsingleton.elim _ _⟩
  exact Fintype.card_unique

lemma rho_mul (d : ℕ) {a b : ℕ} (h : a.Coprime b) :
    rho d (a*b) = rho d a * rho d b := by
  classical
  rcases eq_or_ne a 0 with rfl|ha
  · simp [rho_zero]
  rcases eq_or_ne b 0 with rfl|hb
  · simp [rho_zero]
  let : NeZero a := ⟨ha⟩
  let : NeZero b := ⟨hb⟩
  let e := ZMod.chineseRemainder h
  have he (x : ZMod (a*b)) : x^2 = -((2*d:ℕ):ZMod (a*b)) ↔
      (e x).1^2 = -((2*d:ℕ):ZMod a) ∧ (e x).2^2 = -((2*d:ℕ):ZMod b) := by
    rw [← e.injective.eq_iff, map_pow,map_neg,map_natCast,Prod.ext_iff]
    rfl
  let E : rootSet d (a*b) ≃ rootSet d a × rootSet d b := {
    toFun := fun x => (⟨(e x.val).1,((he _).mp x.property).1⟩,⟨(e x.val).2,((he _).mp x.property).2⟩)
    invFun := fun x => ⟨e.symm (x.1.val,x.2.val),(he _).mpr (by simp [x.1.property,x.2.property])⟩
    left_inv := fun _ => Subtype.ext (by simp)
    right_inv := fun _ => Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp)) }
  simp only [rho_eq_card,← Fintype.card_prod]
  exact Fintype.card_congr E

private theorem roots_lift {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → x^2 = 0)
    (n : R) (hn : IsUnit n) (h₂ : IsUnit (2:R)) :
    Function.Bijective (fun x : {x:R // x^2=n} => (⟨f x,by rw [← map_pow,x.property]⟩ : {x:S // x^2=f n})) := by
  have liftUnit (x : R) (h : IsUnit (f x)) : IsUnit x := by
    obtain ⟨s,hs⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨t,rfl⟩ := hf s
    have he := hk (1-x*t) (by simp [hs])
    exact isUnit_iff_exists_inv.mpr ⟨t*(2-x*t),by linear_combination -he⟩
  have rootUnit (x : {x:S // x^2=f n}) : IsUnit x.val :=
    (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (x.property ▸ hn.map f)
  constructor
  · intro x y hxy
    have h : f x.val = f y.val := congrArg Subtype.val hxy
    have hu : IsUnit (x.val+y.val) := liftUnit _ (by
      rw [map_add,←h,←two_mul]
      exact (by simpa only [map_ofNat] using h₂.map f : IsUnit (2:S)).mul
        (rootUnit ⟨f x.val,by rw [←map_pow,x.property]⟩))
    obtain ⟨t,ht⟩ := isUnit_iff_exists_inv.mp hu
    apply Subtype.ext
    linear_combination t*(x.property - y.property) - (x.val-y.val)*ht
  · intro x
    obtain ⟨y,hy⟩ := hf x.val
    have hu : IsUnit (2*y) := h₂.mul (liftUnit _ (hy ▸ rootUnit x))
    obtain ⟨t,ht⟩ := isUnit_iff_exists_inv.mp hu
    have hε : f (y^2-n) = 0 := by simp [hy,x.property]
    have hε₂ := hk _ hε
    refine ⟨⟨y-(y^2-n)*t,?_⟩,Subtype.ext ?_⟩
    · linear_combination t^2*hε₂ - (y^2-n)*ht
    · simpa [hε] using (show f (y-(y^2-n)*t) = x.val by rw [map_sub,map_mul,hε,zero_mul,sub_zero,hy])

lemma rho_good_lift {d p k : ℕ} (hp : p.Prime) (hn : ¬ p ∣ 2*d) (hk : 0 < k) :
    rho d (p^(k+1)) = rho d (p^k) := by
  let : Fact p.Prime := ⟨hp⟩
  let f := ZMod.castHom (pow_dvd_pow p (show k ≤ k+1 by omega)) (ZMod (p^k))
  have ker (x : ZMod (p^(k+1))) (hx : f x = 0) : x^2=0 := by
    rw [←ZMod.natCast_zmod_val x,map_natCast,ZMod.natCast_eq_zero_iff] at hx
    rw [←ZMod.natCast_zmod_val x,←Nat.cast_pow,ZMod.natCast_eq_zero_iff]
    exact dvd_trans (pow_dvd_pow p (show k+1 ≤ k*2 by omega))
      (by simpa [pow_mul] using pow_dvd_pow_of_dvd hx 2)
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow (a:=2*d) hp (by omega : 0<k+1)).mpr hn
  have h₂ := (ZMod.isUnit_natCast_iff_not_dvd_pow (a:=2) hp (by omega : 0<k+1)).mpr
    (fun h => hn (dvd_mul_of_dvd_left h d))
  have h := roots_lift f (ZMod.ringHom_surjective f) ker _ hu.neg (by simpa using h₂)
  have e := Equiv.ofBijective _ h
  simpa only [rho_eq_card,map_neg,map_natCast] using Fintype.card_congr e

lemma rho_good_pow {d p : ℕ} (hp : p.Prime) (hn : ¬p ∣ 2*d) (k : ℕ) :
    rho d (p^(k+1)) = rho d p := by
  induction k with
  | zero => simp
  | succ k ih => exact (rho_good_lift hp hn (Nat.succ_pos _)).trans ih

lemma rho_ramified_prime {d p : ℕ} (hp : p.Prime) (h : p ∣ 2*d) : rho d p = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [rho_eq_card]
  have hn := (ZMod.natCast_eq_zero_iff _ _).mpr h
  have : Unique (rootSet d p) := {
    default := ⟨0,by simp [hn]⟩
    uniq := fun x => Subtype.ext (by
      have hzero : x.val^2 = 0 := by simpa [hn] using x.property
      exact (pow_eq_zero_iff (by decide : 2≠0)).mp hzero) }
  exact Fintype.card_unique

lemma rho_ramified_pow {d p : ℕ} (hp : p.Prime) (hn : p ∣ 2*d)
    (hs : Squarefree (2*d)) (k : ℕ) : rho d (p^(k+2)) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [rho_eq_card,Fintype.card_eq_zero_iff]
  refine ⟨fun x => ?_⟩
  have hx : p^(k+2) ∣ x.val.val^2+2*d := (ZMod.natCast_eq_zero_iff _ _).mp (by
    push_cast
    simpa only [ZMod.natCast_zmod_val,Nat.cast_mul,Nat.cast_ofNat] using (add_eq_zero_iff_eq_neg.mpr x.property))
  have h2 : p^2 ∣ x.val.val^2+2*d := dvd_trans (pow_dvd_pow p (by omega : 2≤k+2)) hx
  have h1 : p ∣ x.val.val^2 := (Nat.dvd_add_iff_left hn).mpr
    ((dvd_pow_self p (by decide : 2≠0)).trans h2)
  have hx2 := pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow h1) 2
  exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp) (by
    simpa [sq] using (Nat.dvd_add_iff_right hx2).mpr h2)

lemma rho_prime (d p : ℕ) (hp : p.Prime) :
    (rho d p : ℤ) = 1+negWeight d p := by
  let : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl|h₂
  · simp [rho_ramified_prime Nat.prime_two (dvd_mul_right 2 d),negWeight]
  have ho := hp.odd_of_ne_two h₂
  rw [negWeight,if_pos ho,←jacobiSym.legendreSym.to_jacobiSym,add_comm,rho_eq_card]
  simpa [Fintype.card_subtype] using legendreSym.card_sqrts p h₂ (-((2*d:ℕ):ℤ))

end TunnellRankin
end

section
/- The quadratic ideal Dirichlet coefficient as a finite sum of quadratic congruence counts. -/

namespace TunnellRankin
open Finset

private def squareIndicator : ArithmeticFunction ℤ :=
  ⟨fun m => if m ≠ 0 ∧ IsSquare m then 1 else 0,by simp⟩

private lemma coprime_square_iff {a b : ℕ} (hc : a.Coprime b) :
    IsSquare (a*b) ↔ IsSquare a ∧ IsSquare b := by
  have left {x y : ℕ} (hh : x.Coprime y) (hs : IsSquare (x*y)) : IsSquare x := by
    obtain ⟨r,hr⟩ := hs
    obtain ⟨t,ht⟩ := exists_eq_pow_of_mul_eq_pow
      (by change IsUnit (x.gcd y); rw [hh.gcd_eq_one]; simp : IsUnit (gcd x y))
      (by simpa [sq] using hr : x*y=r^2)
    exact ⟨t,by simpa [sq] using ht⟩
  exact ⟨fun h => ⟨left hc h,left hc.symm (mul_comm a b ▸ h)⟩,fun h => h.1.mul h.2⟩

private lemma squareIndicator_mult : squareIndicator.IsMultiplicative := by
  refine ⟨by simp [squareIndicator],?_⟩
  intro a b h
  simp only [squareIndicator,ArithmeticFunction.coe_mk,mul_ne_zero_iff,coprime_square_iff h]
  split_ifs <;> simp_all

private noncomputable def rootFun (d : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun m => (rho d m:ℤ),by simp [rho_zero]⟩

private lemma rootFun_mult (d : ℕ) : (rootFun d).IsMultiplicative :=
  ⟨by simp [rootFun,rho_one],fun h => by simp [rootFun,rho_mul _ h]⟩

private lemma square_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    IsSquare (p^j) ↔ Even j := by
  constructor
  · rintro ⟨b,hb⟩
    rw [←sq] at hb
    have hv := congrArg (fun n : ℕ => n.factorization p) hb
    change (p^j).factorization p = (b^2).factorization p at hv
    rw [Nat.factorization_pow_self hp,Nat.factorization_pow] at hv
    simp only [Finsupp.smul_apply,smul_eq_mul] at hv
    exact ⟨b.factorization p,by omega⟩
  · rintro ⟨k,rfl⟩
    exact ⟨p^k,pow_add p k k⟩

private noncomputable def localRoots (d p k : ℕ) : ℤ :=
  ∑ j ∈ range (k+1),if Even j then (rho d (p^(k-j)):ℤ) else 0

private lemma convolution_pow (d p k : ℕ) (hp : p.Prime) :
    (rootFun d*squareIndicator) (p^k)=localRoots d p k := by
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal' (fun x y => rootFun d x*squareIndicator y),
    Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro j hj
  have hjk : j≤k := by simpa using hj
  simp [squareIndicator,rootFun, Nat.pow_div hjk hp.pos,hp.ne_zero,square_prime_pow hp,
    mul_ite]

private lemma localRoots_step (d p k : ℕ) :
    localRoots d p (k+2) = (rho d (p^(k+2)):ℤ) + localRoots d p k := by
  unfold localRoots
  rw [sum_range_succ',sum_range_succ']
  simp only [Even.zero,if_true,Nat.sub_zero,zero_add,Nat.not_even_one,if_false,add_zero]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j hj
  simp [Nat.even_add]

private lemma negWeight_zero_iff (d p : ℕ) (hp : p.Prime) :
    negWeight d p=0 ↔ p ∣ 2*d := by
  rcases eq_or_ne p 2 with rfl|h₂
  · simp [negWeight]
  let : Fact p.Prime := ⟨hp⟩
  rw [negWeight,if_pos (hp.odd_of_ne_two h₂),←jacobiSym.legendreSym.to_jacobiSym,legendreSym.eq_zero_iff]
  simp only [Int.cast_neg,Int.cast_natCast,neg_eq_zero,ZMod.natCast_eq_zero_iff]

private lemma localRoots_eq (d p k : ℕ) (hp : p.Prime) (hs : Squarefree (2*d)) :
    localRoots d p k = ∑ j ∈ range (k+1),(negWeight d p)^j := by
  induction k using Nat.twoStepInduction with
  | zero =>
    change (∑ j ∈ range 1, if Even j then (rho d (p^(0-j)):ℤ) else 0)=_
    rw [sum_range_one,sum_range_one]
    simp [rho_one]
  | one => simp [localRoots,sum_range_succ,rho_prime d p hp,add_comm]
  | more k ih _ =>
    rw [localRoots_step,ih,sum_range_succ (n:=k+2),sum_range_succ (n:=k+1)]
    suffices h : (rho d (p^(k+2)):ℤ) = (negWeight d p)^(k+1) * (1+negWeight d p) by
      rw [h,pow_succ (negWeight d p) (k+1)]
      ring
    by_cases hz : p∣2*d
    · simp [rho_ramified_pow hp hz hs,(negWeight_zero_iff d p hp).mpr hz]
    have hne := mt (negWeight_zero_iff d p hp).mp hz
    have ht : negWeight d p=0 ∨ negWeight d p=1 ∨ negWeight d p= -1 := by
      unfold negWeight
      split
      · exact jacobiSym.trichotomy _ _
      · simp
    rw [rho_good_pow hp hz (k+1),rho_prime d p hp]
    rcases ht with h|h|h <;> simp_all

theorem idealCoeff_eq_roots (d m : ℕ) (hs : Squarefree (2*d)) :
    idealCoeff d m = ∑ a ∈ m.divisors, if IsSquare (m/a) then (rho d a:ℤ) else 0 := by
  let F : ArithmeticFunction ℤ := ⟨idealCoeff d,by simp [idealCoeff]⟩
  have hF : F.IsMultiplicative := ⟨idealCoeff_one d,idealCoeff_mul d⟩
  have he : F=rootFun d*squareIndicator := (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    F hF _ ((rootFun_mult d).mul squareIndicator_mult)).mpr (fun p k hp => by
      change idealCoeff d (p^k)=_
      rw [idealCoeff_prime_pow d p k hp,convolution_pow d p k hp,localRoots_eq d p k hp hs])
  change F m=_
  rw [he,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun x y => rootFun d x*squareIndicator y)]
  apply sum_congr rfl
  intro a ha
  obtain ⟨hdiv,hm⟩ := Nat.mem_divisors.mp ha
  have hq : 0 < m / a := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdiv)
    (Nat.pos_of_dvd_of_pos hdiv (Nat.pos_of_ne_zero hm))
  simp [rootFun,squareIndicator,hq.ne',mul_ite]

end TunnellRankin
end

section
/- The actual integral ideals enumerated by the quadratic Rankin coefficient. -/
namespace TunnellIdealHNF
open Finset TunnellRankin

theorem rankin_ideal_count (d m : ℕ) (hs : Squarefree (2*d)) (hm : 0 < m) :
    idealCoeff d m=(Nat.card (NormIdeals (2*d) m):ℤ) := by
  have hn : 0<2*d := Nat.pos_of_ne_zero hs.ne_zero
  rw [idealCoeff_eq_roots _ _ hs,ideal_count hn hm,divisors,sum_filter]
  push_cast
  apply sum_congr rfl
  intro a ha
  have hap := Nat.pos_of_mem_divisors ha
  letI : NeZero a := ⟨hap.ne'⟩
  have h : (roots (2*d) a).card=rho d a := by
    rw [roots_zmod _ _ hap,rho_eq_card,Fintype.card_subtype]
  split <;> simp_all

end TunnellIdealHNF
end

section
/- Norm representations in an ideal and integral ideals in its inverse class. -/
namespace TunnellIdealGenerators
open TunnellIdealHNF TunnellShell TunnellHurwitz TunnellToricClass TunnellEmbeddedIdeals
noncomputable section

lemma domain {n : ℕ} (hn : 0<n) : IsDomain (R n) := by
  letI : NoZeroDivisors (R n) := ⟨by
    intro x y h
    by_contra! hxy
    have hN := congrArg Zsqrtd.norm h
    rw [Zsqrtd.norm_mul,Zsqrtd.norm_zero] at hN
    exact (mul_pos (positive_norm hn hxy.1) (positive_norm hn hxy.2)).ne' hN⟩
  exact NoZeroDivisors.to_isDomain _

lemma unit_sign {n : ℕ} (hn : 2≤n) (u : (R n)ˣ) : (u:R n)=1 ∨ (u:R n)= -1 := by
  have h := (Zsqrtd.norm_eq_one_iff' (d:= -(n:ℤ)) (by omega) u.val).mpr u.isUnit
  change u.val.re*u.val.re- -(n:ℤ)*u.val.im*u.val.im=1 at h
  have h0 : u.val.im=0 := by
    by_contra hn0
    have hi : 1≤u.val.im*u.val.im := mul_self_pos.mpr hn0
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0≤(n:ℤ) by omega),mul_self_nonneg u.val.re]
  rw [h0] at h
  have he : (u.val.re-1)*(u.val.re+1)=0 := by nlinarith
  rcases mul_eq_zero.mp he with h|h
  · exact Or.inl (Zsqrtd.ext (by change u.val.re=1; omega) h0)
  · exact Or.inr (Zsqrtd.ext (by change u.val.re= -1; omega) (by simpa using h0))

lemma generator_sign {n : ℕ} (hn : 2≤n) {x y : R n} (h : principal x=principal y) :
    y=x ∨ y= -x := by
  letI := domain (show 0<n by omega)
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  rcases unit_sign hn u with h|h <;> simp [h] at hu <;> exact (by tauto)

def divide {n : ℕ} (I : Ideal (R n)) (x : R n) : Ideal (R n) :=
  (principal x*conjugate I).colon {(normI I:R n)}

lemma mul_right_cancel_ideal {n : ℕ} (hn : Squarefree n) (h2 : n%4=2)
    {I A B : Ideal (R n)} (hI : I≠⊥) (h : A*I=B*I) : A=B := by
  letI := domain (show 0<n by omega)
  apply (Ideal.span_singleton_mul_left_inj (Nat.cast_ne_zero.mpr (normI_positive (by omega) I hI).ne')).mp
  change A*principal (normI I:R n)=B*principal (normI I:R n)
  rw [←norm_conjugate hn h2 I hI,←mul_assoc,←mul_assoc,h]

lemma divide_mul {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {I : Ideal (R n)} (hI : I≠⊥) {x : R n} (hx : x∈I) :
    divide I x*I=principal x := by
  letI := domain (show 0<n by omega)
  let P := principal x*conjugate I
  let N : R n := normI I
  have hp0 : principal x≤I := by rw [principal,Ideal.span_singleton_le_iff_mem]; exact hx
  have hp : P≤principal N := (mul_le_mul_left hp0 _).trans_eq (norm_conjugate hn h2 I hI)
  have hP : divide I x*principal N = P := by
    ext t
    rw [principal,Ideal.mem_mul_span_singleton]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact Submodule.mem_colon_singleton.mp hy
    · intro ht
      obtain ⟨y,hy⟩ := Ideal.mem_span_singleton.mp (hp ht)
      exact ⟨y,Submodule.mem_colon_singleton.mpr (show y*N∈P by rwa [mul_comm,←hy]),(mul_comm _ _).trans hy.symm⟩
  have hN : N≠0 := Nat.cast_ne_zero.mpr (normI_positive (by omega) I hI).ne'
  apply (Ideal.span_singleton_mul_left_inj hN).mp
  change divide I x*I*principal N=principal x*principal N
  calc
    _ = (divide I x*principal N)*I := by ac_rfl
    _ = principal x*(I*conjugate I) := by rw [hP]; dsimp [P]; ac_rfl
    _ = _ := by rw [norm_conjugate hn h2 I hI]

lemma image_principal_mul {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n)
    (x : R n) (I : Ideal (R n)) : image hv (principal x * I) = line (embed n v hv x)*image hv I := by
  rw [image_mul,principal,image_principal hn h2 hv, mul_assoc,←image_order hn h2 hv,←image_mul,Ideal.top_mul]

theorem inverse_class_iff {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n)
    {I B : Ideal (R n)} (hI : I≠⊥) :
    homothetic v (image hv (conjugate I)) (image hv B) ↔ ∃ x : R n, x≠0 ∧ B*I=principal x := by
  let N : Q := normI I
  have hN : N≠0 := by
    intro h
    have H := congrArg QuaternionAlgebra.re h
    change ((normI I:ℕ):ℚ)=0 at H
    exact (normI_positive (by omega) I hI).ne' (by exact_mod_cast H)
  have hNc : N∈C v := mem_C.mpr (Nat.cast_comm (normI I) _).symm
  constructor
  · rintro ⟨c,_,hc,e⟩
    have h : image hv (B*I)=line (c*N)*J v v := by
      rw [image_mul,←e,mul_assoc,←image_mul,mul_comm (conjugate I),norm_conjugate hn h2 I hI,principal,image_principal hn h2 hv,map_natCast,←mul_assoc,line_mul]
    have hm : c*N ∈ image hv (B*I) := by
      rw [h]; exact Submodule.mem_span_singleton_mul.mpr ⟨1,one_J v,mul_one _⟩
    obtain ⟨x,_,ex⟩ := (mem_image _).mp hm
    refine ⟨x,fun H => (mul_ne_zero hc hN) (by simpa [H] using ex.symm),image_injective hn hv ?_⟩
    rw [h,principal,image_principal hn h2 hv,ex]
  · rintro ⟨x,hx,e⟩
    let X := embed n v hv x
    have hX : X≠0 := fun h => hx (embed_inj hn hv (h.trans (map_zero _).symm))
    have hXc : X∈C v := center_image hv (principal x) ⟨x,Ideal.mem_span_singleton_self _,rfl⟩
    have he : line N*image hv B = line X*image hv (conjugate I) := by
      have H : principal (normI I:R n)*B = principal x*conjugate I := by
        rw [←norm_conjugate hn h2 I hI,←e]; ac_rfl
      have H' := congrArg (image hv) H
      rw [image_principal_mul hn h2 hv,image_principal_mul hn h2 hv,map_natCast] at H'
      exact H'
    refine ⟨N⁻¹*X,(mul_C v) (Submodule.mul_mem_mul (mem_C.mpr ((show Commute _ N from mem_C.mp hNc).inv_right₀)) hXc),
      mul_ne_zero (inv_ne_zero hN) hX,?_⟩
    rw [←line_mul,mul_assoc,←he,←mul_assoc,two_sided_inverse hN,one_mul]

end
end TunnellIdealGenerators
end

section
/- Each norm-m ideal in the inverse class contributes exactly two generators. -/
namespace TunnellIdealGenerators
open TunnellIdealHNF TunnellShell TunnellHurwitz TunnellToricClass TunnellEmbeddedIdeals
noncomputable section

abbrev Representations {n : ℕ} (I : Ideal (R n)) (m : ℕ) := {x : R n // x∈I ∧ x≠0 ∧ x.norm.toNat=m*normI I}
abbrev InverseClass {n : ℕ} {v : Triple} (hv : v∈shell n) (I : Ideal (R n)) (m : ℕ) :=
  {B : NormIdeals n m // homothetic v (image hv (conjugate I)) (image hv B.val)}

variable {n m : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n)
  {I : Ideal (R n)} (hI : I≠⊥)

def gen (b : InverseClass hv I m) : R n := ((inverse_class_iff hn h2 hv hI).mp b.property).choose
lemma gen_spec (b : InverseClass hv I m) :
    gen hn h2 hv hI b≠0 ∧ b.val.val*I=principal (gen hn h2 hv hI b) :=
  ((inverse_class_iff hn h2 hv hI).mp b.property).choose_spec

def mkRep (b : InverseClass hv I m) : Representations I m := ⟨gen hn h2 hv hI b,by
  obtain ⟨h₀,he⟩ := gen_spec hn h2 hv hI b
  refine ⟨Ideal.mul_le_right (I:=b.val.val) (J:=I) (he.symm ▸ Ideal.mem_span_singleton_self _),h₀,?_⟩
  rw [←normI_principal hn h2 h₀,←he,normI_mul hn h2 b.val.property.1 hI,show normI b.val.val=m from b.val.property.2]⟩

def repNeg (x : Representations I m) : Representations I m :=
  ⟨-x.val,I.neg_mem x.property.1,neg_ne_zero.mpr x.property.2.1,by simpa only [Zsqrtd.norm_neg] using x.property.2.2⟩

def pick (s : Bool) (b : InverseClass hv I m) : Representations I m :=
  if s then mkRep hn h2 hv hI b else repNeg (mkRep hn h2 hv hI b)

lemma pick_principal (s : Bool) (b : InverseClass hv I m) :
    principal (pick hn h2 hv hI s b).val=b.val.val*I := by
  have he := (gen_spec hn h2 hv hI b).2.symm
  cases s
  · exact (Ideal.span_singleton_neg _).trans he
  · exact he

def repIdeal (x : Representations I m) : InverseClass hv I m := by
  have he := divide_mul hn h2 hI x.property.1
  have hB : divide I x.val≠⊥ := by
    intro e; rw [e,Ideal.bot_mul] at he
    have h : x.val∈principal x.val := Ideal.mem_span_singleton_self _
    rw [←he] at h
    exact x.property.2.1 h
  have hnorm : normI (divide I x.val)*normI I=m*normI I := by
    rw [←normI_mul hn h2 hB hI,he,normI_principal hn h2 x.property.2.1,x.property.2.2]
  exact ⟨⟨divide I x.val,hB,Nat.mul_right_cancel (normI_positive (by omega) I hI) hnorm⟩,
    (inverse_class_iff hn h2 hv hI).mpr ⟨_,x.property.2.1,he⟩⟩

lemma neg_ne_self {x : R n} (hx : x≠0) : -x≠x := by
  intro e; apply hx; apply Zsqrtd.ext
  · have h := congrArg Zsqrtd.re e; change -x.re=x.re at h; change x.re=0; omega
  · have h := congrArg Zsqrtd.im e; change -x.im=x.im at h; change x.im=0; omega

def repEquiv : Bool × InverseClass hv I m ≃ Representations I m := by
  let f (t : Bool × InverseClass hv I m) := pick hn h2 hv hI t.1 t.2
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · rintro ⟨s,b⟩ ⟨s',b'⟩ h
    have he := congrArg (fun x : Representations I m => principal x.val) h
    change principal (pick hn h2 hv hI s b).val=principal (pick hn h2 hv hI s' b').val at he
    rw [pick_principal,pick_principal] at he
    have eb : b=b' := Subtype.ext (Subtype.ext (mul_right_cancel_ideal hn h2 hI he))
    subst b'
    have ex := congrArg Subtype.val h
    obtain hs | hs := Bool.dichotomy s
    all_goals obtain hs' | hs' := Bool.dichotomy s'
    all_goals subst s; subst s'
    · rfl
    · exact False.elim (neg_ne_self (gen_spec hn h2 hv hI b).1 ex)
    · exact False.elim (neg_ne_self (gen_spec hn h2 hv hI b).1 ex.symm)
    · rfl
  · intro x
    let b := repIdeal hn h2 hv hI x
    have he : principal (gen hn h2 hv hI b)=principal x.val :=
      (gen_spec hn h2 hv hI b).2.symm.trans (divide_mul hn h2 hI x.property.1)
    rcases generator_sign (by omega) he with h|h
    · exact ⟨(true,b),Subtype.ext h.symm⟩
    · exact ⟨(false,b),Subtype.ext h.symm⟩

include hn h2 hI in
theorem classwise_count : Nat.card (Representations I m)=2*Nat.card (InverseClass hv I m) := by
  rw [←Nat.card_congr (repEquiv hn h2 hv hI),Nat.card_prod]
  simp

end
end TunnellIdealGenerators
end

section
/- The full ideal theta coefficient counts every integral ideal twice. -/
namespace TunnellClassThetaCount
open TunnellHurwitz TunnellToricLocal TunnellToric TunnellIdealHNF TunnellShell TunnellToricClass TunnellEmbeddedIdeals TunnellIdealGenerators
noncomputable section
variable {n m : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n)

def liftClass (c : ProperIdealClass v) : Ideal (R n) := conjugate (preimage hv c.out)
def classOf (B : NormIdeals n m) : ProperIdealClass v :=
  Quotient.mk _ (integralEquiv hn h2 hv ⟨B.val,B.property.1⟩)

lemma conj_invol (I : Ideal (R n)) : conjugate (conjugate I)=I := by
  ext x; simp only [mem_conjugate,star_star]
lemma conj_ne_bot {I : Ideal (R n)} (hI : I≠⊥) : conjugate I≠⊥ := by
  intro h; apply hI; rw [←conj_invol I,h]; ext t; simp [mem_conjugate]
include hn h2 in
lemma lift_ne_bot (c : ProperIdealClass v) : liftClass hv c≠⊥ :=
  conj_ne_bot (preimage_ne_bot hn h2 hv c.out)

lemma fiber_iff (c : ProperIdealClass v) (B : NormIdeals n m) :
    homothetic v (image hv (conjugate (liftClass hv c))) (image hv B.val) ↔ classOf hn h2 hv B=c := by
  rw [liftClass,conj_invol,image_preimage hn h2 hv]
  calc
    _ ↔ Quotient.mk (idealSetoid v) c.out=classOf hn h2 hv B := Quotient.eq.symm
    _ ↔ _ := by rw [Quotient.out_eq,eq_comm]

def fiberEquiv (c : ProperIdealClass v) :
    InverseClass hv (liftClass hv c) m ≃ {B : NormIdeals n m // classOf hn h2 hv B=c} :=
  Equiv.subtypeEquivRight (fiber_iff hn h2 hv c)

theorem total_count (hm : 0 < m) :
    letI := Fintype.ofEquiv ↥(representatives n) (idealEquiv hn h2 hv).symm
    (∑ c : ProperIdealClass v, Nat.card (Representations (liftClass hv c) m))=2*Nat.card (NormIdeals n m) := by
  classical
  letI := Fintype.ofEquiv ↥(representatives n) (idealEquiv hn h2 hv).symm
  letI : Fintype (NormIdeals n m) := Fintype.ofEquiv (finiteRoot n m) ((divisorEquiv hm).symm.trans (indexedEquiv (by omega)))
  calc
    _=∑ c : ProperIdealClass v, 2*Nat.card {B : NormIdeals n m // classOf hn h2 hv B=c} := by
      apply Finset.sum_congr rfl
      intro c _
      rw [classwise_count hn h2 hv (lift_ne_bot hn h2 hv c),Nat.card_congr (fiberEquiv hn h2 hv c)]
    _=_ := by
      rw [←Finset.mul_sum,←Nat.card_sigma,Nat.card_congr (Equiv.sigmaFiberEquiv (classOf hn h2 hv : NormIdeals n m → _))]

end
end TunnellClassThetaCount
end

section
/- Fricke transformation of a binary quadratic ideal theta series, via the Jacobi theta function. -/

namespace TunnellIdealTheta
open Complex Finset Real
open scoped Classical
noncomputable section

def shift (u z : ℂ) : ℂ := Complex.exp (π*I*u^2*z)*jacobiTheta₂ (u*z) z

lemma shift_hasSum (u z : ℂ) (hz : 0 < z.im) :
    HasSum (fun k : ℤ => Complex.exp (π*I*((k:ℂ)+u)^2*z)) (shift u z) := by
  apply ((hasSum_jacobiTheta₂_term (u*z) hz).mul_left _).congr_fun
  intro k
  rw [jacobiTheta₂_term,←Complex.exp_add]
  congr 1
  ring

lemma shift_invert (u z : ℂ) (hz : z≠0) :
    shift u (-1/z) = (-I*z)^(1/2:ℂ)*jacobiTheta₂ u z := by
  rw [shift,jacobiTheta₂_functional_equation u z]
  rw [show u*(-1/z)= -(u/z) by ring,jacobiTheta₂_neg_left]
  rw [show (π:ℂ)*I*u^2*(-1/z)= -π*I*u^2/z by ring]
  have h : (-I*z)^(1/2:ℂ)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (by simp) hz))
  field_simp

lemma half_scale {r : ℝ} (hr : 0<r) {w : ℂ} (hw : w≠0) :
    ((r:ℂ)*w)^(1/2:ℂ) = (√r:ℂ)*w^(1/2:ℂ) := by
  have hc : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hc hw),Complex.log_ofReal_mul hr hw,add_mul,Complex.exp_add,
    ←Complex.cpow_def_of_ne_zero hw,Complex.ofReal_log hr.le,←Complex.cpow_def_of_ne_zero hc]
  congr 1
  rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow hr.le]
  norm_num

def theta (n a : ℕ) [NeZero a] (b : ℤ) (z : ℂ) : ℂ :=
  ∑ r : ZMod a, shift ((b:ℂ)*r.val/a) (2*a*z)*shift ((r.val:ℂ)/a) (2*n*a*z)

def term (n a : ℕ) (z : ℂ) (uv : ℤ×ℤ) : ℂ :=
  Complex.exp (2*π*I*z*((n:ℂ)*(uv.1:ℂ)^2+(uv.2:ℂ)^2)/a)

def admitted (a : ℕ) (b : ℤ) (uv : ℤ×ℤ) : Prop :=
  (uv.2:ZMod a)=(b:ZMod a)*(uv.1:ZMod a)

private lemma product_sum {f g : ℤ→ℂ} {A B : ℂ} (hf : HasSum f A) (hg : HasSum g B) :
    HasSum (fun v : ℤ×ℤ => f v.1*g v.2) (A*B) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

private lemma half_factors {z : ℂ} (hz : z≠0) (n a : ℕ) [NeZero n] [NeZero a] :
    (-I*(2*n*z/a))^(1/2:ℂ)*(-I*(2*z/a))^(1/2:ℂ)= 2*(√n:ℂ)*(-I*z)/a := by
  have ha : (0:ℝ)<a := Nat.cast_pos.mpr (NeZero.pos a)
  have hn : (0:ℝ)<n := Nat.cast_pos.mpr (NeZero.pos n)
  have he (r : ℝ) (hr : 0<r) : (-I*((r:ℂ)*z))^(1/2:ℂ) = (√r:ℂ)*(-I*z)^(1/2:ℂ) := by
    rw [show -I*((r:ℂ)*z)=(r:ℂ)*(-I*z) by ring,half_scale hr (mul_ne_zero (by simp) hz)]
  rw [show (2:ℂ)*n*z/a= ((2*(n:ℝ)/a:ℝ):ℂ)*z by push_cast; ring,
    show (2:ℂ)*z/a= ((2/(a:ℝ):ℝ):ℂ)*z by push_cast; ring,he _ (by positivity),he _ (by positivity)]
  have hpow : ((-I*z)^(1/2:ℂ))^2 = -I*z := by rw [←Complex.cpow_mul_ofNat]; norm_num
  have hroot : √(2*(n:ℝ)/a)*√(2/(a:ℝ))=2*√n/a := by
    rw [←Real.sqrt_mul (by positivity),show 2*(n:ℝ)/a*(2/a)=(2/a)^2*n by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
    ring
  calc
    _ = (((√(2*(n:ℝ)/a)*√(2/(a:ℝ)):ℝ):ℂ))*((-I*z)^(1/2:ℂ))^2 := by push_cast; ring
    _ = _ := by rw [hpow,hroot]; push_cast; ring

lemma theta_invert_packet (n a : ℕ) [NeZero n] [NeZero a] (b : ℤ) {z : ℂ} (hz : z≠0) :
    theta n a b (-1/(4*n*z)) = 2*(√n:ℂ)*(-I*z)/a *
      ∑ r : ZMod a, jacobiTheta₂ ((b:ℂ)*r.val/a) (2*n*z/a) *
        jacobiTheta₂ (-(r.val:ℂ)/a) (2*z/a) := by
  have ha : (a:ℂ)≠0 := by exact_mod_cast NeZero.ne a
  have hn : (n:ℂ)≠0 := by exact_mod_cast NeZero.ne n
  unfold theta
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  rw [show 2*(a:ℂ)*(-1/(4*n*z))= -1/(2*n*z/a) by field_simp; norm_num,
    show 2*(n:ℂ)*a*(-1/(4*n*z))= -1/(2*z/a) by field_simp; norm_num,
    shift_invert _ _ (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn) hz) ha),
    shift_invert _ _ (div_ne_zero (mul_ne_zero (by norm_num) hz) ha),
    neg_div,jacobiTheta₂_neg_left,←half_factors hz n a]
  ring

private lemma refine_residue {a : ℕ} [NeZero a] (r u : ℤ)
    (h : (u:ZMod a)=(r:ZMod a)) : ∃ k:ℤ, (a:ℤ)*k+r=u := by
  obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub r u a).mp h.symm
  exact ⟨k,by omega⟩

theorem theta_hasSum (n a : ℕ) [NeZero n] [NeZero a] (b : ℤ) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun uv : ℤ×ℤ => if admitted a b uv then term n a z uv else 0) (theta n a b z) := by
  classical
  have ha : (a:ℂ)≠0 := by exact_mod_cast NeZero.ne a
  have hap : (0:ℝ)<a := Nat.cast_pos.mpr (NeZero.pos a)
  have hnp : (0:ℝ)<n := Nat.cast_pos.mpr (NeZero.pos n)
  let cls (r : ZMod a) (uv : ℤ×ℤ) := if (uv.1:ZMod a)=r ∧ (uv.2:ZMod a)=(b:ZMod a)*r then term n a z uv else 0
  have hsum (r : ZMod a) : HasSum (cls r) (shift ((b:ℂ)*r.val/a) (2*a*z)*shift ((r.val:ℂ)/a) (2*n*a*z)) := by
    let e (v : ℤ×ℤ) : ℤ×ℤ := (a*v.2+r.val,a*v.1+b*r.val)
    have hi : Function.Injective e := by
      rintro ⟨x,y⟩ ⟨x',y'⟩ h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp only [e] at h1 h2
      have hac : (a:ℤ)≠0 := by exact_mod_cast NeZero.ne a
      exact Prod.ext (mul_left_cancel₀ hac (add_right_cancel h2)) (mul_left_cancel₀ hac (add_right_cancel h1))
    apply (hi.hasSum_iff ?_).mp
    · have H := product_sum (shift_hasSum ((b:ℂ)*r.val/a) (2*a*z)
          (by simpa [Complex.mul_im] using (show (0:ℝ)<2*a*z.im by positivity)))
        (shift_hasSum ((r.val:ℂ)/a) (2*n*a*z)
          (by simpa [Complex.mul_im] using (show (0:ℝ)<2*n*a*z.im by positivity)))
      apply H.congr_fun
      rintro ⟨x,y⟩
      simp only [Function.comp_apply,e,cls,Int.cast_add,Int.cast_mul,Int.cast_natCast,
        ZMod.natCast_self,zero_mul,zero_add,ZMod.natCast_zmod_val,and_self,ite_true]
      simp only [term,Int.cast_add,Int.cast_mul,Int.cast_natCast,←Complex.exp_add]
      congr 1
      field_simp
      ring
    · rintro ⟨u,v⟩ h
      unfold cls
      split_ifs with hc
      · exfalso; apply h
        obtain ⟨y,hy⟩ := refine_residue (a:=a) r.val u (by simpa using hc.1)
        obtain ⟨x,hx⟩ := refine_residue (a:=a) (b*r.val) v (by simpa using hc.2)
        exact ⟨(x,y),Prod.ext hy hx⟩
      · rfl
  apply (hasSum_sum (s:=univ) (fun r _ => hsum r)).congr_fun
  rintro ⟨u,v⟩
  dsimp only [cls,admitted]
  rw [sum_eq_single (u:ZMod a)]
  · by_cases h : (v:ZMod a)=(b:ZMod a)*(u:ZMod a) <;> simp [h]
  · intro s _ h; simp [Ne.symm h]
  · simp

private lemma dual_hsum (n a : ℕ) [NeZero n] [NeZero a] (b : ℤ) {z : ℂ} (hz : 0 < z.im)
    (r : ZMod a) :
    HasSum (fun uv : ℤ×ℤ => ZMod.stdAddChar (r*((b:ZMod a)*(uv.1:ZMod a)-(uv.2:ZMod a)))*term n a z uv)
      (jacobiTheta₂ ((b:ℂ)*r.val/a) (2*n*z/a) * jacobiTheta₂ (-(r.val:ℂ)/a) (2*z/a)) := by
  have hap : (0:ℝ)<a := Nat.cast_pos.mpr (NeZero.pos a)
  have hnp : (0:ℝ)<n := Nat.cast_pos.mpr (NeZero.pos n)
  have hA : 0 < (2*(n:ℂ)*z/a).im := by
    simp [div_eq_mul_inv,Complex.mul_im,Complex.mul_re]; positivity
  have hB : 0 < (2*z/a).im := by
    simp [div_eq_mul_inv,Complex.mul_im,Complex.mul_re]; positivity
  apply (product_sum (hasSum_jacobiTheta₂_term _ hA) (hasSum_jacobiTheta₂_term _ hB)).congr_fun
  rintro ⟨u,v⟩
  rw [show r*((b:ZMod a)*(u:ZMod a)-v)=(((r.val:ℤ)*(b*u-v):ℤ):ZMod a) by push_cast; simp,
    ZMod.stdAddChar_coe]
  simp only [jacobiTheta₂_term,term,←Complex.exp_add,Int.cast_mul,Int.cast_sub,Int.cast_natCast]
  congr 1
  ring

lemma dual_packet (n a : ℕ) [NeZero n] [NeZero a] (b : ℤ) {z : ℂ} (hz : 0 < z.im) :
    (∑ r : ZMod a, jacobiTheta₂ ((b:ℂ)*r.val/a) (2*n*z/a) * jacobiTheta₂ (-(r.val:ℂ)/a) (2*z/a)) =
      (a:ℂ)*theta n a b z := by
  classical
  apply (hasSum_sum (s:=univ) (fun r _ => dual_hsum n a b hz r)).unique
  apply ((theta_hasSum n a b hz).mul_left (a:ℂ)).congr_fun
  rintro ⟨u,v⟩
  rw [←sum_mul,AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar a),ZMod.card]
  unfold admitted
  simp only [sub_eq_zero,eq_comm (a:=(b:ZMod a)*(u:ZMod a))]
  split_ifs <;> simp_all

/- Every binary ideal form (a x+b y)²/a+n y²/a is Fricke-invariant at weight one and level 4n
with the standard multiplier −i. -/
theorem theta_fricke (n a : ℕ) [NeZero n] [NeZero a] (b : ℤ) {z : ℂ} (hz : 0 < z.im) :
    theta n a b (-1/(4*n*z)) = 2*(√n:ℂ)*(-I*z)*theta n a b z := by
  rw [theta_invert_packet n a b (by intro h; simp [h] at hz),dual_packet n a b hz]
  have ha : (a:ℂ)≠0 := by exact_mod_cast NeZero.ne a
  field_simp

end
end TunnellIdealTheta
end

section
/- The analytic HNF theta series enumerates elements of a given ideal by their normalized norm. -/
namespace TunnellIdealThetaExpansion
open TunnellIdealGenerators TunnellIdealHNF TunnellIdealTheta TunnellClassThetaCount
open TunnellShell TunnellToricClass TunnellToric Complex
open scoped Classical
noncomputable section

variable {n : ℕ}
def normTerm (I : Ideal (R n)) (z : ℂ) (x : I) :=
  Complex.exp (2*Real.pi*Complex.I*z*((x.val.norm:ℤ):ℂ)/normI I)

lemma admit_iff (s : Data n) (u : ℤ×ℤ) :
    admitted s.a (s.b:ℤ) u ↔ (s.a:ℤ)∣u.2-s.b*u.1 := by
  unfold admitted
  rw [← Int.cast_mul, ZMod.intCast_eq_intCast_iff_dvd_sub,dvd_sub_comm]
  
def point (s : Data n) (u : ℤ×ℤ) : R n := ⟨(s.c:ℤ)*u.2,(s.c:ℤ)*u.1⟩

lemma point_mem (s : Data n) {u : ℤ×ℤ} (hu : admitted s.a (s.b:ℤ) u) : point s u∈ideal s := by
  obtain ⟨t,ht⟩ := (admit_iff s u).mp hu
  refine (mem_ideal s _).mpr ⟨⟨u.1,rfl⟩,⟨t,?_⟩⟩
  dsimp only [point]; linear_combination s.c*ht

def pointEquiv (s : Data n) : {u : ℤ×ℤ // admitted s.a (s.b:ℤ) u} ≃ ideal s := by
  let f (u : {u : ℤ×ℤ // admitted s.a (s.b:ℤ) u}) : ideal s := ⟨point s u.val,point_mem s u.property⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b e
    have e₁ := congrArg (fun t : ideal s => t.val.re) e
    have e₂ := congrArg (fun t : ideal s => t.val.im) e
    have hc : (s.c:ℤ)≠0 := by exact_mod_cast s.pos_c.ne'
    exact Subtype.ext (Prod.ext (mul_left_cancel₀ hc e₂) (mul_left_cancel₀ hc e₁))
  · rintro ⟨x,hx⟩
    obtain ⟨u,v,e⟩ := basis_expansion s hx
    refine ⟨⟨(v,s.a*u+s.b*v),(admit_iff s _).mpr ⟨u,by dsimp only; ring⟩⟩,Subtype.ext ?_⟩
    exact e.symm

lemma point_term (s : Data n) (z : ℂ) (u : {u : ℤ×ℤ // admitted s.a (s.b:ℤ) u}) :
    normTerm (ideal s) z (pointEquiv s u)=term n s.a z u.val := by
  have hc : (s.c:ℂ)≠0 := by exact_mod_cast s.pos_c.ne'
  have ha : (s.a:ℂ)≠0 := by exact_mod_cast s.pos_a.ne'
  rw [normTerm,term,normI,quotient_card]
  change Complex.exp (_ * (((s.c:ℤ)*u.val.2*((s.c:ℤ)*u.val.2) - -(n:ℤ)*((s.c:ℤ)*u.val.1)*((s.c:ℤ)*u.val.1):ℤ) : ℂ)/ _) = _
  congr 1
  push_cast
  field_simp
  ring

theorem hnf_hasSum (s : Data n) (hn : 0<n) {z : ℂ} (hz : 0<z.im) :
    letI : NeZero s.a := ⟨s.pos_a.ne'⟩
    HasSum (normTerm (ideal s) z) (theta n s.a s.b z) := by
  letI : NeZero s.a := ⟨s.pos_a.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  have h := theta_hasSum n s.a (s.b:ℤ) hz
  apply (pointEquiv s).hasSum_iff.mp
  apply HasSum.congr_fun _ (fun u => point_term s z u)
  apply (hasSum_subtype_iff_indicator (f:=term n s.a z) (s:={u : ℤ×ℤ | admitted s.a (s.b:ℤ) u})).mpr
  exact h

def valence {I : Ideal (R n)} (x : I) := x.val.norm.toNat/normI I

lemma norm_valence (hn : Squarefree n) (h2 : n%4=2) {I : Ideal (R n)} (hI : I≠⊥) (x : I) :
    x.val.norm.toNat=valence x*normI I := by
  have hpos := normI_positive (by omega) I hI
  by_cases hx : x.val=0
  · simp [valence,hx,Zsqrtd.norm_zero]
  · have he := divide_mul hn h2 hI x.property
    have hB : divide I x.val≠⊥ := by
      intro e; rw [e,Ideal.bot_mul] at he
      have H : x.val∈principal x.val := Ideal.mem_span_singleton_self _
      rw [←he] at H
      exact hx H
    have eq : x.val.norm.toNat=normI (divide I x.val)*normI I := by
      rw [←normI_principal hn h2 hx,←he,normI_mul hn h2 hB hI]
    simp [valence,eq,Nat.mul_div_cancel _ hpos]

end
end TunnellIdealThetaExpansion
end

section
/- The class theta series, its Fourier expansion, and its Fricke transformation. -/
namespace TunnellClassThetaExpansion
open TunnellIdealGenerators TunnellIdealHNF TunnellIdealTheta TunnellClassThetaCount TunnellIdealThetaExpansion
open TunnellShell TunnellToricClass TunnellToric Complex
open scoped Classical
noncomputable section

variable {n : ℕ} {I : Ideal (R n)} (hn : Squarefree n) (h2 : n%4=2) (hI : I≠⊥)

def thetaI (I : Ideal (R n)) (z : ℂ) : ℂ := ∑' x : I, normTerm I z x

lemma thetaI_hasSum (hn' : 0<n) (hI : I≠⊥) {z : ℂ} (hz : 0<z.im) :
    HasSum (normTerm I z) (thetaI I z) := by
  obtain ⟨s,rfl⟩ := normal_form hn' hI
  exact (hnf_hasSum s hn' hz).summable.hasSum

include hn h2 hI in
lemma valence_zero (x : I) : valence x=0 ↔ x.val=0 := by
  constructor
  · intro h; by_contra e
    have eq := norm_valence hn h2 hI x
    rw [h,zero_mul] at eq
    have H := positive_norm (by omega) e
    omega
  · intro h; simp [valence,h,Zsqrtd.norm_zero]

def finiteRep (m : ℕ) (hm : 0 < m) {v : Triple} (hv : v∈shell n) : Finite (Representations I m) := by
  letI := Fintype.ofEquiv (finiteRoot n m) ((divisorEquiv hm).symm.trans (indexedEquiv (by omega)))
  exact Finite.of_equiv _ (repEquiv hn h2 hv hI)

def fiberRep {m : ℕ} (hm : 0 < m) : {x : I // valence x=m} ≃ Representations I m where
  toFun u := ⟨u.val.val,u.val.property,fun e => hm.ne' (u.property.symm.trans ((valence_zero hn h2 hI _).mpr e)),
    (norm_valence hn h2 hI u.val).trans (by rw [u.property])⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,by
    change x.val.norm.toNat/normI I=m
    rw [x.property.2.2,Nat.mul_div_cancel _ (normI_positive (by omega) I hI)]⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fiberZero : {x : I // valence x=0} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0,(valence_zero hn h2 hI _).mpr rfl⟩
  left_inv x := Subtype.ext (Subtype.ext (((valence_zero hn h2 hI x.val).mp x.property).symm))
  right_inv _ := rfl

def thetaCoeff (I : Ideal (R n)) (m : ℕ) := if m=0 then 1 else Nat.card (Representations I m)

include hn h2 hI in
lemma normTerm_fiber {m : ℕ} {z : ℂ} (x : {x : I // valence x=m}) :
    normTerm I z x.val = (Function.Periodic.qParam 1 z)^m := by
  have H := norm_valence hn h2 hI x.val
  rw [x.property] at H
  have e : x.val.val.norm=(m:ℤ)*normI I := by
    have H' : (x.val.val.norm.toNat:ℤ)=(m:ℤ)*normI I := by exact_mod_cast H
    rwa [Int.toNat_of_nonneg (Zsqrtd.norm_nonneg (by omega) _)] at H'
  have hN : (normI I:ℂ)≠0 := by exact_mod_cast (normI_positive (by omega) I hI).ne'
  rw [normTerm,e,Function.Periodic.qParam,←Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp <;> ring

include hn h2 hI in
theorem thetaI_expansion {v : Triple} (hv : v∈shell n) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun m : ℕ => (thetaCoeff I m:ℂ)*(Function.Periodic.qParam 1 z)^m) (thetaI I z) := by
  have H := ((Equiv.sigmaFiberEquiv (@valence n I)).hasSum_iff).mpr (thetaI_hasSum (by omega) hI hz)
  apply H.sigma
  intro m
  let F := {x : I // valence x=m}
  have Hf : Finite F := by
    by_cases hm : m=0
    · subst m; exact Finite.of_equiv Unit (fiberZero hn h2 hI).symm
    · letI := finiteRep hn h2 hI m (Nat.pos_of_ne_zero hm) hv
      exact Finite.of_equiv _ (fiberRep hn h2 hI (Nat.pos_of_ne_zero hm)).symm
  letI := Fintype.ofFinite F
  have hc : Nat.card F=thetaCoeff I m := by
    by_cases hm : m=0
    · subst m; rw [Nat.card_congr (fiberZero hn h2 hI)]; simp [thetaCoeff]
    · simpa [thetaCoeff,hm] using Nat.card_congr (fiberRep hn h2 hI (Nat.pos_of_ne_zero hm))
  have hfin := hasSum_fintype (fun _ : F => (Function.Periodic.qParam 1 z)^m)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,hc] at hfin
  exact hfin.congr_fun (fun x => normTerm_fiber hn h2 hI x)

end
end TunnellClassThetaExpansion
end

section
/- The coefficient theta in the Rankin integral is the full ideal class theta with its constant removed. -/
namespace TunnellFullClassTheta
open TunnellShell TunnellToricClass TunnellToric TunnellClassThetaCount TunnellClassThetaExpansion
open TunnellRankin TunnellIdealHNF Complex Finset
open scoped Classical UpperHalfPlane
noncomputable section

def inverted (n : ℕ) (hn : 0<n) (z : ℍ) : ℍ := ⟨-1/(4*n*(z:ℂ)),by
  have h : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hq : (0:ℝ)<(4*(n:ℂ)*(z:ℂ)).im := by simpa [Complex.mul_im] using (show 0<4*(n:ℝ)*z.im by positivity)
  have hq' : (4*(n:ℂ)*(z:ℂ))≠0 := fun h => by rw [h] at hq; exact lt_irrefl _ hq
  rw [neg_div,one_div,Complex.neg_im,Complex.inv_im,neg_div,neg_neg]
  exact div_pos hq (Complex.normSq_pos.mpr hq')⟩

theorem ideal_fricke {n : ℕ} (hn : 0<n) (I : Ideal (R n)) (hI : I≠⊥) (z : ℍ) :
    thetaI I (inverted n hn z)= 2*(Real.sqrt n:ℂ)*(-Complex.I*z)*thetaI I z := by
  obtain ⟨s,rfl⟩ := normal_form hn hI
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero s.a := ⟨s.pos_a.ne'⟩
  rw [thetaI,(TunnellIdealThetaExpansion.hnf_hasSum s hn (inverted n hn z).im_pos).tsum_eq,
    thetaI,(TunnellIdealThetaExpansion.hnf_hasSum s hn z.im_pos).tsum_eq]
  exact TunnellIdealTheta.theta_fricke n s.a s.b z.im_pos

variable {d : ℕ} {v : Triple} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hv : v∈shell (2*d))

def classFintype : Fintype (ProperIdealClass v) := Fintype.ofEquiv ↥(representatives (2*d)) (idealEquiv hn h2 hv).symm

def full (z : ℍ) : ℂ := by
  letI := classFintype hn h2 hv
  exact ∑ c : ProperIdealClass v, thetaI (liftClass hv c) z

theorem full_fricke (z : ℍ) : full hn h2 hv (inverted (2*d) (by omega) z) =
    2*(Real.sqrt (2*d:ℕ):ℂ)*(-Complex.I*z)*full hn h2 hv z := by
  letI := classFintype hn h2 hv
  simp only [full,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => ideal_fricke (by omega) _ (lift_ne_bot hn h2 hv c) z)

theorem full_expansion (z : ℍ) : letI := classFintype hn h2 hv
    full hn h2 hv z= (Fintype.card (ProperIdealClass v):ℂ)+2*TunnellRankin.theta d z := by
  classical
  letI := classFintype hn h2 hv
  let q := Function.Periodic.qParam 1 (z:ℂ)
  let h : ℂ := Fintype.card (ProperIdealClass v)
  have H := hasSum_sum (s:=univ) (fun (c : ProperIdealClass v) _ => thetaI_expansion hn h2 (lift_ne_bot hn h2 hv c) hv z.im_pos)
  have H' : HasSum (fun m : ℕ => (if m=0 then h else 2*(idealCoeff d m:ℂ))*q^m) (full hn h2 hv z) := by
    apply H.congr_fun
    intro m
    change (if m=0 then h else 2*(idealCoeff d m:ℂ))*q^m = ∑ c : ProperIdealClass v, (thetaCoeff (liftClass hv c) m:ℂ)*q^m
    rw [←sum_mul]; congr 1
    by_cases hm : m=0
    · subst m; simp [h,thetaCoeff]
    · rw [if_neg hm,rankin_ideal_count d m hn (Nat.pos_of_ne_zero hm)]
      simp only [thetaCoeff,hm,if_false,←Nat.cast_sum,Int.cast_natCast]
      exact_mod_cast (total_count hn h2 hv (Nat.pos_of_ne_zero hm)).symm
  have h0 : HasSum (fun m : ℕ => if m=0 then h else 0) h := by simpa using (hasSum_ite_eq (0:ℕ) h)
  have A : HasSum (fun m : ℕ => 2*((idealCoeff d m:ℂ)*q^m)) (full hn h2 hv z-h) := by
    apply (H'.sub h0).congr_fun
    intro m; by_cases hm : m=0
    · subst m; simp [idealCoeff]
    · simp [hm,mul_assoc]
  have e := A.tsum_eq
  rw [tsum_mul_left] at e
  change 2*TunnellRankin.theta d z=full hn h2 hv z-h at e
  change _=h+_
  linear_combination -e

end
end TunnellFullClassTheta
end

section
/- The weak functional equation of the quadratic ideal-class theta on the imaginary axis. -/
namespace TunnellClassThetaMellin
open Complex TunnellRankin TunnellFullClassTheta TunnellShell TunnellToricClass TunnellToric
open Filter MeasureTheory Set Asymptotics
open scoped Topology UpperHalfPlane
noncomputable section

def term (d : ℕ) (u t : ℝ) (m : ℕ) : ℂ :=
  (idealCoeff d m:ℂ)*(Real.exp (-u*m*t):ℝ)

def radial (d : ℕ) (u t : ℝ) := ∑' m : ℕ, term d u t m

lemma comparison_summable {u : ℝ} (hu : 0<u) :
    Summable (fun m : ℕ => (m:ℝ)*Real.exp (-u*m)) := by
  simpa using Real.summable_pow_mul_exp_neg_nat_mul 1 hu

lemma norm_term (d m : ℕ) (u t : ℝ) :
    ‖term d u t m‖≤(m:ℝ)*Real.exp (-u*m*t) := by
  simp only [term,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  gcongr
  exact norm_idealCoeff d m

lemma summable_term (d : ℕ) {u t : ℝ} (hu : 0<u) (ht : 0<t) :
    Summable (term d u t) := by
  apply (comparison_summable (mul_pos hu ht)).of_norm_bounded
  intro m
  convert norm_term d m u t using 1
  congr 2
  ring

lemma continuous_radial (d : ℕ) {u : ℝ} (hu : 0<u) : ContinuousOn (radial d u) (Ioi 0) := by
  intro t ht
  have h : 0<t/2 := by have := ht; change 0<t at this; linarith
  have hs : ContinuousOn (radial d u) (Ioi (t/2)) := by
    apply continuousOn_tsum (u:=fun m : ℕ => (m:ℝ)*Real.exp (-(u*(t/2))*m))
    · intro m; unfold term; fun_prop
    · exact comparison_summable (mul_pos hu h)
    · intro m x hx
      apply (norm_term d m u x).trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (Nat.cast_nonneg _)
      change t/2<x at hx
      nlinarith [mul_nonneg (mul_nonneg hu.le (Nat.cast_nonneg (α:=ℝ) m)) (sub_nonneg.mpr hx.le)]
  exact (hs.continuousAt (isOpen_Ioi.mem_nhds (show t∈Ioi (t/2) by change t/2<t; linarith))).continuousWithinAt

lemma radial_decay (d : ℕ) {u : ℝ} (hu : 0<u) (r : ℝ) :
    radial d u =O[atTop] (fun t : ℝ => t^r) := by
  have hu' : 0<u/2 := by linarith
  refine IsBigO.trans (g:=fun t : ℝ => Real.exp (-(u/2)*t)) ?_ (isLittleO_exp_neg_mul_rpow_atTop hu' r).isBigO
  apply IsBigO.of_bound (∑' m : ℕ,(m:ℝ)*Real.exp (-(u/2)*m))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),radial]
  rw [←tsum_mul_right]
  apply (norm_tsum_le_tsum_norm (summable_term d hu (by linarith : 0<t)).norm).trans
  apply Summable.tsum_le_tsum _ (summable_term d hu (by linarith : 0<t)).norm ((comparison_summable hu').mul_right _)
  intro m
  by_cases hm : m=0
  · subst m; simp [term,idealCoeff]
  · have hm' : 1≤(m:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    rw [mul_assoc,←Real.exp_add]
    apply (norm_term d m u t).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (Nat.cast_nonneg _)
    nlinarith [mul_nonneg (sub_nonneg.mpr hm') (sub_nonneg.mpr ht),
       mul_nonneg hu.le (sub_nonneg.mpr (one_le_mul_of_one_le_of_one_le hm' ht)),
       mul_nonneg hu.le (mul_nonneg (sub_nonneg.mpr hm') (sub_nonneg.mpr ht))]

def axis (v t : ℝ) (hv : 0<v) (ht : 0<t) : ℍ :=
  ⟨Complex.I*(t/v:ℝ),by simpa using div_pos ht hv⟩

lemma theta_axis (d : ℕ) {v t : ℝ} (hv : 0<v) (ht : 0<t) :
    theta d (axis v t hv ht)=radial d (2*Real.pi/v) t := by
  unfold theta radial
  apply tsum_congr
  intro m
  unfold term
  congr 1
  simp only [Function.Periodic.qParam,axis,Complex.ofReal_one,div_one,←Complex.exp_nat_mul,Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

variable {d : ℕ} {b : Triple} (hs : Squarefree (2*d)) (h2 : (2*d)%4=2) (hb : b∈shell (2*d))

def v (d : ℕ) : ℝ := 2*Real.sqrt (2*d:ℕ)

lemma v_pos (hd : 0<d) : 0<v d := by unfold v; positivity
lemma v_sq (d : ℕ) : v d^2=4*(2*d:ℕ) := by unfold v; rw [mul_pow,Real.sq_sqrt (by positivity)]; ring

def hclass : ℂ := (Nat.card (ProperIdealClass b):ℂ)

def classRadial (d : ℕ) (h : ℂ) (t : ℝ) := h+2*radial d (2*Real.pi/v d) t

lemma axial_expansion {t : ℝ} (ht : 0<t) :
    full hs h2 hb (axis (v d) t (v_pos (by omega)) ht)=classRadial d (hclass (b:=b)) t := by
  rw [full_expansion hs h2 hb,theta_axis,classRadial]
  congr 1
  letI := classFintype hs h2 hb
  simp [hclass,Nat.card_eq_fintype_card]

include hs h2 hb in
lemma classRadial_feq {t : ℝ} (ht : 0<t) : classRadial d (hclass (b:=b)) (1/t) =
    (t:ℂ)*classRadial d (hclass (b:=b)) t := by
  have hv := v_pos (show 0<d by omega)
  rw [←axial_expansion hs h2 hb (one_div_pos.mpr ht),←axial_expansion hs h2 hb ht]
  have he : axis (v d) (1/t) hv (one_div_pos.mpr ht)=inverted (2*d) (by omega) (axis (v d) t hv ht) := by
    ext1
    change Complex.I*((1/t)/v d:ℝ) = -1/(4*(2*d:ℕ)*(Complex.I*(t/v d:ℝ)))
    have hv' : (v d:ℂ)^2=4*((2*d:ℕ):ℂ) := by exact_mod_cast v_sq d
    rw [←hv']
    push_cast
    field_simp [Complex.I_ne_zero,hv.ne',ht.ne']
    ring_nf
    rw [Complex.I_sq]
  rw [he,full_fricke]
  congr 1
  rw [←show (v d:ℂ)=2*(Real.sqrt (2*d:ℕ):ℂ) by simp [v]]
  change (v d:ℂ)*(-Complex.I*(Complex.I*(t/v d:ℝ)))=t
  push_cast
  field_simp [hv.ne']
  ring_nf
  rw [Complex.I_sq]
  ring

include hs h2 hb in
def pair : WeakFEPair ℂ := by
  let h := hclass (b:=b)
  let u := 2*Real.pi/v d
  have hu : 0<u := div_pos (by positivity) (v_pos (by omega))
  have hc : ContinuousOn (classRadial d h) (Ioi 0) :=
    continuousOn_const.add (continuousOn_const.mul (continuous_radial _ hu))
  have hr (r : ℝ) : (fun t => classRadial d h t-h) =O[atTop] (fun t : ℝ => t^r) := by
    simpa only [classRadial,add_sub_cancel_left] using (radial_decay d hu r).const_mul_left (2:ℂ)
  exact ⟨classRadial d h,classRadial d h,1,1,h,h,hc.locallyIntegrableOn isOpen_Ioi.measurableSet,
    hc.locallyIntegrableOn isOpen_Ioi.measurableSet,one_pos,one_ne_zero,
    fun t ht => by simpa using classRadial_feq hs h2 hb ht,hr,hr⟩

end
end TunnellClassThetaMellin
end

section
/- The class-number normalization of the central weight-one Eisenstein series. -/
namespace TunnellClassThetaMellin
open Complex TunnellRankin TunnellShell Set Filter
open scoped Topology
noncomputable section

variable {d : ℕ} {b : Triple} (hsq : Squarefree (2*d)) (h2 : (2*d)%4=2) (hb : b∈shell (2*d))

lemma pair_large {s : ℂ} (hs : 1<s.re) :
    (pair hsq h2 hb).Λ s =
      2*Gamma s/((2*Real.pi/v d:ℝ):ℂ)^s * (riemannZeta s * negativeL d (by omega) s) := by
  let u := 2*Real.pi/v d
  have hu : 0<u := div_pos (by positivity) (v_pos (by omega))
  have hs0 : s≠0 := by intro h; rw [h] at hs; norm_num at hs
  have HD := class_hasSum (d:=d) (by omega) hs
  have hsum : Summable (fun m : ℕ => ‖(idealCoeff d m:ℂ)‖/(m:ℝ)^s.re) := by
    apply HD.summable.norm.congr
    intro m
    by_cases hm : m=0
    · subst m; simp [idealCoeff]
    · rw [norm_div,Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm)]
  have hnorm : Summable (fun m : ℕ => ‖(2:ℂ)*(idealCoeff d m:ℂ)‖/(u*(m:ℝ))^s.re) := by
    apply (hsum.mul_left (2/u^s.re)).congr
    intro m
    rw [norm_mul,Complex.norm_ofNat,Real.mul_rpow hu.le (Nat.cast_nonneg _)]
    ring
  have hq (m : ℕ) : 2*(idealCoeff d m:ℂ)=0 ∨ 0<u*m := by
    by_cases hm : m=0
    · simp [hm,idealCoeff]
    · exact Or.inr (mul_pos hu (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)))
  let P := pair hsq h2 hb
  have hF (t : ℝ) (ht : t∈Ioi 0) :
      HasSum (fun m : ℕ => (2*(idealCoeff d m:ℂ)) * (Real.exp (-(u*m)*t):ℝ)) (P.f t-P.f₀) := by
    change HasSum _ (classRadial _ _ t-hclass (b:=b))
    simp only [classRadial,add_sub_cancel_left]
    apply ((summable_term d hu ht).hasSum.mul_left 2).congr_fun
    intro m; simp [term,mul_assoc]
  have H := hasSum_mellin (s:=s) hq (by linarith) hF hnorm
  rw [(P.hasMellin (show P.k<s.re from hs)).2] at H
  apply H.unique
  apply (HD.mul_left (2*Gamma s/(u:ℂ)^s)).congr_fun
  intro m
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hu.le (Nat.cast_nonneg m),Complex.ofReal_natCast]
  ring

include hsq h2 hb in
theorem class_number (hd : d%4=1) :
    (v d:ℂ)*negativeL d (by omega) 1=Real.pi * hclass (b:=b) := by
  let P := pair hsq h2 hb
  let u := 2*Real.pi/v d
  have hv := v_pos (show 0<d by omega)
  have hu : 0<u := div_pos (by positivity) hv
  haveI : NeZero (4*(2*d)) := ⟨by omega⟩
  have hχ : negCharacter d (by omega)≠1 := by
    intro h
    have e := negCharacter_odd hd
    rw [DirichletCharacter.Odd,h,MulChar.one_apply (by simp)] at e
    norm_num at e
  have incl : Tendsto ((↑):ℝ→ℂ) (𝓝[>] (1:ℝ)) (𝓝[≠] (1:ℂ)) := by
    apply continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    intro x hx hx'
    change (x:ℂ)=1 at hx'
    have : x=1 := by exact_mod_cast hx'
    exact (ne_of_gt hx) this
  have hc : ContinuousAt (fun s : ℂ => 2*Gamma s/(u:ℂ)^s * negativeL d (by omega) s) 1 := by
    have hL := ((negCharacter d (by omega)).differentiable_LFunction hχ).continuous.continuousAt (x:=(1:ℂ))
    have hGa : ContinuousAt Gamma (1:ℂ) := (differentiableAt_Gamma 1 (by intro n h; have := congrArg Complex.re h; simp at this; linarith)).continuousAt
    apply ContinuousAt.mul _ hL
    apply (continuousAt_const.mul hGa).div
    · exact continuousAt_id.const_cpow (Or.inl (show (u:ℂ)≠0 by exact_mod_cast hu.ne'))
    · simp [hu.ne']
  have H := (hc.tendsto.comp (incl.mono_right nhdsWithin_le_nhds)).mul (riemannZeta_residue_one.comp incl)
  have H' : Tendsto (fun s : ℝ => ((s:ℂ)-1)*P.Λ s) (𝓝[>] (1:ℝ)) (𝓝 (hclass (b:=b))) := by
    simpa only [P,pair,Complex.ofReal_one,one_smul,smul_eq_mul,one_mul,Function.comp_def] using P.Λ_residue_k.comp incl
  have he := tendsto_nhds_unique H' (H.congr' (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    change 1<s at hs
    change _ = ((s:ℂ)-1)*P.Λ s
    rw [show P.Λ s = _ from pair_large hsq h2 hb (by simpa using hs)]
    dsimp only [Function.comp_apply,u]
    ring))
  simp only [Gamma_one,mul_one,Complex.cpow_one] at he
  dsimp [u] at he
  push_cast at he
  field_simp [hv.ne',Real.pi_ne_zero] at he
  linear_combination -he

end
end TunnellClassThetaMellin
end

section
/- Computing the phase of the primitive odd Gauss sum from quadratic theta duality. -/
namespace TunnellClassThetaMellin
open Complex TunnellRankin DirichletCharacter TunnellShell Set Filter
open scoped Topology

noncomputable section

def product (d : ℕ) (h : 0<d) (s : ℂ) : ℂ :=
  haveI : NeZero (4*(2*d)) := ⟨by omega⟩
  (v d:ℂ)^s * completedRiemannZeta s * (negCharacter d h).completedLFunction s

lemma gamma_normalization {v : ℝ} (hv : 0<v) {s : ℂ} :
    2*Gamma s/((2*Real.pi/v:ℝ):ℂ)^s=(v:ℂ)^s * Gammaℂ s := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (by positivity) hv.le,Gammaℂ_def]
  push_cast
  rw [Complex.cpow_neg]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

variable {d : ℕ} {b : Triple} (hsq : Squarefree (2*d)) (h2 : (2*d)%4=2) (hb : b∈shell (2*d))

lemma product_large (hd : d%4=1) {s : ℂ} (hs : 1<s.re) :
    (pair hsq h2 hb).Λ s=product d (by omega) s := by
  haveI : NeZero (4*(2*d)) := ⟨by omega⟩
  let χ := negCharacter d (by omega)
  have hs0 : s≠0 := by intro h; norm_num [h] at hs
  have hg1 := Gammaℝ_ne_zero_of_re_pos (by linarith : 0<s.re)
  have hg2 := Gammaℝ_ne_zero_of_re_pos (show 0<(s+1).re by simp; linarith)
  rw [pair_large hsq h2 hb hs,gamma_normalization (v_pos (by omega)),←Gammaℝ_mul_Gammaℝ_add_one,
    riemannZeta_def_of_ne_zero hs0,negativeL,LFunction_eq_completed_div_gammaFactor _ _ (.inl hs0),
    (negCharacter_odd hd).gammaFactor_def,product]
  field_simp

lemma product_upper (hd : d%4=1) :
    EqOn (pair hsq h2 hb).Λ (product d (by omega)) {s : ℂ | 0<s.im} := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let P := pair hsq h2 hb
  have h0 {z : ℂ} (hz : 0<z.im) : z≠0 ∧ z≠1 := by
    constructor <;> intro h <;> simp [h] at hz
  have ho : IsOpen {s : ℂ | 0<s.im} := isOpen_lt continuous_const continuous_im
  have hf : AnalyticOnNhd ℂ P.Λ {s : ℂ | 0<s.im} := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro s hs
    exact (P.differentiableAt_Λ (.inl (h0 hs).1) (.inl (by simpa [P,pair] using (h0 hs).2))).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (product d (by omega)) {s : ℂ | 0<s.im} := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro s hs
    have hv : (v d:ℂ)≠0 := by exact_mod_cast (v_pos (show 0<d by omega)).ne'
    have H := (negCharacter d (by omega)).differentiableAt_completedLFunction s (.inl (h0 hs).1) (.inl (h0 hs).2)
    exact (((differentiableAt_id.const_cpow (.inl hv)).mul (differentiableAt_completedZeta (h0 hs).1 (h0 hs).2)).mul H).differentiableWithinAt
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_im_gt 0).isPreconnected
    (z₀:=2+I) (by simp)
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show 1<(2+I).re by norm_num)] with s hs
  exact product_large hsq h2 hb hd hs

include hsq h2 hb in
lemma completed_zero (hd : d%4=1) :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    (negCharacter d (by omega)).completedLFunction 0=hclass (b:=b) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let P := pair hsq h2 hb
  let χ := negCharacter d (by omega)
  let t (r : ℝ) := (r:ℂ)*I
  have tn : Tendsto t (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
    have he : t 0=0 := by simp [t]
    conv in 𝓝[≠] (0:ℂ) => rw [←he]
    apply (show ContinuousAt t 0 by dsimp [t]; fun_prop).continuousWithinAt.tendsto_nhdsWithin
    intro r hr hr0
    exact (ne_of_gt hr) (by simpa [t] using hr0)
  have ht (r : ℝ) (hr : 0<r) : 0<(t r).im := by simpa [t] using hr
  have hZ : Tendsto (fun s : ℂ => s*completedRiemannZeta s) (𝓝[≠] 0) (𝓝 (-1)) := by
    simpa only [HurwitzZeta.completedHurwitzZetaEven_zero,if_true] using HurwitzZeta.completedHurwitzZetaEven_residue_zero 0
  have hχ : χ≠1 := by
    intro h
    have e : χ.Odd := negCharacter_odd hd
    rw [DirichletCharacter.Odd,h,MulChar.one_apply (by simp)] at e
    norm_num at e
  have hv : (v d:ℂ)≠0 := by exact_mod_cast (v_pos (show 0<d by omega)).ne'
  have hvC : ContinuousAt (fun s : ℂ => (v d:ℂ)^s) 0 := continuousAt_id.const_cpow (.inl hv)
  have H₀ := P.Λ_residue_zero.comp tn
  have HH := ((hvC.tendsto.mono_left nhdsWithin_le_nhds).mul hZ).mul
    ((differentiable_completedLFunction hχ).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have he := tendsto_nhds_unique H₀ ((HH.comp tn).congr' (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    change _ = t r*P.Λ (t r)
    rw [show P.Λ (t r)=_ from product_upper hsq h2 hb hd (ht r hr), product]
    dsimp only [Function.comp_apply,χ]
    ring))
  simpa [P,pair,χ] using congrArg Neg.neg he.symm

include hsq h2 hb in
theorem gauss_value (hd : d%4=1) :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    gaussSum (negCharacter d (by omega)) ZMod.stdAddChar=I*(v d:ℂ) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let χ := negCharacter d (by omega)
  have ho : χ.Odd := negCharacter_odd hd
  have hq : χ.IsQuadratic := TunnellRankinEisenstein.negative_quadratic _
  have hp : χ.IsPrimitive := TunnellRankinEisenstein.negative_primitive hd hsq.of_mul_right
  have e := hp.completedLFunction_one_sub 1
  rw [sub_self,hq.inv,rootNumber,if_neg ho.not_even,pow_one,show (1:ℂ)-1/2=1/2 by ring] at e
  have nn : (((4*(2*d):ℕ):ℂ)^(1/2:ℂ))≠0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast NeZero.ne (4*(2*d))))
  have h' : χ.completedLFunction 0 = (gaussSum χ ZMod.stdAddChar/I)*χ.completedLFunction 1 := by
    rw [e]; field_simp
  have hg : Gammaℝ (1+1)=1/(Real.pi:ℂ) := by simpa using (Gammaℝ_mul_Gammaℝ_add_one 1).trans Gammaℂ_one
  have hχ : χ≠1 := by
    intro h; rw [DirichletCharacter.Odd,h,MulChar.one_apply (by simp)] at ho; norm_num at ho
  have hL := χ.LFunction_eq_completed_div_gammaFactor 1 (.inl one_ne_zero)
  rw [ho.gammaFactor_def,hg] at hL
  have hnL : χ.completedLFunction 1 ≠ 0 := by
    intro h; rw [h,zero_div] at hL; exact χ.LFunction_apply_one_ne_zero hχ hL
  have hn := class_number hsq h2 hb hd
  change (v d:ℂ)*χ.LFunction 1=Real.pi*hclass (b:=b) at hn
  rw [hL,←completed_zero hsq h2 hb hd] at hn
  change _=Real.pi*χ.completedLFunction 0 at hn
  rw [h'] at hn
  change gaussSum χ ZMod.stdAddChar=I*(v d:ℂ)
  field_simp [Real.pi_ne_zero] at hn
  simpa only [mul_comm] using hn.symm

end
end TunnellClassThetaMellin
end

section
/- Boundary values of the conductor-32 primitive at all rational cusps. -/

namespace TunnellFricke

open Complex Function Filter Set
open UpperHalfPlane hiding I
open scoped Topology

noncomputable def height (r : ℝ) (z : ℂ) : ℝ := z.im / normSq (z-r)

noncomputable def cusp (r : ℝ) : Filter ℂ := comap (height r) atTop

lemma eventually_upper (r : ℝ) : ∀ᶠ z in cusp r, 0<z.im := by
  filter_upwards [(tendsto_comap (f:=height r) (x:=atTop)).eventually (eventually_gt_atTop 0)] with z hz
  exact (div_pos_iff.mp hz).elim (fun h => h.1) (fun h => False.elim ((normSq_nonneg _).not_gt h.2))

lemma W_im (z : ℂ) : (W z).im = height 0 z / 2 := by
  simp [W,height,Complex.div_im,Complex.mul_im,Complex.normSq_mul,pow_two]
  ring

lemma height_add (r t : ℝ) (z : ℂ) : height (r+t) (z+t) = height r z := by
  simp [height,add_sub_add_right_eq_sub]

lemma height_W (r : ℝ) (hr : r≠0) (z : ℂ) (hz : 0<z.im) :
    height (-1/(2*r)) (W z) = 2*r^2*height r z := by
  have hz0 := ne_zero (⟨z,hz⟩:ℍ)
  have hrC : (r:ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hz' : z-(r:ℂ)≠0 := by
    intro he
    have e := congrArg Complex.im (sub_eq_zero.mp he)
    simp at e
    linarith
  have dif : W z - ((-1/(2*r):ℝ):ℂ) = (z-r)/(2*z*r) := by
    unfold W
    push_cast
    field_simp
    ring
  rw [height,W_im,dif,normSq_div,height,height]
  simp only [ofReal_zero,sub_zero,map_mul,normSq_ofReal]
  field_simp [Complex.normSq_eq_zero.not.mpr hz0,Complex.normSq_eq_zero.not.mpr hz',hr]
  norm_num [normSq_apply]
  <;> ring

lemma move_W (r : ℝ) (hr : r≠0) : Tendsto W (cusp r) (cusp (-1/(2*r))) := by
  apply tendsto_comap_iff.mpr
  apply Tendsto.congr' _ (tendsto_comap (f:=height r) (x:=atTop) |>.const_mul_atTop (show 0<2*r^2 by positivity))
  filter_upwards [eventually_upper r] with z hz
  exact (height_W r hr z hz).symm

lemma move_add (r t : ℝ) : Tendsto (fun z : ℂ => z+t) (cusp r) (cusp (r+t)) := by
  apply tendsto_comap_iff.mpr
  exact tendsto_comap.congr (fun z => (height_add r t z).symm)

lemma move_zero : Tendsto W (cusp 0) (comap Complex.im atTop) := by
  apply tendsto_comap_iff.mpr
  exact ((tendsto_comap (f:=height 0) (x:=atTop)).atTop_mul_const (by norm_num : (0:ℝ)<2⁻¹)).congr (fun z => by simp [Function.comp_def,W_im,div_eq_mul_inv])

noncomputable def gi : GaussianInt := ⟨0,1⟩
lemma coe_gi : (gi:ℂ) = I := by simp [gi,GaussianInt.toComplex_def]

def Bound (J : ℂ → ℂ) (C : ℂ) (x : ℚ) (a : GaussianInt) : Prop :=
  Tendsto J (cusp x) (𝓝 ((a:ℂ)*C))

theorem cusp_rules {J : ℂ → ℂ} {C : ℂ}
    (h0 : Tendsto J (comap Complex.im atTop) (𝓝 0))
    (hT : ∀ z, 0<z.im → J (z+1) = I*J z)
    (hW : ∀ z, 0<z.im → J (W z) = C-J z) :
    Bound J C 0 1 ∧
    (∀ x a, Bound J C x a → Bound J C (x+1) (gi*a)) ∧
    (∀ x a, Bound J C x a → Bound J C (x-1) (-gi*a)) ∧
    (∀ x, x≠0 → ∀ a, Bound J C x a → Bound J C (-1/(2*x)) (1-a)) := by
  unfold Bound
  refine ⟨?_,?_,?_,?_⟩
  · simp only [map_one,one_mul,Rat.cast_zero]
    have ht := tendsto_const_nhds (x:=C) |>.sub (h0.comp move_zero)
    rw [sub_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_upper 0] with z hz
    simp [Function.comp_def,hW z hz]
  · intro x a ha
    simp only [Rat.cast_add,Rat.cast_one,map_mul,coe_gi,mul_assoc]
    have ht := move_add ((x:ℝ)+1) (-1)
    simp only [add_neg_cancel_right] at ht
    apply (ha.comp ht |>.const_mul I).congr'
    filter_upwards [eventually_upper ((x:ℝ)+1)] with z hz
    have he := hT (z-1) (by simpa using hz)
    simpa [Function.comp_def,sub_eq_add_neg] using he.symm
  · intro x a ha
    simp only [Rat.cast_sub,Rat.cast_one,map_mul,map_neg,coe_gi,mul_assoc]
    have ht := move_add ((x:ℝ)-1) 1
    simp only [sub_add_cancel] at ht
    apply (ha.comp ht |>.const_mul (-I)).congr'
    filter_upwards [eventually_upper ((x:ℝ)-1)] with z hz
    change (-I)*J (z+(1:ℝ)) = J z
    simp [hT z hz,← mul_assoc]
  · intro x hx a ha
    have hr : (x:ℝ) ≠ 0 := by exact_mod_cast hx
    have ht := move_W (-1/(2*(x:ℝ))) (by positivity)
    rw [show -1 / (2 * (-1/(2*(x:ℝ)))) = x by field_simp] at ht
    simp only [Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,map_sub,map_one,sub_mul,one_mul]
    apply (tendsto_const_nhds (x:=C) |>.sub (ha.comp ht)).congr'
    filter_upwards [eventually_upper (-1/(2*(x:ℝ)))] with z hz
    simp [Function.comp_def,hW z hz]

end TunnellFricke
end

section
/- The normalized conductor-32 cusp symbol by the nearest-integer Euclidean algorithm. -/

namespace TunnellCuspEuclid

open TunnellFricke

def iunit : GaussianInt := ⟨0,1⟩

def rot (k : ℤ) : GaussianInt :=
  if k%4=0 then 1 else if k%4=1 then iunit else if k%4=2 then -1 else -iunit

lemma rot_succ (k : ℤ) : rot (k+1)=iunit*rot k := by
  unfold rot
  split_ifs <;> first | decide | omega

lemma rot_pred (k : ℤ) : rot (k-1)=(-iunit)*rot k := by
  unfold rot
  split_ifs <;> first | decide | omega

def symbolAux : ℕ → ℤ → ℕ → GaussianInt
  | 0, _, _ => 1
  | fuel+1, a, d =>
    let r := a.bmod d
    rot (a.bdiv d) * (if r=0 then 1 else if 2*r=-(d:ℤ) then 1-iunit else
      1-symbolAux fuel (if 0≤r then -(d:ℤ) else (d:ℤ)) (2*r.natAbs))

def symbol (a : ℤ) (d : ℕ) := symbolAux d a d

lemma symbol_rules (B : ℚ → GaussianInt → Prop) (h0 : B 0 1)
    (hp : ∀ x a, B x a → B (x+1) (iunit*a)) (hm : ∀ x a, B x a → B (x-1) (-iunit*a))
    (hw : ∀ x, x≠0 → ∀ a, B x a → B (-1/(2*x)) (1-a)) (a : ℤ) (d : ℕ) (hd : 0<d) :
    B ((a:ℚ)/d) (symbol a d) := by
  have ht (x : ℚ) (b : GaussianInt) (hb : B x b) (k : ℤ) : B (x+k) (rot k*b) := by
    induction k using Int.induction_on with
    | zero => simpa [rot] using hb
    | succ i ih => simpa [rot_succ,Int.cast_add,add_assoc,mul_assoc] using hp _ _ ih
    | pred i ih =>
      rw [rot_pred]
      simpa [Int.cast_sub,sub_eq_add_neg,add_assoc,mul_assoc] using hm _ _ ih
  suffices all : ∀ (fuel d : ℕ) (a : ℤ), 0<d → d≤fuel → B ((a:ℚ)/d) (symbolAux fuel a d) from all d d a hd le_rfl
  intro fuel
  induction fuel with
  | zero => intro d a hd h; omega
  | succ n ih =>
    intro d a hd hdn
    let r := a.bmod d
    have hr := (Int.bmod_eq_iff (a:=a) hd).mp (rfl : a.bmod d=r)
    have hdq : (d:ℚ) ≠ 0 := by positivity
    have eqr : (a:ℚ)/d = (r:ℚ)/d + (a.bdiv d:ℚ) := by
      field_simp
      exact_mod_cast (Int.bmod_add_bdiv a d).symm
    rw [eqr]
    unfold symbolAux
    apply ht
    change B ((r:ℚ)/d) (if r=0 then 1 else if 2*r=-(d:ℤ) then 1-iunit else _)
    by_cases h0r : r=0
    · simpa [h0r] using h0
    rw [if_neg h0r]
    by_cases he : 2*r=-(d:ℤ)
    · rw [if_pos he]
      have e : (r:ℚ)/d = -1/2 := by
        have hh : 2*(r:ℚ) = -(d:ℚ) := by exact_mod_cast he
        field_simp
        linarith
      rw [e]
      simpa using hw 1 one_ne_zero _ (by simpa using hp _ _ h0)
    · rw [if_neg he]
      have hsmall : 2*r.natAbs<d := by omega
      have hpos : 0<2*r.natAbs := by omega
      have hrq : (r:ℚ)≠0 := by exact_mod_cast h0r
      split_ifs with hsign
      · have ee : (r.natAbs:ℚ)=r := by
          have e : (r.natAbs:ℤ)=r := by omega
          simpa only [Int.cast_natCast] using congrArg (fun a:ℤ => (a:ℚ)) e
        have hh := ih _ (-(d:ℤ)) hpos (by omega)
        rw [Nat.cast_mul,Nat.cast_two,ee,Int.cast_neg,Int.cast_natCast] at hh
        convert hw _ (div_ne_zero (neg_ne_zero.mpr hdq) (mul_ne_zero (by norm_num) hrq)) _ hh using 1 <;> field_simp <;> ring
      · have ee : (r.natAbs:ℚ) = -r := by
          have e : (r.natAbs:ℤ) = -r := by omega
          simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun a:ℤ => (a:ℚ)) e
        have hh := ih _ (d:ℤ) hpos (by omega)
        rw [Nat.cast_mul,Nat.cast_two,ee,Int.cast_natCast] at hh
        convert hw _ (div_ne_zero hdq (mul_ne_zero (by norm_num) (neg_ne_zero.mpr hrq))) _ hh using 1 <;> field_simp <;> ring

open Complex Filter
open scoped Topology

theorem cusp_value {J : ℂ → ℂ} {C : ℂ}
    (h0 : Tendsto J (comap Complex.im atTop) (𝓝 0))
    (hT : ∀ z, 0<z.im → J (z+1) = I*J z)
    (hW : ∀ z, 0<z.im → J (W z) = C-J z) (a : ℤ) (d : ℕ) (hd : 0<d) :
    Bound J C ((a:ℚ)/d) (symbol a d) ∧ Bound J C (-((a:ℚ)/d)) (star (symbol a d)) := by
  obtain ⟨hz,hp,hm,hw⟩ := cusp_rules h0 hT hW
  have hi : star iunit = -iunit := rfl
  apply symbol_rules (fun x g => Bound J C x g ∧ Bound J C (-x) (star g)) _ _ _ _ a d hd
  · exact ⟨hz,by simpa using hz⟩
  · rintro x g ⟨hb,he⟩
    exact ⟨hp _ _ hb,by simpa only [neg_add_rev,neg_add,neg_one_mul,star_mul,hi,show gi=iunit from rfl,neg_neg,star_neg,mul_comm,add_comm,sub_eq_add_neg] using hm (-x) (star g) he⟩
  · rintro x g ⟨hb,he⟩
    exact ⟨hm _ _ hb,by simpa only [neg_add_rev,neg_add,neg_one_mul,star_mul,hi,show gi=iunit from rfl,neg_neg,star_neg,mul_comm,add_comm,sub_eq_add_neg] using hp (-x) (star g) he⟩
  · rintro x hx g ⟨hb,he⟩
    exact ⟨hw _ hx _ hb,by simpa [div_eq_mul_inv] using hw (-x) (neg_ne_zero.mpr hx) _ he⟩

end TunnellCuspEuclid
end

section
/- The integer bottom row and its residue-class parametrization in the weight-one
Rankin Eisenstein family. -/
namespace TunnellRankinEisenstein
open Complex TunnellCMRegularized Filter Set Finset
open UpperHalfPlane hiding I
open scoped Topology ComplexConjugate
noncomputable section

def combine (N : ℕ) [NeZero N] : ZMod N × (ℤ×ℤ) ≃ ℤ×ℤ :=
  (Equiv.prodAssoc _ _ _).symm.trans <|
    (((Equiv.prodComm _ _).trans <| ((Equiv.refl ℤ).prodCongr (ZMod.finEquiv N).symm.toEquiv).trans
      (Int.divModEquiv N).symm).prodCongr (Equiv.refl ℤ)).trans (Equiv.prodComm _ _)

lemma combine_apply (N : ℕ) [NeZero N] (r : ZMod N) (j c : ℤ) :
    combine N (r,j,c) = (c,j*(N:ℤ)+(r.val:ℤ)) := by
  change (c,(Int.divModEquiv N).symm (j,(ZMod.finEquiv N).symm r))=_
  rw [Int.divModEquiv_symm_apply]
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

def coordSum {N k : ℕ} [NeZero N] [NeZero k] (z : ℍ) (r : ZMod N) (s : ℂ) (p : ℤ×ℤ) :=
  kernel s ((p.1:ℂ)+(p.2:ℂ)*((k:ℂ)*conj (z:ℂ))+offset r)

lemma coordinate_summable {N k : ℕ} [NeZero N] [NeZero k] (z : ℍ) (r : ZMod N) {s : ℂ} (hs : 3/2<s.re) :
    Summable (coordSum (k:=k) z r s) := by
  let e := (periods k z).latticeEquivProd.symm.toEquiv
  have h := e.summable_iff.mpr (shifted_summable (periods k z) (offset r) s hs)
  apply h.congr
  intro p
  change kernel s (((periods k z).latticeEquivProd.symm p:ℂ)+offset r)=_
  rw [PeriodPair.latticeEquiv_symm_apply]
  simp [periods,coordSum]

def physicalTerm {N k : ℕ} (χ : DirichletCharacter ℂ N) (z : ℍ) (s : ℂ) (p : ℤ×ℤ) :=
  χ (p.2:ZMod N)*kernel s ((N:ℂ)*k*p.1*conj (z:ℂ)+(p.2:ℂ))

lemma physical_lattice {N k : ℕ} [NeZero N] [NeZero k] (χ : DirichletCharacter ℂ N) (z : ℍ)
    {s : ℂ} (hs : 3/2<s.re) : HasSum (physicalTerm (k:=k) χ z s)
      (kernel s (N:ℂ)*regular N k χ z s) := by
  let F (p : ZMod N × (ℤ×ℤ)) := kernel s (N:ℂ)*χ p.1*coordSum (k:=k) z p.1 s p.2
  have hsum : Summable F := by
    apply Summable.of_norm
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    exact ⟨fun r => (((coordinate_summable (k:=k) z r hs).mul_left (kernel s (N:ℂ)*χ r)).norm),(hasSum_fintype _).summable⟩
  apply (combine N).hasSum_iff.mp
  have hh : ∑' p,F p = kernel s (N:ℂ)*regular N k χ z s := by
    rw [hsum.tsum_prod,tsum_fintype,regular_large _ _ _ _ hs,mul_sum]
    apply sum_congr rfl
    intro r _
    simp [F,coordSum,offset,tsum_mul_left,mul_assoc]
  rw [←hh]
  apply hsum.hasSum.congr_fun
  rintro ⟨r,j,c⟩
  change physicalTerm (k:=k) χ z s (combine N (r,j,c))=_
  rw [combine_apply]
  have he : ((j*(N:ℤ)+(r.val:ℤ):ℤ):ZMod N)=r := by push_cast; simp
  simp only [physicalTerm,he,F,coordSum,offset,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  rw [mul_comm (kernel s (N:ℂ)) (χ r),mul_assoc (χ r),←kernel_mul]
  congr 2
  have hN : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  field_simp
  ring

end
end TunnellRankinEisenstein
end

section
/- The modular transformation of the actual regularized Eisenstein family. -/
namespace TunnellRankinEisenstein
open Complex TunnellCMRegularized Matrix MatrixGroups CongruenceSubgroup ModularGroup Set Filter
open UpperHalfPlane hiding I
open scoped ComplexConjugate Topology
noncomputable section

def rowMove (L a b c e : ℤ) (h : a*e-L*b*c=1) : (ℤ×ℤ) ≃ (ℤ×ℤ) where
  toFun p := (a*p.1+c*p.2,L*b*p.1+e*p.2)
  invFun p := (e*p.1-c*p.2,-L*b*p.1+a*p.2)
  left_inv p := by ext <;> dsimp <;> first | linear_combination p.1*h | linear_combination p.2*h
  right_inv p := by ext <;> dsimp <;> first | linear_combination p.1*h | linear_combination p.2*h

lemma height_kernel {y : ℝ} (hy : 0<y) {j : ℂ} (hj : j≠0) (s : ℂ) :
    ((y/‖j‖^2:ℝ):ℂ)^(s-1) = (y:ℂ)^(s-1)*(j*kernel s (conj j)) := by
  have hu := norm_pos_iff.mpr hj
  have hn : (‖j‖:ℂ)≠0 := ofReal_ne_zero.mpr hu.ne'
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hy.le (sq_nonneg _) (s-1),
    kernel,Complex.norm_conj,←mul_assoc j,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_pow]
  have h : ((‖j‖:ℂ)^2)^(s-1) = exp (((Real.log ‖j‖:ℝ):ℂ)*(2*(s-1))) := by
    rw [←Complex.ofReal_pow,Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_ne_zero 2 hu.ne')),
      ←Complex.ofReal_log (sq_nonneg _),Real.log_pow]
    push_cast
    congr 1
    ring
  rw [h,div_eq_mul_inv,←Complex.exp_neg]
  congr 1
  nth_rw 2 [←Real.exp_log hu]
  rw [Complex.ofReal_exp,←Complex.exp_nat_mul,←Complex.exp_add]
  congr 1
  ring

lemma scalar_reindex {α : Type*} (r : α ≃ α) (f g : α→ℂ) (a : ℂ)
    (h : ∀ x, a*f x=g (r x)) : a*(∑' x,f x)=∑' x,g x := by
  rw [← tsum_mul_left]
  exact (tsum_congr h).trans (r.tsum_eq g)

lemma scalar_action (u v J D K A B : ℂ) (h₁ : v=u*(J*K)) (h₂ : (D*K)*B=A) :
    D*(v*B) = J*(u*A) := by rw [h₁,←h₂]; ring

end
end TunnellRankinEisenstein
end

section
/- The physically normalized analytic Eisenstein family and its full-class theta value. -/
namespace TunnellRankinEisenstein
open Complex TunnellCMRegularized TunnellRankin TunnellShell TunnellRankinCotangent TunnellClassThetaMellin TunnellFullClassTheta
open UpperHalfPlane hiding I

noncomputable section

def eisenstein {N k : ℕ} [NeZero N] [NeZero k] (χ : DirichletCharacter ℂ N) (z : ℍ) (s : ℂ) :=
    (z.im:ℂ)^(s-1) * kernel s (N:ℂ) * regular N k χ z s

lemma eisenstein_analytic {N k : ℕ} [NeZero N] [NeZero k] (χ : DirichletCharacter ℂ N) (z : ℍ) :
    AnalyticOnNhd ℂ (eisenstein (k:=k) χ z) domain := by
  intro s hs
  apply AnalyticAt.mul _ (regular_analytic N k χ z s hs)
  apply AnalyticAt.mul _ ((kernel_differentiable _).analyticAt _)
  have hp : (z.im:ℂ)≠0 := by exact_mod_cast z.im_pos.ne'
  apply Differentiable.analyticAt (f:=fun s : ℂ => (z.im:ℂ)^(s-1))
  exact (differentiable_id.sub_const 1).const_cpow (.inl hp)

/- The eigen-Eisenstein series specializes to the *full* class theta, with the
same constant of proportionality for its zero and nonzero Fourier coefficients. -/
theorem eisenstein_one {d k : ℕ} [NeZero k] {b : Triple} (hs : Squarefree (2*d)) (hd : d%4=1)
    (hb : b∈shell (2*d)) (z : ℍ) :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    eisenstein (k:=k) (negCharacter d (by omega)) z 1=
      (2*Real.pi/(v d:ℂ))*full hs (by omega) hb (multiple ⟨k,NeZero.pos k⟩ z) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  have hc := class_number hs (by omega) hb hd
  have hg := gauss_value hs (by omega) hb hd
  have hv := v_pos (show 0<d by omega)
  have hV : (v d:ℂ)≠0 := by exact_mod_cast hv.ne'
  have hv2 : (v d:ℂ)^2 = ((4*(2*d):ℕ):ℂ) := by exact_mod_cast v_sq d
  letI := classFintype hs (by omega) hb
  rw [eisenstein,sub_self,Complex.cpow_zero,one_mul,kernel_one,regular_central hd hs.of_mul_right,
    full_expansion hs (by omega) hb]
  change _=2*Real.pi/(v d:ℂ)*((Fintype.card _:ℂ)+_)
  simp only [map_inv₀,map_natCast,hg,← Nat.card_eq_fintype_card,←hv2]
  change _=2*Real.pi/(v d:ℂ)*(hclass (b:=b)+_)
  change (v d:ℂ)*((negCharacter d (by omega)).LFunction 1)=Real.pi*hclass (b:=b) at hc
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  rw [show hclass (b:=b)=(v d:ℂ)*(negCharacter d (by omega)).LFunction 1/Real.pi from (eq_div_iff hp).mpr (by simpa [mul_comm] using hc.symm)]
  simp only [map_pow,Complex.conj_ofReal]
  field_simp [hV,hp]
  ring_nf
  rw [Complex.I_sq]
  ring
end
end TunnellRankinEisenstein
end

section
/- The modular transformation of the actual regularized Eisenstein family. -/
namespace TunnellRankinEisenstein
open Complex TunnellCMRegularized Matrix MatrixGroups CongruenceSubgroup ModularGroup Set Filter
open UpperHalfPlane hiding I
open scoped ComplexConjugate Topology
noncomputable section

set_option maxHeartbeats 800000 in
lemma action_large {N k : ℕ} [NeZero N] [NeZero k] (χ : DirichletCharacter ℂ N) (z : ℍ)
    (g : SL(2,ℤ)) (hg : g∈Gamma0 (N*k)) {s : ℂ} (hs : 3/2<s.re) :
    χ (g 1 1:ZMod N)*eisenstein (k:=k) χ (g • z) s=denom g z*eisenstein (k:=k) χ z s := by
  obtain ⟨c,hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hg)
  let a := g 0 0
  let b := g 0 1
  let e := g 1 1
  let L : ℤ := (N*k:ℕ)
  have hd : a*e-L*b*c=1 := by
    have H := g.property
    rw [Matrix.det_fin_two] at H
    dsimp [a,b,e,L]
    rw [hc,Nat.cast_mul] at H
    linear_combination H
  let R := rowMove L a b c e hd
  let J := denom g z
  have hJ : J≠0 := denom_ne_zero _ _
  have hHt : (((g • z).im:ℝ):ℂ)^(s-1) = (z.im:ℂ)^(s-1)*(J*kernel s (conj J)) := by
    rw [ModularGroup.im_smul_eq_div_normSq,Complex.normSq_eq_norm_sq]
    exact height_kernel z.im_pos hJ s
  have hR (p : ℤ×ℤ) :
      χ (e:ZMod N)*kernel s (conj J)*physicalTerm (k:=k) χ (g • z) s p =
        physicalTerm (k:=k) χ z s (R p) := by
    have he : ((R p).2:ZMod N) = (e:ZMod N)*(p.2:ZMod N) := by simp [R,rowMove,L]
    have H : (conj J)*((N:ℂ)*k*(p.1:ℂ)*conj ((g • z:ℍ):ℂ)+(p.2:ℂ)) =
        (N:ℂ)*k*((R p).1:ℂ)*conj (z:ℂ)+((R p).2:ℂ) := by
      have eJ : J=(g 1 0:ℂ)*(z:ℂ)+(g 1 1:ℂ) := by simp [J,ModularGroup.denom_apply]
      have em : ((g • z:ℍ):ℂ)=((a:ℂ)*(z:ℂ)+(b:ℂ))/J := by
        rw [UpperHalfPlane.coe_specialLinearGroup_apply,eJ]
        simp [a,b]
      have hj' : conj J≠0 := by simpa using hJ
      rw [em,map_div₀]
      field_simp [hj']
      simp only [eJ,conj_ofReal,map_add,map_mul,map_intCast,map_natCast,R,rowMove,Equiv.coe_fn_mk,a,b,e,L,
        Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_mul,hc]
      ring
    simp only [physicalTerm,he,map_mul]
    rw [←H,kernel_mul]
    ring
  have H := (physical_lattice (k:=k) χ (g • z) hs).tsum_eq
  have H' := (physical_lattice (k:=k) χ z hs).tsum_eq
  have hh := scalar_reindex R (physicalTerm (k:=k) χ (g • z) s) (physicalTerm (k:=k) χ z s)
    (χ (e:ZMod N)*kernel s (conj J)) hR
  have he := scalar_action ((z.im:ℂ)^(s-1)) ((((g • z).im:ℝ):ℂ)^(s-1)) J (χ (e:ZMod N))
    (kernel s (conj J)) (∑' p,physicalTerm (k:=k) χ z s p) (∑' p,physicalTerm (k:=k) χ (g • z) s p) hHt hh
  rw [H,H'] at he
  simpa only [eisenstein,mul_assoc] using he

theorem action {N k : ℕ} [NeZero N] [NeZero k] (χ : DirichletCharacter ℂ N) (z : ℍ)
    (g : SL(2,ℤ)) (hg : g∈Gamma0 (N*k)) :
    EqOn (fun s => χ (g 1 1:ZMod N)*eisenstein (k:=k) χ (g • z) s)
      (fun s => denom g z*eisenstein (k:=k) χ z s) domain := by
  apply (analyticOnNhd_const.mul (eisenstein_analytic _ _)).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const.mul (eisenstein_analytic _ _)) (convex_halfSpace_re_gt _).isPreconnected
    (z₀:=2) (by norm_num [domain])
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (3:ℝ)/2<(2:ℂ).re by norm_num)] with s hs
  exact action_large _ _ _ hg hs

end
end TunnellRankinEisenstein
end

section
/- Primitive bottom-row unfolding of the weight-one Eisenstein series. -/
namespace TunnellRankinEisenstein
open Complex TunnellCMRegularized EisensteinSeries Set Finset
open UpperHalfPlane hiding I
open scoped Topology ComplexConjugate
noncomputable section

abbrev Primitives := gammaSet 1 1 0

lemma factor_gcd (F : (Fin 2→ℤ)→ℂ) (C : ℕ→ℂ) (hC : C 0=0)
    (hm : ∀ (g : ℕ) (v : Fin 2→ℤ), F ((g:ℤ) • v) = C g * F v) (hS : Summable F) :
    ∑' v,F v = (∑' g,C g)*(∑' v : Primitives,F v) := by
  have H : Summable (fun p : (Σ g : ℕ, gammaSet 1 g 0) => F (gammaSetDivGcdSigmaEquiv.symm p)) :=
    gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr hS
  rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq F,H.tsum_sigma,←tsum_mul_right]
  apply tsum_congr
  intro g
  simp only [gammaSetDivGcdSigmaEquiv_symm_eq]
  by_cases hg : g=0
  · subst g
    simp only [hC,zero_mul]
    have hh (v : gammaSet 1 0 0) : F v=0 := by
      calc
        F v=F ((0:ℤ) • divIntMap 0 v) := congrArg F (gammaSet_eq_gcd_mul_divIntMap v.property)
        _ = C 0 * F (divIntMap 0 v) := hm 0 _
        _ = 0 := by rw [hC,zero_mul]
    simp only [hh,tsum_zero]
  · haveI : NeZero g := ⟨hg⟩
    rw [← (gammaSetDivGcdEquiv g).tsum_eq (fun v : Primitives => F v),← tsum_mul_left]
    apply tsum_congr
    intro v
    calc
      F v = F ((g:ℤ) • divIntMap g v) := congrArg F (gammaSet_eq_gcd_mul_divIntMap v.property)
      _ = C g * F (gammaSetDivGcdEquiv g v) := hm _ _

def nativeTerm {N k : ℕ} (χ : DirichletCharacter ℂ N) (z : ℍ) (s : ℂ) (v : Fin 2→ℤ) :=
    physicalTerm (k:=k) χ z s (v 0,v 1)

lemma primitive_factor {N k : ℕ} [NeZero N] [NeZero k] (χ : DirichletCharacter ℂ N) (z : ℍ) {s : ℂ}
    (hs : 3/2<s.re) : eisenstein (k:=k) χ z s =
    (z.im:ℂ)^(s-1) * χ.LFunction (2*s-1) * ∑' v : Primitives, nativeTerm (k:=k) χ z s v := by
  let C (g : ℕ) := χ g * kernel s (g:ℂ)
  let F := nativeTerm (k:=k) χ z s
  have H : HasSum F (kernel s (N:ℂ)*regular N k χ z s) :=
    (finTwoArrowEquiv ℤ).hasSum_iff.mpr (physical_lattice χ z hs)
  have hm (g : ℕ) (v : Fin 2→ℤ) : F ((g:ℤ) • v) = C g*F v := by
    have he (i : Fin 2) : ((g:ℤ) • v) i=(g:ℤ)*v i := by simp [Pi.smul_apply]
    simp only [F,nativeTerm,physicalTerm,he,Int.cast_mul,Int.cast_natCast,
      map_mul,C]
    rw [show (N:ℂ)*k*((g:ℂ)*(v 0:ℂ))*conj (z:ℂ)+(g:ℂ)*(v 1:ℂ) =
      (g:ℂ)*((N:ℂ)*k*(v 0:ℂ)*conj (z:ℂ)+(v 1:ℂ)) by ring,kernel_mul]
    ring
  have h0 : C 0=0 := by simp [C,kernel]
  have hs' : 1<(2*s-1).re := by simp [Complex.mul_re]; linarith
  have hD : χ.LFunction (2*s-1)=∑' g,C g := by
    rw [χ.LFunction_eq_LSeries hs',LSeries]
    apply tsum_congr
    intro g
    rw [LSeries.term_of_ne_zero' (by intro h; rw [h] at hs'; norm_num at hs')]
    by_cases hg : g=0
    · subst g
      simp [C,kernel,Complex.zero_cpow (show 2*s-1≠0 by intro h; rw [h] at hs'; norm_num at hs')]
    · have hp : 0<(g:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hg)
      dsimp only [C]
      rw [←Complex.ofReal_natCast, kernel_real,
        sign_pos hp,SignType.coe_one,abs_of_pos hp,Complex.ofReal_natCast]
      ring
  rw [eisenstein,mul_assoc,←H.tsum_eq,factor_gcd F C h0 hm H.summable,←hD]
  dsimp [F]
  ring
end
end TunnellRankinEisenstein
end

section
/- Replacing primitive lattice parameters by actual bottom rows of Γ₀(Nk). -/
namespace TunnellRankinEisenstein
open Complex Matrix MatrixGroups ModularGroup CongruenceSubgroup EisensteinSeries TunnellCMRegularized Set
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

def Rows (L : ℕ) := {p : ℤ×ℤ // (L:ℤ)∣p.1 ∧ IsCoprime p.1 p.2}
def Active (N k : ℕ) (v : Primitives) := IsCoprime (((N*k:ℕ):ℤ)*(v.val 0)) (v.val 1)

def rowMap (N k : ℕ) (v : {v : Primitives // Active N k v}) : Rows (N*k) :=
  ⟨(((N*k:ℕ):ℤ)*(v.val.val 0),v.val.val 1),dvd_mul_right _ _,v.property⟩

lemma rowMap_bijective (N k : ℕ) [NeZero N] [NeZero k] : Function.Bijective (rowMap N k) := by
  have hL : ((N*k:ℕ):ℤ)≠0 := by exact_mod_cast mul_ne_zero (NeZero.ne N) (NeZero.ne k)
  constructor
  · intro v w h
    have h₀ := congrArg (fun x : Rows (N*k) => x.val.1) h
    have h₁ := congrArg (fun x : Rows (N*k) => x.val.2) h
    apply Subtype.ext; apply Subtype.ext
    funext i
    fin_cases i
    · exact mul_left_cancel₀ hL h₀
    · exact h₁
  · rintro ⟨⟨c,e⟩,⟨⟨b,hb⟩,hcop⟩⟩
    have hb' : c=((N*k:ℕ):ℤ)*b := hb
    subst c
    let v : Primitives := ⟨![b,e],(mem_gammaSet_one _).mpr (hcop.of_isCoprime_of_dvd_left (dvd_mul_left _ _))⟩
    exact ⟨⟨v,hcop⟩,rfl⟩

def rowTerm {N L : ℕ} (χ : DirichletCharacter ℂ N) (z : ℍ) (s : ℂ) (v : Rows L) :=
  χ (v.val.2:ZMod N)*kernel s ((v.val.1:ℂ)*conj (z:ℂ)+(v.val.2:ℂ))

lemma rows_sum {N k : ℕ} [NeZero N] [NeZero k] (hk : k∣N) (χ : DirichletCharacter ℂ N)
    (z : ℍ) (s : ℂ) :
    (∑' v : Primitives,nativeTerm (k:=k) χ z s v)=∑' v : Rows (N*k),rowTerm χ z s v := by
  let f := fun v : Primitives => nativeTerm (k:=k) χ z s v
  have ha (v : Primitives) (hv : f v≠0) : Active N k v := by
    have hχ : χ (v.val 1:ZMod N)≠0 := by intro h; exact hv (by simp [f,nativeTerm,physicalTerm,h])
    have hco := (ZMod.coe_int_isUnit_iff_isCoprime _ _).mp (by
      by_contra h; exact hχ (χ.map_nonunit h))
    have hp := (mem_gammaSet_one _).mp v.property
    exact (by
      change IsCoprime (((N*k:ℕ):ℤ)*(v.val 0)) (v.val 1)
      rw [Nat.cast_mul]; exact (hco.mul_left (hco.of_isCoprime_of_dvd_left (by exact_mod_cast hk))).mul_left hp)
  have e1 : (∑' w : {v : Primitives // Active N k v}, f w)=∑' v,f v :=
    Subtype.val_injective.tsum_eq (fun v hv => ⟨⟨v,ha v hv⟩,rfl⟩)
  change (∑' v,f v)=_
  rw [←e1,←(Equiv.ofBijective (rowMap N k) (rowMap_bijective N k)).tsum_eq (rowTerm χ z s)]
  apply tsum_congr
  rintro ⟨v,hv⟩
  simp [rowTerm,f,nativeTerm,physicalTerm,Equiv.ofBijective_apply,rowMap,mul_assoc]

def matrixRow {L : ℕ} (g : Gamma0 L) : Rows L :=
  ⟨(g.val 1 0,g.val 1 1),(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp g.property),bottom_row_coprime g.val⟩

lemma matrixRow_surjective (L : ℕ) : Function.Surjective (matrixRow (L:=L)) := by
  rintro ⟨⟨c,e⟩,hL,h⟩
  obtain ⟨g,hc,he⟩ := h.exists_SL2_row 1
  have hg : g∈Gamma0 L := Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hc.symm ▸ hL))
  exact ⟨⟨g,hg⟩,Subtype.ext (Prod.ext hc he)⟩

end
end TunnellRankinEisenstein
end

section
/- A reduction proof for Γ₀(2) in the coordinates (a,b,c,d) representing
the integer matrix with rows (a,b) and (2c,d). -/
namespace TunnellEtaLevel

lemma centered (b a : ℤ) (ha : a≠0) :
    ∃ n : ℤ, 2*(b+n*a).natAbs≤a.natAbs := by
  have pos : 0<a.natAbs := Int.natAbs_pos.mpr ha
  let r := b.bmod a.natAbs
  let q := b.bdiv a.natAbs
  have bound := (Int.bmod_eq_iff (a:=b) pos).mp (rfl : b.bmod a.natAbs=r)
  have he : r+(a.natAbs:ℤ)*q=b := by simpa [q,r,mul_comm] using Int.bmod_add_bdiv b a.natAbs
  by_cases h : 0≤a
  · have ee : (a.natAbs:ℤ)=a := by omega
    rw [ee] at he
    refine ⟨-q,?_⟩
    rw [show b+ -q*a=r by linear_combination -he]
    omega
  · have ee : (a.natAbs:ℤ)= -a := by omega
    rw [ee] at he
    refine ⟨q,?_⟩
    rw [show b+q*a=r by linear_combination -he]
    omega

theorem gamma_two_induction (P : ℤ→ℤ→ℤ→ℤ→Prop)
    (base : ∀ a b d, a*d=1 → P a b 0 d)
    (T : ∀ n a b c d, P (a+2*n*c) (b+n*d) c d → P a b c d)
    (U : ∀ n a b c d, P a b (c+n*a) (d+2*n*b) → P a b c d)
    {a b c d : ℤ} (det : a*d-2*b*c=1) : P a b c d := by
  suffices ∀ m : ℕ, ∀ a b c d : ℤ, a.natAbs=m → a*d-2*b*c=1 → P a b c d by exact this _ _ _ _ _ rfl det
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a b c d hm det
    have ha : a≠0 := by
      intro h
      have he : 2*(b*c) = -1 := by rw [h] at det; linear_combination -det
      omega
    obtain ⟨n,hn⟩ := centered c a ha
    let r := c+n*a
    let e := d+2*n*b
    apply U n
    change P a b r e
    have det' : a*e-2*b*r=1 := by dsimp [e,r]; linear_combination det
    by_cases hr : r=0
    · subst_vars; rw [hr]; apply base; simpa [hr] using det'
    · obtain ⟨j,hj⟩ := centered a (2*r) (mul_ne_zero (by decide) hr)
      apply T j
      let u := a+2*j*r
      have hu : u.natAbs < m := by
        change 2*r.natAbs≤a.natAbs at hn
        rw [show a+j*(2*r)=u by dsimp [u]; ring,Int.natAbs_mul] at hj
        norm_num at hj
        omega
      apply ih _ hu _ _ _ _ rfl
      linear_combination det'

end TunnellEtaLevel
end

section
/- Translation and lower unipotent laws for the level-two eta product. -/
namespace TunnellEtaLevel
open Complex TunnellFricke Matrix MatrixGroups ModularGroup
open UpperHalfPlane hiding I
open scoped ModularForm
noncomputable section

lemma trans_one (z : ℂ) : h (z+1)=I*h z := by
  rw [present,q_T,disk_rot,present z,mul_assoc]

lemma trans (n : ℤ) (z : ℂ) : h (z+(n:ℂ))=I^n*h z := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    simpa [zpow_add₀ I_ne_zero,add_assoc,mul_left_comm,mul_comm,mul_assoc] using
      (trans_one (z+k)).trans (congrArg (I*·) ih)
  | pred k ih =>
    let m : ℤ := -(k:ℤ)
    change h (z+(m:ℂ))=I^m*h z at ih
    change h (z+((m-1:ℤ):ℂ))=I^(m-1)*h z
    have he := trans_one (z+(m:ℂ)-1)
    rw [sub_add_cancel,ih] at he
    simp only [Int.cast_sub,Int.cast_one]
    rw [show z+((m:ℂ)-1)=z+(m:ℂ)-1 by ring]
    apply mul_left_cancel₀ I_ne_zero
    rw [←he,zpow_sub₀ I_ne_zero,zpow_one]
    field_simp

lemma lower (n : ℤ) (z : ℍ) :
    h ((z:ℂ)/(2*(n:ℂ)*z+1))=I^(-n)*(2*(n:ℂ)*z+1)^2*h z := by
  let w := W (z:ℂ) + ((-n:ℤ):ℂ)
  have hw : 0<w.im := by simpa [w] using W_mem z.im_pos
  have hw₀ := ne_zero (⟨w,hw⟩:ℍ)
  have hden : 2*(n:ℂ)*z+1≠0 := by
    have H := linear_ne_zero (cd:=![(2*(n:ℝ)),1]) z (by
      intro he; have hh := congrFun he 1; norm_num at hh)
    simpa using H
  have hW : W w=(z:ℂ)/(2*(n:ℂ)*z+1) := by
    rw [W,div_eq_div_iff (mul_ne_zero two_ne_zero hw₀) hden]
    dsimp [w,W]; push_cast; field_simp [z.ne_zero]; ring
  rw [←hW,h_fricke _ hw,show h w=I^(-n)*h (W z) from trans (-n) _,h_fricke _ z.im_pos]
  dsimp [w,W]; push_cast; field_simp [z.ne_zero]; ring

def mat (a b c d : ℤ) (hd : a*d-2*b*c=1) : SL(2,ℤ) :=
  ⟨!![a,b;2*c,d],by simp [Matrix.det_fin_two]; linear_combination hd⟩

def H (z : ℍ) := h (z:ℂ)

lemma slash_mat (a b c d : ℤ) (hd : a*d-2*b*c=1) (z : ℍ) :
    (H ∣[(2:ℤ)] (mat a b c d hd)) z =
      h (((a:ℂ)*z+b)/(2*(c:ℂ)*z+d))*(2*(c:ℂ)*z+d)^(-(2:ℤ)) := by
  rw [ModularForm.SL_slash_apply]
  unfold H
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,ModularGroup.denom_apply]
  simp [mat]

lemma upper_slash (n : ℤ) : H ∣[(2:ℤ)] (mat 1 n 0 1 (by ring)) = I^n • H := by
  ext z : 1
  simp [slash_mat,trans,H]

lemma lower_slash (n : ℤ) : H ∣[(2:ℤ)] (mat 1 0 n 1 (by ring)) = I^(-n) • H := by
  ext z : 1
  rw [slash_mat]
  simp only [Int.cast_one,one_mul,Int.cast_zero,add_zero,lower,Pi.smul_apply,smul_eq_mul,H,
    _root_.zpow_neg,zpow_ofNat]
  have hden : 2*(n:ℂ)*z+1≠0 := by
    have HH := linear_ne_zero (cd:=![(2*(n:ℝ)),1]) z (by
      intro he; have hh := congrFun he 1; norm_num at hh)
    simpa using HH
  field_simp [hden]

lemma phase {u v : ℤ} (e : (u:ZMod 4)=(v:ZMod 4)) : I^u=I^v := by
  rw [I_zpow_eq_zpow_mod u,I_zpow_eq_zpow_mod v]
  exact congrArg (I^·) ((ZMod.intCast_eq_intCast_iff' u v 4).mp e)

set_option maxRecDepth 8000 in
lemma phase_upper (a b c d n : ℤ) (det : a*d-2*b*c=1) :
    I^((a+2*n*c)*(b+n*d-c))=I^n*I^(a*(b-c)) := by
  rw [←zpow_add₀ I_ne_zero]
  apply phase
  push_cast
  have t : ∀ a b c d n : ZMod 4, a*d-2*b*c=1 →
      (a+2*n*c)*(b+n*d-c)=n+a*(b-c) := by decide
  apply t a b c d n
  simpa using congrArg (fun x : ℤ => (x:ZMod 4)) det

set_option maxRecDepth 8000 in
lemma phase_lower (a b c d n : ℤ) (det : a*d-2*b*c=1) :
    I^(a*(b-(c+n*a)))=I^(-n)*I^(a*(b-c)) := by
  rw [←zpow_add₀ I_ne_zero]
  apply phase
  push_cast
  have t : ∀ a b c d n : ZMod 4, a*d-2*b*c=1 →
      a*(b-(c+n*a))= -n+a*(b-c) := by decide
  apply t a b c d n
  simpa using congrArg (fun x : ℤ => (x:ZMod 4)) det
end
end TunnellEtaLevel
end

section
/- The conductor-32 eta product transforms with trivial character on Γ₀(32). -/
namespace TunnellEtaLevel
open Complex TunnellFricke Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellEtaValue
open UpperHalfPlane hiding I
open scoped ModularForm
noncomputable section

lemma left_upper (a b c d n : ℤ) (hd : a*d-2*b*c=1) :
    mat 1 n 0 1 (by ring)*mat a b c d hd=
      mat (a+2*n*c) (b+n*d) c d (by linear_combination hd) := by
  apply Subtype.ext
  change !![(1:ℤ),n;0,1]*!![a,b;2*c,d]=!![a+2*n*c,b+n*d;2*c,d]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two] <;> ring

lemma left_lower (a b c d n : ℤ) (hd : a*d-2*b*c=1) :
    mat 1 0 n 1 (by ring)*mat a b c d hd=
      mat a b (c+n*a) (d+2*n*b) (by linear_combination hd) := by
  apply Subtype.ext
  change !![(1:ℤ),0;2*n,1]*!![a,b;2*c,d]=!![a,b;2*(c+n*a),d+2*n*b]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two] <;> ring

lemma cancel_phase (w : ℂ) (nw : w≠0) (f g : ℍ → ℂ) (e : w • f = w • g) : f=g := by
  ext z : 1
  exact mul_left_cancel₀ nw (congrFun e z)

lemma gamma_two (a b c d : ℤ) (hd : a*d-2*b*c=1) :
    H ∣[(2:ℤ)] (mat a b c d hd)= I^(a*(b-c)) • H := by
  let P (a b c d : ℤ) := ∀ hd : a*d-2*b*c=1,
    H ∣[(2:ℤ)] (mat a b c d hd)=I^(a*(b-c)) • H
  suffices P a b c d from this hd
  apply gamma_two_induction P _ _ _ hd
  · intro a b d e hd
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simpa using upper_slash b
    · ext z : 1
      rw [slash_mat]
      simp [H,show -(z:ℂ)+(b:ℂ) = -(z+(-b:ℤ)) by push_cast; ring,trans]
      rw [show ((b:ℂ)+ -(z:ℂ)) / -1=(z:ℂ)+((-b:ℤ):ℂ) by push_cast; ring,trans,_root_.zpow_neg]
  · intro n a b c d ih hd
    have he := ih (by linear_combination hd)
    rw [←left_upper a b c d n hd,SlashAction.slash_mul,upper_slash,ModularForm.SL_smul_slash,phase_upper _ _ _ _ _ hd,mul_smul] at he
    exact cancel_phase _ (zpow_ne_zero _ I_ne_zero) _ _ he
  · intro n a b c d ih hd
    have he := ih (by linear_combination hd)
    rw [←left_lower a b c d n hd,SlashAction.slash_mul,lower_slash,ModularForm.SL_smul_slash,phase_lower _ _ _ _ _ hd,mul_smul] at he
    exact cancel_phase _ (zpow_ne_zero _ I_ne_zero) _ _ he

lemma physical (z : ℍ) : etaValue z = h (4*(z:ℂ)) := by
  simp [etaValue,h,show 2*(4*(z:ℂ))=8*z by ring]

theorem eta_level (g : SL(2,ℤ)) (hg : g∈Gamma0 32) (z : ℍ) :
    etaValue (g • z)=denom g z^2*etaValue z := by
  obtain ⟨c,hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hg)
  let a := g 0 0
  let b := g 0 1
  let d := g 1 1
  have hdet : a*d-2*(4*b)*(4*c)=1 := by
    have e := g.property
    rw [Matrix.det_fin_two,hc] at e
    dsimp [a,b,d]; norm_num at e; linear_combination e
  let w : ℍ := ⟨4*(z:ℂ),by simpa [Complex.mul_im] using z.im_pos⟩
  have ee := congrFun (gamma_two a (4*b) (4*c) d hdet) w
  have ep : I^(a*(4*b-4*c))=1 := by
    rw [show a*(4*b-4*c)=4*(a*(b-c)) by ring,_root_.zpow_mul]
    simp [zpow_ofNat,I_pow_four]
  rw [slash_mat,ep,one_smul] at ee
  have hd : denom g z=2*((4*c:ℤ):ℂ)*(w:ℂ)+(d:ℂ) := by
    simp [ModularGroup.denom_apply,hc,w,d]; ring
  have he : 4*((g • z:ℍ):ℂ)=((a:ℂ)*(w:ℂ)+((4*b:ℤ):ℂ))/denom g z := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [ModularGroup.denom_apply,a,b,w,mul_div_assoc',mul_add]; ring
  rw [physical,physical,he,hd]
  change h _ * _ = h (w:ℂ) at ee
  have hn := hd ▸ denom_ne_zero g z
  rw [_root_.zpow_neg,zpow_ofNat,←div_eq_mul_inv,div_eq_iff (pow_ne_zero _ hn)] at ee
  simpa [mul_comm,w] using ee
end
end TunnellEtaLevel
end

section
/- Uniqueness of analytic continuation and the normalized central Mellin integral. -/

namespace TunnellMellin

open Filter Set Complex UpperHalfPlane MatrixGroups MeasureTheory
open scoped Topology ModularForm

theorem entire_unique {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (B : ℝ) (h : ∀ x : ℝ, B<x → f x = g x) : f = g := by
  let a : ℝ := B+1
  have hm : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] a) (𝓝[≠] (a:ℂ)) := by
    exact continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ => by simp_all)
  apply hf.eq_of_frequently_eq hg (hm.frequently ?_)
  apply Filter.Eventually.frequently
  filter_upwards [(eventually_gt_nhds (show B<a by dsimp [a]; linarith)).filter_mono nhdsWithin_le_nhds] with x hx
  exact h x hx

theorem central_integral {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (F : CuspForm Γ 2) :
    ModularForm.L (by decide : (0:ℤ)<2) F 1 =
      (2*Real.pi:ℂ) * ∫ t in Ioi (0:ℝ), F (ofComplex (Complex.I*t)) := by
  rw [ModularForm.L,CuspForm.Λ_eq_mellin,Complex.Gammaℂ_one]
  simp [mellin, smul_eq_mul, mul_comm, div_eq_mul_inv]

end TunnellMellin
end

section
namespace TunnellBaseTranslations
open MatrixGroups UpperHalfPlane Finset

namespace TunnellTranslate

open Matrix MatrixGroups ConjAct Pointwise UpperHalfPlane ModularForm
open Matrix.GeneralLinearGroup

lemma rational_translation_map (r : ℚ) :
    (upperRightHom r).map (Rat.castHom ℝ) = upperRightHom (r : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma translate_apply {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (F : CuspForm Γ k)
    (r : ℝ) (τ : ℍ) : (CuspForm.translate F (upperRightHom r)) τ = F (r +ᵥ τ) := by
  change (⇑F ∣[k] (upperRightHom r)) τ = _
  have hact : upperRightHom r • τ = r +ᵥ τ := by
    ext
    simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, add_comm]
  simp_rw [slash_def, hact]
  simp [σ, denom, val_det_apply]

theorem exists_sum_rational_translates {ι : Type*} [Fintype ι]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hwidth : Γ.strictWidthInfty = 1)
    {k : ℤ} (F : CuspForm Γ k) (r : ι → ℚ) (c : ι → ℂ) :
    ∃ H : Subgroup (GL (Fin 2) ℝ), H.IsArithmetic ∧ H.strictWidthInfty = 1 ∧
      ∃ G : CuspForm H k, ∀ τ : ℍ, G τ = ∑ i, c i * F ((r i : ℝ) +ᵥ τ) := by
  classical
  let T (i : ι) := upperRightHom (r i : ℝ)
  let C (i : ι) := (toConjAct (T i)⁻¹) • Γ
  have hC (i : ι) : (C i).IsArithmetic := by
    have h := Subgroup.IsArithmetic.conj Γ (upperRightHom (r i))⁻¹
    simpa only [map_inv, rational_translation_map, C, T] using h
  let H := 𝒮ℒ ⊓ Finset.univ.inf C
  have hH (s : Finset ι) : (𝒮ℒ ⊓ s.inf C).IsArithmetic := by
    induction s using Finset.induction_on with
    | empty => simpa using (inferInstance : Subgroup.IsArithmetic 𝒮ℒ)
    | insert i s hi ih =>
      rw [Finset.inf_insert, inf_left_comm]
      exact @Subgroup.IsArithmetic.inter _ _ (hC i) ih
  have harith : H.IsArithmetic := hH Finset.univ
  have hHC (i : ι) : H ≤ C i := inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  have hunit : upperRightHom (1 : ℝ) ∈ Γ := by
    have h := Γ.strictWidthInfty_mem_strictPeriods
    rwa [hwidth, Subgroup.mem_strictPeriods_iff] at h
  have hcunit (i : ι) : upperRightHom (1 : ℝ) ∈ C i := by
    change upperRightHom 1 ∈ toConjAct (T i)⁻¹ • Γ
    rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
    have hcomm : T i * upperRightHom 1 = upperRightHom 1 * T i := by
      simp only [T, ← AddChar.map_add_eq_mul, add_comm]
    rwa [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hperiods : H.strictPeriods = AddSubgroup.zmultiples 1 := by
    apply le_antisymm
    · rw [← Subgroup.strictPeriods_SL2Z]
      exact fun x hx => Subgroup.mem_strictPeriods_iff.mpr
        ((Subgroup.mem_strictPeriods_iff.mp hx).1)
    · apply AddSubgroup.zmultiples_le.mpr
      apply Subgroup.mem_strictPeriods_iff.mpr
      constructor
      · have h := (AddSubgroup.mem_zmultiples (1 : ℝ))
        rwa [← Subgroup.strictPeriods_SL2Z, Subgroup.mem_strictPeriods_iff] at h
      · simpa [Finset.inf_eq_iInf] using hcunit
  have hHW : H.strictWidthInfty = 1 := by
    rw [Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty, Eq.comm,
      AddSubgroup.zmultiples_eq_zmultiples_iff
        (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero)] at hperiods
    grind [Subgroup.strictWidthInfty_nonneg]
  let restrictCusp {H Γ : Subgroup (GL (Fin 2) ℝ)} (h : H ≤ Γ) {k : ℤ} (F : CuspForm Γ k) :
      CuspForm H k := {
    toFun := F
    slash_action_eq' g hg := F.slash_action_eq' g (h hg)
    holo' := F.holo'
    zero_at_cusps' hc := F.zero_at_cusps' (hc.mono h) }
  let forms (i : ι) : CuspForm H k := restrictCusp (hHC i) (CuspForm.translate F (T i))
  refine ⟨H, harith, hHW, ∑ i, c i • forms i, ?_⟩
  intro τ
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => congrArg (c i * ·) (translate_apply F _ τ))

end TunnellTranslate

namespace TunnellTwistFourier
open UpperHalfPlane MatrixGroups
open scoped Real

lemma translated_qpow {N : ℕ} [NeZero N] (j : ZMod N) (z : ℍ) (m : ℕ) :
    Function.Periodic.qParam 1 (((-(j.val : ℝ) / (N : ℝ)) +ᵥ z : ℍ) : ℂ) ^ m =
      ZMod.stdAddChar (-(j * (m : ZMod N))) * Function.Periodic.qParam 1 (z : ℂ) ^ m := by
  have h := ZMod.stdAddChar_coe (N := N) (-((j.val : ℤ) * m))
  push_cast at h
  rw [ZMod.natCast_zmod_val] at h
  rw [h]
  simp only [Function.Periodic.qParam, UpperHalfPlane.coe_vadd, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_one, div_one,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

theorem twist_coefficients {N : ℕ} [NeZero N] (w : ZMod N → ℂ)
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ'.IsArithmetic]
    (hΓ : Γ.strictWidthInfty = 1) (hΓ' : Γ'.strictWidthInfty = 1)
    (F : CuspForm Γ 2) (G : CuspForm Γ' 2)
    (heq : ∀ z : ℍ, G z = ∑ j : ZMod N,
      (ZMod.dft.symm w) j * F ((-(j.val : ℝ) / (N : ℝ)) +ᵥ z)) (m : ℕ) :
    (qExpansion 1 G).coeff m = w (m : ZMod N) * (qExpansion 1 F).coeff m := by
  let c := ZMod.dft.symm w
  have hper : (1 : ℝ) ∈ Γ.strictPeriods := hΓ ▸ Γ.strictWidthInfty_mem_strictPeriods
  have hper' : (1 : ℝ) ∈ Γ'.strictPeriods := hΓ' ▸ Γ'.strictWidthInfty_mem_strictPeriods
  symm
  apply ModularFormClass.qExpansion_coeff_unique one_pos hper' _ m
  intro z
  rw [heq z]
  have hterm (j : ZMod N) := (ModularForm.hasSum_qExpansion F one_pos hper
    ((-(j.val : ℝ) / (N : ℝ)) +ᵥ z)).mul_left (c j)
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hterm j)
  apply hsum.congr_fun
  intro k
  simp only [translated_qpow, smul_eq_mul]
  have heval : ∑ j : ZMod N, ZMod.stdAddChar (-(j * (k : ZMod N))) * c j = w k := by
    simpa only [ZMod.dft_apply, smul_eq_mul] using congrFun (ZMod.dft.apply_symm_apply w) (k : ZMod N)
  rw [← heval, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end TunnellTwistFourier
end TunnellBaseTranslations

/- The central value of a twist as vertical integrals at rational cusps. -/

namespace TunnellModularSymbol

open TunnellBaseTranslations TunnellMellin
open MatrixGroups UpperHalfPlane MeasureTheory Set
open scoped ModularForm

lemma integrable_vertical {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (F : CuspForm Γ 2) :
    IntegrableOn (fun t : ℝ => F (ofComplex (Complex.I*t))) (Ioi 0) := by
  have h := ((CuspForm.isStrongFEPair (by decide : (0:ℤ)<2) F).hasMellin 1).1
  simpa [MellinConvergent, ModularForm.weakFEPair] using h

lemma integrable_translate {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (hw : Γ.strictWidthInfty = 1) (F : CuspForm Γ 2) (r : ℚ) :
    IntegrableOn (fun t : ℝ => F ((r:ℝ)+ᵥ ofComplex (Complex.I*t))) (Ioi 0) := by
  obtain ⟨H, hH, _, G, heq⟩ := TunnellTranslate.exists_sum_rational_translates hw F
    (fun _ : Unit => r) (fun _ => 1)
  letI := hH
  simpa [heq] using integrable_vertical G

theorem twist_central_integral {N : ℕ} [NeZero N] (w : ZMod N → ℂ)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hw : Γ.strictWidthInfty = 1)
    (F : CuspForm Γ 2) :
    ∃ (H : Subgroup (GL (Fin 2) ℝ)) (hH : H.IsArithmetic) (_ : H.strictWidthInfty = 1)
      (G : CuspForm H 2),
      (∀ m : ℕ, (qExpansion 1 G).coeff m = w m * (qExpansion 1 F).coeff m) ∧
      ModularForm.L (by decide : (0:ℤ)<2) G 1 =
        ∑ j : ZMod N, ZMod.dft.symm w j *
          ((2*Real.pi:ℂ) * ∫ t in Ioi (0:ℝ), F ((-(j.val:ℝ)/N)+ᵥ ofComplex (Complex.I*t))) := by
  obtain ⟨H,hH,hW,G,he⟩ := TunnellTranslate.exists_sum_rational_translates hw F
    (fun j : ZMod N => -(j.val:ℚ)/N) (ZMod.dft.symm w)
  letI := hH
  have he' (z : ℍ) : G z = ∑ j : ZMod N, ZMod.dft.symm w j * F ((-(j.val:ℝ)/N)+ᵥ z) := by
    simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_neg] using he z
  refine ⟨H,hH,hW,G,TunnellTwistFourier.twist_coefficients w hw hW F G he',?_⟩
  have hi (j : ZMod N) := (integrable_translate hw F (-(j.val:ℚ)/N)).const_mul (ZMod.dft.symm w j)
  rw [central_integral]
  simp_rw [he']
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  · intro j _
    simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_neg] using hi j

theorem gauss_sq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (he : χ.Even) :
    gaussSum χ ZMod.stdAddChar ^ 2 = (N:ℂ) := by
  have h (k : ZMod N) := hχ.fourierTransform_eq_inv_mul_gaussSum k
  simp only [hq.inv,he.eval_neg] at h
  have h2 := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) 1
  rw [funext h, ZMod.dft_mul_const] at h2
  dsimp only at h2
  rw [h] at h2
  simpa [pow_two,he.eval_neg] using h2

theorem primitive_weights {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (he : χ.Even) (j : ZMod N) :
    (gaussSum χ ZMod.stdAddChar) * ZMod.dft.symm (χ : ZMod N → ℂ) j = χ j := by
  rw [ZMod.invDFT_apply',hχ.fourierTransform_eq_inv_mul_gaussSum,neg_neg,hq.inv, smul_eq_mul]
  have h := gauss_sq hχ hq he
  field_simp [NeZero.ne (N:ℂ)]
  linear_combination χ j * h

end TunnellModularSymbol
end

section
/- Normalize the modular-symbol formula for the primitive positive even quadratic twists. -/

namespace TunnellModularSymbol

open MatrixGroups UpperHalfPlane MeasureTheory Set TunnellTwistCharacter
open scoped ModularForm

noncomputable def periodSymbol {Γ : Subgroup (GL (Fin 2) ℝ)} (F : CuspForm Γ 2) (r : ℝ) : ℂ :=
  (2*Real.pi:ℂ) * ∫ t in Ioi (0:ℝ), F (r +ᵥ ofComplex (Complex.I*t))

lemma reflected_symbol {Γ : Subgroup (GL (Fin 2) ℝ)} (F : CuspForm Γ 2)
    (hw : Γ.strictWidthInfty = 1) {N : ℕ} [NeZero N] (a : ZMod N) :
    periodSymbol F (-((-a).val:ℝ)/N) = periodSymbol F ((a.val:ℝ)/N) := by
  by_cases ha : a=0
  · simp [ha]
  have hN : (N:ℝ) ≠ 0 := NeZero.ne _
  have he : -((-a).val:ℝ)/N = -1 + (a.val:ℝ)/N := by
    rw [ZMod.neg_val,if_neg ha,Nat.cast_sub (ZMod.val_lt _).le]
    field_simp
    ring
  have hper : (-1:ℝ) ∈ Γ.strictPeriods :=
    Γ.strictPeriods.neg_mem (hw ▸ Γ.strictWidthInfty_mem_strictPeriods)
  simp only [he,periodSymbol, add_vadd, SlashInvariantForm.vAdd_apply_of_mem_strictPeriods F _ hper]

theorem scaled_twist_integral {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (he : χ.Even)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hw : Γ.strictWidthInfty = 1)
    (F : CuspForm Γ 2) :
    ∃ (H : Subgroup (GL (Fin 2) ℝ)) (hH : H.IsArithmetic) (_ : H.strictWidthInfty = 1)
      (G : CuspForm H 2),
      (∀ m : ℕ, (qExpansion 1 G).coeff m = χ m * (qExpansion 1 F).coeff m) ∧
      gaussSum χ ZMod.stdAddChar * ModularForm.L (by decide : (0:ℤ)<2) G 1 =
        ∑ j : ZMod N, χ j * periodSymbol F ((j.val:ℝ)/N) := by
  obtain ⟨H,hH,hW,G,hcf,hV⟩ := twist_central_integral (χ : ZMod N → ℂ) hw F
  refine ⟨H,hH,hW,G,hcf,?_⟩
  rw [hV,Finset.mul_sum]
  simp_rw [←mul_assoc,primitive_weights hχ hq he]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => by
    simp only [Equiv.neg_apply,he.eval_neg]
    simpa only [neg_neg,periodSymbol,mul_assoc] using congrArg (χ j * ·) (reflected_symbol F hw (-j)))

theorem jacobi_twist_integral {n : ℕ} (hn : n%8=2) (hs : Squarefree n)
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hw : Γ.strictWidthInfty = 1)
    (F : CuspForm Γ 2) :
    haveI : NeZero (4*n) := ⟨by omega⟩
    let χ := character n (by omega)
    ∃ (H : Subgroup (GL (Fin 2) ℝ)) (hH : H.IsArithmetic) (_ : H.strictWidthInfty = 1)
      (G : CuspForm H 2),
      (∀ m : ℕ, (qExpansion 1 G).coeff m = (weight n m:ℂ) * (qExpansion 1 F).coeff m) ∧
      gaussSum χ ZMod.stdAddChar * ModularForm.L (by decide : (0:ℤ)<2) G 1 =
        ∑ j : ZMod (4*n), (weight n j.val:ℂ) * periodSymbol F ((j.val:ℝ)/(4*n)) ∧
      gaussSum χ ZMod.stdAddChar ^ 2 = (4*n:ℂ) := by
  obtain ⟨d,hd⟩ : 2 ∣ n := by exact Nat.dvd_of_mod_eq_zero (by omega)
  subst n
  have hd4 : d%4=1 := by omega
  have hsd := hs.squarefree_of_dvd (dvd_mul_left d 2)
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let χ := character (2*d) (by omega)
  let hh := character_primitive hd4 hsd
  let hq := character_quadratic (2*d) (by omega)
  let he := character_even hd4
  obtain ⟨H,hH,hW,G,hcf,hV⟩ := scaled_twist_integral hh hq he hw F
  refine ⟨H,hH,hW,G,fun m => ?_,?_,?_⟩
  · simpa only [character_apply_nat] using hcf m
  · have hc (j : ZMod (4*(2*d))) : character (2*d) (by omega) j = (weight (2*d) j.val:ℂ) := rfl
    simpa only [Nat.cast_mul,Nat.cast_ofNat,hc] using hV
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using gauss_sq hh hq he

end TunnellModularSymbol
end

section
/- The actual paired vertical integrals are integral multiples of the base central value. -/

namespace TunnellFricke

open Complex Filter Set MeasureTheory TunnellModularSymbol
open UpperHalfPlane hiding I
open scoped Topology

noncomputable def path (r : ℝ) (t : ℂ) := 4*((r:ℂ)+I*t)

lemma path_im (r t : ℝ) : (path r t).im = 4*t := by simp [path,mul_im]

lemma tendsto_path_bottom (r : ℝ) :
    Tendsto (fun t : ℝ => path r t) (𝓝[>] 0) (cusp (4*r)) := by
  apply tendsto_comap_iff.mpr
  apply Tendsto.congr' _ (tendsto_inv_nhdsGT_zero |>.const_mul_atTop (by norm_num : (0:ℝ)<1/4))
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (1/4)*t⁻¹ = height (4*r) (path r t)
  rw [height,path_im,show path r t-(↑(4*r):ℂ) = 4*I*t by simp [path,mul_add,mul_assoc]]
  simp only [map_mul,normSq_I,normSq_ofReal]
  norm_num [normSq_apply]
  have ht' : 0<t := ht
  field_simp <;> norm_num

lemma tendsto_path_top (r : ℝ) :
    Tendsto (fun t : ℝ => path r t) atTop (comap Complex.im atTop) := by
  apply tendsto_comap_iff.mpr
  simpa only [Function.comp_def,path_im,id_eq] using
    (tendsto_id (α:=ℝ) (x:=atTop)).const_mul_atTop (by norm_num : (0:ℝ)<4)

lemma path_deriv (r : ℝ) (z : ℂ) : HasDerivAt (path r) (4*I) z := by
  unfold path
  simpa using (((hasDerivAt_id z).const_mul I).const_add (r:ℂ)).const_mul 4

theorem symbol_eq_boundary {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (hw : Γ.strictWidthInfty=1) (F : CuspForm Γ 2)
    (hF : ∀ z : ℍ, F z = h (4*(z:ℂ))) (r : ℚ) {J : ℂ → ℂ} {A : ℂ}
    (hJ : ∀ z, 0<z.im → HasDerivAt J (c*h z) z)
    (h0 : Tendsto J (comap Complex.im atTop) (𝓝 0))
    (hb : Tendsto J (cusp (4*(r:ℝ))) (𝓝 A)) : periodSymbol F r = A := by
  let f (t : ℝ) := F ((r:ℝ) +ᵥ ofComplex (I*t))
  let g (t : ℝ) := if t=0 then A else J (path r t)
  have hfall (t : ℝ) (ht : 0<t) : f t = h (path r t) := by
    unfold f
    rw [hF,coe_vadd,ofComplex_apply_of_im_pos (by simpa using ht)]
    rfl
  have hder (t : ℝ) (ht : 0<t) : HasDerivAt g (-(2*(Real.pi:ℂ))*f t) t := by
    have hd := (hJ (path r t) (by rw [path_im]; positivity)).comp (t:ℂ) (path_deriv r t) |>.comp_ofReal
    have hh : c*h (path r t)*(4*I) = -(2*(Real.pi:ℂ))*f t := by
      rw [hfall t ht,c]
      linear_combination (2*(Real.pi:ℂ)*h (path r t))*I_sq
    rw [hh] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht.ne'] with u hu
    simp [g,hu,Function.comp_def]
  have hg : ContinuousWithinAt g (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    change Tendsto g _ (𝓝 (g 0))
    simp only [g,if_pos rfl]
    apply (hb.comp (tendsto_path_bottom r)).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [ne_of_gt (show 0<t from ht)]
  have hg' : Tendsto g atTop (𝓝 0) := by
    apply (h0.comp (tendsto_path_top r)).congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [g,ht.ne',Function.comp_def]
  have hi : IntegrableOn f (Ioi 0) := integrable_translate hw F r
  have e := integral_Ioi_of_hasDerivAt_of_tendsto hg hder (hi.const_mul (-(2*(Real.pi:ℂ)))) hg'
  rw [integral_const_mul,show g 0 = A by simp [g],zero_sub] at e
  change 2*(Real.pi:ℂ)*(∫ t in Ioi (0:ℝ), f t) = A
  linear_combination -e

end TunnellFricke
end

section
/- Algebraicity of every normalized positive even twist relative to one explicit eta integral. -/

namespace TunnellFricke

open MeasureTheory Set TunnellCMLSeries TunnellGaussian TunnellModularSymbol Finset
open UpperHalfPlane hiding I

noncomputable def baseConstant : ℂ :=
  (2*Real.pi:ℂ) * ∫ t in Ioi (0:ℝ), h (4*(Complex.I*t))

lemma zero_symbol {Γ : Subgroup (GL (Fin 2) ℝ)} (F : CuspForm Γ 2)
    (hF : ∀ z : ℍ, F z = h (4*(z:ℂ))) : periodSymbol F 0 = baseConstant := by
  unfold periodSymbol baseConstant
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [zero_vadd,hF,ofComplex_apply_of_im_pos (by simpa using ht : 0<(Complex.I*(t:ℂ)).im)]

end TunnellFricke
end

section
/- Finite, explicitly computable normalized rational-cusp evaluations of the quadratic twists. -/

namespace TunnellFiniteSymbols
open TunnellFricke TunnellCuspEuclid TunnellTwistCharacter TunnellModularSymbol
open TunnellCMLSeries UpperHalfPlane Finset
open Set Filter
open scoped Topology

/- The real Gaussian modular-symbol sum, with the conductor-32 winding symbol normalized to one. -/
def winding (n : ℕ) (hn : 0<n) : ℤ :=
  haveI : NeZero (4*n) := ⟨by omega⟩
  ∑ j : ZMod (4*n), weight n j.val * (symbol (j.val:ℤ) n).re

noncomputable def tau (n : ℕ) (hn : 0<n) : ℂ :=
  haveI : NeZero (4*n) := ⟨by omega⟩
  gaussSum (character n hn.ne') ZMod.stdAddChar

lemma paired {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hw : Γ.strictWidthInfty=1) (F : CuspForm Γ 2)
    (hF : ∀ z : ℍ, F z=h (4*(z:ℂ))) (n j : ℕ) (hn : 0<n) :
    periodSymbol F ((j:ℝ)/(4*n)) + periodSymbol F (-(j:ℝ)/(4*n)) =
      2*((symbol (j:ℤ) n).re:ℂ)*baseConstant := by
  obtain ⟨J,hJ,h0,hT,C,hW⟩ := primitive
  obtain ⟨hz,_,_,_⟩ := cusp_rules h0 hT hW
  have e0 := symbol_eq_boundary hw F hF 0 hJ h0 (A:=C) (by simpa [Bound] using hz)
  have hC : C=baseConstant := by simpa only [Rat.cast_zero,zero_symbol F hF] using e0.symm
  let r : ℚ := (j:ℚ)/(4*n)
  have he : 4*(r:ℝ)=((j:ℤ):ℝ)/n := by dsimp [r]; push_cast; field_simp
  obtain ⟨hp,hm⟩ := cusp_value h0 hT hW (j:ℤ) n hn
  have e1 := symbol_eq_boundary hw F hF r hJ h0 (A:=((symbol (j:ℤ) n:GaussianInt):ℂ)*C) (by
    simpa only [Bound,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,he] using hp)
  have e2 := symbol_eq_boundary hw F hF (-r) hJ h0 (A:=((star (symbol (j:ℤ) n):GaussianInt):ℂ)*C) (by
    simpa only [Bound,Rat.cast_neg,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,mul_neg,he] using hm)
  rw [hC] at e1 e2
  have hsum := congrArg₂ (·+·) e1 e2
  simp only [r,Rat.cast_neg,Rat.cast_div,Rat.cast_natCast,Rat.cast_mul,Rat.cast_ofNat,←neg_div,←add_mul] at hsum
  rw [hsum]
  congr 1
  simp [GaussianInt.toComplex_def]
  ring

lemma twist_sum (n : ℕ) (hn : n%8=2) (hs : Squarefree n) (L : ℂ → ℂ)
    (he : AnalyticOnNhd ℂ L univ) (hprod : ∀ s : ℝ, 2<s →
      HasProd (fun p : Nat.Primes => if p.val ∣ 2*n then (1:ℂ) else
        let T := (p.val:ℂ)^(-(s:ℂ))
        (1-(curveTrace n p:ℂ)*T+(p.val:ℂ)*T^2)⁻¹) (L s)) :
    tau n (by omega) * L 1 = (winding n (by omega):ℂ)*baseConstant := by
  obtain ⟨H,hH,hw,F,hF,hfc⟩ := TunnellEtaValue.actual_form
  letI : H.IsArithmetic := hH
  letI : NeZero (4*n) := ⟨by omega⟩
  obtain ⟨K,hK,kw,G,ht,hv,_⟩ := jacobi_twist_integral hn hs hw F
  letI : K.IsArithmetic := hK
  let M := ModularForm.L (by decide : (0:ℤ)<2) G
  have a (m : ℕ) : (qExpansion 1 G).coeff m = gaussCoeff n m := by
    rw [ht,hfc,TunnellArithmetic.eta_eq_mass
      (TunnellTruncated.cubic_congruence (fun N => TunnellCubicFinite.cubic (Polynomial.X^8) N))
      (TunnellTruncated.theta_congruence (fun d N => TunnellBalanced.balanced _ N))]
    rfl
  have hM : AnalyticOnNhd ℂ M univ := fun z _ => (CuspForm.differentiable_L (by decide : (0:ℤ)<2) G).analyticAt z
  have eqM := TunnellMellin.entire_unique he hM 2 (fun s hgt => by
    have hl := (hprod s hgt).unique (lattice_euler n s (by linarith))
    have hsum : HasSum (fun m : ℕ => gaussCoeff n m / (m:ℂ)^(s:ℂ)) (M s) := by
      have h := CuspForm.hasSum_L (by decide : (0:ℤ)<2) G (s:=(s:ℂ)) (by norm_num; linarith)
      simpa only [kw,Complex.ofReal_one,Complex.one_cpow,one_mul,a,M] using h
    exact hl.trans ((shell_expansion n s (by linarith)).unique hsum))
  rw [eqM]
  let χ := character n (by omega)
  let P (j : ZMod (4*n)) := periodSymbol F ((j.val:ℝ)/(4*n))
  let Q (j : ZMod (4*n)) := periodSymbol F (-(j.val:ℝ)/(4*n))
  have evenχ : χ.Even := by
    obtain ⟨d,hd⟩ : 2∣n := Nat.dvd_of_mod_eq_zero (by omega)
    subst n
    exact character_even (by omega)
  have hsym : ∑ j, χ j * P j = ∑ j, χ j * Q j := by
    apply Fintype.sum_equiv (Equiv.neg _)
    intro j
    rw [Equiv.neg_apply,evenχ.eval_neg]
    congr 1
    simpa only [P,Q,Nat.cast_mul,Nat.cast_ofNat] using (reflected_symbol F hw j).symm
  have sum2 : (2:ℂ)*(∑ j, χ j*P j) = 2*(winding n (by omega):ℂ)*baseConstant := by
    calc _ = (∑ j, χ j*P j) + ∑ j, χ j*Q j := by rw [←hsym,two_mul]
         _ = ∑ j, χ j*(P j+Q j) := by simp [mul_add,Finset.sum_add_distrib]
         _ = _ := by
           unfold winding
           simp only [P,Q,paired hw F hF n _ (by omega),Int.cast_sum,Int.cast_mul,Finset.mul_sum,Finset.sum_mul]
           apply Finset.sum_congr rfl
           intro j _
           change (weight n j.val:ℂ)*_=_
           ring
  change gaussSum χ ZMod.stdAddChar * M 1 = _
  change gaussSum χ ZMod.stdAddChar * M 1 = ∑ j, χ j*P j at hv
  linear_combination hv + sum2/2

end TunnellFiniteSymbols
end

section
/- Eta quotients for the Fermat-quartic modular parameter. -/

namespace TunnellLambda
open Complex hiding eta
open ModularForm EisensteinSeries Set Function Filter
open UpperHalfPlane hiding I
open scoped Topology Real ComplexOrder

noncomputable def U (z : ℂ) : ℂ := 16*(eta (8*z)/eta (2*z))^8

lemma qParam_imag (h t : ℝ) : Periodic.qParam h (I*t) = (Real.exp (-2*Real.pi*t/h):ℝ) := by
  rw [Periodic.qParam,ofReal_exp]
  congr 1
  push_cast
  linear_combination (2*(Real.pi:ℂ)*t/h)*I_sq

noncomputable def etaR (t : ℝ) : ℝ := Real.exp (-2*Real.pi*t/24)*∏' n : ℕ, (1-Real.exp (-2*Real.pi*t)^(n+1))

lemma eta_imag (t : ℝ) : eta (I*t) = (etaR t:ℂ) := by
  have hh := (RCLike.isUniformEmbedding_ofReal (𝕜:=ℂ)).isClosedEmbedding.map_tprod
    (L:=SummationFilter.unconditional ℕ) (g:=Complex.ofRealHom.toMonoidHom) (fun n : ℕ => 1-Real.exp (-2*Real.pi*t)^(n+1))
  unfold eta etaR eta_q
  rw [qParam_imag,qParam_imag,ofReal_mul]
  simp only [RingHom.toMonoidHom_eq_coe,MonoidHom.coe_coe,ofRealHom_eq_coe] at hh
  simp only [ofReal_sub,ofReal_one,ofReal_pow] at hh
  simpa only [div_one] using congrArg (fun w : ℂ => (Real.exp (-2*Real.pi*t/24):ℂ)*w) hh.symm

lemma etaR_pos {t : ℝ} (ht : 0<t) : 0<etaR t := by
  have hq : Real.exp (-2*Real.pi*t)<1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos ht])
  have h0 : 0 ≤ etaR t := mul_nonneg (Real.exp_pos _).le (tprod_nonneg (fun n =>
    sub_nonneg.mpr (pow_le_one₀ (Real.exp_pos _).le hq.le)))
  apply lt_of_le_of_ne h0
  intro h
  have hn : eta (I*t) ≠ 0 := eta_ne_zero (show I*t∈upperHalfPlaneSet by change 0<(I*t).im; simpa [mul_im])
  exact hn (by rw [eta_imag,←h,ofReal_zero])

end TunnellLambda
end

section
/- Reality and positivity of the eta differential on the imaginary axis. -/

namespace TunnellFricke

open Complex hiding eta
open ModularForm Function MeasureTheory Set Filter
open scoped Topology

lemma eta_imag {t : ℝ} (ht : 0<t) : ∃ x : ℝ, 0<x ∧ eta (I*t) = x :=
  ⟨TunnellLambda.etaR t,TunnellLambda.etaR_pos ht,TunnellLambda.eta_imag t⟩

noncomputable def imaginaryValue (t : ℝ) := (h (4*(I*t))).re

lemma imaginary_cast {t : ℝ} (ht : 0<t) :
    0 < imaginaryValue t ∧ h (4*(I*t)) = (imaginaryValue t:ℂ) := by
  obtain ⟨a,ha,he⟩ := eta_imag (show 0<4*t by positivity)
  obtain ⟨b,hb,hf⟩ := eta_imag (show 0<8*t by positivity)
  have v : h (4*(I*t)) = ((a^2*b^2:ℝ):ℂ) := by
    rw [h,show 4*(I*(t:ℂ)) = I*((4*t:ℝ):ℂ) by push_cast; ring,
      show 2*(I*(((4*t:ℝ):ℂ))) = I*((8*t:ℝ):ℂ) by push_cast; ring,he,hf]
    push_cast
    rfl
  simp only [imaginaryValue,v,ofReal_re]
  exact ⟨by positivity,trivial⟩

lemma baseConstant_real : baseConstant = ((2*Real.pi*(∫ t in Ioi (0:ℝ), imaginaryValue t):ℝ):ℂ) := by
  unfold baseConstant
  push_cast
  rw [← integral_complex_ofReal]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  exact fun t ht => (imaginary_cast ht).2

end TunnellFricke
end

section
/- The square-value assertion as a finite winding-symbol identity for each squarefree d ≡ 1 mod 4. -/

namespace TunnellFiniteSymbols
open TunnellFricke TunnellModularSymbol TunnellTwistCharacter
open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

lemma base_ne_zero : baseConstant ≠ 0 := by
  rw [baseConstant_real,Complex.ofReal_ne_zero]
  apply (mul_pos (by positivity : 0<2*Real.pi) _).ne'
  obtain ⟨H,hH,hw,F,hF,_⟩ := TunnellEtaValue.actual_form
  letI : H.IsArithmetic := hH
  have hi : IntegrableOn imaginaryValue (Ioi (0:ℝ)) := by
    have hr := (integrable_vertical F).re
    apply hr.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (F (ofComplex (Complex.I*t))).re = (h (4*(Complex.I*t))).re
    rw [hF,ofComplex_apply_of_im_pos (by simpa using (show 0<t from ht) : 0<(Complex.I*(t:ℂ)).im)]
  apply (setIntegral_pos_iff_support_of_nonneg_ae _ hi).mpr
  · have hs : Function.support imaginaryValue ∩ Ioi (0:ℝ) = Ioi 0 :=
      inter_eq_right.mpr (fun _ ht => (imaginary_cast ht).1.ne')
    rw [hs,Real.volume_Ioi]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (imaginary_cast ht).1.le

end TunnellFiniteSymbols
end

section
/- Selling reduction of positive integral ternary lattices of determinant one.
The six entries are conorms for a superbase indexed by the four vertices of a tetrahedron. -/
namespace TunnellSelling
structure W where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
abbrev V := ℤ × ℤ × ℤ × ℤ

def energy (p : W) (u : V) : ℤ :=
  let (x,y,z,t) := u
  p.a*(x-y)^2+p.b*(x-z)^2+p.c*(x-t)^2+p.d*(y-z)^2+p.e*(y-t)^2+p.f*(z-t)^2

def mass (p : W) := p.a+p.b+p.c+p.d+p.e+p.f

def det (p : W) : ℤ :=
  p.a*p.b*p.c+p.a*p.b*p.e+p.a*p.b*p.f+p.a*p.c*p.d
  +p.a*p.c*p.f+p.a*p.d*p.e+p.a*p.d*p.f+p.a*p.e*p.f
  +p.b*p.c*p.d+p.b*p.c*p.e+p.b*p.d*p.e+p.b*p.d*p.f
  +p.b*p.e*p.f+p.c*p.d*p.e+p.c*p.d*p.f+p.c*p.e*p.f
def psd (p : W) : Prop := ∀ u, 0≤energy p u

lemma mass_nonneg {p : W} (h : psd p) : 0≤ mass p := by
  obtain ⟨a,b,c,d,e,f⟩ := p
  have A := h (1,0,0,0); have B := h (0,1,0,0); have C := h (0,0,1,0); have D := h (0,0,0,1)
  norm_num [energy,mass] at *
  omega

def swapW (i : Fin 6) (p : W) : W :=
  ![⟨p.a,p.b,p.c,p.d,p.e,p.f⟩,
    ⟨p.b,p.a,p.c,p.d,p.f,p.e⟩,
    ⟨p.c,p.b,p.a,p.f,p.e,p.d⟩,
    ⟨p.d,p.b,p.f,p.a,p.e,p.c⟩,
    ⟨p.e,p.f,p.c,p.d,p.a,p.b⟩,
    ⟨p.f,p.b,p.d,p.c,p.e,p.a⟩] i

def swapV (i : Fin 6) (u : V) : V :=
  let (x,y,z,t) := u
  ![(x,y,z,t), (x,z,y,t), (x,t,z,y), (z,y,x,t), (t,y,z,x), (z,t,x,y)] i

lemma swap_energy (i : Fin 6) (p : W) (u : V) : energy (swapW i p) (swapV i u)=energy p u := by
  obtain ⟨a,b,c,d,e,f⟩ := p
  obtain ⟨x,y,z,t⟩ := u
  fin_cases i <;> dsimp [swapW,swapV,energy] <;> ring

lemma swap_vv (i : Fin 6) (u : V) : swapV i (swapV i u)=u := by
  obtain ⟨x,y,z,t⟩ := u; fin_cases i <;> rfl

lemma swap_det (i : Fin 6) (p : W) : det (swapW i p)=det p := by
  obtain ⟨a,b,c,d,e,f⟩ := p; fin_cases i <;> dsimp [det,swapW] <;> ring

lemma swap_mass (i : Fin 6) (p : W) : mass (swapW i p)=mass p := by
  obtain ⟨a,b,c,d,e,f⟩ := p; fin_cases i <;> dsimp [mass,swapW] <;> ring

def reduceW (p : W) : W := ⟨-p.a,p.a+p.c,p.a+p.b,p.d+p.a,p.e+p.a,p.f-p.a⟩
def reduceV (u : V) : V := (u.2.2.1+u.2.2.2-u.1,u.2.1,u.2.2.1,u.2.2.2)

lemma reduce_energy (p : W) (u : V) : energy (reduceW p) (reduceV u) = energy p u := by
  obtain ⟨a,b,c,d,e,f⟩ := p; obtain ⟨x,y,z,t⟩ := u; dsimp [energy,reduceW,reduceV]; ring

lemma reduce_vv (u : V) : reduceV (reduceV u)=u := by
  obtain ⟨x,y,z,t⟩ := u; simp [reduceV]

lemma reduce_det (p : W) : det (reduceW p)=det p := by
  obtain ⟨a,b,c,d,e,f⟩ := p; dsimp [det,reduceW]; ring

lemma reduce_mass (p : W) : mass (reduceW p)=mass p+p.a := by dsimp [mass,reduceW]; ring

def nonnegative (p : W) := 0≤p.a ∧ 0≤p.b ∧ 0≤p.c ∧ 0≤p.d ∧ 0≤p.e ∧ 0≤p.f

lemma reduce_to_nonnegative {p : W} (hp : psd p) (hd : det p=1) {N : ℤ} (u : V) (hu : energy p u=N) :
    ∃ q, nonnegative q ∧ det q=1 ∧ ∃ t, energy q t=N := by
  classical
  let P (m : ℕ) := ∃ q, psd q ∧ det q=1 ∧ (∃ t, energy q t=N) ∧ mass q=(m:ℤ)
  have he : ∃ m, P m := ⟨(mass p).toNat,p,hp,hd,⟨u,hu⟩,(Int.toNat_of_nonneg (mass_nonneg hp)).symm⟩
  obtain ⟨q,hq,hdet,⟨t,ht⟩,hm⟩ := Nat.find_spec he
  refine ⟨q,?_,hdet,t,ht⟩
  have good (i : Fin 6) : 0≤(swapW i q).a := by
    by_contra! hn
    let r := swapW i q
    have h₁ : psd r := fun x => by
      have e := swap_energy i q (swapV i x); rw [swap_vv] at e
      rw [show energy r x=_ from e]; exact hq _
    have h₂ : psd (reduceW r) := fun x => by
      have e := reduce_energy r (reduceV x); rw [reduce_vv] at e
      rw [e]; exact h₁ _
    have hr : P (mass (reduceW r)).toNat := ⟨reduceW r,h₂,(reduce_det r).trans ((swap_det i q).trans hdet),
      ⟨reduceV (swapV i t),(reduce_energy r _).trans ((swap_energy i q t).trans ht)⟩,
      (Int.toNat_of_nonneg (mass_nonneg h₂)).symm⟩
    have hmin := Nat.find_min' he hr
    have hmass := reduce_mass r
    have heq : mass r=mass q := swap_mass i q
    change r.a<0 at hn
    have hcast : (Nat.find he:ℤ) ≤ ((mass (reduceW r)).toNat:ℤ) := by exact_mod_cast hmin
    have hnon := mass_nonneg h₂
    omega
  exact ⟨good 0,good 1,good 2,good 3,good 4,good 5⟩

lemma triple_one {a b c : ℤ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (h : a*b*c=1) :
    a=1 ∧ b=1 ∧ c=1 := by
  have e₁ := Int.eq_one_or_neg_one_of_mul_eq_one (show a*(b*c)=1 by simpa [mul_assoc] using h)
  have e₂ := Int.eq_one_or_neg_one_of_mul_eq_one (show b*(a*c)=1 by simpa [mul_assoc,mul_left_comm,mul_comm] using h)
  have e₃ := Int.eq_one_or_neg_one_of_mul_eq_one (show c*(a*b)=1 by simpa [mul_assoc,mul_left_comm,mul_comm] using h)
  omega

lemma three_sq {p : W} (h : nonnegative p) (hd : det p=1) (u : V) :
    ∃ x y z : ℤ, energy p u=x^2+y^2+z^2 := by
  obtain ⟨a,b,c,d,e,f⟩ := p
  obtain ⟨ha,hb,hc,hd',he,hf⟩ := h
  dsimp only at ha hb hc hd' he hf
  dsimp only [det] at hd
  obtain ⟨w,x,y,z⟩ := u
  have t0 := mul_nonneg (mul_nonneg ha hb) hc
  have t1 := mul_nonneg (mul_nonneg ha hb) he
  have t2 := mul_nonneg (mul_nonneg ha hb) hf
  have t3 := mul_nonneg (mul_nonneg ha hc) hd'
  have t4 := mul_nonneg (mul_nonneg ha hc) hf
  have t5 := mul_nonneg (mul_nonneg ha hd') he
  have t6 := mul_nonneg (mul_nonneg ha hd') hf
  have t7 := mul_nonneg (mul_nonneg ha he) hf
  have t8 := mul_nonneg (mul_nonneg hb hc) hd'
  have t9 := mul_nonneg (mul_nonneg hb hc) he
  have t10 := mul_nonneg (mul_nonneg hb hd') he
  have t11 := mul_nonneg (mul_nonneg hb hd') hf
  have t12 := mul_nonneg (mul_nonneg hb he) hf
  have t13 := mul_nonneg (mul_nonneg hc hd') he
  have t14 := mul_nonneg (mul_nonneg hc hd') hf
  have t15 := mul_nonneg (mul_nonneg hc he) hf
  have hone : a*b*c=1 ∨ a*b*e=1 ∨ a*b*f=1 ∨ a*c*d=1 ∨ a*c*f=1 ∨ a*d*e=1 ∨ a*d*f=1 ∨ a*e*f=1 ∨ b*c*d=1 ∨ b*c*e=1 ∨ b*d*e=1 ∨ b*d*f=1 ∨ b*e*f=1 ∨ c*d*e=1 ∨ c*d*f=1 ∨ c*e*f=1 := by omega
  rcases hone with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have z0 : a*c*d=0 := by omega
    have z1 : a*b*e=0 := by omega
    have z2 : a*b*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hb hc h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,w-y,w-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : a*d*e=0 := by omega
    have z2 : a*b*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hb he h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,w-y,x-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : a*d*f=0 := by omega
    have z2 : a*b*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hb hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,w-y,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : a*d*e=0 := by omega
    have z2 : a*c*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hc hd' h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,w-z,x-y,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : a*c*d=0 := by omega
    have z2 : a*e*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hc hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,w-z,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*e=0 := by omega
    have z1 : a*c*d=0 := by omega
    have z2 : a*d*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hd' he h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,x-y,x-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*f=0 := by omega
    have z1 : a*c*d=0 := by omega
    have z2 : a*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hd' hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,x-y,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*e=0 := by omega
    have z1 : a*c*f=0 := by omega
    have z2 : a*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha he hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,x-z,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : b*c*e=0 := by omega
    have z2 : b*d*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hb hc hd' h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-y,w-z,x-y,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : b*c*d=0 := by omega
    have z2 : b*e*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hb hc he h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-y,w-z,x-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*e=0 := by omega
    have z1 : b*c*d=0 := by omega
    have z2 : b*d*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hb hd' he h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-y,x-y,x-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*f=0 := by omega
    have z1 : b*c*d=0 := by omega
    have z2 : b*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hb hd' hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-y,x-y,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*e=0 := by omega
    have z1 : b*c*e=0 := by omega
    have z2 : b*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hb he hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-y,x-z,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*c*d=0 := by omega
    have z1 : b*c*d=0 := by omega
    have z2 : c*d*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hc hd' he h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-z,x-y,x-z,by dsimp [energy]; ring⟩
  · have z0 : a*c*d=0 := by omega
    have z1 : b*c*d=0 := by omega
    have z2 : c*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hc hd' hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-z,x-y,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*c*f=0 := by omega
    have z1 : b*c*e=0 := by omega
    have z2 : c*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hc he hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-z,x-z,y-z,by dsimp [energy]; ring⟩

theorem three_squares {p : W} (hp : psd p) (hd : det p=1) (u : V) :
    ∃ x y z : ℤ, energy p u=x^2+y^2+z^2 := by
  obtain ⟨q,hq,hd',w,he⟩ := reduce_to_nonnegative hp hd u rfl
  exact he ▸ three_sq hq hd' w

end TunnellSelling
end

section
/- Existence of the primitive embeddings used in the ramified toric period. -/
namespace TunnellThreeSquares
open TunnellSelling TunnellShell

/- A prime and two integral quotients defining a unimodular Gram matrix. -/
lemma auxiliary_prime (d : ℕ) (hd : d%4=1) :
    ∃ p b A C : ℤ, 0<p ∧ A*(2*d)=p+1 ∧ p*C=b^2+2*d := by
  have hpos : 0<d := by omega
  let a : ℤ := 2*d-1
  have hbez : IsCoprime a (8*d:ℤ) := by
    refine ⟨a,-(((d:ℤ)-1)/2),?_⟩
    have he : ((d:ℤ)-1)/2*2=(d:ℤ)-1 := by omega
    dsimp [a]
    linear_combination -4*(d:ℤ)*he
  obtain ⟨p,hpgt,hp,hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (8*d) (q:=8*d) (a:=a) (by omega) (by simpa using hbez)
  letI : Fact p.Prime := ⟨hp⟩
  have hmd : (p:ℤ) ≡ -1 [ZMOD (d:ℤ)] := by
    apply (hmod.of_dvd (by exact_mod_cast (dvd_mul_left d 8))).trans
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-2,by dsimp [a]; ring⟩
  have h8 : p%8=1 := by
    have he : (p:ℤ) ≡ a [ZMOD 8] := hmod.of_dvd (by exact_mod_cast (dvd_mul_right 8 d))
    change (p:ℤ)%8=a%8 at he
    dsimp only [a] at he; omega
  have hop : Odd p := Nat.odd_iff.mpr (by omega)
  have hod : Odd d := Nat.odd_iff.mpr (by omega)
  have hnn : ((-2*(d:ℤ)):ZMod p)≠0 := by
    have he : ((2*d:ℕ):ZMod p)≠0 := by
      intro he
      have ht := (ZMod.natCast_eq_zero_iff _ _).mp he
      exact (not_le_of_gt (show 2*d<p by omega)) (Nat.le_of_dvd (by positivity) ht)
    push_cast at he ⊢
    simpa using he
  have hsym : legendreSym p (-2*d)=1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym,jacobiSym.mul_left,jacobiSym.at_neg_two hop,
      ZMod.χ₈'_nat_eq_if_mod_eight,h8,jacobiSym.quadratic_reciprocity_one_mod_four hd hop,
      jacobiSym.mod_left' hmd,jacobiSym.at_neg_one hod,ZMod.χ₄_nat_one_mod_four hd]
    simp [show p%2≠0 by omega]
  obtain ⟨u,hu⟩ := (legendreSym.eq_one_iff p (a:=-2*(d:ℤ)) (by simpa using hnn)).mp hsym
  have hq : (p:ℤ) ∣ ((u.val:ℤ)^2+2*d) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    push_cast at hu
    linear_combination -hu
  obtain ⟨C,hC⟩ := hq
  obtain ⟨t,ht⟩ := hmod.dvd
  push_cast at ht
  refine ⟨p,u.val,1-4*t,C,by exact_mod_cast hp.pos,?_,hC.symm⟩
  dsimp only [a] at ht
  linear_combination ht

def coefficients (p b A C : ℤ) : W :=
  ⟨0,-1,A+1,-b,p+b,C+b+1⟩

lemma form_eval (p b A C : ℤ) (u : V) :
    energy (coefficients p b A C) u=
      A*(u.1-u.2.2.2)^2+p*(u.2.1-u.2.2.2)^2+C*(u.2.2.1-u.2.2.2)^2+
      2*(u.1-u.2.2.2)*(u.2.2.1-u.2.2.2)+2*b*(u.2.1-u.2.2.2)*(u.2.2.1-u.2.2.2) := by
  obtain ⟨x,y,z,t⟩ := u
  dsimp [coefficients,energy]; ring

/- Every positive integer 2d with d congruent to one modulo four is a sum of three squares. -/
theorem shell_nonempty (d : ℕ) (hd : d%4=1) : (shell (2*d)).Nonempty := by
  obtain ⟨p,b,A,C,hp,hA,hC⟩ := auxiliary_prime d hd
  let n : ℤ := 2*d
  have hn : 0<n := by dsimp [n]; omega
  change A*n=p+1 at hA
  change p*C=b^2+n at hC
  let q := coefficients p b A C
  have hdet : det q=1 := by
    dsimp [q,coefficients,det]
    linear_combination A*hC+hA
  have hpos : psd q := by
    rintro ⟨x,y,z,t⟩
    let X := x-t
    let Y := y-t
    let Z := z-t
    have hQ := form_eval p b A C (x,y,z,t)
    change energy q (x,y,z,t)=A*X^2+p*Y^2+C*Z^2+2*X*Z+2*b*Y*Z at hQ
    have hv : p*n*energy q (x,y,z,t)=(p*X+n*Z)^2+n*(p*Y+b*Z)^2+p*X^2 := by
      rw [hQ]
      linear_combination p*X^2*hA+n*Z^2*hC
    have hpn : 0<p*n := mul_pos hp hn
    exact nonneg_of_mul_nonneg_right (show 0≤p*n*energy q (x,y,z,t) by rw [hv]; positivity) hpn
  have hre : energy q (n,b,-p,0)=n := by
    rw [form_eval]
    dsimp only; ring_nf
    linear_combination n*hA+p*hC
  obtain ⟨x,y,z,h⟩ := three_squares hpos hdet (n,b,-p,0)
  exact ⟨(x,y,z),mem_shell.mpr (by change x^2+y^2+z^2=(↑(2*d:ℕ):ℤ); rw [←h,hre]; simp [n])⟩

end TunnellThreeSquares
end

section
/- Bounds for the regularized summand with a variable shortest-vector scale. -/
namespace TunnellRankinMajorant
open Complex TunnellCMRegularized
noncomputable section

lemma kernel_grid {K : ℕ} {s w : ℂ} {t : ℝ} (ht : 1≤t) (hs : 3/4<s.re)
    (hK : 2*s.re≤K) (hw : w≠0 → t⁻¹≤‖w‖) : ‖kernel s w‖≤t^K := by
  by_cases h0 : w=0
  · simp [h0,kernel,pow_nonneg (by linarith : 0≤t)]
  rw [norm_kernel _ _ h0]
  have hp := norm_pos_iff.mpr h0
  have ht' : 0<t := by linarith
  by_cases h : 1≤‖w‖
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)).trans (one_le_pow₀ ht)
  · calc
      _ ≤ ‖w‖^(-(K:ℝ)) := Real.rpow_le_rpow_of_exponent_ge hp (le_of_not_ge h) (by linarith)
      _ ≤ (t⁻¹)^(-(K:ℝ)) := Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ht') (hw h0) (neg_nonpos.mpr (Nat.cast_nonneg _))
      _ = _ := by rw [Real.rpow_neg (inv_nonneg.mpr ht'.le),Real.rpow_natCast,inv_pow,inv_inv]

lemma difference_grid {K : ℕ} {s w z : ℂ} {t : ℝ} (ht : 1≤t) (hs : 3/4<s.re)
    (hK : 2*s.re≤K) (a : ℕ)
    (h₀ : w≠0 → t⁻¹≤‖w‖) (h₁ : w+z≠0 → t⁻¹≤‖w+z‖)
    (h₂ : w+(a:ℂ)*z≠0 → t⁻¹≤‖w+(a:ℂ)*z‖) :
    ‖difference a z w s‖≤(2*(a:ℝ)^2+2*a)*t^K := by
  have ha (u : ℂ) (hu : u≠0 → t⁻¹≤‖u‖) := kernel_grid ht hs hK hu
  unfold difference
  apply (norm_sub_le _ _).trans
  simp only [norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (a:ℝ)^2*(t^K+t^K)+a*(t^K+t^K) := by
      apply add_le_add <;> apply mul_le_mul_of_nonneg_left _ (by positivity)
      · exact (norm_sub_le _ _).trans (add_le_add (ha _ h₁) (ha _ h₀))
      · exact (norm_sub_le _ _).trans (add_le_add (ha _ h₂) (ha _ h₀))
    _ = _ := by ring

lemma difference_tail {R : ℝ} (hR : 0≤R) (a : ℕ) (z : ℂ) :
    ∃ A C : ℝ, 1≤A ∧ 0≤C ∧ ∀ s w : ℂ, ‖s‖≤R → 3/4<s.re → A≤‖w‖ →
      ‖difference a z w s‖*(1+‖w‖)^(5/2:ℝ)≤C := by
  let M := max 1 (a:ℝ)
  let A := max 1 (max (2*M*‖z‖) (3*R*M*‖z‖))
  let C := ((a:ℝ)^2+(a:ℝ)^3)*(9*R^2+8*R)*‖z‖^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hM : 1≤M := le_max_left _ _
  have ha : (a:ℝ)≤M := le_max_right _ _
  refine ⟨A,C*2^(5/2:ℝ),le_max_left _ _,by positivity,?_⟩
  intro s w hsr hs hw
  have h1 : 1≤‖w‖ := (le_max_left _ _).trans hw
  have hp : 0<‖w‖ := by linarith
  have h2 : 2*M*‖z‖≤‖w‖ := (le_max_left _ _).trans ((le_max_right _ _).trans hw)
  have h3 : 3*R*M*‖z‖≤‖w‖ := (le_max_right _ _).trans ((le_max_right _ _).trans hw)
  have hzf (b : ℝ) (hb : 0≤b) (he : b≤M) : b*(‖z‖/‖w‖)≤1/2 ∧ 3*R*(b*(‖z‖/‖w‖))≤1 := by
    constructor
    · rw [←mul_div_assoc,div_le_iff₀ hp]
      nlinarith [mul_le_mul_of_nonneg_right he (norm_nonneg z)]
    · rw [←mul_assoc,←mul_div_assoc,div_le_iff₀ hp]
      nlinarith [mul_le_mul_of_nonneg_right he (mul_nonneg hR (norm_nonneg z))]
  obtain ⟨hu,hsu⟩ := hzf 1 zero_le_one hM
  obtain ⟨hv,hsv⟩ := hzf _ (Nat.cast_nonneg a) ha
  simp only [one_mul] at hu hsu
  have e := difference_bound (s:=s) (z:=z) (w:=w) (norm_pos_iff.mp hp) hsr a
    (by simpa [norm_div] using hu) (by simpa [norm_mul,norm_div] using hv)
    (by simpa [norm_div] using hsu) (by simpa [norm_mul,norm_div] using hsv)
  have he : ‖difference a z w s‖ ≤ C*‖w‖^(-(5/2):ℝ) :=
    e.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) hC)
  have hh : (1+‖w‖)^(5/2:ℝ)≤(2*‖w‖)^(5/2:ℝ) := by gcongr <;> linarith
  apply (mul_le_mul he hh (by positivity) (by positivity)).trans
  rw [Real.mul_rpow (by norm_num) hp.le,Real.rpow_neg hp.le]
  have hn := (Real.rpow_pos_of_pos hp (5/2)).ne'
  field_simp <;> exact le_rfl

lemma summand_weight {K : ℕ} {R : ℝ} (hR : 0≤R) (a : ℕ) (z : ℂ) :
    ∃ C : ℝ, 0≤C ∧ ∀ {s w : ℂ} {t u : ℝ}, 1≤t → 0≤u → ‖s‖≤R → 3/4<s.re → 2*s.re≤K →
      1+u≤t*(1+‖w‖) → (w≠0 → t⁻¹≤‖w‖) → (w+z≠0 → t⁻¹≤‖w+z‖) →
      (w+(a:ℂ)*z≠0 → t⁻¹≤‖w+(a:ℂ)*z‖) →
      ‖difference a z w s‖ ≤ C*t^(K+3)*(1+u)^(-(5/2):ℝ) := by
  obtain ⟨A,B,hA,hB,h⟩ := difference_tail hR a z
  let C := max B ((2*(a:ℝ)^2+2*a)*(1+A)^(5/2:ℝ))
  have hC : 0≤C := hB.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro s w t u ht hu hs hs' hK hw h₀ h₁ h₂
  have ht₀ : 0<t := by linarith
  have hm : ‖difference a z w s‖*(1+‖w‖)^(5/2:ℝ)≤C*t^K := by
    by_cases hw' : A≤‖w‖
    · exact (h _ _ hs hs' hw').trans ((le_max_left _ _).trans (le_mul_of_one_le_right hC (one_le_pow₀ ht)))
    · have e := difference_grid ht hs' hK a h₀ h₁ h₂
      have hh : (1+‖w‖)^(5/2:ℝ) ≤ (1+A)^(5/2:ℝ) := by gcongr; linarith
      calc
        _ ≤ ((2*(a:ℝ)^2+2*a)*t^K)*(1+A)^(5/2:ℝ) := mul_le_mul e hh (by positivity) (by positivity)
        _ = ((2*(a:ℝ)^2+2*a)*(1+A)^(5/2:ℝ))*t^K := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hcomp := Real.rpow_le_rpow (by positivity : 0≤1+u) hw (by norm_num : 0≤(5/2:ℝ))
  rw [Real.mul_rpow ht₀.le (by positivity)] at hcomp
  rw [Real.rpow_neg (by positivity : 0≤1+u),←div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)]
  calc
    _ ≤ ‖difference a z w s‖*(t^(5/2:ℝ)*(1+‖w‖)^(5/2:ℝ)) := mul_le_mul_of_nonneg_left hcomp (norm_nonneg _)
    _ = (‖difference a z w s‖*(1+‖w‖)^(5/2:ℝ))*t^(5/2:ℝ) := by ring
    _ ≤ C*t^K*t^3 := mul_le_mul hm (by exact_mod_cast Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (5/2:ℝ)≤(3:ℕ))) (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring
end
end TunnellRankinMajorant
end

section
/- A single scale controls shortest shifted vectors and coordinate distortion on ℍ. -/
namespace TunnellRankinMajorant
open Complex TunnellRankinEisenstein TunnellCMRegularized
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

def vector (k : ℕ) (z : ℍ) (p : ℤ×ℤ) : ℂ := (p.1:ℂ)+(p.2:ℂ)*((k:ℂ)*conj (z:ℂ))

def scale (N k : ℕ) (z : ℍ) := ((N:ℝ)+2+k*|z.re|)*(1+1/z.im)

lemma scale_base (N k : ℕ) (z : ℍ) : 1≤ scale N k z ∧ (N:ℝ)≤ scale N k z ∧ 1≤ scale N k z*z.im := by
  let A : ℝ := N+2+k*|z.re|
  have hA : 1≤A := by dsimp [A]; linarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (abs_nonneg z.re), Nat.cast_nonneg (α:=ℝ) N]
  have hn : (N:ℝ)≤A := by dsimp [A]; linarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (abs_nonneg z.re), Nat.cast_nonneg (α:=ℝ) N]
  have h1 : 1≤1+1/z.im := by linarith [one_div_pos.mpr z.im_pos]
  change 1≤A*(1+1/z.im) ∧ (N:ℝ)≤A*(1+1/z.im) ∧ 1≤A*(1+1/z.im)*z.im
  have he : (1+1/z.im)*z.im=z.im+1 := by field_simp [z.im_ne_zero]
  rw [mul_assoc,he]
  exact ⟨one_le_mul_of_one_le_of_one_le hA h1,hn.trans (le_mul_of_one_le_right (by linarith) h1),
    one_le_mul_of_one_le_of_one_le hA (by linarith [z.im_pos])⟩

lemma im_vector (k : ℕ) (z : ℍ) (p : ℤ×ℤ) :
    |(vector k z p).im|=|(p.2:ℝ)| *(k:ℝ)*z.im := by
  simp [vector,Complex.mul_im,Complex.mul_re,abs_mul,abs_of_pos z.im_pos,mul_assoc]

lemma re_vector (k : ℕ) (z : ℍ) (p : ℤ×ℤ) :
    (vector k z p).re=(p.1:ℝ)+(p.2:ℝ)*(k:ℝ)*z.re := by
  simp [vector,Complex.mul_re,mul_assoc]

lemma distortion (N k : ℕ) [NeZero k] (z : ℍ) (p : ℤ×ℤ) :
    1+‖vector 1 UpperHalfPlane.I p‖≤ scale N k z*(1+‖vector k z p‖) := by
  let W := vector k z p
  let B := (1+1/z.im)
  have hB : 1≤B := by dsimp [B]; linarith [one_div_pos.mpr z.im_pos]
  have hk : 1≤(k:ℝ) := by exact_mod_cast NeZero.pos k
  have hbi := (im_vector k z p) ▸ abs_im_le_norm W
  have hB' : 1≤B*z.im := by
    have he : B*z.im=z.im+1 := by dsimp [B]; field_simp [z.im_ne_zero]
    rw [he]; linarith [z.im_pos]
  have hl : |(p.2:ℝ)|≤B*‖W‖ := calc
    _ ≤ |(p.2:ℝ)| *(k*(B*z.im)) := le_mul_of_one_le_right (abs_nonneg _) (one_le_mul_of_one_le_of_one_le hk hB')
    _ = B*(|(p.2:ℝ)| *k*z.im) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbi (by linarith)
  have hj : |(p.1:ℝ)|≤‖W‖+k*|z.re| *|(p.2:ℝ)| := by
    rw [show (p.1:ℝ)=W.re-(p.2:ℝ)*k*z.re by rw [re_vector]; ring]
    apply (show |W.re-(p.2:ℝ)*k*z.re|≤|W.re|+|(p.2:ℝ)*k*z.re| by simpa using abs_sub_le W.re 0 ((p.2:ℝ)*k*z.re)).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) k)]
    linarith [abs_re_le_norm W,show |(p.2:ℝ)| *(k:ℝ)*|z.re|=k*|z.re| *|(p.2:ℝ)| by ring]
  have h0 : ‖vector 1 UpperHalfPlane.I p‖ ≤ |(p.1:ℝ)|+|(p.2:ℝ)| := by
    apply (norm_add_le _ _).trans
    simp [norm_mul,Complex.norm_intCast]
  have hm : k*|z.re| *|(p.2:ℝ)|≤k*|z.re| *(B*‖W‖) := mul_le_mul_of_nonneg_left hl (by positivity)
  have hS := (scale_base N k z).1
  change 1+_≤ scale N k z*(1+‖W‖)
  rw [mul_add,mul_one]
  apply add_le_add hS
  calc
    _ ≤ ‖W‖+k*|z.re| *(B*‖W‖)+B*‖W‖ := h0.trans (add_le_add (hj.trans (add_le_add le_rfl hm)) hl)
    _ ≤ _ := by
      change _≤((N:ℝ)+2+k*|z.re|)*B*‖W‖
      nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (mul_nonneg (by linarith : 0≤B) (norm_nonneg W)),
        mul_nonneg (sub_nonneg.mpr hB) (norm_nonneg W)]

lemma grid (N k : ℕ) [NeZero N] [NeZero k] (z : ℍ) (p : ℤ×ℤ) (m : ℤ)
    (hn : vector k z p+(m:ℂ)/N≠0) : (scale N k z)⁻¹≤‖vector k z p+(m:ℂ)/N‖ := by
  obtain ⟨h1,hN,hy⟩ := scale_base N k z
  have hp : 0<scale N k z := by linarith
  have npos : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have nC : (N:ℂ)≠0 := by exact_mod_cast (NeZero.ne N)
  by_cases h : p.2=0
  · let j := p.1*(N:ℤ)+m
    have he : vector k z p+(m:ℂ)/N=(j:ℂ)/N := by simp [vector,h,j,add_div,nC]
    have hj : j≠0 := by intro e; exact hn (by rw [he,e]; simp)
    have hJ : 1≤|(j:ℝ)| := by exact_mod_cast (show 1≤|j| from abs_pos.mpr hj)
    rw [he,norm_div,Complex.norm_intCast,Complex.norm_natCast,←one_div]
    exact div_le_div₀ (by positivity) hJ npos hN
  · have hz : (scale N k z)⁻¹≤z.im := by rw [←one_div,div_le_iff₀ hp]; linarith
    have hP : 1≤|(p.2:ℝ)| := by exact_mod_cast (show 1≤|p.2| from abs_pos.mpr h)
    have hk : 1≤(k:ℝ) := by exact_mod_cast NeZero.pos k
    have e : (vector k z p+(m:ℂ)/N).im=(vector k z p).im := by simp [Complex.div_im]
    apply hz.trans
    calc
      _ ≤ |(p.2:ℝ)| *(k:ℝ)*z.im := le_mul_of_one_le_left z.im_pos.le (one_le_mul_of_one_le_of_one_le hP hk)
      _ = |(vector k z p+(m:ℂ)/N).im| := by rw [e,im_vector]
      _ ≤ _ := abs_im_le_norm _
end
end TunnellRankinMajorant
end

section
/- A uniform polynomial growth bound for the actual continued lattice sum (uniform on |s| ≤ 12). -/
namespace TunnellRankinMajorant
open Complex TunnellRankinEisenstein TunnellCMRegularized Filter Finset
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

lemma period_vector (k : ℕ) [NeZero k] (z : ℍ) (p : ℤ×ℤ) :
    ((periods k z).latticeEquivProd.symm p:ℂ)=vector k z p := by
  rw [PeriodPair.latticeEquiv_symm_apply]
  simp [periods,vector]

lemma summable_fixed : Summable (fun p : ℤ×ℤ => (1+‖vector 1 UpperHalfPlane.I p‖)^(-(5/2):ℝ)) := by
  let L := periods 1 UpperHalfPlane.I
  have h := ZLattice.summable_norm_rpow L.lattice (-(5/2):ℝ) (by simp; norm_num)
  have h0 : Summable (fun w : L.lattice => if w=0 then (1:ℝ) else 0) := (hasSum_ite_eq 0 1).summable
  have ha : Summable (fun w : L.lattice => (1+‖(w:ℂ)‖)^(-(5/2):ℝ)) := by
    apply (h.add h0).of_nonneg_of_le (fun _ => by positivity)
    intro w
    by_cases e : w=0
    · subst w; norm_num
    · have hw : (w:ℂ)≠0 := fun hz => e (Subtype.ext hz)
      simpa [e] using Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hw) (show ‖(w:ℂ)‖≤1+‖(w:ℂ)‖ by linarith) (by norm_num : -(5/2:ℝ)≤0)
  have he := (L.latticeEquivProd.symm.toEquiv.summable_iff).mpr ha
  apply he.congr
  intro p
  change (1+‖((periods 1 UpperHalfPlane.I).latticeEquivProd.symm p:ℂ)‖)^(-(5/2):ℝ)=_
  rw [period_vector]

lemma periodized (k : ℕ) [NeZero k] (z : ℍ) (a : ℕ) (q s : ℂ) :
    regularized (periods k z) a q s=∑' p : ℤ×ℤ,difference a q (vector k z p) s := by
  unfold regularized
  rw [← (periods k z).latticeEquivProd.symm.toEquiv.tsum_eq (fun w : (periods k z).lattice => difference a q w s)]
  apply tsum_congr
  intro p
  rw [←period_vector]
  rfl

lemma shifted_bound (N k : ℕ) [NeZero N] [NeZero k] (a m : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (z : ℍ) {s : ℂ}, ‖s‖≤12 → 3/4<s.re →
      ‖regularized (periods k z) a ((m:ℂ)/N) s‖≤C*(scale N k z)^27 := by
  obtain ⟨D,hD,h⟩ := summand_weight (K:=24) (show (0:ℝ)≤12 by norm_num) a ((m:ℂ)/N)
  let W (p : ℤ×ℤ) := (1+‖vector 1 UpperHalfPlane.I p‖)^(-(5/2):ℝ)
  refine ⟨D*(∑' p,W p),mul_nonneg hD (tsum_nonneg fun _ => by dsimp [W]; positivity),?_⟩
  intro z s hs hDmn
  have tpos := (scale_base N k z).1
  have e (p : ℤ×ℤ) : ‖difference a ((m:ℂ)/N) (vector k z p) s‖≤D*scale N k z^27*W p := by
    apply h tpos (norm_nonneg _) hs hDmn (by norm_num; linarith [Complex.re_le_norm s]) (distortion _ _ _ _)
    · simpa using grid N k z p 0
    · simpa using grid N k z p (m:ℤ)
    · simpa [mul_div_assoc] using grid N k z p ((a:ℤ)*m)
  have hsum : Summable (fun p => D*scale N k z^27*W p) := summable_fixed.mul_left _
  rw [periodized]
  apply (norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) e)).trans
  apply (Summable.tsum_le_tsum e (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) e) hsum).trans
  rw [tsum_mul_left]
  exact le_of_eq (by ring)

theorem regular_bound (N k : ℕ) [NeZero N] [NeZero k] (χ : ZMod N→ℂ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (z : ℍ) {s : ℂ}, ‖s‖≤12 → 3/4<s.re → ‖regular N k χ z s‖≤C*scale N k z^27 := by
  classical
  choose C hC hh using fun r : ZMod N => shifted_bound N k (aux N) r.val
  let A := ∑ r : ZMod N, ‖χ r‖*C r
  let B := ‖(aux N:ℂ)^2-(aux N:ℂ)‖
  have hA : 0≤A := sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (hC _)
  have hB : 0<B := norm_pos_iff.mpr (aux_ne N)
  refine ⟨A/B,div_nonneg hA hB.le,?_⟩
  intro z s hs hs'
  change ‖(∑ r : ZMod N, χ r*regularized (periods k z) (aux N) ((r.val:ℂ)/N) s) / _‖≤_
  rw [norm_div]
  change _/B≤_
  rw [div_le_iff₀ hB]
  apply (norm_sum_le _ _).trans
  simp only [norm_mul]
  calc
    _ ≤ ∑ r : ZMod N, ‖χ r‖*(C r*scale N k z^27) :=
      sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hh r z hs hs') (norm_nonneg _)
    _ = A*scale N k z^27 := by simp [A,sum_mul,mul_assoc]
    _ = A/B*scale N k z^27*B := by field_simp
end
end TunnellRankinMajorant
end

section
/- Polynomial growth of the continued Eisenstein series, valid throughout the upper half-plane. -/
namespace TunnellRankinMajorant
open Complex Matrix MatrixGroups ModularGroup TunnellRankinEisenstein TunnellCMRegularized
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

def size (z : ℍ) := 1+‖(z:ℂ)‖+1/z.im

lemma size_one (z : ℍ) : 1≤ size z := by
  dsimp [size]; linarith [norm_nonneg (z:ℂ),one_div_pos.mpr z.im_pos]

lemma size_im (z : ℍ) : z.im≤ size z := by
  have e : z.im≤‖(z:ℂ)‖ := Complex.im_le_norm _
  dsimp [size]; linarith [one_div_pos.mpr z.im_pos]

lemma size_inv (z : ℍ) : 1/z.im≤ size z := by
  dsimp [size]; linarith [norm_nonneg (z:ℂ)]

lemma scale_le (N k : ℕ) (z : ℍ) : scale N k z≤((N:ℝ)+2+k)*size z^2 := by
  have h := size_one z
  have hr : |z.re|≤ size z := by
    have e : |z.re|≤‖(z:ℂ)‖ := abs_re_le_norm _
    dsimp [size]; linarith [one_div_pos.mpr z.im_pos]
  have h₁ : (N:ℝ)+2+k*|z.re|≤((N:ℝ)+2+k)*size z := by
    nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α:=ℝ) k),
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (sub_nonneg.mpr h)]
  have h₂ : 1+1/z.im≤ size z := by dsimp [size]; linarith [norm_nonneg (z:ℂ)]
  change _ * _ ≤ _
  calc
    _ ≤ (((N:ℝ)+2+k)*size z)*size z := mul_le_mul h₁ h₂ (by linarith [one_div_pos.mpr z.im_pos]) (by positivity)
    _ = _ := by ring

lemma height_power {s : ℂ} (hs : ‖s‖≤12) (hs' : 3/4<s.re) (z : ℍ) :
    ‖(z.im:ℂ)^(s-1)‖≤ size z^12 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos,Complex.sub_re,Complex.one_re]
  have h := size_one z
  by_cases hy : 1≤ z.im
  · have he : s.re-1≤(12:ℕ) := by norm_num; linarith [Complex.re_le_norm s]
    rw [←Real.rpow_natCast (size z)]
    exact (Real.rpow_le_rpow_of_exponent_le hy he).trans (Real.rpow_le_rpow z.im_pos.le (size_im z) (by positivity))
  · apply (Real.rpow_le_rpow_of_exponent_ge z.im_pos (le_of_not_ge hy) (show (-1:ℝ)≤ s.re-1 by linarith)).trans
    rw [Real.rpow_neg_one,←one_div]
    exact (size_inv z).trans (le_self_pow₀ h (by decide))

end
end TunnellRankinMajorant
end

section
/- Polynomial growth of the continued Eisenstein series, valid throughout the upper half-plane. -/
namespace TunnellRankinMajorant
open Complex Matrix MatrixGroups ModularGroup TunnellRankinEisenstein TunnellCMRegularized
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

theorem eisenstein_bound {N k : ℕ} [NeZero N] [NeZero k] (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, 0≤ C ∧ ∀ (z : ℍ) {s : ℂ}, ‖s‖≤12 → 3/4<s.re →
      ‖eisenstein (k:=k) χ z s‖≤ C*(size z)^66 := by
  obtain ⟨B,hB,hh⟩ := regular_bound N k χ
  refine ⟨B*((N:ℝ)+2+k)^27,by positivity,?_⟩
  intro z s hs hs'
  have h1 := size_one z
  have h2 := (scale_base N k z).1
  have hN : 1≤(N:ℝ) := by exact_mod_cast NeZero.pos N
  have hker : ‖kernel s (N:ℂ)‖≤1 := by
    rw [norm_kernel _ _ (by exact_mod_cast NeZero.ne N),Complex.norm_natCast]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  rw [eisenstein,norm_mul,norm_mul]
  calc
    _ ≤ (size z^12*1)*(B*scale N k z^27) := by
      apply mul_le_mul (mul_le_mul (height_power hs hs' z) hker (norm_nonneg _) (by positivity)) (hh z hs hs') (norm_nonneg _) (by positivity)
    _ ≤ size z^12*(B*(((N:ℝ)+2+k)*size z^2)^27) := by rw [mul_one]; gcongr; apply scale_le
    _ = _ := by
      let A : ℝ := N+2+k
      change size z^12*(B*(A*size z^2)^27)=B*A^27*(size z)^66
      rw [mul_pow]
      calc
        _ = B*A^27*((size z)^12*((size z)^2)^27) := by simp only [mul_left_comm,mul_comm,mul_assoc]
        _ = _ := by rw [←pow_mul,←pow_add]

end
end TunnellRankinMajorant
end

section
/- Polynomial distortion at each cusp and rapid decay of the actual conductor-32 newform. -/
namespace TunnellRankinMajorant
open Complex Matrix MatrixGroups ModularGroup Filter Asymptotics Set ConjAct ModularForm
open UpperHalfPlane hiding I
open scoped Pointwise ModularForm
noncomputable section

lemma fd_geometry (z : ℍ) (hz : z∈fd) : 1/2≤z.im ∧ ‖(z:ℂ)‖≤1+z.im := by
  constructor
  · nlinarith [three_le_four_mul_im_sq_of_mem_fd hz,z.im_pos]
  · apply (norm_le_abs_re_add_abs_im _).trans
    change |z.re|+|z.im|≤1+z.im
    rw [abs_of_pos z.im_pos]
    linarith [hz.2]

lemma denom_bounds (g : SL(2,ℤ)) (z : ℍ) (hz : z∈fd) :
    1/2≤‖denom g z‖ ∧ ‖denom g z‖≤ (|(g 1 0:ℝ)|+|(g 1 1:ℝ)|)*(1+z.im) := by
  obtain ⟨hI,hz'⟩ := fd_geometry z hz
  rw [ModularGroup.denom_apply]
  constructor
  · by_cases h : g 1 0=0
    · have e := g.det_coe
      rw [Matrix.det_fin_two,h] at e
      have hd := Int.eq_one_or_neg_one_of_mul_eq_one' (by simpa using e : g 0 0*g 1 1=1)
      rcases hd with ⟨_,ee⟩|⟨_,ee⟩ <;> rw [h,ee] <;> norm_num
    · have H : 1≤|(g 1 0:ℝ)| := by exact_mod_cast (show 1≤|g 1 0| from abs_pos.mpr h)
      apply (hI.trans (le_mul_of_one_le_left z.im_pos.le H)).trans
      apply le_trans _ (abs_im_le_norm _)
      simp [Complex.mul_im,abs_mul,abs_of_pos z.im_pos]
  · apply (norm_add_le _ _).trans
    rw [norm_mul,Complex.norm_intCast,Complex.norm_intCast]
    nlinarith [mul_le_mul_of_nonneg_left hz' (abs_nonneg (g 1 0:ℝ)),mul_nonneg (abs_nonneg (g 1 1:ℝ)) z.im_pos.le]

theorem cusp_size (g : SL(2,ℤ)) :
    ∃ C : ℝ, 1≤C ∧ ∀ (z : ℍ), z∈fd → size (g • z)≤C*(1+z.im)^2 := by
  let A := |(g 0 0:ℝ)|+|(g 0 1:ℝ)|
  let B := |(g 1 0:ℝ)|+|(g 1 1:ℝ)|
  have hA : 0≤A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB : 0≤B := add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨1+2*A+2*B^2,by nlinarith [sq_nonneg B],?_⟩
  intro z hz
  let H := 1+z.im
  let J := denom g z
  have hH : 1≤H := by dsimp [H]; linarith [z.im_pos]
  obtain ⟨hI,hz'⟩ := fd_geometry z hz
  obtain ⟨hJ,hβ⟩ := denom_bounds g z hz
  have hj : 0<‖J‖ := norm_pos_iff.mpr (denom_ne_zero _ _)
  have hJ' : ‖J‖≤B*H := hβ
  have hα : ‖(g 0 0:ℂ)*(z:ℂ)+(g 0 1:ℂ)‖≤A*H := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_intCast]
    dsimp [A,H]
    nlinarith [mul_le_mul_of_nonneg_left hz' (abs_nonneg (g 0 0:ℝ)),mul_nonneg (abs_nonneg (g 0 1:ℝ)) z.im_pos.le]
  have hnorm : ‖((g • z:ℍ):ℂ)‖≤2*A*H := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    change ‖((g 0 0:ℂ)*(z:ℂ)+(g 0 1:ℂ))/J‖≤_
    rw [norm_div,div_le_iff₀ hj]
    apply hα.trans
    change 1/2≤‖J‖ at hJ
    nlinarith [mul_nonneg (mul_nonneg hA (by linarith : 0≤H)) (sub_nonneg.mpr hJ)]
  have hinv : 1/(g • z).im≤2*B^2*H^2 := by
    rw [ModularGroup.im_smul_eq_div_normSq,Complex.normSq_eq_norm_sq,one_div,inv_div,div_le_iff₀ z.im_pos]
    have hsq := pow_le_pow_left₀ (norm_nonneg J) hJ' 2
    change ‖J‖^2≤_
    nlinarith [mul_nonneg (sq_nonneg (B*H)) (sub_nonneg.mpr hI)]
  unfold size
  change _ ≤ (1+2*A+2*B^2)*H^2
  nlinarith [mul_nonneg (sub_nonneg.mpr hH) (by linarith : 0≤H),mul_nonneg hA (mul_nonneg (sub_nonneg.mpr hH) (by linarith : 0≤H))]

theorem eta_rapid (g : SL(2,ℤ)) (P : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (z : ℍ), z∈fd →
      ‖TunnellEtaValue.etaValue (g • z)‖*(1+z.im)^P≤C := by
  obtain ⟨Γ,hΓ,_,F,hF,_⟩ := TunnellEtaValue.actual_form
  letI : Γ.IsArithmetic := hΓ
  let J := (toConjAct (g:GL (Fin 2) ℝ)⁻¹) • Γ
  letI : J.IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl),map_inv,SpecialLinearGroup.map_mapGL]
      using! Subgroup.IsArithmetic.conj Γ (SpecialLinearGroup.mapGL ℚ g)⁻¹
  let f : CuspForm J 2 := CuspForm.translate F g
  obtain ⟨c,hc,hO⟩ := CuspFormClass.exp_decay_atImInfty' f
  have ho : (fun z : ℍ => f z)=O[atImInfty] fun z => z.im^(-((P+2:ℕ):ℝ)) :=
    hO.trans ((isLittleO_exp_neg_mul_rpow_atTop hc _).isBigO.comp_tendsto tendsto_comap)
  obtain ⟨C,hC⟩ := exists_bound_fundamental_domain_of_isBigO (ModularFormClass.continuous f) ho
  let B := |(g 1 0:ℝ)|+|(g 1 1:ℝ)|
  refine ⟨max 0 C*B^2*3^(P+2),by positivity,?_⟩
  intro z hz
  obtain ⟨hI,hzn⟩ := fd_geometry z hz
  have hH : 1+z.im ≤ 3*z.im := by linarith
  have hB : 0≤B := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hj := (denom_bounds g z hz).2
  have he : TunnellEtaValue.etaValue (g • z)=f z*denom g z^2 := by
    change _=((F:ℍ→ℂ) ∣[(2:ℤ)] g) z*_
    rw [ModularForm.SL_slash_apply,TunnellEtaLevel.physical,←hF]
    rw [_root_.zpow_neg,zpow_ofNat]
    field_simp [denom_ne_zero g z]
  have hh (z : ℍ) (hz : z∈fd) : ‖f z‖*z.im^(P+2)≤ max 0 C := by
    have hu := hC z hz
    rw [Real.rpow_neg z.im_pos.le,Real.rpow_natCast,←div_eq_mul_inv,le_div_iff₀ (pow_pos z.im_pos _)] at hu
    exact hu.trans (le_max_right _ _)
  rw [he,norm_mul,norm_pow]
  calc
    _ ≤ ‖f z‖*(B*(1+z.im))^2*(1+z.im)^P := by gcongr
    _ = ‖f z‖*B^2*(1+z.im)^(P+2) := by rw [pow_add]; ring
    _ ≤ ‖f z‖*B^2*(3*z.im)^(P+2) := by gcongr
    _ = (‖f z‖*z.im^(P+2))*B^2*3^(P+2) := by rw [mul_pow]; ring
    _ ≤ _ := by gcongr; exact hh z hz
end
end TunnellRankinMajorant
end

section
/- Polynomial growth of the continued Eisenstein series, valid throughout the upper half-plane. -/
namespace TunnellRankinMajorant
open Complex Matrix MatrixGroups ModularGroup TunnellRankinEisenstein TunnellCMRegularized
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

lemma vector_meas (k : ℕ) (p : ℤ×ℤ) : Measurable (fun z : ℍ => vector k z p) := by
  unfold vector
  fun_prop

lemma eisenstein_meas {N k : ℕ} [NeZero N] [NeZero k] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    Measurable (fun z : ℍ => eisenstein (k:=k) χ z s) := by
  have hk (f : ℍ→ℂ) (hf : Measurable f) : Measurable (fun z => kernel s (f z)) := by
    apply hf.mul
    apply Complex.continuous_exp.measurable.comp
    exact (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp hf.norm)).const_mul _
  have hd (a : ℕ) (p : ℤ×ℤ) (u : ℂ) : Measurable (fun z : ℍ => difference a u (vector k z p) s) := by
    unfold difference
    apply Measurable.sub <;> apply Measurable.const_mul <;> apply Measurable.sub <;> apply hk
    · exact (vector_meas k p).add_const _
    · exact vector_meas k p
    · exact (vector_meas k p).add_const _
    · exact vector_meas k p
  simp only [eisenstein,regular,periodized]
  apply Measurable.mul
  · apply Measurable.mul_const
    apply Measurable.pow_const
    exact Complex.continuous_ofReal.measurable.comp UpperHalfPlane.continuous_im.measurable
  · apply Measurable.div_const
    apply Finset.measurable_sum
    intro r _
    exact (Measurable.tsum (fun p => hd _ p _)).const_mul _
end
end TunnellRankinMajorant
end

section
/- A locally holomorphic parameter under a dominated integral, via the Cauchy derivative bound. -/
namespace TunnellRankinParameter
open Complex Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma derivative_meas {F : ℂ→α→ℂ} (hF : ∀ s, Measurable (F s)) {s₀ : ℂ}
    (h : ∀ x, DifferentiableAt ℂ (F · x) s₀) :
    AEStronglyMeasurable (fun x => deriv (F · x) s₀) μ := by
  let hstep (n : ℕ) : ℂ := 1/((n:ℂ)+1)
  have hlim : Tendsto hstep atTop (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun n => ?_⟩
    change 1/((n:ℂ)+1)≠0
    exact div_ne_zero one_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  let V (n : ℕ) (x : α) := (hstep n)⁻¹*(F (s₀+hstep n) x-F s₀ x)
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f:=V) (fun n => (((hF _).sub (hF _)).const_mul _).aestronglyMeasurable)
  exact Eventually.of_forall fun x => ((h x).hasDerivAt.tendsto_slope_zero.comp hlim)

theorem analytic_integral {U : Set ℂ} (hU : IsOpen U) {F : ℂ→α→ℂ}
    (hF : ∀ s, Measurable (F s)) (hd : ∀ x, AnalyticOnNhd ℂ (F · x) U)
    {B : α→ℝ} (hi : Integrable B μ) (hb : ∀ᵐ x ∂μ, ∀ s∈U,‖F s x‖≤B x) :
    AnalyticOnNhd ℂ (fun s => ∫ x,F s x ∂μ) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro s₀ hs
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU s₀ hs
  let r := ε/3
  have hr : 0<r := by dsimp [r]; linarith
  have hadd : r+r<ε := by dsimp [r]; linarith
  have sub {s : ℂ} (hs' : s∈ball s₀ r) : closedBall s r⊆U := by
    apply Set.Subset.trans _ hball
    apply Metric.closedBall_subset_ball'
    linarith [show dist s s₀<r from hs']
  have hca {s : ℂ} (hs' : s∈ball s₀ r) (x : α) :
      DiffContOnCl ℂ (F · x) (ball s r) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    exact ((hd x _ (sub hs' (closure_ball_subset_closedBall hw))).differentiableAt).differentiableWithinAt
  have hbound : ∀ᵐ x ∂μ, ∀ s∈ball s₀ r, ‖deriv (F · x) s‖≤B x/r := by
    filter_upwards [hb] with x hx
    intro s hs'
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr (hca hs' x)
      (fun w hw => hx _ (sub hs' (sphere_subset_closedBall hw)))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) (ball_mem_nhds s₀ hr)
    (Eventually.of_forall fun s => (hF s).aestronglyMeasurable)
    (hi.mono' (hF s₀).aestronglyMeasurable (hb.mono fun x hx => hx _ hs))
    (derivative_meas hF (fun x => (hd x s₀ hs).differentiableAt)) hbound (hi.div_const _)
    (Eventually.of_forall fun x s hs' => (hd x s (sub hs' (mem_closedBall_self hr.le))).differentiableAt.hasDerivAt)).2.differentiableAt.differentiableWithinAt

end
end TunnellRankinParameter
end

section
/- The actual ℍ-integrands for unfolding, including their measures' weight-two factors. -/
namespace TunnellRankinIntegral
open Complex Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellCMRegularized
open TunnellRankin TunnellRankinEisenstein TunnellEtaValue TunnellShell
open TunnellRankinCotangent TunnellClassThetaMellin TunnellFullClassTheta
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

lemma gamma_dvd {N L : ℕ} (h : N∣L) {g : SL(2,ℤ)} (hg : g∈Gamma0 L) : g∈Gamma0 N :=
  Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by exact_mod_cast h) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hg))))

lemma char_square {N : ℕ} (χ : DirichletCharacter ℂ N) (hχ : χ.IsQuadratic)
    (g : SL(2,ℤ)) (hg : g∈Gamma0 N) : χ (g 1 1:ZMod N)^2 = 1 := by
  have e := g.property
  rw [Matrix.det_fin_two] at e
  have he := congrArg (fun a : ℤ => (a:ZMod N)) e
  simp [Gamma0_mem.mp hg] at he
  have nn : χ (g 1 1:ZMod N) ≠ 0 := by
    intro hz
    have hm := congrArg χ he
    simp [map_mul,hz] at hm
  rcases hχ (g 1 1:ZMod N) with hh|hh|hh <;> simp_all

variable {d : ℕ} {b : Triple} (hsq : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))

lemma full_action {k : ℕ} [NeZero k] (z : ℍ) (g : SL(2,ℤ)) (hg : g∈Gamma0 (4*(2*d)*k)) :
    (negCharacter d (by omega)) (g 1 1:ZMod (4*(2*d)))*
      full hsq (by omega) hb (multiple ⟨k,NeZero.pos k⟩ (g • z)) =
      denom g z*full hsq (by omega) hb (multiple ⟨k,NeZero.pos k⟩ z) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  have hh := action (k:=k) (negCharacter d (by omega)) z g hg
    (show (1:ℂ)∈domain by norm_num [domain])
  dsimp only at hh
  rw [eisenstein_one hsq hd hb,eisenstein_one hsq hd hb] at hh
  have pos : 0<v d := v_pos (by omega)
  have hn : (2*Real.pi/(v d:ℂ))≠0 := div_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) (by exact_mod_cast pos.ne')
  apply mul_left_cancel₀ hn
  linear_combination hh

lemma full_action_one (z : ℍ) (g : SL(2,ℤ)) (hg : g∈Gamma0 (4*(2*d))) :
    full hsq (by omega) hb (g • z)=(negCharacter d (by omega)) (g 1 1:ZMod (4*(2*d)))*
      denom g z*full hsq (by omega) hb z := by
  have e := full_action hsq hd hb (k:=1) z g (by simpa using hg)
  have e1 (w : ℍ) : multiple ⟨1,by decide⟩ w=w := by ext; simp [multiple]
  rw [e1,e1] at e
  have h := char_square (negCharacter d (by omega)) (negative_quadratic _) g hg
  linear_combination (negCharacter d (by omega)) (g 1 1:ZMod (4*(2*d)))*e -
    full hsq (by omega) hb (g • z)*h

lemma height_cancel (y : ℝ) {J : ℂ} (hn : J≠0) :
    (((y/‖J‖^2:ℝ):ℂ)^2*J^2)*(conj J)^2=(y:ℂ)^2 := by
  have hh : (‖J‖:ℂ)^2=J*conj J := by
    rw [mul_conj,normSq_eq_norm_sq,ofReal_pow]
  rw [ofReal_div,ofReal_pow,hh]
  field_simp [hn]

def stripIntegrand (θ : ℍ → ℂ) (s : ℂ) (z : ℍ) : ℂ :=
  (z.im:ℂ)^2*etaValue z*conj (θ z)*conj ((z.im:ℂ)^(conj s-1))

def integrand {N k : ℕ} [NeZero N] [NeZero k] (χ : DirichletCharacter ℂ N)
    (θ : ℍ → ℂ) (s : ℂ) (z : ℍ) : ℂ :=
  (z.im:ℂ)^2*etaValue z*conj (θ z)*conj (eisenstein (k:=k) χ z (conj s))

theorem strip_row (z : ℍ) (g : Gamma0 (4*(2*d)*4)) (s : ℂ) :
    stripIntegrand (full hsq (by omega) hb) s (g.val • z) =
      stripIntegrand (full hsq (by omega) hb) s z*
        conj (rowTerm (negCharacter d (by omega)) z (conj s) (matrixRow g)) := by
  let G := g.val
  have hg32 := gamma_dvd (by exact ⟨d,by ring⟩ : 32∣4*(2*d)*4) g.property
  have hgN := gamma_dvd (dvd_mul_right _ _) g.property
  let J := denom G z
  have hn : J≠0 := denom_ne_zero _ _
  have hJ : conj J=(G 1 0:ℂ)*conj (z:ℂ)+(G 1 1:ℂ) := by
    simp [J,ModularGroup.denom_apply]
  have HH := height_kernel z.im_pos hn (conj s)
  have HC := height_cancel z.im hn
  simp only [stripIntegrand,TunnellEtaLevel.eta_level _ hg32,
    full_action_one hsq hd hb z g.val hgN,ModularGroup.im_smul_eq_div_normSq,Complex.normSq_eq_norm_sq]
  change (((z.im/‖J‖^2:ℝ):ℂ)^2*(J^2*etaValue z)*conj ((negCharacter d (by omega)) (G 1 1:ZMod (4*(2*d)))*J*full hsq (by omega) hb z))*
      conj ((((z.im/‖J‖^2:ℝ):ℂ))^(conj s-1))=_
  rw [HH]
  simp only [map_mul,rowTerm,matrixRow]
  rw [← hJ]
  linear_combination etaValue z*conj (full hsq (by omega) hb z)*
    conj ((z.im:ℂ)^(conj s-1))*conj ((negCharacter d (by omega)) (G 1 1:ZMod (4*(2*d))))*
    conj (kernel (conj s) (conj J))*HC

end
end TunnellRankinIntegral
end

section
/- The integrand is exactly the periodization of its strip kernel. -/
namespace TunnellRankinIntegral
open Complex Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellCMRegularized
open TunnellRankin TunnellRankinEisenstein TunnellEtaValue TunnellShell TunnellFullClassTheta
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

def liftRow {L : ℕ} (r : Rows L) := (matrixRow_surjective L r).choose

lemma liftRow_spec {L : ℕ} (r : Rows L) : matrixRow (liftRow r)=r :=
  (matrixRow_surjective L r).choose_spec

theorem periodization {d : ℕ} {b : Triple} (hsq : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))
    (z : ℍ) (s : ℂ) (hs : 3/2<s.re) :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    integrand (k:=4) (negCharacter d (by omega)) (full hsq (by omega) hb) s z =
      conj ((negCharacter d (by omega)).LFunction (2*conj s-1))*
      ∑' r : Rows (4*(2*d)*4),stripIntegrand (full hsq (by omega) hb) s ((liftRow r).val • z) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  have e (r : Rows (4*(2*d)*4)) := strip_row hsq hd hb z (liftRow r) s
  simp only [liftRow_spec] at e
  rw [integrand,primitive_factor _ _ (by simpa using hs),
    rows_sum (dvd_mul_right 4 (2*d)),tsum_congr e,tsum_mul_left]
  simp only [stripIntegrand,map_mul,Complex.conj_tsum]
  ring
end
end TunnellRankinIntegral
end

section
/- Integral coset and translation coordinates for the unfolding. -/
namespace TunnellRankinIntegral
open Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellRankinEisenstein
noncomputable section

lemma t_row (n : ℤ) (g : SL(2,ℤ)) (j : Fin 2) : (T^n*g).val 1 j=g.val 1 j := by
  change ((T^n).val*g.val) 1 j=_
  simp [coe_T_zpow,Matrix.mul_apply,Fin.sum_univ_two]

lemma trans_mat {g : SL(2,ℤ)} (hc : g 1 0=0) (he : g 1 1=1) : g=T^(g 0 1) := by
  have det := g.det_coe
  rw [Matrix.det_fin_two,hc,he] at det
  have ha : g 0 0=1 := by simpa using det
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha,hc,he,coe_T_zpow,show (1:Fin (0+2))=(1:Fin 2) from rfl]

lemma translation_of_row {g h : SL(2,ℤ)} (eq : ∀ j, g 1 j=h 1 j) : ∃ n : ℤ, g=T^n*h := by
  let m := g*h⁻¹
  have hc : m 1 0=0 := by
    change (g.val*(h⁻¹).val) 1 0=0
    rw [Matrix.mul_apply,Fin.sum_univ_two,SpecialLinearGroup.SL2_inv_expl]
    simp [Matrix.mul_apply,Fin.sum_univ_two,eq]; ring
  have he : m 1 1=1 := by
    have det := h.det_coe
    rw [Matrix.det_fin_two] at det
    change (g.val*(h⁻¹).val) 1 1=1
    rw [Matrix.mul_apply,Fin.sum_univ_two,SpecialLinearGroup.SL2_inv_expl]
    simp [Matrix.mul_apply,Fin.sum_univ_two,eq]; linear_combination det
  exact ⟨m 0 1,by rw [←trans_mat hc he]; simp [m]⟩

def translationRow {L : ℕ} (p : ℤ×Rows L) : Gamma0 L :=
  ⟨T^p.1*(liftRow p.2).val, Gamma0_mem.mpr (by rw [t_row]; exact Gamma0_mem.mp (liftRow p.2).property)⟩

lemma translationRow_row {L : ℕ} (p : ℤ×Rows L) : matrixRow (translationRow p)=p.2 := by
  rw [←liftRow_spec p.2]
  apply Subtype.ext; apply Prod.ext <;> exact t_row _ _ _

lemma translationRow_bijective (L : ℕ) : Function.Bijective (translationRow (L:=L)) := by
  constructor
  · rintro ⟨n,r⟩ ⟨m,t⟩ eq
    have e := congrArg matrixRow eq
    simp only [translationRow_row] at e
    change r=t at e
    subst t
    have eh := congrArg Subtype.val eq
    change T^n*(liftRow r).val=T^m*(liftRow r).val at eh
    have ee := congrArg (fun g : SL(2,ℤ) => g 0 1) (mul_right_cancel eh)
    simp [coe_T_zpow] at ee
    subst m; rfl
  · intro g
    let r := matrixRow g
    have e := liftRow_spec r
    have ej (j : Fin 2) : g.val 1 j=(liftRow r).val 1 j := by
      fin_cases j
      · exact congrArg (fun x : Rows L => x.val.1) e.symm
      · exact congrArg (fun x : Rows L => x.val.2) e.symm
    obtain ⟨n,hn⟩ := translation_of_row ej
    exact ⟨(n,r),Subtype.ext hn.symm⟩

abbrev Cosets (L : ℕ) := SL(2,ℤ) ⧸ Gamma0 L

def rep {L : ℕ} (q : Cosets L) : SL(2,ℤ) := q.out⁻¹

def cosetProd {L : ℕ} (p : Cosets L × Gamma0 L) : SL(2,ℤ) := p.2.val*rep p.1

lemma cosetProd_class {L : ℕ} (q : Cosets L) (g : Gamma0 L) :
    (QuotientGroup.mk (cosetProd (q,g))⁻¹:Cosets L)=q := by
  change QuotientGroup.mk ((g.val*q.out⁻¹)⁻¹)=q
  rw [_root_.mul_inv_rev,inv_inv,QuotientGroup.mk_mul_of_mem _ ((Gamma0 L).inv_mem g.property)]
  exact Quotient.out_eq' _

lemma cosetProd_bijective (L : ℕ) : Function.Bijective (cosetProd (L:=L)) := by
  constructor
  · rintro ⟨q,g⟩ ⟨w,h⟩ eq
    have e := congrArg (fun γ : SL(2,ℤ) => (QuotientGroup.mk γ⁻¹:Cosets L)) eq
    rw [cosetProd_class,cosetProd_class] at e
    subst w
    exact Prod.ext rfl (Subtype.ext (mul_right_cancel eq))
  · intro g
    let q : Cosets L := QuotientGroup.mk g⁻¹
    have he : ((g⁻¹:SL(2,ℤ)):Cosets L)=((q.out:SL(2,ℤ)):Cosets L) := (Quotient.out_eq' q).symm
    have hh := QuotientGroup.eq.mp he
    rw [inv_inv] at hh
    exact ⟨(q,⟨g*q.out,hh⟩),by simp [cosetProd,rep]⟩

def tiles (L : ℕ) : Cosets L × (ℤ × Rows L) ≃ SL(2,ℤ) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.ofBijective _ (translationRow_bijective L))).trans
    (Equiv.ofBijective _ (cosetProd_bijective L))

lemma tiles_apply {L : ℕ} (q : Cosets L) (n : ℤ) (r : Rows L) :
    tiles L (q,n,r)=T^n*(liftRow r).val*rep q := rfl
end
end TunnellRankinIntegral
end

section
/- The open modular polygon tiles almost every point exactly twice when indexed by SL₂(ℤ). -/
namespace TunnellRankinDomain
open Complex Matrix MatrixGroups ModularGroup UpperHalfPlane Set MeasureTheory Metric
open scoped Pointwise Modular
noncomputable section

lemma vertical_null (r : ℝ) : volume {z : ℂ | z.re=r}=0 := by
  let s := ({r}:Set ℝ) ×ˢ (univ:Set ℝ)
  have e : ({z : ℂ | z.re=r}:Set ℂ) = measurableEquivRealProd ⁻¹' s := by ext; simp [s]
  rw [e,volume_preserving_equiv_real_prod.measure_preimage_equiv,Measure.volume_eq_prod]
  simp [s]

lemma boundary_null : volume (fd\fdo)=0 := by
  have h : volume (UpperHalfPlane.coe '' (fd\fdo))=0 := by
    apply measure_mono_null (t:=(sphere (0:ℂ) 1 ∪ {z : ℂ | z.re=1/2}) ∪ {z : ℂ | z.re= -(1/2)})
    · rintro _ ⟨z,⟨hz,hn⟩,rfl⟩
      change 1≤normSq (z:ℂ) ∧ |z.re|≤1/2 at hz
      change ¬(1<normSq (z:ℂ) ∧ |z.re|<1/2) at hn
      by_cases eq : ‖(z:ℂ)‖=1
      · exact Or.inl (Or.inl (by simpa using eq))
      have hnorm : 1<normSq (z:ℂ) := by
        rw [normSq_eq_norm_sq] at hz ⊢
        apply (one_lt_sq_iff₀ (norm_nonneg _)).mpr
        exact lt_of_le_of_ne ((one_le_sq_iff₀ (norm_nonneg _)).mp hz.1) (Ne.symm eq)
      have ha : |z.re|=1/2 := le_antisymm hz.2 (le_of_not_gt fun hh => hn ⟨hnorm,hh⟩)
      rcases abs_choice z.re with h|h
      · exact Or.inl (Or.inr (by change z.re=1/2; linarith))
      · exact Or.inr (by change z.re= -(1/2); linarith)
    · exact measure_union_null (measure_union_null (Measure.addHaar_sphere volume (0:ℂ) 1) (vertical_null _)) (vertical_null _)
  rw [UpperHalfPlane.volume_eq_lintegral,Measure.restrict_eq_zero.mpr h,lintegral_zero_measure]

lemma smul_null (g : SL(2,ℤ)) (s : Set ℍ) (hs : volume s=0) :
    volume ((g • ·) ⁻¹' s) = 0 :=
  measure_preimage_smul_null hs (g:GL (Fin 2) ℝ)

theorem ae_pair : ∀ᵐ z : ℍ, ∃ g : SL(2,ℤ),
    ∀ h : SL(2,ℤ), h • z∈fdo ↔ h=g ∨ h= -g := by
  letI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2→Fin 2→ℤ))
  letI : Countable (SL(2,ℤ)) := Function.Injective.countable (f:=fun g : SL(2,ℤ) => g.val) Subtype.val_injective
  have he : ∀ᵐ z : ℍ, ∀ g : SL(2,ℤ), g • z∉fd\fdo := by
    apply ae_all_iff.mpr
    intro g
    apply ae_iff.mpr
    convert smul_null g _ boundary_null using 2
    ext z
    simp
  filter_upwards [he] with z hz
  obtain ⟨g,hg⟩ := exists_smul_mem_fd z
  have hg' : g • z∈fdo := by by_contra e; exact hz g ⟨hg,e⟩
  refine ⟨g,fun h => ⟨fun hh => ?_,?_⟩⟩
  · have H : (h*g⁻¹) • (g • z)∈fdo := by simpa [mul_smul] using hh
    rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hg' H with eq|eq
    · left; exact mul_inv_eq_one.mp eq
    · right
      calc
        h=(h*g⁻¹)*g := by simp
        _= -g := by rw [eq]; simp
  · rintro (rfl|rfl) <;> simpa only [SL_neg_smul] using hg'

end
end TunnellRankinDomain
end

section
/- Change of variables over the modular polygon, with the factor of two from the center. -/
namespace TunnellRankinDomain
open Complex Matrix MatrixGroups ModularGroup UpperHalfPlane Set MeasureTheory
open scoped Pointwise ENNReal
noncomputable section

local instance : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2→Fin 2→ℤ))
local instance : Countable (SL(2,ℤ)) := Function.Injective.countable (f:=fun g : SL(2,ℤ) => g.val) Subtype.val_injective

def mark : ℍ→ℝ≥0∞ := fdo.indicator (fun _ => 1)

lemma mark_meas : Measurable mark := measurable_const.indicator isOpen_fdo.measurableSet

lemma neg_distinct (g : SL(2,ℤ)) : g≠ -g := by
  intro eq
  have e := congrArg (·*g⁻¹) eq
  have h : (1:SL(2,ℤ))= -1 := by simpa using e
  have := congrArg (fun m : SL(2,ℤ) => m.val 0 0) h
  norm_num at this

lemma ae_mark : ∀ᵐ z : ℍ, ∑' g : SL(2,ℤ), mark (g⁻¹ • z)=2 := by
  classical
  filter_upwards [ae_pair] with z hz
  obtain ⟨w,hw⟩ := hz
  change (∑' g : SL(2,ℤ),mark (((Equiv.inv _) g) • z))=2
  rw [(Equiv.inv (SL(2,ℤ))).tsum_eq (fun g => mark (g • z))]
  have e : ∀ g : SL(2,ℤ), mark (g • z) = if g=w ∨ g= -w then 1 else 0 := by
    intro g
    change (if g • z ∈ fdo then 1 else 0)=_
    rw [hw]
    split_ifs <;> rfl
  simp_rw [e]
  rw [tsum_eq_sum (s:={w,-w}) (fun x hx => if_neg (by simpa using hx))]
  rw [Finset.sum_insert (by simpa using neg_distinct w),Finset.sum_singleton]
  norm_num

def pull (g : SL(2,ℤ)) (f : ℍ→ℝ≥0∞) (z : ℍ) := mark (g⁻¹ • z)*f z

lemma pull_meas (g : SL(2,ℤ)) {f : ℍ→ℝ≥0∞} (hf : Measurable f) : Measurable (pull g f) :=
  (mark_meas.comp (measurePreserving_smul ((g⁻¹:SL(2,ℤ)):GL (Fin 2) ℝ) volume).measurable).mul hf

lemma pull_eq (g : SL(2,ℤ)) {f : ℍ→ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in fdo, f (g • z)=∫⁻ z, pull g f z := by
  have h : MeasurePreserving (fun z : ℍ => g • z) := measurePreserving_smul (g:GL (Fin 2) ℝ) volume
  rw [←h.lintegral_comp (pull_meas g hf),←lintegral_indicator isOpen_fdo.measurableSet]
  apply lintegral_congr
  intro z
  by_cases hz : z∈fdo <;> simp [pull,mark,hz]

theorem tiles_integral {f : ℍ→ℝ≥0∞} (hf : Measurable f) :
    (∑' g : SL(2,ℤ),∫⁻ z in fdo,f (g • z))=2*∫⁻ z,f z := by
  simp_rw [pull_eq _ hf]
  rw [←lintegral_tsum (fun g => (pull_meas g hf).aemeasurable),←lintegral_const_mul _ hf]
  apply lintegral_congr_ae
  filter_upwards [ae_mark] with z hz
  change (∑' g : SL(2,ℤ),mark (g⁻¹ • z)*f z)=2*f z
  rw [ENNReal.tsum_mul_right,hz]
end
end TunnellRankinDomain
end

section
/- Tonelli unfolding over the width-one horizontal strip; the signed rows count both central lifts. -/
namespace TunnellRankinIntegral
open Complex Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellRankinEisenstein
open TunnellRankinDomain UpperHalfPlane MeasureTheory Set
open scoped Pointwise ENNReal
noncomputable section

def stripSet : Set ℍ := (fun z : ℍ => z.re) ⁻¹' Ico 0 1

lemma meas_strip : MeasurableSet stripSet := measurableSet_Ico.preimage continuous_re.measurable

lemma strip_at (n : ℤ) (z : ℍ) : T^n • z∈stripSet ↔ n= -⌊z.re⌋ := by
  change (T^n • z).re∈Ico 0 1 ↔ _
  rw [re_T_zpow_smul,←Int.floor_eq_zero_iff,Int.floor_add_intCast]
  omega

lemma partition (f : ℍ→ℝ≥0∞) (hp : ∀ (n : ℤ) z, f (T^n • z)=f z) (z : ℍ) :
    (∑' n : ℤ,stripSet.indicator f (T^n • z))=f z := by
  classical
  simp only [Set.indicator_apply,strip_at,hp]
  simp

theorem unfold_nonneg (L : ℕ) {f : ℍ→ℝ≥0∞} (hf : Measurable f)
    (hp : ∀ (n : ℤ) z, f (T^n • z)=f z) :
    (∑' (q : Cosets L) (r : Rows L), ∫⁻ z in fdo, f (((liftRow r).val*rep q) • z))=
      2*∫⁻ z in stripSet, f z := by
  let u := stripSet.indicator f
  have hu : Measurable u := hf.indicator meas_strip
  have hm (g : SL(2,ℤ)) : Measurable (fun z : ℍ => u (g • z)) :=
    hu.comp (measurePreserving_smul (g:GL (Fin 2) ℝ) volume).measurable
  have e (q : Cosets L) (r : Rows L) :
      (∑' n : ℤ, ∫⁻ z in fdo,u ((tiles L (q,n,r)) • z))=
        ∫⁻ z in fdo,f (((liftRow r).val*rep q) • z) := by
    rw [←lintegral_tsum (fun n => (hm (tiles L (q,n,r))).aemeasurable)]
    apply lintegral_congr
    intro z
    simp only [tiles_apply,mul_assoc,mul_smul]
    exact partition f hp _
  calc
    _ = ∑' (q : Cosets L) (r : Rows L) (n : ℤ),∫⁻ z in fdo,u ((tiles L (q,n,r)) • z) := by simp_rw [e]
    _ = ∑' (q : Cosets L) (n : ℤ) (r : Rows L),∫⁻ z in fdo,u ((tiles L (q,n,r)) • z) :=
      tsum_congr fun q => ENNReal.tsum_comm
    _ = ∑' p : Cosets L × (ℤ×Rows L),∫⁻ z in fdo,u ((tiles L p) • z) := by
      rw [ENNReal.tsum_prod']
      apply tsum_congr
      intro q
      rw [ENNReal.tsum_prod']
    _ = ∑' g : SL(2,ℤ), ∫⁻ z in fdo, u (g • z) :=
      (tiles L).tsum_eq (fun g : SL(2,ℤ) => ∫⁻ z in fdo,u (g • z))
    _ = _ := by rw [tiles_integral hu,lintegral_indicator meas_strip]
end
end TunnellRankinIntegral
end

section
/- Pushforward to the width-one strip and the complex-valued unfolding identity. -/
namespace TunnellRankinIntegral
open Complex Matrix MatrixGroups ModularGroup TunnellRankinEisenstein
open UpperHalfPlane MeasureTheory Set
open scoped ENNReal
noncomputable section

def wrap (z : ℍ) := T^(-⌊z.re⌋) • z

lemma wrap_meas : Measurable wrap := by
  apply UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff.mp
  have hI : Measurable (fun z : ℍ => -⌊z.re⌋) :=
    (Int.measurable_floor.comp UpperHalfPlane.continuous_re.measurable).neg
  have eq : UpperHalfPlane.coe ∘ wrap = fun z : ℍ => (z:ℂ)+((-⌊z.re⌋:ℤ):ℂ) := by
    funext z
    exact coe_T_zpow_smul_eq z
  rw [eq]
  exact UpperHalfPlane.measurable_coe.add ((measurable_of_countable (fun n : ℤ => (n:ℂ))).comp hI)

lemma wrap_shift (n : ℤ) (z : ℍ) : wrap (T^n • z)=wrap z := by
  simp only [wrap,re_T_zpow_smul,Int.floor_add_intCast,←mul_smul,←_root_.zpow_add]
  rw [show -(⌊z.re⌋+n)+n= -⌊z.re⌋ by omega]

lemma wrap_on {z : ℍ} (hz : z∈stripSet) : wrap z=z := by
  rw [wrap,Int.floor_eq_zero_iff.mpr hz,neg_zero,zpow_zero,one_smul]

def tileMatrix {L : ℕ} (p : Cosets L × Rows L) := (liftRow p.2).val*rep p.1

def tileMap {L : ℕ} (p : Cosets L × Rows L) (z : ℍ) := wrap (tileMatrix p • z)

lemma tileMap_meas {L : ℕ} (p : Cosets L × Rows L) : Measurable (tileMap p) :=
  wrap_meas.comp (measurePreserving_smul (tileMatrix p:GL (Fin 2) ℝ) volume).measurable

def tileMeasure {L : ℕ} (p : Cosets L × Rows L) : Measure ℍ :=
  (volume.restrict fdo).map (tileMap p)

lemma tileMeasure_sum (L : ℕ) : Measure.sum (tileMeasure (L:=L))=(2:ℝ≥0∞) • volume.restrict stripSet := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_sum_measure,ENNReal.tsum_prod',lintegral_smul_measure]
  have e (p : Cosets L × Rows L) : ∫⁻ z,f z ∂tileMeasure p=∫⁻ z in fdo, f (tileMap p z) :=
    lintegral_map hf (tileMap_meas p)
  simp_rw [e]
  change (∑' (q : Cosets L) (r : Rows L),∫⁻ z in fdo,(f ∘ wrap) (((liftRow r).val*rep q) • z))=2*∫⁻ z in stripSet,f z
  rw [unfold_nonneg L (hf.comp wrap_meas) (fun n z => congrArg f (wrap_shift n z))]
  congr 1
  exact setLIntegral_congr_fun meas_strip fun z hz => congrArg f (wrap_on hz)

theorem unfold_complex (L : ℕ) {f : ℍ→ℂ} (hf : Measurable f)
    (hi : IntegrableOn f stripSet) (hp : ∀ (n : ℤ) z, f (T^n • z)=f z) :
    HasSum (fun p : Cosets L × Rows L => ∫ z in fdo, f (tileMatrix p • z))
      (2*∫ z in stripSet,f z) := by
  have hsum : Integrable f (Measure.sum (tileMeasure (L:=L))) := by
    rw [tileMeasure_sum]
    exact hi.smul_measure (by norm_num)
  have e := hasSum_integral_measure hsum
  rw [tileMeasure_sum,integral_smul_measure] at e
  have ee : (2:ℝ≥0∞).toReal • (∫ z in stripSet,f z)=2*∫ z in stripSet,f z := by
    simp [Complex.real_smul]
  rw [ee] at e
  apply e.congr_fun
  intro p
  rw [tileMeasure,integral_map (tileMap_meas p).aemeasurable hf.stronglyMeasurable.aestronglyMeasurable]
  simp only [tileMap,wrap,hp]

end
end TunnellRankinIntegral
end

section
/- Remove the hyperbolic density on the horizontal strip and integrate in height. -/
namespace TunnellRankinIntegral
open Complex UpperHalfPlane MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

def rect : Set (ℝ×ℝ) := Ioi 0 ×ˢ Ico 0 1

def planeCoords : ℂ ≃ᵐ ℝ×ℝ := measurableEquivRealProd.trans MeasurableEquiv.prodComm

def coords (z : ℍ) : ℝ×ℝ := (z.im,z.re)

lemma plane_preserving : MeasurePreserving planeCoords := by
  have h : MeasurePreserving (Prod.swap : ℝ×ℝ→ℝ×ℝ) := by
    simpa only [Measure.volume_eq_prod] using (Measure.measurePreserving_swap (μ:=volume) (ν:=volume) :
      MeasurePreserving (Prod.swap : ℝ×ℝ→ℝ×ℝ) (volume.prod volume) (volume.prod volume))
  exact h.comp volume_preserving_equiv_real_prod

lemma coords_image : planeCoords '' (UpperHalfPlane.coe '' stripSet)=rect := by
  ext p
  constructor
  · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨z.im_pos,hz⟩
  · rintro ⟨hy,hx⟩
    let z : ℍ := ⟨⟨p.2,p.1⟩,hy⟩
    exact ⟨z,⟨z,hx,rfl⟩,Prod.ext rfl rfl⟩

lemma coords_embedding : MeasurableEmbedding coords :=
  planeCoords.measurableEmbedding.comp UpperHalfPlane.measurableEmbedding_coe

lemma coords_preserving : MeasurePreserving coords
    ((volume.comap UpperHalfPlane.coe).restrict stripSet) (volume.restrict rect) := by
  have hc : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe,UpperHalfPlane.measurableEmbedding_coe.map_comap _⟩
  have h := hc.restrict_image_emb UpperHalfPlane.measurableEmbedding_coe stripSet
  rw [Measure.restrict_restrict_of_subset (image_subset_range _ _)] at h
  have hh := plane_preserving.restrict_image_emb planeCoords.measurableEmbedding (UpperHalfPlane.coe '' stripSet)
  rw [coords_image] at hh
  exact hh.comp h

def density (z : ℍ) : ℝ≥0 := (1/⟨z.im,z.im_pos.le⟩)^2

lemma density_meas : Measurable density := by
  apply Measurable.pow_const
  apply Measurable.div measurable_const
  exact UpperHalfPlane.continuous_im.measurable.subtype_mk

lemma density_cancel (z : ℍ) (a : ℂ) : density z • ((z.im:ℂ)^2*a)=a := by
  change (((1/z.im)^2:ℝ):ℂ)*((z.im:ℂ)^2*a)=a
  have nz : (z.im:ℂ)≠0 := by exact_mod_cast z.im_ne_zero
  push_cast
  field_simp

lemma coords_integral (f : ℝ×ℝ→ℂ) :
    (∫ z in stripSet, (z.im:ℂ)^2*f (coords z))=∫ p in rect,f p := by
  rw [UpperHalfPlane.volume_def,restrict_withDensity meas_strip]
  change (∫ z,(z.im:ℂ)^2*f (coords z) ∂((volume.comap UpperHalfPlane.coe).restrict stripSet).withDensity (fun z => (density z:ℝ≥0∞)))=_
  rw [integral_withDensity_eq_integral_smul density_meas]
  simp_rw [density_cancel]
  exact coords_preserving.integral_comp coords_embedding f

lemma coords_integrable (f : ℝ×ℝ→ℂ) :
    IntegrableOn (fun z : ℍ => (z.im:ℂ)^2*f (coords z)) stripSet ↔ IntegrableOn f rect := by
  unfold IntegrableOn
  rw [UpperHalfPlane.volume_def,restrict_withDensity meas_strip]
  change Integrable _ (((volume.comap UpperHalfPlane.coe).restrict stripSet).withDensity (fun z => (density z:ℝ≥0∞))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul density_meas]
  simp_rw [density_cancel]
  exact coords_preserving.integrable_comp_emb coords_embedding

lemma strip_fubini (f : ℝ×ℝ→ℂ) (hi : IntegrableOn f rect) :
    (∫ z in stripSet, (z.im:ℂ)^2*f (coords z))=∫ y in Ioi (0:ℝ), ∫ x in Ico (0:ℝ) 1,f (y,x) := by
  rw [coords_integral,Measure.volume_eq_prod]
  apply setIntegral_prod
  change IntegrableOn f rect (volume.prod volume)
  exact hi
end
end TunnellRankinIntegral
end

section
/- Finiteness of the hyperbolic measure of the open modular polygon. -/
namespace TunnellRankinIntegral
open Complex Matrix MatrixGroups ModularGroup UpperHalfPlane MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

lemma coords_preserving_set (S : Set ℍ) : MeasurePreserving coords
    ((volume.comap UpperHalfPlane.coe).restrict S) (volume.restrict (coords '' S)) := by
  have hc : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe,UpperHalfPlane.measurableEmbedding_coe.map_comap _⟩
  have h := hc.restrict_image_emb UpperHalfPlane.measurableEmbedding_coe S
  rw [Measure.restrict_restrict_of_subset (image_subset_range _ _)] at h
  have hh := plane_preserving.restrict_image_emb planeCoords.measurableEmbedding (UpperHalfPlane.coe '' S)
  rw [Set.image_image] at hh
  exact hh.comp h

lemma fdo_finite : volume fdo < ∞ := by
  let S : Set (ℝ×ℝ) := Ioi (1/4) ×ˢ Icc (-1) 1
  have sub : coords '' fdo⊆S := by
    rintro _ ⟨z,hz,rfl⟩
    change z.im∈Ioi (1/4) ∧ z.re∈Icc (-1) 1
    have hh := three_lt_four_mul_im_sq_of_mem_fdo hz
    have he := abs_lt.mp hz.2
    exact ⟨by change (1:ℝ)/4<z.im; nlinarith [z.im_pos],by constructor <;> linarith⟩
  have hr : IntegrableOn (fun y : ℝ => y^(-2:ℝ)) (Ioi (1/4)) := integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hi : IntegrableOn (fun p : ℝ×ℝ => p.1^(-2:ℝ)) S := by
    unfold IntegrableOn S
    rw [Measure.volume_eq_prod,←Measure.prod_restrict]
    exact hr.comp_fst _
  have hc := (coords_preserving_set fdo).integrable_comp_emb (g:=fun p : ℝ×ℝ => p.1^(-2:ℝ)) coords_embedding
  have hf := (hc.mpr (hi.mono_set sub)).2
  rw [UpperHalfPlane.volume_def,withDensity_apply _ isOpen_fdo.measurableSet]
  change (∫⁻ z in fdo, (density z:ℝ≥0∞) ∂volume.comap UpperHalfPlane.coe)<⊤
  have he (z : ℍ) : (density z:ℝ≥0∞)=‖z.im^(-2:ℝ)‖ₑ := by
    rw [show (-2:ℝ)=-(2:ℕ) by norm_num,Real.rpow_neg z.im_pos.le,Real.rpow_natCast,
      Real.enorm_of_nonneg (by positivity)]
    rw [show (z.im^2)⁻¹=(density z:ℝ) by change (z.im^2)⁻¹=(1/z.im)^2; rw [one_div,inv_pow]]
    simp
  simp_rw [he]
  exact hf

end
end TunnellRankinIntegral
end

section
/- The horizontal integral contains the full ideal class theta; its constant contributes zero. -/
namespace TunnellRankinIntegral
open Complex AddCircle Set Function ModularForm TunnellRankin TunnellCMLSeries TunnellClassThetaMellin
open TunnellFullClassTheta TunnellShell TunnellEtaValue MeasureTheory
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

lemma circle_mean {a : ℕ→ℂ} (ha : Summable a) :
    (∫ x : AddCircle (1:ℝ),circleSeries a x ∂haarAddCircle)=a 0 := by
  let u (n : ℕ) : ℂ := if n=0 then 1 else 0
  have hu : Summable u := (hasSum_ite_eq 0 (1:ℂ)).summable
  have hS : circleSeries u=1 := by
    unfold circleSeries
    rw [tsum_eq_single 0]
    · ext x
      simp [u,fourier_zero]
    · intro j hj
      ext x
      simp [u,hj]
  have eq := (circle_parseval ha hu).tsum_eq
  rw [hS] at eq
  have hh (n : ℕ) : a n*conj (u n)=if n=0 then a 0 else 0 := by
    by_cases e : n=0 <;> simp [u,e]
  simpa [hh] using eq.symm

lemma horizontal_full {d : ℕ} {b : Triple} (hs : Squarefree (2*d)) (hd : d%4=1)
    (hb : b∈shell (2*d)) {t : ℝ} (ht : 0<t) :
    (∫ x : ℝ in 0..1, etaValue (point x t ht)*conj (full hs (by omega) hb (point x t ht)))=
      2*strip d t := by
  letI := classFintype hs (by omega) hb
  let A := circleSeries (mode (twistA 1) t)
  let B := circleSeries (mode (fun m => (idealCoeff d m:ℂ)) t)
  let H : ℂ := Fintype.card (TunnellToricClass.ProperIdealClass b)
  let F (x : AddCircle (1:ℝ)) := A x*conj (H+2*B x)
  have e := fourierCoeff_eq_intervalIntegral F 0 0
  simp only [fourierCoeff,neg_zero,fourier_zero,one_smul,div_one,zero_add] at e
  have eH (x : ℝ) : F (x : AddCircle (1:ℝ))=etaValue (point x t ht)*conj (full hs (by omega) hb (point x t ht)) := by
    rw [TunnellEtaLevel.physical,full_expansion]
    simp only [F,A,B,H,circle_eta x t ht,circle_theta d x t ht]
  rw [←intervalIntegral.integral_congr (fun x _ => eH x),←e]
  change (∫ x : AddCircle (1:ℝ),F x ∂haarAddCircle)=_
  have hmean : ∫ x : AddCircle (1:ℝ),A x ∂haarAddCircle=0 := by
    obtain ⟨C,hC⟩ := base_growth
    simpa [A,mode,twistA,gaussCoeff,twistSign] using circle_mean (summable_mode hC ht)
  have ef (x : AddCircle (1:ℝ)) : F x=conj H*A x + 2*(conj (B x)*A x) := by
    simp only [F,map_add,map_mul,map_ofNat]; ring
  simp_rw [ef]
  rw [integral_add,integral_const_mul,integral_const_mul,hmean,mul_zero,zero_add]
  · rfl
  · exact A.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      |>.const_mul _
  · apply Integrable.const_mul
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (continuous_star.comp B.continuous).mul A.continuous
end
end TunnellRankinIntegral
end

section
/- Uniform-in-horizontal-coordinate decay for polynomially bounded Fourier coefficients. -/
namespace TunnellRankinIntegral
open Complex MeasureTheory TunnellRankin AddCircle
open scoped Nat
noncomputable section

lemma exp_neg_le_ratio {x : ℝ} (hx : 0<x) (m : ℕ) :
    Real.exp (-x) ≤ (m.factorial:ℝ)/x^m := by
  have h := Real.pow_div_factorial_le_exp x hx.le m
  have h0 : 0<(m.factorial:ℝ) := by positivity
  rw [Real.exp_neg,←one_div,div_le_div_iff₀ (Real.exp_pos x) (pow_pos hx m),one_mul]
  simpa only [mul_comm] using (div_le_iff₀ h0).mp h

lemma coefficient_bound {k : ℕ} {a : ℕ→ℂ} {C : ℝ} (hC : 0≤C) (hz : a 0=0)
    (hg : ∀ m : ℕ, ‖a m‖≤C*(m:ℝ)^k) (n : ℕ) {y : ℝ} (hy : 0<y) :
    ‖mode a (4*y) n‖ ≤ (C*((k+2).factorial:ℝ)/y^(k+2)*Real.exp (-y))*((n:ℝ)^2)⁻¹ := by
  by_cases hn : n=0
  · subst n; simp [mode,hz]
  have hp : 0<(n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hp1 : 1≤(n:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have he : Real.exp (-(4*y/2)*n) ≤ Real.exp (-(y*n))*Real.exp (-y) := by
    rw [←Real.exp_add,Real.exp_le_exp]
    nlinarith [mul_nonneg hy.le (sub_nonneg.mpr hp1)]
  rw [mode,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (C*(n:ℝ)^k)*(((k+2).factorial:ℝ)/(y*n)^(k+2)*Real.exp (-y)) := by
      exact mul_le_mul (hg n) (he.trans (mul_le_mul_of_nonneg_right (exp_neg_le_ratio (mul_pos hy hp) _) (Real.exp_pos _).le))
        (Real.exp_pos _).le (mul_nonneg hC (pow_nonneg hp.le _))
    _ = _ := by rw [mul_pow,pow_add (n:ℝ)]; field_simp [hp.ne',hy.ne'] <;> ring

theorem circle_bound {k : ℕ} {a : ℕ→ℂ} {C : ℝ} (hC : 0≤C) (hz : a 0=0)
    (hg : ∀ m : ℕ, ‖a m‖≤C*(m:ℝ)^k) :
    ∃ D : ℝ, 0≤D ∧ ∀ y : ℝ, 0<y → ∀ x : AddCircle (1:ℝ),
      ‖circleSeries (mode a (4*y)) x‖≤D/y^(k+2)*Real.exp (-y) := by
  let S := ∑' n : ℕ, ((n:ℝ)^2)⁻¹
  have hsum := Real.summable_nat_pow_inv.mpr (by decide : 1<2)
  have hS : 0≤S := tsum_nonneg (fun _ => by positivity)
  refine ⟨C*((k+2).factorial:ℝ)*S,by positivity,?_⟩
  intro y hy x
  let V := C*((k+2).factorial:ℝ)/y^(k+2)*Real.exp (-y)
  have ha := summable_mode hg (by positivity : 0<4*y)
  have hh (n : ℕ) : ‖mode a (4*y) n • fourier (T:=1) (n:ℤ)‖=‖mode a (4*y) n‖ := by
    rw [norm_smul,fourier_norm,mul_one]
  calc
    _ ≤ ‖circleSeries (mode a (4*y))‖ := ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ∑' n : ℕ,‖mode a (4*y) n • fourier (T:=1) (n:ℤ)‖ :=
      norm_tsum_le_tsum_norm (by simpa only [hh] using ha.norm)
    _ = ∑' n : ℕ,‖mode a (4*y) n‖ := tsum_congr hh
    _ ≤ ∑' n : ℕ,V*((n:ℝ)^2)⁻¹ := ha.norm.tsum_le_tsum (fun n => coefficient_bound hC hz hg n hy) (hsum.mul_left V)
    _ = _ := by rw [tsum_mul_left]; dsimp [V,S]; ring

end
end TunnellRankinIntegral
end

section
/- Horizontal Fourier bounds and measurable planar strip kernel in actual hyperbolic coordinates. -/
namespace TunnellRankinIntegral
open Complex AddCircle Set Function TunnellRankin TunnellCMLSeries TunnellClassThetaMellin
open TunnellFullClassTheta TunnellShell TunnellEtaValue MeasureTheory
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

def atXY (p : ℝ×ℝ) : ℍ := if hy : 0<p.1 then ⟨⟨p.2,p.1⟩,hy⟩ else UpperHalfPlane.I

lemma at_coords (z : ℍ) : atXY (coords z)=z := by
  ext; simp [atXY,coords,z.im_pos]; rfl

lemma at_point {y : ℝ} (hy : 0<y) (x : ℝ) : atXY (y,x)=point x (4*Real.pi*y) (by positivity) := by
  apply UpperHalfPlane.ext
  apply Complex.ext <;> simp [atXY,hy,point,Complex.mul_re,Complex.mul_im] <;> field_simp [Real.pi_ne_zero]

lemma atXY_meas : Measurable atXY := by
  apply UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff.mp
  let f (p : ℝ×ℝ) : ℂ := ⟨p.2,p.1⟩
  have hf : Measurable f := planeCoords.symm.measurable
  have eq : UpperHalfPlane.coe ∘ atXY = {p : ℝ×ℝ | 0<p.1}.piecewise f (fun _ => (UpperHalfPlane.I:ℂ)) := by
    funext p; by_cases hy : 0<p.1 <;> simp [atXY,hy,f,Set.piecewise,Function.comp_def]
  rw [eq]
  exact hf.piecewise ((isOpen_lt continuous_const continuous_fst).measurableSet) measurable_const

lemma theta_meas (d : ℕ) : Measurable (theta d) := by
  apply Measurable.tsum
  intro n
  apply Measurable.const_mul
  exact ((Periodic.continuous_qParam (h:=1)).comp UpperHalfPlane.continuous_coe).measurable.pow_const n

lemma full_meas {d : ℕ} {b : Triple} (hs : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d)) :
    Measurable (full hs (by omega) hb) := by
  letI := classFintype hs (by omega) hb
  have e := funext (full_expansion hs (by omega) hb)
  rw [e]
  exact measurable_const.add ((theta_meas d).const_mul _)

def planeStrip (θ : ℍ→ℂ) (s : ℝ) (p : ℝ×ℝ) :=
  ((p.1^(s-1):ℝ):ℂ)*(etaValue (atXY p)*conj (θ (atXY p)))

lemma planeStrip_meas {θ : ℍ→ℂ} (hθ : Measurable θ) (s : ℝ) : Measurable (planeStrip θ s) := by
  apply Measurable.mul
  · exact Complex.continuous_ofReal.measurable.comp (measurable_fst.pow measurable_const)
  · exact (etaValue_hol.continuous.measurable.comp atXY_meas).mul (Complex.continuous_conj.measurable.comp (hθ.comp atXY_meas))

lemma planeStrip_eq (θ : ℍ→ℂ) (s : ℝ) (z : ℍ) :
    stripIntegrand θ (s:ℂ) z = (z.im:ℂ)^2*planeStrip θ s (coords z) := by
  have e := ofReal_cpow z.im_pos.le (s-1)
  push_cast at e
  simp only [stripIntegrand,planeStrip,at_coords,Complex.conj_ofReal,←e]
  dsimp [coords]
  ring

lemma stripBounds (d : ℕ) :
    ∃ A B : ℝ, 0≤A ∧ 0≤B ∧ ∀ {y : ℝ}, 0<y → ∀ x : ℝ,
      ‖etaValue (atXY (y,x))‖ ≤ A/y^5*Real.exp (-Real.pi*y) ∧
      ‖theta d (atXY (y,x))‖ ≤ B/y^3*Real.exp (-Real.pi*y) := by
  obtain ⟨C,hC⟩ := base_growth
  have hC' : 0≤C := by have hh := hC 1; simpa using (norm_nonneg _).trans hh
  obtain ⟨A,hA,h₁⟩ := circle_bound hC' (by simp [twistA,gaussCoeff,twistSign]) hC
  obtain ⟨B,hB,h₂⟩ := circle_bound (a:=fun n => (idealCoeff d n:ℂ)) (k:=1) (C:=1) zero_le_one (by simp [idealCoeff])
    (fun n => by simpa using norm_idealCoeff d n)
  refine ⟨A,B,hA,hB,fun {y} hy x => ?_⟩
  have ht : 0<4*Real.pi*y := by positivity
  rw [at_point hy,TunnellEtaLevel.physical,←circle_eta x _ ht,←circle_theta d x _ ht]
  have hp : y≤Real.pi*y := by nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hy.le]
  have he (k : ℕ) (D : ℝ) (hD : 0≤D) :
      D/(Real.pi*y)^k*Real.exp (-(Real.pi*y))≤D/y^k*Real.exp (-Real.pi*y) := by
    rw [neg_mul]
    gcongr
  rw [mul_assoc]
  exact ⟨(h₁ (Real.pi*y) (by positivity) x).trans (he 5 A hA),
    (h₂ (Real.pi*y) (by positivity) x).trans (he 3 B hB)⟩
end
end TunnellRankinIntegral
end

section
/- Absolute integrability on the unfolded strip and its Mellin value in the convergence half-plane. -/
namespace TunnellRankinIntegral
open Complex Set TunnellRankin TunnellCMLSeries TunnellFullClassTheta TunnellShell
open TunnellEtaValue MeasureTheory
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

lemma rpow_kernel {u : ℝ} (hu : -1<u) :
    IntegrableOn (fun y : ℝ => y^u*Real.exp (-Real.pi*y)) (Ioi 0) := by
  simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) hu (by norm_num) Real.pi_pos)

lemma on_rect {f : ℝ→ℝ} (h : IntegrableOn f (Ioi 0)) : IntegrableOn (fun p : ℝ×ℝ => f p.1) rect := by
  unfold IntegrableOn rect
  rw [Measure.volume_eq_prod,←Measure.prod_restrict]
  exact h.comp_fst _

lemma strip_compare {s y A B H : ℝ} (hy : 0<y) :
    y^(s-1)*(A/y^5*Real.exp (-Real.pi*y)*(H+2*(B/y^3)))=
      A*H*(y^(s-6)*Real.exp (-Real.pi*y))+2*A*B*(y^(s-9)*Real.exp (-Real.pi*y)) := by
  have h5 : y^(s-6)=y^(s-1)/y^5 := by
    rw [show s-6=(s-1)-(5:ℕ) by push_cast; ring,Real.rpow_sub hy,Real.rpow_natCast]
  have h8 : y^(s-9)=y^(s-1)/(y^5*y^3) := by
    rw [show s-9=(s-1)-(8:ℕ) by push_cast; ring,Real.rpow_sub hy,Real.rpow_natCast]
    ring
  rw [h5,h8]
  ring

variable {d : ℕ} {b : Triple} (hq : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))

theorem plane_integrable {s : ℝ} (hs : 8<s) :
    IntegrableOn (planeStrip (full hq (by omega) hb) s) rect := by
  letI := classFintype hq (by omega) hb
  let H : ℝ := Fintype.card (TunnellToricClass.ProperIdealClass b)
  obtain ⟨A,B,hA,hB,h⟩ := stripBounds d
  let F (y : ℝ) := A*H*(y^(s-6)*Real.exp (-Real.pi*y))+2*A*B*(y^(s-9)*Real.exp (-Real.pi*y))
  have hf : IntegrableOn F (Ioi 0) :=
    ((rpow_kernel (u:=s-6) (by linarith)).const_mul (A*H)).add
      ((rpow_kernel (u:=s-9) (by linarith)).const_mul (2*A*B))
  apply (on_rect hf).mono' (planeStrip_meas (full_meas hq hd hb) s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ico : MeasurableSet rect)] with p hp
  rcases p with ⟨y,x⟩
  have hy : 0<y := hp.1
  obtain ⟨hf,ht⟩ := h hy x
  have exp_le : Real.exp (-Real.pi*y)≤1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hy])
  have Bbound : ‖theta d (atXY (y,x))‖≤B/y^3 := ht.trans (mul_le_of_le_one_right (by positivity) exp_le)
  have e : ‖full hq (by omega) hb (atXY (y,x))‖≤H+2*(B/y^3) := by
    rw [full_expansion]
    apply (norm_add_le _ _).trans
    simp only [norm_natCast,norm_mul,norm_ofNat,H]
    gcongr
  have normp : ‖((y^(s-1):ℝ):ℂ)‖=y^(s-1) := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hy _)]
  simp only [planeStrip,norm_mul,Complex.norm_conj,normp,F]
  rw [←strip_compare hy]
  gcongr

theorem strip_mellin {s : ℝ} (hs : 8<s) :
    (∫ z in stripSet, stripIntegrand (full hq (by omega) hb) (s:ℂ) z)=
      2*(4*(Real.pi:ℂ))^(-(s:ℂ))*mellin (strip d) (s:ℂ) := by
  let θ := full hq (by omega) hb
  rw [show stripIntegrand θ (s:ℂ)=fun z : ℍ => (z.im:ℂ)^2*planeStrip θ s (coords z) from funext (planeStrip_eq _ _)]
  rw [strip_fubini _ (plane_integrable hq hd hb hs)]
  have e (y : ℝ) (hy : 0<y) : (∫ x in Ico (0:ℝ) 1, planeStrip θ s (y,x)) =
      2*((y:ℂ)^((s:ℂ)-1)*strip d (4*Real.pi*y)) := by
    simp only [planeStrip,integral_const_mul,at_point hy]
    rw [integral_Ico_eq_integral_Ioc,←intervalIntegral.integral_of_le (zero_le_one' ℝ),
      horizontal_full hq hd hb,Complex.ofReal_cpow hy.le]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e,integral_const_mul]
  have h := mellin_comp_mul_left (strip d) (s:ℂ) (show (0:ℝ)<4*Real.pi by positivity)
  simp only [mellin,smul_eq_mul] at h
  rw [h]
  push_cast
  simp only [mellin,smul_eq_mul]
  ring
end
end TunnellRankinIntegral
end

section
/- Unfolding the actual Petersson integral in the absolutely convergent right half-plane. -/
namespace TunnellRankinIntegral
open Complex Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellRankinEisenstein TunnellRankin
open TunnellShell TunnellFullClassTheta TunnellEtaValue Set MeasureTheory
open UpperHalfPlane hiding I
open scoped ComplexConjugate ENNReal
noncomputable section

lemma unfold_tsum (L : ℕ) {f : ℍ→ℂ} (hf : Measurable f)
    (hi : IntegrableOn f stripSet) (hp : ∀ (n : ℤ) z, f (T^n • z)=f z) :
    (∑' q : Cosets L,∫ z in fdo, ∑' r : Rows L,f (tileMatrix (q,r) • z))=
      2*∫ z in stripSet,f z := by
  letI : Countable (Rows L) := Function.Injective.countable (f:=fun r : Rows L => r.val) Subtype.val_injective
  have ha := unfold_complex L hf hi hp
  have en := unfold_nonneg L hf.enorm (fun n z => congrArg (‖·‖ₑ) (hp n z))
  have ht : (∑' (q : Cosets L) (r : Rows L), ∫⁻ z in fdo,‖f (tileMatrix (q,r) • z)‖ₑ)≠⊤ := by
    change (∑' (q : Cosets L) (r : Rows L), ∫⁻ z in fdo,‖f (((liftRow r).val*rep q) • z)‖ₑ)≠⊤
    rw [en]
    exact ENNReal.mul_ne_top (by norm_num) hi.2.ne
  have hh (q : Cosets L) : (∫ z in fdo, ∑' r : Rows L,f (tileMatrix (q,r) • z))=
      ∑' r : Rows L,∫ z in fdo,f (tileMatrix (q,r) • z) := by
    apply integral_tsum
    · intro r
      apply Measurable.aestronglyMeasurable
      exact hf.comp (measurePreserving_smul (tileMatrix (q,r):GL (Fin 2) ℝ) volume).measurable
    · exact ne_top_of_le_ne_top ht (ENNReal.le_tsum q)
  simp_rw [hh]
  rw [←ha.summable.tsum_prod]
  exact ha.tsum_eq

def petersson (L : ℕ) (F : ℍ→ℂ) : ℂ :=
  ∑' q : Cosets L, ∫ z in fdo,F (rep q • z)

variable {d : ℕ} {b : Triple} (hsq : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))

lemma strip_trans (s : ℝ) (n : ℤ) (z : ℍ) :
    stripIntegrand (full hsq (by omega) hb) (s:ℂ) (T^n • z)=stripIntegrand (full hsq (by omega) hb) (s:ℂ) z := by
  have hg (L : ℕ) : (T^n:SL(2,ℤ))∈Gamma0 L := by rw [Gamma0_mem]; simp [coe_T_zpow]
  have hj : denom (T^n:SL(2,ℤ)) z=1 := by rw [ModularGroup.denom_apply]; simp [coe_T_zpow]
  have ht := full_action_one hsq hd hb z (T^n) (hg _)
  rw [hj] at ht
  have he : (T^n:SL(2,ℤ)) 1 1=1 := by simp [coe_T_zpow]
  rw [he,Int.cast_one,map_one,one_mul,one_mul] at ht
  simp only [stripIntegrand,im_T_zpow_smul,TunnellEtaLevel.eta_level _ (hg 32),hj,one_pow,one_mul,ht]

theorem petersson_large (s : ℝ) (hs : 8<s) :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    petersson (4*(2*d)*4) (integrand (k:=4) (negCharacter d (by omega)) (full hsq (by omega) hb) (s:ℂ))=
      4*conj ((negCharacter d (by omega)).LFunction (2*(s:ℂ)-1))*
        (4*(Real.pi:ℂ))^(-(s:ℂ))*mellin (strip d) (s:ℂ) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let θ := full hsq (by omega) hb
  let f := stripIntegrand θ (s:ℂ)
  have he : f=fun z : ℍ => (z.im:ℂ)^2*planeStrip θ s (coords z) := funext (planeStrip_eq _ _)
  have hf : Measurable f := by
    rw [he]
    exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).measurable.pow_const 2).mul
      ((planeStrip_meas (full_meas hsq hd hb) s).comp coords_embedding.measurable)
  have hi : IntegrableOn f stripSet := by rw [he,coords_integrable]; exact plane_integrable hsq hd hb hs
  have hright := unfold_tsum (4*(2*d)*4) hf hi (strip_trans hsq hd hb s)
  have ht := strip_mellin hsq hd hb hs
  change (∫ z in stripSet,f z)=_ at ht
  rw [ht] at hright
  have hp (q : Cosets (4*(2*d)*4)) (z : ℍ) :=
    periodization hsq hd hb (rep q • z) (s:ℂ) (by simpa using (show 3/2<s by linarith))
  simp only [Complex.conj_ofReal,←mul_smul] at hp
  unfold petersson
  simp_rw [hp,integral_const_mul]
  rw [tsum_mul_left]
  change _* (∑' q : Cosets (4*(2*d)*4),∫ z in fdo, ∑' r : Rows (4*(2*d)*4),f (tileMatrix (q,r) • z))=_
  rw [hright]
  ring
end
end TunnellRankinIntegral
end

section
/- Holomorphy of the actual, absolutely convergent Petersson integral across the central point. -/
namespace TunnellRankinIntegral
open Complex Matrix MatrixGroups ModularGroup Set MeasureTheory TunnellRankin TunnellRankinEisenstein
open TunnellShell TunnellFullClassTheta TunnellEtaValue TunnellRankinMajorant TunnellRankinCotangent
open TunnellClassThetaMellin TunnellCMRegularized Metric
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

def window : Set ℂ := {s | 3/4<s.re} ∩ ball 0 12
lemma window_open : IsOpen window := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ball

variable {d : ℕ} {b : Triple} (hsq : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))

lemma full_growth : ∃ C : ℝ, 0≤C ∧ ∀ w : ℍ, ‖full hsq (by omega) hb w‖≤C*(size w)^66 := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  obtain ⟨C,hC,hh⟩ := eisenstein_bound (k:=1) (negCharacter d (by omega))
  let a : ℂ := 2*Real.pi/(v d:ℂ)
  have hv : (v d:ℂ)≠0 := by exact_mod_cast (v_pos (show 0<d by omega)).ne'
  have ha : a≠0 := div_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero)) hv
  refine ⟨C/‖a‖,by positivity,?_⟩
  intro w
  have e := hh w (s:=1) (by norm_num) (by norm_num)
  rw [eisenstein_one hsq hd hb,norm_mul] at e
  have eg : multiple ⟨1,by decide⟩ w=w := by ext; simp [multiple]
  rw [eg] at e
  change ‖a‖*‖full hsq _ hb w‖≤_ at e
  rw [div_mul_eq_mul_div,le_div_iff₀ (norm_pos_iff.mpr ha)]
  simpa only [mul_comm] using e

end
end TunnellRankinIntegral
end

section
namespace TunnellRankinIntegral
open Complex Matrix MatrixGroups ModularGroup Set MeasureTheory TunnellRankin TunnellRankinEisenstein
open TunnellShell TunnellFullClassTheta TunnellEtaValue TunnellRankinMajorant TunnellRankinCotangent
open TunnellClassThetaMellin TunnellCMRegularized Metric
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

lemma bounded_product {y t f g e D C X Y A : ℝ} (hy : 0≤y) (ht : 0≤t) (hf : 0≤f) (hg : 0≤g) (he : 0≤e)
    (hD : 0≤D) (hC : 0≤C) (hX : 0≤X)
    (hyd : y≤t) (hfd : g≤D*t^66) (hed : e≤C*t^66)
    (htd : t^134≤X^134*Y^268) (had : f*Y^268≤A) :
    y^2*f*g*e≤D*C*X^134*A := by
  calc
    _ ≤ t^2*f*(D*t^66)*(C*t^66) := by
      apply mul_le_mul _ hed he (mul_nonneg (mul_nonneg (sq_nonneg _) hf) (mul_nonneg hD (pow_nonneg ht _)))
      apply mul_le_mul _ hfd hg (mul_nonneg (sq_nonneg _) hf)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy hyd 2) hf
    _ = D*C*f*t^134 := by ring
    _ ≤ D*C*f*(X^134*Y^268) := mul_le_mul_of_nonneg_left htd (by positivity)
    _ = D*C*X^134*(f*Y^268) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left had (mul_nonneg (mul_nonneg hD hC) (pow_nonneg hX _))

variable {d : ℕ} {b : Triple} (hsq : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))

lemma integrand_growth (g : SL(2,ℤ)) :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    ∃ M : ℝ, 0≤M ∧ ∀ z∈fdo, ∀ s∈window,
      ‖integrand (k:=4) (negCharacter d (by omega)) (full hsq (by omega) hb) s (g • z)‖≤M := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  obtain ⟨C,hC,hE⟩ := eisenstein_bound (k:=4) (negCharacter d (by omega))
  obtain ⟨D,hD,hF⟩ := full_growth hsq hd hb
  obtain ⟨T,hT,hG⟩ := cusp_size g
  obtain ⟨A,hA,hη⟩ := eta_rapid g 268
  have hT' : 0≤T := by linarith
  refine ⟨D*C*T^134*A,by positivity,?_⟩
  intro z hz s hs
  let w := g • z
  let Y := 1+z.im
  have hw := (size_one w)
  have hY : 0≤Y := by dsimp [Y]; linarith [z.im_pos]
  have hE' := hE w (s:=conj s) (by simpa using (mem_ball_zero_iff.mp hs.2).le) (by simpa using hs.1)
  have hF' := hF w
  have Tbound := pow_le_pow_left₀ (by linarith : 0≤ size w) (hG z (fdo_subset_fd hz)) 134
  change size w^134≤(T*Y^2)^134 at Tbound
  rw [mul_pow,←pow_mul] at Tbound
  have hb := hη z (fdo_subset_fd hz)
  change ‖etaValue w‖*Y^268≤A at hb
  simp only [integrand,norm_mul,Complex.norm_conj,norm_pow,Complex.norm_real,Real.norm_of_nonneg (g • z).im_pos.le]
  change w.im^2*‖etaValue w‖*_*_≤_
  exact bounded_product w.im_pos.le (by linarith) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hD hC hT' (size_im w) hF' hE' Tbound hb

end
end TunnellRankinIntegral
end

section
namespace TunnellRankinIntegral
open Complex Matrix MatrixGroups ModularGroup Set MeasureTheory TunnellRankin TunnellRankinEisenstein
open TunnellShell TunnellFullClassTheta TunnellEtaValue TunnellRankinMajorant TunnellRankinCotangent
open TunnellClassThetaMellin TunnellCMRegularized Metric
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

variable {d : ℕ} {b : Triple} (hsq : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))

theorem petersson_analytic :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    AnalyticOnNhd ℂ (fun s => petersson (4*(2*d)*4) (integrand (k:=4) (negCharacter d (by omega))
      (full hsq (by omega) hb) s)) window := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  letI : NeZero (4*(2*d)*4) := ⟨by omega⟩
  letI := Fintype.ofFinite (Cosets (4*(2*d)*4))
  let θ := full hsq (by omega) hb
  let χ := negCharacter d (by omega)
  let F (s : ℂ) (z : ℍ) := integrand (k:=4) χ θ s z
  have hm (s : ℂ) : Measurable (F s) := by
    apply Measurable.mul
    · apply Measurable.mul
      · exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).measurable.pow_const 2).mul etaValue_hol.continuous.measurable
      · exact Complex.continuous_conj.measurable.comp (full_meas hsq hd hb)
    · exact Complex.continuous_conj.measurable.comp (eisenstein_meas χ (conj s))
  have hdif (z : ℍ) : AnalyticOnNhd ℂ (fun s => F s z) window := by
    apply DifferentiableOn.analyticOnNhd _ window_open
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_mul
    have he := ((eisenstein_analytic (k:=4) χ z) (conj s) (by simpa [domain] using hs.1)).differentiableAt.conj_conj
    simpa only [Function.comp_def,Complex.conj_conj] using he
  simp only [petersson,tsum_fintype]
  apply Finset.analyticOnNhd_fun_sum
  intro q _
  let g := rep q
  obtain ⟨M,hM,hB⟩ := integrand_growth hsq hd hb g
  haveI : IsFiniteMeasure (volume.restrict fdo) := isFiniteMeasure_restrict.mpr fdo_finite.ne
  apply TunnellRankinParameter.analytic_integral (μ:=volume.restrict fdo) window_open
    (F:=fun s z => F s (g • z))
    (fun s => (hm s).comp (measurePreserving_smul (g:GL (Fin 2) ℝ) volume).measurable)
    (fun z => hdif (g • z)) (B:=fun _ => M) (integrable_const _)
  exact (ae_restrict_mem isOpen_fdo.measurableSet).mono fun z hz => hB z hz
end
end TunnellRankinIntegral
end

section
/- A distinguished polynomial representative of the positive square root of 8d in a cyclotomic field. -/

namespace TunnellRootPolynomial
open Finset Polynomial Complex
open scoped Real

noncomputable def root (d : ℕ) := exp (2*(Real.pi:ℂ)*I/(16*d))
noncomputable def angle (d j : ℕ) := Real.pi * j/(8*d)
noncomputable def chord (d j : ℕ) := 2*Real.sin (angle d j)

noncomputable def chordPoly (d j : ℕ) : ℤ[X] := (X^(16*d-j)-X^j)*X^(4*d)
noncomputable def rootPoly (d : ℕ) : ℤ[X] := chordPoly d (2*d) * ∏ j ∈ range (4*d-1), chordPoly d (j+1)

lemma primitive {d : ℕ} (hd : 0<d) : IsPrimitiveRoot (root d) (16*d) := by
  simpa [root] using Complex.isPrimitiveRoot_exp (16*d) (by omega)

lemma root_pow (d j : ℕ) : root d ^ j = exp ((angle d j:ℝ)*I) := by
  rw [root,←exp_nat_mul]; congr 1; unfold angle; push_cast; ring

lemma angle_half {d : ℕ} (hd : 0<d) : angle d (4*d) = Real.pi/2 := by
  simp only [angle,Nat.cast_mul,Nat.cast_ofNat]; field_simp; ring

lemma angle_quarter {d : ℕ} (hd : 0<d) : angle d (2*d) = Real.pi/4 := by
  simp only [angle,Nat.cast_mul,Nat.cast_ofNat]; field_simp; ring

lemma eval_chord {d : ℕ} (hd : 0<d) {j : ℕ} (hj : j≤16*d) :
    aeval (root d) (chordPoly d j) = (chord d j:ℂ) := by
  have hr : root d≠0 := exp_ne_zero _
  have hinv : root d ^ (16*d-j) = (root d^j)⁻¹ := by
    rw [←one_div]
    apply (eq_div_iff (pow_ne_zero j hr)).mpr
    rw [←pow_add,Nat.sub_add_cancel hj,(primitive hd).pow_eq_one]
  have hi : root d^(4*d)=I := by
    rw [root_pow,angle_half hd,ofReal_div,ofReal_ofNat,exp_pi_div_two_mul_I]
  rw [chordPoly,map_mul,map_sub,map_pow,map_pow,map_pow,aeval_X,hinv,hi,root_pow,←exp_neg]
  unfold chord
  push_cast
  rw [two_sin,neg_mul]

lemma chord_pos {d j : ℕ} (hj : 0<j) (hjd : j<8*d) : 0<chord d j := by
  have hd : 0<d := by omega
  apply mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi (by dsimp [angle]; positivity) _)
  dsimp [angle]
  apply (div_lt_iff₀ (by positivity : (0:ℝ)<8*d)).mpr
  apply mul_lt_mul_of_pos_left _ Real.pi_pos
  exact_mod_cast hjd

lemma chord_reflect {d j : ℕ} (hd : 0<d) (hj : j≤8*d) : chord d (8*d-j)=chord d j := by
  have h : angle d (8*d-j) = Real.pi-angle d j := by
    simp only [angle,Nat.cast_sub hj,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  rw [chord,h,Real.sin_pi_sub,chord]

lemma norm_factor {d j : ℕ} (hj : 0<j) (hjd : j<8*d) :
    ‖1-(root d^2)^j‖ = chord d j := by
  rw [norm_sub_rev,←pow_mul,root_pow]
  rw [mul_comm _ I, norm_exp_I_mul_ofReal_sub_one]
  have hr : angle d (2*j)/2=angle d j := by unfold angle; push_cast; ring
  rw [hr,Real.norm_eq_abs]
  exact abs_of_nonneg (chord_pos hj hjd).le

private lemma reflect_product (f : ℕ→ℝ) (m : ℕ) (hs : ∀ j < m, f (m+(j+1))= f (m-1-j)) :
    ∏ j ∈ range (2*m+1), f j = (∏ j ∈ range m, f j)^2*f m := by
  rw [show 2*m+1=m+(m+1) by omega,prod_range_add,prod_range_succ']
  have he : (∏ j ∈ range m, f (m+(j+1))) = ∏ j ∈ range m,f j :=
    (prod_congr rfl (fun j hj => hs j (mem_range.mp hj))).trans (prod_range_reflect f m)
  rw [he]; ring

lemma real_product {d : ℕ} (hd : 0<d) :
    2*(∏ j ∈ range (4*d-1),chord d (j+1))^2 = 8*(d:ℝ) := by
  let m := 4*d-1
  have hm : 4*d=m+1 := by dsimp [m]; omega
  have hn : 8*d=(2*m+1)+1 := by omega
  have hp : IsPrimitiveRoot (root d^2) (8*d) := by
    exact (primitive hd).pow (by omega) (show 16*d = 2*(8*d) by omega)
  rw [hn] at hp
  have prodEq := congrArg norm hp.prod_one_sub_pow_eq_order
  simp only [norm_prod] at prodEq
  have hf : (∏ k ∈ range (2*m+1), ‖1-(root d^2)^(k+1)‖) = ∏ k∈range (2*m+1),chord d (k+1) :=
    prod_congr rfl (fun k hk => norm_factor (Nat.succ_pos _) (by have := mem_range.mp hk; omega))
  rw [hf,reflect_product (fun k => chord d (k+1)) m] at prodEq
  · rw [←hm,chord,angle_half hd,Real.sin_pi_div_two,mul_one] at prodEq
    have hnorm : ‖(((2*m+1:ℕ):ℂ)+1)‖=8*(d:ℝ) := by
      rw [show (((2*m+1:ℕ):ℂ)+1)=((8*d:ℕ):ℂ) by rw [hn]; push_cast; ring]
      simp
    change 2*_=8*(d:ℝ)
    rw [←hnorm,←prodEq]
    ring
  · intro k hk
    have h : m+(k+1)+1=8*d-(m-1-k+1) := by omega
    rw [h,chord_reflect hd (by omega)]

theorem eval_rootPoly {d : ℕ} (hd : 0<d) :
    aeval (root d) (rootPoly d) = (Real.sqrt (8*d):ℂ) := by
  have he : (∏ k∈range (4*d-1),aeval (root d) (chordPoly d (k+1))) =
      ((∏ k∈range (4*d-1),chord d (k+1):ℝ):ℂ) := by
    rw [ofReal_prod]
    exact prod_congr rfl (fun k hk => eval_chord hd (by have := mem_range.mp hk; omega))
  rw [rootPoly,map_mul,map_prod,he,eval_chord hd (by omega),chord,angle_quarter hd,Real.sin_pi_div_four]
  norm_num only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)]
  rw [←ofReal_mul,ofReal_inj]
  have hprod : 0≤∏ j∈range (4*d-1),chord d (j+1) := prod_nonneg (fun k hk => (chord_pos (by omega) (by have := mem_range.mp hk; omega)).le)
  have hh := real_product hd
  have hsq := Real.sq_sqrt (show 0≤8*(d:ℝ) by positivity)
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow,h2,hsq,hh]

end TunnellRootPolynomial
end

section
/- An integer polynomial test for the Gauss sign and a finite modular-symbol square identity. -/

namespace TunnellFiniteSymbols
open Finset Polynomial TunnellRootPolynomial TunnellTwistCharacter

noncomputable def chiPoly (d : ℕ) (hd : 0<d) : ℤ[X] :=
  haveI : NeZero (4*(2*d)) := ⟨by omega⟩
  ∑ j : ZMod (4*(2*d)), C (weight (2*d) j.val)*X^(2*j.val)

lemma eval_chiPoly {d : ℕ} (hd : 0<d) : aeval (root d) (chiPoly d hd)=tau (2*d) (by omega) := by
  let : NeZero (4*(2*d)) := ⟨by omega⟩
  unfold chiPoly tau gaussSum
  simp only [map_sum,map_mul,aeval_C,map_pow,aeval_X]
  apply sum_congr rfl
  intro j _
  change (weight (2*d) j.val:ℂ)*_= (weight (2*d) j.val:ℂ)*_
  congr 1
  have h := ZMod.stdAddChar_coe (N:=4*(2*d)) (j.val:ℤ)
  rw [Int.cast_natCast,ZMod.natCast_zmod_val] at h
  rw [h,root_pow]
  congr 1
  simp only [angle,Nat.cast_mul,Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_natCast,Complex.ofReal_ofNat,Int.cast_natCast]
  ring

/- The sign of the real quadratic Gauss sum, using only division of integer polynomials. -/
noncomputable def epsilon (d : ℕ) (hd : 0<d) : ℤ :=
  if (chiPoly d hd-rootPoly d) %ₘ cyclotomic (16*d) ℤ = 0 then 1 else -1

lemma sign_iff {d : ℕ} (hd : 0<d) :
    (chiPoly d hd-rootPoly d) %ₘ cyclotomic (16*d) ℤ = 0 ↔
      tau (2*d) (by omega)=(Real.sqrt (8*d):ℂ) := by
  rw [modByMonic_eq_zero_iff_dvd (cyclotomic.monic _ _),
    cyclotomic_eq_minpoly (primitive hd) (by omega),
    ←minpoly.isIntegrallyClosed_dvd_iff ((primitive hd).isIntegral (by omega)),
    map_sub,eval_chiPoly hd,eval_rootPoly hd,sub_eq_zero]

lemma signed_root {d : ℕ} (hs : Squarefree d) (hd : d%4=1) :
    tau (2*d) (by omega)=(epsilon d (by omega):ℂ)*(Real.sqrt (8*d):ℂ) := by
  have hd' : 0<d := by omega
  let : NeZero (4*(2*d)) := ⟨by omega⟩
  have hh := TunnellModularSymbol.gauss_sq (character_primitive hd hs)
    (character_quadratic (2*d) (by omega)) (character_even hd)
  change tau (2*d) (by omega)^2=((4*(2*d):ℕ):ℂ) at hh
  have hsq : (Real.sqrt (8*d):ℂ)^2=((4*(2*d):ℕ):ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
    push_cast
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hh.trans hsq.symm) with he|he
  · simp [epsilon,(sign_iff hd').mpr he,he]
  · by_cases h : (chiPoly d hd'-rootPoly d) %ₘ cyclotomic (16*d) ℤ = 0
    · simp [epsilon,h,(sign_iff hd').mp h]
    · simp [epsilon,h,he]

end TunnellFiniteSymbols
end

section
/- The normalized Rankin central period and the exact finite winding-square problem. -/

namespace TunnellRankin
open TunnellCMLSeries TunnellFricke TunnellFiniteSymbols TunnellModularSymbol
open TunnellTwistCharacter ModularForm UpperHalfPlane Set MeasureTheory

lemma modular_on_right {H : Subgroup (GL (Fin 2) ℝ)} [H.IsArithmetic] (hw : H.strictWidthInfty=1)
    (F : CuspForm H 2) (n : ℕ) (hc : ∀ m : ℕ, (qExpansion 1 F).coeff m=gaussCoeff n m)
    (s : ℝ) (hs : 2<s) : ModularForm.L (by decide : (0:ℤ)<2) F (s:ℂ)=latticeValue n s := by
  have ha := CuspForm.hasSum_L (by decide : (0:ℤ)<2) F (s:=(s:ℂ)) (by norm_num; linarith)
  apply HasSum.unique _ (shell_expansion n s (by linarith))
  simpa only [hw,Complex.ofReal_one,Complex.one_cpow,one_mul,hc,gaussCoeff] using ha

lemma continued_halfplane {d : ℕ} (hd : d%4=1) {F L : ℂ→ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hL : AnalyticOnNhd ℂ L univ) :
    AnalyticOnNhd ℂ (continued d (by omega) F L) {z : ℂ | 1≤z.re} := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  have hχ : negCharacter d (by omega)≠1 := by
    intro hz
    have eq := negCharacter_odd hd
    rw [DirichletCharacter.Odd,hz,MulChar.one_apply (by simp)] at eq
    norm_num at eq
  have hG : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0<z.re} := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z _).differentiableWithinAt
    intro n he
    change 0<z.re at hz
    rw [he,Complex.neg_re,Complex.natCast_re] at hz
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  intro z hz
  change 1≤z.re at hz
  have hg := hG.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by linarith : (0:ℝ)<z.re))
  unfold continued
  apply AnalyticAt.div
  · exact (hg.mul (hF z trivial)).mul (hL z trivial)
  · unfold negativeL
    apply ((DirichletCharacter.differentiable_LFunction hχ).analyticAt _).comp
    fun_prop
  · apply DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inl hχ)
    norm_num [Complex.mul_re]
    linarith

/- An explicit continuation of the strip Mellin transform through its central point.
Its value, including the quadratic L-factor and the base periods, is the signed finite winding sum. -/
theorem normalized_mellin (d : ℕ) (hs : Squarefree d) (hd : d%4=1) :
    ∃ M : ℂ→ℂ, AnalyticOnNhd ℂ M {z : ℂ | 1≤z.re} ∧
      (∀ s : ℝ, 5/2<s → M s=mellin (strip d) (s:ℂ)) ∧
      (Real.sqrt (8*d):ℂ)*negativeL d (by omega) 1*M 1 =
      (epsilon d (by omega)*winding (2*d) (by omega):ℤ)*baseConstant^2 := by
  obtain ⟨H,hH,hw,F,hF,hfc⟩ := TunnellEtaValue.actual_form
  letI : H.IsArithmetic := hH
  have hm (m : ℕ) := TunnellArithmetic.eta_eq_mass
    (TunnellTruncated.cubic_congruence (fun N => TunnellCubicFinite.cubic _ N))
    (TunnellTruncated.theta_congruence (fun _ N => TunnellBalanced.balanced _ N)) m
  have hf1 (m : ℕ) : (qExpansion 1 F).coeff m=gaussCoeff 1 m := by
    rw [hfc]
    by_cases ho : Odd m
    · simp [gaussCoeff,twistSign,ho,hm]
    · simp [gaussCoeff,twistSign,ho,TunnellInert.eta_zero_of_mod_four (by have := Nat.odd_iff.not.mp ho; omega : m%4≠1)]
  have hsd : Squarefree (2*d) := (Nat.squarefree_mul (Nat.odd_iff.mpr (by omega) : Odd d).coprime_two_left).mpr
    ⟨Nat.prime_two.squarefree,hs⟩
  obtain ⟨K,hK,kw,G,ht,_,_⟩ := jacobi_twist_integral (show (2*d)%8=2 by omega) hsd hw F
  letI : K.IsArithmetic := hK
  have hg1 (m : ℕ) : (qExpansion 1 G).coeff m=gaussCoeff (2*d) m := by
    rw [ht,hfc,hm]; rfl
  let L₁ := ModularForm.L (by decide : (0:ℤ)<2) F
  let L₂ := ModularForm.L (by decide : (0:ℤ)<2) G
  have hL₁ : AnalyticOnNhd ℂ L₁ univ := fun z _ => (CuspForm.differentiable_L (by decide : (0:ℤ)<2) F).analyticAt z
  have hL₂ : AnalyticOnNhd ℂ L₂ univ := fun z _ => (CuspForm.differentiable_L (by decide : (0:ℤ)<2) G).analyticAt z
  have hb : L₁ 1=baseConstant := by
    unfold L₁
    rw [←zero_symbol F hF,TunnellMellin.central_integral]
    simp [periodSymbol]
  have h := twist_sum (2*d) (by omega) hsd L₂ hL₂ (fun s hgt => by
    rw [show L₂ (s:ℂ)=latticeValue (2*d) s from modular_on_right kw G _ hg1 s hgt]
    exact lattice_euler (2*d) s (by linarith))
  rw [signed_root hs hd] at h
  obtain ⟨_,hv⟩ := continued_center hd (hL₁ 1 trivial) (hL₂ 1 trivial)
  refine ⟨continued d (by omega) L₁ L₂,continued_halfplane hd hL₁ hL₂,fun s hgt => continued_eq (by omega) _ _ s hgt
    (modular_on_right hw F _ hf1 s (by linarith)) (modular_on_right kw G _ hg1 s (by linarith)),?_⟩
  rw [hb] at hv
  rw [Int.cast_mul]
  by_cases e : epsilon d (by omega)=1
  · simp only [e,Int.cast_one,one_mul] at h ⊢
    linear_combination (Real.sqrt (8*d):ℂ)*hv+baseConstant*h
  · have en : epsilon d (by omega)= -1 := by unfold epsilon at e ⊢; split_ifs <;> simp_all
    simp only [en,Int.cast_neg,Int.cast_one,neg_one_mul,neg_mul] at h ⊢
    linear_combination (Real.sqrt (8*d):ℂ)*hv-baseConstant*h

end TunnellRankin
end

section
/- The central Petersson integral and its exact finite winding normalization. -/
namespace TunnellRankinIntegral
open Complex Set Filter Metric TunnellRankin TunnellRankinEisenstein TunnellShell
open TunnellFullClassTheta TunnellRankinCotangent TunnellClassThetaMellin TunnellEtaValue
open TunnellFiniteSymbols TunnellFricke
open UpperHalfPlane hiding I
open scoped ComplexConjugate Topology
noncomputable section

lemma central_unique {F G : ℂ→ℂ} (hf : AnalyticOnNhd ℂ F window)
    (hg : AnalyticOnNhd ℂ G {s : ℂ | 1≤ s.re}) (he : ∀ s : ℝ, 8<s → F s=G s) : F 1=G 1 := by
  let U : Set ℂ := {s : ℂ | 1≤ s.re} ∩ ball 0 12
  have hc : Convex ℝ U := (convex_halfSpace_re_ge 1).inter (convex_ball (0:ℂ) _)
  have hsub : U⊆window := fun s hs => ⟨by have := hs.1; change 1≤ s.re at this; change 3/4 < s.re; linarith,hs.2⟩
  have hm : Tendsto ((↑):ℝ → ℂ) (𝓝[≠] (9:ℝ)) (𝓝[≠] (9:ℂ)) := by
    apply continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    intro x hx hy
    apply hx
    change (x:ℂ)=(9:ℂ) at hy
    exact_mod_cast hy
  apply (hf.mono hsub).eqOn_of_preconnected_of_frequently_eq (hg.mono inter_subset_left) hc.isPreconnected
    (z₀:=(9:ℂ)) (by norm_num [U,mem_ball_zero_iff])
  · apply hm.frequently
    apply Filter.Eventually.frequently
    filter_upwards [(eventually_gt_nhds (show (8:ℝ)<9 by norm_num)).filter_mono nhdsWithin_le_nhds] with s hs
    exact he s hs
  · norm_num [U,mem_ball_zero_iff]

lemma Lstar_analytic {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hn : χ≠1) :
    AnalyticOnNhd ℂ (fun s : ℂ => conj (χ.LFunction (2*conj s-1))) univ := by
  suffices H : Differentiable ℂ (fun s : ℂ => conj (χ.LFunction (2*conj s-1))) from fun s _ => H.analyticAt s
  intro s
  have h : DifferentiableAt ℂ (fun z : ℂ => χ.LFunction (2*z-1)) (conj s) :=
    (DirichletCharacter.differentiable_LFunction hn _).comp _ (by fun_prop)
  simpa only [Function.comp_def,Complex.conj_conj] using h.conj_conj

variable {d : ℕ} {b : Triple} (hsq : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))

include hsq hb in
lemma negative_real :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    conj ((negCharacter d (by omega)).LFunction 1)=(negCharacter d (by omega)).LFunction 1 := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  have hc := class_number hsq (by omega) hb hd
  change (v d:ℂ)*(negCharacter d (by omega)).LFunction 1=Real.pi*hclass (b:=b) at hc
  have h := congrArg conj hc
  simp only [map_mul,Complex.conj_ofReal,hclass,map_natCast] at h
  exact mul_left_cancel₀ (by exact_mod_cast (v_pos (show 0<d by omega)).ne' : (v d:ℂ)≠0) (h.trans hc.symm)

def thetaProduct (θ ψ : ℍ→ℂ) (z : ℍ) := (z.im:ℂ)^2*etaValue z*conj (θ z*ψ z)

lemma central_product :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    let θ := full hsq (by omega) hb
    petersson (4*(2*d)*4) (integrand (k:=4) (negCharacter d (by omega)) θ 1) =
      (2*Real.pi/(v d:ℂ))*petersson (4*(2*d)*4) (thetaProduct θ (fun z => θ (multiple 4 z))) := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let θ := full hsq (by omega) hb
  let a : ℂ := 2*Real.pi/(v d:ℂ)
  have ha : conj a=a := by norm_num [a,map_ofNat]
  have ee (z : ℍ) : integrand (k:=4) (negCharacter d (by omega)) θ 1 z=
      a*thetaProduct θ (fun w => θ (multiple 4 w)) z := by
    rw [integrand,map_one,eisenstein_one hsq hd hb]
    change _*conj (a*θ (multiple 4 z))=_
    simp only [map_mul,ha,thetaProduct]
    ring
  change petersson _ (integrand (k:=4) (negCharacter d (by omega)) θ 1)=a*petersson _ (thetaProduct θ (fun z => θ (multiple 4 z)))
  rw [show integrand (k:=4) (negCharacter d (by omega)) θ 1 = _ from funext ee]
  simp only [petersson,MeasureTheory.integral_const_mul,tsum_mul_left]

/- The weight-two Petersson pairing is the signed finite winding number times the
square of the base period, with denominator exactly 2π². -/
theorem central_winding :
    let θ := full hsq (by omega) hb
    (2*(Real.pi:ℂ)^2)*petersson (4*(2*d)*4) (thetaProduct θ (fun z => θ (multiple 4 z))) =
      (epsilon d (by omega)*winding (2*d) (by omega):ℤ)*baseConstant^2 := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let θ := full hsq (by omega) hb
  let χ := negCharacter d (by omega)
  let a : ℂ := 4*Real.pi
  let P (s : ℂ) := petersson (4*(2*d)*4) (integrand (k:=4) χ θ s)
  obtain ⟨M,hM,hm,hv⟩ := normalized_mellin d hsq.of_mul_right hd
  let G (s : ℂ) := 4*conj (χ.LFunction (2*conj s-1))*a^(-s)*M s
  have hχ : χ≠1 := by
    intro e
    have hh := negCharacter_odd hd
    change χ _= -1 at hh
    rw [e,MulChar.one_apply (by simp)] at hh
    norm_num at hh
  have ha : a≠0 := by dsimp [a]; exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hg : AnalyticOnNhd ℂ G {s : ℂ | 1≤ s.re} := by
    apply AnalyticOnNhd.mul _ hM
    apply AnalyticOnNhd.mul (analyticOnNhd_const.mul ((Lstar_analytic χ hχ).mono (subset_univ _)))
    exact fun s _ => (differentiable_id.neg.const_cpow (.inl ha)).analyticAt s
  have e := central_unique (petersson_analytic hsq hd hb) hg (by
    intro s hs
    dsimp only [G]
    rw [petersson_large hsq hd hb s hs,hm s (by linarith),Complex.conj_ofReal])
  change P 1=G 1 at e
  have eL := negative_real hsq hd hb
  change conj (χ.LFunction 1)=χ.LFunction 1 at eL
  simp only [G,map_one,mul_one,show (2:ℂ)-1=1 by norm_num,eL,Complex.cpow_neg_one] at e
  have hV : v d=Real.sqrt (8*d) := by
    have hh := v_sq d
    push_cast at hh
    nlinarith [v_pos (show 0<d by omega),Real.sq_sqrt (by positivity : 0≤8*(d:ℝ)),Real.sqrt_nonneg (8*(d:ℝ))]
  rw [←hV] at hv
  change (v d:ℂ)*χ.LFunction 1*M 1=_ at hv
  have hh := central_product hsq hd hb
  change P 1=(2*Real.pi/(v d:ℂ))*_ at hh
  have v0 : (v d:ℂ)≠0 := by exact_mod_cast (v_pos (show 0<d by omega)).ne'
  have pi0 : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  rw [hh] at e
  dsimp [a] at e
  field_simp [v0,pi0] at e
  rw [←hv]
  exact e
end
end TunnellRankinIntegral
end

section
/- The geometric Fourier expansion and the Petersson central value for the same level-32 trace. -/
namespace TunnellWindingTrace
open TunnellToric
open scoped UpperHalfPlane Classical
noncomputable section

def mass (d : ℕ) := Fintype.card ↥(representatives (2*d))

end
end TunnellWindingTrace
end

section
/- Identification with the exact signed square asserted by the public reduction,
including its polynomial Gauss sign and its displayed Nat.rec cusp algorithm. -/
namespace TunnellPublicSignedSquare
open TunnellCuspEuclid TunnellFiniteSymbols TunnellTwistCharacter Finset
noncomputable section

def folded := Nat.rec (motive:=fun _ => ℤ → ℕ → GaussianInt) (fun _ _ => 1)
  (fun _ f a n => let r := a.bmod n
                  rot (a.bdiv n)*(if r=0 then 1 else if 2*r= -(n:ℤ) then 1-iunit else
                    1-f (if 0≤r then -(n:ℤ) else (n:ℤ)) (2*r.natAbs)))

lemma folded_step (n : ℕ) (a : ℤ) (d : ℕ) :
    folded (n+1) a d = let r := a.bmod d
      rot (a.bdiv d)*(if r=0 then 1 else if 2*r= -(d:ℤ) then 1-iunit else
        1-folded n (if 0≤r then -(d:ℤ) else (d:ℤ)) (2*r.natAbs)) := rfl

lemma folded_eq (n : ℕ) : folded n=symbolAux n := by
  induction n with
  | zero => rfl
  | succ n ih => funext a d; rw [folded_step,symbolAux,ih]

end
end TunnellPublicSignedSquare
end

section
/- Identifying the published class number, theta series and Petersson moment. -/
namespace SignedSquarePublic
open Polynomial Finset MatrixGroups ModularGroup CongruenceSubgroup MeasureTheory
open scoped UpperHalfPlane Classical ComplexConjugate
noncomputable section
def mass (d : ℕ) : ℕ :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    let s := (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
    (s.filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1)).card
def theta (d : ℕ) (z : ℂ) := (mass d:ℂ) + 2*∑' m : ℕ,
    (∑ e ∈ m.divisors, ((if Odd e then jacobiSym (-((2*d:ℕ):ℤ)) e else 0 : ℤ):ℂ))*Function.Periodic.qParam 1 z^m
def integrand (d : ℕ) (z : ℍ) := (z.im:ℂ)^2*(ModularForm.eta (4*(z:ℂ))^2*ModularForm.eta (8*(z:ℂ))^2)*
    conj (theta d z*theta d (4*(z:ℂ)))
def moment (d : ℕ) := ∑' q : SL(2,ℤ) ⧸ Gamma0 (32*d), ∫ z in fdo, integrand d (q.out⁻¹ • z)

lemma mass_eq (d : ℕ) : mass d=TunnellWindingTrace.mass d := by
  classical
  rw [TunnellWindingTrace.mass,Fintype.card_coe]
  apply congrArg Finset.card
  ext v
  simp only [TunnellToric.representatives,TunnellShell.shell,mem_filter]
  rfl

theorem theta_eq {d : ℕ} {v : TunnellShell.Triple} (hn : Squarefree (2*d)) (hd : d%4=1) (hv : v∈TunnellShell.shell (2*d)) (z : ℍ) :
    theta d z=TunnellFullClassTheta.full hn (by omega) hv z := by
  letI := TunnellFullClassTheta.classFintype hn (by omega) hv
  have hcard := Fintype.card_congr (TunnellToricClass.idealEquiv hn (by omega) hv)
  rw [TunnellFullClassTheta.full_expansion,hcard]
  simp only [theta,mass_eq,TunnellWindingTrace.mass,TunnellRankin.theta,TunnellRankin.idealCoeff,TunnellRankin.negWeight,Int.cast_sum]

theorem moment_eq {d : ℕ} {v : TunnellShell.Triple} (hn : Squarefree (2*d)) (hd : d%4=1) (hv : v∈TunnellShell.shell (2*d)) :
    let θ := TunnellFullClassTheta.full hn (by omega) hv
    moment d=TunnellRankinIntegral.petersson (4*(2*d)*4) (TunnellRankinIntegral.thetaProduct θ (fun z => θ (TunnellRankinCotangent.multiple 4 z))) := by
  let θ := TunnellFullClassTheta.full hn (by omega) hv
  have he : integrand d=TunnellRankinIntegral.thetaProduct θ (fun z => θ (TunnellRankinCotangent.multiple 4 z)) := by
    funext z
    have hh := theta_eq hn hd hv (TunnellRankinCotangent.multiple 4 z)
    change theta d (4*(z:ℂ))=θ _ at hh
    unfold integrand TunnellRankinIntegral.thetaProduct
    rw [theta_eq hn hd hv,hh]; rfl
  have eq : 32*d=4*(2*d)*4 := by ring
  unfold moment TunnellRankinIntegral.petersson
  rw [eq,he]
  rfl

end
end SignedSquarePublic
end

section
/- Rankin's Petersson moment is the finite winding number times a fixed nonzero period. -/
open TunnellFricke TunnellShell TunnellFiniteSymbols TunnellPublicSignedSquare TunnellTwistCharacter
open TunnellCuspEuclid SignedSquarePublic Finset
noncomputable section

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1.H1 := by
  let W (d : ℕ) (hd : 0<d) : ℤ :=
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    epsilon d hd * ∑ j : ZMod (4*(2*d)),TunnellTwistCharacter.weight (2*d) j.val*(folded (2*d) j.val (2*d)).re
  change ∃ C : ℂ, C≠0 ∧ ∀ d : ℕ, Squarefree d → (hd : d%4=1) → moment d=(W d (by omega):ℂ)*C
  have hπ : (2*(Real.pi:ℂ)^2)≠0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero))
  refine ⟨baseConstant^2/(2*(Real.pi:ℂ)^2),div_ne_zero (pow_ne_zero _ base_ne_zero) hπ,?_⟩
  intro d hs hd
  have hn : Squarefree (2*d) :=
    (Nat.squarefree_mul (Nat.odd_iff.mpr (by omega) : Odd d).coprime_two_left).mpr ⟨Nat.prime_two.squarefree,hs⟩
  obtain ⟨v,hv⟩ := TunnellThreeSquares.shell_nonempty d hd
  have hw : W d (by omega)=epsilon d (by omega)*winding (2*d) (by omega) := by
    dsimp only [W]
    rw [folded_eq]
    rfl
  rw [hw,moment_eq hn hd hv,mul_div_assoc']
  apply (eq_div_iff hπ).mpr
  linear_combination TunnellRankinIntegral.central_winding hn hd hv

end

end
