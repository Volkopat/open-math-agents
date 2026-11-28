import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1
import Mathlib

/-! Level lowering for a finite family of rectangular theta products. -/

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

lemma q_T (z : ℂ) : Periodic.qParam 4 (z+1) = I*Periodic.qParam 4 z := by
  simp only [Periodic.qParam]
  push_cast
  rw [show 2*(Real.pi:ℂ)*I*(z+1)/4 = Real.pi/2*I + 2*Real.pi*I*z/4 by ring,
    exp_add,exp_pi_div_two_mul_I]

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
open Finset

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
/- Identification of the archimedean strip pairing with the eta newform and its binary theta partner. -/

namespace TunnellRankin
open Complex Set Function ModularForm MeasureTheory AddCircle
open UpperHalfPlane hiding I
open scoped ComplexConjugate

noncomputable def theta (d : ℕ) (z : ℍ) : ℂ :=
  ∑' m : ℕ,(idealCoeff d m:ℂ)*Periodic.qParam 1 z^m

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

end TunnellTwistCharacter
end

section
/- The distinguished continuation of the unfolded Rankin integral at its central point. -/

namespace TunnellRankin
open TunnellTwistCharacter Complex Set

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
  have he' : (TunnellHurwitz.pure) z=q*(TunnellHurwitz.pure) w*q⁻¹ := hact.symm.trans (by rw [inv_eq_star_of_unit hN]; rfl)
  have he : (TunnellHurwitz.pure) v*(a*q⁻¹)=(a*q⁻¹)*(TunnellHurwitz.pure) z := by
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
    have ht : q*(TunnellHurwitz.pure) w=(TunnellHurwitz.pure) z*q := by
      apply mul_left_cancel₀ hb0
      calc b*(q*(TunnellHurwitz.pure) w)=(c*a)*(TunnellHurwitz.pure) w := by rw [←mul_assoc,←e']
           _=(TunnellHurwitz.pure) v*(c*a) := by rw [←mul_assoc ((TunnellHurwitz.pure) v),mem_C.mp hc,mul_assoc c ((TunnellHurwitz.pure) v),ha.2,mul_assoc]
           _=b*((TunnellHurwitz.pure) z*q) := by rw [e',←mul_assoc,hb.2,mul_assoc]
    apply rep_unique hw hz
    refine ⟨q,hq,hnq,?_⟩
    change q*(TunnellHurwitz.pure) w*star q=(TunnellHurwitz.pure) z
    rw [ht,←inv_eq_star_of_unit hnq,mul_assoc,mul_inv_cancel₀ hq0,mul_one]
  · rintro rfl
    refine ⟨b*a⁻¹,mem_C.mpr ?_,mul_ne_zero hb0 (inv_ne_zero ha0),?_⟩
    · apply mul_right_cancel₀ ha0
      calc ((TunnellHurwitz.pure) v*(b*a⁻¹))*a=(TunnellHurwitz.pure) v*b := by simp [mul_assoc,ha0]
           _=b*(TunnellHurwitz.pure) w := hb.2
           _=(b*a⁻¹*(TunnellHurwitz.pure) v)*a := by rw [mul_assoc,ha.2]; simp [mul_assoc,ha0]
    · rw [←mul_assoc,line_mul,mul_assoc,inv_mul_cancel₀ ha0,mul_one]

abbrev IntegralIdeal (v : Triple) := {A : Lattice // isIdeal v A}

def idealSetoid (v : Triple) : Setoid (IntegralIdeal v) where
  r A B := homothetic v A.val B.val
  iseqv := {
    refl := fun _ => ⟨1,mem_C.mpr (by simp),one_ne_zero,by rw [line_one,one_mul]⟩
    symm := by
      rintro A B ⟨c,hc,h₀,he⟩
      refine ⟨c⁻¹,mem_C.mpr ((show Commute ((TunnellHurwitz.pure) v) c from mem_C.mp hc).inv_right₀),inv_ne_zero h₀,?_⟩
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
  have hN' : N⁻¹∈C v := mem_C.mpr (show Commute ((TunnellHurwitz.pure) v) N from his _).inv_right₀
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
/- Finite Weil trace of a quadratic plane at an odd ramified prime. -/
namespace TunnellRamifiedPlane
open Finset ZMod
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def form (a t : (ZMod p)) (v : (ZMod p)×(ZMod p)) := a*(v.1^2-t*v.2^2)
def gauss (a t : (ZMod p)) : ℂ := ∑ v : (ZMod p)×(ZMod p), (ZMod.stdAddChar (N:=p)) (form a t v)
def trace (a t : (ZMod p)) (f : (ZMod p)×(ZMod p) → ℂ) : ℂ :=
  f (0,0) + gauss a t / (p:ℂ)^2 * ∑ j : (ZMod p), ∑ v : (ZMod p)×(ZMod p), (ZMod.stdAddChar (N:=p)) (j*form a t v)*f v

lemma unary (hp : p≠2) {a : (ZMod p)} (ha : a≠0) :
    ∑ x : (ZMod p), (ZMod.stdAddChar (N:=p)) (a*x^2)=(MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) a * gaussSum (MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) (ZMod.stdAddChar (N:=p)) := by
  classical
  have hc : ringChar (ZMod p)≠2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  let g (y:(ZMod p)) := (ZMod.stdAddChar (N:=p)) (a*y)
  calc
    _ = ∑ y : (ZMod p), ∑ x∈univ.filter (fun x : (ZMod p) => x^2=y),g (x^2) := by
      rw [sum_fiberwise_of_maps_to (fun x _ => mem_univ (x^2))]
    _ = ∑ y : (ZMod p), ((MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) y+1)*g y := by
      apply sum_congr rfl
      intro y _
      have e : ∑ x∈univ.filter (fun x : (ZMod p) => x^2=y), g (x^2) = ∑ _x∈univ.filter (fun x : (ZMod p) => x^2=y),g y :=
        sum_congr rfl (fun x hx => congrArg g (mem_filter.mp hx).2)
      rw [e,sum_const,nsmul_eq_mul]
      have h := quadraticChar_card_sqrts hc y
      rw [Set.toFinset_ofPred] at h
      congr 1
      change _=(quadraticChar (ZMod p) y:ℂ)+1
      exact_mod_cast h
    _ = gaussSum (MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) (AddChar.mulShift (ZMod.stdAddChar (N:=p)) a) := by
      simp only [add_mul,sum_add_distrib,one_mul,g]
      have e := AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar p)
      simp only [ha,if_false] at e
      have e1 : (∑ y:(ZMod p), (ZMod.stdAddChar (N:=p)) (a*y))=0 := by simpa only [mul_comm a, Nat.cast_zero] using e
      rw [e1,add_zero]
      simp only [gaussSum,AddChar.mulShift_apply,mul_comm a]
    _ = _ := by
      have e := gaussSum_mulShift_eq (MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) (ZMod.stdAddChar (N:=p)) (Units.mk0 a ha)
      rw [((quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)).inv] at e
      exact e

theorem gauss_eq (hp : p≠2) {a t:(ZMod p)} (ha:a≠0) (ht:t≠0) :
    gauss a t=(p:ℂ)*(MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) t := by
  classical
  have e : ∀ x y:(ZMod p), form a t (x,y)=a*x^2+(-a*t)*y^2 := by intros; dsimp [form]; ring
  rw [gauss,Fintype.sum_prod_type]
  simp_rw [e,AddChar.map_add_eq_mul,←mul_sum]
  rw [←sum_mul,unary hp ha,unary hp (mul_ne_zero (neg_ne_zero.mpr ha) ht)]
  have hC : ringChar (ZMod p)≠2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  have hne : (MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) ≠ 1 := (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr (quadraticChar_ne_one hC)
  have hG := gaussSum_sq hne ((quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)) (ZMod.isPrimitive_stdAddChar p)
  rw [ZMod.card] at hG
  calc
    _ = (MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) (a*(-a*t)) * gaussSum (MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) (ZMod.stdAddChar (N:=p)) ^ 2 := by rw [map_mul (MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) a (-a*t)]; ring
    _ = (p:ℂ)*(MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) ((a^2)*t) := by rw [hG,show a^2*t=a*(-a*t)*(-1) by ring,map_mul (MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) (a*(-a*t)) (-1)]; ring
    _ = _ := by
      have u : (MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) (a^2) = 1 := by
        change ((quadraticChar (ZMod p) (a^2) : ℤ) : ℂ) = 1
        rw [quadraticChar_sq_one' ha,Int.cast_one]
      rw [map_mul (MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) (a^2) t,u,one_mul]

lemma trace_eq (hp : p≠2) {a t:(ZMod p)} (ha:a≠0) (ht:t≠0) (f : (ZMod p)×(ZMod p) → ℂ) :
    trace a t f=f (0,0)+(MulChar.ringHomComp (quadraticChar (ZMod p)) (Int.castRingHom ℂ)) t*∑ v ∈ univ.filter (fun v => form a t v=0), f v := by
  classical
  have he : (∑ j : (ZMod p), ∑ v:(ZMod p)×(ZMod p), (ZMod.stdAddChar (N:=p)) (j*form a t v)*f v)= (p:ℂ)*∑ v∈univ.filter (fun v => form a t v=0),f v := by
    rw [sum_comm,sum_filter,mul_sum]
    apply sum_congr rfl
    intro v _
    rw [←sum_mul,AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p),ZMod.card]
    split_ifs <;> simp
  rw [trace,he,gauss_eq hp ha ht]
  have hn : (p:ℂ)≠0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  field_simp

theorem trace_anisotropic (hp : p≠2) {a t:(ZMod p)} (ha:a≠0) (ht:t≠0) (hs:¬IsSquare t) (f : (ZMod p)×(ZMod p)→ℂ) :
    trace a t f=0 := by
  classical
  have he : univ.filter (fun v:(ZMod p)×(ZMod p) => form a t v=0) = {(0,0)} := by
    ext ⟨x,y⟩
    simp only [mem_filter,mem_univ,true_and,mem_singleton,form,mul_eq_zero,ha,false_or,sub_eq_zero,Prod.mk.injEq]
    constructor
    · intro h
      by_cases hy : y=0
      · exact ⟨by simpa [hy] using h,hy⟩
      · exfalso; apply hs; refine ⟨x/y,?_⟩
        field_simp; linear_combination -h
    · rintro ⟨rfl,rfl⟩; simp
  rw [trace_eq hp ha ht,he,sum_singleton]
  change _+(quadraticChar (ZMod p) t:ℂ)*_=0
  rw [quadraticChar_neg_one_iff_not_isSquare.mpr hs]; simp

lemma filter_line (r : (ZMod p)) (f : (ZMod p)×(ZMod p)→ℂ) :
    (∑ v∈univ.filter (fun v:(ZMod p)×(ZMod p) => v.1=r*v.2),f v)=∑ y:(ZMod p),f (r*y,y) := by
  classical
  symm
  apply sum_nbij' (fun y => (r*y,y)) Prod.snd
  · simp
  · simp
  · simp
  · intro v hv; exact Prod.ext (mem_filter.mp hv).2.symm rfl
  · simp

theorem trace_split (hp : p≠2) {a r:(ZMod p)} (ha:a≠0) (hr:r≠0) (f : (ZMod p)×(ZMod p)→ℂ) :
    trace a (r^2) f=(∑ y:(ZMod p), f (r*y,y))+(∑ y:(ZMod p), f (-r*y,y)) := by
  classical
  rw [trace_eq hp ha (pow_ne_zero _ hr),←filter_line,←filter_line]
  change _+(quadraticChar (ZMod p) (r^2):ℂ)*_=_
  rw [quadraticChar_sq_one' hr,Int.cast_one,one_mul]
  have h0 : f (0,0)=∑ v:(ZMod p)×(ZMod p), if v=(0,0) then f v else 0 := by simp
  rw [h0,sum_filter,sum_filter,sum_filter,←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  rintro ⟨x,y⟩ _
  have h : form a (r^2) (x,y)=0 ↔ x=r*y ∨ x= -r*y := by
    rw [form,show (x^2-r^2*y^2)=(x-r*y)*(x- -r*y) by ring,mul_eq_zero,mul_eq_zero]
    simp only [ha,false_or,sub_eq_zero]
  have hi (e : x=r*y) (e' : x= -r*y) : y=0 := by
    have h2 : (2:(ZMod p))≠0 := by
      change ¬ ((2:ℕ):(ZMod p))=0
      rw [ZMod.natCast_eq_zero_iff]
      intro h; exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) Nat.prime_two).mp h)
    have z : 2*r*y=0 := by linear_combination e'-e
    exact (mul_eq_zero.mp z).resolve_left (mul_ne_zero h2 hr)
  by_cases e : x=r*y <;> by_cases e' : x= -r*y
  · obtain rfl := hi e e'; simp_all
  · have hxy : (x,y)≠(0,0) := by rintro ⟨⟩; simp at e'
    change (if (x,y)=(0,0) then _ else _) + (if form a (r^2) (x,y)=0 then _ else _) = (if x=r*y then _ else _)+(if x= -r*y then _ else _)
    rw [if_neg hxy]
    rw [if_pos (h.mpr (Or.inl e)),if_pos e,if_neg e']; simp
  · have hxy : (x,y)≠(0,0) := by rintro ⟨⟩; simp at e
    change (if (x,y)=(0,0) then _ else _) + (if form a (r^2) (x,y)=0 then _ else _) = (if x=r*y then _ else _)+(if x= -r*y then _ else _)
    rw [if_neg hxy]
    rw [if_pos (h.mpr (Or.inr e')),if_neg e,if_pos e']
  · have hxy : (x,y)≠(0,0) := by rintro ⟨⟩; simp at e
    change (if (x,y)=(0,0) then _ else _) + (if form a (r^2) (x,y)=0 then _ else _) = (if x=r*y then _ else _)+(if x= -r*y then _ else _)
    rw [if_neg hxy]
    rw [if_neg (fun hx => (h.mp hx).elim e e'),if_neg e,if_neg e']

end
end TunnellRamifiedPlane
end

section
/- The product of local Weil trace densities equals the sum of line families over the squarefree modulus. -/
namespace TunnellLineDensity
open TunnellRamifiedPlane Finset
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
abbrev RootsAt (t : K) (x : K×K) := {r:K // r^2=t ∧ x.1=r*x.2}
def density (t : K) (x : K×K) := Nat.card (RootsAt t x)

lemma scale (t k : K) (hk : k≠0) (x : K×K) : density t (k*x.1,k*x.2)=density t x := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro r; apply and_congr_right; intro _
  change k*x.1=r*(k*x.2) ↔ x.1=r*x.2
  rw [mul_left_comm,mul_right_inj' hk]

lemma roots_sum {p : ℕ} [Fact p.Prime] (hp : p≠2) {a t : ZMod p} (ha : a≠0) (ht : t≠0) (f : ZMod p×ZMod p→ℂ) :
    TunnellRamifiedPlane.trace a t f=∑ x, (density t x:ℂ)*f x := by
  classical
  by_cases h : IsSquare t
  · obtain ⟨r,hr⟩ := h
    have hrr : t=r^2 := by simpa [pow_two] using hr
    have hr0 : r≠0 := by intro hz; apply ht; rw [hrr,hz,zero_pow (by decide)]
    have h2 : (2:ZMod p)≠0 := fun e => hp ((Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp e))
    have he : r≠ -r := fun hh => hr0 ((mul_eq_zero.mp (show (2:ZMod p)*r=0 by rw [two_mul,add_eq_zero_iff_eq_neg]; exact hh)).resolve_left h2)
    rw [hrr,trace_split hp ha hr0,←filter_line,←filter_line,sum_filter,sum_filter,←sum_add_distrib]
    apply sum_congr rfl; intro x _
    have hh : density (r^2) x=(if x.1=r*x.2 then 1 else 0)+(if x.1= -r*x.2 then 1 else 0) := by
      let S : Finset (ZMod p) := {r,-r}
      have hset : univ.filter (fun v:ZMod p => v^2=r^2 ∧ x.1=v*x.2)=S.filter (fun v => x.1=v*x.2) := by
        ext v; simp [S,sq_eq_sq_iff_eq_or_eq_neg]
      have hc : density (r^2) x=(univ.filter (fun v:ZMod p => v^2=r^2 ∧ x.1=v*x.2)).card := by
        rw [density,Nat.card_eq_fintype_card]; exact Fintype.card_subtype _
      rw [hc,hset]; dsimp only [S]; rw [Finset.card_filter,Finset.sum_insert (by simpa using he),Finset.sum_singleton]
    rw [hh]; split_ifs <;> simp [two_mul]
  · rw [trace_anisotropic hp ha ht h]
    symm; apply sum_eq_zero; intro x _
    have hE : IsEmpty (RootsAt t x) := ⟨fun r => h ⟨r.val,by simpa only [pow_two] using r.property.1.symm⟩⟩
    letI := hE
    simp [density]

end
end TunnellLineDensity
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
/- Isotropic subgroups in the product of the ramified discriminant planes factor into lines. -/
namespace TunnellRamifiedLines
open Finset
noncomputable section

variable {F : Type*} [Field F]

variable {d : ℕ}
abbrev P (d : ℕ) := ↥d.primeFactors
abbrev Packet (d : ℕ) := (p : P d) → ZMod p.val × ZMod p.val
private instance prime (p : P d) : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩

lemma selector (r : (p : P d) → ZMod p.val) : ∃ a : ℕ, ∀ p : P d, (a:ZMod p.val)=r p := by
  classical
  have hpair : Set.Pairwise (univ : Finset (P d)) (fun a b : P d => Nat.Coprime a.val b.val) := by
    intro i _ j _ e; exact (Nat.coprime_primes (prime i).out (prime j).out).mpr (fun h => e (Subtype.ext h))
  let A := Nat.chineseRemainderOfFinset (fun p : P d => (r p).val) Subtype.val univ (fun p _ => (prime p).out.ne_zero) hpair
  refine ⟨A.val,fun p => ?_⟩
  have e := A.property p (mem_univ p)
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr e |>.trans (ZMod.natCast_zmod_val _)

end
end TunnellRamifiedLines
end

section
/- Reduction of the integral binary components to their ramified discriminant coordinates. -/
namespace TunnellGluePacket
open TunnellIdealHNF TunnellRamifiedLines
noncomputable section
variable {n d : ℕ} {p : ℕ} [Fact p.Prime] {I J : Ideal (R n)}

lemma int_dvd (hs : Squarefree d) {z : ℤ} (h : ∀ i : P d, (i.val:ℤ)∣z) : (d:ℤ)∣z := by
  rw [←Nat.prod_primeFactors_of_squarefree hs,Nat.cast_prod]
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hpq).isCoprime
  · intro p hp; exact h ⟨p,hp⟩

end
end TunnellGluePacket
end

section
/- Identification of the rectangular translates with the odd discriminant coordinates of a quadratic ideal. -/
namespace TunnellRectangularClasses
open TunnellIdealHNF TunnellRamifiedLines TunnellGluePacket
noncomputable section
variable {d : ℕ}
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩

def reduce (i : P d) : ZMod d →+* ZMod i.val := ZMod.castHom (Nat.dvd_of_mem_primeFactors i.property) _

lemma red_ext (hs : Squarefree d) {r s : ZMod d} (h : ∀ i : P d, reduce i r=reduce i s) : r=s := by
  obtain ⟨a,rfl⟩ := ZMod.intCast_surjective r
  obtain ⟨b,rfl⟩ := ZMod.intCast_surjective s
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub a b d).mpr (int_dvd hs fun i => ?_)
  have hi := h i; rw [map_intCast,map_intCast] at hi
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hi

def redEquiv (hs : Squarefree d) : ZMod d ≃ ((i : P d) → ZMod i.val) := by
  apply Equiv.ofBijective (fun s i => reduce i s)
  constructor
  · intro a b h; exact red_ext hs (congrFun h)
  · intro r; obtain ⟨k,hk⟩ := selector r; exact ⟨k,funext fun i => (map_natCast (reduce i) k).trans (hk i)⟩

end
end TunnellRectangularClasses
end

section
/- The translated theta packet of the even rank-one lattice.  The index D is twice
the positive integral coefficient of its quadratic form. -/
namespace TunnellRankOnePacket
open Complex Finset Real TunnellIdealTheta
open scoped Classical
noncomputable section

def packet (D : ℕ) [NeZero D] (r : ZMod D) (z : ℂ) : ℂ :=
  shift ((r.val:ℂ)/D) ((D:ℂ)*z)

def kernel (D : ℕ) (z : ℂ) (u : ℤ) := Complex.exp (π*I*(u:ℂ)^2*z/D)

def phase (D : ℕ) [NeZero D] (r : ZMod D) := Complex.exp (π*I*(r.val:ℂ)^2/D)

lemma packet_hasSum {D : ℕ} [NeZero D] (r : ZMod D) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun l : ℤ => kernel D z (D*l+r.val)) (packet D r z) := by
  have hD : (D:ℂ)≠0 := by exact_mod_cast NeZero.ne D
  have hp : (0:ℝ)<D := Nat.cast_pos.mpr (NeZero.pos D)
  apply (shift_hasSum ((r.val:ℂ)/D) ((D:ℂ)*z) (by simpa [Complex.mul_im] using (mul_pos hp hz))).congr_fun
  intro l
  unfold kernel
  congr 1
  push_cast
  field_simp

lemma class_hasSum {D : ℕ} [NeZero D] (r : ZMod D) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun n : ℤ => if (n:ZMod D)=r then kernel D z n else 0) (packet D r z) := by
  let e (l : ℤ) := (D:ℤ)*l+r.val
  have hD : (D:ℤ)≠0 := by exact_mod_cast NeZero.ne D
  have hi : Function.Injective e := fun a b h => mul_left_cancel₀ hD (add_right_cancel h)
  apply (hi.hasSum_iff ?_).mp
  · apply (packet_hasSum r hz).congr_fun
    intro l
    simp [Function.comp_def,e]
  · intro n hn
    split_ifs with h
    · exfalso
      apply hn
      obtain ⟨l,hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (r.val:ℤ) n D).mp (by simpa using h.symm)
      exact ⟨l,by dsimp [e]; omega⟩
    · rfl

lemma jacobi_packet {D : ℕ} [NeZero D] (r : ZMod D) {z : ℂ} (hz : 0<z.im) :
    jacobiTheta₂ ((r.val:ℂ)/D) (z/D) = ∑ s : ZMod D, ZMod.stdAddChar (r*s)*packet D s z := by
  have hp : (0:ℝ)<D := Nat.cast_pos.mpr (NeZero.pos D)
  have hz' : 0<(z/(D:ℂ)).im := by simp [div_eq_mul_inv,Complex.mul_im]; positivity
  apply (hasSum_jacobiTheta₂_term _ hz').unique
  apply (hasSum_sum (s:=univ) (fun s _ => (class_hasSum s hz).mul_left (ZMod.stdAddChar (r*s)))).congr_fun
  intro n
  rw [sum_eq_single (n:ZMod D)]
  · rw [if_pos rfl,show r*(n:ZMod D)=(((r.val:ℤ)*n:ℤ):ZMod D) by push_cast; simp,ZMod.stdAddChar_coe]
    simp only [kernel,jacobiTheta₂_term,←Complex.exp_add,Int.cast_mul,Int.cast_natCast]
    congr 1
    ring
  · intro t _ ht
    simp [Ne.symm ht]
  · simp

theorem packet_S {D : ℕ} [NeZero D] (r : ZMod D) {z : ℂ} (hz : 0<z.im) :
    packet D r (-1/z) = ((-I*z)^(1/2:ℂ)/(√(D:ℝ):ℂ))*
      ∑ s : ZMod D, ZMod.stdAddChar (r*s)*packet D s z := by
  have hD : (D:ℂ)≠0 := by exact_mod_cast NeZero.ne D
  have hp : (0:ℝ)<D := Nat.cast_pos.mpr (NeZero.pos D)
  have hzne : z≠0 := by intro e; simp [e] at hz
  rw [packet, show (D:ℂ)*(-1/z)= -1/(z/D) by field_simp, shift_invert _ _ (div_ne_zero hzne hD),
    jacobi_packet r hz]
  congr 1
  rw [show -I*(z/(D:ℂ))=(((D:ℝ)⁻¹:ℝ):ℂ)*(-I*z) by push_cast; ring,
    half_scale (inv_pos.mpr hp) (mul_ne_zero (by simp) hzne),Real.sqrt_inv,Complex.ofReal_inv]
  ring

end
end TunnellRankOnePacket
end

section
/- Rectangular theta packets for a translated ramified quadratic ideal coset. -/
namespace TunnellRectangularIdeal
open TunnellRankOnePacket TunnellIdealHNF
open TunnellClassThetaExpansion TunnellIdealThetaExpansion Finset
open scoped Classical
noncomputable section

lemma offset_sum {D : ℕ} [NeZero D] (r : ℤ) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun l:ℤ => kernel D z ((D:ℤ)*l+r)) (TunnellRankOnePacket.packet D (r:ZMod D) z) := by
  let f (l : ℤ) := (D:ℤ)*l+r
  have hi : Function.Injective f := fun _ _ e => mul_left_cancel₀ (by exact_mod_cast (NeZero.ne D) : (D:ℤ)≠0) (add_right_cancel e)
  have h := class_hasSum (r:ZMod D) hz
  have ht : HasSum (fun l => if ((f l):ZMod D)=(r:ZMod D) then kernel D z (f l) else 0) (TunnellRankOnePacket.packet D (r:ZMod D) z) := by
    apply (hi.hasSum_iff ?_).mpr h
    intro n hn
    split_ifs with e
    · exfalso; apply hn
      obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub r n D).mp e.symm
      exact ⟨k,by dsimp [f]; omega⟩
    · rfl
  simpa [f] using ht

def rect (d a κ : ℕ) [NeZero d] [NeZero a] [NeZero κ] (b s : ℤ) (z : ℂ) :=
  ∑ i : ZMod a,
    TunnellRankOnePacket.packet (2*κ*a) ((2*(κ:ℤ)*b*i.val:ℤ):ZMod (2*κ*a)) z *
    TunnellRankOnePacket.packet (2*κ*a*(2*d)) (((2*(κ:ℤ)*(2*(d:ℤ))*i.val+4*κ*a*s):ℤ):ZMod (2*κ*a*(2*d))) z

def term (d a κ : ℕ) (b s : ℤ) (z : ℂ) (x : ℤ×ℤ) :=
  Complex.exp (2*Real.pi*Complex.I*z*κ*((a*x.1+b*x.2:ℤ)^2+(2*(d:ℂ))*((x.2:ℂ)+(a:ℂ)*s/d)^2)/a)

private lemma product_sum {X Y : Type*} {f : X→ℂ} {g : Y→ℂ} {x y : ℂ} (hf : HasSum f x) (hg : HasSum g y) :
    HasSum (fun z:X×Y => f z.1*g z.2) (x*y) := hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

set_option maxHeartbeats 600000 in
theorem translated (d a κ : ℕ) [NeZero d] [NeZero a] [NeZero κ] (b s : ℤ) {z : ℂ} (hz : 0<z.im) :
    HasSum (term d a κ b s z) (rect d a κ b s z) := by
  classical
  let weight (i : ZMod a) (x : ℤ×ℤ) := if (x.2:ZMod a)=i then term d a κ b s z x else 0
  unfold rect
  have hterm (i : ZMod a) : HasSum (weight i)
      (TunnellRankOnePacket.packet (2*κ*a) ((2*(κ:ℤ)*b*i.val:ℤ):ZMod (2*κ*a)) z *
      TunnellRankOnePacket.packet (2*κ*a*(2*d)) (((2*(κ:ℤ)*(2*(d:ℤ))*i.val+4*κ*a*s):ℤ):ZMod (2*κ*a*(2*d))) z) := by
    let f (l : ℤ×ℤ) := (l.1-b*l.2,(a:ℤ)*l.2+i.val)
    have hi : Function.Injective f := by
      intro l k e
      have he := congrArg Prod.snd e
      have hk := mul_left_cancel₀ (by exact_mod_cast (NeZero.ne a) : (a:ℤ)≠0) (add_right_cancel he)
      have hr := congrArg Prod.fst e; change l.1-b*l.2=k.1-b*k.2 at hr
      exact Prod.ext (by rw [hk] at hr; exact sub_left_inj.mp hr) hk
    apply (hi.hasSum_iff ?_).mp
    · have h₁ := offset_sum (D:=2*κ*a) (2*(κ:ℤ)*b*i.val) hz
      have h₂ := offset_sum (D:=2*κ*a*(2*d)) (2*(κ:ℤ)*(2*(d:ℤ))*i.val+4*κ*a*s) hz
      have H := product_sum h₁ h₂
      apply H.congr_fun
      rintro ⟨l,k⟩
      simp only [Function.comp_apply,f,weight,Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul,zero_add,ZMod.natCast_zmod_val,ite_true]
      simp only [term,kernel,←Complex.exp_add]
      congr 1; push_cast
      have ha : (a:ℂ)≠0 := by exact_mod_cast NeZero.ne a
      have hd : (d:ℂ)≠0 := by exact_mod_cast NeZero.ne d
      have hk : (κ:ℂ)≠0 := by exact_mod_cast NeZero.ne κ
      field_simp; ring
    · rintro ⟨x,y⟩ he
      unfold weight
      split_ifs with h
      · exfalso; apply he
        obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (i.val:ℤ) y a).mp (by simpa using h.symm)
        exact ⟨(x+b*k,k),Prod.ext (by dsimp [f]; ring) (by dsimp [f]; omega)⟩
      · rfl
  apply (hasSum_sum (s:=univ) (fun i _ => hterm i)).congr_fun
  intro x; simp [weight]

end
end TunnellRectangularIdeal
end

section
/- The arithmetic trace of the rectangular theta series in orthogonal local coordinates. -/
namespace TunnellDensityTrace
open TunnellRamifiedLines TunnellRectangularClasses TunnellLineDensity TunnellGluePacket
open TunnellIdealHNF TunnellRectangularIdeal
open scoped Classical
noncomputable section
variable {d : ℕ}
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩

def shifts (hs : Squarefree d) (k : (i : P d) → (ZMod i.val)ˣ) : Packet d ≃ ZMod d×ZMod d where
  toFun x := ((redEquiv hs).symm (fun i => (k i:ZMod i.val)*(x i).1),
    (redEquiv hs).symm (fun i => (k i:ZMod i.val)*(x i).2))
  invFun w i := (((k i)⁻¹:ZMod i.val)*reduce i w.1,((k i)⁻¹:ZMod i.val)*reduce i w.2)
  left_inv x := by
    funext i; apply Prod.ext
    · change ((k i)⁻¹:ZMod i.val) * ((redEquiv hs) ((redEquiv hs).symm _)) i = (x i).1
      rw [Equiv.apply_symm_apply]; exact inv_mul_cancel_left₀ (Units.ne_zero (k i)) _
    · change ((k i)⁻¹:ZMod i.val) * ((redEquiv hs) ((redEquiv hs).symm _)) i = (x i).2
      rw [Equiv.apply_symm_apply]; exact inv_mul_cancel_left₀ (Units.ne_zero (k i)) _
  right_inv w := by
    apply Prod.ext
    · apply (redEquiv hs).injective
      rw [Equiv.apply_symm_apply]; funext i; change (k i:ZMod i.val)*(((k i)⁻¹:ZMod i.val)*_)=_; exact mul_inv_cancel_left₀ (Units.ne_zero (k i)) _
    · apply (redEquiv hs).injective
      rw [Equiv.apply_symm_apply]; funext i; change (k i:ZMod i.val)*(((k i)⁻¹:ZMod i.val)*_)=_; exact mul_inv_cancel_left₀ (Units.ne_zero (k i)) _

lemma shifts_apply (hs : Squarefree d) (k : (i : P d) → (ZMod i.val)ˣ) (x : Packet d) (i : P d) :
    (reduce i (shifts hs k x).1,reduce i (shifts hs k x).2)=((k i:ZMod i.val)*(x i).1,(k i:ZMod i.val)*(x i).2) := by
  apply Prod.ext
  · exact congrFun ((redEquiv hs).apply_symm_apply _) i
  · exact congrFun ((redEquiv hs).apply_symm_apply _) i

end
end TunnellDensityTrace
end

section
/- Recovering the rectangular shift after adjoining orthogonal ramified packet coordinates. -/
namespace TunnellDensityTrace
open TunnellRamifiedLines TunnellRectangularClasses Finset
open scoped Classical
noncomputable section
variable {d : ℕ}
private instance prime_for_density_shift (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩

def complementaryUnit (hs : Squarefree d) (i : P d) : (ZMod i.val)ˣ :=
  ZMod.unitOfCoprime (d/i.val) (Nat.coprime_of_squarefree_mul (by rwa [Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors i.property)]))

def assemble (x : (i : P d) → ZMod i.val) : ZMod d := ∑ i : P d, (((d/i.val)*(x i).val:ℕ):ZMod d)

lemma reduce_assemble (x : (i : P d) → ZMod i.val) (i : P d) :
    reduce i (assemble x)=((d/i.val:ℕ):ZMod i.val)*x i := by
  rw [assemble,map_sum,Finset.sum_eq_single i]
  · rw [map_natCast,Nat.cast_mul,ZMod.natCast_zmod_val]
  · intro j _ hj
    have hc : i.val.Coprime j.val := (Nat.coprime_primes (prime_for_density_shift i).out (prime_for_density_shift j).out).mpr (fun e => hj (Subtype.ext e.symm))
    have hj' := Nat.dvd_of_mem_primeFactors j.property
    have h : i.val ∣ d/j.val := Nat.dvd_div_of_mul_dvd (hc.symm.mul_dvd_of_dvd_of_dvd hj' (Nat.dvd_of_mem_primeFactors i.property))
    simp [map_natCast,(ZMod.natCast_eq_zero_iff _ _).mpr h]
  · simp

theorem shifts_eq (hs : Squarefree d) (x : Packet d) :
    shifts hs (complementaryUnit hs) x = (assemble (fun i => (x i).1),assemble (fun i => (x i).2)) := by
  apply Prod.ext
  · apply red_ext hs; intro i; rw [reduce_assemble]
    have h := congrArg Prod.fst (shifts_apply hs (complementaryUnit hs) x i)
    simpa [complementaryUnit] using h
  · apply red_ext hs; intro i; rw [reduce_assemble]
    have h := congrArg Prod.snd (shifts_apply hs (complementaryUnit hs) x i)
    simpa [complementaryUnit] using h

end
end TunnellDensityTrace
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

def integrand {N k : ℕ} [NeZero N] [NeZero k] (χ : DirichletCharacter ℂ N)
    (θ : ℍ → ℂ) (s : ℂ) (z : ℍ) : ℂ :=
  (z.im:ℂ)^2*etaValue z*conj (θ z)*conj (eisenstein (k:=k) χ z (conj s))

end
end TunnellRankinIntegral
end

section
/- Integral coset and translation coordinates for the unfolding. -/
namespace TunnellRankinIntegral
open Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellRankinEisenstein
noncomputable section

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

end
end TunnellRankinIntegral
end

section
/- Remove the hyperbolic density on the horizontal strip and integrate in height. -/
namespace TunnellRankinIntegral
open Complex UpperHalfPlane MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

def planeCoords : ℂ ≃ᵐ ℝ×ℝ := measurableEquivRealProd.trans MeasurableEquiv.prodComm

def coords (z : ℍ) : ℝ×ℝ := (z.im,z.re)

lemma plane_preserving : MeasurePreserving planeCoords := by
  have h : MeasurePreserving (Prod.swap : ℝ×ℝ→ℝ×ℝ) := by
    simpa only [Measure.volume_eq_prod] using (Measure.measurePreserving_swap (μ:=volume) (ν:=volume) :
      MeasurePreserving (Prod.swap : ℝ×ℝ→ℝ×ℝ) (volume.prod volume) (volume.prod volume))
  exact h.comp volume_preserving_equiv_real_prod

lemma coords_embedding : MeasurableEmbedding coords :=
  planeCoords.measurableEmbedding.comp UpperHalfPlane.measurableEmbedding_coe

def density (z : ℍ) : ℝ≥0 := (1/⟨z.im,z.im_pos.le⟩)^2

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
/- Horizontal Fourier bounds and measurable planar strip kernel in actual hyperbolic coordinates. -/
namespace TunnellRankinIntegral
open Complex AddCircle Set Function TunnellRankin TunnellClassThetaMellin
open TunnellFullClassTheta TunnellShell TunnellEtaValue MeasureTheory
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable section

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

def petersson (L : ℕ) (F : ℍ→ℂ) : ℂ :=
  ∑' q : Cosets L, ∫ z in fdo,F (rep q • z)

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
/- The weight-two eta pairing and its integrability on the level-32 tiles. -/
namespace TunnellHalfPairing
open ModularForm Complex MeasureTheory MatrixGroups ModularGroup CongruenceSubgroup UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate
noncomputable section
def pair (F : ℍ→ℂ) (z : ℍ) := (z.im:ℂ)^2*(ModularForm.eta (4*(z:ℂ))^2*ModularForm.eta (8*(z:ℂ))^2)*conj (F z)
def regular (F : ℍ→ℂ) :=
  Measurable (pair F) ∧ (∀ (g : Gamma0 32) z, pair F (g.val • z)=pair F z) ∧
  ∀ q : SL(2,ℤ) ⧸ Gamma0 32, IntegrableOn (fun z => pair F (q.out⁻¹ • z)) fdo

end
end TunnellHalfPairing
end

section
/- Modular invariance and integrability of the actual theta-product Petersson
integrand, including every translated modular polygon. -/
namespace TunnellLevelPairing
open Complex Matrix MatrixGroups ModularGroup ModularForm CongruenceSubgroup MeasureTheory
open TunnellRankinIntegral TunnellHalfPairing TunnellRankinEisenstein TunnellRankin TunnellShell
open TunnellFullClassTheta TunnellRankinCotangent TunnellClassThetaMellin TunnellEtaValue
open UpperHalfPlane hiding I
open scoped ModularForm ComplexConjugate
noncomputable section

lemma pair_eta (F : ℍ→ℂ) (z : ℍ) : pair F z=(z.im:ℂ)^2*etaValue z*conj (F z) := rfl

lemma pair_pull {g : SL(2,ℤ)} (h : g∈Gamma0 32) (F : ℍ→ℂ) (z : ℍ) :
    pair F (g • z)=pair (F ∣[(2:ℤ)] g) z := by
  let J := denom g z
  have hn : J≠0 := denom_ne_zero _ _
  have hc : conj J≠0 := (map_ne_zero conj).mpr hn
  rw [pair_eta,pair_eta,SL_slash_apply,TunnellEtaLevel.eta_level _ h,ModularGroup.im_smul_eq_div_normSq,normSq_eq_norm_sq]
  change ((z.im/‖J‖^2:ℝ):ℂ)^2*(J^2*etaValue z)*conj (F (g • z)) =
      (z.im:ℂ)^2*etaValue z*conj (F (g • z)*J^(-2:ℤ))
  rw [map_mul,map_zpow₀]
  rw [_root_.zpow_neg,zpow_ofNat]
  field_simp [hc]
  linear_combination etaValue z*conj (F (g • z))*height_cancel z.im hn

variable {d : ℕ} {b : Triple} (hn : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))
def source (z : ℍ) := full hn (by omega) hb z*full hn (by omega) hb (multiple 4 z)

lemma source_invariant (g : SL(2,ℤ)) (h : g∈Gamma0 (32*d)) :
    (source hn hd hb) ∣[(2:ℤ)] g=source hn hd hb := by
  let θ := full hn (by omega) hb
  let χ := negCharacter d (by omega)
  let J := denom g
  have hN : g∈Gamma0 (4*(2*d)) := gamma_dvd (by exact ⟨4,by ring⟩) h
  have hL : g∈Gamma0 (4*(2*d)*4) := by convert h using 2; ring
  funext z
  rw [SL_slash_apply,source,full_action_one hn hd hb z g hN]
  have e := full_action hn hd hb (k:=4) z g hL
  change χ _*θ (multiple 4 (g • z))=J z*θ (multiple 4 z) at e
  change χ _*J z*θ z*θ (multiple 4 (g • z))*(J z)^(-2:ℤ)=θ z*θ (multiple 4 z)
  have hz : J z≠0 := denom_ne_zero _ _
  rw [_root_.zpow_neg,zpow_ofNat]
  field_simp
  linear_combination (θ z)*e

lemma high_invariant (g : SL(2,ℤ)) (h : g∈Gamma0 (32*d)) (z : ℍ) :
    pair (source hn hd hb) (g • z)=pair (source hn hd hb) z := by
  rw [pair_pull (gamma_dvd (dvd_mul_right 32 _) h),source_invariant hn hd hb g h]

lemma high_relation (z : ℍ) :
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    integrand (k:=4) (negCharacter d (by omega)) (full hn (by omega) hb) 1 z =
      (2*Real.pi/(v d:ℂ))*pair (source hn hd hb) z := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  rw [integrand,map_one,eisenstein_one hn hd hb]
  rw [pair_eta]
  unfold source
  simp only [map_mul,map_div₀,Complex.conj_ofReal,map_ofNat]
  have eq4 : multiple ⟨4,by decide⟩ z = multiple 4 z := rfl
  rw [eq4]
  ring

lemma high_meas : Measurable (pair (source hn hd hb)) := by
  have hm := full_meas hn hd hb
  change Measurable (fun z : ℍ => (z.im:ℂ)^2*etaValue z*conj (full hn (by omega) hb z*full hn (by omega) hb (multiple 4 z)))
  apply Measurable.mul
  · exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).measurable.pow_const 2).mul etaValue_hol.continuous.measurable
  · apply Complex.continuous_conj.measurable.comp
    apply hm.mul (hm.comp _)
    exact (UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr (continuous_const.mul UpperHalfPlane.continuous_coe)).measurable

lemma high_integrable (g : SL(2,ℤ)) :
    IntegrableOn (fun z => pair (source hn hd hb) (g • z)) fdo := by
  letI : NeZero (4*(2*d)) := ⟨by omega⟩
  let a : ℂ := 2*Real.pi/(v d:ℂ)
  have ha : a≠0 := div_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) (by exact_mod_cast (v_pos (by omega : 0<d)).ne')
  obtain ⟨C,hC,h⟩ := integrand_growth hn hd hb g
  have h1 : (1:ℂ)∈window := by norm_num [window,mem_ball_zero_iff]
  letI : IsFiniteMeasure (volume.restrict fdo) := isFiniteMeasure_restrict.mpr fdo_finite.ne
  apply (integrable_const (μ:=volume.restrict fdo) (C/‖a‖)).mono'
    (((high_meas hn hd hb).comp (measurePreserving_smul (g:GL (Fin 2) ℝ) volume).measurable).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem isOpen_fdo.measurableSet] with z hz
  have H := h z hz 1 h1
  rw [high_relation hn hd hb,norm_mul] at H
  exact (le_div_iff₀ (norm_pos_iff.mpr ha)).mpr (by simpa [a,mul_comm] using H)

end
end TunnellLevelPairing
end

section
/- Orthogonal prime-to-prime coordinates of a rectangular discriminant group.
Coordinates are represented by the two perpendicular subgroups M x and p y. -/
namespace TunnellPacketCRT
open Complex Real TunnellRankOnePacket
noncomputable section

def merge {p M : ℕ} (hc : p.Coprime M) : ZMod p × ZMod M ≃ ZMod (p*M) :=
  ((ZMod.unitOfCoprime M hc.symm).mulLeft.prodCongr (ZMod.unitOfCoprime p hc).mulLeft).trans
    (ZMod.chineseRemainder hc).symm.toEquiv

lemma merge_lifts {p M : ℕ} (hc : p.Coprime M) (x y : ℤ) :
    merge hc ((x:ZMod p),(y:ZMod M))=(((M:ℤ)*x+p*y:ℤ):ZMod (p*M)) := by
  apply (ZMod.chineseRemainder hc).injective
  change (ZMod.chineseRemainder hc) ((ZMod.chineseRemainder hc).symm _) = _
  rw [RingEquiv.apply_symm_apply,map_intCast]
  apply Prod.ext <;> simp [Units.mulLeft,Equiv.prodCongr,ZMod.coe_unitOfCoprime]

lemma fourier_split {p M : ℕ} [NeZero p] [NeZero M] (hc : p.Coprime M)
    (x y : ZMod p) (u v : ZMod M) :
    ZMod.stdAddChar (merge hc (x,u)*merge hc (y,v)) =
      ZMod.stdAddChar ((M:ZMod p)*x*y)*ZMod.stdAddChar ((p:ZMod M)*u*v) := by
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨y,rfl⟩ := ZMod.intCast_surjective y
  obtain ⟨u,rfl⟩ := ZMod.intCast_surjective u
  obtain ⟨v,rfl⟩ := ZMod.intCast_surjective v
  have hp : (p:ℂ)≠0 := by exact_mod_cast NeZero.ne p
  have hM : (M:ℂ)≠0 := by exact_mod_cast NeZero.ne M
  rw [merge_lifts,merge_lifts,←Int.cast_mul,
    show (M:ZMod p)*(x:ZMod p)*(y:ZMod p)=(((M:ℤ)*x*y:ℤ):ZMod p) by push_cast; rfl,
    show (p:ZMod M)*(u:ZMod M)*(v:ZMod M)=(((p:ℤ)*u*v:ℤ):ZMod M) by push_cast; rfl]
  rw [ZMod.stdAddChar_coe,ZMod.stdAddChar_coe,ZMod.stdAddChar_coe]
  push_cast
  let k : ℤ := x*v+u*y
  have e : (2:ℂ)*π*I*((M*x+p*u)*(M*y+p*v))/(p*M) =
      (2*π*I*(M*x*y)/p+2*π*I*(p*u*v)/M) + (k:ℂ)*(2*π*I) := by
    dsimp [k]; push_cast; field_simp; ring
  rw [e,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one,Complex.exp_add]

def expQ (D : ℕ) (j x : ℤ) : ℂ := Complex.exp (π*I*(j:ℂ)*(x:ℂ)^2/D)

lemma expQ_period {D : ℕ} [NeZero D] (hD : Even D) (j x l : ℤ) :
    expQ D j (x+D*l)=expQ D j x := by
  have hD' : (D:ℂ)≠0 := by exact_mod_cast NeZero.ne D
  obtain ⟨k,hk⟩ := hD
  have hk' : (D:ℂ)=(k:ℂ)+k := by exact_mod_cast hk
  let m : ℤ := j*(x*l+k*l^2)
  have e : (π:ℂ)*I*j*((x:ℂ)+D*l)^2/D =
      π*I*j*(x:ℂ)^2/D + (m:ℂ)*(2*π*I) := by
    dsimp [m]; push_cast; field_simp; rw [hk']; ring
  unfold expQ
  push_cast
  rw [e,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]

lemma phase_lift {D : ℕ} [NeZero D] (hD : Even D) (j x : ℤ) :
    (phase D (x:ZMod D))^j=expQ D j x := by
  let r : ZMod D := x
  have he : ((r.val:ℤ):ZMod D)=(x:ZMod D) := by simp [r]
  obtain ⟨l,hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (r.val:ℤ) x D).mp he
  have he' : x=(r.val:ℤ)+D*l := by omega
  calc
    _ = expQ D j (r.val:ℤ) := by
      change (Complex.exp (π*I*(r.val:ℂ)^2/D))^j = _
      rw [←Complex.exp_int_mul]
      unfold expQ
      push_cast
      congr 1
      ring
    _ = expQ D j x := by conv_rhs => rw [he',expQ_period hD]

lemma translate_trivial {D : ℕ} [NeZero D] (hD : Even D) (j : ℤ) (hj : (2*(D:ℤ))∣j) (r : ZMod D) :
    (phase D r)^j=1 := by
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective r
  obtain ⟨l,rfl⟩ := hj
  rw [phase_lift hD]
  unfold expQ
  have hp : (D:ℂ)≠0 := by exact_mod_cast NeZero.ne D
  convert Complex.exp_int_mul_two_pi_mul_I (l*x^2) using 2
  push_cast; field_simp

lemma translate_split {p k : ℕ} [NeZero p] [NeZero k] (hc : p.Coprime (2*k)) (j : ℤ)
    (hj : 4*(k:ℤ) ∣ j) (x : ZMod p) (u : ZMod (2*k)) :
    (phase (p*(2*k)) (merge hc (x,u)))^j = ZMod.stdAddChar ((j:ZMod p)*(k:ZMod p)*x^2) := by
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨u,rfl⟩ := ZMod.intCast_surjective u
  obtain ⟨l,hl⟩ := hj
  have he : Even (p*(2*k)) := by exact (even_two.mul_right k).mul_left p
  have hp : (p:ℂ)≠0 := by exact_mod_cast NeZero.ne p
  have hk : (k:ℂ)≠0 := by exact_mod_cast NeZero.ne k
  rw [merge_lifts,phase_lift he,
    show (j:ZMod p)*(k:ZMod p)*(x:ZMod p)^2=(((j:ℤ)*(k:ℤ)*x^2:ℤ):ZMod p) by push_cast; rfl,
    ZMod.stdAddChar_coe]
  let m : ℤ := j*x*u+l*p*u^2
  have e : (π:ℂ)*I*j*((2*k:ℂ)*x+p*u)^2/(p*(2*k)) =
      2*π*I*(j*(k:ℂ)*x^2)/p+(m:ℂ)*(2*π*I) := by
    dsimp [m]; rw [hl]; push_cast; field_simp; ring
  unfold expQ
  push_cast
  rw [e,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]

end
end TunnellPacketCRT
end

section
/- Fourier inversion on the prime-to-p complement of a rectangular packet. -/
namespace TunnellPacketComplement
open Finset Complex
noncomputable section

def char {D : ℕ} [NeZero D] (k : ZMod D) (x y : ZMod D) : ℂ := ZMod.stdAddChar (k*x*y)

lemma char_inverse {D : ℕ} [NeZero D] (k : ZMod D) (hk : IsUnit k) (x y : ZMod D) :
    ∑ u, char k x u*char (-k) u y=if x=y then (D:ℂ) else 0 := by
  simp only [char,←AddChar.map_add_eq_mul]
  have h (u:ZMod D) : k*x*u + -k*u*y = u*((x-y)*k) := by ring
  simp only [h]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar D),ZMod.card]
  simp only [hk.mul_left_eq_zero,sub_eq_zero]
  split_ifs <;> simp

def tensor {X Y : Type*} (K : X→X→ℂ) (L : Y→Y→ℂ) (x y : X×Y) : ℂ :=
  K x.1 y.1*L x.2 y.2

lemma tensor_inverse {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {K J : X→X→ℂ} {L M : Y→Y→ℂ} {b c : ℂ}
    (h : ∀ x y, ∑ u,K x u*J u y=if x=y then b else 0)
    (g : ∀ x y, ∑ v,L x v*M v y=if x=y then c else 0) (x y : X×Y) :
    ∑ u,tensor K L x u*tensor J M u y=if x=y then b*c else 0 := by
  rw [Fintype.sum_prod_type]
  unfold tensor
  have e (i : X) (j : Y) : K x.1 i * L x.2 j * (J i y.1 * M j y.2)=
      (K x.1 i*J i y.1)*(L x.2 j*M j y.2) := by ring
  simp only [e,←mul_sum,←sum_mul,h,g]
  rcases x with ⟨x,u⟩
  rcases y with ⟨y,v⟩
  by_cases h : x=y <;> by_cases h' : u=v <;> simp [h,h']

abbrev Box (A M B N : ℕ) := ZMod A × ZMod M × ZMod B × ZMod N

def boxChar (A M B N p : ℕ) [NeZero A] [NeZero M] [NeZero B] [NeZero N] (j : ℤ) :
    Box A M B N → Box A M B N → ℂ :=
  tensor (char (j:ZMod A)) (tensor (char ((j:ZMod M)*p))
    (tensor (char (j:ZMod B)) (char ((j:ZMod N)*p))))

theorem box_inverse {A M B N p : ℕ} [NeZero A] [NeZero M] [NeZero B] [NeZero N]
    (hc : p.Coprime M) (hd : p.Coprime N) (x y : Box A M B N) :
    ∑ u, boxChar A M B N p 1 x u*boxChar A M B N p (-1) u y =
      if x=y then (A:ℂ)*(M*(B*N)) else 0 := by
  have hM := (ZMod.isUnit_iff_coprime p M).mpr hc
  have hN := (ZMod.isUnit_iff_coprime p N).mpr hd
  simpa only [boxChar,Int.cast_one,Int.cast_neg,neg_mul,one_mul] using
    tensor_inverse (char_inverse (1:ZMod A) isUnit_one)
      (tensor_inverse (char_inverse (p:ZMod M) hM)
        (tensor_inverse (char_inverse (1:ZMod B) isUnit_one) (char_inverse (p:ZMod N) hN))) x y

end
end TunnellPacketComplement
end

section
/- The integral weight-two action on a product of four unary lattice packets. -/
namespace TunnellRectangularPacket
open Complex Real Finset TunnellRankOnePacket TunnellPacketCRT MatrixGroups ModularGroup ModularForm
open UpperHalfPlane hiding I
open scoped ModularForm
noncomputable section

lemma packet_Tpow {D : ℕ} [NeZero D] (he : Even D) (r : ZMod D) {z : ℂ} (hz : 0<z.im) (j : ℤ) :
    packet D r (z+(j:ℂ))=(phase D r)^j*packet D r z := by
  apply (packet_hasSum r (z:=z+(j:ℂ)) (by simpa using hz)).unique
  apply ((packet_hasSum r hz).mul_left ((phase D r)^j)).congr_fun
  intro l
  let a : ℤ := D*l+r.val
  have h : (a:ZMod D)=r := by simp [a]
  have hh := phase_lift he j a
  rw [h] at hh
  rw [hh]
  unfold kernel expQ
  rw [←Complex.exp_add]
  congr 1
  dsimp [a]
  ring

lemma packet_neg {D : ℕ} [NeZero D] (r : ZMod D) {z : ℂ} (hz : 0<z.im) :
    packet D (-r) z=packet D r z := by
  apply (class_hasSum (-r) hz).unique
  apply (((Equiv.neg ℤ).hasSum_iff).mpr (class_hasSum r hz)).congr_fun
  intro n
  simp [kernel,neg_eq_iff_eq_neg,Function.comp_def]

lemma packet_Sneg {D : ℕ} [NeZero D] (r : ZMod D) {z : ℂ} (hz : 0<z.im) :
    packet D r (-1/z) = ((-I*z)^(1/2:ℂ)/(√(D:ℝ):ℂ))*
      ∑ s : ZMod D, ZMod.stdAddChar (-(r*s))*packet D s z := by
  let w : ℍ := ⟨z,hz⟩
  have hp : 0<(-1/z).im := by simpa [w,neg_div,one_div,inv_neg] using w.im_inv_neg_coe_pos
  rw [←packet_neg r hp,packet_S _ hz]
  simp only [neg_mul]

abbrev Index (D : Fin 4→ℕ) := (i : Fin 4)→ZMod (D i)
variable (D : Fin 4→ℕ) [∀ i, NeZero (D i)]

def theta (r : Index D) (z : ℍ) : ℂ := ∏ i,packet (D i) (r i) z

def scale : ℂ := -(∏ i, (√(D i:ℝ):ℂ))⁻¹

def pair (r s : Index D) : ℂ := ∏ i, ZMod.stdAddChar (r i*s i)

def negPair (r s : Index D) : ℂ := ∏ i, ZMod.stdAddChar (-(r i*s i))

def diag (j : ℤ) (r : Index D) : ℂ := ∏ i,(phase (D i) (r i))^j

lemma theta_T (he : ∀ i, Even (D i)) (j : ℤ) (r : Index D) (z : ℍ) :
    ((theta D r) ∣[(2:ℤ)] (T^j)) z = diag D j r*theta D r z := by
  rw [SL_slash_apply,modular_T_zpow_smul,theta]
  have hj : denom (T^j:SL(2,ℤ)) z=1 := by rw [ModularGroup.denom_apply]; simp [coe_T_zpow]
  simp only [hj,one_zpow,mul_one,UpperHalfPlane.coe_vadd,Complex.ofReal_intCast,add_comm (j:ℂ)]
  simp only [packet_Tpow (he _) _ z.im_pos,prod_mul_distrib,diag,theta]

private lemma S_slash {K : ∀ i, ZMod (D i)→ZMod (D i)→ℂ}
    (h : ∀ i (r : ZMod (D i)) (z : ℍ), packet (D i) r (-1/(z:ℂ)) =
      ((-I*z)^(1/2:ℂ)/(√(D i:ℝ):ℂ))*∑ s, K i r s*packet (D i) s z)
    (r : Index D) (z : ℍ) :
    ((theta D r) ∣[(2:ℤ)] S) z = scale D*∑ s : Index D, (∏ i, K i (r i) (s i))*theta D s z := by
  rw [SL_slash_apply,modular_S_smul,denom_S]
  unfold theta
  change (∏ i,packet (D i) (r i) (-(↑z:ℂ))⁻¹)*_ = _
  simp only [show (-(↑z:ℂ))⁻¹= -1/(z:ℂ) by ring,h,prod_mul_distrib,Finset.prod_div_distrib,
    prod_const,Finset.card_univ,Fintype.card_fin]
  have pow : ((-I*(z:ℂ))^(1/2:ℂ))^4 = -(z:ℂ)^2 := by
    rw [←Complex.cpow_mul_ofNat,show (1/2:ℂ)*4=2 by norm_num,Complex.cpow_ofNat]
    ring_nf
    simp
  rw [pow,Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]
  unfold scale
  have hn : (z:ℂ)≠0 := z.ne_zero
  rw [zpow_neg,zpow_ofNat]
  field_simp

theorem theta_S (r : Index D) (z : ℍ) :
    ((theta D r) ∣[(2:ℤ)] S) z = scale D*∑ s : Index D,pair D r s*theta D s z :=
  S_slash D (fun i r z => packet_S r z.im_pos) r z

theorem theta_Sminus (r : Index D) (z : ℍ) :
    ((theta D r) ∣[(2:ℤ)] S) z = scale D*∑ s : Index D,negPair D r s*theta D s z :=
  S_slash D (fun i r z => packet_Sneg r z.im_pos) r z

lemma scale_sq : (scale D)^2*(Fintype.card (Index D):ℂ)=1 := by
  have pos (i : Fin 4) : (D i:ℝ)>0 := by exact_mod_cast NeZero.pos (D i)
  have h (i : Fin 4) : (√(D i:ℝ):ℂ)^2=(D i:ℂ) := by exact_mod_cast Real.sq_sqrt (pos i).le
  have p : ∏ i, (√(D i:ℝ):ℂ) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Real.sqrt_pos.mpr (pos i)).ne'
  rw [scale,neg_sq,inv_pow,Fintype.card_pi]
  push_cast
  simp only [ZMod.card,←Finset.prod_pow,h]
  have q : ∏ i,(D i:ℂ) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast NeZero.ne (D i)
  field_simp

end
end TunnellRectangularPacket
end

section
/- The Weyl representative built from the two elementary unipotents of a ramified
quadratic plane. Its first row gives the exact scalar for the level trace. -/
namespace TunnellRamifiedWeyl
open Finset TunnellRamifiedPlane
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def bil (a t : (ZMod p)) (x y : ((ZMod p)×(ZMod p))) : (ZMod p) := 2*a*(x.1*y.1-t*x.2*y.2)
def translate (a t k : (ZMod p)) (f : ((ZMod p)×(ZMod p))→ℂ) (x : ((ZMod p)×(ZMod p))) : ℂ := (ZMod.stdAddChar (N:=p)) (k*form a t x)*f x
def fourier (a t k : (ZMod p)) (f : ((ZMod p)×(ZMod p))→ℂ) (x : ((ZMod p)×(ZMod p))) : ℂ := ∑ u : ((ZMod p)×(ZMod p)), (ZMod.stdAddChar (N:=p)) (k*bil a t x u)*f u
def lower (a t : (ZMod p)) (f : ((ZMod p)×(ZMod p))→ℂ) (x : ((ZMod p)×(ZMod p))) : ℂ :=
  ((p:ℂ)^2)⁻¹*fourier a t 1 (translate a t (-1) (fourier a t (-1) f)) x
def weyl (a t : (ZMod p)) (f : ((ZMod p)×(ZMod p))→ℂ) :=
  translate a t (-1) (lower a t (translate a t (-1) f))

lemma complete (a t : (ZMod p)) (x v u : ((ZMod p)×(ZMod p))) :
    -(form a t x) + bil a t x u - form a t u - bil a t u v - form a t v =
      form (-a) t (u+(v-x)) - bil a t x v := by
  simp [form,bil]
  ring

lemma weyl_kernel (hp : p≠2) {a t : (ZMod p)} (ha : a≠0) (ht : t≠0) (f : ((ZMod p)×(ZMod p))→ℂ) (x : ((ZMod p)×(ZMod p))) :
    weyl a t f x=gauss a t/(p:ℂ)^2*fourier a t (-1) f x := by
  classical
  have hG : gauss (-a) t=gauss a t := (gauss_eq hp (neg_ne_zero.mpr ha) ht).trans (gauss_eq hp ha ht).symm
  have block (u v : ((ZMod p)×(ZMod p))) : (ZMod.stdAddChar (N:=p)) (-(form a t x))* ((ZMod.stdAddChar (N:=p)) (bil a t x u)*
      ((ZMod.stdAddChar (N:=p)) (-form a t u)*((ZMod.stdAddChar (N:=p)) (-bil a t u v)*((ZMod.stdAddChar (N:=p)) (-form a t v)*f v)))) =
      (ZMod.stdAddChar (N:=p)) (form (-a) t (u+(v-x)))*((ZMod.stdAddChar (N:=p)) (-bil a t x v)*f v) := by
    simp only [←mul_assoc,←AddChar.map_add_eq_mul]
    congr 2
    convert complete a t x v u using 1 <;> ring
  have hsum (v : ((ZMod p)×(ZMod p))) : (∑ u : ((ZMod p)×(ZMod p)), (ZMod.stdAddChar (N:=p)) (form (-a) t (u+(v-x))))=gauss a t := by
    rw [←hG,gauss]
    exact Equiv.sum_comp (Equiv.addRight (v-x)) (fun w : ((ZMod p)×(ZMod p)) => (ZMod.stdAddChar (N:=p)) (form (-a) t w))
  unfold weyl lower translate fourier
  simp only [one_mul,neg_one_mul]
  calc
    _ = ((p:ℂ)^2)⁻¹*∑ u : ((ZMod p)×(ZMod p)), ∑ v : ((ZMod p)×(ZMod p)), (ZMod.stdAddChar (N:=p)) (-(form a t x))*((ZMod.stdAddChar (N:=p)) (bil a t x u)*
          ((ZMod.stdAddChar (N:=p)) (-form a t u)*((ZMod.stdAddChar (N:=p)) (-bil a t u v)*((ZMod.stdAddChar (N:=p)) (-form a t v)*f v)))) := by
      rw [mul_left_comm]
      simp only [mul_sum]
    _ = ((p:ℂ)^2)⁻¹*∑ v : ((ZMod p)×(ZMod p)), (∑ u : ((ZMod p)×(ZMod p)), (ZMod.stdAddChar (N:=p)) (form (-a) t (u+(v-x))))*((ZMod.stdAddChar (N:=p)) (-bil a t x v)*f v) := by
      congr 1
      simp only [block,sum_mul]
      rw [sum_comm]
    _ = _ := by simp only [hsum,←mul_sum]; ring

theorem weyl_trace (hp : p≠2) {a t : (ZMod p)} (ha : a≠0) (ht : t≠0) (f : ((ZMod p)×(ZMod p))→ℂ) :
    f 0 + ∑ j : (ZMod p), weyl a t (translate a t j f) 0 = trace a t f := by
  simp [weyl_kernel hp ha ht,fourier,bil,translate,trace,Finset.mul_sum]
  rfl

end
end TunnellRamifiedWeyl
end

section
/- Orthogonal p-primary coordinates for the rectangular discriminant group
(A, pM, B, pN). -/
namespace TunnellSplitIndex
open Finset Complex TunnellPacketComplement TunnellPacketCRT TunnellRectangularPacket
open TunnellRamifiedWeyl TunnellRamifiedPlane
noncomputable section

abbrev dims (A H B K : ℕ) : Fin 4 → ℕ := ![A,H,B,K]

lemma dims₀ (A H B K : ℕ) : dims A H B K 0=A := rfl
lemma dims₁ (A H B K : ℕ) : dims A H B K 1=H := rfl
lemma dims₂ (A H B K : ℕ) : dims A H B K 2=B := rfl
lemma dims₃ (A H B K : ℕ) : dims A H B K 3=K := rfl

instance dims_pos {A H B K : ℕ} [NeZero A] [NeZero H] [NeZero B] [NeZero K] (i : Fin 4) :
    NeZero (dims A H B K i) := by fin_cases i <;> assumption

def toIndex (A H B K : ℕ) : Box A H B K ≃ Index (dims A H B K) where
  toFun b := Fin.cons b.1 (Fin.cons b.2.1 (Fin.cons b.2.2.1 (Fin.cons b.2.2.2 (fun i => Fin.elim0 i))))
  invFun r := (r 0,r 1,r 2,r 3)
  left_inv b := rfl
  right_inv r := by funext i; fin_cases i <;> rfl

variable {A M B N p : ℕ} [NeZero A] [NeZero M] [NeZero B] [NeZero N] [Fact p.Prime]

def pack (hc : p.Coprime M) (hd : p.Coprime N) : (Box A M B N) × (ZMod p × ZMod p) ≃ Index (dims A (p*M) B (p*N)) where
  toFun w := toIndex _ _ _ _ (w.1.1,merge hc (w.2.1,w.1.2.1),w.1.2.2.1,merge hd (w.2.2,w.1.2.2.2))
  invFun r :=
    let b := (toIndex _ _ _ _).symm r
    let u := (merge hc).symm b.2.1
    let v := (merge hd).symm b.2.2.2
    ((b.1,u.2,b.2.2.1,v.2),(u.1,v.1))
  left_inv w := by simp
  right_inv r := by
    simp only [Prod.mk.eta,merge,Equiv.apply_symm_apply,Equiv.symm_apply_apply]

lemma pack₀ (hc : p.Coprime M) (hd : p.Coprime N) (x : (Box A M B N)) (u : (ZMod p × ZMod p)) : pack hc hd (x,u) 0=x.1 := rfl
lemma pack₁ (hc : p.Coprime M) (hd : p.Coprime N) (x : (Box A M B N)) (u : (ZMod p × ZMod p)) : pack hc hd (x,u) 1=merge hc (u.1,x.2.1) := rfl
lemma pack₂ (hc : p.Coprime M) (hd : p.Coprime N) (x : (Box A M B N)) (u : (ZMod p × ZMod p)) : pack hc hd (x,u) 2=x.2.2.1 := rfl
lemma pack₃ (hc : p.Coprime M) (hd : p.Coprime N) (x : (Box A M B N)) (u : (ZMod p × ZMod p)) : pack hc hd (x,u) 3=merge hd (u.2,x.2.2.2) := rfl

lemma pair_split (hc : p.Coprime M) (hd : p.Coprime N)
    {a t : ZMod p} (ha : (M:ZMod p)=2*a) (hb : (N:ZMod p)= -2*a*t)
    (x y : (Box A M B N)) (u v : (ZMod p × ZMod p)) : pair (dims A (p*M) B (p*N)) (pack hc hd (x,u)) (pack hc hd (y,v)) =
    boxChar A M B N p 1 x y*(ZMod.stdAddChar (N:=p)) (bil a t u v) := by
  unfold pair
  rw [Fin.prod_univ_four]
  simp only [pack₀,pack₁,pack₂,pack₃,dims₀,dims₁,dims₂,dims₃]
  change ZMod.stdAddChar (x.1*y.1:ZMod A) *
    ZMod.stdAddChar (merge hc (u.1,x.2.1)*merge hc (v.1,y.2.1):ZMod (p*M)) *
    ZMod.stdAddChar (x.2.2.1*y.2.2.1:ZMod B) *
    ZMod.stdAddChar (merge hd (u.2,x.2.2.2)*merge hd (v.2,y.2.2.2):ZMod (p*N))=_
  rw [fourier_split hc u.1 v.1 x.2.1 y.2.1,fourier_split hd u.2 v.2 x.2.2.2 y.2.2.2]
  have e : bil a t u v=(M:ZMod p)*u.1*v.1+N*u.2*v.2 := by rw [ha,hb]; unfold bil; ring
  rw [e,AddChar.map_add_eq_mul]
  simp only [boxChar,tensor,char,Int.cast_one,one_mul]
  ring

lemma diag_split {k l : ℕ} [NeZero k] [NeZero l] (hc : p.Coprime (2*k)) (hd : p.Coprime (2*l))
    (eA : Even A) (eB : Even B) (j : ℤ) (hA : 2*(A:ℤ)∣j) (hB : 2*(B:ℤ)∣j)
    (hk : 4*(k:ℤ)∣j) (hl : 4*(l:ℤ)∣j) {a t : ZMod p}
    (ha : (k:ZMod p)=a) (hb : (l:ZMod p)= -a*t) (x : Box A (2*k) B (2*l)) (u : (ZMod p × ZMod p)) :
    TunnellRectangularPacket.diag (dims A (p*(2*k)) B (p*(2*l))) j (pack hc hd (x,u))=(ZMod.stdAddChar (N:=p)) ((j:ZMod p)*form a t u) := by
  unfold TunnellRectangularPacket.diag
  rw [Fin.prod_univ_four]
  simp only [pack₀,pack₁,pack₂,pack₃,dims₀,dims₁,dims₂,dims₃]
  rw [translate_trivial eA j hA,translate_trivial eB j hB,translate_split hc j hk,translate_split hd j hl,
    one_mul,mul_one,←AddChar.map_add_eq_mul,ha,hb]
  congr 1
  unfold form
  ring

end
end TunnellSplitIndex
end

section
/- Linear operators on the complementary factor and the ramified quadratic plane
of a four-dimensional theta packet. -/
namespace TunnellPacketOperators
open Complex Finset MatrixGroups ModularGroup ModularForm
open scoped ModularForm
open UpperHalfPlane hiding I
noncomputable section

variable {X Y : Type*}

def Law (F : X→Y→ℍ→ℂ) (g : SL(2,ℤ)) (A : Module.End ℂ (X→Y→ℂ)) : Prop :=
  ∀ x y z, ((F x y) ∣[(2:ℤ)] g) z = A (fun x y => F x y z) x y

lemma law_mul {F : X→Y→ℍ→ℂ} {g h : SL(2,ℤ)} {A B : Module.End ℂ (X→Y→ℂ)}
    (hg : Law F g A) (hh : Law F h B) : Law F (g*h) (A.comp B) := by
  intro x y z
  rw [SlashAction.slash_mul,SL_slash_apply,hg]
  have H : B (fun x y => F x y z)=((denom h z)^(-2:ℤ)) • (fun x y => F x y (h • z)) := by
    funext i j
    rw [←hh i j z,SL_slash_apply]
    simp [mul_comm]
  rw [LinearMap.comp_apply,H,map_smul]
  simp [mul_comm]

def plane (A : Module.End ℂ (Y→ℂ)) : Module.End ℂ (X→Y→ℂ) where
  toFun f x := A (f x)
  map_add' f g := funext (fun x => A.map_add _ _)
  map_smul' c f := funext (fun x => A.map_smul _ _)

def left [Fintype X] (K : X→X→ℂ) : Module.End ℂ (X→Y→ℂ) where
  toFun f x := ∑ u, K x u • f u
  map_add' f g := by ext x y; simp [smul_add,sum_add_distrib]
  map_smul' c f := by ext x y; simp [Finset.mul_sum,mul_left_comm]

lemma commute [Fintype X] (A : Module.End ℂ (Y→ℂ)) (K : X→X→ℂ) (f : X→Y→ℂ) :
    left K (plane A f)=plane A (left K f) := by
  funext x
  change ∑ u, K x u • A (f u) = A (∑ u, K x u • f u)
  simp

lemma left_cancel [Fintype X] [DecidableEq X] (K J : X→X→ℂ) (c : ℂ)
    (h : ∀ x y, ∑ u, K x u*J u y=if x=y then c else 0) (f : X→Y→ℂ) :
    left K (left J f)=c • f := by
  ext x y
  change (∑ u, K x u • (∑ v, J u v • f v)) y = c*f x y
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_sum,←mul_assoc]
  rw [sum_comm]
  simp_rw [←sum_mul,h]
  simp

def matrix [Fintype Y] (A : Y→Y→ℂ) : Module.End ℂ (Y→ℂ) where
  toFun f x := ∑ y, A x y*f y
  map_add' f g := by ext x; simp [mul_add,sum_add_distrib]
  map_smul' c f := by ext x; simp [mul_sum,mul_left_comm]

def diagonal (t : Y→ℂ) : Module.End ℂ (Y→ℂ) where
  toFun f x := t x*f x
  map_add' f g := by ext x; simp [mul_add]
  map_smul' c f := by ext x; simp [mul_left_comm]

def weylLift (m : ℤ) : SL(2,ℤ) := T^(-m)*S*T^(-m)*S*T^(-m)

open TunnellRamifiedPlane TunnellRamifiedWeyl
variable {p : ℕ} [Fact p.Prime]

def U (a t j : (ZMod p)) : Module.End ℂ (((ZMod p) × (ZMod p))→ℂ) := diagonal fun x => (ZMod.stdAddChar (N:=p)) (j*form a t x)
def W (a t j : (ZMod p)) : Module.End ℂ (((ZMod p) × (ZMod p))→ℂ) := matrix fun x y => (ZMod.stdAddChar (N:=p)) (j*bil a t x y)

theorem weyl_slash [Fintype X] [DecidableEq X] (F : X→((ZMod p) × (ZMod p))→ℍ→ℂ) (m : ℤ) (a t : (ZMod p))
    (c b : ℂ) (hc : c*c*b=((p:ℂ)^2)⁻¹) (K J : X→X→ℂ)
    (inv : ∀ x y, ∑ u, K x u*J u y=if x=y then b else 0)
    (hT : Law F (T^(-m)) (plane (U a t (-1))))
    (hS : Law F S (c • (left K).comp (plane (W a t 1))))
    (hi : Law F S (c • (left J).comp (plane (W a t (-1)))))
    (x : X) (v : ((ZMod p) × (ZMod p))) (z : ℍ) :
    ((F x v) ∣[(2:ℤ)] (weylLift m)) z=weyl a t (fun v => F x v z) v := by
  have h := law_mul (law_mul (law_mul (law_mul hT hS) hT) hi) hT x v z
  rw [weylLift,h]
  simp only [LinearMap.comp_apply,LinearMap.smul_apply,map_smul,commute]
  rw [left_cancel K J b inv]
  simp only [map_smul,Pi.smul_apply,smul_eq_mul,←mul_assoc,hc]
  let H := TunnellRamifiedWeyl.fourier a t 1 (TunnellRamifiedWeyl.translate a t (-1)
      (TunnellRamifiedWeyl.fourier a t (-1) (TunnellRamifiedWeyl.translate a t (-1) (fun u => F x u z)))) v
  change ((p:ℂ)^2)⁻¹ * ((ZMod.stdAddChar (N:=p)) ((-1)*form a t v)*H) = (ZMod.stdAddChar (N:=p)) ((-1)*form a t v)*(((p:ℂ)^2)⁻¹*H)
  ac_rfl

end
end TunnellPacketOperators
end

section
/- The p-supported weight-two slash transformations of the actual rectangular
theta packet, including the Weyl representative and its local trace. -/
namespace TunnellLocalizedPacket
open Complex Finset TunnellRankOnePacket TunnellRectangularPacket TunnellPacketComplement TunnellSplitIndex
open TunnellPacketOperators TunnellRamifiedPlane TunnellRamifiedWeyl ModularGroup MatrixGroups
open UpperHalfPlane hiding I
open scoped ModularForm ComplexConjugate
noncomputable section
variable {A M B N p : ℕ} [NeZero A] [NeZero M] [NeZero B] [NeZero N] [Fact p.Prime]

def family (hc : p.Coprime M) (hd : p.Coprime N) (x : (Box A M B N)) (v : (ZMod p × ZMod p)) : ℍ→ℂ :=
  theta (dims A (p*M) B (p*N)) (pack hc hd (x,v))

lemma neg_pair_split (hc : p.Coprime M) (hd : p.Coprime N)
    {a t : ZMod p} (ha : (M:ZMod p)=2*a) (hb : (N:ZMod p)= -2*a*t)
    (x y : (Box A M B N)) (u v : (ZMod p × ZMod p)) : negPair (dims A (p*M) B (p*N)) (pack hc hd (x,u)) (pack hc hd (y,v)) =
    boxChar A M B N p (-1) x y*(ZMod.stdAddChar (N:=p)) (-bil a t u v) := by
  have e := congrArg conj (pair_split hc hd ha hb x y u v)
  rw [map_mul] at e
  rw [negPair]
  simp only [AddChar.map_neg_eq_conj,←map_prod]
  rw [show (∏ i, ZMod.stdAddChar (pack hc hd (x,u) i*pack hc hd (y,v) i))=pair (dims A (p*M) B (p*N)) _ _ from rfl,e]
  congr 1
  simp [boxChar,tensor,char,←AddChar.map_neg_eq_conj,neg_mul]

private lemma sum_rule (hc : p.Coprime M) (hd : p.Coprime N) (K : Index (dims A (p*M) B (p*N))→Index (dims A (p*M) B (p*N))→ℂ)
    (L : (Box A M B N)→(Box A M B N)→ℂ) (Q : (ZMod p × ZMod p)→(ZMod p × ZMod p)→ℂ) (h : ∀ (x y : (Box A M B N)) (u v : (ZMod p × ZMod p)),
        K (pack hc hd (x,u)) (pack hc hd (y,v))= L x y*Q u v)
    (hS : ∀ r z, ((theta (dims A (p*M) B (p*N)) r) ∣[(2:ℤ)] S) z=scale (dims A (p*M) B (p*N))*∑ s, K r s*theta (dims A (p*M) B (p*N)) s z) :
    Law (family hc hd) S (scale (dims A (p*M) B (p*N)) • (left L).comp (plane (matrix Q))) := by
  intro x u z
  rw [family,hS,←(pack hc hd).sum_comp (fun s => K (pack hc hd (x,u)) s*theta (dims A (p*M) B (p*N)) s z),Fintype.sum_prod_type]
  simp only [h,mul_assoc]
  change _ = scale (dims A (p*M) B (p*N)) * (∑ y, L x y • fun v => ∑ w, Q v w*family hc hd y w z) u
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_sum,family]

lemma law_plus (hc : p.Coprime M) (hd : p.Coprime N) {a t : ZMod p}
    (ha : (M:ZMod p)=2*a) (hb : (N:ZMod p)= -2*a*t) :
    Law (family (A:=A) (B:=B) hc hd) S (scale (dims A (p*M) B (p*N)) •
      (left (boxChar A M B N p 1)).comp (plane (W a t 1))) := by
  apply sum_rule hc hd (pair (dims A (p*M) B (p*N))) _ (fun u v => (ZMod.stdAddChar (N:=p)) (1*bil a t u v)) _ (theta_S (dims A (p*M) B (p*N)))
  intro x y u v
  simpa using pair_split hc hd ha hb x y u v

lemma law_minus (hc : p.Coprime M) (hd : p.Coprime N) {a t : ZMod p}
    (ha : (M:ZMod p)=2*a) (hb : (N:ZMod p)= -2*a*t) :
    Law (family (A:=A) (B:=B) hc hd) S (scale (dims A (p*M) B (p*N)) •
      (left (boxChar A M B N p (-1))).comp (plane (W a t (-1)))) := by
  apply sum_rule hc hd (negPair (dims A (p*M) B (p*N))) _ (fun u v => (ZMod.stdAddChar (N:=p)) ((-1)*bil a t u v)) _ (theta_Sminus (dims A (p*M) B (p*N)))
  intro x y u v
  simpa using neg_pair_split hc hd ha hb x y u v

lemma local_scale : scale (dims A (p*M) B (p*N))*scale (dims A (p*M) B (p*N))*((A:ℂ)*(M*(B*N)))=((p:ℂ)^2)⁻¹ := by
  have h := scale_sq (dims A (p*M) B (p*N))
  rw [←Fintype.card_congr (toIndex A (p*M) B (p*N))] at h
  simp only [Box,Fintype.card_prod,ZMod.card,Nat.cast_mul] at h
  have hp : (p:ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp
  linear_combination h

variable {k l : ℕ} [NeZero k] [NeZero l]

lemma law_T (hc : p.Coprime (2*k)) (hd : p.Coprime (2*l)) (eA : Even A) (eB : Even B)
    (j : ℤ) (hA : 2*(A:ℤ)∣j) (hB : 2*(B:ℤ)∣j) (hk : 4*(k:ℤ)∣j) (hl : 4*(l:ℤ)∣j)
    {a t : ZMod p} (ha : (k:ZMod p)=a) (hb : (l:ZMod p)= -a*t) :
    Law (family (A:=A) (B:=B) hc hd) (T^j) (plane (U a t (j:ZMod p))) := by
  intro x u z
  have he : ∀ i, Even ((dims A (p*(2*k)) B (p*(2*l))) i) := by
    intro i; fin_cases i
    · exact eA
    · exact (even_two.mul_right k).mul_left p
    · exact eB
    · exact (even_two.mul_right l).mul_left p
  rw [family,theta_T (dims A (p*(2*k)) B (p*(2*l))) he,diag_split hc hd eA eB j hA hB hk hl ha hb x u]
  rfl

theorem localized_weyl (hc : p.Coprime (2*k)) (hd : p.Coprime (2*l)) (eA : Even A) (eB : Even B)
    (m : ℤ) (hm : (m:ZMod p)=1)
    (hA : 2*(A:ℤ)∣m) (hB : 2*(B:ℤ)∣m) (hk : 4*(k:ℤ)∣m) (hl : 4*(l:ℤ)∣m)
    {a t : ZMod p} (ha : (k:ZMod p)=a) (hb : (l:ZMod p)= -a*t)
    (x : (Box A (2*k) B (2*l))) (v : (ZMod p × ZMod p)) (z : ℍ) :
    ((family hc hd x v) ∣[(2:ℤ)] (weylLift m)) z=weyl a t (fun v => family hc hd x v z) v := by
  have ha' : ((2*k:ℕ):ZMod p)=2*a := by push_cast; rw [ha]
  have hb' : ((2*l:ℕ):ZMod p)= -2*a*t := by push_cast; rw [hb]; ring
  apply weyl_slash _ _ _ _ _ _ local_scale _ _ (box_inverse hc hd) _ (law_plus hc hd ha' hb') (law_minus hc hd ha' hb')
  simpa only [Int.cast_neg,hm] using law_T hc hd eA eB (-m) (dvd_neg.mpr hA) (dvd_neg.mpr hB) (dvd_neg.mpr hk) (dvd_neg.mpr hl) ha hb

end
end TunnellLocalizedPacket
end

section
/- Projective bottom rows index the level 32d to level 32 cosets. -/
namespace TunnellTraceCosets
open Finset Matrix MatrixGroups CongruenceSubgroup TunnellRamifiedLines TunnellGluePacket
noncomputable section
variable {d : ℕ}
private instance pPrime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩

abbrev Choices (d : ℕ) := (i : P d)→Option (ZMod i.val)

def slope (g : SL(2,ℤ)) : Choices d := fun i =>
  if (g 1 0:ZMod i.val)=0 then none else some ((g 1 1:ZMod i.val)/(g 1 0:ZMod i.val))

lemma row_nz (g : SL(2,ℤ)) (i : P d) : (g 1 0:ZMod i.val)=0 → (g 1 1:ZMod i.val)≠0 := by
  intro h0 h1
  have e := g.det_coe
  rw [Matrix.det_fin_two] at e
  have he := congrArg (fun n : ℤ => (n:ZMod i.val)) e
  push_cast at he
  simp [h0,h1] at he

lemma slope_iff (g h : SL(2,ℤ)) (i : P d) : slope g i=slope h i ↔
    (g 1 0:ZMod i.val)*h 1 1-(g 1 1:ZMod i.val)*h 1 0=0 := by
  unfold slope
  by_cases hg : (g 1 0:ZMod i.val)=0 <;> by_cases hh : (h 1 0:ZMod i.val)=0
  · simp [hg,hh]
  · simp [hg,hh,row_nz g i hg]
  · simp [hg,hh,row_nz h i hh]
  · simp only [hg,hh,if_false,Option.some.injEq,div_eq_div_iff hg hh,sub_eq_zero]
    constructor <;> intro H <;> linear_combination -H

lemma slope_level (hs : Squarefree d) (hd : d%4=1) (g h : Gamma0 32) :
    slope (d:=d) g.val=slope h.val ↔ g.val*h.val⁻¹ ∈ Gamma0 (32*d) := by
  have c (g h : SL(2,ℤ)) : (g*h⁻¹) 1 0=g 1 0*h 1 1-g 1 1*h 1 0 := by
    change (g.val*h⁻¹.val) 1 0=_
    rw [Matrix.mul_apply,Fin.sum_univ_two,SpecialLinearGroup.SL2_inv_expl]
    simp; ring
  have h32 : (32:ℤ)∣(g.val*h.val⁻¹) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    (Gamma0_mem.mp (Subgroup.mul_mem _ g.property (Subgroup.inv_mem _ h.property)))
  have cop : IsCoprime (32:ℤ) (d:ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    change Nat.gcd 32 d=1
    have h2 : Nat.Coprime 2 d := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    simpa using h2.pow_left 5
  rw [Gamma0_mem,ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_mul,Nat.cast_ofNat]
  constructor
  · intro e
    apply cop.mul_dvd h32
    apply int_dvd hs
    intro i
    rw [←ZMod.intCast_zmod_eq_zero_iff_dvd,c]
    push_cast
    exact (slope_iff _ _ i).mp (congrFun e i)
  · intro H
    funext i
    apply (slope_iff _ _ i).mpr
    have hi : (i.val:ℤ)∣(g.val*h.val⁻¹) 1 0 := dvd_trans (by exact_mod_cast Nat.dvd_of_mem_primeFactors i.property : (i.val:ℤ)∣(d:ℤ)) (dvd_trans (dvd_mul_left _ _) H)
    have e := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hi
    rw [c] at e
    push_cast at e
    exact e

end
end TunnellTraceCosets
end

section
/- Transitivity of the unnormalized Petersson integral from level 32d to level 32. -/
namespace TunnellPeterssonTrace
open Complex Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellTraceCosets
open TunnellRankinIntegral MeasureTheory
open UpperHalfPlane hiding I
noncomputable section
variable {d : ℕ}

def cls {L : ℕ} (g : SL(2,ℤ)) : Cosets L := QuotientGroup.mk g⁻¹

lemma cls_eq {L : ℕ} (g h : SL(2,ℤ)) : cls (L:=L) g=cls h ↔ g*h⁻¹ ∈ Gamma0 L := by
  simp only [cls,QuotientGroup.eq,inv_inv]

lemma cls_rep {L : ℕ} (q : Cosets L) : cls (rep q)=q := by
  simp [cls,rep,Quotient.out_eq']

def compose (R : Choices d→Gamma0 32) (w : Cosets 32 × Choices d) : SL(2,ℤ) := (R w.2).val*rep w.1

lemma large_cls (R : Choices d→Gamma0 32) (w : Cosets 32 × Choices d) :
    cls (L:=32) (compose R w)=w.1 := cosetProd_class w.1 (R w.2)

def transitive (hs : Squarefree d) (hd : d%4=1) (R : Choices d→Gamma0 32)
    (hR : ∀ j,slope (R j).val=j) : Cosets 32 × Choices d ≃ Cosets (32*d) :=
  Equiv.ofBijective (fun w => cls (compose R w)) (by
    constructor
    · rintro ⟨q,i⟩ ⟨r,j⟩ H
      have h := (cls_eq _ _).mp H
      have h' := gamma_dvd (dvd_mul_right 32 d) h
      have e := (cls_eq _ _).mpr h'
      rw [large_cls,large_cls] at e
      dsimp only at e
      subst r
      have C : (R i).val*(R j).val⁻¹∈Gamma0 (32*d) := by simpa [compose,mul_assoc] using h
      exact Prod.ext rfl (by simpa only [hR] using (slope_level hs hd (R i) (R j)).mpr C)
    · intro q
      obtain ⟨⟨r,h⟩,he⟩ := (cosetProd_bijective 32).surjective (rep q)
      let j := slope (d:=d) h.val
      refine ⟨(r,j),?_⟩
      rw [←cls_rep q]
      apply (cls_eq _ _).mpr
      rw [←he]
      have H := (slope_level hs hd (R j) h).mp (hR j)
      simpa [compose,cosetProd,mul_assoc] using H)

theorem trace_integral (hs : Squarefree d) (hd : d%4=1) (R : Choices d→Gamma0 32)
    (hR : ∀ j,slope (R j).val=j) (F : ℍ→ℂ)
    (H : ∀ g∈Gamma0 (32*d),∀ z,F (g • z)=F z)
    (hi : ∀ (q : Cosets 32) i, IntegrableOn (fun z => F ((R i).val • (rep q • z))) fdo) :
    TunnellRankinIntegral.petersson (32*d) F=TunnellRankinIntegral.petersson 32 (fun z => ∑ i,F ((R i).val • z)) := by
  classical
  letI : NeZero (32*d) := ⟨by omega⟩
  letI := Fintype.ofFinite (Cosets 32)
  letI := Fintype.ofFinite (Cosets (32*d))
  let E := transitive hs hd R hR
  have HE (w : Cosets 32 × Choices d) z : F (rep (E w) • z)=F (compose R w • z) := by
    have hh : cls (rep (E w))=cls (compose R w) := cls_rep (E w)
    have hh' := (cls_eq _ _).mp hh
    simpa [mul_smul] using H _ hh' (compose R w • z)
  unfold TunnellRankinIntegral.petersson
  rw [←E.tsum_eq (fun q => ∫ z in fdo,F (rep q • z))]
  simp only [tsum_fintype,Fintype.sum_prod_type,HE,compose,mul_smul,
    MeasureTheory.integral_finsetSum _ (fun i _ => hi _ i)]

end
end TunnellPeterssonTrace
end

section
/- Regularity and Petersson evaluation after taking an actual coset trace. -/
namespace TunnellModularTraceRegular
open Complex Finset Matrix MatrixGroups ModularGroup ModularForm CongruenceSubgroup MeasureTheory
open TunnellTraceCosets TunnellPeterssonTrace TunnellRankinIntegral TunnellHalfPairing TunnellLevelPairing
open TunnellShell TunnellFullClassTheta TunnellRankinCotangent
open UpperHalfPlane hiding I
open scoped ModularForm ComplexConjugate
noncomputable section
variable {d : ℕ}

def series (R : Choices d→Gamma0 32) (F : ℍ→ℂ) (z : ℍ) := ∑ i,(F ∣[(2:ℤ)] (R i).val) z

lemma pair_series (R : Choices d→Gamma0 32) (F : ℍ→ℂ) (z : ℍ) :
    pair (series R F) z=∑ i,pair F ((R i).val • z) := by
  calc
    _ = ∑ i,pair (F ∣[(2:ℤ)] (R i).val) z := by
      simp only [pair_eta,series,map_sum,mul_sum]
    _ = _ := sum_congr rfl (fun i _ => (pair_pull (R i).property F z).symm)

def move (R : Choices d→Gamma0 32) (g : Gamma0 32) (i : Choices d) : Choices d := slope ((R i)*g).val

lemma move_slope (hs : Squarefree d) (hd : d%4=1) (R : Choices d→Gamma0 32)
    (hR : ∀ j,slope (R j).val=j) (g h : Gamma0 32) : move R g (slope h.val)=slope (h*g).val := by
  apply (slope_level hs hd _ _).mpr
  have e := (slope_level hs hd (R (slope h.val)) h).mp (hR _)
  simpa [Subgroup.coe_mul,mul_assoc] using e

def perm (hs : Squarefree d) (hd : d%4=1) (R : Choices d→Gamma0 32)
    (hR : ∀ j,slope (R j).val=j) (g : Gamma0 32) : Equiv.Perm (Choices d) where
  toFun := move R g
  invFun := move R g⁻¹
  left_inv i := by change move R g⁻¹ (slope ((R i)*g).val)=_; rw [move_slope hs hd R hR]; simp [hR]
  right_inv i := by change move R g (slope ((R i)*g⁻¹).val)=_; rw [move_slope hs hd R hR]; simp [hR]

lemma sum_invariant (hs : Squarefree d) (hd : d%4=1) (R : Choices d→Gamma0 32)
    (hR : ∀ j,slope (R j).val=j) {F : ℍ→ℂ} (hi : ∀ g∈Gamma0 (32*d), ∀ z, F (g • z)=F z)
    (g : Gamma0 32) (z : ℍ) :
    (∑ i,F ((R i).val • (g.val • z)))=∑ i,F ((R i).val • z) := by
  let E := perm hs hd R hR g
  rw [←Equiv.sum_comp E (fun i => F ((R i).val • z))]
  apply sum_congr rfl
  intro i _
  have e := (slope_level hs hd (R i*g) (R (E i))).mp (hR (E i)).symm
  simpa only [Subgroup.coe_mul,mul_smul,inv_smul_smul] using hi _ e ((R (E i)).val • z)

variable {b : Triple} (hs : Squarefree d) (hn : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))

include hs in
theorem regularity (R : Choices d→Gamma0 32) (hR : ∀ j,slope (R j).val=j) :
    regular (series R (source hn hd hb)) ∧
      TunnellRankinIntegral.petersson 32 (pair (series R (source hn hd hb)))=
      TunnellRankinIntegral.petersson (4*(2*d)*4) (pair (source hn hd hb)) := by
  let F := source hn hd hb
  have hi (q : Cosets 32) (i : Choices d) : IntegrableOn (fun z => pair F ((R i).val • (rep q • z))) fdo := by
    simpa only [mul_smul] using high_integrable hn hd hb ((R i).val*rep q)
  have he : pair (series R F)=fun z=>∑ i,pair F ((R i).val • z) := funext (pair_series R F)
  change regular (series R F) ∧ _=_
  constructor
  · unfold regular
    rw [he]
    refine ⟨?_,?_,?_⟩
    · exact Finset.measurable_fun_sum _ (fun i _ => (high_meas hn hd hb).comp (measurePreserving_smul ((R i).val:GL (Fin 2) ℝ) volume).measurable)
    · exact sum_invariant hs hd R hR (high_invariant hn hd hb)
    · intro q
      exact integrable_finsetSum _ (fun i _ => hi q i)
  · change TunnellRankinIntegral.petersson 32 (pair (series R F))=TunnellRankinIntegral.petersson _ (pair F)
    rw [he,←trace_integral hs hd R hR _ (high_invariant hn hd hb) hi]
    congr 1
    ring

end
end TunnellModularTraceRegular
end

section
/- Composition of independent local slash traces in a fixed order. -/
namespace TunnellOrderedTrace
open MatrixGroups ModularGroup ModularForm Finset
open scoped ModularForm UpperHalfPlane
noncomputable section

def word {n : ℕ} {C : Fin n→Type*} (g : (i : Fin n)→C i→SL(2,ℤ)) (j : ∀ i,C i) :=
  (List.ofFn (fun i => g i (j i))).prod

lemma word_cons {n : ℕ} {C : Fin (n+1)→Type*} (g : (i : Fin (n+1))→C i→SL(2,ℤ))
    (j : C 0) (t : ∀ i : Fin n,C i.succ) :
    word g (Fin.cons j t)=g 0 j*word (fun i => g i.succ) t := by
  simp [word,List.ofFn_succ]

lemma sum_cons {n : ℕ} (C : Fin (n+1)→Type*) [∀ i,Fintype (C i)] {E : Type*} [AddCommMonoid E]
    (f : (∀ i,C i)→E) : ∑ i, f i=∑ x : C 0, ∑ t : ∀ i : Fin n,C i.succ,f (Fin.cons x t) := by
  rw [←(Fin.consEquiv C).sum_comp f,Fintype.sum_prod_type]
  rfl

variable {G : Type*} [AddCommMonoid G]
theorem average {n : ℕ} {C V : Fin n→Type*} [∀ i,Fintype (C i)] [∀ i,Fintype (V i)]
    (g : (i : Fin n)→C i→SL(2,ℤ)) (offset : (i : Fin n)→V i→G) (weight : (i : Fin n)→V i→ℂ)
    (ok : Fin n→G→Prop) (F : G→ℍ→ℂ)
    (step : ∀ i s,ok i s → (∑ j : C i,(F s) ∣[(2:ℤ)] (g i j)) =
      ∑ v : V i, weight i v • F (s+offset i v))
    (stable : ∀ i j, i≠j → ∀ s v,ok i s → ok i (s+offset j v))
    (s : G) (hs : ∀ i, ok i s) :
    (∑ j : ∀ i,C i,(F s) ∣[(2:ℤ)] (word g j)) =
      ∑ v : ∀ i,V i,(∏ i,weight i (v i)) • F (s+∑ i,offset i (v i)) := by
  classical
  induction n generalizing s with
  | zero =>
    simp [word]
  | succ n ih =>
    let gt (i : Fin n) := g i.succ
    have H (v : V 0) :
        (∑ j : ∀ i : Fin n,C i.succ,(F (s+offset 0 v)) ∣[(2:ℤ)] (word gt j))=
          ∑ w : ∀ i : Fin n,V i.succ,(∏ i : Fin n,weight i.succ (w i)) •
            F ((s+offset 0 v)+∑ i : Fin n,offset i.succ (w i)) :=
      ih gt (fun i => offset i.succ) (fun i => weight i.succ) (fun i => ok i.succ)
        (fun i => step i.succ) (fun i j ne => stable i.succ j.succ (by simpa))
        _ (fun i => stable i.succ 0 (Fin.succ_ne_zero i) s v (hs i.succ))
    rw [sum_cons C,sum_cons V]
    simp only [word_cons,SlashAction.slash_mul,Fin.prod_univ_succ,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [sum_comm]
    have at0 (j : ∀ i : Fin n,C i.succ) :
        (∑ h : C 0, ((F s) ∣[(2:ℤ)] g 0 h) ∣[(2:ℤ)] word gt j) =
        ∑ v : V 0, weight 0 v • ((F (s+offset 0 v)) ∣[(2:ℤ)] word gt j) := by
      rw [←SlashAction.sum_slash,step 0 s (hs 0),SlashAction.sum_slash]
      simp only [SL_smul_slash]
    calc
      _ = ∑ j : ∀ i : Fin n,C i.succ, ∑ v : V 0,
            weight 0 v • ((F (s+offset 0 v)) ∣[(2:ℤ)] word gt j) :=
        sum_congr rfl (fun j _ => at0 j)
      _ = _ := ?_
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    rw [←Finset.smul_sum,H]
    simp only [Finset.smul_sum,smul_smul,add_assoc]

end
end TunnellOrderedTrace
end

section
/- Explicit words in S,T whose reductions are the desired Bruhat representatives
at just one prime and the identity at all other relevant primes. -/
namespace TunnellTraceLifts
open Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellTraceCosets TunnellPacketOperators TunnellRamifiedLines
noncomputable section
variable {d : ℕ}
private instance pPrime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩

def step (m j : ℤ) : SL(2,ℤ) := -(weylLift m)*T^(m*j)

lemma step_entries (m j : ℤ) : (step m j).val =
    !![1-m^2, (1-m^2)*(m*j)+m^3-2*m; m, m*(m*j)+1-m^2] := by
  change (-((T^(-m)).val*S.val*(T^(-m)).val*S.val*(T^(-m)).val))*(T^(m*j)).val=_
  rw [coe_T_zpow,coe_T_zpow]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [S,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

def localRep (m : ℤ) {q : ℕ} : Option (ZMod q) → SL(2,ℤ)
  | none => 1
  | some j => step m j.val

def reduction (q : ℕ) : SL(2,ℤ)→*SL(2,ZMod q) := SpecialLinearGroup.map (Int.castRingHom _)

lemma off {p q : ℕ} (m : ℤ) (hm : (m:ZMod p)=0) (j : Option (ZMod q)) :
    reduction p (localRep m j)=1 := by
  cases j with
  | none => exact map_one _
  | some j =>
    apply Subtype.ext
    change (Int.castRingHom (ZMod p)).mapMatrix (step m j.val).val=1
    rw [step_entries]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hm]

lemma supported {m : ℤ} (hm : (32:ℤ)∣m) {q : ℕ} (j : Option (ZMod q)) : localRep m j∈Gamma0 32 := by
  cases j with
  | none => exact Subgroup.one_mem _
  | some j =>
    apply Gamma0_mem.mpr
    change ((step m j.val).val 1 0:ZMod 32)=0
    rw [step_entries]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hm

lemma on {m : ℤ} (i : P d) (hm : (m:ZMod i.val)=1) (j : Option (ZMod i.val)) :
    slope (localRep m j) i=j := by
  cases j with
  | none => simp [localRep,TunnellTraceCosets.slope]
  | some j =>
    unfold localRep TunnellTraceCosets.slope
    change (if ((step m j.val).val 1 0:ZMod i.val)=0 then none else some (((step m j.val).val 1 1:ZMod i.val)/((step m j.val).val 1 0:ZMod i.val)))=_
    rw [step_entries]
    simp [hm]

lemma slope_congr (i : P d) {g h : SL(2,ℤ)} (e : reduction i.val g=reduction i.val h) :
    slope g i=slope h i := by
  have hh (j : Fin 2) := congrArg (fun k : SL(2,ZMod i.val) => k 1 j) e
  change ∀ j : Fin 2, (g 1 j:ZMod i.val)=(h 1 j:ZMod i.val) at hh
  simp [TunnellTraceCosets.slope,hh]

lemma single_prod {G I : Type*} [Monoid G] [DecidableEq I] (f : I→G) (i : I) (l : List I)
    (hd : l.Nodup) (h : ∀ j∈l,j≠i → f j=1) :
    (l.map f).prod=if i∈l then f i else 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h' := ih hd.of_cons (fun j hj => h j (by simp [hj]))
    by_cases e : a=i
    · subst a; simp [h',hd.notMem]
    · simp [h',h a (by simp) e,Ne.symm e]

def primes (d : ℕ) : List (P d) := Finset.univ.sort (·≤·)

def lift (m : P d→ℤ) (r : Choices d) : SL(2,ℤ) :=
  ((primes d).map (fun i => localRep (m i) (r i))).prod

lemma lift_mem (m : P d→ℤ) (hm : ∀ i,(32:ℤ)∣m i) (r : Choices d) : lift m r∈Gamma0 32 := by
  unfold lift
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  exact supported (hm i) _

lemma lift_slope (m : P d→ℤ) (one : ∀ i, (m i:ZMod i.val)=1)
    (zero : ∀ i j : P d,i≠j → (m j:ZMod i.val)=0) (r : Choices d) :
    slope (lift m r)=r := by
  funext i
  apply Eq.trans (slope_congr i (h:=localRep (m i) (r i)) ?_) (on i (one i) _)
  unfold lift
  rw [map_list_prod,List.map_map]
  change ((primes d).map (fun j => reduction i.val (localRep (m j) (r j)))).prod=_
  rw [single_prod (fun j => reduction i.val (localRep (m j) (r j))) i (primes d)
    (Finset.sort_nodup _ _) (fun j _ h => off _ (zero i j (Ne.symm h)) _)]
  simp [primes]

end
end TunnellTraceLifts
end

section
/- Multiplying the independent level-lowering traces along the prime factors of d. -/
namespace TunnellPrimeTrace
open Finset TunnellTraceCosets TunnellTraceLifts TunnellRamifiedLines TunnellOrderedTrace
open MatrixGroups ModularGroup ModularForm
open scoped ModularForm UpperHalfPlane
noncomputable section
variable {d : ℕ}

def order (d : ℕ) : Fin (primes d).length ≃ P d :=
  Equiv.ofBijective (primes d).get ⟨(Finset.sort_nodup _ _).injective_get,fun i =>
    List.mem_iff_get.mp (by simp [primes] : i∈primes d)⟩

def addCoord (i : P d) (v : ZMod i.val × ZMod i.val) : ℤ×ℤ :=
  ((((d/i.val)*v.1.val:ℕ):ℤ),(((d/i.val)*v.2.val:ℕ):ℤ))
def admissible (i : P d) (s : ℤ×ℤ) : Prop := (i.val:ℤ)∣s.1 ∧ (i.val:ℤ)∣s.2

lemma stable (i j : P d) (ne : i≠j) (s : ℤ×ℤ) (v : ZMod j.val × ZMod j.val) (hs : admissible i s) :
    admissible i (s+addCoord j v) := by
  have hi := Nat.prime_of_mem_primeFactors i.property
  have hj := Nat.prime_of_mem_primeFactors j.property
  have hc : i.val.Coprime j.val := (Nat.coprime_primes hi hj).mpr (fun h => ne (Subtype.ext h))
  have H : i.val ∣ d/j.val := Nat.dvd_div_of_mul_dvd (hc.symm.mul_dvd_of_dvd_of_dvd
    (Nat.dvd_of_mem_primeFactors j.property) (Nat.dvd_of_mem_primeFactors i.property))
  exact ⟨dvd_add hs.1 (by dsimp [addCoord]; exact_mod_cast dvd_mul_of_dvd_left H v.1.val),
    dvd_add hs.2 (by dsimp [addCoord]; exact_mod_cast dvd_mul_of_dvd_left H v.2.val)⟩

theorem assemble_average (m : P d→ℤ) (F : (ℤ×ℤ)→ℍ→ℂ)
    (w : (i : P d)→ZMod i.val × ZMod i.val→ℂ)
    (H : ∀ i s,admissible i s → (∑ u : Option (ZMod i.val), F s ∣[(2:ℤ)] localRep (m i) u)=
      ∑ v : ZMod i.val × ZMod i.val,w i v • F (s+addCoord i v)) :
    (∑ u : Choices d,F 0 ∣[(2:ℤ)] lift m u)=
      ∑ v : Packet d,(∏ i,w i (v i)) • F (∑ i,addCoord i (v i)) := by
  classical
  let E := order d
  let C := Equiv.piCongrLeft' (fun i : P d => Option (ZMod i.val)) E.symm
  let V := Equiv.piCongrLeft' (fun i : P d => ZMod i.val × ZMod i.val) E.symm
  let g (i : Fin (primes d).length) := fun u : Option (ZMod (E i).val) => localRep (m (E i)) u
  have word_eq (u : Choices d) : word g (C u)=lift m u := by
    unfold word lift
    change (List.ofFn (fun i : Fin (primes d).length => localRep (m ((primes d).get i)) (u ((primes d).get i)))).prod=_
    exact congrArg List.prod (List.ofFn_getElem_eq_map (primes d) (fun i => localRep (m i) (u i)))
  have HH := average g (fun i => addCoord (E i)) (fun i => w (E i))
    (fun i => admissible (E i)) F (fun i => H (E i))
    (fun i j hij => stable (E i) (E j) (E.injective.ne hij)) 0 (fun i => ⟨dvd_zero _,dvd_zero _⟩)
  calc
    _ = ∑ u : Choices d,F 0 ∣[(2:ℤ)] word g (C u) := by simp only [word_eq]
    _ = _ := C.sum_comp (fun u => F 0 ∣[(2:ℤ)] word g u)
    _ = _ := HH
    _ = ∑ v : Packet d,(∏ i,w (E i) ((V v) i)) • F (0+∑ i,addCoord (E i) ((V v) i)) :=
      (V.sum_comp (fun x => (∏ i,w (E i) (x i)) • F (0+∑ i,addCoord (E i) (x i)))).symm
    _ = _ := by
      apply sum_congr rfl; intro v _
      change (∏ i,w (E i) (v (E i))) • F (0+∑ i,addCoord (E i) (v (E i)))=_
      rw [zero_add,E.prod_comp (fun i => w i (v i)),E.sum_comp (fun i => addCoord i (v i))]

end
end TunnellPrimeTrace
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

end
end SignedSquarePublic
end

section
namespace TunnellPublicRectangle
open Finset Polynomial MeasureTheory MatrixGroups ModularGroup CongruenceSubgroup
open scoped UpperHalfPlane Classical ComplexConjugate
noncomputable section
def R (d a k:ℕ) (b u:ℤ) (z:ℂ) := ∑' x:ℤ×ℤ,
    Complex.exp (2*Real.pi*Complex.I*z*k*((a*x.1+b*x.2:ℤ)^2+(2*(d:ℂ))*((x.2:ℂ)+(a:ℂ)*u/d)^2)/a)
def K (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) (u v:ℤ) (z:ℂ) := R d i.1 1 i.2.1 u z*R d i.2.2.1 4 i.2.2.2 v z
def T (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) (z:ℂ) := ∑' w:ZMod d×ZMod d,
    (∏ p:↥d.primeFactors, (Nat.card {t:ZMod p.val // (i.1:ZMod p.val)*t^2= -4*i.2.2.1 ∧
      (w.1.val:ZMod p.val)=t*w.2.val}:ℂ))*K d i w.1.val w.2.val z
def G (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) := 0 < i.1 ∧ 0 < i.2.2.1 ∧ i.1.Coprime d ∧ i.2.2.1.Coprime d

open TunnellRamifiedLines
open TunnellLineDensity TunnellRectangularClasses TunnellRectangularIdeal

theorem R_eq {d a k:ℕ} [NeZero d] [NeZero a] [NeZero k] (b u:ℤ) (z:ℍ) :
    R d a k b u z=rect d a k b u z := (translated d a k b u z.im_pos).tsum_eq

def rootCount (p a c:ℕ) (x y:ZMod p) :=
  Nat.card {t:ZMod p // (a:ZMod p)*t^2= -4*c ∧ x=t*y}

theorem count_eq {p a c:ℕ} [Fact p.Prime] (ha:(a:ZMod p)≠0) (x y:ZMod p) :
    rootCount p a c x y=density (-(4:ZMod p)*c/a) (x,y) := by
  unfold rootCount density RootsAt
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  apply and_congr_left; intro _
  rw [eq_div_iff ha,mul_comm (t^2)]

theorem reduce_val {d:ℕ} [NeZero d] (i:P d) (w:ZMod d) :
    (w.val:ZMod i.val)=reduce i w := by
  have e := congrArg (reduce i) (ZMod.natCast_zmod_val w)
  simpa only [map_natCast] using e

end
end TunnellPublicRectangle
end

section
/- The complete one-prime level trace of a four-dimensional rectangular theta
packet, written with its integral modular-group representatives. -/
namespace TunnellRectangularLocalTrace
open Complex Finset TunnellPacketComplement TunnellLocalizedPacket TunnellTraceLifts
open TunnellPacketOperators TunnellRamifiedPlane TunnellRamifiedWeyl ModularGroup MatrixGroups ModularForm
open UpperHalfPlane hiding I
open scoped ModularForm
noncomputable section
variable {A B k l p : ℕ} [NeZero A] [NeZero B] [NeZero k] [NeZero l] [Fact p.Prime]

lemma neg_slash (g : SL(2,ℤ)) (F : ℍ→ℂ) : F ∣[(2:ℤ)] (-g)= F ∣[(2:ℤ)] g := by
  funext z
  rw [SL_slash_apply,SL_slash_apply,SL_neg_smul]
  rw [ModularGroup.denom_apply (-g) z,ModularGroup.denom_apply g z]
  have h (i j : Fin 2) : ((-g) i j:ℤ) = -(g i j) := rfl
  simp only [h,Int.cast_neg,show (-(g 1 0:ℂ))*(z:ℂ)+ -(g 1 1:ℂ) = -((g 1 0:ℂ)*z+g 1 1) by ring,
    zpow_neg,zpow_ofNat,neg_sq]

variable (hc : p.Coprime (2*k)) (hd : p.Coprime (2*l)) (eA : Even A) (eB : Even B)
    (m : ℤ) (hm : (m:ZMod p)=1)
    (hA : 2*(A:ℤ)∣m) (hB : 2*(B:ℤ)∣m) (hk : 4*(k:ℤ)∣m) (hl : 4*(l:ℤ)∣m)
    {a t : ZMod p} (ha : (k:ZMod p)=a) (hb : (l:ZMod p)= -a*t)
    (hp : p≠2) (ha0 : a≠0) (ht : t≠0)

include hc hd eA eB m hm hA hB hk hl ha hb hp ha0 ht in
lemma actual_step (j : ZMod p) (x : (Box A (2*k) B (2*l))) (v : (ZMod p × ZMod p)) (z : ℍ) :
    ((family hc hd x v) ∣[(2:ℤ)] step m j.val) z=
      weyl a t (TunnellRamifiedWeyl.translate a t j (fun u => family hc hd x u z)) v := by
  let F := family (A:=A) (B:=B) hc hd
  have hW : Law F (weylLift m) (plane ((gauss a t/(p:ℂ)^2) • W a t (-1))) := by
    intro x u z
    rw [localized_weyl hc hd eA eB m hm hA hB hk hl ha hb x u z,weyl_kernel hp ha0 ht]
    rfl
  have hT := law_T hc hd eA eB (m*j.val) (dvd_mul_of_dvd_left hA _) (dvd_mul_of_dvd_left hB _)
    (dvd_mul_of_dvd_left hk _) (dvd_mul_of_dvd_left hl _) ha hb
  have hW' : Law F (-(weylLift m)) (plane ((gauss a t/(p:ℂ)^2) • W a t (-1))) := by
    intro x y z; rw [neg_slash]; exact hW x y z
  have H := law_mul hW' hT x v z
  rw [step,H,weyl_kernel hp ha0 ht]
  simp only [Int.cast_mul,Int.cast_natCast,hm,one_mul,ZMod.natCast_zmod_val]
  rfl

include hc hd eA eB m hm hA hB hk hl ha hb hp ha0 ht in
theorem local_trace (x : (Box A (2*k) B (2*l))) (z : ℍ) :
    (∑ j : Option (ZMod p), ((family hc hd x 0) ∣[(2:ℤ)] localRep m j) z) =
      trace a t (fun u => family hc hd x u z) := by
  rw [Fintype.sum_option]
  change ((family hc hd x 0) ∣[(2:ℤ)] (1:SL(2,ℤ))) z+
    (∑ i : ZMod p, ((family hc hd x 0) ∣[(2:ℤ)] step m i.val) z)=_
  simp only [SlashAction.slash_one,actual_step hc hd eA eB m hm hA hB hk hl ha hb hp ha0 ht]
  exact weyl_trace hp ha0 ht (fun u => family hc hd x u z)

end
end TunnellRectangularLocalTrace
end

section
/- Prime-supported slash traces in the integral residue coordinates of two
quadratic ideal bases. -/
namespace TunnellRectangleRows
open Complex Finset TunnellRankOnePacket TunnellPacketComplement TunnellSplitIndex TunnellPacketCRT
open TunnellLocalizedPacket TunnellRectangularLocalTrace TunnellTraceLifts TunnellRectangularIdeal
open TunnellRamifiedWeyl TunnellRamifiedPlane TunnellLineDensity ModularGroup MatrixGroups ModularForm
open UpperHalfPlane hiding I
open scoped ModularForm
noncomputable section

def raw (D : ℕ) [NeZero D] (r : ℤ) (z : ℍ) : ℂ := packet D (r:ZMod D) z

lemma raw_congr {D H : ℕ} [NeZero D] [NeZero H] (e : D=H) {r s : ℤ} (h : r=s) (z : ℍ) :
    raw D r z=raw H s z := by subst H; subst s; rfl

lemma family_raw {A M B N p : ℕ} [NeZero A] [NeZero M] [NeZero B] [NeZero N] [Fact p.Prime]
    (hc : p.Coprime M) (hd : p.Coprime N) (r s t w : ℤ) (v : ZMod p×ZMod p) (z : ℍ) :
    family hc hd ((r:ZMod A),(s:ZMod M),(t:ZMod B),(w:ZMod N)) v z =
    (raw A r z*raw (p*M) (M*(v.1.val:ℤ)+p*s) z)*
      (raw B t z*raw (p*N) (N*(v.2.val:ℤ)+p*w) z) := by
  rw [family,TunnellRectangularPacket.theta,Fin.prod_univ_four]
  simp only [pack₀,pack₁,pack₂,pack₃,dims₀,dims₁,dims₂,dims₃]
  have h (M : ℕ) (hm : p.Coprime M) (x : ZMod p) (y : ℤ) :
      merge hm (x,(y:ZMod M))=(((M:ℤ)*x.val+p*y:ℤ):ZMod (p*M)) := by
    simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using merge_lifts hm (x.val:ℤ) y
  change packet A _ (z:ℂ)*packet (p*M) _ (z:ℂ)*packet B _ (z:ℂ)*packet (p*N) _ (z:ℂ)=_
  rw [h _ hc,h _ hd]
  unfold raw
  ring

def row (d a κ : ℕ) [NeZero d] [NeZero a] [NeZero κ] (b i s : ℤ) (z : ℍ) :=
  raw (2*κ*a) (2*κ*b*i) z*raw (2*κ*a*(2*d)) (4*κ*d*i+4*κ*a*s) z

lemma rect_sum {d a κ : ℕ} [NeZero d] [NeZero a] [NeZero κ] (b s : ℤ) (z : ℍ) :
    rect d a κ b s z=∑ i : ZMod a, row d a κ b i.val s z := by
  unfold rect row raw
  apply sum_congr rfl
  intro i _
  congr 2
  ring_nf

variable {p e a c : ℕ} [Fact p.Prime] [NeZero e] [NeZero a] [NeZero c]

def rawOrigin (b i h f j k : ℤ) : Box ((2*1*a)) (2*((2*a*e))) ((2*4*c)) (2*((8*c*e))) :=
  ((2*b*i:ℤ),(4*e*i+4*a*h:ℤ),(8*f*j:ℤ),(16*e*j+16*c*k:ℤ))

lemma rows (hc : p.Coprime (2*((2*a*e)))) (hd : p.Coprime (2*((8*c*e)))) (b i h f j k : ℤ) (v : (ZMod p × ZMod p)) (z : ℍ) :
    family hc hd (rawOrigin (e:=e) (a:=a) (c:=c) b i h f j k) v z =
      row (p*e) a 1 b i (p*h+e*v.1.val) z * row (p*e) c 4 f j (p*k+e*v.2.val) z := by
  rw [rawOrigin,family_raw]
  unfold row
  congr 1 <;> congr 1 <;> apply raw_congr <;> push_cast <;> ring

end
end TunnellRectangleRows
end

section
/- A single prime trace of the product of two arbitrary translated quadratic
ideal theta series, in the same coordinates as the geometric line-family trace. -/
namespace TunnellRectangleTrace
open Complex Finset TunnellRectangleRows TunnellRectangularIdeal TunnellRectangularLocalTrace
open TunnellLocalizedPacket TunnellTraceLifts TunnellLineDensity ModularForm ModularGroup MatrixGroups
open UpperHalfPlane hiding I
open scoped ModularForm
noncomputable section

def piece (d a c : ℕ) [NeZero d] [NeZero a] [NeZero c] (b f : ℤ) (s : ℤ×ℤ) (z : ℍ) :=
  rect d a 1 b s.1 z*rect d c 4 f s.2 z

def oneRow (d a c : ℕ) [NeZero d] [NeZero a] [NeZero c] (b f i j : ℤ) (s : ℤ×ℤ) (z : ℍ) :=
  row d a 1 b i s.1 z*row d c 4 f j s.2 z

lemma piece_rows (d a c : ℕ) [NeZero d] [NeZero a] [NeZero c] (b f : ℤ) (s : ℤ×ℤ) :
    piece d a c b f s=∑ q : ZMod a×ZMod c,oneRow d a c b f q.1.val q.2.val s := by
  funext z
  simp only [piece,rect_sum,oneRow,Finset.sum_apply,Fintype.sum_prod_type,sum_mul,mul_sum]
  rw [sum_comm]

variable {p e a c : ℕ} [Fact p.Prime] [NeZero e] [NeZero a] [NeZero c]
def shift (e : ℕ) (v : ZMod p×ZMod p) : ℤ×ℤ := (e*v.1.val,e*v.2.val)

variable (hc : p.Coprime (2*(2*a*e))) (hd : p.Coprime (2*(8*c*e))) (m : ℤ) (hm : (m:ZMod p)=1)
    (hA : 2*((2*1*a:ℕ):ℤ)∣m) (hB : 2*((2*4*c:ℕ):ℤ)∣m) (hk : 4*((2*a*e:ℕ):ℤ)∣m) (hl : 4*((8*c*e:ℕ):ℤ)∣m)
    {α t : ZMod p} (ha : ((2*a*e:ℕ):ZMod p)=α) (hb : ((8*c*e:ℕ):ZMod p)= -α*t)
    (hp : p≠2) (hα : α≠0) (ht : t≠0)

include hc hd m hm hA hB hk hl ha hb hp hα ht in
lemma row_trace (b f i j : ℤ) (s : ℤ×ℤ) (hx : (p:ℤ)∣s.1) (hy : (p:ℤ)∣s.2) :
    (∑ ξ : Option (ZMod p), (oneRow (p*e) a c b f i j s) ∣[(2:ℤ)] localRep m ξ) =
      ∑ u : (ZMod p × ZMod p),(density t u:ℂ) • oneRow (p*e) a c b f i j (s+shift e u) := by
  let h : ℤ := Classical.choose hx
  let k : ℤ := Classical.choose hy
  have hh : s.1=(p:ℤ)*h := Classical.choose_spec hx
  have hk' : s.2=(p:ℤ)*k := Classical.choose_spec hy
  let x := rawOrigin (e:=e) (a:=a) (c:=c) b i h f j k
  have P (u : (ZMod p × ZMod p)) : family hc hd x u=oneRow (p*e) a c b f i j (s+shift e u) := by
    funext z
    simpa only [x,oneRow,shift,Prod.fst_add,Prod.snd_add,hh,hk',Int.natCast_mul] using rows hc hd b i h f j k u z
  have z0 : shift e (0:(ZMod p × ZMod p))=(0:ℤ×ℤ) := by ext <;> simp [shift]
  have Z : family hc hd x 0=oneRow (p*e) a c b f i j s := by simpa only [z0,add_zero] using P 0
  rw [←Z]
  funext z
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [local_trace hc hd (((even_two.mul_right _).mul_right a)) (((even_two.mul_right _).mul_right c)) m hm hA hB hk hl ha hb hp hα ht,
    roots_sum hp hα ht]
  simp only [P]

include hc hd m hm hA hB hk hl ha hb hp hα ht in
theorem piece_trace (b f : ℤ) (s : ℤ×ℤ) (hx : (p:ℤ)∣s.1) (hy : (p:ℤ)∣s.2) :
    (∑ ξ : Option (ZMod p), (piece (p*e) a c b f s) ∣[(2:ℤ)] localRep m ξ) =
      ∑ u : (ZMod p × ZMod p),(density t u:ℂ) • piece (p*e) a c b f (s+shift e u) := by
  simp only [piece_rows,SlashAction.sum_slash,Finset.smul_sum]
  rw [sum_comm]
  simp_rw [row_trace hc hd m hm hA hB hk hl ha hb hp hα ht _ _ _ _ s hx hy]
  rw [sum_comm]

lemma rect_period {d a κ : ℕ} [NeZero d] [NeZero a] [NeZero κ] (b : ℤ) {r s : ℤ}
    (h : (r:ZMod d)=(s:ZMod d)) (z : ℂ) : rect d a κ b r z=rect d a κ b s z := by
  obtain ⟨j,hj⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub r s d).mp h
  unfold rect
  apply sum_congr rfl
  intro i _
  apply congrArg (fun y : ZMod (2*κ*a*(2*d)) =>
    TunnellRankOnePacket.packet (2*κ*a) ((2*(κ:ℤ)*b*i.val:ℤ):ZMod (2*κ*a)) z *
      TunnellRankOnePacket.packet (2*κ*a*(2*d)) y z)
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
  refine ⟨j,?_⟩
  push_cast
  linear_combination 4*(κ:ℤ)*a*hj

end
end TunnellRectangleTrace
end

section
namespace TunnellPublicRectangle
open TunnellRamifiedLines TunnellRectangleTrace TunnellPrimeTrace TunnellDensityTrace TunnellLineDensity
open TunnellRectangularClasses TunnellRectangularIdeal Finset
open scoped UpperHalfPlane Classical
noncomputable section
private instance prime {d:ℕ} (i:P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩

theorem public_trace {d a c:ℕ} [NeZero d] [NeZero a] [NeZero c] (hs : Squarefree d)
    (ha : a.Coprime d) (b f:ℤ) (z:ℍ) :
    T d (a,b,c,f) z=∑ x : Packet d,
      (∏ i:P d,(density (-(4:ZMod i.val)*c/a) (x i):ℂ))*
        piece d a c b f (∑ i:P d,addCoord i (x i)) z := by
  classical
  let k := complementaryUnit hs
  let e := shifts hs k
  let t (i:P d) := -(4:ZMod i.val)*c/a
  have hu (i:P d) : (a:ZMod i.val)≠0 := by
    intro h
    have p := (ZMod.natCast_eq_zero_iff a i.val).mp h
    exact (prime i).out.not_dvd_one (ha ▸ Nat.dvd_gcd p (Nat.dvd_of_mem_primeFactors i.property))
  let F (w:ZMod d×ZMod d) := K d (a,b,c,f) w.1.val w.2.val z
  have H : T d (a,b,c,f) z=∑ w:ZMod d×ZMod d,
      (∏ i:P d,(density (t i) (reduce i w.1,reduce i w.2):ℂ))*F w := by
    unfold T
    rw [tsum_fintype]
    apply sum_congr rfl; intro w _
    apply congrArg (·*F w); apply prod_congr rfl; intro i _
    apply congrArg (fun k:ℕ => (k:ℂ))
    change rootCount i.val a c (w.1.val:ZMod i.val) (w.2.val:ZMod i.val)=_
    rw [count_eq (hu i),reduce_val,reduce_val]
  rw [H,←e.sum_comp (fun w => (∏ i:P d,(density (t i) (reduce i w.1,reduce i w.2):ℂ))*F w)]
  apply sum_congr rfl; intro x _
  congr 1
  · apply prod_congr rfl; intro i _
    change (density (t i) (reduce i ((shifts hs k) x).1,reduce i ((shifts hs k) x).2):ℂ)=_
    rw [shifts_apply]; exact congrArg (fun n:ℕ => (n:ℂ)) (scale (t i) (k i:ZMod i.val) (Units.ne_zero (k i)) (x i))
  · change R d a 1 b ((shifts hs (complementaryUnit hs) x).1.val) z*
      R d c 4 f ((shifts hs (complementaryUnit hs) x).2.val) z=_
    rw [R_eq,R_eq,shifts_eq]
    unfold piece
    congr 1 <;> apply rect_period
    all_goals
      simp [addCoord,assemble,Prod.fst_sum,Prod.snd_sum] <;> simp only [←Int.natCast_ediv,Int.cast_natCast]

end
end TunnellPublicRectangle
end

section
/- The geometric rectangular theta trace is precisely the modular-group trace
of each class-pair theta product. -/
namespace TunnellTraceIdentification
open Complex Finset TunnellRectangleTrace TunnellPrimeTrace
open TunnellDensityTrace TunnellRamifiedLines TunnellTraceCosets TunnellTraceLifts TunnellLineDensity
open ModularGroup MatrixGroups ModularForm
open UpperHalfPlane hiding I
open scoped ModularForm
noncomputable section
variable {d : ℕ} [NeZero d]

lemma piece_modulus {n d a c : ℕ} [NeZero n] [NeZero d] [NeZero a] [NeZero c]
    (e : n=d) (b f : ℤ) : piece n a c b f=piece d a c b f := by subst d; rfl

lemma shift_matches (i : P d) (v : ZMod i.val×ZMod i.val) : shift (d/i.val) v=addCoord i v := by
  ext <;> simp only [shift,addCoord,Nat.cast_mul]

end
end TunnellTraceIdentification
end

section
/- Local density traces for arbitrary positive rectangular coefficients. -/
namespace TunnellRawPrimeTrace
open Complex Finset TunnellTraceIdentification TunnellRectangleTrace TunnellPrimeTrace TunnellDensityTrace
open TunnellRamifiedLines TunnellTraceCosets TunnellTraceLifts TunnellLineDensity
open ModularGroup MatrixGroups ModularForm
open scoped UpperHalfPlane ModularForm
noncomputable section
variable {d a c : ℕ} [NeZero d] [NeZero a] [NeZero c]
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩

lemma unit_at {a : ℕ} (h : a.Coprime d) (i : P d) : (a:ZMod i.val)≠0 :=
  isUnit_iff_ne_zero.mp ((ZMod.isUnit_iff_coprime _ _).mpr (h.of_dvd_right (Nat.dvd_of_mem_primeFactors i.property)))

set_option maxHeartbeats 280000 in
theorem factor (hs : Squarefree d) (hd : d%4=1) (b f : ℤ) (hCa : a.Coprime d) (hCc : c.Coprime d)
    (i : P d) (m : ℤ) (hm : (m:ZMod i.val)=1)
    (hA : 32*(d/i.val)*a ∣ m.natAbs) (hB : 32*(d/i.val)*c ∣ m.natAbs)
    (s : ℤ×ℤ) (hS : TunnellPrimeTrace.admissible i s) :
    (∑ j : Option (ZMod i.val), piece d a c b f s ∣[(2:ℤ)] localRep m j)=
      ∑ v : ZMod i.val × ZMod i.val,(density (-(4:ZMod i.val)*c/a) v:ℂ) •
        piece d a c b f (s+addCoord i v) := by
  let e := d/i.val
  have de : i.val*e=d := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors i.property)
  letI : NeZero e := ⟨by intro h; rw [h,mul_zero] at de; exact NeZero.ne d de.symm⟩
  have hp := (prime i).out
  have hp2 : i.val≠2 := by intro eq; have h := Nat.dvd_of_mem_primeFactors i.property; rw [eq] at h; omega
  have h2 : (2:ZMod i.val)≠0 := by
    change ¬ ((2:ℕ):ZMod i.val)=0
    rw [ZMod.natCast_eq_zero_iff]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have h8 : (8:ZMod i.val)≠0 := by rw [show (8:ZMod i.val)=2^3 by norm_num]; exact pow_ne_zero _ h2
  have he : (e:ZMod i.val)≠0 := by simpa [complementaryUnit,e] using Units.ne_zero (complementaryUnit hs i)
  let α : ZMod i.val := 2*a*e
  let t : ZMod i.val := -(4:ZMod i.val)*c/a
  have hu := unit_at hCa i
  have hv := unit_at hCc i
  have hα : α≠0 := mul_ne_zero (mul_ne_zero h2 hu) he
  have hl : (8:ZMod i.val)*c*e≠0 := mul_ne_zero (mul_ne_zero h8 hv) he
  have hCM : i.val.Coprime (2*(2*a*e)) := ((ZMod.isUnit_iff_coprime _ _).mp
      (isUnit_iff_ne_zero.mpr (by push_cast; exact mul_ne_zero h2 hα))).symm
  have hCN : i.val.Coprime (2*(8*c*e)) := ((ZMod.isUnit_iff_coprime _ _).mp
      (isUnit_iff_ne_zero.mpr (by push_cast; exact mul_ne_zero h2 hl))).symm
  have hlt : (8:ZMod i.val)*c*e= -α*t := by
    dsimp [α,t]
    field_simp [hu]
    <;> ring
  have ht : t≠0 := by intro h; rw [h,mul_zero] at hlt; exact hl hlt
  have H₁ : (32:ℤ)*e*a ∣ m := by exact_mod_cast Int.natCast_dvd.mpr hA
  have H₂ : (32:ℤ)*e*c ∣ m := by exact_mod_cast Int.natCast_dvd.mpr hB
  have H := piece_trace (a:=a) (c:=c) (e:=e) (p:=i.val) (α:=α) (t:=t) hCM hCN m hm (by push_cast; exact dvd_trans (show 2*(2*1*(a:ℤ))∣32*e*a from ⟨8*e,by ring⟩) H₁)
    (by push_cast; exact dvd_trans (show 2*(2*4*(c:ℤ))∣32*e*c from ⟨2*e,by ring⟩) H₂)
    (by push_cast; exact dvd_trans (show 4*(2*(a:ℤ)*e)∣32*e*a from ⟨4,by ring⟩) H₁)
    (by push_cast; exact dvd_trans (show 4*(8*(c:ℤ)*e)∣32*e*c from ⟨1,by ring⟩) H₂)
    (by push_cast; rfl : ((2*a*e:ℕ):ZMod i.val)=α) (by push_cast; exact hlt) hp2 hα ht b f s hS.1 hS.2
  rw [piece_modulus (a:=a) (c:=c) de b f] at H
  simpa only [e,t,shift_matches i] using H

theorem full (hs : Squarefree d) (hd : d%4=1) (b f : ℤ) (hCa : a.Coprime d) (hCc : c.Coprime d)
    (m : P d→ℤ) (hm : ∀ i,(m i:ZMod i.val)=1)
    (hA : ∀ i,32*(d/i.val)*a∣(m i).natAbs) (hB : ∀ i,32*(d/i.val)*c∣(m i).natAbs) (z : ℍ) :
    (∑ j : Choices d,(piece d a c b f 0 ∣[(2:ℤ)] lift m j) z)=
      ∑ u : Packet d,(∏ i : P d,(density (-(4:ZMod i.val)*c/a) (u i):ℂ)) *
        piece d a c b f (∑ i,addCoord i (u i)) z := by
  have H := assemble_average m (piece d a c b f) (fun i v => (density (-(4:ZMod i.val)*c/a) v:ℂ))
    (fun i s h => factor hs hd b f hCa hCc i (m i) (hm i) (hA i) (hB i) s h)
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun H z

end
end TunnellRawPrimeTrace
end

section
/- One prime-supported integer translation for all the finitely many ideal bases. -/
namespace TunnellUniformTranslation
open Finset TunnellRamifiedLines
noncomputable section
variable {d : ℕ}
private instance pPrime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩

theorem exists_translation (hs : Squarefree d) (hd : d%4=1) {α : Type*} [Fintype α]
    (a : α→ℕ) (ha : ∀ (i : P d) u,i.val.Coprime (a u)) :
    ∃ m : P d→ℤ, (∀ i,(m i:ZMod i.val)=1) ∧ (∀ i j : P d,i≠j → (m j:ZMod i.val)=0) ∧
      (∀ i,(32:ℤ)∣m i) ∧ (∀ i u,(32*(d/i.val)*(a u):ℕ)∣(m i).natAbs) := by
  classical
  let C (i : P d) := 32*(d/i.val)*∏ u,a u
  have cop (i : P d) : (C i).Coprime i.val := by
    have dvd := Nat.dvd_of_mem_primeFactors i.property
    have h2 : (2:ℕ).Coprime i.val := Nat.prime_two.coprime_iff_not_dvd.mpr (by intro h; have H := dvd_trans h dvd; omega)
    have h32 : (32:ℕ).Coprime i.val := by simpa using h2.pow_left 5
    have hdiv : (d/i.val).Coprime i.val := by
      simpa [Nat.gcd_eq_right dvd] using Nat.coprime_div_gcd_of_squarefree (n:=i.val) hs (pPrime i).out.ne_zero
    exact (h32.mul_left hdiv).mul_left (Nat.Coprime.prod_left fun u _ => (ha i u).symm)
  let b (i : P d) := (((ZMod.unitOfCoprime (C i) (cop i))⁻¹: (ZMod i.val)ˣ):ZMod i.val).val
  let m (i : P d) : ℕ := C i*b i
  refine ⟨fun i => (m i:ℤ),?_,?_,?_,?_⟩
  · intro i
    change (((m i:ℕ):ℤ):ZMod i.val)=1
    rw [Int.cast_natCast]
    simp only [m,b,Nat.cast_mul,ZMod.natCast_zmod_val]
    rw [←ZMod.coe_unitOfCoprime (C i) (cop i),Units.mul_inv]
  · intro i j hij
    have dvd := Nat.dvd_of_mem_primeFactors j.property
    have hi : i.val∣d/j.val := by
      have hh := dvd_trans (Nat.dvd_of_mem_primeFactors i.property) (dvd_of_eq (Nat.div_mul_cancel dvd).symm)
      apply ((pPrime i).out.dvd_mul.mp hh).resolve_right
      intro eq
      exact hij (Subtype.ext ((Nat.prime_dvd_prime_iff_eq (pPrime i).out (pPrime j).out).mp eq))
    change (((m j:ℕ):ℤ):ZMod i.val)=0
    rw [Int.cast_natCast]
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    exact dvd_trans hi (dvd_trans (dvd_mul_left _ _) (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _)))
  · intro i
    change (32:ℤ)∣((m i:ℕ):ℤ)
    exact_mod_cast (dvd_trans (dvd_mul_right 32 _) (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _)) : 32 ∣ m i)
  · intro i u
    change 32*(d/i.val)*(a u) ∣ m i
    apply dvd_trans _ (dvd_mul_right (C i) (b i))
    exact Nat.mul_dvd_mul_left _ (Finset.dvd_prod_of_mem a (mem_univ u))

end
end TunnellUniformTranslation
end

section
/- Uniform conjugation and level lowering of a finite family of binary theta rectangles. -/
namespace TunnellRawTraceBridge
open Finset MatrixGroups CongruenceSubgroup ModularForm
open TunnellLevelPairing TunnellModularTraceRegular TunnellUniformTranslation TunnellRawPrimeTrace
open TunnellTraceLifts TunnellRamifiedLines TunnellTraceCosets TunnellPrimeTrace TunnellLineDensity
open TunnellPublicRectangle TunnellRectangleTrace TunnellHalfPairing TunnellRankinIntegral
open TunnellRankinCotangent SignedSquarePublic
open scoped ModularForm UpperHalfPlane Classical
noncomputable section

abbrev Form := ℕ×ℤ×ℕ×ℤ
def base (d : ℕ) (i : Form) (z : ℍ) := K d i 0 0 z
def sourceTheta (d : ℕ) (z : ℍ) := theta d z*theta d (4*(z:ℂ))

lemma raw_zero {d : ℕ} [NeZero d] (i : Form) [NeZero i.1] [NeZero i.2.2.1] :
    base d i=piece d i.1 i.2.2.1 i.2.1 i.2.2.2 0 := by
  funext z; simp only [base,K,R_eq,piece,Prod.fst_zero,Prod.snd_zero]

lemma theta_source {d : ℕ} {v : TunnellShell.Triple} (hn : Squarefree (2*d)) (hd : d%4=1)
    (hv : v∈TunnellShell.shell (2*d)) : sourceTheta d=source hn hd hv := by
  funext z
  have E := theta_eq hn hd hv (multiple 4 z)
  change theta d (4*(z:ℂ))=TunnellFullClassTheta.full hn (by omega) hv (multiple 4 z) at E
  rw [sourceTheta,theta_eq hn hd hv z,E]; rfl

theorem lower {d : ℕ} [NeZero d] (hs : Squarefree d) (hd : d%4=1) {n : ℕ} (D : Fin n→Form)
    (good : ∀ i,G d (D i)) (Hbase : ∀ z : ℍ,sourceTheta d z=∑ i,base d (D i) z)
    (Htrace : ∀ i (z : ℍ),
      let j := D i
      letI : NeZero j.1 := ⟨(good i).1.ne'⟩
      letI : NeZero j.2.2.1 := ⟨(good i).2.1.ne'⟩
      T d j z=∑ u : Packet d,(∏ p : P d,(density (-(4:ZMod p.val)*j.2.2.1/j.1) (u p):ℂ)) *
        piece d j.1 j.2.2.1 j.2.1 j.2.2.2 (∑ p,addCoord p (u p)) z) :
    let F := fun z : ℍ => ∑ i,T d (D i) z
    regular F ∧ TunnellRankinIntegral.petersson 32 (pair F)=TunnellRankinIntegral.petersson (32*d) (pair (sourceTheta d)) := by
  have hn : Squarefree (2*d) := (Nat.squarefree_mul (Nat.odd_iff.mpr (by omega) : Odd d).coprime_two_left).mpr ⟨Nat.prime_two.squarefree,hs⟩
  obtain ⟨v,hv⟩ := TunnellThreeSquares.shell_nonempty d hd
  let lead (x : Fin n×Bool) := if x.2 then (D x.1).2.2.1 else (D x.1).1
  have hcop (p : P d) (x : Fin n×Bool) : p.val.Coprime (lead x) := by
    have H := good x.1
    unfold lead
    split <;> first | exact (H.2.2.1.of_dvd_right (Nat.dvd_of_mem_primeFactors p.property)).symm
                     | exact (H.2.2.2.of_dvd_right (Nat.dvd_of_mem_primeFactors p.property)).symm
  obtain ⟨m,hm,hzero,h32,hwidth⟩ := exists_translation hs hd lead hcop
  let R (j : Choices d) : Gamma0 32 := ⟨lift m j,lift_mem m h32 j⟩
  have hR (j : Choices d) : TunnellTraceCosets.slope (R j).val=j := lift_slope m hm hzero j
  have hQ := theta_source hn hd hv
  have B : source hn hd hv=∑ i,base d (D i) := by funext z; rw [←hQ,Finset.sum_apply,Hbase]
  have Tr : series R (source hn hd hv)=fun z : ℍ => ∑ i,T d (D i) z := by
    funext z
    rw [B,series]
    simp only [SlashAction.sum_slash,Finset.sum_apply]
    rw [sum_comm]
    apply sum_congr rfl; intro i _
    let j := D i
    letI : NeZero j.1 := ⟨(good i).1.ne'⟩
    letI : NeZero j.2.2.1 := ⟨(good i).2.1.ne'⟩
    change (∑ q : Choices d,(base d j ∣[(2:ℤ)] lift m q) z)=_
    rw [raw_zero,Htrace i z]
    exact TunnellRawPrimeTrace.full hs hd j.2.1 j.2.2.2 (good i).2.2.1 (good i).2.2.2 m hm
      (fun p => by simpa [lead] using hwidth p (i,false)) (fun p => by simpa [lead] using hwidth p (i,true)) z
  have H := regularity hs hn hd hv R hR
  rw [Tr] at H
  refine ⟨H.1,?_⟩
  rw [H.2,hQ]
  congr 1
  ring

end
end TunnellRawTraceBridge
end

section
/- The modular trace of each finite rectangle presentation realizes its level-32 moment. -/
open Finset TunnellRawTraceBridge TunnellPublicRectangle TunnellHalfPairing
open scoped UpperHalfPlane
noncomputable section

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1.H2 := by
  change ∀ d : ℕ, Squarefree d → d%4=1 → ∀ n (D : Fin n→Form),
    (∀ i,G d (D i)) → (∀ z : ℍ,sourceTheta d z=∑ i,base d (D i) z) →
    let F := fun z : ℍ => ∑ i,T d (D i) z
    regular F ∧ TunnellRankinIntegral.petersson 32 (pair F)=TunnellRankinIntegral.petersson (32*d) (pair (sourceTheta d))
  intro d hs hd n D good hbase
  letI : NeZero d := ⟨by omega⟩
  apply lower hs hd D good hbase
  intro i z
  let j := D i
  letI : NeZero j.1 := ⟨(good i).1.ne'⟩
  letI : NeZero j.2.2.1 := ⟨(good i).2.1.ne'⟩
  exact public_trace (d:=d) (a:=j.1) (c:=j.2.2.1) hs (good i).2.2.1 j.2.1 j.2.2.2 z

end

end
