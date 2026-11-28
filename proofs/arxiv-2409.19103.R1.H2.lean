import OMAReductions.R_arxiv_2409_19103_R1
import Mathlib
/- Adapted from OpenAI, openai/math, commit 3344da59991ed94f9ba711217b29c1d760badfa6,
Apache License 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modified for the OMA definitions, unrestricted removability and Lean 4.33.1. -/
noncomputable section
open Set Filter Function Classical Asymptotics Bornology
open scoped Topology OnePoint
namespace OMA.S_arxiv_2409_19103
@[simp] theorem finiteCoord_coe (z : ℂ) : finiteCoord (z : Sphere) = z := rfl
@[simp] theorem sphereInv_infty : sphereInv ∞ = ((0 : ℂ) : Sphere) := rfl

theorem IsConformalEquivalence.bijOn
    {f : Sphere → Sphere} {U V : Set Sphere} (hf : IsConformalEquivalence f U V) :
    BijOn f U V := by
  obtain ⟨_, hmap, g, _, hgmap, hleft, hright⟩ := hf
  refine ⟨hmap, ?_, ?_⟩
  · intro x hx y hy hxy
    calc
      x = g (f x) := (hleft x hx).symm
      _ = g (f y) := congrArg g hxy
      _ = y := hleft y hy
  · intro y hy
    exact ⟨g y, hgmap hy, hright y hy⟩

namespace CannonMobius
abbrev Sphere := OnePoint ℂ
end CannonMobius

namespace CannonMobius
def coordinate (p : Sphere) : ℂ := p.elim 0 id
end CannonMobius

namespace CannonMobius
lemma coe_coordinate {p : Sphere} (hp : p ≠ ∞) : (coordinate p:Sphere)=p := by
  induction p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z => rfl
end CannonMobius

namespace CannonMobius
def inv (p : Sphere) : Sphere :=
  p.elim ((0:ℂ):Sphere) (fun z => if z=0 then ∞ else (z⁻¹:ℂ))
end CannonMobius

namespace CannonMobius
lemma inv_coe {z : ℂ} (hz : z ≠ 0) : inv (z:Sphere)=(z⁻¹:ℂ) := by simp [inv,hz]
end CannonMobius

namespace CannonMobius
@[simp] lemma inv_zero : inv ((0:ℂ):Sphere)=∞ := by simp [inv]
end CannonMobius

namespace CannonMobius
lemma continuous_inv : Continuous inv := by
  rw [OnePoint.continuous_iff]
  constructor
  · have ht : Tendsto (fun z : ℂ => ((z⁻¹:ℂ):Sphere)) (coclosedCompact ℂ)
        (𝓝 ((0:ℂ):Sphere)) := by
      apply OnePoint.continuous_coe.continuousAt.tendsto.comp
      simpa only [coclosedCompact_eq_cocompact,← Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_cobounded : Tendsto Inv.inv (Bornology.cobounded ℂ) (𝓝 (0:ℂ)))
    apply ht.congr'
    have hn : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ≠ 0 := by
      rw [coclosedCompact_eq_cocompact]
      exact isCompact_singleton.compl_mem_cocompact
    filter_upwards [hn] with z hz
    exact (inv_coe hz).symm
  · apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z=0
    · subst z
      have ht : Tendsto (fun z : ℂ => ((z⁻¹:ℂ):Sphere)) (𝓝[≠] (0:ℂ)) (𝓝 ∞) := by
        apply OnePoint.tendsto_coe_infty.comp
        simpa only [coclosedCompact_eq_cocompact,← Metric.cobounded_eq_cocompact] using
          (tendsto_inv₀_nhdsNE_zero : Tendsto Inv.inv (𝓝[≠] (0:ℂ)) (Bornology.cobounded ℂ))
      have hcon : Tendsto (fun z : ℂ => inv (z:Sphere)) (𝓝[≠] (0:ℂ)) (𝓝 ∞) := ht.congr'
        (Filter.Eventually.mono self_mem_nhdsWithin (fun z hz => (inv_coe hz).symm))
      have hw : ContinuousWithinAt (fun z : ℂ => inv (z:Sphere)) (univ \ {0}) 0 := by
        simpa only [ContinuousWithinAt,compl_eq_univ_sdiff,inv_zero] using hcon
      exact (continuousWithinAt_univ _ _).mp (continuousWithinAt_sdiff_self.mp hw)
    · apply (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)).congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact inv_coe hw
end CannonMobius

namespace CannonMobius
@[simp] lemma inv_infty : inv ∞=((0:ℂ):Sphere) := rfl
lemma inv_involutive : Function.Involutive inv := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z=0
    · simp [hz]
    · rw [inv_coe hz,inv_coe (inv_ne_zero hz),inv_inv]
end CannonMobius

namespace CannonMobius
def inversion : Sphere ≃ₜ Sphere where
  toFun := inv
  invFun := inv
  left_inv := inv_involutive
  right_inv := inv_involutive
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv
end CannonMobius

def chartTransform (p : Sphere) : Sphere ≃ₜ Sphere :=
  if p = ∞ then CannonMobius.inversion else Homeomorph.refl _

theorem chartSymm_eq_transform (p : Sphere) (z : ℂ) :
    chartSymm p z = chartTransform p (z : Sphere) := by
  unfold chartSymm chartTransform
  split_ifs <;> rfl

theorem chartTransform_involutive (p : Sphere) : Function.Involutive (chartTransform p) := by
  by_cases hp : p = ∞
  · rw [chartTransform, if_pos hp]
    change Function.Involutive CannonMobius.inv
    exact CannonMobius.inv_involutive
  · simp only [chartTransform, if_neg hp, Homeomorph.refl_apply]
    exact fun _ => rfl

theorem chart_eq_coordinate_transform (p q : Sphere) :
    chart p q = CannonMobius.coordinate (chartTransform p q) := by
  unfold chart chartTransform
  split_ifs <;> rfl

theorem chartSymm_chart_of_ne (p q : Sphere) (hq : chartTransform p q ≠ ∞) :
    chartSymm p (chart p q) = q := by
  rw [chartSymm_eq_transform, chart_eq_coordinate_transform, CannonMobius.coe_coordinate hq]
  exact chartTransform_involutive p q

theorem chartTransform_center_ne_infty (p : Sphere) : chartTransform p p ≠ ∞ := by
  by_cases hp : p = ∞
  · subst p
    rw [chartTransform, if_pos rfl]
    change CannonMobius.inv ∞ ≠ ∞
    exact OnePoint.coe_ne_infty 0
  · rw [chartTransform, if_neg hp]
    exact hp

theorem chartSymm_chart_self (p : Sphere) : chartSymm p (chart p p) = p :=
  chartSymm_chart_of_ne p p (chartTransform_center_ne_infty p)

theorem continuous_chartSymm (p : Sphere) : Continuous (chartSymm p) := by
  have heq : chartSymm p = fun z : ℂ => chartTransform p (z : Sphere) :=
    funext (chartSymm_eq_transform p)
  rw [heq]
  exact (chartTransform p).continuous.comp OnePoint.continuous_coe

theorem eventually_chartSymm_chart (p : Sphere) :
    ∀ᶠ q in 𝓝 p, chartSymm p (chart p q) = q := by
  have hn : ∀ᶠ q in 𝓝 p, chartTransform p q ≠ ∞ :=
    ((chartTransform p).continuous.continuousAt).eventually
      (isOpen_compl_singleton.mem_nhds (chartTransform_center_ne_infty p))
  exact hn.mono (fun q hq => chartSymm_chart_of_ne p q hq)

theorem IsConformalAt.comp {f g : Sphere → Sphere} {p : Sphere}
    (hg : IsConformalAt g (f p)) (hf : IsConformalAt f p) : IsConformalAt (g ∘ f) p := by
  obtain ⟨hfc, df, hdf, hfder⟩ := hf
  obtain ⟨hgc, dg, hdg, hgder⟩ := hg
  refine ⟨hgc.comp hfc, dg * df, mul_ne_zero hdg hdf, ?_⟩
  have hx : chart (f p) (f (chartSymm p (chart p p))) = chart (f p) (f p) := by
    rw [chartSymm_chart_self]
  have hgder' : HasDerivAt
      (fun z => chart (g (f p)) (g (chartSymm (f p) z))) dg
      (chart (f p) (f (chartSymm p (chart p p)))) := hx.symm ▸ hgder
  have hd := hgder'.comp (chart p p) hfder
  have hcont : Tendsto (fun z => f (chartSymm p z)) (𝓝 (chart p p)) (𝓝 (f p)) := by
    have hfc' : ContinuousAt f (chartSymm p (chart p p)) := by
      rw [chartSymm_chart_self]
      exact hfc
    have hc := hfc'.comp (continuous_chartSymm p).continuousAt
    simpa only [Function.comp_def, chartSymm_chart_self] using hc.tendsto
  have he := hcont.eventually (eventually_chartSymm_chart (f p))
  apply hd.congr_of_eventuallyEq
  filter_upwards [he] with z hz
  change chart (g (f p)) (g (f (chartSymm p z))) =
    chart (g (f p)) (g (chartSymm (f p) (chart (f p) (f (chartSymm p z)))))
  rw [hz]

theorem IsConformalOn.comp {f g : Sphere → Sphere} {U V : Set Sphere}
    (hg : IsConformalOn g V) (hf : IsConformalOn f U) (hUV : MapsTo f U V) :
    IsConformalOn (g ∘ f) U :=
  fun p hp => (hg (f p) (hUV hp)).comp (hf p hp)

theorem IsConformalEquivalence.trans
    {f g : Sphere → Sphere} {U V W : Set Sphere}
    (hf : IsConformalEquivalence f U V) (hg : IsConformalEquivalence g V W) :
    IsConformalEquivalence (g ∘ f) U W := by
  obtain ⟨hfc, hfUV, fi, hfic, hfiVU, hfleft, hfright⟩ := hf
  obtain ⟨hgc, hgVW, gi, hgic, hgiWV, hgleft, hgright⟩ := hg
  refine ⟨hgc.comp hfc hfUV, hgVW.comp hfUV, fi ∘ gi,
    hfic.comp hgic hgiWV, hfiVU.comp hgiWV, ?_, ?_⟩
  · intro z hz
    simp only [Function.comp_apply, hgleft (f z) (hfUV hz), hfleft z hz]
  · intro w hw
    simp only [Function.comp_apply, hfright (gi w) (hgiWV hw), hgright w hw]

theorem IsConformallyRemovable.image_mobius {E : Set Sphere}
    (hE : IsConformallyRemovable E) (M : Mobius) (e : Sphere ≃ₜ Sphere)
    (hM : ∀ p, e p = M • p)
    (he : ∀ p, IsConformalAt e p) (hi : ∀ p, IsConformalAt e.symm p) :
    IsConformallyRemovable (e '' E) := by
  refine ⟨hE.1.image e.continuous,?_⟩
  intro H hconf
  let K := (e.trans H).trans e.symm
  have hKconf : IsConformalOn K Eᶜ := by
    intro p hp
    have hpe : e p ∈ (e '' E)ᶜ := by
      rintro ⟨q,hq,heq⟩
      exact hp ((e.injective heq) ▸ hq)
    have hinner : IsConformalAt (H ∘ e) p := (hconf (e p) hpe).comp (he p)
    exact IsConformalAt.comp (f := H ∘ e) (g := e.symm) (hi (H (e p))) hinner
  obtain ⟨N,hN⟩ := hE.2 K hKconf
  refine ⟨M*N*M⁻¹,?_⟩
  intro q
  have h := congrArg e (hN (e.symm q))
  change e (e.symm (H (e (e.symm q)))) = e (N • e.symm q) at h
  simp only [e.apply_symm_apply] at h
  have hinv : e.symm q = M⁻¹ • q := by
    apply e.injective
    rw [e.apply_symm_apply,hM]
    simp
  rw [hM,hinv] at h
  simpa only [mul_smul] using h

def affineHomeomorph (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := a * z + b
  invFun z := (z - b) / a
  left_inv z := by dsimp; field_simp; ring
  right_inv z := by dsimp; field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def affineSphere (a b : ℂ) (ha : a ≠ 0) : Sphere ≃ₜ Sphere :=
  (affineHomeomorph a b ha).onePointCongr
@[simp] theorem affineSphere_infty (a b : ℂ) (ha : a ≠ 0) : affineSphere a b ha ∞ = ∞ := rfl

@[simp] theorem affineSphere_coe (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    affineSphere a b ha (z : Sphere) = ((a * z + b : ℂ) : Sphere) := rfl

@[simp] theorem chart_infty_apply (q : Sphere) :
    chart OnePoint.infty q = finiteCoord (sphereInv q) := by simp [chart]

namespace CannonMobius
@[simp] lemma coordinate_coe (z : ℂ) : coordinate (z:Sphere)=z := rfl
end CannonMobius

namespace CannonMobius
@[simp] lemma coordinate_inv_coe (z : ℂ) : coordinate (inv (z:Sphere))=z⁻¹ := by
  by_cases hz : z=0
  · simp [hz, coordinate]
  · rw [inv_coe hz,coordinate_coe]
end CannonMobius

theorem finiteCoord_sphereInv_coe (z : ℂ) : finiteCoord (sphereInv (z : Sphere)) = z⁻¹ := by
  change CannonMobius.coordinate (CannonMobius.inv (z : Sphere)) = z⁻¹
  exact CannonMobius.coordinate_inv_coe z

theorem affine_chart_at_infinity (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    chart OnePoint.infty (affineSphere a b ha (chartSymm OnePoint.infty z)) = z / (a + b * z) := by
  by_cases hz : z = 0
  · simp [hz, chart, chartSymm, sphereInv, affineSphere, finiteCoord]
  · have hden : a * z⁻¹ + b = (a + b * z) / z := by field_simp
    have hs : chartSymm OnePoint.infty z = ((z⁻¹ : ℂ) : Sphere) := by
      simp [chartSymm, sphereInv, hz]
    rw [hs, affineSphere_coe]
    rw [chart_infty_apply, finiteCoord_sphereInv_coe, hden, inv_div]

@[simp] theorem chartSymm_coe_apply (p z : ℂ) : chartSymm (p : Sphere) z = (z : Sphere) := by
  simp [chartSymm]

@[simp] theorem chart_coe_apply (p : ℂ) (q : Sphere) :
    chart (p : Sphere) q = finiteCoord q := by
  simp [chart]

@[simp] theorem chart_infty_self : chart OnePoint.infty OnePoint.infty = 0 := by
  simp [finiteCoord]

theorem isConformalAt_affineSphere (a b : ℂ) (ha : a ≠ 0) (p : Sphere) :
    IsConformalAt (affineSphere a b ha) p := by
  refine ⟨(affineSphere a b ha).continuous.continuousAt, ?_⟩
  cases p using OnePoint.rec with
  | infty =>
    refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
    have hd := (hasDerivAt_id (0 : ℂ)).div
      ((hasDerivAt_const (0 : ℂ) a).add ((hasDerivAt_id (0 : ℂ)).const_mul b))
      (by simpa using ha)
    have heq : (fun z => chart (affineSphere a b ha OnePoint.infty)
        (affineSphere a b ha (chartSymm OnePoint.infty z))) = fun z => z / (a + b * z) := by
      funext z
      exact affine_chart_at_infinity a b ha z
    rw [heq, chart_infty_self]
    have hscalar : (1 * (a + b * 0) - 0 * (0 + b * 1)) / (a + b * 0) ^ 2 = a⁻¹ := by
      simp only [mul_zero, add_zero, zero_mul, sub_zero, one_mul]
      field_simp
    rw [← hscalar]
    exact hd
  | coe z =>
    refine ⟨a, ha, ?_⟩
    simpa only [affineSphere_coe, chart_coe_apply, chartSymm_coe_apply,
      finiteCoord, OnePoint.elim_some, id_eq, mul_one] using
        ((hasDerivAt_id z).const_mul a).add_const b

/-- Sphere inversion exchanges zero and infinity and is its own inverse. -/
theorem sphereInv_involutive : Function.Involutive sphereInv := by
  intro p
  cases p using OnePoint.rec with
  | infty => simp [sphereInv]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp [sphereInv]
    · simp [sphereInv, hz, inv_ne_zero hz]

@[simp] theorem sphereInv_sphereInv (p : Sphere) : sphereInv (sphereInv p) = p :=
  sphereInv_involutive p

/-- The concrete chart and inverse chart are inverse at all finite chart values. -/
theorem chart_chartSymm (p : Sphere) (z : ℂ) :
    chart p (chartSymm p z) = z := by
  by_cases hp : p = ∞
  · simp [chart, chartSymm, hp, finiteCoord]
  · simp [chart, chartSymm, hp, finiteCoord]

/-- The identity is conformal in both finite and infinite charts. -/
theorem isConformalAt_id (p : Sphere) : IsConformalAt id p := by
  refine ⟨continuousAt_id, 1, one_ne_zero, ?_⟩
  have heq : (fun z => chart (id p) (id (chartSymm p z))) = id := funext (chart_chartSymm p)
  rw [heq]
  exact hasDerivAt_id _

@[simp] theorem chart_coe_self (p : ℂ) : chart (p : Sphere) (p : Sphere) = p := by
  simp [finiteCoord]

@[simp] theorem sphereInv_zero : sphereInv ((0 : ℂ) : Sphere) = OnePoint.infty := by
  simp [sphereInv]

theorem isConformalAt_inversion (p : Sphere) : IsConformalAt CannonMobius.inversion p := by
  refine ⟨CannonMobius.inversion.continuous.continuousAt, ?_⟩
  cases p using OnePoint.rec with
  | infty =>
    refine ⟨1, one_ne_zero, ?_⟩
    have heq : (fun z => chart (sphereInv OnePoint.infty)
        (sphereInv (chartSymm OnePoint.infty z))) = id := by
      funext z
      simp only [sphereInv_infty, chart_coe_apply, chartSymm, ite_true,
        sphereInv_sphereInv, finiteCoord, OnePoint.elim_some, id_eq]
    change HasDerivAt (fun z => chart (sphereInv OnePoint.infty)
      (sphereInv (chartSymm OnePoint.infty z))) 1 (chart OnePoint.infty OnePoint.infty)
    rw [heq, chart_infty_self]
    exact hasDerivAt_id 0
  | coe z =>
    by_cases hz : z = 0
    · subst z
      refine ⟨1, one_ne_zero, ?_⟩
      have heq : (fun w => chart (sphereInv ((0 : ℂ) : Sphere))
          (sphereInv (chartSymm ((0 : ℂ) : Sphere) w))) = id := by
        funext w
        simp only [sphereInv_zero, chart_infty_apply, chartSymm_coe_apply,
          sphereInv_sphereInv, finiteCoord, OnePoint.elim_some, id_eq]
      change HasDerivAt (fun w => chart (sphereInv ((0 : ℂ) : Sphere))
        (sphereInv (chartSymm ((0 : ℂ) : Sphere) w))) 1 (chart ((0 : ℂ) : Sphere) ((0 : ℂ) : Sphere))
      rw [heq, chart_coe_self]
      exact hasDerivAt_id 0
    · refine ⟨-(z ^ 2)⁻¹, neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hz)), ?_⟩
      have hfp : sphereInv (z : Sphere) = ((z⁻¹ : ℂ) : Sphere) := by simp [sphereInv, hz]
      change HasDerivAt (fun w => chart (sphereInv (z : Sphere))
        (sphereInv (chartSymm (z : Sphere) w))) _ (chart (z : Sphere) (z : Sphere))
      simpa only [hfp, chart_coe_apply, chartSymm_coe_apply,
        finiteCoord_sphereInv_coe, finiteCoord_coe] using hasDerivAt_inv hz

def pointToInfinity (p : Sphere) : Sphere ≃ₜ Sphere :=
  p.elim (Homeomorph.refl _) (fun z =>
    (affineSphere 1 (-z) one_ne_zero).trans CannonMobius.inversion)

theorem isConformalAt_pointToInfinity (p q : Sphere) :
    IsConformalAt (pointToInfinity p) q := by
  cases p using OnePoint.rec with
  | infty => exact isConformalAt_id q
  | coe z =>
    change IsConformalAt (CannonMobius.inversion ∘ affineSphere 1 (-z) one_ne_zero) q
    exact (isConformalAt_inversion _).comp (isConformalAt_affineSphere _ _ _ q)

theorem affineSphere_symm_eq (a b : ℂ) (ha : a ≠ 0) :
    (affineSphere a b ha).symm = affineSphere a⁻¹ (-b / a) (inv_ne_zero ha) := by
  apply Homeomorph.ext
  intro p
  cases p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change (((z - b) / a : ℂ) : Sphere) = ((a⁻¹ * z + -b / a : ℂ) : Sphere)
    congr 1
    ring

theorem isConformalAt_affineSphere_symm (a b : ℂ) (ha : a ≠ 0) (p : Sphere) :
    IsConformalAt (affineSphere a b ha).symm p := by
  rw [affineSphere_symm_eq]
  exact isConformalAt_affineSphere _ _ _ p

theorem isConformalAt_pointToInfinity_symm (p q : Sphere) :
    IsConformalAt (pointToInfinity p).symm q := by
  cases p using OnePoint.rec with
  | infty => exact isConformalAt_id q
  | coe z =>
    change IsConformalAt ((affineSphere 1 (-z) one_ne_zero).symm ∘ CannonMobius.inversion) q
    exact (isConformalAt_affineSphere_symm _ _ _ _).comp (isConformalAt_inversion q)

def affineMobius (a b : ℂ) (ha : a ≠ 0) : Mobius :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, 1] (by simpa using ha)

def inversionMobius : Mobius :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by norm_num)

def pointToInfinityMobius (p : Sphere) : Mobius :=
  p.elim 1 (fun z => inversionMobius * affineMobius 1 (-z) one_ne_zero)

theorem affineSphere_eq_smul (a b : ℂ) (ha : a ≠ 0) (p : Sphere) :
    affineSphere a b ha p = affineMobius a b ha • p := by
  cases p using OnePoint.rec with
  | infty => simp [affineSphere, OnePoint.smul_infty_eq_ite, affineMobius]
  | coe z => simp [affineSphere, affineHomeomorph, OnePoint.smul_some_eq_ite, affineMobius]

theorem inversion_eq_smul (p : Sphere) : CannonMobius.inversion p = inversionMobius • p := by
  change CannonMobius.inv p = inversionMobius • p
  cases p using OnePoint.rec with
  | infty => simp [OnePoint.smul_infty_eq_ite, inversionMobius]
  | coe z =>
    by_cases hz : z = 0
    · simp [hz, OnePoint.smul_some_eq_ite, inversionMobius]
    · simp [hz, OnePoint.smul_some_eq_ite, inversionMobius,
        CannonMobius.inv, div_eq_mul_inv]

theorem pointToInfinity_eq_smul (p q : Sphere) :
    pointToInfinity p q = pointToInfinityMobius p • q := by
  cases p using OnePoint.rec with
  | infty => simp [pointToInfinity, pointToInfinityMobius]
  | coe z =>
    change CannonMobius.inversion (affineSphere 1 (-z) one_ne_zero q) = _
    rw [inversion_eq_smul, affineSphere_eq_smul, ← mul_smul]
    rfl

theorem IsConformallyRemovable.frontier_pointToInfinity {G : Set Sphere}
    (hG : IsConformallyRemovable (frontier G)) (p : Sphere) :
    IsConformallyRemovable (frontier (pointToInfinity p '' G)) := by
  rw [← (pointToInfinity p).image_frontier]
  exact hG.image_mobius (pointToInfinityMobius p) (pointToInfinity p)
    (pointToInfinity_eq_smul p) (isConformalAt_pointToInfinity p)
    (isConformalAt_pointToInfinity_symm p)

def IsPrincipalNormalized (f : Sphere → Sphere) : Prop :=
  f OnePoint.infty = OnePoint.infty ∧
    (fun z : ℂ => finiteCoord (f (z : Sphere)) - z) =O[cobounded ℂ] (fun z => z⁻¹)

theorem isRoundClosedDisk_image_mobius {K : Set Sphere} (hK : IsRoundClosedDisk K)
    (M : Mobius) : IsRoundClosedDisk ((fun p : Sphere => M • p) '' K) := by
  obtain ⟨N, rfl⟩ := hK
  refine ⟨M * N, ?_⟩
  rw [Set.image_image]
  congr 1
  funext p
  exact (mul_smul M N p).symm

theorem isCircleDomain_image_mobius
    {U : Set Sphere} (hU : IsCircleDomain U) (M : Mobius) (e : Sphere ≃ₜ Sphere)
    (he : ∀ p, e p = M • p) : IsCircleDomain (e '' U) := by
  refine ⟨e.isOpenMap _ hU.1, hU.2.1.image e e.continuous.continuousOn, ?_⟩
  intro p hp
  have hpre : e.symm p ∈ Uᶜ := by
    intro hx
    exact hp ⟨e.symm p, hx, e.apply_symm_apply p⟩
  have hcomponent : e '' connectedComponentIn Uᶜ (e.symm p) =
      connectedComponentIn (e '' U)ᶜ p := by
    rw [e.image_connectedComponentIn hpre, e.image_compl, e.apply_symm_apply]
  rcases hU.2.2 (e.symm p) hpre with ⟨q, hq⟩ | hround
  · left
    refine ⟨e q, ?_⟩
    rw [← hcomponent, hq, image_singleton]
  · right
    rw [← hcomponent]
    have hefun : (e : Sphere → Sphere) = fun x => M • x := funext he
    simpa only [hefun] using isRoundClosedDisk_image_mobius hround M

theorem isConformalEquivalence_of_homeomorph (e : Sphere ≃ₜ Sphere) (U : Set Sphere)
    (he : IsConformalOn e U) (hi : IsConformalOn e.symm (e '' U)) :
    IsConformalEquivalence e U (e '' U) := by
  refine ⟨he, mapsTo_image _ _, e.symm, hi, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    simpa only [e.symm_apply_apply] using hp
  · intro p _
    exact e.symm_apply_apply p
  · intro p _
    exact e.apply_symm_apply p

theorem isConformalEquivalence_pointToInfinity (p : Sphere) (U : Set Sphere) :
    IsConformalEquivalence (pointToInfinity p) U (pointToInfinity p '' U) :=
  isConformalEquivalence_of_homeomorph _ U (fun q _ => isConformalAt_pointToInfinity p q)
    (fun q _ => isConformalAt_pointToInfinity_symm p q)

theorem pointToInfinity_apply_self (p : Sphere) : pointToInfinity p p = OnePoint.infty := by
  cases p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change CannonMobius.inv (affineSphere 1 (-z) one_ne_zero (z : Sphere)) = OnePoint.infty
    have heq : affineSphere 1 (-z) one_ne_zero (z : Sphere) = ((0 : ℂ) : Sphere) := by
      simp [affineSphere, affineHomeomorph]
    rw [heq]
    exact CannonMobius.inv_zero

theorem pointToInfinity_preserves_circleDomain (p : Sphere)
    {U : Set Sphere} (hU : IsCircleDomain U) :
    IsCircleDomain (pointToInfinity p '' U) :=
  isCircleDomain_image_mobius hU (pointToInfinityMobius p) (pointToInfinity p)
    (pointToInfinity_eq_smul p)

namespace CannonMobius

end CannonMobius

theorem analyticAt_finite_map_of_conformal
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U)
    (hf : IsConformalOn f U) {z : ℂ} (hz : (z : Sphere) ∈ U)
    (hfinite : f (z : Sphere) ≠ OnePoint.infty) :
    AnalyticAt ℂ (fun w : ℂ => finiteCoord (f (w : Sphere))) z := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hmem : ∀ᶠ w : ℂ in 𝓝 z, (w : Sphere) ∈ U :=
    OnePoint.continuous_coe.continuousAt.eventually (hU.mem_nhds hz)
  have hfin : ∀ᶠ w : ℂ in 𝓝 z, f (w : Sphere) ≠ OnePoint.infty :=
    ((hf _ hz).1.comp OnePoint.continuous_coe.continuousAt).eventually
      (isOpen_compl_singleton.mem_nhds hfinite)
  filter_upwards [hmem, hfin] with w hw hfw
  obtain ⟨_, d, _, hd⟩ := hf _ hw
  have heq : (fun y => chart (f (w : Sphere)) (f (chartSymm (w : Sphere) y))) =
      (fun y : ℂ => finiteCoord (f (y : Sphere))) := by
    funext y
    simp only [chart, hfw, ite_false, chartSymm_coe_apply]
  rw [heq, chart_coe_self] at hd
  exact hd.differentiableAt

def sphereLocalMap (f : Sphere → Sphere) (p : Sphere) : ℂ → ℂ :=
  fun z => chart (f p) (f (chartSymm p z))

theorem analyticAt_infty_chart
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) :
    AnalyticAt ℂ (sphereLocalMap f OnePoint.infty) 0 := by
  let F : Sphere → Sphere := CannonMobius.inversion ∘ f ∘ CannonMobius.inversion
  let V : Set Sphere := CannonMobius.inversion ⁻¹' U
  have hV : IsOpen V := hU.preimage CannonMobius.inversion.continuous
  have hF : IsConformalOn F V := by
    intro p hp
    exact (isConformalAt_inversion _).comp ((hf _ hp).comp (isConformalAt_inversion p))
  have hzero : ((0 : ℂ) : Sphere) ∈ V := by
    change CannonMobius.inv ((0 : ℂ) : Sphere) ∈ U
    simpa only [CannonMobius.inv_zero] using hinf
  have hFzero : F ((0 : ℂ) : Sphere) = ((0 : ℂ) : Sphere) := by
    change CannonMobius.inv (f (CannonMobius.inv ((0 : ℂ) : Sphere))) = _
    rw [CannonMobius.inv_zero, hfix, CannonMobius.inv_infty]
  have ha := analyticAt_finite_map_of_conformal hV hF hzero
    (by rw [hFzero]; exact OnePoint.coe_ne_infty (0 : ℂ))
  change AnalyticAt ℂ (fun z : ℂ => finiteCoord (sphereInv (f (sphereInv (z : Sphere))))) 0 at ha
  have heq : sphereLocalMap f OnePoint.infty =
      (fun z : ℂ => finiteCoord (sphereInv (f (sphereInv (z : Sphere))))) := by
    funext z
    change chart (f OnePoint.infty) (f (chartSymm OnePoint.infty z)) = _
    rw [hfix, chart_infty_apply, chartSymm, if_pos rfl]
  rw [heq]
  exact ha

theorem finiteCoord_sphereInv (p : Sphere) : finiteCoord (sphereInv p) = (finiteCoord p)⁻¹ := by
  cases p using OnePoint.rec with
  | infty => simp [finiteCoord]
  | coe z => simpa only [finiteCoord_coe] using finiteCoord_sphereInv_coe z

theorem analyticAt_dslope_zero {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (dslope u 0) 0 := by
  obtain ⟨p, hp⟩ := hu
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem reciprocal_germ_normalization {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 = 0) (hdu : deriv u 0 ≠ 0) :
    ∃ (a b : ℂ) (R : ℂ → ℂ), a ≠ 0 ∧ AnalyticAt ℂ R 0 ∧
      ∀ z : ℂ, z ≠ 0 → a * (u z)⁻¹ + b = z⁻¹ + z * R z := by
  let v := dslope u 0
  have hv : AnalyticAt ℂ v 0 := analyticAt_dslope_zero hu
  have hv0 : v 0 ≠ 0 := by simpa only [v, dslope_same] using hdu
  let q : ℂ → ℂ := fun z => (v z)⁻¹
  have hq : AnalyticAt ℂ q 0 := hv.inv hv0
  let r := dslope q 0
  let t := dslope r 0
  have ht : AnalyticAt ℂ t 0 := analyticAt_dslope_zero (analyticAt_dslope_zero hq)
  have hu_eq (z : ℂ) : u z = z * v z := by
    simpa only [sub_zero, smul_eq_mul, hu0] using (sub_smul_dslope u 0 z).symm
  have hq_eq (z : ℂ) : q z = q 0 + z * r 0 + z ^ 2 * t z := by
    have h1 : z * r z = q z - q 0 := by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope q 0 z
    have h2 : z * t z = r z - r 0 := by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope r 0 z
    calc
      q z = q 0 + z * r z := by linear_combination -h1
      _ = q 0 + z * r 0 + z ^ 2 * t z := by linear_combination -z * h2
  refine ⟨v 0, -(v 0 * r 0), fun z => v 0 * t z, hv0, analyticAt_const.mul ht, ?_⟩
  intro z hz
  calc
    v 0 * (u z)⁻¹ + -(v 0 * r 0) = v 0 * z⁻¹ * q z - v 0 * r 0 := by
      rw [hu_eq, mul_inv_rev]
      dsimp only [q]
      ring
    _ = z⁻¹ + z * (v 0 * t z) := by
      rw [hq_eq]
      dsimp only [q]
      field_simp
      ring

theorem affine_normalization_expansion
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (a b : ℂ) (R : ℂ → ℂ), a ≠ 0 ∧ AnalyticAt ℂ R 0 ∧
      ∀ z : ℂ, z ≠ 0 → a * finiteCoord (f (z : Sphere)) + b = z + z⁻¹ * R z⁻¹ := by
  have ha := analyticAt_infty_chart hU hf hinf hfix
  have hzero : sphereLocalMap f OnePoint.infty 0 = 0 := by
    simp only [sphereLocalMap, chartSymm, ite_true, sphereInv_zero, hfix, chart_infty_self]
  obtain ⟨_, d, hd, hder⟩ := hf _ hinf
  have hder' : HasDerivAt (sphereLocalMap f OnePoint.infty) d 0 := by
    change HasDerivAt (sphereLocalMap f OnePoint.infty) d
      (chart OnePoint.infty OnePoint.infty) at hder
    rw [chart_infty_self] at hder
    exact hder
  have hdu : deriv (sphereLocalMap f OnePoint.infty) 0 ≠ 0 := hder'.deriv.symm ▸ hd
  obtain ⟨a, b, R, hane, hR, hexp⟩ := reciprocal_germ_normalization ha hzero hdu
  refine ⟨a, b, R, hane, hR, ?_⟩
  intro z hz
  have h := hexp z⁻¹ (inv_ne_zero hz)
  have hchart : (sphereLocalMap f OnePoint.infty z⁻¹)⁻¹ = finiteCoord (f (z : Sphere)) := by
    simp only [sphereLocalMap, hfix, chart_infty_apply, chartSymm, ite_true]
    have hinv : sphereInv ((z⁻¹ : ℂ) : Sphere) = (z : Sphere) := by
      simp [sphereInv, inv_ne_zero hz]
    rw [hinv, finiteCoord_sphereInv, inv_inv]
  simpa only [hchart, inv_inv] using h

theorem affine_normalization_bigO
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ a b : ℂ, a ≠ 0 ∧
      (fun z : ℂ => a * finiteCoord (f (z : Sphere)) + b - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  obtain ⟨a, b, R, ha, hR, hexp⟩ := affine_normalization_expansion hU hf hinf hfix
  have hb : (fun z : ℂ => R z⁻¹) =O[cobounded ℂ] (fun _ => (1 : ℂ)) := by
    simpa only [Function.comp_def] using
      (hR.continuousAt.isBigO (F := ℂ)).comp_tendsto (tendsto_inv₀_cobounded (α := ℂ))
  have hp := (isBigO_refl (fun z : ℂ => z⁻¹) (cobounded ℂ)).mul hb
  refine ⟨a, b, ha, hp.congr' ?_ ?_⟩
  · have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
      rw [Metric.cobounded_eq_cocompact]
      exact (isCompact_singleton.compl_mem_cocompact : {0}ᶜ ∈ cocompact ℂ)
    filter_upwards [hn] with z hz
    change z⁻¹ * R z⁻¹ = a * finiteCoord (f (z : Sphere)) + b - z
    rw [hexp z hz]
    ring
  · exact Eventually.of_forall (fun z => mul_one z⁻¹)

theorem finite_image_of_fixes_infty
    {U : Set Sphere} {f : Sphere → Sphere} (hinj : InjOn f U)
    (hU : OnePoint.infty ∈ U) (hf : f OnePoint.infty = OnePoint.infty)
    {z : ℂ} (hz : (z : Sphere) ∈ U) : f (z : Sphere) ≠ OnePoint.infty := by
  intro h
  exact OnePoint.coe_ne_infty z (hinj hz hU (h.trans hf.symm))

theorem principal_normalize_at_infty
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinj : InjOn f U) (hinf : OnePoint.infty ∈ U)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (a b : ℂ) (ha : a ≠ 0), IsPrincipalNormalized (affineSphere a b ha ∘ f) := by
  obtain ⟨a, b, ha, hbig⟩ := affine_normalization_bigO hU hf hinf hfix
  refine ⟨a, b, ha, ?_, ?_⟩
  · simp only [Function.comp_apply, hfix, affineSphere_infty]
  · have hm : ∀ᶠ z : ℂ in cobounded ℂ, (z : Sphere) ∈ U := by
      have hm := OnePoint.tendsto_coe_infty (hU.mem_nhds hinf)
      change {z : ℂ | (z : Sphere) ∈ U} ∈ cobounded ℂ
      rw [Metric.cobounded_eq_cocompact]
      rw [coclosedCompact_eq_cocompact] at hm
      exact hm
    apply hbig.congr' _ EventuallyEq.rfl
    filter_upwards [hm] with z hz
    have hfin := finite_image_of_fixes_infty hinj hinf hfix hz
    have hp : f (z : Sphere) = ((finiteCoord (f (z : Sphere)) : ℂ) : Sphere) :=
      (CannonMobius.coe_coordinate hfin).symm
    have he := congrArg (fun p : Sphere => finiteCoord (affineSphere a b ha p)) hp
    simpa only [Function.comp_apply, affineSphere_coe, finiteCoord_coe] using
      congrArg (fun w : ℂ => w - z) he.symm

end OMA.S_arxiv_2409_19103
open OMA.S_arxiv_2409_19103
theorem OMA.solution : OMA.R_arxiv_2409_19103_R1.H2 := by
  intro U V f hU hV hrem hf
  obtain ⟨p,hp⟩ := hU.2.1.nonempty
  let A := pointToInfinity p
  let B := pointToInfinity (f p)
  let U' := A '' U
  have hA : IsConformalEquivalence A.symm U' U := by
    refine ⟨fun q _ => isConformalAt_pointToInfinity_symm p q,?_,A,
      fun q _ => isConformalAt_pointToInfinity p q,?_,?_,?_⟩
    · rintro q ⟨x,hx,rfl⟩
      simpa only [A.symm_apply_apply] using hx
    · exact mapsTo_image _ _
    · exact fun q _ => A.apply_symm_apply q
    · exact fun q _ => A.symm_apply_apply q
  let f₀ := B ∘ f ∘ A.symm
  have hf₀ : IsConformalEquivalence f₀ U' (B '' V) :=
    hA.trans (hf.trans (isConformalEquivalence_pointToInfinity (f p) V))
  have hU' : IsCircleDomain U' := pointToInfinity_preserves_circleDomain p hU
  have hinf : OnePoint.infty ∈ U' := by
    rw [← pointToInfinity_apply_self p]
    exact mem_image_of_mem A hp
  have hAi : A.symm OnePoint.infty = p := by
    rw [← pointToInfinity_apply_self p]
    exact A.symm_apply_apply p
  have hfix : f₀ OnePoint.infty = OnePoint.infty := by
    dsimp only [f₀,Function.comp_apply]
    rw [hAi]
    exact pointToInfinity_apply_self (f p)
  obtain ⟨a,b,ha,hnorm⟩ := principal_normalize_at_infty hU'.1 hf₀.1 hf₀.bijOn.injOn hinf hfix
  let C := affineSphere a b ha
  let f₁ := C ∘ f₀
  have hC : IsConformalEquivalence C (B '' V) (C '' (B '' V)) :=
    isConformalEquivalence_of_homeomorph C _ (fun q _ => isConformalAt_affineSphere a b ha q)
      (fun q _ => isConformalAt_affineSphere_symm a b ha q)
  have hf₁ : IsConformalEquivalence f₁ U' (C '' (B '' V)) := hf₀.trans hC
  have hc : IsCircleDomain (C '' (B '' V)) :=
    isCircleDomain_image_mobius (pointToInfinity_preserves_circleDomain (f p) hV)
      (affineMobius a b ha) C (affineSphere_eq_smul a b ha)
  have hrem' : IsConformallyRemovable (frontier U') := hrem.frontier_pointToInfinity p
  have he := hf₁.bijOn.image_eq
  refine ⟨pointToInfinityMobius p, affineMobius a b ha * pointToInfinityMobius (f p), ?_⟩
  have hG : (fun q => pointToInfinityMobius p • q) '' U = U' := by
    simp only [U', A, ← pointToInfinity_eq_smul]
  have hsym (q : Sphere) : (pointToInfinityMobius p)⁻¹ • q = A.symm q := by
    calc
      _ = (pointToInfinityMobius p)⁻¹ • A (A.symm q) := congrArg _ (A.apply_symm_apply q).symm
      _ = A.symm q := by rw [show A (A.symm q) = pointToInfinityMobius p • A.symm q from pointToInfinity_eq_smul _ _, inv_smul_smul]
  have hg : (fun q => (affineMobius a b ha * pointToInfinityMobius (f p)) • f ((pointToInfinityMobius p)⁻¹ • q)) = f₁ := by
    funext q
    simp only [hsym, mul_smul, ← pointToInfinity_eq_smul, ← affineSphere_eq_smul]
    rfl
  rw [hG]
  have hout : IsCircleDomain U' ∧ ∞ ∈ U' ∧ IsConformalEquivalence f₁ U' (f₁ '' U') ∧ IsPrincipalNormalized f₁ ∧ IsCircleDomain (f₁ '' U') ∧ IsConformallyRemovable (frontier U') :=
    ⟨hU', hinf, he.symm ▸ hf₁, hnorm, he.symm ▸ hc, hrem'⟩
  obtain ⟨h1,h2,h3,⟨h4,h5⟩,h6,h7⟩ := hout
  rw [← hg] at h3 h4 h5 h6
  exact ⟨h1,h2,h3,h4,h5,h6,h7⟩

end
