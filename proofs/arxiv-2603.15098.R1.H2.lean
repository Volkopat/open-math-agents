import OMAReductions.R_arxiv_2603_15098_R1
import Mathlib

/- Adapted from OpenAI, openai/math, Apache-2.0, commit
3344da59991ed94f9ba711217b29c1d760badfa6. Ported to the OMA sphere charts. -/
noncomputable section
open Set Filter Topology Classical
open scoped OnePoint
namespace OMA.S_arxiv_2603_15098
@[simp] lemma sphereInv_infty : sphereInv ∞ = ((0 : ℂ) : Sphere) := rfl
@[simp] lemma finiteCoord_coe (z : ℂ) : finiteCoord (z : Sphere) = z := rfl

namespace CannonMobius
def inv (p : Sphere) : Sphere :=
  p.elim ((0:ℂ):Sphere) (fun z => if z=0 then ∞ else (z⁻¹:ℂ)) 

@[simp] lemma inv_infty : inv ∞ = ((0 : ℂ) : Sphere) := rfl
lemma inv_coe {z : ℂ} (hz : z ≠ 0) : inv (z:Sphere)=(z⁻¹:ℂ) := by simp [inv,hz] 

@[simp] lemma inv_zero : inv ((0:ℂ):Sphere)=∞ := by simp [inv] 

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

lemma inv_involutive : Function.Involutive inv := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z=0
    · simp [hz]
    · rw [inv_coe hz,inv_coe (inv_ne_zero hz),inv_inv] 

def inversion : Sphere ≃ₜ Sphere where
  toFun := inv
  invFun := inv
  left_inv := inv_involutive
  right_inv := inv_involutive
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv 

def coordinate (p : Sphere) : ℂ := p.elim 0 id 

@[simp] lemma coordinate_infty : coordinate ∞ = 0 := rfl
lemma coe_coordinate {p : Sphere} (hp : p ≠ ∞) : (coordinate p:Sphere)=p := by
  induction p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z => rfl 

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

def affineHomeomorph (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := a * z + b
  invFun z := (z - b) / a
  left_inv z := by dsimp; field_simp; ring
  right_inv z := by dsimp; field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop 

def affineSphere (a b : ℂ) (ha : a ≠ 0) : Sphere ≃ₜ Sphere :=
  (affineHomeomorph a b ha).onePointCongr 

@[simp] theorem affineSphere_coe (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    affineSphere a b ha (z : Sphere) = ((a * z + b : ℂ) : Sphere) := rfl 

@[simp] theorem chart_infty_apply (q : Sphere) :
    chart OnePoint.infty q = finiteCoord (sphereInv q) := by simp [chart] 

namespace CannonMobius
@[simp] lemma coordinate_coe (z : ℂ) : coordinate (z:Sphere)=z := rfl 

@[simp] lemma coordinate_inv_coe (z : ℂ) : coordinate (inv (z:Sphere))=z⁻¹ := by
  by_cases hz : z=0
  · simp [hz]
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
  have he : (fun z => chart (id p) (id (chartSymm p z))) = id := funext (chart_chartSymm p)
  rw [he]
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

end OMA.S_arxiv_2603_15098
open OMA.S_arxiv_2603_15098

theorem OMA.solution : OMA.R_arxiv_2603_15098_R1.H2 := by
  intro U ho hc
  obtain ⟨p, hp⟩ := hc.nonempty
  let g := pointToInfinity p
  refine ⟨g, g.isOpenMap U ho, hc.image g g.continuous.continuousOn,
    ⟨p, hp, pointToInfinity_apply_self p⟩, ?_⟩
  intro V f hf
  exact (isConformalEquivalence_pointToInfinity p U).trans hf

end
