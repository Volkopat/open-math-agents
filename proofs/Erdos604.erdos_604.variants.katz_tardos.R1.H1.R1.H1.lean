import OMAReductions.R_Erdos604_erdos_604_variants_katz_tardos_R1_H1_R1
import Mathlib

/-
Adapted from OpenAI math, Apache-2.0.
Source: https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6
OAI/Geometry/PinnedDistances. Copyright OpenAI 2026.
Port to Lean 4.33.1 and leaf adaptation to reduction H1.R1: my-other-github-account.
-/
namespace AA
noncomputable section
open Filter
open scoped Topology
namespace Aa
end Aa
end
end AA
namespace AA
universe u1 u2 u3
section
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter MeasureTheory
namespace Aa.Bounded
variable {I:Type u1} {X:Type u2} [Fintype I] [MeasurableSpace X] [MeasurableSingletonClass X]
def AM (w:I→ ℝ) (U:I→ X):Measure X :=
  ∑ i,ENNReal.ofReal (w i)• Measure.dirac (U i)
omit [MeasurableSingletonClass X] in
lemma RN (w:I→ ℝ) (U:I→ X) (hw:∀ i,0≤ w i) :
    AM w U Set.univ=ENNReal.ofReal (∑ i,w i):=by
  simp [AM,Measure.finsetSum_apply,ENNReal.ofReal_sum_of_nonneg (fun i _=> hw i)]
omit [MeasurableSingletonClass X] in
lemma DS (w:I→ ℝ) (U:I→ X)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1):IsProbabilityMeasure (AM w U):=by
  constructor
  rw [RN w U hw,hW,ENNReal.ofReal_one]
lemma DP (w:I→ ℝ) (U:I→ X) (hw:∀ i,0≤ w i) (f:X→ ℝ) :
    ∫ x,f x ∂ AM w U=∑ i,w i*f (U i):=by
  rw [AM,integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
lemma SR (w:I→ ℝ) (U:I→ X) {p:X→ Prop}
    (hp:∀ i,w i≠0→ p (U i)):∀ᵐ x ∂ AM w U,p x:=by
  rw [AM,ae_finsetSum_measure_iff]
  intro i _
  by_cases h:w i=0
  · simp [h]
  · exact Measure.ae_smul_measure (by simpa only [ae_dirac_eq,Filter.eventually_pure] using hp i h) _
omit [MeasurableSingletonClass X] in
lemma IY {Y:Type u3} [MeasurableSpace Y] (w:I→ ℝ) (U:I→ X)
    (f:X→ Y) (hf:Measurable f):(AM w U).map f=AM w (f∘ U):=by
  simp only [AM,Measure.map_finset_sum' hf.aemeasurable,
    Measure.map_smul,Measure.map_dirac' hf,Function.comp_def]
def Jh (w:I→ ℝ) (U:I→ X) (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) :
    ProbabilityMeasure X:=⟨AM w U,DS w U hw hW⟩
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5
section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Aa.Bounded
lemma Fs {X:Type u1} [MeasurableSpace X] (μ:Measure X) [IsFiniteMeasure μ]
    (f:X→ ℝ) (hf:Measurable f) (hbound:∀ x,‖f x‖≤1):Integrable f μ:=by
  exact (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable (Eventually.of_forall hbound)
variable {Ω:Type u2} {E:Type u3} {X:Type u4} {Y:Type u5} [MeasurableSpace Ω] [MeasurableSpace E]
  [MeasurableSpace X] [MeasurableSpace Y]
lemma FW (Q:Measure E) (μ:Measure X)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure μ]
    (f:E × X→ ℝ) (hf:Measurable f) (hbound:∀ p,‖f p‖≤1)
    (s:Set E) (hs:MeasurableSet s) :
    (∫ e in s,∫ x,f (e,x) ∂ μ ∂ Q)=
      ∫ p,(s×ˢ Set.univ).indicator f p ∂ Q.prod μ:=by
  have hi:=Fs (Q.prod μ) f hf hbound
  rw [integral_prod _ (hi.indicator (hs.prod MeasurableSet.univ))]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with e
  by_cases he:e∈s
  · simp [Set.indicator_of_mem,he]
  · simp [Set.indicator_of_notMem,he]
lemma Kp
    (R:Measure Ω) (Q:Measure E) (μ:Measure X) (ν:Measure Y)
    [IsProbabilityMeasure R] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e:Ω→ E) (z:Ω→ X) (w:Ω→ Y)
    (he:Measurable e) (hz:Measurable z) (hw:Measurable w)
    (hmz:R.map (fun r=>(e r,z r))=Q.prod μ)
    (hmw:R.map (fun r=>(e r,w r))=Q.prod ν)
    (f:E × X→ ℝ) (g:E × Y→ ℝ)
    (hf:Measurable f) (hg:Measurable g)
    (hfb:∀ p,‖f p‖≤1) (hgb:∀ p,‖g p‖≤1)
    (heq:∀ᵐ r ∂ R,f (e r,z r)=g (e r,w r)) :
    ∀ᵐ a ∂ Q,(∫ x,f (a,x) ∂ μ)=(∫ y,g (a,y) ∂ ν):=by
  apply Integrable.ae_eq_of_forall_setIntegral_eq
  · exact (Fs (Q.prod μ) f hf hfb).integral_prod_left
  · exact (Fs (Q.prod ν) g hg hgb).integral_prod_left
  · intro s hs _
    rw [FW Q μ f hf hfb s hs,
      FW Q ν g hg hgb s hs,← hmz,← hmw]
    rw [integral_map_of_stronglyMeasurable (he.prodMk hz)
      (hf.indicator (hs.prod MeasurableSet.univ)).stronglyMeasurable,
      integral_map_of_stronglyMeasurable (he.prodMk hw)
      (hg.indicator (hs.prod MeasurableSet.univ)).stronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [heq] with r hr
    by_cases h:e r∈s <;> simp [h,hr]
end Aa.Bounded
end
end
end AA
namespace AA
section
noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
namespace Aa.Bounded
def BL (a c:ℂ) (zw:ℂ × ℂ):ℝ :=
  min 1 ‖(c - a)*(zw.2 - zw.1)/((zw.1 - a)*(c - zw.2))‖
def BR (d:ℂ) (zw:ℂ × ℂ):ℝ :=
  min 1 ‖(zw.1 - zw.2)/(zw.2 - d)‖
def Cy (μ:Measure ℂ) (a c:ℂ):ℝ :=
  ∫ zw,BL a c zw ∂ μ.prod μ
def Cr (ν:Measure ℂ) (d:ℂ):ℝ :=
  ∫ zw,BR d zw ∂ ν.prod ν
lemma Lh (a c:ℂ):Measurable (BL a c):=by
  unfold BL
  fun_prop
lemma Kj (d:ℂ):Measurable (BR d):=by
  unfold BR
  fun_prop
lemma IJ (a c:ℂ) (zw:ℂ × ℂ):0≤ BL a c zw:=by
  exact le_min zero_le_one (norm_nonneg _)
lemma IQ (a c:ℂ) (zw:ℂ × ℂ):BL a c zw≤1 :=
  min_le_left _ _
lemma Et (d:ℂ) (zw:ℂ × ℂ):0≤ BR d zw:=by
  exact le_min zero_le_one (norm_nonneg _)
lemma HX (d:ℂ) (zw:ℂ × ℂ):BR d zw≤1 :=
  min_le_left _ _
lemma Kr (ν:Measure ℂ) [IsFiniteMeasure ν] (d:ℂ) :
    Integrable (BR d) (ν.prod ν):=by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (Kj d).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun zw=> by
    rw [Real.norm_eq_abs,abs_of_nonneg (Et d zw)]
    exact HX d zw
lemma Nh (c:ℂ) (zw:ℂ × ℂ)
    (hz:zw.1≠ c) (hw:zw.2≠ c) :
    Tendsto (fun a=> BL a c zw) (nhds c) (nhds 0):=by
  have hd:(zw.1 - c)*(c - zw.2)≠0 :=
    mul_ne_zero (sub_ne_zero.mpr hz) (sub_ne_zero.mpr hw.symm)
  have hc:ContinuousAt (fun a:ℂ=> BL a c zw) c:=by
    unfold BL
    fun_prop
  simpa [BL] using hc.tendsto
lemma Jx (μ:Measure ℂ) [NullSingletonClass μ] [SFinite μ] (c:ℂ) :
    ∀ᵐ zw ∂ μ.prod μ,zw.1≠ c∧ zw.2≠ c:=by
  rw [Measure.ae_prod_iff_ae_ae]
  · filter_upwards [μ.ae_ne c] with z hz
    filter_upwards [μ.ae_ne c] with w hw
    exact ⟨hz,hw⟩
  · exact ((measurableSet_eq_fun measurable_fst measurable_const).compl).inter
      ((measurableSet_eq_fun measurable_snd measurable_const).compl)
lemma Nn (μ:Measure ℂ) [IsFiniteMeasure μ] [NullSingletonClass μ] (c:ℂ) :
    Tendsto (fun a=> Cy μ a c) (nhds c) (nhds 0):=by
  have h:=tendsto_integral_filter_of_dominated_convergence
    (μ:=μ.prod μ) (l:=nhds c) (F:=fun a zw=> BL a c zw)
    (f:=fun _=>(0:ℝ)) (fun _=>(1:ℝ))
    (Filter.Eventually.of_forall fun a=>(Lh a c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a=> Filter.Eventually.of_forall fun zw=> by
      rw [Real.norm_eq_abs,abs_of_nonneg (IJ a c zw)]
      exact IQ a c zw)
    (integrable_const (1:ℝ))
    ((Jx μ c).mono fun zw hzw=> Nh c zw hzw.1 hzw.2)
  simpa [Cy] using h
lemma Ka (μ:Measure ℂ) [NullSingletonClass μ] [SFinite μ] :
    ∀ᵐ zw ∂ μ.prod μ,zw.1≠ zw.2:=by
  apply (Measure.ae_prod_iff_ae_ae (p:=fun zw:ℂ × ℂ=> zw.1≠ zw.2)
    (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Filter.Eventually.of_forall fun z =>
    (μ.ae_ne z).mono fun w hw=> hw.symm
lemma Qj (ν:Measure ℂ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (d:ℂ):0< Cr ν d:=by
  have hp:∀ᵐ zw ∂ ν.prod ν,0< BR d zw:=by
    filter_upwards [Ka ν,Jx ν d] with zw hzw hd
    exact lt_min zero_lt_one (norm_pos_iff.mpr
      (div_ne_zero (sub_ne_zero.mpr hzw) (sub_ne_zero.mpr hd.2)))
  have hn:0≤ Cr ν d:=integral_nonneg (Et d)
  apply lt_of_le_of_ne hn
  intro he
  have hz:BR d =ᵐ[ν.prod ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (Et d)
      (Kr ν d)).mp he.symm
  have hf:∀ᵐ zw ∂ ν.prod ν,False:=hp.and hz |>.mono fun zw h=> by
    simpa [h.2] using h.1
  simpa using (ae_iff.mp hf)
lemma Qe (μ ν:Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    (c d:ℂ) (hc:c∈ μ.support) :
    ¬ (∀ᵐ a ∂ μ,Cy μ a c= Cr ν d):=by
  intro he
  have ht:=Qj ν d
  have hn:{a | Cy μ a c< Cr ν d}∈ nhds c :=
    (Nn μ c).eventually (eventually_lt_nhds ht)
  have hpos:=(Measure.mem_support_iff_forall c).mp hc _ hn
  have hzero:μ {a | Cy μ a c< Cr ν d}=0:=by
    have hnot:∀ᵐ a ∂ μ,¬ Cy μ a c< Cr ν d :=
      he.mono fun a ha=> by simp [ha]
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hnot
  exact (ne_of_gt hpos) hzero
lemma KX (μ:Measure ℂ) [SFinite μ] :
    Measurable (fun ac:ℂ × ℂ=> Cy μ ac.1 ac.2):=by
  have hm:Measurable (fun v:(ℂ × ℂ) × (ℂ × ℂ) =>
      BL v.1.1 v.1.2 v.2):=by
    unfold BL
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable
lemma Kx (ν:Measure ℂ) [SFinite ν] :
    Measurable (Cr ν):=by
  have hm:Measurable (fun v:ℂ × (ℂ × ℂ)=> BR v.1 v.2):=by
    unfold BR
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable
def Kf (a b c d z:ℂ):ℂ:=b+(c - a)*(d - b)/(z - a)
lemma OJ (a b c d z:ℂ) (hz:z≠ a) :
    Kf a b c d z - d=(d - b)*(c - z)/(z - a):=by
  unfold Kf
  field_simp
  ring
lemma Ss (a b c d:ℂ) (zw:ℂ × ℂ) (hbd:b≠ d)
    (hz:zw.1≠ a) (hw:zw.2≠ a) (hwc:zw.2≠ c) :
    BR d (Kf a b c d zw.1,Kf a b c d zw.2) =
      BL a c zw:=by
  unfold BR BL
  congr 2
  have hma:=sub_ne_zero.mpr hz
  have hwa:=sub_ne_zero.mpr hw
  have hc:=sub_ne_zero.mpr hwc.symm
  have hdb:=sub_ne_zero.mpr hbd.symm
  rw [OJ a b c d zw.2 hw]
  unfold Kf
  field_simp
  ring
private lemma LR (f:ℂ × ℂ→ ℝ) (g:ℂ→ ℝ)
    (hf:Measurable f) (hg:Measurable g) :
    MeasurableSet {v:ℂ × (ℂ × ℂ) | f (v.1,v.2.1)= g v.2.2}:=by
  exact measurableSet_eq_fun (hf.comp (measurable_fst.prodMk measurable_snd.fst))
    (hg.comp measurable_snd.snd)
lemma Kk (μ ν:Measure ℂ) [SFinite μ] [SFinite ν] :
    MeasurableSet {v:ℂ × (ℂ × ℂ) | Cy μ v.1 v.2.1= Cr ν v.2.2} :=
  LR (fun ac=> Cy μ ac.1 ac.2) (Cr ν)
    (KX μ) (Kx ν)
abbrev Sphere:=OnePoint ℂ
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
lemma An:MeasurableEmbedding ((↑):ℂ→ Sphere) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding
end Aa.Bounded
namespace Aa.Bounded
open TopologicalSpace
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
instance Tl:SecondCountableTopology Sphere:=by
  let B:Set (Set Sphere) :=
    (fun U:Set ℂ=> OnePoint.some '' U) '' countableBasis ℂ ∪
      Set.range (fun n:ℕ=>(OnePoint.some '' Metric.closedBall (0:ℂ) (n:ℝ))ᶜ)
  have hcount:B.Countable:=(countable_countableBasis ℂ).image _ |>.union (Set.countable_range _)
  have hbase:IsTopologicalBasis B:=by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      rcases hU with ⟨V,hV,rfl⟩ | ⟨n,rfl⟩
      · exact OnePoint.isOpen_image_coe.mpr ((isBasis_countableBasis ℂ).isOpen hV)
      · exact OnePoint.isOpen_compl_image_coe.mpr ⟨Metric.isClosed_closedBall,isCompact_closedBall _ _⟩
    · intro a U ha hU
      induction a using OnePoint.rec with
      | coe a =>
        have hp:IsOpen (OnePoint.some ⁻¹' U:Set ℂ):=hU.preimage OnePoint.continuous_coe
        obtain ⟨V,hV,haV,hVU⟩:=(isBasis_countableBasis ℂ).mem_nhds_iff.mp (hp.mem_nhds ha)
        refine ⟨OnePoint.some '' V,Or.inl ⟨V,hV,rfl⟩,⟨a,haV,rfl⟩,?_⟩
        rintro z ⟨w,hw,rfl⟩
        exact hVU hw
      | infty =>
        have hc:=((OnePoint.isOpen_iff_of_mem ha).mp hU).2
        obtain ⟨R,hR⟩:=hc.isBounded.subset_closedBall (0:ℂ)
        obtain ⟨n,hn⟩:=exists_nat_gt R
        refine ⟨(OnePoint.some '' Metric.closedBall (0:ℂ) (n:ℝ))ᶜ,Or.inr ⟨n,rfl⟩,?_,?_⟩
        · exact OnePoint.infty_notMem_image_coe
        · intro z hz
          induction z using OnePoint.rec with
          | infty=> exact ha
          | coe z =>
            by_contra hnot
            have hzR:=hR hnot
            have hzn:=Metric.closedBall_subset_closedBall hn.le hzR
            exact hz ⟨z,hzn,rfl⟩
  exact hbase.secondCountableTopology hcount
lemma QX {α:ℕ→ ProbabilityMeasure Sphere} {β:ProbabilityMeasure Sphere}
    (hT:Tendsto α atTop (𝓝 β)) {U:Set Sphere} (hU:IsOpen U) (b:ℝ≥0∞)
    (hbound:∀ᶠ n in atTop,(α n:Measure Sphere) U≤ b) :
    (β:Measure Sphere) U≤ b:=by
  have hp:=ProbabilityMeasure.le_liminf_measure_open_of_tendsto hT hU
  exact hp.trans (liminf_le_of_frequently_le hbound.frequently)
lemma Nw {α:ℕ→ ProbabilityMeasure Sphere} {β:ProbabilityMeasure Sphere}
    (hT:Tendsto α atTop (𝓝 β)) (z:Sphere)
    (hsmall:∀ ε:ℝ,0< ε→∃ U:Set Sphere,IsOpen U∧ z∈ U ∧
      ∀ᶠ n in atTop,(α n:Measure Sphere) U≤ ENNReal.ofReal ε) :
    (β:Measure Sphere) {z}=0:=by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hεtop
  have hεR:(0:ℝ)< ε:=by exact_mod_cast hε
  obtain ⟨U,hU,hz,hB⟩:=hsmall (ε:ℝ) hεR
  have hb:=QX hT hU (ENNReal.ofReal (ε:ℝ)) hB
  rw [ENNReal.ofReal_coe_nnreal] at hb
  simpa only [zero_add] using (measure_mono (Set.singleton_subset_iff.mpr hz)).trans hb
theorem MC {α:ℕ→ ProbabilityMeasure Sphere} {β:ProbabilityMeasure Sphere}
    (hT:Tendsto α atTop (𝓝 β))
    (htail:∀ ε:ℝ,0< ε→∃ R:ℝ,∀ᶠ n in atTop,
      (α n:Measure Sphere) (OnePoint.some '' Metric.closedBall (0:ℂ) R)ᶜ≤ ENNReal.ofReal ε)
    (hball:∀ z:ℂ,∀ ε:ℝ,0< ε→∃ r:ℝ,0< r∧∀ᶠ n in atTop,
      (α n:Measure Sphere) (OnePoint.some '' Metric.ball z r)≤ ENNReal.ofReal ε) :
    NullSingletonClass (β:Measure Sphere):=by
  constructor
  intro z
  apply Nw hT z
  intro ε hε
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨R,hR⟩:=htail ε hε
    exact ⟨_,OnePoint.isOpen_compl_image_coe.mpr ⟨Metric.isClosed_closedBall,isCompact_closedBall _ _⟩,
      OnePoint.infty_notMem_image_coe,hR⟩
  | coe z =>
    obtain ⟨r,hr,hR⟩:=hball z ε hε
    exact ⟨_,OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball,⟨z,Metric.mem_ball_self hr,rfl⟩,hR⟩
def EB (β:ProbabilityMeasure Sphere):Measure ℂ :=
  Measure.comap ((↑):ℂ→ Sphere) (β:Measure Sphere)
lemma GQ (β:ProbabilityMeasure Sphere)
    (hinfty:(β:Measure Sphere) {OnePoint.infty}=0):IsProbabilityMeasure (EB β):=by
  constructor
  rw [EB,An.comap_apply,Set.image_univ]
  have hh:(β:Measure Sphere) (Set.range ((↑):ℂ→ Sphere))ᶜ=0:=by
    simpa only [OnePoint.compl_range_coe] using hinfty
  exact measure_eq_measure_of_null_sdiff (Set.subset_univ _) (by simpa only [← Set.compl_eq_univ_sdiff] using hh) |>.trans (measure_univ)
lemma HG (β:ProbabilityMeasure Sphere) [NullSingletonClass (β:Measure Sphere)] :
    NullSingletonClass (EB β):=by
  constructor
  intro z
  rw [EB,An.comap_apply,Set.image_singleton,measure_singleton]
lemma LY (β:ProbabilityMeasure Sphere)
    (hinfty:(β:Measure Sphere) {OnePoint.infty}=0) :
    (EB β).map ((↑):ℂ→ Sphere)=(β:Measure Sphere):=by
  rw [EB,An.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  change (β:Measure Sphere) (Set.range ((↑):ℂ→ Sphere))ᶜ=0
  simpa only [OnePoint.compl_range_coe] using hinfty
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2
section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Aa.Bounded
abbrev BO (X:Type u1):=X × X × X × X
abbrev Expanded (X:Type u2):=BO X × ((X × X) × (X × X))
lemma RY (μ ν:Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    (Q:Measure (BO ℂ)) [IsProbabilityMeasure Q]
    (hind:Q.map (fun q=>(q.1,q.2.2))=μ.prod (Q.map (fun q=> q.2.2)))
    (hsupp:∀ᵐ q ∂ Q,q.2.2.1∈μ.support)
    (he:∀ᵐ q ∂ Q,Cy μ q.1 q.2.2.1=Cr ν q.2.2.2):False:=by
  let τ:Measure (ℂ × ℂ):=Q.map (fun q=> q.2.2)
  have:IsProbabilityMeasure τ:=Measure.isProbabilityMeasure_map (by fun_prop)
  have hp:=Kk μ ν
  have he':∀ᵐ v ∂ μ.prod τ,Cy μ v.1 v.2.1=Cr ν v.2.2:=by
    rw [← hind]
    exact (ae_map_iff (by fun_prop) hp).mpr he
  have hf:∀ᵐ cd ∂ τ,∀ᵐ a ∂ μ,Cy μ a cd.1=Cr ν cd.2 :=
    (Measure.ae_ae_comm hp).mp ((Measure.ae_prod_iff_ae_ae hp).mp he')
  have hs:∀ᵐ cd ∂ τ,cd.1∈μ.support :=
    (ae_map_iff (by fun_prop) (μ.isClosed_support.measurableSet.preimage measurable_fst)).mpr hsupp
  obtain ⟨cd,hc,hcd⟩:=(hs.and hf).exists
  exact Qe μ ν cd.1 cd.2 hc hcd
lemma Jp (a b c d z v:ℂ) (hz:z≠a)
    (hp:(z-a)*(v-b)=(c-a)*(d-b)):v=Kf a b c d z:=by
  unfold Kf
  have hh:v-b=(c-a)*(d-b)/(z-a):=(eq_div_iff (sub_ne_zero.mpr hz)).mpr (by simpa [mul_comm] using hp)
  linear_combination hh
lemma NM (μ ν:Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ]
    (Q:Measure (BO ℂ)) (R:Measure (Expanded ℂ))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (he:R.map Prod.fst=Q)
    (hm:R.map (fun r=>(r.1,(r.2.1.1,r.2.2.1)))=Q.prod (μ.prod μ))
    (hbd:∀ᵐ q ∂ Q,q.2.1≠q.2.2.2)
    (hz:∀ᵐ r ∂ R,(r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1))
    (hw:∀ᵐ r ∂ R,(r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)) :
    ∀ᵐ r ∂ R,BL r.1.1 r.1.2.2.1 (r.2.1.1,r.2.2.1)=
      BR r.1.2.2.2 (r.2.1.2,r.2.2.2):=by
  have hpred:MeasurableSet {p:BO ℂ × (ℂ × ℂ) |
      p.2.1≠p.1.1∧ p.2.2≠p.1.1∧ p.2.2≠p.1.2.2.1}:=by
    measurability
  have hpair:∀ᵐ p ∂ Q.prod (μ.prod μ),
      p.2.1≠p.1.1∧ p.2.2≠p.1.1∧ p.2.2≠p.1.2.2.1:=by
    rw [Measure.ae_prod_iff_ae_ae hpred]
    exact Eventually.of_forall fun e=> by
      filter_upwards [Jx μ e.1,Jx μ e.2.2.1] with zw ha hc
      exact ⟨ha.1,ha.2,hc.2⟩
  rw [← hm] at hpair
  have hp:=(ae_map_iff (by fun_prop) hpred).mp hpair
  have hd:∀ᵐ r ∂ R,r.1.2.1≠r.1.2.2.2:=by
    rw [← he] at hbd
    exact (ae_map_iff measurable_fst.aemeasurable (by measurability)).mp hbd
  filter_upwards [hp,hd,hz,hw] with r hp hd hz hw
  have hz':=Jp r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 _ _ hp.1 hz
  have hw':=Jp r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 _ _ hp.2.1 hw
  have hh:=(Ss r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2
    (r.2.1.1,r.2.2.1) hd hp.1 hp.2.1 hp.2.2).symm
  simpa only [← hz',← hw'] using hh
lemma NS (μ ν:Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (Q:Measure (BO ℂ)) (R:Measure (Expanded ℂ))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (hm₁:R.map (fun r=>(r.1,(r.2.1.1,r.2.2.1)))=Q.prod (μ.prod μ))
    (hm₂:R.map (fun r=>(r.1,(r.2.1.2,r.2.2.2)))=Q.prod (ν.prod ν))
    (hk:∀ᵐ r ∂ R,BL r.1.1 r.1.2.2.1 (r.2.1.1,r.2.2.1)=
      BR r.1.2.2.2 (r.2.1.2,r.2.2.2)) :
    ∀ᵐ q ∂ Q,Cy μ q.1 q.2.2.1=Cr ν q.2.2.2:=by
  apply Kp R Q (μ.prod μ) (ν.prod ν) Prod.fst
    (fun r=>(r.2.1.1,r.2.2.1)) (fun r=>(r.2.1.2,r.2.2.2))
    (by fun_prop) (by fun_prop) (by fun_prop) hm₁ hm₂
    (fun p=> BL p.1.1 p.1.2.2.1 p.2)
    (fun p=> BR p.1.2.2.2 p.2) ?_ ?_ ?_ ?_ hk
  · unfold BL; fun_prop
  · unfold BR; fun_prop
  · intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (IJ _ _ _)]
    exact IQ _ _ _
  · intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (Et _ _)]
    exact HX _ _
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Aa.Bounded
variable {I:Type u1} {V:Type u2} {X:Type u3} [Fintype I] [Fintype V]
def BU (w:I→ ℝ) (p:I→ V→ ℝ) (r:I × V):ℝ:=w r.1*p r.1 r.2
def BT (w:I→ ℝ) (p:I→ V→ ℝ) (r:I × V × V × V):ℝ :=
  w r.1*p r.1 r.2.1*p r.1 r.2.2.1*p r.1 r.2.2.2
lemma Mb (w:I→ ℝ) (p:I→ V→ ℝ)
    (hw:∑ i,w i=1) (hp:∀ i,∑ x,p i x=1):∑ r,BU w p r=1:=by
  simp only [BU,Fintype.sum_prod_type,← Finset.mul_sum,hp,mul_one,hw]
lemma Qi (w:I→ ℝ) (p:I→ V→ ℝ)
    (hw:∑ i,w i=1) (hp:∀ i,∑ x,p i x=1):∑ r,BT w p r=1:=by
  simp only [BT,Fintype.sum_prod_type,← Finset.mul_sum,hp,mul_one,hw]
def Fh (s:I→ V) (U₁ U₂:V→ X) (r:I × V):BO X :=
  (U₁ (s r.1),U₂ (s r.1),U₁ r.2,U₂ r.2)
def Ee (s:I→ V) (U₁ U₂:V→ X) (r:I × V × V × V):Expanded X :=
  (Fh s U₁ U₂ (r.1,r.2.1),((U₁ r.2.2.1,U₂ r.2.2.1),(U₁ r.2.2.2,U₂ r.2.2.2)))
lemma QM (w:I→ ℝ) (p:I→ V→ ℝ) (F:I→ V→ ℝ) (g h:V→ ℝ) :
    (∑ r,BT w p r*(F r.1 r.2.1*g r.2.2.1*h r.2.2.2))=
      ∑ i,w i*(∑ y,p i y*F i y)*(∑ z,p i z*g z)*(∑ z,p i z*h z):=by
  simp only [BT,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=∑ y,∑ z,∑ t,(w i*p i y*F i y)*(p i z*g z)*(p i t*h t):=by
      apply Finset.sum_congr rfl; intro y _
      apply Finset.sum_congr rfl; intro z _
      apply Finset.sum_congr rfl; intro t _
      ring
    _=(∑ y,w i*(p i y*F i y))*(∑ z,p i z*g z)*(∑ t,p i t*h t):=by
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      ring
    _= _:=by rw [← Finset.mul_sum]
lemma Fx (p:V→ ℝ) (f:V→ ℝ) (H:ℝ)
    (hp:∀ x,0≤p x) (hpsum:∑ x,p x=1) (hf:∀ x,|f x|≤H) :
    |∑ x,p x*f x|≤H:=by
  calc
    _≤∑ x,|p x*f x| := Finset.abs_sum_le_sum_abs _ _
    _=∑ x,p x*|f x| := by simp only [abs_mul,abs_of_nonneg (hp _)]
    _≤∑ x,p x*H:=Finset.sum_le_sum (fun x _=> mul_le_mul_of_nonneg_left (hf x) (hp x))
    _= H:=by rw [← Finset.sum_mul,hpsum,one_mul]
lemma QH (m₁ m₂ A₁ A₂ H₁ H₂:ℝ) (hm₂ : |m₂|≤H₂) (hA₁ : |A₁|≤H₁) :
    |m₁*m₂-A₁*A₂|≤H₂*|m₁-A₁|+H₁*|m₂-A₂| := by
  calc
    _ = |(m₁-A₁)*m₂+A₁*(m₂-A₂)| := by congr 1; ring
    _ ≤ |(m₁-A₁)*m₂|+|A₁*(m₂-A₂)| := abs_add_le _ _
    _≤ _:=by rw [abs_mul,abs_mul]; nlinarith [abs_nonneg (m₁-A₁),abs_nonneg (m₂-A₂)]
lemma Ks (w:I→ ℝ) (p:I→ V→ ℝ) (F:I→ V→ ℝ)
    (g h:V→ ℝ) (A₁ A₂ C H₁ H₂:ℝ)
    (hw:∀ i,0≤w i) (hp:∀ i x,0≤p i x) (hpsum:∀ i,∑ x,p i x=1)
    (hC:0≤C) (hF:∀ i x,|F i x|≤C) (hh:∀ x,|h x|≤H₂)
    (hA₁ : |A₁|≤H₁) :
    |(∑ r,BT w p r*(F r.1 r.2.1*g r.2.2.1*h r.2.2.2))-
      (∑ r,BU w p r*F r.1 r.2)*A₁*A₂|≤
      C*(H₂*(∑ i,w i*|(∑ z,p i z*g z)-A₁|)+H₁*(∑ i,w i*|(∑ z,p i z*h z)-A₂|)):=by
  let M:=fun i=>∑ y,p i y*F i y
  let G:=fun i=>∑ z,p i z*g z
  let H:=fun i=>∑ z,p i z*h z
  have hMC (i) : |M i|≤C:=Fx _ _ _ (hp i) (hpsum i) (hF i)
  rw [QM]
  have he:(∑ r,BU w p r*F r.1 r.2)=∑ i,w i*M i:=by
    simp only [BU,Fintype.sum_prod_type,M,Finset.mul_sum,mul_assoc]
  rw [he]
  change |(∑ i,w i*M i*G i*H i)-(∑ i,w i*M i)*A₁*A₂|≤_
  simp only [Finset.sum_mul,← Finset.sum_sub_distrib]
  calc
    _≤∑ i,|w i*M i*G i*H i-w i*M i*A₁*A₂| := Finset.abs_sum_le_sum_abs _ _
    _=∑ i,w i*|M i| *|G i*H i-A₁*A₂| := by
      apply Finset.sum_congr rfl; intro i _
      rw [show w i*M i*G i*H i-w i*M i*A₁*A₂= w i*M i*(G i*H i-A₁*A₂) by ring]
      rw [abs_mul,abs_mul,abs_of_nonneg (hw i)]
    _≤∑ i,w i*C*(H₂*|G i-A₁|+H₁*|H i-A₂|):=by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hMC i) (hw i)
      · exact QH _ _ _ _ _ _ (Fx _ _ _ (hp i) (hpsum i) hh) hA₁
      · exact abs_nonneg _
      · exact mul_nonneg (hw i) hC
    _= _:=by simp only [Finset.mul_sum,← Finset.sum_add_distrib,G,H]; apply Finset.sum_congr rfl; intros; ring
end Aa.Bounded
end
end
section
end
end AA
namespace AA
universe u1 u2 u3 u4
section
noncomputable section
open NumberField
open scoped BigOperators
namespace Aa.Arithmetic
variable {K:Type u1} [Field K]
variable [NumberField K]
lemma MZ (z:K) (hz:z≠0) :
    (∑ v:InfinitePlace K,(v.mult:ℝ)* Real.log (v z)) +
      ∑ᶠ v:FinitePlace K,Real.log (v z)=0:=by
  have hi:∀ v:InfinitePlace K,0< v z:=fun _=> InfinitePlace.pos_iff.mpr hz
  have hf:∀ v:FinitePlace K,0< v z:=fun _=> FinitePlace.pos_iff.mpr hz
  have h:=congrArg Real.log (NumberField.prod_abs_eq_one hz)
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr fun v _=> pow_ne_zero _ (hi v).ne')
    (finprod_ne_zero fun v=>(hf v).ne'),Real.log_prod (fun v _=> pow_ne_zero _ (hi v).ne'),
    Real.log_finprod hf,Real.log_one] at h
  simpa only [Real.log_pow] using h
def Bh (v:InfinitePlace K):ℝ :=
  (v.mult:ℝ)/ Module.finrank ℚ K
lemma Il:∑ v:InfinitePlace K,Bh v=1:=by
  classical
  unfold Bh
  rw [← Finset.sum_div,← Nat.cast_sum,InfinitePlace.sum_mult_eq,div_self]
  exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=K)).ne'
lemma EV (v:InfinitePlace K):0≤ Bh v:=by
  unfold Bh
  positivity
lemma LK {ι:Type u2} [Finite ι] (z:ι→ K)
    (hz:∀ i,z i≠0) :
    {v:FinitePlace K | ∃ i,v (z i)≠1}.Finite:=by
  have he:{v:FinitePlace K | ∃ i,v (z i)≠1} =
      ⋃ i,Function.mulSupport (fun v:FinitePlace K=> v (z i)):=by
    ext v
    simp
  rw [he]
  exact Set.finite_iUnion (fun i=> FinitePlace.hasFiniteMulSupport (hz i))
lemma Gk (v:AbsoluteValue K ℝ) (a b:K) (ha:a≠0) (hb:b≠0) :
    -Real.log (v a) + -Real.log (v b) = -Real.log (v (a* b)):=by
  rw [map_mul,Real.log_mul (v.pos ha).ne' (v.pos hb).ne']
  ring
lemma Jk {F:Type u3} [Field F] (a b c d t:F)
    (ha:c≠ a) (h:(c-a)*(d-b)=t):d= b+ t/(c-a):=by
  have h':d-b= t/(c-a):=(eq_div_iff (sub_ne_zero.mpr ha)).mpr
    (by simpa [mul_comm] using h)
  rw [← h']
  ring
lemma Pe {F:Type u4} [Field F] (a b c d z w t:F)
    (hc:c≠ a) (hz:z≠ a)
    (hcd:(c-a)*(d-b)=t) (hzw:(z-a)*(w-b)=t) :
    w-d= t*(c-z)/((z-a)*(c-a)):=by
  rw [Jk a b c d t hc hcd,Jk a b z w t hz hzw]
  field_simp
  ring
lemma Qb (v:FinitePlace K) {x y z:K}
    (_hxy:x≠ y) (_hyz:y≠ z) (hxz:x≠ z) :
    min (-Real.log (v (x-y))) (-Real.log (v (y-z))) ≤ -Real.log (v (x-z)):=by
  have h:=v.add_le (x-y) (y-z)
  rw [sub_add_sub_cancel] at h
  have hp:0< v (x-z):=FinitePlace.pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hl:=Real.log_le_log hp h
  by_cases hc:v (x-y)≤ v (y-z)
  · rw [max_eq_right hc] at hl
    exact (min_le_right _ _).trans (neg_le_neg hl)
  · rw [max_eq_left (le_of_not_ge hc)] at hl
    exact (min_le_left _ _).trans (neg_le_neg hl)
lemma HN (z:K) (hz:z≠0) :
    (∑ v:InfinitePlace K,Bh v*(-Real.log (v z))) +
      (Module.finrank ℚ K:ℝ)⁻¹*∑ᶠ v:FinitePlace K,-Real.log (v z)=0:=by
  have hh:=MZ z hz
  simp only [Bh,div_eq_mul_inv]
  rw [finsum_neg_distrib]
  have he:(∑ v:InfinitePlace K,(v.mult:ℝ)*(Module.finrank ℚ K:ℝ)⁻¹*(-Real.log (v z))) =
      -(Module.finrank ℚ K:ℝ)⁻¹*∑ v:InfinitePlace K,(v.mult:ℝ)* Real.log (v z):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he]
  linear_combination -(Module.finrank ℚ K:ℝ)⁻¹* hh
end Aa.Arithmetic
end
end
end AA
namespace AA
universe u1 u2 u3
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
namespace Aa.Ak
variable {P:Type u1} [Fintype P] [DecidableEq P]
structure Depth (P:Type u2) where
  value:P→ P→ ℝ
  symm:∀ x y,value x y= value y x
  Qw:∀ x y z,x≠ y→ y≠ z→ x≠ z →
    min (value x y) (value y z)≤ value x z
namespace Depth
variable (d:Depth P)
def share (r:ℝ) (x y:P):Prop:=x= y∨ r≤ d.value x y
instance (r:ℝ) (x y:P):Decidable (d.share r x y):=Classical.propDecidable _
omit [Fintype P] [DecidableEq P] in
lemma Jr (r:ℝ) (x:P):d.share r x x:=Or.inl rfl
omit [Fintype P] [DecidableEq P] in
lemma Qs {r:ℝ} {x y:P} (h:d.share r x y):d.share r y x:=by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by simpa only [d.symm y x] using h)
omit [Fintype P] in
lemma Ph {r:ℝ} {x y z:P} (hxy:d.share r x y) (hyz:d.share r y z) :
    d.share r x z:=by
  by_cases h₁:x= y
  · subst y; exact hyz
  by_cases h₂:y= z
  · subst z; exact hxy
  by_cases h₃:x= z
  · exact Or.inl h₃
  exact Or.inr ((le_min (hxy.resolve_left h₁) (hyz.resolve_left h₂)).trans
    (d.Qw x y z h₁ h₂ h₃))
omit [Fintype P] [DecidableEq P] in
lemma Ra {r t:ℝ} (htr:t≤ r) {x y:P} (h:d.share r x y) :
    d.share t x y:=h.imp_right (htr.trans ·)
def cell (r:ℝ) (x:P):Finset P:=Finset.univ.filter (d.share r x)
omit [DecidableEq P] in
@[simp] lemma BN (r:ℝ) (x y:P):y∈ d.cell r x↔ d.share r x y:=by
  simp [cell]
omit [DecidableEq P] in
@[simp] lemma CQ (r:ℝ) (x:P):x∈ d.cell r x:=by
  simp [Jr]
lemma Eh {r:ℝ} {x y:P} (h:d.share r x y):d.cell r x= d.cell r y:=by
  ext z
  simp only [BN]
  exact ⟨fun hz=> d.Ph (d.Qs h) hz,fun hz=> d.Ph h hz⟩
omit [DecidableEq P] in
lemma Hh {r t:ℝ} (htr:t≤ r) (x:P):d.cell r x⊆ d.cell t x:=by
  intro z hz
  exact (d.BN t x z).mpr (d.Ra htr ((d.BN r x z).mp hz))
def cells (r:ℝ):Finset (Finset P):=Finset.univ.image (d.cell r)
@[simp] lemma mem_cells (r:ℝ) (C:Finset P):C∈ d.cells r↔∃ x,d.cell r x= C:=by
  simp [cells]
lemma CX (r:ℝ) (x:P):d.cell r x∈ d.cells r:=by simp
lemma Cx {r:ℝ} {C:Finset P} (hC:C∈ d.cells r) {x:P} (hx:x∈ C) :
    C= d.cell r x:=by
  obtain ⟨z,rfl⟩:=(d.mem_cells r C).mp hC
  exact d.Eh ((d.BN r z x).mp hx)
lemma Rk {r:ℝ} {C D:Finset P} (hC:C∈ d.cells r)
    (hD:D∈ d.cells r) (hne:C≠ D):Disjoint C D:=by
  apply Finset.disjoint_left.mpr
  intro x hx hd
  exact hne ((d.Cx hC hx).trans (d.Cx hD hd).symm)
lemma Rq (r:ℝ) (x y:P) :
    (∑ C∈ d.cells r,(if x∈ C∧ y∈ C then (1:ℝ) else 0)) =
      if d.share r x y then 1 else 0:=by
  have h:∀ C∈ d.cells r,(if x∈ C∧ y∈ C then (1:ℝ) else 0) =
      if C= d.cell r x then (if d.share r x y then 1 else 0) else 0:=by
    intro C hC
    by_cases hx:x∈ C
    · rw [d.Cx hC hx]
      simp [d.Jr]
    · have hne:C≠ d.cell r x:=by intro he; apply hx; simpa [he] using d.CQ r x
      simp [hx,hne]
  rw [Finset.sum_congr rfl h]
  simp [d.CX r x]
def AR (r:ℝ):Finset (Finset P) :=
  (d.cells r).filter (fun C=> Fintype.card P<2*C.card)
@[simp] lemma CY (r:ℝ) (C:Finset P):C∈ d.AR r ↔
    C∈ d.cells r∧ Fintype.card P<2*C.card:=by simp [AR]
lemma GW {r:ℝ} {C D:Finset P} (hC:C∈ d.AR r)
    (hD:D∈ d.AR r):C= D:=by
  rw [d.CY] at hC hD
  by_contra hne
  have hd:=d.Rk hC.1 hD.1 hne
  have hc:=Finset.card_le_univ (C∪ D)
  rw [Finset.card_union_of_disjoint hd] at hc
  omega
def DL (r:ℝ):Finset P:=(d.AR r).biUnion id
lemma Gj {r:ℝ} {C:Finset P} (hC:C∈ d.AR r):d.DL r= C:=by
  have he:d.AR r={C}:=Finset.ext fun D=> by
    simp only [Finset.mem_singleton]
    exact ⟨fun hd=> d.GW hd hC,fun hd=> hd ▸ hC⟩
  simp [DL,he]
def transformed (r:ℝ):Multiset (Finset P) :=
  ((d.cells r).filter (fun C=>¬Fintype.card P<2*C.card)).val +
  ((d.AR r).val.map (fun C=> Cᶜ))
def Ch (f:Finset P→ ℝ) (r:ℝ):ℝ:=((d.transformed r).map f).sum
def Bb (r:ℝ) (x y:P):ℝ :=
  d.Ch (fun C=> if x∈ C∧ y∈ C then 1 else 0) r
def BW (r:ℝ):ℝ:=if (d.AR r).Nonempty then 1 else 0
def Ai (r:ℝ) (x:P):ℝ :=
  if (d.AR r).Nonempty∧ x∉ d.DL r then 1 else 0
lemma Kb (f:Finset P→ ℝ) (r:ℝ) :
    d.Ch f r=(∑ C∈ d.cells r,f C) +
      ∑ C∈ d.AR r,(f Cᶜ - f C):=by
  classical
  simp only [Ch,transformed,Multiset.map_add,Multiset.sum_add,
    Multiset.map_map,Finset.sum,Function.comp_def]
  change (∑ C∈(d.cells r).filter (fun C=>¬Fintype.card P<2*C.card),f C) +
    (∑ C∈ d.AR r,f Cᶜ)=(∑ C∈ d.cells r,f C) +
      ∑ C∈ d.AR r,(f Cᶜ - f C)
  rw [Finset.sum_sub_distrib]
  have hh:=Finset.sum_filter_add_sum_filter_not (d.cells r)
    (fun C=> Fintype.card P<2*C.card) f
  change (∑ C∈ d.AR r,f C)+ _= _ at hh
  linarith
lemma CF (r:ℝ) (x y:P) :
    d.Bb r x y=(if d.share r x y then 1 else 0) -
      d.BW r+ d.Ai r x+ d.Ai r y:=by
  unfold Bb
  rw [d.Kb,d.Rq]
  unfold BW Ai
  by_cases hg:(d.AR r).Nonempty
  · obtain ⟨G,hG⟩:=hg
    have he:d.AR r={G}:=Finset.ext fun C=> by
      simp only [Finset.mem_singleton]
      exact ⟨fun hc=> d.GW hc hG,fun hc=> hc ▸ hG⟩
    rw [d.Gj hG]
    have hg:(d.AR r).Nonempty:=⟨G,hG⟩
    simp only [he,Finset.sum_singleton,Finset.mem_compl]
    by_cases hx:x∈ G <;> by_cases hy:y∈ G <;> simp [hx,hy]
    ring
  · have he:d.AR r=∅:=Finset.not_nonempty_iff_eq_empty.mp hg
    simp [he]
lemma Ib (r:ℝ):(d.AR r).Nonempty ↔
    ∃ x:P,∃ C:Finset P,Fintype.card P<2*C.card∧∀ y∈ C,d.share r x y:=by
  constructor
  · rintro ⟨C,hC⟩
    obtain ⟨hC,hc⟩:=(d.CY r C).mp hC
    obtain ⟨x,rfl⟩:=(d.mem_cells r C).mp hC
    exact ⟨x,d.cell r x,hc,fun y hy=>(d.BN r x y).mp hy⟩
  · rintro ⟨x,C,hc,hC⟩
    have hsub:C⊆ d.cell r x:=fun y hy=>(d.BN r x y).mpr (hC y hy)
    refine ⟨d.cell r x,(d.CY r _).mpr ⟨d.CX r x,?_⟩⟩
    have:=Finset.card_le_card hsub
    omega
lemma Ti {r t:ℝ} (htr:t≤ r) (hr:(d.AR r).Nonempty) :
    (d.AR t).Nonempty:=by
  rw [d.Ib] at hr ⊢
  obtain ⟨x,C,hc,hC⟩:=hr
  exact ⟨x,C,hc,fun y hy=> d.Ra htr (hC y hy)⟩
lemma QJ:IsClosed {r:ℝ | (d.AR r).Nonempty}:=by
  simp_rw [d.Ib,Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro x
  apply isClosed_iUnion_of_finite
  intro C
  simp only [Set.ofPred_and]
  apply IsClosed.inter
  · by_cases h:Fintype.card P<2*C.card <;> simp [h]
  · simp_rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    by_cases hxy:x= y
    · simp [share,hxy]
    · simp only [share,hxy,false_or]
      exact isClosed_le continuous_id continuous_const
def radius:ℝ:=∑ x,∑ y,|d.value x y|
omit [DecidableEq P] in
lemma Fw:0≤ d.radius:=by unfold radius; positivity
omit [DecidableEq P] in
lemma Cf (x y:P) : |d.value x y| ≤ d.radius:=by
  have hx:(∑ y,|d.value x y|)≤ d.radius :=
    Finset.single_le_sum (fun z _=> Finset.sum_nonneg (fun w _=> abs_nonneg (d.value z w)))
      (Finset.mem_univ x)
  exact (Finset.single_le_sum (fun z _=> abs_nonneg (d.value x z)) (Finset.mem_univ y)).trans hx
omit [DecidableEq P] in
lemma EO {r:ℝ} (hr:r ≤ -d.radius) (x:P):d.cell r x= Finset.univ:=by
  ext y
  simp only [BN,Finset.mem_univ,iff_true]
  exact Or.inr (hr.trans (abs_le.mp (d.Cf x y)).1)
omit [DecidableEq P] in
lemma FY {r:ℝ} (hr:d.radius< r) (x:P):d.cell r x={x}:=by
  ext y
  simp only [BN,share,Finset.mem_singleton]
  have hh:¬r≤ d.value x y:=not_le.mpr ((abs_le.mp (d.Cf x y)).2.trans_lt hr)
  simp [hh,eq_comm]
lemma IZ (hn:2≤ Fintype.card P) {r:ℝ} (hr:r ≤ -d.radius) :
    (d.AR r).Nonempty:=by
  have:Nonempty P:=Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x⟩:=‹Nonempty P›
  refine ⟨Finset.univ,(d.CY r _).mpr ⟨?_,?_⟩⟩
  · exact (d.mem_cells r _).mpr ⟨x,d.EO hr x⟩
  · simp only [Finset.card_univ]
    omega
lemma Ek (hn:2≤ Fintype.card P) {r:ℝ} (hr:(d.AR r).Nonempty) :
    r≤ d.radius:=by
  by_contra! h
  obtain ⟨C,hC⟩:=hr
  obtain ⟨hC,hc⟩:=(d.CY r C).mp hC
  obtain ⟨x,rfl⟩:=(d.mem_cells r C).mp hC
  rw [d.FY h x,Finset.card_singleton] at hc
  omega
def M:ℝ:=sSup {r:ℝ | (d.AR r).Nonempty}
lemma FC (hn:2≤ Fintype.card P) (r:ℝ) :
    (d.AR r).Nonempty↔ r≤ d.M:=by
  have hne:Set.Nonempty {t:ℝ | (d.AR t).Nonempty}:=⟨-d.radius,d.IZ hn le_rfl⟩
  have hbd:BddAbove {t:ℝ | (d.AR t).Nonempty}:=⟨d.radius,fun t ht=> d.Ek hn ht⟩
  exact ⟨fun hr=> le_csSup hbd hr,fun hr =>
    d.Ti hr (d.QJ.csSup_mem hne hbd)⟩
lemma PZ (hn:2≤ Fintype.card P) : -d.radius≤ d.M∧ d.M≤ d.radius:=by
  constructor
  · exact (d.FC hn _).mp (d.IZ hn le_rfl)
  · exact d.Ek hn ((d.FC hn _).mpr le_rfl)
omit [DecidableEq P] in
lemma Ey (x:P):Measurable (fun r:ℝ=> d.cell r x):=by
  apply measurable_finset_iff.mpr
  intro y
  simp only [BN,share]
  exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const))
lemma Ha:Measurable d.cells:=by
  have hm:Measurable (fun r:ℝ=> fun x:P=> d.cell r x) :=
    measurable_pi_iff.mpr (d.Ey)
  exact (measurable_of_finite (fun f:P→ Finset P=> Finset.univ.image f)).comp hm
lemma EU:Measurable d.AR :=
  (measurable_of_finite (fun s:Finset (Finset P) =>
    s.filter (fun C:Finset P=> Fintype.card P<2*C.card))).comp d.Ha
lemma Py:Measurable d.DL :=
  (measurable_of_finite (fun s:Finset (Finset P)=> s.biUnion id)).comp d.EU
lemma Jv:Measurable d.BW :=
  (measurable_of_finite (fun s:Finset (Finset P)=> if s.Nonempty then (1:ℝ) else 0)).comp
    d.EU
lemma DO (x:P):Measurable (fun r=> d.Ai r x):=by
  have hm:Measurable (fun r:ℝ=>(d.AR r,d.DL r)) :=
    d.EU.prodMk d.Py
  exact (measurable_of_finite
    (fun st:Finset (Finset P) × Finset P=> if st.1.Nonempty∧ x∉ st.2 then (1:ℝ) else 0)).comp hm
lemma Lx (x y:P):Measurable (fun r=> d.Bb r x y):=by
  have hm:Measurable (fun r:ℝ=> if d.share r x y then (1:ℝ) else 0):=by
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_setOfPred.mpr
    exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const))
  have ht:Measurable (fun r =>
      (if d.share r x y then (1:ℝ) else 0) - d.BW r +
        d.Ai r x+ d.Ai r y) :=
    ((hm.sub d.Jv).add (d.DO x)).add
      (d.DO y)
  simpa only [CF] using ht
lemma BP (r:ℝ) (x:P) :
    0≤ d.Ai r x∧ d.Ai r x≤1:=by
  unfold Ai
  split_ifs <;> norm_num
lemma Dq (r:ℝ) (x y:P) :
    0≤ d.Bb r x y∧ d.Bb r x y≤2:=by
  have lo:0≤ d.Bb r x y:=by
    unfold Bb Ch
    apply Multiset.sum_nonneg
    intro t ht
    obtain ⟨C,hC,rfl⟩:=Multiset.mem_map.mp ht
    split_ifs <;> norm_num
  refine ⟨lo,?_⟩
  rw [CF]
  have hx:=(d.BP r x).2
  have hy:=(d.BP r y).2
  by_cases hg:(d.AR r).Nonempty
  · simp only [BW,hg,reduceIte]
    split_ifs <;> linarith
  · simp [BW,Ai,hg]
    split_ifs <;> norm_num
lemma FU (hn:2≤ Fintype.card P) {r:ℝ} (hr:r ≤ -d.radius)
    (x:P):d.Ai r x=0:=by
  have hg:Finset.univ∈ d.AR r:=(d.CY r _).mpr ⟨
    (d.mem_cells r _).mpr ⟨x,d.EO hr x⟩,by simp only [Finset.card_univ]; omega⟩
  simp [Ai,d.Gj hg]
lemma FD (hn:2≤ Fintype.card P) {r:ℝ} (hr:d.radius< r)
    (x:P):d.Ai r x=0:=by
  have hg:¬(d.AR r).Nonempty:=fun hg=> not_le.mpr hr (d.Ek hn hg)
  simp [Ai,hg]
lemma Ms (hn:2≤ Fintype.card P) {r:ℝ} (hr:r ≤ -d.radius)
    (x y:P):d.Bb r x y=0:=by
  have hxy:d.share r x y:=Or.inr (hr.trans (abs_le.mp (d.Cf x y)).1)
  simp [CF,BW,d.IZ hn hr,
    d.FU hn hr,hxy]
lemma LH (hn:2≤ Fintype.card P) {r:ℝ} (hr:d.radius< r)
    (x y:P) (hxy:x≠ y):d.Bb r x y=0:=by
  have hg:¬(d.AR r).Nonempty:=fun hg=> not_le.mpr hr (d.Ek hn hg)
  have hs:¬d.share r x y:=by
    simp only [share,hxy,false_or]
    exact not_le.mpr ((abs_le.mp (d.Cf x y)).2.trans_lt hr)
  simp [CF,BW,hg,hs,d.FD hn hr]
def Ag (x:P):ℝ:=∫ r:ℝ,d.Ai r x
def AN (x y:P) (_:x≠ y):ℝ:=∫ r:ℝ,d.Bb r x y
lemma Ct {f:ℝ→ ℝ} {a b C:ℝ}
    (hm:Measurable f) (hb:∀ r,‖f r‖≤ C)
    (hz:∀ r∉ Set.Icc a b,f r=0):Integrable f:=by
  have hi:IntegrableOn f (Set.Icc a b) :=
    IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall hb)
  have he:(Set.Icc a b).indicator f= f:=by
    apply Set.indicator_eq_self.mpr
    intro r hr
    by_contra hn
    exact hr (hz r hn)
  simpa only [he] using hi.integrable_indicator measurableSet_Icc
lemma De (hn:2≤ Fintype.card P) (x:P) :
    ∀ r∉ Set.Icc (-d.radius) d.radius,d.Ai r x=0:=by
  intro r hr
  by_cases hlo:r ≤ -d.radius
  · exact d.FU hn hlo x
  · exact d.FD hn
      (lt_of_not_ge (fun hhi=> hr ⟨le_of_not_ge hlo,hhi⟩)) x
lemma EN (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    ∀ r∉ Set.Icc (-d.radius) d.radius,d.Bb r x y=0:=by
  intro r hr
  by_cases hlo:r ≤ -d.radius
  · exact d.Ms hn hlo x y
  · exact d.LH hn
      (lt_of_not_ge (fun hhi=> hr ⟨le_of_not_ge hlo,hhi⟩)) x y hxy
lemma Bo (hn:2≤ Fintype.card P) (x:P) :
    Integrable (fun r=> d.Ai r x):=by
  apply Ct (d.DO x) (C:=1)
  · intro r
    rw [Real.norm_eq_abs,abs_of_nonneg (d.BP r x).1]
    exact (d.BP r x).2
  · exact d.De hn x
lemma Dj (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    Integrable (fun r=> d.Bb r x y):=by
  apply Ct (d.Lx x y) (C:=2)
  · intro r
    rw [Real.norm_eq_abs,abs_of_nonneg (d.Dq r x y).1]
    exact (d.Dq r x y).2
  · exact d.EN hn x y hxy
lemma KC {R a:ℝ} (hR:0≤ R) (ha:a∈ Set.Icc (-R) R) :
    (∫ r:ℝ in Set.Icc (-R) R,if r≤ a then (1:ℝ) else 0)= a+ R:=by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -R≤ R)]
  change (∫ r:ℝ in (-R)..R,{r:ℝ | r≤ a}.indicator (fun _=>(1:ℝ)) r)= a+ R
  rw [intervalIntegral.integral_indicator ha,intervalIntegral.integral_const]
  simp
lemma Eg (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    d.value x y= d.M+ d.AN x y hxy - d.Ag x - d.Ag y:=by
  let I:=Set.Icc (-d.radius) d.radius
  have hoc:IntegrableOn (fun r:ℝ=> if r≤ d.value x y then (1:ℝ) else 0) I:=by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_const.ite (measurableSet_le measurable_id measurable_const)
        measurable_const).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun r=> by split_ifs <;> norm_num)
  have hgc:IntegrableOn (fun r:ℝ=> if r≤ d.M then (1:ℝ) else 0) I:=by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_const.ite (measurableSet_le measurable_id measurable_const)
        measurable_const).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun r=> by split_ifs <;> norm_num)
  have hs:IntegrableOn (fun r:ℝ=>(if r≤ d.value x y then (1:ℝ) else 0) -
      (if r≤ d.M then (1:ℝ) else 0)) I:=hoc.sub hgc
  have hx:=(d.Bo hn x).integrableOn (s:=I)
  have hy:=(d.Bo hn y).integrableOn (s:=I)
  have ha:IntegrableOn (fun r:ℝ=>(if r≤ d.value x y then (1:ℝ) else 0) -
      (if r≤ d.M then (1:ℝ) else 0)+ d.Ai r x) I:=hs.add hx
  have he:(∫ r in I,d.Bb r x y) =
      (∫ r in I,if r≤ d.value x y then (1:ℝ) else 0) -
      (∫ r in I,if r≤ d.M then (1:ℝ) else 0) +
      (∫ r in I,d.Ai r x)+(∫ r in I,d.Ai r y):=by
    calc
      _=∫ r in I,((if r≤ d.value x y then (1:ℝ) else 0) -
          (if r≤ d.M then 1 else 0)+ d.Ai r x+ d.Ai r y):=by
        apply setIntegral_congr_fun measurableSet_Icc
        intro r _
        simp only [CF,share,hxy,false_or,BW,
          d.FC hn]
      _= _:=by rw [integral_add ha hy,integral_add hs hx,integral_sub hoc hgc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (d.EN hn x y hxy)] at he
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (d.De hn x),
    setIntegral_eq_integral_of_forall_compl_eq_zero (d.De hn y)] at he
  change d.AN x y hxy= _ at he
  dsimp only [I] at he
  rw [KC d.Fw (abs_le.mp (d.Cf x y)),
    KC d.Fw (d.PZ hn)] at he
  change d.AN x y hxy= _ - _+ d.Ag x+ d.Ag y at he
  linarith
lemma BM (x:P):0≤ d.Ag x :=
  integral_nonneg (fun r=>(d.BP r x).1)
lemma Fl (x y:P) (hxy:x≠ y):0≤ d.AN x y hxy :=
  integral_nonneg (fun r=>(d.Dq r x y).1)
lemma Ei {f:ℝ→ ℝ} {R C:ℝ} (hR:0≤ R)
    (hi:Integrable f) (hb:∀ r,f r≤ C)
    (hz:∀ r∉ Set.Icc (-R) R,f r=0):(∫ r,f r)≤2*R*C:=by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hh:=integral_mono (hi.integrableOn (s:=Set.Icc (-R) R))
    (integrableOn_const (s:=Set.Icc (-R) R) (μ:=volume)
      (C:=C) (measure_Icc_lt_top.ne)) (fun r=> hb r)
  rw [setIntegral_const] at hh
  simp only [Measure.real,Real.volume_Icc,sub_neg_eq_add,
    ENNReal.toReal_ofReal (by linarith:0≤ R+R),smul_eq_mul] at hh
  nlinarith
lemma Ou (hn:2≤ Fintype.card P) (x:P):d.Ag x≤2*d.radius:=by
  have hh:=Ei d.Fw (d.Bo hn x)
    (fun r=>(d.BP r x).2) (d.De hn x)
  change d.Ag x≤ _ at hh
  simpa only [mul_one] using hh
lemma Kg (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    d.AN x y hxy≤4*d.radius:=by
  have hh:=Ei d.Fw (d.Dj hn x y hxy)
    (fun r=>(d.Dq r x y).2) (d.EN hn x y hxy)
  change d.AN x y hxy≤ _ at hh
  linarith
lemma Pg (hn:2≤ Fintype.card P) (hzero:∀ x y,d.value x y=0) :
    d.M=0∧(∀ x,d.Ag x=0) ∧
      (∀ x y (hxy:x≠ y),d.AN x y hxy=0):=by
  have hr:d.radius=0:=by simp [radius,hzero]
  refine ⟨?_,?_,?_⟩
  · have:=d.PZ hn
    rw [hr] at this
    linarith [this.1,this.2]
  · intro x
    have:=d.Ou hn x
    rw [hr] at this
    linarith [d.BM x]
  · intro x y hxy
    have:=d.Kg hn x y hxy
    rw [hr] at this
    linarith [d.Fl x y hxy]
section Param
variable {Ω:Type u3} [MeasurableSpace Ω] (D:Ω→ Depth P)
  (hD:∀ x y,Measurable (fun ω=>(D ω).value x y))
  (R:Ω→ ℝ) (hR:Measurable R)
include hD hR
omit [DecidableEq P] in
lemma LB (x:P):Measurable (fun ω=>(D ω).cell (R ω) x):=by
  apply measurable_finset_iff.mpr
  intro y
  simp only [BN,share]
  exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le hR (hD x y)))
lemma EP:Measurable (fun ω=>(D ω).cells (R ω)):=by
  have hm:Measurable (fun ω=> fun x:P=>(D ω).cell (R ω) x) :=
    measurable_pi_iff.mpr (LB D hD R hR)
  exact (measurable_of_finite (fun f:P→ Finset P=> Finset.univ.image f)).comp hm
lemma DH:Measurable (fun ω=>(D ω).AR (R ω)) :=
  (measurable_of_finite (fun s:Finset (Finset P) =>
    s.filter (fun C:Finset P=> Fintype.card P<2*C.card))).comp
      (EP D hD R hR)
lemma Lb:Measurable (fun ω=>(D ω).DL (R ω)) :=
  (measurable_of_finite (fun s:Finset (Finset P)=> s.biUnion id)).comp
    (DH D hD R hR)
lemma Hj:Measurable (fun ω=>(D ω).BW (R ω)) :=
  (measurable_of_finite (fun s:Finset (Finset P)=> if s.Nonempty then (1:ℝ) else 0)).comp
    (DH D hD R hR)
lemma Dh (x:P):Measurable (fun ω=>(D ω).Ai (R ω) x):=by
  have hm:=(DH D hD R hR).prodMk (Lb D hD R hR)
  exact (measurable_of_finite
    (fun st:Finset (Finset P) × Finset P=> if st.1.Nonempty∧ x∉ st.2 then (1:ℝ) else 0)).comp hm
lemma Ik (x y:P):Measurable (fun ω=>(D ω).Bb (R ω) x y):=by
  have hm:Measurable (fun ω=> if (D ω).share (R ω) x y then (1:ℝ) else 0):=by
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_setOfPred.mpr
    exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le hR (hD x y)))
  have hh:Measurable (fun ω=>(if (D ω).share (R ω) x y then (1:ℝ) else 0) -
      (D ω).BW (R ω)+(D ω).Ai (R ω) x+(D ω).Ai (R ω) y) :=
    ((hm.sub (Hj D hD R hR)).add
    (Dh D hD R hR x)).add
    (Dh D hD R hR y)
  simpa only [CF,Pi.add_apply,Pi.sub_apply] using hh
omit hR
lemma DT (x:P):Measurable (fun ω=>(D ω).Ag x):=by
  have hm:Measurable (fun p:Ω × ℝ=>(D p.1).Ai p.2 x) :=
    Dh (P:=P) (Ω:=Ω × ℝ) (fun p:Ω × ℝ=> D p.1)
      (fun x y=>(hD x y).comp measurable_fst) Prod.snd measurable_snd x
  simpa only [Ag] using hm.stronglyMeasurable.integral_prod_right.measurable
lemma EA (x y:P) (hxy:x≠ y) :
    Measurable (fun ω=>(D ω).AN x y hxy):=by
  have hm:Measurable (fun p:Ω × ℝ=>(D p.1).Bb p.2 x y) :=
    Ik (P:=P) (Ω:=Ω × ℝ) (fun p:Ω × ℝ=> D p.1)
      (fun x y=>(hD x y).comp measurable_fst) Prod.snd measurable_snd x y
  simpa only [AN] using hm.stronglyMeasurable.integral_prod_right.measurable
lemma Ol (hn:2≤ Fintype.card P):Measurable (fun ω=>(D ω).M):=by
  obtain ⟨x,hx,y,hy,hxy⟩:=Finset.one_lt_card.mp (show 1<(Finset.univ:Finset P).card by simpa using (show 1< Fintype.card P by omega))
  have hh:=(((hD x y).sub (EA D hD x y hxy)).add
    (DT D hD x)).add (DT D hD y)
  have he:(fun ω=>(D ω).value x y - (D ω).AN x y hxy +
      (D ω).Ag x+(D ω).Ag y)=(fun ω=>(D ω).M):=by
    funext ω
    have:=(D ω).Eg hn x y hxy
    linarith
  change Measurable (fun ω=>(D ω).value x y - (D ω).AN x y hxy +
      (D ω).Ag x+(D ω).Ag y) at hh
  rwa [he] at hh
variable {μ:Measure Ω} (hi:∀ x y,Integrable (fun ω=>(D ω).value x y) μ)
include hi
omit [DecidableEq P] in
omit hD in
lemma DI:Integrable (fun ω=>(D ω).radius) μ:=by
  unfold radius
  exact integrable_finsetSum _ (fun x _=> integrable_finsetSum _ (fun y _=>(hi x y).abs))
lemma Cj (hn:2≤ Fintype.card P) (x:P) :
    Integrable (fun ω=>(D ω).Ag x) μ:=by
  apply Integrable.mono' ((DI D hi).const_mul 2)
    (DT D hD x).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs,abs_of_nonneg ((D ω).BM x)]
  exact (D ω).Ou hn x
lemma EI (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    Integrable (fun ω=>(D ω).AN x y hxy) μ:=by
  apply Integrable.mono' ((DI D hi).const_mul 4)
    (EA D hD x y hxy).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs,abs_of_nonneg ((D ω).Fl x y hxy)]
  exact (D ω).Kg hn x y hxy
lemma NL (hn:2≤ Fintype.card P):Integrable (fun ω=>(D ω).M) μ:=by
  apply Integrable.mono' (DI D hi) (Ol D hD hn).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ((D ω).PZ hn)
lemma Kt (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    (∫ ω,(D ω).value x y ∂μ) =
      (∫ ω,(D ω).M ∂μ)+(∫ ω,(D ω).AN x y hxy ∂μ) -
      (∫ ω,(D ω).Ag x ∂μ) - (∫ ω,(D ω).Ag y ∂μ):=by
  have hiM:=NL D hD hi hn
  have hiL:=EI D hD hi hn x y hxy
  have hix:=Cj D hD hi hn x
  have hiy:=Cj D hD hi hn y
  calc
    _=∫ ω,(D ω).M+(D ω).AN x y hxy - (D ω).Ag x - (D ω).Ag y ∂μ:=by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω=>(D ω).Eg hn x y hxy)
    _= _:=by
      have h₁:Integrable (fun ω=>(D ω).M+(D ω).AN x y hxy) μ:=hiM.add hiL
      have h₂:Integrable (fun ω=>(D ω).M+(D ω).AN x y hxy - (D ω).Ag x) μ:=h₁.sub hix
      rw [integral_sub h₂ hiy,integral_sub h₁ hix,integral_add hiM hiL]
end Param
end Depth
end Aa.Ak
end
end
end
end AA
namespace AA
universe u1 u2 u3
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
namespace Aa.Ao
def bin (l s x:ℝ):ℤ:=⌊(x-s)/l⌋
def CM (l s x y:ℝ):ℝ:=if bin l s x= bin l s y then 1 else 0
lemma Ts {l:ℝ} (hl:0< l) (s x:ℝ) :
    bin l (s+l) x= bin l s x - 1:=by
  unfold bin
  rw [show (x-(s+l))/l=(x-s)/l - 1 by field_simp; ring]
  exact Int.floor_sub_one _
lemma MP {l:ℝ} (hl:0< l) (x y:ℝ) :
    Function.Periodic (fun s=> CM l s x y) l:=by
  intro s
  simp [CM,Ts hl]
lemma Th (l s x y:ℝ):CM l s x y= CM l s y x:=by
  simp only [CM,eq_comm]
lemma GA (l x y:ℝ):Measurable (fun s=> CM l s x y):=by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_eq_fun
    (((measurable_const.sub measurable_id).div_const l).floor)
    (((measurable_const.sub measurable_id).div_const l).floor)
lemma Rf {l x s:ℝ} (hl:0< l) (hs:s∈ Set.Ioc x (x+l)) :
    bin l s x = -1:=by
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hl).mpr
    norm_num
    linarith [hs.2]
  · apply (div_lt_iff₀ hl).mpr
    norm_num
    linarith [hs.1]
lemma ND {l x y s:ℝ} (hl:0< l) (hxy:x≤ y)
    (hs:s∈ Set.Ioc x (x+l)):CM l s x y= if y< s then 1 else 0:=by
  have he:bin l s y = -1↔ y< s:=by
    simp only [bin,Int.floor_eq_iff]
    constructor
    · intro h
      have:=(div_lt_iff₀ hl).mp h.2
      norm_num at this
      linarith
    · intro h
      constructor
      · apply (le_div_iff₀ hl).mpr
        norm_num
        linarith [hs.2]
      · apply (div_lt_iff₀ hl).mpr
        norm_num
        linarith
  simp only [CM,Rf hl hs,eq_comm (a:=(-1:ℤ))]
  simp only [he]
lemma Ky {l:ℝ} (hl:0< l) (x y:ℝ) :
    (∫ s:ℝ in Set.Ioc 0 l,CM l s x y)= max 0 (l-|x-y|):=by
  wlog hxy:x≤ y
  · simpa only [Th l _ x y,abs_sub_comm x y] using this hl y x (le_of_not_ge hxy)
  have hp:=(MP hl x y).intervalIntegral_add_eq 0 x
  simp only [zero_add] at hp
  rw [intervalIntegral.integral_of_le hl.le,
    intervalIntegral.integral_of_le (by linarith:x≤ x+l)] at hp
  rw [hp]
  have he:(∫ s:ℝ in Set.Ioc x (x+l),CM l s x y) =
      ∫ s:ℝ in Set.Ioc x (x+l),if y< s then (1:ℝ) else 0:=by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact ND hl hxy hs
  rw [he]
  change (∫ s:ℝ in Set.Ioc x (x+l),(Set.Ioi y).indicator (fun _=>(1:ℝ)) s)= _
  rw [setIntegral_indicator measurableSet_Ioi]
  rw [show Set.Ioc x (x+l)∩ Set.Ioi y= Set.Ioc y (x+l) by
    ext s; simp only [Set.mem_inter_iff,Set.mem_Ioc,Set.mem_Ioi]; constructor
    · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨h₃,h₂⟩
    · intro h; exact ⟨⟨hxy.trans_lt h.1,h.2⟩,h.1⟩]
  rw [setIntegral_const]
  simp only [Measure.real,Real.volume_Ioc,smul_eq_mul,mul_one,ENNReal.toReal_ofReal']
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  rw [max_comm]
  congr 1
  ring
lemma Ia (l x y a b:ℝ) :
    IntegrableOn (fun s=> CM l s x y) (Set.Ioc a b):=by
  apply IntegrableOn.of_bound measure_Ioc_lt_top (GA l x y).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun s=> by unfold CM; split_ifs <;> norm_num)
lemma HJ {l:ℝ} (hl:0< l) {s x y:ℝ}
    (h:bin l s x= bin l s y) : |x-y| < l:=by
  have hx:=Int.floor_le ((x-s)/l)
  have hy:=Int.lt_floor_add_one ((y-s)/l)
  have hx':=Int.floor_le ((y-s)/l)
  have hy':=Int.lt_floor_add_one ((x-s)/l)
  change (bin l s x:ℝ)≤(x-s)/l at hx
  change (y-s)/l<(bin l s y:ℝ)+1 at hy
  change (bin l s y:ℝ)≤(y-s)/l at hx'
  change (x-s)/l<(bin l s x:ℝ)+1 at hy'
  rw [h] at hx hy'
  rw [abs_lt]
  constructor
  · have:(y-s)/l<(x-s)/l+1:=by linarith
    have hh:=(div_lt_iff₀ hl).mp this
    field_simp at hh
    linarith
  · have:(x-s)/l<(y-s)/l+1:=by linarith
    have hh:=(div_lt_iff₀ hl).mp this
    field_simp at hh
    linarith
lemma QN {l:ℝ} (hl:0< l) (s x:ℝ) (b:ℤ) :
    bin (2*l) (s+b*l) x=(bin l s x-b)/2:=by
  unfold bin
  rw [show (x-(s+b*l))/(2*l)=((x-s)/l-b)/2 by field_simp; ring]
  have hh:=Int.floor_div_natCast (((x-s)/l)-(b:ℝ)) 2
  norm_num only [Nat.cast_ofNat,Int.floor_sub_intCast] at hh
  exact hh
lemma Lw {l:ℝ} (hl:0< l) (s x y:ℝ) (b:ℤ)
    (h:bin l s x= bin l s y):bin (2*l) (s+b*l) x= bin (2*l) (s+b*l) y:=by
  rw [QN hl,QN hl,h]
def AI (l:ℝ):Measure ℝ :=
  (ENNReal.ofReal l)⁻¹• volume.restrict (Set.Ioc 0 l)
lemma Dd {l:ℝ} (hl:0< l) :
    IsProbabilityMeasure (AI l):=by
  constructor
  simp only [AI,Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter,Real.volume_Ioc,sub_zero,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hl)) ENNReal.ofReal_ne_top
instance Tj (l:ℝ):IsFiniteMeasure (AI l):=by
  by_cases hl:0< l
  · let:=Dd hl
    infer_instance
  · have hz:AI l=0:=by
      simp [AI,Set.Ioc_eq_empty_of_le (not_lt.mp hl)]
    rw [hz]
    infer_instance
lemma KW (l:ℝ) :
    (volume.restrict (Set.Ioc 0 l)).map (fun x=> x+l) =
      volume.restrict (Set.Ioc l (l+l)):=by
  have hh:=(measurePreserving_add_right volume l).restrict_preimage
    (measurableSet_Ioc (a:=l) (b:=l+l))
  have he:(fun x:ℝ=> x+l) ⁻¹' Set.Ioc l (l+l)= Set.Ioc 0 l:=by
    ext x
    simp only [Set.mem_preimage,Set.mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he] at hh
  exact hh.map_eq
open ProbabilityTheory in
def Fr (l:ℝ):Measure ℝ:=bernoulliMeasure 0 l ⟨1/2,by norm_num⟩
instance Lr (l:ℝ):IsProbabilityMeasure (Fr l):=by
  unfold Fr
  infer_instance
lemma MJ (l:ℝ) :
    Fr l=(2:ℝ≥0∞)⁻¹• Measure.dirac 0+(2:ℝ≥0∞)⁻¹• Measure.dirac l:=by
  simp only [Fr,ProbabilityTheory.bernoulliMeasure_def]
  rw [← Measure.coe_nnreal_smul,← Measure.coe_nnreal_smul]
  congr 2
  · rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ((1:ℝ)/2)= _
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  · rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (1-(1:ℝ)/2)= _
    norm_num only [show (1-(1:ℝ)/2)=1/2 by norm_num]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
lemma Rp {l:ℝ} (hl:0< l) :
    (AI l).conv (Fr l)= AI (2*l):=by
  rw [MJ,Measure.conv_add,Measure.conv_smul_right,
    Measure.conv_smul_right,Measure.conv_dirac_zero,Measure.conv_dirac]
  rw [AI,Measure.map_smul,KW]
  have hu:Set.Ioc 0 l∪ Set.Ioc l (l+l)= Set.Ioc 0 (2*l):=by
    rw [Set.Ioc_union_Ioc_eq_Ioc hl.le (by linarith)]
    congr 1; linarith
  have hd:Disjoint (Set.Ioc 0 l) (Set.Ioc l (l+l)) :=
    Set.disjoint_left.mpr (by intro x h₁ h₂; exact (not_lt_of_ge h₁.2) h₂.1)
  rw [smul_smul,smul_smul,← smul_add,← Measure.restrict_union hd measurableSet_Ioc,hu]
  congr 1
  rw [ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤2)]
  norm_num [ENNReal.mul_inv]
def DM:ℕ→ Measure ℝ
  | 0=> AI 1
  | n+1=> Fr (2^n)
instance Sv (n:ℕ):IsProbabilityMeasure (DM n):=by
  cases n with
  | zero=> exact Dd zero_lt_one
  | succ n=> exact Lr _
def Dt:Measure (ℕ→ ℝ):=Measure.infinitePi DM
instance Tz:IsProbabilityMeasure Dt:=by
  unfold Dt
  infer_instance
def shift (n:ℕ) (ω:ℕ→ ℝ):ℝ:=∑ i∈ Finset.range (n+1),ω i
lemma Cc (n:ℕ):Measurable (shift n):=by
  exact Finset.measurable_sum _ (fun i _=> measurable_pi_apply i)
lemma shift_zero (ω:ℕ→ ℝ):shift 0 ω= ω 0:=by simp [shift]
lemma MD (n:ℕ) (ω:ℕ→ ℝ) :
    shift (n+1) ω= shift n ω+ ω (n+1):=by simp [shift,Finset.sum_range_succ]
lemma RQ (n:ℕ):Dt.map (shift n)= AI (2^n):=by
  induction n with
  | zero =>
      simp only [pow_zero]
      rw [show shift 0=(fun ω=> ω 0) by funext ω; exact shift_zero ω]
      exact Measure.infinitePi_map_eval DM 0
  | succ n ih =>
      have hind:=ProbabilityTheory.iIndepFun_infinitePi
        (P:=DM) (X:=fun _=> id) (fun _=> measurable_id)
      have hi:=hind.indepFun_finsetSum_of_notMem
        (fun i=> measurable_pi_apply i) (s:=Finset.range (n+1)) (i:=n+1) (by simp)
      have he:(∑ j∈ Finset.range (n+1),(fun ω:ℕ→ ℝ=> id (ω j)))= shift n:=by
        funext ω
        simp [shift]
      rw [he] at hi
      have hm:=hi.map_add_eq_map_conv_map₀ (Cc n).aemeasurable
        (measurable_pi_apply (n+1)).aemeasurable
      change Dt.map (fun ω=> shift n ω+ ω (n+1))= _ at hm
      simp only [← MD] at hm
      change Dt.map (shift (n+1))=(Dt.map (shift n)).conv ((Measure.infinitePi DM).map (fun f=> f (n+1))) at hm
      rw [ih,Measure.infinitePi_map_eval DM (n+1)] at hm
      rw [DM,Rp (by positivity)] at hm
      simpa only [pow_succ,mul_comm (2^n) (2:ℝ)] using hm
lemma Kv {l:ℝ} (hl:0< l) (x y:ℝ) :
    (∫ s,CM l s x y ∂AI l)= max 0 (1-|x-y|/l):=by
  rw [AI,integral_smul_measure,Ky hl]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal hl.le,smul_eq_mul]
  rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hl.le),mul_zero]
  congr 1
  field_simp
lemma LQ (n:ℕ) (x y:ℝ) :
    (∫ ω,CM (2^n) (shift n ω) x y ∂Dt) =
      max 0 (1-|x-y|/(2^n)):=by
  rw [← integral_map (Cc n).aemeasurable
    (GA (2^n) x y).aestronglyMeasurable,RQ]
  exact Kv (by positivity) x y
lemma IF {l:ℝ} (hl:0< l) (k:ℕ) (x y:ℝ) :
    (∫ s in Set.Ioc 0 (k*l),CM l s x y)=(k:ℝ)*max 0 (l-|x-y|):=by
  have hh:=(MP hl x y).intervalIntegral_add_zsmul_eq (k:ℤ) 0
    (fun a b=>⟨Ia l x y a b,Ia l x y b a⟩)
  simp only [zero_add,zsmul_eq_mul,Int.cast_natCast,
    intervalIntegral.integral_of_le (by positivity:(0:ℝ)≤ k*l),
    intervalIntegral.integral_of_le hl.le,Ky hl] at hh
  exact hh
lemma MH (n:ℕ) (x y:ℝ) :
    (∫ ω,CM ((2:ℝ)^(- (n:ℤ))) (shift 0 ω) x y ∂Dt) =
      max 0 (1-|x-y|/((2:ℝ)^(- (n:ℤ)))):=by
  rw [← integral_map (Cc 0).aemeasurable
    (GA _ x y).aestronglyMeasurable,RQ]
  simp only [pow_zero,AI,ENNReal.ofReal_one,inv_one,one_smul]
  have hl:0<(2:ℝ)^(-(n:ℤ)):=by positivity
  have he:((2^n:ℕ):ℝ)*(2:ℝ)^(-(n:ℤ))=1:=by
    simp [zpow_neg,zpow_natCast]
  have hh:=IF hl (2^n) x y
  rw [he] at hh
  rw [hh,mul_max_of_nonneg _ _ (by positivity:(0:ℝ)≤((2^n:ℕ):ℝ)),mul_zero]
  congr 1
  simp only [Nat.cast_pow,Nat.cast_ofNat,zpow_neg,zpow_natCast,div_inv_eq_mul]
  field_simp
lemma Sr (l:ℝ):∀ᵐ x ∂Fr l,x=0∨ x= l:=by
  rw [MJ]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff (by measurability)).mpr (Or.inl rfl)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff (by measurability)).mpr (Or.inr rfl)
lemma OM (n:ℕ) :
    ∀ᵐ ω ∂Dt,ω (n+1)=0∨ ω (n+1)=(2:ℝ)^n:=by
  have hh:∀ᵐ x ∂DM (n+1),x=0∨ x=(2:ℝ)^n:=Sr _
  apply ae_of_ae_map (μ:=Dt) (f:=fun ω:ℕ→ ℝ=> ω (n+1))
    (p:=fun x:ℝ=> x=0∨ x=(2:ℝ)^n) (measurable_pi_apply (n+1)).aemeasurable
  simpa only [Dt,Measure.infinitePi_map_eval] using hh
lemma Ru (n:ℕ) (x y:ℝ) :
    ∀ᵐ ω ∂Dt,bin (2^n) (shift n ω) x= bin (2^n) (shift n ω) y →
      bin (2^(n+1)) (shift (n+1) ω) x= bin (2^(n+1)) (shift (n+1) ω) y:=by
  filter_upwards [OM n] with ω hω
  intro h
  rcases hω with hω | hω
  · simpa only [MD,hω,pow_succ,mul_comm (2^n) (2:ℝ),
      Int.cast_zero,zero_mul,add_zero] using Lw (by positivity) (shift n ω) x y 0 h
  · simpa only [MD,hω,pow_succ,mul_comm (2^n) (2:ℝ),
      Int.cast_one,one_mul] using Lw (by positivity) (shift n ω) x y 1 h
abbrev Bp:=(ℕ→ ℝ) × (ℕ→ ℝ)
def Aq:Measure Bp:=Dt.prod Dt
instance Tn:IsProbabilityMeasure Aq:=by
  unfold Aq
  infer_instance
def Cq (m:ℤ) (ω:ℕ→ ℝ):ℝ:=shift m.toNat ω
def Ar (m:ℤ) (ω:Bp) (x y:ℝ × ℝ):Prop :=
  bin ((2:ℝ)^m) (Cq m ω.1) x.1= bin ((2:ℝ)^m) (Cq m ω.1) y.1 ∧
  bin ((2:ℝ)^m) (Cq m ω.2) x.2= bin ((2:ℝ)^m) (Cq m ω.2) y.2
lemma Ds (m:ℤ) (x y:ℝ × ℝ) :
    MeasurableSet {ω | Ar m ω x y}:=by
  unfold Ar bin Cq
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      (((measurable_const.sub ((Cc _).comp measurable_fst)).div_const _).floor)
      (((measurable_const.sub ((Cc _).comp measurable_fst)).div_const _).floor)
  · exact measurableSet_eq_fun
      (((measurable_const.sub ((Cc _).comp measurable_snd)).div_const _).floor)
      (((measurable_const.sub ((Cc _).comp measurable_snd)).div_const _).floor)
lemma GR (m:ℤ) (x y:ℝ) :
    (∫ ω,CM ((2:ℝ)^m) (Cq m ω) x y ∂Dt) =
      max 0 (1-|x-y|/((2:ℝ)^m)):=by
  cases m with
  | ofNat n =>
      change (∫ ω,CM ((2:ℝ)^(n:ℤ)) (shift n ω) x y ∂Dt) =
        max 0 (1-|x-y|/((2:ℝ)^(n:ℤ)))
      simpa only [zpow_natCast] using LQ n x y
  | negSucc n =>
      simpa [Cq,Int.negSucc_eq,Int.toNat_of_nonpos] using
        MH (n+1) x y
lemma Ig (m:ℤ) (x y:ℝ × ℝ) :
    Aq.real {ω | Ar m ω x y} =
      max 0 (1-|x.1-y.1|/((2:ℝ)^m))* max 0 (1-|x.2-y.2|/((2:ℝ)^m)):=by
  rw [← integral_indicator_one (Ds m x y)]
  have he:(fun ω:Bp=> Set.indicator {ω | Ar m ω x y} 1 ω) =
      (fun ω=> CM ((2:ℝ)^m) (Cq m ω.1) x.1 y.1 *
        CM ((2:ℝ)^m) (Cq m ω.2) x.2 y.2):=by
    funext ω
    simp only [Set.indicator,Set.mem_ofPred_eq,Ar,CM,Pi.one_apply]
    by_cases h₁:bin ((2:ℝ)^m) (Cq m ω.1) x.1= bin ((2:ℝ)^m) (Cq m ω.1) y.1 <;>
      by_cases h₂:bin ((2:ℝ)^m) (Cq m ω.2) x.2= bin ((2:ℝ)^m) (Cq m ω.2) y.2 <;>
      simp [h₁,h₂]
  rw [he,Aq,integral_prod_mul (fun ω:ℕ→ ℝ=> CM ((2:ℝ)^m) (Cq m ω) x.1 y.1)
    (fun ω:ℕ→ ℝ=> CM ((2:ℝ)^m) (Cq m ω) x.2 y.2),
    GR,GR]
lemma Pf {a b:ℝ} (ha:0≤ a) (hb:0≤ b) :
    1 - max 0 (1-a)* max 0 (1-b)≤ a+b:=by
  by_cases ha':a≤1
  · by_cases hb':b≤1
    · rw [max_eq_right (by linarith),max_eq_right (by linarith)]
      nlinarith [mul_nonneg ha hb]
    · rw [max_eq_left (show 1-b≤0 by linarith)]
      nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith
lemma FK (m:ℤ) (x y:ℝ × ℝ) :
    Aq.real {ω | ¬ Ar m ω x y} ≤
      (|x.1-y.1|+|x.2-y.2|)/((2:ℝ)^m):=by
  change Aq.real {ω | Ar m ω x y}ᶜ≤ _
  rw [measureReal_compl (Ds m x y),probReal_univ,
    Ig,add_div]
  exact Pf (by positivity) (by positivity)
lemma Db (x y:ℝ × ℝ) :
    ∀ᵐ ω ∂Aq,∃ n:ℕ,Ar n ω x y:=by
  rw [ae_iff]
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ (measureReal_nonneg)
  have hb (n:ℕ):Aq.real {ω | ¬ ∃ n:ℕ,Ar n ω x y} ≤
      (|x.1-y.1|+|x.2-y.2|)/((2:ℝ)^n):=by
    refine (measureReal_mono (s₂:={ω | ¬ Ar (n:ℤ) ω x y})
      (by intro ω h hn; exact h ⟨n,hn⟩)).trans ?_
    simpa only [zpow_natCast] using FK (n:ℤ) x y
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num:(1:ℝ)<2))) hb
lemma KD (m:ℤ) (x y:ℝ) :
    ∀ᵐ ω ∂Dt,bin ((2:ℝ)^m) (Cq m ω) x= bin ((2:ℝ)^m) (Cq m ω) y →
      bin ((2:ℝ)^(m+1)) (Cq (m+1) ω) x= bin ((2:ℝ)^(m+1)) (Cq (m+1) ω) y:=by
  by_cases hm:0≤ m
  · obtain ⟨n,rfl⟩:=Int.eq_ofNat_of_zero_le hm
    rw [show (n:ℤ)+1=((n+1:ℕ):ℤ) by omega]
    simpa only [Cq,Int.toNat_natCast,zpow_natCast] using Ru n x y
  · have hm':m+1≤0:=by omega
    filter_upwards with ω
    intro h
    simp only [Cq,Int.toNat_of_nonpos (by omega:m≤0)] at h
    have hh:=Lw (by positivity:0<(2:ℝ)^m) (shift 0 ω) x y 0
    simpa only [Cq,Int.toNat_of_nonpos (by omega:m≤0),
      Int.toNat_of_nonpos hm',zpow_add₀ (by norm_num:(2:ℝ)≠0),zpow_one,
      mul_comm ((2:ℝ)^m) (2:ℝ),Int.cast_zero,zero_mul,add_zero] using hh h
lemma EX (m:ℤ) (x y:ℝ × ℝ) :
    ∀ᵐ ω ∂Aq,Ar m ω x y→ Ar (m+1) ω x y:=by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (KD m x.1 y.1),
    Measure.quasiMeasurePreserving_snd.ae (KD m x.2 y.2)] with ω hx hy
  exact fun h=>⟨hx h.1,hy h.2⟩
lemma SK (m:ℤ) (ω:Bp) (x y:ℝ × ℝ) :
    Ar m ω x y↔ Ar m ω y x:=by simp [Ar,eq_comm]
lemma Sl (m:ℤ) (ω:Bp) (x y z:ℝ × ℝ)
    (hxy:Ar m ω x y) (hyz:Ar m ω y z):Ar m ω x z :=
  ⟨hxy.1.trans hyz.1,hxy.2.trans hyz.2⟩
lemma JE (ω:Bp) {x y:ℝ × ℝ} (hxy:x≠ y) :
    BddBelow {m:ℤ | Ar m ω x y}:=by
  have bound {a b:ℝ} (h:a≠ b) (f:ℤ→ ℝ) :
      BddBelow {m:ℤ | bin ((2:ℝ)^m) (f m) a= bin ((2:ℝ)^m) (f m) b}:=by
    obtain ⟨k,hk⟩:=exists_mem_Ico_zpow (abs_pos.mpr (sub_ne_zero.mpr h)) (by norm_num:(1:ℝ)<2)
    refine ⟨k,fun m hm => ?_⟩
    have hh:=HJ (by positivity:0<(2:ℝ)^m) hm
    exact (zpow_le_zpow_iff_right₀ (by norm_num:(1:ℝ)<2)).mp (hk.1.trans hh.le)
  by_cases h₁:x.1= y.1
  · have h₂:x.2≠ y.2:=fun h₂=> hxy (Prod.ext h₁ h₂)
    exact (bound h₂ (fun m=> Cq m ω.2)).mono (fun _ h=> h.2)
  · exact (bound h₁ (fun m=> Cq m ω.1)).mono (fun _ h=> h.1)
def AX (ω:Bp) (x y:ℝ × ℝ):ℤ:=sInf {m | Ar m ω x y}
def AH (ω:Bp) (x y:ℝ × ℝ):ℝ :=
  -(AX ω x y:ℝ)* Real.log 2
lemma Sk (ω:Bp) (x y:ℝ × ℝ) :
    AX ω x y= AX ω y x:=by
  unfold AX
  congr 1
  ext m
  exact SK m ω x y
lemma JV {ω:Bp} {x y:ℝ × ℝ} (hxy:x≠ y)
    (he:∃ m,Ar m ω x y):Ar (AX ω x y) ω x y :=
  Int.csInf_mem he (JE ω hxy)
lemma GM {ω:Bp} {x y:ℝ × ℝ} (hxy:x≠ y)
    {m:ℤ} (hm:Ar m ω x y):AX ω x y≤ m :=
  csInf_le (JE ω hxy) hm
lemma DF {ω:Bp} {x y:ℝ × ℝ} (hxy:x≠ y)
    (he:∃ m,Ar m ω x y)
    (hn:∀ m,Ar m ω x y→ Ar (m+1) ω x y) (m:ℤ) :
    Ar m ω x y↔ AX ω x y≤ m:=by
  constructor
  · exact GM hxy
  · intro hm
    have hmono:Monotone (fun k=> Ar k ω x y):=monotone_int_of_le_succ hn
    exact hmono hm (JV hxy he)
lemma KA {ω:Bp} {x y:ℝ × ℝ} (hxy:x≠ y) (m:ℤ) :
    AX ω x y= m ↔
      (Ar m ω x y∧∀ k:ℤ,k< m→¬ Ar k ω x y) ∨
      (m=0∧¬ ∃ k:ℤ,Ar k ω x y):=by
  by_cases he:∃ k,Ar k ω x y
  · have hs:=JV hxy he
    constructor
    · intro h
      left
      rw [h] at hs
      refine ⟨hs,fun k hk hks => ?_⟩
      have hh:=GM hxy hks
      omega
    · rintro (⟨hm,hmin⟩ | ⟨_,hn⟩)
      · apply le_antisymm (GM hxy hm)
        by_contra h
        exact hmin _ (by omega) hs
      · exact False.elim (hn he)
  · have hz:AX ω x y=0:=by
      unfold AX
      rw [show {m | Ar m ω x y}=∅ by ext m; simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false]; exact iff_false_intro (fun h=> he ⟨m,h⟩)]
      exact Int.csInf_empty
    simp only [hz]
    constructor
    · intro hm
      exact Or.inr ⟨hm.symm,he⟩
    · rintro (⟨hm,_⟩ | ⟨rfl,_⟩)
      · exact False.elim (he ⟨m,hm⟩)
      · rfl
lemma Ce {x y:ℝ × ℝ} (hxy:x≠ y) :
    Measurable (fun ω=> AX ω x y):=by
  apply measurable_to_countable'
  intro m
  change MeasurableSet {ω | AX ω x y= m}
  have he:{ω:Bp | AX ω x y= m} =
      ({ω | Ar m ω x y}∩{ω | ∀ k< m,¬Ar k ω x y}) ∪
      ({ω | m=0}∩{ω | ¬∃ k,Ar k ω x y}):=by
    ext ω
    exact KA hxy m
  rw [he]
  apply MeasurableSet.union
  · apply (Ds m x y).inter
    have he:{ω:Bp | ∀ k< m,¬Ar k ω x y} =
        ⋂ k:ℤ,⋂ (_:k< m),{ω:Bp | Ar k ω x y}ᶜ:=by
      ext ω
      simp
    rw [he]
    exact MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun (_:k< m)=>(Ds k x y).compl
  · apply (MeasurableSet.const (m=0)).inter
    have he:{ω:Bp | ¬∃ k,Ar k ω x y} =
        (⋃ k:ℤ,{ω:Bp | Ar k ω x y})ᶜ:=by
      ext ω
      simp
    rw [he]
    exact (MeasurableSet.iUnion fun k=> Ds k x y).compl
lemma HQ {x y:ℝ × ℝ} (hxy:x≠ y) :
    Measurable (fun ω=> AH ω x y):=by
  exact (((measurable_of_countable (fun n:ℤ=>(n:ℝ))).comp (Ce hxy)).neg).mul_const _
lemma Oh {x y z:ℝ × ℝ} (hxy:x≠ y) (hyz:y≠ z) (hxz:x≠ z) :
    ∀ᵐ ω ∂Aq,min (AH ω x y) (AH ω y z)≤ AH ω x z:=by
  have hn:∀ᵐ ω ∂Aq,∀ m:ℤ,
      (Ar m ω x y→ Ar (m+1) ω x y) ∧
      (Ar m ω y z→ Ar (m+1) ω y z):=by
    rw [ae_all_iff]
    intro m
    filter_upwards [EX m x y,EX m y z] with ω h₁ h₂ using ⟨h₁,h₂⟩
  filter_upwards [Db x y,Db y z,hn] with ω h₁ h₂ hn
  have e₁:∃ m:ℤ,Ar m ω x y:=by obtain ⟨n,hn⟩:=h₁; exact ⟨n,hn⟩
  have e₂:∃ m:ℤ,Ar m ω y z:=by obtain ⟨n,hn⟩:=h₂; exact ⟨n,hn⟩
  have hm:AX ω x z≤ max (AX ω x y) (AX ω y z):=by
    apply GM hxz
    apply Sl _ ω x y z
    · exact (DF hxy e₁ (fun m=>(hn m).1) _).mpr (le_max_left _ _)
    · exact (DF hyz e₂ (fun m=>(hn m).2) _).mpr (le_max_right _ _)
  have hlog:0< Real.log 2:=Real.log_pos (by norm_num)
  unfold AH
  have hm':(AX ω x z:ℝ)≤ max (AX ω x y:ℝ) (AX ω y z:ℝ):=by exact_mod_cast hm
  by_cases hl:(AX ω x y:ℝ)≤ AX ω y z
  · rw [max_eq_right hl] at hm'
    apply (min_le_right _ _).trans
    nlinarith
  · rw [max_eq_left (le_of_not_ge hl)] at hm'
    apply (min_le_left _ _).trans
    nlinarith
lemma Rw {x y:ℝ × ℝ} (hxy:x≠ y) {R:ℝ} (hR:0< R)
    (hgap:R ≤ |x.1-y.1|+|x.2-y.2|) :
    ∀ᵐ ω ∂Aq,AH ω x y+ Real.log R≤ Real.log 2:=by
  filter_upwards [Db x y] with ω he
  obtain ⟨n,hn⟩:=he
  have hs:=JV hxy ⟨n,hn⟩
  have h₁:=HJ (by positivity:0<(2:ℝ)^(AX ω x y)) hs.1
  have h₂:=HJ (by positivity:0<(2:ℝ)^(AX ω x y)) hs.2
  have hr:R≤2*(2:ℝ)^(AX ω x y):=by linarith
  have hh:=Real.log_le_log hR hr
  rw [Real.log_mul (by norm_num:(2:ℝ)≠0) (by positivity),Real.log_zpow] at hh
  unfold AH
  linarith
lemma PE {x y:ℝ × ℝ} (hxy:x≠ y) {R:ℝ} (hR:0< R)
    (hgap : |x.1-y.1|+|x.2-y.2| ≤ 2*R) (u:ℝ) :
    Aq.real {ω | AH ω x y+ Real.log R < -u}≤4*Real.exp (-u):=by
  obtain ⟨m,hm⟩:=exists_mem_Ico_zpow (mul_pos hR (Real.exp_pos u))
    (by norm_num:(1:ℝ)<2)
  have hl:0< Real.log 2:=Real.log_pos (by norm_num)
  have hm₁:(m:ℝ)*Real.log 2≤ Real.log R+ u:=by
    have hh:=Real.log_le_log (by positivity:0<(2:ℝ)^m) hm.1
    rw [Real.log_zpow,Real.log_mul hR.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
    exact hh
  have hsub:{ω | AH ω x y+ Real.log R < -u} ⊆
      {ω | ¬Ar m ω x y}:=by
    intro ω hω hs
    have hk:(AX ω x y:ℝ)≤(m:ℝ):=by exact_mod_cast GM hxy hs
    have:=mul_le_mul_of_nonneg_right hk hl.le
    change AH ω x y+ Real.log R < -u at hω
    unfold AH at hω
    linarith
  refine (measureReal_mono hsub).trans ((FK m x y).trans ?_)
  have hpow:0<(2:ℝ)^m:=by positivity
  have hm₂:R*Real.exp u<2*(2:ℝ)^m:=by
    simpa only [zpow_add₀ (by norm_num:(2:ℝ)≠0),zpow_one,mul_comm] using hm.2
  apply (div_le_iff₀ hpow).mpr
  have hex:Real.exp u* Real.exp (-u)=1:=by rw [← Real.exp_add]; simp
  have hh:=mul_le_mul_of_nonneg_right hm₂.le (Real.exp_nonneg (-u))
  nlinarith
lemma Ly {x y:ℝ × ℝ} (hxy:x≠ y) {R:ℝ} (hR:0< R)
    (hgap₁:R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) {u:ℝ} (_hu:0≤ u) :
    Aq.real {ω | u < |AH ω x y+ Real.log R|}≤4*Real.exp (-u):=by
  by_cases hsmall:u≤ Real.log 2
  · have hp:Aq.real {ω | u < |AH ω x y+ Real.log R|}≤1 :=
      measureReal_le_one
    have hex:(1:ℝ)/2≤ Real.exp (-u):=by
      have:=Real.exp_le_exp.mpr (neg_le_neg hsmall)
      rw [Real.exp_neg,Real.exp_log (by norm_num:(0:ℝ)<2)] at this
      simpa only [one_div] using this
    linarith
  · have hle:Aq.real {ω | u < |AH ω x y+ Real.log R|} ≤
        Aq.real {ω | AH ω x y+ Real.log R < -u}:=by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono_ae
      filter_upwards [Rw hxy hR hgap₁] with ω hω
      intro hh
      rcases lt_abs.mp hh with hh | hh
      · exact False.elim (hsmall (hh.le.trans hω))
      · change AH ω x y+ Real.log R < -u
        linarith
    exact hle.trans (PE hxy hR hgap₂ u)
lemma GN {x y:ℝ × ℝ} (hxy:x≠ y) {R:ℝ} (hR:0< R)
    (hgap₁:R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    (∫⁻ ω,ENNReal.ofReal |AH ω x y+ Real.log R| ∂Aq)≤ ENNReal.ofReal 4:=by
  rw [lintegral_eq_lintegral_meas_lt Aq
    (by filter_upwards with ω; exact abs_nonneg _)
    (((HQ hxy).add_const _).abs.aemeasurable)]
  have he:IntegrableOn (fun u:ℝ=>4* Real.exp (-u)) (Set.Ioi 0) volume:=by
    change Integrable (fun u:ℝ=>4* Real.exp (-u)) (volume.restrict (Set.Ioi 0))
    simpa only [neg_one_mul] using (integrableOn_exp_mul_Ioi (by norm_num:(-1:ℝ)<0) 0).const_mul 4
  calc
    _≤∫⁻ u:ℝ in Set.Ioi 0,ENNReal.ofReal (4*Real.exp (-u)):=by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [← ENNReal.ofReal_toReal (measure_ne_top Aq _)]
      exact ENNReal.ofReal_le_ofReal (Ly hxy hR hgap₁ hgap₂ hu.le)
    _= ENNReal.ofReal 4:=by
      rw [← ofReal_integral_eq_lintegral_ofReal he (by filter_upwards with u; positivity)]
      congr 1
      rw [integral_const_mul]
      have hi:=integral_exp_mul_Ioi (by norm_num:(-1:ℝ)<0) (0:ℝ)
      simp only [neg_one_mul,mul_zero,Real.exp_zero,neg_div_neg_eq,div_one] at hi
      rw [hi]
      norm_num
lemma Hd {x y:ℝ × ℝ} (hxy:x≠ y) {R:ℝ} (hR:0< R)
    (hgap₁:R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    Integrable (fun ω=> AH ω x y+ Real.log R) Aq:=by
  have hm:AEStronglyMeasurable (fun ω=> AH ω x y+ Real.log R) Aq :=
    ((HQ hxy).add_const (Real.log R)).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  refine ⟨hm.norm,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (by filter_upwards with ω; exact norm_nonneg _)).mpr
  simpa only [Real.norm_eq_abs] using
    (GN hxy hR hgap₁ hgap₂).trans_lt ENNReal.ofReal_lt_top
lemma Je {x y:ℝ × ℝ} (hxy:x≠ y) {R:ℝ} (hR:0< R)
    (hgap₁:R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    (∫ ω,|AH ω x y+ Real.log R| ∂Aq)≤4:=by
  have hi:=(Hd hxy hR hgap₁ hgap₂).abs
  have hh:=GN hxy hR hgap₁ hgap₂
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with ω; exact abs_nonneg _)] at hh
  have hh':=ENNReal.toReal_mono (by simp:ENNReal.ofReal (4:ℝ)≠⊤) hh
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun ω=> abs_nonneg _),
    ENNReal.toReal_ofReal (by norm_num:(0:ℝ)≤4)] using hh'
lemma HB {x y:ℝ × ℝ} (hxy:x≠ y) (m:ℤ) :
    Aq.real {ω | AX ω x y≤ m} =
      max 0 (1-|x.1-y.1|/((2:ℝ)^m))* max 0 (1-|x.2-y.2|/((2:ℝ)^m)):=by
  have hn:∀ᵐ ω ∂Aq,∀ k:ℤ,Ar k ω x y→ Ar (k+1) ω x y:=by
    rw [ae_all_iff]
    exact fun k=> EX k x y
  have he:{ω | AX ω x y≤ m} =ᵐ[Aq] {ω | Ar m ω x y}:=by
    filter_upwards [Db x y,hn] with ω he hn
    apply propext
    obtain ⟨n,hn'⟩:=he
    exact (DF hxy ⟨n,hn'⟩ hn m).symm
  rw [measureReal_def,measure_congr he]
  exact Ig m x y
lemma Lk {x y x' y':ℝ × ℝ} (hxy:x≠ y) (hxy':x'≠ y')
    (h₁ : |x.1-y.1| = |x'.1-y'.1|) (h₂ : |x.2-y.2| = |x'.2-y'.2|) :
    Measure.map (fun ω=> AX ω x y) Aq =
      Measure.map (fun ω=> AX ω x' y') Aq:=by
  apply Measure.ext_of_Iic
  intro m
  rw [Measure.map_apply (Ce hxy) measurableSet_Iic,
    Measure.map_apply (Ce hxy') measurableSet_Iic]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change Aq.real {ω | AX ω x y≤ m}= Aq.real {ω | AX ω x' y'≤ m}
  rw [HB hxy,HB hxy',h₁,h₂]
lemma Mn {x y x' y':ℝ × ℝ} (hxy:x≠ y) (hxy':x'≠ y')
    (h₁ : |x.1-y.1| = |x'.1-y'.1|) (h₂ : |x.2-y.2| = |x'.2-y'.2|) :
    (∫ ω,AH ω x y ∂Aq)=∫ ω,AH ω x' y' ∂Aq:=by
  have hf:Measurable (fun n:ℤ => -(n:ℝ)*Real.log 2):=measurable_of_countable _
  unfold AH
  rw [← integral_map (Ce hxy).aemeasurable hf.aestronglyMeasurable,
      ← integral_map (Ce hxy').aemeasurable hf.aestronglyMeasurable,
      Lk hxy hxy' h₁ h₂]
lemma MX {x y:ℝ × ℝ} (hxy:x≠ y) :
    Measure.map (fun ω=> AX ω (2*x.1,2*x.2) (2*y.1,2*y.2)) Aq =
      Measure.map (fun ω=> AX ω x y+1) Aq:=by
  have hd:(2*x.1,2*x.2)≠(2*y.1,2*y.2):=by
    intro h
    apply hxy
    have h₁:=congrArg Prod.fst h
    have h₂:=congrArg Prod.snd h
    apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> linarith
  apply Measure.ext_of_Iic
  intro m
  rw [Measure.map_apply (Ce hd) measurableSet_Iic,
    Measure.map_apply ((Ce hxy).add_const 1) measurableSet_Iic]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change Aq.real {ω | AX ω (2*x.1,2*x.2) (2*y.1,2*y.2)≤ m} =
    Aq.real {ω | AX ω x y+1≤ m}
  rw [show {ω | AX ω x y+1≤ m}={ω | AX ω x y≤ m-1} by ext ω; simp only [Set.mem_ofPred_eq]; omega,
    HB hd,HB hxy]
  have hpow:(2:ℝ)^(m-1)=(2:ℝ)^m/2:=by rw [zpow_sub₀ (by norm_num),zpow_one]
  have hq (a b:ℝ) : |2*a-2*b| / (2:ℝ)^m = |a-b| / ((2:ℝ)^m/2):=by
    rw [← mul_sub,abs_mul]
    norm_num
    ring
  rw [hpow,hq x.1 y.1,hq x.2 y.2]
lemma Fo {x y:ℝ × ℝ} (hxy:x≠ y) :
    Integrable (fun ω=> AH ω x y) Aq:=by
  let R := |x.1-y.1|+|x.2-y.2|
  have hR:0< R:=by
    by_cases h₁:x.1= y.1
    · have h₂:x.2≠ y.2:=fun h₂=> hxy (Prod.ext h₁ h₂)
      exact add_pos_of_nonneg_of_pos (abs_nonneg _) (abs_pos.mpr (sub_ne_zero.mpr h₂))
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr (sub_ne_zero.mpr h₁)) (abs_nonneg _)
  have hi:=Hd hxy hR (le_refl R) (by linarith:R≤2*R)
  have hh:=hi.sub (integrable_const (Real.log R))
  change Integrable (fun ω=>(AH ω x y+ Real.log R) - Real.log R) Aq at hh
  simpa only [add_sub_cancel_right] using hh
lemma OG {x y:ℝ × ℝ} (hxy:x≠ y) :
    (∫ ω,AH ω (2*x.1,2*x.2) (2*y.1,2*y.2) ∂Aq) =
      (∫ ω,AH ω x y ∂Aq) - Real.log 2:=by
  have hd:(2*x.1,2*x.2)≠(2*y.1,2*y.2):=by
    intro h
    apply hxy
    have h₁:=congrArg Prod.fst h
    have h₂:=congrArg Prod.snd h
    apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> linarith
  have hid:ProbabilityTheory.IdentDistrib
      (fun ω=> AX ω (2*x.1,2*x.2) (2*y.1,2*y.2))
      (fun ω=> AX ω x y+1) Aq Aq :=
    ⟨(Ce hd).aemeasurable,
      ((Ce hxy).add_const 1).aemeasurable,MX hxy⟩
  have hh:=(hid.comp (measurable_of_countable (fun n:ℤ => -(n:ℝ)*Real.log 2))).integral_eq
  change (∫ ω,AH ω (2*x.1,2*x.2) (2*y.1,2*y.2) ∂Aq)= _ at hh
  rw [hh]
  calc
    _=∫ ω,AH ω x y - Real.log 2 ∂Aq:=by
      apply integral_congr_ae
      filter_upwards with ω
      simp [AH]
      ring
    _= _:=by rw [integral_sub (Fo hxy) (integrable_const _)]; simp
lemma Dc {T:Type u1} [MeasurableSpace T]
    {W:T→ Bp} {X Y:T→ ℝ × ℝ}
    (hW:Measurable W) (hX:Measurable X) (hY:Measurable Y) (m:ℤ) :
    MeasurableSet {t | Ar m (W t) (X t) (Y t)}:=by
  unfold Ar bin Cq
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      ((hX.fst.sub ((Cc _).comp hW.fst)).div_const _).floor
      ((hY.fst.sub ((Cc _).comp hW.fst)).div_const _).floor
  · exact measurableSet_eq_fun
      ((hX.snd.sub ((Cc _).comp hW.snd)).div_const _).floor
      ((hY.snd.sub ((Cc _).comp hW.snd)).div_const _).floor
lemma Ju {T:Type u2} [MeasurableSpace T]
    {W:T→ Bp} {X Y:T→ ℝ × ℝ}
    (hW:Measurable W) (hX:Measurable X) (hY:Measurable Y) (hne:∀ t,X t≠ Y t) :
    Measurable (fun t=> AX (W t) (X t) (Y t)):=by
  apply measurable_to_countable'
  intro m
  change MeasurableSet {t | AX (W t) (X t) (Y t)= m}
  have he:{t | AX (W t) (X t) (Y t)= m} =
      ({t | Ar m (W t) (X t) (Y t)} ∩
        ⋂ k:ℤ,⋂ (_:k< m),{t | Ar k (W t) (X t) (Y t)}ᶜ) ∪
      ({t | m=0}∩(⋃ k:ℤ,{t | Ar k (W t) (X t) (Y t)})ᶜ):=by
    ext t
    simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_inter_iff,Set.mem_iInter,
      Set.mem_compl_iff,Set.mem_iUnion]
    exact KA (hne t) m
  rw [he]
  exact ((Dc hW hX hY m).inter
    (MeasurableSet.iInter fun k=> MeasurableSet.iInter fun (_:k< m) =>
      (Dc hW hX hY k).compl)).union
    ((MeasurableSet.const (m=0)).inter (MeasurableSet.iUnion fun k =>
      Dc hW hX hY k).compl)
lemma Fz {T:Type u3} [MeasurableSpace T]
    {W:T→ Bp} {X Y:T→ ℝ × ℝ}
    (hW:Measurable W) (hX:Measurable X) (hY:Measurable Y) (hne:∀ t,X t≠ Y t) :
    Measurable (fun t=> AH (W t) (X t) (Y t)):=by
  exact (((measurable_of_countable (fun n:ℤ=>(n:ℝ))).comp
    (Ju hW hX hY hne)).neg).mul_const _
def BQ (t θ:ℝ):ℝ × ℝ:=(Real.exp t* Real.cos θ,Real.exp t* Real.sin θ)
def CB (t θ:ℝ):ℝ :=
  (∫ ω,AH ω (0,0) (BQ t θ) ∂Aq)+ t
lemma DX (t θ:ℝ):(0,0)≠ BQ t θ:=by
  intro h
  have he:Real.exp t≠0:=Real.exp_ne_zero t
  have h₁:Real.cos θ=0:=(mul_eq_zero.mp (congrArg Prod.fst h).symm).resolve_left he
  have h₂:Real.sin θ=0:=(mul_eq_zero.mp (congrArg Prod.snd h).symm).resolve_left he
  have hh:=Real.sin_sq_add_cos_sq θ
  rw [h₁,h₂] at hh
  norm_num at hh
lemma Rx (t θ:ℝ) :
    Real.exp t ≤ |(BQ t θ).1|+|(BQ t θ).2| ∧
    |(BQ t θ).1|+|(BQ t θ).2| ≤ 2*Real.exp t:=by
  have hsum:1 ≤ |Real.cos θ|+|Real.sin θ| := by
    have hsq:=Real.sin_sq_add_cos_sq θ
    have hpos:=mul_nonneg (abs_nonneg (Real.cos θ)) (abs_nonneg (Real.sin θ))
    have hc:=abs_nonneg (Real.cos θ)
    have hs:=abs_nonneg (Real.sin θ)
    nlinarith [sq_abs (Real.cos θ),sq_abs (Real.sin θ)]
  have hsum' : |Real.cos θ|+|Real.sin θ| ≤ 2:=by
    linarith [Real.abs_cos_le_one θ,Real.abs_sin_le_one θ]
  simp only [BQ,abs_mul,abs_of_pos (Real.exp_pos t)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg t)]
  · nlinarith [mul_le_mul_of_nonneg_left hsum' (Real.exp_nonneg t)]
lemma Ob (t θ:ℝ) :
    CB t θ=∫ ω,AH ω (0,0) (BQ t θ)+ t ∂Aq:=by
  rw [integral_add (Fo (DX t θ)) (integrable_const _)]
  simp [CB]
lemma Qp (t θ:ℝ) : |CB t θ| ≤ 4:=by
  rw [Ob]
  have hg:=Rx t θ
  have hh:=Je (DX t θ) (Real.exp_pos t)
    (by simpa only [zero_sub,abs_neg] using hg.1)
    (by simpa only [zero_sub,abs_neg] using hg.2)
  rw [Real.log_exp] at hh
  have hb : |∫ ω,AH ω (0,0) (BQ t θ)+ t ∂Aq| ≤
      ∫ ω,|AH ω (0,0) (BQ t θ)+ t| ∂Aq:=by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
      (f:=fun ω=> AH ω (0,0) (BQ t θ)+ t) (μ:=Aq))
  exact hb.trans hh
lemma Mk:Measurable (fun p:ℝ × ℝ=> BQ p.1 p.2):=by
  exact (measurable_fst.exp.mul measurable_snd.cos).prodMk
    (measurable_fst.exp.mul measurable_snd.sin)
lemma Mr:Measurable (fun p:ℝ × ℝ=> CB p.1 p.2):=by
  have hm:Measurable (fun p:(ℝ × ℝ) × Bp =>
      AH p.2 (0,0) (BQ p.1.1 p.1.2)) :=
    Fz measurable_snd measurable_const
      (Mk.comp measurable_fst) (fun p=> DX _ _)
  have hi:StronglyMeasurable (fun p:ℝ × ℝ=>∫ ω,
      AH ω (0,0) (BQ p.1 p.2) ∂Aq) :=
    hm.stronglyMeasurable.integral_prod_right
  exact hi.measurable.add measurable_fst
lemma Qm (t θ:ℝ):BQ (t+Real.log 2) θ =
    (2*(BQ t θ).1,2*(BQ t θ).2):=by
  simp only [BQ,Real.exp_add,Real.exp_log (by norm_num:(0:ℝ)<2)]
  congr 1 <;> ring
lemma KT (θ:ℝ):Function.Periodic (fun t=> CB t θ) (Real.log 2):=by
  intro t
  have hm:=OG (DX t θ)
  simp only [mul_zero] at hm
  simp only [CB,Qm,hm]
  ring
lemma Lu (t:ℝ):Function.Periodic (CB t) (2*Real.pi):=by
  intro θ
  simp only [CB,BQ,Real.cos_periodic θ,Real.sin_periodic θ]
lemma Gd {l:ℝ} (hl:0< l) (f:ℝ→ ℝ) :
    (∫ x,f x ∂AI l)= l⁻¹*∫ x in (0:ℝ)..l,f x:=by
  rw [AI,integral_smul_measure,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hl.le,smul_eq_mul,intervalIntegral.integral_of_le hl.le]
lemma Ff {l:ℝ} (hl:0< l) {f:ℝ→ ℝ}
    (hf:Function.Periodic f l) (a:ℝ) :
    (∫ x,f (x+a) ∂AI l)=∫ x,f x ∂AI l:=by
  rw [Gd hl,Gd hl,
    intervalIntegral.integral_comp_add_right]
  congr 1
  simpa only [zero_add,add_comm l a] using hf.intervalIntegral_add_eq a 0
lemma Jc {l:ℝ} (hl:0< l) {f:ℝ→ ℝ}
    (hf:Function.Periodic f l) (a:ℝ) :
    (∫ x,f (a-x) ∂AI l)=∫ x,f (-x) ∂AI l:=by
  have hp:Function.Periodic (fun x=> f (-x)) l:=by
    intro x
    simpa only [neg_add,sub_eq_add_neg] using hf.sub_eq (-x)
  have hh:=Ff hl hp (-a)
  simpa only [neg_add,neg_neg,sub_eq_add_neg,add_comm] using hh
def Mu:ℝ:=∫ ξ,∫ θ,CB (-ξ) θ
  ∂AI (2*Real.pi) ∂AI (Real.log 2)
lemma Lg (t φ:ℝ) :
    (∫ ξ,∫ θ,CB (t-ξ) (θ+φ)
      ∂AI (2*Real.pi) ∂AI (Real.log 2))= Mu:=by
  simp_rw [Ff (by positivity:0<2*Real.pi)
    (Lu _) φ]
  have hp:Function.Periodic
      (fun t=>∫ θ,CB t θ ∂AI (2*Real.pi)) (Real.log 2):=by
    intro x
    apply integral_congr_ae
    filter_upwards with θ
    exact KT θ x
  exact Jc (Real.log_pos (by norm_num)) hp t
def Dg (ξ θ:ℝ) (z:ℂ):ℂ :=
  (Real.exp (-ξ):ℂ)* Complex.exp ((θ:ℂ)*Complex.I)* z
def Am (ξ θ:ℝ) (z:ℂ):ℝ × ℝ :=
  ((Dg ξ θ z).re,(Dg ξ θ z).im)
lemma GU (ξ θ:ℝ) (z w:ℂ) :
    Dg ξ θ (z-w)= Dg ξ θ z - Dg ξ θ w:=by
  exact mul_sub _ _ _
lemma HC (ξ θ:ℝ) (z:ℂ) :
    ‖Dg ξ θ z‖= Real.exp (-ξ)*‖z‖:=by
  simp only [Dg,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),Complex.norm_exp_ofReal_mul_I,mul_one]
lemma CT (ξ θ:ℝ) {z w:ℂ} (hne:z≠ w) :
    Am ξ θ z≠ Am ξ θ w:=by
  intro he
  have h:Dg ξ θ z= Dg ξ θ w:=Complex.ext
    (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hn:=HC ξ θ (z-w)
  rw [GU,h,sub_self,norm_zero] at hn
  have hz:‖z-w‖≠0:=norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  exact (mul_ne_zero (Real.exp_ne_zero _) hz) hn.symm
lemma Dz (ξ θ:ℝ) (z w:ℂ) :
    Real.exp (-ξ)*‖z-w‖ ≤
      |(Am ξ θ z).1-(Am ξ θ w).1| +
      |(Am ξ θ z).2-(Am ξ θ w).2| ∧
    |(Am ξ θ z).1-(Am ξ θ w).1| +
      |(Am ξ θ z).2-(Am ξ θ w).2| ≤ 2*(Real.exp (-ξ)*‖z-w‖):=by
  have hh:=Complex.norm_le_abs_re_add_abs_im (Dg ξ θ (z-w))
  have hr:=Complex.abs_re_le_norm (Dg ξ θ (z-w))
  have hi:=Complex.abs_im_le_norm (Dg ξ θ (z-w))
  rw [HC,GU] at hh hr hi
  simp only [Complex.sub_re,Complex.sub_im] at hh hr hi
  exact ⟨hh,by dsimp only [Am]; linarith⟩
lemma RS (ξ θ:ℝ) {z:ℂ} (hz:z≠0) :
    Dg ξ θ z=(Real.exp (Real.log ‖z‖-ξ):ℂ) *
      Complex.exp (((θ+z.arg:ℝ):ℂ)*Complex.I):=by
  rw [Complex.ofReal_add,add_mul,Complex.exp_add,
    Real.exp_sub,Real.exp_log (norm_pos_iff.mpr hz),
    div_eq_mul_inv,← Real.exp_neg,Complex.ofReal_mul]
  calc
    _=(Real.exp (-ξ):ℂ)* Complex.exp ((θ:ℂ)*Complex.I) *
        ((‖z‖:ℂ)* Complex.exp ((z.arg:ℂ)*Complex.I)):=by
      rw [Complex.norm_mul_exp_arg_mul_I]
      rfl
    _= _:=by ring
lemma So (t θ:ℝ) :
    ((Real.exp t:ℂ)* Complex.exp ((θ:ℂ)*Complex.I)).re=(BQ t θ).1 ∧
    ((Real.exp t:ℂ)* Complex.exp ((θ:ℂ)*Complex.I)).im=(BQ t θ).2:=by
  simp [BQ,Complex.mul_re,Complex.mul_im,Complex.exp_re,Complex.exp_im]
lemma SA (ξ θ:ℝ) {z w:ℂ} (hne:z≠ w) :
    (∫ ω,AH ω (Am ξ θ z) (Am ξ θ w) ∂Aq)
      - ξ+ Real.log ‖z-w‖= CB (Real.log ‖z-w‖-ξ) (θ+(z-w).arg):=by
  have hp:=So (Real.log ‖z-w‖-ξ) (θ+(z-w).arg)
  rw [← RS ξ θ (sub_ne_zero.mpr hne),GU] at hp
  have hm:=Mn (CT ξ θ hne)
    (DX (Real.log ‖z-w‖-ξ) (θ+(z-w).arg))
    (by dsimp only [Am]; simp only [zero_sub,abs_neg,← hp.1]; rfl)
    (by dsimp only [Am]; simp only [zero_sub,abs_neg,← hp.2]; rfl)
  rw [hm,CB]
  ring
abbrev AS:=(ℝ × ℝ) × Bp
def Ip:Measure (ℝ × ℝ) :=
  (AI (Real.log 2)).prod (AI (2*Real.pi))
def As:Measure AS:=Ip.prod Aq
instance Tr:IsProbabilityMeasure Ip:=by
  let:=Dd (Real.log_pos (by norm_num:(1:ℝ)<2))
  let:=Dd (by positivity:0<2*Real.pi)
  exact Measure.prod.instIsProbabilityMeasure _ _
instance TA:IsProbabilityMeasure As:=by
  exact Measure.prod.instIsProbabilityMeasure _ _
def depth (ω:AS) (z w:ℂ):ℝ :=
  AH ω.2 (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w) - ω.1.1
def error (ω:AS) (z w:ℂ):ℝ:=depth ω z w+ Real.log ‖z-w‖
lemma DQ (z:ℂ):Measurable (fun p:ℝ × ℝ=> Am p.1 p.2 z):=by
  unfold Am Dg
  fun_prop
lemma CO {z w:ℂ} (hne:z≠ w):Measurable (fun ω=> depth ω z w):=by
  unfold depth
  exact (Fz measurable_snd
    ((DQ z).comp measurable_fst)
    ((DQ w).comp measurable_fst)
    (fun p=> CT _ _ hne)).sub measurable_fst.fst
lemma Fp {z w:ℂ} (hne:z≠ w):Measurable (fun ω=> error ω z w) :=
  (CO hne).add_const _
lemma GI {z w:ℂ} (hne:z≠ w) (p:ℝ × ℝ) (ω:Bp) :
    error (p,ω) z w= AH ω (Am p.1 p.2 z) (Am p.1 p.2 w) +
      Real.log (Real.exp (-p.1)*‖z-w‖):=by
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)),Real.log_exp]
  simp only [error,depth]
  ring
lemma KP {z w:ℂ} (hne:z≠ w) (p:ℝ × ℝ) :
    Integrable (fun ω=> error (p,ω) z w) Aq:=by
  simp_rw [GI hne p]
  exact Hd (CT _ _ hne)
    (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
    (Dz _ _ _ _).1 (Dz _ _ _ _).2
lemma Ho {z w:ℂ} (hne:z≠ w) (p:ℝ × ℝ) :
    (∫ ω,|error (p,ω) z w| ∂Aq)≤4:=by
  simp_rw [GI hne p]
  exact Je (CT _ _ hne)
    (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
    (Dz _ _ _ _).1 (Dz _ _ _ _).2
lemma Bn {z w:ℂ} (hne:z≠ w) :
    Integrable (fun ω=> error ω z w) As:=by
  apply (integrable_prod_iff (Fp hne).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (KP hne)
  · apply Integrable.of_bound ((Fp hne).norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable) 4
    filter_upwards with p
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=> norm_nonneg _))]
    simpa only [Real.norm_eq_abs] using Ho hne p
lemma Pu {z w:ℂ} (hne:z≠ w) (p:ℝ × ℝ) :
    (∫ ω,error (p,ω) z w ∂Aq) =
      CB (Real.log ‖z-w‖-p.1) (p.2+(z-w).arg):=by
  have hi:Integrable (fun ω=> AH ω (Am p.1 p.2 z) (Am p.1 p.2 w)) Aq :=
    Fo (CT _ _ hne)
  have his:Integrable (fun ω=> AH ω (Am p.1 p.2 z) (Am p.1 p.2 w) - p.1) Aq :=
    hi.sub (integrable_const p.1)
  simp only [error,depth]
  rw [integral_add his (integrable_const (Real.log ‖z-w‖)),integral_sub hi (integrable_const p.1)]
  simp only [integral_const,probReal_univ,one_smul]
  exact SA _ _ hne
lemma Io (t φ:ℝ) :
    Measurable (fun p:ℝ × ℝ=> CB (t-p.1) (p.2+φ)):=by
  have h₁:Measurable (fun p:ℝ × ℝ=> t-p.1):=measurable_const.sub measurable_fst
  have h₂:Measurable (fun p:ℝ × ℝ=> p.2+φ):=measurable_snd.add_const φ
  change Measurable ((fun p:ℝ × ℝ=> CB p.1 p.2) ∘
    (fun p:ℝ × ℝ=>(t-p.1,p.2+φ)))
  apply Measurable.comp Mr
  exact h₁.prodMk h₂
lemma QO {z w:ℂ} (hne:z≠ w) :
    (∫ ω,error ω z w ∂As)= Mu:=by
  rw [As,integral_prod _ (Bn hne)]
  simp_rw [Pu hne]
  have hm:=Io (Real.log ‖z-w‖) (z-w).arg
  have hi:=Integrable.of_bound (μ:=Ip) hm.aestronglyMeasurable 4
    (Filter.Eventually.of_forall (fun p=> by simpa only [Real.norm_eq_abs] using Qp _ _))
  rw [Ip,integral_prod _ hi]
  exact Lg _ _
lemma MY {z w:ℂ} (hne:z≠ w) {u:ℝ} (hu:0≤ u) :
    As.real {ω | u < |error ω z w|}≤4*Real.exp (-u):=by
  have hs:MeasurableSet {ω:AS | u < |error ω z w|} :=
    measurableSet_lt measurable_const (Fp hne).abs
  have hb:As {ω | u < |error ω z w|}≤ ENNReal.ofReal (4*Real.exp (-u)):=by
    rw [As,Measure.prod_apply hs]
    calc
      _≤∫⁻ _p,ENNReal.ofReal (4*Real.exp (-u)) ∂Ip:=by
        apply lintegral_mono
        intro p
        have he:Aq.real {ω | u < |error (p,ω) z w|}≤4*Real.exp (-u):=by
          simp_rw [GI hne p]
          exact Ly (CT _ _ hne)
            (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
            (Dz _ _ _ _).1 (Dz _ _ _ _).2 hu
        have hh:=ENNReal.ofReal_le_ofReal he
        rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] at hh
        exact hh
      _= _:=by simp
  have hh:=ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [measureReal_def]
  simpa only [ENNReal.toReal_ofReal (by positivity:0≤4*Real.exp (-u))] using hh
lemma Es {z w:ℂ} (hne:z≠ w) :
    (∫ ω,|error ω z w| ∂As)≤4:=by
  rw [As,integral_prod _ (Bn hne).abs]
  calc
    _≤∫ _p,(4:ℝ) ∂Ip:=integral_mono
      (Bn hne).abs.integral_prod_left (integrable_const _)
      (Ho hne)
    _= _:=by simp
lemma Tt (ω:AS) (z w:ℂ):depth ω z w= depth ω w z:=by
  simp only [depth,AH,Sk ω.2 (Am ω.1.1 ω.1.2 z)
    (Am ω.1.1 ω.1.2 w)]
lemma Rz {x y z:ℂ} (hxy:x≠ y) (hyz:y≠ z) (hxz:x≠ z) :
    ∀ᵐ ω ∂As,min (depth ω x y) (depth ω y z)≤ depth ω x z:=by
  have hs:MeasurableSet {ω:AS | min (depth ω x y) (depth ω y z)≤ depth ω x z} :=
    measurableSet_le ((CO hxy).min (CO hyz)) (CO hxz)
  apply (Measure.ae_prod_iff_ae_ae hs).mpr
  filter_upwards with p
  filter_upwards [Oh (CT p.1 p.2 hxy)
    (CT p.1 p.2 hyz) (CT p.1 p.2 hxz)] with ω hh
  simpa only [depth,min_sub_sub_right,sub_le_sub_iff_right] using hh
end Aa.Ao
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
namespace Aa.Bg
open Ak
variable {P:Type u1} [Fintype P] [DecidableEq P]
variable {K:Type u2} [Field K] [NumberField K]
variable (Z:P→ K) (hZ:Function.Injective Z)
include hZ
def good (v:InfinitePlace K) (ω:Ao.AS):Prop :=
  ∀ x y z:P,x≠ y→ y≠ z→ x≠ z →
    min (Ao.depth ω (v.embedding (Z x)) (v.embedding (Z y)))
      (Ao.depth ω (v.embedding (Z y)) (v.embedding (Z z))) ≤
        Ao.depth ω (v.embedding (Z x)) (v.embedding (Z z))
omit [Fintype P] [DecidableEq P] [NumberField K] in
lemma Bx (v:InfinitePlace K) {x y:P} (hne:x≠ y) :
    v.embedding (Z x)≠ v.embedding (Z y) :=
  fun hh=> hne (hZ (v.embedding.injective hh))
omit [DecidableEq P] [NumberField K] in
lemma NO (v:InfinitePlace K):MeasurableSet {ω | good Z v ω}:=by
  simp only [good,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  apply MeasurableSet.iInter
  intro z
  apply MeasurableSet.iInter
  intro hxy
  apply MeasurableSet.iInter
  intro hyz
  apply MeasurableSet.iInter
  intro hxz
  exact measurableSet_le
    ((Ao.CO (Bx Z hZ v hxy)).min
      (Ao.CO (Bx Z hZ v hyz)))
    (Ao.CO (Bx Z hZ v hxz))
omit [DecidableEq P] [NumberField K] in
lemma Rr (v:InfinitePlace K):∀ᵐ ω ∂Ao.As,good Z v ω:=by
  simp only [good,Filter.eventually_all]
  intro x y z hxy hyz hxz
  exact Ao.Rz (Bx Z hZ v hxy)
    (Bx Z hZ v hyz) (Bx Z hZ v hxz)
instance TH (v:InfinitePlace K) (ω:Ao.AS):Decidable (good Z v ω) :=
  Classical.propDecidable _
def arch (v:InfinitePlace K) (ω:Ao.AS):Depth P where
  value x y:=if good Z v ω∧ x≠ y then Ao.depth ω (v.embedding (Z x)) (v.embedding (Z y)) else 0
  symm x y:=by
    by_cases h:good Z v ω
    · by_cases hxy:x= y
      · subst y; rfl
      · simp [h,hxy,Ne.symm hxy,Ao.Tt]
    · simp [h]
  Qw x y z hxy hyz hxz:=by
    by_cases h:good Z v ω
    · simpa [h,hxy,hyz,hxz] using h x y z hxy hyz hxz
    · simp [h]
omit [NumberField K] in
lemma DE (v:InfinitePlace K) {x y:P} (hxy:x≠ y) :
    (fun ω=>(arch Z v ω).value x y) =ᵐ[Ao.As]
      (fun ω=> Ao.depth ω (v.embedding (Z x)) (v.embedding (Z y))):=by
  filter_upwards [Rr Z hZ v] with ω h
  simp [arch,h,hxy]
omit [NumberField K] in
lemma BA (v:InfinitePlace K) (x y:P) :
    Measurable (fun ω=>(arch Z v ω).value x y):=by
  by_cases hxy:x= y
  · subst y
    simpa only [arch,ne_eq,not_true_eq_false,and_false,reduceIte] using
      (measurable_const:Measurable (fun _:Ao.AS=>(0:ℝ)))
  · simpa [arch,hxy] using (Ao.CO (Bx Z hZ v hxy)).ite
      (NO Z hZ v) (measurable_const:Measurable (fun _:Ao.AS=>(0:ℝ)))
omit [NumberField K] in
lemma AO (v:InfinitePlace K) (x y:P) :
    Integrable (fun ω=>(arch Z v ω).value x y) Ao.As:=by
  by_cases hxy:x= y
  · subst y
    simpa only [arch,ne_eq,not_true_eq_false,and_false,reduceIte] using
      (integrable_const (0:ℝ):Integrable (fun _:Ao.AS=>(0:ℝ)) Ao.As)
  · have hi:=(Ao.Bn (Bx Z hZ v hxy)).sub
      (integrable_const (Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖))
    have he:(fun ω=> Ao.error ω (v.embedding (Z x)) (v.embedding (Z y)) -
        Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖) =
        (fun ω=> Ao.depth ω (v.embedding (Z x)) (v.embedding (Z y))):=by
      funext ω; simp only [Ao.error,add_sub_cancel_right]
    change Integrable (fun ω=> Ao.error ω (v.embedding (Z x)) (v.embedding (Z y)) -
        Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖) Ao.As at hi
    rw [he] at hi
    exact hi.congr (DE Z hZ v hxy).symm
lemma TE (v:InfinitePlace K) (x y:P) (hxy:x≠ y) :
    (∫ ω,(arch Z v ω).value x y ∂Ao.As) = -Real.log (v (Z x-Z y))+ Ao.Mu:=by
  rw [integral_congr_ae (DE Z hZ v hxy)]
  have hh:=Ao.QO (Bx Z hZ v hxy)
  have hi:=(AO Z hZ v x y).congr (DE Z hZ v hxy)
  simp only [Ao.error] at hh
  rw [integral_add hi (integrable_const _)] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  rw [← map_sub,InfinitePlace.norm_embedding_eq] at hh
  linarith
def finite (v:FinitePlace K):Depth P where
  value x y:=if x= y then 0 else -Real.log (v (Z x-Z y))
  symm x y:=by
    by_cases hxy:x= y
    · subst y; rfl
    · simp only [hxy,Ne.symm hxy,reduceIte]
      rw [← neg_sub (Z x) (Z y),map_neg_eq_map]
  Qw x y z hxy hyz hxz:=by
    simp only [hxy,hyz,hxz,reduceIte]
    exact Arithmetic.Qb v (hZ.ne hxy) (hZ.ne hyz) (hZ.ne hxz)
abbrev TG:={p:P × P // p.1≠ p.2}
def Bq:Finset (FinitePlace K) :=
  (Arithmetic.LK (fun p:TG (P:=P)=> Z p.1.1 - Z p.1.2)
    (fun p=> sub_ne_zero.mpr (hZ.ne p.2))).toFinset
omit [DecidableEq P] in
lemma MM (v:FinitePlace K):v∈ Bq Z hZ↔∃ x y,x≠ y∧ v (Z x-Z y)≠1:=by
  simp only [Bq,Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨⟨x,y⟩,hne⟩,hh⟩
    exact ⟨x,y,hne,hh⟩
  · rintro ⟨x,y,hne,hh⟩
    exact ⟨⟨(x,y),hne⟩,hh⟩
lemma Pm (x y:P) (hxy:x≠ y) :
    (∑ v∈ Bq Z hZ,(finite Z hZ v).value x y) =
      ∑ᶠ v:FinitePlace K,-Real.log (v (Z x-Z y)):=by
  simp only [finite,hxy,reduceIte]
  symm
  apply finsum_eq_sum_of_support_subset
  intro v hv
  apply (MM Z hZ v).mpr
  refine ⟨x,y,hxy,?_⟩
  intro hh
  exact hv (by simp [hh])
def S (x:P):ℝ :=
  (∑ v:InfinitePlace K,Arithmetic.Bh v*∫ ω,(arch Z v ω).Ag x ∂Ao.As) +
    (Module.finrank ℚ K:ℝ)⁻¹*∑ v∈ Bq Z hZ,(finite Z hZ v).Ag x
def L (x y:P) (hxy:x≠ y):ℝ :=
  (∑ v:InfinitePlace K,Arithmetic.Bh v*∫ ω,(arch Z v ω).AN x y hxy ∂Ao.As) +
    (Module.finrank ℚ K:ℝ)⁻¹*∑ v∈ Bq Z hZ,(finite Z hZ v).AN x y hxy
def M:ℝ :=
  (∑ v:InfinitePlace K,Arithmetic.Bh v*∫ ω,(arch Z v ω).M ∂Ao.As) +
    (Module.finrank ℚ K:ℝ)⁻¹*∑ v∈ Bq Z hZ,(finite Z hZ v).M
lemma Fi (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    L Z hZ x y hxy= Ao.Mu - M Z hZ+ S Z hZ x+ S Z hZ y:=by
  have harch:(∑ v:InfinitePlace K,Arithmetic.Bh v *
      (∫ ω,(arch Z v ω).M ∂Ao.As)) +
      (∑ v:InfinitePlace K,Arithmetic.Bh v *
      (∫ ω,(arch Z v ω).AN x y hxy ∂Ao.As)) -
      (∑ v:InfinitePlace K,Arithmetic.Bh v *
      (∫ ω,(arch Z v ω).Ag x ∂Ao.As)) -
      (∑ v:InfinitePlace K,Arithmetic.Bh v *
      (∫ ω,(arch Z v ω).Ag y ∂Ao.As)) =
      (∑ v:InfinitePlace K,Arithmetic.Bh v*(-Real.log (v (Z x-Z y))))+ Ao.Mu:=by
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    have he:∀ v:InfinitePlace K,
        Arithmetic.Bh v*(∫ ω,(arch Z v ω).M ∂Ao.As) +
        Arithmetic.Bh v*(∫ ω,(arch Z v ω).AN x y hxy ∂Ao.As) -
        Arithmetic.Bh v*(∫ ω,(arch Z v ω).Ag x ∂Ao.As) -
        Arithmetic.Bh v*(∫ ω,(arch Z v ω).Ag y ∂Ao.As) =
        Arithmetic.Bh v*(-Real.log (v (Z x-Z y)))+ Arithmetic.Bh v* Ao.Mu:=by
      intro v
      have hh:=Depth.Kt (arch Z v) (BA Z hZ v)
        (AO Z hZ v) hn x y hxy
      rw [TE Z hZ v x y hxy] at hh
      linear_combination -Arithmetic.Bh v* hh
    simp_rw [he]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,Arithmetic.Il,one_mul]
  have hfin:(∑ v∈ Bq Z hZ,(finite Z hZ v).M) +
      (∑ v∈ Bq Z hZ,(finite Z hZ v).AN x y hxy) -
      (∑ v∈ Bq Z hZ,(finite Z hZ v).Ag x) -
      (∑ v∈ Bq Z hZ,(finite Z hZ v).Ag y) =
      ∑ᶠ v:FinitePlace K,-Real.log (v (Z x-Z y)):=by
    rw [← Pm Z hZ x y hxy,← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact ((finite Z hZ v).Eg hn x y hxy).symm
  have hprod:=Arithmetic.HN (Z x-Z y) (sub_ne_zero.mpr (hZ.ne hxy))
  dsimp only [L,M,S]
  linear_combination harch+(Module.finrank ℚ K:ℝ)⁻¹* hfin+ hprod
lemma SM (x:P):0≤ S Z hZ x:=by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun v _=> mul_nonneg (Arithmetic.EV v)
      (integral_nonneg (fun ω=>(arch Z v ω).BM x)))
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _=>(finite Z hZ v).BM x))
end Aa.Bg
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u3} [Fintype P] [DecidableEq P]
variable (d:Depth P)
def count (r:ℝ) (C:Finset P):ℝ:=(d.transformed r).count C
def mass (C:Finset P):ℝ:=if 2≤ C.card then ∫ r,d.count r C else 0
lemma RZ (m:Multiset (Finset P)) (f:Finset P→ ℝ) :
    (m.map f).sum=∑ C,(m.count C:ℝ)* f C:=by
  induction m using Multiset.induction_on with
  | empty=> simp
  | @cons a m ih =>
      simp only [Multiset.map_cons,Multiset.sum_cons,ih,Multiset.count_cons]
      simp_rw [Nat.cast_add,add_mul]
      rw [Finset.sum_add_distrib]
      simp [add_comm]
lemma Fe (f:Finset P→ ℝ) (r:ℝ) :
    d.Ch f r=∑ C,d.count r C* f C:=RZ _ _
lemma HK (r:ℝ) (C:Finset P):0≤ d.count r C:=Nat.cast_nonneg _
lemma JO (r:ℝ) (C:Finset P) (x y:P) (hx:x∈ C) (hy:y∈ C) :
    d.count r C≤ d.Bb r x y:=by
  rw [Bb,d.Fe]
  calc
    d.count r C= d.count r C*(if x∈ C∧ y∈ C then (1:ℝ) else 0):=by simp [hx,hy]
    _≤ _:=Finset.single_le_sum (f:=fun D=> d.count r D*(if x∈ D∧ y∈ D then (1:ℝ) else 0)) (fun D _=> mul_nonneg (d.HK r D) (by positivity)) (Finset.mem_univ C)
lemma PK (C:Finset P):Measurable (fun r=> d.count r C):=by
  let F:Finset (Finset P) × Finset (Finset P)→ ℝ:=fun st =>
    (((st.1.filter (fun D=>¬Fintype.card P<2*D.card)).val +
       st.2.val.map (fun D=> Dᶜ)).count C:ℝ)
  have hh:Measurable (fun r=> F (d.cells r,d.AR r)) :=
    (measurable_of_finite F).comp (d.Ha.prodMk d.EU)
  change Measurable (fun r=> F (d.cells r,d.AR r))
  exact hh
lemma GZ (hn:2≤ Fintype.card P) (C:Finset P) (hC:2≤ C.card) :
    Integrable (fun r=> d.count r C):=by
  obtain ⟨x,hx,y,hy,hxy⟩:=Finset.one_lt_card.mp hC
  apply (d.Dj hn x y hxy).mono' (d.PK C).aestronglyMeasurable
  filter_upwards with r
  simpa only [Real.norm_eq_abs,abs_of_nonneg (d.HK r C)] using d.JO r C x y hx hy
lemma Bf (C:Finset P):0≤ d.mass C:=by
  unfold mass
  split_ifs
  · exact integral_nonneg (fun r=> d.HK r C)
  · rfl
lemma RF (C:Finset P) (hC:C.card≤1):d.mass C=0:=by
  simp [mass,show ¬2≤ C.card by omega]
lemma KE (hn:2≤ Fintype.card P) (C:Finset P) (x y:P)
    (hxy:x≠ y) (hx:x∈ C) (hy:y∈ C) :
    d.mass C≤ d.AN x y hxy:=by
  have hC:2≤ C.card:=Finset.one_lt_card.mpr ⟨x,hx,y,hy,hxy⟩
  rw [mass,if_pos hC,AN]
  exact integral_mono (d.GZ hn C hC) (d.Dj hn x y hxy)
    (fun r=> d.JO r C x y hx hy)
lemma DB (hn:2≤ Fintype.card P) (f:Finset P→ ℝ)
    (hf:∀ C,C.card≤1→ f C=0) :
    (∫ r,d.Ch f r)=∑ C,d.mass C* f C:=by
  have hi (C:Finset P):Integrable (fun r=> d.count r C* f C):=by
    by_cases hC:2≤ C.card
    · exact (d.GZ hn C hC).mul_const _
    · simp [hf C (by omega)]
  simp_rw [d.Fe]
  rw [integral_finsetSum _ (fun C _=> hi C)]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC:2≤ C.card
  · simp [mass,hC,integral_mul_const]
  · simp [mass,hC,hf C (by omega)]
lemma Gh (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    (∑ C,d.mass C*(if x∈ C∧ y∈ C then (1:ℝ) else 0)) =
      d.AN x y hxy:=by
  symm
  apply d.DB hn
  intro C hC
  have hh:¬(x∈ C∧ y∈ C):=by
    rintro ⟨hx,hy⟩
    have:=Finset.one_lt_card.mpr ⟨x,hx,y,hy,hxy⟩
    omega
  simp [hh]
section Param
variable {Ω:Type u4} [MeasurableSpace Ω] (D:Ω→ Depth P)
    (hD:∀ x y,Measurable (fun ω=>(D ω).value x y))
include hD
lemma Lv (C:Finset P) :
    Measurable (fun p:Ω × ℝ=>(D p.1).count p.2 C):=by
  let F:Finset (Finset P) × Finset (Finset P)→ ℝ:=fun st =>
    (((st.1.filter (fun E=>¬Fintype.card P<2*E.card)).val +
       st.2.val.map (fun E=> Eᶜ)).count C:ℝ)
  have hm:Measurable (fun p:Ω×ℝ=>((D p.1).cells p.2,(D p.1).AR p.2)) :=
    (EP (P:=P) (Ω:=Ω×ℝ) (fun p:Ω×ℝ=> D p.1)
      (fun x y=>(hD x y).comp measurable_fst) Prod.snd measurable_snd).prodMk
    (DH (P:=P) (Ω:=Ω×ℝ) (fun p:Ω×ℝ=> D p.1)
      (fun x y=>(hD x y).comp measurable_fst) Prod.snd measurable_snd)
  have hh:Measurable (fun p:Ω×ℝ=> F ((D p.1).cells p.2,(D p.1).AR p.2)) :=
    (measurable_of_finite F).comp hm
  change Measurable (fun p:Ω×ℝ=> F ((D p.1).cells p.2,(D p.1).AR p.2))
  exact hh
lemma Mg (C:Finset P):Measurable (fun ω=>(D ω).mass C):=by
  unfold mass
  split_ifs with hC
  · exact (Lv D hD C).stronglyMeasurable.integral_prod_right.measurable
  · exact measurable_const
lemma Du {μ:Measure Ω}
    (hi:∀ x y,Integrable (fun ω=>(D ω).value x y) μ)
    (hn:2≤ Fintype.card P) (C:Finset P) :
    Integrable (fun ω=>(D ω).mass C) μ:=by
  by_cases hC:2≤ C.card
  · obtain ⟨x,hx,y,hy,hxy⟩:=Finset.one_lt_card.mp hC
    apply (EI D hD hi hn x y hxy).mono'
      (Mg D hD C).aestronglyMeasurable
    filter_upwards with ω
    simpa only [Real.norm_eq_abs,abs_of_nonneg ((D ω).Bf C)] using
      (D ω).KE hn C x y hxy hx hy
  · simp only [mass,hC,reduceIte]
    exact integrable_zero _ _ _
lemma LO {μ:Measure Ω}
    (hi:∀ x y,Integrable (fun ω=>(D ω).value x y) μ)
    (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    (∑ C,(∫ ω,(D ω).mass C ∂μ)*(if x∈ C∧ y∈ C then (1:ℝ) else 0)) =
      ∫ ω,(D ω).AN x y hxy ∂μ:=by
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun C _=>(Du D hD hi hn C).mul_const _)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun ω=>(D ω).Gh hn x y hxy))
end Param
end Aa.Ak.Depth
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Aa.Variance
variable {P:Type u1} [Fintype P] [DecidableEq P]
def Ae (B:Finset P) (x:P):ℝ:=if x∈ B then 1/ B.card else 0
def Az (B:Finset P) (x y:P):ℝ :=
  if x∈ B∧ y∈ B∧ x≠ y then 1/((B.card:ℝ)*(B.card - 1)) else 0
def Fk (B:Finset P) (x y:P):ℝ :=
  if x∈ B∧ x≠ y then
    if y∈ B then 1/((Fintype.card P:ℝ)*(B.card - 1))
    else 1/((Fintype.card P:ℝ)* B.card)
  else 0
lemma Bs (B:Finset P) (hB:B.Nonempty):∑ x,Ae B x=1:=by
  classical
  rw [show (∑ x,Ae B x)=∑ x∈ B,1/(B.card:ℝ) by simp [Ae]]
  simp [hB.card_ne_zero]
lemma Cp (B:Finset P) (hB:2≤ B.card) (x:P) :
    ∑ y,Az B x y= Ae B x:=by
  classical
  by_cases hx:x∈ B
  · have hk:(B.card:ℝ)≠0:=by exact_mod_cast (by omega:B.card≠0)
    have hk1:(B.card:ℝ) - 1≠0:=by
      have:(2:ℝ)≤ B.card:=by exact_mod_cast hB
      linarith
    have he:∀ y,Az B x y= if y∈ B.erase x then
        1/((B.card:ℝ)*(B.card - 1)) else 0:=by
      intro y
      simp only [Az,hx,true_and,Finset.mem_erase,ne_comm (a:=y)]
      simp only [and_comm]
    simp_rw [he]
    simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,
      nsmul_eq_mul,Finset.card_erase_of_mem hx]
    rw [Nat.cast_sub (by omega)]
    simp only [Nat.cast_one,Ae,hx,reduceIte]
    field_simp
  · simp [Az,Ae,hx]
omit [Fintype P] in
lemma Ex (B:Finset P) (x y:P):Az B x y= Az B y x:=by
  simp only [Az,and_left_comm,ne_comm]
omit [Fintype P] in
lemma IU (B:Finset P) (x:P):Az B x x=0:=by
  simp [Az]
omit [DecidableEq P] in
lemma CE (B:Finset P) (hB:2≤ B.card) :
    2≤ Fintype.card P:=hB.trans (Finset.card_le_univ B)
lemma FF (B:Finset P) (hB:2≤ B.card) (x y:P) :
    Fk B x y=(B.card:ℝ)/ Fintype.card P* Az B x y +
      Ae B x/ Fintype.card P*(if y∈ B then 0 else 1):=by
  have hk:(B.card:ℝ)≠0:=by exact_mod_cast (by omega:B.card≠0)
  have hn:(Fintype.card P:ℝ)≠0:=by
    exact_mod_cast (by have:=CE B hB; omega:Fintype.card P≠0)
  have hk1:(B.card:ℝ) - 1≠0:=by
    have:(2:ℝ)≤ B.card:=by exact_mod_cast hB
    linarith
  by_cases hx:x∈ B <;> by_cases hy:y∈ B <;> by_cases hxy:x= y
  all_goals simp_all [Fk,Az,Ae]
  all_goals field_simp
lemma RW (B:Finset P) (hB:2≤ B.card) (x:P) :
    ∑ y,Fk B x y= Ae B x:=by
  have hn:(Fintype.card P:ℝ)≠0:=by
    exact_mod_cast (by have:=CE B hB; omega:Fintype.card P≠0)
  have hout:(∑ y:P,(if y∈ B then (0:ℝ) else 1)) =
      Fintype.card P - (B.card:ℝ):=by
    have he:∀ y:P,(if y∈ B then (0:ℝ) else 1) =
        if y∈ Bᶜ then 1 else 0:=by intro y; simp
    simp_rw [he]
    simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,
      nsmul_eq_mul,mul_one,Finset.card_compl,
      Nat.cast_sub (Finset.card_le_univ B)]
  simp_rw [FF B hB,Finset.sum_add_distrib,
    ← Finset.mul_sum,Cp B hB,hout]
  field_simp
  ring
lemma Oq (B:Finset P) (hB:2≤ B.card) (y:P) :
    ∑ x,Fk B x y=1/ Fintype.card P:=by
  have hk:(B.card:ℝ)≠0:=by exact_mod_cast (by omega:B.card≠0)
  have hne:B.Nonempty:=Finset.card_pos.mp (by omega)
  simp_rw [FF B hB,Finset.sum_add_distrib,
    ← Finset.mul_sum,Ex B _ y,Cp B hB,
    ← Finset.sum_mul,← Finset.sum_div,Bs B hne]
  by_cases hy:y∈ B <;> simp [Ae,hy]
  field_simp
lemma LF (B:Finset P) (x:P):Fk B x x=0:=by
  simp [Fk]
def CI (B:Finset P) (x y:P):ℝ :=
  Az B x y - 2* Fk B x y+ Az Finset.univ x y
lemma QW (B:Finset P) (x:P):CI B x x=0:=by
  simp [CI,IU,LF]
lemma LS (B:Finset P) (hB:2≤ B.card) (x:P) :
    (∑ y,CI B x y)=1/ Fintype.card P - Ae B x:=by
  have hP:2≤(Finset.univ:Finset P).card:=CE B hB
  simp_rw [CI,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,Cp B hB,RW B hB,
    Cp Finset.univ hP]
  simp only [Ae,Finset.mem_univ,reduceIte,Finset.card_univ]
  ring
lemma Rv (B:Finset P) (hB:2≤ B.card) (y:P) :
    (∑ x,CI B x y)= Ae B y - 1/ Fintype.card P:=by
  have hP:2≤(Finset.univ:Finset P).card:=CE B hB
  simp_rw [CI,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,Oq B hB,Ex B _ y,
    Ex Finset.univ _ y,Cp B hB,
    Cp Finset.univ hP]
  simp only [Ae,Finset.mem_univ,reduceIte,Finset.card_univ]
  ring
lemma QC (H L:P→ P→ ℝ) (b:ℝ) (S:P→ ℝ)
    (hdiag:∀ x,H x x=0)
    (hmass:(∑ x,∑ y,H x y)=0)
    (hmarg:∀ x,(∑ y,H x y)+∑ y,H y x=0)
    (hL:∀ x y,x≠ y→ L x y= b+ S x+ S y) :
    (∑ x,∑ y,H x y* L x y)=0:=by
  have hterm (x y:P):H x y* L x y= H x y*(b+ S x+ S y):=by
    by_cases h:x= y
    · subst y; simp [hdiag]
    · rw [hL x y h]
  simp_rw [hterm,mul_add,Finset.sum_add_distrib]
  have hb:(∑ x,∑ y,H x y* b)=(∑ x,∑ y,H x y)* b:=by
    simp_rw [Finset.sum_mul]
  rw [hb,hmass,zero_mul,zero_add]
  have h₁:(∑ x,∑ y,H x y* S x)=∑ x,(∑ y,H x y)* S x:=by
    simp_rw [Finset.sum_mul]
  have h₂:(∑ x,∑ y,H x y* S y)=∑ x,(∑ y,H y x)* S x:=by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  rw [h₁,h₂,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x _
  rw [← add_mul,hmarg,zero_mul]
lemma QF (B:Finset P) (hB:2≤ B.card)
    (L:P→ P→ ℝ) (b:ℝ) (S:P→ ℝ)
    (hL:∀ x y,x≠ y→ L x y= b+ S x+ S y) :
    (∑ x,∑ y,CI B x y* L x y)=0:=by
  apply QC _ _ b S (QW B) _ _ hL
  · simp_rw [LS B hB,Finset.sum_sub_distrib]
    have hn:(Fintype.card P:ℝ)≠0:=by
      exact_mod_cast (by have:=CE B hB; omega:Fintype.card P≠0)
    rw [Bs B (Finset.card_pos.mp (by omega))]
    simp [hn]
  · intro x
    rw [LS B hB,Rv B hB]
    ring
def Ah (B C:Finset P):ℝ:=∑ x∈ C,∑ y∈ C,Az B x y
def Ez (B C:Finset P):ℝ:=∑ x∈ C,∑ y∈ C,Fk B x y
def Ad (B C:Finset P):ℝ:=((B∩ C).card:ℝ)/ B.card
omit [Fintype P] in
lemma Ci (B C:Finset P):∑ x∈ C,Ae B x= Ad B C:=by
  simp only [Ae,Finset.sum_ite_mem,Finset.sum_const,nsmul_eq_mul,mul_one_div,
    Ad,Finset.inter_comm]
omit [Fintype P] in
lemma Eo (B C:Finset P) :
    Ah B C=((B∩ C).card:ℝ)*((B∩ C).card - 1) /
      ((B.card:ℝ)*(B.card - 1)):=by
  classical
  unfold Ah Az
  rw [← Finset.sum_product C C (fun xy:P × P =>
    if xy.1∈ B∧ xy.2∈ B∧ xy.1≠ xy.2 then
      1/((B.card:ℝ)*(B.card - 1)) else 0),← Finset.sum_filter]
  have hf:(C×ˢ C).filter (fun xy=> xy.1∈ B∧ xy.2∈ B∧ xy.1≠ xy.2) =
      (B∩ C).offDiag:=by
    ext ⟨x,y⟩
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_offDiag,Finset.mem_inter]
    tauto
  rw [hf,Finset.sum_const,nsmul_eq_mul,Finset.offDiag_card,← Nat.mul_sub_one]
  by_cases hb:(B∩ C).card=0
  · simp [hb]
  · rw [Nat.cast_mul,Nat.cast_sub (by omega),Nat.cast_one]
    ring
omit [Fintype P] in
lemma Ps (B C:Finset P) :
    (∑ y∈ C,if y∈ B then (0:ℝ) else 1) =
      (C.card:ℝ) - (B∩ C).card:=by
  have he:∀ y,(if y∈ B then (0:ℝ) else 1) =
      if y∉ B then 1 else 0:=by intro y; split_ifs <;> rfl
  simp_rw [he]
  rw [← Finset.sum_filter]
  rw [show C.filter (fun y=> y∉ B)= C \ B by ext y; simp]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_sdiff,
    Nat.cast_sub (Finset.card_le_card Finset.inter_subset_right)]
lemma OY (B C:Finset P) (hB:2≤ B.card) :
    Ez B C=(B.card:ℝ)/ Fintype.card P* Ah B C +
      Ad B C/ Fintype.card P*((C.card:ℝ) - (B∩ C).card):=by
  unfold Ez
  simp_rw [FF B hB,Finset.sum_add_distrib,← Finset.mul_sum,
    Ps B C,← Finset.sum_mul,← Finset.sum_div,Ci B C]
  rfl
omit [Fintype P] in
lemma Bd (B C:Finset P):0≤ Ad B C:=by
  unfold Ad
  positivity
omit [Fintype P] in
lemma Dy (B C:Finset P):Ad B C≤1:=by
  unfold Ad
  apply div_le_one_of_le₀
  · exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₂:=C))
  · positivity
omit [Fintype P] in
lemma BJ (B C:Finset P):0≤ Ah B C:=by
  unfold Ah Az
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  split_ifs with h
  · have:2≤ B.card:=Finset.one_lt_card.mpr ⟨x,h.1,y,h.2.1,h.2.2⟩
    have:(2:ℝ)≤ B.card:=by exact_mod_cast this
    have:0≤(B.card:ℝ) - 1:=by linarith
    positivity
  · rfl
private lemma Sb (k b:ℝ) (hk:k≠0) (hk1:k - 1≠0) :
    b*(b-1)/(k*(k-1))=(b/k)^2 - (b/k)*(1-b/k)/(k-1):=by
  field_simp
  ring
omit [Fintype P] in
lemma GG (B C:Finset P) (hB:2≤ B.card) :
    Ah B C=(Ad B C)^2 - Ad B C*(1-Ad B C) /
      ((B.card:ℝ) - 1):=by
  have hk:(B.card:ℝ)≠0:=by exact_mod_cast (by omega:B.card≠0)
  have hk1:(B.card:ℝ) - 1≠0:=by
    have:(2:ℝ)≤ B.card:=by exact_mod_cast hB
    linarith
  rw [Eo,Ad,Sb _ _ hk hk1]
lemma IH (B C:Finset P) (hB:2≤ B.card) :
    Ez B C= Ad Finset.univ C* Ad B C -
      (B.card:ℝ)/ Fintype.card P *
        (Ad B C*(1-Ad B C)/((B.card:ℝ)-1)):=by
  have hk:(B.card:ℝ)≠0:=by exact_mod_cast (by omega:B.card≠0)
  rw [OY B C hB,GG B C hB]
  simp only [Ad,Finset.univ_inter,Finset.card_univ]
  field_simp
  ring
lemma Mv (B C:Finset P) (hB:2≤ B.card) :
    Ez B C≤ Ad Finset.univ C* Ad B C:=by
  rw [IH B C hB]
  have hp:=Bd B C
  have hp1:=Dy B C
  have hk:(2:ℝ)≤ B.card:=by exact_mod_cast hB
  have hk0:0≤(B.card:ℝ) - 1:=by linarith
  have hp10:0≤1-Ad B C:=sub_nonneg.mpr hp1
  have hh:0≤(B.card:ℝ)/ Fintype.card P *
      (Ad B C*(1-Ad B C)/((B.card:ℝ)-1)):=by positivity
  linarith
lemma NJ (B C:Finset P) (hB:2≤ B.card) :
    (∑ x∈ C,∑ y∈ C,CI B x y) =
      (Ad B C - Ad Finset.univ C)^2 +
      (2*(B.card:ℝ)/ Fintype.card P - 1) *
        (Ad B C*(1-Ad B C)/((B.card:ℝ)-1)) -
      Ad Finset.univ C*(1-Ad Finset.univ C) /
        ((Fintype.card P:ℝ)-1):=by
  have hP:2≤(Finset.univ:Finset P).card:=CE B hB
  simp_rw [CI,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  change Ah B C - 2* Ez B C+ Ah Finset.univ C= _
  rw [GG B C hB,IH B C hB,
    GG Finset.univ C hP]
  simp only [Finset.card_univ]
  ring
private lemma Hq (n m:ℝ) (hm:2≤ m) (hmn:m≤ n) :
    (1/2)*(m/n)^2≤ m*(m-1)/(n*(n-1)) ∧
      m*(m-1)/(n*(n-1))≤(m/n)^2:=by
  have hn:0< n:=by linarith
  have hn1:0< n-1:=by linarith
  have hmn0:0≤ m/n:=div_nonneg (by linarith) hn.le
  have hlow:m/(2*n)≤(m-1)/(n-1):=by
    apply (div_le_div_iff₀ (by positivity) hn1).mpr
    nlinarith [mul_nonneg hn.le (show 0≤ m-2 by linarith)]
  have hupp:(m-1)/(n-1)≤ m/n:=by
    apply (div_le_div_iff₀ hn1 hn).mpr
    nlinarith
  have he:m*(m-1)/(n*(n-1))=(m/n)*((m-1)/(n-1)):=by
    field_simp
  rw [he]
  constructor
  · calc
      (1/2)*(m/n)^2=(m/n)*(m/(2*n)):=by ring
      _≤ _:=mul_le_mul_of_nonneg_left hlow hmn0
  · simpa only [sq] using mul_le_mul_of_nonneg_left hupp hmn0
lemma Cw (C:Finset P) (hC:2≤ C.card) :
    (1/2)*(Ad Finset.univ C)^2≤ Ah Finset.univ C ∧
      Ah Finset.univ C≤(Ad Finset.univ C)^2:=by
  rw [Eo]
  simp only [Ad,Finset.univ_inter,Finset.card_univ]
  apply Hq
  · exact_mod_cast hC
  · exact_mod_cast Finset.card_le_univ C
omit [Fintype P] in
lemma PA (B C:Finset P) (hB:2≤ B.card) :
    (1/2)*(if 2/(B.card:ℝ)≤ Ad B C then (Ad B C)^2 else 0) ≤
      Ah B C:=by
  split_ifs with hp
  · have hk:0<(B.card:ℝ):=by exact_mod_cast (by omega:0< B.card)
    have hb:(2:ℝ)≤(B∩ C).card :=
      (div_le_div_iff_of_pos_right hk).mp hp
    rw [Eo,Ad]
    exact (Hq _ _ hb
      (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₂:=C)))).1
  · simpa only [mul_zero] using BJ B C
omit [Fintype P] in
lemma DN (B C:Finset P) (hC:C.card≤1):Ah B C=0:=by
  unfold Ah
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have:x= y:=Finset.card_le_one.mp hC x hx y hy
  subst y
  exact IU B x
lemma Nu (B C:Finset P) (hC:C.card≤1):Ez B C=0:=by
  unfold Ez
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have:x= y:=Finset.card_le_one.mp hC x hx y hy
  subst y
  exact LF B x
omit [Fintype P] in
lemma Hz (B C:Finset P) (hB:2≤ B.card) (hC:C.card≤1) :
    (if 2/(B.card:ℝ)≤ Ad B C then (Ad B C)^2 else 0)=0:=by
  have hk:0<(B.card:ℝ):=by exact_mod_cast (by omega:0< B.card)
  have hi:(B∩ C).card≤1:=(Finset.card_le_card Finset.inter_subset_right).trans hC
  have hiR:((B∩ C).card:ℝ)<2:=by exact_mod_cast (by omega:(B∩ C).card<2)
  have hp:Ad B C<2/(B.card:ℝ) :=
    (div_lt_div_iff_of_pos_right hk).mpr hiR
  simp only [not_le.mpr hp,reduceIte]
def Cn (B C:Finset P):ℝ:=Ah B C - 2* Ez B C +
    Ah Finset.univ C
lemma MQ (B C:Finset P) :
    Cn B C=∑ x∈ C,∑ y∈ C,CI B x y:=by
  simp only [Cn,Ah,Ez,CI,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
lemma Mt (B C:Finset P) (hC:C.card≤1):Cn B C=0:=by
  simp [Cn,DN _ _ hC,Nu _ _ hC]
private lemma JX (p k ε:ℝ) (hp:0≤ p) (hp1:p≤1)
    (hk:0< k-1) (he:1/(k-1)≤ ε) :
    0≤ p*(1-p)/(k-1)∧ p*(1-p)/(k-1)≤ ε*p:=by
  have hε:0≤ ε:=(by positivity:0≤1/(k-1)).trans he
  constructor
  · exact div_nonneg (mul_nonneg hp (sub_nonneg.mpr hp1)) hk.le
  · calc
      p*(1-p)/(k-1)≤ p/(k-1):=by
        apply div_le_div_of_nonneg_right _ hk.le
        nlinarith [sq_nonneg p]
      _= p*(1/(k-1)):=by ring
      _≤ p*ε:=mul_le_mul_of_nonneg_left he hp
      _= _:=mul_comm _ _
lemma Pp (B C:Finset P) (hB:2≤ B.card) (ε:ℝ)
    (hk:1/((B.card:ℝ)-1)≤ ε)
    (hn:1/((Fintype.card P:ℝ)-1)≤ ε) :
    (Ad B C - Ad Finset.univ C)^2 -
      ε*(Ad B C+ Ad Finset.univ C)≤ Cn B C:=by
  have hkr:(2:ℝ)≤ B.card:=by exact_mod_cast hB
  have hnr:(2:ℝ)≤ Fintype.card P:=by exact_mod_cast CE B hB
  have hp:=JX (Ad B C) (B.card:ℝ) ε
    (Bd B C) (Dy B C) (by linarith) hk
  have ha:=JX (Ad Finset.univ C) (Fintype.card P:ℝ) ε
    (Bd _ C) (Dy _ C) (by linarith) hn
  rw [MQ,NJ B C hB]
  have hc:0≤2*(B.card:ℝ)/ Fintype.card P:=by positivity
  nlinarith [mul_nonneg hc hp.1]
section Family
variable {I:Type u2} [Fintype I]
variable (w:I→ ℝ) (B:I→ Finset P)
lemma HP (C:Finset P) (M:ℝ)
    (hdom:∀ x,(∑ i,w i* Ae (B i) x)≤ M* Ae Finset.univ x) :
    (∑ i,w i* Ad (B i) C)≤ M* Ad Finset.univ C:=by
  simp_rw [← Ci,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun x _=> hdom x
lemma Pz (C:Finset P) (M ε:ℝ)
    (hw:∀ i,0≤ w i) (hW:(∑ i,w i)≤1) (hε:0≤ ε)
    (hB:∀ i,2≤(B i).card)
    (hk:∀ i,1/(((B i).card:ℝ)-1)≤ ε)
    (hn:1/((Fintype.card P:ℝ)-1)≤ ε)
    (hmean:(∑ i,w i* Ad (B i) C)≤ M* Ad Finset.univ C) :
    (∑ i,w i*(Ad (B i) C - Ad Finset.univ C)^2) -
      ε*(M+1)*Ad Finset.univ C≤(∑ i,w i* Cn (B i) C):=by
  let a:=Ad Finset.univ C
  have ha:0≤ a:=Bd _ _
  have hc:(∑ i,w i* Ad (B i) C)+(∑ i,w i)*a≤(M+1)*a:=by
    have:=mul_le_mul_of_nonneg_right hW ha
    dsimp [a] at *
    linarith
  calc
    _≤(∑ i,w i*(Ad (B i) C - a)^2) -
        ε*((∑ i,w i* Ad (B i) C)+(∑ i,w i)*a):=by
      have:=mul_le_mul_of_nonneg_left hc hε
      dsimp [a] at *
      nlinarith
    _=∑ i,w i*((Ad (B i) C - a)^2 - ε*(Ad (B i) C+a)):=by
      simp only [mul_add,Finset.mul_sum,Finset.sum_mul]
      rw [sub_add_eq_sub_sub,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _≤ _:=Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_left
      (Pp (B i) C (hB i) ε (hk i) hn) (hw i)
lemma SN (C:Finset P) (M ε τ:ℝ)
    (hw:∀ i,0≤ w i) (hW:(∑ i,w i)≤1) (hM:0≤ M) (hε:0≤ ε)
    (hτ:0< τ) (hC:2≤ C.card) (ha:τ≤ Ad Finset.univ C)
    (hB:∀ i,2≤(B i).card)
    (hk:∀ i,1/(((B i).card:ℝ)-1)≤ ε)
    (hn:1/((Fintype.card P:ℝ)-1)≤ ε)
    (hmean:(∑ i,w i* Ad (B i) C)≤ M* Ad Finset.univ C) :
    (∑ i,w i*(Ad (B i) C - Ad Finset.univ C)^2) -
      (2*ε*(M+1)/τ)*Ah Finset.univ C≤(∑ i,w i* Cn (B i) C):=by
  have hcomp:=(Cw C hC).1
  have ha0:=Bd (Finset.univ:Finset P) C
  have hmass:Ad Finset.univ C≤2*Ah Finset.univ C/τ:=by
    apply (le_div_iff₀ hτ).mpr
    nlinarith [mul_le_mul_of_nonneg_right ha ha0]
  have herr:=mul_le_mul_of_nonneg_left hmass (show 0≤ ε*(M+1) by positivity)
  have h:=Pz w B C M ε hw hW hε hB hk hn hmean
  have he:ε*(M+1)*(2*Ah Finset.univ C/τ) =
      (2*ε*(M+1)/τ)*Ah Finset.univ C:=by ring
  rw [he] at herr
  linarith
lemma SS (C:Finset P) (M:ℝ)
    (hw:∀ i,0≤ w i) (hM:0≤ M) (hC:2≤ C.card)
    (hB:∀ i,2≤(B i).card)
    (hmean:(∑ i,w i* Ad (B i) C)≤ M* Ad Finset.univ C) :
    (1/2)*(∑ i,w i*(if 2/((B i).card:ℝ)≤ Ad (B i) C then
      (Ad (B i) C)^2 else 0)) - 4*M*Ah Finset.univ C ≤
      (∑ i,w i* Cn (B i) C):=by
  let a:=Ad Finset.univ C
  have ha0:0≤ a:=Bd _ _
  have hp0:=BJ (Finset.univ:Finset P) C
  have hc:=(Cw C hC).1
  have hterm (i:I) :
      (1/2)*(if 2/((B i).card:ℝ)≤ Ad (B i) C then
        (Ad (B i) C)^2 else 0) - 2*a*Ad (B i) C≤ Cn (B i) C:=by
    have h₁:=PA (B i) C (hB i)
    have h₂:=Mv (B i) C (hB i)
    dsimp [Cn,a] at *
    linarith
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hterm i) (hw i))
  have he:(∑ i,w i*((1/2)*(if 2/((B i).card:ℝ)≤ Ad (B i) C then
        (Ad (B i) C)^2 else 0) - 2*a*Ad (B i) C)) =
      (1/2)*(∑ i,w i*(if 2/((B i).card:ℝ)≤ Ad (B i) C then
        (Ad (B i) C)^2 else 0)) - 2*a*(∑ i,w i* Ad (B i) C):=by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hs
  have hmean':=mul_le_mul_of_nonneg_left hmean (show 0≤2*a by positivity)
  have hcomp:=mul_le_mul_of_nonneg_left hc (show 0≤4*M by positivity)
  dsimp [a] at *
  nlinarith
end Family
section CellIntegral
variable {Ω:Type u3} [MeasurableSpace Ω]
section Quantitative
variable {I:Type u5} [Fintype I]
def Aj (w:I→ ℝ) (B:I→ Finset P) (T:ℝ) (D:Finset P):ℝ :=
  if T< D.card then
    ∑ i,w i*(Ad (B i) D - Ad Finset.univ D)^2
  else (1/2)*∑ i,w i *
    (if 2/((B i).card:ℝ)≤ Ad (B i) D then (Ad (B i) D)^2 else 0)
lemma EL (w:I→ ℝ) (B:I→ Finset P) (T:ℝ)
    (hT:1≤ T) (hB:∀ i,2≤(B i).card) (D:Finset P) (hD:D.card≤1) :
    Aj w B T D=0:=by
  have hd:(D.card:ℝ)≤ T:=(by exact_mod_cast hD:(D.card:ℝ)≤1).trans hT
  simp [Aj,not_lt.mpr hd,Hz _ _ (hB _) hD]
lemma Oc (w:I→ ℝ) (B:I→ Finset P) (T M ε τ:ℝ)
    (hw:∀ i,0≤ w i) (hW:(∑ i,w i)≤1)
    (hT:1≤ T) (hM:0≤ M) (hε:0≤ ε) (hτ:0< τ)
    (hscale:τ* Fintype.card P≤ T)
    (hB:∀ i,2≤(B i).card)
    (hk:∀ i,1/(((B i).card:ℝ)-1)≤ ε)
    (hn:1/((Fintype.card P:ℝ)-1)≤ ε)
    (hdom:∀ x,(∑ i,w i* Ae (B i) x)≤ M* Ae Finset.univ x)
    (D:Finset P) :
    Aj w B T D≤(∑ i,w i* Cn (B i) D) +
      (2*ε*(M+1)/τ)*Ah Finset.univ D +
      4*M*(if (D.card:ℝ)≤ T then Ah Finset.univ D else 0):=by
  have hmean:=HP w B D M hdom
  have herr:0≤(2*ε*(M+1)/τ)*Ah Finset.univ D:=by
    exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε)
      (by linarith)) hτ.le) (BJ _ _)
  by_cases hD:T<(D.card:ℝ)
  · have hd2:2≤ D.card:=by
      have:(1:ℝ)< D.card:=hT.trans_lt hD
      exact_mod_cast (show 1< D.card by exact_mod_cast this)
    have hnp:0<(Fintype.card P:ℝ):=by
      exact_mod_cast (show 0< Fintype.card P by have:=Finset.card_le_univ D; omega)
    have ha:τ≤ Ad Finset.univ D:=by
      simp only [Ad,Finset.univ_inter,Finset.card_univ]
      exact (le_div_iff₀ hnp).mpr (hscale.trans hD.le)
    have hh:=SN w B D M ε τ hw hW hM hε hτ hd2 ha hB hk hn hmean
    simp only [Aj,hD,reduceIte,not_le.mpr hD,mul_zero,add_zero]
    linarith
  · simp only [Aj,hD,reduceIte,not_lt.mp hD]
    by_cases hd2:2≤ D.card
    · have hh:=SS w B D M hw hM hd2 hB hmean
      linarith
    · have hd1:D.card≤1:=by omega
      simp [Hz _ _ (hB _) hd1,Mt _ _ hd1,
        DN _ _ hd1]
end Quantitative
end CellIntegral
end Aa.Variance
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Aa.Bg
open Ak
variable {P:Type u1} [Fintype P] [DecidableEq P]
variable {K:Type u2} [Field K] [NumberField K]
variable (Z:P→ K) (hZ:Function.Injective Z)
def CD (C:Finset P):ℝ :=
  (∑ v:InfinitePlace K,Arithmetic.Bh v*∫ ω,(arch Z v ω).mass C ∂Ao.As) +
    (Module.finrank ℚ K:ℝ)⁻¹*∑ v∈ Bq Z hZ,(finite Z hZ v).mass C
lemma KF (C:Finset P):0≤ CD Z hZ C:=by
  exact add_nonneg
    (Finset.sum_nonneg (fun v _=> mul_nonneg (Arithmetic.EV v)
      (integral_nonneg (fun ω=>(arch Z v ω).Bf C))))
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _=>(finite Z hZ v).Bf C)))
lemma JI (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    (∑ C,CD Z hZ C*(if x∈ C∧ y∈ C then (1:ℝ) else 0))= L Z hZ x y hxy:=by
  simp only [CD,add_mul,Finset.sum_add_distrib,Finset.sum_mul,
    mul_assoc,L]
  rw [← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.mul_sum,Depth.LO (arch Z v) (BA Z hZ v)
      (AO Z hZ v) hn x y hxy]
  · congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    exact (finite Z hZ v).Gh hn x y hxy
end Aa.Bg
namespace Aa.Variance
variable {P:Type u3} [Fintype P] [DecidableEq P]
def Ac (m:Finset P→ ℝ) (f:Finset P→ ℝ):ℝ:=∑ C,m C* f C
def AD (m:Finset P→ ℝ) (x y:P):ℝ :=
  Ac m (fun C=> if x∈ C∧ y∈ C then 1 else 0)
lemma QD (m:Finset P→ ℝ) (b:ℝ) (S:P→ ℝ)
    (hL:∀ x y,x≠ y→ AD m x y= b+S x+S y)
    (B:Finset P) (hB:2≤ B.card):Ac m (Cn B)=0:=by
  have he:Ac m (Cn B) =
      ∑ x,∑ y,CI B x y* AD m x y:=by
    simp only [Ac,MQ]
    have hc (C:Finset P):(∑ x∈ C,∑ y∈ C,CI B x y) =
        ∑ x,∑ y,CI B x y*(if x∈ C∧ y∈ C then (1:ℝ) else 0):=by
      simp only [mul_ite,mul_one,mul_zero,ite_and]
      simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
      simp
    simp_rw [hc,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp only [AD,Ac,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  rw [he]
  exact QF B hB _ b S hL
lemma OU {I:Type u4} [Fintype I]
    (m:Finset P→ ℝ) (hm:∀ C,0≤ m C) (b:ℝ) (S:P→ ℝ)
    (hL:∀ x y,x≠ y→ AD m x y= b+S x+S y)
    (w:I→ ℝ) (B:I→ Finset P) (T M ε τ:ℝ)
    (hw:∀ i,0≤ w i) (hW:(∑ i,w i)≤1)
    (hT:1≤ T) (hM:0≤ M) (hε:0≤ ε) (hτ:0< τ)
    (hscale:τ* Fintype.card P≤ T)
    (hB:∀ i,2≤(B i).card)
    (hk:∀ i,1/(((B i).card:ℝ)-1)≤ ε)
    (hn:1/((Fintype.card P:ℝ)-1)≤ ε)
    (hdom:∀ x,(∑ i,w i* Ae (B i) x)≤ M* Ae Finset.univ x) :
    Ac m (Aj w B T) ≤
      (2*ε*(M+1)/τ)*Ac m (Ah Finset.univ) +
      4*M*Ac m (fun C=> if (C.card:ℝ)≤ T then Ah Finset.univ C else 0):=by
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun C _ =>
    mul_le_mul_of_nonneg_left
      (Oc w B T M ε τ hw hW hT hM hε hτ hscale hB hk hn hdom C) (hm C))
  simp only [mul_add,Finset.sum_add_distrib] at hh
  have hz:(∑ C,m C*∑ i,w i* Cn (B i) C)=0:=by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hi (i:I):(∑ C,m C*(w i* Cn (B i) C))=0:=by
      calc
        _= w i* Ac m (Cn (B i)):=by
          simp only [Ac,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro C _
          ring
        _=0:=by rw [QD m b S hL _ (hB i),mul_zero]
    simp_rw [hi]
    exact Finset.sum_const_zero
  rw [hz,zero_add] at hh
  simp only [← mul_add] at hh
  change Ac m (Aj w B T)≤ _ at hh
  have he₁:(∑ C,m C*(2*ε*(M+1)/τ* Ah Finset.univ C)) =
      (2*ε*(M+1)/τ)*Ac m (Ah Finset.univ):=by
    simp only [Ac,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  have he₂:(∑ C,m C*(4*M*(if (C.card:ℝ)≤ T then Ah Finset.univ C else 0))) =
      4*M*Ac m (fun C=> if (C.card:ℝ)≤ T then Ah Finset.univ C else 0):=by
    simp only [Ac,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  rwa [he₁,he₂] at hh
end Aa.Variance
namespace Aa.Bg
open Ak Variance
variable {P:Type u5} [Fintype P] [DecidableEq P]
variable {K:Type u6} [Field K] [NumberField K]
variable (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
def totalMass (C:Finset P):ℝ:=CD Z₁ h₁ C+ CD Z₂ h₂ C
def BB (x:P):ℝ:=S Z₁ h₁ x+ S Z₂ h₂ x
def Gn:ℝ:=2*Ao.Mu - M Z₁ h₁ - M Z₂ h₂
lemma Bi (C:Finset P):0≤ totalMass Z₁ Z₂ h₁ h₂ C :=
  add_nonneg (KF Z₁ h₁ C) (KF Z₂ h₂ C)
lemma Fc (x:P):0≤ BB Z₁ Z₂ h₁ h₂ x :=
  add_nonneg (SM Z₁ h₁ x) (SM Z₂ h₂ x)
lemma EW (hn:2≤ Fintype.card P) (x y:P) (hxy:x≠ y) :
    AD (totalMass Z₁ Z₂ h₁ h₂) x y =
      Gn Z₁ Z₂ h₁ h₂+ BB Z₁ Z₂ h₁ h₂ x+ BB Z₁ Z₂ h₁ h₂ y:=by
  simp only [AD,Ac,totalMass,add_mul,Finset.sum_add_distrib]
  rw [JI Z₁ h₁ hn x y hxy,JI Z₂ h₂ hn x y hxy,
    Fi Z₁ h₁ hn x y hxy,Fi Z₂ h₂ hn x y hxy]
  simp only [Gn,BB]
  ring
theorem MT {I:Type u7} [Fintype I]
    (hnP:2≤ Fintype.card P)
    (w:I→ ℝ) (B:I→ Finset P) (T M₀ ε τ:ℝ)
    (hw:∀ i,0≤ w i) (hW:(∑ i,w i)≤1)
    (hT:1≤ T) (hM:0≤ M₀) (hε:0≤ ε) (hτ:0< τ)
    (hscale:τ* Fintype.card P≤ T)
    (hB:∀ i,2≤(B i).card)
    (hk:∀ i,1/(((B i).card:ℝ)-1)≤ ε)
    (hn:1/((Fintype.card P:ℝ)-1)≤ ε)
    (hdom:∀ x,(∑ i,w i* Ae (B i) x)≤ M₀* Ae Finset.univ x) :
    Ac (totalMass Z₁ Z₂ h₁ h₂) (Aj w B T) ≤
      (2*ε*(M₀+1)/τ)*Ac (totalMass Z₁ Z₂ h₁ h₂) (Ah Finset.univ) +
      4*M₀*Ac (totalMass Z₁ Z₂ h₁ h₂)
        (fun C=> if (C.card:ℝ)≤ T then Ah Finset.univ C else 0) :=
  OU _ (Bi Z₁ Z₂ h₁ h₂) _ _
    (EW Z₁ Z₂ h₁ h₂ hnP) w B T M₀ ε τ hw hW hT hM hε hτ hscale hB hk hn hdom
end Aa.Bg
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u1} [Fintype P] [DecidableEq P]
variable (d:Depth P)
def AF (x:P) (r:ℝ):Prop:=Fintype.card P<2*(d.cell r x).card
instance (x:P) (r:ℝ):Decidable (d.AF x r):=Classical.propDecidable _
omit [DecidableEq P] in
lemma PF (x:P) {r t:ℝ} (htr:t≤ r) (hr:d.AF x r) :
    d.AF x t:=by
  classical
  have hc:=Finset.card_le_card (d.Hh htr x)
  unfold AF at *
  omega
omit [DecidableEq P] in
lemma Qr (x:P) (r:ℝ):d.AF x r ↔
    ∃ C:Finset P,Fintype.card P<2*C.card∧∀ y∈ C,d.share r x y:=by
  classical
  constructor
  · intro h; exact ⟨d.cell r x,h,fun y hy=>(d.BN r x y).mp hy⟩
  · rintro ⟨C,hc,hC⟩
    have hsub:C⊆ d.cell r x:=fun y hy=>(d.BN r x y).mpr (hC y hy)
    have:=Finset.card_le_card hsub
    unfold AF
    omega
lemma Mp (x:P):IsClosed {r:ℝ | d.AF x r}:=by
  classical
  simp_rw [d.Qr,Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro C
  simp only [Set.ofPred_and]
  apply IsClosed.inter
  · by_cases h:Fintype.card P<2*C.card <;> simp [h]
  · simp_rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    by_cases hxy:x= y
    · simp [share,hxy]
    · simp only [share,hxy,false_or]
      exact isClosed_le continuous_id continuous_const
def Hg (x:P):ℝ:=sSup {r:ℝ | d.AF x r}
lemma IM (hn:2≤ Fintype.card P) (x:P) (r:ℝ) :
    d.AF x r↔ r≤ d.Hg x:=by
  classical
  have hlo:d.AF x (-d.radius):=by
    classical
    unfold AF
    rw [d.EO le_rfl,Finset.card_univ]
    omega
  have hle:∀ t,d.AF x t→ t≤ d.radius:=by
    classical
    intro t ht
    exact d.Ek hn ⟨d.cell t x,(d.CY t _).mpr ⟨d.CX t x,ht⟩⟩
  have hne:Set.Nonempty {t:ℝ | d.AF x t}:=⟨-d.radius,hlo⟩
  have hbd:BddAbove {t:ℝ | d.AF x t}:=⟨d.radius,fun t ht=> hle t ht⟩
  have hmem:d.AF x (d.Hg x):=(d.Mp x).csSup_mem hne hbd
  exact ⟨fun hr=> le_csSup hbd hr,fun hr=> d.PF x hr hmem⟩
lemma Hf (x:P) (r:ℝ) :
    d.AF x r↔(d.AR r).Nonempty∧ x∈ d.DL r:=by
  classical
  constructor
  · intro hs
    have hc:d.cell r x∈ d.AR r:=(d.CY r _).mpr ⟨d.CX r x,hs⟩
    exact ⟨⟨_,hc⟩,by rw [d.Gj hc]; exact d.CQ r x⟩
  · rintro ⟨⟨G,hG⟩,hx⟩
    rw [d.Gj hG] at hx
    obtain ⟨hGc,hGm⟩:=(d.CY r G).mp hG
    rwa [d.Cx hGc hx] at hGm
lemma OS (hn:2≤ Fintype.card P) (x:P) (h H:ℝ) (hH:0≤ H) :
    (∫ r:ℝ,if d.AF x (h-r-H)∧¬d.AF x (h-r+H) then (1:ℝ) else 0)=2*H:=by
  classical
  have he:(fun r:ℝ=> if d.AF x (h-r-H)∧¬d.AF x (h-r+H) then (1:ℝ) else 0) =
      (Set.Ico (h-H-d.Hg x) (h+H-d.Hg x)).indicator (fun _=>(1:ℝ)):=by
    classical
    funext r
    simp only [d.IM hn,not_le,Set.indicator_apply,Set.mem_Ico]
    congr 1
    apply propext
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [he,integral_indicator measurableSet_Ico]
  rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith:h-H-d.Hg x≤ h+H-d.Hg x),intervalIntegral.integral_const]
  simp
  ring
def Hr (y:P) (T:ℝ):Finset (Finset P):=by
  classical
  exact Finset.univ.filter (fun C=>∃ r:ℝ,C= d.cell r y∧(C.card:ℝ)< T)
def AZ (y:P) (T:ℝ):Finset P:=(d.Hr y T).biUnion id
omit [DecidableEq P] in
lemma Qo (y:P) (T:ℝ) {C E:Finset P}
    (hC:C∈ d.Hr y T) (hE:E∈ d.Hr y T):C⊆ E∨ E⊆ C:=by
  classical
  obtain ⟨r,rfl,hr⟩:=(Finset.mem_filter.mp hC).2
  obtain ⟨t,rfl,ht⟩:=(Finset.mem_filter.mp hE).2
  rcases le_total t r with h | h
  · exact Or.inl (d.Hh h y)
  · exact Or.inr (d.Hh h y)
lemma No (y:P) (T:ℝ) (hT:0< T) :
    ((d.AZ y T).card:ℝ)< T:=by
  classical
  by_cases hne:(d.Hr y T).Nonempty
  · obtain ⟨C,hC,hmax⟩:=Finset.exists_max_image (d.Hr y T) Finset.card hne
    have he:d.AZ y T= C:=by
      classical
      apply Finset.Subset.antisymm
      · intro x hx
        obtain ⟨E,hE,hx⟩:=Finset.mem_biUnion.mp hx
        change x∈ E at hx
        rcases d.Qo y T hE hC with h | h
        · exact h hx
        · have he:C= E:=Finset.eq_of_subset_of_card_le h (hmax E hE)
          simpa only [he] using hx
      · intro x hx
        exact Finset.mem_biUnion.mpr ⟨C,hC,hx⟩
    rw [he]
    obtain ⟨r,hr,ht⟩:=(Finset.mem_filter.mp hC).2
    exact ht
  · rw [AZ,Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa using hT
lemma Jq (y x:P) (r T:ℝ)
    (hxy:y∈ d.cell r x) (hT:((d.cell r x).card:ℝ)< T) :
    x∈ d.AZ y T:=by
  classical
  have he:=d.Eh ((d.BN r x y).mp hxy)
  apply Finset.mem_biUnion.mpr
  refine ⟨d.cell r y,?_,(d.BN r y x).mpr (d.Qs ((d.BN r x y).mp hxy))⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,r,rfl,by rwa [← he]⟩
end Aa.Ak.Depth
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u2} [Fintype P] [DecidableEq P]
variable (d:Depth P)
lemma Nb (y:P) (T:ℝ) (hne:(d.AZ y T).Nonempty) :
    y∈ d.AZ y T:=by
  classical
  obtain ⟨x,hx⟩:=hne
  obtain ⟨C,hC,hx⟩:=Finset.mem_biUnion.mp hx
  obtain ⟨r,rfl,hr⟩:=(Finset.mem_filter.mp hC).2
  apply Finset.mem_biUnion.mpr
  exact ⟨d.cell r y,hC,d.CQ r y⟩
lemma Jb (hn:2≤ Fintype.card P) (y:P)
    (τ:ℝ) (hτ:0< τ) (hτ1:τ≤1) :
    ((d.AZ y (τ*Fintype.card P)).erase y).card≤ τ*((Fintype.card P:ℝ)-1):=by
  classical
  have hn0:0<(Fintype.card P:ℝ):=by exact_mod_cast (show 0< Fintype.card P by omega)
  have hn1:0≤(Fintype.card P:ℝ)-1:=by
    have:(2:ℝ)≤ Fintype.card P:=by exact_mod_cast hn
    linarith
  by_cases hne:(d.AZ y (τ*Fintype.card P)).Nonempty
  · have hy:=d.Nb y _ hne
    have hc:=d.No y (τ*Fintype.card P) (mul_pos hτ hn0)
    rw [Finset.card_erase_of_mem hy,Nat.cast_sub (Finset.one_le_card.mpr hne),Nat.cast_one]
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.erase_empty,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg hτ.le hn1
end Aa.Ak.Depth
namespace Aa.AL
open MeasureTheory
variable {P:Type u3} [Fintype P] [DecidableEq P]
def mass (p:P→ ℝ) (C:Finset P):ℝ:=∑ y∈ C,p y
omit [Fintype P] [DecidableEq P] in
lemma Bf {p:P→ ℝ} (hp:∀ y,0≤ p y) (C:Finset P):0≤ mass p C :=
  Finset.sum_nonneg (fun y _=> hp y)
omit [Fintype P] [DecidableEq P] in
lemma TD {p:P→ ℝ} (hp:∀ y,0≤ p y) {C D:Finset P} (h:C⊆ D) :
    mass p C≤ mass p D:=Finset.sum_le_sum_of_subset_of_nonneg h (fun y _ _=> hp y)
omit [DecidableEq P] in
lemma Tb {p:P→ ℝ} (hp:∀ y,0≤ p y) (h1:∑ y,p y=1) (C:Finset P) :
    mass p C≤1:=by rw [← h1]; exact TD hp (Finset.subset_univ C)
omit [Fintype P] in
lemma Re (p:P→ ℝ) (C D:Finset P) :
    mass p C= mass p (C \ D)+ mass p (C∩ D):=by
  classical
  symm
  have hh:=Finset.sum_sdiff (f:=p) (Finset.inter_subset_left (s₁:=C) (s₂:=D))
  have he:C \ (C∩ D)= C \ D:=by ext y; simp
  rw [he] at hh
  exact hh
lemma Tp (p:P→ ℝ) (hp:∀ y,0≤ p y) (h1:∑ y,p y=1)
    (C D:Finset P):1≤ mass p C+ mass p D+ mass p (C∪ D)ᶜ:=by
  classical
  rw [← h1]
  have he:=Finset.sum_compl_add_sum (C∪ D) p
  have hu:=(Finset.sum_union_inter (s₁:=C) (s₂:=D) (f:=p))
  have hn:=Bf hp (C∩ D)
  unfold mass at *
  linarith
lemma Rm (p:P→ ℝ) (hp:∀ y,0≤ p y) (h1:∑ y,p y=1)
    (C D:Finset P) (lam:ℝ) (hlam:0≤ lam) (hlam2:lam≤1/2)
    (hC:mass p C≤ lam) :
    mass p C≤2*lam*mass p D+ mass p (C∪ D)ᶜ:=by
  classical
  have hc:=Tp p hp h1 C D
  have hnC:=Bf hp C
  have hnD:=Bf hp D
  have hnE:=Bf hp (C∪D)ᶜ
  have hp2:mass p C≤1/2:=hC.trans hlam2
  nlinarith
end Aa.AL
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u4} [Fintype P] [DecidableEq P]
variable (d:Depth P)
lemma KR {r:ℝ} {x y:P} (hg:¬ d.AF x r)
    (hy:y∈ d.cell r x):1≤ d.Bb r x y:=by
  classical
  have hs:=(d.BN r x y).mp hy
  rw [d.CF,if_pos hs]
  by_cases he:(d.AR r).Nonempty
  · have hx:x∉ d.DL r:=by
      intro hx
      exact hg ((d.Hf x r).mpr ⟨he,hx⟩)
    have hy':y∉ d.DL r:=by
      intro hy'
      have hgy:=(d.Hf y r).mpr ⟨he,hy'⟩
      exact hg (by simpa only [AF,d.Eh hs] using hgy)
    simp [BW,Ai,he,hx,hy']
  · simp [BW,Ai,he]
end Aa.Ak.Depth
namespace Aa.AL
open MeasureTheory Ak
variable {P:Type u5} [Fintype P] [DecidableEq P]
lemma Ed (p:P→ ℝ) (C:Finset P) :
    mass p C=∑ y,if y∈ C then p y else 0:=by
  classical
  simp [mass]
lemma QU (p:P→ ℝ) (x:P) (hx:p x=0) (C:Finset P) :
    mass p C=∑ y,if x≠ y∧ y∈ C then p y else 0:=by
  classical
  rw [Ed]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy:x= y
  · subst y; simp [hx]
  · simp [hxy]
lemma Na (d:Depth P) (p:P→ ℝ) (hp:∀ y,0≤ p y)
    (x:P) (r:ℝ) :
    (if ¬d.AF x r then mass p (d.cell r x) else 0) ≤
      ∑ y,p y* d.Bb r x y:=by
  classical
  by_cases hg:d.AF x r
  · simp only [hg,not_true_eq_false,ite_false]
    exact Finset.sum_nonneg (fun y _=> mul_nonneg (hp y) (d.Dq r x y).1)
  · simp only [hg,not_false_eq_true,ite_true]
    rw [Ed]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy:y∈ d.cell r x
    · simp only [hy,ite_true]
      nlinarith [d.KR hg hy,hp y]
    · simpa only [hy,ite_false] using mul_nonneg (hp y) (d.Dq r x y).1
lemma KM (a b:ℝ) :
    (∫ r:ℝ,if a< r∧ r< b then (1:ℝ) else 0)= max (b-a) 0:=by
  have he:(fun r:ℝ=> if a< r∧ r< b then (1:ℝ) else 0) =
      (Set.Ioo a b).indicator (fun _:ℝ=>(1:ℝ)):=by
    funext r; simp [Set.indicator_apply]
  rw [he,integral_indicator measurableSet_Ioo]
  simp [integral_const,measureReal_def,Real.volume_Ioo,ENNReal.toReal_ofReal']
lemma JL (a b:ℝ) :
    (∫ r:ℝ,if a≤ r∧ r≤ b then (1:ℝ) else 0)= max (b-a) 0:=by
  have he:(fun r:ℝ=> if a≤ r∧ r≤ b then (1:ℝ) else 0) =
      (Set.Icc a b).indicator (fun _:ℝ=>(1:ℝ)):=by
    funext r; simp [Set.indicator_apply]
  rw [he,integral_indicator measurableSet_Icc]
  simp [integral_const,measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal']
lemma Gi (a b:ℝ) :
    Integrable (fun r:ℝ=> if a< r∧ r< b then (1:ℝ) else 0):=by
  have he:(fun r:ℝ=> if a< r∧ r< b then (1:ℝ) else 0) =
      (Set.Ioo a b).indicator (fun _:ℝ=>(1:ℝ)):=by
    funext r; simp [Set.indicator_apply]
  rw [he,integrable_indicator_iff measurableSet_Ioo]
  exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
lemma Fy (a b:ℝ) :
    Integrable (fun r:ℝ=> if a≤ r∧ r≤ b then (1:ℝ) else 0):=by
  have he:(fun r:ℝ=> if a≤ r∧ r≤ b then (1:ℝ) else 0) =
      (Set.Icc a b).indicator (fun _:ℝ=>(1:ℝ)):=by
    funext r; simp [Set.indicator_apply]
  rw [he,integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
def Eb (d d':Depth P) (p:P→ ℝ) (x:P) (h H r:ℝ):ℝ :=
  mass p (d.cell r x∪ d'.cell (h-r-H) x)ᶜ
def ED (d d':Depth P) (p:P→ ℝ) (x:P) (h H r:ℝ):ℝ :=
  mass p (d.cell r x∩ d'.cell (h-r+H) x)
lemma IP (d d':Depth P) (p:P→ ℝ) (x:P) (hx:p x=0)
    (h H r:ℝ) :
    Eb d d' p x h H r=∑ y,p y *
      (if d.value x y< r∧ r< h-H-d'.value x y then (1:ℝ) else 0):=by
  classical
  rw [Eb,Ed]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy:x= y
  · subst y; simp [hx]
  · simp only [Finset.mem_compl,Finset.mem_union,Depth.BN,Depth.share,hxy,false_or,not_or,not_le]
    have he:(d.value x y< r∧ d'.value x y< h-r-H) ↔
        d.value x y< r∧ r< h-H-d'.value x y:=by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
    simp only [he]
    split_ifs <;> simp
lemma Jg (d d':Depth P) (p:P→ ℝ) (x:P) (hx:p x=0)
    (h H r:ℝ) :
    ED d d' p x h H r=∑ y,p y *
      (if h+H-d'.value x y≤ r∧ r≤ d.value x y then (1:ℝ) else 0):=by
  classical
  rw [ED,Ed]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy:x= y
  · subst y; simp [hx]
  · simp only [Finset.mem_inter,Depth.BN,Depth.share,hxy,false_or]
    have he:(r≤ d.value x y∧ h-r+H≤ d'.value x y) ↔
        h+H-d'.value x y≤ r∧ r≤ d.value x y:=by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
    simp only [he]
    split_ifs <;> simp
lemma He (d d':Depth P) (p:P→ ℝ) (x:P) (hx:p x=0)
    (h H:ℝ):Integrable (Eb d d' p x h H):=by
  change Integrable (fun r=> Eb d d' p x h H r)
  simp_rw [IP d d' p x hx]
  exact integrable_finsetSum _ (fun y _=>(Gi _ _).const_mul (p y))
lemma HI (d d':Depth P) (p:P→ ℝ) (x:P) (hx:p x=0)
    (h H:ℝ):Integrable (ED d d' p x h H):=by
  change Integrable (fun r=> ED d d' p x h H r)
  simp_rw [Jg d d' p x hx]
  exact integrable_finsetSum _ (fun y _=>(Fy _ _).const_mul (p y))
lemma Nd (d d':Depth P) (p:P→ ℝ) (x:P) (hx:p x=0)
    (h H:ℝ):(∫ r,Eb d d' p x h H r) =
      ∑ y,p y* max (h-d.value x y-d'.value x y-H) 0:=by
  simp_rw [IP d d' p x hx]
  rw [integral_finsetSum _ (fun y _=>(Gi _ _).const_mul (p y))]
  simp_rw [integral_const_mul,KM]
  apply Finset.sum_congr rfl
  intro y _
  congr 2; ring
lemma Oe (d d':Depth P) (p:P→ ℝ) (x:P) (hx:p x=0)
    (h H:ℝ):(∫ r,ED d d' p x h H r) =
      ∑ y,p y* max (d.value x y+d'.value x y-h-H) 0:=by
  simp_rw [Jg d d' p x hx]
  rw [integral_finsetSum _ (fun y _=>(Fy _ _).const_mul (p y))]
  simp_rw [integral_const_mul,JL]
  apply Finset.sum_congr rfl
  intro y _
  congr 2; ring
lemma QE (a H:ℝ) (hH:0≤ H) :
    max (-a-H) 0+ max (a-H) 0= max (|a|-H) 0:=by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha,max_eq_right (by linarith : -a-H≤0),zero_add]
  · rw [abs_of_nonpos ha,max_eq_right (by linarith:a-H≤0),add_zero]
lemma QT (d d':Depth P) (p:P→ ℝ) (x:P) (hx:p x=0)
    (h H:ℝ) (hH:0≤ H) :
    (∫ r,Eb d d' p x h H r+ ED d d' p x h H r) =
      ∑ y,p y* max (|d.value x y+d'.value x y-h|-H) 0:=by
  rw [integral_add (He d d' p x hx h H) (HI d d' p x hx h H),
    Nd d d' p x hx,Oe d d' p x hx,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  have he:h-d.value x y-d'.value x y-H = -(d.value x y+d'.value x y-h)-H:=by ring
  rw [he,← mul_add,QE _ H hH]
end Aa.AL
namespace Aa.AL
open MeasureTheory Ak
variable {P:Type u6} [Fintype P] [DecidableEq P]
def CJ (d:Depth P) (p:P→ ℝ) (x:P) (T lam r:ℝ):ℝ:=by
  classical
  exact if ¬d.AF x r∧((d.cell r x).card:ℝ)< T∧ mass p (d.cell r x)< lam
    then mass p (d.cell r x) else 0
def BS (d:Depth P) (p:P→ ℝ) (x:P) (r:ℝ):ℝ :=
  if ¬d.AF x r then mass p (d.cell r x) else 0
def EK (d:Depth P) (x:P) (h H r:ℝ):ℝ :=
  if d.AF x (h-r-H)∧¬d.AF x (h-r+H) then 1 else 0
def Dx (d d':Depth P) (p:P→ ℝ) (x:P) (T t:ℝ):ℝ:=by
  classical
  exact ∑ y,p y*(if x∈(d.AZ y T).erase y then d'.Ai t y else 0)
lemma Nc (d d':Depth P) (p:P→ ℝ) (hp:∀ y,0≤ p y)
    (x:P) (T t:ℝ):0≤ Dx d d' p x T t:=by
  classical
  exact Finset.sum_nonneg (fun y _=> mul_nonneg (hp y) (by split_ifs; exact (d'.BP t y).1; rfl))
omit [DecidableEq P] in
lemma HU (d:Depth P) (p:P→ ℝ) (hp:∀ y,0≤ p y)
    (x:P) (r:ℝ):0≤ BS d p x r:=by
  unfold BS
  split_ifs <;> first | exact Bf hp _ | rfl
lemma Qg (d d':Depth P) (p:P→ ℝ) (hp:∀ y,0≤ p y)
    (x:P) (hx:p x=0) (r t T:ℝ)
    (hT:((d.cell r x).card:ℝ)< T) (hg:d'.AF x t) :
    mass p (d.cell r x \ d'.cell t x)≤ Dx d d' p x T t:=by
  classical
  rw [QU p x hx]
  unfold Dx
  apply Finset.sum_le_sum
  intro y _
  by_cases hy:x≠ y∧ y∈ d.cell r x \ d'.cell t x
  · obtain ⟨hxy,hyD⟩:=hy
    obtain ⟨hyU,hyV⟩:=Finset.mem_sdiff.mp hyD
    have hn:x∈(d.AZ y T).erase y :=
      Finset.mem_erase.mpr ⟨hxy,d.Jq y x r T hyU hT⟩
    have hG:d'.cell t x∈ d'.AR t:=(d'.CY t _).mpr ⟨d'.CX t x,hg⟩
    have he:(d'.AR t).Nonempty:=⟨_,hG⟩
    have hyo:y∉ d'.DL t:=by rwa [d'.Gj hG]
    simp [hxy,hyD,hn,Depth.Ai,he,hyo]
  · simp only [hy,ite_false]
    exact mul_nonneg (hp y) (by split_ifs; exact (d'.BP t y).1; rfl)
lemma PV (d d':Depth P) (p:P→ ℝ) (hp:∀ y,0≤ p y)
    (h1:∑ y,p y=1) (x:P) (hx:p x=0) (h H T lam r:ℝ)
    (hlam:0≤ lam) (hlam2:lam≤1/2) :
    CJ d p x T lam r ≤
      2*lam*BS d' p x (h-r-H)+ lam*EK d' x h H r +
      Eb d d' p x h H r+ ED d d' p x h H r +
      Dx d d' p x T (h-r+H):=by
  classical
  have hminus:0≤ Eb d d' p x h H r:=Bf hp _
  have hplus:0≤ ED d d' p x h H r:=Bf hp _
  have hnbr:=Nc d d' p hp x T (h-r+H)
  have hng:=HU d' p hp x (h-r-H)
  have hstr:0≤ EK d' x h H r:=by unfold EK; split_ifs <;> norm_num
  unfold CJ
  split_ifs with ha
  · obtain ⟨haG,haT,haP⟩:=ha
    by_cases hg:d'.AF x (h-r-H)
    · by_cases hg':d'.AF x (h-r+H)
      · have hthree:=Qg d d' p hp x hx r (h-r+H) T haT hg'
        have he:=Re p (d.cell r x) (d'.cell (h-r+H) x)
        change mass p (d.cell r x)= _+ ED d d' p x h H r at he
        nlinarith
      · have hs:EK d' x h H r=1:=by simp [EK,hg,hg']
        rw [hs]
        nlinarith
    · have hone:=Rm p hp h1 (d.cell r x) (d'.cell (h-r-H) x) lam hlam hlam2 haP.le
      have hnge:BS d' p x (h-r-H)= mass p (d'.cell (h-r-H) x):=by
        simp [BS,hg]
      rw [hnge]
      change mass p (d.cell r x)≤ _+ Eb d d' p x h H r at hone
      nlinarith
  · positivity
omit [DecidableEq P] in
lemma Kn (d:Depth P) (p:P→ ℝ) (x:P) :
    Measurable (BS d p x):=by
  classical
  let f:Finset P→ ℝ:=fun C=> if ¬Fintype.card P<2*C.card then mass p C else 0
  have h:=(measurable_of_finite f).comp (d.Ey x)
  have he:BS d p x= f∘(fun r=> d.cell r x):=by
    funext r
    by_cases hg:Fintype.card P<2*(d.cell r x).card
    · simp [BS,f,Depth.AF,hg]
    · simp [BS,f,Depth.AF,hg]
  rw [he]
  exact h
omit [DecidableEq P] in
lemma LA (d:Depth P) (p:P→ ℝ) (x:P) (T lam:ℝ) :
    Measurable (CJ d p x T lam):=by
  classical
  let f:Finset P→ ℝ:=fun C=> if ¬Fintype.card P<2*C.card∧(C.card:ℝ)< T∧ mass p C< lam
      then mass p C else 0
  have h:=(measurable_of_finite f).comp (d.Ey x)
  have he:CJ d p x T lam= f∘(fun r=> d.cell r x):=by
    funext r
    by_cases hg:Fintype.card P<2*(d.cell r x).card
    · simp [CJ,f,Depth.AF,hg]
    · simp [CJ,f,Depth.AF,hg,Nat.not_lt.mp hg]
  rw [he]
  exact h
omit [DecidableEq P] in
lemma Eu (d:Depth P) (hn:2≤ Fintype.card P)
    (p:P→ ℝ) (hp:∀ y,0≤ p y) (h1:∑ y,p y=1) (x:P) (hx:p x=0) :
    Integrable (BS d p x):=by
  classical
  apply Depth.Ct (Kn d p x) (a:=-d.radius) (b:=d.radius) (C:=1)
  · intro r
    rw [Real.norm_eq_abs,abs_of_nonneg (HU d p hp x r)]
    unfold BS
    split_ifs <;> first | exact Tb hp h1 _ | norm_num
  · intro r hr
    by_cases hlo:r ≤ -d.radius
    · have hG:d.AF x r:=by
        unfold Depth.AF
        rw [d.EO hlo x,Finset.card_univ]
        omega
      simp [BS,hG]
    · have hhi:d.radius< r:=by
        by_contra! hhi
        exact hr ⟨(not_le.mp hlo).le,hhi⟩
      simp only [BS]
      rw [d.FY hhi x]
      have he:mass p {x}=0:=by simp [mass,hx]
      split_ifs <;> simp [he]
omit [DecidableEq P] in
lemma Fd (d:Depth P) (hn:2≤ Fintype.card P)
    (p:P→ ℝ) (hp:∀ y,0≤ p y) (h1:∑ y,p y=1) (x:P) (hx:p x=0)
    (T lam:ℝ):Integrable (CJ d p x T lam):=by
  classical
  apply (Eu d hn p hp h1 x hx).mono'
    (LA d p x T lam).aestronglyMeasurable
  filter_upwards with r
  unfold CJ BS
  split_ifs <;> simp_all [abs_of_nonneg (Bf hp (d.cell r x)),Bf hp]
lemma MV (d:Depth P) (hn:2≤ Fintype.card P) (x:P) (h H:ℝ) :
    Integrable (EK d x h H):=by
  classical
  have he:EK d x h H =
      (Set.Ico (h-H-d.Hg x) (h+H-d.Hg x)).indicator (fun _:ℝ=>(1:ℝ)):=by
    funext r
    simp only [EK,d.IM hn,not_le,Set.indicator_apply,Set.mem_Ico]
    congr 1
    apply propext
    constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
  rw [he,integrable_indicator_iff measurableSet_Ico]
  exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
lemma Ki (d d':Depth P) (hn:2≤ Fintype.card P)
    (p:P→ ℝ) (x:P) (T:ℝ):Integrable (Dx d d' p x T):=by
  classical
  unfold Dx
  apply integrable_finsetSum
  intro y _
  apply Integrable.const_mul
  by_cases h:x∈(d.AZ y T).erase y
  · simpa only [h,ite_true] using d'.Bo hn y
  · simp only [h,ite_false]
    exact integrable_zero _ _ _
lemma LW (d d':Depth P) (hn:2≤ Fintype.card P)
    (p:P→ ℝ) (x:P) (T:ℝ) :
    (∫ r,Dx d d' p x T r) =
      ∑ y,p y*(if x∈(d.AZ y T).erase y then d'.Ag y else 0):=by
  classical
  unfold Dx
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y _
    rw [integral_const_mul]
    by_cases hh:x∈(d.AZ y T).erase y
    · simp only [hh,ite_true,Depth.Ag]
    · simp only [hh,ite_false,integral_zero]
  · intro y _
    apply Integrable.const_mul
    by_cases hh:x∈(d.AZ y T).erase y
    · simpa only [hh,ite_true] using d'.Bo hn y
    · simp only [hh,ite_false]; exact integrable_zero _ _ _
end Aa.AL
namespace Aa.AL
open MeasureTheory Ak
variable {P:Type u7} [Fintype P] [DecidableEq P]
lemma MR (d:Depth P) (hn:2≤ Fintype.card P)
    (p:P→ ℝ) (x:P) (hx:p x=0) :
    Integrable (fun r=>∑ y,p y* d.Bb r x y):=by
  apply integrable_finsetSum
  intro y _
  by_cases hxy:x= y
  · subst y; simp only [hx,zero_mul]; exact integrable_zero _ _ _
  · exact (d.Dj hn x y hxy).const_mul _
lemma IK (d:Depth P) (hn:2≤ Fintype.card P)
    (p:P→ ℝ) (hp:∀ y,0≤ p y) (h1:∑ y,p y=1) (x:P) (hx:p x=0) :
    (∫ r,BS d p x r)≤∑ y,p y*∫ r,d.Bb r x y:=by
  calc
    _≤∫ r:ℝ,∑ y,p y* d.Bb r x y :=
      integral_mono (Eu d hn p hp h1 x hx) (MR d hn p x hx)
        (fun r=> Na d p hp x r)
    _= _:=by
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl (fun y _=> integral_const_mul (p y) _)
      · intro y _
        by_cases hxy:x= y
        · subst y; simp only [hx,zero_mul]; exact integrable_zero _ _ _
        · exact (d.Dj hn x y hxy).const_mul _
lemma QB (d d':Depth P) (hn:2≤ Fintype.card P)
    (p:P→ ℝ) (hp:∀ y,0≤ p y) (h1:∑ y,p y=1)
    (x:P) (hx:p x=0) (h H T lam:ℝ)
    (hH:0≤ H) (hlam:0≤ lam) (hlam2:lam≤1/2) :
    (∫ r,CJ d p x T lam r) ≤
      2*lam*(∑ y,p y*∫ r,d'.Bb r x y)+2*lam*H +
      (∑ y,p y* max (|d.value x y+d'.value x y-h|-H) 0) +
      ∑ y,p y*(if x∈(d.AZ y T).erase y then d'.Ag y else 0):=by
  classical
  have hshift₁ (r:ℝ):h-r-H=(h-H)-r:=by ring
  have hshift₂ (r:ℝ):h-r+H=(h+H)-r:=by ring
  have hi₁:Integrable (fun r=>2*lam*BS d' p x (h-r-H)):=by
    simp_rw [hshift₁]
    exact ((integrable_comp_sub_left _ (h-H)).mpr (Eu d' hn p hp h1 x hx)).const_mul _
  have hi₂:Integrable (fun r=> lam*EK d' x h H r) :=
    (MV d' hn x h H).const_mul _
  have hi₃:=(He d d' p x hx h H).add (HI d d' p x hx h H)
  have hi₄:Integrable (fun r=> Dx d d' p x T (h-r+H)):=by
    simp_rw [hshift₂]
    exact (integrable_comp_sub_left _ (h+H)).mpr (Ki d d' hn p x T)
  have hb:=integral_mono (Fd d hn p hp h1 x hx T lam)
    (((hi₁.add hi₂).add hi₃).add hi₄) (fun r=> by
      have hh:=PV d d' p hp h1 x hx h H T lam r hlam hlam2
      dsimp only [Pi.add_apply]
      linarith)
  simp only [Pi.add_apply] at hb
  have he₁:=integral_add ((hi₁.add hi₂).add hi₃) hi₄
  have he₂:=integral_add (hi₁.add hi₂) hi₃
  have he₃:=integral_add hi₁ hi₂
  simp only [Pi.add_apply] at he₁ he₂ he₃
  rw [he₁,he₂,he₃] at hb
  rw [integral_const_mul,integral_const_mul] at hb
  simp_rw [hshift₁,hshift₂] at hb
  rw [integral_sub_left_eq_self,integral_sub_left_eq_self,
    LW d d' hn p x T,QT d d' p x hx h H hH] at hb
  have hs:(∫ r,EK d' x h H r)=2*H:=d'.OS hn x h H hH
  rw [hs] at hb
  have hng:=mul_le_mul_of_nonneg_left (IK d' hn p hp h1 x hx)
    (show 0≤2*lam by positivity)
  linarith
def Av {I:Type u8} [Fintype I] (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P) (a b:P):ℝ :=
  ∑ i,if x i= a then w i* p i b else 0
lemma Mi {I:Type u9} [Fintype I]
    (d d':Depth P) (hn:2≤ Fintype.card P)
    (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (B τ:ℝ) (hB:0≤ B) (hτ:0< τ) (hτ1:τ≤1)
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ i,w i*∑ y,p i y *
      (if x i∈(d.AZ y (τ*Fintype.card P)).erase y then d'.Ag y else 0)) ≤
      B*τ/Fintype.card P*∑ y,d'.Ag y:=by
  classical
  have hn0:0<(Fintype.card P:ℝ):=by exact_mod_cast (show 0< Fintype.card P by omega)
  have hn1:0<(Fintype.card P:ℝ)-1:=by
    have:(2:ℝ)≤ Fintype.card P:=by exact_mod_cast hn
    linarith
  have hid (y:P) :
      (∑ i,w i*(p i y*(if x i∈(d.AZ y (τ*Fintype.card P)).erase y then d'.Ag y else 0))) =
      (∑ a∈(d.AZ y (τ*Fintype.card P)).erase y,Av w p x a y)* d'.Ag y:=by
    rw [Finset.sum_mul]
    simp only [Av,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    have he:(∑ a∈(d.AZ y (τ*Fintype.card P)).erase y,
        if x i= a then w i*p i y else 0) =
        if x i∈(d.AZ y (τ*Fintype.card P)).erase y then w i*p i y else 0:=by
      simp [eq_comm]
    rw [he]
    split_ifs <;> ring
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hid]
  have hb (y:P):(∑ a∈(d.AZ y (τ*Fintype.card P)).erase y,Av w p x a y)≤ B*τ/Fintype.card P:=by
    calc
      _≤((d.AZ y (τ*Fintype.card P)).erase y).card *
          (B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))):=by
        calc
          _≤∑ a∈(d.AZ y (τ*Fintype.card P)).erase y,
              B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1)) :=
            Finset.sum_le_sum (fun a ha=> hdom a y (Finset.ne_of_mem_erase ha))
          _= _:=by simp
      _≤(τ*((Fintype.card P:ℝ)-1))*(B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :=
        mul_le_mul_of_nonneg_right (d.Jb hn y τ hτ hτ1) (by positivity)
      _= _:=by field_simp
  exact Finset.sum_le_sum (fun y _=> mul_le_mul_of_nonneg_right (hb y) (d'.BM y))
end Aa.AL
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Aa.AL
open MeasureTheory Ak Variance
variable {P:Type u1} {I:Type u2} [Fintype P] [DecidableEq P] [Fintype I]
def slice (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P) (lam:ℝ) (C:Finset P):ℝ :=
  ∑ i,w i*(if x i∈ C∧ mass (p i) C< lam then mass (p i) C else 0)
def Cl (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P) (C:Finset P):ℝ :=
  ∑ a∈ C,∑ b∈ C,Av w p x a b
omit [Fintype P] in
lemma Ej (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P) (C:Finset P) :
    Cl w p x C=∑ i,w i*(if x i∈ C then mass (p i) C else 0):=by
  classical
  unfold Cl Av
  calc
    _=∑ a∈ C,∑ i,∑ b∈ C,if x i= a then w i* p i b else 0:=by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _=∑ i,∑ a∈ C,∑ b∈ C,if x i= a then w i* p i b else 0:=Finset.sum_comm
    _= _:=by
      apply Finset.sum_congr rfl
      intro i _
      have he (a:P):(∑ b∈ C,if x i= a then w i*p i b else 0) =
          if x i= a then w i*mass (p i) C else 0:=by
        by_cases h:x i= a <;> simp [h,mass,Finset.mul_sum]
      simp_rw [he]
      by_cases h:x i∈ C <;> simp [h,eq_comm]
omit [Fintype P] in
lemma OP (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hw:∀ i,0≤ w i) (hp:∀ i y,0≤ p i y) (lam:ℝ) (C:Finset P) :
    slice w p x lam C≤ Cl w p x C:=by
  rw [Ej]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  split_ifs <;> simp_all [Bf (hp i)]
omit [Fintype P] in
lemma SF (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) (lam:ℝ) (hlam:0≤ lam) (C:Finset P) :
    slice w p x lam C≤ lam:=by
  calc
    _≤∑ i,w i* lam:=by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      split_ifs with h
      · exact h.2.le
      · exact hlam
    _= _:=by rw [← Finset.sum_mul,hW,one_mul]
omit [Fintype P] in
lemma HA (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hx:∀ i,p i (x i)=0) (a:P):Av w p x a a=0:=by
  classical
  apply Finset.sum_eq_zero
  intro i _
  by_cases h:x i= a
  · rw [if_pos h,← h,hx i,mul_zero]
  · simp [h]
lemma Nz (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hx:∀ i,p i (x i)=0) (B:ℝ)
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1)))
    (C:Finset P):Cl w p x C≤ B*Ah Finset.univ C:=by
  classical
  simp only [Ah,Finset.mul_sum,Cl]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases hab:a= b
  · subst b; simp [HA w p x hx,IU]
  · simpa [Az,hab,div_eq_mul_inv] using hdom a b hab
omit [Fintype P] in
lemma Hs (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hx:∀ i,p i (x i)=0) (lam:ℝ) (C:Finset P) (hC:C.card≤1) :
    slice w p x lam C=0:=by
  classical
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi:x i∈ C
  · have he:C={x i}:=Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi,fun y hy=>(Finset.card_le_one.mp hC y hy (x i) hi)⟩
    simp [he,mass,hx]
  · simp [hi]
lemma Jn (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) (hn:2≤ Fintype.card P)
    (lam τ:ℝ) (hlam:0≤ lam) (hτ:0< τ)
    (hτn:2≤ τ*(Fintype.card P:ℝ)) (C:Finset P)
    (hC:τ*(Fintype.card P:ℝ)≤ C.card) :
    slice w p x lam C≤(2*lam/τ^2)*Ah Finset.univ C:=by
  have hn0:0<(Fintype.card P:ℝ):=by exact_mod_cast (show 0< Fintype.card P by omega)
  have hm:2≤ C.card:=by exact_mod_cast hτn.trans hC
  have hcomp:=(Cw C hm).1
  have ha:τ≤ Ad Finset.univ C:=by
    simpa [Ad] using (le_div_iff₀ hn0).mpr hC
  have hτsq:τ^2≤(Ad Finset.univ C)^2:=sq_le_sq₀ hτ.le (hτ.le.trans ha) |>.mpr ha
  have hlow:τ^2≤2*Ah Finset.univ C:=by linarith
  have hmul:=mul_le_mul_of_nonneg_left hlow hlam
  have he:lam≤(2*lam/τ^2)*Ah Finset.univ C:=by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
    nlinarith
  exact (SF w p x hw hW lam hlam C).trans he
lemma Pd (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hw:∀ i,0≤ w i) (hp:∀ i y,0≤ p i y) (hx:∀ i,p i (x i)=0)
    (B τ lam:ℝ) (hB:0≤ B) (hτ:0≤ τ)
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1)))
    (C:Finset P) (hC:(C.card:ℝ)< τ*Fintype.card P) :
    slice w p x lam C≤ B*τ*Ad Finset.univ C:=by
  by_cases hm:2≤ C.card
  · have hn:0<(Fintype.card P:ℝ):=by exact_mod_cast (show 0< Fintype.card P from lt_of_lt_of_le (by omega) (Finset.card_le_univ C))
    have ha:Ad Finset.univ C≤ τ:=by
      simpa [Ad] using (div_le_iff₀ hn).mpr hC.le
    have ha0:0≤ Ad (Finset.univ:Finset P) C:=Bd _ _
    calc
      _≤ B*Ah Finset.univ C:=(OP w p x hw hp lam C).trans (Nz w p x hx B hdom C)
      _≤ B*(Ad Finset.univ C)^2:=mul_le_mul_of_nonneg_left (Cw C hm).2 hB
      _≤ B*τ*Ad Finset.univ C:=by nlinarith [mul_nonneg hB (mul_nonneg ha0 (sub_nonneg.mpr ha))]
  · rw [Hs w p x hx lam C (by omega)]
    exact mul_nonneg (mul_nonneg hB hτ) (Bd _ _)
end Aa.AL
namespace Aa.Ak.Depth
variable {P:Type u3} [Fintype P] [DecidableEq P]
variable (d:Depth P)
lemma QI (f:Finset P→ ℝ) (r:ℝ) (x:P) :
    (∑ C∈ d.cells r,if x∈ C then f C else 0)= f (d.cell r x):=by
  classical
  have he:∀ C∈ d.cells r,(if x∈ C then f C else 0) =
      if C= d.cell r x then f (d.cell r x) else 0:=by
    intro C hC
    by_cases hx:x∈ C
    · rw [d.Cx hC hx]; simp [d.Jr]
    · have hn:C≠ d.cell r x:=by intro h; apply hx; rw [h]; exact d.CQ r x
      simp [hx,hn]
  rw [Finset.sum_congr rfl he]
  simp [d.CX r x]
lemma It (f:Finset P→ ℝ) (r:ℝ) :
    d.Ch f r =
      (∑ C∈ d.cells r,if ¬Fintype.card P<2*C.card then f C else 0) +
      ∑ C∈ d.AR r,f Cᶜ:=by
  classical
  simp only [Ch,transformed,Multiset.map_add,Multiset.sum_add,
    Multiset.map_map,Function.comp_def]
  change (∑ C∈(d.cells r).filter (fun C=>¬Fintype.card P<2*C.card),f C)+ _= _
  rw [Finset.sum_filter]
  rfl
lemma MS (r:ℝ) :
    (∑ C∈ d.AR r,Variance.Ad Finset.univ Cᶜ) =
      (∑ y,d.Ai r y)/(Fintype.card P:ℝ):=by
  classical
  by_cases hg:(d.AR r).Nonempty
  · obtain ⟨G,hG⟩:=hg
    have hs:d.AR r={G}:=Finset.ext fun C=> by
      simp only [Finset.mem_singleton]
      exact ⟨fun hC=> d.GW hC hG,fun h=> h ▸ hG⟩
    have hne:(d.AR r).Nonempty:=⟨G,hG⟩
    have hi (y:P):d.Ai r y= if y∈ Gᶜ then 1 else 0:=by
      simp [Ai,hne,d.Gj hG]
    simp_rw [hi]
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,mul_one]
    simp [hs,Variance.Ad]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hg,Ai]
end Aa.Ak.Depth
namespace Aa.AL
open MeasureTheory Ak Variance
variable {P:Type u4} {I:Type u5} [Fintype P] [DecidableEq P] [Fintype I]
lemma My (d:Depth P) (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (T lam r:ℝ) :
    (∑ C∈ d.cells r,if ¬Fintype.card P<2*C.card∧(C.card:ℝ)< T then slice w p x lam C else 0) =
      ∑ i,w i* CJ d (p i) (x i) T lam r:=by
  classical
  have he (C:Finset P) :
      (if ¬Fintype.card P<2*C.card∧(C.card:ℝ)< T then slice w p x lam C else 0) =
      ∑ i,w i*(if x i∈ C then
        (if ¬Fintype.card P<2*C.card∧(C.card:ℝ)< T∧ mass (p i) C< lam then mass (p i) C else 0) else 0):=by
    by_cases h:¬Fintype.card P<2*C.card∧(C.card:ℝ)< T
    · simp only [h,slice]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx:x i∈ C <;> simp [hx]
    · simp only [h,ite_false]
      symm
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hx hh
      · exact False.elim (h ⟨hh.1,hh.2.1⟩)
      · exact mul_zero _
      · exact mul_zero _
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.mul_sum,d.QI]
  congr 1
  unfold CJ Depth.AF
  split_ifs <;> rfl
lemma Qx (d:Depth P) (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) (hp:∀ i y,0≤ p i y)
    (hx:∀ i,p i (x i)=0) (hn:2≤ Fintype.card P)
    (B τ lam r:ℝ) (hB:0≤ B) (hlam:0≤ lam) (hτ:0< τ)
    (hτn:2≤ τ*(Fintype.card P:ℝ))
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    d.Ch (slice w p x lam) r ≤
      (2*lam/τ^2)*d.Ch (Ah Finset.univ) r +
      B*τ/(Fintype.card P:ℝ)*(∑ y,d.Ai r y) +
      ∑ i,w i*CJ d (p i) (x i) (τ*Fintype.card P) lam r:=by
  classical
  have hcoef:0≤2*lam/τ^2:=by positivity
  have hnng:∀ C:Finset P,0≤(2*lam/τ^2)*Ah Finset.univ C :=
    fun C=> mul_nonneg hcoef (BJ _ _)
  have hactual :
      (∑ C∈ d.cells r,if ¬Fintype.card P<2*C.card then slice w p x lam C else 0) ≤
      (2*lam/τ^2)*(∑ C∈ d.cells r,if ¬Fintype.card P<2*C.card then Ah Finset.univ C else 0) +
      ∑ i,w i*CJ d (p i) (x i) (τ*Fintype.card P) lam r:=by
    rw [←My,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro C _
    by_cases hg:¬Fintype.card P<2*C.card
    · by_cases hc:(C.card:ℝ)< τ*Fintype.card P
      · simp only [hg,hc,not_false_eq_true,true_and,ite_true]
        linarith [hnng C]
      · simp only [hg,hc,not_false_eq_true,true_and,ite_true,ite_false,add_zero]
        exact Jn w p x hw hW hn lam τ hlam hτ hτn C (le_of_not_gt hc)
    · simp [hg]
  have hgiant:(∑ C∈ d.AR r,slice w p x lam Cᶜ) ≤
      (2*lam/τ^2)*(∑ C∈ d.AR r,Ah Finset.univ Cᶜ) +
      B*τ*(∑ C∈ d.AR r,Ad Finset.univ Cᶜ):=by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro C _
    by_cases hc:(Cᶜ.card:ℝ)< τ*Fintype.card P
    · exact (Pd w p x hw hp hx B τ lam hB hτ.le hdom Cᶜ hc).trans (le_add_of_nonneg_left (hnng Cᶜ))
    · exact (Jn w p x hw hW hn lam τ hlam hτ hτn Cᶜ (le_of_not_gt hc)).trans
        (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hB hτ.le) (Bd _ _)))
  rw [d.MS] at hgiant
  rw [d.It,d.It]
  have he:B*τ*((∑ y,d.Ai r y)/(Fintype.card P:ℝ)) =
      B*τ/(Fintype.card P:ℝ)*(∑ y,d.Ai r y):=by ring
  rw [he] at hgiant
  linarith
end Aa.AL
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u6} [Fintype P] [DecidableEq P]
variable (d:Depth P)
lemma Er (hn:2≤ Fintype.card P) (f:Finset P→ ℝ)
    (hf:∀ C,C.card≤1→ f C=0):Integrable (d.Ch f):=by
  change Integrable (fun r=> d.Ch f r)
  simp_rw [d.Fe]
  apply integrable_finsetSum
  intro C _
  by_cases hC:2≤ C.card
  · exact (d.GZ hn C hC).mul_const _
  · simp only [hf C (by omega),mul_zero]
    exact integrable_zero _ _ _
end Aa.Ak.Depth
namespace Aa.AL
open MeasureTheory Ak Variance
variable {P:Type u7} {I:Type u8} [Fintype P] [DecidableEq P] [Fintype I]
lemma Ro (d:Depth P) (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) (hp:∀ i y,0≤ p i y)
    (hp1:∀ i,∑ y,p i y=1) (hx:∀ i,p i (x i)=0) (hn:2≤ Fintype.card P)
    (B τ lam:ℝ) (hB:0≤ B) (hlam:0≤ lam) (hτ:0< τ)
    (hτn:2≤ τ*(Fintype.card P:ℝ))
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C,d.mass C* slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C,d.mass C*Ah Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*(∑ y,d.Ag y) +
      ∑ i,w i*(∫ r,CJ d (p i) (x i) (τ*Fintype.card P) lam r):=by
  classical
  have hi₁:=(d.Er hn (Ah Finset.univ) (DN _)).const_mul (2*lam/τ^2)
  have hi₂:=(integrable_finsetSum (s:=Finset.univ) (fun y _=> d.Bo hn y)).const_mul (B*τ/Fintype.card P)
  have hi₃:=integrable_finsetSum (s:=Finset.univ) (fun i _ =>
    (Fd d hn (p i) (hp i) (hp1 i) (x i) (hx i) (τ*Fintype.card P) lam).const_mul (w i))
  have hb:=integral_mono (d.Er hn _ (Hs w p x hx lam))
    ((hi₁.add hi₂).add hi₃) (fun r=> Qx d w p x hw hW hp hx hn B τ lam r hB hlam hτ hτn hdom)
  have ha:=integral_add (hi₁.add hi₂) hi₃
  have hb':=integral_add hi₁ hi₂
  simp only [Pi.add_apply] at hb ha hb'
  rw [ha,hb',integral_const_mul,integral_const_mul,
    d.DB hn _ (DN _),
    d.DB hn _ (Hs w p x hx lam),
    integral_finsetSum _ (fun y _=> d.Bo hn y),
    integral_finsetSum _ (fun i _ =>
      (Fd d hn (p i) (hp i) (hp1 i) (x i) (hx i) (τ*Fintype.card P) lam).const_mul (w i))] at hb
  simpa only [integral_const_mul,Depth.Ag] using hb
lemma Pc (d d':Depth P) (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) (hp:∀ i y,0≤ p i y)
    (hp1:∀ i,∑ y,p i y=1) (hx:∀ i,p i (x i)=0) (hn:2≤ Fintype.card P)
    (h:I→ ℝ) (B τ lam H:ℝ) (hB:0≤ B) (hlam:0≤ lam) (hlam2:lam≤1/2)
    (hτ:0< τ) (hτ1:τ≤1) (hτn:2≤ τ*(Fintype.card P:ℝ)) (hH:0≤ H)
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C,d.mass C* slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C,d.mass C*Ah Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y,d.Ag y)+(∑ y,d'.Ag y)) +
      2*lam*(∑ i,w i*∑ y,p i y*∫ r,d'.Bb r (x i) y)+2*lam*H +
      ∑ i,w i*∑ y,p i y*max (|d.value (x i) y+d'.value (x i) y-h i|-H) 0:=by
  have hb:=Ro d w p x hw hW hp hp1 hx hn B τ lam hB hlam hτ hτn hdom
  have ha:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=> mul_le_mul_of_nonneg_left
    (QB d d' hn (p i) (hp i) (hp1 i) (x i) (hx i) (h i) H (τ*Fintype.card P) lam hH hlam hlam2) (hw i))
  have hnbr:=Mi d d' hn w p x B τ hB hτ hτ1 hdom
  simp only [mul_add,Finset.sum_add_distrib] at ha
  have hc:(∑ i,w i*(2*lam*H))=2*lam*H:=by rw [←Finset.sum_mul,hW,one_mul]
  have hi:(∑ i,w i*(2*lam*(∑ y,p i y*∫ r,d'.Bb r (x i) y))) =
      2*lam*(∑ i,w i*(∑ y,p i y*∫ r,d'.Bb r (x i) y)):=by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _=> by ring)
  rw [hc,hi] at ha
  linarith
end Aa.AL
namespace Aa.AL
open MeasureTheory Ak Variance
variable {P:Type u9} {I:Type u10} [Fintype P] [DecidableEq P] [Fintype I]
lemma La (d:Depth P) (hn:2≤ Fintype.card P)
    (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P) (hx:∀ i,p i (x i)=0) :
    (∑ i,w i*∑ y,p i y*∫ r,d.Bb r (x i) y) =
      ∑ C,d.mass C* Cl w p x C:=by
  classical
  have hpair (i:I) (y:P) :
      p i y*(∫ r,d.Bb r (x i) y) =
      ∑ C,d.mass C*(if x i∈ C∧ y∈ C then p i y else 0):=by
    by_cases hxy:x i= y
    · subst y; simp [hx]
    · have h:=d.Gh hn (x i) y hxy
      dsimp [Depth.AN] at h
      rw [← h,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C _
      split_ifs <;> ring
  simp_rw [hpair,Finset.mul_sum]
  conv_lhs=> arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [Ej,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi:x i∈ C
  · simp only [hi,true_and,ite_true,Ed,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  · simp [hi]
lemma FR (d d':Depth P) (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) (hp:∀ i y,0≤ p i y)
    (hp1:∀ i,∑ y,p i y=1) (hx:∀ i,p i (x i)=0) (hn:2≤ Fintype.card P)
    (h:I→ ℝ) (B τ lam H:ℝ) (hB:0≤ B) (hlam:0≤ lam) (hlam2:lam≤1/2)
    (hτ:0< τ) (hτ1:τ≤1) (hτn:2≤ τ*(Fintype.card P:ℝ)) (hH:0≤ H)
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C,d.mass C* slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C,d.mass C*Ah Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y,d.Ag y)+(∑ y,d'.Ag y)) +
      2*lam*B*(∑ C,d'.mass C*Ah Finset.univ C)+2*lam*H +
      ∑ i,w i*∑ y,p i y*max (|d.value (x i) y+d'.value (x i) y-h i|-H) 0:=by
  have hb:=Pc d d' w p x hw hW hp hp1 hx hn h B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom
  rw [La d' hn w p x hx] at hb
  have hd:(∑ C,d'.mass C*Cl w p x C)≤ B*∑ C,d'.mass C*Ah Finset.univ C:=by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C _
    calc
      _≤ d'.mass C*(B*Ah Finset.univ C):=mul_le_mul_of_nonneg_left (Nz w p x hx B hdom C) (d'.Bf C)
      _= _:=by ring
  have hh:=mul_le_mul_of_nonneg_left hd (show 0≤2*lam by positivity)
  nlinarith
end Aa.AL
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Aa.Ao
open MeasureTheory
lemma DV {z w:ℂ} (hne:z≠ w) (t:ℝ) :
    Integrable (fun ω=> max (|error ω z w|-t) 0) As :=
  (((Bn hne).abs.sub (integrable_const t)).sup (integrable_zero _ _ _))
lemma Hm {z w:ℂ} (hne:z≠ w) {t:ℝ} (ht:0≤ t) :
    (∫ ω,max (|error ω z w|-t) 0 ∂As)≤4*Real.exp (-t):=by
  have hm:Measurable (fun ω=> max (|error ω z w|-t) 0) :=
    ((Fp hne).abs.sub_const t).max measurable_const
  have hn (ω:AS):0≤ max (|error ω z w|-t) 0:=le_max_right _ _
  have hi:=DV hne t
  have he:IntegrableOn (fun u:ℝ=>(4*Real.exp (-t))*Real.exp (-u)) (Set.Ioi 0) volume:=by
    simpa only [neg_one_mul,IntegrableOn] using
      (integrableOn_exp_mul_Ioi (by norm_num:(-1:ℝ)<0) 0).const_mul (4*Real.exp (-t))
  have hb:(∫⁻ ω,ENNReal.ofReal (max (|error ω z w|-t) 0) ∂As) ≤
      ENNReal.ofReal (4*Real.exp (-t)):=by
    rw [lintegral_eq_lintegral_meas_lt As
      (Filter.Eventually.of_forall hn) hm.aemeasurable]
    calc
      _≤∫⁻ u:ℝ in Set.Ioi 0,ENNReal.ofReal ((4*Real.exp (-t))*Real.exp (-u)):=by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0:0< u:=hu
        have hs:{ω:AS | u< max (|error ω z w|-t) 0} =
            {ω:AS | u+t < |error ω z w|}:=by
          ext ω
          simp only [Set.mem_ofPred_eq,lt_max_iff]
          constructor
          · rintro (h | h) <;> linarith
          · intro h; exact Or.inl (by linarith)
        rw [hs,← ENNReal.ofReal_toReal (measure_ne_top As _)]
        have hh:=MY hne (add_nonneg hu.le ht)
        apply ENNReal.ofReal_le_ofReal
        calc
          _≤4*Real.exp (-(u+t)):=hh
          _= _:=by rw [neg_add,Real.exp_add]; ring
      _= ENNReal.ofReal (4*Real.exp (-t)):=by
        rw [← ofReal_integral_eq_lintegral_ofReal he (by filter_upwards with u; positivity)]
        congr 1
        rw [integral_const_mul]
        have hz:=integral_exp_mul_Ioi (by norm_num:(-1:ℝ)<0) (0:ℝ)
        simp only [neg_one_mul,mul_zero,Real.exp_zero,neg_div_neg_eq,div_one] at hz
        rw [hz,mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
lemma Nf (a b H:ℝ) :
    max (|a+b|-H) 0≤2*max (|a|-H/2) 0+2*max (|b|-H/2) 0:=by
  apply max_le
  · have ht:=abs_add_le a b
    have h₁:=le_max_left (|a|-H/2) 0
    have h₂:=le_max_left (|b|-H/2) 0
    have h₃:=le_max_right (|a|-H/2) 0
    have h₄:=le_max_right (|b|-H/2) 0
    linarith
  · positivity
lemma OT {z₁ w₁ z₂ w₂:ℂ} (h₁:z₁≠ w₁) (h₂:z₂≠ w₂)
    {H:ℝ} (hH:0≤ H) :
    (∫ ω,max (|error ω z₁ w₁+ error ω z₂ w₂|-H) 0 ∂As) ≤
      16*Real.exp (-H/2):=by
  have hi:Integrable (fun ω=> max (|error ω z₁ w₁+ error ω z₂ w₂|-H) 0) As:=by
    exact Integrable.sup (((Bn h₁).add (Bn h₂)).abs.sub
      (integrable_const H)) (integrable_zero _ _ _)
  have hia:=DV h₁ (H/2)
  have hib:=DV h₂ (H/2)
  have hh:=integral_mono hi ((hia.const_mul 2).add (hib.const_mul 2))
    (fun ω=> Nf (error ω z₁ w₁) (error ω z₂ w₂) H)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hia.const_mul 2) (hib.const_mul 2)] at hh
  simp only [integral_const_mul] at hh
  have hta:=Hm h₁ (div_nonneg hH (by norm_num:(0:ℝ)≤2))
  have htb:=Hm h₂ (div_nonneg hH (by norm_num:(0:ℝ)≤2))
  rw [neg_div'] at hta htb
  linarith
end Aa.Ao
namespace Aa.Bg
open Ak Variance AL
variable {P:Type u1} {I:Type u2} [Fintype P] [DecidableEq P] [Fintype I]
variable {K:Type u3} [Field K] [NumberField K]
variable (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
include h₁ h₂
lemma OX (v:InfinitePlace K) (a b:P) (hab:a≠ b) (t:K)
    (ht:(Z₁ a-Z₁ b)*(Z₂ a-Z₂ b)=t) :
    (fun ω=>(arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)) =ᵐ[Ao.As]
      (fun ω=> Ao.error ω (v.embedding (Z₁ a)) (v.embedding (Z₁ b))+
        Ao.error ω (v.embedding (Z₂ a)) (v.embedding (Z₂ b))):=by
  have he:=Arithmetic.Gk v.val (Z₁ a-Z₁ b) (Z₂ a-Z₂ b)
    (sub_ne_zero.mpr (h₁.ne hab)) (sub_ne_zero.mpr (h₂.ne hab))
  rw [ht] at he
  change -Real.log (v (Z₁ a-Z₁ b)) + -Real.log (v (Z₂ a-Z₂ b)) = -Real.log (v t) at he
  filter_upwards [DE Z₁ h₁ v hab,DE Z₂ h₂ v hab] with ω hA hB
  rw [hA,hB]
  simp only [Ao.error,← map_sub,InfinitePlace.norm_embedding_eq]
  linarith
lemma Ql (v:InfinitePlace K) (a b:P) (hab:a≠ b) (t:K)
    (ht:(Z₁ a-Z₁ b)*(Z₂ a-Z₂ b)=t) (H:ℝ) (hH:0≤ H) :
    (∫ ω,max (|(arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)|-H) 0 ∂Ao.As) ≤
      16*Real.exp (-H/2):=by
  have he:=OX Z₁ Z₂ h₁ h₂ v a b hab t ht
  have he':(fun ω=> max (|(arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)|-H) 0) =ᵐ[Ao.As]
      (fun ω=> max (|Ao.error ω (v.embedding (Z₁ a)) (v.embedding (Z₁ b))+
        Ao.error ω (v.embedding (Z₂ a)) (v.embedding (Z₂ b))|-H) 0):=by
    filter_upwards [he] with ω hh
    rw [hh]
  rw [integral_congr_ae he']
  exact Ao.OT (Bx Z₁ h₁ v hab) (Bx Z₂ h₂ v hab) hH
lemma Hw (v:InfinitePlace K) (w:I→ ℝ) (p:I→ P→ ℝ)
    (x:I→ P) (t:I→ K) (hw:∀ i,0≤ w i) (hW:∑ i,w i=1)
    (hp:∀ i y,0≤ p i y) (hp1:∀ i,∑ y,p i y=1) (hx:∀ i,p i (x i)=0)
    (ht:∀ i y,p i y≠0→(Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (H:ℝ) (hH:0≤ H) :
    (∫ ω,∑ i,w i*∑ y,p i y*max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0 ∂Ao.As)≤16*Real.exp (-H/2):=by
  have hi (i:I) (y:P):Integrable (fun ω=> max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0) Ao.As :=
    ((((AO Z₁ h₁ v _ _).add (AO Z₂ h₂ v _ _)).add (integrable_const _)).abs.sub
      (integrable_const H)).sup (integrable_zero _ _ _)
  rw [integral_finsetSum _ (fun i _=>(integrable_finsetSum (s:=Finset.univ)
    (fun y _=>(hi i y).const_mul _)).const_mul _)]
  simp_rw [integral_const_mul,integral_finsetSum _ (fun y _=>(hi _ y).const_mul _),integral_const_mul]
  calc
    _≤∑ i,w i*∑ y,p i y*(16*Real.exp (-H/2)):=by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      apply Finset.sum_le_sum
      intro y _
      by_cases hy:p i y=0
      · simp [hy]
      · have hxy:x i≠ y:=by intro he; rw [← he,hx i] at hy; exact hy rfl
        exact mul_le_mul_of_nonneg_left (Ql Z₁ Z₂ h₁ h₂ v _ _ hxy _ (ht i y hy) H hH) (hp i y)
    _= _:=by simp only [← Finset.sum_mul,hp1,one_mul,hW]
lemma PO (hn:2≤ Fintype.card P) (v:InfinitePlace K)
    (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P) (t:I→ K)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) (hp:∀ i y,0≤ p i y)
    (hp1:∀ i,∑ y,p i y=1) (hx:∀ i,p i (x i)=0)
    (ht:∀ i y,p i y≠0→(Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam H:ℝ) (hB:0≤ B) (hlam:0≤ lam) (hlam2:lam≤1/2)
    (hτ:0< τ) (hτ1:τ≤1) (hτn:2≤ τ*(Fintype.card P:ℝ)) (hH:0≤ H)
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C,(∫ ω,(arch Z₁ v ω).mass C ∂Ao.As)*slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C,(∫ ω,(arch Z₁ v ω).mass C ∂Ao.As)*Ah Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y,∫ ω,(arch Z₁ v ω).Ag y ∂Ao.As)+
        (∑ y,∫ ω,(arch Z₂ v ω).Ag y ∂Ao.As)) +
      2*lam*B*(∑ C,(∫ ω,(arch Z₂ v ω).mass C ∂Ao.As)*Ah Finset.univ C)+2*lam*H +
      16*Real.exp (-H/2):=by
  have hiM₁ (C:Finset P):=Depth.Du (arch Z₁ v) (BA Z₁ h₁ v)
    (AO Z₁ h₁ v) hn C
  have hiM₂ (C:Finset P):=Depth.Du (arch Z₂ v) (BA Z₂ h₂ v)
    (AO Z₂ h₂ v) hn C
  have hiS₁ (y:P):=Depth.Cj (arch Z₁ v) (BA Z₁ h₁ v)
    (AO Z₁ h₁ v) hn y
  have hiS₂ (y:P):=Depth.Cj (arch Z₂ v) (BA Z₂ h₂ v)
    (AO Z₂ h₂ v) hn y
  have hiE (i:I) (y:P):Integrable (fun ω=> max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0) Ao.As:=by
    have hd:=((AO Z₁ h₁ v (x i) y).add (AO Z₂ h₂ v (x i) y)).add
      (integrable_const (Real.log (v (t i))))
    exact (hd.abs.sub (integrable_const H)).sup (integrable_zero _ _ _)
  have hA:=(integrable_finsetSum (s:=Finset.univ) (fun C _=>(hiM₁ C).mul_const (Ah Finset.univ C))).const_mul (2*lam/τ^2)
  have hS:=((integrable_finsetSum (s:=Finset.univ) (fun y _=> hiS₁ y)).add
    (integrable_finsetSum (s:=Finset.univ) (fun y _=> hiS₂ y))).const_mul (B*τ/Fintype.card P)
  have hA':=(integrable_finsetSum (s:=Finset.univ) (fun C _=>(hiM₂ C).mul_const (Ah Finset.univ C))).const_mul (2*lam*B)
  have hE:=integrable_finsetSum (s:=Finset.univ) (fun i _ =>
    (integrable_finsetSum (s:=Finset.univ) (fun y _=>(hiE i y).const_mul (p i y))).const_mul (w i))
  have hb:=integral_mono (integrable_finsetSum (s:=Finset.univ) (fun C _=>(hiM₁ C).mul_const (slice w p x lam C)))
    ((((hA.add hS).add hA').add (integrable_const (2*lam*H))).add hE)
    (fun ω=> by
      simpa only [Pi.add_apply,sub_neg_eq_add] using
        (FR (arch Z₁ v ω) (arch Z₂ v ω) w p x hw hW hp hp1 hx hn
          (fun i => -Real.log (v (t i))) B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom))
  have hI₁:=integral_add (((hA.add hS).add hA').add (integrable_const (2*lam*H))) hE
  have hI₂:=integral_add ((hA.add hS).add hA') (integrable_const (2*lam*H))
  have hI₃:=integral_add (hA.add hS) hA'
  have hI₄:=integral_add hA hS
  have hI₅:=integral_add (integrable_finsetSum (s:=Finset.univ) (fun y _=> hiS₁ y))
    (integrable_finsetSum (s:=Finset.univ) (fun y _=> hiS₂ y))
  simp only [Pi.add_apply] at hb hI₁ hI₂ hI₃ hI₄ hI₅
  rw [hI₁,hI₂,hI₃,hI₄] at hb
  simp only [integral_const,probReal_univ,one_smul,integral_const_mul] at hb
  rw [hI₅] at hb
  rw [integral_finsetSum _ (fun C _=>(hiM₁ C).mul_const (slice w p x lam C)),
    integral_finsetSum _ (fun C _=>(hiM₁ C).mul_const (Ah Finset.univ C)),
    integral_finsetSum _ (fun C _=>(hiM₂ C).mul_const (Ah Finset.univ C)),
    integral_finsetSum _ (fun y _=> hiS₁ y),integral_finsetSum _ (fun y _=> hiS₂ y)] at hb
  simp only [integral_mul_const] at hb
  have he:=Hw Z₁ Z₂ h₁ h₂ v w p x t hw hW hp hp1 hx ht H hH
  linarith
lemma Oo (hn:2≤ Fintype.card P) (v:FinitePlace K)
    (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P) (t:I→ K)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) (hp:∀ i y,0≤ p i y)
    (hp1:∀ i,∑ y,p i y=1) (hx:∀ i,p i (x i)=0)
    (ht:∀ i y,p i y≠0→(Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam:ℝ) (hB:0≤ B) (hlam:0≤ lam) (hlam2:lam≤1/2)
    (hτ:0< τ) (hτ1:τ≤1) (hτn:2≤ τ*(Fintype.card P:ℝ))
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C,(finite Z₁ h₁ v).mass C*slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C,(finite Z₁ h₁ v).mass C*Ah Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y,(finite Z₁ h₁ v).Ag y)+(∑ y,(finite Z₂ h₂ v).Ag y)) +
      2*lam*B*(∑ C,(finite Z₂ h₂ v).mass C*Ah Finset.univ C):=by
  have hb:=FR (finite Z₁ h₁ v) (finite Z₂ h₂ v) w p x hw hW hp hp1 hx hn
    (fun i => -Real.log (v (t i))) B τ lam 0 hB hlam hlam2 hτ hτ1 hτn (le_refl _) hdom
  have he (i:I) (y:P):p i y* max (|(finite Z₁ h₁ v).value (x i) y+
      (finite Z₂ h₂ v).value (x i) y- -Real.log (v (t i))|-0) 0=0:=by
    by_cases hy:p i y=0
    · simp [hy]
    · have hxy:x i≠ y:=by intro he; rw [← he,hx i] at hy; exact hy rfl
      have hh:=Arithmetic.Gk v.val (Z₁ (x i)-Z₁ y) (Z₂ (x i)-Z₂ y)
        (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
      change -Real.log (v (Z₁ (x i)-Z₁ y)) + -Real.log (v (Z₂ (x i)-Z₂ y)) =
        -Real.log (v ((Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y))) at hh
      rw [ht i y hy] at hh
      simp only [finite,hxy,reduceIte,hh,sub_self,abs_zero,max_self,mul_zero]
  simpa only [he,Finset.sum_const_zero,mul_zero,add_zero] using hb
omit h₁ h₂ in
lemma Ih {Z:P→ K} (hZ:Function.Injective Z) (v:FinitePlace K)
    (hv:v∉ Bq Z hZ):∀ a b,(finite Z hZ v).value a b=0:=by
  intro a b
  by_cases hab:a=b
  · simp [finite,hab]
  · have hunit:v (Z a-Z b)=1:=by
      by_contra h
      exact hv ((MM Z hZ v).mpr ⟨a,b,hab,h⟩)
    simp [finite,hab,hunit]
omit h₁ h₂ in
lemma Pv {Z:P→ K} (hZ:Function.Injective Z) (hn:2≤ Fintype.card P)
    (v:FinitePlace K) (hv:v∉ Bq Z hZ) (C:Finset P):(finite Z hZ v).mass C=0:=by
  have hz:=(finite Z hZ v).Pg hn (Ih hZ v hv)
  by_cases hC:C.card≤1
  · exact (finite Z hZ v).RF C hC
  · obtain ⟨a,ha,b,hb,hab⟩:=Finset.one_lt_card.mp (by omega:1<C.card)
    have hl:=(finite Z hZ v).KE hn C a b hab ha hb
    rw [hz.2.2 a b hab] at hl
    exact le_antisymm hl ((finite Z hZ v).Bf C)
omit h₁ h₂ in
lemma Hu {Z:P→ K} (hZ:Function.Injective Z) (hn:2≤ Fintype.card P)
    (V:Finset (FinitePlace K)) (hV:Bq Z hZ⊆ V) (C:Finset P) :
    (∑ v∈ V,(finite Z hZ v).mass C)=∑ v∈ Bq Z hZ,(finite Z hZ v).mass C:=by
  symm
  exact Finset.sum_subset hV (fun v _ hv=> Pv hZ hn v hv C)
omit h₁ h₂ in
lemma Fn {Z:P→ K} (hZ:Function.Injective Z) (hn:2≤ Fintype.card P)
    (V:Finset (FinitePlace K)) (hV:Bq Z hZ⊆ V) (a:P) :
    (∑ v∈ V,(finite Z hZ v).Ag a)=∑ v∈ Bq Z hZ,(finite Z hZ v).Ag a:=by
  symm
  exact Finset.sum_subset hV (fun v _ hv =>
    ((finite Z hZ v).Pg hn (Ih hZ v hv)).2.1 a)
omit h₁ h₂ in
def BH (V:Finset (FinitePlace K)) (A:InfinitePlace K→ ℝ) (F:FinitePlace K→ ℝ):ℝ :=
  (∑ v,Arithmetic.Bh v* A v)+(Module.finrank ℚ K:ℝ)⁻¹*∑ v∈ V,F v
omit h₁ h₂ in
lemma Gz (V:Finset (FinitePlace K)) {A A':InfinitePlace K→ ℝ} {F F':FinitePlace K→ ℝ}
    (hA:∀ v,A v≤ A' v) (hF:∀ v∈ V,F v≤ F' v):BH V A F≤ BH V A' F':=by
  apply add_le_add
  · exact Finset.sum_le_sum (fun v _=> mul_le_mul_of_nonneg_left (hA v) (Arithmetic.EV v))
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (by positivity)
omit h₁ h₂ in
lemma PX (V:Finset (FinitePlace K)) (A A':InfinitePlace K→ ℝ) (F F':FinitePlace K→ ℝ) :
    BH V (fun v=> A v+A' v) (fun v=> F v+F' v)= BH V A F+ BH V A' F':=by
  simp only [BH,mul_add,Finset.sum_add_distrib]
  ring
omit h₁ h₂ in
lemma PN (V:Finset (FinitePlace K)) (a:ℝ) (A:InfinitePlace K→ ℝ) (F:FinitePlace K→ ℝ) :
    BH V (fun v=> a*A v) (fun v=> a*F v)= a*BH V A F:=by
  simp only [BH,Finset.mul_sum,mul_add]
  congr 1
  · exact Finset.sum_congr rfl (fun v _=> by ring)
  · exact Finset.sum_congr rfl (fun v _=> by ring)
omit h₁ h₂ in
lemma Ev (V:Finset (FinitePlace K)) (a:ℝ) :
    BH V (fun _=> a) (fun _=>0)= a:=by
  simp only [BH,Finset.sum_const_zero,mul_zero,add_zero,← Finset.sum_mul,Arithmetic.Il,one_mul]
omit h₁ h₂ in
lemma DZ {Z:P→ K} (hZ:Function.Injective Z) (hn:2≤ Fintype.card P)
    (V:Finset (FinitePlace K)) (hV:Bq Z hZ⊆ V) (f:Finset P→ ℝ) :
    Ac (CD Z hZ) f= BH V
      (fun v=>∑ C,(∫ ω,(arch Z v ω).mass C ∂Ao.As)*f C)
      (fun v=>∑ C,(finite Z hZ v).mass C*f C):=by
  simp only [Ac,CD,BH,add_mul,Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    exact Finset.sum_congr rfl (fun C _=> by ring)
  · rw [Finset.sum_comm (s:=V)]
    simp_rw [← Finset.sum_mul,Hu hZ hn V hV,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun C _=> by rw [← Finset.mul_sum]; ring)
omit h₁ h₂ in
lemma EC {Z:P→ K} (hZ:Function.Injective Z) (hn:2≤ Fintype.card P)
    (V:Finset (FinitePlace K)) (hV:Bq Z hZ⊆ V) :
    (∑ y,S Z hZ y)= BH V
      (fun v=>∑ y,∫ ω,(arch Z v ω).Ag y ∂Ao.As)
      (fun v=>∑ y,(finite Z hZ v).Ag y):=by
  simp only [S,BH,Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm (s:=V)]
    simp_rw [Fn hZ hn V hV,Finset.mul_sum]
lemma FB (hn:2≤ Fintype.card P)
    (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P) (t:I→ K)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) (hp:∀ i y,0≤ p i y)
    (hp1:∀ i,∑ y,p i y=1) (hx:∀ i,p i (x i)=0)
    (ht:∀ i y,p i y≠0→(Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam H:ℝ) (hB:0≤ B) (hlam:0≤ lam) (hlam2:lam≤1/2)
    (hτ:0< τ) (hτ1:τ≤1) (hτn:2≤ τ*(Fintype.card P:ℝ)) (hH:0≤ H)
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    Ac (CD Z₁ h₁) (slice w p x lam) ≤
      (2*lam/τ^2)*Ac (CD Z₁ h₁) (Ah Finset.univ) +
      B*τ/(Fintype.card P:ℝ)*((∑ y,S Z₁ h₁ y)+(∑ y,S Z₂ h₂ y)) +
      2*lam*B*Ac (CD Z₂ h₂) (Ah Finset.univ)+2*lam*H +
      16*Real.exp (-H/2):=by
  classical
  let V:=Bq Z₁ h₁∪ Bq Z₂ h₂
  have hV₁:Bq Z₁ h₁⊆ V:=Finset.subset_union_left
  have hV₂:Bq Z₂ h₂⊆ V:=Finset.subset_union_right
  have hf (v:FinitePlace K):(∑ C,(finite Z₁ h₁ v).mass C*slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C,(finite Z₁ h₁ v).mass C*Ah Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y,(finite Z₁ h₁ v).Ag y)+(∑ y,(finite Z₂ h₂ v).Ag y)) +
      2*lam*B*(∑ C,(finite Z₂ h₂ v).mass C*Ah Finset.univ C)+0+0:=by
    simpa only [add_zero] using Oo Z₁ Z₂ h₁ h₂ hn v w p x t hw hW hp hp1 hx ht B τ lam hB hlam hlam2 hτ hτ1 hτn hdom
  have hb:=Gz V
    (fun v=> PO Z₁ Z₂ h₁ h₂ hn v w p x t hw hW hp hp1 hx ht B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom)
    (fun v _=> hf v)
  simp only [PX,PN,Ev] at hb
  rw [← DZ h₁ hn V hV₁,← DZ h₁ hn V hV₁,
    ← DZ h₂ hn V hV₂,← EC h₁ hn V hV₁,
    ← EC h₂ hn V hV₂] at hb
  exact hb
lemma KY (hn:2≤ Fintype.card P)
    (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P) (t:I→ K)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i=1) (hp:∀ i y,0≤ p i y)
    (hp1:∀ i,∑ y,p i y=1) (hx:∀ i,p i (x i)=0)
    (ht:∀ i y,p i y≠0→(Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam H:ℝ) (hB:0≤ B) (hlam:0≤ lam) (hlam2:lam≤1/2)
    (hτ:0< τ) (hτ1:τ≤1) (hτn:2≤ τ*(Fintype.card P:ℝ)) (hH:0≤ H)
    (hdom:∀ a b,a≠ b→ Av w p x a b≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    Ac (totalMass Z₁ Z₂ h₁ h₂) (slice w p x lam) ≤
      (2*lam/τ^2+2*lam*B)*Ac (totalMass Z₁ Z₂ h₁ h₂) (Ah Finset.univ) +
      2*B*τ/(Fintype.card P:ℝ)*(∑ y,BB Z₁ Z₂ h₁ h₂ y)+4*lam*H +
      32*Real.exp (-H/2):=by
  have hA:=FB Z₁ Z₂ h₁ h₂ hn w p x t hw hW hp hp1 hx ht B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom
  have ht':∀ i y,p i y≠0→(Z₂ (x i)-Z₂ y)*(Z₁ (x i)-Z₁ y)=t i:=by
    intro i y hy
    rw [mul_comm]
    exact ht i y hy
  have hB':=FB Z₂ Z₁ h₂ h₁ hn w p x t hw hW hp hp1 hx ht' B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom
  simp only [Ac,totalMass,BB,add_mul,Finset.sum_add_distrib] at hA hB' ⊢
  linear_combination hA+hB'
end Aa.Bg
noncomputable section
open Filter
open scoped Topology
end
end
end
end
end
end
end
end AA
namespace AA
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
namespace Aa
open Filter
open scoped Topology
end Aa
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
namespace Aa.Core
variable {V:Type u1} {I:Type u2} [Fintype V] [Fintype I] [DecidableEq V]
structure Au (V:Type u3) (I:Type u4) [DecidableEq V] where
  source:I→ V
  targets:I→ Finset V
  OE:∀ e,source e∉ targets e
  disjoint:∀ e f,e≠ f→ source e=source f→ Disjoint (targets e) (targets f)
namespace Au
variable (G:Au V I)
def size (C:Finset V) (e:I):ℕ:=(G.targets e∩ C).card
def HO (K:ℝ) (C:Finset V) (e:I):Prop :=
  G.source e∈ C∧ K<(G.size C e:ℝ)
instance (K:ℝ) (C:Finset V) (e:I):Decidable (G.HO K C e):=Classical.propDecidable _
def edge (K:ℝ) (C:Finset V) (x y:V):Prop :=
  ∃ e,G.HO K C e∧ G.source e=x∧ y∈ G.targets e∩ C
instance (K:ℝ) (C:Finset V) (x y:V):Decidable (G.edge K C x y):=Classical.propDecidable _
def degree (K:ℝ) (C:Finset V) (v:V):ℝ :=
  (Finset.univ.filter (G.edge K C v)).card+(Finset.univ.filter (fun x=> G.edge K C x v)).card
omit [Fintype V] [Fintype I] in
lemma St (K:ℝ) (C:Finset V) (v:V):¬G.edge K C v v:=by
  rintro ⟨e,_,he,hv⟩
  exact G.OE e (he ▸ (Finset.mem_inter.mp hv).1)
omit [Fintype V] [Fintype I] in
lemma Tf (_K:ℝ) (_C:Finset V) (x y:V) {e f:I}
    (he:G.source e=x) (hf:G.source f=x) (hye:y∈ G.targets e) (hyf:y∈ G.targets f):e=f:=by
  by_contra hn
  exact Finset.disjoint_left.mp (G.disjoint e f hn (he.trans hf.symm)) hye hyf
end Au
end Aa.Core
namespace Aa.Core.Au
open scoped BigOperators
variable {V:Type u5} {I:Type u6} [Fintype V] [Fintype I] [DecidableEq V]
variable (G:Au V I)
def edgeSet (K:ℝ) (C:Finset V):Finset (V × V) :=
  Finset.univ.filter (fun xy=> G.edge K C xy.1 xy.2)
omit [Fintype V] in
lemma LC (K:ℝ) (C:Finset V) (x y:V) :
    (∑ e,if G.HO K C e∧ G.source e=x∧ y∈ G.targets e∩ C then (1:ℝ) else 0)=
      if G.edge K C x y then 1 else 0:=by
  classical
  by_cases hh:G.edge K C x y
  · obtain ⟨e,he,hs,hy⟩:=hh
    rw [if_pos ⟨e,he,hs,hy⟩,Finset.sum_eq_single e]
    · simp [he,hs,hy]
    · intro f _ hfe
      rw [if_neg]
      rintro ⟨_,hfs,hfy⟩
      exact hfe (G.Tf K C x y hfs hs (Finset.mem_inter.mp hfy).1 (Finset.mem_inter.mp hy).1)
    · simp
  · have hn:∀ e,¬(G.HO K C e∧ G.source e=x∧ y∈ G.targets e∩ C) :=
      fun e he=> hh ⟨e,he⟩
    simp only [if_neg (hn _),Finset.sum_const_zero,if_neg hh]
lemma Sy (K:ℝ) (C:Finset V) :
    ((G.edgeSet K C).card:ℝ)=∑ e,if G.HO K C e then (G.size C e:ℝ) else 0:=by
  classical
  have he (e:I):(∑ xy:V × V,if G.HO K C e∧ G.source e=xy.1∧ xy.2∈ G.targets e∩ C then (1:ℝ) else 0)=
      if G.HO K C e then (G.size C e:ℝ) else 0:=by
    by_cases ha:G.HO K C e
    · simp only [ha,true_and,Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (G.source e)]
      · simp only [true_and]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
        change ((Finset.univ.filter (fun y=> y∈ G.targets e∩ C)).card:ℝ)=(G.size C e:ℝ)
        simp only [size,Finset.mem_inter]
        congr 2
        ext y
        simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    · simp [ha]
  change ((Finset.univ.filter (fun xy:V × V=> G.edge K C xy.1 xy.2)).card:ℝ)=_
  rw [← Finset.sum_boole]
  simp_rw [← G.LC K C]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun e _=> he e)
end Aa.Core.Au
namespace Aa
open Aa.Core
end Aa
namespace Aa
open scoped BigOperators
end Aa
namespace Aa
open scoped BigOperators
end Aa
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
namespace Aa.Core.Au
open scoped BigOperators
variable {V:Type u1} {I:Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable (G:Au V I)
end Aa.Core.Au
namespace Aa
open scoped BigOperators
end Aa
namespace Aa
open Filter
open scoped Topology
end Aa
namespace Aa
open Filter
open scoped Topology
end Aa
namespace Aa
open scoped BigOperators
end Aa
namespace Aa
open Filter
open scoped Topology BigOperators
end Aa
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
namespace Aa.Core.Au
open scoped BigOperators
open Variance
variable {V:Type u1} {I:Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable (G:Au V I)
def edges:Finset (V × V):=G.edgeSet (-1) Finset.univ
def Ap:ℝ:=G.edges.card
def Av (x y:V):ℝ:=if (x,y)∈ G.edges then 1/G.Ap else 0
def Af (e:I):ℝ:=(G.targets e).card/ G.Ap
def BV (y:V):Finset V:=Finset.univ.filter (fun x=>(x,y)∈ G.edges)
def Ax (y:V):ℝ:=(G.BV y).card/ G.Ap
omit [Fintype I] in
lemma FI (e:I):G.HO (-1) Finset.univ e:=by
  refine ⟨Finset.mem_univ _,?_⟩
  have h:=Nat.cast_nonneg (α:=ℝ) (G.size Finset.univ e)
  linarith
lemma Ke:G.Ap=∑ e,((G.targets e).card:ℝ):=by
  unfold Ap edges
  rw [Sy]
  simp [G.FI,size]
omit [Fintype I] in
lemma LZ (x y:V):0≤ G.Av x y:=by
  unfold Av Ap
  split_ifs <;> positivity
omit [Fintype I] in
lemma HA (x:V):G.Av x x=0:=by
  have hh:(x,x)∉ G.edges:=by
    intro h
    exact G.St (-1) Finset.univ x (Finset.mem_filter.mp h).2
  simp [Av,hh]
omit [Fintype I] in
lemma AT (e:I):0≤ G.Af e:=by
  unfold Af Ap
  positivity
lemma Bz (hG:0< G.Ap):∑ e,G.Af e=1:=by
  simp only [Af,← Finset.sum_div,← G.Ke,div_self hG.ne']
omit [Fintype I] in
lemma PG (e:I) (y:V) :
    G.Af e*Ae (G.targets e) y= if y∈ G.targets e then 1/G.Ap else 0:=by
  by_cases hy:y∈ G.targets e
  · have hk:((G.targets e).card:ℝ)≠0:=by
      exact_mod_cast (Finset.card_ne_zero.mpr ⟨y,hy⟩)
    simp only [Af,Ae,if_pos hy]
    field_simp
  · simp [Ae,hy]
lemma Gq (x y:V) :
    (∑ e,if G.source e=x then G.Af e* Ae (G.targets e) y else 0) =
      G.Av x y:=by
  have he:=G.LC (-1) Finset.univ x y
  simp only [G.FI,true_and,Finset.mem_inter,Finset.mem_univ,and_true] at he
  have hh:(∑ e,if G.source e=x then G.Af e* Ae (G.targets e) y else 0) =
      (∑ e,if G.source e=x∧ y∈ G.targets e then (1:ℝ) else 0)/G.Ap:=by
    simp only [Finset.sum_div,G.PG]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs:G.source e=x <;> by_cases hy:y∈ G.targets e <;> simp [hs,hy]
  rw [hh,he]
  by_cases he:G.edge (-1) Finset.univ x y <;> simp [Av,edges,edgeSet,he]
lemma Ir (y:V) :
    (∑ e,G.Af e* Ae (G.targets e) y)=∑ x,G.Av x y:=by
  simp_rw [← G.Gq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp
omit [Fintype I] in
lemma GF (y:V):∑ x,G.Av x y=G.Ax y:=by
  simp only [Av,Ax,BV,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  simp only [mul_one_div]
omit [Fintype I] in
lemma GB (x y:V) :
    G.Ax y*Ae (G.BV y) x=G.Av x y:=by
  by_cases he:(x,y)∈ G.edges
  · have hm:x∈ G.BV y:=by simp [BV,he]
    have hk:((G.BV y).card:ℝ)≠0:=by exact_mod_cast (Finset.card_ne_zero.mpr ⟨x,hm⟩)
    simp only [Ax,Ae,if_pos hm,Av,if_pos he]
    field_simp
  · have hm:x∉ G.BV y:=by simp [BV,he]
    simp [Ae,hm,Av,he]
omit [Fintype I] in
lemma KK (hG:0< G.Ap):(∑ x,∑ y,G.Av x y)=1:=by
  rw [← Fintype.sum_prod_type (f:=fun xy:V × V=> G.Av xy.1 xy.2)]
  simp only [Av,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have he:Finset.univ.filter (fun xy:V × V=> xy∈ G.edges)=G.edges:=by simp
  rw [he]
  change G.Ap*(1/G.Ap)=1
  field_simp
omit [Fintype I] in
lemma IL (hG:0< G.Ap):∑ y,G.Ax y=1:=by
  simp_rw [← G.GF]
  rw [Finset.sum_comm,G.KK hG]
lemma Fm (B:ℝ) (hdom:∀ x y,G.Av x y≤ B*Az Finset.univ x y)
    (hn:2≤ Fintype.card V) (y:V) :
    (∑ e,G.Af e*Ae (G.targets e) y)≤ B*Ae Finset.univ y:=by
  rw [G.Ir]
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun x _=> hdom x y)
  simpa only [← Finset.mul_sum,Ex _ _ y,Cp Finset.univ (by simpa using hn)] using hh
omit [Fintype I] in
lemma Nl (B:ℝ) (hdom:∀ x y,G.Av x y≤ B*Az Finset.univ x y)
    (hn:2≤ Fintype.card V) (x:V) :
    (∑ y,G.Ax y*Ae (G.BV y) x)≤ B*Ae Finset.univ x:=by
  simp_rw [G.GB]
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun y _=> hdom x y)
  simpa only [← Finset.mul_sum,Cp Finset.univ (by simpa using hn)] using hh
lemma Nj (T:ℝ) (hT:0≤ T) :
    (∑ y,if ((G.BV y).card:ℝ)<T then G.Ax y else 0) ≤
      (Fintype.card V:ℝ)*T/G.Ap:=by
  have hn:0≤ G.Ap:=by unfold Ap; positivity
  have hh:∀ y,(if ((G.BV y).card:ℝ)<T then G.Ax y else 0)≤ T/G.Ap:=by
    intro y
    split_ifs with hy
    · exact div_le_div_of_nonneg_right hy.le hn
    · exact div_nonneg hT hn
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun y _=> hh y)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_div_assoc] using hs
end Aa.Core.Au
namespace Aa.Core.Au
open scoped BigOperators
variable {V:Type u3} {I:Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G:Au V I)
end Aa.Core.Au
namespace Aa.Core.Au
open scoped BigOperators
variable {V:Type u5} {I:Type u6} [Fintype V] [Fintype I] [DecidableEq V]
variable (G:Au V I)
def EJ (lam:ℝ) (D:Finset V):ℝ :=
  ∑ e,if lam*((G.targets e).card:ℝ)≤(G.size D e:ℝ)∧ G.source e∈ D
    then (G.size D e:ℝ) else 0
omit [Fintype I] in
lemma Rb (x:V):(∑ y,G.Av x y)+(∑ y,G.Av y x)=
    G.degree (-1) Finset.univ x/G.Ap:=by
  simp only [Av,edges,edgeSet,Finset.mem_filter,Finset.mem_univ,true_and,
    ← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,degree,add_div,mul_one_div]
end Aa.Core.Au
namespace Aa
open scoped BigOperators
open Aa.Core
structure AJ (V:Type u7) (I:Type u8) [Fintype V] [Fintype I] [DecidableEq V]
    (G:Au V I) (θ γ c η:ℝ):Prop where
  Cz:2≤ Fintype.card V
  lower:(θ-η)*(Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)≤ G.Ap
  upper:G.Ap≤(θ+η/8)*(Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)
  degree:∀ x,2*(θ-η)*((Fintype.card V:ℝ)-1)≤ G.degree (-1) Finset.univ x
  fiber:∀ e,(Fintype.card V:ℝ)^γ<((G.targets e).card:ℝ)
  subset:∀ D,G.EJ (1/Real.log (Fintype.card V:ℝ)) D≤(θ+η)*(D.card:ℝ)*((D.card:ℝ)-1)
  small:∀ D,(D.card:ℝ)≤(Fintype.card V:ℝ)^(1-c) →
    G.EJ (1/Real.log (Fintype.card V:ℝ)) D≤ η*(D.card:ℝ)*((D.card:ℝ)-1)
end Aa
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
namespace Aa
open scoped BigOperators
open Variance
variable {V:Type u1} {I:Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable {G:Core.Au V I} {θ γ c η:ℝ}
lemma AJ.CR (h:AJ V I G θ γ c η) (hη:η<θ):0<G.Ap:=by
  have hnR:(2:ℝ)≤Fintype.card V:=by exact_mod_cast h.Cz
  have hp:0<(θ-η)*(Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1) :=
    mul_pos (mul_pos (sub_pos.mpr hη) (by linarith)) (by linarith)
  exact hp.trans_le h.lower
lemma AJ.KG (h:AJ V I G θ γ c η) (hη:η<θ) (x y:V) :
    G.Av x y≤(1/(θ-η))*Az Finset.univ x y:=by
  have hnR:(2:ℝ)≤Fintype.card V:=by exact_mod_cast h.Cz
  have hden:0<(Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1):=mul_pos (by linarith) (by linarith)
  by_cases hxy:x=y
  · subst y; simp [G.HA,Az]
  · have he:Az Finset.univ x y=1/((Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)):=by simp [Az,hxy]
    rw [he]
    unfold Core.Au.Av
    split_ifs
    · have hh:=one_div_le_one_div_of_le (mul_pos (sub_pos.mpr hη) hden) (by simpa only [mul_assoc] using h.lower)
      calc
        1/ G.Ap≤1/((θ-η)*((Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1))):=hh
        _= _:=by rw [one_div_mul_one_div]
    · positivity
lemma AJ.To (h:AJ V I G θ γ c η) (hη:η<θ) (hη0:0≤η) (x:V) :
    2*((θ-η)/(θ+η/8))*Ae Finset.univ x≤(∑ y,G.Av x y)+(∑ y,G.Av y x):=by
  rw [G.Rb]
  have hnR:(2:ℝ)≤Fintype.card V:=by exact_mod_cast h.Cz
  have hn0:(0:ℝ)<Fintype.card V:=by linarith
  have hnm:0<(Fintype.card V:ℝ)-1:=by linarith
  have hθ:0<θ+η/8:=by linarith
  have hd:=h.degree x
  have hu:=h.upper
  have hh:(2*(θ-η)*((Fintype.card V:ℝ)-1))/((θ+η/8)*(Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)) ≤
      G.degree (-1) Finset.univ x/G.Ap:=by
    apply div_le_div₀ _ hd (h.CR hη) hu
    exact (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hη.le)) hnm.le).trans hd
  have he:(2*(θ-η)*((Fintype.card V:ℝ)-1))/((θ+η/8)*(Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)) =
      2*((θ-η)/(θ+η/8))*Ae Finset.univ x:=by
    simp only [Ae,Finset.mem_univ,ite_true,Finset.card_univ]
    field_simp
  rwa [he] at hh
lemma AJ.Tk (h:AJ V I G θ γ c η) (hη:η<θ) (hη0:0≤η) (D:Finset V) :
    G.EJ (1/Real.log (Fintype.card V:ℝ)) D/ G.Ap ≤
      ((θ+η)/(θ-η))*Ah Finset.univ D:=by
  have hnR:(2:ℝ)≤Fintype.card V:=by exact_mod_cast h.Cz
  have hden:0<(Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1):=mul_pos (by linarith) (by linarith)
  have hD:0≤(D.card:ℝ)*((D.card:ℝ)-1):=by
    by_cases hz:D.card=0
    · simp [hz]
    · have hh:(1:ℝ)≤D.card:=by exact_mod_cast (show 1≤D.card by omega)
      positivity
  have hb:=h.subset D
  have hcmp:G.EJ (1/Real.log (Fintype.card V:ℝ)) D/ G.Ap ≤
      ((θ+η)*(D.card:ℝ)*((D.card:ℝ)-1))/((θ-η)*(Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)):=by
    apply div_le_div₀ _ hb (mul_pos (mul_pos (sub_pos.mpr hη) (by linarith)) (by linarith)) h.lower
    simpa only [mul_assoc] using mul_nonneg (show 0≤θ+η by linarith) hD
  convert hcmp using 1
  rw [Eo]
  simp only [Finset.univ_inter,Finset.card_univ]
  field_simp
lemma AJ.OH (h:AJ V I G θ γ c η) (hη:η<θ) (hη0:0≤η)
    (D:Finset V) (hDsz:(D.card:ℝ)≤(Fintype.card V:ℝ)^(1-c)) :
    G.EJ (1/Real.log (Fintype.card V:ℝ)) D/ G.Ap ≤
      (η/(θ-η))*Ah Finset.univ D:=by
  have hnR:(2:ℝ)≤Fintype.card V:=by exact_mod_cast h.Cz
  have hD:0≤(D.card:ℝ)*((D.card:ℝ)-1):=by
    by_cases hz:D.card=0
    · simp [hz]
    · have hh:(1:ℝ)≤D.card:=by exact_mod_cast (show 1≤D.card by omega)
      positivity
  have hcmp:G.EJ (1/Real.log (Fintype.card V:ℝ)) D/ G.Ap ≤
      (η*(D.card:ℝ)*((D.card:ℝ)-1))/((θ-η)*(Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)):=by
    apply div_le_div₀ _ (h.small D hDsz) (mul_pos (mul_pos (sub_pos.mpr hη) (by linarith)) (by linarith)) h.lower
    simpa only [mul_assoc] using mul_nonneg hη0 hD
  convert hcmp using 1
  rw [Eo]
  simp only [Finset.univ_inter,Finset.card_univ]
  field_simp
end Aa
namespace Aa.Core.Au
open scoped BigOperators
open Variance AL
variable {V:Type u3} {I:Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G:Au V I)
def FL (C:Finset V):ℝ:=∑ x∈ C,∑ y∈ C,G.Av x y
lemma Pn (C:Finset V):G.FL C= AL.Cl G.Af (fun e=> Ae (G.targets e)) G.source C:=by
  unfold FL AL.Cl AL.Av
  simp_rw [G.Gq]
omit [Fintype V] in
omit [Fintype I] in
lemma Ty (e:I) (C:Finset V):mass (Ae (G.targets e)) C=(G.size C e:ℝ)/(G.targets e).card:=by
  rw [mass,Ci]
  rfl
lemma SY (hne:∀ e,(G.targets e).Nonempty) (lam:ℝ) (C:Finset V) :
    G.FL C= slice G.Af (fun e=> Ae (G.targets e)) G.source lam C+ G.EJ lam C/G.Ap:=by
  classical
  rw [G.Pn,Ej]
  unfold slice EJ
  simp only [Finset.sum_div,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hk:(0:ℝ)<(G.targets e).card:=by exact_mod_cast Finset.card_pos.mpr (hne e)
  have hm:=G.Ty e C
  have hprod:G.Af e*mass (Ae (G.targets e)) C=(G.size C e:ℝ)/G.Ap:=by
    rw [hm,Af]
    field_simp
  have hcmp:lam*((G.targets e).card:ℝ)≤(G.size C e:ℝ)↔ lam≤ mass (Ae (G.targets e)) C:=by
    rw [hm,le_div_iff₀ hk]
  simp only [hcmp]
  by_cases hx:G.source e∈ C <;> by_cases hp:mass (Ae (G.targets e)) C<lam
  · simp [hx,hp,not_le.mpr hp]
  · simp [hx,hp,le_of_not_gt hp,hprod]
  · simp [hx]
  · simp [hx]
omit [Fintype I] in
lemma Tg {B:ℝ} (hdom:∀ x y,G.Av x y≤ B*Az Finset.univ x y) (C:Finset V) :
    G.FL C≤ B*Ah Finset.univ C:=by
  unfold FL Ah
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun x _=> Finset.sum_le_sum (fun y _=> hdom x y))
end Aa.Core.Au
namespace Aa.Variance
open scoped BigOperators
variable {V:Type u5} [Fintype V] [DecidableEq V]
lemma IT (m:Finset V→ ℝ) (q:V→ V→ ℝ) :
    Ac m (fun C=>∑ x∈ C,∑ y∈ C,q x y)=
      ∑ x,∑ y,q x y*AD m x y:=by
  have hc (C:Finset V):(∑ x∈ C,∑ y∈ C,q x y)=
      ∑ x,∑ y,q x y*(if x∈C∧ y∈C then (1:ℝ) else 0):=by
    simp only [mul_ite,mul_one,mul_zero,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp
  simp only [Ac,hc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [AD,Ac,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  ring
lemma Jm (m:Finset V→ ℝ) (b:ℝ) (S:V→ ℝ)
    (hL:∀ x y,x≠y→ AD m x y=b+S x+S y)
    (q:V→ V→ ℝ) (hdiag:∀ x,q x x=0) (h1:(∑ x,∑ y,q x y)=1) :
    Ac m (fun C=>∑ x∈ C,∑ y∈ C,q x y)=
      b+∑ x,((∑ y,q x y)+(∑ y,q y x))*S x:=by
  rw [IT]
  have hp (x y:V):q x y*AD m x y=q x y*(b+S x+S y):=by
    by_cases hxy:x=y
    · subst y; simp [hdiag]
    · rw [hL x y hxy]
  simp_rw [hp,mul_add,Finset.sum_add_distrib]
  have hb:(∑ x,∑ y,q x y*b)=b:=by
    simp only [← Finset.sum_mul,h1,one_mul]
  rw [hb]
  simp only [← Finset.sum_mul,add_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun x y=> q x y*S y)]
  simp only [← Finset.sum_mul]
  ring
lemma JU (m:Finset V→ ℝ) (b:ℝ) (S:V→ ℝ)
    (hL:∀ x y,x≠y→ AD m x y=b+S x+S y) (hn:2≤Fintype.card V) :
    Ac m (Ah Finset.univ)=b+2*(∑ x,Ae Finset.univ x*S x):=by
  have hsum:(∑ x:V,∑ y:V,Az Finset.univ x y)=1:=by
    simp_rw [Cp Finset.univ (by simpa using hn)]
    exact Bs Finset.univ (Finset.card_pos.mp (by simpa using (show 0<Fintype.card V by omega)))
  have hh:=Jm m b S hL (Az Finset.univ) (by intro x; simp [Az]) hsum
  change Ac m (fun C=>∑ x∈ C,∑ y∈ C,Az Finset.univ x y)= _
  rw [hh]
  simp_rw [Ex Finset.univ _ _,Cp Finset.univ (by simpa using hn)]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring
end Aa.Variance
namespace Aa
open scoped BigOperators
open Variance AL
variable {V:Type u6} {I:Type u7} [Fintype V] [Fintype I] [DecidableEq V]
variable {G:Core.Au V I} {θ γ c η:ℝ}
lemma AJ.ML (h:AJ V I G θ γ c η) (hη:η<θ) (hη0:0≤η)
    (m:Finset V→ ℝ) (b:ℝ) (S:V→ ℝ) (hS:∀ x,0≤S x)
    (hL:∀ x y,x≠y→ AD m x y=b+S x+S y) :
    Ac m (Ah Finset.univ) -
      (2-2*((θ-η)/(θ+η/8)))*(∑ x,Ae Finset.univ x*S x)≤ Ac m G.FL:=by
  change _≤ Ac m (fun C=>∑ x∈ C,∑ y∈ C,G.Av x y)
  rw [Jm m b S hL G.Av G.HA (G.KK (h.CR hη)),
    JU m b S hL h.Cz]
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_right (h.To hη hη0 x) (hS x))
  have he:(∑ x:V,2*((θ-η)/(θ+η/8))*Ae Finset.univ x*S x)=
      (2*((θ-η)/(θ+η/8)))*(∑ x:V,Ae Finset.univ x*S x):=by
    simp only [Finset.mul_sum,mul_assoc]
  rw [he] at hh
  linarith
lemma AJ.RT (h:AJ V I G θ γ c η) (hη:η<θ) (hη0:0≤η)
    (m:Finset V→ ℝ) (hm:∀ C,0≤ m C) (b:ℝ) (S:V→ ℝ) (hS:∀ x,0≤S x)
    (hL:∀ x y,x≠y→ AD m x y=b+S x+S y) :
    (θ/(θ-η))*Ac m (fun C=> if (C.card:ℝ)≤(Fintype.card V:ℝ)^(1-c)
      then Ah Finset.univ C else 0) ≤
      Ac m (slice G.Af (fun e=> Ae (G.targets e)) G.source (1/Real.log (Fintype.card V:ℝ))) +
      ((θ+η)/(θ-η)-1)*Ac m (Ah Finset.univ) +
      (2-2*((θ-η)/(θ+η/8)))*(∑ x,Ae Finset.univ x*S x):=by
  have hlo:=h.ML hη hη0 m b S hS hL
  have hne:∀ e,(G.targets e).Nonempty:=by
    intro e
    have hn:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by have:=h.Cz; omega)
    exact Finset.card_pos.mp (by exact_mod_cast ((Real.rpow_pos_of_pos hn γ).trans (h.fiber e)))
  have hpoint (C:Finset V):G.FL C ≤
      slice G.Af (fun e=> Ae (G.targets e)) G.source (1/Real.log (Fintype.card V:ℝ)) C +
      ((θ+η)/(θ-η))*Ah Finset.univ C -
      (θ/(θ-η))*(if (C.card:ℝ)≤(Fintype.card V:ℝ)^(1-c) then Ah Finset.univ C else 0):=by
    rw [G.SY hne (1/Real.log (Fintype.card V:ℝ)) C]
    by_cases hC:(C.card:ℝ)≤(Fintype.card V:ℝ)^(1-c)
    · rw [if_pos hC]
      have hh:=h.OH hη hη0 C hC
      have he:(θ+η)/(θ-η)-θ/(θ-η)=η/(θ-η):=by ring
      calc
        _≤ slice G.Af (fun e=> Ae (G.targets e)) G.source (1/Real.log (Fintype.card V:ℝ)) C+(η/(θ-η))*Ah Finset.univ C:=add_le_add_right hh _
        _= _:=by rw [← he]; ring
    · simp only [if_neg hC,mul_zero,sub_zero]
      exact add_le_add_right (h.Tk hη hη0 C) _
  have hint:=Finset.sum_le_sum (s:=Finset.univ) (fun C _=> mul_le_mul_of_nonneg_left (hpoint C) (hm C))
  change Ac m G.FL≤ _ at hint
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hint
  have hcomm (a:ℝ) (f:Finset V→ ℝ):(∑ C,m C*(a*f C))=a*Ac m f:=by
    simp only [Ac,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun C _=> by ring)
  simp only [hcomm] at hint
  change Ac m G.FL≤ Ac m _+_ - _ at hint
  nlinarith
end Aa
namespace Aa
open scoped BigOperators
open Variance AL Bg
variable {V:Type u8} {I:Type u9} [Fintype V] [Fintype I] [DecidableEq V]
variable {G:Core.Au V I} {θ γ c η:ℝ}
variable {K:Type u10} [Field K] [NumberField K]
variable (Z₁ Z₂:V→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
def AQ:ℝ:=Ac (totalMass Z₁ Z₂ h₁ h₂) (Ah Finset.univ)
def AG:ℝ:=∑ x,Ae Finset.univ x* BB Z₁ Z₂ h₁ h₂ x
def DC (c:ℝ):ℝ:=Ac (totalMass Z₁ Z₂ h₁ h₂)
  (fun C=> if (C.card:ℝ)≤(Fintype.card V:ℝ)^(1-c) then Ah Finset.univ C else 0)
lemma BK:0≤ AQ Z₁ Z₂ h₁ h₂:=by
  exact Finset.sum_nonneg (fun C _=> mul_nonneg (Bi Z₁ Z₂ h₁ h₂ C) (BJ _ _))
lemma Bu:0≤ AG Z₁ Z₂ h₁ h₂:=by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (Fc Z₁ Z₂ h₁ h₂ x)
  simp only [Ae,Finset.mem_univ,ite_true]
  positivity
lemma Ga (c:ℝ):0≤ DC Z₁ Z₂ h₁ h₂ c:=by
  apply Finset.sum_nonneg
  intro C _
  apply mul_nonneg (Bi Z₁ Z₂ h₁ h₂ C)
  dsimp only
  split_ifs
  · exact BJ _ _
  · exact le_refl _
lemma AJ.JY (h:AJ V I G θ γ c η) (hη:η< θ)
    (t:I→ K) (ht:∀ e y,y∈ G.targets e→(Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e)
    (τ lam H:ℝ) (hlam:0≤ lam) (hlam2:lam≤1/2)
    (hτ:0< τ) (hτ1:τ≤1) (hτn:2≤ τ*(Fintype.card V:ℝ)) (hH:0≤ H) :
    Ac (totalMass Z₁ Z₂ h₁ h₂) (slice G.Af (fun e=> Ae (G.targets e)) G.source lam) ≤
      (2*lam/τ^2+2*lam/(θ-η))*AQ Z₁ Z₂ h₁ h₂ +
      (2*τ/(θ-η))*AG Z₁ Z₂ h₁ h₂+4*lam*H+32*Real.exp (-H/2):=by
  have hne:∀ e,(G.targets e).Nonempty:=by
    intro e
    have hn:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by have:=h.Cz; omega)
    exact Finset.card_pos.mp (by exact_mod_cast ((Real.rpow_pos_of_pos hn γ).trans (h.fiber e)))
  have hp:∀ e y,0≤ Ae (G.targets e) y:=by intro e y; unfold Ae; split_ifs <;> positivity
  have hx:∀ e,Ae (G.targets e) (G.source e)=0:=by intro e; simp [Ae,G.OE]
  have ht':∀ e y,Ae (G.targets e) y≠0→(Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e:=by
    intro e y hy
    apply ht e y
    by_contra hn
    exact hy (by simp [Ae,hn])
  have hdom:∀ a b,a≠ b→ AL.Av G.Af (fun e=> Ae (G.targets e)) G.source a b ≤
      (1/(θ-η))/((Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)):=by
    intro a b hab
    have hh:=h.KG hη a b
    simpa [AL.Av,G.Gq,Az,hab,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  have hh:=KY Z₁ Z₂ h₁ h₂ h.Cz G.Af (fun e=> Ae (G.targets e)) G.source t
    G.AT (G.Bz (h.CR hη)) hp (fun e=> Bs _ (hne e)) hx ht'
    (1/(θ-η)) τ lam H (by positivity) hlam hlam2 hτ hτ1 hτn hH hdom
  have he:(∑ x:V,BB Z₁ Z₂ h₁ h₂ x)/(Fintype.card V:ℝ)= AG Z₁ Z₂ h₁ h₂:=by
    simp only [AG,Ae,Finset.mem_univ,ite_true,Finset.card_univ,Finset.sum_div]
    exact Finset.sum_congr rfl (fun x _=> by ring)
  have ha:2*(1/(θ-η))*τ/(Fintype.card V:ℝ)*(∑ x,BB Z₁ Z₂ h₁ h₂ x) =
      (2*τ/(θ-η))*AG Z₁ Z₂ h₁ h₂:=by rw [← he]; ring
  rw [ha] at hh
  convert hh using 1; unfold AQ; ring
lemma AJ.JM (h:AJ V I G θ γ c η) (hη:η< θ) (hη0:0≤ η)
    (t:I→ K) (ht:∀ e y,y∈ G.targets e→(Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e)
    (τ H:ℝ) (hlam:0≤1/Real.log (Fintype.card V:ℝ)) (hlam2:1/Real.log (Fintype.card V:ℝ)≤1/2)
    (hτ:0< τ) (hτ1:τ≤1) (hτn:2≤ τ*(Fintype.card V:ℝ)) (hH:0≤ H) :
    DC Z₁ Z₂ h₁ h₂ c ≤
      (2*(1/Real.log (Fintype.card V:ℝ))/τ^2+2*(1/Real.log (Fintype.card V:ℝ))/(θ-η)+((θ+η)/(θ-η)-1))*AQ Z₁ Z₂ h₁ h₂ +
      (2*τ/(θ-η)+(2-2*((θ-η)/(θ+η/8))))*AG Z₁ Z₂ h₁ h₂ +
      4*(1/Real.log (Fintype.card V:ℝ))*H+32*Real.exp (-H/2):=by
  have hs:=h.RT hη hη0 (totalMass Z₁ Z₂ h₁ h₂) (Bi Z₁ Z₂ h₁ h₂)
    (Gn Z₁ Z₂ h₁ h₂) (BB Z₁ Z₂ h₁ h₂) (Fc Z₁ Z₂ h₁ h₂)
    (EW Z₁ Z₂ h₁ h₂ h.Cz)
  have htS:=h.JY Z₁ Z₂ h₁ h₂ hη t ht τ (1/Real.log (Fintype.card V:ℝ)) H hlam hlam2 hτ hτ1 hτn hH
  have hf:1≤ θ/(θ-η):=(one_le_div (sub_pos.mpr hη)).mpr (by linarith)
  have he:=mul_le_mul_of_nonneg_right hf (Ga Z₁ Z₂ h₁ h₂ c)
  change (θ/(θ-η))*DC Z₁ Z₂ h₁ h₂ c≤ _ at hs
  change _≤ _+((θ+η)/(θ-η)-1)*AQ Z₁ Z₂ h₁ h₂ +
    (2-2*((θ-η)/(θ+η/8)))*AG Z₁ Z₂ h₁ h₂ at hs
  nlinarith
end Aa
namespace Aa.Variance
open scoped BigOperators
variable {P:Type u11} {I:Type u12} [Fintype P] [DecidableEq P] [Fintype I]
lemma Bw (w:I→ ℝ) (B:I→ Finset P) (T:ℝ)
    (hw:∀ i,0≤w i) (C:Finset P):0≤Aj w B T C:=by
  unfold Aj
  split_ifs
  · exact Finset.sum_nonneg (fun i _=> mul_nonneg (hw i) (sq_nonneg _))
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hw i)
    split_ifs <;> positivity
lemma Gu {n k:ℝ} (hn:2≤n) (hnk:n≤k) :
    1/(k-1)≤2/n:=by
  apply (div_le_div_iff₀ (by linarith:0<k-1) (by linarith:0<n)).mpr
  nlinarith
end Aa.Variance
namespace Aa
open scoped BigOperators Topology
open Filter Variance Bg
variable {V:ℕ→ Type u13} {I:ℕ→ Type u14} {K:ℕ→ Type u15} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]
variable (Z₁ Z₂:∀ j,V j→ K j) (h₁:∀ j,Function.Injective (Z₁ j)) (h₂:∀ j,Function.Injective (Z₂ j))
theorem Gg (w:∀ j,I j→ ℝ) (B:∀ j,I j→ Finset (V j))
    (γ c M₀:ℝ) (hγ:0<γ) (hγ1:γ<1) (hcγ:c<γ) (_hc1:c<1) (hM:0≤M₀)
    (hn:Tendsto (fun j=>(Fintype.card (V j):ℝ)) atTop atTop)
    (hw:∀ j i,0≤w j i) (hW:∀ j,(∑ i,w j i)≤1)
    (hsize:∀ᶠ j in atTop,∀ i,(Fintype.card (V j):ℝ)^γ≤((B j i).card:ℝ))
    (hdom:∀ᶠ j in atTop,∀ x,(∑ i,w j i*Ae (B j i) x)≤ M₀*Ae Finset.univ x)
    (hsmall:Tendsto (fun j=> DC (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) c /
      (AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0)) :
    Tendsto (fun j=> Ac (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
      (Aj (w j) (B j) ((Fintype.card (V j):ℝ)^(1-c))) /
      (AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0):=by
  let n:=fun j=>(Fintype.card (V j):ℝ)
  let U:=fun j=> AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let A:=fun j=> AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let D:=fun j=> DC (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) c
  have hU (j):0≤U j:=BK _ _ _ _
  have hA (j):0≤A j:=Bu _ _ _ _
  have hden (j):0<U j+A j+1:=by linarith [hU j,hA j]
  have hNγ:Tendsto (fun j=> n j^γ) atTop atTop:=(tendsto_rpow_atTop hγ).comp hn
  have hcT:Tendsto (fun j=> n j^(c-γ)) atTop (𝓝 0) :=
    by
    have h:=(tendsto_rpow_neg_atTop (by linarith:0<γ-c)).comp hn
    convert h using 1; funext j; congr 1; ring
  have hlim:Tendsto (fun j=>4*(M₀+1)*n j^(c-γ)+4*M₀*(D j/(U j+A j+1))) atTop (𝓝 0):=by
    convert (hcT.const_mul (4*(M₀+1))).add (hsmall.const_mul (4*M₀)) using 1; simp
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun j=> div_nonneg
      (Finset.sum_nonneg fun C _=> mul_nonneg (Bi _ _ _ _ C)
        (Bw _ _ _ (hw j) C)) (hden j).le
  · filter_upwards [hn.eventually (eventually_ge_atTop (2:ℝ)),
      hNγ.eventually (eventually_ge_atTop (2:ℝ)),hsize,hdom] with j hjn hjγ hjs hjd
    have hnpos:0<n j:=by linarith
    have hnγpos:0<n j^γ:=Real.rpow_pos_of_pos hnpos _
    have hnP:2≤Fintype.card (V j):=by exact_mod_cast hjn
    have hbs:∀ i,2≤(B j i).card:=fun i=> by exact_mod_cast (hjγ.trans (hjs i))
    have hbn:n j^γ≤ n j:=by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show 1≤n j by linarith) hγ1.le
    have hk:∀ i,1/(((B j i).card:ℝ)-1)≤2/(n j^γ):=fun i=> Gu hjγ (hjs i)
    have hnerr:1/(n j-1)≤2/(n j^γ):=Gu hjγ hbn
    have hT:1≤n j^(1-c):=Real.one_le_rpow (by linarith) (by linarith)
    have hτ:0<n j^(-c):=Real.rpow_pos_of_pos hnpos _
    have hscale:n j^(-c)*n j≤n j^(1-c):=by
      calc
        _= n j^(-c)*n j^(1:ℝ):=by rw [Real.rpow_one]
        _= n j^((-c)+1):=(Real.rpow_add hnpos _ _).symm
        _= n j^(1-c):=by congr 1;ring
        _≤ n j^(1-c):=le_rfl
    have hv:=MT (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) hnP (w j) (B j)
      (n j^(1-c)) M₀ (2/(n j^γ)) (n j^(-c)) (hw j) (hW j) hT hM
      (by positivity) hτ hscale hbs hk hnerr hjd
    have he:2*(2/(n j^γ))*(M₀+1)/(n j^(-c))=4*(M₀+1)*n j^(c-γ):=by
      rw [Real.rpow_sub hnpos,Real.rpow_neg hnpos.le]
      field_simp
      ring
    rw [he] at hv
    change _≤4*(M₀+1)*n j^(c-γ)*U j+4*M₀*D j at hv
    have hratio:U j/(U j+A j+1)≤1:=(div_le_one (hden j)).mpr (by linarith [hA j])
    have hcoeff:0≤4*(M₀+1)*n j^(c-γ):=by positivity
    calc
      _≤(4*(M₀+1)*n j^(c-γ)*U j+4*M₀*D j)/(U j+A j+1):=div_le_div_of_nonneg_right hv (hden j).le
      _=(4*(M₀+1)*n j^(c-γ))*(U j/(U j+A j+1))+4*M₀*(D j/(U j+A j+1)):=by ring
      _≤ _:=by nlinarith [mul_le_mul_of_nonneg_left hratio hcoeff]
end Aa
noncomputable section
open Filter
open scoped Topology
end
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
namespace Aa
theorem OD (n η U A D:ℕ→ ℝ) (θ:ℝ) (hθ:0< θ)
    (hn:Tendsto n atTop atTop) (hη:Tendsto η atTop (𝓝 0))
    (hη0:∀ j,0≤ η j) (hU:∀ j,0≤ U j) (hA:∀ j,0≤ A j) (hD:∀ j,0≤ D j)
    (hbound:∀ τ H:ℝ,0< τ→ τ≤1→0≤ H→∀ᶠ j in atTop,
      D j≤(2*(1/Real.log (n j))/τ^2+2*(1/Real.log (n j))/(θ-η j)+((θ+η j)/(θ-η j)-1))*U j +
        (2*τ/(θ-η j)+(2-2*((θ-η j)/(θ+η j/8))))*A j +
        4*(1/Real.log (n j))*H+32*Real.exp (-H/2)) :
    Tendsto (fun j=> D j/(U j+A j+1)) atTop (𝓝 0):=by
  have hlamT:Tendsto (fun j=>1/Real.log (n j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hn)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun j=> ha.trans_le (div_nonneg (hD j) (by linarith [hU j,hA j]))
  · intro ε hε
    let τ:=min 1 (ε*θ/16)
    have hτ:0< τ:=lt_min (by norm_num) (by positivity)
    have hτ1:τ≤1:=min_le_left _ _
    have hτb:2*τ/θ≤ ε/8:=by
      apply (div_le_iff₀ hθ).mpr
      have:=min_le_right (1:ℝ) (ε*θ/16)
      dsimp [τ] at ⊢
      linarith
    have htExp:Tendsto (fun H:ℝ=>32*Real.exp (-H/2)) atTop (𝓝 0):=by
      have hd:Tendsto (fun H:ℝ=> H/2) atTop atTop:=by
        simpa only [div_eq_mul_inv,mul_comm,id_eq,one_mul] using
          (tendsto_const_mul_atTop_of_pos (by norm_num:(0:ℝ)<1/2)).mpr tendsto_id
      simpa only [Function.comp_def,neg_div,mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp hd).const_mul 32
    obtain ⟨H,hH,hHb⟩:=(eventually_ge_atTop (0:ℝ) |>.and (htExp.eventually (eventually_lt_nhds (show (0:ℝ)<ε/8 by linarith)))).exists
    let a:=fun j=>2*(1/Real.log (n j))/τ^2+2*(1/Real.log (n j))/(θ-η j)+((θ+η j)/(θ-η j)-1)
    let b:=fun j=>2*τ/(θ-η j)+(2-2*((θ-η j)/(θ+η j/8)))
    let e:=fun j=>4*(1/Real.log (n j))*H+32*Real.exp (-H/2)
    have hθm:Tendsto (fun j=> θ-η j) atTop (𝓝 θ):=by
      simpa using (tendsto_const_nhds (x:=θ)).sub hη
    have hθp:Tendsto (fun j=> θ+η j) atTop (𝓝 θ):=by
      simpa using (tendsto_const_nhds (x:=θ)).add hη
    have hθp8:Tendsto (fun j=> θ+η j/8) atTop (𝓝 θ):=by
      simpa using (tendsto_const_nhds (x:=θ)).add (hη.div_const 8)
    have ha:Tendsto a atTop (𝓝 0):=by
      have ha1:Tendsto (fun j=>2*(1/Real.log (n j))/τ^2) atTop (𝓝 0):=by
        simpa using (hlamT.const_mul 2).div_const (τ^2)
      have ha2:Tendsto (fun j=>2*(1/Real.log (n j))/(θ-η j)) atTop (𝓝 0):=by
        convert (hlamT.const_mul 2).div hθm hθ.ne' using 1 <;> first | rfl | simp
      have ha3:Tendsto (fun j=>(θ+η j)/(θ-η j)-1) atTop (𝓝 0):=by
        simpa [hθ.ne',Pi.div_apply] using (hθp.div hθm hθ.ne').sub (tendsto_const_nhds (x:=1))
      simpa [a] using (ha1.add ha2).add ha3
    have hb:Tendsto b atTop (𝓝 (2*τ/θ)):=by
      have hb1:=(tendsto_const_nhds (x:=2*τ)).div hθm hθ.ne'
      have hb2:Tendsto (fun j=>2-2*((θ-η j)/(θ+η j/8))) atTop (𝓝 0):=by
        simpa [hθ.ne',Pi.div_apply] using (tendsto_const_nhds (x:= (2:ℝ))).sub ((hθm.div hθp8 hθ.ne').const_mul 2)
      simpa [b,Pi.div_apply] using hb1.add hb2
    have he:Tendsto e atTop (𝓝 (32*Real.exp (-H/2))):=by
      simpa [e] using ((hlamT.const_mul 4).mul_const H).add (tendsto_const_nhds (x:=32*Real.exp (-H/2)))
    have hlt:2*τ/θ+32*Real.exp (-H/2)<ε:=by linarith
    have hsum:=(ha.add hb |>.add he).eventually (eventually_lt_nhds (by simpa using hlt))
    filter_upwards [hbound τ H hτ hτ1 hH,hsum,hη.eventually (eventually_lt_nhds hθ),
      (Real.tendsto_log_atTop.comp hn).eventually (eventually_gt_atTop (0:ℝ))] with j hj hjlt hjη hjlog
    have ha0:0≤ a j:=by
      have hr:1≤(θ+η j)/(θ-η j):=(one_le_div (sub_pos.mpr hjη)).mpr (by linarith [hη0 j])
      dsimp [a]
      positivity
    have hb0:0≤ b j:=by
      have hr:(θ-η j)/(θ+η j/8)≤1:=(div_le_one (by linarith [hη0 j]:0<θ+η j/8)).mpr (by linarith [hη0 j])
      have hr0:0≤2-2*((θ-η j)/(θ+η j/8)):=by linarith
      dsimp [b]
      positivity
    have he0:0≤ e j:=by dsimp [e]; positivity
    have hden:0< U j+A j+1:=by linarith [hU j,hA j]
    have hupper:D j≤(a j+b j+e j)*(U j+A j+1):=by
      have hj':D j≤ a j*U j+b j*A j+e j:=by
        simpa only [a,b,e,add_assoc] using hj
      nlinarith only [hj',hU j,hA j,ha0,hb0,he0,mul_nonneg ha0 (hA j),mul_nonneg hb0 (hU j),mul_nonneg he0 (hU j),mul_nonneg he0 (hA j)]
    exact (div_le_iff₀ hden).mpr hupper |>.trans_lt hjlt
end Aa
namespace Aa
open Filter
open scoped Topology
open Bg
variable (V:ℕ→ Type u1) (I:ℕ→ Type u2) (K:ℕ→ Type u3) [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]
variable (G:∀ j,Core.Au (V j) (I j)) (θ γ c:ℝ) (η:ℕ→ ℝ)
  (Z₁ Z₂:∀ j,V j→ K j) (h₁:∀ j,Function.Injective (Z₁ j)) (h₂:∀ j,Function.Injective (Z₂ j))
theorem HS (hθ:0<θ)
    (hn:Tendsto (fun j=>(Fintype.card (V j):ℝ)) atTop atTop)
    (hη:Tendsto η atTop (𝓝 0)) (hη0:∀ j,0≤η j)
    (hG:∀ j,AJ (V j) (I j) (G j) θ γ c (η j))
    (t:∀ j,I j→ K j)
    (ht:∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    Tendsto (fun j=> DC (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) c /
      (AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1))
      atTop (𝓝 0):=by
  apply OD (fun j=>(Fintype.card (V j):ℝ)) η _ _ _ θ hθ hn hη hη0
    (fun j=> BK _ _ _ _) (fun j=> Bu _ _ _ _)
    (fun j=> Ga _ _ _ _ c)
  intro τ H hτ hτ1 hH
  filter_upwards [hη.eventually (eventually_lt_nhds hθ),
    (Real.tendsto_log_atTop.comp hn).eventually (eventually_ge_atTop (2:ℝ)),
    hn.eventually (eventually_ge_atTop (2/τ))] with j hjη hjlog hjn
  have hlog:0≤1/Real.log (Fintype.card (V j):ℝ):=by positivity
  have hlog2:1/Real.log (Fintype.card (V j):ℝ)≤1/2:=by
    exact one_div_le_one_div_of_le (by norm_num) hjlog
  have hτn:2≤τ*(Fintype.card (V j):ℝ):=by
    have:=(div_le_iff₀ hτ).mp hjn
    nlinarith
  exact (hG j).JM (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) hjη (hη0 j)
    (t j) (ht j) τ H hlog hlog2 hτ hτ1 hτn hH
end Aa
namespace Aa.Core.Au
open scoped BigOperators
open Variance
variable {V:Type u4} {I:Type u5} [Fintype V] [Fintype I] [DecidableEq V]
variable (G:Au V I)
def Ay (T:ℝ) (y:V):ℝ:=if T≤((G.BV y).card:ℝ) then G.Ax y else 0
def Aw (T:ℝ) (y:V):Finset V:=if T≤((G.BV y).card:ℝ) then G.BV y else Finset.univ
omit [Fintype I] in
lemma Dp (T:ℝ) (y:V):0≤G.Ay T y:=by
  unfold Ay Ax Ap
  split_ifs <;> positivity
omit [Fintype I] in
lemma OR (T:ℝ) (y:V):G.Ay T y≤G.Ax y:=by
  unfold Ay
  split_ifs
  · exact le_rfl
  · unfold Ax Ap; positivity
omit [Fintype I] in
lemma Ge (T:ℝ) (hG:0<G.Ap):(∑ y,G.Ay T y)≤1:=by
  rw [← G.IL hG]
  exact Finset.sum_le_sum (fun y _=> G.OR T y)
omit [Fintype I] in
lemma Ft (T:ℝ) (hT:T≤Fintype.card V) (y:V):T≤((G.Aw T y).card:ℝ):=by
  unfold Aw
  split_ifs with h
  · exact h
  · simpa using hT
omit [Fintype I] in
lemma Ic (T M:ℝ) (hdom:∀ x y,G.Av x y≤M*Az Finset.univ x y)
    (hn:2≤Fintype.card V) (x:V) :
    (∑ y,G.Ay T y*Ae (G.Aw T y) x)≤M*Ae Finset.univ x:=by
  refine le_trans (Finset.sum_le_sum (fun y _ => ?_)) (G.Nl M hdom hn x)
  unfold Ay Aw
  split_ifs
  · exact le_rfl
  · simp only [zero_mul]
    unfold Ax Ap Ae
    split_ifs <;> positivity
end Aa.Core.Au
namespace Aa
open Filter Variance Bg
open scoped Topology BigOperators
variable {V:ℕ→ Type u6} {I:ℕ→ Type u7} {K:ℕ→ Type u8} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]
variable (G:∀ j,Core.Au (V j) (I j)) (θ γ c:ℝ) (η:ℕ→ ℝ)
  (Z₁ Z₂:∀ j,V j→ K j) (h₁:∀ j,Function.Injective (Z₁ j)) (h₂:∀ j,Function.Injective (Z₂ j))
lemma AJ.Gl {V:Type u9} {I:Type u10} [Fintype V] [Fintype I] [DecidableEq V]
    {G:Core.Au V I} {θ γ c η:ℝ} (h:AJ V I G θ γ c η) (hθ:0<θ)
    (hη:η≤θ/2) (x y:V):G.Av x y≤(2/θ)*Az Finset.univ x y:=by
  have hh:η<θ:=by linarith
  refine (h.KG hh x y).trans (mul_le_mul_of_nonneg_right ?_ (by
    unfold Az
    split_ifs
    · have hn:(2:ℝ)≤Fintype.card V:=by exact_mod_cast h.Cz
      simp only [Finset.card_univ]
      exact div_nonneg (by norm_num) (mul_nonneg (by positivity) (by linarith))
    · exact le_rfl))
  apply (div_le_div_iff₀ (by linarith:0<θ-η) hθ).mpr
  linarith
def Ew (j:ℕ):ℝ:=Ac (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
  (Aj (G j).Af (G j).targets ((Fintype.card (V j):ℝ)^(1-c)))
def JF (j:ℕ):ℝ:=Ac (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
  (Aj ((G j).Ay ((Fintype.card (V j):ℝ)^γ))
    ((G j).Aw ((Fintype.card (V j):ℝ)^γ)) ((Fintype.card (V j):ℝ)^(1-c)))
theorem DG (hθ:0<θ) (hγ:0<γ) (hγ1:γ<1) (hcγ:c<γ)
    (hn:Tendsto (fun j=>(Fintype.card (V j):ℝ)) atTop atTop)
    (hη:Tendsto η atTop (𝓝 0)) (hη0:∀ j,0≤η j) (hηb:∀ j,η j≤θ/2)
    (hG:∀ j,AJ (V j) (I j) (G j) θ γ c (η j))
    (t:∀ j,I j→ K j) (ht:∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    Tendsto (fun j=> Ew G c Z₁ Z₂ h₁ h₂ j /
      (AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) ∧
    Tendsto (fun j=> JF G γ c Z₁ Z₂ h₁ h₂ j /
      (AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0):=by
  have hsmall:=HS V I K G θ γ c η Z₁ Z₂ h₁ h₂ hθ hn hη hη0 hG t ht
  have hηlt (j):η j<θ:=by linarith [hηb j]
  have hpos (j):0<(G j).Ap:=(hG j).CR (hηlt j)
  have hdom (j x y):=(hG j).Gl hθ (hηb j) x y
  constructor
  · exact Gg Z₁ Z₂ h₁ h₂ (fun j=>(G j).Af) (fun j=>(G j).targets)
      γ c (2/θ) hγ hγ1 hcγ (hcγ.trans hγ1) (by positivity) hn
      (fun j=>(G j).AT) (fun j=>(G j).Bz (hpos j) |>.le)
      (Eventually.of_forall fun j e=>(hG j).fiber e |>.le)
      (Eventually.of_forall fun j x=>(G j).Fm _ (hdom j) (hG j).Cz x) hsmall
  · apply Gg Z₁ Z₂ h₁ h₂
      (fun j=>(G j).Ay ((Fintype.card (V j):ℝ)^γ))
      (fun j=>(G j).Aw ((Fintype.card (V j):ℝ)^γ)) γ c (2/θ)
      hγ hγ1 hcγ (hcγ.trans hγ1) (by positivity) hn
      (fun j y=>(G j).Dp _ y)
      (fun j=>(G j).Ge _ (hpos j)) _ _ hsmall
    · apply Eventually.of_forall
      intro j y
      apply (G j).Ft
      have hn1:(1:ℝ)≤Fintype.card (V j):=by exact_mod_cast (by have:=(hG j).Cz; omega:1≤Fintype.card (V j))
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hγ1.le
    · exact Eventually.of_forall fun j x=>(G j).Ic _ _ (hdom j) (hG j).Cz x
end Aa
end
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
namespace Aa.Variance
open scoped BigOperators
variable {P:Type u1} {I:Type u2} [Fintype P] [DecidableEq P] [Fintype I]
lemma NX (w:I→ ℝ) (B:I→ Finset P) (T M κ:ℝ)
    (hw:∀ i,0≤w i) (hW:(∑ i,w i)≤1) (hT:1≤T) (hκ:0≤κ)
    (hk:∀ i,2/((B i).card:ℝ)≤κ)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤M*Ae Finset.univ x) (C:Finset P) :
    (∑ i,w i*(Ad (B i) C)^2) ≤
      2*Aj w B T C+4*Ah Finset.univ C+ κ*M*Ad Finset.univ C:=by
  have hmean:=HP w B C M hdom
  have hm:0≤M*Ad Finset.univ C:=(Finset.sum_nonneg (fun i _=> mul_nonneg (hw i) (Bd _ _))).trans hmean
  unfold Aj
  split_ifs with hlarge
  · have hmC:2≤C.card:=by have:(1:ℝ)<C.card:=hT.trans_lt hlarge; exact_mod_cast this
    have hcomp:=(Cw C hmC).1
    have hb:(∑ i,w i*(Ad Finset.univ C)^2)≤(Ad Finset.univ C)^2:=by
      rw [← Finset.sum_mul]
      nlinarith [sq_nonneg (Ad Finset.univ C)]
    have hh:(∑ i,w i*(Ad (B i) C)^2) ≤
        2*(∑ i,w i*(Ad (B i) C-Ad Finset.univ C)^2) +
        2*(∑ i,w i*(Ad Finset.univ C)^2):=by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      have h:=mul_le_mul_of_nonneg_left (show (Ad (B i) C)^2 ≤
        2*(Ad (B i) C-Ad Finset.univ C)^2+2*(Ad Finset.univ C)^2 by
          nlinarith [sq_nonneg (Ad (B i) C-2*Ad Finset.univ C)]) (hw i)
      nlinarith
    nlinarith [mul_nonneg hκ hm]
  · have hh:(∑ i,w i*(Ad (B i) C)^2) ≤
        (∑ i,w i*(if 2/((B i).card:ℝ)≤Ad (B i) C then (Ad (B i) C)^2 else 0)) +
        κ*(∑ i,w i*Ad (B i) C):=by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · nlinarith [mul_nonneg hκ (mul_nonneg (hw i) (Bd (B i) C))]
      · have hp:Ad (B i) C≤κ:=(le_of_lt (lt_of_not_ge hi)).trans (hk i)
        have h:=mul_le_mul_of_nonneg_left hp (mul_nonneg (hw i) (Bd (B i) C))
        nlinarith
    have hκmean:=mul_le_mul_of_nonneg_left hmean hκ
    nlinarith [BJ Finset.univ C]
lemma Qd {w:I→ ℝ} {B:I→ Finset P} (src:I→ P) (T δ:ℝ)
    (hw:∀ i,0≤w i) (hδ:0<δ) (hk:∀ i,2/((B i).card:ℝ)≤2*δ)
    (C:Finset P) (hC:Ad Finset.univ C≤δ) :
    (∑ i,w i*(if src i∈ C then Ad (B i) C else 0)) ≤
      (∑ i,w i*(if src i∈ C∧ Ad (B i) C<2*δ then Ad (B i) C else 0)) +
      (2/δ)*Aj w B T C:=by
  let err:=fun i=> if T<C.card then (Ad (B i) C-Ad Finset.univ C)^2
    else (1/2)*(if 2/((B i).card:ℝ)≤Ad (B i) C then (Ad (B i) C)^2 else 0)
  have he:Aj w B T C=∑ i,w i*err i:=by
    unfold Aj err
    split_ifs <;> simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hnon (i):0≤err i:=by dsimp [err]; split_ifs <;> positivity
  have hpoint (i):(if src i∈ C then Ad (B i) C else 0) ≤
      (if src i∈ C∧ Ad (B i) C<2*δ then Ad (B i) C else 0)+(2/δ)*err i:=by
    by_cases hs:src i∈ C
    · by_cases hsmall:Ad (B i) C<2*δ
      · simp only [hs,hsmall,true_and,ite_true]
        exact le_add_of_nonneg_right (mul_nonneg (by positivity) (hnon i))
      · have hp2:2*δ≤Ad (B i) C:=le_of_not_gt hsmall
        simp only [hs,hsmall,true_and,ite_true,ite_false,zero_add]
        rw [show (2/δ)*err i=2*err i/δ by ring]
        apply (le_div_iff₀ hδ).mpr
        dsimp [err]
        split_ifs with hl hp
        · have hd:δ≤Ad (B i) C-Ad Finset.univ C:=by linarith
          have hp:=Bd (B i) C
          nlinarith [mul_nonneg (by linarith:0≤Ad (B i) C-2*Ad Finset.univ C)
            (by linarith:0≤Ad (B i) C-Ad Finset.univ C),
            mul_nonneg hp (sub_nonneg.mpr hd)]
        · nlinarith [mul_nonneg (Bd (B i) C)
            (by linarith:0≤Ad (B i) C-δ)]
        · exact False.elim (hp ((hk i).trans hp2))
    · simp only [hs,false_and,ite_false,zero_add]
      exact mul_nonneg (by positivity) (hnon i)
  rw [he,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hh:=mul_le_mul_of_nonneg_left (hpoint i) (hw i)
  convert hh using 1; ring
end Aa.Variance
namespace Aa.Ak.Depth
open MeasureTheory
open scoped BigOperators
variable {P:Type u3} [Fintype P] [DecidableEq P] (d:Depth P)
lemma Gc (r:ℝ) (x:P) :
    x∈ d.DL r↔ Fintype.card P<2*(d.cell r x).card:=by
  constructor
  · intro hx
    obtain ⟨C,hC,hx⟩:=Finset.mem_biUnion.mp hx
    have hc:=(d.CY r C).mp hC
    simpa only [d.Cx hc.1 hx] using hc.2
  · intro hx
    have hc:d.cell r x∈ d.AR r:=(d.CY r _).mpr ⟨d.CX _ _,hx⟩
    rw [d.Gj hc]
    exact d.CQ r x
lemma Qf (r:ℝ) (x:P) :
    x∈ d.DL r↔∃ C:Finset P,Fintype.card P<2*C.card∧∀ y∈ C,d.share r x y:=by
  rw [d.Gc]
  constructor
  · intro hc
    exact ⟨d.cell r x,hc,fun y hy=>(d.BN r x y).mp hy⟩
  · rintro ⟨C,hc,hs⟩
    have hsub:C⊆ d.cell r x:=fun y hy=>(d.BN r x y).mpr (hs y hy)
    have:=Finset.card_le_card hsub
    omega
lemma RK {r t:ℝ} (htr:t≤ r) {x:P} (hx:x∈ d.DL r):x∈ d.DL t:=by
  rw [d.Gc] at hx ⊢
  have:=Finset.card_le_card (d.Hh htr x)
  omega
lemma Ot (x:P):IsClosed {r:ℝ | x∈ d.DL r}:=by
  simp_rw [d.Qf,Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro C
  simp only [Set.ofPred_and]
  apply IsClosed.inter
  · by_cases h:Fintype.card P<2*C.card <;> simp [h]
  · simp_rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    by_cases hxy:x=y
    · simp [share,hxy]
    · simp only [share,hxy,false_or]
      exact isClosed_le continuous_id continuous_const
lemma RV (hn:2≤ Fintype.card P) (x:P):x∈ d.DL (-d.radius):=by
  rw [d.Gc,d.EO le_rfl,Finset.card_univ]
  omega
lemma Md (hn:2≤ Fintype.card P) {r:ℝ} {x:P} (hx:x∈ d.DL r):r≤ d.M:=by
  obtain ⟨C,hC,_⟩:=Finset.mem_biUnion.mp hx
  exact (d.FC hn r).mp ⟨C,hC⟩
def Fj (x:P):ℝ:=sSup {r:ℝ | x∈ d.DL r}
lemma JZ (hn:2≤ Fintype.card P) (x:P) (r:ℝ) :
    x∈ d.DL r↔ r≤ d.Fj x:=by
  have hne:Set.Nonempty {t:ℝ | x∈ d.DL t}:=⟨-d.radius,d.RV hn x⟩
  have hbd:BddAbove {t:ℝ | x∈ d.DL t}:=⟨d.M,fun t ht=> d.Md hn ht⟩
  exact ⟨fun hx=> le_csSup hbd hx,fun hr=> d.RK hr ((d.Ot x).csSup_mem hne hbd)⟩
lemma Iq (hn:2≤ Fintype.card P) (x:P):d.Fj x≤ d.M :=
  d.Md hn ((d.JZ hn x _).mpr le_rfl)
lemma GD (hn:2≤ Fintype.card P) (x:P) :
    (fun r=> d.Ai r x)=(Set.Ioc (d.Fj x) d.M).indicator (fun _=>(1:ℝ)):=by
  funext r
  simp only [Ai,d.FC hn,d.JZ hn,not_le,Set.indicator,Set.mem_Ioc]
  congr 1
  exact propext and_comm
lemma JQ {a b:ℝ} (hab:a≤ b) :
    (∫ r:ℝ,(Set.Ioc a b).indicator (fun _=>(1:ℝ)) r)=b-a:=by
  rw [integral_indicator measurableSet_Ioc,integral_const]
  simp [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
lemma Ie (hn:2≤ Fintype.card P) (x:P):d.Ag x= d.M-d.Fj x:=by
  unfold Ag
  rw [d.GD hn x,JQ (d.Iq hn x)]
lemma KI (hn:2≤ Fintype.card P) (x y:P) :
    (fun r=> d.Ai r x*d.Ai r y) =
      (Set.Ioc (max (d.Fj x) (d.Fj y)) d.M).indicator (fun _=>(1:ℝ)):=by
  funext r
  rw [congrFun (d.GD hn x) r,congrFun (d.GD hn y) r]
  simp only [Set.indicator,Set.mem_Ioc,max_lt_iff]
  split_ifs <;> simp_all
lemma Sn (hn:2≤ Fintype.card P) (x y:P) :
    min (d.Ag x) (d.Ag y)=∫ r,d.Ai r x*d.Ai r y:=by
  rw [d.KI hn x y,JQ (max_le (d.Iq hn x) (d.Iq hn y)),
    d.Ie hn x,d.Ie hn y]
  exact min_sub_sub_left d.M (d.Fj x) (d.Fj y)
end Aa.Ak.Depth
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Aa.EG
variable {P:Type u4} [Fintype P]
def step (a:ℝ):ℝ→ ℝ:=(Set.Ioc 0 a).indicator (fun _=>1)
lemma HR (a:ℝ):Integrable (step a):=by
  rw [step,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
lemma TF (a b:ℝ):(fun r=> step a r*step b r)=step (min a b):=by
  funext r
  simp only [step,Set.indicator,Set.mem_Ioc,le_min_iff]
  split_ifs <;> simp_all
lemma Sg (a:ℝ) (ha:0≤a):(∫ r,step a r)=a:=by
  rw [step,integral_indicator measurableSet_Ioc]
  simp [integral_const,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal ha]
def tail (p a:P→ ℝ) (r:ℝ):ℝ:=∑ x,p x*step (a x) r
def energy (p a b:P→ ℝ):ℝ:=∑ x,∑ y,p x*p y*min (a x) (b y)
lemma NU (p a b:P→ ℝ) :
    (fun r=> tail p a r*tail p b r)= fun r=>∑ x,∑ y,(p x*p y)*step (min (a x) (b y)) r:=by
  funext r
  simp only [tail]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [← congrFun (TF (a x) (b y)) r]
  ring
lemma Da (p a b:P→ ℝ):Integrable (fun r=> tail p a r*tail p b r):=by
  rw [NU]
  exact integrable_finsetSum _ fun x _=> integrable_finsetSum _ fun y _ =>
    (HR _).const_mul _
lemma Hp (p a b:P→ ℝ) (ha:∀ x,0≤a x) (hb:∀ x,0≤b x) :
    energy p a b=∫ r,tail p a r*tail p b r:=by
  rw [NU,integral_finsetSum _ (fun x _=> integrable_finsetSum _ fun y _=>(HR _).const_mul _)]
  simp_rw [integral_finsetSum _ (fun y _=>(HR _).const_mul _),integral_const_mul]
  simp only [Sg _ (le_min (ha _) (hb _)),energy]
lemma OC (p a b:P→ ℝ) (ha:∀ x,0≤a x) (hb:∀ x,0≤b x) :
    2*energy p a b≤ energy p a a+energy p b b:=by
  rw [Hp p a b ha hb,Hp p a a ha ha,Hp p b b hb hb]
  rw [← integral_const_mul,← integral_add (Da p a a) (Da p b b)]
  apply integral_mono ((Da p a b).const_mul 2)
    ((Da p a a).add (Da p b b))
  intro r
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (tail p a r-tail p b r)]
lemma SP (a b c d:ℝ) (ha:0≤a) (hb:0≤b) (hc:0≤c) (hd:0≤d) :
    min (a+b) (c+d)≤ min a c+min a d+min b c+min b d:=by
  simp only [min_def]
  split_ifs <;> linarith
lemma Tu (p a b:P→ ℝ) (hp:∀ x,0≤p x) (ha:∀ x,0≤a x) (hb:∀ x,0≤b x) :
    energy p (a+b) (a+b)≤2*(energy p a a+energy p b b):=by
  have hh:energy p (a+b) (a+b)≤ energy p a a+energy p a b+energy p b a+energy p b b:=by
    unfold energy
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    have h:=mul_le_mul_of_nonneg_left (SP (a x) (b x) (a y) (b y) (ha x) (hb x) (ha y) (hb y))
      (mul_nonneg (hp x) (hp y))
    simpa only [Pi.add_apply,mul_add] using h
  nlinarith [OC p a b ha hb,OC p b a hb ha]
end Aa.EG
namespace Aa.Ak.Depth
open MeasureTheory
open scoped BigOperators
variable {P:Type u5} [Fintype P] [DecidableEq P]
variable (d:Depth P)
def Br (p:P→ ℝ) (r:ℝ):ℝ:=∑ x,p x*d.Ai r x
lemma DW (hn:2≤ Fintype.card P) (x y:P) :
    Integrable (fun r=> d.Ai r x*d.Ai r y):=by
  rw [d.KI hn x y,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
lemma Iw (p:P→ ℝ) (r:ℝ) :
    (d.Br p r)^2=∑ x,∑ y,p x*p y*(d.Ai r x*d.Ai r y):=by
  unfold Br
  rw [pow_two,Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring
lemma Jj (hn:2≤ Fintype.card P) (p:P→ ℝ) :
    EG.energy p d.Ag d.Ag=∫ r,(d.Br p r)^2:=by
  simp only [d.Iw]
  rw [integral_finsetSum _ (fun x _=> integrable_finsetSum _ fun y _=>(d.DW hn x y).const_mul _)]
  simp_rw [integral_finsetSum _ (fun y _=>(d.DW hn _ y).const_mul _),integral_const_mul]
  simp only [EG.energy,d.Sn hn]
theorem KV (d':Depth P) (hn:2≤ Fintype.card P)
    (p:P→ ℝ) (hp:∀ x,0≤p x) :
    (∑ x,∑ y,p x*p y*min (d.Ag x+d'.Ag x) (d.Ag y+d'.Ag y)) ≤
      2*((∫ r,(d.Br p r)^2)+(∫ r,(d'.Br p r)^2)):=by
  rw [← d.Jj hn p,← d'.Jj hn p]
  exact EG.Tu p d.Ag d'.Ag hp d.BM d'.BM
end Aa.Ak.Depth
namespace Aa.Ak.Depth
open MeasureTheory Variance
open scoped BigOperators
variable {P:Type u6} {I:Type u7} [Fintype P] [DecidableEq P] [Fintype I]
variable (d:Depth P)
lemma Px (B:Finset P) {r:ℝ} {G:Finset P} (hG:G∈d.AR r) :
    d.Br (Ae B) r=Ad B Gᶜ:=by
  have hne:(d.AR r).Nonempty:=⟨G,hG⟩
  have he (x):Ae B x*d.Ai r x=if x∈Gᶜ then Ae B x else 0:=by
    simp only [Ai,hne,d.Gj hG,true_and]
    by_cases hx:x∈G <;> simp [hx]
  simp only [Br,he,Finset.sum_ite_mem,Finset.univ_inter,Ci]
lemma PU (p:P→ ℝ) {r:ℝ} (hG:¬(d.AR r).Nonempty):d.Br p r=0:=by
  simp [Br,Ai,hG]
lemma QP (f:Finset P→ ℝ) (hf:∀ C,0≤f C) (r:ℝ):0≤d.Ch f r:=by
  rw [d.Fe]
  exact Finset.sum_nonneg (fun C _=> mul_nonneg (by unfold count; positivity) (hf C))
lemma KN (f:Finset P→ ℝ) (hf:∀ C,0≤f C) {r:ℝ} {G:Finset P}
    (hG:G∈d.AR r):f Gᶜ≤d.Ch f r:=by
  have hs:d.AR r={G}:=Finset.ext fun C=> by
    simp only [Finset.mem_singleton]
    exact ⟨fun hC=> d.GW hC hG,fun h=> h ▸ hG⟩
  rw [d.It,hs,Finset.sum_singleton]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun C _=> by split_ifs <;> simp_all only [le_refl]))
lemma Mh (w:I→ ℝ) (B:I→ Finset P) (T M κ:ℝ)
    (hw:∀ i,0≤w i) (hW:(∑ i,w i)≤1) (hT:1≤T) (hκ:0≤κ)
    (hk:∀ i,2/((B i).card:ℝ)≤κ)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤M*Ae Finset.univ x) (r:ℝ) :
    (∑ i,w i*(d.Br (Ae (B i)) r)^2) ≤
      d.Ch (fun C=>2*Aj w B T C+4*Ah Finset.univ C) r +
      κ*M*d.Br (Ae Finset.univ) r:=by
  have hf (C:Finset P):0≤2*Aj w B T C+4*Ah Finset.univ C :=
    add_nonneg (mul_nonneg (by norm_num) (Bw w B T hw C))
      (mul_nonneg (by norm_num) (BJ _ _))
  by_cases hg:(d.AR r).Nonempty
  · obtain ⟨G,hG⟩:=hg
    simp_rw [d.Px _ hG]
    exact (NX w B T M κ hw hW hT hκ hk hdom Gᶜ).trans
      (add_le_add (d.KN _ hf hG) le_rfl)
  · simp only [d.PU _ hg,zero_pow (by norm_num:2≠0),mul_zero,Finset.sum_const_zero,add_zero]
    exact d.QP _ hf r
lemma ES (hn:2≤Fintype.card P) (p:P→ ℝ) :
    Integrable (fun r=>(d.Br p r)^2):=by
  simp only [d.Iw]
  exact integrable_finsetSum _ fun x _=> integrable_finsetSum _ fun y _ =>
    (d.DW hn x y).const_mul _
lemma Mx (hn:2≤Fintype.card P) (p:P→ ℝ) :
    (∫ r,d.Br p r)=∑ x,p x*d.Ag x:=by
  simp only [Br]
  rw [integral_finsetSum _ (fun x _=>(d.Bo hn x).const_mul _)]
  simp only [integral_const_mul,Ag]
theorem FT (hn:2≤Fintype.card P)
    (w:I→ ℝ) (B:I→ Finset P) (T M κ:ℝ)
    (hw:∀ i,0≤w i) (hW:(∑ i,w i)≤1) (hT:1≤T) (hκ:0≤κ)
    (hB:∀ i,2≤(B i).card) (hk:∀ i,2/((B i).card:ℝ)≤κ)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤M*Ae Finset.univ x) :
    (∑ i,w i*(∫ r,(d.Br (Ae (B i)) r)^2)) ≤
      2*Ac d.mass (Aj w B T) +
      4*Ac d.mass (Ah Finset.univ) +
      κ*M*(∑ x,Ae Finset.univ x*d.Ag x):=by
  let f:=fun C=>2*Aj w B T C+4*Ah Finset.univ C
  have hf:∀ C,C.card≤1→ f C=0:=by
    intro C hC
    simp [f,EL w B T hT hB C hC,DN Finset.univ C hC]
  have hi₁:Integrable (fun r=>∑ i,w i*(d.Br (Ae (B i)) r)^2) :=
    integrable_finsetSum _ (fun i _=>(d.ES hn _).const_mul _)
  have hi₂:Integrable (fun r=> d.Ch f r):=d.Er hn f hf
  have hi₃:Integrable (fun r=> κ*M*d.Br (Ae Finset.univ) r) :=
    (integrable_finsetSum _ (fun x _=>(d.Bo hn x).const_mul _)).const_mul _
  have hh:=integral_mono hi₁ (hi₂.add hi₃) (d.Mh w B T M κ hw hW hT hκ hk hdom)
  simp only [Pi.add_apply] at hh
  rw [integral_finsetSum _ (fun i _=>(d.ES hn _).const_mul _),
    integral_add hi₂ hi₃,integral_const_mul,d.Mx hn _,d.DB hn f hf] at hh
  try simp only [integral_const_mul] at hh
  have he:(∑ C,d.mass C*f C)=
      2*Ac d.mass (Aj w B T)+4*Ac d.mass (Ah Finset.univ):=by
    simp only [Ac,f,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl; intro C _; ring
    · apply Finset.sum_congr rfl; intro C _; ring
  rwa [he] at hh
end Aa.Ak.Depth
namespace Aa.EG
open scoped BigOperators
variable {P:Type u8} [Fintype P]
lemma SB (p S L E:P→ ℝ) (c:ℝ)
    (hp:∀ x,0≤p x) (hsum:(∑ x,p x)=1)
    (hL:∀ x,0≤L x)
    (hS:∀ x,p x≠0→ S x=c+L x-E x) :
    (∑ x,p x*S x)-(∑ x,p x*L x)-(∑ x,p x*|E x|)≤energy p S S:=by
  have hpair (x y:P) :
      p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2) ≤
        p x*p y*min (S x) (S y):=by
    by_cases hx:p x=0
    · simp [hx]
    by_cases hy:p y=0
    · simp [hy]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hp x) (hp y))
    have hxS:=hS x hx
    have hyS:=hS y hy
    apply le_min <;> linarith [hL x,hL y,le_abs_self (E x),le_abs_self (E y),neg_abs_le (E x),neg_abs_le (E y)]
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun y _=> hpair x y))
  change _≤energy p S S at hh
  have he:(∑ x,∑ y,p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2))=
      (∑ x,p x*S x)-(∑ x,p x*L x)-(∑ x,p x*|E x|):=by
    have hform (x y:P):p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2)=
        (p x*S x)*p y/2+p x*(p y*S y)/2-
        ((p x*L x)*p y/2+p x*(p y*L y)/2+(p x*|E x|)*p y/2+p x*(p y*|E y|)/2):=by ring
    simp_rw [hform,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_div,
      ← Finset.mul_sum,← Finset.sum_mul,hsum,mul_one,one_mul]
    ring
  rwa [he] at hh
end Aa.EG
namespace Aa.Ak.Depth
open MeasureTheory Variance
open scoped BigOperators
variable {P:Type u9} {I:Type u10} [Fintype P] [DecidableEq P] [Fintype I]
lemma Qa (d d':Depth P) (hn:2≤Fintype.card P)
    (w:I→ ℝ) (B:I→ Finset P) (T M κ:ℝ)
    (hw:∀ i,0≤w i) (hW:(∑ i,w i)≤1) (hT:1≤T) (hκ:0≤κ)
    (hB:∀ i,2≤(B i).card) (hk:∀ i,2/((B i).card:ℝ)≤κ)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤M*Ae Finset.univ x) :
    (∑ i,w i*EG.energy (Ae (B i)) (d.Ag+d'.Ag) (d.Ag+d'.Ag)) ≤
      4*(Ac d.mass (Aj w B T)+Ac d'.mass (Aj w B T))+
      8*(Ac d.mass (Ah Finset.univ)+Ac d'.mass (Ah Finset.univ))+
      2*κ*M*(∑ x,Ae Finset.univ x*(d.Ag x+d'.Ag x)):=by
  have hm (i):=d.KV d' hn (Ae (B i))
    (fun x=> by unfold Ae; split_ifs <;> positivity)
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=> mul_le_mul_of_nonneg_left (hm i) (hw i))
  change (∑ i,w i*EG.energy (Ae (B i)) (d.Ag+d'.Ag) (d.Ag+d'.Ag))≤_ at hsum
  have h₁:=d.FT hn w B T M κ hw hW hT hκ hB hk hdom
  have h₂:=d'.FT hn w B T M κ hw hW hT hκ hB hk hdom
  have hr:(∑ i,w i*(2*((∫ r,(d.Br (Ae (B i)) r)^2)+
      (∫ r,(d'.Br (Ae (B i)) r)^2))))=
      2*((∑ i,w i*(∫ r,(d.Br (Ae (B i)) r)^2))+
      (∑ i,w i*(∫ r,(d'.Br (Ae (B i)) r)^2))):=by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hr] at hsum
  simp only [mul_add,Finset.sum_add_distrib]
  linarith
lemma IC (d d':Depth P) (hn:2≤Fintype.card P)
    (w:I→ ℝ) (B:I→ Finset P) (src:I→ P) (t:I→ ℝ) (T M κ:ℝ)
    (hw:∀ i,0≤w i) (hW:(∑ i,w i)≤1) (hT:1≤T) (hκ:0≤κ)
    (hB:∀ i,2≤(B i).card) (hk:∀ i,2/((B i).card:ℝ)≤κ)
    (hsrc:∀ i,src i∉B i)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤M*Ae Finset.univ x) :
    (∑ i,w i*∑ y,Ae (B i) y*(d.Ag y+d'.Ag y)) ≤
      4*(Ac d.mass (Aj w B T)+Ac d'.mass (Aj w B T))+
      8*(Ac d.mass (Ah Finset.univ)+Ac d'.mass (Ah Finset.univ))+
      2*κ*M*(∑ x,Ae Finset.univ x*(d.Ag x+d'.Ag x))+
      (∑ i,w i*∑ y,Ae (B i) y*(AD d.mass (src i) y+AD d'.mass (src i) y))+
      (∑ i,w i*∑ y,Ae (B i) y*|d.value (src i) y+d'.value (src i) y-t i|):=by
  have hp (i:I) (y:P):0≤Ae (B i) y:=by unfold Ae; split_ifs <;> positivity
  have hL (dd:Depth P) (x y:P):0≤AD dd.mass x y:=by
    apply Finset.sum_nonneg; intro C _
    exact mul_nonneg (dd.Bf C) (by dsimp; split_ifs <;> norm_num)
  have hs (i:I) (y:P) (hy:Ae (B i) y≠0):y∈B i:=by
    by_contra hh; exact hy (by simp [Ae,hh])
  have hv (dd:Depth P) (i:I) (y:P) (hy:Ae (B i) y≠0) :
      AD dd.mass (src i) y=dd.AN (src i) y (fun he=> hsrc i (he ▸ hs i y hy)) :=
    dd.Gh hn _ _ _
  have he (i:I):=EG.SB (Ae (B i))
    (d.Ag+d'.Ag)
    (fun y=> AD d.mass (src i) y+AD d'.mass (src i) y)
    (fun y=> d.value (src i) y+d'.value (src i) y-t i)
    (d.M+d'.M-d.Ag (src i)-d'.Ag (src i)-t i)
    (hp i) (Bs (B i) (Finset.card_pos.mp (by have:=hB i; omega)))
    (fun y=> add_nonneg (hL d _ _) (hL d' _ _)) (by
      intro y hy
      have hxy:src i≠y:=fun h=> hsrc i (h ▸ hs i y hy)
      have hx:=d.Eg hn (src i) y hxy
      have hx':=d'.Eg hn (src i) y hxy
      rw [hv d i y hy,hv d' i y hy]
      simp only [Pi.add_apply]
      linarith)
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=> mul_le_mul_of_nonneg_left (he i) (hw i))
  have hu:=Qa d d' hn w B T M κ hw hW hT hκ hB hk hdom
  simp only [Pi.add_apply,mul_sub,Finset.sum_sub_distrib] at hh
  linarith
end Aa.Ak.Depth
noncomputable section
end
end
end
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Aa.Bg
open Ak MeasureTheory Variance
open scoped BigOperators
variable {P:Type u1} [Fintype P] [DecidableEq P]
variable {K:Type u2} [Field K] [NumberField K]
variable (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
def Fq:Finset (NumberField.FinitePlace K) :=by
  classical
  exact Bq Z₁ h₁∪ Bq Z₂ h₂
def average (f:Depth P→ Depth P→ ℝ):ℝ :=
  (∑ v:NumberField.InfinitePlace K,Arithmetic.Bh v *
    ∫ ω,f (arch Z₁ v ω) (arch Z₂ v ω) ∂Ao.As) +
  (Module.finrank ℚ K:ℝ)⁻¹*∑ v∈ Fq Z₁ Z₂ h₁ h₂,
    f (finite Z₁ h₁ v) (finite Z₂ h₂ v)
def AU (f:Depth P→ Depth P→ ℝ):Prop :=
  ∀ v:NumberField.InfinitePlace K,
    Integrable (fun ω=> f (arch Z₁ v ω) (arch Z₂ v ω)) Ao.As
lemma SI {f g:Depth P→ Depth P→ ℝ}
    (hi:AU Z₁ Z₂ f) (hj:AU Z₁ Z₂ g)
    (hfg:∀ d d',f d d'≤g d d') :
    average Z₁ Z₂ h₁ h₂ f≤average Z₁ Z₂ h₁ h₂ g :=by
  classical
  apply add_le_add
  · apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (integral_mono (hi v) (hj v) (fun ω=> hfg _ _))
      (Arithmetic.EV v)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun v _=> hfg _ _)
lemma Di {f g:Depth P→ Depth P→ ℝ}
    (hi:AU Z₁ Z₂ f) (hj:AU Z₁ Z₂ g) :
    average Z₁ Z₂ h₁ h₂ (fun d d'=> f d d'+g d d')=
      average Z₁ Z₂ h₁ h₂ f+average Z₁ Z₂ h₁ h₂ g :=by
  classical
  unfold average
  simp only [integral_add (hi _) (hj _),mul_add,Finset.sum_add_distrib]
  ring
lemma FE (f:Depth P→ Depth P→ ℝ) (c:ℝ) :
    average Z₁ Z₂ h₁ h₂ (fun d d'=> c*f d d')=c*average Z₁ Z₂ h₁ h₂ f :=by
  classical
  unfold average
  simp only [integral_const_mul,Finset.mul_sum,mul_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro v _ <;> ring
lemma Iu {J:Type u3} [Fintype J] (f:J→ Depth P→ Depth P→ ℝ)
    (hi:∀ j,AU Z₁ Z₂ (f j)) :
    average Z₁ Z₂ h₁ h₂ (fun d d'=>∑ j,f j d d')=
      ∑ j,average Z₁ Z₂ h₁ h₂ (f j) :=by
  classical
  unfold average
  simp_rw [integral_finsetSum _ (fun j _=> hi j _),Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_comm (s:=Fq Z₁ Z₂ h₁ h₂)]
  simp only [Finset.sum_add_distrib]
lemma Ld (hn:2≤Fintype.card P) (x:P) :
    average Z₁ Z₂ h₁ h₂ (fun d _=> d.Ag x)=S Z₁ h₁ x :=by
  classical
  unfold average S
  congr 2
  exact Fn h₁ hn _ Finset.subset_union_left x
lemma Kw (hn:2≤Fintype.card P) (x:P) :
    average Z₁ Z₂ h₁ h₂ (fun _ d'=> d'.Ag x)=S Z₂ h₂ x :=by
  classical
  unfold average S
  congr 2
  exact Fn h₂ hn _ Finset.subset_union_right x
lemma Jl (hn:2≤Fintype.card P) (C:Finset P) :
    average Z₁ Z₂ h₁ h₂ (fun d _=> d.mass C)=CD Z₁ h₁ C :=by
  classical
  unfold average CD
  congr 2
  exact Hu h₁ hn _ Finset.subset_union_left C
lemma IG (hn:2≤Fintype.card P) (C:Finset P) :
    average Z₁ Z₂ h₁ h₂ (fun _ d'=> d'.mass C)=CD Z₂ h₂ C :=by
  classical
  unfold average CD
  congr 2
  exact Hu h₂ hn _ Finset.subset_union_right C
omit [NumberField K] in
include h₁ in
lemma DY (hn:2≤Fintype.card P) (x:P) :
    AU Z₁ Z₂ (fun d _=> d.Ag x) :=
  fun v=> Depth.Cj (arch Z₁ v) (BA Z₁ h₁ v)
    (AO Z₁ h₁ v) hn x
omit [NumberField K] in
include h₂ in
lemma DU (hn:2≤Fintype.card P) (x:P) :
    AU Z₁ Z₂ (fun _ d'=> d'.Ag x) :=
  fun v=> Depth.Cj (arch Z₂ v) (BA Z₂ h₂ v)
    (AO Z₂ h₂ v) hn x
omit [NumberField K] in
include h₁ in
lemma Dw (hn:2≤Fintype.card P) (C:Finset P) :
    AU Z₁ Z₂ (fun d _=> d.mass C) :=
  fun v=> Depth.Du (arch Z₁ v) (BA Z₁ h₁ v)
    (AO Z₁ h₁ v) hn C
omit [NumberField K] in
include h₂ in
lemma Dn (hn:2≤Fintype.card P) (C:Finset P) :
    AU Z₁ Z₂ (fun _ d'=> d'.mass C) :=
  fun v=> Depth.Du (arch Z₂ v) (BA Z₂ h₂ v)
    (AO Z₂ h₂ v) hn C
end Aa.Bg
namespace Aa.Bg
open Ak MeasureTheory Variance
open scoped BigOperators
variable {P:Type u4} [Fintype P] [DecidableEq P]
variable {K:Type u5} [Field K] [NumberField K]
variable (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
omit Z₁ Z₂ h₁ h₂ in
def Co (p:P→ ℝ) (d d':Depth P):ℝ:=∑ y,p y*(d.Ag y+d'.Ag y)
omit Z₁ Z₂ h₁ h₂ in
def Bm (q:Finset P→ ℝ) (d d':Depth P):ℝ :=
  Ac d.mass q+Ac d'.mass q
omit [NumberField K] in
include h₁ h₂ in
lemma DA (hn:2≤Fintype.card P) (p:P→ ℝ) :
    AU Z₁ Z₂ (Co p):=by
  intro v
  exact integrable_finsetSum (s:=Finset.univ) (fun y _ =>
    ((DY Z₁ Z₂ h₁ hn y v).add
      (DU Z₁ Z₂ h₂ hn y v)).const_mul (p y))
omit [NumberField K] in
include h₁ h₂ in
lemma Cm (hn:2≤Fintype.card P) (q:Finset P→ ℝ) :
    AU Z₁ Z₂ (Bm q):=by
  intro v
  exact (integrable_finsetSum (s:=Finset.univ) (fun C _ =>
      (Dw Z₁ Z₂ h₁ hn C v).mul_const (q C))).add
    (integrable_finsetSum (s:=Finset.univ) (fun C _ =>
      (Dn Z₁ Z₂ h₂ hn C v).mul_const (q C)))
lemma EY (hn:2≤Fintype.card P) (p:P→ ℝ) :
    average Z₁ Z₂ h₁ h₂ (Co p)=∑ y,p y*BB Z₁ Z₂ h₁ h₂ y:=by
  unfold Co
  rw [Iu Z₁ Z₂ h₁ h₂ _ (fun y v =>
    ((DY Z₁ Z₂ h₁ hn y v).add
      (DU Z₁ Z₂ h₂ hn y v)).const_mul (p y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [FE,Di Z₁ Z₂ h₁ h₂
    (DY Z₁ Z₂ h₁ hn y) (DU Z₁ Z₂ h₂ hn y),
    Ld Z₁ Z₂ h₁ h₂ hn,Kw Z₁ Z₂ h₁ h₂ hn]
  rfl
lemma Hc (hn:2≤Fintype.card P) (q:Finset P→ ℝ) :
    average Z₁ Z₂ h₁ h₂ (Bm q)=Ac (totalMass Z₁ Z₂ h₁ h₂) q:=by
  have he:Bm q=(fun d d'=>∑ C,q C*(d.mass C+d'.mass C)):=by
    funext d d'
    simp only [Bm,Ac,mul_add,Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> ring
  rw [he,Iu Z₁ Z₂ h₁ h₂ _ (fun C v =>
    ((Dw Z₁ Z₂ h₁ hn C v).add
      (Dn Z₁ Z₂ h₂ hn C v)).const_mul (q C))]
  apply Finset.sum_congr rfl
  intro C _
  rw [FE,Di Z₁ Z₂ h₁ h₂
    (Dw Z₁ Z₂ h₁ hn C) (Dn Z₁ Z₂ h₂ hn C),
    Jl Z₁ Z₂ h₁ h₂ hn,IG Z₁ Z₂ h₁ h₂ hn]
  simp only [totalMass]; ring
omit Z₁ Z₂ h₁ h₂ in
lemma Sf {I:Type u6} [Fintype I] (w:I→ ℝ) (p:I→ P→ ℝ) (x:I→ P)
    (d d':Depth P) :
    Bm (AL.Cl w p x) d d'=
      ∑ i,w i*∑ y,p i y*(AD d.mass (x i) y+AD d'.mass (x i) y):=by
  have he (m:Finset P→ ℝ):Ac m (AL.Cl w p x)=
      ∑ i,w i*∑ y,p i y*AD m (x i) y:=by
    unfold AL.Cl
    rw [IT]
    unfold AL.Av
    simp only [Finset.sum_mul]
    calc
      _=∑ a,∑ i,∑ y,(if x i=a then w i*p i y else 0)*AD m a y:=by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _=∑ i,∑ a,∑ y,(if x i=a then w i*p i y else 0)*AD m a y:=Finset.sum_comm
      _= _:=by
        simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
        simp [Finset.mul_sum,mul_assoc]
  simp only [Bm,he,mul_add,Finset.sum_add_distrib]
end Aa.Bg
namespace Aa.Bg
open Ak MeasureTheory Variance
open scoped BigOperators
variable {P:Type u7} {I:Type u8} [Fintype P] [DecidableEq P] [Fintype I]
variable {K:Type u9} [Field K] [NumberField K]
variable (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
omit Z₁ Z₂ h₁ h₂ in
lemma LM (w:I→ ℝ) (p:I→ P→ ℝ) (d d':Depth P) :
    Co (fun y=>∑ i,w i*p i y) d d'=∑ i,w i*∑ y,p i y*(d.Ag y+d'.Ag y):=by
  simp only [Co,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm
lemma Te {f g:Depth P→ Depth P→ ℝ}
    (hi:AU Z₁ Z₂ f) (hj:AU Z₁ Z₂ g) :
    average Z₁ Z₂ h₁ h₂ (fun d d'=> f d d'-g d d')=
      average Z₁ Z₂ h₁ h₂ f-average Z₁ Z₂ h₁ h₂ g:=by
  classical
  unfold average
  simp only [integral_sub (hi _) (hj _),mul_sub,Finset.sum_sub_distrib]
  ring
lemma Hb (hn:2≤Fintype.card P)
    (w:I→ ℝ) (B:I→ Finset P) (src:I→ P) (t:I→ K) (T M κ:ℝ)
    (hw:∀ i,0≤w i) (hW:(∑ i,w i)=1) (hT:1≤T) (hκ:0≤κ)
    (hB:∀ i,2≤(B i).card) (hk:∀ i,2/((B i).card:ℝ)≤κ)
    (hsrc:∀ i,src i∉B i)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤M*Ae Finset.univ x)
    (ht:∀ i y,y∈B i→(Z₁ (src i)-Z₁ y)*(Z₂ (src i)-Z₂ y)=t i) :
    (∑ y,(∑ i,w i*Ae (B i) y)*BB Z₁ Z₂ h₁ h₂ y) ≤
      4*Ac (totalMass Z₁ Z₂ h₁ h₂) (Aj w B T)+
      8*AQ Z₁ Z₂ h₁ h₂+
      2*κ*M*AG Z₁ Z₂ h₁ h₂+
      Ac (totalMass Z₁ Z₂ h₁ h₂) (AL.Cl w (fun i=> Ae (B i)) src)+16:=by
  classical
  let p:I→ P→ ℝ:=fun i=> Ae (B i)
  let r:P→ ℝ:=fun y=>∑ i,w i*p i y
  let q:=AL.Cl w p src
  let vcell:=Aj w B T
  let pc:=Ah (Finset.univ:Finset P)
  let unif:=Ae (Finset.univ:Finset P)
  let R:Depth P→ Depth P→ ℝ:=fun d d' =>
    4*Bm vcell d d'+8*Bm pc d d'+2*κ*M*Co unif d d'+Bm q d d'
  let f:Depth P→ Depth P→ ℝ:=fun d d'=> Co r d d'-R d d'
  have hp (i y):0≤p i y:=by dsimp [p,Ae]; split_ifs <;> positivity
  have hp1 (i):∑ y,p i y=1:=Bs (B i) (Finset.card_pos.mp (by have:=hB i; omega))
  have hx (i):p i (src i)=0:=by simp [p,Ae,hsrc i]
  have ht' (i y) (hy:p i y≠0):(Z₁ (src i)-Z₁ y)*(Z₂ (src i)-Z₂ y)=t i:=by
    apply ht i y
    by_contra hn'; exact hy (by simp [p,Ae,hn'])
  have hL:=DA Z₁ Z₂ h₁ h₂ hn r
  have hV:=Cm Z₁ Z₂ h₁ h₂ hn vcell
  have hP:=Cm Z₁ Z₂ h₁ h₂ hn pc
  have hA:=DA Z₁ Z₂ h₁ h₂ hn unif
  have hQ:=Cm Z₁ Z₂ h₁ h₂ hn q
  have hR:AU Z₁ Z₂ R:=fun v =>
    ((((hV v).const_mul 4).add ((hP v).const_mul 8)).add ((hA v).const_mul (2*κ*M))).add (hQ v)
  have hf:AU Z₁ Z₂ f:=fun v=>(hL v).sub (hR v)
  have hb (d d':Depth P) (a:I→ ℝ) :
      f d d'≤∑ i,w i*∑ y,p i y*|d.value (src i) y+d'.value (src i) y-a i| := by
    have hh:=d.IC d' hn w B src a T M κ hw hW.le hT hκ hB hk hsrc hdom
    rw [← LM,← Sf] at hh
    change Co r d d'≤R d d'+_ at hh
    exact sub_le_iff_le_add'.mpr hh
  have ha (v:NumberField.InfinitePlace K) :
      (∫ ω,f (arch Z₁ v ω) (arch Z₂ v ω) ∂Ao.As)≤16:=by
    let E:Ao.AS→ ℝ:=fun ω=>∑ i,w i*∑ y,p i y*
      |(arch Z₁ v ω).value (src i) y+(arch Z₂ v ω).value (src i) y+Real.log (v (t i))|
    have hi:Integrable E Ao.As:=integrable_finsetSum (s:=Finset.univ) (fun i _ =>
      (integrable_finsetSum (s:=Finset.univ) (fun y _ =>
        ((((AO Z₁ h₁ v _ _).add (AO Z₂ h₂ v _ _)).add
          (integrable_const _)).abs.const_mul (p i y)))).const_mul (w i))
    have hu:(∫ ω,E ω ∂Ao.As)≤16:=by
      simpa only [E,sub_zero,max_eq_left (abs_nonneg (_:ℝ)),neg_zero,zero_div,Real.exp_zero,mul_one]
        using Hw Z₁ Z₂ h₁ h₂ v w p src t hw hW hp hp1 hx ht' 0 (by norm_num)
    exact (integral_mono (hf v) hi (fun ω=> by
      simpa only [sub_neg_eq_add] using hb (arch Z₁ v ω) (arch Z₂ v ω) (fun i => -Real.log (v (t i))))).trans hu
  have hv (v:NumberField.FinitePlace K):f (finite Z₁ h₁ v) (finite Z₂ h₂ v)≤0:=by
    have he (i y):p i y*|(finite Z₁ h₁ v).value (src i) y+
        (finite Z₂ h₂ v).value (src i) y-(-Real.log (v (t i)))|=0:=by
      by_cases hy:p i y=0
      · simp [hy]
      · have hxy:src i≠y:=by intro hh; exact hsrc i (hh ▸ (by
          by_contra hm; exact hy (by simp [p,Ae,hm])))
        have hh:=Arithmetic.Gk v.val (Z₁ (src i)-Z₁ y) (Z₂ (src i)-Z₂ y)
          (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
        rw [ht' i y hy] at hh
        change -Real.log (v (Z₁ (src i)-Z₁ y)) + -Real.log (v (Z₂ (src i)-Z₂ y)) = -Real.log (v (t i)) at hh
        simp only [finite,if_neg hxy,hh,sub_self,abs_zero,mul_zero]
    simpa only [he,Finset.sum_const_zero,mul_zero] using
      hb (finite Z₁ h₁ v) (finite Z₂ h₂ v) (fun i => -Real.log (v (t i)))
  have hg:average Z₁ Z₂ h₁ h₂ f≤16:=by
    change BH (Fq Z₁ Z₂ h₁ h₂) _ _≤16
    have hh:=Gz (Fq Z₁ Z₂ h₁ h₂) ha (fun v _=> hv v)
    rwa [Ev] at hh
  have hRe:average Z₁ Z₂ h₁ h₂ R =
      4*Ac (totalMass Z₁ Z₂ h₁ h₂) vcell+
      8*Ac (totalMass Z₁ Z₂ h₁ h₂) pc+
      2*κ*M*(∑ y,unif y*BB Z₁ Z₂ h₁ h₂ y)+
      Ac (totalMass Z₁ Z₂ h₁ h₂) q:=by
    unfold R
    rw [Di Z₁ Z₂ h₁ h₂ (fun v=>(((hV v).const_mul 4).add ((hP v).const_mul 8)).add ((hA v).const_mul (2*κ*M))) hQ,
      Di Z₁ Z₂ h₁ h₂ (fun v=>((hV v).const_mul 4).add ((hP v).const_mul 8)) (fun v=>(hA v).const_mul (2*κ*M)),
      Di Z₁ Z₂ h₁ h₂ (fun v=>(hV v).const_mul 4) (fun v=>(hP v).const_mul 8)]
    simp only [FE,Hc Z₁ Z₂ h₁ h₂ hn,EY Z₁ Z₂ h₁ h₂ hn]
  change average Z₁ Z₂ h₁ h₂ (fun d d'=> Co r d d'-R d d')≤16 at hg
  rw [Te Z₁ Z₂ h₁ h₂ hL hR,EY Z₁ Z₂ h₁ h₂ hn,hRe] at hg
  exact sub_le_iff_le_add'.mp hg
end Aa.Bg
namespace Aa.Variance
open scoped BigOperators
variable {P:Type u10} [Fintype P] [DecidableEq P]
lemma Mc (m:Finset P→ ℝ) (b:ℝ) (S:P→ ℝ)
    (hm:∀ C:Finset P,(0:ℝ)≤ m C) (hL:∀ x y,x≠y→ AD m x y=b+S x+S y)
    (hn:3≤Fintype.card P) (x:P) :
    (∑ y,Ae Finset.univ y*S y)-2*Ac m (Ah Finset.univ)≤S x:=by
  let n:ℝ:=Fintype.card P
  have hn3:3≤n:=by dsimp [n]; exact_mod_cast hn
  have hn0:n≠0:=by linarith
  let A:ℝ:=(∑ y,Ae Finset.univ y*S y)
  let W:ℝ:=Ac m (Ah Finset.univ)
  have hW:0≤W:=Finset.sum_nonneg (fun C _=> mul_nonneg (hm C) (BJ _ _))
  have hu:W=b+2*A:=JU m b S hL (by omega)
  have hs:(∑ y,S y)=n*A:=by
    dsimp [A,Ae,n]
    simp only [Finset.mem_univ,ite_true]
    rw [← Finset.mul_sum]
    have hn0':(Fintype.card P:ℝ)≠0:=hn0
    field_simp
  have hnn:0≤∑ y∈ Finset.univ.erase x,(b+S x+S y):=by
    apply Finset.sum_nonneg
    intro y hy
    rw [← hL x y (Finset.ne_of_mem_erase hy).symm]
    exact Finset.sum_nonneg (fun C _=> mul_nonneg (hm C) (by dsimp; split_ifs <;> norm_num))
  have hsx:(∑ y∈ Finset.univ.erase x,S y)=(∑ y,S y)-S x:=by
    exact eq_sub_of_add_eq (Finset.sum_erase_add Finset.univ S (Finset.mem_univ x))
  have hcount:((Finset.univ.erase x).card:ℝ)=n-1:=by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,Nat.cast_sub (by omega),Nat.cast_one]
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hcount,hsx,hs] at hnn
  change A-2*W≤S x
  nlinarith [mul_nonneg (by linarith:0≤n-3) hW]
end Aa.Variance
namespace Aa
open Bg Variance
open scoped BigOperators
variable {P:Type u11} {I:Type u12} [Fintype P] [Fintype I] [DecidableEq P]
variable {K:Type u13} [Field K] [NumberField K]
theorem JK (G:Core.Au P I)
    (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
    (hn:3≤Fintype.card P) (hG:0<G.Ap)
    (T M κ:ℝ) (hT:1≤T) (hκ:0≤κ)
    (hB:∀ i,2≤(G.targets i).card) (hk:∀ i,2/((G.targets i).card:ℝ)≤κ)
    (hdom:∀ x y,G.Av x y≤M*Az Finset.univ x y)
    (t:I→ K) (ht:∀ i y,y∈G.targets i →
      (Z₁ (G.source i)-Z₁ y)*(Z₂ (G.source i)-Z₂ y)=t i) :
    (1-2*κ*M)*AG Z₁ Z₂ h₁ h₂ ≤
      4*Ac (totalMass Z₁ Z₂ h₁ h₂) (Aj G.Af G.targets T)+
      (10+M)*AQ Z₁ Z₂ h₁ h₂+16:=by
  have hn2:2≤Fintype.card P:=by omega
  have hh:=Hb Z₁ Z₂ h₁ h₂ hn2 G.Af G.targets G.source t T M κ
    G.AT (G.Bz hG) hT hκ hB hk G.OE
    (G.Fm M hdom hn2) ht
  let m:=totalMass Z₁ Z₂ h₁ h₂
  let S:=BB Z₁ Z₂ h₁ h₂
  let r:P→ ℝ:=fun y=>∑ i,G.Af i*Ae (G.targets i) y
  have hr0 (y):0≤r y:=by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (G.AT i)
    unfold Ae; split_ifs <;> positivity
  have hr1:∑ y,r y=1:=by
    dsimp [r]
    rw [Finset.sum_comm]
    have hp1 (i:I):∑ y,Ae (G.targets i) y=1 :=
      Bs (G.targets i) (Finset.card_pos.mp (by have:=hB i; omega))
    simp_rw [← Finset.mul_sum,hp1,mul_one]
    exact G.Bz hG
  have hl:AG Z₁ Z₂ h₁ h₂-2*AQ Z₁ Z₂ h₁ h₂≤∑ y,r y*S y:=by
    have hlo (y):=Mc m (Gn Z₁ Z₂ h₁ h₂) S
      (Bi Z₁ Z₂ h₁ h₂) (EW Z₁ Z₂ h₁ h₂ hn2) hn y
    have hu:=Finset.sum_le_sum (s:=Finset.univ) (fun y _=> mul_le_mul_of_nonneg_left (hlo y) (hr0 y))
    simpa only [← Finset.sum_mul,hr1,one_mul,AG,AQ,m,S] using hu
  have he:AL.Cl G.Af (fun i=> Ae (G.targets i)) G.source=G.FL:=by
    funext C; exact (G.Pn C).symm
  have hq:Ac m G.FL≤M*AQ Z₁ Z₂ h₁ h₂:=by
    simp only [Ac,Finset.mul_sum,AQ]
    calc
      _≤∑ C,m C*(M*Ah Finset.univ C):=Finset.sum_le_sum (fun C _ =>
        mul_le_mul_of_nonneg_left (G.Tg hdom C) (Bi Z₁ Z₂ h₁ h₂ C))
      _= _:=by apply Finset.sum_congr rfl; intro C _; dsimp [m]; ring
  rw [he] at hh
  change (∑ y,r y*S y)≤_ at hh
  change Ac (totalMass Z₁ Z₂ h₁ h₂) G.FL≤_ at hq
  nlinarith
end Aa
namespace Aa
open Filter
open scoped Topology
lemma Oj (W A V δ:ℕ→ ℝ) (B:ℝ) (hB:0≤B)
    (hW:∀ j,0≤W j) (hA:∀ j,0≤A j)
    (hδ:Tendsto δ atTop (𝓝 0))
    (hV:Tendsto (fun j=> V j/(W j+A j+1)) atTop (𝓝 0))
    (hbal:∀ᶠ j in atTop,(1-δ j)*A j≤4*V j+(10+B)*W j+16) :
    ∀ᶠ j in atTop,A j≤(64+4*B)*(W j+1):=by
  filter_upwards [hbal,hδ.eventually (eventually_lt_nhds (by norm_num:(0:ℝ)<1/4)),
    hV.eventually (eventually_lt_nhds (by norm_num:(0:ℝ)<1/16))] with j hb hd hv
  have hden:0<W j+A j+1:=by linarith [hW j,hA j]
  have hv':=(div_lt_iff₀ hden).mp hv
  nlinarith [hW j,hA j,mul_nonneg (hW j) hB]
end Aa
namespace Aa
open Bg Variance Filter
open scoped Topology BigOperators
variable {V:ℕ→ Type u14} {I:ℕ→ Type u15} {K:ℕ→ Type u16} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]
variable (G:∀ j,Core.Au (V j) (I j)) (θ γ c:ℝ) (η:ℕ→ ℝ)
  (Z₁ Z₂:∀ j,V j→ K j) (h₁:∀ j,Function.Injective (Z₁ j)) (h₂:∀ j,Function.Injective (Z₂ j))
theorem ID (hθ:0<θ) (hγ:0<γ) (hγ1:γ<1) (hcγ:c<γ)
    (hn:Tendsto (fun j=>(Fintype.card (V j):ℝ)) atTop atTop)
    (hη:Tendsto η atTop (𝓝 0)) (hη0:∀ j,0≤η j) (hηb:∀ j,η j≤θ/2)
    (hG:∀ j,AJ (V j) (I j) (G j) θ γ c (η j))
    (t:∀ j,I j→ K j) (ht:∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    ∀ᶠ j in atTop,AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) ≤
      (64+8/θ)*(AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1):=by
  let n:ℕ→ ℝ:=fun j=> Fintype.card (V j)
  let κ:ℕ→ ℝ:=fun j=>2/(n j)^γ
  have hnγ:Tendsto (fun j=>(n j)^γ) atTop atTop:=(tendsto_rpow_atTop hγ).comp hn
  have hκ:Tendsto κ atTop (𝓝 0):=by
    simpa only [κ,div_eq_mul_inv,mul_zero,Function.comp_def] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnγ)
  have hv:=(DG G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht).1
  have hs:=Oj
    (fun j=> AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
    (fun j=> AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
    (Ew G c Z₁ Z₂ h₁ h₂) (fun j=>2*κ j*(2/θ)) (2/θ) (by positivity)
    (fun j=> BK _ _ _ _) (fun j=> Bu _ _ _ _)
    (by simpa using (tendsto_const_nhds.mul hκ).mul_const (2/θ)) hv
  have hb:∀ᶠ j in atTop,
      (1-2*κ j*(2/θ))*AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) ≤
      4*Ew G c Z₁ Z₂ h₁ h₂ j+(10+2/θ)*AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+16:=by
    filter_upwards [hn.eventually (eventually_ge_atTop (3:ℝ)),hnγ.eventually (eventually_ge_atTop (2:ℝ))] with j hj hjγ
    have hn3:3≤Fintype.card (V j):=by exact_mod_cast hj
    have hne:0<(G j).Ap:=(hG j).CR (by linarith [hηb j])
    have hn0:0<n j:=by change (0:ℝ)<Fintype.card (V j); linarith
    have hBk (i):(n j)^γ≤((G j).targets i).card:=(hG j).fiber i |>.le
    have hBk2 (i):2≤((G j).targets i).card:=by exact_mod_cast hjγ.trans (hBk i)
    have hk (i):2/(((G j).targets i).card:ℝ)≤κ j :=
      div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hn0 _) (hBk i)
    have hT:1≤(n j)^(1-c):=Real.one_le_rpow (by linarith) (by linarith)
    exact JK (G j) (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) hn3 hne
      ((n j)^(1-c)) (2/θ) (κ j) hT (by dsimp [κ]; positivity) hBk2 hk
      ((hG j).Gl hθ (hηb j)) (t j) (ht j)
  have hh:=hs hb
  convert hh using 1; ring_nf
end Aa
end
end
end
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Aa.AV
open scoped BigOperators
def Be (δ u:ℝ):ℝ:=max 0 (min (u-δ) (1-δ-u))
lemma Dv (δ u:ℝ):0≤Be δ u:=le_max_left _ _
lemma IN (δ u:ℝ):Be δ (1-u)=Be δ u:=by
  unfold Be
  rw [show 1-u-δ=1-δ-u by ring,show 1-δ-(1-u)=u-δ by ring,min_comm]
lemma BX {δ u:ℝ} (hu:u≤δ):Be δ u=0:=by
  unfold Be
  exact max_eq_left ((min_le_left _ _).trans (sub_nonpos.mpr hu))
lemma DR {δ u:ℝ} (hu:1-δ≤u):Be δ u=0:=by
  rw [← IN]
  exact BX (by linarith)
lemma Pj {δ u:ℝ} (hδ:0≤δ) (hu:u≤1):Be δ u≤1:=by
  exact max_le (by norm_num) ((min_le_left _ _).trans (by linarith))
lemma Mf (δ u v:ℝ) : |Be δ u-Be δ v|≤|u-v| := by
  have hm:=abs_max_sub_max_le_max (0:ℝ) (min (u-δ) (1-δ-u)) 0 (min (v-δ) (1-δ-v))
  have hn:=abs_min_sub_min_le_max (u-δ) (1-δ-u) (v-δ) (1-δ-v)
  have he:1-δ-u-(1-δ-v)=-(u-v):=by ring
  have hf:u-δ-(v-δ)=u-v:=by ring
  simp only [he,hf,abs_neg,max_self] at hn
  exact hm.trans (max_le (by simp [abs_nonneg]) hn)
lemma MI {δ u:ℝ} (hu:0<Be δ u):δ<u∧ u<1-δ:=by
  have h:0< min (u-δ) (1-δ-u):=(lt_max_iff.mp hu).resolve_left (lt_irrefl _)
  have:=lt_min_iff.mp h
  constructor <;> linarith
lemma Tq {δ u:ℝ} (hu:2*δ≤u) (hu':u≤1-2*δ):δ≤Be δ u:=by
  exact le_max_iff.mpr (Or.inr (le_min (by linarith) (by linarith)))
def Ck (δ p a:ℝ):ℝ := |Be δ p-Be δ a|+Be δ a*|p-a|
lemma Hl (δ p a:ℝ):0≤Ck δ p a :=
  add_nonneg (abs_nonneg _) (mul_nonneg (Dv _ _) (abs_nonneg _))
lemma Sp (δ p a:ℝ):Ck δ (1-p) (1-a)=Ck δ p a:=by
  simp only [Ck,IN,show 1-p-(1-a)=-(p-a) by ring,abs_neg]
lemma SZ {δ p a:ℝ} (hδ:0≤δ) (ha:a≤1):Ck δ p a≤2*|p-a| := by
  have:=Mf δ p a
  have:=mul_le_mul_of_nonneg_right (Pj hδ ha) (abs_nonneg (p-a))
  unfold Ck
  linarith
lemma Ri {δ p a ε:ℝ} (hδ:0≤δ) (ha:a≤1) (hε:0<ε) :
    Ck δ p a≤ε+(p-a)^2/ε:=by
  apply (SZ hδ ha).trans
  apply (mul_le_mul_iff_left₀ hε).mp
  have he:(ε+(p-a)^2/ε)*ε=ε^2+(p-a)^2:=by field_simp
  rw [he]
  nlinarith [sq_nonneg (|p-a|-ε),sq_abs (p-a)]
lemma MK {δ p a:ℝ} (hδ:0<δ) (ha:a<δ/2) (hp:p≤1) :
    Ck δ p a≤(4/δ^2)*(p-a)^2∧ Ck δ p a≤(4/δ^2)*(p^2/2):=by
  have hz:Be δ a=0:=BX (by linarith)
  rw [Ck,hz,sub_zero,abs_of_nonneg (Dv _ _),zero_mul,add_zero]
  by_cases hh:Be δ p=0
  · rw [hh]; constructor <;> positivity
  · have ht:0<Be δ p:=lt_of_le_of_ne (Dv _ _) (Ne.symm hh)
    have hpd:=(MI ht).1
    have ht1:=Pj hδ.le hp
    have hd2:0<δ^2:=sq_pos_of_pos hδ
    constructor
    · apply ht1.trans
      apply (mul_le_mul_iff_left₀ hd2).mp
      have he:((4/δ^2)*(p-a)^2)*δ^2=4*(p-a)^2:=by field_simp
      rw [he]
      nlinarith [sq_nonneg (p-a-δ/2),mul_nonneg (by linarith:0≤p-a-δ/2) hδ.le]
    · apply ht1.trans
      apply (mul_le_mul_iff_left₀ hd2).mp
      have he:((4/δ^2)*(p^2/2))*δ^2=2*p^2:=by field_simp; ring
      rw [he]
      nlinarith [sq_nonneg (p-δ),mul_nonneg (by linarith:0≤p-δ) hδ.le]
end Aa.AV
namespace Aa.Variance
open scoped BigOperators
open AV
variable {P:Type u1} {I:Type u2} [Fintype P] [Fintype I] [DecidableEq P]
noncomputable def Bl (w:I→ ℝ) (B:I→ Finset P) (δ:ℝ) (C:Finset P):ℝ :=
  ∑ i,w i*Ck δ (Ad (B i) C) (Ad Finset.univ C)
lemma ME (w:I→ ℝ) (B:I→ Finset P) (T δ ε:ℝ)
    (hw:∀ i,0≤w i) (hW:(∑ i,w i)≤1) (hδ:0<δ) (hε:0<ε)
    (hk:∀ i,2/((B i).card:ℝ)≤δ) (C:Finset P)
    (hlarge:δ/2≤Ad Finset.univ C→ T<C.card)
    (hpair:δ/2≤Ad Finset.univ C→1≤(8/δ^2)*Ah Finset.univ C) :
    Bl w B δ C≤(8*ε/δ^2)*Ah Finset.univ C+
      (1/ε+4/δ^2)*Aj w B T C:=by
  have hv:0≤Aj w B T C:=Bw w B T hw C
  by_cases ha:δ/2≤Ad Finset.univ C
  · have he:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (Ri (p:=Ad (B i) C) hδ.le (Dy (Finset.univ:Finset P) C) hε) (hw i))
    change Bl w B δ C≤_ at he
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,← mul_div_assoc,← Finset.sum_div] at he
    have hvf:Aj w B T C=∑ i,w i*(Ad (B i) C-Ad Finset.univ C)^2:=by
      simp only [Aj,if_pos (hlarge ha)]
    rw [← hvf] at he
    have he2:(∑ i,w i)*ε≤ε:=by nlinarith
    have he3:ε≤(8*ε/δ^2)*Ah Finset.univ C:=by
      have hh:=mul_le_mul_of_nonneg_left (hpair ha) hε.le
      calc
        ε= ε*1:=by ring
        _≤ ε*((8/δ^2)*Ah Finset.univ C):=hh
        _= _:=by ring
    have hx:0≤(4/δ^2)*Aj w B T C:=mul_nonneg (by positivity) hv
    have hh:Aj w B T C/ε=(1/ε)*Aj w B T C:=by ring
    rw [hh] at he
    nlinarith
  · have hat:Ad Finset.univ C<δ/2:=lt_of_not_ge ha
    have hb:Bl w B δ C≤(4/δ^2)*Aj w B T C:=by
      unfold Bl Aj
      split_ifs with hl
      · rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hh:=(MK hδ hat (Dy (B i) C)).1
        have hm:=mul_le_mul_of_nonneg_left hh (hw i)
        convert hm using 1; ring
      · simp only [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        by_cases hpk:2/((B i).card:ℝ)≤Ad (B i) C
        · rw [if_pos hpk]
          have hh:=(MK hδ hat (Dy (B i) C)).2
          have hm:=mul_le_mul_of_nonneg_left hh (hw i)
          convert hm using 1; ring
        · rw [if_neg hpk]
          have hp:Ad (B i) C≤δ:=(le_of_lt (lt_of_not_ge hpk)).trans (hk i)
          simp only [Ck,BX hp,BX (show Ad Finset.univ C≤δ by linarith),
            sub_self,abs_zero,zero_mul,add_zero,mul_zero]
          norm_num
    have hx:0≤(8*ε/δ^2)*Ah Finset.univ C:=mul_nonneg (by positivity) (BJ _ _)
    have hy:0≤(1/ε)*Aj w B T C:=mul_nonneg (by positivity) hv
    nlinarith
end Aa.Variance
namespace Aa.Variance
open scoped BigOperators
variable {P:Type u3} {I:Type u4} [Fintype P] [Fintype I] [DecidableEq P]
lemma Og (δ:ℝ) (hδ:0<δ) (hn:4≤δ*(Fintype.card P:ℝ))
    (C:Finset P) (ha:δ/2≤Ad Finset.univ C):2≤C.card:=by
  have hn0:(0:ℝ)<Fintype.card P:=by
    by_contra! h
    have:=mul_nonpos_of_nonneg_of_nonpos hδ.le h
    linarith
  simp only [Ad,Finset.univ_inter,Finset.card_univ] at ha
  have hh:=(le_div_iff₀ hn0).mp ha
  exact_mod_cast (show (2:ℝ)≤C.card by nlinarith)
lemma OB (δ:ℝ) (hδ:0<δ) (hn:4≤δ*(Fintype.card P:ℝ))
    (C:Finset P) (ha:δ/2≤Ad Finset.univ C) :
    1≤(8/δ^2)*Ah Finset.univ C:=by
  have hpair:=(Cw C (Og δ hδ hn C ha)).1
  have han:=Bd (Finset.univ:Finset P) C
  have hh:δ^2≤8*Ah Finset.univ C:=by nlinarith
  have he:(8/δ^2)*Ah Finset.univ C=(8*Ah Finset.univ C)/δ^2:=by ring
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by simpa using hh)
lemma Jd (m:Finset P→ ℝ) (hm:∀ C,0≤ m C)
    (w:I→ ℝ) (B:I→ Finset P) (T δ ε:ℝ)
    (hw:∀ i,0≤w i) (hW:(∑ i,w i)≤1) (hδ:0<δ) (hε:0<ε)
    (hn:4≤δ*(Fintype.card P:ℝ)) (hT:T<δ*(Fintype.card P:ℝ)/2)
    (hk:∀ i,2/((B i).card:ℝ)≤δ) :
    Ac m (Bl w B δ)≤
      (8*ε/δ^2)*Ac m (Ah Finset.univ)+
      (1/ε+4/δ^2)*Ac m (Aj w B T):=by
  have hn0:(0:ℝ)<Fintype.card P:=by
    by_contra! h
    have:=mul_nonpos_of_nonneg_of_nonpos hδ.le h
    linarith
  have hpoint (C:Finset P):=ME w B T δ ε hw hW hδ hε hk C
    (fun ha=> by
      simp only [Ad,Finset.univ_inter,Finset.card_univ] at ha
      have hh:=(le_div_iff₀ hn0).mp ha
      linarith) (OB δ hδ hn C)
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun C _ =>
    mul_le_mul_of_nonneg_left (hpoint C) (hm C))
  change Ac m (Bl w B δ)≤_ at hh
  convert hh using 1
  simp only [Ac,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> ring
end Aa.Variance
namespace Aa
open Filter
open scoped Topology
lemma Lc (E V W D:ℕ→ ℝ) (δ K:ℝ) (hδ:0<δ) (hK:0<K)
    (hE:∀ j,0≤E j) (hD:∀ j,0<D j)
    (hW:∀ᶠ j in atTop,W j≤K*D j)
    (hV:Tendsto (fun j=> V j/D j) atTop (𝓝 0))
    (hb:∀ ε:ℝ,0<ε→∀ᶠ j in atTop,
      E j≤(8*ε/δ^2)*W j+(1/ε+4/δ^2)*V j) :
    Tendsto (fun j=> E j/D j) atTop (𝓝 0):=by
  apply Metric.tendsto_atTop.mpr
  intro ζ hζ
  let ε:ℝ:=ζ*δ^2/(32*K)
  have hε:0<ε:=by dsimp [ε]; positivity
  have heq:(8*ε/δ^2)*K=ζ/4:=by dsimp [ε]; field_simp; ring
  have hc:0<1/ε+4/δ^2:=by positivity
  have hh:∀ᶠ j in atTop,|(1/ε+4/δ^2)*(V j/D j)|<ζ/2:=by
    have hh0:Tendsto (fun j=>(1/ε+4/δ^2)*(V j/D j)) atTop (𝓝 0):=by
      simpa only [mul_zero] using hV.const_mul (1/ε+4/δ^2)
    exact (hh0.eventually (Metric.ball_mem_nhds (0:ℝ) (half_pos hζ))).mono
      (fun j hj=> by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hj)
  have hh':∀ᶠ j in atTop,|E j/D j-0|<ζ:=by
    filter_upwards [hb ε hε,hW,hh] with j hj hjw hjv
    have hn:=div_nonneg (hE j) (hD j).le
    rw [sub_zero,abs_of_nonneg hn]
    have hp:=mul_le_mul_of_nonneg_left hjw (show 0≤8*ε/δ^2 by positivity)
    have hle:E j/D j≤(8*ε/δ^2)*K+(1/ε+4/δ^2)*(V j/D j):=by
      apply (div_le_iff₀ (hD j)).mpr
      have he:((8*ε/δ^2)*K+(1/ε+4/δ^2)*(V j/D j))*D j =
        (8*ε/δ^2)*(K*D j)+(1/ε+4/δ^2)*V j:=by field_simp [ne_of_gt (hD j)]
      rw [he]
      linarith
    rw [heq] at hle
    have:=(le_abs_self _).trans_lt hjv
    linarith
  obtain ⟨N,hN⟩:=eventually_atTop.mp hh'
  exact ⟨N,fun j hj=> by simpa only [Real.dist_eq] using hN j hj⟩
end Aa
namespace Aa
open Filter Variance Bg
open scoped Topology BigOperators
variable {P:ℕ→ Type u5} {I:ℕ→ Type u6} [∀ j,Fintype (P j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (P j)]
lemma HL (m:∀ j,Finset (P j)→ ℝ) (hm:∀ j C,0≤ m j C)
    (w:∀ j,I j→ ℝ) (B:∀ j,I j→ Finset (P j)) (D:ℕ→ ℝ) (γ c δ:ℝ)
    (hD:∀ j,0<D j) (hδ:0<δ) (hγ:0<γ) (hc:0<c)
    (hn:Tendsto (fun j=>(Fintype.card (P j):ℝ)) atTop atTop)
    (hw:∀ j i,0≤w j i) (hW:∀ j,(∑ i,w j i)≤1)
    (hsize:∀ j i,(Fintype.card (P j):ℝ)^γ≤((B j i).card:ℝ))
    (hWD:∀ j,Ac (m j) (Ah Finset.univ)≤D j)
    (hV:Tendsto (fun j=> Ac (m j)
      (Aj (w j) (B j) ((Fintype.card (P j):ℝ)^(1-c)))/D j) atTop (𝓝 0)) :
    Tendsto (fun j=> Ac (m j) (Bl (w j) (B j) δ)/D j) atTop (𝓝 0):=by
  let n:=fun j=>(Fintype.card (P j):ℝ)
  have hnγ:Tendsto (fun j=> n j^γ) atTop atTop:=(tendsto_rpow_atTop hγ).comp hn
  have hnc:Tendsto (fun j=> n j^(-c)) atTop (𝓝 0):=(tendsto_rpow_neg_atTop hc).comp hn
  apply Lc _ _ (fun j=> Ac (m j) (Ah Finset.univ)) D δ 1 hδ (by norm_num)
    (fun j=> Finset.sum_nonneg (fun C _=> mul_nonneg (hm j C)
      (Finset.sum_nonneg (fun i _=> mul_nonneg (hw j i) (AV.Hl _ _ _))))) hD
    (Eventually.of_forall (fun j=> by simpa using hWD j)) hV
  intro ε hε
  filter_upwards [hn.eventually (eventually_gt_atTop (4/δ)),
    hnγ.eventually (eventually_ge_atTop (2/δ)),hnc.eventually (gt_mem_nhds (half_pos hδ))] with j hj hjγ hjc
  have hn0:0<n j:=(by positivity:0<4/δ).trans hj
  have hnj:4≤δ*n j:=by
    have hh:=(div_lt_iff₀ hδ).mp hj
    nlinarith
  have hT:n j^(1-c)<δ*n j/2:=by
    rw [sub_eq_add_neg,Real.rpow_add hn0,Real.rpow_one]
    nlinarith
  have hk (i):2/((B j i).card:ℝ)≤δ:=by
    have hbs:0<((B j i).card:ℝ):=(Real.rpow_pos_of_pos hn0 γ).trans_le (hsize j i)
    apply (div_le_iff₀ hbs).mpr
    have hh:=(div_le_iff₀ hδ).mp (hjγ.trans (hsize j i))
    nlinarith
  exact Jd (m j) (hm j) (w j) (B j) (n j^(1-c)) δ ε
    (hw j) (hW j) hδ hε hnj hT hk
end Aa
namespace Aa
open Filter Variance Bg
open scoped Topology BigOperators
variable {V:ℕ→ Type u7} {I:ℕ→ Type u8} {K:ℕ→ Type u9} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]
variable (G:∀ j,Core.Au (V j) (I j)) (θ γ c:ℝ) (η:ℕ→ ℝ)
  (Z₁ Z₂:∀ j,V j→ K j) (h₁:∀ j,Function.Injective (Z₁ j)) (h₂:∀ j,Function.Injective (Z₂ j))
theorem GY (δ:ℝ) (hδ:0<δ) (hθ:0<θ)
    (hγ:0<γ) (hγ1:γ<1) (hc:0<c) (hcγ:c<γ)
    (hn:Tendsto (fun j=>(Fintype.card (V j):ℝ)) atTop atTop)
    (hη:Tendsto η atTop (𝓝 0)) (hη0:∀ j,0≤η j) (hηb:∀ j,η j≤θ/2)
    (hG:∀ j,AJ (V j) (I j) (G j) θ γ c (η j))
    (t:∀ j,I j→ K j) (ht:∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    Tendsto (fun j=> Ac (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
        (Bl (G j).Af (G j).targets δ)/
      (AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) ∧
    Tendsto (fun j=> Ac (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
        (Bl ((G j).Ay ((Fintype.card (V j):ℝ)^γ))
          ((G j).Aw ((Fintype.card (V j):ℝ)^γ)) δ)/
      (AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0):=by
  have hv:=DG G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht
  let m:=fun j=> totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let D:=fun j=> AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1
  have hD (j):0<D j:=by dsimp [D]; linarith [BK (Z₁ j) (Z₂ j) (h₁ j) (h₂ j),Bu (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)]
  have hWD (j):Ac (m j) (Ah Finset.univ)≤D j:=by
    change AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)≤_
    dsimp [D]
    linarith [Bu (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)]
  have hpos (j):0<(G j).Ap:=(hG j).CR (by linarith [hηb j])
  constructor
  · exact HL m (fun j=> Bi _ _ _ _)
      (fun j=>(G j).Af) (fun j=>(G j).targets) D γ c δ hD hδ hγ hc hn
      (fun j=>(G j).AT) (fun j=>((G j).Bz (hpos j)).le)
      (fun j i=>((hG j).fiber i).le) hWD hv.1
  · apply HL m (fun j=> Bi _ _ _ _)
      (fun j=>(G j).Ay ((Fintype.card (V j):ℝ)^γ))
      (fun j=>(G j).Aw ((Fintype.card (V j):ℝ)^γ)) D γ c δ hD hδ hγ hc hn
      (fun j=>(G j).Dp _) (fun j=>(G j).Ge _ (hpos j)) _ hWD hv.2
    intro j y
    apply (G j).Ft
    have hn1:(1:ℝ)≤Fintype.card (V j):=by exact_mod_cast (by have:=(hG j).Cz; omega:1≤Fintype.card (V j))
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hγ1.le
end Aa
end
end
end
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators
namespace Aa.AV
variable {P:Type u1} [Fintype P] [DecidableEq P]
def Ef (s:Finset (Finset P)):Prop :=
  ∀ A∈ s,∀ B∈ s,A⊆ B∨ B⊆ A∨ Disjoint A B
def value (s:Finset (Finset P)) (d:Finset P→ ℝ) (a:ℝ) (x:P):ℝ :=
  a+∑ C∈ s,if x∈ C then d C else 0
def mass (b:P→ ℝ) (C:Finset P):ℝ:=∑ x∈ C,b x
omit [Fintype P] in
lemma Sj {s:Finset (Finset P)} (hs:Ef s) (C:Finset P):Ef (s.erase C) :=
  fun _ hA _ hB=> hs _ (Finset.mem_of_mem_erase hA) _ (Finset.mem_of_mem_erase hB)
omit [Fintype P] in
lemma Pq {s:Finset (Finset P)} (hs:Ef s)
    (C:Finset P) (hC:C∈ s) (hmin:∀ D∈ s,C.card≤ D.card)
    (d:Finset P→ ℝ) (a:ℝ) :
    ∀ x∈ C,value (s.erase C) d a x= a+∑ D∈ s.erase C,if C⊆ D then d D else 0:=by
  intro x hx
  unfold value
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  have hDs:=Finset.mem_of_mem_erase hD
  have hDC:D≠ C:=(Finset.mem_erase.mp hD).1
  have hnot:¬D⊆ C:=by
    intro hh
    exact hDC (Finset.eq_of_subset_of_card_le hh (hmin D hDs))
  by_cases hCD:C⊆ D
  · simp [hCD,hCD hx]
  · have hd:Disjoint C D:=(hs C hC D hDs).resolve_left hCD |>.resolve_left hnot
    have hxD:x∉ D:=fun hxD=> Finset.disjoint_left.mp hd hx hxD
    simp [hCD,hxD]
omit [Fintype P] in
lemma Ta {s:Finset (Finset P)} (C:Finset P) (hC:C∈ s)
    (d:Finset P→ ℝ) (a:ℝ) (x:P) :
    value s d a x= value (s.erase C) d a x+(if x∈ C then d C else 0):=by
  unfold value
  rw [← Finset.add_sum_erase _ _ hC]
  ring
lemma GS (s:Finset (Finset P)) (hs:Ef s)
    (b:P→ ℝ) (hb:∑ x,b x=0) (d:Finset P→ ℝ) (a:ℝ)
    (g:ℝ→ ℝ) (hg:∀ u v,|g u-g v| ≤ |u-v|) :
    |∑ x,b x*g (value s d a x)| ≤ ∑ C∈ s,|d C| * |mass b C| := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hsn:s.Nonempty
    · obtain ⟨C,hC,hmin⟩:=Finset.exists_min_image s Finset.card hsn
      let q:=a+∑ D∈ s.erase C,if C⊆ D then d D else 0
      let Δ:=g (q+d C)-g q
      have hΔ : |Δ| ≤ |d C| := by simpa only [Δ,add_sub_cancel_left] using hg (q+d C) q
      have he (x:P):g (value s d a x) =
          g (value (s.erase C) d a x)+(if x∈ C then Δ else 0):=by
        rw [Ta C hC]
        by_cases hx:x∈ C
        · rw [if_pos hx,if_pos hx,Pq hs C hC hmin d a x hx]
          dsimp only [Δ,q]
          ring
        · simp [hx]
      have hi:=ih (s.erase C) (Finset.erase_ssubset hC) (Sj hs C)
      have he':(∑ x,b x*g (value s d a x)) =
          (∑ x,b x*g (value (s.erase C) d a x))+Δ*mass b C:=by
        simp_rw [he,mul_add,Finset.sum_add_distrib]
        congr 1
        simp only [mul_ite,mul_zero,mass,Finset.mul_sum]
        simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
        exact Finset.sum_congr rfl (fun x _=> by ring)
      rw [he',← Finset.add_sum_erase _ _ hC]
      calc
        _ ≤ |∑ x,b x*g (value (s.erase C) d a x)|+|Δ*mass b C| := abs_add_le _ _
        _≤(∑ D∈ s.erase C,|d D| * |mass b D|)+|d C| * |mass b C| := by
          apply add_le_add hi
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)
        _= _:=by ring
    · have hs0:=Finset.not_nonempty_iff_eq_empty.mp hsn
      simp only [hs0,value,Finset.sum_empty,add_zero,← Finset.sum_mul,hb,zero_mul,abs_zero,le_refl]
def ind (C:Finset P) (x:P):ℝ:=if x∈ C then 1 else 0
def distance (s:Finset (Finset P)) (l:Finset P→ ℝ) (x y:P):ℝ :=
  ∑ C∈ s,l C*|ind C x-ind C y|
def AW (s:Finset (Finset P)) (l:Finset P→ ℝ) (y:P):ℝ :=
  ∑ C∈ s,l C*ind C y
def coeff (l:Finset P→ ℝ) (y:P) (C:Finset P):ℝ :=
  if y∈ C then -l C else l C
def CZ (s:Finset (Finset P)) (l:Finset P→ ℝ) (p q:P→ ℝ):ℝ :=
  ∑ C∈ s,l C*|mass p C-mass q C|
omit [Fintype P] in
lemma MN (s:Finset (Finset P)) (l:Finset P→ ℝ) (x y:P) :
    distance s l x y=distance s l y x:=by
  simp only [distance,abs_sub_comm]
omit [Fintype P] in
lemma QY (s:Finset (Finset P)) (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤ l C)
    (x y:P):0≤ distance s l x y :=
  Finset.sum_nonneg (fun C hC=> mul_nonneg (hl C hC) (abs_nonneg _))
omit [Fintype P] in
lemma GH (s:Finset (Finset P)) (l:Finset P→ ℝ) (x y:P) :
    distance s l x y=value s (coeff l y) (AW s l y) x:=by
  simp only [distance,value,AW,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hx:x∈ C <;> by_cases hy:y∈ C <;> simp [ind,coeff,hx,hy]
omit [Fintype P] in
lemma Oi (l:Finset P→ ℝ) (y:P) (C:Finset P) (hC:0≤ l C) :
    |coeff l y C|=l C:=by
  unfold coeff
  split_ifs <;> simp [abs_of_nonneg hC]
lemma OL (s:Finset (Finset P)) (hs:Ef s)
    (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤ l C) (p q:P→ ℝ)
    (hpq:∑ x,p x=∑ x,q x) (y:P) (g:ℝ→ ℝ)
    (hg:∀ u v,|g u-g v| ≤ |u-v|) :
    |(∑ x,p x*g (distance s l x y))-(∑ x,q x*g (distance s l x y))| ≤ CZ s l p q:=by
  have hb:(∑ x,(p x-q x))=0:=by rw [Finset.sum_sub_distrib,hpq,sub_self]
  have hh:=GS s hs (fun x=> p x-q x) hb (coeff l y) (AW s l y) g hg
  simp only [← GH,sub_mul,Finset.sum_sub_distrib,mass] at hh
  simp only [CZ,mass]
  convert hh using 1
  exact Finset.sum_congr rfl (fun C hC=> by rw [Oi l y C (hl C hC)])
lemma Fv (s:Finset (Finset P)) (hs:Ef s)
    (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤ l C) (p q:P→ ℝ)
    (hpq:∑ x,p x=∑ x,q x) (x' y:P) :
    |(∑ x,p x*|distance s l x y-distance s l x' y|)-
      (∑ x,q x*|distance s l x y-distance s l x' y|)| ≤ CZ s l p q:=by
  apply OL s hs l hl p q hpq y (fun u => |u-distance s l x' y|)
  intro u v
  simpa only [sub_sub_sub_cancel_right] using abs_abs_sub_abs_le_abs_sub (u-distance s l x' y) (v-distance s l x' y)
omit [Fintype P] in
lemma TB (s:Finset (Finset P)) (d e:Finset P→ ℝ) (a b:ℝ) (x:P) :
    value s d a x-value s e b x=value s (fun C=> d C-e C) (a-b) x:=by
  simp only [value]
  have he:(∑ C∈ s,if x∈ C then d C-e C else 0) =
      (∑ C∈ s,if x∈ C then d C else 0)-(∑ C∈ s,if x∈ C then e C else 0):=by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun C _=> by split_ifs <;> ring)
  rw [he]
  ring
lemma Jy (s:Finset (Finset P)) (hs:Ef s)
    (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤ l C) (p q:P→ ℝ)
    (hpq:∑ x,p x=∑ x,q x) (x x':P) :
    |(∑ y,p y*|distance s l x y-distance s l x' y|)-
      (∑ y,q y*|distance s l x y-distance s l x' y|)| ≤ 2*CZ s l p q:=by
  have hb:(∑ y,(p y-q y))=0:=by rw [Finset.sum_sub_distrib,hpq,sub_self]
  have hh:=GS s hs (fun y=> p y-q y) hb
    (fun C=> coeff l x C-coeff l x' C) (AW s l x-AW s l x') abs abs_abs_sub_abs_le_abs_sub
  have he (y:P):value s (fun C=> coeff l x C-coeff l x' C) (AW s l x-AW s l x') y =
      distance s l x y-distance s l x' y:=by
    rw [← TB,← GH,← GH,MN s l y x,MN s l y x']
  simp only [he,sub_mul,Finset.sum_sub_distrib,mass] at hh
  refine hh.trans ?_
  simp only [CZ,mass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C hC
  have hc : |coeff l x C-coeff l x' C| ≤ 2*l C:=by
    calc
      _ ≤ |coeff l x C|+|coeff l x' C| := abs_sub _ _
      _= _:=by rw [Oi l x C (hl C hC),Oi l x' C (hl C hC)]; ring
  calc
    _≤(2*l C)*|∑ y∈ C,p y-∑ y∈ C,q y| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _= _:=by ring
omit [Fintype P] [DecidableEq P] in
lemma Bf (p:P→ ℝ) (hp:∀ x,0≤ p x) (C:Finset P):0≤ mass p C :=
  Finset.sum_nonneg (fun x _=> hp x)
lemma Sx (p:P→ ℝ) (hp:∑ x,p x=1) (C:Finset P) (y:P) :
    (∑ x,p x*|ind C x-ind C y|)= if y∈ C then 1-mass p C else mass p C:=by
  by_cases hy:y∈ C
  · have he (x:P):p x*|ind C x-ind C y|=p x-(if x∈ C then p x else 0):=by
      by_cases hx:x∈ C <;> simp [ind,hx,hy]
    simp_rw [he]
    simp only [Finset.sum_sub_distrib,hp,← Finset.sum_filter,
      Finset.filter_mem_eq_inter,Finset.univ_inter,if_pos hy,mass]
  · have he (x:P):p x*|ind C x-ind C y|=if x∈ C then p x else 0:=by
      by_cases hx:x∈ C <;> simp [ind,hx,hy]
    simp_rw [he]
    simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,if_neg hy,mass]
lemma Mo (s:Finset (Finset P)) (l:Finset P→ ℝ)
    (hl:∀ C∈ s,0≤ l C) (p:P→ ℝ) (hp:∑ x,p x=1) (η:ℝ)
    (hbal:∀ C∈ s,0< l C→ η≤ mass p C∧ η≤1-mass p C) (y:P) :
    η*(∑ C∈ s,l C)≤∑ x,p x*distance s l x y:=by
  simp only [distance,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro C hC
  have he:(∑ x,p x*(l C*|ind C x-ind C y|)) =
      l C*(∑ x,p x*|ind C x-ind C y|):=by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _=> by ring)
  rw [he,Sx p hp]
  by_cases hpos:0< l C
  · rcases hbal C hC hpos with ⟨h1,h2⟩
    have hh:η≤ if y∈ C then 1-mass p C else mass p C:=by split_ifs <;> assumption
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hh (hl C hC)
  · have hz:l C=0:=le_antisymm (le_of_not_gt hpos) (hl C hC)
    simp [hz]
omit [Fintype P] in
lemma PL (s:Finset (Finset P)) (hs:Ef s)
    (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤ l C)
    (hn:(s.filter (fun C=>0< l C)).Nonempty) :
    ∃ C∈ s,0< l C∧∀ x∈ C,∀ y∈ C,distance s l x y=0:=by
  obtain ⟨C,hC,hmin⟩:=Finset.exists_min_image (s.filter (fun C=>0< l C)) Finset.card hn
  rcases Finset.mem_filter.mp hC with ⟨hCs,hCl⟩
  refine ⟨C,hCs,hCl,?_⟩
  intro x hx y hy
  unfold distance
  apply Finset.sum_eq_zero
  intro D hD
  by_cases hd:0< l D
  · have hcD:C.card≤ D.card:=hmin D (Finset.mem_filter.mpr ⟨hD,hd⟩)
    rcases hs C hCs D hD with hCD | hDC | hdis
    · simp [ind,hCD hx,hCD hy]
    · have he:C=D:=(Finset.eq_of_subset_of_card_le hDC hcD).symm
      simp [ind,← he,hx,hy]
    · have hxD:x∉ D:=fun h=> Finset.disjoint_left.mp hdis hx h
      have hyD:y∉ D:=fun h=> Finset.disjoint_left.mp hdis hy h
      simp [ind,hxD,hyD]
  · have hz:l D=0:=le_antisymm (le_of_not_gt hd) (hl D hD)
    simp [hz]
lemma OQ (s:Finset (Finset P)) (hs:Ef s)
    (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤ l C) (p:P→ ℝ)
    (hp0:∀ x,0≤ p x) (hp:∑ x,p x=1) (η:ℝ) (hη:0≤ η)
    (hbal:∀ C∈ s,0< l C→ η≤ mass p C∧ η≤1-mass p C) :
    η^3*(∑ C∈ s,l C) ≤
      ∑ y,p y*∑ x',p x'*∑ x,p x*|distance s l x y-distance s l x' y| := by
  let L:=∑ C∈ s,l C
  have hL:0≤ L:=Finset.sum_nonneg hl
  have hf0 (y x':P):0≤∑ x,p x*|distance s l x y-distance s l x' y| :=
    Finset.sum_nonneg (fun x _=> mul_nonneg (hp0 x) (abs_nonneg _))
  by_cases hn:(s.filter (fun C=>0< l C)).Nonempty
  · obtain ⟨C,hC,hCl,hzero⟩:=PL s hs l hl hn
    have hm:η≤ mass p C:=(hbal C hC hCl).1
    have hc0:=Bf p hp0 C
    have hy (y:P) (hy:y∈ C):mass p C*(η*L) ≤
        ∑ x',p x'*∑ x,p x*|distance s l x y-distance s l x' y| := by
      calc
        _=∑ x'∈ C,p x'*(η*L):=by simp only [mass,Finset.sum_mul]
        _≤∑ x'∈ C,p x'*∑ x,p x*|distance s l x y-distance s l x' y| := by
          apply Finset.sum_le_sum
          intro x' hx'
          apply mul_le_mul_of_nonneg_left _ (hp0 x')
          simp only [hzero x' hx' y hy,sub_zero,abs_of_nonneg (QY s l hl _ _)]
          exact Mo s l hl p hp η hbal y
        _≤ _:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
          (fun x' _ _=> mul_nonneg (hp0 x') (hf0 y x'))
    calc
      _≤ mass p C*(mass p C*(η*L)):=by
        have hsq:η*η≤ mass p C*mass p C:=mul_le_mul hm hm hη hc0
        have hmL:=mul_le_mul_of_nonneg_right hsq (mul_nonneg hη hL)
        dsimp only [L] at hmL
        nlinarith only [hmL]
      _=∑ y∈ C,p y*(mass p C*(η*L)):=by simp only [mass,Finset.sum_mul]
      _≤∑ y∈ C,p y*∑ x',p x'*∑ x,p x*|distance s l x y-distance s l x' y| :=
        Finset.sum_le_sum (fun y hyC=> mul_le_mul_of_nonneg_left (hy y hyC) (hp0 y))
      _≤ _:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        (fun y _ _=> mul_nonneg (hp0 y) (Finset.sum_nonneg (fun x' _=> mul_nonneg (hp0 x') (hf0 y x'))))
  · have hz:∑ C∈ s,l C=0:=by
      apply Finset.sum_eq_zero
      intro C hC
      have hnot:¬0< l C:=fun hc=> hn ⟨C,Finset.mem_filter.mpr ⟨hC,hc⟩⟩
      exact le_antisymm (le_of_not_gt hnot) (hl C hC)
    rw [hz,mul_zero]
    exact Finset.sum_nonneg (fun y _=> mul_nonneg (hp0 y)
      (Finset.sum_nonneg (fun x' _=> mul_nonneg (hp0 x') (hf0 y x'))))
omit [Fintype P] [DecidableEq P] in
lemma RO (s:Finset (Finset P)) (l:Finset P→ ℝ) (p q:P→ ℝ) :
    CZ s l p q=CZ s l q p:=by simp only [CZ,abs_sub_comm]
def BG (s:Finset (Finset P)) (l:Finset P→ ℝ) (x x' y:P):ℝ :=
  |distance s l x y-distance s l x' y|
def Dm (s:Finset (Finset P)) (l:Finset P→ ℝ) (p:P→ ℝ) (y:P):ℝ :=
  ∑ x',p x'*∑ x,p x*BG s l x x' y
omit [Fintype P] in
lemma Qk (s:Finset (Finset P)) (l:Finset P→ ℝ) (x x' y:P) :
    BG s l x x' y=BG s l x' x y:=abs_sub_comm _ _
lemma Gx {a b c:ℝ} (h : |a-b| ≤ c):a≤ b+c :=
  by have:=(abs_le.mp h).2; linarith
lemma Ns (s:Finset (Finset P)) (hs:Ef s)
    (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤ l C) (p q:P→ ℝ)
    (hp0:∀ x,0≤ p x) (hq0:∀ x,0≤ q x)
    (hp:∑ x,p x=1) (hq:∑ x,q x=1) (y:P) :
    Dm s l p y≤ Dm s l q y+2*CZ s l p q:=by
  have h1 (x':P):(∑ x,p x*BG s l x x' y) ≤
      (∑ x,q x*BG s l x x' y)+CZ s l p q :=
    Gx (Fv s hs l hl p q (hp.trans hq.symm) x' y)
  have h2 (x:P):(∑ x',p x'*BG s l x x' y) ≤
      (∑ x',q x'*BG s l x x' y)+CZ s l p q:=by
    simpa only [BG,abs_sub_comm] using
      Gx (Fv s hs l hl p q (hp.trans hq.symm) x y)
  calc
    _≤∑ x',p x'*((∑ x,q x*BG s l x x' y)+CZ s l p q) :=
      Finset.sum_le_sum (fun x' _=> mul_le_mul_of_nonneg_left (h1 x') (hp0 x'))
    _=(∑ x,q x*∑ x',p x'*BG s l x x' y)+CZ s l p q:=by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul]
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun x _=> Finset.sum_congr rfl (fun x' _=> by ring))
    _≤(∑ x,q x*((∑ x',q x'*BG s l x x' y)+CZ s l p q))+CZ s l p q:=by
      exact add_le_add (Finset.sum_le_sum (fun x _=> mul_le_mul_of_nonneg_left (h2 x) (hq0 x))) le_rfl
    _= Dm s l q y+2*CZ s l p q:=by
      simp only [Dm,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hq,one_mul]
      rw [show (∑ x,q x*∑ x',q x'*BG s l x x' y) =
          ∑ x,q x*∑ x',q x'*BG s l x' x y from by simp_rw [Qk s l _ _ y]]
      ring
lemma Pw (s:Finset (Finset P)) (l:Finset P→ ℝ) (p:P→ ℝ)
    (hp0:∀ x,0≤ p x) (hp:∑ x,p x=1) (y:P) (R:ℝ) :
    Dm s l p y≤2*∑ x,p x*|distance s l x y-R| := by
  have ht (x x':P):BG s l x x' y ≤
      |distance s l x y-R|+|distance s l x' y-R| := by
    simpa only [BG,abs_sub_comm (R:ℝ)] using abs_sub_le (distance s l x y) R (distance s l x' y)
  calc
    _≤∑ x',p x'*∑ x,p x*(|distance s l x y-R|+|distance s l x' y-R|):=by
      apply Finset.sum_le_sum
      intro x' _
      apply mul_le_mul_of_nonneg_left _ (hp0 x')
      exact Finset.sum_le_sum (fun x _=> mul_le_mul_of_nonneg_left (ht x x') (hp0 x))
    _= _:=by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul]
      ring
lemma JN (s:Finset (Finset P)) (hs:Ef s)
    (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤ l C) (a p q:P→ ℝ)
    (ha0:∀ x,0≤ a x) (ha:∑ x,a x=1) (hpq:∑ x,p x=∑ x,q x) :
    (∑ y,p y*Dm s l a y) ≤
      (∑ y,q y*Dm s l a y)+2*CZ s l p q:=by
  have ht (x x':P):(∑ y,p y*BG s l x x' y) ≤
      (∑ y,q y*BG s l x x' y)+2*CZ s l p q :=
    Gx (Jy s hs l hl p q hpq x x')
  have he (b:P→ ℝ):(∑ y,b y*Dm s l a y) =
      ∑ x',a x'*∑ x,a x*∑ y,b y*BG s l x x' y:=by
    simp only [Dm,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_congr rfl (fun y _=> by ring)
  rw [he p,he q]
  calc
    _≤∑ x',a x'*∑ x,a x*((∑ y,q y*BG s l x x' y)+2*CZ s l p q):=by
      apply Finset.sum_le_sum
      intro x' _
      apply mul_le_mul_of_nonneg_left _ (ha0 x')
      exact Finset.sum_le_sum (fun x _=> mul_le_mul_of_nonneg_left (ht x x') (ha0 x))
    _= _:=by simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,ha,one_mul]
lemma SH (s:Finset (Finset P)) (hs:Ef s)
    (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤ l C) (a t:P→ ℝ) (ρ:P→ P→ ℝ)
    (ha0:∀ x,0≤ a x) (ht0:∀ y,0≤ t y) (hρ0:∀ y x,0≤ ρ y x)
    (ha:∑ x,a x=1) (ht:∑ y,t y=1) (hρ:∀ y,∑ x,ρ y x=1) (R:P→ ℝ) :
    (∑ y,a y*Dm s l a y) ≤
      2*(∑ y,t y*∑ x,ρ y x*|distance s l x y-R y|)+
      2*(∑ y,t y*CZ s l (ρ y) a)+2*CZ s l t a:=by
  have hlast:=JN s hs l hl a a t ha0 ha (ha.trans ht.symm)
  rw [RO s l a t] at hlast
  have hy (y:P):Dm s l a y ≤
      2*(∑ x,ρ y x*|distance s l x y-R y|)+2*CZ s l (ρ y) a:=by
    have h1:=Ns s hs l hl a (ρ y) ha0 (hρ0 y) ha (hρ y) y
    rw [RO s l a (ρ y)] at h1
    exact h1.trans (add_le_add (Pw s l (ρ y) (hρ0 y) (hρ y) y (R y)) le_rfl)
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun y _=> mul_le_mul_of_nonneg_left (hy y) (ht0 y))
  have he:(∑ y,t y*(2*(∑ x,ρ y x*|distance s l x y-R y|)+2*CZ s l (ρ y) a)) =
      2*(∑ y,t y*∑ x,ρ y x*|distance s l x y-R y|)+2*(∑ y,t y*CZ s l (ρ y) a):=by
    simp only [mul_add,Finset.sum_add_distrib]
    rw [Finset.mul_sum,Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun y _=> by ring)
  rw [he] at hsum
  linarith
end Aa.AV
end
end
end
end
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u1} [Fintype P] [DecidableEq P]
variable (d:Depth P)
def At:Finset (Finset P):=by
  classical
  exact Finset.univ.filter (fun C=>∃ r:ℝ,C∈ d.cells r)
lemma Iv (C:Finset P):C∈ d.At↔∃ r:ℝ,C∈ d.cells r:=by
  classical
  simp [At]
lemma Mm (r:ℝ):d.cells r⊆ d.At :=
  fun C hC=>(d.Iv C).mpr ⟨r,hC⟩
lemma KH:AV.Ef d.At:=by
  intro C hC B hB
  obtain ⟨r,hr⟩:=(d.Iv C).mp hC
  obtain ⟨t,ht⟩:=(d.Iv B).mp hB
  by_cases hi:Disjoint C B
  · exact Or.inr (Or.inr hi)
  · obtain ⟨x,hxC,hxB⟩:=Finset.not_disjoint_iff.mp hi
    rw [d.Cx hr hxC,d.Cx ht hxB]
    rcases le_total t r with h | h
    · exact Or.inl (d.Hh h x)
    · exact Or.inr (Or.inl (d.Hh h x))
def ET (f:Finset P→ ℝ) (C:Finset P) (r:ℝ):ℝ :=
  if C∈ d.cells r then f C else 0
def Al (f:Finset P→ ℝ) (C:Finset P):ℝ:=∫ r,d.ET f C r
lemma Po (f:Finset P→ ℝ) (C:Finset P):Measurable (d.ET f C) :=
  (measurable_of_finite (fun s:Finset (Finset P)=> if C∈ s then f C else 0)).comp d.Ha
lemma Pl (f:Finset P→ ℝ) (C:Finset P) (r:ℝ):‖d.ET f C r‖ ≤ |f C| := by
  unfold ET
  split_ifs <;> simp [Real.norm_eq_abs,abs_nonneg]
lemma NA (f:Finset P→ ℝ) (hfu:f Finset.univ=0)
    (hfs:∀ x,f {x}=0) (C:Finset P) (r:ℝ) (hr:r∉ Set.Icc (-d.radius) d.radius) :
    d.ET f C r=0:=by
  unfold ET
  split_ifs with hc
  · obtain ⟨x,rfl⟩:=(d.mem_cells r C).mp hc
    rcases not_and_or.mp hr with hlo | hhi
    · rw [d.EO (le_of_lt (lt_of_not_ge hlo)),hfu]
    · rw [d.FY (lt_of_not_ge hhi),hfs]
  · rfl
lemma DJ (f:Finset P→ ℝ) (hfu:f Finset.univ=0)
    (hfs:∀ x,f {x}=0) (C:Finset P):Integrable (d.ET f C):=by
  exact Ct (d.Po f C) (d.Pl f C)
    (d.NA f hfu hfs C)
lemma El (f:Finset P→ ℝ) (hf:∀ C,0≤ f C) (C:Finset P) :
    0≤ d.Al f C:=by
  apply integral_nonneg
  intro r
  unfold ET
  split_ifs
  · exact hf C
  · exact le_rfl
lemma OO (f:Finset P→ ℝ) (C:Finset P) (hC:f C=0) :
    d.Al f C=0:=by simp [Al,ET,hC]
lemma OV (f:Finset P→ ℝ) (C:Finset P) (hC:C∉ d.At) :
    d.Al f C=0:=by
  have hh (r:ℝ):C∉ d.cells r:=fun hc=> hC ((d.Iv C).mpr ⟨r,hc⟩)
  simp [Al,ET,hh]
lemma GX (f:Finset P→ ℝ) (hfu:f Finset.univ=0)
    (hfs:∀ x,f {x}=0) (g:Finset P→ ℝ) :
    (∫ r,∑ C∈ d.cells r,f C*g C)=∑ C∈ d.At,d.Al f C*g C:=by
  have he (r:ℝ):(∑ C∈ d.cells r,f C*g C) =
      ∑ C∈ d.At,d.ET f C r*g C:=by
    simp only [ET,ite_mul,zero_mul,← Finset.sum_filter]
    congr 1
    ext C
    simp only [Finset.mem_filter]
    exact ⟨fun hc=>⟨d.Mm r hc,hc⟩,fun hc=> hc.2⟩
  simp only [he]
  rw [integral_finsetSum _ (fun C _=>(d.DJ f hfu hfs C).mul_const (g C))]
  exact Finset.sum_congr rfl (fun C _=> by rw [integral_mul_const]; rfl)
lemma FA (hn:2≤ Fintype.card P) (f:Finset P→ ℝ)
    (hfs:∀ C,C.card≤1→ f C=0) (hsym:∀ C,f Cᶜ=f C) :
    (∑ C,d.mass C*f C)=∑ C∈ d.At,d.Al f C:=by
  have hu:f Finset.univ=0:=by simpa using (hsym ∅).trans (hfs ∅ (by simp))
  rw [← d.DB hn f hfs]
  have he (r:ℝ):d.Ch f r=∑ C∈ d.cells r,f C:=by
    simp only [d.Kb,hsym,sub_self,Finset.sum_const_zero,add_zero]
  simp only [he]
  simpa using d.GX f hu (fun x=> hfs {x} (by simp)) (fun _=>1)
lemma NQ (p:P→ ℝ) (w:ℝ→ ℝ) (η:ℝ)
    (hws:∀ u,¬(η≤ u∧ η≤1-u)→ w u=0) (C:Finset P)
    (hC:0< d.Al (fun B=> w (AV.mass p B)) C) :
    η≤ AV.mass p C∧ η≤1-AV.mass p C:=by
  by_contra hn
  have hz:=d.OO (fun B=> w (AV.mass p B)) C (hws _ hn)
  linarith
lemma Ln (p:P→ ℝ) (hp0:∀ x,0≤ p x) (hp:∑ x,p x=1)
    (w:ℝ→ ℝ) (hw:∀ u,0≤ w u) (η:ℝ) (hη:0≤ η)
    (hws:∀ u,¬(η≤ u∧ η≤1-u)→ w u=0) :
    η^3*(∑ C∈ d.At,d.Al (fun B=> w (AV.mass p B)) C) ≤
      ∑ y,p y*AV.Dm d.At (d.Al (fun B=> w (AV.mass p B))) p y:=by
  exact AV.OQ d.At d.KH _
    (fun C _=> d.El _ (fun C=> hw _) C) p hp0 hp η hη
    (fun C _ hC=> d.NQ p w η hws C hC)
end Aa.Ak.Depth
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u2} [Fintype P] [DecidableEq P]
variable (d:Depth P)
omit [Fintype P] [DecidableEq P] in
lemma Gp (x y z:P) (hxy:x≠ y) (hyz:y≠ z) (hxz:x≠ z)
    (hlt:d.value x y< d.value y z):d.value x z=d.value x y:=by
  have h1:=d.Qw x y z hxy hyz hxz
  rw [min_eq_left (le_of_lt hlt)] at h1
  apply le_antisymm _ h1
  by_contra! hn
  have h2:=d.Qw x z y hxz hyz.symm hxy
  rw [d.symm z y] at h2
  exact (lt_min hn hlt).not_ge h2
def BI (x y:P) (u:ℝ):Finset P :=
  Finset.univ.filter (fun z=> z=y∨(z≠ x∧ u≤ d.value y z-d.value x z))
lemma NK (x y:P) (hxy:x≠ y) (u:ℝ) (hu:0< u) :
    d.BI x y u=d.cell (d.value x y+u) y:=by
  ext z
  simp only [BI,Finset.mem_filter,Finset.mem_univ,true_and,BN,share]
  by_cases hzy:z=y
  · simp [hzy]
  by_cases hzx:z=x
  · subst z
    have hlt:¬d.value x y+u≤ d.value y x:=by rw [d.symm y x]; linarith
    simp [hxy,hxy.symm,hlt]
  · simp only [hzx,ne_eq,false_or,not_false_eq_true,true_and,eq_comm (a:=y) (b:=z),hzy]
    constructor
    · intro h
      have hlt:d.value x z< d.value z y:=by rw [d.symm z y]; linarith
      have he:=d.Gp x z y (Ne.symm hzx) hzy hxy hlt
      linarith
    · intro h
      have hlt:d.value x y< d.value y z:=by linarith
      rw [d.Gp x y z hxy (Ne.symm hzy) (Ne.symm hzx) hlt]
      linarith
lemma JG (x y:P) (hxy:x≠ y) (u:ℝ) (hu:u<0)
    (hne:∀ z,u≠ d.value x y-d.value x z) :
    (d.BI x y u)ᶜ=d.cell (d.value x y-u) x:=by
  ext z
  simp only [Finset.mem_compl,BI,Finset.mem_filter,Finset.mem_univ,true_and,BN,share]
  by_cases hzx:z=x
  · subst z
    simp [hxy]
  by_cases hzy:z=y
  · subst z
    have hlt:¬d.value x y-u≤ d.value x y:=by linarith
    simp [hxy,hxy.symm,hlt]
  · simp only [hzy,false_or,ne_eq,not_false_eq_true,true_and,eq_comm (a:=x) (b:=z),hzx,not_le]
    constructor
    · intro h
      have hlt:d.value y z< d.value z x:=by rw [d.symm z x]; linarith
      have he:=d.Gp y z x (Ne.symm hzy) hzx hxy.symm hlt
      rw [d.symm y x] at he
      linarith
    · intro h
      have hlt:d.value y x< d.value x z:=by rw [d.symm y x]; linarith
      have he:=d.Gp y x z hxy.symm (Ne.symm hzx) (Ne.symm hzy) hlt
      rw [d.symm y x] at he
      have hn:=hne z
      rw [he]
      rcases lt_or_eq_of_le h with h | h
      · linarith
      · exfalso
        apply hn
        linarith
lemma Tw (p:P→ ℝ) (hp:∑ x,p x=1) (C:Finset P) :
    AV.mass p Cᶜ=1-AV.mass p C:=by
  have hh:=Finset.sum_add_sum_compl C p
  simp only [AV.mass]
  rw [hp] at hh
  linarith
lemma FM (p:P→ ℝ) (hp:∑ x,p x=1) (w:ℝ→ ℝ)
    (hw:∀ u,w (1-u)=w u) (x y:P) (hxy:x≠ y) :
    ∀ᵐ u:ℝ,w (AV.mass p (d.BI x y u)) =
      (if d.value x y< d.value x y+u then w (AV.mass p (d.cell (d.value x y+u) y)) else 0)+
      (if d.value x y< d.value x y-u then w (AV.mass p (d.cell (d.value x y-u) x)) else 0):=by
  have hn:∀ᵐ u:ℝ,∀ z:P,u≠ d.value x y-d.value x z :=
    ae_all_iff.mpr (fun z=> volume.ae_ne _)
  filter_upwards [hn,volume.ae_ne (0:ℝ)] with u hne hu
  rcases lt_or_gt_of_ne hu with hu | hu
  · have he:=d.JG x y hxy u hu hne
    have hm:=Tw p hp (d.BI x y u)
    rw [he] at hm
    rw [if_neg (by linarith),if_pos (by linarith),zero_add,hm,hw]
  · rw [d.NK x y hxy u hu,if_pos (by linarith),if_neg (by linarith),add_zero]
end Aa.Ak.Depth
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u3} [Fintype P] [DecidableEq P]
variable (d:Depth P)
def Cv (f:Finset P→ ℝ) (a:ℝ) (x:P) (r:ℝ):ℝ :=
  if a< r then f (d.cell r x) else 0
omit [DecidableEq P] in
lemma Ml (f:Finset P→ ℝ) (a:ℝ) (x:P) :
    Measurable (d.Cv f a x):=by
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · exact (measurable_of_finite f).comp (d.Ey x)
  · exact measurable_const
omit [DecidableEq P] in
lemma Ec (f:Finset P→ ℝ) (hfs:∀ x,f {x}=0)
    (a:ℝ) (ha : -d.radius≤ a) (x:P):Integrable (d.Cv f a x):=by
  apply Ct (d.Ml f a x)
      (C:=∑ C:Finset P,|f C|) (a:= -d.radius) (b:=d.radius)
  · intro r
    unfold Cv
    split_ifs
    · simpa only [Real.norm_eq_abs] using (Finset.single_le_sum (s:=Finset.univ) (f:=fun C:Finset P => |f C|)
        (fun _ _=> abs_nonneg _) (Finset.mem_univ (d.cell r x)))
    · simpa using Finset.sum_nonneg (fun C (_:C∈(Finset.univ:Finset (Finset P)))=> abs_nonneg (f C))
  · intro r hr
    rcases not_and_or.mp hr with hlo | hhi
    · have hh:¬a< r:=by have:=lt_of_not_ge hlo; linarith
      simp [Cv,hh]
    · simp [Cv,d.FY (lt_of_not_ge hhi) x,hfs]
lemma Os (f:Finset P→ ℝ) (r:ℝ) (x y:P) (hxy:x≠ y) :
    (∑ C∈ d.cells r,f C*|AV.ind C x-AV.ind C y|) =
      d.Cv f (d.value x y) x r+d.Cv f (d.value x y) y r:=by
  have hmem (z:P) (C:Finset P) (hC:C∈ d.cells r):z∈ C↔ C=d.cell r z :=
    ⟨fun hz=> d.Cx hC hz,fun he=> by rw [he]; exact d.CQ r z⟩
  by_cases hr:r≤ d.value x y
  · have hce:d.cell r x=d.cell r y:=d.Eh (Or.inr hr)
    have hz:∑ C∈ d.cells r,f C*|AV.ind C x-AV.ind C y|=0:=by
      apply Finset.sum_eq_zero
      intro C hC
      have hm:x∈ C↔ y∈ C:=by rw [hmem x C hC,hmem y C hC,hce]
      simp only [AV.ind,hm,sub_self,abs_zero,mul_zero]
    simp [hz,Cv,not_lt.mpr hr]
  · have hlt:d.value x y< r:=lt_of_not_ge hr
    have hns:¬d.share r x y:=by simpa [share,hxy] using hr
    have he (C:Finset P) (hC:C∈ d.cells r) :
        f C*|AV.ind C x-AV.ind C y| =
          (if C=d.cell r x then f (d.cell r x) else 0)+
          (if C=d.cell r y then f (d.cell r y) else 0):=by
      by_cases hx:x∈ C <;> by_cases hy:y∈ C
      · have hc:=d.Cx hC hx
        have hh:d.share r x y:=by rwa [hc,d.BN] at hy
        exact (hns hh).elim
      · have hc:=(hmem x C hC).mp hx
        have hn:C≠ d.cell r y:=fun h=> hy ((hmem y C hC).mpr h)
        simp only [AV.ind,if_pos hx,if_neg hy,sub_zero,abs_one,mul_one,if_pos hc,if_neg hn,add_zero]
        rw [hc]
      · have hc:=(hmem y C hC).mp hy
        have hn:C≠ d.cell r x:=fun h=> hx ((hmem x C hC).mpr h)
        simp only [AV.ind,if_neg hx,if_pos hy,zero_sub,abs_neg,abs_one,mul_one,if_pos hc,if_neg hn,zero_add]
        rw [hc]
      · have hn1:C≠ d.cell r x:=fun h=> hx ((hmem x C hC).mpr h)
        have hn2:C≠ d.cell r y:=fun h=> hy ((hmem y C hC).mpr h)
        simp [AV.ind,hx,hy,hn1,hn2]
    rw [Finset.sum_congr rfl he,Finset.sum_add_distrib]
    simp [d.CX,Cv,hlt]
lemma IW (f:Finset P→ ℝ) (hfu:f Finset.univ=0)
    (hfs:∀ x,f {x}=0) (x y:P) (hxy:x≠ y) :
    AV.distance d.At (d.Al f) x y =
      (∫ r,d.Cv f (d.value x y) x r)+(∫ r,d.Cv f (d.value x y) y r):=by
  rw [AV.distance,← d.GX f hfu hfs (fun C => |AV.ind C x-AV.ind C y|)]
  simp only [d.Os f _ x y hxy]
  exact integral_add (d.Ec f hfs _ (abs_le.mp (d.Cf x y)).1 x)
    (d.Ec f hfs _ (abs_le.mp (d.Cf x y)).1 y)
end Aa.Ak.Depth
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u4} [Fintype P] [DecidableEq P]
variable (d:Depth P)
lemma RH (p:P→ ℝ) (hp:∑ x,p x=1) (w:ℝ→ ℝ)
    (hwu:w 1=0) (hws:∀ x,w (p x)=0) (hwsym:∀ u,w (1-u)=w u)
    (x y:P) (hxy:x≠ y) :
    AV.distance d.At (d.Al (fun C=> w (AV.mass p C))) x y =
      ∫ u,w (AV.mass p (d.BI x y u)):=by
  let f:Finset P→ ℝ:=fun C=> w (AV.mass p C)
  have hfu:f Finset.univ=0:=by simpa [f,AV.mass,hp] using hwu
  have hfs:∀ z,f {z}=0:=by intro z; simpa [f,AV.mass] using hws z
  have hi (z:P):=d.Ec f hfs (d.value x y)
    (abs_le.mp (d.Cf x y)).1 z
  have hiY:Integrable (fun u=> d.Cv f (d.value x y) y (d.value x y+u)):=by
    exact ((measurePreserving_add_left volume (d.value x y)).integrable_comp (hi y).aestronglyMeasurable).mpr (hi y)
  have hiX:Integrable (fun u=> d.Cv f (d.value x y) x (d.value x y-u)) :=
    (integrable_comp_sub_left _ _).mpr (hi x)
  rw [d.IW f hfu hfs x y hxy]
  have he:=integral_congr_ae (d.FM p hp w hwsym x y hxy)
  change (∫ u,w (AV.mass p (d.BI x y u))) =
    ∫ u,d.Cv f (d.value x y) y (d.value x y+u)+d.Cv f (d.value x y) x (d.value x y-u) at he
  rw [he,integral_add hiY hiX,integral_add_left_eq_self,integral_sub_left_eq_self]
  exact add_comm _ _
end Aa.Ak.Depth
namespace Aa.Tail
open MeasureTheory
open scoped NNReal
variable {P:Type u5} [Fintype P]
def step (a u:ℝ):ℝ:=if u≤ a then 1 else 0
def law (b:ℝ) (p:P→ ℝ) (f:P→ ℝ) (u:ℝ):ℝ:=b+∑ z,p z*step (f z) u
lemma QA (a:ℝ):Measurable (step a):=by
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const
lemma LX (b:ℝ) (p f:P→ ℝ):Measurable (law b p f) :=
  measurable_const.add (Finset.measurable_sum _ (fun _z _=> measurable_const.mul (QA _)))
lemma QL (a b u:ℝ) : |step a u-step b u| =
    if min a b< u∧ u≤ max a b then 1 else 0:=by
  unfold step
  rcases le_total a b with h | h
  · rw [min_eq_left h,max_eq_right h]
    by_cases hua:u≤ a
    · have hub:u≤ b:=hua.trans h
      simp [hua,hub,not_lt.mpr hua]
    · have hau:a< u:=lt_of_not_ge hua
      by_cases hub:u≤ b <;> simp [hua,hub,hau]
  · rw [min_eq_right h,max_eq_left h]
    by_cases hub:u≤ b
    · have hua:u≤ a:=hub.trans h
      simp [hua,hub,not_lt.mpr hub]
    · have hbu:b< u:=lt_of_not_ge hub
      by_cases hua:u≤ a <;> simp [hua,hub,hbu]
lemma FV (a b:ℝ):(fun u => |step a u-step b u|) =
    (Set.Ioc (min a b) (max a b)).indicator (fun _:ℝ=>1):=by
  funext u
  simp [QL,Set.indicator_apply]
lemma Fu (a b:ℝ):Integrable (fun u => |step a u-step b u|):=by
  rw [FV,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
lemma Kd (a b:ℝ):(∫ u,|step a u-step b u|) = |a-b| := by
  rw [FV,integral_indicator measurableSet_Ioc]
  simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,measureReal_def,Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_max (a:=a) (b:=b)))]
  rcases le_total a b with hh | hh
  · simp [max_eq_right hh,min_eq_left hh,abs_of_nonpos (sub_nonpos.mpr hh)]
  · simp [max_eq_left hh,min_eq_right hh,abs_of_nonneg (sub_nonneg.mpr hh)]
lemma MF (b:ℝ) (p f g:P→ ℝ) (hp:∀ z,0≤ p z) (u:ℝ) :
    |law b p f u-law b p g u| ≤ ∑ z,p z*|step (f z) u-step (g z) u| := by
  have he:law b p f u-law b p g u=∑ z,p z*(step (f z) u-step (g z) u):=by
    simp only [law,mul_sub,Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _≤∑ z,|p z*(step (f z) u-step (g z) u)| := Finset.abs_sum_le_sum_abs _ _
    _= _:=by simp only [abs_mul,abs_of_nonneg (hp _)]
lemma Mz (b:ℝ) (p f g:P→ ℝ) (hp:∀ z,0≤ p z)
    (w:ℝ→ ℝ) (Λ:ℝ≥0) (hw:LipschitzWith Λ w) :
    (∫ u,|w (law b p f u)-w (law b p g u)|)≤(Λ:ℝ)*∑ z,p z*|f z-g z| := by
  let h:ℝ→ ℝ:=fun u=>(Λ:ℝ)*∑ z,p z*|step (f z) u-step (g z) u|
  have hi:Integrable h:=(integrable_finsetSum (s:=Finset.univ)
    (fun z _=>(Fu (f z) (g z)).const_mul (p z))).const_mul _
  have hb (u:ℝ) : |w (law b p f u)-w (law b p g u)| ≤ h u:=by
    have hh:=hw.norm_sub_le (law b p f u) (law b p g u)
    simp only [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (MF b p f g hp u) Λ.coe_nonneg)
  have hm:Measurable (fun u => |w (law b p f u)-w (law b p g u)|) :=
    ((hw.continuous.measurable.comp (LX b p f)).sub
      (hw.continuous.measurable.comp (LX b p g))).abs
  have hi':=hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun u=> by
    simpa only [Real.norm_eq_abs,abs_abs] using hb u))
  calc
    _≤∫ u,h u:=integral_mono hi' hi hb
    _= _:=by
      simp only [h,integral_const_mul]
      rw [integral_finsetSum _ (fun z _=>(Fu (f z) (g z)).const_mul (p z))]
      simp only [integral_const_mul,Kd]
end Aa.Tail
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u6} [Fintype P] [DecidableEq P]
variable (d:Depth P)
omit [DecidableEq P] in
lemma LP (f:Finset P→ ℝ) (hfu:f Finset.univ=0)
    (hfs:∀ x,f {x}=0) (x:P):Integrable (fun r=> f (d.cell r x)):=by
  apply Ct ((measurable_of_finite f).comp (d.Ey x))
    (C:=∑ C:Finset P,|f C|) (a:= -d.radius) (b:=d.radius)
  · intro r
    simpa only [Function.comp_def,Real.norm_eq_abs] using (Finset.single_le_sum (s:=Finset.univ) (f:=fun C:Finset P => |f C|)
      (fun _ _=> abs_nonneg _) (Finset.mem_univ (d.cell r x)))
  · intro r hr
    change f (d.cell r x)=0
    rcases not_and_or.mp hr with hlo | hhi
    · rw [d.EO (le_of_lt (lt_of_not_ge hlo)),hfu]
    · rw [d.FY (lt_of_not_ge hhi),hfs]
lemma MW (f:Finset P→ ℝ) (hfu:f Finset.univ=0)
    (hfs:∀ x,f {x}=0) (y:P) :
    AV.AW d.At (d.Al f) y=∫ r,f (d.cell r y):=by
  rw [AV.AW,← d.GX f hfu hfs (fun C=> AV.ind C y)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  have he (C:Finset P) (hC:C∈ d.cells r):f C*AV.ind C y =
      if C=d.cell r y then f (d.cell r y) else 0:=by
    by_cases hy:y∈ C
    · have hc:=d.Cx hC hy
      subst C
      simp [AV.ind,d.CQ]
    · have hn:C≠ d.cell r y:=fun h=> hy (h ▸ d.CQ r y)
      simp [AV.ind,hy,hn]
  change (∑ C∈ d.cells r,f C*AV.ind C y)=f (d.cell r y)
  rw [Finset.sum_congr rfl he]
  simp [d.CX]
lemma Jt (p:P→ ℝ) (hp:∑ x,p x=1) (w:ℝ→ ℝ)
    (hws:∀ x,w (p x)=0) (hwsym:∀ u,w (1-u)=w u)
    (x y:P) (hxy:x≠ y):Integrable (fun u=> w (AV.mass p (d.BI x y u))):=by
  let f:Finset P→ ℝ:=fun C=> w (AV.mass p C)
  have hfs:∀ z,f {z}=0:=by intro z; simpa [f,AV.mass] using hws z
  have hi (z:P):=d.Ec f hfs (d.value x y)
    (abs_le.mp (d.Cf x y)).1 z
  have hiY:Integrable (fun u=> d.Cv f (d.value x y) y (d.value x y+u)) :=
    ((measurePreserving_add_left volume (d.value x y)).integrable_comp (hi y).aestronglyMeasurable).mpr (hi y)
  have hiX:Integrable (fun u=> d.Cv f (d.value x y) x (d.value x y-u)) :=
    (integrable_comp_sub_left _ _).mpr (hi x)
  apply (hiY.add hiX).congr
  filter_upwards [d.FM p hp w hwsym x y hxy] with u hu
  exact hu.symm
end Aa.Ak.Depth
namespace Aa.Tail
open MeasureTheory Ak
open scoped NNReal
variable {P:Type u7} [Fintype P] [DecidableEq P]
def Cu (p:P→ ℝ) (x y z:P):ℝ:=if z=x∨ z=y then 0 else p z
omit [Fintype P] in
lemma Sa (p:P→ ℝ) (hp:∀ z,0≤ p z) (x y z:P):0≤ Cu p x y z:=by
  unfold Cu
  split_ifs <;> simp [hp]
lemma Ed (p:P→ ℝ) (C:Finset P):AV.mass p C=∑ z,if z∈ C then p z else 0:=by
  simp [AV.mass]
lemma Ix (d:Depth P) (p:P→ ℝ) (x y:P) (hxy:x≠ y) (u:ℝ) :
    AV.mass p (d.BI x y u)=
      law (p y) (Cu p x y) (fun z=> d.value y z-d.value x z) u:=by
  rw [Ed]
  have he (z:P):(if z∈ d.BI x y u then p z else 0)=
      (if z=y then p y else 0)+Cu p x y z*step (d.value y z-d.value x z) u:=by
    by_cases hy:z=y
    · subst z; simp [Depth.BI,Cu]
    by_cases hx:z=x
    · subst z; simp [Depth.BI,Cu,hxy]
    · simp [Depth.BI,Cu,step,hx,hy,mul_ite]
  simp only [he,Finset.sum_add_distrib]
  simp [law]
lemma NZ (d:Depth P) (p:P→ ℝ) (x y:P) (hx:p x=0) (hxy:x≠ y) (c u:ℝ) :
    AV.mass p (d.cell (u-c) y)=law (p y) (Cu p x y) (fun z=> d.value y z+c) u:=by
  rw [Ed]
  have he (z:P):(if z∈ d.cell (u-c) y then p z else 0)=
      (if z=y then p y else 0)+Cu p x y z*step (d.value y z+c) u:=by
    by_cases hy:z=y
    · subst z; simp [Cu,d.CQ]
    by_cases hz:z=x
    · subst z; simp [Cu,hx,hxy]
    · have hh:u-c≤ d.value y z↔ u≤ d.value y z+c:=by constructor <;> intro hh <;> linarith
      simp [Depth.BN,Depth.share,Cu,step,hz,hy,Ne.symm hy,hh,mul_ite]
  simp only [he,Finset.sum_add_distrib]
  simp [law]
lemma KJ (d d':Depth P) (p:P→ ℝ) (hp0:∀ z,0≤ p z) (hp:∑ z,p z=1)
    (w:ℝ→ ℝ) (Λ:ℝ≥0) (hw:LipschitzWith Λ w)
    (hwu:w 1=0) (hws:∀ z,w (p z)=0) (hwsym:∀ u,w (1-u)=w u)
    (x y:P) (hpx:p x=0) (hxy:x≠ y) (c:ℝ) :
    |AV.distance d.At (d.Al (fun C=> w (AV.mass p C))) x y-
      AV.AW d'.At (d'.Al (fun C=> w (AV.mass p C))) y| ≤
      (Λ:ℝ)*∑ z,Cu p x y z*|d.value y z-d.value x z-(d'.value y z+c)| := by
  let f:Finset P→ ℝ:=fun C=> w (AV.mass p C)
  have hfu:f Finset.univ=0:=by simpa [f,AV.mass,hp] using hwu
  have hfs:∀ z,f {z}=0:=by intro z; simpa [f,AV.mass] using hws z
  let a:=law (p y) (Cu p x y) (fun z=> d.value y z-d.value x z)
  let b:=law (p y) (Cu p x y) (fun z=> d'.value y z+c)
  have hia:Integrable (fun u=> w (a u)):=by
    simpa only [Ix d p x y hxy] using
      d.Jt p hp w hws hwsym x y hxy
  have hib0:=d'.LP f hfu hfs y
  have hib:Integrable (fun u=> w (b u)):=by
    have hh:=((measurePreserving_add_right volume (-c)).integrable_comp hib0.aestronglyMeasurable).mpr hib0
    simpa only [Function.comp_def,f,← sub_eq_add_neg,NZ d' p x y hpx hxy c] using hh
  have he:(∫ u,w (b u))=AV.AW d'.At (d'.Al f) y:=by
    rw [d'.MW f hfu hfs y]
    have hh:=integral_add_right_eq_self (μ:=volume) (fun r=> f (d'.cell r y)) (-c)
    simpa only [f,← sub_eq_add_neg,NZ d' p x y hpx hxy c] using hh
  rw [d.RH p hp w hwu hws hwsym x y hxy,← he]
  simp only [Ix d p x y hxy]
  change |(∫ u,w (a u))-(∫ u,w (b u))| ≤ _
  rw [← integral_sub hia hib]
  calc
    _≤∫ u,|w (a u)-w (b u)| := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun u=> w (a u)-w (b u))
    _≤ _:=Mz (p y) (Cu p x y) _ _ (Sa p hp0 x y) w Λ hw
end Aa.Tail
namespace Aa.Arithmetic
variable {K:Type u8} [Field K]
lemma Tx (v:AbsoluteValue K ℝ) (a b c d z w t:K)
    (hc:c≠ a) (hz:z≠ a) (hcz:c≠ z) (ht:t≠0)
    (hcd:(c-a)*(d-b)=t) (hzw:(z-a)*(w-b)=t) :
    -Real.log (v (w-d)) = -Real.log (v (c-z))+Real.log (v (z-a))-
      Real.log (v t)+Real.log (v (c-a)):=by
  rw [Pe a b c d z w t hc hz hcd hzw,
    map_div₀,map_mul,map_mul,
    Real.log_div (mul_ne_zero (v.pos ht).ne' (v.pos (sub_ne_zero.mpr hcz)).ne')
      (mul_ne_zero (v.pos (sub_ne_zero.mpr hz)).ne' (v.pos (sub_ne_zero.mpr hc)).ne'),
    Real.log_mul (v.pos ht).ne' (v.pos (sub_ne_zero.mpr hcz)).ne',
    Real.log_mul (v.pos (sub_ne_zero.mpr hz)).ne' (v.pos (sub_ne_zero.mpr hc)).ne']
  ring
lemma HM (v:AbsoluteValue K ℝ) (a b:K):v (a-b)=v (b-a):=by
  rw [← neg_sub b a,map_neg_eq_map]
lemma Kz {P:Type u9} (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁)
    (h₂:Function.Injective Z₂) (v:AbsoluteValue K ℝ) (x y z:P)
    (hxy:x≠ y) (hxz:x≠ z) (hyz:y≠ z) (t:K)
    (hy:(Z₁ x-Z₁ y)*(Z₂ x-Z₂ y)=t)
    (hz:(Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t) :
    -Real.log (v (Z₂ y-Z₂ z)) = -Real.log (v (Z₁ y-Z₁ z))-
      (-Real.log (v (Z₁ x-Z₁ z)))-Real.log (v t)-(-Real.log (v (Z₁ x-Z₁ y))):=by
  have ht:t≠0:=by rw [← hy]; exact mul_ne_zero (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
  have hh:=Tx v (Z₁ x) (Z₂ x) (Z₁ y) (Z₂ y) (Z₁ z) (Z₂ z) t
    (h₁.ne hxy.symm) (h₁.ne hxz.symm) (h₁.ne hyz) ht
    (by convert hy using 1; ring) (by convert hz using 1; ring)
  rw [HM v (Z₂ z) (Z₂ y),HM v (Z₁ z) (Z₁ x),
    HM v (Z₁ y) (Z₁ x)] at hh
  linarith
end Aa.Arithmetic
end
end
end
end
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators
namespace Aa.Ak.Depth
open MeasureTheory AV
open scoped BigOperators
variable {P:Type u1} [Fintype P] [DecidableEq P]
variable (d:Depth P)
lemma QS (f:Finset P→ ℝ) (hfu:f Finset.univ=0)
    (hfs:∀ x,f {x}=0) (C:Finset P) :
    |d.Al f C|≤2*d.radius*|f C| := by
  rw [← Real.norm_eq_abs,Al]
  apply (norm_integral_le_integral_norm _).trans
  exact Ei d.Fw (d.DJ f hfu hfs C).norm
    (d.Pl f C) (fun r hr=> by rw [d.NA f hfu hfs C r hr,norm_zero])
lemma NH (f:Finset P→ ℝ) (g:Finset P→ ℝ) :
    (∑ C∈ d.At,d.Al f C*g C)=∑ C,d.Al f C*g C:=by
  exact Finset.sum_subset (Finset.subset_univ _) (fun C _ hC=> by rw [d.OV f C hC,zero_mul])
lemma Si (f g:Finset P→ ℝ) (C:Finset P) :
    d.Al (fun B=> f B*g B) C=d.Al f C*g C:=by
  unfold Al
  rw [← integral_mul_const]
  congr 1
  funext r
  simp only [ET,ite_mul,zero_mul]
lemma Gs (f g:Finset P→ ℝ)
    (hfu:f Finset.univ=0) (hfs:∀ x,f {x}=0)
    (hgu:g Finset.univ=0) (hgs:∀ x,g {x}=0) (C:Finset P) :
    |d.Al f C-d.Al g C|≤d.Al (fun B => |f B-g B|) C:=by
  rw [Al,Al,← integral_sub (d.DJ f hfu hfs C) (d.DJ g hgu hgs C)]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans_eq
  congr 1
  funext r
  simp only [ET,Real.norm_eq_abs]
  split_ifs <;> simp
lemma Km (f g:Finset P→ ℝ)
    (hfu:f Finset.univ=0) (hfs:∀ x,f {x}=0)
    (hgu:g Finset.univ=0) (hgs:∀ x,g {x}=0) (x y:P) :
    |distance d.At (d.Al f) x y-distance d.At (d.Al g) x y|≤
      ∑ C∈ d.At,d.Al (fun B => |f B-g B|) C:=by
  unfold distance
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro C hC
  rw [← sub_mul,abs_mul,abs_abs]
  have hi : |ind C x-ind C y|≤1:=by unfold ind; split_ifs <;> norm_num
  have h1:=mul_le_mul_of_nonneg_right (d.Gs f g hfu hfs hgu hgs C) (abs_nonneg (ind C x-ind C y))
  exact h1.trans (by simpa using mul_le_mul_of_nonneg_left hi (d.El _ (fun B=> abs_nonneg _) C))
lemma Nt (f g:Finset P→ ℝ)
    (hfu:f Finset.univ=0) (hfs:∀ x,f {x}=0)
    (hgu:g Finset.univ=0) (hgs:∀ x,g {x}=0) (y:P) :
    |AW d.At (d.Al f) y-AW d.At (d.Al g) y|≤
      ∑ C∈ d.At,d.Al (fun B => |f B-g B|) C:=by
  unfold AW
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro C hC
  rw [← sub_mul,abs_mul]
  have hi : |ind C y|≤1:=by unfold ind; split_ifs <;> norm_num
  have h1:=mul_le_mul_of_nonneg_right (d.Gs f g hfu hfs hgu hgs C) (abs_nonneg (ind C y))
  exact h1.trans (by simpa using mul_le_mul_of_nonneg_left hi (d.El _ (fun B=> abs_nonneg _) C))
lemma Pr (f:Finset P→ ℝ) (p a:P→ ℝ) :
    CZ d.At (d.Al f) p a =
      ∑ C∈ d.At,d.Al (fun B=> f B*|AV.mass p B-AV.mass a B|) C:=by
  simp only [CZ,d.Si]
variable {Ω:Type u2} [MeasurableSpace Ω] (D:Ω→ Depth P)
    (hD:∀ x y,Measurable (fun ω=>(D ω).value x y))
include hD
lemma IX (f:Finset P→ ℝ) (C:Finset P) :
    Measurable (fun ω=>(D ω).Al f C):=by
  have hm:Measurable (fun p:Ω×ℝ=>(D p.1).ET f C p.2) :=
    (measurable_of_finite (fun s:Finset (Finset P)=> if C∈ s then f C else 0)).comp
    (EP (P:=P) (Ω:=Ω×ℝ) (fun p:Ω×ℝ=> D p.1)
      (fun x y=>(hD x y).comp measurable_fst) Prod.snd measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right.measurable
lemma IS {μ:Measure Ω}
    (hi:∀ x y,Integrable (fun ω=>(D ω).value x y) μ)
    (f:Finset P→ ℝ) (hfu:f Finset.univ=0) (hfs:∀ x,f {x}=0) (C:Finset P) :
    Integrable (fun ω=>(D ω).Al f C) μ:=by
  apply (((DI D hi).const_mul 2).mul_const |f C|).mono'
    (IX D hD f C).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω=>(D ω).QS f hfu hfs C)
lemma Gv {μ:Measure Ω}
    (hi:∀ x y,Integrable (fun ω=>(D ω).value x y) μ)
    (f g:Finset P→ ℝ) (hfu:f Finset.univ=0) (hfs:∀ x,f {x}=0) :
    Integrable (fun ω=>∑ C∈(D ω).At,(D ω).Al f C*g C) μ:=by
  simp only [NH]
  exact integrable_finsetSum _ (fun C _=>(IS D hD hi f hfu hfs C).mul_const (g C))
lemma EZ {μ:Measure Ω}
    (hi:∀ x y,Integrable (fun ω=>(D ω).value x y) μ)
    (f:Finset P→ ℝ) (hfu:f Finset.univ=0) (hfs:∀ x,f {x}=0) (x y:P) :
    Integrable (fun ω=> distance (D ω).At ((D ω).Al f) x y) μ :=
  Gv D hD hi f (fun B => |ind B x-ind B y|) hfu hfs
lemma ER {μ:Measure Ω}
    (hi:∀ x y,Integrable (fun ω=>(D ω).value x y) μ)
    (f:Finset P→ ℝ) (hfu:f Finset.univ=0) (hfs:∀ x,f {x}=0) (y:P) :
    Integrable (fun ω=> AW (D ω).At ((D ω).Al f) y) μ :=
  Gv D hD hi f (fun B=> ind B y) hfu hfs
end Aa.Ak.Depth
namespace Aa.AV
lemma Iy (δ:ℝ):LipschitzWith 1 (Be δ):=by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using Mf δ x y
end Aa.AV
namespace Aa.Bg
open Ak MeasureTheory Variance AV
open scoped BigOperators
variable {P:Type u3} [Fintype P] [DecidableEq P]
variable {K:Type u4} [Field K] [NumberField K]
variable (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
include h₁ h₂
lemma OZ (v:NumberField.InfinitePlace K) (x y z:P)
    (hxy:x≠y) (hxz:x≠z) (hyz:y≠z) (t:K)
    (hy:(Z₁ x-Z₁ y)*(Z₂ x-Z₂ y)=t) (hz:(Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t) :
    (fun ω=>(arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-
      ((arch Z₂ v ω).value y z+(Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))))) =ᵐ[Ao.As]
    (fun ω=> Ao.error ω (v.embedding (Z₁ y)) (v.embedding (Z₁ z))-
      Ao.error ω (v.embedding (Z₁ x)) (v.embedding (Z₁ z))-
      Ao.error ω (v.embedding (Z₂ y)) (v.embedding (Z₂ z))):=by
  have he:=Arithmetic.Kz Z₁ Z₂ h₁ h₂ v.val x y z hxy hxz hyz t hy hz
  filter_upwards [DE Z₁ h₁ v hyz,DE Z₁ h₁ v hxz,DE Z₂ h₂ v hyz] with ω ha hb hc
  rw [ha,hb,hc]
  simp only [Ao.error,← map_sub,NumberField.InfinitePlace.norm_embedding_eq]
  change -Real.log (v (Z₂ y-Z₂ z)) = -Real.log (v (Z₁ y-Z₁ z)) -
    -Real.log (v (Z₁ x-Z₁ z)) - Real.log (v t) - -Real.log (v (Z₁ x-Z₁ y)) at he
  linarith
lemma KQ (v:NumberField.InfinitePlace K) (x y z:P)
    (hxy:x≠y) (hxz:x≠z) (hyz:y≠z) (t:K)
    (hy:(Z₁ x-Z₁ y)*(Z₂ x-Z₂ y)=t) (hz:(Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t) :
    (∫ ω,|(arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-
      ((arch Z₂ v ω).value y z+(Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))))| ∂Ao.As)≤12:=by
  have hEq:=OZ Z₁ Z₂ h₁ h₂ v x y z hxy hxz hyz t hy hz
  have heq:=integral_congr_ae (hEq.fun_comp (abs:ℝ→ ℝ))
  dsimp only [Function.comp_def] at heq
  rw [heq]
  have ha:=Ao.Bn (Bx Z₁ h₁ v hyz)
  have hb:=Ao.Bn (Bx Z₁ h₁ v hxz)
  have hc:=Ao.Bn (Bx Z₂ h₂ v hyz)
  have hh:=integral_mono ((ha.sub hb).sub hc).abs ((ha.abs.add hb.abs).add hc.abs) (fun ω =>
    (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl))
  dsimp only [Pi.sub_apply,Pi.add_apply] at hh
  have hAdd:=integral_add (ha.abs.add hb.abs) hc.abs
  have hAdd2:=integral_add ha.abs hb.abs
  dsimp only [Pi.add_apply] at hAdd hAdd2
  rw [hAdd,hAdd2] at hh
  have h1:=Ao.Es (Bx Z₁ h₁ v hyz)
  have h2:=Ao.Es (Bx Z₁ h₁ v hxz)
  have h3:=Ao.Es (Bx Z₂ h₂ v hyz)
  linarith
lemma RM (v:NumberField.InfinitePlace K) (p:P→ ℝ)
    (hp0:∀ z,0≤p z) (hp:∑ z,p z=1) (x y:P) (hpx:p x=0) (hpy:p y≠0)
    (t:K) (ht:∀ z,p z≠0→(Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t)
    (δ:ℝ) (hδ:0≤δ) (hps:∀ z,p z≤δ) :
    (∫ ω,|distance (arch Z₁ v ω).At ((arch Z₁ v ω).Al (fun C=> Be δ (mass p C))) x y-
      AW (arch Z₂ v ω).At ((arch Z₂ v ω).Al (fun C=> Be δ (mass p C))) y| ∂Ao.As)≤12:=by
  have hxy:x≠y:=fun hh=> hpy (hh ▸ hpx)
  let f:Finset P→ ℝ:=fun C=> Be δ (mass p C)
  have hfu:f Finset.univ=0:=by simp only [f,mass,hp]; exact DR (by linarith)
  have hfs (z):f {z}=0:=by simp only [f,mass,Finset.sum_singleton]; exact BX (hps z)
  have hl:=Depth.EZ (arch Z₁ v) (BA Z₁ h₁ v) (AO Z₁ h₁ v) f hfu hfs x y
  have hr:=Depth.ER (arch Z₂ v) (BA Z₂ h₂ v) (AO Z₂ h₂ v) f hfu hfs y
  let c:=Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))
  let E:Ao.AS→ ℝ:=fun ω=>∑ z,Tail.Cu p x y z*
    |(arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-((arch Z₂ v ω).value y z+c)|
  have hEi (z:P):Integrable (fun ω=> Tail.Cu p x y z*
    |(arch Z₁ v ω).value y z-(arch Z₁ v ω).value x z-((arch Z₂ v ω).value y z+c)|) Ao.As :=
    ((((AO Z₁ h₁ v y z).sub (AO Z₁ h₁ v x z)).sub
      ((AO Z₂ h₂ v y z).add (integrable_const c))).abs.const_mul _)
  have hi:Integrable E Ao.As:=integrable_finsetSum _ (fun z _=> hEi z)
  have hh:=integral_mono (hl.sub hr).abs hi (fun ω=> by
    simpa only [f,E,Pi.sub_apply,NNReal.coe_one,one_mul] using Tail.KJ
      (arch Z₁ v ω) (arch Z₂ v ω) p hp0 hp (Be δ) 1 (Iy δ)
      (DR (by linarith)) (fun z=> BX (hps z)) (IN δ) x y hpx hxy c)
  apply hh.trans
  unfold E
  rw [integral_finsetSum Finset.univ (fun z _=> hEi z)]
  simp only [integral_const_mul]
  apply le_trans (Finset.sum_le_sum (fun z _=> show Tail.Cu p x y z* _≤12*p z from ?_))
    (by rw [← Finset.mul_sum,hp,mul_one])
  by_cases hzx:z=x
  · subst z; simp [Tail.Cu,hpx]
  by_cases hzy:z=y
  · subst z; simp only [Tail.Cu,or_true,reduceIte,zero_mul]; exact mul_nonneg (by norm_num) (hp0 y)
  by_cases hpz:p z=0
  · simp [Tail.Cu,hzx,hzy,hpz]
  · simp only [Tail.Cu,hzx,hzy,or_self,reduceIte]
    have he:=KQ Z₁ Z₂ h₁ h₂ v x y z hxy (Ne.symm hzx) (Ne.symm hzy) t (ht y hpy) (ht z hpz)
    dsimp [c]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left he (hp0 z)
end Aa.Bg
noncomputable section
namespace Aa.Bg
open Ak MeasureTheory Variance AV
open scoped BigOperators
variable {P:Type u5} [Fintype P] [DecidableEq P]
variable {K:Type u6} [Field K] [NumberField K]
variable (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
include h₁ h₂
lemma PQ (v:NumberField.FinitePlace K) (p:P→ ℝ)
    (hp0:∀ z,0≤p z) (hp:∑ z,p z=1) (x y:P) (hpx:p x=0) (hpy:p y≠0)
    (t:K) (ht:∀ z,p z≠0→(Z₁ x-Z₁ z)*(Z₂ x-Z₂ z)=t)
    (δ:ℝ) (hδ:0≤δ) (hps:∀ z,p z≤δ) :
    |distance (finite Z₁ h₁ v).At ((finite Z₁ h₁ v).Al (fun C=> Be δ (mass p C))) x y-
      AW (finite Z₂ h₂ v).At ((finite Z₂ h₂ v).Al (fun C=> Be δ (mass p C))) y|≤0:=by
  have hxy:x≠y:=fun hh=> hpy (hh ▸ hpx)
  let c:=Real.log (v t)-Real.log (v (Z₁ x-Z₁ y))
  have hh:=Tail.KJ (finite Z₁ h₁ v) (finite Z₂ h₂ v) p hp0 hp (Be δ) 1
    (Iy δ) (DR (by linarith)) (fun z=> BX (hps z))
    (IN δ) x y hpx hxy c
  simp only [NNReal.coe_one,one_mul] at hh
  apply hh.trans
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro z _
  by_cases hxz:x=z
  · subst z; simp [Tail.Cu]
  by_cases hyz:y=z
  · subst z; simp [Tail.Cu]
  by_cases hpz:p z=0
  · simp [Tail.Cu,hpz]
  · have he:=Arithmetic.Kz Z₁ Z₂ h₁ h₂ v.val x y z hxy hxz hyz t (ht y hpy) (ht z hpz)
    change -Real.log (v (Z₂ y-Z₂ z)) = -Real.log (v (Z₁ y-Z₁ z)) -
      -Real.log (v (Z₁ x-Z₁ z)) - Real.log (v t) - -Real.log (v (Z₁ x-Z₁ y)) at he
    suffices (finite Z₁ h₁ v).value y z-(finite Z₁ h₁ v).value x z-
      ((finite Z₂ h₂ v).value y z+c)=0 by rw [this,abs_zero,mul_zero]
    simp only [finite,if_neg hyz,if_neg hxz,c]
    linarith
omit [NumberField K] in
lemma FO (v:NumberField.InfinitePlace K) (p:P→ ℝ)
    (δ:ℝ) (hpu:Be δ (mass p Finset.univ)=0) (hps:∀ x,Be δ (mass p {x})=0)
    (x y:P) :
    Integrable (fun ω => |distance (arch Z₁ v ω).At ((arch Z₁ v ω).Al (fun C=> Be δ (mass p C))) x y-
      AW (arch Z₂ v ω).At ((arch Z₂ v ω).Al (fun C=> Be δ (mass p C))) y|) Ao.As:=by
  exact ((Depth.EZ (arch Z₁ v) (BA Z₁ h₁ v)
    (AO Z₁ h₁ v) _ hpu hps x y).sub
    (Depth.ER (arch Z₂ v) (BA Z₂ h₂ v)
      (AO Z₂ h₂ v) _ hpu hps y)).abs
variable {I:Type u7} [Fintype I]
omit Z₁ Z₂ h₁ h₂ in
def By (w:I→ ℝ) (p:I→ P→ ℝ) (src:I→ P) (δ:ℝ) (d d':Depth P):ℝ :=
  ∑ i,w i*∑ y,p i y*|distance d.At (d.Al (fun C=> Be δ (mass (p i) C))) (src i) y-
    AW d'.At (d'.Al (fun C=> Be δ (mass (p i) C))) y|
omit [NumberField K] in
lemma En (w:I→ ℝ) (p:I→ P→ ℝ) (src:I→ P)
    (hp:∀ i,∑ z,p i z=1) (δ:ℝ) (hδ:0≤δ) (hps:∀ i z,p i z≤δ) :
    AU Z₁ Z₂ (By w p src δ):=by
  intro v
  apply integrable_finsetSum
  intro i _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro y _
  apply Integrable.const_mul
  exact FO Z₁ Z₂ h₁ h₂ v (p i) δ
    (by simp only [mass,hp]; exact DR (by linarith))
    (fun z=> by simp only [mass,Finset.sum_singleton]; exact BX (hps i z)) (src i) y
lemma Hy (w:I→ ℝ) (p:I→ P→ ℝ) (src:I→ P) (t:I→ K)
    (hw:∀ i,0≤w i) (hW:∑ i,w i=1) (hp0:∀ i z,0≤p i z)
    (hp:∀ i,∑ z,p i z=1) (hpx:∀ i,p i (src i)=0)
    (ht:∀ i z,p i z≠0→(Z₁ (src i)-Z₁ z)*(Z₂ (src i)-Z₂ z)=t i)
    (δ:ℝ) (hδ:0≤δ) (hps:∀ i z,p i z≤δ) :
    average Z₁ Z₂ h₁ h₂ (By w p src δ)≤12:=by
  classical
  have hi (v:NumberField.InfinitePlace K) (i:I) (y:P) :=
    FO Z₁ Z₂ h₁ h₂ v (p i) δ
      (by simp only [mass,hp]; exact DR (by linarith))
      (fun z=> by simp only [mass,Finset.sum_singleton]; exact BX (hps i z)) (src i) y
  have ha (v:NumberField.InfinitePlace K) :
      (∫ ω,By w p src δ (arch Z₁ v ω) (arch Z₂ v ω) ∂Ao.As)≤12:=by
    unfold By
    rw [integral_finsetSum _ (fun i _=>(integrable_finsetSum _ (fun y _=>(hi v i y).const_mul (p i y))).const_mul (w i))]
    simp only [integral_const_mul]
    have he (i:I):(∫ ω,∑ y,p i y*|distance (arch Z₁ v ω).At
        ((arch Z₁ v ω).Al (fun C=> Be δ (mass (p i) C))) (src i) y-
        AW (arch Z₂ v ω).At ((arch Z₂ v ω).Al (fun C=> Be δ (mass (p i) C))) y| ∂Ao.As)≤12:=by
      rw [integral_finsetSum _ (fun y _=>(hi v i y).const_mul (p i y))]
      simp only [integral_const_mul]
      calc
        _≤∑ y,p i y*12:=Finset.sum_le_sum (fun y _=> by
          by_cases hy:p i y=0
          · simp [hy]
          · exact mul_le_mul_of_nonneg_left (RM Z₁ Z₂ h₁ h₂ v (p i) (hp0 i) (hp i)
              (src i) y (hpx i) hy (t i) (ht i) δ hδ (hps i)) (hp0 i y))
        _=12:=by rw [← Finset.sum_mul,hp,one_mul]
    exact (Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (he i) (hw i))).trans_eq
      (by rw [← Finset.sum_mul,hW,one_mul])
  have hv (v:NumberField.FinitePlace K) :
      By w p src δ (finite Z₁ h₁ v) (finite Z₂ h₂ v)≤0:=by
    apply Finset.sum_nonpos
    intro i _
    apply mul_nonpos_of_nonneg_of_nonpos (hw i)
    apply Finset.sum_nonpos
    intro y _
    by_cases hy:p i y=0
    · simp [hy]
    · exact mul_nonpos_of_nonneg_of_nonpos (hp0 i y) (PQ Z₁ Z₂ h₁ h₂ v
        (p i) (hp0 i) (hp i) (src i) y (hpx i) hy (t i) (ht i) δ hδ (hps i))
  change BH (Fq Z₁ Z₂ h₁ h₂) _ _≤12
  have hh:=Gz (Fq Z₁ Z₂ h₁ h₂) ha (fun v _=> hv v)
  rwa [Ev] at hh
end Aa.Bg
noncomputable section
namespace Aa.AV
open MeasureTheory Ak Variance
open scoped BigOperators
variable {P:Type u8} [Fintype P] [DecidableEq P]
lemma Hk (p:P→ ℝ) (hp:∑ x,p x=1) (C:Finset P):mass p Cᶜ=1-mass p C:=by
  have hh:=Finset.sum_compl_add_sum C p
  rw [hp] at hh
  exact eq_sub_of_add_eq hh
omit [Fintype P] [DecidableEq P] in
lemma Mw (p:P→ ℝ) (δ:ℝ) (hδ:0≤δ) (hp:∀ x,p x≤δ)
    (C:Finset P) (hC:C.card≤1):mass p C≤δ:=by
  have hh:=Finset.sum_le_sum (s:=C) (fun x _=> hp x)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  have hc:(C.card:ℝ)≤1:=by exact_mod_cast hC
  exact hh.trans (by nlinarith)
omit [Fintype P] [DecidableEq P] in
lemma Gr (p a:P→ ℝ) (δ:ℝ) (hδ:0≤δ)
    (hp:∀ x,p x≤δ) (ha:∀ x,a x≤δ) (C:Finset P) (hC:C.card≤1) :
    Ck δ (mass p C) (mass a C)=0:=by
  simp only [Ck,BX (Mw p δ hδ hp C hC),
    BX (Mw a δ hδ ha C hC),sub_self,abs_zero,zero_mul,add_zero]
lemma Nx (p a:P→ ℝ) (hp:∑ x,p x=1) (ha:∑ x,a x=1)
    (δ:ℝ) (C:Finset P) :
    Ck δ (mass p Cᶜ) (mass a Cᶜ)=Ck δ (mass p C) (mass a C):=by
  rw [Hk p hp,Hk a ha,Sp]
def Dr (d:Depth P) (δ:ℝ) (p a:P→ ℝ):ℝ :=
  ∑ C∈ d.At,d.Al (fun B=> Ck δ (mass p B) (mass a B)) C
lemma OI (d:Depth P) (hn:2≤Fintype.card P) (δ:ℝ) (hδ:0≤δ)
    (p a:P→ ℝ) (hp:∑ x,p x=1) (ha:∑ x,a x=1)
    (hps:∀ x,p x≤δ) (has:∀ x,a x≤δ) :
    Dr d δ p a=Ac d.mass (fun C=> Ck δ (mass p C) (mass a C)):=by
  symm
  exact d.FA hn _ (Gr p a δ hδ hps has)
    (Nx p a hp ha δ)
omit [DecidableEq P] in
lemma BC (p:P→ ℝ) (hp:∑ x,p x=1) (δ:ℝ) (hδ:0≤δ) :
    Be δ (mass p Finset.univ)=0:=by
  simp only [mass,hp]
  exact DR (by linarith)
omit [Fintype P] [DecidableEq P] in
lemma Cg (p:P→ ℝ) (δ:ℝ) (hp:∀ x,p x≤δ) (x:P) :
    Be δ (mass p {x})=0:=by
  simp only [mass,Finset.sum_singleton]
  exact BX (hp x)
end Aa.AV
namespace Aa.Ak.Depth
open AV MeasureTheory
variable {P:Type u9} [Fintype P] [DecidableEq P]
lemma Im (d:Depth P) (f g:Finset P→ ℝ)
    (hf:f Finset.univ=0) (hfs:∀ x,f {x}=0) (hg:g Finset.univ=0) (hgs:∀ x,g {x}=0)
    (hfg:∀ C,f C≤g C) (C:Finset P):d.Al f C≤d.Al g C:=by
  apply integral_mono (d.DJ f hf hfs C) (d.DJ g hg hgs C)
  intro r
  simp only [ET]
  split_ifs
  · exact hfg C
  · rfl
end Aa.Ak.Depth
namespace Aa.AV
open MeasureTheory Ak Variance
variable {P:Type u10} [Fintype P] [DecidableEq P]
lemma Lf (d:Depth P) (δ:ℝ) (hδ:0≤δ) (p a:P→ ℝ)
    (hp:∑ x,p x=1) (ha:∑ x,a x=1) (hps:∀ x,p x≤δ) (has:∀ x,a x≤δ) (x y:P) :
    |distance d.At (d.Al (fun C=> Be δ (mass p C))) x y-
      distance d.At (d.Al (fun C=> Be δ (mass a C))) x y|≤Dr d δ p a:=by
  apply (d.Km _ _ (BC p hp δ hδ) (Cg p δ hps)
    (BC a ha δ hδ) (Cg a δ has) x y).trans
  apply Finset.sum_le_sum
  intro C _
  apply d.Im
  · simp only [BC p hp δ hδ,BC a ha δ hδ,sub_self,abs_zero]
  · intro z; simp only [Cg p δ hps,Cg a δ has,sub_self,abs_zero]
  · simp only [Ck,BC p hp δ hδ,BC a ha δ hδ,sub_self,abs_zero,zero_mul,add_zero]
  · intro z; exact Gr p a δ hδ hps has _ (by simp)
  · intro C; exact le_add_of_nonneg_right (mul_nonneg (Dv _ _) (abs_nonneg _))
lemma NV (d:Depth P) (δ:ℝ) (hδ:0≤δ) (p a:P→ ℝ)
    (hp:∑ x,p x=1) (ha:∑ x,a x=1) (hps:∀ x,p x≤δ) (has:∀ x,a x≤δ) (y:P) :
    |AW d.At (d.Al (fun C=> Be δ (mass p C))) y-
      AW d.At (d.Al (fun C=> Be δ (mass a C))) y|≤Dr d δ p a:=by
  apply (d.Nt _ _ (BC p hp δ hδ) (Cg p δ hps)
    (BC a ha δ hδ) (Cg a δ has) y).trans
  apply Finset.sum_le_sum
  intro C _
  apply d.Im
  · simp only [BC p hp δ hδ,BC a ha δ hδ,sub_self,abs_zero]
  · intro z; simp only [Cg p δ hps,Cg a δ has,sub_self,abs_zero]
  · simp only [Ck,BC p hp δ hδ,BC a ha δ hδ,sub_self,abs_zero,zero_mul,add_zero]
  · intro z; exact Gr p a δ hδ hps has _ (by simp)
  · intro C; exact le_add_of_nonneg_right (mul_nonneg (Dv _ _) (abs_nonneg _))
lemma LL (d:Depth P) (δ:ℝ) (hδ:0≤δ) (p a:P→ ℝ)
    (hp:∑ x,p x=1) (ha:∑ x,a x=1) (hps:∀ x,p x≤δ) (has:∀ x,a x≤δ) :
    CZ d.At (d.Al (fun C=> Be δ (mass a C))) p a≤Dr d δ p a:=by
  rw [d.Pr]
  apply Finset.sum_le_sum
  intro C _
  apply d.Im
  · simp only [BC a ha δ hδ,zero_mul]
  · intro z; simp only [Cg a δ has,zero_mul]
  · simp only [Ck,BC p hp δ hδ,BC a ha δ hδ,sub_self,abs_zero,zero_mul,add_zero]
  · intro z; exact Gr p a δ hδ hps has _ (by simp)
  · intro C; exact le_add_of_nonneg_left (abs_nonneg _)
end Aa.AV
noncomputable section
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4
section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
namespace Aa.AV
open MeasureTheory Ak Variance
open scoped BigOperators
variable {P:Type u1} {I:Type u2} [Fintype P] [DecidableEq P] [Fintype I]
omit [Fintype P] [DecidableEq P] in
lemma Sz (s:Finset (Finset P)) (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤l C)
    (w:I→ ℝ) (p:I→ P→ ℝ) (a:P→ ℝ) (hw:∀ i,0≤w i) (hW:∑ i,w i=1) :
    CZ s l (fun y=>∑ i,w i*p i y) a≤∑ i,w i*CZ s l (p i) a:=by
  have hm (C:Finset P):mass (fun y=>∑ i,w i*p i y) C-mass a C=
      ∑ i,w i*(mass (p i) C-mass a C):=by
    simp only [mass,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hW,one_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  unfold CZ
  simp only [hm]
  calc
    _≤∑ C∈ s,l C*∑ i,w i*|mass (p i) C-mass a C| := by
      apply Finset.sum_le_sum
      intro C hC
      apply mul_le_mul_of_nonneg_left _ (hl C hC)
      convert Finset.abs_sum_le_sum_abs (s:=Finset.univ) (fun i=> w i*(mass (p i) C-mass a C)) using 1
      simp only [abs_mul,abs_of_nonneg (hw _)]
    _= _:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun C _=> by ring))
omit [DecidableEq P] in
lemma QG (p:P→ ℝ) (hp0:∀ x,0≤p x) (hp:∑ x,p x=1) (C:Finset P):mass p C≤1 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _=> hp0 x)).trans_eq hp
omit [DecidableEq P] in
lemma Tv (s:Finset (Finset P)) (l:Finset P→ ℝ) (hl:∀ C∈ s,0≤l C)
    (p a:P→ ℝ) (hp0:∀ x,0≤p x) (ha0:∀ x,0≤a x)
    (hp:∑ x,p x=1) (ha:∑ x,a x=1):CZ s l p a≤∑ C∈ s,l C:=by
  apply Finset.sum_le_sum
  intro C hC
  have hh : |mass p C-mass a C|≤1:=abs_le.mpr ⟨by linarith [Bf p hp0 C,QG a ha0 ha C],
    by linarith [Bf a ha0 C,QG p hp0 hp C]⟩
  simpa using mul_le_mul_of_nonneg_left hh (hl C hC)
lemma KL (d d':Depth P) (δ:ℝ) (hδ:0≤δ) (p a:P→ ℝ)
    (hp:∑ x,p x=1) (ha:∑ x,a x=1) (hps:∀ x,p x≤δ) (has:∀ x,a x≤δ) (x y:P) :
    |distance d.At (d.Al (fun C=> Be δ (mass a C))) x y-
        AW d'.At (d'.Al (fun C=> Be δ (mass a C))) y|≤
      |distance d.At (d.Al (fun C=> Be δ (mass p C))) x y-
        AW d'.At (d'.Al (fun C=> Be δ (mass p C))) y|+
      Dr d δ p a+Dr d' δ p a:=by
  have h1:=Lf d δ hδ p a hp ha hps has x y
  have h2:=NV d' δ hδ p a hp ha hps has y
  let A:=distance d.At (d.Al (fun C=> Be δ (mass a C))) x y
  let B:=AW d'.At (d'.Al (fun C=> Be δ (mass a C))) y
  let C:=distance d.At (d.Al (fun C=> Be δ (mass p C))) x y
  let D:=AW d'.At (d'.Al (fun C=> Be δ (mass p C))) y
  change |C-A|≤Dr d δ p a at h1
  change |D-B|≤Dr d' δ p a at h2
  change |A-B|≤|C-D|+Dr d δ p a+Dr d' δ p a
  have hh1 : |A-B|≤|A-C|+|C-B| := abs_sub_le A C B
  have hh2 : |C-B|≤|C-D|+|D-B| := abs_sub_le C D B
  have hh3 : |A-C|=|C-A| := abs_sub_comm A C
  rw [hh3] at hh1
  linarith only [hh1,hh2,h1,h2]
lemma Gm (d:Depth P) (hn:2≤Fintype.card P) (w:I→ ℝ)
    (B:I→ Finset P) (hB:∀ i,(B i).Nonempty) (δ:ℝ) (hδ:0≤δ)
    (hp:∀ i x,Ae (B i) x≤δ) (ha:∀ x,Ae (Finset.univ:Finset P) x≤δ) :
    (∑ i,w i*Dr d δ (Ae (B i)) (Ae Finset.univ))=
      Ac d.mass (Bl w B δ):=by
  have ha1:∑ x,Ae (Finset.univ:Finset P) x=1:=Bs _ (by
    apply Finset.univ_nonempty_iff.mpr
    exact Fintype.card_pos_iff.mp (by omega))
  simp only [OI d hn δ hδ _ _ (Bs _ (hB _)) ha1 (hp _) ha]
  simp only [Ac,Finset.mul_sum,Bl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro i _
  simp only [mass,Ci]
  ring
lemma SQ (d d':Depth P) (δ:ℝ) (hδ:0≤δ)
    (a t:P→ ℝ) (ρ:P→ P→ ℝ) (w:I→ ℝ) (p:I→ P→ ℝ) (src:I→ P)
    (ha0:∀ x,0≤a x) (ht0:∀ y,0≤t y) (hρ0:∀ y x,0≤ρ y x) (hw:∀ i,0≤w i)
    (ha:∑ x,a x=1) (ht:∑ y,t y=1) (hρ:∀ y,∑ x,ρ y x=1) (hW:∑ i,w i=1)
    (hp:∀ i,∑ y,p i y=1) (hp0:∀ i y,0≤p i y)
    (has:∀ x,a x≤δ) (hps:∀ i x,p i x≤δ)
    (htm:t=fun y=>∑ i,w i*p i y)
    (hedge:∀ F:P→ P→ ℝ,(∑ y,t y*∑ x,ρ y x*F x y)=∑ i,w i*∑ y,p i y*F (src i) y) :
    δ^3*(∑ C∈ d.At,d.Al (fun B=> Be δ (mass a B)) C)≤
      2*Bg.By w p src δ d d'+
      4*(∑ i,w i*Dr d δ (p i) a)+2*(∑ i,w i*Dr d' δ (p i) a)+
      2*(∑ y,t y*CZ d.At (d.Al (fun B=> Be δ (mass a B))) (ρ y) a):=by
  let l:=d.Al (fun B=> Be δ (mass a B))
  have hl (C) (_:C∈d.At):0≤l C:=d.El _ (fun C=> Dv _ _) C
  have hlow:=d.Ln a ha0 ha (Be δ) (Dv δ) δ hδ (fun u hn=> by
    apply le_antisymm _ (Dv δ u)
    by_contra hh
    have hu:=MI (lt_of_not_ge hh)
    exact hn ⟨hu.1.le,by linarith [hu.2]⟩)
  have hupper:=SH d.At d.KH l hl a t ρ ha0 ht0 hρ0 ha ht hρ
    (AW d'.At (d'.Al (fun B=> Be δ (mass a B))))
  rw [hedge] at hupper
  have hproj:(∑ i,w i*∑ y,p i y*
      |distance d.At l (src i) y-AW d'.At (d'.Al (fun B=> Be δ (mass a B))) y|)≤
      Bg.By w p src δ d d'+∑ i,w i*Dr d δ (p i) a+∑ i,w i*Dr d' δ (p i) a:=by
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=> mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s:=Finset.univ) (fun y _=> mul_le_mul_of_nonneg_left
        (KL d d' δ hδ (p i) a (hp i) ha (hps i) has (src i) y) (hp0 i y))) (hw i))
    simpa only [Bg.By,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hp,one_mul,l] using hh
  have hcost:CZ d.At l t a≤∑ i,w i*Dr d δ (p i) a:=by
    rw [htm]
    exact (Sz d.At l hl w p a hw hW).trans (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (LL d δ hδ (p i) a (hp i) ha (hps i) has) (hw i)))
  dsimp only [l] at hupper hproj hcost
  linarith
end Aa.AV
noncomputable section
namespace Aa.Core.Au
open MeasureTheory Ak Variance AV
open scoped BigOperators
variable {V:Type u3} {I:Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G:Au V I)
omit [Fintype V] in
lemma DK (B:Finset V) (x:V):0≤Ae B x:=by
  unfold Ae
  split_ifs <;> positivity
def AY (y:V):V→ ℝ :=
  if (G.BV y).Nonempty then Ae (G.BV y) else Ae Finset.univ
omit [Fintype I] in
lemma Ep (y x:V):0≤G.AY y x:=by
  unfold AY
  split_ifs <;> exact DK _ _
omit [Fintype I] in
lemma Fb (hn:2≤Fintype.card V) (y:V):∑ x,G.AY y x=1:=by
  unfold AY
  split_ifs with h
  · exact Bs _ h
  · exact Bs _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
omit [Fintype I] in
lemma Cs (y:V):0≤G.Ax y:=by unfold Ax Ap; positivity
omit [Fintype I] in
lemma Ht (y x:V):G.Ax y*G.AY y x=G.Av x y:=by
  by_cases h:(G.BV y).Nonempty
  · simpa only [AY,if_pos h] using G.GB x y
  · have he:G.BV y=∅:=Finset.not_nonempty_iff_eq_empty.mp h
    have hh:=G.GB x y
    have hw:G.Ax y=0:=by simp [Ax,he]
    simp only [hw,zero_mul] at hh ⊢
    exact hh
lemma IV (F:V→ V→ ℝ) :
    (∑ y,G.Ax y*∑ x,G.AY y x*F x y)=
      ∑ e,G.Af e*∑ y,Ae (G.targets e) y*F (G.source e) y:=by
  simp only [Finset.mul_sum,← mul_assoc,G.Ht,← G.Gq,Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext y
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro y _
  simp only [ite_mul,zero_mul]
  simp
lemma Sh:G.Ax=fun y=>∑ e,G.Af e*Ae (G.targets e) y:=by
  funext y
  rw [G.Ir,G.GF]
def BF (T:ℝ):ℝ:=∑ y,if ((G.BV y).card:ℝ)<T then G.Ax y else 0
omit [Fintype I] in
lemma Ov (T:ℝ):0≤G.BF T:=by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact G.Cs y
  · rfl
omit [Fintype I] in
lemma Se (d:Depth V) (δ T:ℝ) (hδ:0≤δ) (hT:0<T)
    (has:∀ x,Ae (Finset.univ:Finset V) x≤δ)
    (hrs:∀ y x,Ae (G.Aw T y) x≤δ)
    (hrn:∀ y,(G.Aw T y).Nonempty) (hn:2≤Fintype.card V) :
    (∑ y,G.Ax y*CZ d.At (d.Al (fun B=> Be δ (mass (Ae Finset.univ) B)))
      (G.AY y) (Ae Finset.univ))≤
      (∑ y,G.Ay T y*Dr d δ (Ae (G.Aw T y)) (Ae Finset.univ))+
      G.BF T*(∑ C∈ d.At,d.Al (fun B=> Be δ (mass (Ae Finset.univ) B)) C):=by
  have ha:∑ x,Ae (Finset.univ:Finset V) x=1 :=
    Bs _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
  unfold BF
  rw [Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  by_cases hs:T≤((G.BV y).card:ℝ)
  · have hy:(G.BV y).Nonempty:=Finset.card_pos.mp (by exact_mod_cast hT.trans_le hs)
    have he:G.Aw T y=G.BV y:=by simp only [Aw,if_pos hs]
    have hh:=LL d δ hδ (Ae (G.Aw T y)) (Ae Finset.univ)
      (Bs _ (hrn y)) ha (hrs y) has
    simp only [he] at hh
    simpa only [Ay,if_pos hs,AY,if_pos hy,not_lt_of_ge hs,ite_false,zero_mul,add_zero,he]
      using mul_le_mul_of_nonneg_left hh (G.Cs y)
  · have hh:=Tv d.At (d.Al (fun B=> Be δ (mass (Ae Finset.univ) B)))
      (fun C _=> d.El _ (fun B=> Dv _ _) C)
      (G.AY y) (Ae Finset.univ) (G.Ep y) (DK _)
      (G.Fb hn y) ha
    simpa only [Ay,if_neg hs,lt_of_not_ge hs,ite_true,zero_mul,zero_add] using
      mul_le_mul_of_nonneg_left hh (G.Cs y)
lemma IA (d d':Depth V) (δ T:ℝ) (hδ:0≤δ) (hT:0<T)
    (hn:2≤Fintype.card V) (hG:0<G.Ap)
    (has:∀ x,Ae (Finset.univ:Finset V) x≤δ)
    (hps:∀ e x,Ae (G.targets e) x≤δ) (hpn:∀ e,(G.targets e).Nonempty)
    (hrs:∀ y x,Ae (G.Aw T y) x≤δ) (hrn:∀ y,(G.Aw T y).Nonempty) :
    δ^3*(∑ C∈ d.At,d.Al (fun B=> Be δ (mass (Ae Finset.univ) B)) C)≤
      2*Bg.By G.Af (fun e=> Ae (G.targets e)) G.source δ d d'+
      4*(∑ e,G.Af e*Dr d δ (Ae (G.targets e)) (Ae Finset.univ))+
      2*(∑ e,G.Af e*Dr d' δ (Ae (G.targets e)) (Ae Finset.univ))+
      2*(∑ y,G.Ay T y*Dr d δ (Ae (G.Aw T y)) (Ae Finset.univ))+
      2*G.BF T*(∑ C∈ d.At,d.Al (fun B=> Be δ (mass (Ae Finset.univ) B)) C):=by
  have ha:∑ x,Ae (Finset.univ:Finset V) x=1 :=
    Bs _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
  have hh:=SQ d d' δ hδ (Ae Finset.univ) G.Ax G.AY G.Af
    (fun e=> Ae (G.targets e)) G.source (DK _) G.Cs G.Ep
    G.AT ha (G.IL hG) (G.Fb hn) (G.Bz hG)
    (fun e=> Bs _ (hpn e)) (fun e=> DK _) has hps G.Sh G.IV
  have hc:=G.Se d δ T hδ hT has hrs hrn hn
  linarith
end Aa.Core.Au
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23
section
namespace Aa.Ak.Depth
open MeasureTheory
variable {P:Type u1} [Fintype P] [DecidableEq P]
variable (d:Depth P)
lemma PY (r:ℝ) (C:Finset P) (hC:C∈ d.transformed r) :
    2*C.card≤Fintype.card P:=by
  rw [transformed,Multiset.mem_add] at hC
  rcases hC with hC | hC
  · exact Nat.le_of_not_gt (Finset.mem_filter.mp hC).2
  · obtain ⟨B,hB,hBC⟩:=Multiset.mem_map.mp hC
    have hh:=(d.CY r B).mp hB
    subst C
    rw [Finset.card_compl]
    have:=Finset.card_le_univ B
    omega
lemma TC (C:Finset P) (hC:Fintype.card P<2*C.card):d.mass C=0:=by
  have hz (r:ℝ):d.count r C=0:=by
    unfold count
    have hh:C∉ d.transformed r:=fun hc=> hC.not_ge (d.PY r C hc)
    simp [Multiset.count_eq_zero.mpr hh]
  simp [mass,hz]
end Aa.Ak.Depth
namespace Aa.Bg
open Ak
variable {P:Type u2} [Fintype P] [DecidableEq P]
variable {K:Type u3} [Field K] [NumberField K]
variable (Z:P→ K) (hZ:Function.Injective Z)
lemma Sc (C:Finset P) (hC:Fintype.card P<2*C.card):CD Z hZ C=0:=by
  simp only [CD,Depth.TC _ C hC,MeasureTheory.integral_zero,mul_zero,Finset.sum_const_zero,add_zero]
lemma RD (Z₂:P→ K) (h₂:Function.Injective Z₂)
    (C:Finset P) (hC:1/2<Variance.Ad Finset.univ C) :
    totalMass Z Z₂ hZ h₂ C=0:=by
  have hn0:(0:ℝ)<Fintype.card P:=by
    by_contra! hn
    have hz:Fintype.card P=0:=by exact_mod_cast (le_antisymm hn (Nat.cast_nonneg _))
    simp [Variance.Ad,hz] at hC
    linarith
  have hh:Fintype.card P<2*C.card:=by
    simp only [Variance.Ad,Finset.univ_inter,Finset.card_univ] at hC
    have hl:=(lt_div_iff₀ hn0).mp hC
    exact_mod_cast (show (Fintype.card P:ℝ)<2*C.card by linarith)
  simp only [totalMass,Sc _ _ C hh,add_zero]
end Aa.Bg
namespace Aa.Variance
open scoped BigOperators
open AV AL
variable {P:Type u4} {I:Type u5} [Fintype P] [Fintype I] [DecidableEq P]
omit [Fintype P] in
lemma Mj (w:I→ ℝ) (B:I→ Finset P) (src:I→ P) (lam:ℝ)
    (hw:∀ i,0≤w i) (C:Finset P):0≤ slice w (fun i=> Ae (B i)) src lam C:=by
  unfold slice
  exact Finset.sum_nonneg (fun i _=> mul_nonneg (hw i) (by
    split_ifs
    · simp only [AL.mass,Ci]; exact Bd _ _
    · exact le_rfl))
omit [Fintype P] in
lemma Rd (w:I→ ℝ) (B:I→ Finset P) (src:I→ P)
    (hw:∀ i,0≤w i) (hW:(∑ i,w i)≤1) (C:Finset P) :
    Cl w (fun i=> Ae (B i)) src C≤1:=by
  rw [Ej]
  apply le_trans _ hW
  apply Finset.sum_le_sum
  intro i _
  by_cases hi:src i∈ C
  · simp only [if_pos hi,AL.mass,Ci]
    nlinarith [mul_le_mul_of_nonneg_left (Dy (B i) C) (hw i)]
  · simp [hi,hw i]
lemma Kh (m:Finset P→ ℝ) (hm:∀ C,0≤ m C)
    (hhalf:∀ C,1/2<Ad Finset.univ C→ m C=0)
    (w:I→ ℝ) (B:I→ Finset P) (src:I→ P) (T δ:ℝ)
    (hw:∀ i,0≤w i) (hW:(∑ i,w i)≤1) (hδ:0<δ) (_hδ4:δ≤1/4)
    (hk:∀ i,2/((B i).card:ℝ)≤4*δ) :
    Ac m (Cl w (fun i=> Ae (B i)) src)≤
      Ac m (slice w (fun i=> Ae (B i)) src (4*δ))+
      (1/δ)*Ac m (Aj w B T)+
      (1/δ)*Ac m (fun C=> Be δ (Ad Finset.univ C)):=by
  have hpoint (C:Finset P) :
      m C*Cl w (fun i=> Ae (B i)) src C ≤
        m C*(slice w (fun i=> Ae (B i)) src (4*δ) C+
          (1/δ)*Aj w B T C+(1/δ)*Be δ (Ad Finset.univ C)):=by
    by_cases hh:1/2<Ad Finset.univ C
    · rw [hhalf C hh]; simp
    have ha:Ad Finset.univ C≤1/2:=le_of_not_gt hh
    apply mul_le_mul_of_nonneg_left _ (hm C)
    by_cases hs:Ad Finset.univ C≤2*δ
    · have hx:=Qd (B:=B) src T (2*δ) hw (by positivity) (fun i=> by nlinarith [hk i]) C hs
      have he:(∑ i,w i*(if src i∈ C then Ad (B i) C else 0)) =
          Cl w (fun i=> Ae (B i)) src C:=by
        rw [Ej]; simp only [AL.mass,Ci]
      have hf:(∑ i,w i*(if src i∈ C∧ Ad (B i) C<2*(2*δ) then Ad (B i) C else 0)) =
          slice w (fun i=> Ae (B i)) src (4*δ) C:=by
        unfold slice
        simp only [AL.mass,Ci,show (2:ℝ)*(2*δ)=4*δ by ring]
      rw [he,hf,show (2:ℝ)/(2*δ)=1/δ by ring] at hx
      exact hx.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) (Dv _ _)))
    · have htent:δ≤Be δ (Ad Finset.univ C):=Tq (le_of_not_ge hs) (by linarith)
      have hh:1≤(1/δ)*Be δ (Ad Finset.univ C):=by
        have:=mul_le_mul_of_nonneg_left htent (show 0≤1/δ by positivity)
        simpa [ne_of_gt hδ] using this
      have he:=(Rd w B src hw hW C).trans hh
      have hn:=Mj w B src (4*δ) hw C
      have hv:=mul_nonneg (show 0≤1/δ by positivity) (Bw w B T hw C)
      linarith
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun C _=> hpoint C)
  change Ac m (Cl w (fun i=> Ae (B i)) src)≤_ at hh
  convert hh using 1
  simp only [Ac,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  have hcomm (f:Finset P→ ℝ) :
      (1/δ)*∑ C,m C* f C=∑ C,m C*((1/δ)*f C):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    ring
  simp only [Finset.mul_sum] at hcomm
  rw [hcomm,hcomm]
end Aa.Variance
namespace Aa
open Filter Variance Bg AV
open scoped Topology BigOperators
lemma Gy (W A X:ℕ→ ℝ) (C:ℝ) (hC:0<C)
    (hW:∀ j,0≤W j) (hA:∀ j,0≤A j) (hX:∀ j,0≤X j)
    (hWtop:Tendsto W atTop atTop)
    (hcomp:∀ᶠ j in atTop,A j≤C*(W j+1))
    (hrate:Tendsto (fun j=> X j/(W j+A j+1)) atTop (𝓝 0)) :
    Tendsto (fun j=> X j/W j) atTop (𝓝 0):=by
  have hb:∀ᶠ j in atTop,X j/W j≤(2+2*C)*(X j/(W j+A j+1)):=by
    filter_upwards [hWtop.eventually (eventually_ge_atTop (1:ℝ)),hcomp] with j hj hc
    have hw:0<W j:=by linarith
    have hd:0<W j+A j+1:=by linarith [hA j]
    apply (div_le_iff₀ hw).mpr
    have hbound:W j+A j+1≤(2+2*C)*W j:=by nlinarith
    have hh:=mul_le_mul_of_nonneg_left hbound (hX j)
    convert (div_le_div_of_nonneg_right hh hd.le) using 1 <;> field_simp
  exact squeeze_zero' (Eventually.of_forall (fun j=> div_nonneg (hX j) (hW j))) hb
    (by simpa using hrate.const_mul (2+2*C))
lemma JC (W A V L Q S a:ℕ→ ℝ) (C δ b:ℝ)
    (hC:0<C) (hδ:0<δ) (hb:0≤b) (hbC:2*b*C≤1/8)
    (hW:∀ j,0≤W j) (hA:∀ j,0≤A j) (hV:∀ j,0≤V j)
    (hWtop:Tendsto W atTop atTop)
    (hcomp:∀ᶠ j in atTop,A j≤C*(W j+1))
    (ha:Tendsto a atTop (𝓝 0))
    (hvar:Tendsto (fun j=> V j/(W j+A j+1)) atTop (𝓝 0))
    (hQ:∀ᶠ j in atTop,W j-a j*A j≤Q j)
    (hS:∀ᶠ j in atTop,S j≤W j/8+b*A j+32)
    (hext:∀ᶠ j in atTop,Q j≤S j+V j/δ+L j/δ) :
    ∀ᶠ j in atTop,(δ/4)*W j≤L j:=by
  have hv:=Gy W A V C hC hW hA hV hWtop hcomp hvar
  have ha0:Tendsto (fun j => |a j|) atTop (𝓝 0):=by simpa using ha.abs
  filter_upwards [hWtop.eventually (eventually_ge_atTop (256:ℝ)),hcomp,
    ha0.eventually (gt_mem_nhds (show 0<1/(8*C) by positivity)),
    hv.eventually (gt_mem_nhds (show 0<δ/8 by positivity)),hQ,hS,hext] with j hw hc ha hv hq hs he
  have hw0:0<W j:=by linarith
  have hac:A j≤2*C*W j:=by nlinarith
  have ha':a j*A j≤W j/4:=by
    have hh:=mul_le_mul_of_nonneg_right (le_trans (le_abs_self (a j)) ha.le) (hA j)
    have hh':=mul_le_mul_of_nonneg_left hac (show 0≤1/(8*C) by positivity)
    have hz:(1/(8*C))*(2*C*W j)=W j/4:=by field_simp; ring
    rw [hz] at hh'
    exact hh.trans hh'
  have hbA:b*A j≤W j/8:=by
    have h1:=mul_le_mul_of_nonneg_left hac hb
    have h2:=mul_le_mul_of_nonneg_right hbC hw0.le
    nlinarith
  have hv':V j/δ≤W j/8:=by
    have hh:=(div_lt_iff₀ hw0).mp hv
    apply (div_le_iff₀ hδ).mpr
    nlinarith
  have hL:W j/4≤L j/δ:=by linarith
  have:=(le_div_iff₀ hδ).mp hL
  nlinarith
end Aa
noncomputable section
namespace Aa.AV
open Ak Variance
variable {P:Type u9} [Fintype P] [DecidableEq P]
lemma Li (d:Depth P) (hn:2≤Fintype.card P) (δ:ℝ) (hδ:0≤δ)
    (has:∀ x,Ae (Finset.univ:Finset P) x≤δ) :
    (∑ C∈ d.At,d.Al (fun B=> Be δ (mass (Ae Finset.univ) B)) C)=
      Ac d.mass (fun C=> Be δ (Ad Finset.univ C)):=by
  have ha:∑ x,Ae (Finset.univ:Finset P) x=1 :=
    Bs _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
  symm
  simp only [← Ci]
  change Ac d.mass (fun C=> Be δ (mass (Ae Finset.univ) C))=_
  exact d.FA hn _ (fun C hC=> BX (Mw _ δ hδ has C hC))
    (fun C=> by rw [Hk _ ha,IN])
end Aa.AV
namespace Aa.Bg
open Ak Variance AV MeasureTheory
open scoped BigOperators
variable {P:Type u10} [Fintype P] [DecidableEq P]
variable {K:Type u11} [Field K] [NumberField K]
variable (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
lemma Sw (f:Depth P→ Depth P→ ℝ) :
    average Z₂ Z₁ h₂ h₁ f=average Z₁ Z₂ h₁ h₂ (fun d d'=> f d' d):=by
  classical
  unfold average Fq
  rw [Finset.union_comm (Bq Z₂ h₂)]
omit [NumberField K] in
include h₁ in
lemma Gb (hn:2≤Fintype.card P) (f:Finset P→ ℝ) :
    AU Z₁ Z₂ (fun d _=> Ac d.mass f):=by
  intro v
  apply integrable_finsetSum
  intro C _
  exact (Dw Z₁ Z₂ h₁ hn C v).mul_const (f C)
omit [NumberField K] in
include h₂ in
lemma FN (hn:2≤Fintype.card P) (f:Finset P→ ℝ) :
    AU Z₁ Z₂ (fun _ d'=> Ac d'.mass f):=by
  intro v
  apply integrable_finsetSum
  intro C _
  exact (Dn Z₁ Z₂ h₂ hn C v).mul_const (f C)
lemma LU (hn:2≤Fintype.card P) (f:Finset P→ ℝ) :
    average Z₁ Z₂ h₁ h₂ (fun d _=> Ac d.mass f)=Ac (CD Z₁ h₁) f:=by
  simp only [Ac,mul_comm _ (f _)]
  rw [Iu Z₁ Z₂ h₁ h₂ _ (fun C v=>(Dw Z₁ Z₂ h₁ hn C v).const_mul (f C))]
  simp_rw [FE,Jl Z₁ Z₂ h₁ h₂ hn]
lemma KU (hn:2≤Fintype.card P) (f:Finset P→ ℝ) :
    average Z₁ Z₂ h₁ h₂ (fun _ d'=> Ac d'.mass f)=Ac (CD Z₂ h₂) f:=by
  simp only [Ac,mul_comm _ (f _)]
  rw [Iu Z₁ Z₂ h₁ h₂ _ (fun C v=>(Dn Z₁ Z₂ h₂ hn C v).const_mul (f C))]
  simp_rw [FE,IG Z₁ Z₂ h₁ h₂ hn]
def CP (f:Finset P→ ℝ) (d d':Depth P):ℝ :=
  Ac d.mass f+Ac d'.mass f
omit [NumberField K] in
include h₁ h₂ in
lemma Ea (hn:2≤Fintype.card P) (f:Finset P→ ℝ) :
    AU Z₁ Z₂ (CP f):=fun v =>
  (Gb Z₁ Z₂ h₁ hn f v).add (FN Z₁ Z₂ h₂ hn f v)
lemma KO (hn:2≤Fintype.card P) (f:Finset P→ ℝ) :
    average Z₁ Z₂ h₁ h₂ (CP f)=Ac (totalMass Z₁ Z₂ h₁ h₂) f:=by
  change average Z₁ Z₂ h₁ h₂ (fun d d'=> Ac d.mass f+Ac d'.mass f)=_
  rw [Di Z₁ Z₂ h₁ h₂ (Gb Z₁ Z₂ h₁ hn f)
    (FN Z₁ Z₂ h₂ hn f),LU Z₁ Z₂ h₁ h₂ hn,
    KU Z₁ Z₂ h₁ h₂ hn]
  simp only [Ac,totalMass,add_mul,Finset.sum_add_distrib]
end Aa.Bg
namespace Aa.Core.Au
open Ak Variance AV Bg
variable {V:Type u12} {I:Type u13} [Fintype V] [Fintype I] [DecidableEq V]
variable (G:Au V I)
lemma Pt (d d':Depth V) (δ T:ℝ) (hδ:0≤δ) (hT:0<T)
    (hn:2≤Fintype.card V) (hG:0<G.Ap)
    (has:∀ x,Ae (Finset.univ:Finset V) x≤δ)
    (hps:∀ e x,Ae (G.targets e) x≤δ) (hpn:∀ e,(G.targets e).Nonempty)
    (hrs:∀ y x,Ae (G.Aw T y) x≤δ) (hrn:∀ y,(G.Aw T y).Nonempty) :
    δ^3*CP (fun C=> Be δ (Ad Finset.univ C)) d d'≤
      2*(By G.Af (fun e=> Ae (G.targets e)) G.source δ d d'+
        By G.Af (fun e=> Ae (G.targets e)) G.source δ d' d)+
      6*CP (Bl G.Af G.targets δ) d d'+
      2*CP (Bl (G.Ay T) (G.Aw T) δ) d d'+
      2*G.BF T*CP (fun C=> Be δ (Ad Finset.univ C)) d d':=by
  have h1:=G.IA d d' δ T hδ hT hn hG has hps hpn hrs hrn
  have h2:=G.IA d' d δ T hδ hT hn hG has hps hpn hrs hrn
  simp only [Li _ hn δ hδ has,
    Gm _ hn G.Af G.targets hpn δ hδ hps has,
    Gm _ hn (G.Ay T) (G.Aw T) hrn δ hδ hrs has] at h1 h2
  dsimp only [CP]
  linarith
end Aa.Core.Au
namespace Aa.Bg
open Ak Variance AV MeasureTheory
variable {V:Type u14} {I:Type u15} [Fintype V] [Fintype I] [DecidableEq V]
variable {K:Type u16} [Field K] [NumberField K]
variable (G:Core.Au V I) (Z₁ Z₂:V→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
lemma Ko (t:I→ K) (ht:∀ e y,y∈G.targets e →
      (Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e)
    (δ T:ℝ) (hδ:0≤δ) (hT:0<T) (hn:2≤Fintype.card V) (hG:0<G.Ap)
    (has:∀ x,Ae (Finset.univ:Finset V) x≤δ)
    (hps:∀ e x,Ae (G.targets e) x≤δ) (hpn:∀ e,(G.targets e).Nonempty)
    (hrs:∀ y x,Ae (G.Aw T y) x≤δ) (hrn:∀ y,(G.Aw T y).Nonempty) :
    δ^3*Ac (totalMass Z₁ Z₂ h₁ h₂) (fun C=> Be δ (Ad Finset.univ C))≤
      48+6*Ac (totalMass Z₁ Z₂ h₁ h₂) (Bl G.Af G.targets δ)+
      2*Ac (totalMass Z₁ Z₂ h₁ h₂) (Bl (G.Ay T) (G.Aw T) δ)+
      2*G.BF T*Ac (totalMass Z₁ Z₂ h₁ h₂) (fun C=> Be δ (Ad Finset.univ C)):=by
  have hL:=Ea Z₁ Z₂ h₁ h₂ hn (fun C=> Be δ (Ad Finset.univ C))
  have hF:=Ea Z₁ Z₂ h₁ h₂ hn (Bl G.Af G.targets δ)
  have hR:=Ea Z₁ Z₂ h₁ h₂ hn (Bl (G.Ay T) (G.Aw T) δ)
  have hp:=fun e=> Bs (G.targets e) (hpn e)
  have hD:=En Z₁ Z₂ h₁ h₂ G.Af (fun e=> Ae (G.targets e)) G.source hp δ hδ hps
  have hD':=En Z₂ Z₁ h₂ h₁ G.Af (fun e=> Ae (G.targets e)) G.source hp δ hδ hps
  have hh:=SI Z₁ Z₂ h₁ h₂ (fun v=>(hL v).const_mul (δ^3))
    (fun v=>(((((hD v).add (hD' v)).const_mul 2).add ((hF v).const_mul 6)).add
      ((hR v).const_mul 2)).add ((hL v).const_mul (2*G.BF T)))
    (fun d d'=> G.Pt d d' δ T hδ hT hn hG has hps hpn hrs hrn)
  rw [Di Z₁ Z₂ h₁ h₂
    (fun v=>((((hD v).add (hD' v)).const_mul 2).add ((hF v).const_mul 6)).add ((hR v).const_mul 2))
    (fun v=>(hL v).const_mul (2*G.BF T))] at hh
  rw [Di Z₁ Z₂ h₁ h₂
    (fun v=>(((hD v).add (hD' v)).const_mul 2).add ((hF v).const_mul 6))
    (fun v=>(hR v).const_mul 2)] at hh
  rw [Di Z₁ Z₂ h₁ h₂
    (fun v=>((hD v).add (hD' v)).const_mul 2) (fun v=>(hF v).const_mul 6)] at hh
  simp only [FE] at hh
  have hpx (e):Ae (G.targets e) (G.source e)=0:=by simp [Ae,G.OE e]
  have hte (e) (z) (hz:Ae (G.targets e) z≠0) :
      (Z₁ (G.source e)-Z₁ z)*(Z₂ (G.source e)-Z₂ z)=t e:=by
    apply ht
    by_contra h
    exact hz (by simp [Ae,h])
  have hd:=Hy Z₁ Z₂ h₁ h₂ G.Af (fun e=> Ae (G.targets e)) G.source t
    G.AT (G.Bz hG) (fun e=> Core.Au.DK (G.targets e)) hp hpx hte δ hδ hps
  have hd':=Hy Z₂ Z₁ h₂ h₁ G.Af (fun e=> Ae (G.targets e)) G.source t
    G.AT (G.Bz hG) (fun e=> Core.Au.DK (G.targets e)) hp hpx
    (fun e z hz=> by rw [mul_comm]; exact hte e z hz) δ hδ hps
  rw [Sw] at hd'
  rw [Di Z₁ Z₂ h₁ h₂ hD (fun v=> hD' v)] at hh
  simp only [KO Z₁ Z₂ h₁ h₂ hn] at hh
  linarith
end Aa.Bg
noncomputable section
namespace Aa
open Filter Variance Core.Au
open scoped Topology
variable {V:Type u17} {I:Type u18} [Fintype V] [Fintype I] [DecidableEq V]
omit [Fintype V] in
lemma FZ (B:Finset V) (δ:ℝ) (hδ:0<δ) (hB:1/δ≤(B.card:ℝ)) :
    B.Nonempty∧∀ x,Ae B x≤δ:=by
  have hb:0<(B.card:ℝ):=(one_div_pos.mpr hδ).trans_le hB
  refine ⟨Finset.card_pos.mp (by exact_mod_cast hb),?_⟩
  intro x
  unfold Ae
  split_ifs
  · exact (div_le_iff₀ hb).mpr (by have:=(div_le_iff₀ hδ).mp hB; nlinarith)
  · exact hδ.le
lemma AJ.Sd {G:Core.Au V I} {θ γ c η:ℝ}
    (hG:AJ V I G θ γ c η) (hθ:0<θ) (hη:η≤θ/2) :
    G.BF ((Fintype.card V:ℝ)^γ)≤(4/θ)*(Fintype.card V:ℝ)^(γ-1):=by
  let n:ℝ:=Fintype.card V
  have hn:2≤n:=by dsimp only [n]; exact_mod_cast hG.Cz
  have hn0:0<n:=by linarith
  have hE:=hG.CR (by linarith)
  have hEl:(θ/4)*n^2≤G.Ap:=by
    have hp:0≤(n-1)*n:=mul_nonneg (by linarith) hn0.le
    have hh:=mul_nonneg (show 0≤θ-η-θ/2 by linarith) hp
    have hh':=mul_nonneg (show 0≤θ/4 by positivity) (show 0≤n*(n-2) by positivity)
    dsimp [n] at *
    nlinarith [hG.lower]
  apply (G.Nj _ (Real.rpow_nonneg hn0.le γ)).trans
  change n*n^γ/G.Ap≤(4/θ)*n^(γ-1)
  rw [Real.rpow_sub hn0,Real.rpow_one]
  apply (div_le_iff₀ hE).mpr
  have hh:=mul_le_mul_of_nonneg_left hEl (show 0≤(4/θ)*(n^γ/n) by positivity)
  have he:(4/θ)*(n^γ/n)*((θ/4)*n^2)=n*n^γ:=by field_simp
  rw [he] at hh
  exact hh
variable {Vn:ℕ→ Type u19} {In:ℕ→ Type u20} [∀ j,Fintype (Vn j)] [∀ j,Fintype (In j)] [∀ j,DecidableEq (Vn j)]
lemma Of (G:∀ j,Core.Au (Vn j) (In j)) (θ γ c:ℝ) (η:ℕ→ ℝ)
    (hθ:0<θ) (hγ1:γ<1) (hη:∀ j,η j≤θ/2)
    (hn:Tendsto (fun j=>(Fintype.card (Vn j):ℝ)) atTop atTop)
    (hG:∀ j,AJ (Vn j) (In j) (G j) θ γ c (η j)) :
    Tendsto (fun j=>(G j).BF ((Fintype.card (Vn j):ℝ)^γ)) atTop (𝓝 0):=by
  apply squeeze_zero (fun j=>(G j).Ov _) (fun j=>(hG j).Sd hθ (hη j))
  have hh:=(tendsto_rpow_neg_atTop (show 0<1-γ by linarith)).comp hn
  have he : -(1-γ)=γ-1:=by ring
  rw [he] at hh
  simpa using hh.const_mul (4/θ)
lemma JA (G:∀ j,Core.Au (Vn j) (In j)) (θ γ c:ℝ) (η:ℕ→ ℝ)
    (γ0:0<γ) (γ1:γ<1) (δ:ℝ) (hδ:0<δ)
    (hn:Tendsto (fun j=>(Fintype.card (Vn j):ℝ)) atTop atTop)
    (hG:∀ j,AJ (Vn j) (In j) (G j) θ γ c (η j)) :
    ∀ᶠ j in atTop,
      (∀ x,Ae (Finset.univ:Finset (Vn j)) x≤δ) ∧
      (∀ e,((G j).targets e).Nonempty)∧(∀ e x,Ae ((G j).targets e) x≤δ) ∧
      (∀ y,((G j).Aw ((Fintype.card (Vn j):ℝ)^γ) y).Nonempty) ∧
      (∀ y x,Ae ((G j).Aw ((Fintype.card (Vn j):ℝ)^γ) y) x≤δ):=by
  have hpow:=(tendsto_rpow_atTop γ0).comp hn
  filter_upwards [hn.eventually (eventually_ge_atTop (1/δ)),hpow.eventually (eventually_ge_atTop (1/δ))] with j hnδ hnγ
  have hn1:(1:ℝ)≤Fintype.card (Vn j):=by exact_mod_cast (show 1≤Fintype.card (Vn j) by have:=(hG j).Cz; omega)
  have hs:(Fintype.card (Vn j):ℝ)^γ≤Fintype.card (Vn j):=by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 γ1.le
  have hf (e):=FZ ((G j).targets e) δ hδ (hnγ.trans ((hG j).fiber e).le)
  have hr (y):=FZ ((G j).Aw ((Fintype.card (Vn j):ℝ)^γ) y) δ hδ
    (hnγ.trans ((G j).Ft _ hs y))
  exact ⟨(FZ Finset.univ δ hδ (by simpa using hnδ)).2,
    fun e=>(hf e).1,fun e=>(hf e).2,fun y=>(hr y).1,fun y=>(hr y).2⟩
end Aa
noncomputable section
namespace Aa
open Filter Variance Bg AV
open scoped Topology BigOperators
lemma Js (W F R L o:ℕ→ ℝ) (δ b:ℝ) (hδ:0<δ) (hb:0<b)
    (hW:Tendsto W atTop atTop)
    (hF:Tendsto (fun j=> F j/W j) atTop (𝓝 0))
    (hR:Tendsto (fun j=> R j/W j) atTop (𝓝 0))
    (ho:Tendsto o atTop (𝓝 0))
    (hlow:∀ᶠ j in atTop,b*W j≤L j)
    (hupp:∀ᶠ j in atTop,δ^3*L j≤48+6*F j+2*R j+2*o j*L j):False:=by
  have h48:Tendsto (fun j=>(48:ℝ)/W j) atTop (𝓝 0):=by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using (tendsto_inv_atTop_zero.comp hW).const_mul 48
  have he:Tendsto (fun j=>(48+6*F j+2*R j)/W j) atTop (𝓝 0):=by
    convert (h48.add (hF.const_mul 6)).add (hR.const_mul 2) using 1
    · ext j; ring
    · norm_num
  have hbound:=ho.eventually (gt_mem_nhds (show 0<δ^3/4 by positivity))
  have hsmall:=he.eventually (gt_mem_nhds (show 0<δ^3*b/2 by positivity))
  obtain ⟨j,hjW,hjo,hje,hjl,hju⟩:=(hW.eventually (eventually_gt_atTop (0:ℝ)) |>.and
    (hbound.and (hsmall.and (hlow.and hupp)))).exists
  have hl0:0<L j:=(mul_pos hb hjW).trans_le hjl
  have hopen:=mul_le_mul_of_nonneg_right hjo.le hl0.le
  have he':=(div_lt_iff₀ hjW).mp hje
  have hl':=mul_le_mul_of_nonneg_left hjl (show 0≤δ^3/2 by positivity)
  nlinarith
end Aa
end
end
end
end
end AA
namespace AA
universe u1 u2 u3
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace Aa.Bounded
lemma Rg {J:Type u1} [Fintype J] (w T V:J→ ℝ) (C ε:ℝ)
    (hw:∀ j,0< w j) (hW:∑ j,w j=1)
    (hT:∀ j,0≤ T j) (hV:∀ j,0≤ V j)
    (hC:0≤ C) (hε:0< ε)
    (hTC:∑ j,w j* T j≤ C) (hVE:∑ j,w j* V j≤ ε) :
    ∃ j,T j≤2*C+1∧ V j≤2*ε:=by
  have hne:(Finset.univ:Finset J).Nonempty:=by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty] at hW
    norm_num at hW
  have hs:∑ j,w j*(T j+(C+1)/ε*V j)≤∑ j,w j*(2*C+1):=by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul]
    rw [hW,one_mul]
    have hv:=mul_le_mul_of_nonneg_left hVE (show 0≤(C+1)/ε by positivity)
    have he:(∑ j,w j*((C+1)/ε*V j))=(C+1)/ε*(∑ j,w j*V j):=by
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    rw [he]
    have he':(C+1)/ε*ε=C+1:=by field_simp
    rw [he'] at hv
    linarith
  obtain ⟨j,_,hj⟩:=Finset.exists_le_of_sum_le hne hs
  have hj':T j+(C+1)/ε*V j≤2*C+1:=(mul_le_mul_iff_right₀ (hw j)).mp hj
  refine ⟨j,(le_add_of_nonneg_right (mul_nonneg (by positivity) (hV j))).trans hj',?_⟩
  have hv':(C+1)/ε*V j≤2*C+1:=by linarith [hT j]
  have he:(C+1)/ε*(2*ε)=2*(C+1):=by field_simp
  by_contra h
  have hh:=mul_lt_mul_of_pos_left (lt_of_not_ge h) (show 0<(C+1)/ε by positivity)
  rw [he] at hh
  linarith
end Aa.Bounded
namespace Aa.Bounded
open Ak Variance Bg NumberField
variable {P:Type u2} [Fintype P] [DecidableEq P]
variable {K:Type u3} [Field K] [NumberField K]
variable (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
omit Z₁ Z₂ h₁ h₂ in
lemma EH (q:Finset P→ ℝ) (hq:∀ C,0≤q C) (d d':Depth P) :
    0≤ Bm q d d':=by
  exact add_nonneg (Finset.sum_nonneg (fun C _=> mul_nonneg (d.Bf C) (hq C)))
    (Finset.sum_nonneg (fun C _=> mul_nonneg (d'.Bf C) (hq C)))
omit Z₁ Z₂ h₁ h₂ in
def CA (d d':Depth P):ℝ :=
  Bm (Ah Finset.univ) d d'+ Co (Ae Finset.univ) d d'
omit Z₁ Z₂ h₁ h₂ in
lemma JT (d d':Depth P):0≤ CA d d':=by
  apply add_nonneg (EH _ (fun C=> BJ _ _) _ _)
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (add_nonneg (d.BM x) (d'.BM x))
  simp only [Ae,Finset.mem_univ,ite_true]; positivity
omit [NumberField K] in
include h₁ h₂ in
lemma Hv (hn:2≤Fintype.card P) :
    AU Z₁ Z₂ (CA (P:=P)):=by
  intro v
  exact (Cm Z₁ Z₂ h₁ h₂ hn _ v).add
    (DA Z₁ Z₂ h₁ h₂ hn _ v)
lemma Pb (hn:2≤Fintype.card P) :
    average Z₁ Z₂ h₁ h₂ CA= AQ Z₁ Z₂ h₁ h₂+ AG Z₁ Z₂ h₁ h₂:=by
  unfold CA
  rw [Di Z₁ Z₂ h₁ h₂
    (Cm Z₁ Z₂ h₁ h₂ hn _) (DA Z₁ Z₂ h₁ h₂ hn _),
    Hc Z₁ Z₂ h₁ h₂ hn,EY Z₁ Z₂ h₁ h₂ hn]
  rfl
def BD (f:Depth P→ Depth P→ ℝ) (v:InfinitePlace K):ℝ :=
  ∫ ω,f (arch Z₁ v ω) (arch Z₂ v ω) ∂ Ao.As
omit [Fintype P] [NumberField K] in
lemma FQ (f:Depth P→ Depth P→ ℝ) (hf:∀ d d',0≤f d d')
    (v:InfinitePlace K):0≤BD Z₁ Z₂ f v:=integral_nonneg (fun _=> hf _ _)
lemma HV (f:Depth P→ Depth P→ ℝ) (hf:∀ d d',0≤f d d') :
    (∑ v,Arithmetic.Bh v* BD Z₁ Z₂ f v)≤ average Z₁ Z₂ h₁ h₂ f:=by
  apply le_add_of_nonneg_right
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _=> hf _ _))
omit Z₁ Z₂ h₁ h₂ in
lemma Rj (v:InfinitePlace K):0<Arithmetic.Bh v:=by
  unfold Arithmetic.Bh
  apply div_pos
  · exact_mod_cast (InfinitePlace.mult_pos (w:=v))
  · exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)
lemma Tc (hn:2≤Fintype.card P) (q:Finset P→ ℝ) (hq:∀ C,0≤q C)
    (C ε:ℝ) (hC:0≤C) (hε:0<ε)
    (hscale:AQ Z₁ Z₂ h₁ h₂+ AG Z₁ Z₂ h₁ h₂≤ C)
    (hvar:Ac (totalMass Z₁ Z₂ h₁ h₂) q≤ ε) :
    ∃ v:InfinitePlace K,
      BD Z₁ Z₂ CA v≤2*C+1∧ BD Z₁ Z₂ (Bm q) v≤2*ε:=by
  apply Rg Arithmetic.Bh _ _ C ε Rj Arithmetic.Il
    (FQ Z₁ Z₂ _ JT)
    (FQ Z₁ Z₂ _ (EH q hq)) hC hε
  · exact (HV Z₁ Z₂ h₁ h₂ _ JT).trans
      (by rw [Pb Z₁ Z₂ h₁ h₂ hn]; exact hscale)
  · exact (HV Z₁ Z₂ h₁ h₂ _ (EH q hq)).trans
      (by rw [Hc Z₁ Z₂ h₁ h₂ hn]; exact hvar)
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6
section
noncomputable section
open scoped BigOperators
namespace Aa.Bounded
variable {P:Type u1} [Fintype P] [DecidableEq P]
def CV (u:P→ ℂ) (x y:P):ℝ :=
  if x=y then 0 else |Real.log ‖u x-u y‖|
def Dl (u:P→ ℂ):ℝ :=
  (∑ x,∑ y,CV u x y)/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))
omit [Fintype P] in
lemma Ii (u:P→ ℂ) (x y:P):0≤ CV u x y:=by
  unfold CV; split_ifs <;> positivity
lemma Hn (u:P→ ℂ) (C:ℝ) (hn:2≤ Fintype.card P)
    (hC:Dl u≤ C) :
    (∑ x,∑ y,CV u x y)≤ C*(Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1):=by
  have hnR:(2:ℝ)≤ Fintype.card P:=by exact_mod_cast hn
  have hp:0<(Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1):=mul_pos (by linarith) (by linarith)
  simpa only [mul_assoc] using (div_le_iff₀ hp).mp hC
lemma Jf (u:P→ ℂ) (hn:2≤ Fintype.card P):0≤ Dl u:=by
  have hnR:(2:ℝ)≤ Fintype.card P:=by exact_mod_cast hn
  exact div_nonneg (Finset.sum_nonneg (fun _ _=> Finset.sum_nonneg (fun _ _=> Ii _ _ _))) (mul_nonneg (by linarith) (by linarith))
lemma Qy (u:P→ ℂ) (C:ℝ) (hn:2≤ Fintype.card P) (hC:Dl u≤ C) :
    ∃ x:P,(∑ y,CV u x y)≤ C*(Fintype.card P:ℝ):=by
  have hnR:(2:ℝ)≤ Fintype.card P:=by exact_mod_cast hn
  have hC0:0≤ C:=(Jf u hn).trans hC
  have hsum:=Hn u C hn hC
  by_contra hnot
  push Not at hnot
  have hpos:Finset.univ.Nonempty (α:=P):=Finset.card_pos.mp (by simpa using (show 0<Fintype.card P by omega))
  have hs:=Finset.sum_lt_sum_of_nonempty hpos (fun x _=> hnot x)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  nlinarith
omit [Fintype P] in
lemma Ry (u:P→ ℂ) (R:ℝ) (hR:1< R) (x y:P) (hxy:R<‖u x-u y‖) :
    Real.log R≤ CV u x y:=by
  have hne:x≠ y:=by intro he; subst y; simp at hxy; linarith
  rw [CV,if_neg hne]
  have hl:=Real.log_le_log (by linarith:0<R) hxy.le
  exact hl.trans (le_abs_self _)
lemma MB (u:P→ ℂ) (C:ℝ) (x:P)
    (hx:(∑ y,CV u x y)≤ C*(Fintype.card P:ℝ))
    (hn:2≤ Fintype.card P) (R:ℝ) (hR:1< R) :
    ((Finset.univ.filter (fun y=> R<‖u y-u x‖)).card:ℝ)/(Fintype.card P:ℝ)≤ C/Real.log R:=by
  let A:=Finset.univ.filter (fun y=> R<‖u y-u x‖)
  have hlog:=Real.log_pos hR
  have hn0:(0:ℝ)<Fintype.card P:=by exact_mod_cast (show 0<Fintype.card P by omega)
  have hs:(A.card:ℝ)*Real.log R≤∑ y,CV u x y:=by
    calc
      (A.card:ℝ)*Real.log R=∑ y∈ A,Real.log R:=by simp
      _≤∑ y∈ A,CV u x y:=by
        apply Finset.sum_le_sum
        intro y hy
        apply Ry u R hR x y
        simpa only [norm_sub_rev] using (Finset.mem_filter.mp hy).2
      _≤∑ y,CV u x y:=Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun y _ _=> Ii u x y)
  apply (div_le_div_iff₀ hn0 hlog).mpr
  nlinarith
omit [Fintype P] in
lemma Rl (u:P→ ℂ) (hu:Function.Injective u) (z:ℂ) (r:ℝ)
    (_hr:0<r) (_hr2:r<1/2) (x y:P) (hx:‖u x-z‖<r) (hy:‖u y-z‖<r) (hxy:x≠y) :
    -Real.log (2*r)≤ CV u x y:=by
  have hne:u x-u y≠0:=sub_ne_zero.mpr (fun h=> hxy (hu h))
  have hp:=norm_pos_iff.mpr hne
  have hd:‖u x-u y‖<2*r:=by
    have hh:=norm_sub_le_norm_sub_add_norm_sub (u x) z (u y)
    rw [norm_sub_rev z] at hh
    linarith
  have hh:=Real.log_le_log hp hd.le
  rw [CV,if_neg hxy]
  have habs:=neg_le_abs (Real.log ‖u x-u y‖)
  linarith
lemma Qt (u:P→ ℂ) (hu:Function.Injective u) (C:ℝ)
    (hn:2≤ Fintype.card P) (hC:Dl u≤ C) (z:ℂ) (r:ℝ)
    (hr:0<r) (hr2:r<1/2) :
    (((Finset.univ.filter (fun x=>‖u x-z‖<r)).card:ℝ)/(Fintype.card P:ℝ))^2 ≤
      1/(Fintype.card P:ℝ)+C/(-Real.log (2*r)):=by
  let A:=Finset.univ.filter (fun x=>‖u x-z‖<r)
  let T := -Real.log (2*r)
  have hT:0<T:=by dsimp [T]; exact neg_pos.mpr (Real.log_neg (by positivity) (by linarith))
  have hnR:(2:ℝ)≤ Fintype.card P:=by exact_mod_cast hn
  have hn0:(0:ℝ)<Fintype.card P:=by linarith
  have hC0:0≤ C:=(Jf u hn).trans hC
  have ha:(A.card:ℝ)≤ Fintype.card P:=by exact_mod_cast Finset.card_le_univ A
  have ha0:(0:ℝ)≤ A.card:=Nat.cast_nonneg _
  have hsum:=Hn u C hn hC
  have hpoint:∀ x y:P,(if x∈A∧ y∈A∧ x≠y then T else 0)≤ CV u x y:=by
    intro x y
    split_ifs with h
    · exact Rl u hu z r hr hr2 x y (Finset.mem_filter.mp h.1).2
        (Finset.mem_filter.mp h.2.1).2 h.2.2
    · exact Ii _ _ _
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun y _=> hpoint x y))
  have heq:(∑ x:P,∑ y:P,if x∈A∧ y∈A∧ x≠y then T else 0) =
      (A.card:ℝ)*((A.card:ℝ)-1)*T:=by
    have hrw (x:P):(∑ y:P,if x∈A∧ y∈A∧ x≠y then T else 0) =
        if x∈A then ((A.card:ℝ)-1)*T else 0:=by
      by_cases hx:x∈A
      · simp only [hx,true_and,if_pos]
        have hf:Finset.univ.filter (fun y=> y∈A∧ x≠y)=A.erase x:=by
          ext y; simp [ne_comm,and_comm]
        rw [← Finset.sum_filter,hf,Finset.sum_const,Finset.card_erase_of_mem hx,nsmul_eq_mul]
        rw [Nat.cast_sub (Finset.one_le_card.mpr ⟨x,hx⟩),Nat.cast_one]
      · simp [hx]
    simp_rw [hrw]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
    ring
  rw [heq] at hs
  have hcub:(A.card:ℝ)^2*T≤(Fintype.card P:ℝ)*T+C*(Fintype.card P:ℝ)^2:=by
    have hCT:=mul_nonneg hC0 hn0.le
    have hAT:=mul_le_mul_of_nonneg_right ha hT.le
    nlinarith
  change ((A.card:ℝ)/(Fintype.card P:ℝ))^2≤1/(Fintype.card P:ℝ)+C/T
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
  apply (mul_le_mul_iff_left₀ hT).mp
  have he:(1/(Fintype.card P:ℝ)+C/T)*(Fintype.card P:ℝ)^2*T =
      (Fintype.card P:ℝ)*T+C*(Fintype.card P:ℝ)^2:=by field_simp [ne_of_gt hn0,ne_of_gt hT]
  rw [he]
  exact hcub
end Aa.Bounded
namespace Aa.Bounded
open Ak Variance Bg NumberField MeasureTheory
open scoped BigOperators
lemma Od {J:Type u2} [Fintype J] (p f:J→ ℝ) (a:ℝ)
    (hp:∀ j,0≤ p j) (hs:∑ j,p j=1) :
    (∑ j,p j*|f j-∑ k,p k*f k|)≤2*∑ j,p j*|f j-a| := by
  have hm : |a-∑ j,p j*f j| ≤ ∑ j,p j*|f j-a| := by
    have he:a-(∑ j,p j*f j)=∑ j,p j*(a-f j):=by
      simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul]
    rw [he]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul,abs_of_nonneg (hp j),abs_sub_comm]
  calc
    _≤∑ j,p j*(|f j-a|+|a-∑ k,p k*f k|):=by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (abs_sub_le (f j) a _) (hp j)
    _=(∑ j,p j*|f j-a|)+|a-∑ k,p k*f k| := by simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul]
    _≤ _:=by linarith
variable {P:Type u3} [Fintype P] [DecidableEq P]
def AK (f:P→ P→ ℝ):ℝ:=∑ x,∑ y,Az Finset.univ x y* f x y
lemma GJ (hn:2≤ Fintype.card P) (x y:P):0≤ Az Finset.univ x y:=by
  have hn':(2:ℝ)≤ Fintype.card P:=by exact_mod_cast hn
  simp only [Az,Finset.mem_univ,true_and,Finset.card_univ]
  split_ifs
  · exact div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))
  · exact le_rfl
lemma NB (hn:2≤ Fintype.card P):AK (fun _ _:P=>1)=1:=by
  simp only [AK,mul_one,Cp Finset.univ (by simpa using hn)]
  apply Bs
  exact Finset.card_pos.mp (by simpa using (show 0<Fintype.card P by omega))
lemma Ja (hn:2≤ Fintype.card P) {f g:P→ P→ ℝ}
    (h:∀ x y,x≠y→ f x y≤ g x y):AK f≤ AK g:=by
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  by_cases hxy:x=y
  · subst y; simp [Az]
  · exact mul_le_mul_of_nonneg_left (h x y hxy) (GJ hn x y)
lemma Kc (f g:P→ P→ ℝ):AK (fun x y=> f x y+g x y)=AK f+AK g:=by
  simp only [AK,mul_add,Finset.sum_add_distrib]
lemma Sq (hn:2≤ Fintype.card P) (f:P→ ℝ) :
    AK (fun x _=> f x)=∑ x,Ae Finset.univ x*f x:=by
  simp only [AK,← Finset.sum_mul,Cp Finset.univ (by simpa using hn)]
lemma RB (hn:2≤ Fintype.card P) (f:P→ ℝ) :
    AK (fun _ y=> f y)=∑ y,Ae Finset.univ y*f y:=by
  rw [AK,Finset.sum_comm]
  simp_rw [Ex Finset.univ _ _,← Finset.sum_mul,Cp Finset.univ (by simpa using hn)]
lemma NW (hn:2≤ Fintype.card P) (f:P→ P→ ℝ) (a:ℝ) :
    AK (fun x y => |f x y-AK f|)≤2*AK (fun x y => |f x y-a|):=by
  have h:=Od (fun z:P×P=> Az Finset.univ z.1 z.2)
    (fun z=> f z.1 z.2) a (fun z=> GJ hn z.1 z.2)
    (by simpa only [Fintype.sum_prod_type,AK,mul_one] using NB (P:=P) hn)
  simpa only [Fintype.sum_prod_type,AK] using h
lemma PS (d:Depth P) (_hn:2≤ Fintype.card P) :
    AK (AD d.mass)=Ac d.mass (Ah Finset.univ):=by
  exact (IT d.mass (Az Finset.univ)).symm
lemma NY (d:Depth P) (hn:2≤ Fintype.card P) :
    AK (fun x y => |d.value x y-d.M|)≤ Ac d.mass (Ah Finset.univ)+
      2*(∑ x,Ae Finset.univ x*d.Ag x):=by
  calc
    _≤ AK (fun x y=> AD d.mass x y+d.Ag x+d.Ag y):=by
      apply Ja hn
      intro x y hxy
      rw [show AD d.mass x y=d.AN x y hxy from d.Gh hn x y hxy,
        d.Eg hn x y hxy]
      have hL:=d.Fl x y hxy
      have hx:=d.BM x
      have hy:=d.BM y
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    _= _:=by rw [Kc,Kc,PS d hn,Sq hn,RB hn]; ring
end Aa.Bounded
namespace Aa.Bounded
open Ak Variance Bg NumberField MeasureTheory
open scoped BigOperators
variable {P:Type u4} [Fintype P] [DecidableEq P]
def EM (d:Depth P):ℝ :=
  Ac d.mass (Ah Finset.univ)+∑ x,Ae Finset.univ x*d.Ag x
lemma OA (d:Depth P):0≤ EM d:=by
  refine add_nonneg (Finset.sum_nonneg (fun C _=> mul_nonneg (d.Bf C) (BJ _ _))) ?_
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (d.BM x)
  simp only [Ae,Finset.mem_univ,ite_true]; positivity
lemma SC (d d':Depth P):CA d d'=EM d+EM d':=by
  simp only [CA,EM,Bm,Co,mul_add,Finset.sum_add_distrib]; ring
lemma Nr (d d':Depth P):EM d≤ CA d d':=by
  rw [SC]; exact le_add_of_nonneg_right (OA d')
def Cd (u:P→ ℂ) (x y:P):ℝ := -Real.log ‖u x-u y‖
def BZ (u:P→ ℂ) (ω:Ao.AS) (x y:P):ℝ :=
  if x=y then 0 else |Ao.error ω (u x) (u y)|
lemma LN (u:P→ ℂ) (d:Depth P) (ω:Ao.AS)
    (hn:2≤ Fintype.card P) (hd:∀ x y,x≠y→ d.value x y=Ao.depth ω (u x) (u y)) :
    AK (fun x y => |Cd u x y-AK (Cd u)|) ≤
      4*EM d+2*AK (BZ u ω):=by
  have h1:=NW hn (Cd u) d.M
  have h2:AK (fun x y => |Cd u x y-d.M|) ≤
      AK (fun x y => |d.value x y-d.M|)+AK (BZ u ω):=by
    rw [← Kc]
    apply Ja hn
    intro x y hxy
    simp only [BZ,if_neg hxy]
    have he:Cd u x y-d.M=(d.value x y-d.M)-Ao.error ω (u x) (u y):=by
      rw [hd x y hxy]; simp only [Cd,Ao.error]; ring
    rw [he]
    exact abs_sub _ _
  have h3:=NY d hn
  have hL:0≤ Ac d.mass (Ah Finset.univ) :=
    Finset.sum_nonneg (fun C _=> mul_nonneg (d.Bf C) (BJ _ _))
  unfold EM
  linarith
lemma Gf (u:P→ ℂ) (hu:Function.Injective u) :
    Integrable (fun ω=> AK (BZ u ω)) Ao.As:=by
  apply integrable_finsetSum
  intro x _
  apply integrable_finsetSum
  intro y _
  by_cases hxy:x=y
  · simp only [BZ,hxy,ite_true,mul_zero]; exact integrable_zero _ _ _
  · simpa only [BZ,if_neg hxy] using
      ((Ao.Bn (hu.ne hxy)).abs.const_mul (Az Finset.univ x y))
lemma On (u:P→ ℂ) (hu:Function.Injective u) (hn:2≤ Fintype.card P) :
    (∫ ω,AK (BZ u ω) ∂ Ao.As)≤4:=by
  have hi (x y:P):Integrable (fun ω=> Az Finset.univ x y*BZ u ω x y) Ao.As:=by
    by_cases hxy:x=y
    · simp only [BZ,hxy,ite_true,mul_zero]; exact integrable_zero _ _ _
    · simpa only [BZ,if_neg hxy] using
        ((Ao.Bn (hu.ne hxy)).abs.const_mul (Az Finset.univ x y))
  simp only [AK]
  rw [integral_finsetSum _ (fun x _=> integrable_finsetSum _ (fun y _=> hi x y))]
  simp_rw [integral_finsetSum _ (fun y _=> hi _ y),integral_const_mul]
  calc
    _≤∑ x,∑ y,Az Finset.univ x y*4:=by
      apply Finset.sum_le_sum; intro x _
      apply Finset.sum_le_sum; intro y _
      apply mul_le_mul_of_nonneg_left _ (GJ hn x y)
      by_cases hxy:x=y
      · simp only [BZ,hxy,ite_true,integral_zero]; norm_num
      · simpa only [BZ,if_neg hxy] using Ao.Es (hu.ne hxy)
    _=4:=by
      have h:=NB (P:=P) hn
      simp only [AK,mul_one] at h
      simp only [← Finset.sum_mul,h,one_mul]
variable {K:Type u5} [Field K] [NumberField K]
variable (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
omit [NumberField K] in
include h₁ h₂ in
lemma Hi (hn:2≤ Fintype.card P) (v:InfinitePlace K) :
    AK (fun x y => |Cd (fun x=> v.embedding (Z₁ x)) x y-
      AK (Cd (fun x=> v.embedding (Z₁ x)))|)≤4*BD Z₁ Z₂ CA v+8:=by
  let u:P→ ℂ:=fun x=> v.embedding (Z₁ x)
  let L:=AK (fun x y => |Cd u x y-AK (Cd u)|)
  have hu:Function.Injective u:=v.embedding.injective.comp h₁
  have he:=On u hu hn
  have hbound:∀ᵐ ω ∂ Ao.As,L≤4*CA (arch Z₁ v ω) (arch Z₂ v ω)+2*AK (BZ u ω):=by
    filter_upwards [Rr Z₁ h₁ v] with ω hgood
    have h:=LN u (arch Z₁ v ω) ω hn (fun x y hxy=> by simp [arch,hgood,hxy,u])
    have hs:=Nr (arch Z₁ v ω) (arch Z₂ v ω)
    dsimp only [L]
    linarith
  have hh:=integral_mono_ae (integrable_const L)
    (((Hv Z₁ Z₂ h₁ h₂ hn v).const_mul 4).add ((Gf u hu).const_mul 2)) hbound
  simp only [Pi.add_apply] at hh
  rw [integral_add ((Hv Z₁ Z₂ h₁ h₂ hn v).const_mul 4)
    ((Gf u hu).const_mul 2),integral_const_mul,integral_const_mul] at hh
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul] at hh
  change L≤4*BD Z₁ Z₂ CA v+8
  change L≤4*BD Z₁ Z₂ CA v+2*(∫ ω,AK (BZ u ω) ∂ Ao.As) at hh
  linarith
end Aa.Bounded
namespace Aa.Bounded
open Variance
variable {P:Type u6} [Fintype P] [DecidableEq P]
def CN (u:P→ ℂ) (x:P):ℂ:=(Real.exp (AK (Cd u)):ℂ)*u x
lemma GK (u:P→ ℂ) (hu:Function.Injective u) :
    Function.Injective (CN u):=by
  intro x y h
  apply hu
  exact mul_left_cancel₀ (by exact_mod_cast (Real.exp_ne_zero (AK (Cd u)))) h
lemma Nq (u:P→ ℂ) :
    Dl u=AK (fun x y => |Real.log ‖u x-u y‖|):=by
  unfold Dl AK
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  by_cases hxy:x=y
  · simp [Az,CV,hxy]
  · simp [Az,CV,hxy,div_eq_mul_inv,mul_comm]
lemma PI (u:P→ ℂ) (hu:Function.Injective u) (x y:P) (hxy:x≠y) :
    Real.log ‖CN u x-CN u y‖=AK (Cd u)+Real.log ‖u x-u y‖:=by
  have hz:‖u x-u y‖≠0:=norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hu.ne hxy))
  simp only [CN,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [Real.log_mul (Real.exp_ne_zero _) hz,Real.log_exp]
lemma IB (u:P→ ℂ) (hu:Function.Injective u) (hn:2≤Fintype.card P) :
    Dl (CN u)=AK (fun x y => |Cd u x y-AK (Cd u)|):=by
  rw [Nq]
  apply le_antisymm
  all_goals
    apply Ja hn
    intro x y hxy
    rw [PI u hu x y hxy]
    have he : |AK (Cd u)+Real.log ‖u x-u y‖|=|Cd u x y-AK (Cd u)| := by rw [← abs_neg]; congr 1; unfold Cd; ring
    rw [he]
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3 u4
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace Aa.Bounded
local instance (p:Prop):Decidable p:=Classical.propDecidable p
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
variable {V:Type u1} {X:Type u2} [Fintype V] [MeasurableSpace X] [MeasurableSingletonClass X]
def Bv (U:V→ X):Measure X:=AM (fun _=>(Fintype.card V:ℝ)⁻¹) U
omit [MeasurableSingletonClass X] in
lemma Lm (U:V→ X) (hn:0<Fintype.card V):IsProbabilityMeasure (Bv U):=by
  apply DS
  · intro; positivity
  · simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hn.ne')
def Bj (U:V→ X) (hn:0<Fintype.card V):ProbabilityMeasure X :=
  ⟨Bv U,Lm U hn⟩
lemma JH (U:V→ X) (s:Set X) [DecidablePred (fun x=> U x∈s)] :
    Bv U s=ENNReal.ofReal (((Finset.univ.filter (fun x=> U x∈s)).card:ℝ)/(Fintype.card V:ℝ)):=by
  simp only [Bv,AM,Measure.finsetSum_apply,Measure.smul_apply,
    smul_eq_mul,Measure.dirac_apply,Set.indicator_apply,Pi.one_apply,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rw [div_eq_mul_inv,ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
variable {P:ℕ→ Type u4} [∀ n,Fintype (P n)] [∀ n,DecidableEq (P n)]
lemma EE (u:∀ n,P n→ ℂ) (x:∀ n,P n)
    (hu:∀ n,Function.Injective (u n)) (hn:∀ n,2≤Fintype.card (P n))
    (hcard:Tendsto (fun n=>(Fintype.card (P n):ℝ)) atTop atTop)
    (C:ℝ) (hC:0≤C) (hlog:∀ n,Dl (u n)≤C)
    (hx:∀ n,(∑ y,CV (u n) (x n) y)≤C*(Fintype.card (P n):ℝ))
    (β:ProbabilityMeasure Sphere)
    (ht:Tendsto (fun n=> Bj (fun y=>((u n y-u n (x n)):Sphere))
      (by have:=hn n; omega)) atTop (𝓝 β)) :
    NullSingletonClass (β:Measure Sphere):=by
  apply MC ht
  · intro ε hε
    let R:=Real.exp (C/ε+1)
    have hR:1<R:=by dsimp [R]; rw [Real.one_lt_exp_iff]; positivity
    refine ⟨R,Eventually.of_forall (fun n => ?_)⟩
    change Bv (fun y=>((u n y-u n (x n)):Sphere)) _≤_
    rw [JH]
    apply ENNReal.ofReal_le_ofReal
    have hh:=MB (u n) C (x n) (hx n) (hn n) R hR
    have hs:(Finset.univ.filter (fun y=>(((u n y-u n (x n)):Sphere))∈
        (OnePoint.some '' Metric.closedBall (0:ℂ) R)ᶜ))=
        Finset.univ.filter (fun y=> R<‖u n y-u n (x n)‖):=by
      ext y
      simp [Metric.mem_closedBall,dist_eq_norm]
    change (((Finset.univ.filter (fun y=>(((u n y-u n (x n)):Sphere))∈
      (OnePoint.some '' Metric.closedBall (0:ℂ) R)ᶜ)).card:ℝ)/(Fintype.card (P n):ℝ))≤ε
    rw [hs]
    apply hh.trans
    rw [show Real.log R=C/ε+1 by simp [R]]
    apply (div_le_iff₀ (by positivity:0<C/ε+1)).mpr
    have he:ε*(C/ε+1)=C+ε:=by field_simp
    rw [he]
    linarith
  · intro z ε hε
    let T:=2*C/ε^2+1
    let r:=Real.exp (-T)/2
    have hT:0<T:=by dsimp [T]; positivity
    have hr:0<r:=by dsimp [r]; positivity
    have hr2:r<1/2:=by dsimp [r]; have hh:=Real.exp_lt_one_iff.mpr (neg_neg_of_pos hT); linarith
    have hsmall:Tendsto (fun n=>1/(Fintype.card (P n):ℝ)) atTop (𝓝 0):=by simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp hcard)
    have hsmall':∀ᶠ n in atTop,1/(Fintype.card (P n):ℝ)≤ε^2/2 :=
      hsmall.eventually_le_const (by positivity)
    refine ⟨r,hr,hsmall'.mono (fun n hn' => ?_)⟩
    change Bv (fun y=>((u n y-u n (x n)):Sphere)) _≤_
    rw [JH]
    apply ENNReal.ofReal_le_ofReal
    have hs:(Finset.univ.filter (fun y=>(((u n y-u n (x n)):Sphere))∈
        OnePoint.some '' Metric.ball z r))=
        Finset.univ.filter (fun y=>‖u n y-(z+u n (x n))‖<r):=by
      ext y
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_image,OnePoint.coe_eq_coe,exists_eq_right,
        Metric.mem_ball,dist_eq_norm]
      ring_nf
    rw [hs]
    have hh:=Qt (u n) (hu n) C (hn n) (hlog n) (z+u n (x n)) r hr hr2
    have hl : -Real.log (2*r)=T:=by
      rw [show 2*r=Real.exp (-T) by dsimp [r]; ring,Real.log_exp,neg_neg]
    rw [hl] at hh
    have hCT:C/T≤ε^2/2:=by
      apply (div_le_iff₀ hT).mpr
      have he:ε^2/2*T=C+ε^2/2:=by dsimp [T]; field_simp
      rw [he]
      linarith [sq_nonneg ε]
    nlinarith
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Aa.Bounded
variable {I:Type u1} {V:Type u2} {X:Type u3} {Y:Type u4} [Fintype I] [Fintype V]
  [MeasurableSpace X] [MeasurableSpace Y]
lemma RJ (w:I→ ℝ) (p:I→ V→ ℝ) (U:I × V→ X)
    (hw:∀ i,0≤w i) (hp:∀ i x,0≤p i x) (hpsum:∀ i,∑ x,p i x=1) :
    AM (BT w p) (fun r=> U (r.1,r.2.1))=AM (BU w p) U:=by
  unfold AM BT BU
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  rw [show (∑ z,∑ t,ENNReal.ofReal (w i*p i x*p i z*p i t)• Measure.dirac (U (i,x))) =
    ∑ z,ENNReal.ofReal (w i*p i x*p i z)• Measure.dirac (U (i,x)) by
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg (fun t _=> mul_nonneg (mul_nonneg (mul_nonneg (hw i) (hp i x)) (hp i z)) (hp i t)),
        ← Finset.mul_sum,hpsum,mul_one]]
  rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg (fun z _=> mul_nonneg (mul_nonneg (hw i) (hp i x)) (hp i z)),
    ← Finset.mul_sum,hpsum,mul_one]
lemma RA (w v:I→ ℝ) (U:I→ X) (hle:∀ i,w i≤v i) :
    AM w U≤AM v U:=by
  apply Measure.le_iff.mpr
  intro s hs
  simp only [AM,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  apply Finset.sum_le_sum
  intro i _
  gcongr
  exact hle i
lemma Rt (w:I→ ℝ) (v:V→ ℝ) (U:I→ X) (W:V→ Y)
    (hw:∀ i,0≤w i) :
    (AM w U).prod (AM v W)=
      AM (fun r:I × V=> w r.1*v r.2) (fun r=>(U r.1,W r.2)):=by
  simp only [AM,← Measure.sum_fintype,Measure.prod_sum,
    Measure.prod_smul_left,Measure.prod_smul_right,Measure.dirac_prod_dirac,
    smul_smul,ENNReal.ofReal_mul (hw _),mul_comm]
lemma RG (w:I→ ℝ) (U:I→ X) (c:ℝ) (hc:0≤c) :
    AM (fun i=> c*w i) U=ENNReal.ofReal c •AM w U:=by
  simp only [AM,ENNReal.ofReal_mul hc,Finset.smul_sum,smul_smul]
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Aa.Bounded
open Variance
variable {V:Type u5} {I:Type u6} {X:Type u7} [Fintype V] [DecidableEq V] [Fintype I]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X]
variable (G:Core.Au V I)
lemma Qz (F:V→ V→ ℝ) :
    (∑ e,G.Af e*∑ y,Ae (G.targets e) y*F (G.source e) y)=
      ∑ x,∑ y,G.Av x y*F x y:=by
  rw [← G.IV]
  simp only [Finset.mul_sum,← mul_assoc,G.Ht]
  exact Finset.sum_comm
lemma Me (U:V→ V→ X) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty) :
    AM (BU G.Af (fun e=> Ae (G.targets e)))
      (fun r=> U (G.source r.1) r.2)=
    AM (fun r:V × V=> G.Av r.1 r.2) (fun r=> U r.1 r.2):=by
  have hw (r:I × V):0≤BU G.Af (fun e=> Ae (G.targets e)) r :=
    mul_nonneg (G.AT _) (Core.Au.DK _ _)
  let:IsProbabilityMeasure (AM (BU G.Af (fun e=> Ae (G.targets e)))
      (fun r=> U (G.source r.1) r.2)):=DS _ _ hw
        (Mb _ _ (G.Bz hG) (fun e=> Bs _ (hB e)))
  let:IsProbabilityMeasure (AM (fun r:V × V=> G.Av r.1 r.2) (fun r=> U r.1 r.2)) :=
    DS _ _ (fun r=> G.LZ _ _)
      (by simpa only [Fintype.sum_prod_type] using G.KK hG)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [DP _ _ hw,DP _ _ (fun r=> G.LZ _ _)]
  simp only [BU,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum]
  exact Qz G (fun x y=> f (U x y))
omit G in
lemma Nv (hn:2≤Fintype.card V) (x y:V) :
    Az Finset.univ x y≤2*(Fintype.card V:ℝ)⁻¹*(Fintype.card V:ℝ)⁻¹:=by
  have hnR:(2:ℝ)≤Fintype.card V:=by exact_mod_cast hn
  have hn0:(0:ℝ)<Fintype.card V:=by linarith
  simp only [Az,Finset.mem_univ,true_and,Finset.card_univ]
  split_ifs
  · field_simp
    apply (div_le_iff₀ (by linarith:0<(Fintype.card V:ℝ)-1)).mpr
    nlinarith
  · positivity
omit [Fintype I] [MeasurableSingletonClass X] [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X] in
lemma JW (U:V→ X) (hn:2≤Fintype.card V) (M:ℝ) (hM:0≤M)
    (hdom:∀ x y,G.Av x y≤M*Az Finset.univ x y) :
    AM (fun r:V × V=> G.Av r.1 r.2) (fun r=>(U r.1,U r.2))≤
      ENNReal.ofReal (2*M)•(Bv U).prod (Bv U):=by
  rw [Bv,Rt _ _ _ _ (fun _=> by positivity),← RG _ _ _ (by positivity)]
  apply RA
  intro r
  calc
    _≤ M*Az Finset.univ r.1 r.2:=hdom _ _
    _≤ M*(2*(Fintype.card V:ℝ)⁻¹*(Fintype.card V:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (Nv hn _ _) hM
    _= _:=by ring
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Aa.Bounded
variable {X:Type u1} {Y:Type u2} [MeasurableSpace X] [MeasurableSpace Y]
lemma Jo (j:X→ Y) (hj:MeasurableEmbedding j)
    (μ:Measure Y) [IsProbabilityMeasure μ] (hfin:∀ᵐ y ∂ μ,y∈range j) :
    IsProbabilityMeasure (μ.comap j):=by
  constructor
  rw [hj.comap_apply,image_univ]
  exact measure_eq_measure_of_null_sdiff (subset_univ _) (by
    convert ae_iff.mp hfin using 2
    ext y
    simp) |>.trans measure_univ
lemma KB (j:X→ Y) (hj:MeasurableEmbedding j)
    (μ:Measure Y) (hfin:∀ᵐ y ∂ μ,y∈range j):(μ.comap j).map j=μ:=by
  rw [hj.map_comap]
  exact Measure.restrict_eq_self_of_ae_mem hfin
lemma SJ (j:X→ Y) (hj:MeasurableEmbedding j) (μ:Measure Y)
    {s:Set X}:(∀ᵐ x ∂ μ.comap j,x∈s)↔ μ (j '' sᶜ)=0:=by
  rw [ae_iff,hj.comap_apply]
  rfl
variable [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
lemma Ji (j:X→ Y) (hj:Topology.IsOpenEmbedding j)
    [HasOuterApproxClosed Y] (α:ℕ→ ProbabilityMeasure Y) (β:ProbabilityMeasure Y)
    (ht:Tendsto α atTop (𝓝 β)) (s:Set X) (hs:IsClosed s)
    (hα:∀ n,(α n:Measure Y) (j '' sᶜ)=0) :
    ∀ᵐ x ∂ (β:Measure Y).comap j,x∈s:=by
  rw [SJ j hj.measurableEmbedding]
  apply le_antisymm _ zero_le
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht
    (hj.isOpenMap _ hs.isOpen_compl)).trans
  apply liminf_le_of_frequently_le'
  exact (Eventually.of_forall (fun n=> le_of_eq (hα n))).frequently
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Aa.Bounded
lemma GV {A:Type u3} {B:Type u4} {X:Type u5} {Y:Type u6} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y] (j:A→ X) (k:B→ Y)
    (hj:Measurable j) (hk:MeasurableEmbedding k)
    (f:A→ B) (g:X→ Y) (hf:Measurable f) (hg:Measurable g)
    (μ:Measure A) (ν:Measure B) (hcomm:k∘ f=g∘ j)
    (hm:(μ.map j).map g=ν.map k):μ.map f=ν:=by
  apply hk.map_injective
  rw [Measure.map_map hk.measurable hf,hcomm,← Measure.map_map hg hj]
  exact hm
lemma SX {A:Type u7} {B:Type u8} [MeasurableSpace A] [MeasurableSpace B]
    (j:A→ B) (hj:MeasurableEmbedding j) (μ ν:Measure A)
    (h:μ.map j ≪ ν.map j):μ≪ν:=by
  intro s hs
  have hν:ν.map j (j '' s)=0:=by
    rw [hj.map_apply,hj.injective.preimage_image]
    exact hs
  have hμ:=h hν
  rwa [hj.map_apply,hj.injective.preimage_image] at hμ
lemma Go {A:Type u9} {B:Type u10} [MeasurableSpace A] [MeasurableSpace B]
    (j:A→ B) (hj:MeasurableEmbedding j) (μ:Measure A) :
    ∀ᵐ x ∂ μ.map j,x∈range j:=by
  apply (ae_map_iff hj.measurable.aemeasurable hj.measurableSet_range).mpr
  exact Eventually.of_forall (fun _=> mem_range_self _)
abbrev Df:ℂ × ℂ→ Sphere × Sphere:=Prod.map OnePoint.some OnePoint.some
abbrev CK:BO ℂ→ BO Sphere:=Prod.map OnePoint.some
  (Prod.map OnePoint.some Df)
abbrev BE:Expanded ℂ→ Expanded Sphere:=Prod.map CK (Prod.map Df Df)
lemma Bt:Topology.IsOpenEmbedding Df :=
  OnePoint.isOpenEmbedding_coe.prodMap OnePoint.isOpenEmbedding_coe
lemma Ca:Topology.IsOpenEmbedding CK :=
  OnePoint.isOpenEmbedding_coe.prodMap (OnePoint.isOpenEmbedding_coe.prodMap Bt)
lemma CL:Topology.IsOpenEmbedding BE :=
  Ca.prodMap (Bt.prodMap Bt)
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Aa.Bounded
open Variance
variable {V:Type u11} {I:Type u12} [Fintype V] [DecidableEq V] [Fintype I]
variable (G:Core.Au V I)
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
omit [Fintype I] in
lemma Gt (r:I × V) :
    0≤BU G.Af (fun e=> Ae (G.targets e)) r :=
  mul_nonneg (G.AT _) (Core.Au.DK _ _)
omit [Fintype I] in
lemma FJ (r:I × V × V × V) :
    0≤BT G.Af (fun e=> Ae (G.targets e)) r :=
  mul_nonneg (mul_nonneg (mul_nonneg (G.AT _) (Core.Au.DK _ _))
    (Core.Au.DK _ _)) (Core.Au.DK _ _)
def Ba (U₁ U₂:V→ Sphere) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty):ProbabilityMeasure (BO Sphere) :=
  Jh (BU G.Af (fun e=> Ae (G.targets e)))
    (Fh G.source U₁ U₂) (Gt G)
      (Mb _ _ (G.Bz hG) (fun e=> Bs _ (hB e)))
def Bk (U₁ U₂:V→ Sphere) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty):ProbabilityMeasure (Expanded Sphere) :=
  Jh (BT G.Af (fun e=> Ae (G.targets e)))
    (Ee G.source U₁ U₂) (FJ G)
      (Qi _ _ (G.Bz hG) (fun e=> Bs _ (hB e)))
lemma JP (U₁ U₂:V→ Sphere) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty) :
    (Bk G U₁ U₂ hG hB:Measure (Expanded Sphere)).map Prod.fst=
      (Ba G U₁ U₂ hG hB:Measure (BO Sphere)):=by
  change (AM _ _).map _=AM _ _
  rw [IY _ _ _ measurable_fst]
  exact RJ G.Af (fun e=> Ae (G.targets e)) (Fh G.source U₁ U₂) G.AT (fun e=> Core.Au.DK _) (fun e=> Bs _ (hB e))
lemma Lq (U₁ U₂:V→ Sphere) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty) (hn:2≤Fintype.card V) (M:ℝ) (hM:0≤M)
    (hdom:∀ x y,G.Av x y≤M*Az Finset.univ x y) :
    (Ba G U₁ U₂ hG hB:Measure (BO Sphere)).map (fun q=>(q.1,q.2.2.1))≤
      ENNReal.ofReal (2*M)•(Bv U₁).prod (Bv U₁):=by
  change (AM (BU G.Af (fun e=> Ae (G.targets e)))
    (Fh G.source U₁ U₂)).map (fun q=>(q.1,q.2.2.1))≤_
  rw [IY _ _ (fun q:BO Sphere=>(q.1,q.2.2.1)) (by fun_prop)]
  change AM (BU G.Af (fun e=> Ae (G.targets e))) (fun r=>(U₁ (G.source r.1),U₁ r.2))≤_
  rw [Me G (fun x y=>(U₁ x,U₁ y)) hG hB]
  exact JW G U₁ hn M hM hdom
lemma Lj (U₁ U₂:V→ Sphere) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty) (hn:2≤Fintype.card V) (M:ℝ) (hM:0≤M)
    (hdom:∀ x y,G.Av x y≤M*Az Finset.univ x y) :
    (Ba G U₁ U₂ hG hB:Measure (BO Sphere)).map (fun q=>(q.2.1,q.2.2.2))≤
      ENNReal.ofReal (2*M)•(Bv U₂).prod (Bv U₂):=by
  change (AM (BU G.Af (fun e=> Ae (G.targets e)))
    (Fh G.source U₁ U₂)).map (fun q=>(q.2.1,q.2.2.2))≤_
  rw [IY _ _ (fun q:BO Sphere=>(q.2.1,q.2.2.2)) (by fun_prop)]
  change AM (BU G.Af (fun e=> Ae (G.targets e))) (fun r=>(U₂ (G.source r.1),U₂ r.2))≤_
  rw [Me G (fun x y=>(U₂ x,U₂ y)) hG hB]
  exact JW G U₂ hn M hM hdom
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace Aa.Ao
def level (ω:AS) (r:ℝ):ℤ:=⌊(-r-ω.1.1)/Real.log 2⌋
def label (ω:AS) (r:ℝ) (z:ℂ):ℤ × ℤ :=
  (bin ((2:ℝ)^level ω r) (Cq (level ω r) ω.2.1) (Am ω.1.1 ω.1.2 z).1,
   bin ((2:ℝ)^level ω r) (Cq (level ω r) ω.2.2) (Am ω.1.1 ω.1.2 z).2)
lemma Qu (z w:ℂ) :
    ∀ᵐ ω ∂ As,
      (∃ m,Ar m ω.2 (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w)) ∧
      (∀ m,Ar m ω.2 (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w) →
        Ar (m+1) ω.2 (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w)):=by
  have hm (m:ℤ):MeasurableSet {ω:AS | Ar m ω.2
      (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w)} :=
    Dc measurable_snd
      ((DQ z).comp measurable_fst) ((DQ w).comp measurable_fst) m
  have hs:MeasurableSet {ω:AS |
      (∃ m,Ar m ω.2 (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w)) ∧
      (∀ m,Ar m ω.2 (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w) →
        Ar (m+1) ω.2 (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w))}:=by
    simp only [Set.ofPred_and,Set.ofPred_exists,Set.ofPred_forall]
    refine (MeasurableSet.iUnion hm).inter (MeasurableSet.iInter (fun m => ?_))
    convert (hm m).compl.union (hm (m+1)) using 1
    ext ω
    exact imp_iff_not_or
  apply (Measure.ae_prod_iff_ae_ae hs).mpr
  filter_upwards with p
  have hn:∀ᵐ ω ∂ Aq,∀ m,Ar m ω (Am p.1 p.2 z) (Am p.1 p.2 w) →
      Ar (m+1) ω (Am p.1 p.2 z) (Am p.1 p.2 w):=by
    exact eventually_countable_forall.mpr (fun m=> EX m _ _)
  filter_upwards [Db (Am p.1 p.2 z) (Am p.1 p.2 w),hn] with ω he hn
  obtain ⟨n,he⟩:=he
  exact ⟨⟨(n:ℤ),he⟩,hn⟩
lemma SV {ω:AS} {z w:ℂ} (hzw:z≠w)
    (he:∃ m,Ar m ω.2 (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w))
    (hn:∀ m,Ar m ω.2 (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w) →
      Ar (m+1) ω.2 (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w)) (r:ℝ) :
    label ω r z=label ω r w↔ r≤depth ω z w:=by
  rw [show label ω r z=label ω r w↔ Ar (level ω r) ω.2
    (Am ω.1.1 ω.1.2 z) (Am ω.1.1 ω.1.2 w) by simp only [label,Prod.mk.injEq,Ar]]
  rw [DF (CT _ _ hzw) he hn]
  unfold level depth AH
  rw [Int.le_floor,le_div_iff₀ (Real.log_pos (by norm_num:(1:ℝ)<2))]
  constructor <;> intro h <;> linarith
def side (ω:AS) (r m:ℝ):ℝ:=Real.exp (m+ω.1.1)*(2:ℝ)^level ω r
lemma SG (ω:AS) (r m:ℝ):0<side ω r m:=by unfold side; positivity
lemma SD (ω:AS) (r m:ℝ) :
    Real.log (side ω r m)=m+ω.1.1+(level ω r:ℝ)*Real.log 2:=by
  unfold side
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity),Real.log_exp,Real.log_zpow]
lemma Pk (ω:AS) (r m:ℝ) :
    Real.exp (m-r)/2< side ω r m∧ side ω r m≤ Real.exp (m-r):=by
  have hl:=Int.floor_le ((-r-ω.1.1)/Real.log 2)
  have hu:=Int.lt_floor_add_one ((-r-ω.1.1)/Real.log 2)
  have hp:0<Real.log 2:=Real.log_pos (by norm_num)
  have hl':=(le_div_iff₀ hp).mp hl
  have hu':=(div_lt_iff₀ hp).mp hu
  change (level ω r:ℝ)*Real.log 2≤ -r-ω.1.1 at hl'
  change -r-ω.1.1<((level ω r:ℝ)+1)*Real.log 2 at hu'
  constructor
  · rw [← Real.exp_log (by norm_num:(0:ℝ)<2),← Real.exp_sub]
    rw [← Real.exp_log (SG ω r m),Real.exp_lt_exp,SD]
    nlinarith
  · rw [← Real.exp_log (SG ω r m),Real.exp_le_exp,SD]
    linarith
lemma Rh {ω:AS} {r m:ℝ} {z w:ℂ}
    (h:label ω r z=label ω r w) :
    ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖<2*side ω r m:=by
  have h₁:=HJ (by positivity:0<(2:ℝ)^level ω r) (congrArg Prod.fst h)
  have h₂:=HJ (by positivity:0<(2:ℝ)^level ω r) (congrArg Prod.snd h)
  have hh:=(Dz ω.1.1 ω.1.2 z w).1
  have hm:=mul_lt_mul_of_pos_left (show Real.exp (-ω.1.1)*‖z-w‖<2*(2:ℝ)^level ω r by linarith)
    (Real.exp_pos (m+ω.1.1))
  have he:Real.exp (m+ω.1.1)*Real.exp (-ω.1.1)=Real.exp m:=by rw [← Real.exp_add]; congr 1; ring
  rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  unfold side
  rw [← mul_assoc,he] at hm
  nlinarith
end Aa.Ao
namespace Aa.Bg
open NumberField Ak
variable {P:Type u1} {K:Type u2} [Fintype P] [DecidableEq P] [Field K] [NumberField K]
variable (Z:P→ K) (hZ:Function.Injective Z) (v:InfinitePlace K)
omit [NumberField K] in
include hZ in
lemma RU:∀ᵐ ω ∂ Ao.As,∀ r x y,
    (arch Z v ω).share r x y↔ Ao.label ω r (v.embedding (Z x))=Ao.label ω r (v.embedding (Z y)):=by
  have hr:∀ᵐ ω ∂ Ao.As,∀ x y,
      (∃ m,Ao.Ar m ω.2 (Ao.Am ω.1.1 ω.1.2 (v.embedding (Z x))) (Ao.Am ω.1.1 ω.1.2 (v.embedding (Z y)))) ∧
      (∀ m,Ao.Ar m ω.2 (Ao.Am ω.1.1 ω.1.2 (v.embedding (Z x))) (Ao.Am ω.1.1 ω.1.2 (v.embedding (Z y))) →
        Ao.Ar (m+1) ω.2 (Ao.Am ω.1.1 ω.1.2 (v.embedding (Z x))) (Ao.Am ω.1.1 ω.1.2 (v.embedding (Z y)))):=by
    simp only [Filter.eventually_all]
    exact fun x y=> Ao.Qu _ _
  filter_upwards [Rr Z hZ v,hr] with ω hg hr
  intro r x y
  by_cases hxy:x=y
  · subst y; simp [Depth.share]
  · rw [Depth.share,or_iff_right hxy]
    change (r≤ if good Z v ω∧ x≠y then Ao.depth ω (v.embedding (Z x)) (v.embedding (Z y)) else 0)↔ _
    rw [if_pos ⟨hg,hxy⟩]
    exact (Ao.SV (Bx Z hZ v hxy) (hr x y).1 (hr x y).2 r).symm
end Aa.Bg
end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace Aa.Ao
lemma Tm {l:ℝ} (hl:0<l) (s x y:ℝ) :
    |(bin l s x:ℝ)-(bin l s y:ℝ)| < |x-y|/l+1:=by
  have hx:=Int.floor_le ((x-s)/l)
  have hy:=Int.lt_floor_add_one ((y-s)/l)
  have hx':=Int.lt_floor_add_one ((x-s)/l)
  have hy':=Int.floor_le ((y-s)/l)
  have hh:(x-s)/l-(y-s)/l=(x-y)/l:=by ring
  have hle:=div_le_div_of_nonneg_right (le_abs_self (x-y)) hl.le
  have hge:=div_le_div_of_nonneg_right (neg_abs_le (x-y)) hl.le
  rw [neg_div] at hge
  unfold bin
  apply abs_lt.mpr
  constructor <;> linarith
lemma Oa (ω:AS) (r m:ℝ) (z w:ℂ) :
    Real.exp (-ω.1.1)*‖z-w‖/(2:ℝ)^level ω r =
      ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖/side ω r m:=by
  rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  unfold side
  have he:Real.exp (-ω.1.1)*Real.exp (m+ω.1.1)=Real.exp m:=by
    rw [← Real.exp_add]; congr 1; ring
  field_simp
  nlinarith [congrArg (fun t:ℝ=>‖z-w‖*t) he]
lemma RP (ω:AS) (r m:ℝ) (z w:ℂ) :
    |((label ω r z).1:ℝ)-((label ω r w).1:ℝ)| <
      ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖/side ω r m+1 ∧
    |((label ω r z).2:ℝ)-((label ω r w).2:ℝ)| <
      ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖/side ω r m+1:=by
  have h₁ : |(Am ω.1.1 ω.1.2 z).1-(Am ω.1.1 ω.1.2 w).1|≤
      Real.exp (-ω.1.1)*‖z-w‖:=by
    simpa only [← HC ω.1.1 ω.1.2 (z-w),GU,Am,Complex.sub_re] using
      Complex.abs_re_le_norm (Dg ω.1.1 ω.1.2 z-Dg ω.1.1 ω.1.2 w)
  have h₂ : |(Am ω.1.1 ω.1.2 z).2-(Am ω.1.1 ω.1.2 w).2|≤
      Real.exp (-ω.1.1)*‖z-w‖:=by
    simpa only [← HC ω.1.1 ω.1.2 (z-w),GU,Am,Complex.sub_im] using
      Complex.abs_im_le_norm (Dg ω.1.1 ω.1.2 z-Dg ω.1.1 ω.1.2 w)
  have hp:0<(2:ℝ)^level ω r:=by positivity
  constructor
  · exact (Tm hp _ _ _).trans_le (add_le_add
      ((div_le_div_of_nonneg_right h₁ hp.le).trans_eq (Oa ω r m z w)) le_rfl)
  · exact (Tm hp _ _ _).trans_le (add_le_add
      ((div_le_div_of_nonneg_right h₂ hp.le).trans_eq (Oa ω r m z w)) le_rfl)
lemma OW {P:Type u3} [DecidableEq P] (A:Finset P) (u:P→ ℂ)
    (ω:AS) (r m:ℝ) (b:ℂ) (R L:ℝ) (M:ℕ)
    (hR:0≤R) (hL:0<L) (hside:L≤ side ω r m)
    (hM:2*R/L+1≤M)
    (hA:∀ x∈A,‖(Real.exp m:ℂ)*u x+b‖≤R) :
    (A.image (fun x=> label ω r (u x))).card≤(2*M+1)^2:=by
  classical
  rcases A.eq_empty_or_nonempty with h | ⟨x₀,hx₀⟩
  · simp [h]
  let l₀:=label ω r (u x₀)
  have hd (x:P) (hx:x∈A) :
      ‖(Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u x₀‖≤2*R:=by
    rw [show (Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u x₀=
      ((Real.exp m:ℂ)*u x+b)-((Real.exp m:ℂ)*u x₀+b) by ring]
    exact (norm_sub_le _ _).trans (by linarith [hA x hx,hA x₀ hx₀])
  have hg (x:P) (hx:x∈A) :
      |((label ω r (u x)).1:ℝ)-(l₀.1:ℝ)|≤M ∧
      |((label ω r (u x)).2:ℝ)-(l₀.2:ℝ)|≤M:=by
    have hb:‖(Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u x₀‖/side ω r m+1≤M:=by
      apply le_trans _ hM
      apply add_le_add _ le_rfl
      exact div_le_div₀ (by positivity) (hd x hx) hL hside
    exact ⟨(RP ω r m _ _).1.le.trans hb,(RP ω r m _ _).2.le.trans hb⟩
  have hs:A.image (fun x=> label ω r (u x)) ⊆
      (Finset.Icc (l₀.1-(M:ℤ)) (l₀.1+(M:ℤ))) ×ˢ
      (Finset.Icc (l₀.2-(M:ℤ)) (l₀.2+(M:ℤ))):=by
    intro p hp
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hp
    have hh:=hg x hx
    rcases abs_le.mp hh.1 with ⟨ha,hb⟩
    rcases abs_le.mp hh.2 with ⟨hc,hd⟩
    simp only [Finset.mem_product,Finset.mem_Icc]
    constructor
    · constructor
      · exact_mod_cast (show (l₀.1:ℝ)-(M:ℝ)≤((label ω r (u x)).1:ℝ) by linarith)
      · exact_mod_cast (show ((label ω r (u x)).1:ℝ)≤(l₀.1:ℝ)+(M:ℝ) by linarith)
    · constructor
      · exact_mod_cast (show (l₀.2:ℝ)-(M:ℝ)≤((label ω r (u x)).2:ℝ) by linarith)
      · exact_mod_cast (show ((label ω r (u x)).2:ℝ)≤(l₀.2:ℝ)+(M:ℝ) by linarith)
  calc
    _≤ _:=Finset.card_le_card hs
    _=(2*M+1)^2:=by
      rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
      have he (z:ℤ):(z+(M:ℤ)+1-(z-(M:ℤ))).toNat=2*M+1:=by omega
      rw [he,he,pow_two]
end Aa.Ao
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace Aa.Ak.Depth
variable {P:Type u1} [Fintype P] [DecidableEq P]
variable (d:Depth P)
lemma Su (r:ℝ) (f:P→ ℝ) :
    (∑ C∈ d.cells r,∑ x∈C,f x)=∑ x,f x:=by
  have hh (x:P):(∑ C∈ d.cells r,if x∈C then f x else 0)=f x:=by
    rw [Finset.sum_eq_single (d.cell r x)]
    · simp [d.Jr]
    · intro C hC hne
      rw [if_neg]
      exact fun hx=> hne (d.Cx hC hx)
    · simp
  calc
    _=∑ C∈ d.cells r,∑ x,if x∈C then f x else 0:=by simp
    _=∑ x,∑ C∈ d.cells r,if x∈C then f x else 0:=Finset.sum_comm
    _= _:=by simp_rw [hh]
lemma LD (r:ℝ) (p:P→ ℝ) (v:Finset P→ ℝ) :
    (∑ x,p x*v (d.cell r x))=∑ C∈d.cells r,v C*(∑ x∈C,p x):=by
  rw [← d.Su r (fun x=> p x*v (d.cell r x))]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← d.Cx hC hx]
  ring
end Aa.Ak.Depth
namespace Aa.Bounded
open Ak Variance
variable {P:Type u2} [Fintype P] [DecidableEq P]
omit [DecidableEq P] in
lemma HW (p f g:P→ ℝ) (hp:∀ x,0≤ p x) (h1:∑ x,p x=1)
    (η:ℝ) (hfg:∀ x,|f x-g x| ≤ η) :
    |(∑ x,p x*f x)-(∑ x,p x*g x)| ≤ η:=by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x,|p x*f x-p x*g x| := Finset.abs_sum_le_sum_abs _ _
    _=∑ x,p x*|f x-g x| := by simp_rw [← mul_sub,abs_mul,abs_of_nonneg (hp _)]
    _ ≤ ∑ x,p x*η:=Finset.sum_le_sum (fun x _=> mul_le_mul_of_nonneg_left (hfg x) (hp x))
    _= η:=by rw [← Finset.sum_mul,h1,one_mul]
lemma MG (d:Depth P) (r:ℝ) (p a f:P→ ℝ)
    (hp:∀ x,0≤ p x) (ha:∀ x,0≤ a x) (hp1:∑ x,p x=1) (ha1:∑ x,a x=1)
    (A:Finset (Finset P)) (hA:A⊆d.cells r) (v:Finset P→ ℝ) (η H:ℝ)
    (hf:∀ x,|f x-v (d.cell r x)| ≤ η)
    (hv:∀ C∈d.cells r,|v C| ≤ if C∈A then H else 0) :
    |(∑ x,p x*f x)-(∑ x,a x*f x)| ≤
      2*η+H*(∑ C∈A,|(∑ x∈C,p x)-(∑ x∈C,a x)|):=by
  have hpa : |(∑ x,p x*v (d.cell r x))-(∑ x,a x*v (d.cell r x))| ≤
      H*(∑ C∈A,|(∑ x∈C,p x)-(∑ x∈C,a x)|):=by
    rw [d.LD,d.LD,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ C∈d.cells r,|v C*(∑ x∈C,p x)-v C*(∑ x∈C,a x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ C∈d.cells r,if C∈A then H*|(∑ x∈C,p x)-(∑ x∈C,a x)| else 0:=by
        apply Finset.sum_le_sum
        intro C hC
        rw [← mul_sub,abs_mul]
        simpa only [ite_mul,zero_mul] using mul_le_mul_of_nonneg_right (hv C hC) (abs_nonneg _)
      _= _:=by rw [Finset.sum_ite_mem,Finset.inter_eq_right.mpr hA,Finset.mul_sum]
  have h₁:=HW p f (fun x=> v (d.cell r x)) hp hp1 η hf
  have h₂:=HW a f (fun x=> v (d.cell r x)) ha ha1 η hf
  have hh:=abs_add_three ((∑ x,p x*f x)-(∑ x,p x*v (d.cell r x)))
    ((∑ x,p x*v (d.cell r x))-(∑ x,a x*v (d.cell r x)))
    ((∑ x,a x*v (d.cell r x))-(∑ x,a x*f x))
  rw [abs_sub_comm (∑ x,a x*v (d.cell r x))] at hh
  convert le_trans hh (by linarith:_≤2*η+H*(∑ C∈A,|(∑ x∈C,p x)-(∑ x∈C,a x)|)) using 1
  congr 1
  ring
lemma LI (B C:Finset P) (hB:B.Nonempty) :
    Ad B Cᶜ=1-Ad B C:=by
  rw [← Ci,← Ci,← Bs B hB]
  have hh:=Finset.sum_compl_add_sum C (Ae B)
  linarith
variable {I:Type u3} [Fintype I]
def BY (w:I→ ℝ) (B:I→ Finset P) (C:Finset P):ℝ :=
  ∑ i,w i*|Ad (B i) C-Ad Finset.univ C|
lemma Lz (w:I→ ℝ) (B:I→ Finset P) (hB:∀ i,(B i).Nonempty)
    (hn:0<Fintype.card P) (C:Finset P) :
    BY w B Cᶜ=BY w B C:=by
  unfold BY
  apply Finset.sum_congr rfl
  intro i _
  rw [LI _ _ (hB i),LI _ _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn)),
    sub_sub_sub_cancel_left,abs_sub_comm]
lemma LV (w:I→ ℝ) (B:I→ Finset P) (M:ℝ)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i≤1)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤ M*Ae Finset.univ x) (C:Finset P) :
    BY w B C≤(M+1)*Ad Finset.univ C:=by
  have hmean:=HP w B C M hdom
  calc
    _ ≤ ∑ i,w i*(Ad (B i) C+Ad Finset.univ C):=by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (abs_sub_le_iff.mpr ⟨by linarith [Bd (Finset.univ:Finset P) C],by linarith [Bd (B i) C]⟩) (hw i)
    _=(∑ i,w i*Ad (B i) C)+(∑ i,w i)*Ad Finset.univ C:=by simp [mul_add,Finset.sum_add_distrib,Finset.sum_mul]
    _ ≤ (M+1)*Ad Finset.univ C:=by nlinarith [mul_le_mul_of_nonneg_right hW (Bd (Finset.univ:Finset P) C)]
lemma LJ (w:I→ ℝ) (B:I→ Finset P) (M T δ:ℝ)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i≤1) (hM:0≤ M) (hT:0≤ T) (hδ:0<δ)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤ M*Ae Finset.univ x)
    (C:Finset P) :
    BY w B C ≤ Aj w B T C/δ+δ+(M+1)*T/Fintype.card P:=by
  by_cases hC:T<(C.card:ℝ)
  · have hy (t:ℝ) : |t| ≤ t^2/δ+δ:=by
      have hh : |t| *δ≤ t^2+δ*δ:=by nlinarith [sq_nonneg (|t| -δ),sq_abs t]
      calc
        |t| = (|t| *δ)/δ:=by field_simp
        _≤(t^2+δ*δ)/δ:=div_le_div_of_nonneg_right hh hδ.le
        _= _:=by field_simp
    have hh:BY w B C≤ Aj w B T C/δ+δ:=by
      rw [Aj,if_pos hC]
      calc
        _ ≤ ∑ i,w i*((Ad (B i) C-Ad Finset.univ C)^2/δ+δ) :=
          Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (hy _) (hw i))
        _=(∑ i,w i*(Ad (B i) C-Ad Finset.univ C)^2)/δ+(∑ i,w i)*δ:=by
          simp only [mul_add,← mul_div_assoc,Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul]
        _ ≤ _:=by nlinarith [mul_le_mul_of_nonneg_right hW hδ.le]
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=LV w B M hw hW hdom C
    have hc:Ad (Finset.univ:Finset P) C≤ T/Fintype.card P:=by
      simp only [Ad,Finset.univ_inter,Finset.card_univ]
      exact div_le_div_of_nonneg_right (le_of_not_gt hC) (by positivity)
    have hv:=Bw w B T hw C
    have hm:=mul_le_mul_of_nonneg_left hc (show 0≤ M+1 by linarith)
    rw [← mul_div_assoc] at hm
    linarith [div_nonneg hv hδ.le]
end Aa.Bounded
end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace Aa.Ak.Depth
variable {P:Type u4} [Fintype P] [DecidableEq P]
variable (d:Depth P)
def Dk (C:Finset P):Finset P:=if Fintype.card P<2*C.card then Cᶜ else C
lemma OK (r:ℝ) (f:Finset P→ ℝ) :
    (∑ C∈d.cells r,f (Dk C))=d.Ch f r:=by
  classical
  simp only [Ch,transformed,Multiset.map_add,Multiset.sum_add,Multiset.map_map,
    Function.comp_def,Dk]
  simp_rw [apply_ite f]
  rw [Finset.sum_ite]
  change (∑ C∈(d.cells r).filter (fun C=> Fintype.card P<2*C.card),f Cᶜ)+
    (∑ C∈(d.cells r).filter (fun C=>¬Fintype.card P<2*C.card),f C) =
    (∑ C∈(d.cells r).filter (fun C=>¬Fintype.card P<2*C.card),f C)+
    (∑ C∈(d.cells r).filter (fun C=> Fintype.card P<2*C.card),f Cᶜ)
  ring
end Aa.Ak.Depth
namespace Aa.Bounded
open Ak Variance
variable {P:Type u5} {I:Type u6} [Fintype P] [DecidableEq P] [Fintype I]
lemma Jz (w:I→ ℝ) (B:I→ Finset P) (hB:∀ i,(B i).Nonempty)
    (hn:0<Fintype.card P) (C:Finset P) :
    BY w B (Depth.Dk C)=BY w B C:=by
  unfold Depth.Dk
  split_ifs
  · exact Lz w B hB hn C
  · rfl
lemma JS (d:Depth P) (r:ℝ) (A:Finset (Finset P))
    (N M T δ:ℝ) (w:I→ ℝ) (B:I→ Finset P)
    (hn:0<Fintype.card P) (hA:A⊆d.cells r) (hN:(A.card:ℝ)≤ N)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i≤1) (hB:∀ i,(B i).Nonempty)
    (hM:0≤ M) (hT:0≤ T) (hδ:0<δ)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤ M*Ae Finset.univ x) :
    (∑ C∈A,BY w B C) ≤
      d.Ch (Aj w B T) r/δ+N*(δ+(M+1)*T/Fintype.card P):=by
  have hv (C):0≤ Aj w B T C:=Bw w B T hw C
  calc
    _=∑ C∈A,BY w B (Depth.Dk C):=by
      simp_rw [Jz w B hB hn]
    _≤∑ C∈A,(Aj w B T (Depth.Dk C)/δ+(δ+(M+1)*T/Fintype.card P)):=by
      apply Finset.sum_le_sum
      intro C _
      simpa only [add_assoc] using LJ w B M T δ hw hW hM hT hδ hdom (Depth.Dk C)
    _=(∑ C∈A,Aj w B T (Depth.Dk C))/δ+
        (A.card:ℝ)*(δ+(M+1)*T/Fintype.card P):=by
      simp [Finset.sum_add_distrib,Finset.sum_div]
      ring
    _≤(∑ C∈d.cells r,Aj w B T (Depth.Dk C))/δ+
        N*(δ+(M+1)*T/Fintype.card P):=by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hA (fun C _ _=> hv _)) hδ.le
      · apply mul_le_mul_of_nonneg_right hN
        positivity
    _= _:=by rw [d.OK]
def Bc (w:I→ ℝ) (B:I→ Finset P) (f:P→ ℝ):ℝ :=
  ∑ i,w i*|(∑ x,Ae (B i) x*f x)-(∑ x,Ae Finset.univ x*f x)|
lemma Om (w:I→ ℝ) (B:I→ Finset P) (f:P→ ℝ) (hw:∀ i,0≤ w i) :
    0≤ Bc w B f:=Finset.sum_nonneg (fun i _=> mul_nonneg (hw i) (abs_nonneg _))
lemma Iz (d:Depth P) (r:ℝ) (A:Finset (Finset P))
    (N M T δ η H:ℝ) (w:I→ ℝ) (B:I→ Finset P)
    (hn:0<Fintype.card P) (hA:A⊆d.cells r) (hN:(A.card:ℝ)≤ N)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i≤1) (hB:∀ i,(B i).Nonempty)
    (hM:0≤ M) (hT:0≤ T) (hδ:0<δ) (hη:0≤ η) (hH:0≤ H)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤ M*Ae Finset.univ x)
    (f:P→ ℝ) (v:Finset P→ ℝ)
    (hf:∀ x,|f x-v (d.cell r x)| ≤ η)
    (hv:∀ C∈d.cells r,|v C| ≤ if C∈A then H else 0) :
    Bc w B f≤2*η+H*(d.Ch (Aj w B T) r/δ+
      N*(δ+(M+1)*T/Fintype.card P)):=by
  have hp (S:Finset P) (x:P):0≤ Ae S x:=by unfold Ae; split_ifs <;> positivity
  have hh (i:I):=MG d r (Ae (B i)) (Ae Finset.univ) f
    (hp _) (hp _) (Bs _ (hB i))
    (Bs _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn))) A hA v η H hf hv
  simp only [Ci] at hh
  have hmean:=JS d r A N M T δ w B hn hA hN hw hW hB hM hT hδ hdom
  calc
    _≤∑ i,w i*(2*η+H*(∑ C∈A,|Ad (B i) C-Ad Finset.univ C|)) :=
      Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (hh i) (hw i))
    _=(∑ i,w i)*(2*η)+H*(∑ C∈A,BY w B C):=by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul]
      congr 1
      simp only [BY,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _≤ _:=add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hW (show 0≤2*η by positivity))
      (mul_le_mul_of_nonneg_left hmean hH)
end Aa.Bounded
end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace Aa.Bounded
open Ak
variable {P:Type u7} [Fintype P] [DecidableEq P]
lemma RI (d:Depth P) (u:P→ ℂ) (ω:Ao.AS) (r m:ℝ) (b:ℂ)
    (hn:0<Fintype.card P)
    (hshare:∀ x y,d.share r x y↔ Ao.label ω r (u x)=Ao.label ω r (u y))
    (R L η H ε:ℝ) (M:ℕ) (hR:0≤R) (hL:0<L)
    (hside:L≤ Ao.side ω r m) (hupper:Ao.side ω r m≤ ε)
    (hM:2*R/L+1≤M)
    (f:ℂ→ ℝ) (hbound:∀ z,|f z|≤H)
    (hcont:∀ z w,‖z-w‖<2*ε → |f z-f w|≤η)
    (hout:∀ z,R<‖z‖ → |f z|≤η) :
    ∃ A:Finset (Finset P),∃ v:Finset P→ ℝ,
      A⊆d.cells r∧ A.card≤(2*M+1)^2 ∧
      (∀ x,|f ((Real.exp m:ℂ)*u x+b)-v (d.cell r x)|≤η) ∧
      (∀ C∈d.cells r,|v C|≤ if C∈A then H else 0):=by
  classical
  let:Nonempty P:=Fintype.card_pos_iff.mp hn
  let D:Finset P:=Finset.univ.filter (fun x=>‖(Real.exp m:ℂ)*u x+b‖≤R)
  let A:=D.image (d.cell r)
  let rep (C:Finset P):P:=if h:C∈A then (Finset.mem_image.mp h).choose else Classical.arbitrary P
  have hr (C:Finset P) (hC:C∈A):rep C∈D∧ d.cell r (rep C)=C:=by
    simpa only [rep,dif_pos hC] using (Finset.mem_image.mp hC).choose_spec
  have hAc:A⊆d.cells r:=Finset.image_subset_image (Finset.filter_subset _ _)
  have hcount:A.card≤(2*M+1)^2:=by
    apply le_trans (Finset.card_le_card_of_injOn (fun C=> Ao.label ω r (u (rep C)))
      (t:=D.image (fun x=> Ao.label ω r (u x))) ?_ ?_)
    · apply Ao.OW D u ω r m b R L M hR hL hside hM
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro C hC
      exact Finset.mem_image.mpr ⟨rep C,(hr C hC).1,rfl⟩
    · intro C hC E hE he
      rw [← (hr C hC).2,← (hr E hE).2]
      exact d.Eh ((hshare _ _).mpr he)
  let v (C:Finset P):=if C∈A then f ((Real.exp m:ℂ)*u (rep C)+b) else 0
  refine ⟨A,v,hAc,hcount,?_,?_⟩
  · intro x
    by_cases hx:d.cell r x∈A
    · simp only [v,if_pos hx]
      apply hcont
      have he:d.share r x (rep (d.cell r x)):=by
        rw [← d.BN]
        have hmem:=d.CQ r (rep (d.cell r x))
        rwa [(hr _ hx).2] at hmem
      have hd:=Ao.Rh (m:=m) ((hshare _ _).mp he)
      have heq:((Real.exp m:ℂ)*u x+b)-((Real.exp m:ℂ)*u (rep (d.cell r x))+b)=
          (Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u (rep (d.cell r x)):=by ring
      rw [heq]
      exact hd.trans_le (by linarith)
    · simp only [v,if_neg hx,sub_zero]
      apply hout
      by_contra hh
      have hxD:x∈D:=Finset.mem_filter.mpr ⟨Finset.mem_univ x,le_of_not_gt hh⟩
      exact hx (Finset.mem_image.mpr ⟨x,hxD,rfl⟩)
  · intro C _
    by_cases hC:C∈A
    · simpa only [v,if_pos hC] using hbound ((Real.exp m:ℂ)*u (rep C)+b)
    · simp only [v,if_neg hC,abs_zero,le_refl]
end Aa.Bounded
end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace Aa.Bounded
lemma PW (g:ℝ→ ℝ) (hg:Integrable g) (hg0:∀ r,0≤g r)
    (t D a b:ℝ) (hb:0≤b) (h:∀ r∈Set.Icc t (t+1),D≤a+b*g r) :
    D≤a+b*(∫ r,g r):=by
  have hi (c:ℝ):IntegrableOn (fun _:ℝ=> c) (Set.Icc t (t+1)) :=
    integrableOn_const isCompact_Icc.measure_lt_top.ne
  have hv:(volume (Set.Icc t (t+1))).toReal=1:=by simp [Real.volume_Icc]
  have hc (c:ℝ):(∫ r in Set.Icc t (t+1),c)=c:=by
    rw [integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,hv,one_smul]
  have hh:=setIntegral_mono_on (hi D) ((hi a).add (hg.integrableOn.const_mul b)) measurableSet_Icc h
  simp only [Pi.add_apply] at hh
  rw [integral_add (hi a) (hg.integrableOn.const_mul b),hc D,hc a,integral_const_mul] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hg (ae_of_all _ hg0)) hb))
end Aa.Bounded
namespace Aa.Ao
lemma PM (ω:AS) (m ε r:ℝ) (hε:0<ε)
    (hr:r∈Set.Icc (m-Real.log ε) (m-Real.log ε+1)) :
    ε/(2*Real.exp 1)≤ side ω r m∧ side ω r m≤ ε:=by
  have he:Real.exp (Real.log ε-1)/2=ε/(2*Real.exp 1):=by
    rw [Real.exp_sub,Real.exp_log hε]
    ring
  constructor
  · rw [← he]
    exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hr.2])) (by norm_num)).trans
      (Pk ω r m).1.le
  · exact (Pk ω r m).2.trans (by rw [← Real.exp_log hε]; exact Real.exp_le_exp.mpr (by linarith [hr.1]))
end Aa.Ao
end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace Aa.Bounded
open Ak Variance Bg NumberField
variable {P:Type u8} {I:Type u9} [Fintype P] [DecidableEq P] [Fintype I]
lemma Mq (d:Depth P) (u:P→ ℂ) (ω:Ao.AS) (m:ℝ) (b:ℂ)
    (hn:2≤ Fintype.card P)
    (hshare:∀ r x y,d.share r x y↔ Ao.label ω r (u x)=Ao.label ω r (u y))
    (R ε η H M T δ:ℝ) (N:ℕ) (hR:0≤ R) (hε:0<ε)
    (hN:2*R/(ε/(2*Real.exp 1))+1≤ N)
    (hη:0≤ η) (hH:0≤ H) (hM:0≤ M) (hT:1≤ T) (hδ:0<δ)
    (w:I→ ℝ) (B:I→ Finset P)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i≤ 1) (hB:∀ i,2≤ (B i).card)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤ M*Ae Finset.univ x)
    (f:ℂ→ ℝ) (hbound:∀ z,|f z|≤ H)
    (hcont:∀ z z',‖z-z'‖<2*ε → |f z-f z'|≤ η)
    (hout:∀ z,R<‖z‖ → |f z|≤ η) :
    Bc w B (fun x=> f ((Real.exp m:ℂ)*u x+b)) ≤
      2*η+H*(Ac d.mass (Aj w B T)/δ+
        ((2*N+1)^2:ℕ)*(δ+(M+1)*T/Fintype.card P)):=by
  have hq (C):0≤ Aj w B T C:=Bw w B T hw C
  have hi:=d.Er hn _ (EL w B T hT hB)
  have hsum (r):0≤ d.Ch (Aj w B T) r:=by
    rw [d.Fe]
    exact Finset.sum_nonneg (fun C _=> mul_nonneg (d.HK r C) (hq C))
  let a:=2*η+H*((((2*N+1)^2:ℕ):ℝ)*(δ+(M+1)*T/Fintype.card P))
  have hh:=PW _ hi hsum (m-Real.log ε)
    (Bc w B (fun x=> f ((Real.exp m:ℂ)*u x+b))) a (H/δ) (by positivity) ?_
  · rw [d.DB hn _ (EL w B T hT hB)] at hh
    convert hh using 1; simp only [a,Ac]; ring
  · intro r hr
    have hs:=Ao.PM ω m ε r hε hr
    obtain ⟨A,v,hA,hAc,hf,hv⟩:=RI d u ω r m b (by omega) (hshare r)
      R (ε/(2*Real.exp 1)) η H ε N hR (by positivity) hs.1 hs.2 hN f hbound hcont hout
    have h:=Iz d r A (((2*N+1)^2:ℕ):ℝ) M T δ η H w B
      (by omega) hA (by exact_mod_cast hAc) hw hW
      (fun i=> Finset.card_pos.mp (by have:=hB i; omega)) hM (by linarith) hδ hη hH hdom _ v hf hv
    convert h using 1; simp only [a]; ring
variable {K:Type u10} [Field K] [NumberField K]
omit [NumberField K] in
lemma QV (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
    (v:InfinitePlace K) (m:ℝ) (b:ℂ) (hn:2≤ Fintype.card P)
    (R ε η H M T δ:ℝ) (N:ℕ) (hR:0≤ R) (hε:0<ε)
    (hN:2*R/(ε/(2*Real.exp 1))+1≤ N)
    (hη:0≤ η) (hH:0≤ H) (hM:0≤ M) (hT:1≤ T) (hδ:0<δ)
    (w:I→ ℝ) (B:I→ Finset P)
    (hw:∀ i,0≤ w i) (hW:∑ i,w i≤ 1) (hB:∀ i,2≤ (B i).card)
    (hdom:∀ x,(∑ i,w i*Ae (B i) x)≤ M*Ae Finset.univ x)
    (f:ℂ→ ℝ) (hbound:∀ z,|f z|≤ H)
    (hcont:∀ z z',‖z-z'‖<2*ε → |f z-f z'|≤ η)
    (hout:∀ z,R<‖z‖ → |f z|≤ η) :
    Bc w B (fun x=> f ((Real.exp m:ℂ)*v.embedding (Z₁ x)+b)) ≤
      2*η+H*(BD Z₁ Z₂ (Bm (Aj w B T)) v/δ+
        ((2*N+1)^2:ℕ)*(δ+(M+1)*T/Fintype.card P)):=by
  let D:=Bc w B (fun x=> f ((Real.exp m:ℂ)*v.embedding (Z₁ x)+b))
  let a:=2*η+H*((((2*N+1)^2:ℕ):ℝ)*(δ+(M+1)*T/Fintype.card P))
  let q:=Aj w B T
  have hq (C):0≤ q C:=Bw w B T hw C
  have hi:=Cm Z₁ Z₂ h₁ h₂ hn q v
  have hh:∀ᵐ ω ∂ Ao.As,D≤ a+(H/δ)*Bm q (arch Z₁ v ω) (arch Z₂ v ω):=by
    filter_upwards [RU Z₁ h₁ v] with ω hω
    have hh:=Mq (arch Z₁ v ω) (fun x=> v.embedding (Z₁ x)) ω m b hn hω
      R ε η H M T δ N hR hε hN hη hH hM hT hδ w B hw hW hB hdom f hbound hcont hout
    have hmass:Ac (arch Z₁ v ω).mass q≤ Bm q (arch Z₁ v ω) (arch Z₂ v ω):=by
      apply le_add_of_nonneg_right
      exact Finset.sum_nonneg (fun C _=> mul_nonneg ((arch Z₂ v ω).Bf C) (hq C))
    have he:2*η+H*(Ac (arch Z₁ v ω).mass q/δ+
        ((2*N+1)^2:ℕ)*(δ+(M+1)*T/Fintype.card P))=a+(H/δ)*Ac (arch Z₁ v ω).mass q:=by
      simp only [a]; ring
    rw [show Aj w B T=q from rfl,he] at hh
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass (by positivity)))
  have hh':=integral_mono_ae (integrable_const D) ((integrable_const a).add (hi.const_mul (H/δ))) hh
  simp only [Pi.add_apply] at hh'
  rw [integral_add (integrable_const a) (hi.const_mul (H/δ)),integral_const_mul] at hh'
  simp only [integral_const,probReal_univ,one_smul] at hh'
  calc
    _≤ a+(H/δ)*BD Z₁ Z₂ (Bm q) v:=hh'
    _= _:=by dsimp only [a,q]; ring
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11
section
noncomputable section
open scoped BigOperators Topology ZeroAtInfty
open Filter MeasureTheory
namespace Aa.Bounded
lemma QR (D V A:ℕ→ ℝ) (H M:ℝ)
    (hD:∀ n,0≤ D n) (hH:0≤ H)
    (hV:Tendsto V atTop (𝓝 0)) (hA:Tendsto A atTop (𝓝 0))
    (h:∀ η,0<η→∃ N:ℝ,0≤ N∧∀ δ,0<δ →
      ∀ n,D n≤ 2*η+H*(V n/δ+N*(δ+(M+1)*A n))) :
    Tendsto D atTop (𝓝 0):=by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n=> ha.trans_le (hD n))
  · intro b hb
    obtain ⟨N,hN,h⟩:=h (b/8) (by positivity)
    let δ:=b/(4*(H*N+1))
    have hδ:0<δ:=by dsimp [δ]; positivity
    have he:(H*N+1)*δ=b/4:=by dsimp [δ]; field_simp
    have hNd:H*N*δ≤ b/4:=by nlinarith
    have hlt:2*(b/8)+H*(0/δ+N*(δ+(M+1)*0))<b:=by simp only [zero_div,mul_zero,add_zero]; nlinarith
    have ht:=(tendsto_const_nhds.add ((hV.div_const δ).add
      ((tendsto_const_nhds.add (hA.const_mul (M+1))).const_mul N) |>.const_mul H)).eventually
      (eventually_lt_nhds hlt)
    exact ht.mono (fun n hn=>(h δ hδ n).trans_lt hn)
lemma PC (f:C₀(ℂ,ℝ)) (η:ℝ) (hη:0<η) :
    ∃ R:ℝ,0≤ R∧∀ z,R<‖z‖ → |f z|≤ η:=by
  have hf:=(Metric.tendsto_nhds.mp (zero_at_infty f) η hη)
  obtain ⟨K,hK,hsub⟩:=mem_cocompact.mp hf
  obtain ⟨R,hR⟩:=hK.isBounded.subset_closedBall (0:ℂ)
  refine ⟨max R 0,le_max_right _ _,?_⟩
  intro z hz
  have hzK:z∉K:=by
    intro hzK
    have hh:=Metric.mem_closedBall.mp (hR hzK)
    simp only [dist_zero_right] at hh
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_left _ _) hz)) hh
  simpa only [Real.dist_eq,sub_zero] using (show dist (f z) 0<η from hsub hzK).le
lemma MU (f:C₀(ℂ,ℝ)) (η:ℝ) (hη:0<η) :
    ∃ ε:ℝ,0<ε∧∀ z w,‖z-w‖<2*ε → |f z-f w|≤ η:=by
  obtain ⟨δ,hδ,hd⟩:=Metric.uniformContinuous_iff.mp (ZeroAtInftyContinuousMap.uniformContinuous f) η hη
  refine ⟨δ/2,by positivity,?_⟩
  intro z w hzw
  have hh:=hd (show dist z w<δ by rw [dist_eq_norm]; linarith)
  exact (by simpa only [Real.dist_eq] using hh.le)
def Qv (f:C(Sphere,ℝ)):C₀(ℂ,ℝ) where
  toFun:=fun z=> f (z:Sphere)-f OnePoint.infty
  continuous_toFun:=(f.continuous.comp OnePoint.continuous_coe).sub continuous_const
  zero_at_infty':=by
    have hco:Tendsto ((↑):ℂ→ Sphere) (cocompact ℂ) (𝓝 OnePoint.infty) :=
      OnePoint.tendsto_coe_infty.mono_left cocompact_le_coclosedCompact
    simpa using ((f.continuous.tendsto OnePoint.infty).comp hco).sub_const (f OnePoint.infty)
lemma PR (f:C(Sphere,ℝ)) (z:ℂ) : |Qv f z|≤ 2*‖f‖:=by
  have h₁:=f.norm_coe_le_norm (z:Sphere)
  have h₂:=f.norm_coe_le_norm OnePoint.infty
  change |f (z:Sphere)-f OnePoint.infty|≤ 2*‖f‖
  simpa only [Real.norm_eq_abs,two_mul] using
    (norm_sub_le (f (z:Sphere)) (f OnePoint.infty)).trans (add_le_add h₁ h₂)
end Aa.Bounded
end
end
section
noncomputable section
open scoped BigOperators Topology ZeroAtInfty
open Filter MeasureTheory
namespace Aa.Bounded
open Ak Variance Bg NumberField
variable {P:Type u1} {I:Type u2} [Fintype P] [DecidableEq P] [Fintype I]
lemma Ma (w:I→ ℝ) (B:I→ Finset P) (f:P→ ℝ) (c:ℝ)
    (hn:0<Fintype.card P) (hB:∀ i,(B i).Nonempty) :
    Bc w B (fun x=> f x-c)=Bc w B f:=by
  have hh (S:Finset P) (hS:S.Nonempty) :
      (∑ x,Ae S x*(f x-c))=(∑ x,Ae S x*f x)-c:=by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,Bs S hS,one_mul]
  unfold Bc
  simp_rw [hh _ (hB _),hh Finset.univ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn))]
  simp only [sub_sub_sub_cancel_right]
variable {V:ℕ→ Type u3} {J:ℕ→ Type u4} {K:ℕ→ Type u5}
  [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (J n)]
  [∀ n,Field (K n)] [∀ n,NumberField (K n)]
omit [∀ (n:ℕ),NumberField (K n)] in
lemma OF (Z₁ Z₂:∀ n,V n→ K n)
    (h₁:∀ n,Function.Injective (Z₁ n)) (h₂:∀ n,Function.Injective (Z₂ n))
    (v:∀ n,InfinitePlace (K n)) (m:ℕ→ ℝ) (b:ℕ→ ℂ)
    (w:∀ n,J n→ ℝ) (B:∀ n,J n→ Finset (V n)) (T:ℕ→ ℝ) (M H:ℝ)
    (hn:∀ n,2≤ Fintype.card (V n)) (hT:∀ n,1≤ T n) (hM:0≤ M) (hH:0≤ H)
    (hw:∀ n i,0≤ w n i) (hW:∀ n,∑ i,w n i≤ 1) (hB:∀ n i,2≤ (B n i).card)
    (hdom:∀ n x,(∑ i,w n i*Ae (B n i) x)≤ M*Ae Finset.univ x)
    (hvar:Tendsto (fun n=> BD (Z₁ n) (Z₂ n) (Bm (Aj (w n) (B n) (T n))) (v n)) atTop (𝓝 0))
    (hsmall:Tendsto (fun n=> T n/Fintype.card (V n)) atTop (𝓝 0))
    (f:C₀(ℂ,ℝ)) (hbound:∀ z,|f z|≤ H) :
    Tendsto (fun n=> Bc (w n) (B n)
      (fun x=> f ((Real.exp (m n):ℂ)*(v n).embedding (Z₁ n x)+b n))) atTop (𝓝 0):=by
  apply QR _ _ _ H M (fun n=> Om _ _ _ (hw n)) hH hvar hsmall
  intro η hη
  obtain ⟨R,hR,hout⟩:=PC f η hη
  obtain ⟨ε,hε,hcont⟩:=MU f η hη
  obtain ⟨N,hN⟩:=exists_nat_ge (2*R/(ε/(2*Real.exp 1))+1)
  refine ⟨((2*N+1)^2:ℕ),by positivity,?_⟩
  intro δ hδ n
  have hh:=QV (Z₁ n) (Z₂ n) (h₁ n) (h₂ n) (v n) (m n) (b n) (hn n)
    R ε η H M (T n) δ N hR hε hN hη.le hH hM (hT n) hδ
    (w n) (B n) (hw n) (hW n) (hB n) (hdom n) f hbound hcont hout
  convert hh using 1
  ring
omit [∀ (n:ℕ),NumberField (K n)] in
lemma Fa (Z₁ Z₂:∀ n,V n→ K n)
    (h₁:∀ n,Function.Injective (Z₁ n)) (h₂:∀ n,Function.Injective (Z₂ n))
    (v:∀ n,InfinitePlace (K n)) (m:ℕ→ ℝ) (b:ℕ→ ℂ)
    (w:∀ n,J n→ ℝ) (B:∀ n,J n→ Finset (V n)) (T:ℕ→ ℝ) (M:ℝ)
    (hn:∀ n,2≤ Fintype.card (V n)) (hT:∀ n,1≤ T n) (hM:0≤ M)
    (hw:∀ n i,0≤ w n i) (hW:∀ n,∑ i,w n i≤ 1) (hB:∀ n i,2≤ (B n i).card)
    (hdom:∀ n x,(∑ i,w n i*Ae (B n i) x)≤ M*Ae Finset.univ x)
    (hvar:Tendsto (fun n=> BD (Z₁ n) (Z₂ n) (Bm (Aj (w n) (B n) (T n))) (v n)) atTop (𝓝 0))
    (hsmall:Tendsto (fun n=> T n/Fintype.card (V n)) atTop (𝓝 0))
    (f:C(Sphere,ℝ)) :
    Tendsto (fun n=> Bc (w n) (B n)
      (fun x=> f (((Real.exp (m n):ℂ)*(v n).embedding (Z₁ n x)+b n):Sphere))) atTop (𝓝 0):=by
  have ht:=OF Z₁ Z₂ h₁ h₂ v m b w B T M (2*‖f‖) hn hT hM (by positivity)
    hw hW hB hdom hvar hsmall (Qv f) (PR f)
  convert ht using 1
  funext n
  symm
  apply Ma _ _ _ _ (by have:=hn n; omega)
  intro i
  exact Finset.card_pos.mp (by have:=hB n i; omega)
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Aa.Bounded
open Variance
variable {V:Type u6} {I:Type u7} [Fintype V] [DecidableEq V] [Fintype I]
variable (G:Core.Au V I)
omit [Fintype I] in
lemma KZ (T H:ℝ) (hT:0<T) (hn:2≤Fintype.card V)
    (f:V→ ℝ) (hf:∀ x,|f x|≤H) :
    (∑ y,G.Ax y*|(∑ x,G.AY y x*f x)-∑ x,Ae Finset.univ x*f x|)≤
      Bc (G.Ay T) (G.Aw T) f+2*H*G.BF T:=by
  have hA : |∑ x,Ae (Finset.univ:Finset V) x*f x|≤H :=
    Fx _ _ _ (Core.Au.DK _) (Bs _
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))) hf
  unfold Bc Core.Au.BF
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy:T≤((G.BV y).card:ℝ)
  · have hne:(G.BV y).Nonempty:=Finset.card_pos.mp (by exact_mod_cast hT.trans_le hy)
    simp only [Core.Au.Ay,Core.Au.Aw,Core.Au.AY,
      if_pos hy,if_pos hne,not_lt_of_ge hy,ite_false,mul_zero,add_zero]
    exact le_rfl
  · have hbound : |(∑ x,G.AY y x*f x)-∑ x,Ae Finset.univ x*f x|≤2*H:=by
      have hh:=Fx _ _ _ (G.Ep y) (G.Fb hn y) hf
      exact (abs_sub _ _).trans (by linarith)
    simp only [Core.Au.Ay,if_neg hy,lt_of_not_ge hy,ite_true,zero_mul,zero_add]
    nlinarith [mul_le_mul_of_nonneg_left hbound (G.Cs y)]
lemma Nk (T H C:ℝ) (hT:0<T) (hn:2≤Fintype.card V)
    (f g:V→ ℝ) (hf:∀ x,|f x|≤H) (hg:∀ y,|g y|≤C) :
    |(∑ e,G.Af e*∑ y,Ae (G.targets e) y*(f (G.source e)*g y))-
      (∑ x,Ae Finset.univ x*f x)*(∑ y,G.Ax y*g y)|≤
      C*(Bc (G.Ay T) (G.Aw T) f+2*H*G.BF T):=by
  have hC:0≤C:=(abs_nonneg (g (Classical.choice (Fintype.card_pos_iff.mp (by omega))))).trans (hg _)
  rw [← G.IV (fun x y=> f x*g y)]
  have he:(∑ y,G.Ax y*∑ x,G.AY y x*(f x*g y))-
      (∑ x,Ae Finset.univ x*f x)*(∑ y,G.Ax y*g y)=
      ∑ y,G.Ax y*((∑ x,G.AY y x*f x)-∑ x,Ae Finset.univ x*f x)*g y:=by
    simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  calc
    _≤∑ y,|G.Ax y*((∑ x,G.AY y x*f x)-∑ x,Ae Finset.univ x*f x)*g y| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤ C*(∑ y,G.Ax y*|(∑ x,G.AY y x*f x)-∑ x,Ae Finset.univ x*f x|):=by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul,abs_mul,abs_of_nonneg (G.Cs y)]
      nlinarith [mul_le_mul_of_nonneg_left (hg y) (mul_nonneg (G.Cs y) (abs_nonneg ((∑ x,G.AY y x*f x)-∑ x,Ae Finset.univ x*f x)))]
    _≤ _:=mul_le_mul_of_nonneg_left (KZ G T H hT hn f hf) hC
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace Aa.Bounded
open Variance
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
local instance:MeasurableSingletonClass (BO Sphere):=inferInstance
local instance:MeasurableSingletonClass ((Sphere × Sphere) × (Sphere × Sphere)):=inferInstance
local instance:MeasurableSingletonClass (Expanded Sphere):=Prod.instMeasurableSingletonClass
variable {V:Type u8} {I:Type u9} [Fintype V] [DecidableEq V] [Fintype I]
variable (G:Core.Au V I)
omit G [Fintype I] in
lemma FH (U:V→ Sphere) (f:Sphere→ ℝ) :
    (∫ z,f z ∂ Bv U)=∑ x,Ae Finset.univ x*f (U x):=by
  rw [Bv,DP _ _ (fun _=> inv_nonneg.mpr (Nat.cast_nonneg _))]
  simp only [Ae,Finset.mem_univ,ite_true,Finset.card_univ,one_div]
lemma Em (U₁ U₂:V→ Sphere) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty) (f:BO Sphere→ ℝ) :
    (∫ q,f q ∂ (Ba G U₁ U₂ hG hB:Measure (BO Sphere)))=
      ∑ e,G.Af e*∑ y,Ae (G.targets e) y*f (Fh G.source U₁ U₂ (e,y)):=by
  change (∫ q,f q ∂ AM _ _)=_
  rw [DP _ _ (Gt G)]
  simp only [BU,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum]
lemma Ij (U₁ U₂:V→ Sphere) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty) (f:Expanded Sphere→ ℝ) :
    (∫ r,f r ∂ (Bk G U₁ U₂ hG hB:Measure (Expanded Sphere)))=
      ∑ r,BT G.Af (fun e=> Ae (G.targets e)) r*f (Ee G.source U₁ U₂ r):=by
  change (∫ r,f r ∂ AM (BT G.Af (fun e=> Ae (G.targets e))) (Ee G.source U₁ U₂))=_
  exact DP _ _ (FJ G) f
lemma Np (U₁ U₂:V→ Sphere) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty) (hn:2≤Fintype.card V)
    (π:Sphere × Sphere→ Sphere) (f:BO Sphere→ ℝ) (g h:Sphere→ ℝ) (C H₁ H₂:ℝ)
    (hC:0≤C) (hf:∀ q,|f q|≤C) (hg:∀ z,|g z|≤H₁) (hh:∀ z,|h z|≤H₂) :
    |(∫ r,f r.1*g (π r.2.1)*h (π r.2.2) ∂ (Bk G U₁ U₂ hG hB:Measure (Expanded Sphere)))-
      (∫ q,f q ∂ (Ba G U₁ U₂ hG hB:Measure (BO Sphere)))*
        (∫ z,g z ∂ Bv (fun x=> π (U₁ x,U₂ x)))*(∫ z,h z ∂ Bv (fun x=> π (U₁ x,U₂ x)))|≤
      C*(H₂*Bc G.Af G.targets (fun x=> g (π (U₁ x,U₂ x)))+
        H₁*Bc G.Af G.targets (fun x=> h (π (U₁ x,U₂ x)))):=by
  rw [Ij,Em,FH,FH]
  have hA : |∑ x,Ae (Finset.univ:Finset V) x*g (π (U₁ x,U₂ x))|≤H₁:=by
    exact Fx _ _ _ (Core.Au.DK _) (Bs _
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))) (fun x=> hg _)
  have hb:=Ks G.Af (fun e=> Ae (G.targets e))
    (fun e y=> f (Fh G.source U₁ U₂ (e,y))) (fun x=> g (π (U₁ x,U₂ x))) (fun x=> h (π (U₁ x,U₂ x)))
    (∑ x,Ae Finset.univ x*g (π (U₁ x,U₂ x))) (∑ x,Ae Finset.univ x*h (π (U₁ x,U₂ x)))
    C H₁ H₂ G.AT (fun e=> Core.Au.DK _) (fun e=> Bs _ (hB e))
    hC (fun e y=> hf _) (fun x=> hh _) hA
  simpa only [Ee,Bc,BU,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum] using hb
lemma QK (U₁ U₂:V→ Sphere) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty) (g:Sphere × Sphere→ ℝ) :
    (∫ q,g q.2.2 ∂ (Ba G U₁ U₂ hG hB:Measure (BO Sphere)))=
      ∑ y,G.Ax y*g (U₁ y,U₂ y):=by
  rw [Em]
  simp only [Fh,Finset.mul_sum,← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_mul,G.Ir,G.GF]
lemma Kl (U₁ U₂:V→ Sphere) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty) (hn:2≤Fintype.card V) (T H C:ℝ) (hT:0<T)
    (f:Sphere→ ℝ) (g:Sphere × Sphere→ ℝ) (hf:∀ z,|f z|≤H) (hg:∀ z,|g z|≤C) :
    |(∫ q,f q.1*g q.2.2 ∂ (Ba G U₁ U₂ hG hB:Measure (BO Sphere)))-
      (∫ z,f z ∂ Bv U₁)*(∫ q,g q.2.2 ∂ (Ba G U₁ U₂ hG hB:Measure (BO Sphere)))|≤
      C*(Bc (G.Ay T) (G.Aw T) (fun x=> f (U₁ x))+2*H*G.BF T):=by
  rw [QK,Em,FH]
  exact Nk G T H C hT hn (fun x=> f (U₁ x)) (fun x=> g (U₁ x,U₂ x))
    (fun x=> hf _) (fun x=> hg _)
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace Aa.Bounded
local instance:MeasurableSpace Sphere:=borel Sphere
variable {V:ℕ→ Type u10} {I:ℕ→ Type u11} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]
variable (G:∀ n,Core.Au (V n) (I n)) (U₁ U₂:∀ n,V n→ Sphere)
  (hG:∀ n,0<(G n).Ap) (hB:∀ n e,((G n).targets e).Nonempty)
  (hn:∀ n,2≤Fintype.card (V n))
include hn
lemma NR (π:Sphere × Sphere→ Sphere)
    (hd:∀ f:C(Sphere,ℝ),Tendsto (fun n=> Bc (G n).Af (G n).targets
      (fun x=> f (π (U₁ n x,U₂ n x)))) atTop (𝓝 0))
    (f:BO Sphere →ᵇ ℝ) (g h:Sphere →ᵇ ℝ) :
    Tendsto (fun n=>(∫ r,f r.1*g (π r.2.1)*h (π r.2.2)
      ∂ (Bk (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (Expanded Sphere)))-
      (∫ q,f q ∂ (Ba (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (BO Sphere)))*
        (∫ z,g z ∂ Bv (fun x=> π (U₁ n x,U₂ n x)))*
        (∫ z,h z ∂ Bv (fun x=> π (U₁ n x,U₂ n x)))) atTop (𝓝 0):=by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have ht:=((hd g.toContinuousMap).const_mul ‖h‖ |>.add
    ((hd h.toContinuousMap).const_mul ‖g‖)).const_mul ‖f‖
  simp only [mul_zero,zero_add] at ht
  apply squeeze_zero (fun n=> abs_nonneg _) (fun n => ?_) ht
  exact Np (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) π f g h
    ‖f‖ ‖g‖ ‖h‖ (norm_nonneg _) (fun q=> by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm q)
    (fun z=> by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm z)
    (fun z=> by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm z)
lemma Ll (T:ℕ→ ℝ) (hT:∀ n,0<T n)
    (hd:∀ f:C(Sphere,ℝ),Tendsto (fun n=> Bc ((G n).Ay (T n))
      ((G n).Aw (T n)) (fun x=> f (U₁ n x))) atTop (𝓝 0))
    (ho:Tendsto (fun n=>(G n).BF (T n)) atTop (𝓝 0))
    (f:Sphere →ᵇ ℝ) (g:Sphere × Sphere →ᵇ ℝ) :
    Tendsto (fun n=>(∫ q,f q.1*g q.2.2 ∂ (Ba (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (BO Sphere)))-
      (∫ z,f z ∂ Bv (U₁ n))*(∫ q,g q.2.2 ∂ (Ba (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (BO Sphere))))
      atTop (𝓝 0):=by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have ht:=((hd f.toContinuousMap).add (ho.const_mul (2*‖f‖))).const_mul ‖g‖
  simp only [mul_zero,zero_add] at ht
  apply squeeze_zero (fun n=> abs_nonneg _) (fun n => ?_) ht
  exact Kl (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) (T n) ‖f‖ ‖g‖ (hT n) f g
    (fun z=> by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm z)
    (fun z=> by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm z)
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace Aa.Bounded
variable {E:Type u1} {X:Type u2} {J:Type u3} [MeasurableSpace E] [MeasurableSpace X]
  [TopologicalSpace E] [TopologicalSpace X] [BorelSpace E] [BorelSpace X]
  [SecondCountableTopology E] [SecondCountableTopology X]
  [HasOuterApproxClosed E] [HasOuterApproxClosed X] [Fintype J]
omit [SecondCountableTopology E] in
lemma Ox
    (Rn:ℕ→ ProbabilityMeasure (E × (J→ X))) (R:ProbabilityMeasure (E × (J→ X)))
    (Qn:ℕ→ ProbabilityMeasure E) (Q:ProbabilityMeasure E)
    (αn:ℕ→ J→ ProbabilityMeasure X) (β:J→ ProbabilityMeasure X)
    (hR:Tendsto Rn atTop (𝓝 R)) (hQ:Tendsto Qn atTop (𝓝 Q))
    (hα:∀ j,Tendsto (fun n=> αn n j) atTop (𝓝 (β j)))
    (herr:∀ (f:E →ᵇ ℝ) (g:J→ X →ᵇ ℝ),
      Tendsto (fun n=>(∫ p,f p.1*(∏ j,g j (p.2 j)) ∂ (Rn n:Measure (E × (J→ X))))-
        (∫ e,f e ∂ (Qn n:Measure E))*(∏ j,∫ x,g j x ∂ (αn n j:Measure X))) atTop (𝓝 0)) :
    (R:Measure (E × (J→ X)))=(Q:Measure E).prod (Measure.pi (fun j=>(β j:Measure X))):=by
  apply Measure.eq_prod_of_integral_mul_prod_boundedContinuousFunction
  intro f g
  let F:E × (J→ X) →ᵇ ℝ :=
    f.compContinuous ⟨Prod.fst,continuous_fst⟩ *
      ∏ j,(g j).compContinuous ⟨fun p:E × (J→ X)=> p.2 j,by fun_prop⟩
  have hRf:=ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hR F
  have hQf:=ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ f
  have hβg (j):=ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (hα j) (g j)
  have ht:=hRf.sub (hQf.mul (tendsto_finsetProd Finset.univ (fun j _=> hβg j)))
  have hF (p:E × (J→ X)):F p=f p.1*∏ j,g j (p.2 j):=by simp [F]
  simp only [hF] at ht
  have he:=tendsto_nhds_unique ht (herr f g)
  rw [integral_fintype_prod_eq_prod]
  exact sub_eq_zero.mp he
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace Aa.Bounded
lemma Ku {X:Type u4} {Y:Type u5} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
    [HasOuterApproxClosed X] [HasOuterApproxClosed Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    (Rn:ℕ→ ProbabilityMeasure (X × Y)) (R:ProbabilityMeasure (X × Y))
    (μn:ℕ→ ProbabilityMeasure X) (μ:ProbabilityMeasure X)
    (νn:ℕ→ ProbabilityMeasure Y) (ν:ProbabilityMeasure Y)
    (hR:Tendsto Rn atTop (𝓝 R)) (hμ:Tendsto μn atTop (𝓝 μ)) (hν:Tendsto νn atTop (𝓝 ν))
    (herr:∀ (f:X →ᵇ ℝ) (g:Y →ᵇ ℝ),
      Tendsto (fun n=>(∫ p,f p.1*g p.2 ∂ (Rn n:Measure (X × Y)))-
        (∫ x,f x ∂ (μn n:Measure X))*(∫ y,g y ∂ (νn n:Measure Y))) atTop (𝓝 0)) :
    (R:Measure (X × Y))=(μ:Measure X).prod (ν:Measure Y):=by
  apply Measure.eq_prod_of_integral_mul_boundedContinuousFunction
  intro f g
  let F:X × Y →ᵇ ℝ:=f.compContinuous ⟨Prod.fst,continuous_fst⟩ *
    g.compContinuous ⟨Prod.snd,continuous_snd⟩
  have ht:=(ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hR F).sub
    ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f).mul
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν g))
  exact sub_eq_zero.mp (tendsto_nhds_unique ht (herr f g))
lemma Rs {T:Type u6} {E:Type u7} {X:Type u8} [MeasurableSpace T] [MeasurableSpace E] [MeasurableSpace X]
    (R:Measure T) (Q:Measure E) (μ:Measure X) [SFinite Q] [IsFiniteMeasure μ]
    (e:T→ E) (z w:T→ X) (he:Measurable e) (hz:Measurable z) (hw:Measurable w)
    (hm:R.map (fun r=>(e r,![z r,w r]))=Q.prod (Measure.pi (fun _:Fin 2=> μ))) :
    R.map (fun r=>(e r,(z r,w r)))=Q.prod (μ.prod μ):=by
  have hp:Measurable (fun r=>(e r,![z r,w r])):=by
    apply he.prodMk
    apply measurable_pi_lambda
    intro j
    fin_cases j
    · exact hz
    · exact hw
  let hme:=MeasurableEquiv.finTwoArrow (α:=X)
  have hm2:Measurable (Prod.map (id:E→ E) hme):=measurable_id.prodMap hme.measurable
  have hh:=congrArg (fun m:Measure (E × (Fin 2→ X))=> m.map (Prod.map id hme)) hm
  rw [Measure.map_map hm2 hp,← Measure.map_prod_map _ _ measurable_id hme.measurable,
    Measure.map_id,(measurePreserving_finTwoArrow μ).map_eq] at hh
  exact hh
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace Aa.Bounded
variable {E:Type u9} {X:Type u10} {T:Type u11} [MeasurableSpace E] [MeasurableSpace X] [MeasurableSpace T]
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace T]
  [BorelSpace E] [BorelSpace X] [BorelSpace T]
  [SecondCountableTopology E] [SecondCountableTopology X]
  [HasOuterApproxClosed E] [HasOuterApproxClosed X]
lemma Jw (Rn:ℕ→ ProbabilityMeasure T) (R:ProbabilityMeasure T)
    (Qn:ℕ→ ProbabilityMeasure E) (Q:ProbabilityMeasure E)
    (αn:ℕ→ ProbabilityMeasure X) (β:ProbabilityMeasure X)
    (e:T→ E) (z w:T→ X) (he:Continuous e) (hz:Continuous z) (hw:Continuous w)
    (hR:Tendsto Rn atTop (𝓝 R)) (hQ:Tendsto Qn atTop (𝓝 Q)) (hα:Tendsto αn atTop (𝓝 β))
    (herr:∀ (f:E →ᵇ ℝ) (g h:X →ᵇ ℝ),
      Tendsto (fun n=>(∫ r,f (e r)*g (z r)*h (w r) ∂ (Rn n:Measure T))-
        (∫ q,f q ∂ (Qn n:Measure E))*(∫ x,g x ∂ (αn n:Measure X))*
          (∫ x,h x ∂ (αn n:Measure X))) atTop (𝓝 0)) :
    (R:Measure T).map (fun r=>(e r,(z r,w r)))=(Q:Measure E).prod ((β:Measure X).prod β):=by
  let k:T→ E × (Fin 2→ X):=fun r=>(e r,![z r,w r])
  have hk:Continuous k:=by
    apply he.prodMk
    apply continuous_pi
    intro i
    fin_cases i
    · exact hz
    · exact hw
  have hRm:=ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Rn R hR hk
  have hh:=Ox (fun n=>(Rn n).map hk.measurable.aemeasurable)
    (R.map hk.measurable.aemeasurable) Qn Q (fun n _=> αn n) (fun _:Fin 2=> β) hRm hQ (fun _=> hα) ?_
  · exact Rs (R:Measure T) (Q:Measure E) (β:Measure X) e z w he.measurable hz.measurable hw.measurable hh
  · intro f g
    have hl:=herr f (g 0) (g 1)
    convert hl using 1
    funext n
    rw [show ((Rn n).map hk.measurable.aemeasurable:Measure (E × (Fin 2→ X)))=(Rn n:Measure T).map k from rfl]
    rw [integral_map_of_stronglyMeasurable hk.measurable (by fun_prop)]
    simp only [Fin.prod_univ_two,k,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,mul_assoc]
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace Aa.Bounded
variable {X:Type u12} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X]
lemma GC (μ ν:Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h:∀ f:X →ᵇ ℝ≥0,(∫⁻ x,f x ∂ μ)≤∫⁻ x,f x ∂ ν):μ≤ν:=by
  have hclosed (K:Set X) (hK:IsClosed K):μ K≤ν K:=by
    exact le_of_tendsto_of_tendsto
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hK μ)
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hK ν)
      (Eventually.of_forall (fun n=> h (hK.apprSeq n)))
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top μ s)]
  exact iSup_le (fun K=> iSup_le (fun hKs=> iSup_le (fun hK=>(hclosed K hK).trans (measure_mono hKs))))
lemma QZ (μn νn:ℕ→ ProbabilityMeasure X) (μ ν:ProbabilityMeasure X)
    (hμ:Tendsto μn atTop (𝓝 μ)) (hν:Tendsto νn atTop (𝓝 ν)) (c:ℝ≥0)
    (hle:∀ n,(μn n:Measure X)≤(c:ℝ≥0∞)•(νn n:Measure X)) :
    (μ:Measure X)≤(c:ℝ≥0∞)•(ν:Measure X):=by
  have:IsFiniteMeasure ((c:ℝ≥0∞)•(ν:Measure X)):=(ν:Measure X).smul_finite ENNReal.coe_ne_top
  apply GC
  intro f
  have hμf:=ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hμ f
  have hνf:=ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hν f
  rw [lintegral_smul_measure]
  apply le_of_tendsto_of_tendsto hμf
    (ENNReal.Tendsto.const_mul hνf (Or.inr ENNReal.coe_ne_top))
  filter_upwards [] with n
  simpa only [lintegral_smul_measure,smul_eq_mul] using lintegral_mono' (hle n) (le_refl (fun x=>(f x:ℝ≥0∞)))
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace Aa.Bounded
variable {X:Type u13} {Y:Type u14} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
  [HasOuterApproxClosed Y]
lemma Td (αn:ℕ→ ProbabilityMeasure X) (α:ProbabilityMeasure X)
    (βn:ℕ→ ProbabilityMeasure Y) (β:ProbabilityMeasure Y)
    (f:X→ Y) (hf:Continuous f) (hα:Tendsto αn atTop (𝓝 α))
    (hβ:Tendsto βn atTop (𝓝 β)) (hm:∀ n,(αn n:Measure X).map f=(βn n:Measure Y)) :
    (α:Measure X).map f=(β:Measure Y):=by
  have he (n):(αn n).map hf.measurable.aemeasurable=βn n:=ProbabilityMeasure.toMeasure_injective (hm n)
  have hl:=ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous αn α hα hf
  simp only [he] at hl
  exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hl hβ)
omit [HasOuterApproxClosed Y] in
lemma HZ [TopologicalSpace.PseudoMetrizableSpace Y]
    (αn:ℕ→ ProbabilityMeasure X) (α:ProbabilityMeasure X)
    (βn:ℕ→ ProbabilityMeasure Y) (β:ProbabilityMeasure Y)
    (f:X→ Y) (hf:Continuous f) (hα:Tendsto αn atTop (𝓝 α))
    (hβ:Tendsto βn atTop (𝓝 β)) (c:ℝ≥0)
    (hm:∀ n,(αn n:Measure X).map f≤(c:ℝ≥0∞)•(βn n:Measure Y)) :
    (α:Measure X).map f≪(β:Measure Y):=by
  have hl:=QZ (fun n=>(αn n).map hf.measurable.aemeasurable)
    βn (α.map hf.measurable.aemeasurable) β
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous αn α hα hf) hβ c hm
  exact Measure.absolutelyContinuous_of_le_smul hl
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction NNReal ENNReal
namespace Aa.Bounded
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
variable {V:ℕ→ Type u1} {I:ℕ→ Type u2} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]
variable (G:∀ n,Core.Au (V n) (I n)) (U₁ U₂:∀ n,V n→ Sphere)
  (hG:∀ n,0<(G n).Ap) (hB:∀ n e,((G n).targets e).Nonempty)
  (hn:∀ n,2≤Fintype.card (V n))
lemma Gw (π:Sphere × Sphere→ Sphere) (hπ:Continuous π)
    (β:ProbabilityMeasure Sphere) (Q:ProbabilityMeasure (BO Sphere))
    (R:ProbabilityMeasure (Expanded Sphere))
    (hα:Tendsto (fun n=> Bj (fun x=> π (U₁ n x,U₂ n x)) (by have:=hn n;omega)) atTop (𝓝 β))
    (hQ:Tendsto (fun n=> Ba (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 Q))
    (hR:Tendsto (fun n=> Bk (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 R))
    (hd:∀ f:C(Sphere,ℝ),Tendsto (fun n=> Bc (G n).Af (G n).targets
      (fun x=> f (π (U₁ n x,U₂ n x)))) atTop (𝓝 0)) :
    (R:Measure (Expanded Sphere)).map (fun r=>(r.1,(π r.2.1,π r.2.2)))=
      (Q:Measure (BO Sphere)).prod ((β:Measure Sphere).prod β):=by
  apply Jw (fun n=> Bk (G n) (U₁ n) (U₂ n) (hG n) (hB n)) R
    (fun n=> Ba (G n) (U₁ n) (U₂ n) (hG n) (hB n)) Q
    (fun n=> Bj (fun x=> π (U₁ n x,U₂ n x)) (by have:=hn n;omega)) β
    Prod.fst (fun r=> π r.2.1) (fun r=> π r.2.2) continuous_fst
    (hπ.comp (continuous_fst.comp continuous_snd)) (hπ.comp (continuous_snd.comp continuous_snd)) hR hQ hα
  exact NR G U₁ U₂ hG hB hn π hd
lemma RL (T:ℕ→ ℝ) (hT:∀ n,0<T n)
    (β:ProbabilityMeasure Sphere) (Q:ProbabilityMeasure (BO Sphere))
    (hα:Tendsto (fun n=> Bj (U₁ n) (by have:=hn n;omega)) atTop (𝓝 β))
    (hQ:Tendsto (fun n=> Ba (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 Q))
    (hd:∀ f:C(Sphere,ℝ),Tendsto (fun n=> Bc ((G n).Ay (T n))
      ((G n).Aw (T n)) (fun x=> f (U₁ n x))) atTop (𝓝 0))
    (ho:Tendsto (fun n=>(G n).BF (T n)) atTop (𝓝 0)) :
    (Q:Measure (BO Sphere)).map (fun q=>(q.1,q.2.2))=
      (β:Measure Sphere).prod ((Q:Measure (BO Sphere)).map (fun q=> q.2.2)):=by
  let Qn:=fun n=> Ba (G n) (U₁ n) (U₂ n) (hG n) (hB n)
  have hc:Continuous (fun q:BO Sphere=>(q.1,q.2.2)):=by fun_prop
  have ht:Continuous (fun q:BO Sphere=> q.2.2):=by fun_prop
  apply Ku (fun n=>(Qn n).map hc.measurable.aemeasurable)
    (Q.map hc.measurable.aemeasurable)
    (fun n=> Bj (U₁ n) (by have:=hn n;omega)) β
    (fun n=>(Qn n).map ht.measurable.aemeasurable) (Q.map ht.measurable.aemeasurable)
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Qn Q hQ hc) hα
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Qn Q hQ ht)
  intro f g
  have hh:=Ll G U₁ U₂ hG hB hn T hT hd ho f g
  convert hh using 1
  funext n
  change (∫ q,f q.1*g q.2 ∂ (Qn n:Measure (BO Sphere)).map (fun q=>(q.1,q.2.2)))-
    (∫ z,f z ∂ Bv (U₁ n))*(∫ p,g p ∂ (Qn n:Measure (BO Sphere)).map (fun q=> q.2.2))=_
  rw [integral_map_of_stronglyMeasurable hc.measurable (by fun_prop),
    integral_map_of_stronglyMeasurable ht.measurable g.continuous.stronglyMeasurable]
lemma RX (β₁ β₂:ProbabilityMeasure Sphere) (Q:ProbabilityMeasure (BO Sphere))
    (hα₁:Tendsto (fun n=> Bj (U₁ n) (by have:=hn n;omega)) atTop (𝓝 β₁))
    (hα₂:Tendsto (fun n=> Bj (U₂ n) (by have:=hn n;omega)) atTop (𝓝 β₂))
    (hQ:Tendsto (fun n=> Ba (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 Q))
    (M:ℝ) (hM:0≤M) (hdom:∀ n x y,(G n).Av x y≤M*Variance.Az Finset.univ x y) :
    Measure.AbsolutelyContinuous ((Q:Measure (BO Sphere)).map (fun q=>(q.1,q.2.2.1))) ((β₁:Measure Sphere).prod β₁) ∧
    Measure.AbsolutelyContinuous ((Q:Measure (BO Sphere)).map (fun q=>(q.2.1,q.2.2.2))) ((β₂:Measure Sphere).prod β₂):=by
  let c:ℝ≥0:=⟨2*M,by positivity⟩
  have hc:(c:ℝ≥0∞)=ENNReal.ofReal (2*M):=by
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    rfl
  constructor
  · apply HZ
      (fun n=> Ba (G n) (U₁ n) (U₂ n) (hG n) (hB n)) Q
      (fun n=>(Bj (U₁ n) (by have:=hn n;omega)).prod
        (Bj (U₁ n) (by have:=hn n;omega))) (β₁.prod β₁)
      (fun q=>(q.1,q.2.2.1)) (by fun_prop) hQ
      (ProbabilityMeasure.continuous_prod.tendsto (β₁,β₁) |>.comp (hα₁.prodMk_nhds hα₁)) c
    intro n
    rw [hc]
    exact Lq (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) M hM (hdom n)
  · apply HZ
      (fun n=> Ba (G n) (U₁ n) (U₂ n) (hG n) (hB n)) Q
      (fun n=>(Bj (U₂ n) (by have:=hn n;omega)).prod
        (Bj (U₂ n) (by have:=hn n;omega))) (β₂.prod β₂)
      (fun q=>(q.2.1,q.2.2.2)) (by fun_prop) hQ
      (ProbabilityMeasure.continuous_prod.tendsto (β₂,β₂) |>.comp (hα₂.prodMk_nhds hα₂)) c
    intro n
    rw [hc]
    exact Lj (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) M hM (hdom n)
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Aa.Bounded
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
lemma Sm (q:BO Sphere)
    (h₁:(q.1,q.2.2.1)∈range Df) (h₂:(q.2.1,q.2.2.2)∈range Df) :
    q∈range CK:=by
  obtain ⟨⟨a,c⟩,ha⟩:=h₁
  obtain ⟨⟨b,d⟩,hb⟩:=h₂
  exact ⟨(a,b,c,d),by ext <;> simp_all [Df,CK,Prod.mk.injEq]⟩
lemma Pa (r:Expanded Sphere)
    (h₁:(r.1,(r.2.1.1,r.2.2.1))∈range (Prod.map CK Df))
    (h₂:(r.1,(r.2.1.2,r.2.2.2))∈range (Prod.map CK Df)) :
    r∈range BE:=by
  obtain ⟨⟨q,z,w⟩,hz⟩:=h₁
  obtain ⟨⟨q',v,t⟩,hv⟩:=h₂
  refine ⟨(q,((z,v),(w,t))),?_⟩
  have he:CK q=r.1:=congrArg Prod.fst hz
  have hz':=congrArg Prod.snd hz
  have hv':=congrArg Prod.snd hv
  apply Prod.ext he
  dsimp [BE]
  ext <;> simp_all [Df,Prod.mk.injEq]
lemma JJ {A:Type u3} {B:Type u4} {X:Type u5} {Y:Type u6} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y] (j:A→ X) (k:B→ Y)
    (hj:Measurable j) (hk:MeasurableEmbedding k)
    (f:A→ B) (g:X→ Y) (hf:Measurable f) (hg:Measurable g)
    (μ:Measure A) (ν:Measure B) (hcomm:k∘ f=g∘ j)
    (hm:(μ.map j).map g≪ν.map k):μ.map f≪ν:=by
  apply SX k hk
  rw [Measure.map_map hk.measurable hf,hcomm,← Measure.map_map hg hj]
  exact hm
lemma Ow (μ ν:Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q:Measure (BO Sphere))
    (h₁:Q.map (fun q=>(q.1,q.2.2.1))≪(μ.map OnePoint.some).prod (μ.map OnePoint.some))
    (h₂:Q.map (fun q=>(q.2.1,q.2.2.2))≪(ν.map OnePoint.some).prod (ν.map OnePoint.some)) :
    ∀ᵐ q ∂ Q,q∈range CK:=by
  have hpμ:=Go Df Bt.measurableEmbedding (μ.prod μ)
  have hpν:=Go Df Bt.measurableEmbedding (ν.prod ν)
  rw [← Measure.map_prod_map _ _ An.measurable
    An.measurable] at hpμ hpν
  have hq₁:=(ae_map_iff (by fun_prop) Bt.measurableEmbedding.measurableSet_range).mp
    (h₁.ae_le hpμ)
  have hq₂:=(ae_map_iff (by fun_prop) Bt.measurableEmbedding.measurableSet_range).mp
    (h₂.ae_le hpν)
  exact (hq₁.and hq₂).mono (fun q h=> Sm q h.1 h.2)
lemma KS (μ ν:Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q:Measure (BO ℂ)) (R:Measure (Expanded Sphere)) [IsProbabilityMeasure Q]
    (h₁:R.map (fun r=>(r.1,(r.2.1.1,r.2.2.1)))=
      (Q.map CK).prod ((μ.map OnePoint.some).prod (μ.map OnePoint.some)))
    (h₂:R.map (fun r=>(r.1,(r.2.1.2,r.2.2.2)))=
      (Q.map CK).prod ((ν.map OnePoint.some).prod (ν.map OnePoint.some))) :
    ∀ᵐ r ∂ R,r∈range BE:=by
  have hj:=Ca.measurableEmbedding.prodMap Bt.measurableEmbedding
  have hpμ:=Go _ hj (Q.prod (μ.prod μ))
  have hpν:=Go _ hj (Q.prod (ν.prod ν))
  rw [← Measure.map_prod_map _ _ Ca.measurableEmbedding.measurable
    Bt.measurableEmbedding.measurable,
    ← Measure.map_prod_map _ _ An.measurable
    An.measurable,← h₁] at hpμ
  rw [← Measure.map_prod_map _ _ Ca.measurableEmbedding.measurable
    Bt.measurableEmbedding.measurable,
    ← Measure.map_prod_map _ _ An.measurable
    An.measurable,← h₂] at hpν
  have hq₁:=(ae_map_iff (by fun_prop) hj.measurableSet_range).mp hpμ
  have hq₂:=(ae_map_iff (by fun_prop) hj.measurableSet_range).mp hpν
  exact (hq₁.and hq₂).mono (fun r h=> Pa r h.1 h.2)
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2
section
noncomputable section
open MeasureTheory Filter
namespace Aa.Bounded
lemma Oy (μ ν:Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (Q:Measure (BO ℂ)) (R:Measure (Expanded ℂ))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (he:R.map Prod.fst=Q)
    (hm₁:R.map (fun r=>(r.1,(r.2.1.1,r.2.2.1)))=Q.prod (μ.prod μ))
    (hm₂:R.map (fun r=>(r.1,(r.2.1.2,r.2.2.2)))=Q.prod (ν.prod ν))
    (hind:Q.map (fun q=>(q.1,q.2.2))=μ.prod (Q.map (fun q=> q.2.2)))
    (hac₁:Q.map (fun q=>(q.1,q.2.2.1))≪μ.prod μ)
    (hac₂:Q.map (fun q=>(q.2.1,q.2.2.2))≪ν.prod ν)
    (hz:∀ᵐ r ∂ R,(r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1))
    (hw:∀ᵐ r ∂ R,(r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)):False:=by
  have hbd:∀ᵐ q ∂ Q,q.2.1≠q.2.2.2 :=
    (ae_map_iff (μ:=Q) (f:=fun q=>(q.2.1,q.2.2.2)) (p:=fun p:ℂ × ℂ=> p.1≠p.2) (by fun_prop)
      (measurableSet_eq_fun measurable_fst measurable_snd).compl).mp (hac₂.ae_le (Ka ν))
  have hsupp:∀ᵐ q ∂ Q,q.2.2.1∈μ.support:=by
    have hs:∀ᵐ p ∂ μ.prod μ,p.2∈μ.support:=by
      rw [Measure.ae_prod_iff_ae_ae (μ.isClosed_support.measurableSet.preimage measurable_snd)]
      exact Eventually.of_forall (fun _=> μ.support_mem_ae)
    exact (ae_map_iff (μ:=Q) (f:=fun q=>(q.1,q.2.2.1)) (p:=fun p:ℂ × ℂ=> p.2∈μ.support) (by fun_prop)
      (μ.isClosed_support.measurableSet.preimage measurable_snd)).mp (hac₁.ae_le hs)
  exact RY μ ν Q hind hsupp
    (NS μ ν Q R hm₁ hm₂ (NM μ ν Q R he hm₁ hbd hz hw))
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Aa.Bounded
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
lemma NC (β₁ β₂:ProbabilityMeasure Sphere)
    [NullSingletonClass (β₁:Measure Sphere)] [NullSingletonClass (β₂:Measure Sphere)]
    (Q:Measure (BO Sphere)) (R:Measure (Expanded Sphere))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (he:R.map Prod.fst=Q)
    (hm₁:R.map (fun r=>(r.1,(r.2.1.1,r.2.2.1)))=Q.prod ((β₁:Measure Sphere).prod β₁))
    (hm₂:R.map (fun r=>(r.1,(r.2.1.2,r.2.2.2)))=Q.prod ((β₂:Measure Sphere).prod β₂))
    (hind:Q.map (fun q=>(q.1,q.2.2))=(β₁:Measure Sphere).prod (Q.map (fun q=> q.2.2)))
    (hac₁:Q.map (fun q=>(q.1,q.2.2.1))≪(β₁:Measure Sphere).prod β₁)
    (hac₂:Q.map (fun q=>(q.2.1,q.2.2.2))≪(β₂:Measure Sphere).prod β₂)
    (hz:∀ᵐ r ∂ R.comap BE,(r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1))
    (hw:∀ᵐ r ∂ R.comap BE,(r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)):False:=by
  let μ:=EB β₁
  let ν:=EB β₂
  have hμ:μ.map OnePoint.some=(β₁:Measure Sphere):=LY β₁ (measure_singleton _)
  have hν:ν.map OnePoint.some=(β₂:Measure Sphere):=LY β₂ (measure_singleton _)
  let:IsProbabilityMeasure μ:=GQ β₁ (measure_singleton _)
  let:IsProbabilityMeasure ν:=GQ β₂ (measure_singleton _)
  let:NullSingletonClass μ:=HG β₁
  let:NullSingletonClass ν:=HG β₂
  have hQfin:∀ᵐ q ∂ Q,q∈range CK:=Ow μ ν Q
    (by simpa only [hμ] using hac₁) (by simpa only [hν] using hac₂)
  let Qc:=Q.comap CK
  let:IsProbabilityMeasure Qc:=Jo _ Ca.measurableEmbedding Q hQfin
  have hQ:Qc.map CK=Q:=KB _ Ca.measurableEmbedding Q hQfin
  have hRfin:∀ᵐ r ∂ R,r∈range BE:=KS μ ν Qc R
    (by simpa only [hQ,hμ] using hm₁) (by simpa only [hQ,hν] using hm₂)
  let Rc:=R.comap BE
  let:IsProbabilityMeasure Rc:=Jo _ CL.measurableEmbedding R hRfin
  have hR:Rc.map BE=R:=KB _ CL.measurableEmbedding R hRfin
  have hec:Rc.map Prod.fst=Qc:=by
    apply GV BE CK CL.measurableEmbedding.measurable
      Ca.measurableEmbedding Prod.fst Prod.fst measurable_fst measurable_fst Rc Qc rfl
    rw [hR,hQ,he]
  have hm₁c:Rc.map (fun r=>(r.1,(r.2.1.1,r.2.2.1)))=Qc.prod (μ.prod μ):=by
    apply GV BE (Prod.map CK Df)
      CL.measurableEmbedding.measurable
      (Ca.measurableEmbedding.prodMap Bt.measurableEmbedding)
      (fun r=>(r.1,(r.2.1.1,r.2.2.1))) (fun r=>(r.1,(r.2.1.1,r.2.2.1)))
      (by fun_prop) (by fun_prop) Rc (Qc.prod (μ.prod μ)) rfl
    rw [hR,hm₁,← Measure.map_prod_map _ _ Ca.measurableEmbedding.measurable
      Bt.measurableEmbedding.measurable,← Measure.map_prod_map _ _
      An.measurable An.measurable,hQ,hμ]
  have hm₂c:Rc.map (fun r=>(r.1,(r.2.1.2,r.2.2.2)))=Qc.prod (ν.prod ν):=by
    apply GV BE (Prod.map CK Df)
      CL.measurableEmbedding.measurable
      (Ca.measurableEmbedding.prodMap Bt.measurableEmbedding)
      (fun r=>(r.1,(r.2.1.2,r.2.2.2))) (fun r=>(r.1,(r.2.1.2,r.2.2.2)))
      (by fun_prop) (by fun_prop) Rc (Qc.prod (ν.prod ν)) rfl
    rw [hR,hm₂,← Measure.map_prod_map _ _ Ca.measurableEmbedding.measurable
      Bt.measurableEmbedding.measurable,← Measure.map_prod_map _ _
      An.measurable An.measurable,hQ,hν]
  have htarget:(Qc.map (fun q=> q.2.2)).map Df=Q.map (fun q=> q.2.2):=by
    rw [Measure.map_map Bt.measurableEmbedding.measurable (by fun_prop)]
    change Qc.map ((fun q:BO Sphere=> q.2.2)∘ CK)=_
    rw [← Measure.map_map (by fun_prop) Ca.measurableEmbedding.measurable,hQ]
  have hindc:Qc.map (fun q=>(q.1,q.2.2))=μ.prod (Qc.map (fun q=> q.2.2)):=by
    apply GV CK (Prod.map OnePoint.some Df)
      Ca.measurableEmbedding.measurable
      (An.prodMap Bt.measurableEmbedding)
      (fun q=>(q.1,q.2.2)) (fun q=>(q.1,q.2.2))
      (by fun_prop) (by fun_prop) Qc (μ.prod (Qc.map (fun q=> q.2.2))) rfl
    rw [hQ,hind,← Measure.map_prod_map _ _ An.measurable
      Bt.measurableEmbedding.measurable,hμ,htarget]
  have hac₁c:Qc.map (fun q=>(q.1,q.2.2.1))≪μ.prod μ:=by
    apply JJ CK Df Ca.measurableEmbedding.measurable
      Bt.measurableEmbedding (fun q=>(q.1,q.2.2.1)) (fun q=>(q.1,q.2.2.1))
      (by fun_prop) (by fun_prop) Qc (μ.prod μ) rfl
    rw [hQ,← Measure.map_prod_map _ _ An.measurable
      An.measurable,hμ]
    exact hac₁
  have hac₂c:Qc.map (fun q=>(q.2.1,q.2.2.2))≪ν.prod ν:=by
    apply JJ CK Df Ca.measurableEmbedding.measurable
      Bt.measurableEmbedding (fun q=>(q.2.1,q.2.2.2)) (fun q=>(q.2.1,q.2.2.2))
      (by fun_prop) (by fun_prop) Qc (ν.prod ν) rfl
    rw [hQ,← Measure.map_prod_map _ _ An.measurable
      An.measurable,hν]
    exact hac₂
  exact Oy μ ν Qc Rc hec hm₁c hm₂c hindc hac₁c hac₂c hz hw
end Aa.Bounded
end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace Aa.Bounded
open Variance
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
local instance:MeasurableSingletonClass (BO Sphere):=inferInstance
local instance:MeasurableSingletonClass ((Sphere × Sphere) × (Sphere × Sphere)):=inferInstance
local instance:MeasurableSingletonClass (Expanded Sphere):=Prod.instMeasurableSingletonClass
variable {V:Type u1} {I:Type u2} [Fintype V] [DecidableEq V] [Fintype I]
variable (G:Core.Au V I)
def NI:Set (Expanded ℂ):={r | (r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
    (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)}
def Oz:Set (Expanded ℂ):={r | (r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
    (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)}
lemma PJ:IsClosed NI:=isClosed_eq (by fun_prop) (by fun_prop)
lemma PH:IsClosed Oz:=isClosed_eq (by fun_prop) (by fun_prop)
omit [Fintype I] in
lemma JR {r:I × V × V × V}
    (hr:BT G.Af (fun e=> Ae (G.targets e)) r≠0) :
    r.2.1∈G.targets r.1∧ r.2.2.1∈G.targets r.1∧ r.2.2.2∈G.targets r.1:=by
  refine ⟨?_,?_,?_⟩
  all_goals
    by_contra h
    simp [BT,Ae,h] at hr
lemma HY (U₁ U₂:V→ ℂ) (hG:0<G.Ap)
    (hB:∀ e,(G.targets e).Nonempty)
    (hrel:∀ e y z,y∈G.targets e→ z∈G.targets e →
      (U₁ y-U₁ (G.source e))*(U₂ y-U₂ (G.source e))=
      (U₁ z-U₁ (G.source e))*(U₂ z-U₂ (G.source e))) :
    (Bk G (fun x=>(U₁ x:Sphere)) (fun x=>(U₂ x:Sphere)) hG hB :
      Measure (Expanded Sphere)) (BE '' NIᶜ)=0 ∧
    (Bk G (fun x=>(U₁ x:Sphere)) (fun x=>(U₂ x:Sphere)) hG hB :
      Measure (Expanded Sphere)) (BE '' Ozᶜ)=0:=by
  have hzero (s:Set (Expanded ℂ))
      (hs:∀ r,BT G.Af (fun e=> Ae (G.targets e)) r≠0 →
        Ee G.source U₁ U₂ r∈s) :
      (Bk G (fun x=>(U₁ x:Sphere)) (fun x=>(U₂ x:Sphere)) hG hB :
        Measure (Expanded Sphere)) (BE '' sᶜ)=0:=by
    have hh:∀ᵐ r ∂ AM (BT G.Af (fun e=> Ae (G.targets e)))
        (Ee G.source (fun x=>(U₁ x:Sphere)) (fun x=>(U₂ x:Sphere))),
        r∉BE '' sᶜ:=by
      apply SR
      intro r hr
      rintro ⟨q,hq,hqe⟩
      have he:q=Ee G.source U₁ U₂ r:=CL.injective hqe
      subst q
      exact hq (hs r hr)
    change (AM (BT G.Af (fun e=> Ae (G.targets e)))
      (Ee G.source (fun x=>(U₁ x:Sphere)) (fun x=>(U₂ x:Sphere)))) (BE '' sᶜ)=0
    simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.mp hh
  constructor
  · apply hzero
    intro r hr
    have hm:=JR G hr
    exact hrel r.1 r.2.2.1 r.2.1 hm.2.1 hm.1
  · apply hzero
    intro r hr
    have hm:=JR G hr
    exact hrel r.1 r.2.2.2 r.2.1 hm.2.2 hm.1
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Aa.Bounded
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
variable {V:ℕ→ Type u1} {I:ℕ→ Type u2} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]
theorem Lo
    (G:∀ n,Core.Au (V n) (I n)) (U₁ U₂:∀ n,V n→ ℂ)
    (hG:∀ n,0<(G n).Ap) (hB:∀ n e,((G n).targets e).Nonempty)
    (hn:∀ n,2≤Fintype.card (V n))
    (β₁ β₂:ProbabilityMeasure Sphere) (Q:ProbabilityMeasure (BO Sphere))
    (R:ProbabilityMeasure (Expanded Sphere))
    [NullSingletonClass (β₁:Measure Sphere)] [NullSingletonClass (β₂:Measure Sphere)]
    (hα₁:Tendsto (fun n=> Bj (fun x=>(U₁ n x:Sphere)) (by have:=hn n;omega)) atTop (𝓝 β₁))
    (hα₂:Tendsto (fun n=> Bj (fun x=>(U₂ n x:Sphere)) (by have:=hn n;omega)) atTop (𝓝 β₂))
    (hQ:Tendsto (fun n=> Ba (G n) (fun x=>(U₁ n x:Sphere))
      (fun x=>(U₂ n x:Sphere)) (hG n) (hB n)) atTop (𝓝 Q))
    (hR:Tendsto (fun n=> Bk (G n) (fun x=>(U₁ n x:Sphere))
      (fun x=>(U₂ n x:Sphere)) (hG n) (hB n)) atTop (𝓝 R))
    (hd₁:∀ f:C(Sphere,ℝ),Tendsto (fun n=> Bc (G n).Af (G n).targets
      (fun x=> f (U₁ n x:Sphere))) atTop (𝓝 0))
    (hd₂:∀ f:C(Sphere,ℝ),Tendsto (fun n=> Bc (G n).Af (G n).targets
      (fun x=> f (U₂ n x:Sphere))) atTop (𝓝 0))
    (T:ℕ→ ℝ) (hT:∀ n,0<T n)
    (hdR:∀ f:C(Sphere,ℝ),Tendsto (fun n=> Bc ((G n).Ay (T n))
      ((G n).Aw (T n)) (fun x=> f (U₁ n x:Sphere))) atTop (𝓝 0))
    (ho:Tendsto (fun n=>(G n).BF (T n)) atTop (𝓝 0))
    (M:ℝ) (hM:0≤M) (hdom:∀ n x y,(G n).Av x y≤M*Variance.Az Finset.univ x y)
    (hrel:∀ n e y z,y∈(G n).targets e→ z∈(G n).targets e →
      (U₁ n y-U₁ n ((G n).source e))*(U₂ n y-U₂ n ((G n).source e))=
      (U₁ n z-U₁ n ((G n).source e))*(U₂ n z-U₂ n ((G n).source e))):False:=by
  let:TopologicalSpace.PseudoMetrizableSpace Sphere:=inferInstance
  let:TopologicalSpace.PseudoMetrizableSpace (BO Sphere):=inferInstance
  let:TopologicalSpace.PseudoMetrizableSpace (Sphere × Sphere):=inferInstance
  let:TopologicalSpace.PseudoMetrizableSpace (Expanded Sphere):=inferInstance
  let S₁:=fun n x=>(U₁ n x:Sphere)
  let S₂:=fun n x=>(U₂ n x:Sphere)
  have hm₁:=Gw G S₁ S₂ hG hB hn Prod.fst continuous_fst β₁ Q R hα₁ hQ hR hd₁
  have hm₂:=Gw G S₁ S₂ hG hB hn Prod.snd continuous_snd β₂ Q R hα₂ hQ hR hd₂
  have he:=Td
    (fun n=> Bk (G n) (S₁ n) (S₂ n) (hG n) (hB n)) R
    (fun n=> Ba (G n) (S₁ n) (S₂ n) (hG n) (hB n)) Q
    Prod.fst continuous_fst hR hQ
    (fun n=> JP (G n) (S₁ n) (S₂ n) (hG n) (hB n))
  have hi:=RL G S₁ S₂ hG hB hn T hT β₁ Q hα₁ hQ hdR ho
  have hac:=RX G S₁ S₂ hG hB hn β₁ β₂ Q hα₁ hα₂ hQ M hM hdom
  have hz:=Ji BE CL
    (fun n=> Bk (G n) (S₁ n) (S₂ n) (hG n) (hB n)) R hR
    NI PJ
    (fun n=>(HY (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hrel n)).1)
  have hw:=Ji BE CL
    (fun n=> Bk (G n) (S₁ n) (S₂ n) (hG n) (hB n)) R hR
    Oz PH
    (fun n=>(HY (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hrel n)).2)
  exact NC β₁ β₂ Q R he hm₁ hm₂ hi hac.1 hac.2 hz hw
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace Aa.Bounded
local instance:MeasurableSpace Sphere:=borel Sphere
local instance:BorelSpace Sphere:=⟨rfl⟩
variable {V:ℕ→ Type u1} {I:ℕ→ Type u2} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]
theorem IE
    (G:∀ n,Core.Au (V n) (I n)) (u₁ u₂:∀ n,V n→ ℂ)
    (x₁ x₂:∀ n,V n) (hu₁:∀ n,Function.Injective (u₁ n)) (hu₂:∀ n,Function.Injective (u₂ n))
    (hG:∀ n,0<(G n).Ap) (hB:∀ n e,((G n).targets e).Nonempty)
    (hn:∀ n,2≤Fintype.card (V n))
    (hcard:Tendsto (fun n=>(Fintype.card (V n):ℝ)) atTop atTop)
    (C:ℝ) (hC:0≤C) (hlog₁:∀ n,Dl (u₁ n)≤C) (hlog₂:∀ n,Dl (u₂ n)≤C)
    (hx₁:∀ n,(∑ y,CV (u₁ n) (x₁ n) y)≤C*(Fintype.card (V n):ℝ))
    (hx₂:∀ n,(∑ y,CV (u₂ n) (x₂ n) y)≤C*(Fintype.card (V n):ℝ))
    (hd₁:∀ f:C(Sphere,ℝ),Tendsto (fun n=> Bc (G n).Af (G n).targets
      (fun x=> f ((u₁ n x-u₁ n (x₁ n)):Sphere))) atTop (𝓝 0))
    (hd₂:∀ f:C(Sphere,ℝ),Tendsto (fun n=> Bc (G n).Af (G n).targets
      (fun x=> f ((u₂ n x-u₂ n (x₂ n)):Sphere))) atTop (𝓝 0))
    (T:ℕ→ ℝ) (hT:∀ n,0<T n)
    (hdR:∀ f:C(Sphere,ℝ),Tendsto (fun n=> Bc ((G n).Ay (T n))
      ((G n).Aw (T n)) (fun x=> f ((u₁ n x-u₁ n (x₁ n)):Sphere))) atTop (𝓝 0))
    (ho:Tendsto (fun n=>(G n).BF (T n)) atTop (𝓝 0))
    (M:ℝ) (hM:0≤M) (hdom:∀ n x y,(G n).Av x y≤M*Variance.Az Finset.univ x y)
    (hrel:∀ n e y z,y∈(G n).targets e→ z∈(G n).targets e →
      (u₁ n y-u₁ n ((G n).source e))*(u₂ n y-u₂ n ((G n).source e))=
      (u₁ n z-u₁ n ((G n).source e))*(u₂ n z-u₂ n ((G n).source e))):False:=by
  let:TopologicalSpace.PseudoMetrizableSpace Sphere:=inferInstance
  let:TopologicalSpace.PseudoMetrizableSpace (BO Sphere):=inferInstance
  let:TopologicalSpace.PseudoMetrizableSpace (Sphere × Sphere):=inferInstance
  let:TopologicalSpace.PseudoMetrizableSpace (Expanded Sphere):=inferInstance
  let:TopologicalSpace (ProbabilityMeasure Sphere):=inferInstance
  let:TopologicalSpace (ProbabilityMeasure (BO Sphere)):=inferInstance
  let:TopologicalSpace (ProbabilityMeasure (Expanded Sphere)):=inferInstance
  let:CompactSpace (BO Sphere):=inferInstance
  let:CompactSpace (Expanded Sphere):=inferInstance
  let:CompactSpace (ProbabilityMeasure Sphere):=inferInstance
  let:CompactSpace (ProbabilityMeasure (BO Sphere)):=inferInstance
  let:CompactSpace (ProbabilityMeasure (Expanded Sphere)):=inferInstance
  let U₁:=fun n x=> u₁ n x-u₁ n (x₁ n)
  let U₂:=fun n x=> u₂ n x-u₂ n (x₂ n)
  let α₁:=fun n=> Bj (fun x=>(U₁ n x:Sphere)) (by have:=hn n;omega)
  let α₂:=fun n=> Bj (fun x=>(U₂ n x:Sphere)) (by have:=hn n;omega)
  let Qn:=fun n=> Ba (G n) (fun x=>(U₁ n x:Sphere))
    (fun x=>(U₂ n x:Sphere)) (hG n) (hB n)
  let Rn:=fun n=> Bk (G n) (fun x=>(U₁ n x:Sphere))
    (fun x=>(U₂ n x:Sphere)) (hG n) (hB n)
  let L:=fun n=>(α₁ n,α₂ n,Qn n,Rn n)
  obtain ⟨l,_,φ,hφ,hl⟩:=isCompact_univ.tendsto_subseq (fun n=> mem_univ (L n))
  have ha₁:Tendsto (α₁∘ φ) atTop (𝓝 l.1):=continuous_fst.tendsto l |>.comp hl
  have ha₂:Tendsto (α₂∘ φ) atTop (𝓝 l.2.1) :=
    (continuous_fst.comp continuous_snd).tendsto l |>.comp hl
  have hq:Tendsto (Qn∘ φ) atTop (𝓝 l.2.2.1) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto l |>.comp hl
  have hr:Tendsto (Rn∘ φ) atTop (𝓝 l.2.2.2) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto l |>.comp hl
  let:NullSingletonClass (l.1:Measure Sphere):=EE
    (fun n=> u₁ (φ n)) (fun n=> x₁ (φ n)) (fun n=> hu₁ (φ n)) (fun n=> hn (φ n))
    (hcard.comp hφ.tendsto_atTop) C hC (fun n=> hlog₁ (φ n)) (fun n=> hx₁ (φ n)) l.1 ha₁
  let:NullSingletonClass (l.2.1:Measure Sphere):=EE
    (fun n=> u₂ (φ n)) (fun n=> x₂ (φ n)) (fun n=> hu₂ (φ n)) (fun n=> hn (φ n))
    (hcard.comp hφ.tendsto_atTop) C hC (fun n=> hlog₂ (φ n)) (fun n=> hx₂ (φ n)) l.2.1 ha₂
  apply Lo (fun n=> G (φ n)) (fun n=> U₁ (φ n)) (fun n=> U₂ (φ n))
    (fun n=> hG (φ n)) (fun n=> hB (φ n)) (fun n=> hn (φ n))
    l.1 l.2.1 l.2.2.1 l.2.2.2 ha₁ ha₂ hq hr
    (fun f=>(hd₁ f).comp hφ.tendsto_atTop) (fun f=>(hd₂ f).comp hφ.tendsto_atTop)
    (T∘ φ) (fun n=> hT (φ n)) (fun f=>(hdR f).comp hφ.tendsto_atTop)
    (ho.comp hφ.tendsto_atTop) M hM (fun n=> hdom (φ n))
  intro n e y z hy hz
  simpa only [U₁,U₂,sub_sub_sub_cancel_right] using hrel (φ n) e y z hy hz
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3 u4
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Aa.Bounded
open Ak Bg Variance NumberField
lemma FX (x w:ℕ→ ℝ) (C:ℝ)
    (hx:∀ n,0≤x n) (hw:∀ n,0≤w n) (hC:∀ n,w n≤C)
    (ht:Tendsto (fun n=> x n/(w n+1)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0):=by
  apply squeeze_zero hx _ (by simpa only [mul_zero] using tendsto_const_nhds.mul ht (a:=C+1))
  intro n
  have hp:0<w n+1:=by linarith [hw n]
  calc
    x n=(w n+1)*(x n/(w n+1)):=by field_simp
    _≤(C+1)*(x n/(w n+1)) :=
      mul_le_mul_of_nonneg_right (by linarith [hC n]) (div_nonneg (hx n) hp.le)
variable {P:Type u1} [Fintype P] [DecidableEq P]
variable {K:Type u2} [Field K] [NumberField K]
lemma SW (q r:Finset P→ ℝ) (d d':Depth P) :
    Bm (fun C=> q C+r C) d d'=Bm q d d'+Bm r d d':=by
  simp only [Bm,Ac,mul_add,Finset.sum_add_distrib]
  ring
omit [NumberField K] in
lemma ON (Z₁ Z₂:P→ K) (h₁:Function.Injective Z₁) (h₂:Function.Injective Z₂)
    (hn:2≤Fintype.card P) (q r:Finset P→ ℝ) (v:InfinitePlace K) :
    BD Z₁ Z₂ (Bm (fun C=> q C+r C)) v=
      BD Z₁ Z₂ (Bm q) v+BD Z₁ Z₂ (Bm r) v:=by
  unfold BD
  simp only [SW]
  exact integral_add (Cm Z₁ Z₂ h₁ h₂ hn q v)
    (Cm Z₁ Z₂ h₁ h₂ hn r v)
omit [NumberField K] in
lemma Ny (Z₁ Z₂:P→ K) (q:Finset P→ ℝ) (v:InfinitePlace K) :
    BD Z₂ Z₁ (Bm q) v=BD Z₁ Z₂ (Bm q) v:=by
  unfold BD
  congr 1
  funext ω
  exact add_comm _ _
omit [NumberField K] in
lemma Ng (Z₁ Z₂:P→ K) (v:InfinitePlace K) :
    BD Z₂ Z₁ CA v=BD Z₁ Z₂ CA v:=by
  unfold BD
  congr 1
  funext ω
  simp only [CA,Bm,Co]
  congr 1
  · exact add_comm _ _
  · apply Finset.sum_congr rfl
    intro x _
    rw [add_comm ((arch Z₂ v ω).Ag x)]
omit [DecidableEq P] in
lemma MA (m q r:Finset P→ ℝ) :
    Ac m (fun C=> q C+r C)=Ac m q+Ac m r:=by
  simp only [Ac,mul_add,Finset.sum_add_distrib]
variable {V:ℕ→ Type u3} {L:ℕ→ Type u4} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)]
  [∀ n,Field (L n)] [∀ n,NumberField (L n)]
lemma Kq (Z₁ Z₂:∀ n,V n→ L n)
    (h₁:∀ n,Function.Injective (Z₁ n)) (h₂:∀ n,Function.Injective (Z₂ n))
    (hn:∀ n,2≤Fintype.card (V n)) (q r:∀ n,Finset (V n)→ ℝ)
    (hq:∀ n C,0≤q n C) (hr:∀ n C,0≤r n C)
    (C:ℝ) (hC:0≤C)
    (hscale:∀ n,AQ (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)+
      AG (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)≤C)
    (hqt:Tendsto (fun n=> Ac (totalMass (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)) (q n)) atTop (𝓝 0))
    (hrt:Tendsto (fun n=> Ac (totalMass (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)) (r n)) atTop (𝓝 0)) :
    ∃ v:∀ n,InfinitePlace (L n),
      (∀ n,BD (Z₁ n) (Z₂ n) CA (v n)≤2*C+1) ∧
      Tendsto (fun n=> BD (Z₁ n) (Z₂ n) (Bm (q n)) (v n)) atTop (𝓝 0) ∧
      Tendsto (fun n=> BD (Z₁ n) (Z₂ n) (Bm (r n)) (v n)) atTop (𝓝 0):=by
  let m:=fun n=> totalMass (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)
  let ε:=fun n=> Ac (m n) (q n)+Ac (m n) (r n)+1/((n:ℝ)+1)
  have hq0 (n):0≤Ac (m n) (q n) :=
    Finset.sum_nonneg (fun D _=> mul_nonneg (Bi _ _ _ _ _) (hq n D))
  have hr0 (n):0≤Ac (m n) (r n) :=
    Finset.sum_nonneg (fun D _=> mul_nonneg (Bi _ _ _ _ _) (hr n D))
  have he (n):0<ε n:=by
    have hh:0<1/((n:ℝ)+1):=by positivity
    dsimp only [ε]
    linarith [hq0 n,hr0 n]
  have het:Tendsto ε atTop (𝓝 0):=by
    have hi:Tendsto (fun n:ℕ=>1/((n:ℝ)+1)) atTop (𝓝 0):=by
      simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa only [add_zero] using (hqt.add hrt).add hi
  have hs (n):=Tc (Z₁ n) (Z₂ n) (h₁ n) (h₂ n) (hn n)
    (fun D=> q n D+r n D) (fun D=> add_nonneg (hq n D) (hr n D)) C (ε n) hC (he n) (hscale n)
    (by rw [MA]; dsimp [ε,m]; linarith [show 0≤1/((n:ℝ)+1) by positivity])
  choose v hvscale hv using hs
  have hvq (n):0≤BD (Z₁ n) (Z₂ n) (Bm (q n)) (v n) :=
    FQ _ _ _ (EH _ (hq n)) _
  have hvr (n):0≤BD (Z₁ n) (Z₂ n) (Bm (r n)) (v n) :=
    FQ _ _ _ (EH _ (hr n)) _
  have hsum (n):=hv n
  simp only [ON _ _ (h₁ _) (h₂ _) (hn _)] at hsum
  refine ⟨v,hvscale,?_,?_⟩
  · apply squeeze_zero hvq _ (by simpa only [mul_zero] using het.const_mul 2)
    intro n
    linarith [hsum n,hvr n]
  · apply squeeze_zero hvr _ (by simpa only [mul_zero] using het.const_mul 2)
    intro n
    linarith [hsum n,hvq n]
lemma Ni (n:ℕ→ ℝ) (hn:∀ j,0<n j)
    (ht:Tendsto n atTop atTop) (c:ℝ) (hc:0<c) :
    Tendsto (fun j=>(n j)^(1-c)/n j) atTop (𝓝 0):=by
  have hh:=(tendsto_rpow_neg_atTop hc).comp ht
  convert hh using 1
  funext j
  rw [show 1-c=1+(-c) by ring,Real.rpow_add (hn j),Real.rpow_one]
  simp only [Function.comp_apply]
  exact mul_div_cancel_left₀ _ (hn j).ne'
end Aa.Bounded
end
end
end AA
namespace AA
universe u1 u2 u3
section
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace Aa
open Bounded Bg Variance Ak NumberField
variable {V:ℕ→ Type u1} {I:ℕ→ Type u2} {K:ℕ→ Type u3} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]
variable (G:∀ j,Core.Au (V j) (I j)) (θ γ c:ℝ) (η:ℕ→ ℝ)
  (Z₁ Z₂:∀ j,V j→ K j) (h₁:∀ j,Function.Injective (Z₁ j)) (h₂:∀ j,Function.Injective (Z₂ j))
theorem LG (hθ:0<θ) (hγ:0<γ) (hγ1:γ<1) (hc:0<c) (hcγ:c<γ)
    (hn:Tendsto (fun j=>(Fintype.card (V j):ℝ)) atTop atTop)
    (hη:Tendsto η atTop (𝓝 0)) (hη0:∀ j,0≤η j) (hηb:∀ j,η j≤θ/2)
    (hG:∀ j,AJ (V j) (I j) (G j) θ γ c (η j))
    (t:∀ j,I j→ K j) (ht:∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e)
    (C:ℝ) (hC:0≤C) (hscale:∀ j,AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+
      AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)≤C):False:=by
  let n:=fun j=>(Fintype.card (V j):ℝ)
  let T:=fun j=> n j^(1-c)
  let S:=fun j=> n j^γ
  let q:=fun j=> Aj (G j).Af (G j).targets (T j)
  let r:=fun j=> Aj ((G j).Ay (S j)) ((G j).Aw (S j)) (T j)
  have hq (j D):0≤q j D:=Bw _ _ _ (G j).AT D
  have hr (j D):0≤r j D:=Bw _ _ _ ((G j).Dp _) D
  have h2 (j):2≤Fintype.card (V j):=(hG j).Cz
  have hn2 (j):(2:ℝ)≤n j:=by dsimp only [n]; exact_mod_cast h2 j
  have hn0 (j):0<n j:=by linarith [hn2 j]
  have hpos (j):0<(G j).Ap:=(hG j).CR (by linarith [hηb j])
  have hdom (j x y):=(hG j).Gl hθ (hηb j) x y
  have hT (j):1≤T j:=Real.one_le_rpow (by linarith [hn2 j]) (by linarith)
  have hS (j):1<S j:=Real.one_lt_rpow (by linarith [hn2 j]) hγ
  have hSn (j):S j≤n j:=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show 1≤n j by linarith [hn2 j]) hγ1.le
  have hB (j e):2≤((G j).targets e).card:=by
    have hh:=(hS j).trans ((hG j).fiber e)
    exact_mod_cast hh
  have hR (j y):2≤((G j).Aw (S j) y).card:=by
    have hh:=(hS j).trans_le ((G j).Ft (S j) (hSn j) y)
    exact_mod_cast hh
  have hvar:=DG G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht
  let W:=fun j=> AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  have hW (j):0≤W j:=add_nonneg (BK _ _ _ _) (Bu _ _ _ _)
  have hf0 (j):0≤Ew G c Z₁ Z₂ h₁ h₂ j :=
    Finset.sum_nonneg (fun D _=> mul_nonneg (Bi _ _ _ _ D) (hq j D))
  have hr0 (j):0≤ JF G γ c Z₁ Z₂ h₁ h₂ j :=
    Finset.sum_nonneg (fun D _=> mul_nonneg (Bi _ _ _ _ D) (hr j D))
  have hft:=FX _ W C hf0 hW hscale hvar.1
  have hrt:=FX _ W C hr0 hW hscale hvar.2
  obtain ⟨v,hv,hvf,hvr⟩:=Kq Z₁ Z₂ h₁ h₂ h2 q r hq hr C hC hscale hft hrt
  let z₁:=fun j x=>(v j).embedding (Z₁ j x)
  let z₂:=fun j x=>(v j).embedding (Z₂ j x)
  have hz₁ (j):Function.Injective (z₁ j):=(v j).embedding.injective.comp (h₁ j)
  have hz₂ (j):Function.Injective (z₂ j):=(v j).embedding.injective.comp (h₂ j)
  let u₁:=fun j=> CN (z₁ j)
  let u₂:=fun j=> CN (z₂ j)
  let D:ℝ:=4*(2*C+1)+8
  have hD:0≤D:=by dsimp [D]; positivity
  have hlog₁ (j):Dl (u₁ j)≤D:=by
    rw [IB _ (hz₁ j) (h2 j)]
    exact (Hi (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) (h2 j) (v j)).trans (by dsimp [D]; linarith [hv j])
  have hlog₂ (j):Dl (u₂ j)≤D:=by
    rw [IB _ (hz₂ j) (h2 j)]
    have hh:=Hi (Z₂ j) (Z₁ j) (h₂ j) (h₁ j) (h2 j) (v j)
    rw [Ng] at hh
    exact hh.trans (by dsimp [D]; linarith [hv j])
  choose x₁ hx₁ using (fun j=> Qy (u₁ j) D (h2 j) (hlog₁ j))
  choose x₂ hx₂ using (fun j=> Qy (u₂ j) D (h2 j) (hlog₂ j))
  have hsmall:=Ni n hn0 hn c hc
  let m₁:=fun j=> AK (Cd (z₁ j))
  let m₂:=fun j=> AK (Cd (z₂ j))
  have hd₁:=Fa Z₁ Z₂ h₁ h₂ v m₁ (fun j => -u₁ j (x₁ j))
    (fun j=>(G j).Af) (fun j=>(G j).targets) T (2/θ) h2 hT (by positivity)
    (fun j=>(G j).AT) (fun j=>(G j).Bz (hpos j) |>.le) hB
    (fun j=>(G j).Fm _ (hdom j) (h2 j)) hvf hsmall
  have hvf₂:Tendsto (fun j=> BD (Z₂ j) (Z₁ j) (Bm (q j)) (v j)) atTop (𝓝 0):=by
    simpa only [Ny] using hvf
  have hd₂:=Fa Z₂ Z₁ h₂ h₁ v m₂ (fun j => -u₂ j (x₂ j))
    (fun j=>(G j).Af) (fun j=>(G j).targets) T (2/θ) h2 hT (by positivity)
    (fun j=>(G j).AT) (fun j=>(G j).Bz (hpos j) |>.le) hB
    (fun j=>(G j).Fm _ (hdom j) (h2 j)) hvf₂ hsmall
  have hdR:=Fa Z₁ Z₂ h₁ h₂ v m₁ (fun j => -u₁ j (x₁ j))
    (fun j=>(G j).Ay (S j)) (fun j=>(G j).Aw (S j)) T (2/θ) h2 hT (by positivity)
    (fun j=>(G j).Dp _) (fun j=>(G j).Ge _ (hpos j)) hR
    (fun j=>(G j).Ic _ _ (hdom j) (h2 j)) hvr hsmall
  apply IE G u₁ u₂ x₁ x₂
    (fun j=> GK _ (hz₁ j)) (fun j=> GK _ (hz₂ j))
    hpos (fun j e=> Finset.card_pos.mp (by have:=hB j e; omega)) h2 hn D hD hlog₁ hlog₂ hx₁ hx₂
    (by simpa only [sub_eq_add_neg,u₁,CN,z₁,m₁] using hd₁)
    (by simpa only [sub_eq_add_neg,u₂,CN,z₂,m₂] using hd₂)
    S (fun j=> Real.rpow_pos_of_pos (hn0 j) γ)
    (by simpa only [sub_eq_add_neg,u₁,CN,z₁,m₁] using hdR)
    (Of G θ γ c η hθ hγ1 hηb hn hG) (2/θ) (by positivity) hdom
  intro j e y z hy hz
  have he:=(ht j e y hy).trans (ht j e z hz).symm
  have hem:=congrArg (v j).embedding he
  simp only [map_mul,map_sub] at hem
  dsimp only [u₁,u₂,CN,z₁,z₂]
  linear_combination (Real.exp (AK (Cd (z₁ j))):ℂ)*
    (Real.exp (AK (Cd (z₂ j))):ℂ)*hem
end Aa
end
end
end AA
namespace AA
universe u1 u2 u3
section
noncomputable section
open Filter
open scoped Topology
namespace Aa
open Bg Variance AV AL
open scoped BigOperators
variable {V:ℕ→ Type u1} {I:ℕ→ Type u2} {K:ℕ→ Type u3} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]
theorem Hx
    (G:∀ j,Core.Au (V j) (I j)) (θ γ c:ℝ) (η:ℕ→ ℝ)
    (Z₁ Z₂:∀ j,V j→ K j) (h₁:∀ j,Function.Injective (Z₁ j)) (h₂:∀ j,Function.Injective (Z₂ j))
    (hθ:0<θ) (hγ:0<γ) (hγ1:γ<1) (hc:0<c) (hcγ:c<γ)
    (hn:Tendsto (fun j=>(Fintype.card (V j):ℝ)) atTop atTop)
    (hη:Tendsto η atTop (𝓝 0)) (hη0:∀ j,0≤η j) (hηb:∀ j,η j≤θ/2)
    (hG:∀ j,AJ (V j) (I j) (G j) θ γ c (η j))
    (t:∀ j,I j→ K j) (ht:∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e):False:=by
  let W:=fun j=> AQ (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let A:=fun j=> AG (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  have hcomp:=ID G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht
  by_cases htop:¬ Tendsto W atTop atTop
  · rw [tendsto_atTop] at htop
    push Not at htop
    obtain ⟨C,hC⟩:=htop
    obtain ⟨φ,hφ,hb⟩:=exists_seq_forall_of_frequently (hC.and_eventually hcomp)
    have hp:0<C:=(BK _ _ _ _).trans_lt (hb 0).1
    apply LG (fun j=> G (φ j)) θ γ c (η∘ φ)
      (fun j=> Z₁ (φ j)) (fun j=> Z₂ (φ j)) (fun j=> h₁ (φ j)) (fun j=> h₂ (φ j))
      hθ hγ hγ1 hc hcγ (hn.comp hφ) (hη.comp hφ) (fun j=> hη0 (φ j)) (fun j=> hηb (φ j))
      (fun j=> hG (φ j)) (fun j=> t (φ j)) (fun j=> ht (φ j))
      (C+(64+8/θ)*(C+1)) (by positivity)
    intro j
    change W (φ j)+A (φ j)≤_
    obtain ⟨hw,ha⟩:=hb j
    have hh:=mul_le_mul_of_nonneg_left (add_le_add_right hw.le 1) (show 0≤64+8/θ by positivity)
    dsimp only [A,W] at *
    linarith
  push Not at htop
  let m:=fun j=> totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let C:ℝ:=64+8/θ
  have hC:0<C:=by dsimp [C]; positivity
  let τ:ℝ:=min 1 (θ/(64*C))
  have hτ:0<τ:=lt_min (by norm_num) (by positivity)
  have hτ1:τ≤1:=min_le_left _ _
  have hτC:64*τ*C≤θ:=by
    have hh:=(le_div_iff₀ (show 0<64*C by positivity)).mp (min_le_right (1:ℝ) (θ/(64*C)))
    dsimp [τ]
    nlinarith
  let b:ℝ:=4*τ/θ
  have hb:0≤b:=by dsimp [b]; positivity
  have hbC:2*b*C≤1/8:=by
    dsimp [b]
    apply (mul_le_mul_iff_left₀ hθ).mp
    field_simp
    nlinarith
  let R:ℝ:=8/τ^2+16/θ
  have hR:0<R:=by dsimp [R]; positivity
  let δ:ℝ:=min (1/8) ((1/8)/R)
  have hδ:0<δ:=lt_min (by norm_num) (by positivity)
  have hδ8:δ≤1/8:=min_le_left _ _
  have hδR:δ*R≤1/8:=(le_div_iff₀ hR).mp (min_le_right _ _)
  let Q:=fun j=> Ac (m j) (G j).FL
  let S:=fun j=> Ac (m j) (slice (G j).Af
    (fun e=> Ae ((G j).targets e)) (G j).source (4*δ))
  let a:=fun j=>2-2*((θ-η j)/(θ+η j/8))
  have ha:Tendsto a atTop (𝓝 0):=by
    have hh:=(tendsto_const_nhds (x:=(2:ℝ))).sub ((tendsto_const_nhds (x:=(2:ℝ))).mul
      (((tendsto_const_nhds (x:=θ)).sub hη).div (tendsto_const_nhds.add (hη.div_const 8))
      (show θ+(0:ℝ)/8≠0 by simpa using hθ.ne')))
    convert hh using 1 <;> first | rfl | simp [hθ.ne']
  have hlow:∀ᶠ j in atTop,(δ/4)*W j≤Ac (m j) (fun B=> Be δ (Ad Finset.univ B)):=by
    apply JC W A (Ew G c Z₁ Z₂ h₁ h₂) _ Q S a C δ b hC hδ hb hbC
      (fun j=> BK _ _ _ _) (fun j=> Bu _ _ _ _)
      (fun j=> Finset.sum_nonneg (fun B _=> mul_nonneg (Bi _ _ _ _ B)
        (Bw _ _ _ (G j).AT B))) htop hcomp ha
      (DG G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht).1
    · exact Eventually.of_forall (fun j=>(hG j).ML (by linarith [hηb j]) (hη0 j)
        (m j) (Gn (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
        (BB (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)) (Fc _ _ _ _)
        (EW _ _ _ _ (hG j).Cz))
    · filter_upwards [hn.eventually (eventually_ge_atTop (2/τ))] with j hj
      have hh:=(hG j).JY (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
        (by linarith [hηb j]) (t j) (ht j) τ (4*δ) 0 (by positivity) (by linarith) hτ hτ1
        (by have:=(div_le_iff₀ hτ).mp hj; nlinarith) (by norm_num)
      have hi:1/(θ-η j)≤2/θ:=by
        apply (div_le_div_iff₀ (by linarith [hηb j]:0<θ-η j) hθ).mpr
        linarith [hηb j]
      have h1:2*(4*δ)/τ^2+2*(4*δ)/(θ-η j)≤1/8:=by
        have hh':=mul_le_mul_of_nonneg_left hi (show 0≤8*δ by positivity)
        dsimp [R] at hδR
        simp only [div_eq_mul_inv] at hδR hh' ⊢
        nlinarith
      have h2:2*τ/(θ-η j)≤b:=by
        have hh':=mul_le_mul_of_nonneg_left hi (show 0≤2*τ by positivity)
        dsimp [b]
        simp only [div_eq_mul_inv] at hh' ⊢
        nlinarith
      have hW0:=BK (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
      have hA0:=Bu (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
      have h1':=mul_le_mul_of_nonneg_right h1 hW0
      have h2':=mul_le_mul_of_nonneg_right h2 hA0
      simp only [neg_zero,zero_div,Real.exp_zero,mul_zero,add_zero,mul_one] at hh
      dsimp [S,W,A]
      linarith
    · have hnγ:=(tendsto_rpow_atTop hγ).comp hn
      filter_upwards [hnγ.eventually (eventually_ge_atTop (2/(4*δ)))] with j hj
      have hk (i:I j):2/(((G j).targets i).card:ℝ)≤4*δ:=by
        have hsize:=(hG j).fiber i
        have hn0:0<(((G j).targets i).card:ℝ):=(show 0<2/(4*δ) by positivity).trans_le (hj.trans hsize.le)
        apply (div_le_iff₀ hn0).mpr
        have hh:=(div_le_iff₀ (show 0<4*δ by positivity)).mp (hj.trans hsize.le)
        nlinarith
      have hh:=Kh (m j) (Bi _ _ _ _)
        (RD _ _ _ _) (G j).Af (G j).targets (G j).source
        ((Fintype.card (V j):ℝ)^(1-c)) δ (G j).AT
        ((G j).Bz ((hG j).CR (by linarith [hηb j]))).le hδ (by linarith) hk
      dsimp [Q,S,Ew]
      have he:(G j).FL= Cl (G j).Af (fun e=> Ae ((G j).targets e)) (G j).source:=funext (G j).Pn
      rw [←he] at hh
      simpa only [m,one_div,mul_comm,div_eq_mul_inv,one_mul] using hh
  let F:=fun j=> Ac (m j) (Bl (G j).Af (G j).targets δ)
  let R:=fun j=> Ac (m j) (Bl
    ((G j).Ay ((Fintype.card (V j):ℝ)^γ)) ((G j).Aw ((Fintype.card (V j):ℝ)^γ)) δ)
  have hF0 (j):0≤F j:=Finset.sum_nonneg (fun C _=> mul_nonneg (Bi _ _ _ _ C)
    (Finset.sum_nonneg (fun e _=> mul_nonneg ((G j).AT e) (Hl _ _ _))))
  have hR0 (j):0≤R j:=Finset.sum_nonneg (fun C _=> mul_nonneg (Bi _ _ _ _ C)
    (Finset.sum_nonneg (fun y _=> mul_nonneg ((G j).Dp _ y) (Hl _ _ _))))
  have hcut:=GY G θ γ c η Z₁ Z₂ h₁ h₂ δ hδ hθ hγ hγ1 hc hcγ hn hη hη0 hηb hG t ht
  have hf:=Gy W A F (64+8/θ) (by positivity)
    (fun j=> BK _ _ _ _) (fun j=> Bu _ _ _ _) hF0 htop hcomp hcut.1
  have hr:=Gy W A R (64+8/θ) (by positivity)
    (fun j=> BK _ _ _ _) (fun j=> Bu _ _ _ _) hR0 htop hcomp hcut.2
  apply Js W F R (fun j=> Ac (m j) (fun C=> Be δ (Ad Finset.univ C)))
    (fun j=>(G j).BF ((Fintype.card (V j):ℝ)^γ)) δ (δ/4) hδ (by positivity)
    htop hf hr (Of G θ γ c η hθ hγ1 hηb hn hG) hlow
  filter_upwards [JA G θ γ c η hγ hγ1 δ hδ hn hG] with j hj
  exact Ko (G j) (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) (t j) (ht j) δ
    ((Fintype.card (V j):ℝ)^γ) hδ.le (Real.rpow_pos_of_pos (by exact_mod_cast (show 0<Fintype.card (V j) by have:=(hG j).Cz; omega)) γ)
    (hG j).Cz ((hG j).CR (by linarith [hηb j])) hj.1 hj.2.2.1 hj.2.1 hj.2.2.2.2 hj.2.2.2.1
end Aa
end
end
end AA
namespace AA
universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11
section
noncomputable section
namespace Aa
open Filter
open scoped Topology BigOperators
lemma Nm (θ:ℝ):Tendsto (fun j:ℕ=> θ/((j:ℝ)+2)) atTop (𝓝 0):=by
  have ht:Tendsto (fun j:ℕ=>(j:ℝ)+2) atTop atTop:=tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop ht
end Aa
noncomputable section
namespace Aa.Transfer
open MvPolynomial
end Aa.Transfer
namespace Aa
open scoped BigOperators
end Aa
end
end
end
end AA
namespace AA
section
noncomputable section
open Filter
open scoped Topology
namespace Aa
end Aa
end
end
end AA
namespace AA
section
noncomputable section
open Filter
open scoped Topology BigOperators
namespace Aa
end Aa
end
end
end AA
open Filter Finset
open scoped EuclideanGeometry
namespace LeafPort
open Filter Finset AA.Aa
open scoped Topology
lemma degree_eq {V:Type} {I:Type} [Fintype V] [Fintype I] [DecidableEq V]
    (G:Core.Au V I) (x:V) :
    G.degree (-1) univ x=(#{y | ∃ e,G.source e= x∧ y∈ G.targets e}:ℝ) +
      #{y | ∃ e,G.source e= y∧ x∈ G.targets e}:=by
  have h (p q:V→ Prop) [DecidablePred p] [DecidablePred q] (hpq:∀ y,p y↔ q y) :
      (#{y | p y}:ℝ) = #{y | q y}:=by
    congr 2
    ext y
    simp [hpq y]
  unfold Core.Au.degree
  congr 1 <;> apply h <;> intro y <;>
    simp [Core.Au.edge,G.FI]
theorem obstruction:OMA.R_Erdos604_erdos_604_variants_katz_tardos_R1_H1_R1.H1:=by
  intro θ γ c hθ hc hcγ hγ V I K _ _ _ _ _ s T Z₁ Z₂ t hl hd hZ ht hG
  let G:∀ j,Core.Au (V j) (I j):=fun j=>⟨s j,T j,hl j,hd j⟩
  refine Hx G θ γ c (fun j=> θ/((j:ℝ)+2)) Z₁ Z₂
    (fun j=>(hZ j).1) (fun j=>(hZ j).2) hθ (hc.trans hcγ) hγ hc hcγ
    (tendsto_atTop_mono (fun j=>(hG j).1.le) tendsto_natCast_atTop_atTop)
    (Nm θ) (fun j=> by positivity) (fun j => ?_) (fun j => ?_) t ht
  · apply div_le_div_of_nonneg_left hθ.le (by norm_num:(0:ℝ)<2)
    have:0≤(j:ℝ):=Nat.cast_nonneg j
    linarith
  · obtain ⟨-,h2,hlo,hup,hdg,hfib,hsub,hsmall⟩:=hG j
    exact ⟨by exact_mod_cast h2,by rw [Core.Au.Ke]; exact hlo,
      by rw [Core.Au.Ke]; exact hup,fun x=> by rw [degree_eq]; exact hdg x,
      hfib,hsub,hsmall⟩
end LeafPort
theorem OMA.solution:OMA.R_Erdos604_erdos_604_variants_katz_tardos_R1_H1_R1.H1 :=
  LeafPort.obstruction
