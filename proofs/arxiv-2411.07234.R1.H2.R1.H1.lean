import OMAReductions.R_arxiv_2411_07234_R1_H2_R1

/-! Adaptation of the backward conditional-expectation and pairing arguments from
OpenAI, openai/math revision 3344da59991ed94f9ba711217b29c1d760badfa6,
Entropy.lean and HilbertCodes.lean, under Apache License 2.0. -/

namespace OMA.RokhlinBackward

open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal RealInnerProductSpace

section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

private abbrev completedFactor (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[m₀] s ∧ ∃ t : Set Ω, MeasurableSet[m] t ∧
    ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t
  measurableSet_empty := ⟨@MeasurableSet.empty Ω m₀,∅,@MeasurableSet.empty Ω m,Eventually.of_forall fun _ => Iff.rfl⟩
  measurableSet_compl := by
    rintro s ⟨hs,t,ht,he⟩
    exact ⟨hs.compl,tᶜ,ht.compl,he.mono fun x hx => not_congr hx⟩
  measurableSet_iUnion := by
    intro s hs
    choose t ht he using fun n => (hs n).2
    refine ⟨MeasurableSet.iUnion fun n => (hs n).1,⋃ n, t n,MeasurableSet.iUnion ht,?_⟩
    filter_upwards [ae_all_iff.mpr he] with x hx
    simp only [mem_iUnion]
    exact exists_congr fun n => hx n

lemma completedFactor_le (m : MeasurableSpace Ω) : completedFactor (m₀ := m₀) μ m ≤ m₀ :=
  fun _ hs => hs.1

lemma le_completedFactor {m : MeasurableSpace Ω} (hm : m ≤ m₀) : m ≤ completedFactor (m₀ := m₀) μ m :=
  fun s hs => ⟨hm s hs,s,hs,Eventually.of_forall fun _ => Iff.rfl⟩

lemma completedFactor_mono : Monotone (completedFactor (m₀ := m₀) μ) := by
  intro m n h s hs
  obtain ⟨hs,t,ht,he⟩ := hs
  exact ⟨hs,t,h t ht,he⟩

lemma completedFactor_congr_set (m : MeasurableSpace Ω) (s t : Set Ω)
    (hs : MeasurableSet[m₀] s) (ht : MeasurableSet[completedFactor (m₀ := m₀) μ m] t)
    (he : ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t) : MeasurableSet[completedFactor (m₀ := m₀) μ m] s := by
  obtain ⟨_,r,hr,her⟩ := ht
  exact ⟨hs,r,hr,he.and her |>.mono fun x hx => hx.1.trans hx.2⟩

lemma measurable_completedFactor_of_ae {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (m : MeasurableSpace Ω) {f : Ω → Y} (hf : Measurable[m₀] f)
    (h : AEStronglyMeasurable[m] f μ) : Measurable[completedFactor (m₀ := m₀) μ m] f := by
  intro s hs
  exact ⟨hf hs,(h.mk f) ⁻¹' s,h.stronglyMeasurable_mk.measurable hs,
    h.ae_eq_mk.mono fun x hx => by simp only [mem_preimage,hx]⟩

lemma completedFactor_iInf_measurable {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (m : ℕ → MeasurableSpace Ω) {f : Ω → Y} (hf : Measurable[m₀] f)
    (h : ∀ n, AEStronglyMeasurable[m n] f μ) :
    Measurable[⨅ n, completedFactor (m₀ := m₀) μ (m n)] f := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr fun n =>
    measurable_completedFactor_of_ae μ (m n) hf (h n) hs

end


section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

lemma aeStrong_limit_factor {E : Type*} [TopologicalSpace E] [Nonempty E]
    [TopologicalSpace.IsCompletelyMetrizableSpace E] (m : MeasurableSpace Ω)
    {f : ℕ → Ω → E} {g : Ω → E} (hf : ∀ n, AEStronglyMeasurable[m] (f n) μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    AEStronglyMeasurable[m] g μ := by
  let F : ℕ → Ω → E := fun n => (hf n).mk (f n)
  have hF : ∀ n, StronglyMeasurable[m] (F n) := fun n => (hf n).stronglyMeasurable_mk
  refine ⟨fun x => limUnder atTop (fun n => F n x),StronglyMeasurable.limUnder hF,?_⟩
  filter_upwards [ht,ae_all_iff.mpr (fun n => (hf n).ae_eq_mk)] with x hx he
  have h : Tendsto (fun n => F n x) atTop (𝓝 (g x)) := by
    convert hx using 1
    funext n
    exact (he n).symm
  exact h.limUnder_eq.symm

lemma simpleFunc_aeStrong_of_completed (m : MeasurableSpace Ω)
    (g : @SimpleFunc Ω (completedFactor (m₀ := m₀) μ m) ℝ) :
    AEStronglyMeasurable[m] g μ := by
  classical
  have hsets : ∀ c : ℝ, ∃ t : Set Ω, MeasurableSet[m] t ∧
      ∀ᵐ x ∂μ, g x = c ↔ x ∈ t := fun c => (@SimpleFunc.measurableSet_fiber Ω ℝ (completedFactor (m₀ := m₀) μ m) g c).2
  choose t ht he using hsets
  let G : Ω → ℝ := fun x => ∑ c ∈ (@SimpleFunc.range Ω ℝ (completedFactor (m₀ := m₀) μ m) g), (t c).indicator (fun _ => c) x
  have hm : StronglyMeasurable[m] G :=
    Finset.stronglyMeasurable_fun_sum _ fun c _ => stronglyMeasurable_const.indicator (ht c)
  refine ⟨G,hm,?_⟩
  filter_upwards [ae_all_iff.mpr (fun c : (@SimpleFunc.range Ω ℝ (completedFactor (m₀ := m₀) μ m) g) => he c.val)] with x hx
  have hi (c : ℝ) (hc : c ∈ (@SimpleFunc.range Ω ℝ (completedFactor (m₀ := m₀) μ m) g)) :
      (t c).indicator (fun _ => c) x = if g x = c then c else 0 := by
    simp only [Set.indicator_apply]
    rw [←hx ⟨c,hc⟩]
  dsimp [G]
  simp_rw [Finset.sum_congr rfl hi]
  symm
  rw [Finset.sum_eq_single (g x)]
  · simp only [ite_true]
  · intro c hc hne
    exact if_neg (Ne.symm hne)
  · intro hnot
    exact False.elim (hnot (@SimpleFunc.mem_range_self Ω ℝ (completedFactor (m₀ := m₀) μ m) g x))

lemma aeStrong_of_measurable_completed (m : MeasurableSpace Ω)
    {f : Ω → ℝ} (hf : Measurable[completedFactor (m₀ := m₀) μ m] f) :
    AEStronglyMeasurable[m] f μ := by
  have hs := hf.stronglyMeasurable
  exact aeStrong_limit_factor (m₀ := m₀) μ m (fun n => simpleFunc_aeStrong_of_completed (m₀ := m₀) μ m (hs.approx n))
    (Eventually.of_forall hs.tendsto_approx)

end


section
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

local instance complete_iInf (K : ℕ → Submodule 𝕜 H) [∀ n, CompleteSpace (K n)] :
    CompleteSpace ↥(⨅ n, K n) := by
  have h : IsClosed (↑(⨅ n, K n) : Set H) := by
    simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun n => (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (K n))).isClosed
  exact h.completeSpace_coe

lemma antitone_projection_tendsto (K : ℕ → Submodule 𝕜 H)
    [∀ n, CompleteSpace (K n)] (hK : Antitone K) (x : H) :
    Tendsto (fun n => (K n).starProjection x) atTop
      (𝓝 ((⨅ n, K n).starProjection x)) := by
  have he : (⨆ n, (K n)ᗮ)ᗮ = ⨅ n, K n := by
    apply le_antisymm
    · apply le_iInf
      intro n
      simpa only [Submodule.orthogonal_orthogonal] using
        (Submodule.orthogonal_le (le_iSup (fun n => (K n)ᗮ) n))
    · intro x hx y hy
      have hy' : y ∈ (⨅ n, K n)ᗮ :=
        (iSup_le (fun n => Submodule.orthogonal_le (iInf_le K n))) hy
      exact inner_eq_zero_symm.mp (hy' x hx)
  have he' : (⨆ n, (K n)ᗮ).topologicalClosure = (⨅ n, K n)ᗮ := by
    rw [←Submodule.orthogonal_orthogonal_eq_closure,he]
  have ht := Submodule.starProjection_tendsto_closure_iSup
    (fun n => (K n)ᗮ) (fun a b h => Submodule.orthogonal_le (hK h)) x
  simp only [he'] at ht
  have hh := (tendsto_const_nhds (x := x) (f := atTop)).sub ht
  simpa only [Submodule.starProjection_orthogonal_val,sub_sub_cancel] using hh

end


section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

lemma lpMeas_completed_eq (m : MeasurableSpace Ω) (hm : m ≤ m₀) :
    @lpMeas Ω ℝ ℝ _ _ _ (completedFactor (m₀ := m₀) μ m) m₀ 2 μ = @lpMeas Ω ℝ ℝ _ _ _ m m₀ 2 μ := by
  ext f
  simp only [mem_lpMeas_iff_aestronglyMeasurable]
  constructor
  · intro h
    have hm' : Measurable[completedFactor (m₀ := m₀) μ m] (h.mk f) := h.stronglyMeasurable_mk.measurable
    exact (aeStrong_of_measurable_completed (m₀ := m₀) μ m hm').congr h.ae_eq_mk.symm
  · exact fun h => h.mono (le_completedFactor (m₀ := m₀) μ hm)

lemma lpMeas_completed_iInf (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀) :
    @lpMeas Ω ℝ ℝ _ _ _ (⨅ n, completedFactor (m₀ := m₀) μ (m n)) m₀ 2 μ = ⨅ n, @lpMeas Ω ℝ ℝ _ _ _ (m n) m₀ 2 μ := by
  ext f
  simp only [Submodule.mem_iInf,mem_lpMeas_iff_aestronglyMeasurable]
  constructor
  · intro h n
    have h' := h.mono (iInf_le (fun n => completedFactor (m₀ := m₀) μ (m n)) n)
    have hh : f ∈ @lpMeas Ω ℝ ℝ _ _ _ (completedFactor (m₀ := m₀) μ (m n)) m₀ 2 μ := by
      exact mem_lpMeas_iff_aestronglyMeasurable.mpr h'
    rw [lpMeas_completed_eq μ (m n) (hm n)] at hh
    exact mem_lpMeas_iff_aestronglyMeasurable.mp hh
  · intro h
    exact (completedFactor_iInf_measurable μ m (Lp.stronglyMeasurable f).measurable h).stronglyMeasurable.aestronglyMeasurable

lemma reverse_conditional_L2 (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => (condExpL2 ℝ ℝ (hm n) f : Lp ℝ 2 μ)) atTop
      (𝓝 (condExpL2 ℝ ℝ
        (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
          (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f : Lp ℝ 2 μ)) := by
  let K : ℕ → Submodule ℝ (Lp ℝ 2 μ) := fun n => @lpMeas Ω ℝ ℝ _ _ _ (m n) m₀ 2 μ
  let (n : ℕ) : Fact (m n ≤ m₀) := ⟨hm n⟩
  have hK : Antitone K := by
    intro a b hab f hf
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      ((mem_lpMeas_iff_aestronglyMeasurable.mp hf).mono (hanti hab))
  have h := antitone_projection_tendsto K hK f
  have ht : Fact ((⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀) :=
    ⟨(iInf_le _ 0).trans (completedFactor_le μ (m 0))⟩
  let := ht
  simpa only [K, ←lpMeas_completed_iInf μ m hm, Submodule.starProjection_apply,condExpL2] using h

end


section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [retained6 : IsProbabilityMeasure μ]

include retained6 in
lemma reverse_tail_pairing_along (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (c : ℕ → ℕ) (hc : Tendsto c atTop atTop)
    (f : Lp ℝ 2 μ) (g : ℕ → Lp ℝ 2 μ)
    (hg : ∀ n, AEStronglyMeasurable[m (c n)] (g n) μ) (hb : ∀ n, ‖g n‖ ≤ 1) :
    Tendsto (fun n => ⟪f - (condExpL2 ℝ ℝ
      (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
        (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f : Lp ℝ 2 μ), g n⟫)
      atTop (𝓝 0) := by
  let _ := retained6
  let ft : Lp ℝ 2 μ := condExpL2 ℝ ℝ
    (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
      (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f
  have he n : ⟪f-ft,g n⟫ = ⟪(condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft,g n⟫ := by
    simp only [inner_sub_left,inner_condExpL2_eq_inner_fun (hm (c n)) f (g n) (hg n)]
  have hbound n : |⟪f-ft,g n⟫| ≤ ‖(condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft‖ := by
    rw [he]
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg ((condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft),hb n])
  have ht := (reverse_conditional_L2 μ m hm hanti f).comp hc
  have ht' : Tendsto (fun n => ‖(condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft‖) atTop (𝓝 0) := by
    simpa only [ft,sub_self,norm_zero,Function.comp_apply] using (ht.sub (tendsto_const_nhds (x := ft))).norm
  exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hbound n) ht'

lemma integral_tail_replacement (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (c : ℕ → ℕ) (hc : Tendsto c atTop atTop)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable[m (c n)] (g n)) (hb : ∀ n x, |g n x| ≤ 1) :
    Tendsto (fun n => ∫ x, (f x-μ[f | ⨅ n, completedFactor (m₀ := m₀) μ (m n)] x)*g n x ∂μ)
      atTop (𝓝 0) := by
  have hgm n : MemLp (g n) 2 μ := MemLp.of_bound
    ((hg n).mono (hm (c n)) le_rfl).aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb n x)
  let G n : Lp ℝ 2 μ := (hgm n).toLp (g n)
  let ht : (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ :=
    (iInf_le _ 0).trans (completedFactor_le μ (m 0))
  let F : Lp ℝ 2 μ := hf.toLp f
  let FT : Lp ℝ 2 μ := condExpL2 ℝ ℝ ht F
  have hG n : AEStronglyMeasurable[m (c n)] (G n) μ :=
    (hg n).stronglyMeasurable.aestronglyMeasurable.congr (hgm n).coeFn_toLp.symm
  have hGb n : ‖G n‖ ≤ 1 := by
    have hb' : ∀ᵐ x ∂μ, ‖G n x‖ ≤ (1:ℝ) := by
      filter_upwards [(hgm n).coeFn_toLp] with x hx
      simpa only [G,hx,Real.norm_eq_abs] using hb n x
    simpa only [measureUnivNNReal,measure_univ,ENNReal.toNNReal_one,NNReal.coe_one,Real.one_rpow,one_mul]
      using Lp.norm_le_of_ae_bound (f := G n) (by norm_num : (0:ℝ) ≤ 1) hb'
  have hh := reverse_tail_pairing_along μ m hm hanti c hc F G hG hGb
  change Tendsto (fun n => ⟪F-FT,G n⟫) atTop (𝓝 0) at hh
  convert hh using 1
  funext n
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,(hgm n).coeFn_toLp,
    hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) ht,Lp.coeFn_sub F FT] with x hx hy hz hw
  change F x = f x at hx
  change G n x = g n x at hy
  change FT x = μ[f | ⨅ n, completedFactor (m₀ := m₀) μ (m n)] x at hz
  rw [hw,Pi.sub_apply,hx,hy,hz]
  simp [mul_comm]

end


end OMA.RokhlinBackward

theorem OMA.solution : OMA.R_arxiv_2411_07234_R1_H2_R1.H1 := by
  intro X _ μ _ m hm hanti f hf w hw hb
  exact OMA.RokhlinBackward.integral_tail_replacement μ m hm hanti id Filter.tendsto_id f hf w hw hb

/-
Apache License 2.0 for the adapted source portions.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
