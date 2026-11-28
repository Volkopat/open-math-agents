import OMAReductions.R_arxiv_2411_07234_R1

/-! The fixed-layout step for Rokhlin's multiple-mixing problem. The adaptation uses
the conditioning and final indicator argument in OpenAI, `openai/math` revision
`3344da59991ed94f9ba711217b29c1d760badfa6`, files
`lean/OAI/Dynamics/MultipleMixing/Entropy.lean`, `HilbertCodes.lean`, `Tail.lean`,
and `Main.lean`, under Apache License 2.0. The filtration is expressed directly
by its one-coordinate generators, and the two analytic inputs are explicit. -/

namespace OMA.R_arxiv_2411_07234_R1_H2_R1

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal


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
    simp only [Set.mem_iUnion]
    exact exists_congr fun n => hx n

lemma completedFactor_le (m : MeasurableSpace Ω) : completedFactor (m₀ := m₀) μ m ≤ m₀ :=
  fun _ hs => hs.1
private abbrev completedTail (m : ℕ → MeasurableSpace Ω) : MeasurableSpace Ω :=
  ⨅ n, completedFactor μ (m n)

private theorem completedTail_le (m : ℕ → MeasurableSpace Ω) : completedTail μ m ≤ m₀ :=
  (iInf_le _ 0).trans (completedFactor_le μ _)

end


section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {A : Type*} [MeasurableSpace A]
private def timeMap (T : Ω ≃ᵐ Ω) (n : ℤ) : Ω → Ω :=
  ⇑((T.toEquiv : Equiv.Perm Ω) ^ n)

lemma timeMap_add (T : Ω ≃ᵐ Ω) (m n : ℤ) : timeMap T (m+n) = timeMap T m ∘ timeMap T n := by
  simp only [timeMap,zpow_add,Equiv.Perm.coe_mul]
lemma timeMap_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T n = (T : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_natCast,Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv]
lemma timeMap_neg_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T (-(n:ℤ)) = (T.symm : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_neg,zpow_natCast,←inv_pow,Equiv.Perm.coe_pow]
  rfl

lemma timeMap_measurable (T : Ω ≃ᵐ Ω) (n : ℤ) : Measurable (timeMap T n) := by
  induction n using Int.negInduction with
  | nat n => rw [timeMap_nat]; exact T.measurable.iterate n
  | neg _ n => rw [timeMap_neg_nat]; exact T.symm.measurable.iterate n

private abbrev observableProcess (T : Ω ≃ᵐ Ω) (a : Ω → A) : ℤ → Ω → A :=
  fun q x => a (timeMap T q x)

private abbrev processPast (F : ℤ → Ω → A) (t : ℤ) : MeasurableSpace Ω :=
  ⨆ q : {q : ℤ // q < t}, MeasurableSpace.comap (F q) inferInstance

private theorem processPast_le (F : ℤ → Ω → A) (hF : ∀ q, Measurable (F q)) (t : ℤ) :
    processPast F t ≤ m₀ :=
  iSup_le fun q => (hF q).comap_le

omit m₀ in
private theorem processPast_mono (F : ℤ → Ω → A) : Monotone (processPast F) := by
  intro s t h
  apply iSup_le
  intro q
  exact le_iSup_of_le ⟨q.val, q.property.trans_le h⟩ le_rfl

omit m₀ in
private theorem processPast_coord (F : ℤ → Ω → A) {q t : ℤ} (h : q < t) :
    Measurable[processPast F t] (F q) :=
  measurable_iff_comap_le.mpr (le_iSup_of_le ⟨q, h⟩ le_rfl)

private abbrev observableTail (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (a : Ω → A) :
    MeasurableSpace Ω :=
  completedTail μ (fun n => processPast (observableProcess T a) (-(n:ℤ)))

private theorem observableProcess_measurable (T : Ω ≃ᵐ Ω) (a : Ω → A)
    (ha : Measurable a) (q : ℤ) : Measurable (observableProcess T a q) :=
  ha.comp (timeMap_measurable T q)

end


section
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
private noncomputable def clippedConditional (m : MeasurableSpace Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => max 0 (min 1 (μ[f | m] x))

omit [IsProbabilityMeasure μ] in
lemma clippedConditional_bounds (m : MeasurableSpace Ω) (f : Ω → ℝ) (x : Ω) :
    clippedConditional (m₀ := m₀) μ m f x ∈ Set.Icc (0:ℝ) 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

omit [IsProbabilityMeasure μ] in
lemma clippedConditional_measurable (m : MeasurableSpace Ω) (f : Ω → ℝ) :
    Measurable[m] (clippedConditional (m₀ := m₀) μ m f) := by
  exact measurable_const.max (measurable_const.min stronglyMeasurable_condExp.measurable)

omit [IsProbabilityMeasure μ] in
lemma clippedConditional_ae (m : MeasurableSpace Ω) (f : Ω → ℝ)
    (hf : ∀ᵐ x ∂μ, f x ∈ Set.Icc (0:ℝ) 1) :
    clippedConditional (m₀ := m₀) μ m f =ᵐ[μ] μ[f | m] := by
  let : MeasurableSpace Ω := m₀
  have hn := condExp_nonneg (m := m) (hf.mono fun _ h => h.1)
  have hb := condExp_le_nonneg_const (m := m) (show (0:ℝ) ≤ 1 by norm_num) (hf.mono fun _ h => h.2)
  filter_upwards [hn,hb] with x hx hy
  change (0:ℝ) ≤ μ[f | m] x at hx
  simp only [clippedConditional,min_eq_right hy,max_eq_right hx]

lemma clippedConditional_mean (m : MeasurableSpace Ω) (hm : m ≤ m₀) (f : Ω → ℝ)
    (hf : ∀ᵐ x ∂μ, f x ∈ Set.Icc (0:ℝ) 1) :
    (∫ x, clippedConditional (m₀ := m₀) μ m f x ∂μ) = ∫ x, f x ∂μ := by
  let : MeasurableSpace Ω := m₀
  rw [integral_congr_ae (clippedConditional_ae (m₀ := m₀) μ m f hf),integral_condExp hm]
end


private abbrev OrdinaryMixing {X : Type} [MeasurableSpace X] (μ : Measure X) (T : X ≃ᵐ X) :
    Prop :=
  ∀ s t : Set X, MeasurableSet s → MeasurableSet t →
    Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s * μ t))

private abbrev ProperRectangles {X : Type} [MeasurableSpace X] (μ : Measure X)
    (T : X ≃ᵐ X) {k : ℕ} (d : ℕ → Fin k → ℕ) : Prop :=
  ∀ J : Finset (Fin k), J ≠ Finset.univ → ∀ s : J → Set X,
    (∀ j, MeasurableSet (s j)) →
    Tendsto (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop (𝓝 (∏ j : J, μ (s j)))

/-- Backward conditional-expectation convergence paired with a bounded observable from the
corresponding level. The tail uses relative completion inside the ambient measure space. -/
def H1 : Prop :=
  ∀ (X : Type) [m₀ : MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace X), (∀ n, m n ≤ m₀) → Antitone m →
    ∀ f : X → ℝ, MemLp f 2 μ → ∀ w : ℕ → X → ℝ,
    (∀ n, Measurable[m n] (w n)) → (∀ n x, |w n x| ≤ 1) →
    Tendsto (fun n => ∫ x, (f x - μ[f | completedTail μ m] x) * w n x ∂μ) atTop (𝓝 0)

/-- Centered tail correlations vanish in a mixing finite-alphabet process with independent
limiting proper rectangles. -/
def H2 : Prop :=
  ∀ (X A : Type) [MeasurableSpace X] [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X ≃ᵐ X), MeasurePreserving T μ μ → OrdinaryMixing μ T →
    ∀ k, 3 ≤ k → ∀ d : ℕ → Fin k → ℕ, ProperRectangles μ T d →
    ∀ (a : X → A), Measurable a → ∀ g : X → ℝ,
    Measurable[observableTail μ T a] g → (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ (i : Fin k) (f : Fin k → A → ℝ), (∀ j z, |f j z| ≤ 1) →
    Tendsto (fun r => ∫ x, (g ((T^[d r i]) x) - ∫ y, g y ∂μ) *
      ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0)

section
variable {Ω : Type} [m₀ : MeasurableSpace Ω]


lemma integral_comp_preserving (μ : Measure Ω) (U : Ω → Ω) (hU : MeasurePreserving U μ μ)
    (f : Ω → ℝ) (hf : Measurable f) : (∫ x, f (U x) ∂μ) = ∫ x, f x ∂μ := by
  have h := integral_map (μ := μ) hU.measurable.aemeasurable
    (hf.aestronglyMeasurable (μ := Measure.map U μ))
  simpa only [hU.map_eq] using h.symm

lemma integral_mean_interval (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ x, g x ∈ Set.Icc (0:ℝ) 1) :
    (∫ x, g x ∂μ) ∈ Set.Icc (0:ℝ) 1 := by
  have hi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hb x).1]; exact (hb x).2)
  exact ⟨integral_nonneg fun x => (hb x).1, by
    simpa using integral_mono hi (integrable_const (1:ℝ)) (fun x => (hb x).2)⟩


lemma real_integrable_bound (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)


variable {I A : Type} [Fintype I] [DecidableEq I]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]


theorem remote_last_replacement (hMart : H1) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (d : ℕ → I → ℕ) (i : I) (hremote : ∀ r j, j ≠ i → d r j+r < d r i)
    (a : Ω → A) (ha : Measurable a) (f : I → A → ℝ)
    (hf : ∀ j z, f j z ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun r => ∫ x,
      (f i (a ((T^[d r i]) x)) - clippedConditional μ (observableTail μ T a) (fun y => f i (a y)) ((T^[d r i]) x)) *
      ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  let F := observableProcess T a
  let m (n : ℕ) := processPast F (-(n:ℤ))
  have hm n : m n ≤ m₀ := processPast_le F (observableProcess_measurable T a ha) _
  have hanti : Antitone m := fun n l h => processPast_mono F (by omega)
  let w r x := ∏ j ∈ Finset.univ.erase i, f j (F ((d r j:ℤ)-(d r i:ℤ)) x)
  have hw r : Measurable[m r] (w r) := by
    apply Finset.measurable_prod
    intro j hj
    apply (measurable_of_finite (f j)).comp
    apply processPast_coord
    have hh := hremote r j (Finset.ne_of_mem_erase hj)
    omega
  have hwb r x : |w r x| ≤ 1 := by
    dsimp [w]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => by
      rw [abs_of_nonneg (hf j _).1]; exact (hf j _).2)
  have hfm : Measurable (fun x => f i (a x)) := (measurable_of_finite _).comp ha
  have hfb x : |f i (a x)| ≤ 1 := by rw [abs_of_nonneg (hf i _).1]; exact (hf i _).2
  have hflp : MemLp (fun x => f i (a x)) 2 μ := MemLp.of_bound hfm.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfb x)
  have hrep := hMart Ω μ m hm hanti _ hflp w hw hwb
  let g := clippedConditional μ (observableTail μ T a) (fun x => f i (a x))
  have hgm : Measurable g := (clippedConditional_measurable μ _ _).mono (completedTail_le μ _) le_rfl
  have hgae : g =ᵐ[μ] μ[(fun x => f i (a x)) | observableTail μ T a] :=
    clippedConditional_ae μ _ _ (Eventually.of_forall fun x => hf i (a x))
  have he r : (∫ x, (f i (a x)-g x)*w r x ∂μ) =
      ∫ x, (f i (a x)-μ[(fun x => f i (a x)) | observableTail μ T a] x)*w r x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hgae] with x hx
    rw [hx]
  have ht : Tendsto (fun r => ∫ x, (f i (a x)-g x)*w r x ∂μ) atTop (𝓝 0) := by
    simpa only [he] using hrep
  convert ht using 1
  funext r
  have hwm : Measurable (w r) := (hw r).mono (hm r) le_rfl
  have hi := integral_comp_preserving μ (T^[d r i]) (hT.iterate (d r i)) (fun x => (f i (a x)-g x)*w r x) ((hfm.sub hgm).mul hwm)
  rw [←hi]
  apply integral_congr_ae
  filter_upwards with x
  change (_-g ((T^[d r i]) x))*_ = (_-g ((T^[d r i]) x))*_
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  dsimp [w,F,observableProcess]
  rw [←timeMap_nat T (d r i)]
  symm
  change f j (a ((timeMap T ((d r j:ℤ)-(d r i:ℤ)) ∘ timeMap T (d r i)) x)) = _
  rw [←timeMap_add,sub_add_cancel,timeMap_nat]


theorem last_centered_correlation_zero (hMart : H1) (hCorr : H2) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    {k : ℕ} (hk : 3 ≤ k) (d : ℕ → Fin k → ℕ)
    (hrect : ∀ J : Finset (Fin k), J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    (i : Fin k) (hremote : ∀ r j, j ≠ i → d r j+r < d r i)
    (a : Ω → A) (ha : Measurable a) (f : Fin k → A → ℝ)
    (hf : ∀ j z, f j z ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun r => ∫ x, (f i (a ((T^[d r i]) x))-∫ y, f i (a y) ∂μ) *
      ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  let g := clippedConditional μ (observableTail μ T a) (fun y => f i (a y))
  have hg : Measurable[observableTail μ T a] g := clippedConditional_measurable μ _ _
  have hgb x : g x ∈ Set.Icc (0:ℝ) 1 := clippedConditional_bounds μ _ _ x
  have hgm : Measurable g := hg.mono (completedTail_le μ _) le_rfl
  have hf1 j z : |f j z| ≤ 1 := by rw [abs_of_nonneg (hf j z).1]; exact (hf j z).2
  have hc : (∫ x, g x ∂μ) = ∫ x, f i (a x) ∂μ :=
    clippedConditional_mean μ _ (completedTail_le μ _) _ (Eventually.of_forall fun x => hf i (a x))
  have htail := hCorr Ω A μ T hT hmix k hk d hrect a ha g hg hgb i f hf1
  have hrep := remote_last_replacement hMart μ T hT d i hremote a ha f hf
  have ht := hrep.add htail
  rw [add_zero] at ht
  convert ht using 1
  funext r
  let w x := ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x))
  have hwm : Measurable w := Finset.measurable_prod _ fun j _ =>
    (measurable_of_finite _).comp (ha.comp (T.measurable.iterate _))
  have hw x : |w x| ≤ 1 := by
    dsimp [w]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => hf1 j _)
  have hfm : Measurable (fun x => f i (a ((T^[d r i]) x))) :=
    (measurable_of_finite _).comp (ha.comp (T.measurable.iterate _))
  have hi1 : Integrable (fun x => (f i (a ((T^[d r i]) x))-g ((T^[d r i]) x))*w x) μ := by
    apply real_integrable_bound μ ((hfm.sub (hgm.comp (T.measurable.iterate _))).mul hwm) 1
    intro x
    simp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
    rw [abs_mul]
    apply (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) _ (abs_nonneg _) (hw x)
    exact abs_le.mpr ⟨by linarith [(hf i (a ((T^[d r i]) x))).1,(hgb ((T^[d r i]) x)).2],
      by linarith [(hf i (a ((T^[d r i]) x))).2,(hgb ((T^[d r i]) x)).1]⟩
  have hmean := integral_mean_interval μ g hgm hgb
  have hi2 : Integrable (fun x => (g ((T^[d r i]) x)-∫ y, g y ∂μ)*w x) μ := by
    apply real_integrable_bound μ (((hgm.comp (T.measurable.iterate _)).sub measurable_const).mul hwm) 1
    intro x
    simp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
    rw [abs_mul]
    apply (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) _ (abs_nonneg _) (hw x)
    exact abs_le.mpr ⟨by linarith [(hgb ((T^[d r i]) x)).1,hmean.2],
      by linarith [(hgb ((T^[d r i]) x)).2,hmean.1]⟩
  change (∫ x, (_-_)*w x ∂μ) = (∫ x, _*w x ∂μ)+(∫ x, _*w x ∂μ)
  rw [←integral_add hi1 hi2]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hc]
  ring

end


section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω I : Type*} [retained25 : MeasurableSpace Ω] [Fintype I]

private noncomputable def setIndicator (s : Set Ω) (x : Ω) : ℝ := by classical exact if x ∈ s then 1 else 0
include retained25 in
lemma setIndicator_bounds (s : Set Ω) (x : Ω) : setIndicator s x ∈ Set.Icc (0:ℝ) 1 := by
  let _ := retained25
  unfold setIndicator
  split_ifs <;> norm_num
lemma setIndicator_measurable {s : Set Ω} (hs : MeasurableSet s) : Measurable (setIndicator s) := by
  exact Measurable.ite hs measurable_const measurable_const
include retained25 in
lemma prod_setIndicator (s : I → Set Ω) (x : Ω) :
    (∏ i, setIndicator (s i) x) = setIndicator (⋂ i, s i) x := by
  let _ := retained25
  classical
  by_cases hx : x ∈ ⋂ i, s i
  · have hmem i : x ∈ s i := Set.mem_iInter.mp hx i
    simp [setIndicator,hx,hmem]
  · have hn : ∃ i, x ∉ s i := by simpa only [Set.mem_iInter,not_forall] using hx
    obtain ⟨i,hi⟩ := hn
    rw [setIndicator,if_neg hx]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [setIndicator,hi])
lemma integral_setIndicator (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x, setIndicator s x ∂μ) = (μ s).toReal := by
  have he : setIndicator s = s.indicator (1 : Ω → ℝ) := by
    funext x
    simp [setIndicator,Set.indicator]
  rw [he]
  exact integral_indicator_one hs
lemma integral_prod_setIndicator (μ : Measure Ω) (s : I → Set Ω) (hs : ∀ i, MeasurableSet (s i)) :
    (∫ x, ∏ i, setIndicator (s i) x ∂μ) = (μ (⋂ i, s i)).toReal := by
  simp_rw [prod_setIndicator]
  exact integral_setIndicator μ (MeasurableSet.iInter hs)
include retained25 in
lemma setIndicator_preimage (s : Set Ω) (U : Ω → Ω) (x : Ω) :
    setIndicator s (U x) = setIndicator (U ⁻¹' s) x := by
  let _ := retained25
  rfl
end


theorem main : H1 → H2 → OMA.R_arxiv_2411_07234_R1.H2 := by
  intro hMart hCorr X _ μ _ T hT hmix k hk d hd hrect S hS
  classical
  let i : Fin k := ⟨k-1,by omega⟩
  have hremote r j (hj : j ≠ i) : d r j+r < d r i := by
    apply hd r j i
    have hne : j.val ≠ k-1 := fun h => hj (Fin.ext h)
    have := j.isLt
    change j.val < k-1
    omega
  let a : X → (Fin k → Bool) := fun x j => if x ∈ S j then true else false
  have ha : Measurable a := measurable_pi_iff.mpr fun j =>
    Measurable.ite (hS j) measurable_const measurable_const
  let f : Fin k → (Fin k → Bool) → ℝ := fun j z => if z j then 1 else 0
  have hf j z : f j z ∈ Set.Icc (0:ℝ) 1 := by dsimp [f]; split_ifs <;> norm_num
  have hfa j x : f j (a x) = setIndicator (S j) x := by
    by_cases hx : x ∈ S j <;> simp [f,a,setIndicator,hx]
  have ht := last_centered_correlation_zero hMart hCorr μ T hT hmix hk d hrect i hremote a ha f hf
  simp_rw [hfa] at ht
  rw [integral_setIndicator μ (hS i)] at ht
  let J : Finset (Fin k) := Finset.univ.erase i
  have hJ : J ≠ Finset.univ := by
    intro h
    have : i ∈ J := h ▸ Finset.mem_univ i
    exact Finset.notMem_erase i Finset.univ this
  have hp := hrect J hJ (fun j => S j) (fun j => hS j)
  have hpR := (ENNReal.continuousAt_toReal (show (∏ j : J, μ (S j)) ≠ ∞ from ENNReal.prod_ne_top (fun _ _ => measure_ne_top μ _))).tendsto.comp hp
  let w r x := ∏ j ∈ J, setIndicator (S j) ((T^[d r j]) x)
  have hwmeas r : Measurable (w r) := Finset.measurable_prod _ fun j _ =>
    (setIndicator_measurable (hS j)).comp (T.measurable.iterate _)
  have hwb r x : |w r x| ≤ 1 := by
    dsimp [w]
    rw [Finset.abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro j hj
    have hh := setIndicator_bounds (S j) ((T^[d r j]) x)
    rw [abs_of_nonneg hh.1]
    exact hh.2
  have hwi r : Integrable (w r) μ := real_integrable_bound μ (hwmeas r) 1 (hwb r)
  have hew r : (∫ x, w r x ∂μ) = (μ (⋂ j : J, (T^[d r j]) ⁻¹' S j)).toReal := by
    have he : w r = fun x => ∏ j : J, setIndicator (S j) ((T^[d r j]) x) := by
      funext x
      exact (Finset.prod_coe_sort J (fun j => setIndicator (S j) ((T^[d r j]) x))).symm
    rw [he]
    simp_rw [setIndicator_preimage]
    exact integral_prod_setIndicator μ _ (fun j => (hS j).preimage (T.measurable.iterate _))
  have hpR' : Tendsto (fun r => ∫ x, w r x ∂μ) atTop (𝓝 (∏ j ∈ J, (μ (S j)).toReal)) := by
    change Tendsto (fun r => (μ (⋂ j : J, (T^[d r j]) ⁻¹' S j)).toReal) atTop
      (𝓝 ((∏ j : J, μ (S j)).toReal)) at hpR
    rw [ENNReal.toReal_prod,Finset.prod_coe_sort J (fun j => (μ (S j)).toReal)] at hpR
    simpa only [hew] using hpR
  have hwhole r : (∫ x, ∏ j, setIndicator (S j) ((T^[d r j]) x) ∂μ) =
      (μ (⋂ j, (T^[d r j]) ⁻¹' S j)).toReal := by
    simp_rw [setIndicator_preimage]
    exact integral_prod_setIndicator μ _ (fun j => (hS j).preimage (T.measurable.iterate _))
  have hsplit r : (∫ x, (setIndicator (S i) ((T^[d r i]) x)-(μ (S i)).toReal)*w r x ∂μ) =
      (μ (⋂ j, (T^[d r j]) ⁻¹' S j)).toReal - (μ (S i)).toReal*(∫ x, w r x ∂μ) := by
    have hi : Integrable (fun x => setIndicator (S i) ((T^[d r i]) x)*w r x) μ := by
      apply real_integrable_bound μ (((setIndicator_measurable (hS i)).comp (T.measurable.iterate _)).mul (hwmeas r)) 1
      intro x
      change |setIndicator (S i) ((T^[d r i]) x)*w r x| ≤ 1
      rw [abs_mul]
      apply (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) _ (abs_nonneg _) (hwb r x)
      have hh := setIndicator_bounds (S i) ((T^[d r i]) x)
      rw [abs_of_nonneg hh.1]
      exact hh.2
    simp_rw [sub_mul]
    rw [integral_sub hi ((hwi r).const_mul _),integral_const_mul]
    congr 1
    rw [←hwhole]
    apply integral_congr_ae
    filter_upwards with x
    exact Finset.mul_prod_erase Finset.univ (fun j => setIndicator (S j) ((T^[d r j]) x)) (Finset.mem_univ i)
  change Tendsto (fun r => ∫ x, (setIndicator (S i) ((T^[d r i]) x)-(μ (S i)).toReal)*w r x ∂μ) atTop (𝓝 0) at ht
  simp_rw [hsplit] at ht
  have hconst : Tendsto (fun _ : ℕ => (μ (S i)).toReal) atTop (𝓝 ((μ (S i)).toReal)) := tendsto_const_nhds
  have hsum := ht.add (hconst.mul hpR')
  change Tendsto (fun r => ((μ (⋂ j, (T^[d r j]) ⁻¹' S j)).toReal -
    (μ (S i)).toReal*(∫ x, w r x ∂μ))+(μ (S i)).toReal*(∫ x, w r x ∂μ)) atTop
    (𝓝 (0+(μ (S i)).toReal*(∏ j ∈ J, (μ (S j)).toReal))) at hsum
  simp only [sub_add_cancel,zero_add] at hsum
  have hprod : (μ (S i)).toReal*(∏ j ∈ J, (μ (S j)).toReal) = (∏ j, μ (S j)).toReal := by
    rw [ENNReal.toReal_prod]
    exact Finset.mul_prod_erase Finset.univ (fun j => (μ (S j)).toReal) (Finset.mem_univ i)
  rw [hprod] at hsum
  exact (ENNReal.tendsto_toReal_iff (fun _ => measure_ne_top μ _) (ENNReal.prod_ne_top (fun _ _ => measure_ne_top μ _))).mp hsum

end OMA.R_arxiv_2411_07234_R1_H2_R1

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
