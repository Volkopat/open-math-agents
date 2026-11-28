import OMAStatements.S_mo_107177
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.Nat

/-! Probability infrastructure simplified using Mathlib; the original
counterexample and strong-law argument are due to @Git-Tim1 (PR #11318). -/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace OMA_mo_107177_Aux

abbrev V : Type := ℕ × ℝ

/-- The class of subsets of `ℕ × ℝ` with finite horizontal slices. -/
def C : Set (Set V) :=
  {A | ∀ k : ℕ, {r : ℝ | (k, r) ∈ A}.Finite}

private lemma countable_of_mem_C {A : Set V} (hA : A ∈ C) : A.Countable := by
  have hEq : A = ⋃ k : ℕ, (Prod.mk k) '' {r : ℝ | (k, r) ∈ A} := by
    ext ⟨k, r⟩
    simp
  rw [hEq]
  exact Set.countable_iUnion fun k => ((hA k).countable).image (Prod.mk k)

private lemma measurableSet_of_mem_C {A : Set V} (hA : A ∈ C) : MeasurableSet A :=
  (countable_of_mem_C hA).measurableSet

private lemma prob_eq_one_of_compl_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Set Ω} (hE : MeasurableSet E)
    (hEc : P Eᶜ = 0) : P E = 1 := by
  exact (prob_compl_eq_zero_iff hE).mp hEc

private lemma prob_compl_eq_zero_of_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Set Ω} (hE : MeasurableSet E)
    (hE1 : P E = 1) : P Eᶜ = 0 := by
  exact (prob_compl_eq_zero_iff hE).mpr hE1

private lemma prob_inter_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E F : Set Ω}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hE1 : P E = 1) (hF1 : P F = 1) :
    P (E ∩ F) = 1 := by
  exact (mem_ae_iff_prob_eq_one (hE.inter hF)).mp
    (Filter.inter_mem ((mem_ae_iff_prob_eq_one hE).mpr hE1)
      ((mem_ae_iff_prob_eq_one hF).mpr hF1))

private lemma measureReal_finset_eq_sum {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] (F : Finset α) :
    μ.real (F : Set α) = ∑ a ∈ F, μ.real {a} := by
  exact (sum_measureReal_singleton (μ := μ) F).symm

private lemma countable_atoms (μ : Measure V) [IsProbabilityMeasure μ] :
    {v : V | μ {v} ≠ 0}.Countable := by
  simpa only [pos_iff_ne_zero] using
    (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
      (fun v : V => measurableSet_singleton v)
      (fun _ _ h => Set.disjoint_singleton.mpr h))

private lemma empirical_eq_sum_indicator {α : Type*} (x : ℕ → α) (A : Set α) (n : ℕ) :
    OMA.S_mo_107177.empirical x A n =
      (∑ k ∈ Finset.range n, A.indicator (fun _ => (1 : ℝ)) (x k)) / (n : ℝ) := by
  classical
  unfold OMA.S_mo_107177.empirical
  congr 1
  simp only [Set.indicator_apply, Finset.sum_boole]

private lemma measurable_empirical {α : Type*} [MeasurableSpace α] {A : Set α}
    (hA : MeasurableSet A) (n : ℕ) :
    Measurable (fun x : ℕ → α => OMA.S_mo_107177.empirical x A n) := by
  have hEq : (fun x : ℕ → α => OMA.S_mo_107177.empirical x A n) =
      fun x => (∑ k ∈ Finset.range n, A.indicator (fun _ => (1 : ℝ)) (x k)) / (n : ℝ) := by
    ext x
    exact empirical_eq_sum_indicator x A n
  rw [hEq]
  refine Measurable.div_const ?_ _
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (measurable_const.indicator hA).comp (measurable_pi_apply k)

private lemma empirical_nonneg {α : Type*} (x : ℕ → α) (A : Set α) (n : ℕ) :
    0 ≤ OMA.S_mo_107177.empirical x A n := by
  unfold OMA.S_mo_107177.empirical
  positivity

private lemma empirical_mono {α : Type*} (x : ℕ → α) {A B : Set α} (hAB : A ⊆ B) (n : ℕ) :
    OMA.S_mo_107177.empirical x A n ≤ OMA.S_mo_107177.empirical x B n := by
  classical
  unfold OMA.S_mo_107177.empirical
  gcongr

private lemma empirical_empty {α : Type*} (x : ℕ → α) (n : ℕ) :
    OMA.S_mo_107177.empirical x ∅ n = 0 := by
  unfold OMA.S_mo_107177.empirical
  simp

private lemma empirical_union_disjoint {α : Type*} (x : ℕ → α) {A B : Set α}
    (hAB : Disjoint A B) (n : ℕ) :
    OMA.S_mo_107177.empirical x (A ∪ B) n =
      OMA.S_mo_107177.empirical x A n + OMA.S_mo_107177.empirical x B n := by
  rw [empirical_eq_sum_indicator, empirical_eq_sum_indicator, empirical_eq_sum_indicator,
    ← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrFun (Set.indicator_union_of_disjoint hAB _) (x k)

private lemma empirical_finset_eq_sum {α : Type*} (x : ℕ → α) (F : Finset α) (n : ℕ) :
    OMA.S_mo_107177.empirical x (F : Set α) n = ∑ a ∈ F, OMA.S_mo_107177.empirical x {a} n := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [empirical_empty]
  | insert a s ha ih =>
    rw [Finset.coe_insert, Set.insert_eq,
      empirical_union_disjoint x (Set.disjoint_singleton_left.mpr (by simpa using ha)),
      ih, Finset.sum_insert ha]

private lemma empirical_le_card_div_of_no_repeat {α : Type*} (x : ℕ → α) (F : Finset α)
    (hno : ∀ i j, i < j → x i = x j → x i ∉ (F : Set α)) (n : ℕ) :
    OMA.S_mo_107177.empirical x (F : Set α) n ≤ (F.card : ℝ) / (n : ℝ) := by
  classical
  unfold OMA.S_mo_107177.empirical
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
  exact_mod_cast show (((Finset.range n).filter (fun k => x k ∈ (F : Set α))).card) ≤ F.card by
    set s := (Finset.range n).filter (fun k => x k ∈ (F : Set α))
    have hinj : Set.InjOn x (s : Set ℕ) := by
      intro i hi j hj hij
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · exact absurd (Finset.mem_filter.mp hi).2 (hno i j hlt hij)
      · rfl
      · exact absurd (Finset.mem_filter.mp hj).2 (hno j i hgt hij.symm)
    have hsub : s.image x ⊆ F := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨k, hk, rfl⟩
      exact Finset.mem_coe.mp (Finset.mem_filter.mp hk).2
    calc
      s.card = (s.image x).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ F.card := Finset.card_le_card hsub

private lemma empirical_eq_one_of_forall_mem {α : Type*} (x : ℕ → α) (A : Set α) {n : ℕ}
    (hn : 1 ≤ n) (hmem : ∀ k < n, x k ∈ A) :
    OMA.S_mo_107177.empirical x A n = 1 := by
  classical
  unfold OMA.S_mo_107177.empirical
  have hfilt : (Finset.range n).filter (fun k => x k ∈ A) = Finset.range n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
    exact hmem k
  rw [hfilt, Finset.card_range]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  exact div_self hn0

/-- The SLLN event for a single measurable set has full product measure. -/
private def sllnEvent (μ : Measure V) (A : Set V) : Set (ℕ → V) :=
  {x : ℕ → V | Tendsto (OMA.S_mo_107177.empirical x A) atTop (𝓝 (μ.real A))}

private lemma measurableSet_sllnEvent (μ : Measure V) {A : Set V} (hA : MeasurableSet A) :
    MeasurableSet (sllnEvent μ A) :=
  measurableSet_tendsto (𝓝 (μ.real A)) (measurable_empirical hA)

private lemma prob_sllnEvent (μ : Measure V) [IsProbabilityMeasure μ] {A : Set V}
    (hA : MeasurableSet A) :
    (Measure.infinitePi (fun _ : ℕ => μ)) (sllnEvent μ A) = 1 := by
  let P : Measure (ℕ → V) := Measure.infinitePi (fun _ : ℕ => μ)
  let f : V → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hA
  let X : ℕ → (ℕ → V) → ℝ := fun k x => f (x k)
  have hXmeas : ∀ k, Measurable (X k) := fun k => hf.comp (measurable_pi_apply k)
  have hint : Integrable (X 0) P := by
    refine Integrable.of_bound (hXmeas 0).aestronglyMeasurable 1 (ae_of_all P fun x => ?_)
    show ‖A.indicator (fun _ => (1 : ℝ)) (x 0)‖ ≤ 1
    by_cases hx : x 0 ∈ A <;> simp [hx]
  have hindep : Pairwise (Function.onFun (· ⟂ᵢ[P] ·) X) := by
    have hi : iIndepFun X P := iIndepFun_infinitePi (P := fun _ : ℕ => μ) (fun _ => hf)
    exact fun i j hij => hi.indepFun hij
  have hmap : ∀ k, P.map (X k) = μ.map f := fun k => by
    change P.map (f ∘ fun x : ℕ → V => x k) = μ.map f
    rw [← Measure.map_map hf (measurable_pi_apply k), Measure.infinitePi_map_eval]
  have hident : ∀ k, IdentDistrib (X k) (X 0) P P := fun k =>
    { aemeasurable_fst := (hXmeas k).aemeasurable
      aemeasurable_snd := (hXmeas 0).aemeasurable
      map_eq := by rw [hmap k, hmap 0] }
  have hmean : ∫ x, X 0 x ∂P = μ.real A := by
    change ∫ x, f (x 0) ∂P = μ.real A
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable,
      Measure.infinitePi_map_eval]
    change ∫ v, A.indicator (fun _ => (1 : ℝ)) v ∂μ = μ.real A
    rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
  have hae := ProbabilityTheory.strong_law_ae_real X hint hindep hident
  rw [hmean] at hae
  have hcompl : P (sllnEvent μ A)ᶜ = 0 := by
    have hEq : (sllnEvent μ A)ᶜ =
        {x : ℕ → V | ¬ Tendsto (fun n => (∑ k ∈ Finset.range n, X k x) / (n : ℝ))
          atTop (𝓝 (μ.real A))} := by
      ext x
      simp only [Set.mem_compl_iff, sllnEvent, Set.mem_ofPred_eq]
      refine not_congr (tendsto_congr fun n => ?_)
      exact empirical_eq_sum_indicator x A n
    rw [hEq]
    exact ae_iff.mp hae
  exact prob_eq_one_of_compl_eq_zero P (measurableSet_sllnEvent μ hA) hcompl

/-- The event that no non-atom of `μ` appears twice in the sample sequence. -/
private def noRepeatEvent (μ : Measure V) : Set (ℕ → V) :=
  ⋂ (i : ℕ) (j : ℕ) (_ : i < j), {x : ℕ → V | x i = x j → μ {x i} ≠ 0}

private lemma measurableSet_noRepeatEvent (μ : Measure V) [IsProbabilityMeasure μ] :
    MeasurableSet (noRepeatEvent μ) := by
  let S : Set V := {v : V | μ {v} ≠ 0}
  have hS : MeasurableSet S := (countable_atoms μ).measurableSet
  let D : Set (V × V) := Set.diagonal V ∩ (Sᶜ ×ˢ Set.univ)
  have hD : MeasurableSet D := isClosed_diagonal.measurableSet.inter (hS.compl.prod .univ)
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  have hEq : {x : ℕ → V | x i = x j → μ {x i} ≠ 0} =
      ((fun x : ℕ → V => (x i, x j)) ⁻¹' D)ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_preimage, D, Set.mem_inter_iff,
      Set.mem_diagonal_iff, Set.mem_prod, Set.mem_univ, and_true, S]
    tauto
  rw [hEq]
  exact (hD.preimage ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).compl

private lemma prob_noRepeatEvent (μ : Measure V) [IsProbabilityMeasure μ] :
    (Measure.infinitePi (fun _ : ℕ => μ)) (noRepeatEvent μ) = 1 := by
  let P : Measure (ℕ → V) := Measure.infinitePi (fun _ : ℕ => μ)
  let S : Set V := {v : V | μ {v} ≠ 0}
  have hS : MeasurableSet S := (countable_atoms μ).measurableSet
  let D : Set (V × V) := Set.diagonal V ∩ (Sᶜ ×ˢ Set.univ)
  have hD : MeasurableSet D := isClosed_diagonal.measurableSet.inter (hS.compl.prod .univ)
  have hprod0 : (μ.prod μ) D = 0 := by
    rw [Measure.prod_apply hD]
    have hslice : ∀ u : V, μ (Prod.mk u ⁻¹' D) = 0 := fun u => by
      by_cases hu : μ {u} = 0
      · have hsub : Prod.mk u ⁻¹' D ⊆ {u} := by
          intro v hv
          simp only [Set.mem_preimage, D, Set.mem_inter_iff, Set.mem_diagonal_iff] at hv
          exact hv.1.symm
        exact le_antisymm ((measure_mono hsub).trans_eq hu) zero_le
      · have hemp : Prod.mk u ⁻¹' D = ∅ := by
          ext v
          simp [D, S, hu]
        rw [hemp, measure_empty]
    simp [hslice]
  refine prob_eq_one_of_compl_eq_zero P (measurableSet_noRepeatEvent μ) ?_
  rw [noRepeatEvent, Set.compl_iInter]
  refine measure_iUnion_null fun i => ?_
  rw [Set.compl_iInter]
  refine measure_iUnion_null fun j => ?_
  rw [Set.compl_iInter]
  refine measure_iUnion_null fun hij => ?_
  have hEq : ({x : ℕ → V | x i = x j → μ {x i} ≠ 0})ᶜ =
      (fun x : ℕ → V => (x i, x j)) ⁻¹' D := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, D, Set.mem_inter_iff,
      Set.mem_diagonal_iff, Set.mem_prod, Set.mem_univ, and_true, S]
    tauto
  rw [hEq, ← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hD,
    Measure.infinitePi_map_eval_prod (ne_of_lt hij)]
  exact hprod0

private def tailSet (M : ℕ) : Set V :=
  {p : V | M ≤ p.1}

private lemma measurableSet_tailSet (M : ℕ) : MeasurableSet (tailSet M) :=
  measurable_fst measurableSet_Ici

private lemma tendsto_measureReal_tailSet (μ : Measure V) [IsProbabilityMeasure μ] :
    Tendsto (fun M : ℕ => μ.real (tailSet M)) atTop (𝓝 0) := by
  have hanti : Antitone tailSet := fun m n hmn p hp => le_trans hmn hp
  have hinter : ⋂ M : ℕ, tailSet M = ∅ := by
    ext ⟨k, r⟩
    simp only [Set.mem_iInter, tailSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_forall]
    exact ⟨k + 1, by omega⟩
  have hμ : Tendsto (fun M : ℕ => μ (tailSet M)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (fun M => (measurableSet_tailSet M).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
    rwa [hinter, measure_empty] at h
  simpa [Measure.real, Function.comp_def] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hμ

private lemma tendsto_empirical_of_finset (μ : Measure V) [IsProbabilityMeasure μ]
    {x : ℕ → V}
    (hatom : ∀ a : V, μ {a} ≠ 0 → x ∈ sllnEvent μ {a})
    (hno : x ∈ noRepeatEvent μ)
    (F : Finset V) :
    Tendsto (OMA.S_mo_107177.empirical x (F : Set V)) atTop (𝓝 (μ.real (F : Set V))) := by
  classical
  let Fatom : Finset V := F.filter (fun v => μ {v} ≠ 0)
  let Fnon : Finset V := F.filter (fun v => μ {v} = 0)
  have hdisj : Disjoint (Fatom : Set V) (Fnon : Set V) := by
    rw [Set.disjoint_left]
    intro v hv1 hv2
    simp only [Finset.mem_coe, Fatom, Fnon, Finset.mem_filter] at hv1 hv2
    exact hv1.2 hv2.2
  have hunion : (F : Set V) = (Fatom : Set V) ∪ (Fnon : Set V) := by
    ext v
    simp only [Finset.mem_coe, Set.mem_union, Fatom, Fnon, Finset.mem_filter]
    by_cases hv : μ {v} = 0 <;> tauto
  have hatom_lim :
      Tendsto (OMA.S_mo_107177.empirical x (Fatom : Set V)) atTop (𝓝 (μ.real (Fatom : Set V))) := by
    have h1 : OMA.S_mo_107177.empirical x (Fatom : Set V) =
        fun n => ∑ a ∈ Fatom, OMA.S_mo_107177.empirical x {a} n := by
      ext n
      exact empirical_finset_eq_sum x Fatom n
    rw [h1, measureReal_finset_eq_sum]
    refine tendsto_finsetSum Fatom fun a ha => ?_
    exact hatom a (Finset.mem_filter.mp ha).2
  have hnon_meas : μ.real (Fnon : Set V) = 0 := by
    rw [measureReal_finset_eq_sum]
    refine Finset.sum_eq_zero fun a ha => ?_
    have ha0 : μ {a} = 0 := (Finset.mem_filter.mp ha).2
    simp [Measure.real, ha0]
  have hnon_lim :
      Tendsto (OMA.S_mo_107177.empirical x (Fnon : Set V)) atTop (𝓝 (μ.real (Fnon : Set V))) := by
    rw [hnon_meas]
    have hupper : Tendsto (fun n : ℕ => (Fnon.card : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero (fun n => empirical_nonneg x _ n) (fun n => ?_) hupper
    refine empirical_le_card_div_of_no_repeat x Fnon (fun i j hij hEq hmem => ?_) n
    have hmem' := Finset.mem_filter.mp (Finset.mem_coe.mp hmem)
    have hne : μ {x i} ≠ 0 := by
      have h1 := Set.mem_iInter.mp hno i
      have h2 := Set.mem_iInter.mp h1 j
      have h3 := Set.mem_iInter.mp h2 hij
      exact h3 hEq
    exact hne hmem'.2
  have hEqFun : OMA.S_mo_107177.empirical x (F : Set V) =
      fun n => OMA.S_mo_107177.empirical x (Fatom : Set V) n +
        OMA.S_mo_107177.empirical x (Fnon : Set V) n := by
    ext n
    rw [hunion, empirical_union_disjoint x hdisj]
  rw [hEqFun, hunion, measureReal_union hdisj Fnon.finite_toSet.measurableSet]
  exact hatom_lim.add hnon_lim

private lemma simultaneousStrongLaw_C : OMA.S_mo_107177.simultaneousStrongLaw C := by
  intro μ hμ
  let P : Measure (ℕ → V) := Measure.infinitePi (fun _ : ℕ => μ)
  let S : Set V := {v : V | μ {v} ≠ 0}
  let E1 : Set (ℕ → V) := ⋂ a ∈ S, sllnEvent μ {a}
  let E2 : Set (ℕ → V) := noRepeatEvent μ
  let E3 : Set (ℕ → V) := ⋂ M : ℕ, sllnEvent μ (tailSet M)
  have hE1m : MeasurableSet E1 :=
    MeasurableSet.biInter (countable_atoms μ) fun a _ =>
      measurableSet_sllnEvent μ (measurableSet_singleton a)
  have hE2m : MeasurableSet E2 := measurableSet_noRepeatEvent μ
  have hE3m : MeasurableSet E3 :=
    MeasurableSet.iInter fun M => measurableSet_sllnEvent μ (measurableSet_tailSet M)
  have hE1p : P E1 = 1 := by
    refine prob_eq_one_of_compl_eq_zero P hE1m ?_
    have hc : E1ᶜ = ⋃ a ∈ S, (sllnEvent μ {a})ᶜ := by
      ext x
      simp [E1]
    rw [hc]
    exact (measure_biUnion_null_iff (countable_atoms μ)).mpr fun a _ =>
      prob_compl_eq_zero_of_eq_one P (measurableSet_sllnEvent μ (measurableSet_singleton a))
        (prob_sllnEvent μ (measurableSet_singleton a))
  have hE2p : P E2 = 1 := prob_noRepeatEvent μ
  have hE3p : P E3 = 1 := by
    refine prob_eq_one_of_compl_eq_zero P hE3m ?_
    rw [Set.compl_iInter]
    exact measure_iUnion_null fun M =>
      prob_compl_eq_zero_of_eq_one P (measurableSet_sllnEvent μ (measurableSet_tailSet M))
        (prob_sllnEvent μ (measurableSet_tailSet M))
  refine ⟨E1 ∩ E2 ∩ E3, (hE1m.inter hE2m).inter hE3m,
    prob_inter_eq_one P (hE1m.inter hE2m) hE3m (prob_inter_eq_one P hE1m hE2m hE1p hE2p) hE3p, ?_⟩
  rintro x ⟨⟨hx1, hx2⟩, hx3⟩ A hA
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail0 := Metric.tendsto_atTop.mp (tendsto_measureReal_tailSet μ) (ε / 4) (by linarith)
  obtain ⟨M, hM⟩ := htail0
  have hμtail : μ.real (tailSet M) < ε / 4 := by
    have h0 := hM M le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h0
    exact h0
  let Ahead : Set V := A \ tailSet M
  let Atail : Set V := A ∩ tailSet M
  have hAhead_fin : Ahead.Finite := by
    have hsub : Ahead ⊆ ⋃ k ∈ Finset.range M, (Prod.mk k) '' {r : ℝ | (k, r) ∈ A} := by
      intro ⟨k, r⟩ hkr
      simp only [Ahead, Set.mem_sdiff, tailSet, Set.mem_ofPred_eq, not_le] at hkr
      exact Set.mem_biUnion (Finset.mem_range.mpr hkr.2) ⟨r, hkr.1, rfl⟩
    exact (Set.Finite.biUnion (Finset.finite_toSet (Finset.range M)) fun k _ =>
      (hA k).image (Prod.mk k)).subset hsub
  let F : Finset V := hAhead_fin.toFinset
  have hFcoe : (F : Set V) = Ahead := Set.Finite.coe_toFinset hAhead_fin
  have hhatom : ∀ a : V, μ {a} ≠ 0 → x ∈ sllnEvent μ {a} := fun a ha => by
    have h := Set.mem_iInter.mp hx1 a
    exact Set.mem_iInter.mp h ha
  have hhead_lim : Tendsto (OMA.S_mo_107177.empirical x Ahead) atTop (𝓝 (μ.real Ahead)) := by
    rw [← hFcoe]
    exact tendsto_empirical_of_finset μ hhatom hx2 F
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hhead_lim (ε / 4) (by linarith)
  have htail_lim : Tendsto (OMA.S_mo_107177.empirical x (tailSet M)) atTop
      (𝓝 (μ.real (tailSet M))) := Set.mem_iInter.mp hx3 M
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp htail_lim (ε / 4) (by linarith)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hdisj : Disjoint Ahead Atail := Set.disjoint_left.mpr fun _ hp1 hp2 => hp1.2 hp2.2
  have hunion : A = Ahead ∪ Atail := (Set.sdiff_union_inter A (tailSet M)).symm
  have hAtail_meas : MeasurableSet Atail :=
    (measurableSet_of_mem_C hA).inter (measurableSet_tailSet M)
  have hemp_add : OMA.S_mo_107177.empirical x A n =
      OMA.S_mo_107177.empirical x Ahead n + OMA.S_mo_107177.empirical x Atail n := by
    conv_lhs => rw [hunion]
    exact empirical_union_disjoint x hdisj n
  have hμ_add : μ.real A = μ.real Ahead + μ.real Atail := by
    conv_lhs => rw [hunion]
    exact measureReal_union hdisj hAtail_meas
  have h1 : |OMA.S_mo_107177.empirical x Ahead n - μ.real Ahead| < ε / 4 := by
    simpa [Real.dist_eq] using hN1 n (le_trans (le_max_left _ _) hn)
  have h2 : |OMA.S_mo_107177.empirical x (tailSet M) n - μ.real (tailSet M)| < ε / 4 := by
    simpa [Real.dist_eq] using hN2 n (le_trans (le_max_right _ _) hn)
  have h2' : OMA.S_mo_107177.empirical x (tailSet M) n < ε / 2 := by
    have := (abs_lt.mp h2).2
    linarith
  have h3 : OMA.S_mo_107177.empirical x Atail n ≤ OMA.S_mo_107177.empirical x (tailSet M) n :=
    empirical_mono x Set.inter_subset_right n
  have h3' : 0 ≤ OMA.S_mo_107177.empirical x Atail n := empirical_nonneg x Atail n
  have h4 : μ.real Atail ≤ μ.real (tailSet M) := measureReal_mono Set.inter_subset_right
  have h4' : 0 ≤ μ.real Atail := measureReal_nonneg
  rw [Real.dist_eq, hemp_add, hμ_add]
  have h1' := abs_lt.mp h1
  rw [abs_lt]
  constructor <;> linarith

/-- Atomless probability measure supported on slice `{j} × [0, 1]`. -/
private noncomputable def sliceMeasure (j : ℕ) : Measure V :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).map (Prod.mk j)

private lemma isProbabilityMeasure_unitIcc :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

private lemma isProbabilityMeasure_sliceMeasure (j : ℕ) :
    IsProbabilityMeasure (sliceMeasure j) := by
  have := isProbabilityMeasure_unitIcc
  exact Measure.isProbabilityMeasure_map measurable_prodMk_left.aemeasurable

private lemma sliceMeasure_slice_eq_one (j : ℕ) :
    sliceMeasure j {p : V | p.1 = j} = 1 := by
  have := isProbabilityMeasure_unitIcc
  have hmeas : MeasurableSet {p : V | p.1 = j} := measurable_fst (measurableSet_singleton j)
  rw [sliceMeasure, Measure.map_apply measurable_prodMk_left hmeas]
  have hpre : Prod.mk j ⁻¹' {p : V | p.1 = j} = Set.univ := by
    ext r
    simp
  rw [hpre, measure_univ]

private lemma sliceMeasure_real_eq_zero_of_finite_slice (j : ℕ) {A : Set V}
    (hA : MeasurableSet A) (hfin : {r : ℝ | (j, r) ∈ A}.Finite) :
    (sliceMeasure j).real A = 0 := by
  have h0 : sliceMeasure j A = 0 := by
    rw [sliceMeasure, Measure.map_apply measurable_prodMk_left hA]
    refine le_antisymm ?_ zero_le
    calc
      (volume.restrict (Set.Icc (0 : ℝ) 1)) (Prod.mk j ⁻¹' A)
          ≤ volume (Prod.mk j ⁻¹' A) := Measure.restrict_le_self _
      _ = 0 := hfin.countable.measure_zero volume
  simp [Measure.real, h0]

private lemma exists_bad_sample (j : ℕ) {G : Set (Set V)}
    (hG : OMA.S_mo_107177.universallyGlivenkoCantelli G) :
    ∃ (x : ℕ → V) (n : ℕ), 1 ≤ n ∧ (∀ k : ℕ, (x k).1 = j) ∧
      ∀ A ∈ G, |OMA.S_mo_107177.empirical x A n - (sliceMeasure j).real A| < 1 / 2 := by
  have : IsProbabilityMeasure (sliceMeasure j) := isProbabilityMeasure_sliceMeasure j
  let P : Measure (ℕ → V) := Measure.infinitePi (fun _ : ℕ => sliceMeasure j)
  obtain ⟨E, hEm, hEp, hEprop⟩ := hG (sliceMeasure j) inferInstance
  let Slice : Set V := {p : V | p.1 = j}
  have hSlicem : MeasurableSet Slice := measurable_fst (measurableSet_singleton j)
  let Ωj : Set (ℕ → V) := ⋂ k : ℕ, (fun x : ℕ → V => x k) ⁻¹' Slice
  have hΩm : MeasurableSet Ωj :=
    MeasurableSet.iInter fun k => hSlicem.preimage (measurable_pi_apply k)
  have hΩp : P Ωj = 1 := by
    refine prob_eq_one_of_compl_eq_zero P hΩm ?_
    rw [Set.compl_iInter]
    refine measure_iUnion_null fun k => ?_
    have hpre : ((fun x : ℕ → V => x k) ⁻¹' Slice)ᶜ = (fun x : ℕ → V => x k) ⁻¹' Sliceᶜ := rfl
    rw [hpre, ← Measure.map_apply (measurable_pi_apply k) hSlicem.compl,
      Measure.infinitePi_map_eval]
    exact prob_compl_eq_zero_of_eq_one (sliceMeasure j) hSlicem (sliceMeasure_slice_eq_one j)
  have hInter : P (E ∩ Ωj) = 1 := prob_inter_eq_one P hEm hΩm hEp hΩp
  have hne : (E ∩ Ωj).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty.mp hemp, measure_empty] at hInter
    exact zero_ne_one hInter
  obtain ⟨x, hxE, hxΩ⟩ := hne
  obtain ⟨N, hN⟩ := hEprop x hxE (1 / 2) (by norm_num)
  refine ⟨x, max N 1, le_max_right N 1, fun k => ?_, fun A hA => hN (max N 1) (le_max_left N 1) A hA⟩
  exact Set.mem_iInter.mp hxΩ k

private lemma not_countable_union_uGC :
    ¬ ∃ G : ℕ → Set (Set V), C = (⋃ j, G j) ∧
      ∀ j, OMA.S_mo_107177.universallyGlivenkoCantelli (G j) := by
  rintro ⟨G, hC, hG⟩
  choose x n hn hx hbound using fun j => exists_bad_sample j (hG j)
  let F : ℕ → Finset ℝ := fun j => (Finset.range (n j)).image (fun k => (x j k).2)
  let Astar : Set V := {p : V | p.2 ∈ F p.1}
  have hAstar_mem : Astar ∈ C := by
    intro k
    have hEq : {r : ℝ | (k, r) ∈ Astar} = (F k : Set ℝ) := by
      ext r
      simp [Astar]
    rw [hEq]
    exact (F k).finite_toSet
  have hAstar_union : Astar ∈ ⋃ j, G j := by rwa [← hC]
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hAstar_union
  have hμ0 : (sliceMeasure j).real Astar = 0 :=
    sliceMeasure_real_eq_zero_of_finite_slice j (measurableSet_of_mem_C hAstar_mem) (hAstar_mem j)
  have hemp1 : OMA.S_mo_107177.empirical (x j) Astar (n j) = 1 := by
    refine empirical_eq_one_of_forall_mem (x j) Astar (hn j) fun k hk => ?_
    show (x j k).2 ∈ F (x j k).1
    rw [hx j k]
    exact Finset.mem_image_of_mem (fun k => (x j k).2) (Finset.mem_range.mpr hk)
  have hlt := hbound j Astar hj
  rw [hemp1, hμ0] at hlt
  norm_num at hlt

end OMA_mo_107177_Aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_107177.main) := by
  intro hmain
  have h := hmain OMA_mo_107177_Aux.V OMA_mo_107177_Aux.C
    (fun _ hA => OMA_mo_107177_Aux.measurableSet_of_mem_C hA)
    OMA_mo_107177_Aux.simultaneousStrongLaw_C
  exact OMA_mo_107177_Aux.not_countable_union_uGC h
