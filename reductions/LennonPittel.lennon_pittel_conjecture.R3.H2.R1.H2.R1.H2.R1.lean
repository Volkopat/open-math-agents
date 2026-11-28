import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1
import Mathlib

/-! Port of part of the Lennon-Pittel lower-tail proof by Bo Cowgill,
https://github.com/bocowgill/lennon-pittel at commit cf950d0596591bba912b1568aa394f99986f8191,
Copyright 2026 Bo Cowgill, used under the Apache License 2.0.
Changes: modules flattened into one file, comments removed, declarations not needed here dropped,
names adapted to the pinned Mathlib, the marked model renamed and tied to the parent reduction's
definitions (after moon-4's port of the same model for the parent step).
This reduction proves the diagonal and incomparable mean-product estimate from two first-moment
bounds of the source, kept as hypotheses H1 and H2. -/


-- StandardExponentialScoreLaw
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DiagLP
end DiagLP
end

-- BoundedProductChernoff
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
end DiagLP
end

-- IidScoreRanks
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DiagLP
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
theorem ae_injective_iid (n : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ μ), Function.Injective (x : Fin n → ℝ) := by
  let law : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ μ
  have hind : iIndepFun (fun i (x : Fin n → ℝ) ↦ x i) law :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  refine ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ ?_
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ ↦ hij
  have hi := (measurable_pi_apply i : Measurable (fun x : Fin n → ℝ ↦ x i))
  have hj := (measurable_pi_apply j : Measurable (fun x : Fin n → ℝ ↦ x j))
  
  have hpair : law.map (fun x ↦ (x i, x j)) = μ.prod μ :=
    ((indepFun_iff_map_prod_eq_prod_map_map hi.aemeasurable hj.aemeasurable).1
      (hind.indepFun hij)).trans
        (congrArg₂ Measure.prod (measurePreserving_eval (fun _ : Fin n ↦ μ) i).map_eq
          (measurePreserving_eval (fun _ : Fin n ↦ μ) j).map_eq)
  let diagonal : Set (ℝ × ℝ) := {z | z.1 = z.2}
  have hd : MeasurableSet diagonal := measurableSet_eq_fun measurable_fst measurable_snd
  have hnull : (μ.prod μ) diagonal = 0 := by
    rw [Measure.prod_apply hd]
    have hsection (u : ℝ) : Prod.mk u ⁻¹' diagonal = {u} :=
      Set.ext fun _ ↦ eq_comm
    simp [hsection]
  have hpull : law {x | x i = x j} = 0 := by
    rw [← hpair, Measure.map_apply (hi.prodMk hj) hd] at hnull
    exact hnull
  exact ae_iff.2 (by simpa [hij] using hpull)
private theorem perm_eq_of_lt_iff {n : ℕ} {p q : Equiv.Perm (Fin n)}
    (h : ∀ i j, p i < p j ↔ q i < q j) : p = q := by
  let f := fun i ↦ q (p.symm i)
  have hf : StrictMono f := fun i j hij ↦ (h (p.symm i) (p.symm j)).1
    (by simpa using hij)
  exact Equiv.ext fun i ↦ by
    simpa [f] using (hf.id_le (p i)).antisymm (hf.le_id (p i))
theorem measurePreserving_rank_of_iid {n : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    {r : (Fin n → ℝ) → Equiv.Perm (Fin n)} (hr : Measurable r)
    (hcmp : ∀ x, Function.Injective x → ∀ i j, r x i < r x j ↔ x i < x j) :
    MeasurePreserving r (Measure.pi fun _ : Fin n ↦ μ)
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure := by
  let law : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ μ
  let ν : Measure (Equiv.Perm (Fin n)) := law.map r
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hr.aemeasurable
  
  have hequal (p q : Equiv.Perm (Fin n)) : ν {p} = ν {q} := by
    let e : Equiv.Perm (Fin n) := q.trans p.symm
    let reindex := MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e.symm
    have hm : MeasurePreserving reindex law law :=
      measurePreserving_piCongrLeft (fun _ : Fin n ↦ μ) e.symm
    have he (x : Fin n → ℝ) (i : Fin n) : reindex x i = x (e i) := by
      simp [reindex, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    have hcongr : r ⁻¹' ({p} : Set (Equiv.Perm (Fin n))) =ᶠ[ae law] reindex ⁻¹' (r ⁻¹' {q}) :=
      (ae_injective_iid μ n).mono fun x hx ↦ by
        have hre : r (reindex x) = e.trans (r x) := perm_eq_of_lt_iff fun i j ↦
          (hcmp (reindex x) (by
            simpa only [Function.Injective, Function.comp_apply, he] using hx.comp e.injective) i j).trans
            (by simpa only [he, Equiv.trans_apply] using (hcmp x hx (e i) (e j)).symm)
        apply propext
        change (r x = p) ↔ r (reindex x) = q
        rw [hre]
        constructor
        · rintro rfl
          simp [e, Equiv.trans_assoc]
        · intro h
          apply Equiv.ext
          intro i
          have hi := DFunLike.congr_fun h (e.symm i)
          simpa [e] using hi
    change law.map r {p} = law.map r {q}
    rw [Measure.map_apply hr (measurableSet_singleton p),
      Measure.map_apply hr (measurableSet_singleton q)]
    exact (measure_congr hcongr).trans
      (hm.measure_preimage (hr (measurableSet_singleton q)).nullMeasurableSet)
  refine ⟨hr, Measure.ext_of_singleton fun p ↦ ?_⟩
  
  have hsum : ν {p} * (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) = 1 := by
    calc
      _ = ∑' q : Equiv.Perm (Fin n), ν {q} := by
        rw [tsum_fintype, Finset.sum_congr rfl (fun q _ ↦ hequal q p), Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_comm]
      _ = 1 := by simpa only [Measure.toPMF_apply] using ν.toPMF.tsum_coe
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), PMF.uniformOfFintype_apply]
  exact ENNReal.eq_inv_of_mul_eq_one_left hsum
end DiagLP
end

-- MarkedCounting
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype A] [Nonempty A]
private noncomputable def uniformMarkLaw (A : Type*) [MeasurableSpace A] [Fintype A] [Nonempty A] :
    Measure A :=
  (PMF.uniformOfFintype A).toMeasure
private instance uniformMarkLaw_isProbabilityMeasure : IsProbabilityMeasure (uniformMarkLaw A) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype A).toMeasure)
private noncomputable def markedLaw (P : Measure Ω) (E : Set (Ω × A)) : Measure (Ω × A) :=
  ProbabilityTheory.cond (P.prod (uniformMarkLaw A)) E
private noncomputable def markedNormalizer (P : Measure Ω) (E : Set (Ω × A)) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ a, E.indicator 1 (ω, a) ∂P
variable [MeasurableSingletonClass A]
private theorem lintegral_restrict_uniformMarkLaw (P : Measure Ω)
    {E : Set (Ω × A)} (hE : MeasurableSet E) {f : Ω × A → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in E, f z ∂P.prod (uniformMarkLaw A)) =
      (Fintype.card A : ℝ≥0∞)⁻¹ * (∫⁻ ω, ∑ a, E.indicator f (ω, a) ∂P) := by
  rw [← lintegral_indicator hE, lintegral_prod _ (hf.indicator hE).aemeasurable]
  simp only [lintegral_fintype, uniformMarkLaw, PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton _), PMF.uniformOfFintype_apply, ← Finset.sum_mul]
  rw [lintegral_mul_const' _ _ (by simp [Fintype.card_ne_zero]), mul_comm]
theorem uniform_mark_event_mass (P : Measure Ω) {E : Set (Ω × A)} (hE : MeasurableSet E) :
    (P.prod (uniformMarkLaw A)) E = (Fintype.card A : ℝ≥0∞)⁻¹ * markedNormalizer P E := by
  simpa [markedNormalizer] using
    lintegral_restrict_uniformMarkLaw P hE (f := 1) measurable_const
theorem marked_counting_identity (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hE : MeasurableSet E)
    (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0)
    {f : Ω × A → ℝ≥0∞} (hf : Measurable f) :
    markedNormalizer P E * (∫⁻ z, f z ∂markedLaw P E) =
      ∫⁻ ω, ∑ a, E.indicator f (ω, a) ∂P := by
  have hscaled : (Fintype.card A : ℝ≥0∞) * (P.prod (uniformMarkLaw A)) E =
      markedNormalizer P E := by
    rw [uniform_mark_event_mass P hE, ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]
  rw [← hscaled, markedLaw, ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul,
    lintegral_restrict_uniformMarkLaw P hE hf]
  rw [mul_assoc, ← mul_assoc ((P.prod (uniformMarkLaw A)) E),
    ENNReal.mul_inv_cancel hpos (measure_lt_top _ _).ne, one_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]
section StableMarriage
open StableMarriage
scoped instance matchingMeasurableSpace (n : ℕ) : MeasurableSpace (Matching n) := ⊤
scoped instance matchingDiscreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (Matching n) :=
  ⟨fun _ ↦ trivial⟩
scoped instance profileDiscreteMeasurableSpace (n : ℕ) : DiscreteMeasurableSpace (Profile n) :=
  ⟨fun _ ↦ trivial⟩
end StableMarriage
end DiagLP
end

-- ScoreRanks
section
open Function MeasureTheory Set
namespace DiagLP
private noncomputable def scoreImage {n : ℕ} (x : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image x
private theorem card_scoreImage {n : ℕ} {x : Fin n → ℝ} (hx : Injective x) :
    (scoreImage x).card = n := by
  rw [scoreImage, Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
private noncomputable def scoreEquiv {n : ℕ} (x : Fin n → ℝ) (hx : Injective x) :
    Fin n ≃ (scoreImage x : Set ℝ) :=
  Equiv.ofBijective (fun i ↦ ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩)
    ⟨fun _ _ h ↦ hx (congrArg Subtype.val h), fun y ↦
      let ⟨i, _, hi⟩ := Finset.mem_image.mp (show y.val ∈ Finset.univ.image x from y.property)
      ⟨i, Subtype.ext hi⟩⟩
private noncomputable def rankPermutation {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) := by
  classical
  exact if h : Injective x then
    (scoreEquiv x h).trans ((scoreImage x).orderIsoOfFin (card_scoreImage h)).symm.toEquiv
  else Equiv.refl _
theorem rankPermutation_lt_iff {n : ℕ} {x : Fin n → ℝ} (hx : Injective x) (i j : Fin n) :
    rankPermutation x i < rankPermutation x j ↔ x i < x j := by
  classical
  unfold rankPermutation
  rw [dif_pos hx]
  exact ((scoreImage x).orderIsoOfFin (card_scoreImage hx)).symm.lt_iff_lt
    (x := scoreEquiv x hx i) (y := scoreEquiv x hx j)
private def rankChamber {n : ℕ} (p : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {x | ∀ i j, p i < p j → x i < x j}
private theorem measurableSet_rankChamber {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurableSet (rankChamber p) := by
  unfold rankChamber
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j ↦ ?_
  by_cases h : p i < p j
  · simpa only [h, true_implies] using
      (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j) :
        MeasurableSet {x : Fin n → ℝ | x i < x j})
  · simp [h]
private theorem measurableSet_injective_row (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | Injective x} := by
  unfold Injective
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j ↦ ?_
  by_cases h : i = j
  · simp [h]
  · exact ((measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j) :
      MeasurableSet {x : Fin n → ℝ | x i = x j}).compl).congr (by ext x; simp [h])
private theorem rankPermutation_eq_iff {n : ℕ} {x : Fin n → ℝ} (hx : Injective x)
    (p : Equiv.Perm (Fin n)) : rankPermutation x = p ↔ x ∈ rankChamber p := by
  constructor
  · rintro rfl i j hij
    exact (rankPermutation_lt_iff hx i j).mp hij
  · intro hp
    have hmono : StrictMono (rankPermutation x ∘ p.symm) := fun i j hij ↦
      (rankPermutation_lt_iff hx (p.symm i) (p.symm j)).mpr <|
        hp (p.symm i) (p.symm j) (by simpa using hij)
    apply Equiv.ext
    intro i
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, id_eq] using
      le_antisymm (hmono.le_id (p i)) (hmono.id_le (p i))
theorem measurable_rankPermutation (n : ℕ) :
    @Measurable (Fin n → ℝ) (Equiv.Perm (Fin n)) inferInstance ⊤ rankPermutation := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  apply measurable_to_countable'
  intro p
  have hpre : rankPermutation ⁻¹' {p} =
      ({x : Fin n → ℝ | Injective x} ∩ rankChamber p) ∪
        ({x : Fin n → ℝ | Injective x}ᶜ ∩ {x : Fin n → ℝ | Equiv.refl (Fin n) = p}) := by
    ext x
    by_cases hx : Injective x
    · simpa only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
        mem_compl_iff, hx, not_true_eq_false, true_and, false_and, or_false] using
          rankPermutation_eq_iff hx p
    · simp [rankPermutation, hx]
  rw [hpre]
  exact ((measurableSet_injective_row n).inter (measurableSet_rankChamber p)).union
    ((measurableSet_injective_row n).compl.inter (MeasurableSet.const _))
private abbrev ScoreProfile (n : ℕ) := (Fin n ⊕ Fin n) → Fin n → ℝ
private noncomputable def profileOfScores {n : ℕ} (x : ScoreProfile n) : StableMarriage.Profile n :=
  ⟨fun m ↦ rankPermutation (x (.inl m)), fun w ↦ rankPermutation (x (.inr w))⟩
theorem measurable_profileOfScores (n : ℕ) : Measurable (@profileOfScores n) := by
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  let : DiscreteMeasurableSpace (Equiv.Perm (Fin n)) :=
    ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hrow (r : Fin n ⊕ Fin n) (p : Equiv.Perm (Fin n)) :
      MeasurableSet {x : ScoreProfile n | rankPermutation (x r) = p} :=
    ((measurable_rankPermutation n).comp (measurable_pi_apply r)) (measurableSet_singleton p)
  apply measurable_to_countable'
  rintro ⟨men, women⟩
  change MeasurableSet {x | profileOfScores x = ⟨men, women⟩}
  simp only [profileOfScores, StableMarriage.Profile.mk.injEq, funext_iff, Set.ofPred_and,
    Set.ofPred_forall]
  exact (MeasurableSet.iInter fun m ↦ hrow (.inl m) (men m)).inter
    (MeasurableSet.iInter fun w ↦ hrow (.inr w) (women w))
private def IsScoreBlockingPair {n : ℕ} (x : ScoreProfile n) (μ : StableMarriage.Matching n)
    (m w : Fin n) : Prop :=
  μ m ≠ w ∧ x (.inl m) w < x (.inl m) (μ m) ∧ x (.inr w) m < x (.inr w) (μ.symm w)
private def IsScoreStable {n : ℕ} (x : ScoreProfile n) (μ : StableMarriage.Matching n) : Prop :=
  ∀ m w, ¬ IsScoreBlockingPair x μ m w
theorem isBlockingPair_profileOfScores_iff {n : ℕ} {x : ScoreProfile n}
    (hx : ∀ r, Injective (x r)) (μ : StableMarriage.Matching n) (m w : Fin n) :
    StableMarriage.IsBlockingPair (profileOfScores x) μ m w ↔ IsScoreBlockingPair x μ m w := by
  simp only [StableMarriage.IsBlockingPair, profileOfScores, IsScoreBlockingPair,
    rankPermutation_lt_iff (hx (.inl m)), rankPermutation_lt_iff (hx (.inr w))]
theorem isStable_profileOfScores_iff {n : ℕ} {x : ScoreProfile n}
    (hx : ∀ r, Injective (x r)) (μ : StableMarriage.Matching n) :
    StableMarriage.IsStable (profileOfScores x) μ ↔ IsScoreStable x μ := by
  simp only [StableMarriage.IsStable, IsScoreStable, isBlockingPair_profileOfScores_iff hx]
theorem measurableSet_isScoreStable {n : ℕ} (μ : StableMarriage.Matching n) :
    MeasurableSet {x : ScoreProfile n | IsScoreStable x μ} := by
  have hcell (r : Fin n ⊕ Fin n) (a : Fin n) : Measurable (fun x : ScoreProfile n ↦ x r a) :=
    (measurable_pi_apply a).comp (measurable_pi_apply r)
  unfold IsScoreStable
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun m ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun w ↦ ?_
  by_cases h : μ m = w
  · simp [IsScoreBlockingPair, h]
  · exact ((measurableSet_lt (hcell (.inl m) w) (hcell (.inl m) (μ m))).inter
      (measurableSet_lt (hcell (.inr w) m) (hcell (.inr w) (μ.symm w)))).compl.congr
        (Set.ext fun x ↦ by simp [IsScoreBlockingPair, h])
end DiagLP
end

-- ContinuousScoreBridge
section
open scoped BigOperators ENNReal DiagLP
open MeasureTheory Set
namespace DiagLP
private noncomputable def unitScoreLaw : Measure ℝ :=
  volume.restrict (Icc 0 1)
private instance : IsProbabilityMeasure unitScoreLaw :=
  ⟨by simp [unitScoreLaw, Real.volume_Icc]⟩
private instance : NullSingletonClass unitScoreLaw :=
  Measure.restrict.instNullSingletonClass _
private noncomputable def rankRowsEquiv (n : ℕ) :
    ((Fin n ⊕ Fin n) → Equiv.Perm (Fin n)) ≃ StableMarriage.Profile n where
  toFun p := ⟨p ∘ Sum.inl, p ∘ Sum.inr⟩
  invFun p := Sum.elim p.manRank p.womanRank
  left_inv _ := funext fun i ↦ Sum.rec (fun _ ↦ rfl) (fun _ ↦ rfl) i
  right_inv := fun ⟨_, _⟩ ↦ rfl
private theorem measurePreserving_rankRowsEquiv (n : ℕ) :
    MeasurePreserving (rankRowsEquiv n)
      (Measure.pi fun _ : Fin n ⊕ Fin n ↦
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
      (StableMarriage.uniformProfile n).toMeasure := by
  refine ⟨measurable_of_countable _, Measure.ext_of_singleton fun p ↦ ?_⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton p)]
  rw [show (rankRowsEquiv n) ⁻¹' {p} = {(rankRowsEquiv n).symm p} by
    ext x
    simp [← Equiv.eq_symm_apply]]
  rw [StableMarriage.uniformProfile, PMF.toMeasure_apply_singleton _ p (measurableSet_singleton _)]
  simp [← Fintype.card_congr (rankRowsEquiv n), ENNReal.inv_pow]
private noncomputable def continuousScoreLaw (n : ℕ) : Measure (ScoreProfile n) :=
  Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw
private instance (n : ℕ) : IsProbabilityMeasure (continuousScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n ⊕ Fin n ↦
    Measure.pi fun _ : Fin n ↦ unitScoreLaw))
theorem ae_injective_rows (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r, Function.Injective (x r) :=
  ae_all_iff.2 fun _ ↦ Measure.tendsto_eval_ae_ae.eventually (ae_injective_iid unitScoreLaw n)
theorem measurePreserving_profileOfScores (n : ℕ) :
    MeasurePreserving (@profileOfScores n) (continuousScoreLaw n)
      (StableMarriage.uniformProfile n).toMeasure :=
  (measurePreserving_rankRowsEquiv n).comp
    (measurePreserving_pi _ _ fun _ ↦
      measurePreserving_rank_of_iid unitScoreLaw (measurable_rankPermutation n)
        (fun _ hx ↦ rankPermutation_lt_iff hx))
end DiagLP
end

-- CoexposureGoodScores
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal DiagLP
namespace DiagLP
variable {n : ℕ}
private def maleSpouseScore (x : ScoreProfile n) (μ : Matching n) (i : Fin n) : ℝ :=
  x (.inl i) (μ i)
private def femaleSpouseScore (x : ScoreProfile n) (μ : Matching n) (j : Fin n) : ℝ :=
  x (.inr j) (μ.symm j)
private def femaleSpouseTotal (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ j, femaleSpouseScore x μ j
private def GoodSpouseScores (x : ScoreProfile n) (μ : Matching n) : Prop :=
  2 ≤ femaleSpouseTotal x μ ∧
    (∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤ 12 * Real.log n / n) ∧
    (∀ i, maleSpouseScore x μ i ≤ 8 * Real.log n / (femaleSpouseTotal x μ - 1))
private theorem measurable_scoreCoordinate (r : Fin n ⊕ Fin n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ x r i) :=
  (measurable_pi_apply i).comp (measurable_pi_apply r)
theorem measurable_maleSpouseScore (μ : Matching n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ maleSpouseScore x μ i) :=
  measurable_scoreCoordinate (.inl i) (μ i)
theorem ae_unitOpen_scores (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r i, x r i ∈ Ioo (0 : ℝ) 1 := by
  have hopen : ∀ᵐ t ∂unitScoreLaw, t ∈ Ioo (0 : ℝ) 1 := by
    rw [unitScoreLaw, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  exact ae_all_iff.2 fun r ↦ ae_all_iff.2 fun i ↦
    (Measure.tendsto_eval_ae_ae (i := r)
      (μ := fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)).eventually
      ((Measure.tendsto_eval_ae_ae (i := i) (μ := fun _ : Fin n ↦ unitScoreLaw)).eventually hopen)
end DiagLP
end

-- CoexposureScoreEstimates
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace DiagLP
private def scoreSimplex (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s}
end DiagLP
end

-- PittelSimplexRadial
section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DiagLP
private noncomputable def spouseAngle {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i / (∑ j, x j)
private noncomputable def spouseAngularLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (n.factorial : ℝ≥0∞) • Measure.map spouseAngle (volume.restrict (scoreSimplex n 1))
end DiagLP
end

-- PittelSimplexMoments
section
open Filter MeasureTheory Set
open scoped ENNReal BigOperators Topology
namespace DiagLP
private noncomputable def pittelAngularSquareScore {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (n : ℝ) * ∑ i, w i ^ 2
section Moments
variable {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
variable (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)
variable (hmoment : ∀ a : Fin n → ℕ, (∫ w, ∏ i, w i ^ a i ∂μ) =
  (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
    ((n - 1 + ∑ i, a i).factorial : ℝ))
end Moments
end DiagLP
end

-- ExponentialSpouseSquareTail
section
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace DiagLP
local instance : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)
end DiagLP
end

-- ExponentialSpouseAngles
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace DiagLP
end DiagLP
end

-- CoexposureScoreRow
section
open Set
open scoped BigOperators
namespace DiagLP
variable {ι : Type*}
private noncomputable def scoreRowKernel (J : Finset ι) (y : ι → ℝ) (x : ℝ) : ℝ :=
  ∏ j ∈ J, (1 - x * y j)
private noncomputable def scoreRowMass (J : Finset ι) (y : ι → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, scoreRowKernel J y x
theorem continuous_scoreRowKernel (J : Finset ι) (y : ι → ℝ) :
    Continuous (scoreRowKernel J y) := by
  unfold scoreRowKernel
  fun_prop
private theorem scoreRowKernel_nonneg {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ scoreRowKernel J y x := by
  unfold scoreRowKernel
  exact Finset.prod_nonneg fun j hj ↦ sub_nonneg.mpr (calc
    x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy₀ j hj)
    _ ≤ 1 := by simpa using hy₁ j hj)
theorem scoreRowKernel_le_exp {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    scoreRowKernel J y x ≤ Real.exp (-(∑ j ∈ J, y j) * x) := by
  unfold scoreRowKernel
  rw [show -(∑ j ∈ J, y j) * x = ∑ j ∈ J, -(x * y j) by
    calc
      -(∑ j ∈ J, y j) * x = -(x * ∑ j ∈ J, y j) := by ring
      _ = _ := by rw [Finset.mul_sum, Finset.sum_neg_distrib], Real.exp_sum]
  exact Finset.prod_le_prod
    (fun j hj ↦ sub_nonneg.mpr (calc
      x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy₀ j hj)
      _ ≤ 1 := by simpa using hy₁ j hj))
    (fun j _ ↦ Real.one_sub_le_exp_neg _)
private theorem integral_exp_neg_mul {r a b : ℝ} (hr : 0 < r) :
    (∫ x in a..b, Real.exp (-r * x)) = (Real.exp (-r * a) - Real.exp (-r * b)) / r := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun z ↦ -(Real.exp (-r * z)) / r) (Real.exp (-r * x)) x := by
    exact (((Real.hasDerivAt_exp (-r * x)).comp x
      (hasDerivAt_const_mul (-r))).neg.div_const r).congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring
theorem scoreRowMass_le_exp_tail {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {r a b : ℝ} (hr : 0 < r) (hrsum : r ≤ ∑ j ∈ J, y j)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    scoreRowMass J y a b ≤ Real.exp (-r * a) / r := by
  calc
    scoreRowMass J y a b ≤ ∫ x in a..b, Real.exp (-r * x) := by
      unfold scoreRowMass
      refine intervalIntegral.integral_mono_on hab
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx ↦ ?_
      have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hx.1, hx.2.trans hb⟩
      exact (scoreRowKernel_le_exp hy₀ hy₁ hx').trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg hrsum) hx'.1))
    _ = (Real.exp (-r * a) - Real.exp (-r * b)) / r := integral_exp_neg_mul hr
    _ ≤ Real.exp (-r * a) / r :=
      div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hr.le
section FiniteRows
variable [Fintype ι] [DecidableEq ι]
end FiniteRows
section SuccessorMass
open MeasureTheory
open scoped ENNReal
private noncomputable def rowNonblockingLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  (unitScoreLaw.prod unitScoreLaw).restrict (Iio x ×ˢ Iio y)ᶜ
private instance (x y : ℝ) : IsFiniteMeasure (rowNonblockingLaw x y) := by
  unfold rowNonblockingLaw
  infer_instance
theorem unitScoreLaw_apply_Iio {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    unitScoreLaw (Iio a) = ENNReal.ofReal a := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iio]
  have heq : Iio a ∩ Icc (0 : ℝ) 1 = Ico 0 a := by
    ext t
    change (t < a ∧ 0 ≤ t ∧ t ≤ 1) ↔ (0 ≤ t ∧ t < a)
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.le.trans ha.2⟩⟩
  rw [heq, Real.volume_Ico, sub_zero]
theorem rowNonblockingLaw_apply_avoiding {x a y : ℝ} (hxa : x ≤ a)
    (ha : a ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    rowNonblockingLaw x y (Iio a ×ˢ Iio y)ᶜ = ENNReal.ofReal (1 - a * y) := by
  have hs : MeasurableSet (Iio a ×ˢ Iio y) := measurableSet_Iio.prod measurableSet_Iio
  have hsub : (Iio x ×ˢ Iio y : Set (ℝ × ℝ)) ⊆ Iio a ×ˢ Iio y :=
    fun _ h ↦ ⟨h.1.trans_le hxa, h.2⟩
  rw [rowNonblockingLaw, Measure.restrict_apply hs.compl,
    inter_eq_left.mpr (compl_subset_compl.mpr hsub), measure_compl hs (measure_ne_top _ _),
    measure_univ, Measure.prod_prod, unitScoreLaw_apply_Iio ha, unitScoreLaw_apply_Iio hy,
    ← ENNReal.ofReal_mul ha.1, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (mul_nonneg ha.1 hy.1)]
private def scoreSuccessorPairEvent (x v : ℝ) (y : ι → ℝ) :
    Set ((ℝ × ℝ) × (ι → ℝ × ℝ)) :=
  {z | x < z.1.1 ∧ z.1.2 < v ∧ ∀ h, ¬((z.2 h).1 < z.1.1 ∧ (z.2 h).2 < y h)}
theorem measurableSet_scoreSuccessorPairEvent [Fintype ι] (x v : ℝ) (y : ι → ℝ) :
    MeasurableSet (scoreSuccessorPairEvent x v y) := by
  unfold scoreSuccessorPairEvent
  simp only [ofPred_and, ofPred_forall]
  refine (measurableSet_lt measurable_const measurable_fst.fst).inter
    ((measurableSet_lt measurable_fst.snd measurable_const).inter
      (MeasurableSet.iInter fun h ↦ ?_))
  have hmeas : Measurable (fun z : (ℝ × ℝ) × (ι → ℝ × ℝ) ↦ z.2 h) :=
    (measurable_pi_apply h).comp measurable_snd
  exact ((measurableSet_lt hmeas.fst measurable_fst.fst).inter
    (measurableSet_lt hmeas.snd measurable_const)).compl
private theorem scoreSuccessorPairEvent_section {x v : ℝ} (y : ι → ℝ) (uv : ℝ × ℝ)
    (h : uv ∈ Ioi x ×ˢ Iio v) :
    Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y =
      Set.pi univ (fun j ↦ (Iio uv.1 ×ˢ Iio (y j))ᶜ) := by
  ext z
  simp only [mem_preimage, scoreSuccessorPairEvent, mem_ofPred_eq, mem_pi, mem_univ,
    true_implies, mem_compl_iff, mem_prod, mem_Iio]
  exact ⟨fun h' ↦ h'.2.2, fun h' ↦ ⟨h.1, h.2, h'⟩⟩
private theorem scoreSuccessorPairEvent_section_empty {x v : ℝ} (y : ι → ℝ) (uv : ℝ × ℝ)
    (h : uv ∉ Ioi x ×ˢ Iio v) :
    Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact h ⟨hz.1, hz.2.1⟩
theorem scoreSuccessorPairEvent_mass [Fintype ι] {x v : ℝ} {y : ι → ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    ((rowNonblockingLaw x v).prod (Measure.pi fun j ↦ rowNonblockingLaw x (y j)))
        (scoreSuccessorPairEvent x v y) =
      ENNReal.ofReal (v * scoreRowMass Finset.univ y x 1) := by
  let T : Set (ℝ × ℝ) := Ioi x ×ˢ Iio v
  let F : ℝ × ℝ → ℝ≥0∞ := fun uv ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1)
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Iio
  have hsupp : ∀ᵐ uv ∂rowNonblockingLaw x v, uv ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    unfold rowNonblockingLaw unitScoreLaw
    rw [Measure.prod_restrict]
    exact ae_restrict_of_ae (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))
  rw [Measure.prod_apply (measurableSet_scoreSuccessorPairEvent x v y)]
  have hsection :
      (fun uv ↦ (Measure.pi fun j ↦ rowNonblockingLaw x (y j))
        (Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y)) =ᵐ[rowNonblockingLaw x v]
          T.indicator F := by
    filter_upwards [hsupp] with uv hu
    by_cases ht : uv ∈ T
    · rw [scoreSuccessorPairEvent_section y uv ht, Measure.pi_pi, Set.indicator_of_mem ht]
      simp only [rowNonblockingLaw_apply_avoiding ht.1.le hu.1 (hy _)]
      unfold F scoreRowKernel
      exact (ENNReal.ofReal_prod_of_nonneg fun j _ ↦ sub_nonneg.mpr (by
        nlinarith [(hy j).1, (hy j).2, hu.1.2,
          mul_nonneg (sub_nonneg.mpr hu.1.2) (hy j).1])).symm
    · rw [scoreSuccessorPairEvent_section_empty y uv ht, measure_empty, Set.indicator_of_notMem ht]
  rw [lintegral_congr_ae hsection, lintegral_indicator hT]
  have hsub : T ⊆ (Iio x ×ˢ Iio v : Set (ℝ × ℝ))ᶜ := by
    intro uv h h'
    exact (not_lt_of_ge (show x < uv.1 from h.1).le) (show uv.1 < x from h'.1)
  have hrestrict : (rowNonblockingLaw x v).restrict T =
      (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio v)) := by
    rw [rowNonblockingLaw, Measure.restrict_restrict_of_subset hsub]
    exact (Measure.prod_restrict _ _).symm
  rw [hrestrict]
  have hf : Measurable fun u ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y u) :=
    (continuous_scoreRowKernel Finset.univ y).measurable.ennreal_ofReal
  unfold F
  rw [show (fun uv : ℝ × ℝ ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1)) =
    (fun uv : ℝ × ℝ ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1) * (1 : ℝ≥0∞)) by
      funext uv; rw [mul_one]]
  rw [lintegral_prod_mul hf.aemeasurable measurable_const.aemeasurable, lintegral_const, one_mul,
    Measure.restrict_apply_univ, unitScoreLaw_apply_Iio hv]
  have hleft : unitScoreLaw.restrict (Ioi x) = volume.restrict (Ioc x 1) := by
    rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext u
    change (x < u ∧ 0 ≤ u ∧ u ≤ 1) ↔ (x < u ∧ u ≤ 1)
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hx.1.trans h.1.le, h.2⟩⟩
  rw [hleft, scoreRowMass, intervalIntegral.integral_of_le hx.2,
    ENNReal.ofReal_mul hv.1, mul_comm (ENNReal.ofReal v)]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact ((continuous_scoreRowKernel Finset.univ y).intervalIntegrable x 1).1
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc x 1))]
      with u hu
    exact scoreRowKernel_nonneg (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
      ⟨hx.1.trans hu.1.le, hu.2⟩
end SuccessorMass
end DiagLP
end

-- ExposedRotations
section
open StableMarriage
namespace DiagLP
variable {n : ℕ}
private def IsEligibleSuccessor (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  p.manRank m (μ m) < p.manRank m w ∧ p.womanRank w m < p.womanRank w (μ.symm w)
private abbrev premiseOf {A B : Prop} (_ : A → B) := A
private abbrev IsSuccessor (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  premiseOf (@MarkedLP.IsSuccessor.unique n p μ m w w)
private theorem IsSuccessor.mk {p : Profile n} {μ : Matching n} {m w : Fin n}
    (h₁ : IsEligibleSuccessor p μ m w)
    (h₂ : ∀ w', IsEligibleSuccessor p μ m w' → p.manRank m w ≤ p.manRank m w') :
    IsSuccessor p μ m w := by
  constructor
  · exact h₁
  · exact h₂
private theorem IsSuccessor.eligible {p : Profile n} {μ : Matching n} {m w : Fin n}
    (h : IsSuccessor p μ m w) : IsEligibleSuccessor p μ m w := by
  obtain ⟨h₁, _⟩ := h
  exact h₁
private theorem IsSuccessor.min_rank {p : Profile n} {μ : Matching n} {m w : Fin n}
    (h : IsSuccessor p μ m w) :
    ∀ w', IsEligibleSuccessor p μ m w' → p.manRank m w ≤ p.manRank m w' := by
  obtain ⟨_, h₂⟩ := h
  exact h₂
private abbrev IsExposedRotation (p : Profile n) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Prop :=
  premiseOf (@MarkedLP.IsExposedRotation.womanRank_eliminate_le n p μ ρ)
private theorem IsExposedRotation.mk {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (h₁ : ρ.IsCycle) (h₂ : ∀ m, ρ m ≠ m → IsSuccessor p μ m (μ (ρ m))) :
    IsExposedRotation p μ ρ := by
  constructor
  · exact h₁
  · exact h₂
private theorem IsExposedRotation.isCycle {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (h : IsExposedRotation p μ ρ) : ρ.IsCycle := by
  obtain ⟨h₁, _⟩ := h
  exact h₁
private theorem IsExposedRotation.successor {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (h : IsExposedRotation p μ ρ) : ∀ m, ρ m ≠ m → IsSuccessor p μ m (μ (ρ m)) := by
  obtain ⟨_, h₂⟩ := h
  exact h₂
private def eliminateRotation (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Matching n :=
  ρ.trans μ
@[simp] theorem eliminateRotation_apply (μ : Matching n) (ρ : Equiv.Perm (Fin n)) (m : Fin n) :
    eliminateRotation μ ρ m = μ (ρ m) := rfl
variable {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
theorem IsSuccessor.unique {m w w' : Fin n}
    (h : IsSuccessor p μ m w) (h' : IsSuccessor p μ m w') : w = w' :=
  (p.manRank m).injective <| le_antisymm ((IsSuccessor.min_rank h) w' (IsSuccessor.eligible h')) ((IsSuccessor.min_rank h') w (IsSuccessor.eligible h))
theorem IsExposedRotation.womanRank_eliminate_le (hρ : IsExposedRotation p μ ρ) (w : Fin n) :
    p.womanRank w ((eliminateRotation μ ρ).symm w) ≤ p.womanRank w (μ.symm w) :=
  let ⟨m, hm⟩ := (eliminateRotation μ ρ).surjective w
  have hle : p.womanRank (μ (ρ m)) m ≤ p.womanRank (μ (ρ m)) (ρ m) :=
    if h : ρ m = m then
      (congrArg (p.womanRank (μ (ρ m))) h.symm).le
    else by
      simpa only [Equiv.symm_apply_apply] using (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m h)).2.le
  have htarget : p.womanRank (eliminateRotation μ ρ m)
        ((eliminateRotation μ ρ).symm (eliminateRotation μ ρ m)) ≤
      p.womanRank (eliminateRotation μ ρ m) (μ.symm (eliminateRotation μ ρ m)) := by
    have hinv : (eliminateRotation μ ρ).symm (μ (ρ m)) = m :=
      (eliminateRotation μ ρ).symm_apply_apply m
    simpa only [eliminateRotation_apply, hinv, Equiv.symm_apply_apply] using hle
  hm ▸ htarget
theorem IsExposedRotation.isStable_eliminate (hρ : IsExposedRotation p μ ρ)
    (hμ : IsStable p μ) : IsStable p (eliminateRotation μ ρ) :=
  fun m w hb ↦
    have hwOld : p.womanRank w m < p.womanRank w (μ.symm w) :=
      hb.2.2.trans_le (hρ.womanRank_eliminate_le w)
    have hne : μ m ≠ w := fun h ↦ (ne_of_lt hwOld)
      (congrArg (p.womanRank w) ((μ.symm_apply_apply m).symm.trans (congrArg μ.symm h)))
    have hnot : ¬ p.manRank m w < p.manRank m (μ m) := fun h ↦
      hμ m w ⟨hne, h, hwOld⟩
    if hm : ρ m = m then
      hnot (by simpa only [eliminateRotation_apply, hm] using hb.2.1)
    else
      have hbelow : p.manRank m (μ m) < p.manRank m w :=
        lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank m).injective he))
      (not_lt_of_ge ((IsSuccessor.min_rank ((IsExposedRotation.successor hρ) m hm)) w ⟨hbelow, hwOld⟩)) hb.2.1
end DiagLP
end

-- CoexposureScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private abbrev ScorePairIndex (n : ℕ) := Fin n × Fin n
private abbrev DiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 = q.2} → ℝ × ℝ
private abbrev OffDiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2} → ℝ × ℝ
private noncomputable def unitScorePairLaw : Measure (ℝ × ℝ) :=
  unitScoreLaw.prod unitScoreLaw
private instance : IsProbabilityMeasure unitScorePairLaw :=
  inferInstanceAs (IsProbabilityMeasure (unitScoreLaw.prod unitScoreLaw))
private noncomputable def diagonalScoreLaw (n : ℕ) : Measure (DiagonalScorePairs n) :=
  Measure.pi fun _ ↦ unitScorePairLaw
private noncomputable def offDiagonalScoreLaw (n : ℕ) : Measure (OffDiagonalScorePairs n) :=
  Measure.pi fun _ ↦ unitScorePairLaw
private instance (n : ℕ) : IsProbabilityMeasure (offDiagonalScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : {q : ScorePairIndex n // q.1 ≠ q.2} ↦
    unitScorePairLaw))
private theorem measurePreserving_scoreUncurry (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm
      (Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScoreLaw) := by
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  rw [MeasurableEquiv.map_apply]
  rw [show (MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i ↦ Set.univ.pi fun j ↦ s (i,j)) by
    ext x
    simp [Set.mem_pi, Prod.forall]]
  simp_rw [Measure.pi_pi]
  rw [← Finset.prod_product']
  simp
private def manScoreIndex {n : ℕ} (μ : Matching n) : ScorePairIndex n ≃ ScorePairIndex n :=
  Equiv.prodCongr (Equiv.refl _) μ
private def womanScoreIndex {n : ℕ} (μ : Matching n) : ScorePairIndex n ≃ ScorePairIndex n :=
  (manScoreIndex μ).trans (Equiv.prodComm _ _)
private def scorePairEquiv {n : ℕ} (μ : Matching n) :
    ScoreProfile n ≃ᵐ (ScorePairIndex n → ℝ × ℝ) :=
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n ↦ Fin n → ℝ)).trans
    (((MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ) (manScoreIndex μ).symm)).prodCongr
    ((MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
        (womanScoreIndex μ).symm)))).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (ScorePairIndex n)).symm
private theorem scorePairEquiv_apply {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (i j : Fin n) :
    scorePairEquiv μ x (i,j) = (x (.inl i) (μ j), x (.inr (μ j)) i) := by
  change ((MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
      (manScoreIndex μ).symm) (fun q ↦ x (.inl q.1) q.2) (i,j),
    (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
      (womanScoreIndex μ).symm) (fun q ↦ x (.inr q.1) q.2) (i,j)) = _
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    manScoreIndex, womanScoreIndex]
private theorem measurePreserving_scorePairEquiv {n : ℕ} (μ : Matching n) :
    MeasurePreserving (scorePairEquiv μ) (continuousScoreLaw n)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScorePairLaw) := by
  exact ((measurePreserving_arrowProdEquivProdArrow ℝ ℝ (ScorePairIndex n)
    (fun _ ↦ unitScoreLaw) (fun _ ↦ unitScoreLaw)).symm).comp
    ((((measurePreserving_piCongrLeft (fun _ ↦ unitScoreLaw) (manScoreIndex μ).symm).comp
      (measurePreserving_scoreUncurry n)).prod
      ((measurePreserving_piCongrLeft (fun _ ↦ unitScoreLaw) (womanScoreIndex μ).symm).comp
        (measurePreserving_scoreUncurry n))).comp
      (measurePreserving_sumPiEquivProdPi (fun _ ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)))
private def splitScorePairs {n : ℕ} (μ : Matching n) :
    ScoreProfile n ≃ᵐ DiagonalScorePairs n × OffDiagonalScorePairs n :=
  (scorePairEquiv μ).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      fun q ↦ q.1 = q.2)
theorem measurePreserving_splitScorePairs {n : ℕ} (μ : Matching n) :
    MeasurePreserving (splitScorePairs μ) (continuousScoreLaw n)
      ((diagonalScoreLaw n).prod (offDiagonalScoreLaw n)) :=
  (measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScorePairLaw)
    fun q : ScorePairIndex n ↦ q.1 = q.2).comp
    (measurePreserving_scorePairEquiv μ)
private def diagonalPairAt {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ × ℝ :=
  d ⟨(i,i), rfl⟩
theorem diagonalPairAt_splitScorePairs {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (i : Fin n) :
    diagonalPairAt (splitScorePairs μ x).1 i = (x (.inl i) (μ i), x (.inr (μ i)) i) :=
  scorePairEquiv_apply μ x i i
theorem splitScorePairs_offDiagonal_apply {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (q : {q : ScorePairIndex n // q.1 ≠ q.2}) :
    (splitScorePairs μ x).2 q =
      (x (.inl q.val.1) (μ q.val.2), x (.inr (μ q.val.2)) q.val.1) :=
  scorePairEquiv_apply μ x q.val.1 q.val.2
theorem unitScoreLaw_Iio_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    unitScoreLaw (Set.Iio x) = ENNReal.ofReal x := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iio]
  rw [show Set.Iio x ∩ Set.Icc 0 1 = Set.Ico 0 x by
    ext t
    exact ⟨fun ⟨hlt, hlo, _⟩ ↦ ⟨hlo, hlt⟩,
      fun ⟨hlo, hlt⟩ ↦ ⟨hlt, hlo, hlt.le.trans hx.2⟩⟩]
  rw [Real.volume_Ico, sub_zero]
private def nonblockingScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  (Set.Iio x ×ˢ Set.Iio y)ᶜ
private def offDiagonalNonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    Set (OffDiagonalScorePairs n) :=
  Set.univ.pi fun q ↦
    nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2
theorem isScoreStable_iff_splitScorePairs {n : ℕ} (μ : Matching n) (x : ScoreProfile n) :
    IsScoreStable x μ ↔ (splitScorePairs μ x).2 ∈
      offDiagonalNonblocking (splitScorePairs μ x).1 := by
  constructor
  · intro h q _
    simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs]
    exact fun ⟨hm, hw⟩ ↦ h q.val.1 (μ q.val.2)
      ⟨μ.injective.ne q.property, hm, by simpa only [Equiv.symm_apply_apply] using hw⟩
  · intro h i w hw
    let j := μ.symm w
    have hj : μ j = w := μ.apply_symm_apply w
    have hij : i ≠ j := fun he ↦ hw.1 ((congrArg μ he).trans hj)
    have hcell := h (i := ⟨(i,j), hij⟩) (Set.mem_univ _)
    simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs] at hcell
    apply hcell
    exact ⟨by simpa only [hj] using hw.2.1, by simpa only [hj] using hw.2.2⟩
theorem offDiagonalScoreLaw_restrict_nonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d) =
      Measure.pi fun q : {q : ScorePairIndex n // q.1 ≠ q.2} ↦ unitScorePairLaw.restrict
        (nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2) :=
  Measure.restrict_pi_pi _ _
theorem continuousScoreLaw_lintegral_stable_and_diagonal {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x in {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}, f x
      ∂continuousScoreLaw n) =
      ∫⁻ d in C, ∫⁻ v, f ((splitScorePairs μ).symm (d,v))
        ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) ∂diagonalScoreLaw n := by
  let S : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let E : Set (DiagonalScorePairs n × OffDiagonalScorePairs n) :=
    {z | z.1 ∈ C ∧ z.2 ∈ offDiagonalNonblocking z.1}
  let f' := f ∘ (splitScorePairs μ).symm
  have hS : MeasurableSet S := (measurableSet_isScoreStable μ).inter
    ((measurable_fst.comp (splitScorePairs μ).measurable) hC)
  have hE_pre : E = (splitScorePairs μ).symm ⁻¹' S := by
    ext z
    have h := isScoreStable_iff_splitScorePairs μ ((splitScorePairs μ).symm z)
    simpa [E, S, and_comm] using (and_congr_right fun _ : z.1 ∈ C ↦ h.symm)
  have hE : MeasurableSet E := hE_pre ▸ hS.preimage (splitScorePairs μ).symm.measurable
  have hpre : (splitScorePairs μ) ⁻¹' E = S := by
    ext x
    simp [E, S, ← isScoreStable_iff_splitScorePairs, and_comm]
  have hf' : Measurable f' := hf.comp (splitScorePairs μ).symm.measurable
  calc
    _ = ∫⁻ z in E, f' z ∂((diagonalScoreLaw n).prod (offDiagonalScoreLaw n)) := by
      rw [← (measurePreserving_splitScorePairs μ).setLIntegral_comp_preimage hE hf', hpre]
      simp [f', S]
    _ = _ := by
      rw [← lintegral_indicator hE,
        lintegral_prod _ (hf'.indicator hE).aemeasurable, ← lintegral_indicator hC]
      refine lintegral_congr fun d ↦ ?_
      by_cases hd : d ∈ C
      · have hnon : MeasurableSet (offDiagonalNonblocking d) :=
          MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
        rw [Set.indicator_of_mem hd, ← lintegral_indicator hnon]
        refine lintegral_congr fun v ↦ ?_
        by_cases hv : v ∈ offDiagonalNonblocking d <;> simp [E, f', hd, hv]
      · rw [Set.indicator_of_notMem hd]
        simp [E, hd]
theorem measurePreserving_rowTargetAndCompetitors {ι X : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace X] (m : ι → Measure X)
    [∀ i, SigmaFinite (m i)] (j : ι) :
    MeasurePreserving (fun r : ι → X ↦ (r j, fun k : {k : ι // k ≠ j} ↦ r k.val))
      (Measure.pi m) ((m j).prod (Measure.pi fun k : {k : ι // k ≠ j} ↦ m k.val)) := by
  let : Unique {k : ι // k = j} :=
    ⟨⟨⟨j, rfl⟩⟩, fun k ↦ Subtype.ext k.property⟩
  let : Fintype {k : ι // k = j} := Subtype.fintype (fun k ↦ k = j)
  exact ((measurePreserving_piUnique (fun k : {k : ι // k = j} ↦ m k.val)).prod
    (MeasurePreserving.id _)).comp (measurePreserving_piEquivPiSubtypeProd m fun k ↦ k = j)
end DiagLP
end

-- CoexposureSpouseMarginal
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
end DiagLP
end

-- CoexposureSpouseShells
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace DiagLP
end DiagLP
end

-- PittelMeanTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
end DiagLP
end

-- MarkedSpouseAngleComparison
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
end DiagLP
end

-- StableMaleSpouseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
end DiagLP
end

-- FiniteProductDensity
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
end DiagLP
end

-- SmallSpouseTotalLog
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace DiagLP
end DiagLP
end

-- MeanUpperBound
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace DiagLP
private noncomputable def meanUpperConstant : ℝ := Real.exp 2 + 1
end DiagLP
end

-- PivotSpouseProductLower
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
private def maleSpouseTotal {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ i, maleSpouseScore x μ i
theorem measurable_maleSpouseTotal {n : ℕ} (μ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ maleSpouseTotal x μ) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_maleSpouseScore μ i
end DiagLP
end

-- PivotForwardRevealCell
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
private def forwardEligibleScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  Ioi x ×ˢ Iio y
theorem measurableSet_forwardEligibleScoreCell (x y : ℝ) :
    MeasurableSet (forwardEligibleScoreCell x y) :=
  measurableSet_Ioi.prod measurableSet_Iio
private noncomputable def stableScoreCellLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  unitScorePairLaw.restrict (nonblockingScoreCell x y)
theorem stableScoreCellLaw_restrict_forwardEligible (x y : ℝ) :
    (stableScoreCellLaw x y).restrict (forwardEligibleScoreCell x y) =
      (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y)) := by
  rw [stableScoreCellLaw, Measure.restrict_restrict_of_subset]
  · exact (Measure.prod_restrict (Ioi x) (Iio y)).symm
  · rintro z hz hblock
    have h₁ : x < z.1 := (mem_prod.mp hz).1
    have h₂ : z.1 < x := (mem_prod.mp hblock).1
    exact (not_lt_of_ge h₁.le) h₂
private theorem unitScorePairLaw_ae_fst_ne (x : ℝ) :
    ∀ᵐ z ∂unitScorePairLaw, z.1 ≠ x := by
  exact (Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw) (ν := unitScoreLaw)).ae
    (unitScoreLaw.ae_ne x)
theorem stableScoreCellLaw_restrict_not_forwardEligible (x y : ℝ) :
    (stableScoreCellLaw x y).restrict (forwardEligibleScoreCell x y)ᶜ =
      unitScoreLaw.prod (unitScoreLaw.restrict (Ici y)) := by
  rw [stableScoreCellLaw,
    Measure.restrict_restrict (measurableSet_forwardEligibleScoreCell x y).compl]
  calc
    _ = unitScorePairLaw.restrict (univ ×ˢ Ici y) := by
      apply Measure.restrict_congr_set
      filter_upwards [unitScorePairLaw_ae_fst_ne x] with z hz
      apply propext
      change (¬ (x < z.1 ∧ z.2 < y)) ∧ (¬ (z.1 < x ∧ z.2 < y)) ↔ z ∈ univ ×ˢ Ici y
      simp only [mem_prod, mem_univ, true_and, mem_Ici]
      refine ⟨fun h ↦ le_of_not_gt ?_,
        fun hy ↦ ⟨fun h ↦ hy.not_gt h.2, fun h ↦ hy.not_gt h.2⟩⟩
      intro hy
      exact (lt_or_gt_of_ne hz).elim (fun hlt ↦ h.2 ⟨hlt, hy⟩) (fun hlt ↦ h.1 ⟨hlt, hy⟩)
    _ = _ := by rw [unitScorePairLaw, ← Measure.prod_restrict, Measure.restrict_univ]
private noncomputable def inactiveFemaleScoreLaw (y : ℝ) : Measure ℝ :=
  (unitScoreLaw (Ici y))⁻¹ • unitScoreLaw.restrict (Ici y)
theorem unitScoreLaw_Ici_of_mem_Icc {y : ℝ} (hy : y ∈ Icc 0 1) :
    unitScoreLaw (Ici y) = ENNReal.ofReal (1 - y) := by
  rw [← compl_Iio, measure_compl measurableSet_Iio (measure_ne_top _ _),
    measure_univ, unitScoreLaw_Iio_of_mem_Icc hy, ENNReal.ofReal_sub _ hy.1, ENNReal.ofReal_one]
theorem inactiveFemaleScoreLaw_isProbabilityMeasure {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    IsProbabilityMeasure (inactiveFemaleScoreLaw y) := by
  have hm : unitScoreLaw (Ici y) ≠ 0 := by
    rw [unitScoreLaw_Ici_of_mem_Icc ⟨hy0, hy1.le⟩]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hy1)).ne'
  refine ⟨?_⟩
  rw [inactiveFemaleScoreLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, ENNReal.inv_mul_cancel hm (measure_ne_top _ _)]
private def forwardScoreCellFlagEvent (x y : ℝ) (b : Bool) : Set (ℝ × ℝ) :=
  if b then forwardEligibleScoreCell x y else (forwardEligibleScoreCell x y)ᶜ
theorem measurableSet_forwardScoreCellFlagEvent (x y : ℝ) (b : Bool) :
    MeasurableSet (forwardScoreCellFlagEvent x y b) := by
  cases b
  · exact (measurableSet_forwardEligibleScoreCell x y).compl
  · exact measurableSet_forwardEligibleScoreCell x y
private noncomputable def forwardScoreCellFlagLaw (x y : ℝ) (b : Bool) : Measure (ℝ × ℝ) :=
  if b then (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y))
  else unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))
private instance (x y : ℝ) (b : Bool) : IsFiniteMeasure (forwardScoreCellFlagLaw x y b) := by
  cases b
  · exact inferInstanceAs
      (IsFiniteMeasure (unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))))
  · exact inferInstanceAs
      (IsFiniteMeasure ((unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y))))
theorem stableScoreCellLaw_restrict_flag (x y : ℝ) (b : Bool) :
    (stableScoreCellLaw x y).restrict (forwardScoreCellFlagEvent x y b) =
      forwardScoreCellFlagLaw x y b := by
  cases b
  · exact stableScoreCellLaw_restrict_not_forwardEligible x y
  · exact stableScoreCellLaw_restrict_forwardEligible x y
private abbrev OffDiagonalCellIndex (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2}
private def forwardScoreMaskEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (OffDiagonalScorePairs n) :=
  univ.pi fun q ↦ forwardScoreCellFlagEvent
    (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q)
theorem measurableSet_forwardScoreMaskEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : MeasurableSet (forwardScoreMaskEvent d flag) :=
  (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦
    measurableSet_forwardScoreCellFlagEvent _ _ _)
theorem offDiagonalScoreLaw_restrict_nonblocking_mask {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag) =
      Measure.pi fun q : OffDiagonalCellIndex n ↦ forwardScoreCellFlagLaw
        (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q) := by
  rw [offDiagonalScoreLaw_restrict_nonblocking, forwardScoreMaskEvent, Measure.restrict_pi_pi]
  congr 1
  funext q
  exact stableScoreCellLaw_restrict_flag _ _ _
theorem measurePreserving_offDiagonalScoreLaw_splitMask {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : OffDiagonalCellIndex n ↦ ℝ × ℝ)
        (fun q ↦ flag q = true))
      (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag))
      ((Measure.pi fun q : {q : OffDiagonalCellIndex n // flag q = true} ↦
        (unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)).prod
          (unitScoreLaw.restrict (Iio (diagonalPairAt d q.val.val.2).2))).prod
        (Measure.pi fun q : {q : OffDiagonalCellIndex n // flag q ≠ true} ↦
          unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d q.val.val.2).2)))) := by
  rw [offDiagonalScoreLaw_restrict_nonblocking_mask]
  convert measurePreserving_piEquivPiSubtypeProd
    (fun q : OffDiagonalCellIndex n ↦ forwardScoreCellFlagLaw
      (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q))
    (fun q ↦ flag q = true) using 2
  · congr 1
    funext q
    simp [forwardScoreCellFlagLaw, q.property]
  · congr 1
    funext q
    simp [forwardScoreCellFlagLaw, q.property]
private abbrev ForwardActiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q = true}
private abbrev ForwardInactiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q ≠ true}
private noncomputable def forwardScoreMaskInactiveLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure (ForwardInactiveCellIndex flag → ℝ × ℝ) :=
  Measure.pi fun q ↦
    unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d q.val.val.2).2))
private instance {n : ℕ} (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (forwardScoreMaskInactiveLaw d flag) := by
  unfold forwardScoreMaskInactiveLaw
  infer_instance
private def forwardScoreMaskRevealAndInactive {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (z : OffDiagonalScorePairs n) :
    (ForwardActiveCellIndex flag → ℝ) × (ForwardInactiveCellIndex flag → ℝ × ℝ) :=
  (fun q ↦ (z q.val).1, fun q ↦ z q.val)
theorem measurable_forwardScoreMaskRevealAndInactive {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (forwardScoreMaskRevealAndInactive flag) :=
  (measurable_pi_iff.2 fun q ↦ measurable_fst.comp (measurable_pi_apply q.val)).prodMk
    (measurable_pi_iff.2 fun q ↦ measurable_pi_apply q.val)
private noncomputable def forwardScoreMaskActiveMaleLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Measure (ForwardActiveCellIndex flag → ℝ) :=
  Measure.pi fun q ↦
    unitScoreLaw (Iio (diagonalPairAt d q.val.val.2).2) •
      unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)
private instance {n : ℕ} (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (forwardScoreMaskActiveMaleLaw d flag) := by
  have (q : ForwardActiveCellIndex flag) : IsFiniteMeasure
      (unitScoreLaw (Iio (diagonalPairAt d q.val.val.2).2) •
        unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)) :=
    Measure.smul_finite _ (measure_ne_top _ _)
  unfold forwardScoreMaskActiveMaleLaw
  infer_instance
theorem map_forwardScoreMaskRevealAndInactive {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure.map (forwardScoreMaskRevealAndInactive flag)
      (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag)) =
      (forwardScoreMaskActiveMaleLaw d flag).prod (forwardScoreMaskInactiveLaw d flag) := by
  let μ (q : ForwardActiveCellIndex flag) :=
    (unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)).prod
      (unitScoreLaw.restrict (Iio (diagonalPairAt d q.val.val.2).2))
  have (q : ForwardActiveCellIndex flag) : IsFiniteMeasure (μ q) := by
    unfold μ
    infer_instance
  have hproj : MeasurePreserving
      (fun z : ForwardActiveCellIndex flag → ℝ × ℝ ↦ fun q ↦ (z q).1)
      (Measure.pi μ) (Measure.pi fun q ↦ (μ q).map Prod.fst) :=
    measurePreserving_pi μ _ (fun _ ↦ ⟨measurable_fst, rfl⟩)
  have hsplit := measurePreserving_offDiagonalScoreLaw_splitMask d flag
  have h := ((hproj.prod (MeasurePreserving.id (forwardScoreMaskInactiveLaw d flag))).comp
    hsplit).map_eq
  change Measure.map (forwardScoreMaskRevealAndInactive flag) _ =
    (Measure.pi fun q ↦ (μ q).map Prod.fst).prod (forwardScoreMaskInactiveLaw d flag) at h
  simpa only [μ, Measure.map_fst_prod, Measure.restrict_apply_univ,
    forwardScoreMaskActiveMaleLaw] using h
private abbrev ForwardInactiveColumnIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (j : Fin n) := {q : ForwardInactiveCellIndex flag // q.val.val.2 = j}
private def forwardInactiveColumnsEquiv {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    (ForwardInactiveCellIndex flag → ℝ × ℝ) ≃ᵐ
      ((j : Fin n) → ForwardInactiveColumnIndex flag j → ℝ × ℝ) where
  toFun z _ q := z q.val
  invFun z q := z q.val.val.2 ⟨q, rfl⟩
  left_inv _ := rfl
  right_inv z := by
    funext j q
    obtain ⟨q, rfl⟩ := q
    rfl
  measurable_toFun := measurable_pi_iff.2 fun _ ↦
    measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 fun q ↦
    (measurable_pi_apply (⟨q, rfl⟩ : ForwardInactiveColumnIndex flag q.val.val.2)).comp
      (measurable_pi_apply q.val.val.2)
private theorem measurePreserving_forwardInactiveColumnsEquiv_pi {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool)
    (μ : ForwardInactiveCellIndex flag → Measure (ℝ × ℝ)) [∀ q, SigmaFinite (μ q)] :
    MeasurePreserving (forwardInactiveColumnsEquiv flag) (Measure.pi μ)
      (Measure.pi fun j : Fin n ↦
        Measure.pi fun q : ForwardInactiveColumnIndex flag j ↦ μ q.val) := by
  let e := (forwardInactiveColumnsEquiv flag).symm
  refine MeasurePreserving.symm e ⟨e.measurable, (Measure.pi_eq fun s _ ↦ ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  rw [show e ⁻¹' (univ.pi s) = univ.pi
      (fun j : Fin n ↦ univ.pi fun q : ForwardInactiveColumnIndex flag j ↦ s q.val) by
    ext z
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, e,
      forwardInactiveColumnsEquiv, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
      Equiv.symm, Equiv.coe_fn_mk]
    constructor
    · intro h j q
      obtain ⟨q, rfl⟩ := q
      exact h q
    · intro h q
      exact h q.val.val.2 ⟨q, rfl⟩]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_sigma']
  exact Fintype.prod_equiv
    (Equiv.sigmaFiberEquiv (fun q : ForwardInactiveCellIndex flag ↦ q.val.val.2))
    (fun q : Σ j : Fin n, ForwardInactiveColumnIndex flag j ↦ μ q.2.val (s q.2.val))
    (fun q : ForwardInactiveCellIndex flag ↦ μ q (s q)) (fun _ ↦ rfl)
private noncomputable def forwardScoreMaskInactiveColumnLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure ((j : Fin n) → ForwardInactiveColumnIndex flag j → ℝ × ℝ) :=
  Measure.pi fun j : Fin n ↦ Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
    unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d j).2))
private instance {n : ℕ} (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (forwardScoreMaskInactiveColumnLaw d flag) := by
  unfold forwardScoreMaskInactiveColumnLaw
  infer_instance
theorem measurePreserving_forwardInactiveColumnsEquiv {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurePreserving (forwardInactiveColumnsEquiv flag) (forwardScoreMaskInactiveLaw d flag)
      (forwardScoreMaskInactiveColumnLaw d flag) := by
  unfold forwardScoreMaskInactiveLaw forwardScoreMaskInactiveColumnLaw
  convert measurePreserving_forwardInactiveColumnsEquiv_pi flag
    (fun q ↦ unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d q.val.val.2).2)))
    using 2
  funext j
  congr 1
  funext q
  rw [q.property]
theorem map_forwardScoreMaskRevealAndInactiveColumns {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure.map
      (Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag)
      (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag)) =
      (forwardScoreMaskActiveMaleLaw d flag).prod (forwardScoreMaskInactiveColumnLaw d flag) := by
  rw [← Measure.map_map (measurable_id.prodMap (forwardInactiveColumnsEquiv flag).measurable)
    (measurable_forwardScoreMaskRevealAndInactive flag), map_forwardScoreMaskRevealAndInactive,
    ← Measure.map_prod_map _ _ measurable_id (forwardInactiveColumnsEquiv flag).measurable,
    Measure.map_id, (measurePreserving_forwardInactiveColumnsEquiv d flag).map_eq]
private noncomputable def normalizedForwardInactiveColumnLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) :
    Measure (ForwardInactiveColumnIndex flag j → ℝ × ℝ) :=
  Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
    unitScoreLaw.prod (inactiveFemaleScoreLaw (diagonalPairAt d j).2)
theorem normalizedForwardInactiveColumnLaw_isProbabilityMeasure {n : ℕ}
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) (j : Fin n)
    (hy0 : 0 ≤ (diagonalPairAt d j).2) (hy1 : (diagonalPairAt d j).2 < 1) :
    IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag j) := by
  have := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  unfold normalizedForwardInactiveColumnLaw
  infer_instance
private theorem pi_smul_finite {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i))
    [∀ i, IsFiniteMeasure (ν i)] (a : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ⊤) :
    (Measure.pi fun i ↦ a i • ν i) = (∏ i, a i) • Measure.pi ν := by
  have (i : ι) : IsFiniteMeasure (a i • ν i) := Measure.smul_finite (ν i) (ha i)
  refine Measure.pi_eq fun s _ ↦ ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]
theorem forwardScoreMaskInactiveColumnLaw_eq_smul {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (hy0 : ∀ j, 0 ≤ (diagonalPairAt d j).2) (hy1 : ∀ j, (diagonalPairAt d j).2 < 1) :
    forwardScoreMaskInactiveColumnLaw d flag =
      (∏ j, (ENNReal.ofReal (1 - (diagonalPairAt d j).2)) ^
        Fintype.card (ForwardInactiveColumnIndex flag j)) •
        Measure.pi (normalizedForwardInactiveColumnLaw d flag) := by
  let a (j : Fin n) := ENNReal.ofReal (1 - (diagonalPairAt d j).2)
  have (j : Fin n) : IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag j) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag j (hy0 j) (hy1 j)
  have hcolumn (j : Fin n) :
      (Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
        unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d j).2))) =
        a j ^ Fintype.card (ForwardInactiveColumnIndex flag j) •
          normalizedForwardInactiveColumnLaw d flag j := by
    let y := (diagonalPairAt d j).2
    have := inactiveFemaleScoreLaw_isProbabilityMeasure (hy0 j) (hy1 j)
    have hcell : unitScoreLaw.prod (unitScoreLaw.restrict (Ici y)) =
        a j • (unitScoreLaw.prod (inactiveFemaleScoreLaw y)) := by
      rw [inactiveFemaleScoreLaw, Measure.prod_smul_right, smul_smul,
        unitScoreLaw_Ici_of_mem_Icc ⟨hy0 j, (hy1 j).le⟩]
      change _ = (a j * (a j)⁻¹) • _
      rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hy1 j))).ne'
        ENNReal.ofReal_ne_top, one_smul]
    change (Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
      unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))) = _
    simp_rw [hcell]
    simpa only [Finset.prod_const, Finset.card_univ, normalizedForwardInactiveColumnLaw] using
      pi_smul_finite (fun _ : ForwardInactiveColumnIndex flag j ↦
        unitScoreLaw.prod (inactiveFemaleScoreLaw y)) (fun _ ↦ a j)
        (fun _ ↦ ENNReal.ofReal_ne_top)
  unfold forwardScoreMaskInactiveColumnLaw
  simp_rw [hcolumn]
  exact pi_smul_finite (normalizedForwardInactiveColumnLaw d flag) _
    (fun j ↦ ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
end DiagLP
end

-- PivotReverseEligibility
section
open MeasureTheory Set
open scoped ENNReal
namespace DiagLP
theorem measurePreserving_inactiveFemaleScoreLaw {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    MeasurePreserving (fun u : ℝ ↦ y + (1 - y) * u) unitScoreLaw
      (inactiveFemaleScoreLaw y) := by
  let a := 1 - y
  have ha : 0 < a := sub_pos.mpr hy1
  let f (u : ℝ) := y + a * u
  have hf : Measurable f := by unfold f; fun_prop
  have hpre : f ⁻¹' Icc y 1 = Icc 0 1 := by
    ext u
    change (y ≤ y + a * u ∧ y + a * u ≤ 1) ↔ (0 ≤ u ∧ u ≤ 1)
    have hae : y + a = 1 := by dsimp [a]; ring
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨nonneg_of_mul_nonneg_right (by linarith) ha, le_of_not_gt fun h ↦ ?_⟩
      linarith [mul_lt_mul_of_pos_left h ha]
    · rintro ⟨h0, h1⟩
      exact ⟨by linarith [mul_nonneg ha.le h0],
        by linarith [mul_le_mul_of_nonneg_left h1 ha.le]⟩
  have hmap : Measure.map f (volume : Measure ℝ) = ENNReal.ofReal a⁻¹ • volume := by
    change Measure.map ((y + ·) ∘ (a * ·)) volume = _
    rw [← Measure.map_map (measurable_const_add y) (measurable_const_mul a),
      Real.map_volume_mul_left ha.ne', abs_of_nonneg (inv_nonneg.mpr ha.le),
      Measure.map_smul, map_add_left_eq_self]
  have hs : Ici y ∩ Icc (0 : ℝ) 1 = Icc y 1 := by
    ext u
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hy0.trans h.1, h.2⟩⟩
  refine ⟨hf, ?_⟩
  change Measure.map f unitScoreLaw = _
  rw [unitScoreLaw, ← hpre, ← Measure.restrict_map hf measurableSet_Icc, hmap,
    inactiveFemaleScoreLaw, unitScoreLaw_Ici_of_mem_Icc ⟨hy0, hy1.le⟩,
    ← ENNReal.ofReal_inv_of_pos ha, Measure.restrict_smul, unitScoreLaw,
    Measure.restrict_restrict measurableSet_Ici, hs]
end DiagLP
end

-- PivotReverseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
variable {ι : Type*}
private def reverseSuccessorPairEvent (y x : ℝ) (v : ι → ℝ) :
    Set ((ℝ × ℝ) × (ι → ℝ × ℝ)) :=
  {z | y < z.1.2 ∧ z.1.1 < x ∧ ∀ j, ¬((z.2 j).2 < z.1.2 ∧ (z.2 j).1 < v j)}
theorem measurableSet_reverseSuccessorPairEvent [Fintype ι] (y x : ℝ) (v : ι → ℝ) :
    MeasurableSet (reverseSuccessorPairEvent y x v) := by
  unfold reverseSuccessorPairEvent
  simp only [ofPred_and, ofPred_forall]
  refine (measurableSet_lt measurable_const measurable_fst.snd).inter
    ((measurableSet_lt measurable_fst.fst measurable_const).inter
      (MeasurableSet.iInter fun j ↦ ?_))
  have h : Measurable (fun z : (ℝ × ℝ) × (ι → ℝ × ℝ) ↦ z.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact ((measurableSet_lt h.snd measurable_fst.snd).inter
    (measurableSet_lt h.fst measurable_const)).compl
private theorem rowNonblockingLaw_zero_eq_unitScorePairLaw (v : ℝ) :
    rowNonblockingLaw 0 v = unitScorePairLaw := by
  unfold rowNonblockingLaw unitScorePairLaw
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  simp only [mem_compl_iff, not_not, ofPred_mem_eq, Measure.prod_prod,
    unitScoreLaw_apply_Iio (show (0 : ℝ) ∈ Icc 0 1 by norm_num), ENNReal.ofReal_zero, zero_mul]
theorem reverseSuccessorPairEvent_mass [Fintype ι] {y x : ℝ} {v : ι → ℝ}
    (hy0 : 0 ≤ y) (hy1 : y < 1) (hx : x ∈ Icc 0 1) (hv : ∀ j, v j ∈ Icc 0 1) :
    ((unitScoreLaw.prod (inactiveFemaleScoreLaw y)).prod
      (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y)))
        (reverseSuccessorPairEvent y x v) =
      ENNReal.ofReal (x * scoreRowMass Finset.univ v 0 1) := by
  let a := 1 - y
  have ha : 0 < a := sub_pos.mpr hy1
  let g (z : ℝ × ℝ) := (z.2, y + a * z.1)
  let inactive := unitScoreLaw.prod (inactiveFemaleScoreLaw y)
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  have hg : MeasurePreserving g unitScorePairLaw inactive :=
    ((MeasurePreserving.id unitScoreLaw).prod
      (measurePreserving_inactiveFemaleScoreLaw hy0 hy1)).comp Measure.measurePreserving_swap
  have hπ : MeasurePreserving (fun z : ι → ℝ × ℝ ↦ fun j ↦ g (z j))
      (Measure.pi fun _ : ι ↦ unitScorePairLaw) (Measure.pi fun _ : ι ↦ inactive) :=
    measurePreserving_pi _ _ fun _ ↦ hg
  have h := hg.prod hπ
  have hlt (s t : ℝ) : y + a * s < y + a * t ↔ s < t :=
    (add_lt_add_iff_left y).trans (mul_lt_mul_iff_of_pos_left ha)
  have hzero (t : ℝ) : y < y + a * t ↔ 0 < t := by
    simpa only [mul_zero, add_zero] using hlt 0 t
  have he : Prod.map g (fun z : ι → ℝ × ℝ ↦ fun j ↦ g (z j)) ⁻¹'
      reverseSuccessorPairEvent y x v = scoreSuccessorPairEvent 0 x v := by
    ext z
    simp only [mem_preimage, reverseSuccessorPairEvent, scoreSuccessorPairEvent, mem_ofPred_eq,
      Prod.map_fst, Prod.map_snd, g, hzero, hlt]
  change (inactive.prod (Measure.pi fun _ : ι ↦ inactive))
    (reverseSuccessorPairEvent y x v) = _
  rw [← h.map_eq, Measure.map_apply h.measurable
    (measurableSet_reverseSuccessorPairEvent y x v), he]
  simpa only [rowNonblockingLaw_zero_eq_unitScorePairLaw] using
    scoreSuccessorPairEvent_mass (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hx hv
private def reverseSuccessorColumnEvent [DecidableEq ι] (y : ℝ) (v : ι → ℝ) (i : ι) :
    Set (ι → ℝ × ℝ) :=
  (fun z : ι → ℝ × ℝ ↦ (z i, fun j : {j : ι // j ≠ i} ↦ z j.val)) ⁻¹'
    reverseSuccessorPairEvent y (v i) (fun j : {j : ι // j ≠ i} ↦ v j.val)
theorem measurableSet_reverseSuccessorColumnEvent [Fintype ι] [DecidableEq ι]
    (y : ℝ) (v : ι → ℝ) (i : ι) : MeasurableSet (reverseSuccessorColumnEvent y v i) :=
  (measurableSet_reverseSuccessorPairEvent y (v i) (fun j : {j : ι // j ≠ i} ↦ v j.val)).preimage
    ((measurable_pi_apply i).prodMk (measurable_pi_iff.2 fun j ↦ measurable_pi_apply j.val))
theorem reverseSuccessorColumnEvent_mass [Fintype ι] [DecidableEq ι] {y : ℝ} {v : ι → ℝ}
    (i : ι) (hy0 : 0 ≤ y) (hy1 : y < 1) (hv : ∀ j, v j ∈ Icc 0 1) :
    (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y))
      (reverseSuccessorColumnEvent y v i) =
      ENNReal.ofReal (v i * scoreRowMass Finset.univ (fun j : {j : ι // j ≠ i} ↦ v j.val) 0 1) := by
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  let ν := unitScoreLaw.prod (inactiveFemaleScoreLaw y)
  have h := measurePreserving_rowTargetAndCompetitors (fun _ : ι ↦ ν) i
  rw [reverseSuccessorColumnEvent, ← Measure.map_apply h.measurable
    (measurableSet_reverseSuccessorPairEvent y _ _), h.map_eq]
  exact reverseSuccessorPairEvent_mass hy0 hy1 (hv i) fun j ↦ hv j.val
theorem reverseSuccessorColumnEvent_mass_le [Fintype ι] [DecidableEq ι] {y X a : ℝ}
    {v : ι → ℝ} (i : ι) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hv : ∀ j, v j ∈ Icc 0 1) (hX : 0 < X) (ha : 0 < a)
    (hcomp : X / a ≤ ∑ j : {j : ι // j ≠ i}, v j.val) :
    (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y))
      (reverseSuccessorColumnEvent y v i) ≤ ENNReal.ofReal a * ENNReal.ofReal (v i / X) := by
  let S := ∑ j : {j : ι // j ≠ i}, v j.val
  have hS : 0 < S := (div_pos hX ha).trans_le hcomp
  rw [reverseSuccessorColumnEvent_mass i hy0 hy1 hv, ← ENNReal.ofReal_mul ha.le]
  apply ENNReal.ofReal_le_ofReal
  have hrow : scoreRowMass Finset.univ (fun j : {j : ι // j ≠ i} ↦ v j.val) 0 1 ≤ 1 / S := by
    simpa only [mul_zero, neg_zero, Real.exp_zero] using
      (scoreRowMass_le_exp_tail (J := Finset.univ) (y := fun j : {j : ι // j ≠ i} ↦ v j.val)
        (fun j _ ↦ (hv j.val).1) (fun j _ ↦ (hv j.val).2) hS le_rfl
        (a := 0) (b := 1) le_rfl zero_le_one le_rfl)
  calc
    _ ≤ v i * (1 / S) := mul_le_mul_of_nonneg_left hrow (hv i).1
    _ = v i / S := by ring
    _ ≤ v i / (X / a) := div_le_div_of_nonneg_left (hv i).1 (div_pos hX ha) hcomp
    _ = _ := by rw [div_div_eq_mul_div]; ring
end DiagLP
end

-- ReverseSuccessorRotation
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
private def swapProfile (p : Profile n) : Profile n :=
  ⟨p.womanRank, p.manRank⟩
theorem isStable_swapProfile_iff : IsStable (swapProfile p) μ.symm ↔ IsStable p μ := by
  constructor
  · intro h m w hb
    exact h w m
      ⟨fun he ↦ hb.1 ((congrArg μ he).symm.trans (μ.apply_symm_apply w)), hb.2.2, hb.2.1⟩
  · intro h w m hb
    refine h m w ⟨fun he ↦ hb.1 ?_, hb.2.2, hb.2.1⟩
    simpa only [Equiv.symm_apply_apply] using (congrArg μ.symm he).symm
end DiagLP
end

-- PivotReverseScoreSuccessor
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
theorem exists_reverseSuccessorColumnEvent_of_isSuccessor {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (hs : IsScoreStable x μ) (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (i j : Fin n) (hji : j ≠ i)
    (hj : IsSuccessor (swapProfile (profileOfScores x)) μ.symm (μ i) j) :
    ∃ q : ForwardInactiveColumnIndex flag i, q.val.val.val.1 = j ∧
      (forwardInactiveColumnsEquiv flag (fun q ↦ (splitScorePairs μ x).2 q.val)) i ∈
        reverseSuccessorColumnEvent (diagonalPairAt (splitScorePairs μ x).1 i).2
          (fun k ↦ (diagonalPairAt (splitScorePairs μ x).1 k.val.val.val.1).1) q := by
  let d := (splitScorePairs μ x).1
  let z := (splitScorePairs μ x).2
  let a : OffDiagonalCellIndex n := ⟨(j, i), hji⟩
  have hmale (m : Fin n) (w w' : Fin n) :
      (profileOfScores x).manRank m w < (profileOfScores x).manRank m w' ↔
        x (.inl m) w < x (.inl m) w' := rankPermutation_lt_iff (ht (.inl m)) w w'
  have hfemale (m m' : Fin n) :
      (profileOfScores x).womanRank (μ i) m < (profileOfScores x).womanRank (μ i) m' ↔
        x (.inr (μ i)) m < x (.inr (μ i)) m' := rankPermutation_lt_iff (ht (.inr (μ i))) m m'
  have hmalej : x (.inl j) (μ i) < x (.inl j) (μ j) :=
    (hmale _ _ _).mp (by simpa only [swapProfile, Equiv.symm_symm] using (IsSuccessor.eligible hj).2)
  have hfemalej : x (.inr (μ i)) i < x (.inr (μ i)) j :=
    (hfemale _ _).mp (by simpa only [swapProfile, Equiv.symm_apply_apply] using (IsSuccessor.eligible hj).1)
  have ha : flag a ≠ true := by
    intro h
    have hh := mem_pi.mp hmask a (mem_univ _)
    change z a ∈ forwardScoreCellFlagEvent (diagonalPairAt d j).1
      (diagonalPairAt d i).2 (flag a) at hh
    dsimp only [z, d] at hh
    rw [h, forwardScoreCellFlagEvent, if_pos rfl, forwardEligibleScoreCell,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs] at hh
    exact hmalej.not_gt (mem_prod.mp hh).1
  let q : ForwardInactiveColumnIndex flag i := ⟨⟨a, ha⟩, rfl⟩
  let col := (forwardInactiveColumnsEquiv flag (fun k ↦ z k.val)) i
  have hcell (k : ForwardInactiveColumnIndex flag i) :
      col k = (x (.inl k.val.val.val.1) (μ i), x (.inr (μ i)) k.val.val.val.1) := by
    change (splitScorePairs μ x).2 k.val.val = _
    rw [splitScorePairs_offDiagonal_apply, k.property]
  refine ⟨q, rfl, ?_⟩
  change col ∈ reverseSuccessorColumnEvent (diagonalPairAt d i).2
    (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) q
  change (diagonalPairAt d i).2 < (col q).2 ∧
    (col q).1 < (diagonalPairAt d j).1 ∧
    ∀ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
      ¬ ((col k.val).2 < (col q).2 ∧
        (col k.val).1 < (diagonalPairAt d k.val.val.val.val.1).1)
  simp only [hcell, d, diagonalPairAt_splitScorePairs, q, a]
  refine ⟨hfemalej, hmalej, fun k h ↦ ?_⟩
  let m := k.val.val.val.val.1
  have hne : m ≠ i := fun hm ↦ k.val.val.val.property (hm.trans k.val.property.symm)
  have hbetter : x (.inl m) (μ i) < x (.inl m) (μ m) := h.2
  have hnotbetter : ¬ x (.inr (μ i)) m < x (.inr (μ i)) i :=
    fun hh ↦ hs m (μ i) ⟨μ.injective.ne hne, hbetter,
      by simpa only [Equiv.symm_apply_apply] using hh⟩
  have hww : x (.inr (μ i)) i < x (.inr (μ i)) m :=
    lt_of_le_of_ne (le_of_not_gt hnotbetter) ((ht (.inr (μ i))).ne hne.symm)
  have hel : IsEligibleSuccessor (swapProfile (profileOfScores x)) μ.symm (μ i) m := by
    simpa only [IsEligibleSuccessor, swapProfile, Equiv.symm_apply_apply, Equiv.symm_symm] using
      And.intro ((hfemale _ _).mpr hww) ((hmale _ _ _).mpr hbetter)
  exact (not_lt_of_ge ((IsSuccessor.min_rank hj) m hel)) ((hfemale _ _).mpr h.1)
private def forwardInactiveReverseArcEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n) :
    Set (ForwardInactiveColumnIndex flag i → ℝ × ℝ) :=
  ⋃ q : {q : ForwardInactiveColumnIndex flag i // q.val.val.val.1 = j},
    reverseSuccessorColumnEvent (diagonalPairAt d i).2
      (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) q.val
theorem measurableSet_forwardInactiveReverseArcEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n) :
    MeasurableSet (forwardInactiveReverseArcEvent d flag i j) :=
  MeasurableSet.iUnion fun q ↦ measurableSet_reverseSuccessorColumnEvent _ _ q.val
theorem isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (hs : IsScoreStable x μ) (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (i j : Fin n) (hji : j ≠ i) :
    IsSuccessor (swapProfile (profileOfScores x)) μ.symm (μ i) j ↔
      (forwardInactiveColumnsEquiv flag (fun q ↦ (splitScorePairs μ x).2 q.val)) i ∈
        forwardInactiveReverseArcEvent (splitScorePairs μ x).1 flag i j := by
  constructor
  · intro hj
    obtain ⟨q, hq, htest⟩ := exists_reverseSuccessorColumnEvent_of_isSuccessor
      μ x flag hs ht hmask i j hji hj
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, htest⟩
  · intro h
    obtain ⟨q, hq⟩ := mem_iUnion.mp h
    let d := (splitScorePairs μ x).1
    let z := (splitScorePairs μ x).2
    let col := (forwardInactiveColumnsEquiv flag (fun k ↦ z k.val)) i
    have hcell (k : ForwardInactiveColumnIndex flag i) :
        col k = (x (.inl k.val.val.val.1) (μ i), x (.inr (μ i)) k.val.val.val.1) := by
      change (splitScorePairs μ x).2 k.val.val = _
      rw [splitScorePairs_offDiagonal_apply, k.property]
    change (diagonalPairAt d i).2 < (col q.val).2 ∧
      (col q.val).1 < (diagonalPairAt d q.val.val.val.val.1).1 ∧
      ∀ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q.val},
        ¬ ((col k.val).2 < (col q.val).2 ∧
          (col k.val).1 < (diagonalPairAt d k.val.val.val.val.1).1) at hq
    simp only [hcell, d, diagonalPairAt_splitScorePairs, q.property] at hq
    have hf (a b : Fin n) : (profileOfScores x).womanRank (μ i) a <
        (profileOfScores x).womanRank (μ i) b ↔ x (.inr (μ i)) a < x (.inr (μ i)) b :=
      rankPermutation_lt_iff (ht (.inr (μ i))) a b
    have hm (a : Fin n) : (profileOfScores x).manRank a (μ i) <
        (profileOfScores x).manRank a (μ a) ↔ x (.inl a) (μ i) < x (.inl a) (μ a) :=
      rankPermutation_lt_iff (ht (.inl a)) _ _
    refine (IsSuccessor.mk (?_) (?_))
    · simpa only [IsEligibleSuccessor, swapProfile, Equiv.symm_symm, Equiv.symm_apply_apply] using
        And.intro ((hf i j).mpr hq.1) ((hm j).mpr hq.2.1)
    · intro m hel
      change (profileOfScores x).womanRank (μ i) j ≤ (profileOfScores x).womanRank (μ i) m
      apply le_of_not_gt
      intro hlt
      have hsmall := (hf m j).mp hlt
      have hmale : x (.inl m) (μ i) < x (.inl m) (μ m) :=
        (hm m).mp (by simpa only [swapProfile, Equiv.symm_symm] using hel.2)
      have hmi : m ≠ i := fun e ↦ (lt_irrefl _ (e ▸ hmale))
      let a : OffDiagonalCellIndex n := ⟨(m, i), hmi⟩
      have ha : flag a ≠ true := by
        intro he
        have hh := mem_pi.mp hmask a (mem_univ _)
        change (splitScorePairs μ x).2 a ∈ forwardScoreCellFlagEvent
          (diagonalPairAt (splitScorePairs μ x).1 m).1
          (diagonalPairAt (splitScorePairs μ x).1 i).2 (flag a) at hh
        rw [he, forwardScoreCellFlagEvent, if_pos rfl, forwardEligibleScoreCell,
          splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs] at hh
        exact hmale.not_gt (mem_prod.mp hh).1
      let k : ForwardInactiveColumnIndex flag i := ⟨⟨a, ha⟩, rfl⟩
      have hk : k ≠ q.val := fun he ↦ hsmall.ne
        (congrArg (fun b : ForwardInactiveColumnIndex flag i ↦
          x (.inr (μ i)) b.val.val.val.1) he |>.trans (congrArg (x (.inr (μ i))) q.property))
      exact hq.2.2 ⟨k, hk⟩ ⟨hsmall, hmale⟩
theorem normalizedForwardInactiveColumnLaw_reverseArc_le {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n) {X a : ℝ}
    (hy0 : 0 ≤ (diagonalPairAt d i).2) (hy1 : (diagonalPairAt d i).2 < 1)
    (hx : ∀ k, (diagonalPairAt d k).1 ∈ Icc 0 1) (hX : 0 < X) (ha : 0 < a)
    (hcomp : ∀ q : ForwardInactiveColumnIndex flag i, q.val.val.val.1 = j →
      X / a ≤ ∑ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
        (diagonalPairAt d k.val.val.val.val.1).1) :
    normalizedForwardInactiveColumnLaw d flag i (forwardInactiveReverseArcEvent d flag i j) ≤
      ENNReal.ofReal a * ENNReal.ofReal ((diagonalPairAt d j).1 / X) := by
  by_cases h : ∃ q : ForwardInactiveColumnIndex flag i, q.val.val.val.1 = j
  · obtain ⟨q, hq⟩ := h
    have he : forwardInactiveReverseArcEvent d flag i j =
        reverseSuccessorColumnEvent (diagonalPairAt d i).2
          (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) q := by
      ext z
      change (z ∈ ⋃ q' : {q' : ForwardInactiveColumnIndex flag i // q'.val.val.val.1 = j},
        reverseSuccessorColumnEvent (diagonalPairAt d i).2
          (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) q'.val) ↔ _
      rw [mem_iUnion]
      refine ⟨?_, fun hz ↦ ⟨⟨q, hq⟩, hz⟩⟩
      rintro ⟨q', hz⟩
      have hq' : q'.val = q := Subtype.ext (Subtype.ext (Subtype.ext
        (Prod.ext (q'.property.trans hq.symm) (q'.val.property.trans q.property.symm))))
      simpa only [hq'] using hz
    rw [he, ← hq]
    exact reverseSuccessorColumnEvent_mass_le q hy0 hy1 (fun k ↦ hx k.val.val.val.1)
      hX ha (hcomp q hq)
  · have he : forwardInactiveReverseArcEvent d flag i j = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨q, _⟩ := mem_iUnion.mp hz
      exact h ⟨q.val, q.property⟩
    simp only [he, measure_empty, zero_le]
end DiagLP
end

-- PivotRelaxedArcEvents
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
private abbrev forwardInactiveColumnMan {n : ℕ} {flag : OffDiagonalCellIndex n → Bool}
    {i : Fin n} (q : ForwardInactiveColumnIndex flag i) : Fin n :=
  q.val.val.val.1
theorem forwardInactiveColumnMan_injective {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (i : Fin n) : Function.Injective (forwardInactiveColumnMan (flag := flag) (i := i)) := by
  intro q t h
  exact Subtype.ext (Subtype.ext (Subtype.ext
    (Prod.ext h (q.property.trans t.property.symm))))
private abbrev ForwardKeptColumnIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (P : Finset (Fin n)) (i : Fin n) :=
  {q : ForwardInactiveColumnIndex flag i // forwardInactiveColumnMan q ∉ P}
private abbrev forwardInactiveColumnThreshold {n : ℕ} (d : DiagonalScorePairs n)
    {flag : OffDiagonalCellIndex n → Bool} {i : Fin n}
    (q : ForwardInactiveColumnIndex flag i) : ℝ :=
  (diagonalPairAt d (forwardInactiveColumnMan q)).1
private noncomputable def forwardKeptCompetitorMass {n : ℕ} (d : DiagonalScorePairs n)
    {flag : OffDiagonalCellIndex n → Bool} {P : Finset (Fin n)} {i : Fin n}
    (t : ForwardKeptColumnIndex flag P i) : ℝ :=
  ∑ q : {q : ForwardKeptColumnIndex flag P i // q ≠ t},
    forwardInactiveColumnThreshold d q.val.val
end DiagLP
end

-- FinitePrerequisites
section
namespace DiagLP
end DiagLP
end

-- RotationDiamond
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}
private theorem moved_image {f : Equiv.Perm (Fin n)} {i : Fin n} (hi : f i ≠ i) :
    f (f i) ≠ f i :=
  f.injective.ne hi
private theorem eq_of_common_moved (hρ : IsExposedRotation p μ ρ) (hσ : IsExposedRotation p μ σ)
    {m : Fin n} (hmρ : ρ m ≠ m) (hmσ : σ m ≠ m) : ρ = σ := by
  have hagree (i : Fin n) (hiρ : ρ i ≠ i) (hiσ : σ i ≠ i) : ρ i = σ i :=
    μ.injective (((IsExposedRotation.successor hρ) i hiρ).unique ((IsExposedRotation.successor hσ) i hiσ))
  have horbit (k : ℕ) :
      (ρ ^ k) m = (σ ^ k) m ∧ ρ ((ρ ^ k) m) ≠ (ρ ^ k) m ∧ σ ((σ ^ k) m) ≠ (σ ^ k) m := by
    induction k with
    | zero => simpa using And.intro (rfl : m = m) (And.intro hmρ hmσ)
    | succ k ih =>
      obtain ⟨heq, hmoveρ, hmoveσ⟩ := ih
      have hmoveσ' : σ ((ρ ^ k) m) ≠ (ρ ^ k) m := heq ▸ hmoveσ
      simp only [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨(hagree _ hmoveρ hmoveσ').trans (congrArg σ heq),
        moved_image hmoveρ, moved_image hmoveσ⟩
  apply Equiv.ext
  intro i
  by_cases hi : ρ i ≠ i
  · obtain ⟨k, hk⟩ := (IsExposedRotation.isCycle hρ).exists_pow_eq hmρ hi
    have his : σ i ≠ i := by
      rw [← hk, (horbit k).1]
      exact (horbit k).2.2
    exact hagree i hi his
  · have his : σ i = i := by
      by_contra hsi
      obtain ⟨k, hk⟩ := (IsExposedRotation.isCycle hσ).exists_pow_eq hmσ hsi
      apply hi
      rw [← hk, ← (horbit k).1]
      exact (horbit k).2.1
    exact (not_ne_iff.mp hi).trans his.symm
theorem IsExposedRotation.disjoint_moved (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) (m : Fin n) (hm : ρ m ≠ m) : σ m = m := by
  by_contra hs
  exact hne (eq_of_common_moved hρ hσ hm hs)
end DiagLP
end

-- ManOptimal
section
open StableMarriage
open scoped BigOperators
namespace DiagLP
variable {n : ℕ}
private def MenWeaklyPrefer (p : Profile n) (μ ν : Matching n) : Prop :=
  ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)
private def IsManOptimal (p : Profile n) (μ : Matching n) : Prop :=
  IsStable p μ ∧ ∀ ν, IsStable p ν → MenWeaklyPrefer p μ ν
end DiagLP
end

-- RotationCycle
section
namespace DiagLP
open Function
end DiagLP
end

-- TargetSuccessor
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
end DiagLP
end

-- RotationReachability
section
open scoped BigOperators
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n}
end DiagLP
end

-- RotationLabels
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n}
end DiagLP
end

-- RotationPathIndependence
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n}
end DiagLP
end

-- RotationTrace
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n}
namespace RotationSequence
variable {μ ν τ : Matching n} {rs ss : List (Equiv.Perm (Fin n))}
end RotationSequence
end DiagLP
end

-- RotationIdeals
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
end DiagLP
end

-- CoexposedRotations
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
end DiagLP
end

-- CoexposedRotationMultiplicity
section
open StableMarriage
open scoped BigOperators
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ : Matching n}
private noncomputable def numExposedRotations (p : Profile n) (μ : Matching n) : ℕ :=
  Nat.card {ρ : Equiv.Perm (Fin n) // IsExposedRotation p μ ρ}
end DiagLP
end

-- CoexposureCycleMoment
section
open StableMarriage MeasureTheory
open scoped BigOperators ENNReal
namespace DiagLP
private def RealizesSuccessorPermutation {n : ℕ} (p : Profile n) (M σ : Matching n) : Prop :=
  ∀ i ∈ σ.support, IsSuccessor p M i (M (σ i))
theorem realizesSuccessorPermutation_one {n : ℕ} (p : Profile n) (M : Matching n) :
    RealizesSuccessorPermutation p M 1 := by
  intro i hi
  simp at hi
theorem realizesSuccessorPermutation_iff_factors {n : ℕ}
    {p : Profile n} {M σ : Matching n} :
    RealizesSuccessorPermutation p M σ ↔
      ∀ ρ ∈ σ.cycleFactorsFinset, IsExposedRotation p M ρ := by
  constructor
  · intro h ρ hρ
    obtain ⟨hc, heq⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hρ
    refine (IsExposedRotation.mk (hc) (fun i hi ↦ ?_))
    have hmem := Equiv.Perm.mem_support.mpr hi
    rw [heq i hmem]
    exact h i (Equiv.Perm.mem_cycleFactorsFinset_support_le hρ hmem)
  · intro h i hi
    obtain ⟨ρ, hρ, hmem⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hi
    rw [← (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hρ).2 i hmem]
    exact (IsExposedRotation.successor (h ρ hρ)) i (Equiv.Perm.mem_support.mp hmem)
private theorem exposedRotation_pairwise_disjoint {n : ℕ} {p : Profile n} {M : Matching n}
    {C : Finset (Matching n)} (hC : ∀ ρ ∈ C, IsExposedRotation p M ρ) :
    (C : Set (Matching n)).Pairwise Equiv.Perm.Disjoint := by
  intro ρ hρ σ hσ hne i
  by_cases hi : ρ i = i
  · exact Or.inl hi
  · exact Or.inr ((hC ρ hρ).disjoint_moved (hC σ hσ) hne i hi)
open scoped Classical in
private theorem sum_realized_cycleFactors {n : ℕ} {A : Type*} [AddCommMonoid A]
    (p : Profile n) (M : Matching n) (f : Finset (Matching n) → A) :
    (∑ σ ∈ Finset.univ.filter (RealizesSuccessorPermutation p M), f σ.cycleFactorsFinset) =
      ∑ S ∈ (Finset.univ.filter (IsExposedRotation p M)).powerset, f S := by
  let C := Finset.univ.filter (IsExposedRotation p M)
  let P := Finset.univ.filter (RealizesSuccessorPermutation p M)
  have hC : ∀ ρ, ρ ∈ C ↔ IsExposedRotation p M ρ := by simp [C]
  have hP : ∀ σ, σ ∈ P ↔ RealizesSuccessorPermutation p M σ := by simp [P]
  refine Finset.sum_bij (fun σ _ ↦ σ.cycleFactorsFinset) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro σ hσ
    exact Finset.mem_powerset.mpr fun ρ hρ ↦
      (hC ρ).mpr (realizesSuccessorPermutation_iff_factors.mp ((hP σ).mp hσ) ρ hρ)
  · intro σ _ τ _ h
    exact Equiv.Perm.cycleFactorsFinset_injective h
  · intro S hS
    have hrot : ∀ ρ ∈ S, IsExposedRotation p M ρ :=
      fun ρ hρ ↦ (hC ρ).mp (Finset.mem_powerset.mp hS hρ)
    have hd := exposedRotation_pairwise_disjoint hrot
    let σ := S.noncommProd id (hd.mono' fun _ _ ↦ Equiv.Perm.Disjoint.commute)
    have heq : σ.cycleFactorsFinset = S :=
      Equiv.Perm.cycleFactorsFinset_eq_finset.mpr
        ⟨fun ρ hρ ↦ (IsExposedRotation.isCycle (hrot ρ hρ)), hd, rfl⟩
    refine ⟨σ, (hP σ).mpr (realizesSuccessorPermutation_iff_factors.mpr ?_), heq⟩
    simpa only [heq] using hrot
theorem card_realizesSuccessorPermutation {n : ℕ} (p : Profile n) (M : Matching n) :
    Nat.card {σ : Matching n // RealizesSuccessorPermutation p M σ} =
      2 ^ numExposedRotations p M := by
  classical
  let C := Finset.univ.filter (IsExposedRotation p M)
  let P := Finset.univ.filter (RealizesSuccessorPermutation p M)
  have hC : ∀ ρ, ρ ∈ C ↔ IsExposedRotation p M ρ := by simp [C]
  have hP : ∀ σ, σ ∈ P ↔ RealizesSuccessorPermutation p M σ := by simp [P]
  rw [numExposedRotations, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_of_subtype P hP, Fintype.card_of_subtype C hC, ← Finset.card_powerset]
  simpa using (sum_realized_cycleFactors p M (fun _ ↦ (1 : ℕ)))
theorem sum_successorPermutation_cycleWeight_indicators {n : ℕ} {Ω : Type*}
    (P : Ω → Profile n) (M : Matching n) (x : Ω) (b : ℝ≥0∞) :
    (∑ σ : Matching n, ({y | RealizesSuccessorPermutation (P y) M σ} : Set Ω).indicator
      (fun _ ↦ b ^ σ.cycleFactorsFinset.card) x) = (b + 1) ^ numExposedRotations (P x) M := by
  classical
  let C := Finset.univ.filter (IsExposedRotation (P x) M)
  have hC : ∀ ρ, ρ ∈ C ↔ IsExposedRotation (P x) M ρ := by simp [C]
  have hcard : numExposedRotations (P x) M = C.card := by
    rw [numExposedRotations, Nat.card_eq_fintype_card, Fintype.card_of_subtype C hC]
  calc
    _ = ∑ σ ∈ Finset.univ.filter (RealizesSuccessorPermutation (P x) M),
        b ^ σ.cycleFactorsFinset.card := by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_filter]
    _ = ∑ S ∈ C.powerset, b ^ S.card :=
      sum_realized_cycleFactors (P x) M (fun S ↦ b ^ S.card)
    _ = (b + 1) ^ C.card := by simpa only [Finset.prod_const] using
      (Finset.prod_add_one (f := fun _ ↦ b) C).symm
    _ = _ := by rw [hcard]
theorem lintegral_cycleWeight_numExposedRotations_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (hP : Measurable P) (M : Matching n)
    (b : ℝ≥0∞) (bound : Matching n → ℝ≥0∞)
    (harc : ∀ σ, ν {x | RealizesSuccessorPermutation (P x) M σ} ≤ bound σ) :
    (∫⁻ x, (b + 1) ^ numExposedRotations (P x) M ∂ν) ≤
      ∑ σ : Matching n, b ^ σ.cycleFactorsFinset.card * bound σ := by
  have hm (σ : Matching n) : MeasurableSet {x | RealizesSuccessorPermutation (P x) M σ} :=
    hP (MeasurableSet.of_discrete : MeasurableSet {p : Profile n |
      RealizesSuccessorPermutation p M σ})
  simp_rw [← sum_successorPermutation_cycleWeight_indicators P M _ b]
  rw [lintegral_finsetSum _ (fun σ _ ↦ measurable_const.indicator (hm σ))]
  exact Finset.sum_le_sum fun σ _ ↦
    (lintegral_indicator_const (hm σ) _).le.trans (mul_le_mul_right (harc σ) _)
theorem sum_weighted_successorPermutation_product_by_support {n : ℕ}
    (f : Matching n → ℝ≥0∞) (a : ℝ≥0∞) (w : Fin n → ℝ≥0∞) :
    (∑ σ : Matching n, f σ * ∏ i ∈ σ.support, a * w (σ i)) =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.support = s), f σ) *
          (a ^ s.card * ∏ i ∈ s, w i) := by
  classical
  have hmem (σ : Matching n) (_ : σ ∈ (Finset.univ : Finset (Matching n))) :
      σ.support ∈ (Finset.univ : Finset (Fin n)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ _)
  rw [← Finset.sum_fiberwise_of_maps_to hmem (fun σ ↦ f σ * ∏ i ∈ σ.support, a * w (σ i))]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  rw [σ.prod_comp σ.support (fun j ↦ a * w j)
    (fun _ h ↦ Equiv.Perm.mem_support.mpr h), (Finset.mem_filter.mp hσ).2,
    Finset.prod_mul_distrib, Finset.prod_const]
end DiagLP
end

-- PivotReverseMaskJointLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private noncomputable def forwardMaskRevealLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (A : Set (ForwardActiveCellIndex flag → ℝ)) :
    Measure (OffDiagonalScorePairs n) :=
  (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
    (forwardScoreMaskEvent d flag)).restrict
      ((Prod.fst ∘ forwardScoreMaskRevealAndInactive flag) ⁻¹' A)
theorem measure_realizesReverseSuccessorPermutation_fixedMask {n : ℕ}
    (μ σ : Matching n) (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (A : Set (ForwardActiveCellIndex flag → ℝ)) (hA : MeasurableSet A)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    forwardMaskRevealLaw d flag A {z | RealizesSuccessorPermutation
      (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm σ} =
      ((forwardScoreMaskActiveMaleLaw d flag) A *
        (forwardScoreMaskInactiveColumnLaw d flag) univ) *
      ∏ i ∈ σ.support,
        normalizedForwardInactiveColumnLaw d flag (μ.symm i)
          (forwardInactiveReverseArcEvent d flag (μ.symm i) (μ.symm (σ i))) := by
  let ν := ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
    (forwardScoreMaskEvent d flag)
  let G := (Prod.fst ∘ forwardScoreMaskRevealAndInactive flag) ⁻¹' A
  let P (z : OffDiagonalScorePairs n) :=
    swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))
  let f := Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag
  let L := forwardScoreMaskInactiveColumnLaw d flag
  let R := forwardScoreMaskActiveMaleLaw d flag
  let L₀ := normalizedForwardInactiveColumnLaw d flag
  let : ∀ i : Fin n, IsProbabilityMeasure (L₀ i) := fun i ↦
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  have hf : Measurable f :=
    (measurable_id.prodMap (forwardInactiveColumnsEquiv flag).measurable).comp
      (measurable_forwardScoreMaskRevealAndInactive flag)
  let B (i : Fin n) : Set (ForwardInactiveColumnIndex flag i → ℝ × ℝ) :=
    if μ i ∈ σ.support then forwardInactiveReverseArcEvent d flag i (μ.symm (σ (μ i)))
    else univ
  have hB (i : Fin n) : MeasurableSet (B i) := by
    by_cases h : μ i ∈ σ.support
    · simpa only [B, if_pos h] using measurableSet_forwardInactiveReverseArcEvent d flag i _
    · simp only [B, if_neg h, MeasurableSet.univ]
  have hrect : MeasurableSet (A ×ˢ univ.pi B) := hA.prod (MeasurableSet.univ_pi hB)
  have hnon : MeasurableSet (offDiagonalNonblocking d) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
  have hevent : {z | RealizesSuccessorPermutation (P z) μ.symm σ} =ᵐ[ν.restrict G]
      f ⁻¹' (A ×ˢ univ.pi B) := by
    filter_upwards [ae_restrict_mem (hA.preimage (measurable_fst.comp
        (measurable_forwardScoreMaskRevealAndInactive flag))),
      ae_restrict_of_ae (ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)),
      ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_mem hnon)),
      ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae ht))]
      with z hzG hzmask hzstable hzt
    let x := (splitScorePairs μ).symm (d, z)
    have he : splitScorePairs μ x = (d, z) := (splitScorePairs μ).apply_symm_apply _
    have hxstable : IsScoreStable x μ := (isScoreStable_iff_splitScorePairs μ x).2
      (by simpa only [he] using hzstable)
    have hxmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag :=
      by simpa only [he] using hzmask
    have harc (i : Fin n) (hi : μ i ∈ σ.support) :
        IsSuccessor (P z) μ.symm (μ i) (μ.symm (σ (μ i))) ↔ (f z).2 i ∈ B i := by
      have hne : μ.symm (σ (μ i)) ≠ i := fun h ↦
        Equiv.Perm.mem_support.mp hi (by simpa only [Equiv.apply_symm_apply] using congrArg μ h)
      rw [show B i = forwardInactiveReverseArcEvent d flag i (μ.symm (σ (μ i))) by
        simp only [B, if_pos hi]]
      have h := isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent
        μ x flag hxstable hzt hxmask i _ hne
      rw [he] at h
      exact h
    apply propext
    constructor
    · intro h
      refine ⟨hzG, mem_pi.mpr fun i _ ↦ ?_⟩
      by_cases hi : μ i ∈ σ.support
      · exact (harc i hi).mp (h (μ i) hi)
      · simp only [B, if_neg hi, mem_univ]
    · intro h j hj
      have hi : μ (μ.symm j) ∈ σ.support := by simpa only [Equiv.apply_symm_apply] using hj
      have hB' := mem_pi.mp h.2 (μ.symm j) (mem_univ _)
      simpa only [Equiv.apply_symm_apply] using (harc _ hi).mpr hB'
  have hl : L (univ.pi B) = L univ * ∏ i, L₀ i (B i) := by
    change forwardScoreMaskInactiveColumnLaw d flag (univ.pi B) =
      forwardScoreMaskInactiveColumnLaw d flag univ * _
    rw [forwardScoreMaskInactiveColumnLaw_eq_smul d flag hy0 hy1, Measure.smul_apply,
      Measure.smul_apply, Measure.pi_pi, measure_univ, smul_eq_mul, smul_eq_mul, mul_one]
  have hp : (∏ i, L₀ i (B i)) =
      ∏ i ∈ σ.support, L₀ (μ.symm i) (forwardInactiveReverseArcEvent d flag
        (μ.symm i) (μ.symm (σ i))) := by
    let g (i : Fin n) := if i ∈ σ.support then
      L₀ (μ.symm i) (forwardInactiveReverseArcEvent d flag (μ.symm i) (μ.symm (σ i))) else 1
    calc
      _ = ∏ i, g (μ i) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        by_cases hi : μ i ∈ σ.support
        · simp only [B, g, if_pos hi]
          exact congrArg (fun j ↦ L₀ j (forwardInactiveReverseArcEvent d flag j (μ.symm (σ (μ i)))))
            (μ.symm_apply_apply i).symm
        · simp only [B, g, if_neg hi, measure_univ]
      _ = ∏ i, g i := Fintype.prod_equiv μ _ _ (fun _ ↦ rfl)
      _ = _ := by simp only [g, Finset.prod_ite_mem, Finset.univ_inter]
  calc
    _ = (ν.restrict G) (f ⁻¹' (A ×ˢ univ.pi B)) := measure_congr hevent
    _ = ν (f ⁻¹' (A ×ˢ univ.pi B)) := by
      rw [Measure.restrict_apply (hrect.preimage hf), inter_eq_left.mpr (fun _ hz ↦ hz.1)]
    _ = R A * L (univ.pi B) := by
      rw [← Measure.map_apply hf hrect, map_forwardScoreMaskRevealAndInactiveColumns d flag,
        Measure.prod_prod]
    _ = _ := by rw [hl, hp, mul_assoc]
theorem forwardMaskRevealLaw_univ {n : ℕ} (μ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (A : Set (ForwardActiveCellIndex flag → ℝ))
    (hA : MeasurableSet A)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    forwardMaskRevealLaw d flag A univ =
      (forwardScoreMaskActiveMaleLaw d flag) A * (forwardScoreMaskInactiveColumnLaw d flag) univ := by
  simpa only [realizesSuccessorPermutation_one, Set.ofPred_true, Equiv.Perm.support_one,
    Finset.prod_empty, mul_one] using
    measure_realizesReverseSuccessorPermutation_fixedMask μ 1 d flag A hA hy0 hy1 ht
end DiagLP
end

-- RowCompetition
section
open Set
open scoped BigOperators
namespace DiagLP
variable {ι : Type*} {J : Finset ι} {a : ι → ℝ} {A b : ℝ}
end DiagLP
end

-- ReverseArcRelativeLower
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
private noncomputable def reverseLowerArcError (X : ℝ) : ℝ := 1 / (1 + X)
end DiagLP
end

-- ReverseIIDLabelGood
section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace DiagLP
section Measures
variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
variable [Fintype α] [DiscreteMeasurableSpace α]
private def iidLabelGood (A : Set α) (F : α → Set α) (e : ι → ι) : Set (ι → α) :=
  {x | Function.Injective x ∧ (∀ i, x i ∉ A) ∧ ∀ i, x (e i) ∉ F (x i)}
end Measures
end DiagLP
end

-- ReverseCycleLabelMultiplicity
section
open scoped BigOperators ENNReal
namespace DiagLP
variable {α : Type*} [Fintype α] [DecidableEq α]
private abbrev GoodLabeling (k : ℕ) (A : Finset α) (F : α → Finset α) :=
  Σ e : derangements (Fin k),
    {x : Fin k → α // x ∈ iidLabelGood (A : Set α) (fun a ↦ ↑(F a)) e.val}
private abbrev GoodSupport (k : ℕ) (A : Finset α) (F : α → Finset α) :=
  {σ : Equiv.Perm α // σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i}
variable {k : ℕ} {A : Finset α} {F : α → Finset α}
private def labelingEmbedding (l : GoodLabeling k A F) : Fin k ↪ α :=
  ⟨l.2.val, l.2.property.1⟩
private def labelingPerm (l : GoodLabeling k A F) : Equiv.Perm α :=
  l.1.val.viaFintypeEmbedding (labelingEmbedding l)
omit [Fintype α] in
private theorem labelingPerm_apply (l : GoodLabeling k A F) (i : Fin k) :
    labelingPerm l (l.2.val i) = l.2.val (l.1.val i) :=
  l.1.val.viaFintypeEmbedding_apply_image (labelingEmbedding l) i
private theorem mem_labelingPerm_support (l : GoodLabeling k A F) (a : α) :
    a ∈ (labelingPerm l).support ↔ ∃ i, l.2.val i = a := by
  rw [Equiv.Perm.mem_support]
  constructor
  · intro h
    by_contra h'
    exact h (l.1.val.viaFintypeEmbedding_apply_notMem_range (labelingEmbedding l) h')
  · rintro ⟨i, rfl⟩
    rw [labelingPerm_apply]
    exact (labelingEmbedding l).injective.ne (l.1.property i)
private noncomputable def labelingOrder (l : GoodLabeling k A F) :
    Fin k ≃ (labelingPerm l).support :=
  Equiv.ofBijective (fun i ↦ ⟨l.2.val i, (mem_labelingPerm_support l _).mpr ⟨i, rfl⟩⟩)
    ⟨fun _ _ h ↦ l.2.property.1 (congrArg Subtype.val h), fun a ↦ by
      obtain ⟨i, hi⟩ := (mem_labelingPerm_support l _).mp a.property
      exact ⟨i, Subtype.ext hi⟩⟩
private noncomputable def labelingSupport (l : GoodLabeling k A F) : GoodSupport k A F :=
  ⟨labelingPerm l, by
    constructor
    · simpa only [Fintype.card_coe, Fintype.card_fin] using
        (Fintype.card_congr (labelingOrder l)).symm
    · intro a ha
      obtain ⟨i, rfl⟩ := (mem_labelingPerm_support l a).mp ha
      rw [labelingPerm_apply]
      exact ⟨l.2.property.2.1 i, l.2.property.2.2 i⟩⟩
private def supportPositionPerm (s : GoodSupport k A F) (t : Fin k ≃ s.val.support) :
    Equiv.Perm (Fin k) :=
  t.symm.permCongr s.val.subtypePermOfSupport
private theorem supportPositionPerm_label (s : GoodSupport k A F) (t : Fin k ≃ s.val.support)
    (i : Fin k) : (t (supportPositionPerm s t i)).val = s.val (t i).val := by
  simp only [supportPositionPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl
private def supportLabeling (s : GoodSupport k A F) (t : Fin k ≃ s.val.support) :
    GoodLabeling k A F :=
  ⟨⟨supportPositionPerm s t, fun i hi ↦
      Equiv.Perm.mem_support.mp (t i).property
        ((supportPositionPerm_label s t i).symm.trans (congrArg (fun j ↦ (t j).val) hi))⟩,
    ⟨fun i ↦ (t i).val, Subtype.val_injective.comp t.injective,
      fun i ↦ (s.property.2 _ (t i).property).1, fun i ↦ by
        change (t (supportPositionPerm s t i)).val ∉ F (t i).val
        rw [supportPositionPerm_label]
        exact (s.property.2 _ (t i).property).2⟩⟩
private theorem labelingSupport_supportLabeling (s : GoodSupport k A F)
    (t : Fin k ≃ s.val.support) :
    labelingSupport (supportLabeling s t) = s := by
  apply Subtype.ext
  ext a
  change labelingPerm (supportLabeling s t) a = s.val a
  by_cases ha : a ∈ s.val.support
  · obtain ⟨i, hi⟩ := t.surjective ⟨a, ha⟩
    have hi' : (t i).val = a := congrArg Subtype.val hi
    rw [← hi']
    exact (labelingPerm_apply (supportLabeling s t) i).trans (supportPositionPerm_label s t i)
  · have hnot : a ∉ Set.range (labelingEmbedding (supportLabeling s t)) :=
      fun ⟨i, hi⟩ ↦ ha (hi ▸ (t i).property)
    exact ((supportLabeling s t).1.val.viaFintypeEmbedding_apply_notMem_range
      (labelingEmbedding (supportLabeling s t)) hnot).trans ((Equiv.Perm.notMem_support.mp ha).symm)
private noncomputable def supportOrderEquivFiber (s : GoodSupport k A F) :
    (Fin k ≃ s.val.support) ≃ {l : GoodLabeling k A F // labelingSupport l = s} := by
  let f (t : Fin k ≃ s.val.support) :
      {l : GoodLabeling k A F // labelingSupport l = s} :=
    ⟨supportLabeling s t, labelingSupport_supportLabeling s t⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro t u h
    exact Equiv.ext fun i ↦ Subtype.ext (congrArg (fun z ↦ z.val.2.val i) h)
  · rintro ⟨l, rfl⟩
    refine ⟨labelingOrder l, Subtype.ext (Sigma.subtype_ext ?_ rfl)⟩
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply (labelingEmbedding l).injective
    exact (supportPositionPerm_label (labelingSupport l) (labelingOrder l) i).trans
      (labelingPerm_apply l i)
private theorem card_supportFiber (s : GoodSupport k A F) :
    Nat.card {l : GoodLabeling k A F // labelingSupport l = s} = k.factorial := by
  classical
  let t : Fin k ≃ s.val.support := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, s.property.1])
  rw [← Nat.card_congr (supportOrderEquivFiber s), Nat.card_eq_fintype_card,
    ← Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin k)) t), Fintype.card_perm,
    Fintype.card_fin]
open scoped Classical in
theorem sum_iidLabelGood_eq_factorial_mul_sum_support
    (k : ℕ) (r : α → ℝ≥0∞) (A : Finset α) (F : α → Finset α) :
    (∑ e : derangements (Fin k),
      ∑ x ∈ Finset.univ.filter
        (fun x ↦ x ∈ iidLabelGood (A : Set α) (fun a ↦ ↑(F a)) e.val),
          ∏ i, r (x i)) =
      (k.factorial : ℝ≥0∞) * ∑ σ ∈ Finset.univ.filter
        (fun σ : Equiv.Perm α ↦ σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i),
          ∏ i ∈ σ.support, r i := by
  let W (s : GoodSupport k A F) : ℝ≥0∞ := ∏ i ∈ s.val.support, r i
  have hw (l : GoodLabeling k A F) : (∏ i, r (l.2.val i)) = W (labelingSupport l) := by
    calc
      _ = ∏ j : (labelingPerm l).support, r j.val :=
        Fintype.prod_equiv (labelingOrder l) (fun i ↦ r (l.2.val i))
          (fun j ↦ r j.val) (fun _ ↦ rfl)
      _ = _ := Finset.prod_coe_sort _ r
  calc
    _ = ∑ l : GoodLabeling k A F, ∏ i, r (l.2.val i) := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      exact Finset.sum_subtype _ (fun _ ↦ by simp) _
    _ = ∑ l : GoodLabeling k A F, W (labelingSupport l) :=
      Finset.sum_congr rfl (fun l _ ↦ hw l)
    _ = ∑ s : GoodSupport k A F, ∑ l : {l // labelingSupport l = s}, W (labelingSupport l.val) :=
      (Fintype.sum_fiberwise labelingSupport (fun l ↦ W (labelingSupport l))).symm
    _ = ∑ s : GoodSupport k A F, (k.factorial : ℝ≥0∞) * W s := by
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      have hc : Fintype.card {l // labelingSupport l = s} = k.factorial :=
        (Nat.card_eq_fintype_card.symm.trans (card_supportFiber s))
      calc
        _ = ∑ _l : {l // labelingSupport l = s}, W s :=
          Finset.sum_congr rfl (fun l _ ↦ congrArg W l.property)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
    _ = _ := by
      have h : (∑ s : GoodSupport k A F, W s) = ∑ σ ∈ Finset.univ.filter
          (fun σ : Equiv.Perm α ↦ σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i),
            ∏ i ∈ σ.support, r i := (Finset.sum_subtype
        (Finset.univ.filter (fun σ : Equiv.Perm α ↦
          σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i))
        (fun σ ↦ Finset.mem_filter_univ σ) (fun σ ↦ ∏ i ∈ σ.support, r i)).symm
      rw [← Finset.mul_sum, h]
end DiagLP
end

-- PivotReverseMaskLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
open scoped Classical in
private noncomputable def goodReverseSupportPermutations {n : ℕ} (k : ℕ)
    (A : Finset (Fin n)) (F : Fin n → Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ ↦ σ.support.card = k ∧
    ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i
theorem mem_goodReverseSupportPermutations {n k : ℕ} {A : Finset (Fin n)}
    {F : Fin n → Finset (Fin n)} {σ : Matching n} :
    σ ∈ goodReverseSupportPermutations k A F ↔ σ.support.card = k ∧
      ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i := by
  classical
  simp [goodReverseSupportPermutations]
private noncomputable def reverseGoodLabelLoss {n : ℕ} (k : ℕ) (r : Fin n → ℝ≥0∞)
    (A : Finset (Fin n)) (η : ℝ≥0∞) : ℝ≥0∞ :=
  (k.choose 2 : ℝ≥0∞) * (∑ i, (r i) ^ 2) + (k : ℝ≥0∞) * (∑ i ∈ A, r i) + k * η
private noncomputable def forwardMaskForbiddenTargets {n : ℕ} (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ ¬ ∃ q : ForwardInactiveColumnIndex flag (μ.symm i),
    q.val.val.val.1 = μ.symm j
theorem notMem_forwardMaskForbiddenTargets_iff {n : ℕ} (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n) :
    j ∉ forwardMaskForbiddenTargets μ flag i ↔
      ∃ q : ForwardInactiveColumnIndex flag (μ.symm i), q.val.val.val.1 = μ.symm j := by
  classical
  simp [forwardMaskForbiddenTargets]
private noncomputable def realizedReversePermutationCount {n : ℕ} (S : Finset (Matching n))
    (p : Profile n) (M : Matching n) : ℕ := by
  classical
  exact (S.filter (RealizesSuccessorPermutation p M)).card
theorem lintegral_realizedReversePermutationCount {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (hP : Measurable P) (M : Matching n)
    (S : Finset (Matching n)) :
    (∫⁻ z, (realizedReversePermutationCount S (P z) M : ℝ≥0∞) ∂ν) =
      ∑ σ ∈ S, ν {z | RealizesSuccessorPermutation (P z) M σ} := by
  classical
  let E (σ : Matching n) : Set Ω := {z | RealizesSuccessorPermutation (P z) M σ}
  have hm (σ : Matching n) : MeasurableSet (E σ) :=
    hP (MeasurableSet.of_discrete : MeasurableSet {p : Profile n |
      RealizesSuccessorPermutation p M σ})
  have hpoint (z : Ω) : (realizedReversePermutationCount S (P z) M : ℝ≥0∞) =
      ∑ σ ∈ S, (E σ).indicator (fun _ ↦ (1 : ℝ≥0∞)) z := by
    calc
      _ = ∑ σ ∈ S.filter (RealizesSuccessorPermutation (P z) M), (1 : ℝ≥0∞) := by
        simp [realizedReversePermutationCount]
      _ = _ := by simp only [Finset.sum_filter, Set.indicator_apply, E, Set.mem_ofPred_eq]
  simp_rw [hpoint]
  rw [lintegral_finsetSum _ (fun σ _ ↦ measurable_const.indicator (hm σ))]
  exact Finset.sum_congr rfl fun σ _ ↦ lintegral_indicator_one (hm σ)
private noncomputable def reverseSpouseWeights {n : ℕ} (μ : Matching n) (d : DiagonalScorePairs n) :
    Fin n → ℝ≥0∞ := fun j ↦
  ENNReal.ofReal ((diagonalPairAt d (μ.symm j)).1 / ∑ i, (diagonalPairAt d i).1)
theorem sum_reverseSpouseWeights {n : ℕ} (μ : Matching n) (d : DiagonalScorePairs n)
    (hx : ∀ i, 0 ≤ (diagonalPairAt d i).1) (hX : 0 < ∑ i, (diagonalPairAt d i).1) :
    ∑ i, reverseSpouseWeights μ d i = 1 := by
  let X := ∑ i, (diagonalPairAt d i).1
  let w (i : Fin n) := (diagonalPairAt d (μ.symm i)).1 / X
  change (∑ i, ENNReal.ofReal (w i)) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ div_nonneg (hx _) hX.le),
    ← Fintype.sum_equiv μ (fun i ↦ (diagonalPairAt d i).1 / X) w
      (fun i ↦ by simp only [w, Equiv.symm_apply_apply]), ← Finset.sum_div,
    div_self hX.ne', ENNReal.ofReal_one]
end DiagLP
end

-- PivotReverseCompetitorMass
section
open StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private theorem sum_subtype_ne_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (j : α) :
    (∑ i : {i // i ≠ j}, f i.val) = (∑ i, f i) - f j := by
  have h := Finset.sum_erase_add (Finset.univ : Finset α) f (Finset.mem_univ j)
  rw [Finset.sum_subtype (p := fun x ↦ x ≠ j) _ (by simp) f] at h
  exact eq_sub_of_add_eq h
private theorem sum_subtype_bool_eq {α : Type*} [Fintype α] (b : α → Bool)
    (f : α → ℝ) :
    (∑ i : {i // b i = true}, f i.val) = (∑ i, if b i then f i else 0) := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm
private noncomputable def forwardMaskOmittedMass {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) : ℝ :=
  ∑ i : {i : Fin n // i ≠ j}, if flag ⟨(i.val, j), i.property⟩ then
    (diagonalPairAt d i.val).1 else 0
private def inactiveColumnEquiv {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) :
    ForwardInactiveColumnIndex flag j ≃
      {i : {i : Fin n // i ≠ j} // flag ⟨(i.val, j), i.property⟩ ≠ true} where
  toFun q := by
    let i : {i : Fin n // i ≠ j} := ⟨forwardInactiveColumnMan q, fun h ↦
      q.val.val.property (h.trans q.property.symm)⟩
    have hcell : (⟨(i.val, j), i.property⟩ : OffDiagonalCellIndex n) = q.val.val :=
      Subtype.ext (Prod.ext rfl q.property.symm)
    exact ⟨i, by rw [hcell]; exact q.val.property⟩
  invFun i := ⟨⟨⟨(i.val.val, j), i.val.property⟩, i.property⟩, rfl⟩
  left_inv q := forwardInactiveColumnMan_injective flag j rfl
  right_inv i := Subtype.ext (Subtype.ext rfl)
theorem sum_forwardInactiveColumn_eq {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) :
    (∑ q : ForwardInactiveColumnIndex flag j, forwardInactiveColumnThreshold d q) =
      (∑ i, (diagonalPairAt d i).1) - (diagonalPairAt d j).1 -
        forwardMaskOmittedMass d flag j := by
  classical
  let b (i : {i : Fin n // i ≠ j}) := flag ⟨(i.val, j), i.property⟩
  let f (i : Fin n) := (diagonalPairAt d i).1
  have ha : (∑ i : {i // b i = true}, f i.val.val) = forwardMaskOmittedMass d flag j :=
    sum_subtype_bool_eq b (fun i ↦ f i.val)
  have hi :
      (∑ q : ForwardInactiveColumnIndex flag j, forwardInactiveColumnThreshold d q) =
        ∑ i : {i // ¬ b i = true}, f i.val.val :=
    (inactiveColumnEquiv flag j).sum_comp (fun i ↦ f i.val.val)
  have h := Fintype.sum_subtype_add_sum_subtype (fun i ↦ b i = true) (fun i ↦ f i.val)
  rw [ha, ← hi, sum_subtype_ne_eq] at h
  linarith only [h]
theorem sum_forwardInactiveCompetitor_eq {n : ℕ} (d : DiagonalScorePairs n)
    {flag : OffDiagonalCellIndex n → Bool} {j : Fin n}
    (q : ForwardInactiveColumnIndex flag j) :
    (∑ t : {t : ForwardInactiveColumnIndex flag j // t ≠ q},
      forwardInactiveColumnThreshold d t.val) =
      (∑ i, (diagonalPairAt d i).1) - (diagonalPairAt d j).1 -
        forwardMaskOmittedMass d flag j - forwardInactiveColumnThreshold d q := by
  rw [sum_subtype_ne_eq, sum_forwardInactiveColumn_eq]
theorem forwardKeptCompetitorMass_ge {n : ℕ} (d : DiagonalScorePairs n)
    {flag : OffDiagonalCellIndex n → Bool} {P : Finset (Fin n)} {j : Fin n}
    (t : ForwardKeptColumnIndex flag P j) (hx : ∀ i, 0 ≤ (diagonalPairAt d i).1) :
    (∑ i, (diagonalPairAt d i).1) - (diagonalPairAt d j).1 -
        forwardMaskOmittedMass d flag j - (∑ i ∈ P, (diagonalPairAt d i).1) -
        forwardInactiveColumnThreshold d t.val ≤ forwardKeptCompetitorMass d t := by
  classical
  let f (i : Fin n) := (diagonalPairAt d i).1
  let g (q : ForwardInactiveColumnIndex flag j) := forwardInactiveColumnThreshold d q
  let p (q : ForwardInactiveColumnIndex flag j) := forwardInactiveColumnMan q ∉ P
  let e (q : {q // ¬ p q}) := forwardInactiveColumnMan q.val
  have hinj : Function.Injective e := fun _ _ h ↦
    Subtype.ext (forwardInactiveColumnMan_injective flag j h)
  have hsubset : Finset.univ.image e ⊆ P := by
    intro i hi
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hi
    exact not_not.mp q.property
  have homit : (∑ q : {q // ¬ p q}, g q.val) ≤ ∑ i ∈ P, f i := calc
    _ = ∑ i ∈ Finset.univ.image e, f i :=
      (Finset.sum_image fun _ _ _ _ h ↦ hinj h).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ ↦ hx i)
  have hsplit := Fintype.sum_subtype_add_sum_subtype p g
  change (∑ q : {q // p q}, g q.val) + (∑ q : {q // ¬ p q}, g q.val) =
    (∑ q : ForwardInactiveColumnIndex flag j, forwardInactiveColumnThreshold d q) at hsplit
  rw [sum_forwardInactiveColumn_eq] at hsplit
  have htarget := sum_subtype_ne_eq (fun q : {q // p q} ↦ g q.val) t
  change _ ≤ ∑ q : {q : {q // p q} // q ≠ t}, g q.val.val
  linarith only [homit, hsplit, htarget]
theorem sum_forwardMaskForbiddenTargets_reverseSpouseWeights {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) (w : Fin n)
    (hx : ∀ i, 0 ≤ (diagonalPairAt d i).1) (hX : 0 < ∑ i, (diagonalPairAt d i).1) :
    (∑ i ∈ forwardMaskForbiddenTargets μ flag w, reverseSpouseWeights μ d i) =
      ENNReal.ofReal (((diagonalPairAt d (μ.symm w)).1 +
        forwardMaskOmittedMass d flag (μ.symm w)) / (∑ i, (diagonalPairAt d i).1)) := by
  classical
  let F := forwardMaskForbiddenTargets μ flag w
  let f (i : Fin n) := (diagonalPairAt d i).1
  let X := ∑ i, f i
  let j := μ.symm w
  let a (q : ForwardInactiveColumnIndex flag j) := μ (forwardInactiveColumnMan q)
  have hinj : Function.Injective a := fun _ _ h ↦
    forwardInactiveColumnMan_injective flag j (μ.injective h)
  have himage : Finset.univ.image a = Fᶜ := by
    ext i
    rw [Finset.mem_image, Finset.mem_compl]
    constructor
    · rintro ⟨q, _, rfl⟩
      exact (notMem_forwardMaskForbiddenTargets_iff μ flag w _).mpr
        ⟨q, (μ.symm_apply_apply _).symm⟩
    · intro hi
      obtain ⟨q, hq⟩ := (notMem_forwardMaskForbiddenTargets_iff μ flag w i).mp hi
      exact ⟨q, Finset.mem_univ _, (congrArg μ hq).trans (μ.apply_symm_apply i)⟩
  have hinactive : (∑ i ∈ Fᶜ, f (μ.symm i)) =
      ∑ q : ForwardInactiveColumnIndex flag j, forwardInactiveColumnThreshold d q := calc
    _ = ∑ i ∈ Finset.univ.image a, f (μ.symm i) := by rw [himage]
    _ = _ := by
      rw [Finset.sum_image fun _ _ _ _ h ↦ hinj h]
      simp only [a, Equiv.symm_apply_apply, f, forwardInactiveColumnThreshold]
  have htotal : (∑ i, f (μ.symm i)) = X := μ.symm.sum_comp f
  have hsplit := Finset.sum_add_sum_compl F (fun i ↦ f (μ.symm i))
  rw [hinactive, htotal, sum_forwardInactiveColumn_eq] at hsplit
  have hF : (∑ i ∈ F, f (μ.symm i)) = f j + forwardMaskOmittedMass d flag j := by
    linarith only [hsplit]
  change (∑ i ∈ F, ENNReal.ofReal (f (μ.symm i) / X)) =
    ENNReal.ofReal ((f j + forwardMaskOmittedMass d flag j) / X)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ div_nonneg (hx (μ.symm i)) hX.le),
    ← Finset.sum_div, hF]
end DiagLP
end

-- PivotForwardMaskProbability
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
private noncomputable def forwardCellFlag (x y : ℝ) (z : ℝ × ℝ) : Bool := by
  classical
  exact decide (z ∈ forwardEligibleScoreCell x y)
@[simp] theorem forwardCellFlag_eq_true {x y : ℝ} {z : ℝ × ℝ} :
    forwardCellFlag x y z = true ↔ z ∈ forwardEligibleScoreCell x y := by
  classical
  simp [forwardCellFlag]
private noncomputable def forwardMaskOfScores {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (q : OffDiagonalCellIndex n) : Bool :=
  forwardCellFlag (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (z q)
theorem forwardMaskOfScores_eq_iff {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    forwardMaskOfScores d z = flag ↔ z ∈ forwardScoreMaskEvent d flag := by
  rw [funext_iff, forwardScoreMaskEvent, mem_univ_pi]
  apply forall_congr'
  intro q
  cases flag q with
  | false =>
    simp [forwardScoreCellFlagEvent, forwardMaskOfScores, ← Bool.not_eq_true]
  | true =>
    simp [forwardScoreCellFlagEvent, forwardMaskOfScores]
end DiagLP
end

-- PivotForwardRevealRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
private abbrev ForwardRevealedMaleScores {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  ForwardActiveCellIndex flag → ℝ
private abbrev ForwardInactiveColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  (i : Fin n) → ForwardInactiveColumnIndex flag i → ℝ × ℝ
private def forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    OffDiagonalScorePairs n → ForwardRevealedMaleScores flag × ForwardInactiveColumns flag :=
  Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag
theorem measurable_forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (forwardRevealWithColumns flag) :=
  (measurable_id.prodMap (forwardInactiveColumnsEquiv flag).measurable).comp
    (measurable_forwardScoreMaskRevealAndInactive flag)
end DiagLP
end

-- PivotForwardPivotReadout
section
open MeasureTheory Set StableMarriage
namespace DiagLP
private noncomputable def forwardPivotIncrement {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n)
    (a : ForwardRevealedMaleScores flag) (m : Fin n) : ℝ :=
  if hm : ρ m ≠ m then
    let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    if hq : flag q = true then a ⟨q, hq⟩ - (diagonalPairAt d m).1 else 0
  else 0
theorem measurable_forwardPivotIncrement {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (m : Fin n) :
    Measurable (fun a ↦ forwardPivotIncrement d flag ρ a m) := by
  by_cases hm : ρ m ≠ m
  · let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    by_cases hq : flag q = true
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = true := hq
      have he : Measurable (fun a : ForwardRevealedMaleScores flag ↦ a ⟨q, hq⟩) :=
        measurable_pi_apply _
      simpa only [forwardPivotIncrement, dif_pos hm, dif_pos hq'] using
        he.sub_const (diagonalPairAt d m).1
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) ≠ true := hq
      simp only [forwardPivotIncrement, dif_pos hm, dif_neg hq']
      exact measurable_const
  · simp only [forwardPivotIncrement, dif_neg hm]
    exact measurable_const
end DiagLP
end

-- SingletonIdealAnchor
section
namespace DiagLP
variable {α : Type*} [PartialOrder α]
end DiagLP
end

-- SingletonRotationAnchor
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
end DiagLP
end

-- ReverseRotationIdeals
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ : Equiv.Perm (Fin n)}
private def IsReverseExposedRotation (p : Profile n) (ν : Matching n) (σ : Equiv.Perm (Fin n)) : Prop :=
  IsExposedRotation (swapProfile p) ν.symm σ
private def undoReverseRotation (ν : Matching n) (σ : Equiv.Perm (Fin n)) : Matching n :=
  (eliminateRotation ν.symm σ).symm
theorem IsReverseExposedRotation.undo_stable
    (hσ : IsReverseExposedRotation p ν σ) (hν : IsStable p ν) :
    IsStable p (undoReverseRotation ν σ) := by
  apply isStable_swapProfile_iff.mp
  simpa only [undoReverseRotation, Equiv.symm_symm] using
    (show IsExposedRotation (swapProfile p) ν.symm σ from hσ).isStable_eliminate
      (isStable_swapProfile_iff.mpr hν)
end DiagLP
end

-- PivotCrossBlocker
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}
private def IsPivotCrossBlocker (p : Profile n) (A N : Matching n) (ρ : Equiv.Perm (Fin n))
    (m w : Fin n) : Prop :=
  ρ m ≠ m ∧ N.symm w ≠ A.symm w ∧
    p.manRank m w < p.manRank m (A (ρ m)) ∧ p.womanRank w m < p.womanRank w (N.symm w)
private theorem IsPivotCrossBlocker.old_partner_ne {m w : Fin n}
    (h : IsPivotCrossBlocker p A N ρ m w) (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    A m ≠ w := by
  rintro rfl
  apply h.2.1
  rw [← hfixed m h.1, N.symm_apply_apply, hfixed m h.1, A.symm_apply_apply]
theorem IsPivotCrossBlocker.manRank_old_lt {m w : Fin n}
    (h : IsPivotCrossBlocker p A N ρ m w) (hN : IsStable p N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    p.manRank m (A m) < p.manRank m w := by
  have hne := h.old_partner_ne hfixed
  have hnot : ¬ p.manRank m w < p.manRank m (A m) := fun hlt ↦
    hN m w ⟨(hfixed m h.1).trans_ne hne, (hfixed m h.1).symm ▸ hlt, h.2.2.2⟩
  exact lt_of_le_of_ne (le_of_not_gt hnot) (fun heq ↦ hne ((p.manRank m).injective heq))
theorem IsPivotCrossBlocker.womanRank_old_lt {m w : Fin n}
    (h : IsPivotCrossBlocker p A N ρ m w) (hρ : IsExposedRotation p A ρ)
    (hN : IsStable p N) (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    p.womanRank w (A.symm w) < p.womanRank w m := by
  have hnot : ¬ p.womanRank w m < p.womanRank w (A.symm w) := fun hlt ↦
    (not_lt_of_ge ((IsSuccessor.min_rank ((IsExposedRotation.successor hρ) m h.1)) w ⟨h.manRank_old_lt hN hfixed, hlt⟩)) h.2.2.1
  apply lt_of_le_of_ne (le_of_not_gt hnot)
  intro heq
  have hh := (p.womanRank w).injective heq
  exact h.old_partner_ne hfixed ((congrArg A hh).symm.trans (A.apply_symm_apply w))
theorem isExposedRotation_iff_no_pivotCrossBlocker
    (hρ : IsExposedRotation p A ρ) (hN : IsStable p N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    IsExposedRotation p N ρ ↔ ∀ m w, ¬ IsPivotCrossBlocker p A N ρ m w := by
  constructor
  · intro he m w h
    have ht := hfixed (ρ m) (ρ.injective.ne h.1)
    have hman : p.manRank m (N m) < p.manRank m w := by
      rw [hfixed m h.1]
      exact h.manRank_old_lt hN hfixed
    have hle := (IsSuccessor.min_rank ((IsExposedRotation.successor he) m h.1)) w ⟨hman, h.2.2.2⟩
    rw [ht] at hle
    exact (not_lt_of_ge hle) h.2.2.1
  · intro h
    refine (IsExposedRotation.mk ((IsExposedRotation.isCycle hρ)) (fun m hm ↦ ?_))
    have hold := hfixed m hm
    have ht := hfixed (ρ m) (ρ.injective.ne hm)
    have hs := (IsExposedRotation.successor hρ) m hm
    constructor
    · constructor
      · simpa only [hold, ht] using (IsSuccessor.eligible hs).1
      · have hinv := N.symm_apply_apply (ρ m)
        rw [ht] at hinv
        simpa only [ht, hinv, Equiv.symm_apply_apply] using (IsSuccessor.eligible hs).2
    · intro w hw
      by_cases hw' : N.symm w = A.symm w
      · have hwA : IsEligibleSuccessor p A m w :=
          ⟨by simpa only [hold] using hw.1, by simpa only [hw'] using hw.2⟩
        simpa only [ht] using (IsSuccessor.min_rank hs) w hwA
      · apply le_of_not_gt
        intro hlt
        exact h m w ⟨hm, hw', by simpa only [ht] using hlt, hw.2⟩
private def IsPivotCrossRectangle (x : ScoreProfile n) (A N : Matching n)
    (ρ : Equiv.Perm (Fin n)) (m w : Fin n) : Prop :=
  ρ m ≠ m ∧ N.symm w ≠ A.symm w ∧
    x (.inl m) (A m) < x (.inl m) w ∧ x (.inl m) w < x (.inl m) (A (ρ m)) ∧
    x (.inr w) (A.symm w) < x (.inr w) m ∧ x (.inr w) m < x (.inr w) (N.symm w)
theorem isPivotCrossBlocker_iff_score_rectangle {x : ScoreProfile n}
    (hx : ∀ i, Function.Injective (x i))
    (hρ : IsExposedRotation (profileOfScores x) A ρ) (hN : IsStable (profileOfScores x) N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) (m w : Fin n) :
    IsPivotCrossBlocker (profileOfScores x) A N ρ m w ↔ IsPivotCrossRectangle x A N ρ m w := by
  let hm := rankPermutation_lt_iff (hx (.inl m))
  let hw := rankPermutation_lt_iff (hx (.inr w))
  exact ⟨fun h ↦ ⟨h.1, h.2.1, (hm _ _).mp (h.manRank_old_lt hN hfixed),
    (hm _ _).mp h.2.2.1, (hw _ _).mp (h.womanRank_old_lt hρ hN hfixed), (hw _ _).mp h.2.2.2⟩,
    fun ⟨ha, hb, _, hc, _, hd⟩ ↦ ⟨ha, hb, (hm _ _).mpr hc, (hw _ _).mpr hd⟩⟩
theorem isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle {x : ScoreProfile n}
    (hx : ∀ i, Function.Injective (x i))
    (hρ : IsExposedRotation (profileOfScores x) A ρ) (hN : IsScoreStable x N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    IsExposedRotation (profileOfScores x) N ρ ↔
      ∀ m w, ¬ IsPivotCrossRectangle x A N ρ m w := by
  have hstable := (isStable_profileOfScores_iff hx N).mpr hN
  simpa only [isPivotCrossBlocker_iff_score_rectangle hx hρ hstable hfixed] using
    isExposedRotation_iff_no_pivotCrossBlocker hρ hstable hfixed
end DiagLP
end

-- PivotReversePermutationCompatibility
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ ρ σ : Matching n}
theorem RealizesSuccessorPermutation.womanRank_eliminate_le
    (hσ : RealizesSuccessorPermutation p μ σ) (w : Fin n) :
    p.womanRank w ((eliminateRotation μ σ).symm w) ≤ p.womanRank w (μ.symm w) :=
  let ⟨m, hm⟩ := (eliminateRotation μ σ).surjective w
  have hle : p.womanRank (μ (σ m)) m ≤ p.womanRank (μ (σ m)) (σ m) :=
    if he : σ m = m then (congrArg (p.womanRank (μ (σ m))) he.symm).le
    else by simpa only [Equiv.symm_apply_apply] using
      (IsSuccessor.eligible (hσ m (Equiv.Perm.mem_support.mpr he))).2.le
  have htarget : p.womanRank (eliminateRotation μ σ m)
      ((eliminateRotation μ σ).symm (eliminateRotation μ σ m)) ≤
        p.womanRank (eliminateRotation μ σ m) (μ.symm (eliminateRotation μ σ m)) := by
    have hinv : (eliminateRotation μ σ).symm (μ (σ m)) = m :=
      (eliminateRotation μ σ).symm_apply_apply m
    simpa only [eliminateRotation_apply, hinv, Equiv.symm_apply_apply] using hle
  hm ▸ htarget
theorem RealizesSuccessorPermutation.isStable_eliminate
    (hσ : RealizesSuccessorPermutation p μ σ) (hμ : IsStable p μ) :
    IsStable p (eliminateRotation μ σ) :=
  fun m w hb ↦
    have hwOld : p.womanRank w m < p.womanRank w (μ.symm w) :=
      hb.2.2.trans_le (hσ.womanRank_eliminate_le w)
    have hne : μ m ≠ w := fun h ↦ (ne_of_lt hwOld)
      (congrArg (p.womanRank w) ((μ.symm_apply_apply m).symm.trans (congrArg μ.symm h)))
    have hnot : ¬ p.manRank m w < p.manRank m (μ m) := fun h ↦
      hμ m w ⟨hne, h, hwOld⟩
    if hm : σ m = m then
      hnot (by simpa only [eliminateRotation_apply, hm] using hb.2.1)
    else
      have hbelow : p.manRank m (μ m) < p.manRank m w :=
        lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank m).injective he))
      (not_lt_of_ge ((IsSuccessor.min_rank (hσ m (Equiv.Perm.mem_support.mpr hm))) w ⟨hbelow, hwOld⟩)) hb.2.1
theorem RealizesSuccessorPermutation.undo_stable
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) (hμ : IsStable p μ) :
    IsStable p (undoReverseRotation μ σ) :=
  isStable_swapProfile_iff.mp (hσ.isStable_eliminate (isStable_swapProfile_iff.mpr hμ))
theorem undoReverseRotation_symm_apply (μ σ : Matching n) (w : Fin n) :
    (undoReverseRotation μ σ).symm w = μ.symm (σ w) :=
  rfl
theorem undoReverseRotation_apply_of_not_mem_support {m : Fin n} (hm : μ m ∉ σ.support) :
    undoReverseRotation μ σ m = μ m :=
  (undoReverseRotation μ σ).symm.injective <| calc
    (undoReverseRotation μ σ).symm (undoReverseRotation μ σ m) = m :=
      (undoReverseRotation μ σ).symm_apply_apply m
    _ = μ.symm (μ m) := (μ.symm_apply_apply m).symm
    _ = (undoReverseRotation μ σ).symm (μ m) := by
      rw [undoReverseRotation_symm_apply, Equiv.Perm.notMem_support.mp hm]
end DiagLP
end

-- ReverseSupportWeightUpper
section
open scoped BigOperators ENNReal
namespace DiagLP
theorem sum_supportPermutation_weights_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (r : α → ℝ≥0∞) (hr : ∑ i, r i = 1) :
    (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm α)).filter (fun σ ↦ σ.support.card = k),
      ∏ i ∈ σ.support, r i) ≤ 1 := by
  classical
  have hfac : (k.factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  apply (ENNReal.mul_le_mul_iff_right hfac (ENNReal.natCast_ne_top _)).mp
  rw [mul_one]
  calc
    _ = ∑ e : derangements (Fin k),
        ∑ x ∈ Finset.univ.filter
          (fun x ↦ x ∈ iidLabelGood (∅ : Set α) (fun _ ↦ ∅) e.val), ∏ i, r (x i) := by
      simpa using (sum_iidLabelGood_eq_factorial_mul_sum_support k r ∅ (fun _ ↦ ∅)).symm
    _ ≤ ∑ _e : derangements (Fin k), (1 : ℝ≥0∞) :=
      Finset.sum_le_sum fun e _ ↦ calc
        _ ≤ ∑ x : Fin k → α, ∏ i, r (x i) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = 1 := by rw [← Fintype.prod_sum]; simp [hr]
    _ = (Fintype.card (derangements (Fin k)) : ℝ≥0∞) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ ≤ _ := by
      have h := Fintype.card_subtype_le (fun e : Equiv.Perm (Fin k) ↦ e ∈ derangements (Fin k))
      rw [Fintype.card_perm, Fintype.card_fin] at h
      exact_mod_cast h
end DiagLP
end

-- PivotCompatibilityLoss
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private structure ReverseCompatibilityControls {n : ℕ} (μ ρ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (U : Set (ForwardRevealedMaleScores flag))
    (a D : ℝ) : Prop where
  measurable_reveal : MeasurableSet U
  female_nonneg : ∀ i, 0 ≤ (diagonalPairAt d i).2
  female_lt_one : ∀ i, (diagonalPairAt d i).2 < 1
  male_mem : ∀ i, (diagonalPairAt d i).1 ∈ Icc 0 1
  male_total_pos : 0 < ∑ i, (diagonalPairAt d i).1
  inflation_pos : 0 < a
  kept_mass : ∀ i (t : ForwardKeptColumnIndex flag ρ.support i),
    (∑ j, (diagonalPairAt d j).1) / a ≤ forwardKeptCompetitorMass d t
  increment_nonneg : ∀ v ∈ U, ∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement d flag ρ v m
  increment_sum_le : ∀ v ∈ U, (∑ m ∈ ρ.support, forwardPivotIncrement d flag ρ v m) ≤ D
  tie_free : ∀ᵐ z ∂(offDiagonalScoreLaw n),
    ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)
  pivot_exposed : ∀ᵐ z ∂forwardMaskRevealLaw d flag U,
    IsExposedRotation (profileOfScores ((splitScorePairs μ).symm (d, z))) μ ρ
end DiagLP
end

-- RotationUndoSequences
section
open StableMarriage
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {hopt : IsManOptimal p μ₀}
end DiagLP
end

-- PivotCompatibleLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private def memFinset {α : Type} {S : Finset α} {Q : α → Prop} (_ : ∀ {σ}, σ ∈ S ↔ Q σ) := S
private noncomputable def compatibleReversePermutations {n : ℕ} (S : Finset (Matching n))
    (p : Profile n) (μ ρ : Matching n) : Finset (Matching n) :=
  memFinset (@MarkedLP.mem_compatibleReversePermutations n S p μ ρ)
private def premise {A B : Prop} (_ : A → B) := A
private abbrev SourceSuccessor {n} (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  premise (@MarkedLP.IsSuccessor.unique n p μ m w w)
private lemma sourceSuccessor_iff {n} (p : Profile n) (μ : Matching n) (m w : Fin n) :
    SourceSuccessor p μ m w ↔ IsSuccessor p μ m w := by
  constructor
  · rintro ⟨he,hm⟩
    exact (IsSuccessor.mk (he) (hm))
  · rintro ⟨he,hm⟩
    constructor <;> assumption
private abbrev SourceExposed {n} (p : Profile n) (μ ρ : Matching n) : Prop :=
  premise (@MarkedLP.IsExposedRotation.womanRank_eliminate_le n p μ ρ)
private lemma sourceExposed_iff {n} (p : Profile n) (μ ρ : Matching n) :
    SourceExposed p μ ρ ↔ IsExposedRotation p μ ρ := by
  constructor
  · rintro ⟨hc,hs⟩
    exact (IsExposedRotation.mk (hc) (fun m hm => (sourceSuccessor_iff ..).mp (hs m hm)))
  · rintro ⟨hc,hs⟩
    constructor
    · exact hc
    · exact fun m hm => (sourceSuccessor_iff ..).mpr (hs m hm)
theorem mem_compatibleReversePermutations {n : ℕ} {S : Finset (Matching n)}
    {p : Profile n} {μ ρ σ : Matching n} : σ ∈ compatibleReversePermutations S p μ ρ ↔
    σ ∈ S ∧ RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
      IsExposedRotation p (undoReverseRotation μ σ) ρ := by
  apply (MarkedLP.mem_compatibleReversePermutations (S:=S) (p:=p) (μ:=μ) (ρ:=ρ) (σ:=σ)).trans
  apply and_congr_right
  intro _
  refine and_congr ?_ (sourceExposed_iff ..)
  exact forall_congr' fun i => forall_congr' fun _ => sourceSuccessor_iff ..
private structure ReverseUnfilteredControls {n : ℕ} (μ ρ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (K : ℕ) (η : ℝ≥0∞) : Prop where
  forbidden_weight : ∀ i,
    ∑ j ∈ forwardMaskForbiddenTargets μ flag i, reverseSpouseWeights μ d j ≤ η
  label_loss : ∀ k ∈ Finset.Icc 2 K,
    reverseGoodLabelLoss k (reverseSpouseWeights μ d) (ρ.support.map μ.toEmbedding) η ≤
      ENNReal.ofReal (1 / 4)
  cumulative_error : (K : ℝ) * reverseLowerArcError (∑ i, (diagonalPairAt d i).1) ≤ 1 / 4
private noncomputable def compatibleReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k : ℕ) (p : Profile n) : Finset (Matching n) :=
  compatibleReversePermutations
    (goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
      (forwardMaskForbiddenTargets μ flag)) p μ ρ
end DiagLP
end

-- PivotReverseIncrementFilter
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private def reverseScoreIncrement {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (w j : Fin n) : ℝ := x (.inr w) j - x (.inr w) (μ.symm w)
theorem measurable_reverseScoreIncrement {n : ℕ} (μ : Matching n) (w j : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ reverseScoreIncrement x μ w j) := by
  have hrow : Measurable (fun x : ScoreProfile n ↦ x (.inr w)) := measurable_pi_apply _
  exact ((measurable_pi_apply j).comp hrow).sub ((measurable_pi_apply (μ.symm w)).comp hrow)
theorem measurable_fixedDiagonalReconstruction {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) :
    Measurable (fun z : OffDiagonalScorePairs n ↦ (splitScorePairs μ).symm (d, z)) :=
  (splitScorePairs μ).symm.measurable.comp (measurable_const.prodMk measurable_id)
private noncomputable def reverseIncrementCutoff (n : ℕ) (X : ℝ) : ℝ := 16 * Real.log (n : ℝ) / X
end DiagLP
end

-- PivotReverseFilteredCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private def shortCycleCapBad (L : ℕ) (T : Multiset ℕ) : Prop :=
  (3 / 2 : ℝ) * Real.log (L : ℝ) < ((T.filter (· ≤ L)).card : ℝ)
private def reverseCollectionIncrementGood {n : ℕ} (x : ScoreProfile n) (μ σ : Matching n)
    (t : ℝ) : Prop :=
  ∀ w ∈ σ.support, reverseScoreIncrement x μ w (μ.symm (σ w)) ≤ t
private noncomputable def filteredReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact (compatibleReverseSupportFamily μ ρ flag k (profileOfScores x)).filter fun σ ↦
    (¬ shortCycleCapBad L σ.cycleType) ∧ reverseCollectionIncrementGood x μ σ t
theorem measurable_finsetCard_of_mem {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (F : Ω → Finset α) (hF : ∀ a, MeasurableSet {z | a ∈ F z}) :
    Measurable (fun z ↦ ((F z).card : ℝ≥0∞)) := by
  classical
  let G (a : α) := ({z | a ∈ F z} : Set Ω).indicator (fun _ ↦ (1 : ℝ≥0∞))
  have hG (a : α) : Measurable (G a) := measurable_const.indicator (hF a)
  have he : (fun z ↦ ((F z).card : ℝ≥0∞)) = fun z ↦ ∑ a, G a z := by
    funext z
    have hs : Finset.univ.filter (fun a ↦ a ∈ F z) = F z := by ext a; simp
    simp only [G, indicator_apply, mem_ofPred_eq, ← Finset.sum_filter, hs]
    simp
  rw [he]
  exact Finset.measurable_sum _ fun a _ ↦ hG a
end DiagLP
end

-- ReverseColoredPermutations
section
open scoped BigOperators
namespace DiagLP
private def colorSize {α : Type*} [Fintype α] (c : α → Fin 3) (i : Fin 3) : ℕ :=
  Fintype.card {x // c x = i}
private theorem colorSize_sum {α : Type*} [Fintype α] (c : α → Fin 3) :
    ∑ i, colorSize c i = Fintype.card α := by
  simpa only [colorSize, Fintype.card_sigma] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv c)
private abbrev ColorShape (α : Type*) [Fintype α] :=
  Fin (Fintype.card α + 1) × Fin (Fintype.card α + 1)
private def colorShape {α : Type*} [Fintype α] (c : α → Fin 3) : ColorShape α :=
  (⟨colorSize c 0, Nat.lt_succ_of_le (Fintype.card_subtype_le (fun x ↦ c x = 0))⟩,
    ⟨colorSize c 1, Nat.lt_succ_of_le (Fintype.card_subtype_le (fun x ↦ c x = 1))⟩)
private theorem colorSize_eq_of_colorShape_eq {α : Type*} [Fintype α] {c d : α → Fin 3}
    (h : colorShape c = colorShape d) (i : Fin 3) : colorSize c i = colorSize d i := by
  have h₀ : colorSize c 0 = colorSize d 0 := congrArg (fun q : ColorShape α ↦ q.1.val) h
  have h₁ : colorSize c 1 = colorSize d 1 := congrArg (fun q : ColorShape α ↦ q.2.val) h
  have h₂ : colorSize c 2 = colorSize d 2 := by
    have hc := colorSize_sum c
    have hd := colorSize_sum d
    rw [Fin.sum_univ_three] at hc hd
    omega
  fin_cases i <;> assumption
private noncomputable def colorRelabel {α : Type*} [Fintype α] {c d : α → Fin 3}
    (h : colorShape c = colorShape d) : Equiv.Perm α :=
  Equiv.ofFiberEquiv fun i ↦ Fintype.equivOfCardEq (colorSize_eq_of_colorShape_eq h i)
private theorem colorRelabel_map {α : Type*} [Fintype α] {c d : α → Fin 3}
    (h : colorShape c = colorShape d) (a : α) : d (colorRelabel h a) = c a :=
  Equiv.ofFiberEquiv_map _ _
private abbrev ColorPreservingPerm (α : Type*) :=
  Σ c : α → Fin 3, {σ : Equiv.Perm α // ∀ a, c (σ a) = c a}
open scoped Classical in
private theorem card_colorPreservingPerm_le {α : Type*} [Fintype α] :
    Nat.card (ColorPreservingPerm α) ≤
      (Fintype.card α).factorial * (Fintype.card α + 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  let S := Set.range (colorShape (α := α))
  let shape (c : α → Fin 3) : S := ⟨colorShape c, ⟨c, rfl⟩⟩
  let rep (v : S) : α → Fin 3 := Classical.choose v.property
  have hrep (v : S) : colorShape (rep v) = v.val := Classical.choose_spec v.property
  let base (c : α → Fin 3) : Equiv.Perm α := colorRelabel (hrep (shape c))
  let encode (p : ColorPreservingPerm α) : S × Equiv.Perm α :=
    (shape p.1, (base p.1).trans p.2.val)
  have hencode (p : ColorPreservingPerm α) (a : α) :
      p.1 ((encode p).2 a) = rep (shape p.1) a :=
    (p.2.property _).trans (colorRelabel_map (hrep (shape p.1)) a)
  have hinj : Function.Injective encode := by
    rintro ⟨c, σ⟩ ⟨d, τ⟩ heq
    have hshape : shape c = shape d := congrArg Prod.fst heq
    have hperm := congrArg Prod.snd heq
    have hcd : c = d := by
      funext a
      obtain ⟨x, rfl⟩ := ((encode ⟨c, σ⟩).2).surjective a
      have hc := hencode ⟨c, σ⟩ x
      have hd := hencode ⟨d, τ⟩ x
      rw [hshape] at hc
      exact hc.trans (hd.symm.trans (congrArg (fun e : Equiv.Perm α ↦ d (e x)) hperm).symm)
    subst d
    have hστ : σ = τ := by
      apply Subtype.ext
      ext a
      obtain ⟨x, rfl⟩ := (base c).surjective a
      exact congrArg (fun e : Equiv.Perm α ↦ e x) hperm
    rw [hστ]
  calc
    _ ≤ Fintype.card (S × Equiv.Perm α) := Fintype.card_le_of_injective encode hinj
    _ ≤ _ := by
      rw [Fintype.card_prod, Fintype.card_perm, mul_comm, pow_two]
      apply Nat.mul_le_mul_left
      calc
        _ ≤ Fintype.card (ColorShape α) := Fintype.card_subtype_le _
        _ = _ := by simp only [ColorShape, Fintype.card_prod, Fintype.card_fin]
open scoped Classical in
theorem sum_three_pow_cycleFactorsFinset_support_le {n : ℕ} (s : Finset (Fin n)) :
    (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ ↦ σ.support = s),
      3 ^ σ.cycleFactorsFinset.card) ≤ s.card.factorial * (s.card + 1) ^ 2 := by
  let F := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ ↦ σ.support = s)
  have hsupport (σ : F) : σ.val.support = s := (Finset.mem_filter.mp σ.property).2
  let restrict (σ : F) : Equiv.Perm s :=
    σ.val.subtypePerm (Equiv.Perm.isInvariant_of_support_le (hsupport σ).le)
  have hrestrict : Function.Injective restrict := by
    intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ s
    · exact congrArg (fun e : Equiv.Perm s ↦ (e ⟨x, hx⟩ : Fin n)) h
    · have hσ : x ∉ σ.val.support := by rwa [hsupport σ]
      have hτ : x ∉ τ.val.support := by rwa [hsupport τ]
      exact (Equiv.Perm.notMem_support.mp hσ).trans (Equiv.Perm.notMem_support.mp hτ).symm
  let cycle (σ : F) (a : s) : σ.val.cycleFactorsFinset :=
    ⟨σ.val.cycleOf a, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (by
      rw [hsupport σ]
      exact a.property)⟩
  let A := Σ σ : F, σ.val.cycleFactorsFinset → Fin 3
  let f (p : A) : ColorPreservingPerm s :=
    ⟨p.2 ∘ cycle p.1, ⟨restrict p.1, fun a ↦
      congrArg p.2 (Subtype.ext (Equiv.Perm.cycleOf_self_apply p.1.val a))⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨σ, c⟩ ⟨τ, d⟩ heq
    have hστ : σ = τ := hrestrict (congrArg (fun p : ColorPreservingPerm s ↦ p.2.val) heq)
    subst τ
    suffices c = d by rw [this]
    funext ρ
    obtain ⟨a, ha⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp ρ.property).1.nonempty_support
    have has : a ∈ s := (hsupport σ) ▸ Equiv.Perm.mem_cycleFactorsFinset_support_le ρ.property ha
    let x : s := ⟨a, has⟩
    have hρ : cycle σ x = ρ := Subtype.ext (Equiv.Perm.cycle_is_cycleOf ha ρ.property).symm
    have h := congrArg (fun p : ColorPreservingPerm s ↦ p.1 x) heq
    change c (cycle σ x) = d (cycle σ x) at h
    rwa [hρ] at h
  have hA : Nat.card A = ∑ σ ∈ F, 3 ^ σ.cycleFactorsFinset.card := by
    simp only [Nat.card_eq_fintype_card, A, Fintype.card_sigma, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_coe]
    exact Finset.sum_attach F (fun σ ↦ 3 ^ σ.cycleFactorsFinset.card)
  change (∑ σ ∈ F, 3 ^ σ.cycleFactorsFinset.card) ≤ _
  rw [← hA]
  calc
    _ ≤ Nat.card (ColorPreservingPerm s) := Nat.card_le_card_of_injective f hf
    _ ≤ (Fintype.card s).factorial * (Fintype.card s + 1) ^ 2 :=
      card_colorPreservingPerm_le (α := s)
    _ = _ := by rw [Fintype.card_coe]
end DiagLP
end

-- CoexposureGaussianSum
section
open scoped BigOperators ENNReal
open Finset Filter
namespace DiagLP
private theorem sum_cast_range_gaussian (j : ℕ) :
    (∑ i ∈ range j, (i : ℝ)) = (j : ℝ) * ((j : ℝ) - 1) / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    ring
theorem descFactorial_div_pow_le_exp {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (n.descFactorial j : ℝ) / (n : ℝ) ^ j ≤
      Real.exp (-((j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)))) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hi (i : ℕ) (h : i ∈ range j) : i ≤ n := (mem_range.mp h).le.trans hj
  have hpow : (n : ℝ) ^ j = ∏ _i ∈ range j, (n : ℝ) := by simp
  calc
    _ = ∏ i ∈ range j, (1 - (i : ℝ) / (n : ℝ)) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, hpow, ← prod_div_distrib]
      refine prod_congr rfl fun i h ↦ ?_
      rw [Nat.cast_sub (hi i h)]
      field_simp
    _ ≤ ∏ i ∈ range j, Real.exp (-((i : ℝ) / (n : ℝ))) :=
      prod_le_prod (fun i h ↦ sub_nonneg.mpr ((div_le_one (by positivity)).mpr
        (Nat.cast_le.mpr (hi i h)))) fun i _ ↦ by
          simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-((i : ℝ) / (n : ℝ)))
    _ = _ := by
      rw [← Real.exp_sum, sum_neg_distrib, ← sum_div, sum_cast_range_gaussian]
      congr 1
      ring
private theorem sum_exp_neg_div_le (s : ℝ) (hs : 0 < s) (m : ℕ) :
    (∑ j ∈ range m, Real.exp (-((j : ℝ) / s))) ≤ 1 + s := by
  let r := Real.exp (-(1 / s))
  have hr₀ : 0 ≤ r := Real.exp_nonneg _
  have hr₁ : r < 1 := by
    calc
      r < Real.exp 0 := Real.exp_lt_exp.mpr (neg_neg_of_pos (one_div_pos.mpr hs))
      _ = 1 := Real.exp_zero
  have hrle : r ≤ s / (1 + s) := by
    calc
      r = (Real.exp (1 / s))⁻¹ := Real.exp_neg _
      _ ≤ (1 / s + 1)⁻¹ :=
        inv_anti₀ (by positivity) (Real.add_one_le_exp (1 / s))
      _ = s / (1 + s) := by field_simp
  have hmul : 1 ≤ (1 + s) * (1 - r) := by
    have h := (le_div_iff₀ (by positivity : 0 < 1 + s)).mp hrle
    nlinarith
  have heq (j : ℕ) : Real.exp (-((j : ℝ) / s)) = r ^ j := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [heq]
  have hgeom : (∑ j ∈ range m, r ^ j) * (1 - r) ≤ 1 := by
    rw [geom_sum_mul_of_le_one hr₁.le]
    exact sub_le_self _ (pow_nonneg hr₀ _)
  exact le_of_mul_le_mul_right (hgeom.trans hmul) (sub_pos.mpr hr₁)
theorem coexposure_descFactorial_sum_le_sqrt {n : ℕ} (hn : 0 < n) {δ C : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ)) :
    (∑ j ∈ range (n + 1), (1 + δ) ^ j * ((n.descFactorial j : ℝ) / (n : ℝ) ^ j)) ≤
      2 * Real.exp ((C + 3 / 2) ^ 2 / 2) * Real.sqrt (n : ℝ) := by
  let s := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs₂ : s ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hs₁ : 1 ≤ s := by
    change 1 ≤ Real.sqrt (n : ℝ)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  let D := C + 3 / 2
  have hexp (j : ℕ) :
      (j : ℝ) * δ - (j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)) ≤
        D ^ 2 / 2 - (j : ℝ) / s := by
    let t := (j : ℝ) / s
    have ht : 0 ≤ t := by positivity
    have ht₂ : (j : ℝ) ^ 2 / (n : ℝ) = t ^ 2 := by
      simp only [t, div_pow, hs₂]
    have ht₁ : (j : ℝ) / (n : ℝ) ≤ t := by
      rw [← hs₂, pow_two, ← div_div]
      exact div_le_self ht hs₁
    have hδj : (j : ℝ) * δ ≤ C * t := by
      calc
        _ ≤ (j : ℝ) * (C / s) :=
          mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg _)
        _ = C * t := by dsimp [t]; ring
    calc
      _ = (j : ℝ) * δ - ((j : ℝ) ^ 2 / (n : ℝ) - (j : ℝ) / (n : ℝ)) / 2 := by ring
      _ ≤ C * t - (t ^ 2 - t) / 2 := by rw [ht₂]; linarith
      _ ≤ D ^ 2 / 2 - t := by dsimp [D]; nlinarith [sq_nonneg (t - (C + 3 / 2))]
  calc
    _ ≤ ∑ j ∈ range (n + 1), Real.exp (D ^ 2 / 2) * Real.exp (-((j : ℝ) / s)) := by
      refine sum_le_sum fun j hj ↦ ?_
      have hj' : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
      have hδp : (1 + δ) ^ j ≤ (Real.exp δ) ^ j :=
        pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp δ) _
      calc
        _ ≤ (Real.exp δ) ^ j *
            Real.exp (-((j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)))) :=
          mul_le_mul hδp (descFactorial_div_pow_le_exp hn hj') (by positivity) (by positivity)
        _ = Real.exp ((j : ℝ) * δ - (j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ))) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
        _ ≤ _ := by
          rw [← Real.exp_add, ← sub_eq_add_neg]
          exact Real.exp_le_exp.mpr (hexp j)
    _ = Real.exp (D ^ 2 / 2) * ∑ j ∈ range (n + 1), Real.exp (-((j : ℝ) / s)) :=
      (mul_sum ..).symm
    _ ≤ Real.exp (D ^ 2 / 2) * (1 + s) :=
      mul_le_mul_of_nonneg_left (sum_exp_neg_div_le s hs _) (Real.exp_nonneg _)
    _ ≤ _ := by
      calc
        _ ≤ Real.exp (D ^ 2 / 2) * (2 * s) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
        _ = _ := by dsimp [D, s]; ring
private noncomputable def coexposureEsymm {ι : Type*} (s : Finset ι) (j : ℕ) (w : ι → ℝ) : ℝ :=
  ∑ t ∈ s.powersetCard j, ∏ i ∈ t, w i
private theorem coexposureEsymm_zero {ι : Type*} (s : Finset ι) (w : ι → ℝ) :
    coexposureEsymm s 0 w = 1 := by simp [coexposureEsymm]
private theorem coexposureEsymm_congr {ι : Type*} {s : Finset ι} (j : ℕ) {w v : ι → ℝ}
    (h : ∀ i ∈ s, w i = v i) : coexposureEsymm s j w = coexposureEsymm s j v :=
  sum_congr rfl fun _ ht ↦ prod_congr rfl fun i hi ↦ h i ((mem_powersetCard.mp ht).1 hi)
private theorem coexposureEsymm_nonneg {ι : Type*} (s : Finset ι) (j : ℕ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ coexposureEsymm s j w :=
  sum_nonneg fun _ _ ↦ prod_nonneg fun i _ ↦ hw i
private theorem coexposureEsymm_insert_succ {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι} (ha : a ∉ s) (j : ℕ) (w : ι → ℝ) :
    coexposureEsymm (insert a s) (j + 1) w =
      coexposureEsymm s (j + 1) w + w a * coexposureEsymm s j w := by
  have hnot (k : ℕ) {t : Finset ι} (ht : t ∈ s.powersetCard k) : a ∉ t :=
    fun hat ↦ ha ((mem_powersetCard.mp ht).1 hat)
  have hdisj : Disjoint (s.powersetCard (j + 1)) ((s.powersetCard j).image (insert a)) :=
    disjoint_left.mpr fun t ht ht' ↦ by
      obtain ⟨u, _, rfl⟩ := mem_image.mp ht'
      exact hnot (j + 1) ht (mem_insert_self a u)
  have hinj : Set.InjOn (insert a) (s.powersetCard j : Set (Finset ι)) := by
    intro t ht u hu he
    have he' := congrArg (fun v : Finset ι ↦ v.erase a) he
    simpa only [erase_insert (hnot j ht), erase_insert (hnot j hu)] using he'
  unfold coexposureEsymm
  rw [powersetCard_succ_insert ha j, sum_union hdisj, sum_image hinj, mul_sum]
  congr 1
  exact sum_congr rfl fun t ht ↦ prod_insert (hnot j ht)
private theorem coexposureEsymm_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ) :
    coexposureEsymm s 1 w = ∑ i ∈ s, w i := by
  induction s using Finset.induction_on with
  | empty => simp [coexposureEsymm, powersetCard_one]
  | @insert a s ha ih =>
    rw [coexposureEsymm_insert_succ ha 0, coexposureEsymm_zero, mul_one,
      ih, sum_insert ha, add_comm]
private theorem coexposureEsymm_insert_insert {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a b : ι} (ha : a ∉ insert b s) (hb : b ∉ s) (j : ℕ) (w : ι → ℝ) :
    coexposureEsymm (insert a (insert b s)) (j + 2) w =
      coexposureEsymm s (j + 2) w + (w a + w b) * coexposureEsymm s (j + 1) w +
        w a * w b * coexposureEsymm s j w := by
  rw [show j + 2 = (j + 1) + 1 by rfl, coexposureEsymm_insert_succ ha,
    coexposureEsymm_insert_succ hb, coexposureEsymm_insert_succ hb]
  ring
private abbrev coexposureSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}
private theorem exists_coexposure_smoothing {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (hw : w ∈ coexposureSimplex ι) {a b : ι} (hab : a ≠ b) (hne : w a ≠ w b)
    (j : ℕ) :
    ∃ v ∈ coexposureSimplex ι, coexposureEsymm univ j w ≤ coexposureEsymm univ j v ∧
      (∑ i, (v i) ^ 2) < ∑ i, (w i) ^ 2 := by
  classical
  let t := (univ.erase a).erase b
  have hat : a ∉ t := fun h ↦ notMem_erase a _ (mem_erase.mp h).2
  have hbt : b ∉ t := notMem_erase _ _
  have hat' : a ∉ insert b t := by simp [hab, hat]
  have hdecomp : insert a (insert b t) = univ := by
    ext i
    by_cases hi : i = a
    · simp [hi]
    by_cases hi' : i = b
    · simp [hi']
    simp [t, hi, hi']
  have hsplit (f : ι → ℝ) : (∑ i, f i) = f a + f b + ∑ i ∈ t, f i := by
    rw [← hdecomp, sum_insert hat', sum_insert hbt]
    ring
  let c := (w a + w b) / 2
  let v := fun i ↦ if i = a ∨ i = b then c else w i
  have hva : v a = c := by simp [v]
  have hvb : v b = c := by simp [v]
  have hvt (i : ι) (hi : i ∈ t) : v i = w i := by
    have hia : i ≠ a := fun h ↦ hat (h ▸ hi)
    have hib : i ≠ b := fun h ↦ hbt (h ▸ hi)
    simp [v, hia, hib]
  have hsum : ∑ i, v i = 1 := by
    rw [← hw.2, hsplit v, hsplit w, hva, hvb, sum_congr rfl hvt]
    dsimp [c]
    ring
  have hnonneg (i : ι) : 0 ≤ v i := by
    dsimp [v, c]
    split_ifs <;> positivity [hw.1 i, hw.1 a, hw.1 b]
  refine ⟨v, ⟨hnonneg, hsum⟩, ?_, ?_⟩
  · cases j with
    | zero => simp only [coexposureEsymm_zero, le_refl]
    | succ j =>
      cases j with
      | zero =>
        rw [show 0 + 1 = 1 by rfl, coexposureEsymm_one, coexposureEsymm_one, hw.2, hsum]
      | succ j =>
        change coexposureEsymm univ (j + 2) w ≤ coexposureEsymm univ (j + 2) v
        rw [← hdecomp, coexposureEsymm_insert_insert hat' hbt,
          coexposureEsymm_insert_insert hat' hbt,
          coexposureEsymm_congr (j + 2) hvt, coexposureEsymm_congr (j + 1) hvt,
          coexposureEsymm_congr j hvt, hva, hvb]
        have hcc : c + c = w a + w b := by dsimp [c]; ring
        have hm : w a * w b ≤ c * c := by dsimp [c]; nlinarith [sq_nonneg (w a - w b)]
        rw [hcc]
        gcongr
        exact coexposureEsymm_nonneg t j hw.1
  · rw [hsplit (fun i ↦ (v i) ^ 2), hsplit (fun i ↦ (w i) ^ 2)]
    simp only [hva, hvb]
    rw [sum_congr rfl (fun i hi ↦ congrArg (fun z : ℝ ↦ z ^ 2) (hvt i hi))]
    dsimp [c]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]
theorem coexposureEsymm_le_uniform {n : ℕ} (hn : 0 < n) (j : ℕ) {w : Fin n → ℝ}
    (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) :
    coexposureEsymm univ j w ≤ (n.choose j : ℝ) * (1 / (n : ℝ)) ^ j := by
  classical
  let E := coexposureEsymm (univ : Finset (Fin n)) j
  have hE : Continuous E :=
    continuous_finsetSum _ fun t _ ↦ continuous_finsetProd _ fun i _ ↦ continuous_apply i
  let S := coexposureSimplex (Fin n)
  have hS : IsCompact S := by
    exact isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin n)
  have hwS : w ∈ S := ⟨hw₀, hw⟩
  obtain ⟨u, hu, humax⟩ := hS.exists_isMaxOn ⟨w, hwS⟩ hE.continuousOn
  let T := S ∩ {v | E v = E u}
  have hT : IsCompact T := hS.inter_right (isClosed_eq hE continuous_const)
  have hsq : Continuous (fun v : Fin n → ℝ ↦ ∑ i, (v i) ^ 2) :=
    continuous_finsetSum _ fun i _ ↦ (continuous_apply i).pow 2
  obtain ⟨v, hv, hvmin⟩ := hT.exists_isMinOn ⟨u, hu, rfl⟩ hsq.continuousOn
  have hconst (a b : Fin n) : v a = v b := by
    by_contra hne
    have hab : a ≠ b := fun h ↦ hne (congrArg v h)
    obtain ⟨z, hz, hzE, hzsq⟩ := exists_coexposure_smoothing hv.1 hab hne j
    have hzT : z ∈ T := ⟨hz, (humax hz).antisymm (hv.2 ▸ hzE)⟩
    exact (not_lt_of_ge (hvmin hzT)) hzsq
  let a : Fin n := ⟨0, hn⟩
  have hvc : ∑ i : Fin n, v i = (n : ℝ) * v a := by
    calc
      _ = ∑ _i : Fin n, v a := sum_congr rfl fun i _ ↦ hconst i a
      _ = _ := by simp
  have hva : v a = 1 / (n : ℝ) := by
    apply (eq_div_iff (by positivity : (n : ℝ) ≠ 0)).mpr
    rw [mul_comm, ← hvc]
    exact hv.1.2
  have hveq (i : Fin n) : v i = 1 / (n : ℝ) := (hconst i a).trans hva
  calc
    E w ≤ E u := humax hwS
    _ = E v := hv.2.symm
    _ = coexposureEsymm univ j (fun _ ↦ 1 / (n : ℝ)) :=
      coexposureEsymm_congr j fun i _ ↦ hveq i
    _ = _ := by
      calc
        coexposureEsymm univ j (fun _ : Fin n ↦ 1 / (n : ℝ)) =
            ∑ _t ∈ (univ : Finset (Fin n)).powersetCard j, (1 / (n : ℝ)) ^ j :=
          sum_congr rfl fun _ ht ↦ by rw [prod_const, (mem_powersetCard.mp ht).2]
        _ = _ := by simp [sum_const, nsmul_eq_mul, card_powersetCard]
theorem coexposure_weighted_powerset_sum_le_sqrt {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) {δ C : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ)) :
    (∑ t ∈ (univ : Finset (Fin n)).powerset,
      (1 + δ) ^ t.card * (t.card.factorial : ℝ) * ∏ i ∈ t, w i) ≤
        2 * Real.exp ((C + 3 / 2) ^ 2 / 2) * Real.sqrt (n : ℝ) := by
  calc
    _ = ∑ j ∈ range (n + 1), (1 + δ) ^ j * (j.factorial : ℝ) * coexposureEsymm univ j w := by
      rw [sum_powerset, card_univ, Fintype.card_fin]
      refine sum_congr rfl fun j _ ↦ ?_
      unfold coexposureEsymm
      rw [mul_sum]
      exact sum_congr rfl fun t ht ↦ by rw [(mem_powersetCard.mp ht).2]
    _ ≤ ∑ j ∈ range (n + 1), (1 + δ) ^ j * ((n.descFactorial j : ℝ) / (n : ℝ) ^ j) := by
      refine sum_le_sum fun j _ ↦ ?_
      calc
        _ ≤ (1 + δ) ^ j * (j.factorial : ℝ) * ((n.choose j : ℝ) * (1 / (n : ℝ)) ^ j) :=
          mul_le_mul_of_nonneg_left (coexposureEsymm_le_uniform hn j hw₀ hw) (by positivity)
        _ = _ := by
          rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, div_pow, one_pow]
          ring
    _ ≤ _ := coexposure_descFactorial_sum_le_sqrt hn hδ₀ hδ
end DiagLP
end

-- ReverseQuadraticGaussian
section
open Finset
open scoped BigOperators ENNReal
namespace DiagLP
theorem reverse_weighted_powerset_sum_le_n_mul_sqrt {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) {δ C : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ)) :
    (∑ t ∈ (univ : Finset (Fin n)).powerset,
      (t.card.factorial : ℝ) * ((t.card : ℝ) + 1) ^ 2 * (1 + δ) ^ t.card *
        ∏ i ∈ t, w i) ≤
      2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) * (n : ℝ) * Real.sqrt n := by
  let s := Real.sqrt (n : ℝ)
  let u := 1 / s
  let Δ := (1 + δ) * (1 + u) ^ 2 - 1
  have hs₀ : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs₁ : 1 ≤ s := by
    simpa [s] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hs₂ : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hu₀ : 0 ≤ u := one_div_nonneg.mpr hs₀.le
  have hu₁ : u ≤ 1 := (div_le_one hs₀).mpr hs₁
  have hΔ : 1 + Δ = (1 + δ) * (1 + u) ^ 2 := by dsimp [Δ]; ring
  have hΔ₀ : 0 ≤ Δ := sub_nonneg.mpr
    (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith)))
  have hu_sq : u ^ 2 ≤ u := by nlinarith [mul_nonneg hu₀ (sub_nonneg.mpr hu₁)]
  have hpert : Δ ≤ (4 * C + 3) / s :=
    calc
      Δ ≤ (1 + δ) * (1 + 3 * u) - 1 :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)) _
      _ ≤ 4 * δ + 3 * u := by nlinarith [mul_nonneg hδ₀ (sub_nonneg.mpr hu₁)]
      _ ≤ _ := by
        have hδs : δ ≤ C / s := hδ
        rw [add_div, mul_div_assoc]
        dsimp only [u]
        rw [mul_one_div]
        linarith only [hδs]
  have hq (j : ℕ) : ((j : ℝ) + 1) ^ 2 ≤ (n : ℝ) * ((1 + u) ^ 2) ^ j := by
    have hbern : 1 + (j : ℝ) * u ≤ (1 + u) ^ j := one_add_mul_le_pow (by linarith) j
    have hsu : s * u = 1 := by
      dsimp only [u]
      rw [mul_one_div, div_self hs₀.ne']
    have hscale : (j : ℝ) + 1 ≤ s * (1 + (j : ℝ) * u) := by
      rw [mul_add, mul_one, mul_left_comm s, hsu, mul_one]
      linarith only [hs₁]
    calc
      _ ≤ (s * ((1 + u) ^ j)) ^ 2 :=
        pow_le_pow_left₀ (by positivity)
          (hscale.trans (mul_le_mul_of_nonneg_left hbern hs₀.le)) _
      _ = _ := by
        rw [mul_pow, hs₂, ← pow_mul, ← pow_mul, Nat.mul_comm j 2]
  calc
    _ ≤ ∑ t ∈ (univ : Finset (Fin n)).powerset,
          (n : ℝ) * ((1 + Δ) ^ t.card * (t.card.factorial : ℝ) * ∏ i ∈ t, w i) := by
      refine sum_le_sum fun t _ ↦ ?_
      calc
        _ ≤ (t.card.factorial : ℝ) * ((n : ℝ) * ((1 + u) ^ 2) ^ t.card) *
              (1 + δ) ^ t.card * ∏ i ∈ t, w i :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hq _) (Nat.cast_nonneg _))
              (pow_nonneg (by positivity) _))
            (prod_nonneg fun i _ ↦ hw₀ i)
        _ = _ := by
          rw [hΔ, mul_pow (1 + δ) ((1 + u) ^ 2)]
          ring
    _ = (n : ℝ) * ∑ t ∈ (univ : Finset (Fin n)).powerset,
          (1 + Δ) ^ t.card * (t.card.factorial : ℝ) * ∏ i ∈ t, w i := (mul_sum ..).symm
    _ ≤ (n : ℝ) * (2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left
        (coexposure_weighted_powerset_sum_le_sqrt hn hw₀ hw hΔ₀ hpert)
        (Nat.cast_nonneg n)
    _ = _ := by ring
theorem reverse_weighted_powerset_sum_le_n_mul_sqrt_ennreal {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) {δ C : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ)) :
    (∑ t ∈ (univ : Finset (Fin n)).powerset,
      (t.card.factorial : ℝ≥0∞) * ((t.card : ℝ≥0∞) + 1) ^ 2 *
        (ENNReal.ofReal (1 + δ)) ^ t.card * ∏ i ∈ t, ENNReal.ofReal (w i)) ≤
      ENNReal.ofReal (2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) * (n : ℝ) * Real.sqrt n) := by
  have ha : 0 ≤ 1 + δ := by positivity
  calc
    _ = ENNReal.ofReal (∑ t ∈ (univ : Finset (Fin n)).powerset,
          (t.card.factorial : ℝ) * ((t.card : ℝ) + 1) ^ 2 *
            (1 + δ) ^ t.card * ∏ i ∈ t, w i) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun t _ ↦
        mul_nonneg (by positivity) (prod_nonneg fun i _ ↦ hw₀ i))]
      refine sum_congr rfl fun t _ ↦ ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_pow ha,
        ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hw₀ i)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (reverse_weighted_powerset_sum_le_n_mul_sqrt hn hw₀ hw hδ₀ hδ)
end DiagLP
end

-- ReverseCycleCollectionMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
theorem sum_three_colored_successorPermutation_product_le {n : ℕ}
    (a : ℝ≥0∞) (w : Fin n → ℝ≥0∞) :
    (∑ σ : Matching n, (3 : ℝ≥0∞) ^ σ.cycleFactorsFinset.card *
      ∏ i ∈ σ.support, a * w (σ i)) ≤
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        (s.card.factorial : ℝ≥0∞) * ((s.card : ℝ≥0∞) + 1) ^ 2 * a ^ s.card *
          ∏ i ∈ s, w i := by
  classical
  rw [sum_weighted_successorPermutation_product_by_support]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  have hs :
      (∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.support = s),
        (3 : ℝ≥0∞) ^ σ.cycleFactorsFinset.card) ≤
        (s.card.factorial : ℝ≥0∞) * ((s.card : ℝ≥0∞) + 1) ^ 2 := by
    exact_mod_cast sum_three_pow_cycleFactorsFinset_support_le s
  simpa only [mul_assoc] using
    (mul_le_mul_left hs (a ^ s.card * ∏ i ∈ s, w i))
theorem lintegral_four_pow_numExposedRotations_le_mul {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (hP : Measurable P) (M : Matching n)
    (c : ℝ≥0∞)
    (hn : 0 < n) {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    {δ C : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ))
    (harc : ∀ σ : Matching n, ν {x | RealizesSuccessorPermutation (P x) M σ} ≤ c *
      ∏ i ∈ σ.support, ENNReal.ofReal (1 + δ) * ENNReal.ofReal (w (σ i))) :
    (∫⁻ x, (4 : ℝ≥0∞) ^ numExposedRotations (P x) M ∂ν) ≤
      c * ENNReal.ofReal (2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) *
        (n : ℝ) * Real.sqrt n) := by
  have h := lintegral_cycleWeight_numExposedRotations_le ν P hP M 3 _ harc
  rw [show (3 : ℝ≥0∞) + 1 = 4 by norm_num] at h
  refine h.trans ?_
  simp_rw [← mul_assoc, mul_comm _ c, mul_assoc c]
  rw [← Finset.mul_sum]
  exact mul_le_mul_right ((sum_three_colored_successorPermutation_product_le _ _).trans
    (reverse_weighted_powerset_sum_le_n_mul_sqrt_ennreal hn hw₀ hw hδ₀ hδ)) c
end DiagLP
end

-- PivotReverseMaskMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
theorem ae_diagonal_ae_injective_scoreRows {n : ℕ} (μ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ᵐ z ∂offDiagonalScoreLaw n,
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r) :=
  Measure.ae_ae_of_ae_prod
    (((measurePreserving_splitScorePairs μ).symm).quasiMeasurePreserving.ae (ae_injective_rows n))
theorem lintegral_four_pow_numReverseExposedRotations_fixedMask_le {n : ℕ}
    (μ : Matching n) (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (A : Set (ForwardActiveCellIndex flag → ℝ)) (hA : MeasurableSet A) (hn : 0 < n)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Icc 0 1)
    (hX : 0 < ∑ i, (diagonalPairAt d i).1)
    {δ C : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ))
    (hcomp : ∀ (i : Fin n) (q : ForwardInactiveColumnIndex flag i),
      (∑ j, (diagonalPairAt d j).1) / (1 + δ) ≤
        ∑ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
          (diagonalPairAt d k.val.val.val.val.1).1)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    let ν := ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
      (forwardScoreMaskEvent d flag)
    let G := (Prod.fst ∘ forwardScoreMaskRevealAndInactive flag) ⁻¹' A
    (∫⁻ z in G, (4 : ℝ≥0∞) ^ numExposedRotations
      (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm ∂ν) ≤
      (forwardScoreMaskActiveMaleLaw d flag) A *
        (forwardScoreMaskInactiveColumnLaw d flag) univ *
        ENNReal.ofReal (2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) * (n : ℝ) * Real.sqrt n) := by
  intro ν G
  let X := ∑ i, (diagonalPairAt d i).1
  let w (j : Fin n) := (diagonalPairAt d (μ.symm j)).1 / X
  let P (z : OffDiagonalScorePairs n) :=
    swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))
  have hP : Measurable P :=
    (show Measurable (swapProfile (n := n)) from fun _ _ ↦ MeasurableSet.of_discrete).comp
      ((measurable_profileOfScores n).comp
        ((splitScorePairs μ).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have hw₀ (j : Fin n) : 0 ≤ w j := div_nonneg (hx _).1 hX.le
  have hw : ∑ j, w j = 1 := by
    rw [← Fintype.sum_equiv μ (fun i ↦ (diagonalPairAt d i).1 / X) w
      (fun i ↦ by simp only [w, Equiv.symm_apply_apply]), ← Finset.sum_div]
    exact div_self hX.ne'
  refine lintegral_four_pow_numExposedRotations_le_mul (ν.restrict G) P hP μ.symm
    ((forwardScoreMaskActiveMaleLaw d flag) A * (forwardScoreMaskInactiveColumnLaw d flag) univ)
    hn hw₀ hw hδ₀ hδ fun σ ↦ ?_
  change forwardMaskRevealLaw d flag A {z | RealizesSuccessorPermutation (P z) μ.symm σ} ≤ _
  rw [measure_realizesReverseSuccessorPermutation_fixedMask μ σ d flag A hA hy0 hy1 ht]
  refine mul_le_mul_right (Finset.prod_le_prod' fun i _ ↦ ?_) _
  exact normalizedForwardInactiveColumnLaw_reverseArc_le d flag (μ.symm i) (μ.symm (σ i))
    (hy0 _) (hy1 _) hx hX (by positivity) (fun q _ ↦ hcomp _ q)
end DiagLP
end

-- PivotReverseFilterMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private structure ReverseFilterUpperControls {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (δ C : ℝ) : Prop where
  perturbation_nonneg : 0 ≤ δ
  perturbation_le : δ ≤ C / Real.sqrt (n : ℝ)
  competitor_mass : ∀ (i : Fin n) (q : ForwardInactiveColumnIndex flag i),
    (∑ j, (diagonalPairAt d j).1) / (1 + δ) ≤
      ∑ t : {t : ForwardInactiveColumnIndex flag i // t ≠ q},
        (diagonalPairAt d t.val.val.val.val.1).1
  available_mass : ∀ i, (∑ j, (diagonalPairAt d j).1) / 2 ≤
    ∑ q : ForwardInactiveColumnIndex flag i, (diagonalPairAt d q.val.val.val.1).1
private noncomputable def reverseFilterSecondMomentConstant (C : ℝ) : ℝ :=
  2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2)
theorem shortCycleLoss_budget_of_log (K L : ℕ) {δ B : ℝ} (hδ : 0 ≤ δ)
    (hKδ : (K : ℝ) * δ ≤ B)
    (hL : (512 / 3 : ℝ) * Real.exp B ≤ Real.log (L : ℝ)) :
    ENNReal.ofReal (1 + δ) ^ K * ENNReal.ofReal (4 / Real.log (L : ℝ)) ≤
      ENNReal.ofReal (3 / 128) := by
  have hbase : 0 ≤ 1 + δ := by linarith
  have hlog : 0 < Real.log (L : ℝ) := (by positivity : 0 < (512 / 3 : ℝ) * Real.exp B).trans_le hL
  have hp : (1 + δ) ^ K ≤ Real.exp B := by
    calc
      _ ≤ (Real.exp δ) ^ K := pow_le_pow_left₀ hbase
        (by linarith only [Real.add_one_le_exp δ]) _
      _ = Real.exp ((K : ℝ) * δ) := (Real.exp_nat_mul δ K).symm
      _ ≤ _ := Real.exp_le_exp.mpr hKδ
  rw [← ENNReal.ofReal_pow hbase, ← ENNReal.ofReal_mul (pow_nonneg hbase _)]
  apply ENNReal.ofReal_le_ofReal
  refine (mul_le_mul_of_nonneg_right hp (by positivity)).trans ?_
  rw [← mul_div_assoc, div_le_iff₀ hlog]
  linarith only [hL]
theorem reverseIncrementLoss_budget_of {n K : ℕ} (C : ℝ) (hn : 0 < n) (hK : 2 ≤ K)
    (hlarge : (128 / 3 : ℝ) * Real.sqrt (reverseFilterSecondMomentConstant C) ≤ (n : ℝ) ^ 2) :
    ENNReal.ofReal (Real.sqrt (reverseFilterSecondMomentConstant C) / (n : ℝ) ^ 2) ≤
      ENNReal.ofReal (3 / 128) * ((K - 1 : ℕ) : ℝ≥0∞) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ ≤ ENNReal.ofReal (3 / 128) := by
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) ^ 2)]
      linarith only [hlarge]
    _ = ENNReal.ofReal (3 / 128) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_right (by exact_mod_cast (show 1 ≤ K - 1 by omega)) _
theorem eventually_reverseFilterLossBudgets (K L : ℕ → ℕ) (δ : ℕ → ℝ) (C B : ℝ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n) (hL : Tendsto L atTop atTop)
    (hδ : ∀ᶠ n in atTop, 0 ≤ δ n ∧ (K n : ℝ) * δ n ≤ B) :
    ∀ᶠ n in atTop, 2 ≤ L n ∧
      ENNReal.ofReal (1 + δ n) ^ K n * ENNReal.ofReal (4 / Real.log (L n : ℝ)) ≤
        ENNReal.ofReal (3 / 128) ∧
      ENNReal.ofReal (Real.sqrt (reverseFilterSecondMomentConstant C) / (n : ℝ) ^ 2) ≤
        ENNReal.ofReal (3 / 128) * ((K n - 1 : ℕ) : ℝ≥0∞) := by
  have hlog : Tendsto (fun n ↦ Real.log (L n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hL)
  filter_upwards [hK, hL.eventually_ge_atTop 2, hδ, hlog.eventually_ge_atTop
      ((512 / 3 : ℝ) * Real.exp B), eventually_ge_atTop (1 : ℕ),
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
        ((128 / 3 : ℝ) * Real.sqrt (reverseFilterSecondMomentConstant C))]
    with n hKn hLn hδn hlogn hn hlarge
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  exact ⟨hLn, shortCycleLoss_budget_of_log (K n) (L n) hδn.1 hδn.2 hlogn,
    reverseIncrementLoss_budget_of C (Nat.zero_lt_of_lt hn) hKn (hlarge.trans hsq)⟩
end DiagLP
end

-- PivotForwardExposureReveal
section
open MeasureTheory Set StableMarriage
namespace DiagLP
private theorem forwardEligible_iff_flag {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (flag : OffDiagonalCellIndex n → Bool) (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (i j : Fin n) (hij : i ≠ j) :
    IsEligibleSuccessor (profileOfScores x) μ i (μ j) ↔ flag ⟨(i, j), hij⟩ = true := by
  let q : OffDiagonalCellIndex n := ⟨(i, j), hij⟩
  let d := (splitScorePairs μ x).1
  let z := (splitScorePairs μ x).2
  have he : IsEligibleSuccessor (profileOfScores x) μ i (μ j) ↔
      z q ∈ forwardEligibleScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j).2 := by
    dsimp only [z, d]
    rw [splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
      diagonalPairAt_splitScorePairs]
    simp only [IsEligibleSuccessor, forwardEligibleScoreCell, mem_prod, mem_Ioi, mem_Iio,
      Equiv.symm_apply_apply, profileOfScores, rankPermutation_lt_iff (ht (.inl i)),
      rankPermutation_lt_iff (ht (.inr (μ j))), q]
  have hh : z q ∈ forwardScoreCellFlagEvent (diagonalPairAt d i).1 (diagonalPairAt d j).2
      (flag q) := mem_pi.mp hmask q (mem_univ _)
  change _ ↔ flag q = true
  rw [he]
  by_cases hq : flag q = true
  · simp only [hq, forwardScoreCellFlagEvent] at hh
    simp only [hq, iff_true]
    exact hh
  · simp only [forwardScoreCellFlagEvent, if_neg hq, mem_compl_iff] at hh
    exact ⟨fun h ↦ (hh h).elim, fun h ↦ (hq h).elim⟩
private def forwardRevealExposureEvent {n : ℕ} (ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (ForwardRevealedMaleScores flag) :=
  {v | ρ.IsCycle ∧ ∀ m, ρ m ≠ m →
    ∃ q : ForwardActiveCellIndex flag, q.val.val = (m, ρ m) ∧
      ∀ t : ForwardActiveCellIndex flag, t.val.val.1 = m → v q ≤ v t}
theorem isExposedRotation_iff_forwardRevealExposureEvent {n : ℕ} (μ ρ : Matching n)
    (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag) :
    IsExposedRotation (profileOfScores x) μ ρ ↔
      (forwardRevealWithColumns flag (splitScorePairs μ x).2).1 ∈
        forwardRevealExposureEvent ρ flag := by
  let v := (forwardRevealWithColumns flag (splitScorePairs μ x).2).1
  let p := profileOfScores x
  have hscore (q : ForwardActiveCellIndex flag) :
      v q = x (.inl q.val.val.1) (μ q.val.val.2) :=
    congrArg Prod.fst (splitScorePairs_offDiagonal_apply μ x q.val)
  have hle (m j k : Fin n) :
      p.manRank m (μ j) ≤ p.manRank m (μ k) ↔ x (.inl m) (μ j) ≤ x (.inl m) (μ k) := by
    rw [← not_lt, ← not_lt]
    exact not_congr (rankPermutation_lt_iff (ht (.inl m)) _ _)
  constructor
  · intro h
    refine ⟨(IsExposedRotation.isCycle h), fun m hm ↦ ?_⟩
    let q₀ : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    let q : ForwardActiveCellIndex flag := ⟨q₀,
      (forwardEligible_iff_flag μ x flag ht hmask m (ρ m) hm.symm).mp (IsSuccessor.eligible ((IsExposedRotation.successor h) m hm))⟩
    refine ⟨q, rfl, fun t htm ↦ ?_⟩
    have htne : m ≠ t.val.val.2 := htm.symm ▸ t.val.property
    have hteq : (⟨(m, t.val.val.2), htne⟩ : OffDiagonalCellIndex n) = t.val :=
      Subtype.ext (Prod.ext htm.symm rfl)
    have hflag : flag ⟨(m, t.val.val.2), htne⟩ = true := by rw [hteq]; exact t.property
    have htel := (forwardEligible_iff_flag μ x flag ht hmask m t.val.val.2 htne).mpr hflag
    change v q ≤ v t
    rw [hscore q, hscore t, htm]
    exact (hle m (ρ m) t.val.val.2).mp ((IsSuccessor.min_rank ((IsExposedRotation.successor h) m hm)) _ htel)
  · rintro ⟨hcyc, htest⟩
    refine (IsExposedRotation.mk (hcyc) (fun m hm ↦ ?_))
    obtain ⟨q, hq, hmin⟩ := htest m hm
    have hq' : (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = q.val := Subtype.ext hq.symm
    refine (IsSuccessor.mk ((forwardEligible_iff_flag μ x flag ht hmask m (ρ m) hm.symm).mpr
      (hq' ▸ q.property)) (?_))
    intro w hwel
    let j := μ.symm w
    have hjw : μ j = w := μ.apply_symm_apply w
    have hj : m ≠ j := fun h ↦ (lt_irrefl _ (by simpa only [← hjw, ← h] using hwel.1))
    let t : ForwardActiveCellIndex flag := ⟨⟨(m, j), hj⟩,
      (forwardEligible_iff_flag μ x flag ht hmask m j hj).mp (hjw.symm ▸ hwel)⟩
    have h := hmin t rfl
    change v q ≤ v t at h
    rw [hscore q, hscore t, hq] at h
    exact hjw ▸ (hle m (ρ m) j).mpr h
theorem measurableSet_forwardRevealExposureEvent {n : ℕ} (ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) : MeasurableSet (forwardRevealExposureEvent ρ flag) := by
  unfold forwardRevealExposureEvent
  simp only [ofPred_and, ofPred_forall, ofPred_exists]
  refine (MeasurableSet.const _).inter (MeasurableSet.iInter fun (m : Fin n) ↦
    MeasurableSet.iInter fun (_ : ρ m ≠ m) ↦ MeasurableSet.iUnion
      fun (q : ForwardActiveCellIndex flag) ↦ (MeasurableSet.const _).inter
        (MeasurableSet.iInter fun (t : ForwardActiveCellIndex flag) ↦
          MeasurableSet.iInter fun (_ : t.val.val.1 = m) ↦ ?_))
  exact measurableSet_le (measurable_pi_apply q) (measurable_pi_apply t)
theorem ae_isExposedRotation_of_forwardReveal_subset {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (hU : MeasurableSet U)
    (hsub : U ⊆ forwardRevealExposureEvent ρ flag)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    ∀ᵐ z ∂forwardMaskRevealLaw d flag U,
      IsExposedRotation (profileOfScores ((splitScorePairs μ).symm (d, z))) μ ρ := by
  unfold forwardMaskRevealLaw
  filter_upwards [ae_restrict_mem (hU.preimage (measurable_fst.comp
      (measurable_forwardScoreMaskRevealAndInactive flag))),
    ae_restrict_of_ae (ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae ht))] with z hz hzmask hzt
  let x := (splitScorePairs μ).symm (d, z)
  have he : splitScorePairs μ x = (d, z) := (splitScorePairs μ).apply_symm_apply _
  apply (isExposedRotation_iff_forwardRevealExposureEvent μ ρ x flag hzt
    (by simpa only [he] using hzmask)).mpr
  simpa only [he, Function.comp_apply, forwardRevealWithColumns, Prod.map_fst, id_eq] using
    hsub hz
end DiagLP
end

-- PivotEligibilityScale
section
open Filter Real
open scoped BigOperators ENNReal Topology
namespace DiagLP
theorem reverseGoodLabelLoss_le_of_squareRoot {n k : ℕ} {a C B E : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hk : (k : ℝ) ≤ a * Real.sqrt (n : ℝ)) (r : Fin n → ℝ≥0∞)
    (A : Finset (Fin n)) (η : ℝ≥0∞)
    (hsq : ∑ i, (r i) ^ 2 ≤ ENNReal.ofReal (C / n))
    (hsupport : ∑ i ∈ A, r i ≤ ENNReal.ofReal (B / Real.sqrt n))
    (hforbid : η ≤ ENNReal.ofReal (E / Real.sqrt n)) :
    reverseGoodLabelLoss k r A η ≤ ENNReal.ofReal (C * a ^ 2 / 2 + (B + E) * a) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hk2 : (k : ℝ) ^ 2 ≤ a ^ 2 * n := by
    simpa only [mul_pow, Real.sq_sqrt hnR.le] using pow_le_pow_left₀ (Nat.cast_nonneg k) hk 2
  have hc : (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith only [Nat.cast_nonneg (α := ℝ) k]
  have hterm₁ : (k.choose 2 : ℝ) * (C / n) ≤ C * a ^ 2 / 2 := calc
    _ ≤ (a ^ 2 * n / 2) * (C / n) :=
      mul_le_mul_of_nonneg_right (hc.trans (div_le_div_of_nonneg_right hk2 (by norm_num)))
        (div_nonneg hC hnR.le)
    _ = _ := by field_simp
  have hterm₂ {v : ℝ} (hv : 0 ≤ v) : (k : ℝ) * (v / Real.sqrt n) ≤ v * a := calc
    _ ≤ (a * Real.sqrt n) * (v / Real.sqrt n) :=
      mul_le_mul_of_nonneg_right hk (div_nonneg hv hs.le)
    _ = _ := by field_simp
  calc
    reverseGoodLabelLoss k r A η ≤
        (k.choose 2 : ℝ≥0∞) * ENNReal.ofReal (C / n) +
          (k : ℝ≥0∞) * ENNReal.ofReal (B / Real.sqrt n) +
          (k : ℝ≥0∞) * ENNReal.ofReal (E / Real.sqrt n) :=
      add_le_add (add_le_add (mul_le_mul_right hsq _) (mul_le_mul_right hsupport _))
        (mul_le_mul_right hforbid _)
    _ ≤ _ := by
      simp only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith only [hterm₁, hterm₂ hB, hterm₂ hE,
        show (B + E) * a = B * a + E * a by ring])
theorem eventually_reverseArcLowerBudget_uniform {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : ℕ) (X : ℝ),
      c * (n : ℝ) ^ (3 / 5 : ℝ) ≤ X → (K : ℝ) ≤ a * Real.sqrt n →
      (K : ℝ) * reverseLowerArcError X ≤ 1 / 4 := by
  have hlim := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (a / c)
  filter_upwards [(tendsto_order.mp hlim).2 (1 / 4) (by norm_num),
    eventually_gt_atTop (0 : ℕ)] with n hsmall hn K X hX hK
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hd : 0 < c * (n : ℝ) ^ (3 / 5 : ℝ) := mul_pos hc (Real.rpow_pos_of_pos hn' _)
  calc
    _ = (K : ℝ) / (1 + X) := by rw [reverseLowerArcError, mul_one_div]
    _ ≤ (a * Real.sqrt n) / (c * (n : ℝ) ^ (3 / 5 : ℝ)) :=
      div_le_div₀ (mul_nonneg ha (Real.sqrt_nonneg _)) hK hd (by linarith)
    _ = (a / c) * (n : ℝ) ^ (-(1 / 10) : ℝ) := by
      rw [Real.sqrt_eq_rpow, show (-(1 / 10) : ℝ) = 1 / 2 - 3 / 5 by norm_num,
        Real.rpow_sub hn']
      ring
    _ ≤ _ := hsmall.le
end DiagLP
end

-- PivotEligibleRevealControls
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private def reverseDiagonalMaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).1
private structure ReverseMaskGeometry {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (s u p : ℝ) : Prop where
  score_mem : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1
  total_ge_two : 2 ≤ reverseDiagonalMaleTotal d
  max_nonneg : 0 ≤ s
  omitted_nonneg : 0 ≤ u
  pivot_nonneg : 0 ≤ p
  max_score : ∀ i, (diagonalPairAt d i).1 ≤ s * reverseDiagonalMaleTotal d
  omitted_score : ∀ i, forwardMaskOmittedMass d flag i ≤ u * reverseDiagonalMaleTotal d
  pivot_score : (∑ i ∈ ρ.support, (diagonalPairAt d i).1) ≤ p * reverseDiagonalMaleTotal d
private def reverseRawArcError (s u : ℝ) : ℝ := 2 * (2 * s + u)
private def reverseRelaxedArcInflation (s u p : ℝ) : ℝ := 1 + 2 * (2 * s + u + p)
private def eligiblePivotRevealSet {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (D : ℝ) :
    Set (ForwardRevealedMaleScores flag) :=
  {v | (∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ) ∧
    (∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement d flag ρ v m) ∧
    (∑ m ∈ ρ.support, forwardPivotIncrement d flag ρ v m) ≤ D}
theorem measurableSet_eligiblePivotRevealSet {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (D : ℝ) :
    MeasurableSet (eligiblePivotRevealSet d flag ρ D) := by
  have hs : MeasurableSet {v : ForwardRevealedMaleScores flag |
      ∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ} := by
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun τ ↦ ?_
    by_cases ht : τ = ρ
    · simpa only [ht, iff_true, ofPred_mem_eq] using
        measurableSet_forwardRevealExposureEvent ρ flag
    · simpa only [ht, iff_false, ← mem_compl_iff, ofPred_mem_eq] using
        (measurableSet_forwardRevealExposureEvent τ flag).compl
  have hnonneg : MeasurableSet {v : ForwardRevealedMaleScores flag |
      ∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement d flag ρ v m} := by
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun m ↦ ?_
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun _ ↦
      measurableSet_le measurable_const (measurable_forwardPivotIncrement d flag ρ m)
  have hsum : MeasurableSet {v : ForwardRevealedMaleScores flag |
      (∑ m ∈ ρ.support, forwardPivotIncrement d flag ρ v m) ≤ D} :=
    measurableSet_le (Finset.measurable_sum _ (fun m _ ↦
      measurable_forwardPivotIncrement d flag ρ m)) measurable_const
  exact hs.inter (hnonneg.inter hsum)
theorem total_div_one_add_two_mul_le_remaining {X q : ℝ} (hX : 0 ≤ X) (hq : 0 ≤ q)
    (hq' : q ≤ 1 / 2) : X / (1 + 2 * q) ≤ X * (1 - q) := by
  have hp : 0 < 1 + 2 * q := by linarith
  apply (div_le_iff₀ hp).mpr
  calc
    X = X * 1 := (mul_one _).symm
    _ ≤ X * ((1 - q) * (1 + 2 * q)) := by
      apply mul_le_mul_of_nonneg_left _ hX
      nlinarith only [mul_nonneg hq (show 0 ≤ 1 - 2 * q by linarith)]
    _ = _ := (mul_assoc ..).symm
namespace ReverseMaskGeometry
variable {n : ℕ} {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
  {μ ρ : Matching n} {s u p : ℝ}
theorem available_ge (h : ReverseMaskGeometry d flag ρ s u p) (i : Fin n) :
    reverseDiagonalMaleTotal d * (1 - (s + u)) ≤
      ∑ q : ForwardInactiveColumnIndex flag i, forwardInactiveColumnThreshold d q := by
  rw [sum_forwardInactiveColumn_eq]
  have hi := h.max_score i
  have hm := h.omitted_score i
  unfold reverseDiagonalMaleTotal at *
  nlinarith only [hi, hm]
theorem competitor_ge (h : ReverseMaskGeometry d flag ρ s u p) {i : Fin n}
    (q : ForwardInactiveColumnIndex flag i) :
    reverseDiagonalMaleTotal d * (1 - (2 * s + u)) ≤
      ∑ t : {t : ForwardInactiveColumnIndex flag i // t ≠ q},
        forwardInactiveColumnThreshold d t.val := by
  rw [sum_forwardInactiveCompetitor_eq]
  have hi := h.max_score i
  have hm := h.omitted_score i
  have hq := h.max_score (forwardInactiveColumnMan q)
  unfold reverseDiagonalMaleTotal at *
  change _ ≤ _ - _ - _ - (diagonalPairAt d (forwardInactiveColumnMan q)).1
  nlinarith only [hi, hm, hq]
theorem kept_competitor_ge (h : ReverseMaskGeometry d flag ρ s u p) {i : Fin n}
    (q : ForwardKeptColumnIndex flag ρ.support i) :
    reverseDiagonalMaleTotal d * (1 - (2 * s + u + p)) ≤ forwardKeptCompetitorMass d q := by
  refine le_trans ?_ (forwardKeptCompetitorMass_ge d q (fun j ↦ (h.score_mem j).1.1))
  have hi := h.max_score i
  have hm := h.omitted_score i
  have hq := h.max_score (forwardInactiveColumnMan q.val)
  have hp := h.pivot_score
  unfold reverseDiagonalMaleTotal at *
  change _ ≤ _ - _ - _ - _ - (diagonalPairAt d (forwardInactiveColumnMan q.val)).1
  nlinarith only [hi, hm, hq, hp]
theorem forbidden_weight_le (h : ReverseMaskGeometry d flag ρ s u p) (i : Fin n) :
    (∑ j ∈ forwardMaskForbiddenTargets μ flag i, reverseSpouseWeights μ d j) ≤
      ENNReal.ofReal (s + u) := by
  have hX : 0 < reverseDiagonalMaleTotal d := by linarith [h.total_ge_two]
  rw [sum_forwardMaskForbiddenTargets_reverseSpouseWeights μ d flag i
    (fun j ↦ (h.score_mem j).1.1) hX]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hX).mpr
  linarith only [h.max_score (μ.symm i), h.omitted_score (μ.symm i)]
theorem pivot_weight_le (h : ReverseMaskGeometry d flag ρ s u p) :
    (∑ j ∈ ρ.support.map μ.toEmbedding, reverseSpouseWeights μ d j) ≤ ENNReal.ofReal p := by
  have hX : 0 < reverseDiagonalMaleTotal d := by linarith [h.total_ge_two]
  simp only [Finset.sum_map, reverseSpouseWeights, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
  change (∑ i ∈ ρ.support, ENNReal.ofReal ((diagonalPairAt d i).1 /
    reverseDiagonalMaleTotal d)) ≤ _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ div_nonneg (h.score_mem i).1.1 hX.le),
    ← Finset.sum_div]
  exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hX).mpr h.pivot_score)
theorem momentControls (h : ReverseMaskGeometry d flag ρ s u p) (K : ℕ) (D C : ℝ)
    (hq : 2 * s + u + p ≤ 1 / 2)
    (hlabel : ∀ k ∈ Finset.Icc 2 K,
      reverseGoodLabelLoss k (reverseSpouseWeights μ d) (ρ.support.map μ.toEmbedding)
        (ENNReal.ofReal (s + u)) ≤ ENNReal.ofReal (1 / 4))
    (hδ : (K : ℝ) * reverseLowerArcError (reverseDiagonalMaleTotal d) ≤ 1 / 4)
    (hu : reverseRawArcError s u ≤ C / Real.sqrt (n : ℝ))
    (ht : ∀ᵐ z ∂offDiagonalScoreLaw n,
      ∀ row, Function.Injective ((splitScorePairs μ).symm (d, z) row)) :
    ReverseCompatibilityControls μ ρ d flag (eligiblePivotRevealSet d flag ρ D)
        (reverseRelaxedArcInflation s u p) D ∧
      ReverseUnfilteredControls μ ρ d flag K (ENNReal.ofReal (s + u)) ∧
      ReverseFilterUpperControls d flag (reverseRawArcError s u) C := by
  let X := reverseDiagonalMaleTotal d
  let U := eligiblePivotRevealSet d flag ρ D
  have hX : 0 < X := by linarith [h.total_ge_two]
  have hm (i : Fin n) : (diagonalPairAt d i).1 ∈ Icc 0 1 :=
    ⟨(h.score_mem i).1.1, (h.score_mem i).1.2.le⟩
  have hU : MeasurableSet U := measurableSet_eligiblePivotRevealSet d flag ρ D
  have hrel : 0 ≤ 2 * s + u + p := by
    linarith [h.max_nonneg, h.omitted_nonneg, h.pivot_nonneg]
  have hraw : 0 ≤ 2 * s + u := by linarith [h.max_nonneg, h.omitted_nonneg]
  have hraw' : 2 * s + u ≤ 1 / 2 := by linarith [h.pivot_nonneg]
  have hhalf (q : ℝ) (hq : q ≤ 1 / 2) : X / 2 ≤ X * (1 - q) := calc
    _ = X * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hX.le
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hU, fun i ↦ (h.score_mem i).2.1, fun i ↦ (h.score_mem i).2.2, hm, hX,
      show 0 < reverseRelaxedArcInflation s u p from by
        unfold reverseRelaxedArcInflation
        linarith,
      fun i q ↦ (total_div_one_add_two_mul_le_remaining hX.le hrel hq).trans
        (h.kept_competitor_ge q),
      fun _ hv ↦ hv.2.1, fun _ hv ↦ hv.2.2, ht, ?_⟩
    exact ae_isExposedRotation_of_forwardReveal_subset μ ρ d flag U hU
      (fun _ hv ↦ (hv.1 ρ).mpr rfl) ht
  · exact ⟨h.forbidden_weight_le, hlabel, hδ⟩
  · refine ⟨show 0 ≤ reverseRawArcError s u from mul_nonneg (by norm_num) hraw, hu,
      fun i q ↦ (total_div_one_add_two_mul_le_remaining hX.le hraw hraw').trans
        (h.competitor_ge q), fun i ↦ (hhalf _ (by linarith [h.max_nonneg])).trans
          (h.available_ge i)⟩
end ReverseMaskGeometry
theorem reverseCompatibilityBudget_of_squareRoot {n K : ℕ} {a X D κ Q V : ℝ}
    (hn : 0 < n) (hQ : 0 ≤ Q) (hV : 0 ≤ V)
    (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (ha : 1 ≤ a) (ha₂ : a ≤ 2) (haQ : a ≤ 1 + Q / Real.sqrt (n : ℝ))
    (hD : D / X ≤ V / Real.sqrt (n : ℝ))
    (hsmall : Real.exp (κ * Q) * (2 * κ * V) ≤ 3 / 32) :
    ENNReal.ofReal a ^ K * (K : ℝ≥0∞) * ENNReal.ofReal (a * D / X) ≤
      ENNReal.ofReal (3 / 32) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have ha₀ : 0 ≤ a := by linarith
  have hpow : a ^ K ≤ Real.exp (κ * Q) := by
    calc
      _ ≤ (Real.exp (Q / Real.sqrt (n : ℝ))) ^ K := pow_le_pow_left₀ ha₀
        (haQ.trans (by linarith only [Real.add_one_le_exp (Q / Real.sqrt (n : ℝ))])) _
      _ = Real.exp ((K : ℝ) * (Q / Real.sqrt (n : ℝ))) := (Real.exp_nat_mul ..).symm
      _ ≤ _ := Real.exp_le_exp.mpr (calc
        _ ≤ (κ * Real.sqrt (n : ℝ)) * (Q / Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hK (div_nonneg hQ hs.le)
        _ = _ := by field_simp)
  have hfac : a * D / X ≤ 2 * (V / Real.sqrt (n : ℝ)) := by
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left hD ha₀).trans
      (mul_le_mul_of_nonneg_right ha₂ (div_nonneg hV hs.le))
  have hfac' : ENNReal.ofReal (a * D / X) ≤
      ENNReal.ofReal (2 * (V / Real.sqrt (n : ℝ))) := ENNReal.ofReal_le_ofReal hfac
  calc
    _ ≤ ENNReal.ofReal (Real.exp (κ * Q)) * (K : ℝ≥0∞) *
        ENNReal.ofReal (2 * (V / Real.sqrt (n : ℝ))) := by
      rw [← ENNReal.ofReal_pow ha₀]
      exact mul_le_mul' (mul_le_mul_left (ENNReal.ofReal_le_ofReal hpow) _) hfac'
    _ = ENNReal.ofReal (Real.exp (κ * Q) * ((K : ℝ) *
        (2 * (V / Real.sqrt (n : ℝ))))) := by
      rw [mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      refine (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hK (by positivity)) (Real.exp_nonneg _)).trans ?_
      refine le_of_eq_of_le ?_ hsmall
      field_simp
      done
theorem eventually_reverseRawMaskBudget (Cx : ℝ) :
    ∀ᶠ n : ℕ in atTop, 1 < n ∧
      2 * (Cx * Real.log n / n) + (n : ℝ) ^ (-11 / 20 : ℝ) ≤ 1 / Real.sqrt (n : ℝ) := by
  have hlog := (((isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).const_mul_left
    (4 * Cx)).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 20 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_gt_atTop (1 : ℕ), hlog, hpow.eventually_ge_atTop 2]
    with n hn hln hpn
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let R := Real.sqrt (n : ℝ)
  have hR : 0 < R := Real.sqrt_pos.mpr hn₀
  have hR2 : R ^ 2 = (n : ℝ) := Real.sq_sqrt hn₀.le
  have hln' : 4 * Cx * Real.log n ≤ R := by
    have hh : |4 * Cx * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 / 2 : ℝ)| := hln
    rw [← Real.sqrt_eq_rpow, abs_of_nonneg hR.le] at hh
    exact (le_abs_self _).trans hh
  have hA : 2 * (Cx * Real.log n / n) ≤ 1 / (2 * R) := by
    calc
      _ = (4 * Cx * Real.log n) / (2 * (n : ℝ)) := by ring
      _ ≤ R / (2 * (n : ℝ)) := div_le_div_of_nonneg_right hln' (by positivity)
      _ = _ := by rw [← hR2]; field_simp
  have hB : (n : ℝ) ^ (-11 / 20 : ℝ) ≤ 1 / (2 * R) := by
    rw [show (-11 / 20 : ℝ) = -(1 / 2 + 1 / 20) by norm_num, Real.rpow_neg hn₀.le,
      Real.rpow_add hn₀, ← Real.sqrt_eq_rpow, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    rw [mul_comm 2]
    exact mul_le_mul_of_nonneg_left hpn hR.le
  exact ⟨hn, (add_le_add hA hB).trans_eq (by ring)⟩
theorem reverseMaleTotal_ge_of_scoreBand {n : ℕ} {X Y c : ℝ}
    (hn : 0 < n) (hc : 0 ≤ c) (hY : 0 < Y)
    (hY' : Y ≤ (n : ℝ) ^ (2 / 5 : ℝ)) (hXY : c * n ≤ X * Y) :
    c * (n : ℝ) ^ (3 / 5 : ℝ) ≤ X := by
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ((le_div_iff₀ hY).mpr ?_).trans ((div_le_iff₀ hY).mpr hXY)
  calc
    _ ≤ (c * (n : ℝ) ^ (3 / 5 : ℝ)) * (n : ℝ) ^ (2 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hY' (by positivity)
    _ = c * (n : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hn₀, show (3 / 5 : ℝ) + 2 / 5 = 1 by norm_num,
        Real.rpow_one]
theorem reversePivotIncrementRatio_le_of_scoreProduct {n : ℕ} {X Y c B D : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y) (hB : 0 ≤ B)
    (hXY : c * n ≤ X * Y) (hD : Y * D ≤ B * Real.sqrt (n : ℝ)) :
    D / X ≤ (B / c) / Real.sqrt (n : ℝ) := by
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn
  have hR : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn₀
  calc
    _ ≤ ((B * Real.sqrt (n : ℝ)) / Y) / X :=
      div_le_div_of_nonneg_right ((le_div_iff₀ hY).mpr (by linarith)) hX.le
    _ = (B * Real.sqrt (n : ℝ)) / (X * Y) := by ring
    _ ≤ (B * Real.sqrt (n : ℝ)) / (c * n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hXY
    _ = (B * Real.sqrt (n : ℝ)) / (c * (Real.sqrt (n : ℝ)) ^ 2) := by
      rw [Real.sq_sqrt hn₀.le]
    _ = _ := by field_simp
private structure EligibleReverseMomentCertificate {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (K L : ℕ) (D s u p : ℝ) : Prop where
  n_pos : 0 < n
  short_scale : 2 ≤ L
  compatibility : ReverseCompatibilityControls μ ρ d flag (eligiblePivotRevealSet d flag ρ D)
    (reverseRelaxedArcInflation s u p) D
  unfiltered : ReverseUnfilteredControls μ ρ d flag K (ENNReal.ofReal (s + u))
  upper : ReverseFilterUpperControls d flag (reverseRawArcError s u) 2
  relaxed_inflation_ge_one : 1 ≤ reverseRelaxedArcInflation s u p
  compatibility_budget : ENNReal.ofReal (reverseRelaxedArcInflation s u p) ^ K *
    (K : ℝ≥0∞) * ENNReal.ofReal
      (reverseRelaxedArcInflation s u p * D / reverseDiagonalMaleTotal d) ≤
    ENNReal.ofReal (3 / 32)
  short_budget : ENNReal.ofReal (1 + reverseRawArcError s u) ^ K *
    ENNReal.ofReal (4 / Real.log (L : ℝ)) ≤ ENNReal.ofReal (3 / 128)
  increment_budget : ENNReal.ofReal
    (Real.sqrt (reverseFilterSecondMomentConstant 2) / (n : ℝ) ^ 2) ≤
    ENNReal.ofReal (3 / 128) * ((K - 1 : ℕ) : ℝ≥0∞)
theorem eventually_eligibleReverseMomentCertificate (K L : ℕ → ℕ)
    {Cx H B V κ c : ℝ} (hCx : 0 ≤ Cx) (hH : 0 ≤ H) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hκ : 0 ≤ κ) (hc : 0 < c)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : H * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * V) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop,
      let s := Cx * Real.log (n : ℝ) / n
      let u := (n : ℝ) ^ (-11 / 20 : ℝ)
      let p := B / Real.sqrt (n : ℝ)
      ∀ (μ ρ : Matching n) (d : DiagonalScorePairs n)
        (flag : OffDiagonalCellIndex n → Bool) (D : ℝ),
        ReverseMaskGeometry d flag ρ s u p →
        c * (n : ℝ) ^ (3 / 5 : ℝ) ≤ reverseDiagonalMaleTotal d →
        (∑ j, (reverseSpouseWeights μ d j) ^ 2) ≤ ENNReal.ofReal (H / n) →
        D / reverseDiagonalMaleTotal d ≤ V / Real.sqrt (n : ℝ) →
        (∀ᵐ z ∂offDiagonalScoreLaw n,
          ∀ row, Function.Injective ((splitScorePairs μ).symm (d, z) row)) →
        EligibleReverseMomentCertificate μ ρ d flag (K n) (L n) D s u p := by
  let s (n : ℕ) := Cx * Real.log (n : ℝ) / n
  let u (n : ℕ) := (n : ℝ) ^ (-11 / 20 : ℝ)
  let δ (n : ℕ) := reverseRawArcError (s n) (u n)
  let R (n : ℕ) := Real.sqrt (n : ℝ)
  have hraw := eventually_reverseRawMaskBudget Cx
  have hδ : ∀ᶠ n in atTop, 0 ≤ δ n ∧ (K n : ℝ) * δ n ≤ 2 * κ := by
    filter_upwards [hraw, hK] with n hn hk
    have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn.1.le)
    have hR : 0 < R n := Real.sqrt_pos.2 hn₀
    have hs : 0 ≤ s n := div_nonneg (mul_nonneg hCx hlog) hn₀.le
    have hu : 0 ≤ u n := Real.rpow_nonneg hn₀.le _
    have hn' : 2 * s n + u n ≤ 1 / R n := hn.2
    have hδn : δ n ≤ 2 / R n := by
      change 2 * (2 * s n + u n) ≤ 2 / R n
      calc
        _ ≤ 2 * (1 / R n) := mul_le_mul_of_nonneg_left hn' (by norm_num)
        _ = _ := by ring
    refine ⟨show 0 ≤ 2 * (2 * s n + u n) by positivity, ?_⟩
    calc
      _ ≤ (K n : ℝ) * (2 / R n) := mul_le_mul_of_nonneg_left hδn (Nat.cast_nonneg _)
      _ ≤ (κ * R n) * (2 / R n) :=
        mul_le_mul_of_nonneg_right hk.2 (div_nonneg (by norm_num) hR.le)
      _ = _ := by field_simp
  have hfilter := eventually_reverseFilterLossBudgets K L δ 2 (2 * κ)
    (hK.mono fun _ h ↦ h.1) hL hδ
  have hlarge : ∀ᶠ n in atTop, 2 * (1 + B) ≤ R n :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  filter_upwards [hraw, hK, hfilter, hlarge,
    eventually_reverseArcLowerBudget_uniform hκ hc]
    with n hraw_n hKn hf hlarge_n hlow
  dsimp only
  intro μ ρ d flag D hgeom hXrate hweights hD ht
  let X := reverseDiagonalMaleTotal d
  let p := B / R n
  let a := reverseRelaxedArcInflation (s n) (u n) p
  have hn : 0 < n := by omega
  have hR : 0 < R n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hraw' : 2 * s n + u n ≤ 1 / R n := hraw_n.2
  have hq₁ : 2 * s n + u n + p ≤ (1 + B) / R n := by
    rw [add_div]
    exact add_le_add_left hraw' p
  have hq : 2 * s n + u n + p ≤ 1 / 2 := hq₁.trans
    ((div_le_iff₀ hR).mpr (by linarith))
  have ha : 1 ≤ a := by
    change 1 ≤ 1 + 2 * (2 * s n + u n + p)
    have hs : 0 ≤ s n := hgeom.max_nonneg
    have hu : 0 ≤ u n := hgeom.omitted_nonneg
    have hp : 0 ≤ p := hgeom.pivot_nonneg
    exact le_add_of_nonneg_right (by positivity)
  have ha₂ : a ≤ 2 := by
    change 1 + 2 * (2 * s n + u n + p) ≤ 2
    linarith
  have haQ : a ≤ 1 + (2 * (1 + B)) / R n := by
    change 1 + 2 * (2 * s n + u n + p) ≤ _
    rw [mul_div_assoc]
    linarith
  have hη : ENNReal.ofReal (s n + u n) ≤ ENNReal.ofReal (1 / R n) :=
    ENNReal.ofReal_le_ofReal (by linarith [hgeom.max_nonneg])
  have hlabel : ∀ k ∈ Finset.Icc 2 (K n),
      reverseGoodLabelLoss k (reverseSpouseWeights μ d) (ρ.support.map μ.toEmbedding)
        (ENNReal.ofReal (s n + u n)) ≤ ENNReal.ofReal (1 / 4) := by
    intro k hk
    have hk' : (k : ℝ) ≤ (K n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact (reverseGoodLabelLoss_le_of_squareRoot hn hH hB (by norm_num : 0 ≤ (1 : ℝ))
      (hk'.trans hKn.2) _ _ _ hweights hgeom.pivot_weight_le hη).trans
      (ENNReal.ofReal_le_ofReal hsmallLabel)
  have hδlo := hlow (K n) X hXrate hKn.2
  have hupper : δ n ≤ 2 / R n := by
    change 2 * (2 * s n + u n) ≤ 2 / R n
    calc
      _ ≤ 2 * (1 / R n) := mul_le_mul_of_nonneg_left hraw' (by norm_num)
      _ = _ := by ring
  obtain ⟨hcomp, hunf, hup⟩ := hgeom.momentControls (μ := μ) (K n) D 2 hq hlabel hδlo hupper ht
  refine ⟨hn, hf.1, hcomp, hunf, hup, ha, ?_, hf.2.1, hf.2.2⟩
  exact reverseCompatibilityBudget_of_squareRoot hn (by linarith) hV hKn.2 ha ha₂ haQ
    hD hsmallCompat
end DiagLP
end

-- PivotSpouseBandMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private def pivotDiagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).2
private def pivotBaseDiagonalBand (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | let X := reverseDiagonalMaleTotal d
       let Y := pivotDiagonalFemaleTotal d
       (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
       2 ≤ Y ∧ Y ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧ (n : ℝ) / 128 ≤ X * Y ∧
       (∀ i, (diagonalPairAt d i).2 / Y ≤ 12 * Real.log n / n) ∧
       ∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (Y - 1)}
theorem normalizedMaleScore_le_of_spouseProduct {n : ℕ} {X Y x : ℝ}
    (hn : 0 < n) (hY : 2 ≤ Y) (hXY : (n : ℝ) / 128 ≤ X * Y)
    (hx : x ≤ 8 * Real.log n / (Y - 1)) :
    x / X ≤ 2048 * Real.log n / n := by
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog := Real.log_nonneg (show 1 ≤ (n : ℝ) by exact_mod_cast hn)
  have hY₀ : 0 < Y := by linarith
  have hY₁ : 0 < Y - 1 := by linarith
  have hXY₀ : 0 < X * Y := (div_pos hn₀ (by norm_num)).trans_le hXY
  have hX₀ : 0 < X := pos_of_mul_pos_left hXY₀ hY₀.le
  have hquot : Y / (Y - 1) ≤ 2 := (div_le_iff₀ hY₁).2 (by linarith)
  calc
    x / X ≤ (8 * Real.log n / (Y - 1)) / X := div_le_div_of_nonneg_right hx hX₀.le
    _ = (8 * Real.log n * (Y / (Y - 1))) / (X * Y) := by
      field_simp
    _ ≤ (8 * Real.log n * 2) / (X * Y) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hquot (mul_nonneg (by norm_num) hlog)) hXY₀.le
    _ ≤ (8 * Real.log n * 2) / ((n : ℝ) / 128) := div_le_div_of_nonneg_left
      (by positivity) (div_pos hn₀ (by norm_num)) hXY
    _ = _ := by ring
end DiagLP
end

-- CoexposureScoreMomentBound
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
end DiagLP
end

-- PivotSpouseSquareRegularity
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
private def largeSpouseAngularSquareSet (n : ℕ) : Set (Fin n → ℝ) :=
  {w | 24 < pittelAngularSquareScore w}
end DiagLP
end

-- ForestDeterministic
section
open scoped BigOperators Classical
namespace DiagLP
end DiagLP
end

-- ForestProductProbability
section
open scoped BigOperators Classical
namespace DiagLP
end DiagLP
end

-- ForestRankOne
section
namespace DiagLP
end DiagLP
end

-- ForestRowThinning
section
open scoped BigOperators Classical
namespace DiagLP
end DiagLP
end

-- ForwardSuccessorRowLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
end DiagLP
end

-- ForwardSuccessorOutcome
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
end DiagLP
end

-- PivotForwardRowDeficit
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
end DiagLP
end

-- PivotForwardForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private def IsSoleForwardExposedRotation {n : ℕ} (p : Profile n) (μ σ : Matching n) : Prop :=
  IsExposedRotation p μ σ ∧ ∀ τ, IsExposedRotation p μ τ → τ = σ
end DiagLP
end

-- PivotLocalEligibility
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
private def certifiedSet {α : Type} [MeasurableSpace α] {t : Set α} (_ : MeasurableSet t) := t
private def LocalPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) : Prop :=
  d ∈ certifiedSet (MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag)
private theorem LocalPivotGeometry.base {n : ℕ} {b A B : ℝ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    (h : LocalPivotGeometry b A B μ ρ d flag) : d ∈ pivotBaseDiagonalBand n := by
  obtain ⟨he,_,_,_,_,_,_,_⟩ := h
  exact he
private theorem LocalPivotGeometry.male_squares {n : ℕ} {b A B : ℝ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    (h : LocalPivotGeometry b A B μ ρ d flag) : (∑ j, (reverseSpouseWeights μ d j) ^ 2) ≤ ENNReal.ofReal (24 / (n : ℝ)) := by
  obtain ⟨_,_,_,_,he,_,_,_⟩ := h
  exact he
private theorem LocalPivotGeometry.omitted_score {n : ℕ} {b A B : ℝ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    (h : LocalPivotGeometry b A B μ ρ d flag) : ∀ j, forwardMaskOmittedMass d flag j ≤ (n : ℝ) ^ (-11 / 20 : ℝ) * reverseDiagonalMaleTotal d := by
  obtain ⟨_,_,_,_,_,_,he,_⟩ := h
  exact he
private theorem LocalPivotGeometry.pivot_score {n : ℕ} {b A B : ℝ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    (h : LocalPivotGeometry b A B μ ρ d flag) : (∑ i ∈ ρ.support, (diagonalPairAt d i).1) ≤ (B / Real.sqrt (n : ℝ)) * reverseDiagonalMaleTotal d := by
  obtain ⟨_,_,_,_,_,_,_,he⟩ := h
  exact he
private noncomputable def localPivotIncrementCap {n : ℕ} (B : ℝ) (d : DiagonalScorePairs n) : ℝ :=
  B * Real.sqrt (n : ℝ) / pivotDiagonalFemaleTotal d
private def IsLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (x : ScoreProfile n)
    (μ ρ : Matching n) : Prop :=
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  LocalPivotGeometry b A B μ ρ z.1 flag ∧
    (forwardRevealWithColumns flag z.2).1 ∈
      eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)
theorem isLocallyEligiblePivot_reconstruct_iff {n : ℕ} {b A B : ℝ}
    (μ ρ : Matching n) (d : DiagonalScorePairs n) (z : OffDiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (hmask : z ∈ forwardScoreMaskEvent d flag) :
    IsLocallyEligiblePivot b A B ((splitScorePairs μ).symm (d, z)) μ ρ ↔
      LocalPivotGeometry b A B μ ρ d flag ∧
        (forwardRevealWithColumns flag z).1 ∈
          eligiblePivotRevealSet d flag ρ (localPivotIncrementCap B d) := by
  have hflag := (forwardMaskOfScores_eq_iff d z flag).mpr hmask
  unfold IsLocallyEligiblePivot
  rw [MeasurableEquiv.apply_symm_apply]
  dsimp only
  rw [hflag]
theorem IsLocallyEligiblePivot.isSoleForwardExposed {n : ℕ} {b A B : ℝ}
    {x : ScoreProfile n} {μ ρ : Matching n}
    (h : IsLocallyEligiblePivot b A B x μ ρ)
    (ht : ∀ row, Function.Injective (x row)) :
    IsSoleForwardExposedRotation (profileOfScores x) μ ρ := by
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  have hmask : z.2 ∈ forwardScoreMaskEvent z.1 flag :=
    (forwardMaskOfScores_eq_iff _ _ _).mp rfl
  have he (τ : Matching n) := (isExposedRotation_iff_forwardRevealExposureEvent μ τ x flag ht
    hmask).trans (h.2.1 τ)
  exact ⟨(he ρ).mpr rfl, fun τ hτ ↦ (he τ).mp hτ⟩
theorem reverseDiagonalMaleTotal_splitScorePairs {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) :
    reverseDiagonalMaleTotal (splitScorePairs μ x).1 = maleSpouseTotal x μ :=
  Finset.sum_congr rfl fun i _ ↦ congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x i)
theorem eventually_localPivotGeometry_certificate (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop, ∀ {b A : ℝ} (μ ρ : Matching n) (d : DiagonalScorePairs n)
      (flag : OffDiagonalCellIndex n → Bool), LocalPivotGeometry b A B μ ρ d flag →
      (∀ᵐ z ∂offDiagonalScoreLaw n,
        ∀ row, Function.Injective ((splitScorePairs μ).symm (d, z) row)) →
      EligibleReverseMomentCertificate μ ρ d flag (K n) (L n) (localPivotIncrementCap B d)
        (2048 * Real.log (n : ℝ) / n) ((n : ℝ) ^ (-11 / 20 : ℝ))
        (B / Real.sqrt (n : ℝ)) := by
  have hc : 0 < (1 / 128 : ℝ) := by norm_num
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ (1 / 128 : ℝ) * (n : ℝ) ^ (3 / 5 : ℝ) :=
    ((((tendsto_rpow_atTop (by norm_num : 0 < (3 / 5 : ℝ))).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc).eventually_ge_atTop 2)
  filter_upwards [eventually_eligibleReverseMomentCertificate K L
    (Cx := 2048) (H := 24) (V := B / (1 / 128)) (by norm_num) (by norm_num) hB
    (div_nonneg hB hc.le) hκ hc hK hL hsmallLabel hsmallCompat,
    hlarge, eventually_gt_atTop (0 : ℕ)] with n hcert hlarge hn
  intro b A μ ρ d flag hgeom ht
  have hY : 0 < pivotDiagonalFemaleTotal d := lt_of_lt_of_le (by norm_num) (LocalPivotGeometry.base hgeom).2.1
  have hXY : (1 / 128 : ℝ) * n ≤ reverseDiagonalMaleTotal d * pivotDiagonalFemaleTotal d := by
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact (LocalPivotGeometry.base hgeom).2.2.2.1
  have hXrate := reverseMaleTotal_ge_of_scoreBand hn hc.le hY (LocalPivotGeometry.base hgeom).2.2.1 hXY
  have hX : 0 < reverseDiagonalMaleTotal d := lt_of_lt_of_le (by norm_num) (hlarge.trans hXrate)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n from hn))
  have hgeometry : ReverseMaskGeometry d flag ρ (2048 * Real.log (n : ℝ) / n)
      ((n : ℝ) ^ (-11 / 20 : ℝ)) (B / Real.sqrt (n : ℝ)) := by
    refine ⟨(LocalPivotGeometry.base hgeom).1, hlarge.trans hXrate, ?_, by positivity, by positivity, ?_,
      (LocalPivotGeometry.omitted_score hgeom), (LocalPivotGeometry.pivot_score hgeom)⟩
    · exact div_nonneg (mul_nonneg (by norm_num) hlog) (Nat.cast_nonneg _)
    · intro i
      apply (div_le_iff₀ hX).mp
      exact normalizedMaleScore_le_of_spouseProduct hn (LocalPivotGeometry.base hgeom).2.1 (LocalPivotGeometry.base hgeom).2.2.2.1
        ((LocalPivotGeometry.base hgeom).2.2.2.2.2 i)
  have hD : pivotDiagonalFemaleTotal d * localPivotIncrementCap B d ≤ B * Real.sqrt (n : ℝ) := by
    rw [localPivotIncrementCap, mul_comm, div_mul_cancel₀ _ hY.ne']
  exact hcert μ ρ d flag _ hgeometry hXrate (LocalPivotGeometry.male_squares hgeom)
    (reversePivotIncrementRatio_le_of_scoreProduct hn hc hX hY hB hXY hD) ht
theorem eventually_ae_diagonal_localPivotGeometry_certificate (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop, ∀ μ : Matching n, ∀ᵐ d ∂diagonalScoreLaw n,
      ∀ {b A : ℝ} (ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool),
        LocalPivotGeometry b A B μ ρ d flag →
        EligibleReverseMomentCertificate μ ρ d flag (K n) (L n) (localPivotIncrementCap B d)
          (2048 * Real.log (n : ℝ) / n) ((n : ℝ) ^ (-11 / 20 : ℝ))
          (B / Real.sqrt (n : ℝ)) := by
  filter_upwards [eventually_localPivotGeometry_certificate K L hB hκ hK hL hsmallLabel
    hsmallCompat] with n hn μ
  filter_upwards [ae_diagonal_ae_injective_scoreRows μ] with d ht b A ρ flag hgeom
  exact hn μ ρ d flag hgeom ht
private theorem measurable_diagonalMaleScore {n : ℕ} (i : Fin n) :
    Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).1) :=
  (measurable_pi_apply _).fst
private theorem measurable_diagonalFemaleScore {n : ℕ} (i : Fin n) :
    Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
  (measurable_pi_apply _).snd
private theorem measurable_pivotDiagonalFemaleTotal (n : ℕ) :
    Measurable (@pivotDiagonalFemaleTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_diagonalFemaleScore i
theorem measurableSet_localPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurableSet {d : DiagonalScorePairs n | LocalPivotGeometry b A B μ ρ d flag} := MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag

private theorem measurable_jointForwardPivotIncrement {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (m : Fin n) :
    Measurable (fun z : DiagonalScorePairs n × ForwardRevealedMaleScores flag ↦
      forwardPivotIncrement z.1 flag ρ z.2 m) := by
  by_cases hm : ρ m ≠ m
  · let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    by_cases hq : flag q = true
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = true := hq
      simp only [forwardPivotIncrement, dif_pos hm, dif_pos hq']
      exact (((measurable_pi_apply (⟨q, hq⟩ : ForwardActiveCellIndex flag)).comp
          (measurable_snd : Measurable (@Prod.snd (DiagonalScorePairs n) _))).sub
          ((measurable_diagonalMaleScore m).comp measurable_fst))
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) ≠ true := hq
      simp only [forwardPivotIncrement, dif_pos hm, dif_neg hq']
      exact measurable_const
  · simp only [forwardPivotIncrement, dif_neg hm]
    exact measurable_const
theorem measurableSet_jointEligiblePivotReveal {n : ℕ}
    (B : ℝ) (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) :
    MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      z.2 ∈ eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)} := by
  have hs : MeasurableSet {v : ForwardRevealedMaleScores flag |
      ∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ} := by
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun τ ↦ ?_
    by_cases ht : τ = ρ
    · simpa only [ht, iff_true, ofPred_mem_eq] using
        measurableSet_forwardRevealExposureEvent ρ flag
    · simpa only [ht, iff_false, ← mem_compl_iff, ofPred_mem_eq] using
        (measurableSet_forwardRevealExposureEvent τ flag).compl
  have hcap : Measurable (fun z : DiagonalScorePairs n × ForwardRevealedMaleScores flag ↦
      localPivotIncrementCap B z.1) :=
    measurable_const.div ((measurable_pivotDiagonalFemaleTotal n).comp measurable_fst)
  have hnonneg : MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      ∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement z.1 flag ρ z.2 m} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_le measurable_const (measurable_jointForwardPivotIncrement flag ρ m)
  have hsum : MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      (∑ m ∈ ρ.support, forwardPivotIncrement z.1 flag ρ z.2 m) ≤
        localPivotIncrementCap B z.1} :=
    measurableSet_le (Finset.measurable_sum _ fun m _ ↦
      measurable_jointForwardPivotIncrement flag ρ m) hcap
  exact (measurable_snd hs).inter (hnonneg.inter hsum)
theorem measurable_jointForwardMaskOfScores (n : ℕ) :
    Measurable (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦
      forwardMaskOfScores z.1 z.2) := by
  apply measurable_pi_iff.2
  intro q
  apply measurable_to_bool
  have hz : Measurable (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦ z.2 q) :=
    (measurable_pi_apply q).comp measurable_snd
  have he : (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦
      forwardMaskOfScores z.1 z.2 q) ⁻¹' {true} =
      {z | (diagonalPairAt z.1 q.val.1).1 < (z.2 q).1} ∩
      {z | (z.2 q).2 < (diagonalPairAt z.1 q.val.2).2} := by
    ext z
    exact forwardCellFlag_eq_true.trans Set.mem_prod
  rw [he]
  exact (measurableSet_lt ((measurable_diagonalMaleScore _).comp measurable_fst) hz.fst).inter
    (measurableSet_lt hz.snd ((measurable_diagonalFemaleScore _).comp measurable_fst))
theorem measurableSet_isLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (μ ρ : Matching n) :
    MeasurableSet {x : ScoreProfile n | IsLocallyEligiblePivot b A B x μ ρ} := by
  let Z := splitScorePairs μ
  let mask (x : ScoreProfile n) := forwardMaskOfScores (Z x).1 (Z x).2
  let E (flag : OffDiagonalCellIndex n → Bool) := {x : ScoreProfile n | mask x = flag ∧
    LocalPivotGeometry b A B μ ρ (Z x).1 flag ∧
    (forwardRevealWithColumns flag (Z x).2).1 ∈
      eligiblePivotRevealSet (Z x).1 flag ρ (localPivotIncrementCap B (Z x).1)}
  have hmask : Measurable mask := (measurable_jointForwardMaskOfScores n).comp Z.measurable
  have hE : {x : ScoreProfile n | IsLocallyEligiblePivot b A B x μ ρ} = ⋃ flag, E flag := by
    ext x
    refine ⟨fun h ↦ mem_iUnion.mpr ⟨mask x, rfl, h.1, h.2⟩, fun h ↦ ?_⟩
    obtain ⟨f, hf, hg, hv⟩ := mem_iUnion.mp h
    subst f
    exact ⟨hg, hv⟩
  rw [hE]
  refine MeasurableSet.iUnion fun flag ↦ (hmask (measurableSet_singleton flag)).inter
    ((((measurable_fst.comp Z.measurable) (measurableSet_localPivotGeometry b A B μ ρ flag))).inter ?_)
  exact (measurableSet_jointEligiblePivotReveal B flag ρ).preimage
    ((measurable_fst.comp Z.measurable).prodMk
      (measurable_fst.comp ((measurable_forwardRevealWithColumns flag).comp
        (measurable_snd.comp Z.measurable))))
end DiagLP
end

-- PivotMarkedDecorationCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
variable {n : ℕ}
private noncomputable def markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun σ ↦ σ.support.card ≤ K ∧
    σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x
theorem mem_markedFilteredChoices {μ ρ σ : Matching n} {flag : OffDiagonalCellIndex n → Bool}
    {K L : ℕ} {t : ℝ} {x : ScoreProfile n} :
    σ ∈ markedFilteredChoices μ ρ flag K L t x ↔ σ.support.card ≤ K ∧
      σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x := by
  classical
  simp [markedFilteredChoices]
theorem measurableSet_mem_markedFilteredChoices (μ ρ σ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    {t : ScoreProfile n → ℝ} (ht : Measurable t) :
    MeasurableSet {x : ScoreProfile n | σ ∈ markedFilteredChoices μ ρ flag K L (t x) x} := by
  classical
  have hinc :
      MeasurableSet {x : ScoreProfile n | reverseCollectionIncrementGood x μ σ (t x)} := by
    have he : {x : ScoreProfile n | reverseCollectionIncrementGood x μ σ (t x)} =
        ⋂ w : σ.support, {x : ScoreProfile n |
          reverseScoreIncrement x μ w.val (μ.symm (σ w.val)) ≤ t x} := by
      ext x
      exact ⟨fun h ↦ mem_iInter.mpr fun w ↦ h w.val w.property,
        fun h w hw ↦ mem_iInter.mp h ⟨w, hw⟩⟩
    rw [he]
    exact MeasurableSet.iInter fun w ↦
      measurableSet_le (measurable_reverseScoreIncrement μ w.val (μ.symm (σ w.val))) ht
  have hcomp : MeasurableSet {x : ScoreProfile n |
      σ ∈ compatibleReverseSupportFamily μ ρ flag σ.support.card (profileOfScores x)} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete : MeasurableSet
      {p : Profile n | σ ∈ compatibleReverseSupportFamily μ ρ flag σ.support.card p})
  simp only [mem_markedFilteredChoices, filteredReverseSupportFamily, Finset.mem_filter,
    ofPred_and]
  exact (MeasurableSet.const _).inter (hcomp.inter ((MeasurableSet.const _).inter hinc))
theorem measurable_card_markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    {t : ScoreProfile n → ℝ} (ht : Measurable t) :
    Measurable (fun x ↦ ((markedFilteredChoices μ ρ flag K L (t x) x).card : ℝ)) := by
  have h := measurable_finsetCard_of_mem (fun x ↦ markedFilteredChoices μ ρ flag K L (t x) x)
    (fun σ ↦ measurableSet_mem_markedFilteredChoices μ ρ σ flag K L ht)
  simpa only [Function.comp_def, ENNReal.toReal_natCast] using
    ENNReal.measurable_toReal.comp h
private noncomputable def localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsLocallyEligiblePivot b A B x μ ρ then
    ((markedFilteredChoices μ ρ (forwardMaskOfScores (splitScorePairs μ x).1
      (splitScorePairs μ x).2) K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x).card : ℝ)
    else 0
private theorem measurable_mask_switch {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Countable β] [MeasurableSingletonClass β] {M : α → β}
    (hM : Measurable M) {f : β → α → γ} (hf : ∀ j, Measurable (f j)) :
    Measurable (fun x ↦ f (M x) x) := by
  intro s hs
  let E (j : β) := {x : α | M x = j ∧ f j x ∈ s}
  have he : (fun x ↦ f (M x) x) ⁻¹' s = ⋃ j, E j := by
    ext x
    change f (M x) x ∈ s ↔ x ∈ ⋃ j, E j
    simp only [mem_iUnion, E, mem_ofPred_eq]
    exact ⟨fun hx ↦ ⟨M x, rfl, hx⟩, fun ⟨j, hj, hx⟩ ↦ hj.symm ▸ hx⟩
  rw [he]
  exact MeasurableSet.iUnion fun j ↦ (hM (measurableSet_singleton j)).inter (hf j hs)
theorem measurable_localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    Measurable (localFilteredDecorationCount b A B K L μ ρ) := by
  classical
  let M (x : ScoreProfile n) :=
    forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2
  let t (x : ScoreProfile n) := reverseIncrementCutoff n (maleSpouseTotal x μ)
  let f (flag : OffDiagonalCellIndex n → Bool) (x : ScoreProfile n) :=
    ((markedFilteredChoices μ ρ flag K L (t x) x).card : ℝ)
  have hM : Measurable M :=
    (measurable_jointForwardMaskOfScores n).comp (splitScorePairs μ).measurable
  have ht : Measurable t := measurable_const.div (measurable_maleSpouseTotal μ)
  have hf (flag : OffDiagonalCellIndex n → Bool) : Measurable (f flag) :=
    measurable_card_markedFilteredChoices μ ρ flag K L ht
  exact (measurable_mask_switch hM hf).ite (measurableSet_isLocallyEligiblePivot b A B μ ρ)
    measurable_const
theorem localFilteredDecorationCount_nonneg (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (x : ScoreProfile n) :
    0 ≤ localFilteredDecorationCount b A B K L μ ρ x := by
  classical
  unfold localFilteredDecorationCount
  split <;> positivity
theorem localFilteredDecorationCount_le_factorial (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (x : ScoreProfile n) :
    localFilteredDecorationCount b A B K L μ ρ x ≤ (n.factorial : ℝ) := by
  classical
  unfold localFilteredDecorationCount
  split
  · apply Nat.cast_le.mpr
    simpa only [Fintype.card_perm, Fintype.card_fin] using
      Finset.card_le_univ (markedFilteredChoices μ ρ
        (forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2)
        K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x)
  · positivity
theorem integrable_localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (ν : Measure (ScoreProfile n)) [IsFiniteMeasure ν] :
    Integrable (localFilteredDecorationCount b A B K L μ ρ) ν := by
  refine (integrable_const (n.factorial : ℝ)).mono'
    (measurable_localFilteredDecorationCount b A B K L μ ρ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (localFilteredDecorationCount_nonneg b A B K L μ ρ x)]
  exact localFilteredDecorationCount_le_factorial b A B K L μ ρ x
theorem localFilteredDecorationCount_of_eligible_of_fixedMask {b A B : ℝ}
    (K L : ℕ) {μ ρ : Matching n} {x : ScoreProfile n} {flag : OffDiagonalCellIndex n → Bool}
    (h : IsLocallyEligiblePivot b A B x μ ρ)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag) :
    localFilteredDecorationCount b A B K L μ ρ x = ((
      markedFilteredChoices μ ρ flag K L
        (reverseIncrementCutoff n (reverseDiagonalMaleTotal (splitScorePairs μ x).1)) x).card :
      ℝ) := by
  classical
  rw [localFilteredDecorationCount, if_pos h, (forwardMaskOfScores_eq_iff _ _ _).mpr hmask,
    reverseDiagonalMaleTotal_splitScorePairs]
section MatchingEndpoints
variable {x : ScoreProfile n} {μ₀ μ ρ σ : Matching n}
  {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
end MatchingEndpoints
end DiagLP
end

-- PivotRestrictedMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
theorem forwardMaskRevealLaw_mono {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    {U V : Set (ForwardRevealedMaleScores flag)} (hUV : U ⊆ V) :
    forwardMaskRevealLaw d flag U ≤ forwardMaskRevealLaw d flag V :=
  Measure.restrict_mono (Set.preimage_mono hUV) le_rfl
theorem ReverseCompatibilityControls.restrict_reveal {n : ℕ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    {U V : Set (ForwardRevealedMaleScores flag)} {a D : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hV : MeasurableSet V) (hVU : V ⊆ U) :
    ReverseCompatibilityControls μ ρ d flag V a D :=
  ⟨hV, h.female_nonneg, h.female_lt_one, h.male_mem, h.male_total_pos, h.inflation_pos,
    h.kept_mass, fun v hv ↦ h.increment_nonneg v (hVU hv),
    fun v hv ↦ h.increment_sum_le v (hVU hv), h.tie_free,
    ae_mono (forwardMaskRevealLaw_mono d flag hVU) h.pivot_exposed⟩
section ConditionalOrder
variable {Ω : Type*} {m m₀ : MeasurableSpace Ω}
end ConditionalOrder
private noncomputable def stableMarkScoreLaw {n : ℕ} (μ : Matching n) : Measure (ScoreProfile n) :=
  (continuousScoreLaw n).restrict {x | IsScoreStable x μ}
private instance {n : ℕ} (μ : Matching n) : IsFiniteMeasure (stableMarkScoreLaw μ) :=
  inferInstanceAs (IsFiniteMeasure ((continuousScoreLaw n).restrict _))
theorem lintegral_stableMarkScoreLaw {n : ℕ} (μ : Matching n)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂stableMarkScoreLaw μ) =
      ∫⁻ d, ∫⁻ z, f ((splitScorePairs μ).symm (d, z))
        ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) ∂diagonalScoreLaw n := by
  simpa only [stableMarkScoreLaw, mem_univ, and_true, Measure.restrict_univ] using
    continuousScoreLaw_lintegral_stable_and_diagonal μ (C := univ) MeasurableSet.univ hf
theorem lintegral_offDiagonalNonblocking_eq_sum_masks {n : ℕ}
    (d : DiagonalScorePairs n) (f : OffDiagonalScorePairs n → ℝ≥0∞) :
    (∫⁻ z, f z ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d))) =
      ∑ flag : OffDiagonalCellIndex n → Bool,
        ∫⁻ z in forwardScoreMaskEvent d flag, f z
          ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) := by
  classical
  have hU : (⋃ flag ∈ (Finset.univ : Finset (OffDiagonalCellIndex n → Bool)),
      forwardScoreMaskEvent d flag) = univ := by
    ext z
    constructor
    · exact fun _ ↦ mem_univ _
    · intro _
      exact mem_iUnion.mpr ⟨forwardMaskOfScores d z, mem_iUnion.mpr
        ⟨Finset.mem_univ _, (forwardMaskOfScores_eq_iff _ _ _).mp rfl⟩⟩
  let ν := (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)
  calc
    _ = ∫⁻ z in ⋃ flag ∈ (Finset.univ : Finset (OffDiagonalCellIndex n → Bool)),
        forwardScoreMaskEvent d flag, f z ∂ν := by rw [hU, Measure.restrict_univ]
    _ = _ := by
      refine lintegral_biUnion_finset ?_ (fun flag _ ↦ measurableSet_forwardScoreMaskEvent d flag) _
      intro a _ b _ hab
      exact Set.disjoint_left.mpr fun z ha hb ↦ hab
        (((forwardMaskOfScores_eq_iff d z a).mpr ha).symm.trans
          ((forwardMaskOfScores_eq_iff d z b).mpr hb))
end DiagLP
end

-- PivotFullRevealLaw
section
open MeasureTheory Set StableMarriage
open scoped ENNReal
namespace DiagLP
private abbrev PivotMaleRevealData (n : ℕ) :=
  DiagonalScorePairs n × (OffDiagonalCellIndex n → Bool) × (OffDiagonalCellIndex n → ℝ)
private abbrev PivotFullRevealData (n : ℕ) := PivotMaleRevealData n × (OffDiagonalCellIndex n → ℝ)
variable {n : ℕ}
private def extendPivotActiveValues (flag : OffDiagonalCellIndex n → Bool)
    (a : ForwardActiveCellIndex flag → ℝ) (q : OffDiagonalCellIndex n) : ℝ :=
  if h : flag q = true then a ⟨q, h⟩ else 0
theorem measurable_extendPivotActiveValues (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (extendPivotActiveValues flag) := by
  apply measurable_pi_iff.2
  intro q
  by_cases h : flag q = true
  · simpa only [extendPivotActiveValues, dif_pos h] using
      (measurable_pi_apply (⟨q, h⟩ : ForwardActiveCellIndex flag))
  · simp only [extendPivotActiveValues, dif_neg h]
    exact measurable_const
private noncomputable def pivotMaleRevealFromScores (z : DiagonalScorePairs n × OffDiagonalScorePairs n) :
    PivotMaleRevealData n :=
  let flag := forwardMaskOfScores z.1 z.2
  (z.1, flag, fun q ↦ if flag q = true then (z.2 q).1 else 0)
private noncomputable def pivotFullRevealFromScores (z : DiagonalScorePairs n × OffDiagonalScorePairs n) :
    PivotFullRevealData n :=
  (pivotMaleRevealFromScores z,
    fun q ↦ if forwardMaskOfScores z.1 z.2 q = true then (z.2 q).2 else 0)
theorem measurable_pivotMaleRevealFromScores (n : ℕ) :
    Measurable (@pivotMaleRevealFromScores n) := by
  have hmask := measurable_jointForwardMaskOfScores n
  apply measurable_fst.prodMk (hmask.prodMk ?_)
  apply measurable_pi_iff.2
  intro q
  exact Measurable.ite (measurableSet_eq_fun ((measurable_pi_apply q).comp hmask)
    measurable_const) ((measurable_pi_apply q).comp measurable_snd).fst measurable_const
theorem measurable_pivotFullRevealFromScores (n : ℕ) :
    Measurable (@pivotFullRevealFromScores n) := by
  have hmask := measurable_jointForwardMaskOfScores n
  apply (measurable_pivotMaleRevealFromScores n).prodMk
  apply measurable_pi_iff.2
  intro q
  exact Measurable.ite (measurableSet_eq_fun ((measurable_pi_apply q).comp hmask)
    measurable_const) ((measurable_pi_apply q).comp measurable_snd).snd measurable_const
private noncomputable def pivotMaleReveal (μ : Matching n) (x : ScoreProfile n) : PivotMaleRevealData n :=
  pivotMaleRevealFromScores (splitScorePairs μ x)
private noncomputable def pivotFullReveal (μ : Matching n) (x : ScoreProfile n) : PivotFullRevealData n :=
  pivotFullRevealFromScores (splitScorePairs μ x)
theorem measurable_pivotMaleReveal (μ : Matching n) : Measurable (pivotMaleReveal μ) :=
  (measurable_pivotMaleRevealFromScores n).comp (splitScorePairs μ).measurable
theorem measurable_pivotFullReveal (μ : Matching n) : Measurable (pivotFullReveal μ) :=
  (measurable_pivotFullRevealFromScores n).comp (splitScorePairs μ).measurable
private noncomputable def pivotMaleRevealSpace (μ : Matching n) : MeasurableSpace (ScoreProfile n) :=
  MeasurableSpace.comap (pivotMaleReveal μ) inferInstance
private noncomputable def pivotFullRevealSpace (μ : Matching n) : MeasurableSpace (ScoreProfile n) :=
  MeasurableSpace.comap (pivotFullReveal μ) inferInstance
theorem pivotMaleRevealSpace_le (μ : Matching n) :
    pivotMaleRevealSpace μ ≤ (inferInstance : MeasurableSpace (ScoreProfile n)) :=
  (measurable_pivotMaleReveal μ).comap_le
theorem pivotFullRevealSpace_le (μ : Matching n) :
    pivotFullRevealSpace μ ≤ (inferInstance : MeasurableSpace (ScoreProfile n)) :=
  (measurable_pivotFullReveal μ).comap_le
theorem pivotMaleRevealSpace_le_full (μ : Matching n) :
    pivotMaleRevealSpace μ ≤ pivotFullRevealSpace μ := by
  unfold pivotMaleRevealSpace pivotFullRevealSpace
  change MeasurableSpace.comap (Prod.fst ∘ pivotFullReveal μ) _ ≤ _
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_fst.comap_le
private def pivotMaleRevealSection (flag : OffDiagonalCellIndex n → Bool)
    (z : DiagonalScorePairs n × ForwardRevealedMaleScores flag) : PivotMaleRevealData n :=
  (z.1, flag, extendPivotActiveValues flag z.2)
private def pivotFullRevealSection (flag : OffDiagonalCellIndex n → Bool)
    (z : DiagonalScorePairs n × ForwardRevealedMaleScores flag × ForwardRevealedMaleScores flag) :
    PivotFullRevealData n :=
  (pivotMaleRevealSection flag (z.1, z.2.1), extendPivotActiveValues flag z.2.2)
theorem measurable_pivotMaleRevealSection (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (pivotMaleRevealSection flag) :=
  measurable_fst.prodMk
    (measurable_const.prodMk ((measurable_extendPivotActiveValues flag).comp measurable_snd))
theorem measurable_pivotFullRevealSection (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (pivotFullRevealSection flag) :=
  ((measurable_pivotMaleRevealSection flag).comp
    (measurable_fst.prodMk measurable_snd.fst)).prodMk
    ((measurable_extendPivotActiveValues flag).comp measurable_snd.snd)
theorem pivotMaleReveal_reconstruct (μ : Matching n) (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (hflag : z ∈ forwardScoreMaskEvent d flag) :
    pivotMaleReveal μ ((splitScorePairs μ).symm (d, z)) =
      pivotMaleRevealSection flag (d, (forwardRevealWithColumns flag z).1) := by
  have he : forwardMaskOfScores d z = flag := (forwardMaskOfScores_eq_iff d z flag).2 hflag
  simp only [pivotMaleReveal, MeasurableEquiv.apply_symm_apply, pivotMaleRevealFromScores, he,
    pivotMaleRevealSection]
  congr 2
theorem pivotFullReveal_reconstruct (μ : Matching n) (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (hflag : z ∈ forwardScoreMaskEvent d flag) :
    pivotFullReveal μ ((splitScorePairs μ).symm (d, z)) =
      pivotFullRevealSection flag
        (d, (forwardRevealWithColumns flag z).1, fun q ↦ (z q.val).2) := by
  have he : forwardMaskOfScores d z = flag := (forwardMaskOfScores_eq_iff d z flag).2 hflag
  apply Prod.ext
  · exact pivotMaleReveal_reconstruct μ d z flag hflag
  · simp only [pivotFullReveal, MeasurableEquiv.apply_symm_apply, pivotFullRevealFromScores,
      pivotFullRevealSection, he]
    funext q
    by_cases h : flag q = true <;> simp [extendPivotActiveValues, h]
private def pivotEligibleRevealDataSet (b A B : ℝ) (μ ρ : Matching n) : Set (PivotMaleRevealData n) :=
  {z | LocalPivotGeometry b A B μ ρ z.1 z.2.1 ∧
    (fun q : ForwardActiveCellIndex z.2.1 ↦ z.2.2 q.val) ∈
      eligiblePivotRevealSet z.1 z.2.1 ρ (localPivotIncrementCap B z.1)}
theorem measurableSet_pivotEligibleRevealDataSet (b A B : ℝ) (μ ρ : Matching n) :
    MeasurableSet (pivotEligibleRevealDataSet b A B μ ρ) := by
  let F (flag : OffDiagonalCellIndex n → Bool) (z : PivotMaleRevealData n) :
      DiagonalScorePairs n × ForwardRevealedMaleScores flag :=
    (z.1, fun q ↦ z.2.2 q.val)
  have hF (flag : OffDiagonalCellIndex n → Bool) : Measurable (F flag) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun q ↦
      (measurable_pi_apply q.val).comp measurable_snd.snd)
  let E (flag : OffDiagonalCellIndex n → Bool) : Set (PivotMaleRevealData n) :=
    {z | z.2.1 = flag} ∩
    (Prod.fst ⁻¹' {d | LocalPivotGeometry b A B μ ρ d flag} ∩
      F flag ⁻¹' {z | z.2 ∈ eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)})
  have he : pivotEligibleRevealDataSet b A B μ ρ = ⋃ flag, E flag := by
    ext z
    refine ⟨fun h ↦ mem_iUnion.mpr ⟨z.2.1, rfl, h.1, h.2⟩, fun h ↦ ?_⟩
    obtain ⟨flag, heq, hd, ha⟩ := mem_iUnion.mp h
    change z.2.1 = flag at heq
    subst flag
    exact ⟨hd, ha⟩
  rw [he]
  refine MeasurableSet.iUnion fun flag ↦
    (measurableSet_eq_fun measurable_snd.fst measurable_const).inter ?_
  exact ((measurableSet_localPivotGeometry b A B μ ρ flag).preimage measurable_fst).inter
    ((measurableSet_jointEligiblePivotReveal B flag ρ).preimage (hF flag))
theorem mem_pivotEligibleRevealDataSet_iff (b A B : ℝ) (μ ρ : Matching n)
    (x : ScoreProfile n) :
    pivotMaleReveal μ x ∈ pivotEligibleRevealDataSet b A B μ ρ ↔
      IsLocallyEligiblePivot b A B x μ ρ := by
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  have h : (fun q : ForwardActiveCellIndex flag ↦
      (pivotMaleReveal μ x).2.2 q.val) = (forwardRevealWithColumns flag z.2).1 := by
    funext q
    change (if flag q.val = true then (z.2 q.val).1 else 0) = (z.2 q.val).1
    rw [if_pos q.property]
  change (LocalPivotGeometry b A B μ ρ z.1 flag ∧
    (fun q : ForwardActiveCellIndex flag ↦ (pivotMaleReveal μ x).2.2 q.val) ∈
      eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)) ↔
    IsLocallyEligiblePivot b A B x μ ρ
  rw [h]
  rfl
theorem measurableSet_isLocallyEligiblePivot_maleRevealSpace (b A B : ℝ)
    (μ ρ : Matching n) :
    @MeasurableSet (ScoreProfile n) (pivotMaleRevealSpace μ)
      {x | IsLocallyEligiblePivot b A B x μ ρ} := by
  exact MeasurableSpace.measurableSet_comap.mpr
    ⟨pivotEligibleRevealDataSet b A B μ ρ, measurableSet_pivotEligibleRevealDataSet b A B μ ρ,
      Set.ext fun _ ↦ mem_pivotEligibleRevealDataSet_iff b A B μ ρ _⟩
private noncomputable def pivotActiveMaleIntervalLaw (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Measure (ForwardRevealedMaleScores flag) :=
  Measure.pi fun q : ForwardActiveCellIndex flag ↦
    unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)
private noncomputable def pivotActiveFemaleIntervalLaw (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Measure (ForwardRevealedMaleScores flag) :=
  Measure.pi fun q : ForwardActiveCellIndex flag ↦
    unitScoreLaw.restrict (Iio (diagonalPairAt d q.val.val.2).2)
private instance (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (pivotActiveFemaleIntervalLaw d flag) := by
  unfold pivotActiveFemaleIntervalLaw
  infer_instance
private def pivotFullRevealWithColumns (flag : OffDiagonalCellIndex n → Bool)
    (z : OffDiagonalScorePairs n) :
    ForwardRevealedMaleScores flag × ForwardRevealedMaleScores flag ×
      ForwardInactiveColumns flag :=
  ((forwardRevealWithColumns flag z).1, fun q ↦ (z q.val).2, (forwardRevealWithColumns flag z).2)
theorem measurePreserving_pivotFullRevealWithColumns (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurePreserving (pivotFullRevealWithColumns flag) (forwardMaskRevealLaw d flag univ)
      ((pivotActiveMaleIntervalLaw d flag).prod ((pivotActiveFemaleIntervalLaw d flag).prod
        (forwardScoreMaskInactiveColumnLaw d flag))) := by
  let m (q : ForwardActiveCellIndex flag) :=
    unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)
  let f (q : ForwardActiveCellIndex flag) :=
    unitScoreLaw.restrict (Iio (diagonalPairAt d q.val.val.2).2)
  let (q : ForwardActiveCellIndex flag) : IsFiniteMeasure (m q) := by dsimp [m]; infer_instance
  let (q : ForwardActiveCellIndex flag) : IsFiniteMeasure (f q) := by dsimp [f]; infer_instance
  have hActive := measurePreserving_arrowProdEquivProdArrow ℝ ℝ
    (ForwardActiveCellIndex flag) m f
  have hInactive := measurePreserving_forwardInactiveColumnsEquiv d flag
  have h :=
    (measurePreserving_prodAssoc (pivotActiveMaleIntervalLaw d flag)
      (pivotActiveFemaleIntervalLaw d flag) (forwardScoreMaskInactiveColumnLaw d flag)).comp
        ((hActive.prod hInactive).comp (measurePreserving_offDiagonalScoreLaw_splitMask d flag))
  rw [forwardMaskRevealLaw, preimage_univ, Measure.restrict_univ]
  exact h
private noncomputable def pivotInactiveSectionMean (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (F : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞)
    (a : ForwardRevealedMaleScores flag) : ℝ≥0∞ :=
  ∫⁻ c, F (a, c) ∂Measure.pi (normalizedForwardInactiveColumnLaw d flag)
theorem measurable_pivotInactiveSectionMean (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    {F : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hF : Measurable F) (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2)
    (hy1 : ∀ i, (diagonalPairAt d i).2 < 1) :
    Measurable (pivotInactiveSectionMean d flag F) := by
  let (i : Fin n) : IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag i) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  exact hF.lintegral_prod_right'
theorem lintegral_pivotFullReveal_test_eq_inactiveSectionMean
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    {F : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hF : Measurable F)
    {G : ForwardRevealedMaleScores flag × ForwardRevealedMaleScores flag → ℝ≥0∞}
    (hG : Measurable G) (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2)
    (hy1 : ∀ i, (diagonalPairAt d i).2 < 1) :
    let R := pivotFullRevealWithColumns flag
    let μ := forwardMaskRevealLaw d flag univ
    (∫⁻ z, G ((R z).1, (R z).2.1) * F ((R z).1, (R z).2.2) ∂μ) =
      ∫⁻ z, G ((R z).1, (R z).2.1) * pivotInactiveSectionMean d flag F (R z).1 ∂μ := by
  dsimp only
  let A := ForwardRevealedMaleScores flag
  let C := ForwardInactiveColumns flag
  let M := pivotActiveMaleIntervalLaw d flag
  let W := pivotActiveFemaleIntervalLaw d flag
  let L := forwardScoreMaskInactiveColumnLaw d flag
  let (i : Fin n) : IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag i) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  let h := (measurePreserving_prodAssoc M W L).symm.comp
    (measurePreserving_pivotFullRevealWithColumns d flag)
  let F₁ (p : (A × A) × C) := G p.1 * F (p.1.1, p.2)
  let F₂ (p : (A × A) × C) := G p.1 * pivotInactiveSectionMean d flag F p.1.1
  have hF₁ : Measurable F₁ := (hG.comp measurable_fst).mul
    (hF.comp (measurable_fst.fst.prodMk measurable_snd))
  have hF₂ : Measurable F₂ := (hG.comp measurable_fst).mul
    ((measurable_pivotInactiveSectionMean d flag hF hy0 hy1).comp measurable_fst.fst)
  change (∫⁻ z, F₁ ((⇑(MeasurableEquiv.prodAssoc (α := A) (β := A) (γ := C)).symm ∘
      pivotFullRevealWithColumns flag) z)
      ∂forwardMaskRevealLaw d flag univ) =
    ∫⁻ z, F₂ ((⇑(MeasurableEquiv.prodAssoc (α := A) (β := A) (γ := C)).symm ∘
      pivotFullRevealWithColumns flag) z)
      ∂forwardMaskRevealLaw d flag univ
  rw [h.lintegral_comp hF₁, h.lintegral_comp hF₂, lintegral_prod F₁ hF₁.aemeasurable,
    lintegral_prod F₂ hF₂.aemeasurable]
  apply lintegral_congr
  intro a
  change (∫⁻ c, G a * F (a.1, c) ∂L) =
    ∫⁻ _ : C, G a * pivotInactiveSectionMean d flag F a.1 ∂L
  have hFa : Measurable (fun c : C ↦ F (a.1, c)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_const_mul _ hFa, lintegral_const]
  change G a * (∫⁻ c, F (a.1, c) ∂forwardScoreMaskInactiveColumnLaw d flag) =
    G a * pivotInactiveSectionMean d flag F a.1 * L univ
  have hL := forwardScoreMaskInactiveColumnLaw_eq_smul d flag hy0 hy1
  have hmass : L univ = ∏ j, ENNReal.ofReal (1 - (diagonalPairAt d j).2) ^
      Fintype.card (ForwardInactiveColumnIndex flag j) := by
    change forwardScoreMaskInactiveColumnLaw d flag univ = _
    rw [hL, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [hL, lintegral_smul_measure, smul_eq_mul, ← hmass]
  change G a * (L univ * pivotInactiveSectionMean d flag F a.1) = _
  ac_rfl
private noncomputable def pivotInactiveColumnBaseLaw (flag : OffDiagonalCellIndex n → Bool) :
    Measure (ForwardInactiveColumns flag) :=
  Measure.pi fun j ↦ Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦ unitScorePairLaw
private instance (flag : OffDiagonalCellIndex n → Bool) :
    IsProbabilityMeasure (pivotInactiveColumnBaseLaw flag) := by
  unfold pivotInactiveColumnBaseLaw
  infer_instance
private def pivotInactiveAllowed (flag : OffDiagonalCellIndex n → Bool) :
    Set (DiagonalScorePairs n × ForwardInactiveColumns flag) :=
  {z | ∀ j (q : ForwardInactiveColumnIndex flag j),
    (diagonalPairAt z.1 j).2 ≤ (z.2 j q).2}
theorem measurableSet_pivotInactiveAllowed (flag : OffDiagonalCellIndex n → Bool) :
    MeasurableSet (pivotInactiveAllowed flag) := by
  unfold pivotInactiveAllowed
  simp only [ofPred_forall]
  refine MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun q ↦ ?_
  have hy : Measurable (fun z : DiagonalScorePairs n × ForwardInactiveColumns flag ↦
      (diagonalPairAt z.1 j).2) := by
    have hd : Measurable (@Prod.fst (DiagonalScorePairs n) (ForwardInactiveColumns flag)) :=
      measurable_fst
    exact ((measurable_pi_apply (⟨(j, j), rfl⟩ : {q : ScorePairIndex n // q.1 = q.2})).comp
      hd).snd
  have hc : Measurable (fun z : DiagonalScorePairs n × ForwardInactiveColumns flag ↦
      (z.2 j q).2) := ((measurable_pi_apply q).comp
        ((measurable_pi_apply j).comp measurable_snd)).snd
  exact measurableSet_le hy hc
theorem pivotInactiveColumnBaseLaw_restrict (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    (pivotInactiveColumnBaseLaw flag).restrict (Prod.mk d ⁻¹' pivotInactiveAllowed flag) =
      forwardScoreMaskInactiveColumnLaw d flag := by
  have he : Prod.mk d ⁻¹' pivotInactiveAllowed flag =
      univ.pi fun j ↦ univ.pi fun _ : ForwardInactiveColumnIndex flag j ↦
        (univ : Set ℝ) ×ˢ Ici (diagonalPairAt d j).2 := by
    ext z
    simp [pivotInactiveAllowed]
  rw [he, pivotInactiveColumnBaseLaw, Measure.restrict_pi_pi,
    forwardScoreMaskInactiveColumnLaw]
  congr 1
  funext j
  rw [Measure.restrict_pi_pi]
  congr 1
  funext q
  rw [unitScorePairLaw, ← Measure.prod_restrict, Measure.restrict_univ]
private noncomputable def pivotInactiveColumnMass (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : ℝ≥0∞ :=
  ∏ j, ENNReal.ofReal (1 - (diagonalPairAt d j).2) ^
    Fintype.card (ForwardInactiveColumnIndex flag j)
theorem measurable_pivotInactiveColumnMass (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (fun d ↦ pivotInactiveColumnMass d flag) := by
  unfold pivotInactiveColumnMass
  refine Finset.univ.measurable_prod fun j _ ↦ ?_
  have hy : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d j).2) :=
    (measurable_pi_apply (⟨(j, j), rfl⟩ : {q : ScorePairIndex n // q.1 = q.2})).snd
  exact (ENNReal.measurable_ofReal.comp (measurable_const.sub hy)).pow_const _
private noncomputable def pivotJointInactiveMean (flag : OffDiagonalCellIndex n → Bool)
    (F : DiagonalScorePairs n × ForwardRevealedMaleScores flag ×
      ForwardInactiveColumns flag → ℝ≥0∞)
    (da : DiagonalScorePairs n × ForwardRevealedMaleScores flag) : ℝ≥0∞ :=
  (pivotInactiveColumnMass da.1 flag)⁻¹ *
    ∫⁻ c, (pivotInactiveAllowed flag).indicator (fun z ↦ F (z.1, da.2, z.2)) (da.1, c)
      ∂pivotInactiveColumnBaseLaw flag
theorem measurable_pivotJointInactiveMean (flag : OffDiagonalCellIndex n → Bool)
    {F : DiagonalScorePairs n × ForwardRevealedMaleScores flag ×
      ForwardInactiveColumns flag → ℝ≥0∞} (hF : Measurable F) :
    Measurable (pivotJointInactiveMean flag F) := by
  let D := DiagonalScorePairs n
  let A := ForwardRevealedMaleScores flag
  let C := ForwardInactiveColumns flag
  let W : Set ((D × A) × C) := (fun z ↦ (z.1.1, z.2)) ⁻¹' pivotInactiveAllowed flag
  have hW : MeasurableSet W := (measurableSet_pivotInactiveAllowed flag).preimage
    (measurable_fst.fst.prodMk measurable_snd)
  let J (z : (D × A) × C) := W.indicator (fun z ↦ F (z.1.1, z.1.2, z.2)) z
  have hJ : Measurable J := (hF.comp (measurable_fst.fst.prodMk
    (measurable_fst.snd.prodMk measurable_snd))).indicator hW
  have hInt : Measurable (fun da : D × A ↦
      ∫⁻ c, J (da, c) ∂pivotInactiveColumnBaseLaw flag) := hJ.lintegral_prod_right'
  have hmass : Measurable (fun da : D × A ↦ (pivotInactiveColumnMass da.1 flag)⁻¹) :=
    ((measurable_pivotInactiveColumnMass flag).comp measurable_fst).inv
  exact hmass.mul hInt
theorem pivotJointInactiveMean_eq_sectionMean (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    {F : DiagonalScorePairs n × ForwardRevealedMaleScores flag ×
      ForwardInactiveColumns flag → ℝ≥0∞}
    (a : ForwardRevealedMaleScores flag) (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2)
    (hy1 : ∀ i, (diagonalPairAt d i).2 < 1) :
    pivotJointInactiveMean flag F (d, a) =
      pivotInactiveSectionMean d flag (fun z ↦ F (d, z.1, z.2)) a := by
  let E := Prod.mk d ⁻¹' pivotInactiveAllowed flag
  have hE : MeasurableSet E :=
    (measurableSet_pivotInactiveAllowed flag).preimage measurable_prodMk_left
  have hfun : (fun c ↦ (pivotInactiveAllowed flag).indicator
      (fun z ↦ F (z.1, a, z.2)) (d, c)) = E.indicator (fun c ↦ F (d, a, c)) := by
    funext c
    by_cases hc : c ∈ E
    · rw [indicator_of_mem (show (d, c) ∈ pivotInactiveAllowed flag from hc),
        indicator_of_mem hc]
    · rw [indicator_of_notMem (show (d, c) ∉ pivotInactiveAllowed flag from hc),
        indicator_of_notMem hc]
  have h0 : pivotInactiveColumnMass d flag ≠ 0 := by
    unfold pivotInactiveColumnMass
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦
      pow_ne_zero _ (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hy1 j))).ne'
  have htop : pivotInactiveColumnMass d flag ≠ ∞ := by
    unfold pivotInactiveColumnMass
    exact ENNReal.prod_ne_top fun j _ ↦ ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  unfold pivotJointInactiveMean
  simp only [hfun, lintegral_indicator hE]
  change _ * (∫⁻ c, F (d, a, c) ∂(pivotInactiveColumnBaseLaw flag).restrict E) = _
  rw [pivotInactiveColumnBaseLaw_restrict, forwardScoreMaskInactiveColumnLaw_eq_smul d flag hy0 hy1,
    lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.inv_mul_cancel_left h0 htop
private noncomputable def pivotInactiveMeanFromReveal
    (F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞)
    (z : PivotMaleRevealData n) : ℝ≥0∞ :=
  pivotJointInactiveMean z.2.1 (F z.2.1) (z.1, fun q ↦ z.2.2 q.val)
set_option maxHeartbeats 600000 in
theorem measurable_pivotInactiveMeanFromReveal
    {F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hF : ∀ flag, Measurable (F flag)) :
    Measurable (pivotInactiveMeanFromReveal F) := by
  let D := DiagonalScorePairs n
  let A := OffDiagonalCellIndex n → ℝ
  let P := OffDiagonalCellIndex n → Bool
  let read (flag : P) (z : D × A) : D × ForwardRevealedMaleScores flag :=
    (z.1, fun q ↦ z.2 q.val)
  have hread (flag : P) : Measurable (read flag) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun q ↦
      (measurable_pi_apply q.val).comp measurable_snd)
  let T (z : (D × A) × P) :=
    pivotJointInactiveMean z.2 (F z.2) (read z.2 z.1)
  have hT : Measurable T := by
    apply measurable_from_prod_countable_left
    intro flag
    change Measurable (pivotJointInactiveMean flag (F flag) ∘ read flag)
    exact (measurable_pivotJointInactiveMean flag (hF flag)).comp (hread flag)
  let g (z : PivotMaleRevealData n) : (D × A) × P := ((z.1, z.2.2), z.2.1)
  have hg : Measurable g :=
    (measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst
  change Measurable (T ∘ g)
  exact hT.comp hg
theorem pivotInactiveMeanFromReveal_section
    (F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (a : ForwardRevealedMaleScores flag) :
    pivotInactiveMeanFromReveal F (pivotMaleRevealSection flag (d, a)) =
      pivotJointInactiveMean flag (F flag) (d, a) := by
  change pivotJointInactiveMean flag (F flag)
    (d, fun q ↦ extendPivotActiveValues flag a q.val) = _
  have he : (fun q : ForwardActiveCellIndex flag ↦ extendPivotActiveValues flag a q.val) = a := by
    funext q
    rw [extendPivotActiveValues, dif_pos q.property]
  rw [he]
theorem pivotInactiveMeanFromReveal_section_le {B : ℝ≥0∞}
    {F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hB : ∀ flag z, F flag z ≤ B) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (a : ForwardRevealedMaleScores flag)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1) :
    pivotInactiveMeanFromReveal F (pivotMaleRevealSection flag (d, a)) ≤ B := by
  rw [pivotInactiveMeanFromReveal_section, pivotJointInactiveMean_eq_sectionMean d flag a hy0 hy1]
  let (i : Fin n) : IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag i) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  unfold pivotInactiveSectionMean
  refine (lintegral_mono fun c ↦ hB flag (d, a, c)).trans_eq ?_
  rw [lintegral_const, measure_univ, mul_one]
theorem ae_diagonalFemale_mem_Ico (n : ℕ) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ i, (diagonalPairAt d i).2 ∈ Ico (0 : ℝ) 1 := by
  have hu : ∀ᵐ t ∂unitScoreLaw, t ∈ Ico (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
      MeasurableSet (Icc (0 : ℝ) 1)), unitScoreLaw.ae_ne (1 : ℝ)] with t ht hn
    exact ⟨ht.1, lt_of_le_of_ne ht.2 hn⟩
  have hp : ∀ᵐ z ∂unitScorePairLaw, z.2 ∈ Ico (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_snd (μ := unitScoreLaw) (ν := unitScoreLaw)).ae hu
  exact ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae
    (μ := fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦ unitScorePairLaw)
    (i := ⟨(i, i), rfl⟩)).eventually hp
theorem ae_pivotInactiveMeanFromReveal_le_stableMarkScoreLaw
    (μ : Matching n) {B : ℝ≥0∞}
    {F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hB : ∀ flag z, F flag z ≤ B) :
    ∀ᵐ x ∂stableMarkScoreLaw μ,
      pivotInactiveMeanFromReveal F (pivotMaleReveal μ x) ≤ B := by
  have hd : MeasurePreserving (fun x ↦ (splitScorePairs μ x).1)
      (continuousScoreLaw n) (diagonalScoreLaw n) :=
    measurePreserving_fst.comp (measurePreserving_splitScorePairs μ)
  have h := hd.quasiMeasurePreserving.ae (ae_diagonalFemale_mem_Ico n)
  apply ae_restrict_of_ae
  filter_upwards [h] with x hx
  let d := (splitScorePairs μ x).1
  let z := (splitScorePairs μ x).2
  let flag := forwardMaskOfScores d z
  have hf : z ∈ forwardScoreMaskEvent d flag := (forwardMaskOfScores_eq_iff d z flag).mp rfl
  have he : pivotMaleReveal μ x =
      pivotMaleRevealSection flag (d, (forwardRevealWithColumns flag z).1) := by
    simpa only [d, z, Prod.mk.eta, MeasurableEquiv.symm_apply_apply] using
      pivotMaleReveal_reconstruct μ d z flag hf
  rw [he]
  exact pivotInactiveMeanFromReveal_section_le hB d flag _ (fun i ↦ (hx i).1) (fun i ↦ (hx i).2)
set_option maxHeartbeats 900000 in
theorem setLIntegral_stableMark_fullReveal_eq_inactiveMean (μ : Matching n)
    {F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hF : ∀ flag, Measurable (F flag)) {Z : ScoreProfile n → ℝ≥0∞} (hZ : Measurable Z)
    (hY : ∀ᵐ d ∂diagonalScoreLaw n, ∀ i, (diagonalPairAt d i).2 ∈ Ico (0 : ℝ) 1)
    (hfactor : ∀ᵐ d ∂diagonalScoreLaw n, ∀ flag,
      ∀ᵐ z ∂forwardMaskRevealLaw d flag univ,
        Z ((splitScorePairs μ).symm (d, z)) =
          F flag (d, (forwardRevealWithColumns flag z).1, (forwardRevealWithColumns flag z).2))
    {S : Set (ScoreProfile n)} (hS : @MeasurableSet _ (pivotFullRevealSpace μ) S) :
    (∫⁻ x in S, Z x ∂stableMarkScoreLaw μ) =
      ∫⁻ x in S, pivotInactiveMeanFromReveal F (pivotMaleReveal μ x)
        ∂stableMarkScoreLaw μ := by
  have hS₀ : MeasurableSet S := pivotFullRevealSpace_le μ S hS
  obtain ⟨U, hU, hUeq⟩ := MeasurableSpace.measurableSet_comap.mp hS
  have hmean : Measurable (fun x ↦ pivotInactiveMeanFromReveal F (pivotMaleReveal μ x)) :=
    (measurable_pivotInactiveMeanFromReveal hF).comp (measurable_pivotMaleReveal μ)
  rw [← lintegral_indicator hS₀, ← lintegral_indicator hS₀,
    lintegral_stableMarkScoreLaw μ (hZ.indicator hS₀),
    lintegral_stableMarkScoreLaw μ (hmean.indicator hS₀)]
  apply lintegral_congr_ae
  filter_upwards [hY, hfactor] with d hd hD
  rw [lintegral_offDiagonalNonblocking_eq_sum_masks, lintegral_offDiagonalNonblocking_eq_sum_masks]
  apply Finset.sum_congr rfl
  intro flag _
  let ν := forwardMaskRevealLaw d flag univ
  have hν : ν = ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
      (forwardScoreMaskEvent d flag) := by
    simp only [ν, forwardMaskRevealLaw, preimage_univ, Measure.restrict_univ]
  rw [← hν]
  have hmask : ∀ᵐ z ∂ν, z ∈ forwardScoreMaskEvent d flag := by
    rw [hν]
    exact ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)
  let R := pivotFullRevealWithColumns flag
  let X (z : OffDiagonalScorePairs n) := (splitScorePairs μ).symm (d, z)
  let A := ForwardRevealedMaleScores flag
  let V : Set (A × A) := (fun a ↦ pivotFullRevealSection flag (d, a)) ⁻¹' U
  let G : A × A → ℝ≥0∞ := V.indicator 1
  let T (p : A × ForwardInactiveColumns flag) := F flag (d, p.1, p.2)
  have hV : MeasurableSet V := hU.preimage
    ((measurable_pivotFullRevealSection flag).comp (measurable_const.prodMk measurable_id))
  have hG : Measurable G := measurable_const.indicator hV
  have hT : Measurable T := (hF flag).comp (measurable_const.prodMk measurable_id)
  have hSiff (z : OffDiagonalScorePairs n) (hz : z ∈ forwardScoreMaskEvent d flag) :
      X z ∈ S ↔ ((R z).1, (R z).2.1) ∈ V := by
    rw [← hUeq]
    change pivotFullReveal μ (X z) ∈ U ↔
      pivotFullRevealSection flag (d, (R z).1, (R z).2.1) ∈ U
    rw [pivotFullReveal_reconstruct μ d z flag hz]
    rfl
  calc
    _ = ∫⁻ z, G ((R z).1, (R z).2.1) * T ((R z).1, (R z).2.2) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hmask, hD flag] with z hz hfz
      change S.indicator Z (X z) =
        V.indicator 1 ((R z).1, (R z).2.1) * T ((R z).1, (R z).2.2)
      by_cases h : X z ∈ S
      · rw [indicator_of_mem h _, indicator_of_mem ((hSiff z hz).mp h) _]
        change Z (X z) = 1 * T ((R z).1, (R z).2.2)
        rw [one_mul]
        exact hfz
      · rw [indicator_of_notMem h _, indicator_of_notMem (mt (hSiff z hz).mpr h) _, zero_mul]
    _ = ∫⁻ z, G ((R z).1, (R z).2.1) * pivotInactiveSectionMean d flag T (R z).1 ∂ν :=
      lintegral_pivotFullReveal_test_eq_inactiveSectionMean d flag hT hG
        (fun i ↦ (hd i).1) (fun i ↦ (hd i).2)
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hmask] with z hz
      have hm : pivotInactiveMeanFromReveal F (pivotMaleReveal μ (X z)) =
          pivotInactiveSectionMean d flag T (R z).1 := by
        rw [show X z = (splitScorePairs μ).symm (d, z) from rfl,
          pivotMaleReveal_reconstruct μ d z flag hz, pivotInactiveMeanFromReveal_section]
        exact pivotJointInactiveMean_eq_sectionMean d flag _
          (fun i ↦ (hd i).1) (fun i ↦ (hd i).2)
      change V.indicator 1 ((R z).1, (R z).2.1) * pivotInactiveSectionMean d flag T (R z).1 =
        S.indicator (fun x ↦ pivotInactiveMeanFromReveal F (pivotMaleReveal μ x)) (X z)
      by_cases h : X z ∈ S
      · rw [indicator_of_mem h _, indicator_of_mem ((hSiff z hz).mp h) _, hm]
        exact one_mul _
      · rw [indicator_of_notMem h _,
          indicator_of_notMem (mt (hSiff z hz).mpr h) _, zero_mul]
end DiagLP
end

-- PivotConditionalMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
variable {n : ℕ}
private noncomputable def localPivotConditionalMean (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ScoreProfile n → ℝ :=
  (stableMarkScoreLaw μ)[localFilteredDecorationCount b A B K L μ ρ|pivotMaleRevealSpace μ]
end DiagLP
end

-- CycleSupportCount
section
open Equiv.Perm Finset
open scoped BigOperators Classical
namespace DiagLP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end DiagLP
end

-- PointedSymmetricSums
section
open Finset
open scoped BigOperators
namespace DiagLP
end DiagLP
end

-- SingletonGaussianLength
section
open scoped BigOperators
open Finset
namespace DiagLP
end DiagLP
end

-- PivotSingletonLength
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
end DiagLP
end

-- SingletonAnchorCounting
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal DiagLP
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
open scoped Classical in
private noncomputable def singletonAnchorLengthWeight {W : Type*} [AddCommMonoid W]
    (p : Profile n) (μ : Matching n) (g : ℕ → W) : W :=
  ∑ σ : Matching n, if IsSoleForwardExposedRotation p μ σ then g σ.support.card else 0
open scoped Classical in
private noncomputable def profileSingletonAnchorLengthWeight {W : Type*} [AddCommMonoid W]
    (p : Profile n) (g : ℕ → W) : W :=
  ∑ μ : Matching n, if IsStable p μ then singletonAnchorLengthWeight p μ g else 0
private def scoreStableSingletonAnchorEvent (μ σ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ IsSoleForwardExposedRotation (profileOfScores x) μ σ}
theorem measurableSet_scoreStableSingletonAnchorEvent (μ σ : Matching n) :
    MeasurableSet (scoreStableSingletonAnchorEvent μ σ) :=
  (measurableSet_isScoreStable μ).inter
    ((measurable_profileOfScores n) (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | IsSoleForwardExposedRotation p μ σ}))
theorem lintegral_profileSingletonAnchorLengthWeight_eq_sum_scoreStableSingletonAnchorEvent
    (n : ℕ) (g : ℕ → ℝ≥0∞) :
    (∫⁻ p, profileSingletonAnchorLengthWeight p g ∂(uniformProfile n).toMeasure) =
      ∑ μ : Matching n, ∑ σ : Matching n,
        g σ.support.card * continuousScoreLaw n (scoreStableSingletonAnchorEvent μ σ) := by
  classical
  let f (μ σ : Matching n) := (scoreStableSingletonAnchorEvent μ σ).indicator
    (fun _ ↦ g σ.support.card)
  have hf (μ σ : Matching n) : Measurable (f μ σ) :=
    measurable_const.indicator (measurableSet_scoreStableSingletonAnchorEvent μ σ)
  have he : (fun x ↦ profileSingletonAnchorLengthWeight (profileOfScores x) g) =ᵐ[
      continuousScoreLaw n] fun x ↦ ∑ μ : Matching n, ∑ σ : Matching n, f μ σ x := by
    filter_upwards [ae_injective_rows n] with x hx
    unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    by_cases hμ : IsScoreStable x μ <;>
      simp [f, scoreStableSingletonAnchorEvent, Set.indicator,
        isStable_profileOfScores_iff hx μ, hμ]
  rw [← (measurePreserving_profileOfScores n).lintegral_comp Measurable.of_discrete,
    lintegral_congr_ae he, lintegral_finsetSum _ (fun μ _ ↦
      Finset.measurable_sum _ fun σ _ ↦ hf μ σ)]
  exact Finset.sum_congr rfl fun μ _ ↦ by
    rw [lintegral_finsetSum _ (fun σ _ ↦ hf μ σ)]
    exact Finset.sum_congr rfl fun σ _ ↦
      lintegral_indicator_const (measurableSet_scoreStableSingletonAnchorEvent μ σ) _
end DiagLP
end

-- ForwardRowDeficitConcentration
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DiagLP
end DiagLP
end

-- MarkedForwardRowDeficit
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
end DiagLP
end

-- SingletonDiagonalExceptions
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
end DiagLP
end

-- PivotSingletonMarkedLength
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private noncomputable def singletonMomentScale : ℝ := meanUpperConstant * Real.exp 5
theorem singletonMomentScale_pos : 0 < singletonMomentScale := by
  unfold singletonMomentScale meanUpperConstant
  positivity
private class LPHypB : Prop where
  bound : ∀ᶠ n : ℕ in atTop,
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal ((singletonMomentScale * (108 + 48 * Real.exp 4)) *
          Real.sqrt n * Real.log n + (n : ℝ) ^ (-3 : ℝ))
theorem eventually_lintegral_profileSingletonAnchorCount_le [h : LPHypB] :
    ∀ᶠ n : ℕ in atTop,
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal ((singletonMomentScale * (108 + 48 * Real.exp 4)) *
          Real.sqrt n * Real.log n + (n : ℝ) ^ (-3 : ℝ)) := h.bound
end DiagLP
end

-- PivotAggregateMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
variable {n : ℕ}
private noncomputable def pivotDecorationSupportCap (κ : ℝ) (n : ℕ) : ℕ :=
  ⌊κ * Real.sqrt (n : ℝ)⌋₊
theorem eventually_pivotDecorationSupportCap_bounds {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ pivotDecorationSupportCap κ n ∧
      (pivotDecorationSupportCap κ n : ℝ) ≤ κ * Real.sqrt (n : ℝ) ∧
      κ * Real.sqrt (n : ℝ) / 2 ≤ ((pivotDecorationSupportCap κ n - 1 : ℕ) : ℝ) := by
  have ht : Tendsto (fun n : ℕ ↦ κ * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hκ
  filter_upwards [ht.eventually_ge_atTop 4] with n hn
  let t := κ * Real.sqrt (n : ℝ)
  let K := pivotDecorationSupportCap κ n
  change 4 ≤ t at hn
  have hK : t < (K : ℝ) + 1 := Nat.lt_floor_add_one t
  have hK' : (K : ℝ) ≤ t := Nat.floor_le (by positivity)
  have h₂ : 2 ≤ K := by
    exact_mod_cast (show (2 : ℝ) ≤ K by linarith)
  refine ⟨h₂, hK', ?_⟩
  rw [Nat.cast_sub (by omega : 1 ≤ K)]
  push_cast
  linarith
end DiagLP
end

-- PivotDecorationRevealInvariance
section
open MeasureTheory Set StableMarriage
namespace DiagLP
variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}
private structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2
theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩
theorem SameReverseReveal.inactiveCell_eq (h : SameReverseReveal μ flag x y)
    (q : ForwardInactiveCellIndex flag) :
    (splitScorePairs μ x).2 q.val = (splitScorePairs μ y).2 q.val :=
  congrFun (congrFun (congrArg Prod.snd h.observed) q.val.val.2)
    (⟨q, rfl⟩ : ForwardInactiveColumnIndex flag q.val.val.2)
theorem SameReverseReveal.male_eq (h : SameReverseReveal μ flag x y) (m w : Fin n) :
    x (.inl m) w = y (.inl m) w := by
  by_cases hw : w = μ m
  · subst w
    simpa only [diagonalPairAt_splitScorePairs] using
      congrArg (fun d ↦ (diagonalPairAt d m).1) h.diagonal
  · let q : OffDiagonalCellIndex n :=
      ⟨(m, μ.symm w), fun he ↦ hw ((congrArg μ he).trans (μ.apply_symm_apply w)).symm⟩
    have hcell : ((splitScorePairs μ x).2 q).1 = ((splitScorePairs μ y).2 q).1 := by
      by_cases hq : flag q = true
      · exact congrFun (congrArg Prod.fst h.observed) (⟨q, hq⟩ : ForwardActiveCellIndex flag)
      · exact congrArg Prod.fst (h.inactiveCell_eq ⟨q, hq⟩)
    simpa only [splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply] using hcell
theorem SameReverseReveal.female_spouse_eq (h : SameReverseReveal μ flag x y) (w : Fin n) :
    x (.inr w) (μ.symm w) = y (.inr w) (μ.symm w) := by
  simpa only [diagonalPairAt_splitScorePairs, Equiv.apply_symm_apply] using
    congrArg (fun d ↦ (diagonalPairAt d (μ.symm w)).2) h.diagonal
private theorem SameReverseReveal.female_eq_of_spouse_lt
    (h : SameReverseReveal μ flag x y)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (hw : x (.inr w) (μ.symm w) < x (.inr w) m) :
    x (.inr w) m = y (.inr w) m := by
  have hne : m ≠ μ.symm w := fun e ↦ hw.ne (congrArg (x (.inr w)) e.symm)
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hq : flag q ≠ true := by
    intro he
    have hc := mem_pi.mp hmask q (mem_univ _)
    change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
      (diagonalPairAt (splitScorePairs μ x).1 m).1
      (diagonalPairAt (splitScorePairs μ x).1 (μ.symm w)).2 (flag q) at hc
    rw [he, forwardScoreCellFlagEvent, if_pos rfl, forwardEligibleScoreCell,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
      diagonalPairAt_splitScorePairs] at hc
    exact hw.not_gt (by simpa only [q, Equiv.apply_symm_apply, mem_Iio] using (mem_prod.mp hc).2)
  simpa only [splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply] using
    congrArg Prod.snd (h.inactiveCell_eq ⟨q, hq⟩)
private theorem SameReverseReveal.reverseSuccessor_iff (h : SameReverseReveal μ flag x y)
    (hsx : IsScoreStable x μ) (hsy : IsScoreStable y μ)
    (htx : ∀ r, Function.Injective (x r)) (hty : ∀ r, Function.Injective (y r))
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag)
    (w j : Fin n) (hj : j ≠ μ.symm w) :
    IsSuccessor (swapProfile (profileOfScores x)) μ.symm w j ↔
      IsSuccessor (swapProfile (profileOfScores y)) μ.symm w j := by
  let i := μ.symm w
  have hcol := congrFun (congrArg Prod.snd h.observed) i
  have hx := isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent μ x flag hsx htx hmx i j hj
  have hy := isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent μ y flag hsy hty hmy i j hj
  change _ ↔ (forwardRevealWithColumns flag (splitScorePairs μ x).2).2 i ∈
    forwardInactiveReverseArcEvent (splitScorePairs μ x).1 flag i j at hx
  rw [hcol, h.diagonal] at hx
  simpa only [i, Equiv.apply_symm_apply] using hx.trans hy.symm
private theorem SameReverseReveal.forwardExposed_iff (h : SameReverseReveal μ flag x y)
    (htx : ∀ r, Function.Injective (x r)) (hty : ∀ r, Function.Injective (y r))
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag) :
    IsExposedRotation (profileOfScores x) μ ρ ↔ IsExposedRotation (profileOfScores y) μ ρ := by
  rw [isExposedRotation_iff_forwardRevealExposureEvent μ ρ x flag htx hmx,
    isExposedRotation_iff_forwardRevealExposureEvent μ ρ y flag hty hmy, h.observed]
private theorem reverseScore_spouse_lt
    (ht : ∀ r, Function.Injective (x r))
    {w j : Fin n} (h : IsSuccessor (swapProfile (profileOfScores x)) μ.symm w j) :
    x (.inr w) (μ.symm w) < x (.inr w) j :=
  (rankPermutation_lt_iff (ht (.inr w)) _ _).mp (IsSuccessor.eligible h).1
private theorem SameReverseReveal.crossRectangle
    (h : SameReverseReveal μ flag x y)
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (htx : ∀ r, Function.Injective (x r))
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ)
    {m w : Fin n}
    (hR : IsPivotCrossRectangle x μ (undoReverseRotation μ σ) ρ m w) :
    IsPivotCrossRectangle y μ (undoReverseRotation μ σ) ρ m w := by
  have hw : w ∈ σ.support := Equiv.Perm.mem_support.mpr fun he ↦
    hR.2.1 (by rw [undoReverseRotation_symm_apply, he])
  have hf := h.female_eq_of_spouse_lt hmx hR.2.2.2.2.1
  have hj := h.female_eq_of_spouse_lt hmx (reverseScore_spouse_lt htx (hσ w hw))
  unfold IsPivotCrossRectangle
  rw [← h.male_eq, ← h.male_eq, ← h.male_eq, ← h.female_spouse_eq, ← hf,
    undoReverseRotation_symm_apply, ← hj, ← undoReverseRotation_symm_apply]
  exact hR
theorem filteredReverseSupportFamily_eq_of_same_forwardReveal
    (h : SameReverseReveal μ flag x y)
    (hsx : IsScoreStable x μ) (hsy : IsScoreStable y μ)
    (htx : ∀ r, Function.Injective (x r)) (hty : ∀ r, Function.Injective (y r))
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag)
    (hρx : IsExposedRotation (profileOfScores x) μ ρ) (k L : ℕ) (t : ℝ) :
    filteredReverseSupportFamily μ ρ flag k L t x =
      filteredReverseSupportFamily μ ρ flag k L t y := by
  classical
  have hρy := h.forwardExposed_iff htx hty hmx hmy |>.mp hρx
  ext σ
  simp only [filteredReverseSupportFamily, Finset.mem_filter, compatibleReverseSupportFamily,
    mem_compatibleReversePermutations]
  have hreal : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ ↔
      RealizesSuccessorPermutation (swapProfile (profileOfScores y)) μ.symm σ := by
    have hiff (w : Fin n) (hw : w ∈ σ.support) := h.reverseSuccessor_iff hsx hsy htx hty hmx hmy
      w (μ.symm (σ w)) (μ.symm.injective.ne (Equiv.Perm.mem_support.mp hw))
    exact ⟨fun hr w hw ↦ (hiff w hw).mp (hr w hw), fun hr w hw ↦ (hiff w hw).mpr (hr w hw)⟩
  have hcompat (hc : σ ∈ goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
      (forwardMaskForbiddenTargets μ flag))
      (hrx : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ)
      (hry : RealizesSuccessorPermutation (swapProfile (profileOfScores y)) μ.symm σ) :
      IsExposedRotation (profileOfScores x) (undoReverseRotation μ σ) ρ ↔
        IsExposedRotation (profileOfScores y) (undoReverseRotation μ σ) ρ := by
    have hdisj : ∀ m ∈ ρ.support, μ m ∉ σ.support := by
      exact fun m hm hms ↦ (mem_goodReverseSupportPermutations.mp hc).2 _ hms |>.1
        (Finset.mem_map.mpr ⟨m, hm, rfl⟩)
    have hfixed (m : Fin n) (hm : ρ m ≠ m) : undoReverseRotation μ σ m = μ m :=
      undoReverseRotation_apply_of_not_mem_support (hdisj m (Equiv.Perm.mem_support.mpr hm))
    have hxN := (isStable_profileOfScores_iff htx _).mp
      (hrx.undo_stable ((isStable_profileOfScores_iff htx μ).mpr hsx))
    have hyN := (isStable_profileOfScores_iff hty _).mp
      (hry.undo_stable ((isStable_profileOfScores_iff hty μ).mpr hsy))
    rw [isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle htx hρx hxN hfixed,
      isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle hty hρy hyN hfixed]
    exact ⟨fun hn m w hr ↦ hn m w (h.symm.crossRectangle hmy hty hry hr),
      fun hn m w hr ↦ hn m w (h.crossRectangle hmx htx hrx hr)⟩
  have hinc (hrx : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ) :
      reverseCollectionIncrementGood x μ σ t ↔ reverseCollectionIncrementGood y μ σ t := by
    have he (w : Fin n) (hw : w ∈ σ.support) :
        reverseScoreIncrement x μ w (μ.symm (σ w)) =
          reverseScoreIncrement y μ w (μ.symm (σ w)) := by
      unfold reverseScoreIncrement
      rw [h.female_eq_of_spouse_lt hmx (reverseScore_spouse_lt htx (hrx w hw)),
        h.female_spouse_eq]
    exact ⟨fun hi w hw ↦ he w hw ▸ hi w hw, fun hi w hw ↦ (he w hw).symm ▸ hi w hw⟩
  constructor
  · rintro ⟨⟨hc, hrx, hex⟩, hs, hi⟩
    have hry := hreal.mp hrx
    exact ⟨⟨hc, hry, (hcompat hc hrx hry).mp hex⟩, hs, (hinc hrx).mp hi⟩
  · rintro ⟨⟨hc, hry, hey⟩, hs, hi⟩
    have hrx := hreal.mpr hry
    exact ⟨⟨hc, hrx, (hcompat hc hrx hry).mpr hey⟩, hs, (hinc hrx).mpr hi⟩
private noncomputable def reverseRevealFillOffDiagonal (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    OffDiagonalScorePairs n :=
  fun q ↦ if h : flag q = true then
    (r.1 ⟨q, h⟩, (diagonalPairAt d q.val.2).2 * (((q.val.1.val : ℝ) + 1) / (n + 1)))
  else r.2 q.val.2 ⟨⟨q, h⟩, rfl⟩
theorem measurable_reverseRevealFillOffDiagonal (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (fun a : DiagonalScorePairs n ×
      (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
      reverseRevealFillOffDiagonal a.1 flag a.2) := by
  refine measurable_pi_iff.2 fun q ↦ ?_
  by_cases h : flag q = true
  · have hm : Measurable (fun a : DiagonalScorePairs n ×
        (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦ a.2.1 ⟨q, h⟩) :=
      (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
    have hf : Measurable (fun a : DiagonalScorePairs n ×
        (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
        (diagonalPairAt a.1 q.val.2).2) :=
      measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)
    simpa only [reverseRevealFillOffDiagonal, dif_pos h] using hm.prodMk (hf.mul_const _)
  · have hI : Measurable (fun a : DiagonalScorePairs n ×
        (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
        a.2.2 q.val.2 ⟨⟨q, h⟩, rfl⟩) :=
      (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        (measurable_snd.comp measurable_snd))
    simpa only [reverseRevealFillOffDiagonal, dif_neg h] using hI
private noncomputable def reverseRevealFill (μ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) : ScoreProfile n :=
  (splitScorePairs μ).symm (d, reverseRevealFillOffDiagonal d flag r)
theorem measurable_reverseRevealFill (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (fun a : DiagonalScorePairs n ×
      (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
      reverseRevealFill μ a.1 flag a.2) :=
  (splitScorePairs μ).symm.measurable.comp
    (measurable_fst.prodMk (measurable_reverseRevealFillOffDiagonal flag))
@[simp] theorem splitScorePairs_reverseRevealFill (μ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    splitScorePairs μ (reverseRevealFill μ d flag r) =
      (d, reverseRevealFillOffDiagonal d flag r) :=
  (splitScorePairs μ).apply_symm_apply _
@[simp] theorem forwardRevealWithColumns_reverseRevealFillOffDiagonal (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    forwardRevealWithColumns flag (reverseRevealFillOffDiagonal d flag r) = r := by
  apply Prod.ext
  · funext q
    change ((reverseRevealFillOffDiagonal d flag r) q.val).1 = _
    simp only [reverseRevealFillOffDiagonal, dif_pos q.property]
  · funext i q
    obtain ⟨q, rfl⟩ := q
    change (reverseRevealFillOffDiagonal d flag r) q.val = _
    simp only [reverseRevealFillOffDiagonal, dif_neg q.property]
private noncomputable def discardActiveFemale (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x : ScoreProfile n) : ScoreProfile n :=
  reverseRevealFill μ (splitScorePairs μ x).1 flag
    (forwardRevealWithColumns flag (splitScorePairs μ x).2)
theorem sameReverseReveal_discardActiveFemale (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (x : ScoreProfile n) :
    SameReverseReveal μ flag x (discardActiveFemale μ flag x) := by
  constructor <;> simp only [discardActiveFemale, splitScorePairs_reverseRevealFill,
    forwardRevealWithColumns_reverseRevealFillOffDiagonal]
private def markedCellActive (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (m w : Fin n) : Prop :=
  ∃ h : m ≠ μ.symm w, flag ⟨(m, μ.symm w), h⟩ = true
private theorem activeCell_scores
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (ha : markedCellActive μ flag m w) :
    x (.inl m) (μ m) < x (.inl m) w ∧ x (.inr w) m < x (.inr w) (μ.symm w) := by
  obtain ⟨hne, hf⟩ := ha
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hc := mem_pi.mp hmask q (mem_univ _)
  change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
    (diagonalPairAt (splitScorePairs μ x).1 m).1
    (diagonalPairAt (splitScorePairs μ x).1 (μ.symm w)).2 (flag q) at hc
  rw [show flag q = true from hf, forwardScoreCellFlagEvent, if_pos rfl,
    forwardEligibleScoreCell, splitScorePairs_offDiagonal_apply,
    diagonalPairAt_splitScorePairs, diagonalPairAt_splitScorePairs] at hc
  simpa only [q, Equiv.apply_symm_apply, mem_prod, mem_Ioi, mem_Iio] using hc
private theorem spouse_le_female_of_not_active (hs : IsScoreStable x μ)
    (ht : ∀ row, Function.Injective (x row))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (ha : ¬ markedCellActive μ flag m w) :
    x (.inr w) (μ.symm w) ≤ x (.inr w) m := by
  apply le_of_not_gt
  intro hf
  have hne : m ≠ μ.symm w := fun he ↦ hf.ne (congrArg (x (.inr w)) he)
  have hw : μ m ≠ w := fun he ↦ hne (μ.symm_apply_eq.mpr he.symm).symm
  have hm : x (.inl m) (μ m) < x (.inl m) w :=
    lt_of_le_of_ne (le_of_not_gt fun hlt ↦ hs m w ⟨hw, hlt, hf⟩)
      (fun he ↦ hw (ht (.inl m) he))
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hq : flag q ≠ true := fun he ↦ ha ⟨hne, he⟩
  have hc := mem_pi.mp hmask q (mem_univ _)
  change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
    (diagonalPairAt (splitScorePairs μ x).1 m).1
    (diagonalPairAt (splitScorePairs μ x).1 (μ.symm w)).2 (flag q) at hc
  rw [forwardScoreCellFlagEvent, if_neg hq, forwardEligibleScoreCell,
    splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
    diagonalPairAt_splitScorePairs] at hc
  apply hc
  simpa only [q, Equiv.apply_symm_apply, mem_prod, mem_Ioi, mem_Iio] using And.intro hm hf
private theorem female_discardActiveFemale_of_active {m w : Fin n}
    (ha : markedCellActive μ flag m w) :
    discardActiveFemale μ flag x (.inr w) m =
      x (.inr w) (μ.symm w) * (((m.val : ℝ) + 1) / (n + 1)) := by
  obtain ⟨hne, hf⟩ := ha
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hq : flag q = true := hf
  have h := congrArg (fun a ↦ (a.2 q).2)
    (splitScorePairs_reverseRevealFill μ (splitScorePairs μ x).1 flag
      (forwardRevealWithColumns flag (splitScorePairs μ x).2))
  simpa only [discardActiveFemale, splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply,
    reverseRevealFillOffDiagonal, dif_pos hq, diagonalPairAt_splitScorePairs] using h
private theorem female_discardActiveFemale_of_not_active {m w : Fin n}
    (ha : ¬ markedCellActive μ flag m w) :
    discardActiveFemale μ flag x (.inr w) m = x (.inr w) m := by
  have h := sameReverseReveal_discardActiveFemale μ flag x
  by_cases hm : m = μ.symm w
  · subst m
    exact (h.female_spouse_eq w).symm
  · let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hm⟩
    have hq : flag q ≠ true := fun he ↦ ha ⟨hm, he⟩
    simpa only [splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply] using
      (congrArg Prod.snd (h.inactiveCell_eq ⟨q, hq⟩)).symm
private theorem fraction_lt_one (m : Fin n) : ((m.val : ℝ) + 1) / (n + 1) < 1 := by
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  rw [one_mul]
  have hm : (m.val : ℝ) < n := by exact_mod_cast m.isLt
  linarith
private theorem female_discardActiveFemale_lt_of_active
    (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (ha : markedCellActive μ flag m w) :
    discardActiveFemale μ flag x (.inr w) m < x (.inr w) (μ.symm w) := by
  have hpos := (h0 (.inr w) m).trans_lt (activeCell_scores hmask ha).2
  rw [female_discardActiveFemale_of_active ha]
  simpa only [mul_one] using mul_lt_mul_of_pos_left (fraction_lt_one m) hpos
theorem discardActiveFemale_valid (hs : IsScoreStable x μ)
    (ht : ∀ row, Function.Injective (x row)) (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag) :
    let y := discardActiveFemale μ flag x
    IsScoreStable y μ ∧ (∀ row, Function.Injective (y row)) ∧
      (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag := by
  intro y
  let h := sameReverseReveal_discardActiveFemale μ flag x
  change SameReverseReveal μ flag x y at h
  have hlt {m w : Fin n} (ha : markedCellActive μ flag m w) :
      y (.inr w) m < x (.inr w) (μ.symm w) :=
    female_discardActiveFemale_lt_of_active h0 hmask ha
  have hunchanged {m w : Fin n} (ha : ¬ markedCellActive μ flag m w) :
      y (.inr w) m = x (.inr w) m := female_discardActiveFemale_of_not_active ha
  have hnot {m w : Fin n} (ha : ¬ markedCellActive μ flag m w) :
      x (.inr w) (μ.symm w) ≤ y (.inr w) m :=
    (spouse_le_female_of_not_active hs ht hmask ha).trans_eq (hunchanged ha).symm
  refine ⟨?_, ?_, ?_⟩
  · intro m w hb
    by_cases ha : markedCellActive μ flag m w
    · have hm := (activeCell_scores hmask ha).1
      rw [h.male_eq, h.male_eq] at hm
      exact hm.not_gt hb.2.1
    · exact (hnot ha).not_gt (by rw [h.female_spouse_eq]; exact hb.2.2)
  · intro r
    cases r with
    | inl m =>
      intro a b he
      exact ht (.inl m) (by simpa only [h.male_eq] using he)
    | inr w =>
      intro a b he
      by_cases ha : markedCellActive μ flag a w <;> by_cases hb : markedCellActive μ flag b w
      · have hpos := (h0 (.inr w) a).trans_lt (activeCell_scores hmask ha).2
        change discardActiveFemale μ flag x (.inr w) a =
          discardActiveFemale μ flag x (.inr w) b at he
        rw [female_discardActiveFemale_of_active ha, female_discardActiveFemale_of_active hb] at he
        have hdiv := mul_left_cancel₀ hpos.ne' he
        have hcast : (a.val : ℝ) = (b.val : ℝ) := by
          have hh := (div_left_inj' (by positivity : (n : ℝ) + 1 ≠ 0)).mp hdiv
          linarith
        exact Fin.ext (by exact_mod_cast hcast)
      · exact ((he ▸ hlt ha).not_ge (hnot hb)).elim
      · exact ((he.symm ▸ hlt hb).not_ge (hnot ha)).elim
      · exact ht (.inr w) ((hunchanged ha).symm.trans (he.trans (hunchanged hb)))
  · apply mem_pi.mpr
    intro q _
    let m := q.val.1
    let i := q.val.2
    change (splitScorePairs μ y).2 q ∈ forwardScoreCellFlagEvent
      (diagonalPairAt (splitScorePairs μ y).1 m).1
      (diagonalPairAt (splitScorePairs μ y).1 i).2 (flag q)
    by_cases hf : flag q = true
    · have hq : markedCellActive μ flag m (μ i) := by
        have hne : m ≠ μ.symm (μ i) := by
          simpa only [Equiv.symm_apply_apply] using q.property
        refine ⟨hne, ?_⟩
        convert hf using 2
        exact Subtype.ext (by simp only [m, i, Equiv.symm_apply_apply])
      have hm := (activeCell_scores hmask hq).1
      rw [h.male_eq, h.male_eq] at hm
      have hY := hlt hq
      rw [h.female_spouse_eq] at hY
      rw [hf, forwardScoreCellFlagEvent, if_pos rfl, forwardEligibleScoreCell,
        splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
        diagonalPairAt_splitScorePairs]
      exact ⟨hm, by simpa only [Equiv.symm_apply_apply, mem_Iio, m, i] using hY⟩
    · rw [← h.diagonal, ← h.inactiveCell_eq ⟨q, hf⟩]
      exact mem_pi.mp hmask q (mem_univ _)
theorem filteredReverseSupportFamily_eq_discardActiveFemale
    (hs : IsScoreStable x μ) (ht : ∀ row, Function.Injective (x row))
    (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hρ : IsExposedRotation (profileOfScores x) μ ρ) (k L : ℕ) (t : ℝ) :
    filteredReverseSupportFamily μ ρ flag k L t x =
      filteredReverseSupportFamily μ ρ flag k L t (discardActiveFemale μ flag x) := by
  obtain ⟨hs', ht', hmask'⟩ := discardActiveFemale_valid hs ht h0 hmask
  exact filteredReverseSupportFamily_eq_of_same_forwardReveal
    (sameReverseReveal_discardActiveFemale μ flag x) hs hs' ht ht' hmask hmask' hρ k L t
@[simp] theorem discardActiveFemale_reconstruct (μ : Matching n) (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    discardActiveFemale μ flag ((splitScorePairs μ).symm (d, z)) =
      reverseRevealFill μ d flag (forwardRevealWithColumns flag z) := by
  simp only [discardActiveFemale, MeasurableEquiv.apply_symm_apply]
theorem SameReverseReveal.localEligibility_iff (h : SameReverseReveal μ flag x y)
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag)
    (b A B : ℝ) :
    IsLocallyEligiblePivot b A B x μ ρ ↔ IsLocallyEligiblePivot b A B y μ ρ := by
  have ex := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ
    (splitScorePairs μ x).1 (splitScorePairs μ x).2 flag hmx
  have ey := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ
    (splitScorePairs μ y).1 (splitScorePairs μ y).2 flag hmy
  rw [Prod.mk.eta, MeasurableEquiv.symm_apply_apply, h.diagonal,
    congrArg Prod.fst h.observed] at ex
  rw [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] at ey
  exact ex.trans ey.symm
theorem localFilteredDecorationCount_eq_discardActiveFemale
    (hs : IsScoreStable x μ) (ht : ∀ row, Function.Injective (x row))
    (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (b A B : ℝ) (K L : ℕ) (ρ : Matching n) :
    localFilteredDecorationCount b A B K L μ ρ x =
      localFilteredDecorationCount b A B K L μ ρ (discardActiveFemale μ flag x) := by
  classical
  obtain ⟨_, _, hmask'⟩ := discardActiveFemale_valid hs ht h0 hmask
  have h := sameReverseReveal_discardActiveFemale μ flag x
  have he := h.localEligibility_iff (ρ := ρ) hmask hmask' b A B
  by_cases hE : IsLocallyEligiblePivot b A B x μ ρ
  · rw [localFilteredDecorationCount_of_eligible_of_fixedMask K L hE hmask,
      localFilteredDecorationCount_of_eligible_of_fixedMask K L (he.mp hE) hmask',
      ← h.diagonal]
    have hρ := (hE.isSoleForwardExposed ht).1
    congr 2
    ext σ
    simp only [mem_markedFilteredChoices]
    rw [filteredReverseSupportFamily_eq_discardActiveFemale hs ht h0 hmask hρ]
  · have hy := fun h' ↦ hE (he.mpr h')
    simp only [localFilteredDecorationCount, if_neg hE, if_neg hy]
theorem ae_diagonal_ae_localFilteredDecorationCount_eq_reverseRevealFill
    (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ (flag : OffDiagonalCellIndex n → Bool)
      (U : Set (ForwardRevealedMaleScores flag)), ∀ᵐ z ∂forwardMaskRevealLaw d flag U,
      localFilteredDecorationCount b A B K L μ ρ ((splitScorePairs μ).symm (d, z)) =
        localFilteredDecorationCount b A B K L μ ρ
          (reverseRevealFill μ d flag (forwardRevealWithColumns flag z)) := by
  have hu : ∀ᵐ a ∂(diagonalScoreLaw n).prod (offDiagonalScoreLaw n),
      ∀ r i, (splitScorePairs μ).symm a r i ∈ Ioo (0 : ℝ) 1 :=
    (measurePreserving_splitScorePairs μ).symm.quasiMeasurePreserving.ae (ae_unitOpen_scores n)
  filter_upwards [ae_diagonal_ae_injective_scoreRows μ, Measure.ae_ae_of_ae_prod hu]
    with d ht h0
  intro flag U
  have hnon : MeasurableSet (offDiagonalNonblocking d) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
  filter_upwards [ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae ht)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae h0)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_mem hnon)),
    ae_restrict_of_ae (ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag))]
    with z hz hu hstable hmask
  let x := (splitScorePairs μ).symm (d, z)
  have hsplit : splitScorePairs μ x = (d, z) := (splitScorePairs μ).apply_symm_apply _
  have hs : IsScoreStable x μ := (isScoreStable_iff_splitScorePairs μ x).mpr
    (by simpa only [hsplit] using hstable)
  have hm : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag := by
    simpa only [hsplit] using hmask
  simpa only [x, discardActiveFemale_reconstruct] using
    localFilteredDecorationCount_eq_discardActiveFemale hs hz
      (fun r i ↦ (hu r i).1.le) hm b A B K L ρ
end DiagLP
end

-- PivotEnlargedConditionalMean
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal
namespace DiagLP
variable {n : ℕ}
private noncomputable def localPivotInactiveStatistic (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (s : DiagonalScorePairs n × ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    ℝ≥0∞ :=
  ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ (reverseRevealFill μ s.1 flag s.2))
theorem measurable_localPivotInactiveStatistic (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (localPivotInactiveStatistic b A B K L μ ρ flag) :=
  ENNReal.measurable_ofReal.comp ((measurable_localFilteredDecorationCount b A B K L μ ρ).comp
    (measurable_reverseRevealFill μ flag))
private theorem localPivotInactiveStatistic_le (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool)
    (s : DiagonalScorePairs n × ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    localPivotInactiveStatistic b A B K L μ ρ flag s ≤ ENNReal.ofReal (n.factorial : ℝ) :=
  ENNReal.ofReal_le_ofReal (localFilteredDecorationCount_le_factorial b A B K L μ ρ _)
private noncomputable def localPivotInactiveMean (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ :=
  (pivotInactiveMeanFromReveal (localPivotInactiveStatistic b A B K L μ ρ)
    (pivotMaleReveal μ x)).toReal
theorem measurable_maleReveal_localPivotInactiveMean (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) :
    Measurable[pivotMaleRevealSpace μ] (localPivotInactiveMean b A B K L μ ρ) := by
  have hmap : Measurable[pivotMaleRevealSpace μ] (pivotMaleReveal μ) :=
    fun S hS ↦ ⟨S, hS, rfl⟩
  exact ENNReal.measurable_toReal.comp
    ((measurable_pivotInactiveMeanFromReveal
      (measurable_localPivotInactiveStatistic b A B K L μ ρ)).comp hmap)
private theorem ae_localPivotInactiveMeanENN_le (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ∀ᵐ x ∂stableMarkScoreLaw μ, pivotInactiveMeanFromReveal
      (localPivotInactiveStatistic b A B K L μ ρ) (pivotMaleReveal μ x) ≤
        ENNReal.ofReal (n.factorial : ℝ) :=
  ae_pivotInactiveMeanFromReveal_le_stableMarkScoreLaw μ
    (localPivotInactiveStatistic_le b A B K L μ ρ)
theorem integrable_localPivotInactiveMean (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    Integrable (localPivotInactiveMean b A B K L μ ρ) (stableMarkScoreLaw μ) := by
  refine (integrable_const (n.factorial : ℝ)).mono'
    (((measurable_maleReveal_localPivotInactiveMean b A B K L μ ρ).mono
      (pivotMaleRevealSpace_le μ) le_rfl).aestronglyMeasurable) ?_
  filter_upwards [ae_localPivotInactiveMeanENN_le b A B K L μ ρ] with x hx
  have hnonneg : 0 ≤ localPivotInactiveMean b A B K L μ ρ x := ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
    (ENNReal.toReal_ofReal (Nat.cast_nonneg _))
theorem setIntegral_localPivotInactiveMean_eq {b A B : ℝ} (K L : ℕ) (μ ρ : Matching n)
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotFullRevealSpace μ] S) :
    (∫ x in S, localPivotInactiveMean b A B K L μ ρ x ∂stableMarkScoreLaw μ) =
      ∫ x in S, localFilteredDecorationCount b A B K L μ ρ x ∂stableMarkScoreLaw μ := by
  let F := localPivotInactiveStatistic b A B K L μ ρ
  let Z := localFilteredDecorationCount b A B K L μ ρ
  let ν := stableMarkScoreLaw μ
  let m := localPivotInactiveMean b A B K L μ ρ
  have hfactor : ∀ᵐ d ∂diagonalScoreLaw n, ∀ flag,
      ∀ᵐ z ∂forwardMaskRevealLaw d flag univ,
        ENNReal.ofReal (Z ((splitScorePairs μ).symm (d, z))) =
          F flag (d, (forwardRevealWithColumns flag z).1, (forwardRevealWithColumns flag z).2) := by
    filter_upwards [ae_diagonal_ae_localFilteredDecorationCount_eq_reverseRevealFill b A B K L μ ρ]
      with d hd flag
    exact (hd flag univ).mono fun z hz ↦ congrArg ENNReal.ofReal hz
  have he := setLIntegral_stableMark_fullReveal_eq_inactiveMean μ
    (measurable_localPivotInactiveStatistic b A B K L μ ρ)
    (ENNReal.measurable_ofReal.comp (measurable_localFilteredDecorationCount b A B K L μ ρ))
    (ae_diagonalFemale_mem_Ico n) hfactor hS
  have hraw : (fun x ↦ ENNReal.ofReal (m x)) =ᵐ[ν.restrict S]
      fun x ↦ pivotInactiveMeanFromReveal F (pivotMaleReveal μ x) := by
    filter_upwards [ae_restrict_of_ae (ae_localPivotInactiveMeanENN_le b A B K L μ ρ)] with x hx
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx)
  have hnm : 0 ≤ᵐ[ν.restrict S] m := Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg
  have hnZ : 0 ≤ᵐ[ν.restrict S] Z :=
    Eventually.of_forall (localFilteredDecorationCount_nonneg b A B K L μ ρ)
  change (∫ x in S, m x ∂ν) = ∫ x in S, Z x ∂ν
  rw [integral_eq_lintegral_of_nonneg_ae hnm
      ((integrable_localPivotInactiveMean b A B K L μ ρ).integrableOn (s := S)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hnZ
      ((integrable_localFilteredDecorationCount b A B K L μ ρ ν).integrableOn (s := S)).aestronglyMeasurable,
    lintegral_congr_ae hraw]
  exact congrArg ENNReal.toReal he.symm
theorem localPivotInactiveMean_ae_eq_conditionalMean (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) :
    localPivotInactiveMean b A B K L μ ρ =ᵐ[stableMarkScoreLaw μ]
      localPivotConditionalMean b A B K L μ ρ := by
  let ν := stableMarkScoreLaw μ
  have hf := integrable_localFilteredDecorationCount b A B K L μ ρ ν
  have hg := integrable_localPivotInactiveMean b A B K L μ ρ
  have hm := (measurable_maleReveal_localPivotInactiveMean b A B K L μ ρ).stronglyMeasurable
  exact ae_eq_condExp_of_forall_setIntegral_eq (pivotMaleRevealSpace_le μ) hf
    (fun _ _ _ ↦ hg.integrableOn) (fun _ hS _ ↦
      setIntegral_localPivotInactiveMean_eq K L μ ρ (pivotMaleRevealSpace_le_full μ _ hS))
    hm.aestronglyMeasurable
theorem localPivotConditionalMean_mem_Icc_ae (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ∀ᵐ x ∂stableMarkScoreLaw μ,
      localPivotConditionalMean b A B K L μ ρ x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  filter_upwards [localPivotInactiveMean_ae_eq_conditionalMean b A B K L μ ρ,
    ae_localPivotInactiveMeanENN_le b A B K L μ ρ] with x h hx
  rw [← h]
  exact ⟨ENNReal.toReal_nonneg, (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
    (ENNReal.toReal_ofReal (Nat.cast_nonneg _))⟩
end DiagLP
end

-- PivotLaterRevealReplay
section
open MeasureTheory Set StableMarriage
namespace DiagLP
variable {n : ℕ}
private def ScoreForwardEligible (x : ScoreProfile n) (A : Matching n) (m w : Fin n) : Prop :=
  x (.inl m) (A m) < x (.inl m) w ∧ x (.inr w) m < x (.inr w) (A.symm w)
private def ScorePairAgrees (x y : ScoreProfile n) (m w : Fin n) : Prop :=
  x (.inl m) w = y (.inl m) w ∧ x (.inr w) m = y (.inr w) m
private structure FullForwardRevealAgrees (x y : ScoreProfile n) (A : Matching n) : Prop where
  spouse : ∀ m, ScorePairAgrees x y m (A m)
  eligible_iff : ∀ m w, ScoreForwardEligible x A m w ↔ ScoreForwardEligible y A m w
  cell : ∀ m w, ScoreForwardEligible x A m w → ScorePairAgrees x y m w
variable {x y : ScoreProfile n} {A B : Matching n}
theorem FullForwardRevealAgrees.symm (h : FullForwardRevealAgrees x y A) :
    FullForwardRevealAgrees y x A where
  spouse m := ⟨(h.spouse m).1.symm, (h.spouse m).2.symm⟩
  eligible_iff m w := (h.eligible_iff m w).symm
  cell m w hw :=
    let hc := h.cell m w ((h.eligible_iff m w).mpr hw)
    ⟨hc.1.symm, hc.2.symm⟩
end DiagLP
end

-- PivotComparableCentered
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
private structure PivotCountParameters where
  lowerLength : ℝ
  upperLength : ℝ
  geometryBudget : ℝ
  supportCap : ℕ
  shortCutoff : ℕ
private abbrev PivotMark (n : ℕ) := Matching n × Matching n
theorem integrable_of_ae_abs_le_real {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ᵐ x ∂ν, |f x| ≤ C) : Integrable f ν :=
  (integrable_const C).mono' hf.aestronglyMeasurable <|
    hC.mono fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx
theorem integrable_mul_of_ae_abs_le_real {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hC : 0 ≤ C) (hf' : ∀ᵐ x ∂ν, |f x| ≤ C) (hg' : ∀ᵐ x ∂ν, |g x| ≤ D) :
    Integrable (f * g) ν := by
  apply integrable_of_ae_abs_le_real (hf.mul hg) (C := C * D)
  filter_upwards [hf', hg'] with x hx hy
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hC
namespace PivotCountParameters
variable {n : ℕ}
private noncomputable def localCount (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  localFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff i.1 i.2
private noncomputable def localMean (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  localPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff i.1 i.2
private noncomputable def onStableMark (i : PivotMark n) (f : ScoreProfile n → ℝ) :
    ScoreProfile n → ℝ :=
  {x | IsScoreStable x i.1}.indicator f
private noncomputable def mean (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  onStableMark i (q.localMean i)
theorem stronglyMeasurable_maleReveal_localMean (q : PivotCountParameters) (i : PivotMark n) :
    StronglyMeasurable[pivotMaleRevealSpace i.1] (q.localMean i) :=
  stronglyMeasurable_condExp
theorem measurable_localMean (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.localMean i) :=
  ((q.stronglyMeasurable_maleReveal_localMean i).mono (pivotMaleRevealSpace_le i.1)).measurable
theorem measurable_onStableMark (i : PivotMark n) {f : ScoreProfile n → ℝ} (hf : Measurable f) :
    Measurable (onStableMark i f) := hf.indicator (measurableSet_isScoreStable i.1)
theorem measurable_mean (q : PivotCountParameters) (i : PivotMark n) : Measurable (q.mean i) :=
  measurable_onStableMark i (q.measurable_localMean i)
theorem localMean_mem_Icc_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂stableMarkScoreLaw i.1, q.localMean i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) :=
  localPivotConditionalMean_mem_Icc_ae _ _ _ _ _ _ _
theorem ae_scoreLaw_on_stableMark (i : PivotMark n) {P : ScoreProfile n → Prop}
    (h : ∀ᵐ x ∂stableMarkScoreLaw i.1, P x) :
    ∀ᵐ x ∂continuousScoreLaw n, IsScoreStable x i.1 → P x :=
  (ae_restrict_iff' (measurableSet_isScoreStable i.1)).mp h
theorem mean_mem_Icc_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂continuousScoreLaw n, q.mean i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  filter_upwards [ae_scoreLaw_on_stableMark i (q.localMean_mem_Icc_ae i)] with x hx
  by_cases h : x ∈ {y | IsScoreStable y i.1}
  · simpa only [mean, onStableMark, indicator_of_mem h] using hx h
  · simp [mean, onStableMark, h]
end PivotCountParameters
end DiagLP
end

-- PivotCenteredReduction
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace DiagLP
variable {n : ℕ}
private def IncomparableAnchors (p : Profile n) (μ ν : Matching n) : Prop :=
  ¬ MenWeaklyPrefer p μ ν ∧ ¬ MenWeaklyPrefer p ν μ
theorem measurableSet_incomparableAnchors (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IncomparableAnchors (profileOfScores x) μ ν} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | IncomparableAnchors p μ ν})
namespace PivotCountParameters
end PivotCountParameters
end DiagLP
end

-- PivotTwoCycleForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
end DiagLP
end

-- LogarithmicCutoffs
section
open Filter
open scoped Topology BigOperators
namespace DiagLP
private noncomputable def logarithmicCycleCutoff (n : ℕ) : ℕ := ⌊Real.log (n : ℝ)⌋₊
theorem tendsto_logarithmicCycleCutoff : Tendsto logarithmicCycleCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
end DiagLP
end

-- PivotIncomparableAnchors
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace DiagLP
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
private abbrev IncomparableEligibleAnchorMarks (b A B : ℝ) (x : ScoreProfile n) :=
  {ij : (Matching n × Matching n) × (Matching n × Matching n) //
    IsScoreStable x ij.1.1 ∧ IsScoreStable x ij.2.1 ∧
      IsLocallyEligiblePivot b A B x ij.1.1 ij.1.2 ∧
      IsLocallyEligiblePivot b A B x ij.2.1 ij.2.2 ∧
      (¬ MenWeaklyPrefer (profileOfScores x) ij.1.1 ij.2.1) ∧
      (¬ MenWeaklyPrefer (profileOfScores x) ij.2.1 ij.1.1)}
private def incomparableEligibleAnchorMarksEvent (b A B : ℝ)
    (i j : Matching n × Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x i.1 ∧ IsScoreStable x j.1 ∧
    IsLocallyEligiblePivot b A B x i.1 i.2 ∧ IsLocallyEligiblePivot b A B x j.1 j.2 ∧
    (¬ MenWeaklyPrefer (profileOfScores x) i.1 j.1) ∧
    (¬ MenWeaklyPrefer (profileOfScores x) j.1 i.1)}
theorem measurableSet_incomparableEligibleAnchorMarksEvent (b A B : ℝ)
    (i j : Matching n × Matching n) : MeasurableSet (incomparableEligibleAnchorMarksEvent b A B i j) :=
  (measurableSet_isScoreStable i.1).inter ((measurableSet_isScoreStable j.1).inter
    ((measurableSet_isLocallyEligiblePivot b A B i.1 i.2).inter
      ((measurableSet_isLocallyEligiblePivot b A B j.1 j.2).inter
        (measurable_profileOfScores n (MeasurableSet.of_discrete :
          MeasurableSet {p : Profile n | (¬ MenWeaklyPrefer p i.1 j.1) ∧
            (¬ MenWeaklyPrefer p j.1 i.1)})))))
theorem natCard_incomparableEligibleAnchorMarks_eq_sum {R : Type*} [AddCommMonoidWithOne R]
    (b A B : ℝ) (x : ScoreProfile n) :
    (Nat.card (IncomparableEligibleAnchorMarks b A B x) : R) =
      ∑ i : Matching n × Matching n, ∑ j : Matching n × Matching n,
        (incomparableEligibleAnchorMarksEvent b A B i j).indicator (fun _ ↦ (1 : R)) x := by
  classical
  let P (ij : (Matching n × Matching n) × (Matching n × Matching n)) :=
    x ∈ incomparableEligibleAnchorMarksEvent b A B ij.1 ij.2
  change (Nat.card {ij // P ij} : R) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype P, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases h : x ∈ incomparableEligibleAnchorMarksEvent b A B i j
  · rw [if_pos (show P (i, j) from h), indicator_of_mem h, Nat.cast_one]
  · rw [if_neg (show ¬ P (i, j) from h), indicator_of_notMem h]
private noncomputable def twoForwardWindowConstant (b A : ℝ) : ℝ :=
  Real.exp (1 + 2 * A) * ((A + 1) / b) ^ 2 * (27 + 48 * A)
private class LPHypA : Prop where
  bound : ∀ {b A : ℝ}, 0 < b → 0 ≤ A →
    ∀ᶠ n : ℕ in atTop, ∀ B : ℝ,
      (∫⁻ x, (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ≥0∞)
        ∂continuousScoreLaw n) ≤
        2 * ENNReal.ofReal (meanUpperConstant * twoForwardWindowConstant b A * Real.sqrt n * Real.log n +
          (n : ℝ) ^ (-3 : ℝ))
theorem eventually_lintegral_card_incomparableEligibleAnchorMarks_le [h : LPHypA] {b A : ℝ}
    (hb : 0 < b) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop, ∀ B : ℝ,
      (∫⁻ x, (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ≥0∞)
        ∂continuousScoreLaw n) ≤
        2 * ENNReal.ofReal (meanUpperConstant * twoForwardWindowConstant b A * Real.sqrt n * Real.log n +
          (n : ℝ) ^ (-3 : ℝ)) := h.bound hb hA
end DiagLP
end

-- PivotLocalMomentUpper
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace DiagLP
variable {n : ℕ}
private theorem measurable_localUpperReverseProfile (μ : Matching n)
    (d : DiagonalScorePairs n) : Measurable (fun z : OffDiagonalScorePairs n ↦
      swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) :=
  (show Measurable (swapProfile (n := n)) from fun _ _ ↦ MeasurableSet.of_discrete).comp
    ((measurable_profileOfScores n).comp (measurable_fixedDiagonalReconstruction μ d))
private theorem markedFilteredChoice_realizes {μ ρ σ : Matching n}
    {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ} {x : ScoreProfile n}
    (h : σ ∈ markedFilteredChoices μ ρ flag K L t x) :
    RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ := by
  classical
  exact (mem_compatibleReversePermutations.mp (Finset.mem_filter.mp
    (mem_markedFilteredChoices.mp h).2).1).2.1
theorem lintegral_realizedReverseSupportCard_le (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (k : ℕ) {a D δ C : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hu : ReverseFilterUpperControls d flag δ C) :
    (∫⁻ z, (realizedReversePermutationCount (Finset.univ.filter
      (fun σ : Matching n ↦ σ.support.card = k))
      (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm : ℝ≥0∞)
      ∂forwardMaskRevealLaw d flag U) ≤
      (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (1 + δ) ^ k := by
  classical
  let ν := forwardMaskRevealLaw d flag U
  let P := fun z : OffDiagonalScorePairs n ↦ swapProfile (profileOfScores
    ((splitScorePairs μ).symm (d, z)))
  let S := (Finset.univ : Finset (Matching n)).filter (fun σ ↦ σ.support.card = k)
  let r := reverseSpouseWeights μ d
  let c := ν univ
  let q := ENNReal.ofReal (1 + δ)
  change (∫⁻ z, (realizedReversePermutationCount S (P z) μ.symm : ℝ≥0∞) ∂ν) ≤ c * q ^ k
  rw [lintegral_realizedReversePermutationCount ν P (measurable_localUpperReverseProfile μ d) μ.symm S]
  calc
    _ ≤ ∑ σ ∈ S, (c * q ^ k) * ∏ i ∈ σ.support, r i := by
      refine Finset.sum_le_sum fun σ hσ ↦ ?_
      have hk : σ.support.card = k := (Finset.mem_filter.mp hσ).2
      have he := measure_realizesReverseSuccessorPermutation_fixedMask μ σ d flag U
        h.measurable_reveal h.female_nonneg h.female_lt_one h.tie_free
      rw [← forwardMaskRevealLaw_univ μ d flag U h.measurable_reveal h.female_nonneg
        h.female_lt_one h.tie_free] at he
      change ν {z | RealizesSuccessorPermutation (P z) μ.symm σ} ≤ _
      rw [he, mul_assoc]
      refine mul_le_mul_right ?_ c
      calc
        _ ≤ ∏ i ∈ σ.support, q * r (σ i) := by
          refine Finset.prod_le_prod' fun i _ ↦ ?_
          exact normalizedForwardInactiveColumnLaw_reverseArc_le d flag (μ.symm i) (μ.symm (σ i))
            (h.female_nonneg _) (h.female_lt_one _) h.male_mem h.male_total_pos
            (by linarith [hu.perturbation_nonneg]) (fun j _ ↦ hu.competitor_mass _ j)
        _ = _ := by
          rw [σ.prod_comp σ.support (fun i ↦ q * r i) (fun _ hi ↦ Equiv.Perm.mem_support.mpr hi),
            Finset.prod_mul_distrib, Finset.prod_const, hk]
    _ = (c * q ^ k) * ∑ σ ∈ S, ∏ i ∈ σ.support, r i := (Finset.mul_sum ..).symm
    _ ≤ (c * q ^ k) * 1 := mul_le_mul_right
      (sum_supportPermutation_weights_le_one k r
        (sum_reverseSpouseWeights μ d (fun i ↦ (h.male_mem i).1) h.male_total_pos)) _
    _ = _ := mul_one _
private theorem card_markedFilteredChoices_le_sum_supportSizes
    (μ ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    (t : ℝ) (x : ScoreProfile n) :
    (markedFilteredChoices μ ρ flag K L t x).card ≤
      ∑ k ∈ Finset.range (K + 1), realizedReversePermutationCount (Finset.univ.filter
        (fun σ : Matching n ↦ σ.support.card = k)) (swapProfile (profileOfScores x)) μ.symm := by
  classical
  let S (k : ℕ) := (Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k)).filter
    (RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm)
  have hdisj : (↑(Finset.range (K + 1)) : Set ℕ).PairwiseDisjoint S := by
    intro k _ l _ hne
    exact Finset.disjoint_left.mpr fun σ hk hl ↦
      hne (((Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2).symm.trans
        ((Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2))
  change _ ≤ ∑ k ∈ Finset.range (K + 1), (S k).card
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro σ hσ
  exact Finset.mem_biUnion.mpr ⟨σ.support.card,
    Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_markedFilteredChoices.mp hσ).1),
    Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, markedFilteredChoice_realizes hσ⟩⟩
theorem lintegral_markedFilteredChoices_fixedMask_le (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (K L : ℕ) (t : ℝ) {a D δ C : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hu : ReverseFilterUpperControls d flag δ C) :
    (∫⁻ z, ((markedFilteredChoices μ ρ flag K L t
      ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞) ∂forwardMaskRevealLaw d flag U) ≤
      (forwardMaskRevealLaw d flag U) univ * (ENNReal.ofReal (1 + δ) ^ K * (↑(K + 1) : ℝ≥0∞)) := by
  classical
  let ν := forwardMaskRevealLaw d flag U
  let f (k : ℕ) (z : OffDiagonalScorePairs n) : ℝ≥0∞ :=
    realizedReversePermutationCount (Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k))
      (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm
  let q := ENNReal.ofReal (1 + δ)
  have hf (k : ℕ) : Measurable (f k) :=
    (show Measurable (fun p : Profile n ↦ (realizedReversePermutationCount
      (Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k)) p μ.symm : ℝ≥0∞)) from
        fun _ _ ↦ MeasurableSet.of_discrete).comp (measurable_localUpperReverseProfile μ d)
  have hq : 1 ≤ q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hu.perturbation_nonneg)
  calc
    _ ≤ ∫⁻ z, ∑ k ∈ Finset.range (K + 1), f k z ∂ν := by
      apply lintegral_mono
      intro z
      change _ ≤ ∑ k ∈ Finset.range (K + 1), f k z
      dsimp only [f]
      rw [← Nat.cast_sum]
      exact Nat.cast_le.mpr (card_markedFilteredChoices_le_sum_supportSizes μ ρ flag K L t _)
    _ = ∑ k ∈ Finset.range (K + 1), ∫⁻ z, f k z ∂ν := lintegral_finsetSum _ (fun k _ ↦ hf k)
    _ ≤ ∑ _k ∈ Finset.range (K + 1), ν univ * q ^ K := by
      refine Finset.sum_le_sum fun k hk ↦ ?_
      exact (lintegral_realizedReverseSupportCard_le μ ρ d flag U k h hu).trans
        (mul_le_mul_right (pow_le_pow_right' hq (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) _)
    _ = ν univ * (q ^ K * (↑(K + 1) : ℝ≥0∞)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ac_rfl
private theorem card_markedFilteredChoices_le_two_pow
    (μ ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    (t : ℝ) (x : ScoreProfile n) :
    (markedFilteredChoices μ ρ flag K L t x).card ≤
      2 ^ numExposedRotations (swapProfile (profileOfScores x)) μ.symm := by
  classical
  let P := fun σ : Matching n ↦
    RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ
  let S := Finset.univ.filter P
  have hc : S.card = Nat.card {σ : Matching n // P σ} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype S (by simp [S])]
  rw [← card_realizesSuccessorPermutation, ← hc]
  exact Finset.card_le_card fun σ hσ ↦ Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, markedFilteredChoice_realizes hσ⟩
theorem lintegral_sq_markedFilteredChoices_fixedMask_le (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (K L : ℕ) (t : ℝ) (hn : 0 < n) {a D δ C : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hu : ReverseFilterUpperControls d flag δ C) :
    (∫⁻ z, ((markedFilteredChoices μ ρ flag K L t
      ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞) ^ 2 ∂forwardMaskRevealLaw d flag U) ≤
      (forwardMaskRevealLaw d flag U) univ *
        ENNReal.ofReal (reverseFilterSecondMomentConstant C * (n : ℝ) * Real.sqrt n) := by
  let P := fun z : OffDiagonalScorePairs n ↦ swapProfile (profileOfScores
    ((splitScorePairs μ).symm (d, z)))
  calc
    _ ≤ ∫⁻ z, (4 : ℝ≥0∞) ^ numExposedRotations (P z) μ.symm ∂forwardMaskRevealLaw d flag U := by
      apply lintegral_mono
      intro z
      have hc : ((markedFilteredChoices μ ρ flag K L t
          ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞) ≤
          (2 : ℝ≥0∞) ^ numExposedRotations (P z) μ.symm := by
        exact_mod_cast card_markedFilteredChoices_le_two_pow μ ρ flag K L t
          ((splitScorePairs μ).symm (d, z))
      refine (pow_le_pow_left' hc 2).trans_eq ?_
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    _ ≤ _ := by
      have hm := lintegral_four_pow_numReverseExposedRotations_fixedMask_le μ d flag U
        h.measurable_reveal hn h.female_nonneg h.female_lt_one h.male_mem h.male_total_pos
        hu.perturbation_nonneg hu.perturbation_le hu.competitor_mass h.tie_free
      dsimp only at hm
      rw [← forwardMaskRevealLaw_univ μ d flag U h.measurable_reveal h.female_nonneg
        h.female_lt_one h.tie_free] at hm
      exact hm
private noncomputable def localPivotMomentCeiling (b A B c : ℝ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ :=
  {x | IsLocallyEligiblePivot b A B x μ ρ}.indicator (fun _ ↦ c) x
theorem measurable_maleReveal_localPivotMomentCeiling (b A B c : ℝ) (μ ρ : Matching n) :
    Measurable[pivotMaleRevealSpace μ] (localPivotMomentCeiling b A B c μ ρ) :=
  measurable_const.indicator (measurableSet_isLocallyEligiblePivot_maleRevealSpace b A B μ ρ)
private theorem lintegral_fixedMask_localPivotMoment_le {b A B c : ℝ} (K L e : ℕ)
    (he : e ≠ 0) (μ ρ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) {W : Set (PivotMaleRevealData n)}
    (hW : MeasurableSet W)
    (hfixed : ∀ U : Set (ForwardRevealedMaleScores flag), MeasurableSet U →
      U ⊆ eligiblePivotRevealSet d flag ρ (localPivotIncrementCap B d) →
      LocalPivotGeometry b A B μ ρ d flag →
      (∫⁻ z, ((markedFilteredChoices μ ρ flag K L
        (reverseIncrementCutoff n (reverseDiagonalMaleTotal d))
        ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞) ^ e ∂forwardMaskRevealLaw d flag U) ≤
        (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal c) :
    let R (z : OffDiagonalScorePairs n) := (splitScorePairs μ).symm (d, z)
    let S := pivotMaleReveal μ ⁻¹' W
    let ν := ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
      (forwardScoreMaskEvent d flag)
    (∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal
      (localFilteredDecorationCount b A B K L μ ρ x) ^ e) (R z) ∂ν) ≤
      ∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal
        (localPivotMomentCeiling b A B c μ ρ x)) (R z) ∂ν := by
  classical
  dsimp only
  let R (z : OffDiagonalScorePairs n) := (splitScorePairs μ).symm (d, z)
  let S := pivotMaleReveal μ ⁻¹' W
  let ν := ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
    (forwardScoreMaskEvent d flag)
  let U₀ := eligiblePivotRevealSet d flag ρ (localPivotIncrementCap B d)
  let U := U₀ ∩ (fun v ↦ pivotMaleRevealSection flag (d, v)) ⁻¹' W
  let V := (fun z ↦ (forwardRevealWithColumns flag z).1) ⁻¹' U
  let N (z : OffDiagonalScorePairs n) : ℝ≥0∞ := ((markedFilteredChoices μ ρ flag K L
    (reverseIncrementCutoff n (reverseDiagonalMaleTotal d)) (R z)).card : ℝ≥0∞) ^ e
  have hmask : ∀ᵐ z ∂ν, z ∈ forwardScoreMaskEvent d flag :=
    ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)
  change (∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal
    (localFilteredDecorationCount b A B K L μ ρ x) ^ e) (R z) ∂ν) ≤
    ∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal
      (localPivotMomentCeiling b A B c μ ρ x)) (R z) ∂ν
  by_cases hgeo : LocalPivotGeometry b A B μ ρ d flag
  · have hU : MeasurableSet U := (measurableSet_eligiblePivotRevealSet d flag ρ _).inter
      (hW.preimage ((measurable_pivotMaleRevealSection flag).comp
        (measurable_const.prodMk measurable_id)))
    have hV : MeasurableSet V := hU.preimage (measurable_forwardRevealWithColumns flag).fst
    have hV' (z : OffDiagonalScorePairs n) (hz : z ∈ forwardScoreMaskEvent d flag) :
        z ∈ V ↔ R z ∈ S ∧ IsLocallyEligiblePivot b A B (R z) μ ρ := by
      have hE := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ d z flag hz
      have hR := pivotMaleReveal_reconstruct μ d z flag hz
      change ((forwardRevealWithColumns flag z).1 ∈ U₀ ∧
        pivotMaleRevealSection flag (d, (forwardRevealWithColumns flag z).1) ∈ W) ↔ _
      change _ ↔ pivotMaleReveal μ (R z) ∈ W ∧ _
      rw [show pivotMaleReveal μ (R z) = _ from hR, hE, and_iff_right hgeo, and_comm]
    have hceil : (fun z ↦ S.indicator (fun x ↦ ENNReal.ofReal
        (localPivotMomentCeiling b A B c μ ρ x)) (R z)) =ᵐ[ν]
        V.indicator (fun _ ↦ ENNReal.ofReal c) := by
      filter_upwards [hmask] with z hz
      by_cases hs : R z ∈ S <;> by_cases hE : IsLocallyEligiblePivot b A B (R z) μ ρ <;>
        simp [localPivotMomentCeiling, indicator_apply, hV' z hz, hs, hE]
    have hN : (fun z ↦ S.indicator (fun x ↦ ENNReal.ofReal
        (localFilteredDecorationCount b A B K L μ ρ x) ^ e) (R z)) =ᵐ[ν] V.indicator N := by
      filter_upwards [hmask] with z hz
      by_cases hs : R z ∈ S
      · by_cases hE : IsLocallyEligiblePivot b A B (R z) μ ρ
        · have hR : splitScorePairs μ (R z) = (d, z) := (splitScorePairs μ).apply_symm_apply _
          have hz' : (splitScorePairs μ (R z)).2 ∈
              forwardScoreMaskEvent (splitScorePairs μ (R z)).1 flag := by rw [hR]; exact hz
          rw [indicator_of_mem hs, indicator_of_mem ((hV' z hz).mpr ⟨hs, hE⟩),
            localFilteredDecorationCount_of_eligible_of_fixedMask K L hE hz', hR]
          simp [N]
        · simp [localFilteredDecorationCount, hV' z hz, hs, hE, zero_pow he]
      · simp [hV' z hz, hs]
    rw [lintegral_congr_ae hN, lintegral_congr_ae hceil, lintegral_indicator hV,
      lintegral_indicator hV, lintegral_const, mul_comm]
    exact hfixed U hU inter_subset_left hgeo
  · have hz : (fun z ↦ S.indicator (fun x ↦ ENNReal.ofReal
        (localFilteredDecorationCount b A B K L μ ρ x) ^ e) (R z)) =ᵐ[ν] (fun _ ↦ 0) := by
      filter_upwards [hmask] with z hz
      have hE := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ d z flag hz
      have hnot : ¬ IsLocallyEligiblePivot b A B (R z) μ ρ := fun h ↦ hgeo (hE.mp h).1
      simp [localFilteredDecorationCount, indicator_apply, hnot, zero_pow he]
    rw [lintegral_congr_ae hz, lintegral_zero]
    exact zero_le
theorem setLIntegral_localPivotMoment_le {b A B c : ℝ} (K L e : ℕ) (he : e ≠ 0)
    (μ ρ : Matching n)
    (hfixed : ∀ᵐ d ∂diagonalScoreLaw n, ∀ (flag : OffDiagonalCellIndex n → Bool)
      (U : Set (ForwardRevealedMaleScores flag)), MeasurableSet U →
      U ⊆ eligiblePivotRevealSet d flag ρ (localPivotIncrementCap B d) →
      LocalPivotGeometry b A B μ ρ d flag →
      (∫⁻ z, ((markedFilteredChoices μ ρ flag K L
        (reverseIncrementCutoff n (reverseDiagonalMaleTotal d))
        ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞) ^ e ∂forwardMaskRevealLaw d flag U) ≤
        (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal c)
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotMaleRevealSpace μ] S) :
    (∫⁻ x in S, ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ x) ^ e
      ∂stableMarkScoreLaw μ) ≤
      ∫⁻ x in S, ENNReal.ofReal (localPivotMomentCeiling b A B c μ ρ x) ∂stableMarkScoreLaw μ := by
  have hSm := pivotMaleRevealSpace_le μ _ hS
  change ∃ W : Set (PivotMaleRevealData n), MeasurableSet W ∧ pivotMaleReveal μ ⁻¹' W = S at hS
  obtain ⟨W, hW, rfl⟩ := hS
  let S := pivotMaleReveal μ ⁻¹' W
  let f := fun x ↦ ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ x) ^ e
  let g := fun x ↦ ENNReal.ofReal (localPivotMomentCeiling b A B c μ ρ x)
  have hf : Measurable f := (ENNReal.measurable_ofReal.comp
    (measurable_localFilteredDecorationCount b A B K L μ ρ)).pow_const _
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    ((measurable_maleReveal_localPivotMomentCeiling b A B c μ ρ).mono
      (pivotMaleRevealSpace_le μ) le_rfl)
  change (∫⁻ x in S, f x ∂stableMarkScoreLaw μ) ≤ ∫⁻ x in S, g x ∂stableMarkScoreLaw μ
  calc
    _ = ∫⁻ x, S.indicator f x ∂stableMarkScoreLaw μ := (lintegral_indicator hSm f).symm
    _ ≤ ∫⁻ x, S.indicator g x ∂stableMarkScoreLaw μ := by
      rw [lintegral_stableMarkScoreLaw μ (hf.indicator hSm),
        lintegral_stableMarkScoreLaw μ (hg.indicator hSm)]
      apply lintegral_mono_ae
      filter_upwards [hfixed] with d hd
      rw [lintegral_offDiagonalNonblocking_eq_sum_masks d,
        lintegral_offDiagonalNonblocking_eq_sum_masks d]
      exact Finset.sum_le_sum fun flag _ ↦
        lintegral_fixedMask_localPivotMoment_le K L e he μ ρ d flag hW (hd flag)
    _ = _ := lintegral_indicator hSm g
theorem integrable_localFilteredDecorationCount_pow (b A B : ℝ) (K L e : ℕ)
    (μ ρ : Matching n) (ν : Measure (ScoreProfile n)) [IsFiniteMeasure ν] :
    Integrable (fun x ↦ localFilteredDecorationCount b A B K L μ ρ x ^ e) ν := by
  refine (integrable_const ((n.factorial : ℝ) ^ e)).mono'
    ((measurable_localFilteredDecorationCount b A B K L μ ρ).pow_const e).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  have hp : 0 ≤ localFilteredDecorationCount b A B K L μ ρ x ^ e :=
    pow_nonneg (localFilteredDecorationCount_nonneg b A B K L μ ρ x) _
  rw [Real.norm_eq_abs, abs_of_nonneg hp]
  exact pow_le_pow_left₀ (localFilteredDecorationCount_nonneg b A B K L μ ρ x)
    (localFilteredDecorationCount_le_factorial b A B K L μ ρ x) e
private theorem setIntegral_localPivotMoment_le_of_setLIntegral {b A B c : ℝ} (K L e : ℕ)
    (hc : 0 ≤ c) (μ ρ : Matching n) {S : Set (ScoreProfile n)}
    (hlin : (∫⁻ x in S, ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ x) ^ e
      ∂stableMarkScoreLaw μ) ≤
      ∫⁻ x in S, ENNReal.ofReal (localPivotMomentCeiling b A B c μ ρ x) ∂stableMarkScoreLaw μ) :
    (∫ x in S, localFilteredDecorationCount b A B K L μ ρ x ^ e ∂stableMarkScoreLaw μ) ≤
      ∫ x in S, localPivotMomentCeiling b A B c μ ρ x ∂stableMarkScoreLaw μ := by
  have hf := (integrable_localFilteredDecorationCount_pow b A B K L e μ ρ
    (stableMarkScoreLaw μ)).integrableOn (s := S)
  have hg := ((integrable_const c (μ := stableMarkScoreLaw μ)).indicator
    (measurableSet_isLocallyEligiblePivot b A B μ ρ)).integrableOn (s := S)
  have hnf : ∀ᵐ x ∂(stableMarkScoreLaw μ).restrict S,
      0 ≤ localFilteredDecorationCount b A B K L μ ρ x ^ e :=
    Eventually.of_forall fun x ↦ pow_nonneg (localFilteredDecorationCount_nonneg b A B K L μ ρ x) _
  have hng : ∀ᵐ x ∂(stableMarkScoreLaw μ).restrict S, 0 ≤ localPivotMomentCeiling b A B c μ ρ x :=
    Eventually.of_forall fun x ↦ Set.indicator_nonneg (fun _ _ ↦ hc) x
  rw [integral_eq_lintegral_of_nonneg_ae hnf hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hng hg.aestronglyMeasurable]
  apply ENNReal.toReal_mono ((hasFiniteIntegral_iff_ofReal hng).mp hg.2).ne
  simpa only [ENNReal.ofReal_pow (localFilteredDecorationCount_nonneg b A B K L μ ρ _)] using hlin
private theorem pow_arcInflation_le_of_support {K : ℕ} {δ κ : ℝ} (hn : 0 < n)
    (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 2 / Real.sqrt (n : ℝ))
    (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    ENNReal.ofReal (1 + δ) ^ K ≤ ENNReal.ofReal (Real.exp (2 * κ)) := by
  have hn' : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  rw [← ENNReal.ofReal_pow (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (1 + δ) ^ K ≤ (Real.exp δ) ^ K := pow_le_pow_left₀ (by positivity)
      (by simpa only [add_comm] using Real.add_one_le_exp δ) _
    _ = Real.exp ((K : ℝ) * δ) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr <| calc
      (K : ℝ) * δ ≤ (κ * Real.sqrt (n : ℝ)) * (2 / Real.sqrt (n : ℝ)) :=
        mul_le_mul hK hδ' hδ (by positivity)
      _ = 2 * κ := by field_simp
private abbrev LocalUpperMomentControls (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) : Prop :=
  ∀ᵐ d ∂diagonalScoreLaw n, ∀ flag,
    LocalPivotGeometry b A B μ ρ d flag →
    EligibleReverseMomentCertificate μ ρ d flag K L (localPivotIncrementCap B d)
      (2048 * Real.log (n : ℝ) / n) ((n : ℝ) ^ (-11 / 20 : ℝ))
      (B / Real.sqrt (n : ℝ))
theorem setIntegral_localFilteredDecorationCount_le {b A B κ : ℝ} (K L : ℕ)
    (μ ρ : Matching n) (hκ : 0 ≤ κ) (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hcert : LocalUpperMomentControls b A B K L μ ρ)
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotMaleRevealSpace μ] S) :
    (∫ x in S, localFilteredDecorationCount b A B K L μ ρ x ∂stableMarkScoreLaw μ) ≤
      ∫ x in S, localPivotMomentCeiling b A B
        (Real.exp (2 * κ) * (↑(K + 1) : ℝ)) μ ρ x ∂stableMarkScoreLaw μ := by
  have hlin := setLIntegral_localPivotMoment_le (b := b) (A := A) (B := B)
    (c := Real.exp (2 * κ) * (↑(K + 1) : ℝ)) K L 1 one_ne_zero μ ρ ?_ hS
  · simpa only [pow_one] using
      setIntegral_localPivotMoment_le_of_setLIntegral K L 1 (by positivity) μ ρ hlin
  filter_upwards [hcert] with d hd flag U hU hsub hgeo
  have h := hd flag hgeo
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_natCast]
  simp only [pow_one]
  refine (lintegral_markedFilteredChoices_fixedMask_le μ ρ d flag U K L _
    (h.compatibility.restrict_reveal hU hsub) h.upper).trans ?_
  exact mul_le_mul_right (mul_le_mul_left (pow_arcInflation_le_of_support h.n_pos hκ
    h.upper.perturbation_nonneg h.upper.perturbation_le hK) _) _
theorem setIntegral_sq_localFilteredDecorationCount_le {b A B : ℝ} (K L : ℕ)
    (μ ρ : Matching n) (hcert : LocalUpperMomentControls b A B K L μ ρ)
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotMaleRevealSpace μ] S) :
    (∫ x in S, localFilteredDecorationCount b A B K L μ ρ x ^ 2 ∂stableMarkScoreLaw μ) ≤
      ∫ x in S, localPivotMomentCeiling b A B
        (reverseFilterSecondMomentConstant 2 * (n : ℝ) * Real.sqrt n) μ ρ x ∂stableMarkScoreLaw μ := by
  have hc : 0 ≤ reverseFilterSecondMomentConstant 2 * (n : ℝ) * Real.sqrt n := by
    unfold reverseFilterSecondMomentConstant
    positivity
  apply setIntegral_localPivotMoment_le_of_setLIntegral K L 2 hc μ ρ
  apply setLIntegral_localPivotMoment_le K L 2 (by decide) μ ρ _ hS
  filter_upwards [hcert] with d hd flag U hU hsub hgeo
  have h := hd flag hgeo
  exact lintegral_sq_markedFilteredChoices_fixedMask_le μ ρ d flag U K L _ h.n_pos
    (h.compatibility.restrict_reveal hU hsub) h.upper
theorem localPivotConditionalMean_le_ceiling_ae {b A B κ : ℝ} (K L : ℕ)
    (μ ρ : Matching n) (hκ : 0 ≤ κ) (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hcert : LocalUpperMomentControls b A B K L μ ρ) :
    localPivotConditionalMean b A B K L μ ρ ≤ᵐ[stableMarkScoreLaw μ]
      localPivotMomentCeiling b A B (Real.exp (2 * κ) * (↑(K + 1) : ℝ)) μ ρ := by
  let ν := stableMarkScoreLaw μ
  let m := pivotMaleRevealSpace μ
  let f := localFilteredDecorationCount b A B K L μ ρ
  let g := localPivotMomentCeiling b A B (Real.exp (2 * κ) * (↑(K + 1) : ℝ)) μ ρ
  have hm := pivotMaleRevealSpace_le μ
  have hf : Integrable f ν := integrable_localFilteredDecorationCount b A B K L μ ρ ν
  have hg : Integrable g ν := (integrable_const _).indicator
    (measurableSet_isLocallyEligiblePivot b A B μ ρ)
  have hgm : StronglyMeasurable[m] g :=
    (measurable_maleReveal_localPivotMomentCeiling b A B _ μ ρ).stronglyMeasurable
  have hcm : StronglyMeasurable[m] (ν[f|m]) := stronglyMeasurable_condExp
  change ν[f|m] ≤ᵐ[ν] g
  apply ae_of_ae_trim hm
  refine ae_le_of_forall_setIntegral_le
    ((integrable_condExp (f := f)).trim hm hcm) (hg.trim hm hgm) fun S hS _ ↦ ?_
  rw [← setIntegral_trim hm hgm hS, ← setIntegral_trim hm hcm hS, setIntegral_condExp hm hf hS]
  exact setIntegral_localFilteredDecorationCount_le K L μ ρ hκ hK hcert hS
theorem eventually_localPivotConditionalMean_le_ceiling_ae (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop, ∀ (μ ρ : Matching n) (b A : ℝ),
      localPivotConditionalMean b A B (K n) (L n) μ ρ ≤ᵐ[stableMarkScoreLaw μ]
        localPivotMomentCeiling b A B (Real.exp (2 * κ) * (↑(K n + 1) : ℝ)) μ ρ := by
  filter_upwards [eventually_ae_diagonal_localPivotGeometry_certificate K L hB hκ hK hL
    hsmallLabel hsmallCompat, hK] with n hn hcap μ ρ b A
  exact localPivotConditionalMean_le_ceiling_ae (K n) (L n) μ ρ hκ hcap.2 <|
    (hn μ).mono fun d hd flag hgeom ↦ hd ρ flag hgeom
private theorem stableMark_localEligibility_mass_le (b A B : ℝ) (μ ρ : Matching n) :
    stableMarkScoreLaw μ {x | IsLocallyEligiblePivot b A B x μ ρ} ≤
      continuousScoreLaw n (scoreStableSingletonAnchorEvent μ ρ) := by
  rw [stableMarkScoreLaw, Measure.restrict_apply (measurableSet_isLocallyEligiblePivot b A B μ ρ)]
  apply measure_mono_ae
  filter_upwards [ae_injective_rows n] with x hx he
  exact ⟨he.2, he.1.isSoleForwardExposed hx⟩
theorem sum_stableMark_localEligibility_mass_le (b A B : ℝ) :
    (∑ μ : Matching n, ∑ ρ : Matching n,
      stableMarkScoreLaw μ {x | IsLocallyEligiblePivot b A B x μ ρ}) ≤
    ∫⁻ p, profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
      ∂(uniformProfile n).toMeasure := by
  rw [lintegral_profileSingletonAnchorLengthWeight_eq_sum_scoreStableSingletonAnchorEvent]
  simpa only [one_mul] using Finset.sum_le_sum fun μ (_ : μ ∈ Finset.univ) ↦
    Finset.sum_le_sum fun ρ (_ : ρ ∈ Finset.univ) ↦ stableMark_localEligibility_mass_le b A B μ ρ
theorem integral_sq_localFilteredDecorationCount_le_mass {b A B : ℝ} (K L : ℕ)
    (μ ρ : Matching n) (hcert : LocalUpperMomentControls b A B K L μ ρ) :
    (∫ x, localFilteredDecorationCount b A B K L μ ρ x ^ 2 ∂stableMarkScoreLaw μ) ≤
      (reverseFilterSecondMomentConstant 2 * (n : ℝ) * Real.sqrt n) *
        (stableMarkScoreLaw μ).real {x | IsLocallyEligiblePivot b A B x μ ρ} := by
  have h := setIntegral_sq_localFilteredDecorationCount_le K L μ ρ hcert
    (S := univ) MeasurableSet.univ
  rw [Measure.restrict_univ] at h
  unfold localPivotMomentCeiling at h
  rw [integral_indicator_const _ (measurableSet_isLocallyEligiblePivot b A B μ ρ), smul_eq_mul,
    mul_comm] at h
  exact h
theorem eventually_sum_integral_sq_localFilteredDecorationCount_le [LPHypB] (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop, ∀ b A : ℝ,
      (∑ μ : Matching n, ∑ ρ : Matching n,
        ∫ x, localFilteredDecorationCount b A B (K n) (L n) μ ρ x ^ 2 ∂stableMarkScoreLaw μ) ≤
        reverseFilterSecondMomentConstant 2 * (n : ℝ) * Real.sqrt n *
          ((singletonMomentScale * (108 + 48 * Real.exp 4)) * Real.sqrt n * Real.log n +
            (n : ℝ) ^ (-3 : ℝ)) := by
  filter_upwards [eventually_ae_diagonal_localPivotGeometry_certificate K L hB hκ hK hL
    hsmallLabel hsmallCompat, eventually_lintegral_profileSingletonAnchorCount_le,
    eventually_gt_atTop (0 : ℕ)] with n hn hmass hn' b A
  let E (μ ρ : Matching n) := {x | IsLocallyEligiblePivot b A B x μ ρ}
  let c := reverseFilterSecondMomentConstant 2 * (n : ℝ) * Real.sqrt n
  let M := (singletonMomentScale * (108 + 48 * Real.exp 4)) * Real.sqrt n * Real.log n +
    (n : ℝ) ^ (-3 : ℝ)
  have hc : 0 ≤ c := by unfold c reverseFilterSecondMomentConstant; positivity
  have hM : 0 ≤ M := by
    have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn')
    have hs := singletonMomentScale_pos
    unfold M
    positivity
  have hmass' : (∑ μ : Matching n, ∑ ρ : Matching n, stableMarkScoreLaw μ (E μ ρ)) ≤
      ENNReal.ofReal M := (sum_stableMark_localEligibility_mass_le b A B).trans hmass
  have hreal : (∑ μ : Matching n, ∑ ρ : Matching n, (stableMarkScoreLaw μ).real (E μ ρ)) ≤ M := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass'
    rw [ENNReal.toReal_ofReal hM, ENNReal.toReal_sum (fun μ _ ↦
      ENNReal.sum_ne_top.mpr fun ρ _ ↦ measure_ne_top (stableMarkScoreLaw μ) (E μ ρ))] at h
    simp_rw [ENNReal.toReal_sum (fun ρ _ ↦ measure_ne_top (stableMarkScoreLaw _) (E _ ρ))] at h
    exact h
  calc
    _ ≤ ∑ μ : Matching n, ∑ ρ : Matching n, c * (stableMarkScoreLaw μ).real (E μ ρ) := by
      refine Finset.sum_le_sum fun μ _ ↦ Finset.sum_le_sum fun ρ _ ↦ ?_
      exact integral_sq_localFilteredDecorationCount_le_mass (K n) (L n) μ ρ <|
        (hn μ).mono fun d hd flag hgeom ↦ hd ρ flag hgeom
    _ = c * ∑ μ : Matching n, ∑ ρ : Matching n, (stableMarkScoreLaw μ).real (E μ ρ) := by
      simp_rw [Finset.mul_sum]
    _ ≤ c * M := mul_le_mul_of_nonneg_left hreal hc
end DiagLP
end

-- PivotVarianceClosure
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators ENNReal Topology
namespace DiagLP
namespace PivotCountParameters
variable {n : ℕ}
private noncomputable def incomparableMeanProductMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n,
    {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.mean i * q.mean j) x
theorem integrable_incomparableMeanProductMass (q : PivotCountParameters) :
    Integrable (q.incomparableMeanProductMass (n := n)) (continuousScoreLaw n) := by
  have h (i : PivotMark n) : ∀ᵐ x ∂continuousScoreLaw n, |q.mean i x| ≤ (n.factorial : ℝ) :=
    (q.mean_mem_Icc_ae i).mono fun x hx ↦ (abs_of_nonneg hx.1).symm ▸ hx.2
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (integrable_mul_of_ae_abs_le_real (q.measurable_mean i) (q.measurable_mean j)
      (by positivity) (h i) (h j)).indicator (measurableSet_incomparableAnchors i.1 j.1)
theorem integral_incomparableMeanProductMass_nonneg (q : PivotCountParameters) :
    0 ≤ ∫ x, q.incomparableMeanProductMass x ∂continuousScoreLaw n := by
  apply integral_nonneg_of_ae
  have h := ae_all_iff.2 (q.mean_mem_Icc_ae (n := n))
  filter_upwards [h] with x hx
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    Set.indicator_nonneg (fun _ _ ↦ mul_nonneg (hx i).1 (hx j).1) _
private theorem mean_le_eligibleCeiling_ae (q : PivotCountParameters) (i : PivotMark n)
    {c : ℝ}
    (h : q.localMean i ≤ᵐ[stableMarkScoreLaw i.1]
      localPivotMomentCeiling q.lowerLength q.upperLength q.geometryBudget c i.1 i.2) :
    ∀ᵐ x ∂continuousScoreLaw n,
      q.mean i x ≤ {y | IsScoreStable y i.1 ∧
        IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget y i.1 i.2}.indicator
        (fun _ ↦ c) x := by
  filter_upwards [ae_scoreLaw_on_stableMark i h] with x hx
  by_cases hs : IsScoreStable x i.1
  · have he : {y | IsScoreStable y i.1 ∧
          IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget y i.1 i.2}.indicator
          (fun _ ↦ c) x = localPivotMomentCeiling q.lowerLength q.upperLength
            q.geometryBudget c i.1 i.2 x := by
      classical
      simp only [localPivotMomentCeiling, indicator_apply, mem_ofPred_eq, hs, true_and]
    rw [he, mean, onStableMark, indicator_of_mem (show x ∈ {y | IsScoreStable y i.1} from hs)]
    exact hx hs
  · simp [mean, onStableMark, hs]
private theorem incomparableMeanProductMass_le_ae (q : PivotCountParameters)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : PivotMark n, q.localMean i ≤ᵐ[stableMarkScoreLaw i.1]
      localPivotMomentCeiling q.lowerLength q.upperLength q.geometryBudget c i.1 i.2) :
    ∀ᵐ x ∂continuousScoreLaw n, q.incomparableMeanProductMass x ≤
      c ^ 2 * (Nat.card (IncomparableEligibleAnchorMarks
        q.lowerLength q.upperLength q.geometryBudget x) : ℝ) := by
  classical
  have hμ := ae_all_iff.2 (q.mean_mem_Icc_ae (n := n))
  have hcμ := ae_all_iff.2 (fun i : PivotMark n ↦ q.mean_le_eligibleCeiling_ae i (h i))
  filter_upwards [hμ, hcμ] with x hμ hx
  rw [natCard_incomparableEligibleAnchorMarks_eq_sum, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  let E (k : PivotMark n) := IsScoreStable x k.1 ∧
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x k.1 k.2
  by_cases hinc : IncomparableAnchors (profileOfScores x) i.1 j.1
  · have hmem : x ∈ incomparableEligibleAnchorMarksEvent
        q.lowerLength q.upperLength q.geometryBudget i j ↔ E i ∧ E j := by
      change (IsScoreStable x i.1 ∧ IsScoreStable x j.1 ∧
        IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 ∧
        IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x j.1 j.2 ∧
        IncomparableAnchors (profileOfScores x) i.1 j.1) ↔ _
      simp [E, hinc, and_assoc, and_left_comm]
    have hprod : q.mean i x * q.mean j x ≤
        (if E i then c else 0) * (if E j then c else 0) := by
      have hk (k : PivotMark n) : q.mean k x ≤ if E k then c else 0 := by
        simpa only [indicator_apply, E, mem_ofPred_eq] using hx k
      exact mul_le_mul (hk i) (hk j) (hμ j).1 (by split <;> positivity)
    change {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
      (q.mean i * q.mean j) x ≤ _
    rw [indicator_of_mem (show x ∈ {y | IncomparableAnchors (profileOfScores y) i.1 j.1}
      from hinc), Pi.mul_apply, indicator_apply, hmem]
    by_cases hi : E i <;> by_cases hj : E j <;> simpa [hi, hj, pow_two] using hprod
  · have he : x ∉ incomparableEligibleAnchorMarksEvent
        q.lowerLength q.upperLength q.geometryBudget i j :=
      fun hm ↦ hinc hm.2.2.2.2
    simp [hinc, he]
private theorem integrable_bareIncomparableAnchorCount (b A B : ℝ) :
    Integrable (fun x : ScoreProfile n ↦
      (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ)) (continuousScoreLaw n) := by
  simp_rw [natCard_incomparableEligibleAnchorMarks_eq_sum]
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (integrable_const _).indicator (measurableSet_incomparableEligibleAnchorMarksEvent b A B i j)
theorem integral_incomparableMeanProductMass_le (q : PivotCountParameters) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : PivotMark n, q.localMean i ≤ᵐ[stableMarkScoreLaw i.1]
      localPivotMomentCeiling q.lowerLength q.upperLength q.geometryBudget c i.1 i.2) :
    (∫ x, q.incomparableMeanProductMass x ∂continuousScoreLaw n) ≤
      c ^ 2 * ∫ x, (Nat.card (IncomparableEligibleAnchorMarks
        q.lowerLength q.upperLength q.geometryBudget x) : ℝ) ∂continuousScoreLaw n := by
  rw [← integral_const_mul]
  exact integral_mono_ae q.integrable_incomparableMeanProductMass
    ((integrable_bareIncomparableAnchorCount _ _ _).const_mul _)
    (q.incomparableMeanProductMass_le_ae hc h)
end PivotCountParameters
private theorem eventually_log_natCast_atLeast (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, a ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop a
private theorem eventually_pivotMomentEnvelope_le {C D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ n : ℕ in atTop, D * (n : ℝ) * Real.sqrt n *
      (C * Real.sqrt n * Real.log n + (n : ℝ) ^ (-3 : ℝ)) ≤
      (D * (C + 1)) * ((n : ℝ) ^ 2 * Real.log n) := by
  filter_upwards [eventually_log_natCast_atLeast 1, eventually_ge_atTop (1 : ℕ)] with n hlog hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn'
  have hremainder : (n : ℝ) ^ (-3 : ℝ) ≤ Real.sqrt n * Real.log n :=
    (Real.rpow_le_one_of_one_le_of_nonpos hn' (by norm_num)).trans
      (one_le_mul_of_one_le_of_one_le hs hlog)
  calc
    _ ≤ D * (n : ℝ) * Real.sqrt n * (C * Real.sqrt n * Real.log n + Real.sqrt n * Real.log n) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hremainder _) (by positivity)
    _ = _ := by
      rw [show C * Real.sqrt n * Real.log n + Real.sqrt n * Real.log n =
        (C + 1) * Real.sqrt n * Real.log n by ring]
      calc
        _ = D * (C + 1) * ((n : ℝ) * (Real.sqrt n) ^ 2 * Real.log n) := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]; ring
private theorem isLittleO_of_eventually_nonneg_le_pivotMomentEnvelope {f : ℕ → ℝ} {D : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ f n ∧
      f n ≤ D * ((n : ℝ) ^ 2 * Real.log n)) :
    f =o[atTop] (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2) := by
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [h, eventually_log_natCast_atLeast (D / c)] with n hf hn
  have hlog := Real.log_natCast_nonneg n
  have hDc : D ≤ c * Real.log n := by
    have := (div_le_iff₀ hc).mp hn
    rwa [mul_comm] at this
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf.1, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ D * ((n : ℝ) ^ 2 * Real.log n) := hf.2
    _ ≤ (c * Real.log n) * ((n : ℝ) ^ 2 * Real.log n) :=
      mul_le_mul_of_nonneg_right hDc (by positivity)
    _ = _ := by ring
variable {n : ℕ}
private noncomputable def pivotRawDiagonalMass (q : PivotCountParameters) (n : ℕ) : ℝ :=
  ∑ i : PivotMark n, ∫ x, (q.localCount i x) ^ 2 ∂stableMarkScoreLaw i.1
theorem isLittleO_pivotRawDiagonalMass [LPHypB] (b A B κ : ℝ) (K L : ℕ → ℕ)
    (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    (fun n : ℕ ↦ pivotRawDiagonalMass ⟨b, A, B, K n, L n⟩ n) =o[atTop]
      (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2) := by
  let D := reverseFilterSecondMomentConstant 2
  let C := singletonMomentScale * (108 + 48 * Real.exp 4)
  have hD : 0 ≤ D := by unfold D reverseFilterSecondMomentConstant; positivity
  refine isLittleO_of_eventually_nonneg_le_pivotMomentEnvelope
    (D := D * (C + 1)) ?_
  filter_upwards [eventually_sum_integral_sq_localFilteredDecorationCount_le K L
    hB hκ hK hL hsmallLabel hsmallCompat, eventually_pivotMomentEnvelope_le (C := C) hD]
    with n h₁ h₂
  unfold pivotRawDiagonalMass
  refine ⟨Finset.sum_nonneg fun i _ ↦ integral_nonneg fun x ↦ sq_nonneg _, ?_⟩
  rw [Fintype.sum_prod_type]
  exact (h₁ b A).trans h₂
private theorem integral_bareIncomparableAnchorCount_le {b A B : ℝ} {m : ℝ} (hm : 0 ≤ m)
    (h : (∫⁻ x, (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ≥0∞)
        ∂continuousScoreLaw n) ≤ 2 * ENNReal.ofReal m) :
    (∫ x, (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ) ∂continuousScoreLaw n) ≤
      2 * m := by
  have hI := PivotCountParameters.integrable_bareIncomparableAnchorCount (n := n) b A B
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x ↦ Nat.cast_nonneg (Nat.card (IncomparableEligibleAnchorMarks b A B x)))
    hI.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_natCast]
  have hfin : (2 : ℝ≥0∞) * ENNReal.ofReal m ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hh := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm, ENNReal.toReal_ofNat] at hh
theorem isLittleO_incomparableMeanProductMass [LPHypA] (b A B κ : ℝ) (K L : ℕ → ℕ)
    (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    (fun n : ℕ ↦ ∫ x, (PivotCountParameters.mk b A B (K n) (L n)).incomparableMeanProductMass x
      ∂continuousScoreLaw n) =o[atTop] (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2) := by
  let C := meanUpperConstant * twoForwardWindowConstant b A
  let a := Real.exp (2 * κ) * (κ + 1)
  let D := 2 * a ^ 2
  have hC : 0 ≤ C := by unfold C meanUpperConstant twoForwardWindowConstant; positivity
  have ha : 0 ≤ a := by unfold a; positivity
  have hD : 0 ≤ D := by unfold D; positivity
  refine isLittleO_of_eventually_nonneg_le_pivotMomentEnvelope
    (D := D * (C + 1)) ?_
  filter_upwards [eventually_localPivotConditionalMean_le_ceiling_ae K L hB hκ hK hL
    hsmallLabel hsmallCompat, eventually_lintegral_card_incomparableEligibleAnchorMarks_le hb hA,
    eventually_pivotMomentEnvelope_le (C := C) hD, hK, eventually_ge_atTop (1 : ℕ)]
    with n hmean hbare henvelope hcap hn
  let q := PivotCountParameters.mk b A B (K n) (L n)
  let c := Real.exp (2 * κ) * (↑(K n + 1) : ℝ)
  let m := C * Real.sqrt n * Real.log n + (n : ℝ) ^ (-3 : ℝ)
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn'
  have hc : 0 ≤ c := by unfold c; positivity
  have hm : 0 ≤ m := by unfold m; positivity
  have hc' : c ≤ a * Real.sqrt n := by
    unfold c a
    rw [mul_assoc, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add hcap.2 hs) (by positivity)
  have hsq : c ^ 2 ≤ a ^ 2 * (n : ℝ) * Real.sqrt n := by
    calc
      c ^ 2 ≤ (a * Real.sqrt n) ^ 2 := pow_le_pow_left₀ hc hc' _
      _ = a ^ 2 * (n : ℝ) := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hs
  refine ⟨q.integral_incomparableMeanProductMass_nonneg, ?_⟩
  calc
    _ ≤ c ^ 2 * ∫ x, (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ)
        ∂continuousScoreLaw n :=
      q.integral_incomparableMeanProductMass_le hc fun i ↦ hmean i.1 i.2 b A
    _ ≤ c ^ 2 * (2 * m) :=
      mul_le_mul_of_nonneg_left (integral_bareIncomparableAnchorCount_le hm (hbare B)) (sq_nonneg _)
    _ ≤ (a ^ 2 * (n : ℝ) * Real.sqrt n) * (2 * m) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = D * (n : ℝ) * Real.sqrt n * m := by unfold D; ring
    _ ≤ _ := henvelope
namespace PivotCountParameters
end PivotCountParameters
end DiagLP
end

noncomputable section
open MeasureTheory Filter DiagLP Asymptotics
open scoped Topology DiagLP
private def params (b A B κ : ℝ) (n : ℕ) : PivotCountParameters :=
  ⟨b,A,B,pivotDecorationSupportCap κ n,logarithmicCycleCutoff n⟩

private def admissible (b A B κ : ℝ) : Prop :=
  0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ 0 < B ∧ 0 < κ ∧ κ < b ∧
    24*κ^2/2 + (B+1)*κ ≤ 1/4 ∧
    Real.exp (κ*(2*(1+B))) * (2*κ*(B/(1/128))) ≤ 3/32

private theorem diag_estimate [LPHypA] [LPHypB] : ∀ b A B κ : ℝ, admissible b A B κ →
  (fun n : ℕ => pivotRawDiagonalMass (params b A B κ n) n +
    ∫ x, (params b A B κ n).incomparableMeanProductMass x ∂continuousScoreLaw n) =o[atTop]
      (fun n : ℕ => ((n:ℝ)*Real.log n)^2) := by
  intro b A B κ hq
  obtain ⟨hb, -, hA, hB, hκ, -, hlabel, hcompat⟩ := hq
  have hK : ∀ᶠ n : ℕ in atTop, 2 ≤ pivotDecorationSupportCap κ n ∧
      (pivotDecorationSupportCap κ n : ℝ) ≤ κ * Real.sqrt (n : ℝ) :=
    (eventually_pivotDecorationSupportCap_bounds hκ).mono fun _ h => ⟨h.1, h.2.1⟩
  exact (isLittleO_pivotRawDiagonalMass b A B κ _ _ hB.le hκ.le hK
      tendsto_logarithmicCycleCutoff hlabel hcompat).add
    (isLittleO_incomparableMeanProductMass b A B κ _ _ hb (by linarith) hB.le hκ.le hK
      tendsto_logarithmicCycleCutoff hlabel hcompat)
end


noncomputable section
namespace OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H2_R1
open MeasureTheory Filter DiagLP Asymptotics StableMarriage
open scoped Topology ENNReal DiagLP

/-- Cowgill's first-moment bound for anchors with incomparable eligible marks. -/
def H1 : Prop := ∀ {b A : ℝ}, 0 < b → 0 ≤ A →
  ∀ᶠ n : ℕ in atTop, ∀ B : ℝ,
    (∫⁻ x, (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ≥0∞)
      ∂continuousScoreLaw n) ≤
      2 * ENNReal.ofReal (meanUpperConstant * twoForwardWindowConstant b A * Real.sqrt n * Real.log n +
        (n : ℝ) ^ (-3 : ℝ))

/-- Cowgill's first-moment bound for the singleton anchor count. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop,
    (∫⁻ p, profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
      ∂(uniformProfile n).toMeasure) ≤
      ENNReal.ofReal ((singletonMomentScale * (108 + 48 * Real.exp 4)) *
        Real.sqrt n * Real.log n + (n : ℝ) ^ (-3 : ℝ))

theorem main : H1 → H2 → OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1.H2 := by
  intro h1 h2
  haveI : LPHypA := ⟨h1⟩
  haveI : LPHypB := ⟨h2⟩
  exact diag_estimate

end OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H2_R1
end
