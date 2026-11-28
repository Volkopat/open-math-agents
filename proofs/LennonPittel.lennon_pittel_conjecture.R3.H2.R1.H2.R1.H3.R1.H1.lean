import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H3_R1
import Mathlib

/-! Port of part of the Lennon-Pittel lower-tail proof by Bo Cowgill,
https://github.com/bocowgill/lennon-pittel at commit cf950d0596591bba912b1568aa394f99986f8191,
Copyright 2026 Bo Cowgill, used under the Apache License 2.0.
Changes: modules flattened into one file, comments removed, declarations not needed here dropped,
names adapted to the pinned Mathlib, the marked model renamed and tied to the parent reduction's
definitions (after moon-4's port of the same model for the parent step).
This step is the source theorem sum_residualPairMass_le_regularOrientation. -/


-- IidScoreRanks
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace StepC
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
end StepC
end

-- MarkedCounting
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepC
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype A] [Nonempty A]
private noncomputable def uniformMarkLaw (A : Type*) [MeasurableSpace A] [Fintype A] [Nonempty A] :
    Measure A :=
  (PMF.uniformOfFintype A).toMeasure
private instance uniformMarkLaw_isProbabilityMeasure : IsProbabilityMeasure (uniformMarkLaw A) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype A).toMeasure)
private noncomputable def markedLaw (P : Measure Ω) (E : Set (Ω × A)) : Measure (Ω × A) :=
  ProbabilityTheory.cond (P.prod (uniformMarkLaw A)) E
theorem markedLaw_isProbabilityMeasure (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0) :
    IsProbabilityMeasure (markedLaw P E) :=
  ProbabilityTheory.cond_isProbabilityMeasure hpos
variable [MeasurableSingletonClass A]
section StableMarriage
open StableMarriage
scoped instance matchingMeasurableSpace (n : ℕ) : MeasurableSpace (Matching n) := ⊤
scoped instance matchingDiscreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (Matching n) :=
  ⟨fun _ ↦ trivial⟩
scoped instance profileDiscreteMeasurableSpace (n : ℕ) : DiscreteMeasurableSpace (Profile n) :=
  ⟨fun _ ↦ trivial⟩
end StableMarriage
end StepC
end

-- ScoreRanks
section
open Function MeasureTheory Set
namespace StepC
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
end StepC
end

-- ContinuousScoreBridge
section
open scoped BigOperators ENNReal StepC
open MeasureTheory Set
namespace StepC
private noncomputable def unitScoreLaw : Measure ℝ :=
  volume.restrict (Icc 0 1)
private instance : IsProbabilityMeasure unitScoreLaw :=
  ⟨by simp [unitScoreLaw, Real.volume_Icc]⟩
private instance : NullSingletonClass unitScoreLaw :=
  Measure.restrict.instNullSingletonClass _
private noncomputable def continuousScoreLaw (n : ℕ) : Measure (ScoreProfile n) :=
  Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw
private instance (n : ℕ) : IsProbabilityMeasure (continuousScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n ⊕ Fin n ↦
    Measure.pi fun _ : Fin n ↦ unitScoreLaw))
theorem ae_injective_rows (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r, Function.Injective (x r) :=
  ae_all_iff.2 fun _ ↦ Measure.tendsto_eval_ae_ae.eventually (ae_injective_iid unitScoreLaw n)
end StepC
end

-- CoexposureGoodScores
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal StepC
namespace StepC
variable {n : ℕ}
private def maleSpouseScore (x : ScoreProfile n) (μ : Matching n) (i : Fin n) : ℝ :=
  x (.inl i) (μ i)
private def femaleSpouseScore (x : ScoreProfile n) (μ : Matching n) (j : Fin n) : ℝ :=
  x (.inr j) (μ.symm j)
private def femaleSpouseTotal (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ j, femaleSpouseScore x μ j
private theorem measurable_scoreCoordinate (r : Fin n ⊕ Fin n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ x r i) :=
  (measurable_pi_apply i).comp (measurable_pi_apply r)
theorem measurable_maleSpouseScore (μ : Matching n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ maleSpouseScore x μ i) :=
  measurable_scoreCoordinate (.inl i) (μ i)
theorem measurable_femaleSpouseScore (μ : Matching n) (j : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ femaleSpouseScore x μ j) :=
  measurable_scoreCoordinate (.inr j) (μ.symm j)
theorem measurable_femaleSpouseTotal (μ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ femaleSpouseTotal x μ) :=
  Finset.measurable_sum _ (fun j _ ↦ measurable_femaleSpouseScore μ j)
end StepC
end

-- CoexposureScoreEstimates
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepC
private def scoreSimplex (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s}
theorem measurableSet_scoreSimplex (n : ℕ) (s : ℝ) :
    MeasurableSet (scoreSimplex n s) := by
  unfold scoreSimplex
  rw [ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i) measurable_const)
theorem volume_scoreSimplex (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    volume (scoreSimplex n s) = ENNReal.ofReal (s ^ n / (n.factorial : ℝ)) := by
  induction n generalizing s with
  | zero =>
    simp [scoreSimplex, hs, volume_pi]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
    let S : Set (ℝ × (Fin n → ℝ)) :=
      {a | 0 ≤ a.1 ∧ a.2 ∈ scoreSimplex n (s - a.1)}
    have heq : e ⁻¹' S = scoreSimplex (n + 1) s := by
      ext y
      simp only [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        Fin.removeNth, Fin.succAbove_zero, Set.mem_preimage, S, scoreSimplex, mem_ofPred_eq,
        Fin.forall_fin_succ, Fin.sum_univ_succ]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2.1⟩, by linarith [h.2.2]⟩,
        fun h ↦ ⟨h.1.1, h.1.2, by linarith [h.2]⟩⟩
    have hS : MeasurableSet S :=
      e.measurableSet_preimage.mp (heq.symm ▸ measurableSet_scoreSimplex _ _)
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piFinSuccAbove _ _
    rw [← heq, he.measure_preimage_emb e.measurableEmbedding]
    change ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) S = _
    rw [Measure.prod_apply hS]
    let f (t : ℝ) : ℝ := (s - t) ^ n / (n.factorial : ℝ)
    have hslice (t : ℝ) :
        volume (Prod.mk t ⁻¹' S) = (Icc 0 s).indicator (fun t ↦ ENNReal.ofReal (f t)) t := by
      by_cases ht : t ∈ Icc 0 s
      · rw [indicator_of_mem ht, ← ih (sub_nonneg.mpr ht.2)]
        congr 1
        ext y
        change (0 ≤ t ∧ y ∈ scoreSimplex n (s - t)) ↔ y ∈ scoreSimplex n (s - t)
        exact and_iff_right ht.1
      · rw [indicator_of_notMem ht]
        have hempty : Prod.mk t ⁻¹' S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          change 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s - t at hy
          have hsum : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ ↦ hy.2.1 i
          exact ht ⟨hy.1, by linarith [hy.2.2]⟩
        rw [hempty, measure_empty]
    rw [lintegral_congr hslice, lintegral_indicator measurableSet_Icc]
    have hfi : IntegrableOn f (Icc 0 s) := (by fun_prop : Continuous f).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hfi
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ by
        dsimp only [f]
        exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) (Nat.cast_nonneg _))]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
    congr 1
    dsimp only [f]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ n) s, sub_self,
      sub_zero, integral_pow, zero_pow (by omega : n + 1 ≠ 0), sub_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_succ]
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]
end StepC
end

-- PittelSimplexRadial
section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace StepC
private noncomputable def spouseAngle {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i / (∑ j, x j)
theorem measurable_spouseAngle (n : ℕ) : Measurable (@spouseAngle n) :=
  measurable_pi_iff.2 fun i ↦ (measurable_pi_apply i).div
    (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)
private noncomputable def spouseAngularLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (n.factorial : ℝ≥0∞) • Measure.map spouseAngle (volume.restrict (scoreSimplex n 1))
theorem isProbabilityMeasure_spouseAngularLaw (n : ℕ) :
    IsProbabilityMeasure (spouseAngularLaw n) := by
  refine ⟨?_⟩
  rw [spouseAngularLaw, Measure.smul_apply, Measure.map_apply (measurable_spouseAngle n)
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
    volume_scoreSimplex n zero_le_one]
  have hf : (n.factorial : ℝ≥0∞) ≠ 0 := by positivity
  rw [one_pow, one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast,
    smul_eq_mul, ENNReal.mul_inv_cancel hf (by simp)]
private instance (n : ℕ) : IsProbabilityMeasure (spouseAngularLaw n) :=
  isProbabilityMeasure_spouseAngularLaw n
private noncomputable def spouseRadialLaw (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun s ↦ ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ)))
private instance (n : ℕ) : SigmaFinite (spouseRadialLaw n) := by
  unfold spouseRadialLaw
  infer_instance
theorem ae_spouseRadialLaw_pos (n : ℕ) :
    ∀ᵐ s ∂(spouseRadialLaw n), 0 < s := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
private theorem measurable_spouseTotal (n : ℕ) :
    Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
private theorem measurableSet_spouseOrthant (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)
theorem ae_spouseAngularLaw {n : ℕ} (hn : 0 < n) :
    ∀ᵐ w ∂(spouseAngularLaw n), (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 := by
  have hs0 : volume (scoreSimplex n 0) = 0 := by
    rw [volume_scoreSimplex n le_rfl, zero_pow hn.ne', zero_div, ENNReal.ofReal_zero]
  have hu := ae_restrict_mem (μ := (volume : Measure (Fin n → ℝ)))
    (measurableSet_scoreSimplex n 1)
  have hz : ∀ᵐ x ∂((volume : Measure (Fin n → ℝ)).restrict (scoreSimplex n 1)),
      x ∉ scoreSimplex n 0 := by
    rw [ae_iff]
    change (volume.restrict (scoreSimplex n 1)) {x | ¬ x ∉ scoreSimplex n 0} = 0
    simp only [not_not, ofPred_mem_eq]
    rw [Measure.restrict_apply (measurableSet_scoreSimplex n 0)]
    exact le_antisymm ((measure_mono inter_subset_left).trans_eq hs0) zero_le
  rw [spouseAngularLaw]
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_spouseAngle n).aemeasurable
    (show MeasurableSet {w : Fin n → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} from
      (measurableSet_spouseOrthant n).inter
        (measurableSet_eq_fun (measurable_spouseTotal n) measurable_const))]
  · filter_upwards [hu, hz] with x hx hx0
    have hsum : 0 < ∑ i, x i := lt_of_not_ge fun h ↦ hx0 ⟨hx.1, h⟩
    exact ⟨fun i ↦ div_nonneg (hx.1 i) hsum.le, by
      simp only [spouseAngle, ← Finset.sum_div, div_self hsum.ne']⟩
theorem volume_preimage_spouseScale (n : ℕ) {c : ℝ} (hc : 0 < c)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    volume ((fun (x : Fin n → ℝ) i ↦ c⁻¹ * x i) ⁻¹' s) =
      ENNReal.ofReal (c ^ n) * volume s := by
  let M := Matrix.diagonal (fun _ : Fin n ↦ c⁻¹)
  have hdet : Matrix.det M = (c⁻¹) ^ n := by simp [M]
  have hm : Matrix.det M ≠ 0 := by rw [hdet]; positivity
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hm
  have heq : ⇑(Matrix.toLin' M) = fun x i ↦ c⁻¹ * x i := by
    funext x i
    simp [M, Matrix.diagonal_toLin', LinearMap.smul_apply]
  rw [heq, hdet, ← inv_pow, inv_inv, abs_of_nonneg (by positivity)] at h
  rw [← smul_eq_mul, ← Measure.smul_apply, ← h, Measure.map_apply (by fun_prop) hs]
theorem spouseRadialLaw_Iic {n : ℕ} (hn : 0 < n) (u : ℝ) :
    spouseRadialLaw n (Iic u) = ENNReal.ofReal ((max u 0) ^ n / (n.factorial : ℝ)) := by
  rw [spouseRadialLaw, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have heq : Iic u ∩ Ioi (0 : ℝ) = Ioc 0 u := by ext; simp [and_comm]
  rw [heq]
  by_cases hu : 0 < u
  · rw [max_eq_left hu.le]
    let f : ℝ → ℝ := fun s ↦ s ^ (n - 1) / ((n - 1).factorial : ℝ)
    have hf : Continuous f := by fun_prop
    change (∫⁻ s in Ioc 0 u, ENNReal.ofReal (f s)) = _
    rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
    · rw [← intervalIntegral.integral_of_le hu.le]
      congr 1
      unfold f
      have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
      rw [intervalIntegral.integral_div, integral_pow, hpred, zero_pow hn.ne', sub_zero]
      have hfac : n.factorial = n * (n - 1).factorial := by
        nth_rw 1 [← hpred]
        rw [Nat.factorial_succ, hpred]
      rw [hfac, Nat.cast_mul, div_div]
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hpred
      rw [hcast]
    · exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs ↦ by
        exact div_nonneg (pow_nonneg hs.1.le _) (Nat.cast_nonneg _)
  · have hu' : u ≤ 0 := le_of_not_gt hu
    simp [Ioc_eq_empty_of_le hu', max_eq_right hu', zero_pow hn.ne']
private def angularSector (n : ℕ) (u : ℝ) (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  scoreSimplex n u ∩ spouseAngle ⁻¹' t
private theorem measurableSet_angularSector {n : ℕ} (u : ℝ) {t : Set (Fin n → ℝ)}
    (ht : MeasurableSet t) : MeasurableSet (angularSector n u t) :=
  (measurableSet_scoreSimplex n u).inter (ht.preimage (measurable_spouseAngle n))
private theorem spouseAngle_scale {n : ℕ} (x : Fin n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    spouseAngle (fun i ↦ c * x i) = spouseAngle x := by
  funext i
  simp only [spouseAngle, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc
private theorem volume_angularSector {n : ℕ} (u : ℝ) (hu : 0 < u)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    volume (angularSector n u t) =
      ENNReal.ofReal (u ^ n) * volume (angularSector n 1 t) := by
  rw [← volume_preimage_spouseScale n hu (measurableSet_angularSector 1 ht)]
  congr 1
  ext x
  simp only [angularSector, mem_inter_iff, mem_preimage,
    spouseAngle_scale x (inv_ne_zero hu.ne')]
  have hmul : ∀ z : ℝ, u⁻¹ * z ≤ 1 ↔ z ≤ u := fun z ↦ by
    rw [inv_mul_eq_div, div_le_iff₀ hu, one_mul]
  simp only [scoreSimplex, mem_ofPred_eq, ← Finset.mul_sum, hmul]
  have hsign : ∀ z : ℝ, 0 ≤ u⁻¹ * z ↔ 0 ≤ z := fun z ↦
    (mul_nonneg_iff_of_pos_left (inv_pos.mpr hu))
  simp only [hsign]
private theorem spouseAngularLaw_apply {n : ℕ} {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    spouseAngularLaw n t = (n.factorial : ℝ≥0∞) * volume (angularSector n 1 t) := by
  rw [spouseAngularLaw, Measure.smul_apply, Measure.map_apply (measurable_spouseAngle n) ht,
    Measure.restrict_apply (ht.preimage (measurable_spouseAngle n))]
  simp only [smul_eq_mul, angularSector, inter_comm]
private theorem volume_angularSector_eq_mul {n : ℕ} (hn : 0 < n) (u : ℝ)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    volume (angularSector n u t) = spouseRadialLaw n (Iic u) * spouseAngularLaw n t := by
  rw [spouseRadialLaw_Iic hn, spouseAngularLaw_apply ht]
  by_cases hu : 0 < u
  · rw [max_eq_left hu.le, volume_angularSector u hu ht, ← mul_assoc]
    congr 1
    have hnR' : (0 : ℝ) < n.factorial := by positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      div_mul_cancel₀ _ hnR'.ne']
  · have hu' : u ≤ 0 := le_of_not_gt hu
    have hsub : angularSector n u t ⊆ scoreSimplex n 0 :=
      fun _ hx ↦ ⟨hx.1.1, hx.1.2.trans hu'⟩
    have h0 : volume (scoreSimplex n 0) = 0 := by
      rw [volume_scoreSimplex n le_rfl, zero_pow hn.ne', zero_div, ENNReal.ofReal_zero]
    simp only [max_eq_right hu', zero_pow hn.ne', zero_div, ENNReal.ofReal_zero, zero_mul]
    exact le_antisymm ((measure_mono hsub).trans_eq h0) zero_le
private def angularRay {n : ℕ} (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ x i} ∩ spouseAngle ⁻¹' t
private theorem measure_angularRay_radius {n : ℕ} (hn : 0 < n)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i) (volume.restrict (angularRay t)) =
      spouseAngularLaw n t • spouseRadialLaw n := by
  let μ := Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i) (volume.restrict (angularRay t))
  let ν := spouseAngularLaw n t • spouseRadialLaw n
  have hμ (u : ℝ) : μ (Iic u) = volume (angularSector n u t) := by
    change (Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i)
      (volume.restrict (angularRay t))) (Iic u) = _
    rw [Measure.map_apply (measurable_spouseTotal n) measurableSet_Iic,
      Measure.restrict_apply (measurableSet_Iic.preimage (measurable_spouseTotal n))]
    congr 1
    ext x
    simp only [angularRay, angularSector, scoreSimplex, mem_inter_iff, mem_preimage,
      mem_Iic, mem_ofPred_eq]
    tauto
  have hcdf (u : ℝ) : μ (Iic u) = ν (Iic u) := by
    change μ (Iic u) = (spouseAngularLaw n t • spouseRadialLaw n) (Iic u)
    rw [hμ, volume_angularSector_eq_mul hn u ht, Measure.smul_apply, smul_eq_mul, mul_comm]
  have hfin (u : ℝ) : μ (Iic u) ≠ ∞ := by
    rw [hμ]
    exact ne_top_of_le_ne_top (by rw [volume_scoreSimplex n (le_max_right u 0)]; simp)
      (measure_mono fun x hx ↦ ⟨hx.1.1, hx.1.2.trans (le_max_left u 0)⟩ :
        volume (angularSector n u t) ≤ volume (scoreSimplex n (max u 0)))
  apply Measure.ext_of_Ioc' μ ν
  · intro a b _
    exact ne_top_of_le_ne_top (hfin b) (measure_mono fun _ hx ↦ hx.2)
  · intro a b hab
    have hν (u : ℝ) : ν (Iic u) ≠ ∞ := hcdf u ▸ hfin u
    rw [← show Iic b \ Iic a = Ioc a b by ext x; simp [and_comm],
      measure_sdiff (Iic_subset_Iic.mpr hab.le)
      measurableSet_Iic.nullMeasurableSet (hfin a),
      measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet (hν a),
      hcdf a, hcdf b]
private theorem measure_map_spouseRadialAngular {n : ℕ} (hn : 0 < n) :
    Measure.map (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x))
      (volume.restrict {x : Fin n → ℝ | ∀ i, 0 ≤ x i}) =
      (spouseRadialLaw n).prod (spouseAngularLaw n) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  have hmeas : Measurable (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x)) :=
    (measurable_spouseTotal n).prodMk (measurable_spouseAngle n)
  rw [Measure.map_apply hmeas (hs.prod ht), Measure.restrict_apply ((hs.prod ht).preimage hmeas)]
  rw [← mul_comm, ← smul_eq_mul, ← Measure.smul_apply, ← measure_angularRay_radius hn ht,
    Measure.map_apply (measurable_spouseTotal n) hs,
    Measure.restrict_apply (hs.preimage (measurable_spouseTotal n))]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq, angularRay]
  tauto
theorem lintegral_spouseRadialAngular {n : ℕ} (hn : 0 < n)
    {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂(volume.restrict {x | ∀ i, 0 ≤ x i})) =
      ∫⁻ s, ∫⁻ w, f (fun i ↦ s * w i) ∂(spouseAngularLaw n) ∂(spouseRadialLaw n) := by
  let decode : ℝ × (Fin n → ℝ) → (Fin n → ℝ) := fun p i ↦ p.1 * p.2 i
  have hdecode : Measurable decode := by unfold decode; fun_prop
  have hpair : Measurable (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x)) :=
    (measurable_spouseTotal n).prodMk (measurable_spouseAngle n)
  rw [← lintegral_prod (fun p ↦ f (decode p)) (hf.comp hdecode).aemeasurable,
    ← measure_map_spouseRadialAngular hn]
  change _ = ∫⁻ z, (f ∘ decode) z ∂(Measure.map (fun x : Fin n → ℝ ↦
    (∑ i, x i, spouseAngle x)) (volume.restrict {x | ∀ i, 0 ≤ x i}))
  rw [lintegral_map (hf.comp hdecode) hpair]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure (Fin n → ℝ)))
    (measurableSet_spouseOrthant n)] with x hx
  congr 1
  funext i
  change x i = (∑ j, x j) * (x i / ∑ j, x j)
  by_cases h : (∑ j, x j) = 0
  · have hle : x i ≤ ∑ j, x j :=
      Finset.single_le_sum (fun j _ ↦ hx j) (Finset.mem_univ i)
    rw [h, zero_mul]
    exact le_antisymm (h ▸ hle) (hx i)
  · field_simp
end StepC
end

-- CoexposureScoreRow
section
open Set
open scoped BigOperators
namespace StepC
variable {ι : Type*}
private noncomputable def scoreRowKernel (J : Finset ι) (y : ι → ℝ) (x : ℝ) : ℝ :=
  ∏ j ∈ J, (1 - x * y j)
private noncomputable def scoreRowMass (J : Finset ι) (y : ι → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, scoreRowKernel J y x
theorem continuous_scoreRowKernel (J : Finset ι) (y : ι → ℝ) :
    Continuous (scoreRowKernel J y) := by
  unfold scoreRowKernel
  fun_prop
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
theorem rowNonblockingLaw_apply_univ {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    rowNonblockingLaw x y univ = ENNReal.ofReal (1 - x * y) := by
  rw [← rowNonblockingLaw_apply_avoiding le_rfl hx hy]
  unfold rowNonblockingLaw
  rw [Measure.restrict_apply_univ,
    Measure.restrict_apply (measurableSet_Iio.prod measurableSet_Iio).compl, inter_self]
end SuccessorMass
end StepC
end

-- ExposedRotations
section
open StableMarriage
namespace StepC
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
theorem IsExposedRotation.manRank_lt_eliminate_of_moved (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : ρ m ≠ m) :
    p.manRank m (μ m) < p.manRank m (eliminateRotation μ ρ m) :=
  (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m hm)).1
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
end StepC
end

-- CoexposureScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
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
private abbrev OffDiagonalScoreRows (n : ℕ) := (i : Fin n) → {j : Fin n // i ≠ j} → ℝ × ℝ
private def offDiagonalRowsEquiv (n : ℕ) : OffDiagonalScorePairs n ≃ᵐ OffDiagonalScoreRows n where
  toFun v i j := v ⟨(i,j), j.property⟩
  invFun v q := v q.val.1 ⟨q.val.2, q.property⟩
  left_inv v := by
    funext q
    cases q
    rfl
  right_inv _ := rfl
  measurable_toFun := measurable_pi_iff.2 fun _ ↦
    measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 fun q ↦
    (measurable_pi_apply (⟨q.val.2, q.property⟩ : {j : Fin n // q.val.1 ≠ j})).comp
      (measurable_pi_apply q.val.1)
private noncomputable def stableScoreRowLaw {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) :
    Measure ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  Measure.pi fun j ↦ unitScorePairLaw.restrict
    (nonblockingScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j.val).2)
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
private def scoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (j : {j : Fin n // i ≠ j}) : Set ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  {r | (diagonalPairAt d i).1 < (r j).1 ∧ (r j).2 < (diagonalPairAt d j.val).2 ∧
    ∀ k : {k : {k : Fin n // i ≠ k} // k ≠ j},
      ¬ ((r k.val).1 < (r j).1 ∧ (r k.val).2 < (diagonalPairAt d k.val.val).2)}
theorem scoreRowSuccessorEvent_of_isSuccessor {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (hs : IsScoreStable x μ) (ht : ∀ row, Function.Injective (x row))
    (i : Fin n) (j : {j : Fin n // i ≠ j}) (hj : IsSuccessor (profileOfScores x) μ i (μ j.val)) :
    offDiagonalRowsEquiv n (splitScorePairs μ x).2 i ∈
      scoreRowSuccessorEvent (splitScorePairs μ x).1 i j := by
  have hcell (a : {a : Fin n // i ≠ a}) :
      offDiagonalRowsEquiv n (splitScorePairs μ x).2 i a =
        (x (.inl i) (μ a.val), x (.inr (μ a.val)) i) := by
    simpa [offDiagonalRowsEquiv] using
      splitScorePairs_offDiagonal_apply μ x ⟨(i,a.val),a.property⟩
  simp only [scoreRowSuccessorEvent, Set.mem_ofPred_eq, hcell, diagonalPairAt_splitScorePairs]
  have hman (w w' : Fin n) : (profileOfScores x).manRank i w < (profileOfScores x).manRank i w'
      ↔ x (.inl i) w < x (.inl i) w' :=
    rankPermutation_lt_iff (ht (.inl i)) w w'
  have hwoman (w m m' : Fin n) :
      (profileOfScores x).womanRank w m < (profileOfScores x).womanRank w m'
        ↔ x (.inr w) m < x (.inr w) m' :=
    rankPermutation_lt_iff (ht (.inr w)) m m'
  refine ⟨(hman _ _).1 (IsSuccessor.eligible hj).1, ?_, ?_⟩
  · simpa only [Equiv.symm_apply_apply] using (hwoman _ _ _).1 (IsSuccessor.eligible hj).2
  · intro k hk
    have hwk : x (.inr (μ k.val.val)) i <
        x (.inr (μ k.val.val)) (μ.symm (μ k.val.val)) := by
      simpa only [Equiv.symm_apply_apply] using hk.2
    have hmle : x (.inl i) (μ i) ≤ x (.inl i) (μ k.val.val) :=
      le_of_not_gt fun h ↦ hs i (μ k.val.val) ⟨μ.injective.ne k.val.property, h, hwk⟩
    have hmne := (ht (.inl i)).ne (μ.injective.ne k.val.property)
    have hel : IsEligibleSuccessor (profileOfScores x) μ i (μ k.val.val) :=
      ⟨(hman _ _).2 (lt_of_le_of_ne hmle hmne), (hwoman _ _ _).2 hwk⟩
    exact (not_lt_of_ge ((IsSuccessor.min_rank hj) _ hel)) ((hman _ _).2 hk.1)
theorem measurableSet_scoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    MeasurableSet (scoreRowSuccessorEvent d i j) :=
  (measurableSet_scoreSuccessorPairEvent (diagonalPairAt d i).1 (diagonalPairAt d j.val).2
    (fun k : {k : {k : Fin n // i ≠ k} // k ≠ j} ↦ (diagonalPairAt d k.val.val).2)).preimage
    (measurePreserving_rowTargetAndCompetitors
      (fun _ : {k : Fin n // i ≠ k} ↦ unitScorePairLaw) j).measurable
end StepC
end

-- CoexposureSpouseMarginal
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepC
private def femaleSpouseByHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) : Fin n → ℝ :=
  fun j ↦ femaleSpouseScore x μ (μ j)
theorem femaleSpouseTotal_eq_sum_byHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) :
    femaleSpouseTotal x μ = ∑ j, femaleSpouseByHusband μ x j :=
  (Equiv.sum_comp μ (femaleSpouseScore x μ)).symm
end StepC
end

-- FiniteProductDensity
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepC
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
theorem pi_smul_coordinates (ν : ∀ i, Measure (Ω i)) [∀ i, IsFiniteMeasure (ν i)]
    (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i ↦ c i • ν i) = (∏ i, c i) • Measure.pi ν := by
  let (i : ι) : IsFiniteMeasure (c i • ν i) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hc i)) (measure_lt_top _ _)⟩
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]
end StepC
end

-- PivotSpouseProductLower
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepC
private def maleSpouseTotal {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ i, maleSpouseScore x μ i
end StepC
end

-- PivotForwardRevealCell
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepC
private def forwardEligibleScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  Ioi x ×ˢ Iio y
private abbrev OffDiagonalCellIndex (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2}
private abbrev ForwardActiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q = true}
private abbrev ForwardInactiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q ≠ true}
private def forwardScoreMaskRevealAndInactive {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (z : OffDiagonalScorePairs n) :
    (ForwardActiveCellIndex flag → ℝ) × (ForwardInactiveCellIndex flag → ℝ × ℝ) :=
  (fun q ↦ (z q.val).1, fun q ↦ z q.val)
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
end StepC
end

-- ReverseSuccessorRotation
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
private def swapProfile (p : Profile n) : Profile n :=
  ⟨p.womanRank, p.manRank⟩
@[simp] theorem swapProfile_swapProfile (p : Profile n) : swapProfile (swapProfile p) = p := rfl
theorem isStable_swapProfile_iff : IsStable (swapProfile p) μ.symm ↔ IsStable p μ := by
  constructor
  · intro h m w hb
    exact h w m
      ⟨fun he ↦ hb.1 ((congrArg μ he).symm.trans (μ.apply_symm_apply w)), hb.2.2, hb.2.1⟩
  · intro h w m hb
    refine h m w ⟨fun he ↦ hb.1 ?_, hb.2.2, hb.2.1⟩
    simpa only [Equiv.symm_apply_apply] using (congrArg μ.symm he).symm
private def reverseRotationCycle (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  μ.symm.trans (ρ.trans μ)
theorem IsExposedRotation.isExposedRotation_swap_eliminate
    (hρ : IsExposedRotation p μ ρ) (hμ : IsStable p μ) :
    IsExposedRotation (swapProfile p) (eliminateRotation μ ρ).symm
      (reverseRotationCycle μ ρ) := by
  refine (IsExposedRotation.mk (?_) (?_))
  · change (μ * ρ * μ⁻¹).IsCycle
    exact (IsExposedRotation.isCycle hρ).conj
  · intro w hw
    obtain ⟨m, rfl⟩ := μ.surjective w
    have hm : ρ m ≠ m := by
      intro he
      apply hw
      simp [reverseRotationCycle, he]
    have hback : ρ (ρ.symm m) ≠ ρ.symm m := by
      intro he
      have he' : m = ρ.symm m := by simpa only [Equiv.apply_symm_apply] using he
      exact hm ((congrArg ρ he').trans (ρ.apply_symm_apply m))
    have hnew : (eliminateRotation μ ρ).symm (reverseRotationCycle μ ρ (μ m)) = m := by
      simp [reverseRotationCycle, eliminateRotation]
    have hcurrent : (eliminateRotation μ ρ).symm (μ m) = ρ.symm m := by
      simp [eliminateRotation]
    refine IsSuccessor.mk ?_ ?_
    · have hprev := (IsSuccessor.eligible ((IsExposedRotation.successor hρ) (ρ.symm m) hback)).2
      have hwlt : p.womanRank (μ m) (ρ.symm m) < p.womanRank (μ m) m := by
        simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using hprev
      simp only [IsEligibleSuccessor, swapProfile, hnew, hcurrent, Equiv.symm_symm,
        eliminateRotation_apply]
      exact ⟨hwlt, (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m hm)).1⟩
    · intro t ht
      simp only [IsEligibleSuccessor, swapProfile, hcurrent, Equiv.symm_symm,
        eliminateRotation_apply] at ht
      change p.womanRank (μ m) ((eliminateRotation μ ρ).symm
        (reverseRotationCycle μ ρ (μ m))) ≤ p.womanRank (μ m) t
      rw [hnew]
      by_contra hbad
      
      have hwbad := lt_of_not_ge hbad
      have hne : μ t ≠ μ m := fun he ↦
        (ne_of_lt hwbad) (congrArg (p.womanRank (μ m)) (μ.injective he))
      have hnot : ¬ p.manRank t (μ m) < p.manRank t (μ t) := fun ht' ↦
        hμ t (μ m) ⟨hne, ht', by simpa only [Equiv.symm_apply_apply] using hwbad⟩
      have hf : IsEligibleSuccessor p μ t (μ m) :=
        ⟨lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank t).injective he)),
          by simpa only [Equiv.symm_apply_apply] using hwbad⟩
      by_cases htfix : ρ t = t
      · exact (not_lt_of_ge hf.1.le) (by simpa only [htfix] using ht.2)
      · exact (not_lt_of_ge ((IsSuccessor.min_rank ((IsExposedRotation.successor hρ) t htfix)) _ hf)) ht.2
end StepC
end

-- FinitePrerequisites
section
namespace StepC
theorem mem_family_of_downward_closed {α : Type*} [Finite α] {F : Set (Set α)}
    (hempty : ∅ ∈ F)
    (hinter : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∩ B ∈ F)
    (hunion : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∪ B ∈ F)
    (hcover : ∀ a : α, ∃ A ∈ F, a ∈ A) {I : Set α}
    (hdown : ∀ ⦃a b : α⦄, (∀ A ∈ F, b ∈ A → a ∈ A) → b ∈ I → a ∈ I) :
    I ∈ F := by
  
  let P (b : α) : Set α := ⋂₀ {A : Set α | A ∈ F ∧ b ∈ A}
  have hInf : InfClosed F := fun _ hA _ hB ↦ hinter hA hB
  have hP (b : α) : P b ∈ F := by
    obtain ⟨A, hA, hbA⟩ := hcover b
    change sInf {A : Set α | A ∈ F ∧ b ∈ A} ∈ F
    exact hInf.sInf_mem_of_nonempty (Set.toFinite _) ⟨A, hA, hbA⟩ fun _ h ↦ h.1
  
  have hEq : I = ⋃ b : I, P b := by
    ext a
    constructor
    · intro ha
      exact Set.mem_iUnion_of_mem ⟨a, ha⟩ (Set.mem_sInter.mpr fun _ h ↦ h.2)
    · intro ha
      obtain ⟨b, hab⟩ := Set.mem_iUnion.mp ha
      exact hdown (fun A hA hb ↦ Set.mem_sInter.mp hab A ⟨hA, hb⟩) b.property
  have hSup : SupClosed F := fun _ hA _ hB ↦ hunion hA hB
  rw [hEq]
  exact hSup.iSup_mem hempty fun b : I ↦ hP b
end StepC
end

-- RotationDiamond
section
open StableMarriage
namespace StepC
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
theorem IsExposedRotation.persist_eliminate (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) :
    IsExposedRotation p (eliminateRotation μ σ) ρ := by
  refine (IsExposedRotation.mk ((IsExposedRotation.isCycle hρ)) (fun m hm ↦ ?_))
  let μ' := eliminateRotation μ σ
  have hold : μ' m = μ m := congrArg μ (hρ.disjoint_moved hσ hne m hm)
  have hnext : μ' (ρ m) = μ (ρ m) :=
    congrArg μ (hρ.disjoint_moved hσ hne (ρ m) (moved_image hm))
  have hs := (IsExposedRotation.successor hρ) m hm
  have helig : IsEligibleSuccessor p μ' m (μ' (ρ m)) := by
    refine ⟨?_, ?_⟩
    · simpa only [hold, hnext] using (IsSuccessor.eligible hs).1
    · rw [Equiv.symm_apply_apply, hnext]
      simpa only [Equiv.symm_apply_apply] using (IsSuccessor.eligible hs).2
  refine (IsSuccessor.mk (helig) (fun w hw ↦ ?_))
  have hman : p.manRank m (μ' m) < p.manRank m w := hw.1
  rw [hold] at hman
  have hbefore : IsEligibleSuccessor p μ m w :=
    ⟨hman, hw.2.trans_le (hσ.womanRank_eliminate_le w)⟩
  change p.manRank m (μ' (ρ m)) ≤ p.manRank m w
  rw [hnext]
  exact (IsSuccessor.min_rank hs) w hbefore
theorem IsExposedRotation.eliminate_comm (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) :
    eliminateRotation (eliminateRotation μ ρ) σ = eliminateRotation (eliminateRotation μ σ) ρ := by
  apply Equiv.ext
  intro m
  simp only [eliminateRotation_apply]
  by_cases hr : ρ m = m
  · by_cases hs : σ m = m
    · simp only [hr, hs]
    · have hfix := hσ.disjoint_moved hρ hne.symm (σ m) (moved_image hs)
      simp only [hr, hfix]
  · have hfix := hρ.disjoint_moved hσ hne m hr
    have hfix' := hρ.disjoint_moved hσ hne (ρ m) (moved_image hr)
    simp only [hfix, hfix']
end StepC
end

-- ManOptimal
section
open StableMarriage
open scoped BigOperators
namespace StepC
variable {n : ℕ}
private def MenWeaklyPrefer (p : Profile n) (μ ν : Matching n) : Prop :=
  ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)
private def IsManOptimal (p : Profile n) (μ : Matching n) : Prop :=
  IsStable p μ ∧ ∀ ν, IsStable p ν → MenWeaklyPrefer p μ ν
private def betterPartner (p : Profile n) (μ ν : Matching n) (m : Fin n) : Fin n :=
  if p.manRank m (μ m) ≤ p.manRank m (ν m) then μ m else ν m
private theorem betterPartner_spec (p : Profile n) (μ ν : Matching n) (m : Fin n) :
    (betterPartner p μ ν m = μ m ∨ betterPartner p μ ν m = ν m) ∧
      p.manRank m (betterPartner p μ ν m) ≤ p.manRank m (μ m) ∧
      p.manRank m (betterPartner p μ ν m) ≤ p.manRank m (ν m) := by
  unfold betterPartner
  split
  · rename_i h
    exact ⟨Or.inl rfl, le_rfl, h⟩
  · rename_i h
    exact ⟨Or.inr rfl, le_of_not_ge h, le_rfl⟩
private theorem woman_prefers_husband {p : Profile n} {μ : Matching n}
    (hμ : IsStable p μ) {m w : Fin n}
    (hm : p.manRank m w < p.manRank m (μ m)) :
    p.womanRank w (μ.symm w) < p.womanRank w m := by
  have hneq : μ m ≠ w := fun h ↦ hm.ne (congrArg (p.manRank m) h.symm)
  have hn : ¬ p.womanRank w m < p.womanRank w (μ.symm w) :=
    fun h ↦ hμ m w ⟨hneq, hm, h⟩
  exact lt_of_le_of_ne (le_of_not_gt hn) fun h ↦
    hneq ((Equiv.symm_apply_eq μ).mp ((p.womanRank w).injective h)).symm
private theorem betterPartner_injective {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    Function.Injective (betterPartner p μ ν) := by
  let f := betterPartner p μ ν
  have hcross (a b : Fin n) (ha : f a = μ a) (hb : f b = ν b) (h : f a = f b) :
      a = b := by
    by_contra hab
    have haw : μ a = f a := ha.symm
    have hbw : ν b = f a := hb.symm.trans h.symm
    have haν : p.manRank a (f a) < p.manRank a (ν a) :=
      lt_of_le_of_ne (betterPartner_spec p μ ν a).2.2 fun e ↦
        hab (ν.injective (((p.manRank a).injective e).symm.trans hbw.symm))
    have hbμ : p.manRank b (f a) < p.manRank b (μ b) :=
      lt_of_le_of_ne (h.symm ▸ (betterPartner_spec p μ ν b).2.1) fun e ↦
        hab (μ.injective (haw.trans ((p.manRank b).injective e)))
    have hμhusband : μ.symm (f a) = a := (Equiv.symm_apply_eq μ).2 ha
    have hνhusband : ν.symm (f a) = b := (Equiv.symm_apply_eq ν).2 hbw.symm
    have hfab : p.womanRank (f a) a < p.womanRank (f a) b :=
      by simpa only [hμhusband] using woman_prefers_husband hμ hbμ
    have hfba : p.womanRank (f a) b < p.womanRank (f a) a :=
      by simpa only [hνhusband] using woman_prefers_husband hν haν
    exact lt_asymm hfab hfba
  intro a b h
  rcases (betterPartner_spec p μ ν a).1 with ha | ha <;>
    rcases (betterPartner_spec p μ ν b).1 with hb | hb
  · exact μ.injective (ha.symm.trans (h.trans hb))
  · exact hcross a b ha hb h
  · exact (hcross b a hb ha h.symm).symm
  · exact ν.injective (ha.symm.trans (h.trans hb))
theorem exists_stable_manRank_min {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      ∀ m, p.manRank m (τ m) = min (p.manRank m (μ m)) (p.manRank m (ν m)) := by
  have hinj := betterPartner_injective hμ hν
  let τ : Matching n := Equiv.ofBijective (betterPartner p μ ν)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hleft : MenWeaklyPrefer p τ μ := fun m ↦ (betterPartner_spec p μ ν m).2.1
  have hright : MenWeaklyPrefer p τ ν := fun m ↦ (betterPartner_spec p μ ν m).2.2
  refine ⟨τ, ?_, fun m ↦ ?_⟩
  · intro m w hb
    have conflict (σ : Matching n) (hσ : IsStable p σ) (hpref : MenWeaklyPrefer p τ σ)
        (hsource : τ (τ.symm w) = σ (τ.symm w)) : False := by
      have hhusband : σ.symm w = τ.symm w :=
        (Equiv.symm_apply_eq σ).2 ((τ.apply_symm_apply w).symm.trans hsource)
      have hm : p.manRank m w < p.manRank m (σ m) := hb.2.1.trans_le (hpref m)
      exact hσ m w ⟨fun he ↦ hm.ne (congrArg (p.manRank m) he.symm), hm,
        hhusband.symm ▸ hb.2.2⟩
    exact ((betterPartner_spec p μ ν (τ.symm w)).1).elim (conflict μ hμ hleft)
      (conflict ν hν hright)
  · have hsource : τ m = μ m ∨ τ m = ν m := (betterPartner_spec p μ ν m).1
    rcases hsource with h | h
    · have hle := hright m
      rw [h] at hle ⊢
      exact (min_eq_left hle).symm
    · have hle := hleft m
      rw [h] at hle ⊢
      exact (min_eq_right hle).symm
private def manOptimal_swapProfile (p : Profile n) : Profile n :=
  ⟨p.womanRank, p.manRank⟩
private theorem isStable_swap {p : Profile n} {μ : Matching n}
    (hμ : IsStable p μ) : IsStable (manOptimal_swapProfile p) μ.symm := by
  intro w m hb
  exact hμ m w ⟨fun h ↦ hb.1 ((Equiv.symm_apply_eq μ).2 h.symm), hb.2.2, hb.2.1⟩
theorem exists_stable_manRank_max {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      ∀ m, p.manRank m (τ m) = max (p.manRank m (μ m)) (p.manRank m (ν m)) := by
  obtain ⟨σ, hσ, hmin⟩ := exists_stable_manRank_min (isStable_swap hμ) (isStable_swap hν)
  let τ := σ.symm
  have hw (w : Fin n) : p.womanRank w (τ.symm w) =
      min (p.womanRank w (μ.symm w)) (p.womanRank w (ν.symm w)) := hmin w
  
  have hworse (δ : Matching n) (hδ : IsStable p δ)
      (hδrank : ∀ w, p.womanRank w (τ.symm w) ≤ p.womanRank w (δ.symm w)) (m : Fin n) :
      p.manRank m (δ m) ≤ p.manRank m (τ m) := by
    by_contra h
    have hh := woman_prefers_husband hδ (lt_of_not_ge h)
    exact (not_lt_of_ge (hδrank (τ m))) (by simpa only [Equiv.symm_apply_apply] using hh)
  refine ⟨τ, isStable_swap hσ, fun m ↦ ?_⟩
  have hchoice : τ m = μ m ∨ τ m = ν m := by
    let w := τ m
    rcases le_total (p.womanRank w (μ.symm w)) (p.womanRank w (ν.symm w)) with h | h
    · have hhusband := (p.womanRank w).injective ((hw w).trans (min_eq_left h))
      exact Or.inl ((Equiv.symm_apply_eq μ).mp (hhusband.symm.trans (τ.symm_apply_apply m)))
    · have hhusband := (p.womanRank w).injective ((hw w).trans (min_eq_right h))
      exact Or.inr ((Equiv.symm_apply_eq ν).mp (hhusband.symm.trans (τ.symm_apply_apply m)))
  rcases hchoice with h | h
  · have hle := hworse ν hν (fun w ↦ (hw w).le.trans (min_le_right _ _)) m
    rw [h] at hle ⊢
    exact (max_eq_left hle).symm
  · have hle := hworse μ hμ (fun w ↦ (hw w).le.trans (min_le_left _ _)) m
    rw [h] at hle ⊢
    exact (max_eq_right hle).symm
end StepC
end

-- RotationCycle
section
namespace StepC
open Function
private theorem periodicPt_of_repeat {α : Type*} {f : α → α} {x : α} {i j : ℕ}
    (hij : i < j) (heq : f^[i] x = f^[j] x) :
    f^[i] x ∈ periodicPts f :=
  mk_mem_periodicPts (Nat.sub_pos_of_lt hij)
    (show f^[j - i] (f^[i] x) = f^[i] x by
      rw [← iterate_add_apply, Nat.sub_add_cancel hij.le, ← heq])
private theorem nonempty_periodicPts {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    (periodicPts f).Nonempty :=
  let x := Classical.choice (inferInstance : Nonempty α)
  have hrepeat : ∃ i j, f^[i] x = f^[j] x ∧ i ≠ j := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  let ⟨i, j, heq, hne⟩ := hrepeat
  (lt_or_gt_of_ne hne).elim
    (fun h ↦ ⟨_, periodicPt_of_repeat h heq⟩)
    (fun h ↦ ⟨_, periodicPt_of_repeat h heq.symm⟩)
theorem exists_cycle_permutation {α : Type*} [Finite α] {s : Set α} [Nonempty s]
    (f : s → s) (hnf : ∀ x, f x ≠ x) :
    ∃ ρ : Equiv.Perm α, ρ.IsCycle ∧
      ∀ a, ρ a ≠ a → ∃ ha : a ∈ s, ρ a = (f ⟨a, ha⟩).1 := by
  classical
  let ⟨a, ha⟩ := nonempty_periodicPts f
  let hbij := bijOn_periodicPts f
  let e : Equiv.Perm (periodicPts f) := Equiv.ofBijective _ hbij.bijective
  let τ : Equiv.Perm s := Equiv.Perm.ofSubtype e
  let σ : Equiv.Perm α := Equiv.Perm.ofSubtype τ
  have hτ (x : s) (hx : x ∈ periodicPts f) : τ x = f x :=
    Equiv.Perm.ofSubtype_apply_of_mem e hx
  have hσ (x : s) (hx : x ∈ periodicPts f) : σ x.1 = (f x).1 :=
    (Equiv.Perm.ofSubtype_apply_coe τ x).trans (congrArg Subtype.val (hτ x hx))
  have hmove : σ a.1 ≠ a.1 := fun h ↦ hnf a (Subtype.ext ((hσ a ha).symm.trans h))
  exact ⟨σ.cycleOf a.1, σ.isCycle_cycleOf hmove, fun x hne ↦
    have hsame : σ.SameCycle a.1 x := Classical.byContradiction fun h ↦
      hne (Equiv.Perm.cycleOf_apply_of_not_sameCycle h)
    have heq := hsame.cycleOf_apply
    have hσne : σ x ≠ x := fun h ↦ hne (heq.trans h)
    have hx : x ∈ s := Classical.byContradiction fun h ↦
      hσne (Equiv.Perm.ofSubtype_apply_of_not_mem τ h)
    have hper : (⟨x, hx⟩ : s) ∈ periodicPts f := Classical.byContradiction fun h ↦
      hσne <| (Equiv.Perm.ofSubtype_apply_of_mem τ hx).trans <|
        congrArg Subtype.val (Equiv.Perm.ofSubtype_apply_of_not_mem e h)
    ⟨hx, heq.trans (hσ ⟨x, hx⟩ hper)⟩⟩
end StepC
end

-- TargetSuccessor
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
private theorem target_partner_eligible (hν : IsStable p ν)
    (hle : ∀ i, p.manRank i (μ i) ≤ p.manRank i (ν i))
    {m : Fin n} (hm : μ m ≠ ν m) : IsEligibleSuccessor p μ m (ν m) :=
  let j := μ.symm (ν m)
  have hjμ : μ j = ν m := μ.apply_symm_apply _
  have hjm : j ≠ m := fun h ↦ hm ((congrArg μ h).symm.trans hjμ)
  have hjν : ν j ≠ ν m := ν.injective.ne hjm
  have hjmove : μ j ≠ ν j := fun h ↦ hjν (h.symm.trans hjμ)
  have hjrank : p.manRank j (μ j) < p.manRank j (ν j) :=
    lt_of_le_of_ne (hle j) ((p.manRank j).injective.ne hjmove)
  have hw : ¬ p.womanRank (ν m) j < p.womanRank (ν m) m := fun h ↦
    hν j (ν m) ⟨hjν, by simpa only [hjμ] using hjrank,
      by simpa only [Equiv.symm_apply_apply] using h⟩
  ⟨lt_of_le_of_ne (hle m) ((p.manRank m).injective.ne hm),
    lt_of_le_of_ne (le_of_not_gt hw) ((p.womanRank (ν m)).injective.ne hjm.symm)⟩
private theorem successor_husband_moves (hν : IsStable p ν) {m w : Fin n}
    (hw : IsEligibleSuccessor p μ m w) (hbound : p.manRank m w ≤ p.manRank m (ν m)) :
    μ (μ.symm w) ≠ ν (μ.symm w) :=
  let j := μ.symm w
  have hjμ : μ j = w := μ.apply_symm_apply w
  have hjm : j ≠ m := fun h ↦
    (ne_of_lt hw.1) (congrArg (p.manRank m) ((congrArg μ h).symm.trans hjμ))
  fun heq ↦
    have hjν : ν j = w := heq.symm.trans hjμ
    have hwm : w ≠ ν m := fun h ↦ hjm (ν.injective (hjν.trans h))
    have hlt : p.manRank m w < p.manRank m (ν m) :=
      lt_of_le_of_ne hbound ((p.manRank m).injective.ne hwm)
    have hjνsymm : ν.symm w = j := by
      simpa only [Equiv.symm_apply_apply] using (congrArg ν.symm hjν).symm
    hν m w ⟨hwm.symm, hlt, by simpa only [hjνsymm] using hw.2⟩
theorem exists_successor_towards_target (_hμ : IsStable p μ) (hν : IsStable p ν)
    (hle : ∀ i, p.manRank i (μ i) ≤ p.manRank i (ν i)) {m : Fin n} (hm : μ m ≠ ν m) :
    ∃ j : Fin n, IsSuccessor p μ m (μ j) ∧ μ j ≠ ν j ∧
      p.manRank m (μ j) ≤ p.manRank m (ν m) := by
  classical
  let candidates := Finset.univ.filter (IsEligibleSuccessor p μ m)
  have htarget : ν m ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, target_partner_eligible hν hle hm⟩
  obtain ⟨w, hw, hmin⟩ := candidates.exists_min_image (p.manRank m) ⟨ν m, htarget⟩
  have heligible : IsEligibleSuccessor p μ m w := (Finset.mem_filter.mp hw).2
  have hsuccessor : IsSuccessor p μ m w :=
    (IsSuccessor.mk (heligible) (fun v hv ↦ hmin v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)))
  have hbound : p.manRank m w ≤ p.manRank m (ν m) := hmin (ν m) htarget
  have hj : μ (μ.symm w) = w := μ.apply_symm_apply w
  exact ⟨μ.symm w, by simpa only [hj] using hsuccessor,
    successor_husband_moves hν heligible hbound,
    by simpa only [hj] using hbound⟩
end StepC
end

-- RotationReachability
section
open scoped BigOperators
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n}
private inductive RotationSequence (p : Profile n) :
    Matching n → List (Equiv.Perm (Fin n)) → Matching n → Prop where
  | nil {μ : Matching n} (hμ : IsStable p μ) : RotationSequence p μ [] μ
  | cons {μ ν : Matching n} {ρ : Equiv.Perm (Fin n)} {rs : List (Equiv.Perm (Fin n))}
      (hμ : IsStable p μ) (hρ : IsExposedRotation p μ ρ)
      (rest : RotationSequence p (eliminateRotation μ ρ) rs ν) :
      RotationSequence p μ (ρ :: rs) ν
private def totalManRank (p : Profile n) (μ : Matching n) : ℕ :=
  ∑ m : Fin n, (p.manRank m (μ m) : ℕ)
private theorem totalManRank_le {μ ν : Matching n}
    (hle : ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)) :
    totalManRank p μ ≤ totalManRank p ν :=
  Finset.sum_le_sum fun m _ ↦ hle m
private theorem totalManRank_lt_eliminate {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (hρ : IsExposedRotation p μ ρ) :
    totalManRank p μ < totalManRank p (eliminateRotation μ ρ) :=
  have hle (m : Fin n) : p.manRank m (μ m) ≤ p.manRank m (eliminateRotation μ ρ m) :=
    if hm : ρ m = m then
      le_of_eq (by simp only [eliminateRotation_apply, hm])
    else (hρ.manRank_lt_eliminate_of_moved hm).le
  let ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
  Finset.sum_lt_sum (fun i _ ↦ hle i)
    ⟨m, Finset.mem_univ m, hρ.manRank_lt_eliminate_of_moved hm⟩
theorem exists_exposedRotation_towards_target {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) (hle : MenWeaklyPrefer p μ ν) (hne : μ ≠ ν) :
    ∃ ρ, IsExposedRotation p μ ρ ∧ MenWeaklyPrefer p (eliminateRotation μ ρ) ν := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, μ m ≠ ν m := by
    simpa only [not_forall] using mt (fun h : ∀ i, μ i = ν i ↦ Equiv.ext h) hne
  let changed : Set (Fin n) := {i | μ i ≠ ν i}
  let : Nonempty changed := ⟨⟨m, hm⟩⟩
  
  choose next hsucc hchanged hbound using fun i : changed ↦
    exists_successor_towards_target hμ hν hle i.property
  let f : changed → changed := fun i ↦ ⟨next i, hchanged i⟩
  have hnf (i : changed) : f i ≠ i := fun h ↦
    have he : next i = i.val := congrArg Subtype.val h
    (lt_irrefl _) (by simpa only [he] using (IsSuccessor.eligible (hsucc i)).1)
  obtain ⟨ρ, hcycle, hedge⟩ := exists_cycle_permutation f hnf
  refine ⟨ρ, (IsExposedRotation.mk (hcycle) (?_)), ?_⟩
  · intro i hi
    obtain ⟨ha, hρ⟩ := hedge i hi
    simpa only [hρ] using hsucc ⟨i, ha⟩
  · intro i
    by_cases hi : ρ i = i
    · simpa only [eliminateRotation_apply, hi] using hle i
    · obtain ⟨ha, hρ⟩ := hedge i hi
      simpa only [eliminateRotation_apply, hρ] using hbound ⟨i, ha⟩
theorem exists_rotationSequence_of_menWeaklyPrefer {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) (hle : MenWeaklyPrefer p μ ν) :
    ∃ rs, RotationSequence p μ rs ν := by
  classical
  let gap := fun σ : Matching n ↦ totalManRank p ν - totalManRank p σ
  refine (measure gap).wf.induction
    (C := fun σ ↦ IsStable p σ →
      MenWeaklyPrefer p σ ν →
      ∃ rs, RotationSequence p σ rs ν) μ ?_ hμ hle
  intro σ ih hσ hσν
  by_cases h : σ = ν
  · exact ⟨[], h ▸ RotationSequence.nil hσ⟩
  · obtain ⟨ρ, hρ, hnext⟩ := exists_exposedRotation_towards_target hσ hν hσν h
    have hinc := totalManRank_lt_eliminate hρ
    have hbound := totalManRank_le hnext
    have hdrop : gap (eliminateRotation σ ρ) < gap σ := by
      dsimp only [gap]
      omega
    obtain ⟨rs, hrs⟩ := ih _ hdrop (hρ.isStable_eliminate hσ) hnext
    exact ⟨ρ :: rs, .cons hσ hρ hrs⟩
theorem exists_rotationSequence_of_manOptimal {μ ν : Matching n}
    (hopt : IsManOptimal p μ) (hν : IsStable p ν) :
    ∃ rs, RotationSequence p μ rs ν :=
  exists_rotationSequence_of_menWeaklyPrefer hopt.1 hν (hopt.2 ν hν)
end StepC
end

-- RotationLabels
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n}
private structure RotationLabel (n : ℕ) where
  cycle : Equiv.Perm (Fin n)
  oldPartner : Fin n → Option (Fin n)
private def rotationLabel (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : RotationLabel n :=
  ⟨ρ, fun m ↦ if ρ m = m then none else some (μ m)⟩
private def rotationLabels : Matching n → List (Equiv.Perm (Fin n)) → List (RotationLabel n)
  | _, [] => []
  | μ, ρ :: rs => rotationLabel μ ρ :: rotationLabels (eliminateRotation μ ρ) rs
theorem rotationLabel_eliminate_of_fixes {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}
    (hfix : ∀ m, ρ m ≠ m → σ m = m) :
    rotationLabel (eliminateRotation μ σ) ρ = rotationLabel μ ρ := by
  unfold rotationLabel
  congr 1
  funext m
  by_cases hm : ρ m = m
  · simp [hm]
  · simp [hm, hfix m hm]
theorem RotationSequence.menWeaklyPrefer {μ ν : Matching n} {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) : MenWeaklyPrefer p μ ν := by
  induction h with
  | nil => exact fun _ ↦ le_rfl
  | @cons μ ν ρ rs hμ hρ rest ih =>
    intro m
    by_cases hm : ρ m = m
    · simpa only [eliminateRotation_apply, hm] using ih m
    · exact (hρ.manRank_lt_eliminate_of_moved hm).le.trans (ih m)
theorem IsExposedRotation.partner_ne_of_moved_of_rotationSequence {μ ν : Matching n}
    {ρ : Equiv.Perm (Fin n)} {rs : List (Equiv.Perm (Fin n))}
    (hρ : IsExposedRotation p μ ρ) (hpath : RotationSequence p (eliminateRotation μ ρ) rs ν)
    {m : Fin n} (hm : ρ m ≠ m) : μ m ≠ ν m :=
  fun he ↦ ((hρ.manRank_lt_eliminate_of_moved hm).trans_le
    (hpath.menWeaklyPrefer m)).ne (congrArg (p.manRank m) he)
end StepC
end

-- RotationPathIndependence
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n}
theorem RotationSequence.pull_rotation_to_front {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (hpath : RotationSequence p μ rs ν)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : ρ m ≠ m) (hend : μ m ≠ ν m) :
    ∃ ts, RotationSequence p (eliminateRotation μ ρ) ts ν ∧
      (rotationLabels μ rs).Perm
        (rotationLabel μ ρ :: rotationLabels (eliminateRotation μ ρ) ts) := by
  classical
  induction hpath generalizing ρ with
  | nil _ => exact (hend rfl).elim
  | @cons μ ν σ rs hμ hσ htail ih =>
    by_cases h : ρ = σ
    · subst σ
      exact ⟨rs, htail, List.Perm.refl _⟩
    · have hend' : eliminateRotation μ σ m ≠ ν m := by
        simpa only [eliminateRotation_apply, hρ.disjoint_moved hσ h m hm] using hend
      obtain ⟨ts, hts, hp⟩ := ih (hρ.persist_eliminate hσ h) hm hend'
      have hc := hρ.eliminate_comm hσ h
      have hts' : RotationSequence p (eliminateRotation (eliminateRotation μ ρ) σ) ts ν :=
        hc.symm ▸ hts
      have hlρ := rotationLabel_eliminate_of_fixes (μ := μ) (hρ.disjoint_moved hσ h)
      have hrev : σ ≠ ρ := Ne.symm h
      have hlσ := rotationLabel_eliminate_of_fixes (μ := μ) (hσ.disjoint_moved hρ hrev)
      refine ⟨σ :: ts, .cons (hρ.isStable_eliminate hμ) (hσ.persist_eliminate hρ hrev) hts', ?_⟩
      simp only [rotationLabels, hlσ, hc]
      rw [hlρ] at hp
      exact (List.Perm.cons _ hp).trans (List.Perm.swap _ _ _)
theorem RotationSequence.rotationLabels_perm {μ ν : Matching n}
    {rs ss : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) (h' : RotationSequence p μ ss ν) :
    (rotationLabels μ rs).Perm (rotationLabels μ ss) := by
  induction h generalizing ss with
  | nil _ =>
    cases h' with
    | nil _ => exact List.Perm.refl _
    | cons _ hσ htail =>
      obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hσ)
      exact ((hσ.partner_ne_of_moved_of_rotationSequence htail hm) rfl).elim
  | cons _ hρ htail ih =>
    obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
    have hend := hρ.partner_ne_of_moved_of_rotationSequence htail hm
    obtain ⟨ts, hts, hp⟩ := h'.pull_rotation_to_front hρ hm hend
    exact (List.Perm.cons _ (ih hts)).trans hp.symm
end StepC
end

-- RotationTrace
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n}
private def rotationLabelNewPartner (r : RotationLabel n) (m : Fin n) : Option (Fin n) :=
  r.oldPartner (r.cycle m)
theorem rotationLabelNewPartner_eq {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    {m : Fin n} (hm : ρ m ≠ m) :
    rotationLabelNewPartner (rotationLabel μ ρ) m = some (eliminateRotation μ ρ m) := by
  have hnext : ρ (ρ m) ≠ ρ m := fun h ↦ hm (ρ.injective h)
  simp [rotationLabelNewPartner, rotationLabel, eliminateRotation_apply, hnext]
namespace RotationSequence
variable {μ ν τ : Matching n} {rs ss : List (Equiv.Perm (Fin n))}
theorem isStable_end (h : RotationSequence p μ rs ν) : IsStable p ν := by
  induction h with
  | nil hμ => exact hμ
  | cons _ _ _ ih => exact ih
theorem append (h : RotationSequence p μ rs ν) (k : RotationSequence p ν ss τ) :
    RotationSequence p μ (rs ++ ss) τ := by
  induction h with
  | nil _ => exact k
  | cons hμ hρ _ ih => exact .cons hμ hρ (ih k)
theorem rotationLabels_append (h : RotationSequence p μ rs ν) :
    rotationLabels μ (rs ++ ss) = rotationLabels μ rs ++ rotationLabels ν ss := by
  induction h with
  | nil _ => rfl
  | cons _ _ _ ih => simp only [List.cons_append, rotationLabels, ih]
theorem label_moves_someone (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs) : ∃ m, r.cycle m ≠ m := by
  induction h with
  | nil _ => exact (List.not_mem_nil hr).elim
  | cons _ hρ _ ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
      exact ⟨m, hm⟩
    · exact ih hr
theorem label_rank_bounds (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs)
    {m : Fin n} (hm : r.cycle m ≠ m) :
    ∃ old new, r.oldPartner m = some old ∧ rotationLabelNewPartner r m = some new ∧
      p.manRank m (μ m) ≤ p.manRank m old ∧ p.manRank m old < p.manRank m new ∧
      p.manRank m new ≤ p.manRank m (ν m) := by
  induction h with
  | nil _ => exact (List.not_mem_nil hr).elim
  | @cons μ ν ρ rs hμ hρ rest ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨μ m, eliminateRotation μ ρ m, ?_, rotationLabelNewPartner_eq hm,
        le_rfl, hρ.manRank_lt_eliminate_of_moved hm, rest.menWeaklyPrefer m⟩
      simp [rotationLabel, show ρ m ≠ m from hm]
    · obtain ⟨old, new, hold, hnew, hle, hlt, hend⟩ := ih hr
      have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
        .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
      exact ⟨old, new, hold, hnew, (hstep.menWeaklyPrefer m).trans hle, hlt, hend⟩
theorem partner_eq_or_label_newPartner (h : RotationSequence p μ rs ν) (m : Fin n) :
    μ m = ν m ∨ ∃ r, r ∈ rotationLabels μ rs ∧ r.cycle m ≠ m ∧
      rotationLabelNewPartner r m = some (ν m) := by
  induction h with
  | nil _ => exact Or.inl rfl
  | @cons μ ν ρ rs _ _ _ ih =>
    rcases ih with he | ⟨r, hr, hm, hnew⟩
    · by_cases hm : ρ m = m
      · exact Or.inl (by simpa only [eliminateRotation_apply, hm] using he)
      · exact Or.inr ⟨rotationLabel μ ρ, List.mem_cons_self, hm,
          (rotationLabelNewPartner_eq hm).trans (congrArg some he)⟩
    · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, hm, hnew⟩
theorem separating_prefix (h : RotationSequence p μ rs ν) {a b : RotationLabel n}
    (hne : a ≠ b) (hmem : a ∈ rotationLabels μ rs ∨ b ∈ rotationLabels μ rs) :
    ∃ τ ts, RotationSequence p μ ts τ ∧
      ((a ∈ rotationLabels μ ts ∧ b ∉ rotationLabels μ ts) ∨
        (b ∈ rotationLabels μ ts ∧ a ∉ rotationLabels μ ts)) := by
  classical
  induction h with
  | nil _ => exact (hmem.elim (List.not_mem_nil ·) (List.not_mem_nil ·)).elim
  | @cons μ _ ρ _ hμ hρ _ ih =>
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
    by_cases ha : rotationLabel μ ρ = a
    · exact ⟨_, _, hstep, Or.inl (by simp [rotationLabels, ha, Ne.symm hne])⟩
    · by_cases hb : rotationLabel μ ρ = b
      · exact ⟨_, _, hstep, Or.inr (by simp [rotationLabels, hb, hne])⟩
      · simp only [rotationLabels, List.mem_cons, Ne.symm ha, Ne.symm hb, false_or] at hmem
        obtain ⟨τ, ts, hts, hsep⟩ := ih hmem
        exact ⟨τ, ρ :: ts, .cons hμ hρ hts, by
          simpa only [rotationLabels, List.mem_cons, Ne.symm ha, Ne.symm hb, false_or]⟩
end RotationSequence
end StepC
end

-- RotationIdeals
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
private def Rotation (p : Profile n) (μ₀ : Matching n) :=
  {r : RotationLabel n // ∃ ν rs, RotationSequence p μ₀ rs ν ∧ r ∈ rotationLabels μ₀ rs}
private instance : Finite (RotationLabel n) :=
  Finite.of_injective (fun r : RotationLabel n ↦ (r.cycle, r.oldPartner)) (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)
private instance : Finite (Rotation p μ₀) :=
  Finite.of_injective Subtype.val Subtype.val_injective
private def eliminatedRotations (p : Profile n) (μ₀ ν : Matching n) : Set (Rotation p μ₀) :=
  {r | ∃ rs, RotationSequence p μ₀ rs ν ∧ r.val ∈ rotationLabels μ₀ rs}
theorem RotationSequence.mem_eliminatedRotations_iff {ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ₀ rs ν)
    {r : Rotation p μ₀} :
    r ∈ eliminatedRotations p μ₀ ν ↔ r.val ∈ rotationLabels μ₀ rs :=
  ⟨fun ⟨_, hs, hr⟩ ↦ (hs.rotationLabels_perm h).mem_iff.mp hr, fun hr ↦ ⟨rs, h, hr⟩⟩
theorem eliminatedRotations_start (h : IsStable p μ₀) :
    eliminatedRotations p μ₀ μ₀ = ∅ := by
  ext r
  simp only [(RotationSequence.nil h).mem_eliminatedRotations_iff, rotationLabels,
    List.not_mem_nil, Set.notMem_empty]
private def Rotation.IsPrerequisite (r s : Rotation p μ₀) : Prop :=
  ∀ ν, s ∈ eliminatedRotations p μ₀ ν → r ∈ eliminatedRotations p μ₀ ν
private instance : PartialOrder (Rotation p μ₀) where
  le := Rotation.IsPrerequisite
  le_refl _ _ hr := hr
  le_trans _ _ _ hrs hst ν ht := hrs ν (hst ν ht)
  le_antisymm r s hrs hsr := by
    classical
    apply Subtype.ext
    by_contra hne
    obtain ⟨ν, rs, h, hr⟩ := r.property
    obtain ⟨τ, ts, ht, hsep⟩ := h.separating_prefix hne (Or.inl hr)
    rcases hsep with ⟨hr', hs'⟩ | ⟨hs', hr'⟩
    · exact hs' (ht.mem_eliminatedRotations_iff.mp
        (hsr τ (ht.mem_eliminatedRotations_iff.mpr hr')))
    · exact hr' (ht.mem_eliminatedRotations_iff.mp
        (hrs τ (ht.mem_eliminatedRotations_iff.mpr hs')))
private theorem RotationSequence.exists_exposed_prefix_of_mem {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs) :
    ∃ τ ts us, RotationSequence p μ ts τ ∧ IsExposedRotation p τ r.cycle ∧
      rotationLabel τ r.cycle = r ∧ rs = ts ++ r.cycle :: us := by
  induction h with
  | nil => exact (List.not_mem_nil hr).elim
  | @cons μ ν ρ rs hμ hρ htail ih =>
    rw [rotationLabels, List.mem_cons] at hr
    rcases hr with he | hr
    · subst r
      exact ⟨μ, [], rs, .nil hμ, hρ, rfl, rfl⟩
    · obtain ⟨τ, ts, us, ht, he, hl, hs⟩ := ih hr
      exact ⟨τ, ρ :: ts, us, .cons hμ hρ ht, he, hl, congrArg (ρ :: ·) hs⟩
theorem Rotation.lt_iff_before_exposure (hopt : IsManOptimal p μ₀)
    {r s : Rotation p μ₀} (hne : r ≠ s) :
    r < s ↔ ∀ ν, IsStable p ν → IsExposedRotation p ν s.val.cycle →
      rotationLabel ν s.val.cycle = s.val → r ∈ eliminatedRotations p μ₀ ν := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨hrs, _⟩ ν hν he hl
    obtain ⟨ts, ht⟩ := exists_rotationSequence_of_manOptimal hopt hν
    have hstep : RotationSequence p ν [s.val.cycle] (eliminateRotation ν s.val.cycle) :=
      .cons hν he (.nil (he.isStable_eliminate hν))
    have hnext := ht.append hstep
    have hs : s ∈ eliminatedRotations p μ₀ (eliminateRotation ν s.val.cycle) := by
      apply hnext.mem_eliminatedRotations_iff.mpr
      simp [ht.rotationLabels_append, rotationLabels, hl]
    have hr := hnext.mem_eliminatedRotations_iff.mp (hrs _ hs)
    rw [ht.rotationLabels_append, List.mem_append, rotationLabels, rotationLabels, hl,
      List.mem_singleton] at hr
    exact ht.mem_eliminatedRotations_iff.mpr (hr.resolve_right (fun h ↦ hne (Subtype.ext h)))
  · intro hbefore
    refine ⟨fun ν hν ↦ ?_, hne⟩
    obtain ⟨rs, h, hs⟩ := hν
    obtain ⟨τ, ts, us, ht, he, hl, hsplit⟩ := h.exists_exposed_prefix_of_mem hs
    have hr := ht.mem_eliminatedRotations_iff.mp (hbefore τ ht.isStable_end he hl)
    refine h.mem_eliminatedRotations_iff.mpr ?_
    rw [hsplit, ht.rotationLabels_append]
    exact List.mem_append_left _ hr
theorem mem_eliminatedRotations_iff_newRank_le {ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) {r : Rotation p μ₀} {m w : Fin n} (hm : r.val.cycle m ≠ m)
    (hw : rotationLabelNewPartner r.val m = some w) :
    r ∈ eliminatedRotations p μ₀ ν ↔ p.manRank m w ≤ p.manRank m (ν m) := by
  constructor
  · rintro ⟨rs, h, hr⟩
    obtain ⟨_, w', _, hw', _, _, hle⟩ := h.label_rank_bounds hr hm
    exact (Option.some.inj (hw'.symm.trans hw)) ▸ hle
  · intro hle
    obtain ⟨σ, rs, hσ, hr⟩ := r.property
    
    obtain ⟨τ, hτ, hmax⟩ := exists_stable_manRank_max hν hσ.isStable_end
    obtain ⟨as, ha⟩ := exists_rotationSequence_of_manOptimal hopt hν
    obtain ⟨bs, hb⟩ := exists_rotationSequence_of_menWeaklyPrefer hν hτ (fun i ↦ by
      rw [hmax i]
      exact le_max_left _ _)
    obtain ⟨cs, hc⟩ := exists_rotationSequence_of_menWeaklyPrefer hσ.isStable_end hτ (fun i ↦ by
      rw [hmax i]
      exact le_max_right _ _)
    have hrc : r.val ∈ rotationLabels μ₀ (rs ++ cs) := by
      rw [hσ.rotationLabels_append]
      exact List.mem_append_left _ hr
    have hra := ((hσ.append hc).rotationLabels_perm (ha.append hb)).mem_iff.mp hrc
    rw [ha.rotationLabels_append, List.mem_append] at hra
    rcases hra with hr' | hr'
    · exact ⟨as, ha, hr'⟩
    · 
      obtain ⟨_, w', _, hw', hstart, hstep, _⟩ := hb.label_rank_bounds hr' hm
      have heq := Option.some.inj (hw'.symm.trans hw)
      subst w'
      exact ((hstep.trans_le (hle.trans hstart)).false).elim
private theorem Rotation.exists_newPartner (r : Rotation p μ₀) :
    ∃ m w, r.val.cycle m ≠ m ∧ rotationLabelNewPartner r.val m = some w := by
  obtain ⟨ν, rs, h, hr⟩ := r.property
  obtain ⟨m, hm⟩ := h.label_moves_someone hr
  obtain ⟨_, w, _, hw, _, _, _⟩ := h.label_rank_bounds hr hm
  exact ⟨m, w, hm, hw⟩
theorem exists_eliminatedRotations_inter {μ ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      eliminatedRotations p μ₀ τ = eliminatedRotations p μ₀ μ ∩ eliminatedRotations p μ₀ ν := by
  obtain ⟨τ, hτ, hmin⟩ := exists_stable_manRank_min hμ hν
  refine ⟨τ, hτ, Set.ext fun r ↦ ?_⟩
  obtain ⟨m, w, hm, hw⟩ := r.exists_newPartner
  rw [Set.mem_inter_iff, mem_eliminatedRotations_iff_newRank_le hopt hτ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hμ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hν hm hw, hmin m, le_min_iff]
theorem exists_eliminatedRotations_union {μ ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      eliminatedRotations p μ₀ τ = eliminatedRotations p μ₀ μ ∪ eliminatedRotations p μ₀ ν := by
  obtain ⟨τ, hτ, hmax⟩ := exists_stable_manRank_max hμ hν
  refine ⟨τ, hτ, Set.ext fun r ↦ ?_⟩
  obtain ⟨m, w, hm, hw⟩ := r.exists_newPartner
  rw [Set.mem_union, mem_eliminatedRotations_iff_newRank_le hopt hτ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hμ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hν hm hw, hmax m, le_max_iff]
theorem eliminatedRotations_subset_iff {μ ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    eliminatedRotations p μ₀ μ ⊆ eliminatedRotations p μ₀ ν ↔ MenWeaklyPrefer p μ ν := by
  constructor
  · intro hsub m
    obtain ⟨rs, h⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    rcases h.partner_eq_or_label_newPartner m with he | ⟨r, hr, hm, hw⟩
    · rw [← he]
      exact hopt.2 ν hν m
    · let r' : Rotation p μ₀ := ⟨r, μ, rs, h, hr⟩
      have hmem : r' ∈ eliminatedRotations p μ₀ μ := ⟨rs, h, hr⟩
      exact (mem_eliminatedRotations_iff_newRank_le hopt hν hm hw).mp (hsub hmem)
  · intro hle r hr
    obtain ⟨m, w, hm, hw⟩ := r.exists_newPartner
    exact (mem_eliminatedRotations_iff_newRank_le hopt hν hm hw).mpr
      (((mem_eliminatedRotations_iff_newRank_le hopt hμ hm hw).mp hr).trans (hle m))
private def stableMatchingToRotationIdeal (ν : {ν : Matching n // IsStable p ν}) :
    LowerSet (Rotation p μ₀) :=
  ⟨eliminatedRotations p μ₀ ν.val, fun _ _ hrs hs ↦ hrs ν.val hs⟩
theorem stableMatchingToRotationIdeal_bijective (hopt : IsManOptimal p μ₀) :
    Function.Bijective (stableMatchingToRotationIdeal (p := p) (μ₀ := μ₀)) := by
  constructor
  · intro μ ν h
    have he : eliminatedRotations p μ₀ μ.val = eliminatedRotations p μ₀ ν.val :=
      congrArg (fun I : LowerSet (Rotation p μ₀) ↦ I.carrier) h
    have hμν := (eliminatedRotations_subset_iff hopt μ.property ν.property).mp he.le
    have hνμ := (eliminatedRotations_subset_iff hopt ν.property μ.property).mp he.ge
    exact Subtype.ext (Equiv.ext fun m ↦ (p.manRank m).injective ((hμν m).antisymm (hνμ m)))
  · intro I
    let F := Set.range fun ν : {ν : Matching n // IsStable p ν} ↦
      eliminatedRotations p μ₀ ν.val
    have hempty : ∅ ∈ F := ⟨⟨μ₀, hopt.1⟩, eliminatedRotations_start hopt.1⟩
    have hinter : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∩ B ∈ F := by
      rintro _ _ ⟨μ, rfl⟩ ⟨ν, rfl⟩
      obtain ⟨τ, hτ, he⟩ := exists_eliminatedRotations_inter hopt μ.property ν.property
      exact ⟨⟨τ, hτ⟩, he⟩
    have hunion : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∪ B ∈ F := by
      rintro _ _ ⟨μ, rfl⟩ ⟨ν, rfl⟩
      obtain ⟨τ, hτ, he⟩ := exists_eliminatedRotations_union hopt μ.property ν.property
      exact ⟨⟨τ, hτ⟩, he⟩
    have hcover (r : Rotation p μ₀) : ∃ A ∈ F, r ∈ A := by
      obtain ⟨ν, rs, h, hr⟩ := r.property
      exact ⟨_, ⟨⟨ν, h.isStable_end⟩, rfl⟩, ⟨rs, h, hr⟩⟩
    have hdown : ∀ ⦃r s : Rotation p μ₀⦄, (∀ A ∈ F, s ∈ A → r ∈ A) → s ∈ I → r ∈ I := by
      intro r s hrs hs
      refine I.lower (show r ≤ s from fun ν hν ↦ ?_) hs
      obtain ⟨rs, h, hmem⟩ := hν
      exact hrs _ ⟨⟨ν, h.isStable_end⟩, rfl⟩ ⟨rs, h, hmem⟩
    have hI : (I : Set (Rotation p μ₀)) ∈ F :=
      mem_family_of_downward_closed hempty hinter hunion hcover hdown
    obtain ⟨ν, hν⟩ := hI
    exact ⟨ν, LowerSet.ext hν⟩
private noncomputable def stableMatchingEquivRotationIdeals (hopt : IsManOptimal p μ₀) :
    {ν : Matching n // IsStable p ν} ≃ LowerSet (Rotation p μ₀) :=
  Equiv.ofBijective stableMatchingToRotationIdeal (stableMatchingToRotationIdeal_bijective hopt)
end StepC
end

-- CoexposedRotations
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
private def rotationOfExposed (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) : Rotation p μ₀ :=
  ⟨rotationLabel μ ρ, by
    obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
    refine ⟨_, rs ++ [ρ], hrs.append hstep, ?_⟩
    simp [hrs.rotationLabels_append, rotationLabels]⟩
theorem rotationOfExposed_not_mem_eliminatedRotations (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) :
    rotationOfExposed hopt hμ hρ ∉ eliminatedRotations p μ₀ μ := by
  obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
  exact fun hr ↦ (not_le_of_gt (hρ.manRank_lt_eliminate_of_moved hm))
    ((mem_eliminatedRotations_iff_newRank_le hopt hμ (m := m) hm
      (rotationLabelNewPartner_eq hm)).mp hr)
end StepC
end

-- CoexposureCycleMoment
section
open StableMarriage MeasureTheory
open scoped BigOperators ENNReal
namespace StepC
private def RealizesSuccessorPermutation {n : ℕ} (p : Profile n) (M σ : Matching n) : Prop :=
  ∀ i ∈ σ.support, IsSuccessor p M i (M (σ i))
end StepC
end

-- RowCompetition
section
open Set
open scoped BigOperators
namespace StepC
variable {ι : Type*} {J : Finset ι} {a : ι → ℝ} {A b : ℝ}
private theorem rowCompetition_integral_rpow (hb : 0 < b) (hA : 0 ≤ A) :
    (∫ z in (0 : ℝ)..1, (1 - b * z) ^ (A / b)) =
      (1 - (1 - b) ^ (1 + A / b)) / (A + b) := by
  have hr : 0 ≤ A / b := div_nonneg hA hb.le
  have h := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1)
    (f := fun x : ℝ ↦ x ^ (A / b)) b 1
  simp only [mul_one, mul_zero, sub_zero] at h
  rw [integral_rpow (Or.inl (by linarith : -1 < A / b)), Real.one_rpow,
    add_comm (A / b) 1] at h
  apply (eq_div_iff (by positivity : A + b ≠ 0)).2
  have h' := (eq_div_iff (by positivity : 1 + A / b ≠ 0)).1 h
  rw [show A + b = b * (1 + A / b) by field_simp; ring]
  linear_combination h'
theorem scoreRowMass_lower_power (hb : 0 < b) (hb1 : b ≤ 1)
    (ha : ∀ j ∈ J, a j ∈ Icc 0 b) (hsum : ∑ j ∈ J, a j ≤ A) :
    (1 - (1 - b) ^ (1 + A / b)) / (A + b) ≤ scoreRowMass J a 0 1 := by
  have hA := (Finset.sum_nonneg fun j hj ↦ (ha j hj).1).trans hsum
  have hcont : Continuous fun t : ℝ ↦ (1 - b * t) ^ (A / b) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).rpow_const
      fun _ ↦ Or.inr (div_nonneg hA hb.le)
  rw [← rowCompetition_integral_rpow hb hA]
  refine intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
    ((continuous_scoreRowKernel J a).intervalIntegrable _ _) fun t ht ↦ ?_
  have hbt : b * t ≤ 1 := (mul_le_of_le_one_left ht.1 hb1).trans ht.2
  have hbase := sub_nonneg.mpr hbt
  have hweight (j) (hj : j ∈ J) : 0 ≤ a j / b := div_nonneg (ha j hj).1 hb.le
  calc
    (1 - b * t) ^ (A / b) ≤ (1 - b * t) ^ ((∑ j ∈ J, a j) / b) :=
      Real.rpow_le_rpow_of_exponent_ge' hbase (sub_le_self _ (mul_nonneg hb.le ht.1))
        (div_nonneg (Finset.sum_nonneg fun j hj ↦ (ha j hj).1) hb.le)
        (div_le_div_of_nonneg_right hsum hb.le)
    _ = ∏ j ∈ J, (1 - b * t) ^ (a j / b) := by
      rw [Finset.sum_div, Real.rpow_sum_of_nonneg hbase hweight]
    _ ≤ scoreRowKernel J a t := by
      refine Finset.prod_le_prod (fun j _ ↦ Real.rpow_nonneg hbase _) fun j hj ↦ ?_
      have h := rpow_one_add_le_one_add_mul_self (s := -(b * t)) (by linarith only [hbt])
        (hweight j hj) ((div_le_one hb).mpr (ha j hj).2)
      rw [← sub_eq_add_neg] at h
      refine h.trans_eq ?_
      field_simp
      ring
theorem scoreRowMass_lower_reciprocal (ha : ∀ j ∈ J, a j ∈ Icc 0 1)
    (hsum : ∑ j ∈ J, a j ≤ A) :
    1 / (1 + A) ≤ scoreRowMass J a 0 1 := by
  have hA := (Finset.sum_nonneg fun j hj ↦ (ha j hj).1).trans hsum
  simpa [Real.zero_rpow (by linarith only [hA] : 1 + A ≠ 0), add_comm A 1] using
    scoreRowMass_lower_power zero_lt_one le_rfl ha hsum
end StepC
end

-- ReverseIIDLabelGood
section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StepC
section Measures
variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
private theorem iid_two_marginal (μ : Measure α) [IsProbabilityMeasure μ]
    {i j : ι} (hij : i ≠ j) {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.pi (fun _ : ι ↦ μ)) {x | x i ∈ A ∧ x j ∈ B} = μ A * μ B := by
  have h : iIndepFun (fun i (x : ι → α) ↦ x i) (Measure.pi (fun _ : ι ↦ μ)) :=
    iIndepFun_pi (X := fun _ : ι ↦ id) (fun _ ↦ measurable_id.aemeasurable)
  have hp := (h.indepFun hij).measure_inter_preimage_eq_mul A B hA hB
  exact hp.trans (congrArg₂ (· * ·)
    ((measurePreserving_eval (fun _ : ι ↦ μ) i).measure_preimage hA.nullMeasurableSet)
    ((measurePreserving_eval (fun _ : ι ↦ μ) j).measure_preimage hB.nullMeasurableSet))
variable [Fintype α] [DiscreteMeasurableSpace α]
theorem iid_forbiddenArc_measure_le (μ : Measure α) [IsProbabilityMeasure μ]
    {i j : ι} (hij : i ≠ j) (F : α → Set α) :
    (Measure.pi (fun _ : ι ↦ μ)) {x | x j ∈ F (x i)} ≤
      ∑ a, μ {a} * μ (F a) := by
  have he : {x : ι → α | x j ∈ F (x i)} =
      ⋃ a : α, {x : ι → α | x i = a ∧ x j ∈ F a} := by
    ext x
    simp
  rw [he]
  refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  exact (iid_two_marginal μ hij (A := {a}) MeasurableSet.of_discrete
    (B := F a) MeasurableSet.of_discrete).le
theorem iid_labelCollision_measure_le (μ : Measure α) [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : ι ↦ μ)) {x | ¬ Function.Injective x} ≤
      ((Fintype.card ι).choose 2 : ℝ≥0∞) * ∑ a, (μ {a}) ^ 2 := by
  classical
  let pairs := (Finset.univ : Finset ι).powersetCard 2
  let C (s : ↥pairs) : Set (ι → α) := {x | ¬ Set.InjOn x (s.val : Set ι)}
  have hsub : {x | ¬ Function.Injective x} ⊆ ⋃ s, C s := by
    intro x hx
    obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hx
    have hm : {i, j} ∈ pairs :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hij⟩
    refine Set.mem_iUnion.mpr ⟨⟨{i, j}, hm⟩, ?_⟩
    change ¬ Set.InjOn x (↑({i, j} : Finset ι))
    rw [Finset.coe_pair, Set.injOn_pair]
    exact fun h ↦ hij (h heq)
  calc
    _ ≤ ∑ s, (Measure.pi (fun _ : ι ↦ μ)) (C s) :=
      (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _ : ↥pairs, ∑ a, (μ {a}) ^ 2 := by
      refine Finset.sum_le_sum fun s _ ↦ ?_
      obtain ⟨i, j, hij, hs⟩ :=
        Finset.card_eq_two.mp (Finset.mem_powersetCard.mp s.property).2
      have he : C s = {x : ι → α | x j ∈ ({x i} : Set α)} := by
        ext x
        simp [C, hs, hij, eq_comm]
      rw [he]
      simpa only [pow_two] using iid_forbiddenArc_measure_le μ hij (fun a ↦ {a})
    _ = _ := by simp [pairs, Finset.card_powersetCard, nsmul_eq_mul]
private def iidLabelGood (A : Set α) (F : α → Set α) (e : ι → ι) : Set (ι → α) :=
  {x | Function.Injective x ∧ (∀ i, x i ∉ A) ∧ ∀ i, x (e i) ∉ F (x i)}
theorem iidLabelGood_measure_lower (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) (F : α → Set α) (e : ι → ι) (he : ∀ i, e i ≠ i)
    (η : ℝ≥0∞) (hη : ∀ a, μ (F a) ≤ η) :
    1 - (((Fintype.card ι).choose 2 : ℝ≥0∞) * (∑ a, (μ {a}) ^ 2) +
        (Fintype.card ι : ℝ≥0∞) * μ A + (Fintype.card ι : ℝ≥0∞) * η) ≤
      (Measure.pi (fun _ : ι ↦ μ)) (iidLabelGood A F e) := by
  classical
  let ν := Measure.pi (fun _ : ι ↦ μ)
  let C : Set (ι → α) := {x | ¬ Function.Injective x}
  let P : Set (ι → α) := ⋃ i, {x | x i ∈ A}
  let M : Set (ι → α) := ⋃ i, {x | x (e i) ∈ F (x i)}
  have hbad : (iidLabelGood A F e)ᶜ = C ∪ P ∪ M := by
    ext x
    simp only [iidLabelGood, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union, C, P, M,
      Set.mem_iUnion, not_and_or, not_forall, not_not, or_assoc]
  have hP : ν P ≤ (Fintype.card ι : ℝ≥0∞) * μ A := by
    calc
      _ ≤ ∑ i : ι, ν {x | x i ∈ A} := measure_iUnion_fintype_le _ _
      _ = ∑ _ : ι, μ A := Finset.sum_congr rfl fun i _ ↦
        (measurePreserving_eval (fun _ : ι ↦ μ) i).measure_preimage
          MeasurableSet.of_discrete.nullMeasurableSet
      _ = _ := by simp [nsmul_eq_mul]
  have hM : ν M ≤ (Fintype.card ι : ℝ≥0∞) * η := by
    calc
      _ ≤ ∑ i : ι, ν {x | x (e i) ∈ F (x i)} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _ : ι, η := by
        refine Finset.sum_le_sum fun i _ ↦
          (iid_forbiddenArc_measure_le μ (he i).symm F).trans ?_
        calc
          _ ≤ ∑ a, μ {a} * η := Finset.sum_le_sum fun a _ ↦ mul_le_mul_right (hη a) _
          _ = _ := by rw [← Finset.sum_mul]; simp
      _ = _ := by simp [nsmul_eq_mul]
  have hcomp : ν (iidLabelGood A F e) = 1 - ν (iidLabelGood A F e)ᶜ := by
    rw [← (measure_univ : ν univ = 1), ← measure_compl
      MeasurableSet.of_discrete (measure_ne_top ν _), compl_compl]
  rw [← show ν (iidLabelGood A F e) = _ from rfl, hcomp, hbad]
  apply tsub_le_tsub_left
  exact (measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add (iid_labelCollision_measure_le μ) hP)) hM)
omit [Fintype α] in
private theorem iidLabelFinset_measure_eq_sum (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Finset (ι → α)) :
    (Measure.pi (fun _ : ι ↦ μ)) (S : Set (ι → α)) = ∑ x ∈ S, ∏ i, μ {x i} := by
  rw [← sum_measure_singleton]
  simp only [Measure.pi_singleton]
end Measures
open scoped Classical in
theorem iidLabelGood_sum_weights_lower {ι α : Type*} [Fintype ι] [Fintype α]
    (r : α → ℝ≥0∞) (hr : ∑ a, r a = 1) (A : Finset α) (F : α → Finset α)
    (e : ι → ι) (he : ∀ i, e i ≠ i) (η : ℝ≥0∞)
    (hη : ∀ a, ∑ b ∈ F a, r b ≤ η) :
    1 - (((Fintype.card ι).choose 2 : ℝ≥0∞) * (∑ a, (r a) ^ 2) +
        (Fintype.card ι : ℝ≥0∞) * (∑ a ∈ A, r a) + (Fintype.card ι : ℝ≥0∞) * η) ≤
      ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ iidLabelGood (A : Set α) (fun a ↦ ↑(F a)) e),
        ∏ i, r (x i) := by
  classical
  let : MeasurableSpace α := ⊤
  let : DiscreteMeasurableSpace α := ⟨fun _ ↦ trivial⟩
  let μ := (PMF.ofFintype r hr).toMeasure
  let G := iidLabelGood (A : Set α) (fun a ↦ ↑(F a)) e
  let S := Finset.univ.filter (fun x ↦ x ∈ G)
  have hS : (S : Set (ι → α)) = G := by simp [S]
  have hmass (s : Finset α) : μ (s : Set α) = ∑ a ∈ s, r a :=
    (PMF.ofFintype r hr).toMeasure_apply_finset s
  have hatom (a : α) : μ {a} = r a :=
    (PMF.ofFintype r hr).toMeasure_apply_singleton a MeasurableSet.of_discrete
  have hg := iidLabelGood_measure_lower μ (A : Set α) (fun a ↦ ↑(F a)) e he η
    (fun a ↦ (hmass (F a)).symm ▸ hη a)
  change _ ≤ (Measure.pi (fun _ : ι ↦ μ)) G at hg
  rw [← hS, iidLabelFinset_measure_eq_sum μ S, hmass A] at hg
  simpa only [hatom] using hg
end StepC
end

-- PivotReverseMaskLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
open scoped Classical in
private noncomputable def goodReverseSupportPermutations {n : ℕ} (k : ℕ)
    (A : Finset (Fin n)) (F : Fin n → Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ ↦ σ.support.card = k ∧
    ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i
private noncomputable def forwardMaskForbiddenTargets {n : ℕ} (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ ¬ ∃ q : ForwardInactiveColumnIndex flag (μ.symm i),
    q.val.val.val.1 = μ.symm j
end StepC
end

-- PivotReverseCompetitorMass
section
open StableMarriage
open scoped BigOperators ENNReal
namespace StepC
end StepC
end

-- PivotForwardMaskProbability
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepC
private noncomputable def forwardCellFlag (x y : ℝ) (z : ℝ × ℝ) : Bool := by
  classical
  exact decide (z ∈ forwardEligibleScoreCell x y)
private noncomputable def forwardMaskOfScores {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (q : OffDiagonalCellIndex n) : Bool :=
  forwardCellFlag (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (z q)
end StepC
end

-- PivotForwardRevealRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepC
private abbrev ForwardRevealedMaleScores {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  ForwardActiveCellIndex flag → ℝ
private abbrev ForwardInactiveColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  (i : Fin n) → ForwardInactiveColumnIndex flag i → ℝ × ℝ
private def forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    OffDiagonalScorePairs n → ForwardRevealedMaleScores flag × ForwardInactiveColumns flag :=
  Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag
end StepC
end

-- PivotForwardPivotReadout
section
open MeasureTheory Set StableMarriage
namespace StepC
private noncomputable def forwardPivotIncrement {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n)
    (a : ForwardRevealedMaleScores flag) (m : Fin n) : ℝ :=
  if hm : ρ m ≠ m then
    let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    if hq : flag q = true then a ⟨q, hq⟩ - (diagonalPairAt d m).1 else 0
  else 0
end StepC
end

-- SingletonIdealAnchor
section
namespace StepC
variable {α : Type*} [PartialOrder α]
private def singletonAnchorIdeal (r : α) : LowerSet α :=
  ⟨(Set.Ici r)ᶜ, fun _ _ hst ht hrs ↦ ht (hrs.trans hst)⟩
@[simp] theorem mem_singletonAnchorIdeal {r s : α} :
    s ∈ singletonAnchorIdeal r ↔ ¬ r ≤ s :=
  Iff.rfl
theorem lowerSet_eq_singletonAnchorIdeal_iff [Finite α] (I : LowerSet α) (r : α) :
    I = singletonAnchorIdeal r ↔ ∀ s : α, Minimal (fun t : α ↦ t ∉ I) s ↔ s = r :=
  ⟨fun h s ↦ h.symm ▸
    minimal_iff_eq (fun hr ↦ (mem_singletonAnchorIdeal.mp hr) le_rfl)
      (fun _ ht ↦ not_not.mp fun hrt ↦ ht (mem_singletonAnchorIdeal.mpr hrt)),
    fun h ↦ LowerSet.ext (Set.ext fun s ↦
      show s ∈ I ↔ ¬ r ≤ s from
      ⟨fun hs hrs ↦ ((h r).mpr rfl).prop (I.lower hrs hs),
        fun hrs ↦ Classical.byContradiction fun hs ↦
          
          let ⟨t, hts, ht⟩ := Finite.exists_le_minimal (p := fun t : α ↦ t ∉ I) hs
          hrs (by simpa only [(h t).mp ht] using hts)⟩)⟩
end StepC
end

-- SingletonRotationAnchor
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
private def Rotation.IsExposedAt (r : Rotation p μ₀) (μ : Matching n) : Prop :=
  IsExposedRotation p μ r.val.cycle ∧ rotationLabel μ r.val.cycle = r.val
theorem Rotation.isExposedAt_iff_minimal (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (r : Rotation p μ₀) :
    r.IsExposedAt μ ↔ Minimal (fun s ↦ s ∉ eliminatedRotations p μ₀ μ) r := by
  rw [minimal_iff_forall_lt]
  constructor
  · rintro ⟨he, hl⟩
    have hr : rotationOfExposed hopt hμ he = r := Subtype.ext hl
    refine ⟨hr ▸ rotationOfExposed_not_mem_eliminatedRotations hopt hμ he, ?_⟩
    intro s hsr
    exact not_not_intro
      ((Rotation.lt_iff_before_exposure hopt hsr.ne).mp hsr μ hμ he hl)
  · classical
    rintro ⟨hr, hbefore⟩
    let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨μ, hμ⟩
    let J : LowerSet (Rotation p μ₀) :=
      ⟨insert r (I : Set (Rotation p μ₀)), by
        intro s t hst ht
        rcases Set.mem_insert_iff.mp ht with rfl | ht
        · rcases eq_or_lt_of_le hst with rfl | hsr
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (not_not.mp (hbefore hsr))
        · exact Set.mem_insert_of_mem _ (I.lower hst ht)⟩
    let e := stableMatchingEquivRotationIdeals hopt
    let ν := e.symm J
    have hν : eliminatedRotations p μ₀ ν.val = (J : Set (Rotation p μ₀)) :=
      congrArg (fun K : LowerSet (Rotation p μ₀) ↦ (K : Set (Rotation p μ₀)))
        (e.apply_symm_apply J)
    have hle : eliminatedRotations p μ₀ μ ⊆ eliminatedRotations p μ₀ ν.val := by
      rw [hν]
      exact fun s hs ↦ Set.mem_insert_of_mem _ hs
    have hne : μ ≠ ν.val := by
      intro h
      apply hr
      rw [h, hν]
      exact Set.mem_insert r _
    obtain ⟨ρ, hρ, hnext⟩ := exists_exposedRotation_towards_target hμ ν.property
      ((eliminatedRotations_subset_iff hopt hμ ν.property).mp hle) hne
    let q := rotationOfExposed hopt hμ hρ
    obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    have hstable := hρ.isStable_eliminate hμ
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil hstable)
    have hq : q ∈ eliminatedRotations p μ₀ (eliminateRotation μ ρ) := by
      apply (hrs.append hstep).mem_eliminatedRotations_iff.mpr
      simp [hrs.rotationLabels_append, rotationLabels, q, rotationOfExposed]
    have hq' := (eliminatedRotations_subset_iff hopt hstable ν.property).mpr hnext hq
    rw [hν] at hq'
    have hqr : q = r := (Set.mem_insert_iff.mp hq').resolve_right
      (rotationOfExposed_not_mem_eliminatedRotations hopt hμ hρ)
    rw [← hqr]
    exact ⟨hρ, rfl⟩
private noncomputable def singletonRotationAnchor (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀) :
    {ν : Matching n // IsStable p ν} :=
  (stableMatchingEquivRotationIdeals hopt).symm (singletonAnchorIdeal r)
theorem eliminatedRotations_singletonRotationAnchor
    (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀) :
    eliminatedRotations p μ₀ (singletonRotationAnchor hopt r).val = (Set.Ici r)ᶜ :=
  congrArg (fun I : LowerSet (Rotation p μ₀) ↦ (I : Set (Rotation p μ₀)))
    ((stableMatchingEquivRotationIdeals hopt).apply_symm_apply (singletonAnchorIdeal r))
theorem eq_singletonRotationAnchor_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (ν : {ν : Matching n // IsStable p ν}) :
    ν = singletonRotationAnchor hopt r ↔
      ∀ s : Rotation p μ₀, s.IsExposedAt ν.val ↔ s = r := by
  let e := stableMatchingEquivRotationIdeals hopt
  change ν = e.symm (singletonAnchorIdeal r) ↔ _
  rw [← e.apply_eq_iff_eq, e.apply_symm_apply, lowerSet_eq_singletonAnchorIdeal_iff]
  simp only [Rotation.isExposedAt_iff_minimal hopt ν.property]
  rfl
end StepC
end

-- UndoableRotations
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
end StepC
end

-- ReverseRotationIdeals
section
open StableMarriage
namespace StepC
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
theorem IsReverseExposedRotation.forward_exposed
    (hσ : IsReverseExposedRotation p ν σ) (hν : IsStable p ν) :
    IsExposedRotation p (undoReverseRotation ν σ) (reverseRotationCycle ν.symm σ) := by
  simpa only [undoReverseRotation, swapProfile_swapProfile] using
    (show IsExposedRotation (swapProfile p) ν.symm σ from hσ).isExposedRotation_swap_eliminate
      (isStable_swapProfile_iff.mpr hν)
private def reverseExposedRotationLabel (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) : Rotation p μ₀ :=
  rotationOfExposed hopt (σ.property.undo_stable hν) (σ.property.forward_exposed hν)
end StepC
end

-- PivotCrossBlocker
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}
end StepC
end

-- PivotReversePermutationCompatibility
section
open StableMarriage
namespace StepC
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
end StepC
end

-- UndoMaximalSubset
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n}
private abbrev MaximalEliminatedRotation (p : Profile n) (μ₀ ν : Matching n) :=
  {r : Rotation p μ₀ // Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r}
private def undoMaximalSubsetIdeal (hν : IsStable p ν)
    (D : Set (MaximalEliminatedRotation p μ₀ ν)) : LowerSet (Rotation p μ₀) :=
  ⟨eliminatedRotations p μ₀ ν \ (Subtype.val '' D), by
    let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨ν, hν⟩
    intro b a hab hb
    refine ⟨I.lower hab hb.1, ?_⟩
    rintro ⟨r, hr, rfl⟩
    exact hb.2 ⟨r, hr, hab.antisymm (r.property.2 hb.1 hab)⟩⟩
private theorem mem_undoMaximalSubsetIdeal_iff (hν : IsStable p ν)
    (D : Set (MaximalEliminatedRotation p μ₀ ν)) (r : MaximalEliminatedRotation p μ₀ ν) :
    r.val ∈ undoMaximalSubsetIdeal hν D ↔ r ∉ D := by
  change (r.val ∈ eliminatedRotations p μ₀ ν ∧ r.val ∉ Subtype.val '' D) ↔ r ∉ D
  rw [and_iff_right r.property.1, Subtype.val_injective.mem_set_image]
private def undoMaximalSubsetIdealEmbedding (hν : IsStable p ν) :
    Set (MaximalEliminatedRotation p μ₀ ν) ↪ LowerSet (Rotation p μ₀) :=
  ⟨undoMaximalSubsetIdeal hν, by
    intro D E h
    ext r
    apply not_iff_not.mp
    rw [← mem_undoMaximalSubsetIdeal_iff hν D r,
      ← mem_undoMaximalSubsetIdeal_iff hν E r, h]⟩
private noncomputable def undoMaximalSubsetEmbedding (hopt : IsManOptimal p μ₀) (hν : IsStable p ν) :
    Set (MaximalEliminatedRotation p μ₀ ν) ↪ {μ : Matching n // IsStable p μ} :=
  (undoMaximalSubsetIdealEmbedding hν).trans
    (stableMatchingEquivRotationIdeals hopt).symm.toEmbedding
theorem eliminatedRotations_undoMaximalSubsetEmbedding (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (D : Set (MaximalEliminatedRotation p μ₀ ν)) :
    eliminatedRotations p μ₀ (undoMaximalSubsetEmbedding hopt hν D).val =
      eliminatedRotations p μ₀ ν \ (Subtype.val '' D) :=
  congrArg (fun I : LowerSet (Rotation p μ₀) ↦ (I : Set (Rotation p μ₀)))
    ((stableMatchingEquivRotationIdeals hopt).apply_symm_apply (undoMaximalSubsetIdeal hν D))
end StepC
end

-- PivotIdealExposure
section
open StableMarriage
namespace StepC
theorem minimal_compl_diff_maximal_iff {α : Type*} [PartialOrder α]
    (I : LowerSet α) (D : Set α) (hD : ∀ t ∈ D, Maximal (· ∈ I) t) (s : α) :
    Minimal (· ∉ (I : Set α) \ D) s ↔
      s ∈ D ∨ (Minimal (· ∉ I) s ∧ ∀ t ∈ D, ¬ t < s) := by
  simp only [minimal_iff_forall_lt, not_not]
  constructor
  · rintro ⟨hs, hpred⟩
    by_cases hsD : s ∈ D
    · exact Or.inl hsD
    · exact Or.inr ⟨⟨fun hsI ↦ hs ⟨hsI, hsD⟩, fun _ hts ↦ (hpred hts).1⟩,
        fun _ htD hts ↦ (hpred hts).2 htD⟩
  · rintro (hsD | ⟨⟨hsI, hpred⟩, hcompat⟩)
    · have hsI := (hD s hsD).prop
      refine ⟨fun h ↦ h.2 hsD, fun t hts ↦ ⟨I.lower hts.le hsI, ?_⟩⟩
      exact fun htD ↦ hts.not_ge ((hD t htD).2 hsI hts.le)
    · exact ⟨fun h ↦ hsI h.1, fun t hts ↦ ⟨hpred hts, fun htD ↦ hcompat t htD hts⟩⟩
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
theorem isExposedAt_undoMaximalSubsetEmbedding_iff
    (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (D : Set (MaximalEliminatedRotation p μ₀ μ)) (s : Rotation p μ₀) :
    s.IsExposedAt (undoMaximalSubsetEmbedding hopt hμ D).val ↔
      s ∈ Subtype.val '' D ∨ (s.IsExposedAt μ ∧ ∀ t ∈ Subtype.val '' D, ¬ t < s) := by
  rw [Rotation.isExposedAt_iff_minimal hopt (undoMaximalSubsetEmbedding hopt hμ D).property,
    Rotation.isExposedAt_iff_minimal hopt hμ,
    eliminatedRotations_undoMaximalSubsetEmbedding]
  let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨μ, hμ⟩
  apply minimal_compl_diff_maximal_iff I
  rintro _ ⟨t, _, rfl⟩
  exact t.property
theorem pivot_isExposedAt_undo_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (D : Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)) :
    r.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val ↔
      ∀ s ∈ Subtype.val '' D, ¬ s < r := by
  let A := singletonRotationAnchor hopt r
  have hA : r.IsExposedAt A.val := ((eq_singletonRotationAnchor_iff hopt r A).mp rfl r).mpr rfl
  have hrI : r ∉ eliminatedRotations p μ₀ A.val :=
    ((Rotation.isExposedAt_iff_minimal hopt A.property r).mp hA).prop
  have hrD : r ∉ Subtype.val '' D := by
    rintro ⟨s, _, hs⟩
    exact hrI (hs ▸ s.property.prop)
  rw [isExposedAt_undoMaximalSubsetEmbedding_iff hopt A.property D r]
  exact ⟨fun h ↦ (h.resolve_left hrD).2, fun h ↦ Or.inr ⟨hA, h⟩⟩
theorem isExposedAt_undo_pivot_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (D : Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val))
    (hr : r.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val)
    (s : Rotation p μ₀) :
    s.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val ↔
      s = r ∨ s ∈ Subtype.val '' D := by
  let A := singletonRotationAnchor hopt r
  have hcompat := (pivot_isExposedAt_undo_iff hopt r D).mp hr
  rw [isExposedAt_undoMaximalSubsetEmbedding_iff hopt A.property D s,
    (eq_singletonRotationAnchor_iff hopt r A).mp rfl s]
  constructor
  · rintro (hsD | ⟨hsr, _⟩)
    · exact Or.inr hsD
    · exact Or.inl hsr
  · rintro (rfl | hsD)
    · exact Or.inr ⟨rfl, hcompat⟩
    · exact Or.inl hsD
end StepC
end

-- ReverseRotationPersistence
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ τ : Equiv.Perm (Fin n)}
end StepC
end

-- RotationUndoSequences
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {hopt : IsManOptimal p μ₀}
private inductive RotationUndoSequence (hopt : IsManOptimal p μ₀) :
    Matching n → List (Rotation p μ₀) → Matching n → Prop where
  | nil {ν : Matching n} (hν : IsStable p ν) : RotationUndoSequence hopt ν [] ν
  | cons {ν τ : Matching n} {r : Rotation p μ₀} {rs : List (Rotation p μ₀)}
      (hν : IsStable p ν)
      (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ})
      (hlabel : reverseExposedRotationLabel hopt hν σ = r)
      (rest : RotationUndoSequence hopt (undoReverseRotation ν σ.val) rs τ) :
      RotationUndoSequence hopt ν (r :: rs) τ
theorem RotationUndoSequence.isStable_end {rs : List (Rotation p μ₀)}
    (h : RotationUndoSequence hopt ν rs μ) : IsStable p μ := by
  induction h with
  | nil hν => exact hν
  | cons _ _ _ _ ih => exact ih
end StepC
end

-- PivotIncidenceCounting
section
open StableMarriage
open scoped BigOperators
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ ν μ : Matching n} {hopt : IsManOptimal p μ₀}
private def rotationLength (r : Rotation p μ₀) : ℕ :=
  r.val.cycle.support.card
private structure PivotDecoration (hopt : IsManOptimal p μ₀) (K : ℕ) (r : Rotation p μ₀) where
  removed : Finset (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)
  totalLength_le : (∑ s ∈ removed, rotationLength s.val) ≤ K
  pivot_exposed : r.IsExposedAt
    (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property removed).val
namespace PivotDecoration
variable {K : ℕ} {r : Rotation p μ₀}
private noncomputable def matching (D : PivotDecoration hopt K r) : {M : Matching n // IsStable p M} :=
  undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D.removed
theorem isExposedAt_matching_iff (D : PivotDecoration hopt K r) (s : Rotation p μ₀) :
    s.IsExposedAt D.matching.val ↔ s = r ∨ s ∈ Subtype.val ''
      (↑D.removed :
        Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)) :=
  isExposedAt_undo_pivot_iff hopt r D.removed D.pivot_exposed s
end PivotDecoration
private abbrev LongPivot (p : Profile n) (μ₀ : Matching n) (K : ℕ) :=
  {r : Rotation p μ₀ // K < rotationLength r}
end StepC
end

-- PivotReversePermutationDecoration
section
open StableMarriage
open scoped BigOperators
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n}
end StepC
end

-- PivotCompatibleLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
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
private noncomputable def compatibleReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k : ℕ) (p : Profile n) : Finset (Matching n) :=
  compatibleReversePermutations
    (goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
      (forwardMaskForbiddenTargets μ flag)) p μ ρ
end StepC
end

-- PivotReverseIncrementFilter
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
private def reverseScoreIncrement {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (w j : Fin n) : ℝ := x (.inr w) j - x (.inr w) (μ.symm w)
private noncomputable def reverseIncrementCutoff (n : ℕ) (X : ℝ) : ℝ := 16 * Real.log (n : ℝ) / X
end StepC
end

-- PivotReverseFilteredCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
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
end StepC
end

-- ShortCycleChebyshev
section
open scoped BigOperators ENNReal
namespace StepC
theorem shortCycleHarmonic_le_log (k L : ℕ) (hL : 2 ≤ L) :
    (∑ j ∈ Finset.Icc 2 (min L k), (1 : ℝ) / j) ≤ Real.log (L : ℝ) := by
  have h₁ : 1 ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have he : (Finset.Icc 1 L).erase 1 = Finset.Icc 2 L := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hh := harmonic_le_one_add_log L
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  rw [← Finset.sum_erase_add (Finset.Icc 1 L) (fun j ↦ (j : ℝ)⁻¹) h₁, he,
    Nat.cast_one, inv_one] at hh
  calc
    _ ≤ ∑ j ∈ Finset.Icc 2 L, (1 : ℝ) / j :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj ↦ Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
          (Finset.mem_Icc.mp hj).2.trans (min_le_left _ _)⟩)
        (fun j _ _ ↦ by positivity)
    _ ≤ _ := by
      simp only [one_div]
      linarith only [hh]
end StepC
end

-- UniformShortCycleMoments
section
open Equiv Equiv.Perm
open scoped BigOperators
namespace StepC
variable {α : Type*} [Fintype α] [DecidableEq α]
private def shortCycleCount (L : ℕ) (σ : Perm α) : ℕ :=
  (σ.cycleType.filter (· ≤ L)).card
private abbrev CycleComplement (c : Perm α) := {x : α // x ∉ c.support}
private theorem disjoint_ofSubtype_cycleComplement (c : Perm α)
    (τ : Perm (CycleComplement c)) : Disjoint τ.ofSubtype c := by
  intro x
  by_cases hx : x ∈ c.support
  · exact Or.inl (ofSubtype_apply_of_not_mem τ (not_not_intro hx))
  · exact Or.inr (notMem_support.mp hx)
private theorem mem_cycleFactorsFinset_of_complement_mul (c : Perm α) (hc : c.IsCycle)
    (τ : Perm (CycleComplement c)) : c ∈ (τ.ofSubtype * c).cycleFactorsFinset := by
  rw [(disjoint_ofSubtype_cycleComplement c τ).cycleFactorsFinset_mul_eq_union,
    hc.cycleFactorsFinset_eq_singleton]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self c)
private theorem remainder_support_subset {c g : Perm α} (h : c ∈ g.cycleFactorsFinset) :
    (g * c⁻¹).support ≤ c.supportᶜ := by
  intro x hx
  exact Finset.mem_compl.mpr fun hxc ↦
    Finset.disjoint_left.mp (disjoint_mul_inv_of_mem_cycleFactorsFinset h).disjoint_support hx hxc
private noncomputable def markedCycleEquivComplement (c : Perm α) (hc : c.IsCycle) :
    {g : Perm α // c ∈ g.cycleFactorsFinset} ≃ Perm (CycleComplement c) :=
  (Equiv.ofBijective
    (fun τ : Perm (CycleComplement c) ↦ ⟨τ.ofSubtype * c,
      mem_cycleFactorsFinset_of_complement_mul c hc τ⟩)
    ⟨fun _ _ h ↦ ofSubtype_injective (mul_right_cancel (congrArg Subtype.val h)),
      fun g ↦ by
        have hs := remainder_support_subset g.property
        let τ : Perm (CycleComplement c) :=
          (g.val * c⁻¹).subtypePerm (fun x ↦ by
            simpa only [Finset.mem_compl] using isInvariant_of_support_le hs x)
        have hτ : τ.ofSubtype = g.val * c⁻¹ :=
          ofSubtype_subtypePerm _ (fun x hx ↦
            Finset.mem_compl.mp (hs (mem_support.mpr hx)))
        refine ⟨τ, Subtype.ext ?_⟩
        change τ.ofSubtype * c = g.val
        rw [hτ, inv_mul_cancel_right]⟩).symm
private theorem sum_markedCycle_remainders {A : Type*} [AddCommMonoid A]
    (c : Perm α) (hc : c.IsCycle) (F : Multiset ℕ → A) :
    (∑ g ∈ Finset.univ.filter (fun g : Perm α ↦ c ∈ g.cycleFactorsFinset),
      F (g * c⁻¹).cycleType) =
      ∑ τ : Perm (CycleComplement c), F τ.cycleType := by
  classical
  rw [Finset.sum_subtype (p := fun g : Perm α ↦ c ∈ g.cycleFactorsFinset) _ (by simp)]
  let e := (markedCycleEquivComplement c hc).symm
  symm
  refine Fintype.sum_equiv e _ _ fun τ ↦ ?_
  change F τ.cycleType = F ((τ.ofSubtype * c) * c⁻¹).cycleType
  rw [mul_inv_cancel_right, cycleType_ofSubtype]
open scoped Classical in
private theorem sum_cycleFactors_remainders {A : Type*} [AddCommMonoid A]
    (Q : ℕ → Prop) [DecidablePred Q] (F : Multiset ℕ → A) :
    (∑ g : Perm α, ∑ c ∈ g.cycleFactorsFinset.filter (fun c ↦ Q c.support.card),
      F (g * c⁻¹).cycleType) =
    ∑ c ∈ Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ Q c.support.card),
      ∑ τ : Perm (CycleComplement c), F τ.cycleType := by
  classical
  calc
    _ = ∑ g : Perm α, ∑ c : Perm α,
        if c ∈ g.cycleFactorsFinset ∧ Q c.support.card then F (g * c⁻¹).cycleType else 0 := by
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [← Finset.sum_filter]
      congr 1
      ext c
      simp
    _ = ∑ c : Perm α, ∑ g : Perm α,
        if c ∈ g.cycleFactorsFinset ∧ Q c.support.card then F (g * c⁻¹).cycleType else 0 :=
      Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      by_cases hc : c.IsCycle ∧ Q c.support.card
      · rw [if_pos hc]
        simp only [hc.2, and_true]
        rw [← Finset.sum_filter]
        exact sum_markedCycle_remainders c hc.1 F
      · rw [if_neg hc]
        refine Finset.sum_eq_zero fun g _ ↦ if_neg fun hg ↦ ?_
        exact hc ⟨(mem_cycleFactorsFinset_iff.mp hg.1).1, hg.2⟩
private theorem shortCycleCount_eq_card (L : ℕ) (g : Perm α) :
    shortCycleCount L g = (g.cycleFactorsFinset.filter (fun c ↦ c.support.card ≤ L)).card := by
  simp only [shortCycleCount, Equiv.Perm.cycleType, Multiset.filter_map, Multiset.card_map]
  rfl
private theorem card_cycleComplement (c : Perm α) :
    Fintype.card (CycleComplement c) = Fintype.card α - c.support.card := by
  rw [← Finset.card_compl, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun x ↦ Finset.mem_compl.symm)
open scoped Classical in
private theorem sum_shortCycleCount_eq_sum_cycleComplement (L : ℕ) :
    (∑ g : Perm α, (shortCycleCount L g : ℝ)) =
      ∑ c ∈ Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card ≤ L),
        (Nat.factorial (Fintype.card α - c.support.card) : ℝ) := by
  convert sum_cycleFactors_remainders (α := α) (· ≤ L) (fun _ ↦ (1 : ℝ)) using 1
  · refine Finset.sum_congr rfl fun g _ ↦ ?_
    simp [shortCycleCount_eq_card]
  · refine Finset.sum_congr rfl fun c _ ↦ ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_perm,
      card_cycleComplement]
open scoped Classical in
private theorem sum_cycleComplement_support_card (j : ℕ) (hj₂ : 2 ≤ j) (hjk : j ≤ Fintype.card α) :
    (∑ c ∈ Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card = j),
      (Nat.factorial (Fintype.card α - c.support.card) : ℝ)) =
      (Nat.factorial (Fintype.card α) : ℝ) * (1 / (j : ℝ)) := by
  let s := Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card = j)
  change ∑ c ∈ s, _ = _
  have hs (c : Perm α) (hc : c ∈ s) : c.support.card = j := (Finset.mem_filter.mp hc).2.2
  have he : s = Finset.univ.filter (fun c : Perm α ↦ c.cycleType = {j}) := by
    ext c
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hc, hj⟩
      rw [hc.cycleType, hj]
    · intro h
      have hc : c.IsCycle := card_cycleType_eq_one.mp (by rw [h]; simp)
      rw [hc.cycleType, Multiset.singleton_inj] at h
      exact ⟨hc, h⟩
  have hm : s.card * (Nat.factorial (Fintype.card α - j) * j) =
      Nat.factorial (Fintype.card α) := by
    rw [he]
    simpa [hjk, hj₂] using card_of_cycleType_mul_eq α ({j} : Multiset ℕ)
  have hmR : (s.card : ℝ) * ((Nat.factorial (Fintype.card α - j) : ℝ) * (j : ℝ)) =
      (Nat.factorial (Fintype.card α) : ℝ) := by exact_mod_cast hm
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  calc
    _ = ∑ _ ∈ s, (Nat.factorial (Fintype.card α - j) : ℝ) :=
      Finset.sum_congr rfl fun c hc ↦ by rw [hs c hc]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, eq_div_iff hjR, mul_assoc]
      exact hmR
private theorem sum_shortCycleCount_general (L : ℕ) :
    (∑ g : Perm α, (shortCycleCount L g : ℝ)) =
      (Nat.factorial (Fintype.card α) : ℝ) *
        ∑ j ∈ Finset.Icc 2 (min L (Fintype.card α)), (1 : ℝ) / j := by
  classical
  let s := Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card ≤ L)
  let t := Finset.Icc 2 (min L (Fintype.card α))
  have hmaps (c : Perm α) (hc : c ∈ s) : c.support.card ∈ t := by
    obtain ⟨hcyc, hL⟩ := (Finset.mem_filter.mp hc).2
    exact Finset.mem_Icc.mpr ⟨hcyc.two_le_card_support, le_min hL (Finset.card_le_univ _)⟩
  rw [sum_shortCycleCount_eq_sum_cycleComplement]
  change (∑ c ∈ s, (Nat.factorial (Fintype.card α - c.support.card) : ℝ)) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  obtain ⟨hj₂, hmin⟩ := Finset.mem_Icc.mp hj
  have hjk : j ≤ Fintype.card α := hmin.trans (min_le_right _ _)
  have hjL : j ≤ L := hmin.trans (min_le_left _ _)
  have hfiber : s.filter (fun c ↦ c.support.card = j) =
      Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card = j) := by
    ext c
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hc, _⟩, h⟩
      exact ⟨hc, h⟩
    · rintro ⟨hc, rfl⟩
      exact ⟨⟨hc, hjL⟩, rfl⟩
  rw [hfiber]
  exact sum_cycleComplement_support_card (α := α) j hj₂ hjk
theorem sum_shortCycleCount (k L : ℕ) :
    (∑ g : Perm (Fin k), (shortCycleCount L g : ℝ)) =
      (Nat.factorial k : ℝ) * ∑ j ∈ Finset.Icc 2 (min L k), (1 : ℝ) / j := by
  simpa only [Fintype.card_fin] using sum_shortCycleCount_general (α := Fin k) L
private theorem shortCycleCount_remove {g c : Perm α} {L : ℕ}
    (hc : c ∈ g.cycleFactorsFinset) (hL : c.support.card ≤ L) :
    (shortCycleCount L (g * c⁻¹) : ℝ) = (shortCycleCount L g : ℝ) - 1 := by
  have hd := (disjoint_mul_inv_of_mem_cycleFactorsFinset hc).cycleType_mul
  rw [inv_mul_cancel_right, (mem_cycleFactorsFinset_iff.mp hc).1.cycleType] at hd
  have heq : shortCycleCount L g = shortCycleCount L (g * c⁻¹) + 1 := by
    simp [shortCycleCount, hd, Multiset.filter_add, Multiset.filter_singleton, hL]
  rw [heq, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
open scoped Classical in
private theorem sum_shortCyclePairs_eq_sum_cycleComplement (L : ℕ) :
    (∑ g : Perm α, (shortCycleCount L g : ℝ) * ((shortCycleCount L g : ℝ) - 1)) =
      ∑ c ∈ Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card ≤ L),
        ∑ τ : Perm (CycleComplement c), (shortCycleCount L τ : ℝ) := by
  calc
    _ = ∑ g : Perm α, ∑ c ∈ g.cycleFactorsFinset.filter (fun c ↦ c.support.card ≤ L),
        (shortCycleCount L (g * c⁻¹) : ℝ) := by
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      have hconst : ∀ c ∈ g.cycleFactorsFinset.filter (fun c ↦ c.support.card ≤ L),
          (shortCycleCount L (g * c⁻¹) : ℝ) = (shortCycleCount L g : ℝ) - 1 := by
        intro c hc
        obtain ⟨hcg, hcL⟩ := Finset.mem_filter.mp hc
        exact shortCycleCount_remove hcg hcL
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, ← shortCycleCount_eq_card]
    _ = _ := sum_cycleFactors_remainders (· ≤ L) (fun t ↦ ((t.filter (· ≤ L)).card : ℝ))
private theorem shortCycleHarmonic_mono (L k k' : ℕ) (h : k ≤ k') :
    (∑ j ∈ Finset.Icc 2 (min L k), (1 : ℝ) / j) ≤
      ∑ j ∈ Finset.Icc 2 (min L k'), (1 : ℝ) / j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨h₂, hjmax⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨h₂, hjmax.trans (min_le_min_left L h)⟩
  · intro j _ _
    positivity
private theorem sum_shortCyclePairs_general (L : ℕ) :
    (∑ g : Perm α, (shortCycleCount L g : ℝ) * ((shortCycleCount L g : ℝ) - 1)) ≤
      (Nat.factorial (Fintype.card α) : ℝ) *
        (∑ j ∈ Finset.Icc 2 (min L (Fintype.card α)), (1 : ℝ) / j) ^ 2 := by
  classical
  let s := Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card ≤ L)
  let H : ℝ := ∑ j ∈ Finset.Icc 2 (min L (Fintype.card α)), (1 : ℝ) / j
  rw [sum_shortCyclePairs_eq_sum_cycleComplement]
  change (∑ c ∈ s, ∑ τ : Perm (CycleComplement c), (shortCycleCount L τ : ℝ)) ≤
    (Nat.factorial (Fintype.card α) : ℝ) * H ^ 2
  calc
    _ ≤ ∑ c ∈ s, (Nat.factorial (Fintype.card α - c.support.card) : ℝ) * H := by
      refine Finset.sum_le_sum fun c _ ↦ ?_
      rw [sum_shortCycleCount_general, card_cycleComplement]
      exact mul_le_mul_of_nonneg_left (shortCycleHarmonic_mono L _ _ (Nat.sub_le _ _)) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← sum_shortCycleCount_eq_sum_cycleComplement (α := α) L,
        sum_shortCycleCount_general]
      change (Nat.factorial (Fintype.card α) : ℝ) * H * H = _
      rw [pow_two, mul_assoc]
theorem sum_shortCycleCount_mul_sub_one_le (k L : ℕ) :
    (∑ g : Perm (Fin k), (shortCycleCount L g : ℝ) * ((shortCycleCount L g : ℝ) - 1)) ≤
      (Nat.factorial k : ℝ) * (∑ j ∈ Finset.Icc 2 (min L k), (1 : ℝ) / j) ^ 2 := by
  simpa only [Fintype.card_fin] using sum_shortCyclePairs_general (α := Fin k) L
end StepC
end

-- PivotScoreLock
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
end StepC
end

-- PivotForwardExposureReveal
section
open MeasureTheory Set StableMarriage
namespace StepC
private def forwardRevealExposureEvent {n : ℕ} (ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (ForwardRevealedMaleScores flag) :=
  {v | ρ.IsCycle ∧ ∀ m, ρ m ≠ m →
    ∃ q : ForwardActiveCellIndex flag, q.val.val = (m, ρ m) ∧
      ∀ t : ForwardActiveCellIndex flag, t.val.val.1 = m → v q ≤ v t}
end StepC
end

-- PivotPairToggle
section
open StableMarriage
open scoped BigOperators
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n} {hopt : IsManOptimal p μ₀}
  {K : ℕ} {r : Rotation p μ₀}
namespace PivotDecoration
private def removedLabels (D : PivotDecoration hopt K r) : Set (Rotation p μ₀) :=
  Subtype.val '' (↑D.removed :
    Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val))
theorem matching_eliminated (D : PivotDecoration hopt K r) :
    eliminatedRotations p μ₀ D.matching.val =
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt r).val \ D.removedLabels :=
  eliminatedRotations_undoMaximalSubsetEmbedding hopt
    (singletonRotationAnchor hopt r).property D.removed
private noncomputable def eraseRemovedLabel (D : PivotDecoration hopt K r) (γ : Rotation p μ₀) :
    PivotDecoration hopt K r := by
  classical
  let E := D.removed.filter (fun s ↦ s.val ≠ γ)
  have hE : E ⊆ D.removed := Finset.filter_subset _ _
  refine ⟨E, ?_, ?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun _ _ _ ↦ Nat.zero_le _)).trans D.totalLength_le
  · apply (pivot_isExposedAt_undo_iff hopt r E).mpr
    rintro _ ⟨s, hs, rfl⟩
    exact (pivot_isExposedAt_undo_iff hopt r D.removed).mp D.pivot_exposed _
      ⟨s, hE hs, rfl⟩
end PivotDecoration
private abbrev PivotCode (hopt : IsManOptimal p μ₀) (K : ℕ) :=
  Σ r : LongPivot p μ₀ K, PivotDecoration hopt K r.val
private structure ResidualPivotPair (hopt : IsManOptimal p μ₀) (K : ℕ) where
  early : PivotCode hopt K
  late : PivotCode hopt K
  pivot_lt : early.1.val < late.1.val
  shared : ∃ γ ∈ late.2.removedLabels,
    γ ∈ eliminatedRotations p μ₀ (singletonRotationAnchor hopt early.1.val).val
namespace ResidualPivotPair
private noncomputable def sharedLabel (R : ResidualPivotPair hopt K) : Rotation p μ₀ :=
  Classical.choose R.shared
private noncomputable def toggledEarly (R : ResidualPivotPair hopt K) : PivotCode hopt K :=
  ⟨R.early.1, R.early.2.eraseRemovedLabel R.sharedLabel⟩
theorem early_anchor_ideal_subset_late_anchor (R : ResidualPivotPair hopt K) :
    eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val ⊆
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.late.1.val).val := by
  rw [eliminatedRotations_singletonRotationAnchor,
    eliminatedRotations_singletonRotationAnchor]
  exact fun _ hs hls ↦ hs (R.pivot_lt.le.trans hls)
theorem toggle_early_ideal_diff_late (R : ResidualPivotPair hopt K) :
    eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
        eliminatedRotations p μ₀ R.late.2.matching.val =
      (R.late.2.removedLabels ∩
        eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val) \
          R.toggledEarly.2.removedLabels := by
  rw [PivotDecoration.matching_eliminated, PivotDecoration.matching_eliminated]
  ext s
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨ha, he⟩, hn⟩
    refine ⟨⟨?_, ha⟩, he⟩
    by_contra h
    exact hn ⟨R.early_anchor_ideal_subset_late_anchor ha, h⟩
  · rintro ⟨⟨hl, ha⟩, he⟩
    exact ⟨⟨ha, he⟩, fun h ↦ h.2 hl⟩
theorem isExposedAt_late_of_mem_toggle_early_ideal_diff_late (R : ResidualPivotPair hopt K)
    {s : Rotation p μ₀} (hs : s ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
      eliminatedRotations p μ₀ R.late.2.matching.val) :
    s.IsExposedAt R.late.2.matching.val := by
  rw [R.toggle_early_ideal_diff_late] at hs
  exact (R.late.2.isExposedAt_matching_iff s).mpr (Or.inr hs.1.1)
private noncomputable def shortOrientationLabels (R : ResidualPivotPair hopt K) :
    Finset (Rotation p μ₀) := by
  classical
  exact (R.late.2.removed.filter fun s ↦
    s.val ∈ eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val ∧
    s.val ∉ R.toggledEarly.2.removedLabels).map ⟨Subtype.val, Subtype.val_injective⟩
theorem coe_shortOrientationLabels (R : ResidualPivotPair hopt K) :
    (↑R.shortOrientationLabels : Set (Rotation p μ₀)) =
      eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
        eliminatedRotations p μ₀ R.late.2.matching.val := by
  classical
  rw [R.toggle_early_ideal_diff_late]
  ext s
  simp only [shortOrientationLabels, Finset.mem_coe, Finset.mem_map, Finset.mem_filter,
    Function.Embedding.coeFn_mk, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · rintro ⟨t, ⟨ht, ha, he⟩, rfl⟩
    exact ⟨⟨⟨t, ht, rfl⟩, ha⟩, he⟩
  · rintro ⟨⟨⟨t, ht, rfl⟩, ha⟩, he⟩
    exact ⟨t, ⟨ht, ha, he⟩, rfl⟩
private noncomputable def shortOrientationMen (R : ResidualPivotPair hopt K) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦
    p.manRank m (R.late.2.matching.val m) < p.manRank m (R.toggledEarly.2.matching.val m)
private noncomputable def longOrientationMen (R : ResidualPivotPair hopt K) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦
    p.manRank m (R.toggledEarly.2.matching.val m) < p.manRank m (R.late.2.matching.val m)
private theorem exists_diff_label_moving_of_rank_lt {A B : Matching n}
    (hopt : IsManOptimal p μ₀) (hA : IsStable p A) (hB : IsStable p B)
    (hAB : MenWeaklyPrefer p A B) {m : Fin n}
    (hm : p.manRank m (A m) < p.manRank m (B m)) :
    ∃ s : Rotation p μ₀,
      s ∈ eliminatedRotations p μ₀ B \ eliminatedRotations p μ₀ A ∧
        s.val.cycle m ≠ m ∧ rotationLabelNewPartner s.val m = some (B m) := by
  obtain ⟨us, hfirst⟩ := exists_rotationSequence_of_manOptimal hopt hA
  obtain ⟨vs, hnext⟩ := exists_rotationSequence_of_menWeaklyPrefer hA hB hAB
  rcases hnext.partner_eq_or_label_newPartner m with he | ⟨l, hl, hmove, hnew⟩
  · exact (hm.ne (congrArg (p.manRank m) he)).elim
  · have hall := hfirst.append hnext
    have hlall : l ∈ rotationLabels μ₀ (us ++ vs) := by
      rw [hfirst.rotationLabels_append]
      exact List.mem_append_right _ hl
    let s : Rotation p μ₀ := ⟨l, B, us ++ vs, hall, hlall⟩
    refine ⟨s, ⟨hall.mem_eliminatedRotations_iff.mpr hlall, ?_⟩, hmove, hnew⟩
    intro hmem
    exact hm.not_ge ((mem_eliminatedRotations_iff_newRank_le hopt hA hmove hnew).mp hmem)
theorem shortOrientationMen_subset (R : ResidualPivotPair hopt K) :
    R.shortOrientationMen ⊆ R.shortOrientationLabels.biUnion (fun s ↦ s.val.cycle.support) := by
  classical
  intro m hm
  let A := R.toggledEarly.2.matching
  let B := R.late.2.matching
  obtain ⟨J, hJ, hIJ⟩ := exists_eliminatedRotations_union hopt A.property B.property
  have hAJ : MenWeaklyPrefer p A.val J := (eliminatedRotations_subset_iff hopt A.property hJ).mp
    (by rw [hIJ]; exact Set.subset_union_left)
  have hBJ : MenWeaklyPrefer p B.val J := (eliminatedRotations_subset_iff hopt B.property hJ).mp
    (by rw [hIJ]; exact Set.subset_union_right)
  have hm' : p.manRank m (B.val m) < p.manRank m (A.val m) := (Finset.mem_filter.mp hm).2
  obtain ⟨s, hs, hmove, _⟩ := exists_diff_label_moving_of_rank_lt hopt B.property hJ hBJ
    (hm'.trans_le (hAJ m))
  rw [hIJ] at hs
  have hmem : s ∈ eliminatedRotations p μ₀ A.val \ eliminatedRotations p μ₀ B.val :=
    ⟨hs.1.resolve_right hs.2, hs.2⟩
  exact Finset.mem_biUnion.mpr
    ⟨s, by simpa only [← Finset.mem_coe, R.coe_shortOrientationLabels] using hmem,
      Equiv.Perm.mem_support.mpr hmove⟩
private theorem exists_rank_max_and_eliminated_union {A B : Matching n}
    (hopt : IsManOptimal p μ₀) (hA : IsStable p A) (hB : IsStable p B) :
    ∃ J, IsStable p J ∧ (∀ m, p.manRank m (J m) =
      max (p.manRank m (A m)) (p.manRank m (B m))) ∧
      eliminatedRotations p μ₀ J =
        eliminatedRotations p μ₀ A ∪ eliminatedRotations p μ₀ B := by
  obtain ⟨J, hJ, hIJ⟩ := exists_eliminatedRotations_union hopt hA hB
  obtain ⟨L, hL, hLrank⟩ := exists_stable_manRank_max hA hB
  have hAL : MenWeaklyPrefer p A L := fun m ↦ by rw [hLrank]; exact le_max_left _ _
  have hBL : MenWeaklyPrefer p B L := fun m ↦ by rw [hLrank]; exact le_max_right _ _
  have hJL : MenWeaklyPrefer p J L := (eliminatedRotations_subset_iff hopt hJ hL).mp
    (by
      rw [hIJ]
      exact Set.union_subset ((eliminatedRotations_subset_iff hopt hA hL).mpr hAL)
        ((eliminatedRotations_subset_iff hopt hB hL).mpr hBL))
  have hAJ : MenWeaklyPrefer p A J := (eliminatedRotations_subset_iff hopt hA hJ).mp
    (by rw [hIJ]; exact Set.subset_union_left)
  have hBJ : MenWeaklyPrefer p B J := (eliminatedRotations_subset_iff hopt hB hJ).mp
    (by rw [hIJ]; exact Set.subset_union_right)
  refine ⟨J, hJ, fun m ↦ le_antisymm ?_ (max_le (hAJ m) (hBJ m)), hIJ⟩
  simpa only [hLrank] using hJL m
private noncomputable def relativePermutation (R : ResidualPivotPair hopt K) : Equiv.Perm (Fin n) :=
  R.toggledEarly.2.matching.val.trans R.late.2.matching.val.symm
theorem relativePermutation_apply_of_mem_shortLabel (R : ResidualPivotPair hopt K)
    {s : Rotation p μ₀} (hs : s ∈ R.shortOrientationLabels)
    {m : Fin n} (hm : s.val.cycle m ≠ m) :
    R.relativePermutation m = s.val.cycle m := by
  let A := R.toggledEarly.2.matching
  let B := R.late.2.matching
  have hsD : s ∈ eliminatedRotations p μ₀ A.val \ eliminatedRotations p μ₀ B.val :=
    R.coe_shortOrientationLabels ▸ (Finset.mem_coe.mpr hs)
  have hE : s.IsExposedAt B.val := R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late hsD
  obtain ⟨J, hJ, hJrank, hIJ⟩ := exists_rank_max_and_eliminated_union hopt A.property B.property
  have hBJ : MenWeaklyPrefer p B.val J := (eliminatedRotations_subset_iff hopt B.property hJ).mp
    (by rw [hIJ]; exact Set.subset_union_right)
  have hJmem : s ∈ eliminatedRotations p μ₀ J := hIJ ▸ Or.inl hsD.1
  have hnew := rotationLabelNewPartner_eq (μ := B.val) hm
  rw [hE.2] at hnew
  have hle := (mem_eliminatedRotations_iff_newRank_le hopt hJ hm hnew).mp hJmem
  have hlt := (hE.1.manRank_lt_eliminate_of_moved hm).trans_le hle
  obtain ⟨t, ht, htm, htn⟩ := exists_diff_label_moving_of_rank_lt hopt B.property hJ hBJ hlt
  rw [hIJ] at ht
  have hEt : t.IsExposedAt B.val :=
    R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late ⟨ht.1.resolve_right ht.2, ht.2⟩
  have heq : t = s := by
    by_contra hts
    have hcycles : s.val.cycle ≠ t.val.cycle := fun he ↦ hts (Subtype.ext
      (hEt.2.symm.trans ((congrArg (rotationLabel B.val) he).symm.trans hE.2)))
    exact htm (hE.1.disjoint_moved hEt.1 hcycles m hm)
  rw [heq] at htn
  have hJpartner : eliminateRotation B.val s.val.cycle m = J m :=
    Option.some.inj (hnew.symm.trans htn)
  rw [hJrank] at hlt
  have hAgt : p.manRank m (B.val m) < p.manRank m (A.val m) :=
    (lt_max_iff.mp hlt).resolve_right (lt_irrefl _)
  have hApartner : A.val m = J m := (p.manRank m).injective (by
    rw [hJrank, max_eq_left hAgt.le])
  change B.val.symm (A.val m) = _
  rw [hApartner, ← hJpartner, eliminateRotation_apply, Equiv.symm_apply_apply]
theorem cycle_mem_relativePermutation_cycleFactors (R : ResidualPivotPair hopt K)
    {s : Rotation p μ₀} (hs : s ∈ R.shortOrientationLabels) :
    s.val.cycle ∈ R.relativePermutation.cycleFactorsFinset := by
  have hsD : s ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
      eliminatedRotations p μ₀ R.late.2.matching.val :=
    R.coe_shortOrientationLabels ▸ (Finset.mem_coe.mpr hs)
  have hE := R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late hsD
  exact Equiv.Perm.mem_cycleFactorsFinset_iff.mpr ⟨(IsExposedRotation.isCycle hE.1), fun _ hm ↦
    (R.relativePermutation_apply_of_mem_shortLabel hs (Equiv.Perm.mem_support.mp hm)).symm⟩
theorem exists_shortLabel_of_cycleFactor (R : ResidualPivotPair hopt K)
    {c : Equiv.Perm (Fin n)} (hc : c ∈ R.relativePermutation.cycleFactorsFinset)
    {m : Fin n} (hm : m ∈ c.support) (hmshort : m ∈ R.shortOrientationMen) :
    ∃ s ∈ R.shortOrientationLabels, s.val.cycle = c := by
  classical
  obtain ⟨s, hs, hms⟩ := Finset.mem_biUnion.mp (R.shortOrientationMen_subset hmshort)
  exact ⟨s, hs, (Equiv.Perm.cycle_is_cycleOf hms
    (R.cycle_mem_relativePermutation_cycleFactors hs)).trans
      (Equiv.Perm.cycle_is_cycleOf hm hc).symm⟩
end ResidualPivotPair
end StepC
end

-- PivotFilteredDecoration
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
variable {n : ℕ} {x : ScoreProfile n} {μ₀ : Matching n}
  {hopt : IsManOptimal (profileOfScores x) μ₀} {K : ℕ}
  {r : Rotation (profileOfScores x) μ₀}
end StepC
end

-- PivotEligibleRevealControls
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
private def reverseDiagonalMaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).1
private def eligiblePivotRevealSet {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (D : ℝ) :
    Set (ForwardRevealedMaleScores flag) :=
  {v | (∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ) ∧
    (∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement d flag ρ v m) ∧
    (∑ m ∈ ρ.support, forwardPivotIncrement d flag ρ v m) ≤ D}
namespace ReverseMaskGeometry
variable {n : ℕ} {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
  {μ ρ : Matching n} {s u p : ℝ}
end ReverseMaskGeometry
end StepC
end

-- PivotSpouseBandMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
private def pivotDiagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).2
private def pivotBaseDiagonalBand (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | let X := reverseDiagonalMaleTotal d
       let Y := pivotDiagonalFemaleTotal d
       (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
       2 ≤ Y ∧ Y ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧ (n : ℝ) / 128 ≤ X * Y ∧
       (∀ i, (diagonalPairAt d i).2 / Y ≤ 12 * Real.log n / n) ∧
       ∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (Y - 1)}
end StepC
end

-- ForestDeterministic
section
open scoped BigOperators Classical
namespace StepC
private def RealizesDirectedCycle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) (σ : Equiv.Perm ι) : Prop :=
  σ.IsCycle ∧ ∀ i ∈ σ.support, f i = some (σ i)
end StepC
end

-- ForwardSuccessorRowLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
private noncomputable def normalizedStableScoreRowLaw {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n) :
    Measure ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  (stableScoreRowLaw d i univ)⁻¹ • stableScoreRowLaw d i
theorem isSuccessor_of_scoreRowSuccessorEvent {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (ht : ∀ row, Function.Injective (x row))
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (h : offDiagonalRowsEquiv n (splitScorePairs μ x).2 i ∈
      scoreRowSuccessorEvent (splitScorePairs μ x).1 i j) :
    IsSuccessor (profileOfScores x) μ i (μ j.val) := by
  have hcell (a : {a : Fin n // i ≠ a}) :
      offDiagonalRowsEquiv n (splitScorePairs μ x).2 i a =
        (x (.inl i) (μ a.val), x (.inr (μ a.val)) i) :=
    splitScorePairs_offDiagonal_apply μ x ⟨(i, a.val), a.property⟩
  simp only [scoreRowSuccessorEvent, Set.mem_ofPred_eq, hcell, diagonalPairAt_splitScorePairs] at h
  have hman (w w' : Fin n) : (profileOfScores x).manRank i w < (profileOfScores x).manRank i w'
      ↔ x (.inl i) w < x (.inl i) w' :=
    rankPermutation_lt_iff (ht (.inl i)) w w'
  have hwoman (w m m' : Fin n) :
      (profileOfScores x).womanRank w m < (profileOfScores x).womanRank w m'
        ↔ x (.inr w) m < x (.inr w) m' :=
    rankPermutation_lt_iff (ht (.inr w)) m m'
  refine (IsSuccessor.mk (⟨(hman _ _).2 h.1, ?_⟩) (?_))
  · simpa only [Equiv.symm_apply_apply] using (hwoman (μ j.val) i j.val).2 h.2.1
  · intro w hw
    apply le_of_not_gt
    intro hlt
    have hi : i ≠ μ.symm w := by
      intro hi
      have heq : μ i = w := by rw [hi, Equiv.apply_symm_apply]
      exact (ne_of_lt hw.1) (congrArg ((profileOfScores x).manRank i) heq)
    let k : {k : Fin n // i ≠ k} := ⟨μ.symm w, hi⟩
    have hk : k ≠ j := by
      intro heq
      have hwj : w = μ j.val := by
        have hval := congrArg (fun k : {k : Fin n // i ≠ k} ↦ μ k.val) heq
        simpa only [k, Equiv.apply_symm_apply] using hval
      exact (ne_of_lt hlt) (congrArg ((profileOfScores x).manRank i) hwj)
    have hlt' : x (.inl i) w < x (.inl i) (μ j.val) := (hman _ _).1 hlt
    have hel' : x (.inr w) i < x (.inr w) (μ.symm w) := (hwoman _ _ _).1 hw.2
    exact h.2.2 ⟨k, hk⟩ (by simpa only [k, Equiv.apply_symm_apply] using And.intro hlt' hel')
end StepC
end

-- ForwardSuccessorOutcome
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
private def uniqueScoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (j : {j : Fin n // i ≠ j}) : Set ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  scoreRowSuccessorEvent d i j ∩ ⋂ k : {k : {k : Fin n // i ≠ k} // k ≠ j},
    (scoreRowSuccessorEvent d i k.val)ᶜ
private theorem measurableSet_uniqueScoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    MeasurableSet (uniqueScoreRowSuccessorEvent d i j) :=
  (measurableSet_scoreRowSuccessorEvent d i j).inter
    (MeasurableSet.iInter fun k ↦ (measurableSet_scoreRowSuccessorEvent d i k.val).compl)
private theorem uniqueScoreRowSuccessorEvent_of_unique {n : ℕ} {d : DiagonalScorePairs n}
    {i : Fin n} {r : {j : Fin n // i ≠ j} → ℝ × ℝ} {j : {j : Fin n // i ≠ j}}
    (hj : r ∈ scoreRowSuccessorEvent d i j)
    (huniq : ∀ k, r ∈ scoreRowSuccessorEvent d i k → k = j) :
    r ∈ uniqueScoreRowSuccessorEvent d i j :=
  ⟨hj, Set.mem_iInter.mpr fun k hk ↦ k.property (huniq k.val hk)⟩
private theorem uniqueScoreRowSuccessorEvent_unique {n : ℕ} {d : DiagonalScorePairs n}
    {i : Fin n} {r : {j : Fin n // i ≠ j} → ℝ × ℝ} {j k : {j : Fin n // i ≠ j}}
    (hj : r ∈ uniqueScoreRowSuccessorEvent d i j)
    (hk : r ∈ scoreRowSuccessorEvent d i k) : k = j := by
  by_contra hne
  exact (Set.mem_iInter.mp hj.2 ⟨k, hne⟩) hk
private noncomputable def forwardSuccessorOutcome {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (r : {j : Fin n // i ≠ j} → ℝ × ℝ) : Option (Fin n) := by
  classical
  exact if h : ∃ j, r ∈ uniqueScoreRowSuccessorEvent d i j then some h.choose.val else none
private theorem forwardSuccessorOutcome_eq_some_iff_unique {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (r : {j : Fin n // i ≠ j} → ℝ × ℝ) (j : {j : Fin n // i ≠ j}) :
    forwardSuccessorOutcome d i r = some j.val ↔ r ∈ uniqueScoreRowSuccessorEvent d i j := by
  classical
  unfold forwardSuccessorOutcome
  split
  · rename_i h
    constructor
    · intro he
      have hej : h.choose = j := Subtype.ext (Option.some.inj he)
      simpa only [hej] using h.choose_spec
    · intro hj
      rw [uniqueScoreRowSuccessorEvent_unique hj h.choose_spec.1]
  · rename_i h
    constructor
    · intro he
      cases he
    · exact fun hj ↦ (h ⟨j, hj⟩).elim
theorem forwardSuccessorOutcome_ne_some_self {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (r : {j : Fin n // i ≠ j} → ℝ × ℝ) : forwardSuccessorOutcome d i r ≠ some i := by
  classical
  unfold forwardSuccessorOutcome
  split
  · rename_i h
    exact fun he ↦ h.choose.property (Option.some.inj he).symm
  · intro he
    cases he
theorem measurable_forwardSuccessorOutcome {n : ℕ} [MeasurableSpace (Option (Fin n))]
    (d : DiagonalScorePairs n) (i : Fin n) : Measurable (forwardSuccessorOutcome d i) := by
  apply measurable_to_countable'
  intro o
  cases o with
  | none =>
    have hset : forwardSuccessorOutcome d i ⁻¹' {none} =
        (⋃ j, uniqueScoreRowSuccessorEvent d i j)ᶜ := by
      classical
      ext r
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion]
      unfold forwardSuccessorOutcome
      split <;> simp_all
    rw [hset]
    exact (MeasurableSet.iUnion (measurableSet_uniqueScoreRowSuccessorEvent d i)).compl
  | some j =>
    by_cases hj : i = j
    · subst j
      have hset : forwardSuccessorOutcome d i ⁻¹' {some i} = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun r ↦ forwardSuccessorOutcome_ne_some_self d i r
      rw [hset]
      exact MeasurableSet.empty
    · have hset : forwardSuccessorOutcome d i ⁻¹' {some j} =
          uniqueScoreRowSuccessorEvent d i ⟨j, hj⟩ :=
        Set.ext fun r ↦ forwardSuccessorOutcome_eq_some_iff_unique d i r ⟨j, hj⟩
      rw [hset]
      exact measurableSet_uniqueScoreRowSuccessorEvent d i ⟨j, hj⟩
private theorem scoreRowSuccessorEvent_unique_of_injective {n : ℕ} {d : DiagonalScorePairs n}
    {i : Fin n} {r : {j : Fin n // i ≠ j} → ℝ × ℝ}
    (hinj : Function.Injective (fun k ↦ (r k).1))
    {j k : {j : Fin n // i ≠ j}} (hj : r ∈ scoreRowSuccessorEvent d i j)
    (hk : r ∈ scoreRowSuccessorEvent d i k) : k = j := by
  by_contra hne
  have hle : (r j).1 ≤ (r k).1 :=
    le_of_not_gt fun h ↦ hj.2.2 ⟨k, hne⟩ ⟨h, hk.2.1⟩
  have hge : (r k).1 ≤ (r j).1 :=
    le_of_not_gt fun h ↦ hk.2.2 ⟨j, fun e ↦ hne e.symm⟩ ⟨h, hj.2.1⟩
  exact hne (hinj (le_antisymm hge hle))
theorem forwardSuccessorOutcome_eq_some_iff {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (r : {j : Fin n // i ≠ j} → ℝ × ℝ) (j : {j : Fin n // i ≠ j})
    (hinj : Function.Injective (fun k ↦ (r k).1)) :
    forwardSuccessorOutcome d i r = some j.val ↔ r ∈ scoreRowSuccessorEvent d i j :=
  (forwardSuccessorOutcome_eq_some_iff_unique d i r j).trans
    ⟨fun h ↦ h.1, fun hj ↦ uniqueScoreRowSuccessorEvent_of_unique hj fun _ hk ↦
      scoreRowSuccessorEvent_unique_of_injective hinj hj hk⟩
private theorem ae_injective_unitScoreLaw_pi (ι : Type*) [Fintype ι] :
    ∀ᵐ x ∂(Measure.pi fun _ : ι ↦ unitScoreLaw), Function.Injective (x : ι → ℝ) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hpres := measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) ↦ unitScoreLaw) e
  filter_upwards [hpres.quasiMeasurePreserving.ae
    (ae_injective_iid unitScoreLaw (Fintype.card ι))] with x hx
  intro i j hij
  apply e.injective
  apply hx
  simpa only [MeasurableEquiv.piCongrLeft_apply_apply] using hij
theorem ae_injective_fst_normalizedStableScoreRowLaw {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n) :
    ∀ᵐ r ∂normalizedStableScoreRowLaw d i,
      Function.Injective (fun k ↦ (r k).1) := by
  let ι := {j : Fin n // i ≠ j}
  let ν := Measure.pi fun _ : ι ↦ unitScorePairLaw
  have hm : Measure.map Prod.fst unitScorePairLaw = unitScoreLaw := by
    simp [unitScorePairLaw]
  have hmap : ν.map (fun (r : ι → ℝ × ℝ) k ↦ (r k).1) =
      Measure.pi fun _ : ι ↦ unitScoreLaw := by
    unfold ν
    rw [Measure.pi_map_pi (fun _ ↦ measurable_fst.aemeasurable)]
    simp only [hm]
  have hpres : MeasurePreserving (fun (r : ι → ℝ × ℝ) k ↦ (r k).1) ν
      (Measure.pi fun _ : ι ↦ unitScoreLaw) :=
    ⟨measurable_pi_iff.2 fun k ↦ measurable_fst.comp (measurable_pi_apply k), hmap⟩
  have hν : ∀ᵐ r ∂ν, Function.Injective (fun k ↦ (r k).1) :=
    hpres.quasiMeasurePreserving.ae (ae_injective_unitScoreLaw_pi ι)
  have hsub : stableScoreRowLaw d i ≤ ν := by
    rw [stableScoreRowLaw, ← Measure.restrict_pi_pi]
    exact Measure.restrict_le_self
  exact (Measure.smul_absolutelyContinuous.trans
    (Measure.absolutelyContinuous_of_le hsub)).ae_le hν
end StepC
end

-- PivotForwardRowDeficit
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepC
end StepC
end

-- PivotForwardForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
private def IsSoleForwardExposedRotation {n : ℕ} (p : Profile n) (μ σ : Matching n) : Prop :=
  IsExposedRotation p μ σ ∧ ∀ τ, IsExposedRotation p μ τ → τ = σ
end StepC
end

-- PivotLocalEligibility
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepC
private def certifiedSet {α : Type} [MeasurableSpace α] {t : Set α} (_ : MeasurableSet t) := t
private def LocalPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) : Prop :=
  d ∈ certifiedSet (MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag)
private noncomputable def localPivotIncrementCap {n : ℕ} (B : ℝ) (d : DiagonalScorePairs n) : ℝ :=
  B * Real.sqrt (n : ℝ) / pivotDiagonalFemaleTotal d
private def IsLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (x : ScoreProfile n)
    (μ ρ : Matching n) : Prop :=
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  LocalPivotGeometry b A B μ ρ z.1 flag ∧
    (forwardRevealWithColumns flag z.2).1 ∈
      eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)
theorem measurableSet_localPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurableSet {d : DiagonalScorePairs n | LocalPivotGeometry b A B μ ρ d flag} := MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag

end StepC
end

-- PivotMarkedDecorationCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
variable {n : ℕ}
private noncomputable def markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun σ ↦ σ.support.card ≤ K ∧
    σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x
private noncomputable def localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsLocallyEligiblePivot b A B x μ ρ then
    ((markedFilteredChoices μ ρ (forwardMaskOfScores (splitScorePairs μ x).1
      (splitScorePairs μ x).2) K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x).card : ℝ)
    else 0
section MatchingEndpoints
variable {x : ScoreProfile n} {μ₀ μ ρ σ : Matching n}
  {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
end MatchingEndpoints
theorem exists_singletonRotationAnchor_of_soleForwardExposed {p : Profile n}
    {μ₀ μ ρ : Matching n} (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (hsole : IsSoleForwardExposedRotation p μ ρ) :
    ∃ r : Rotation p μ₀, (singletonRotationAnchor hopt r).val = μ ∧ r.val.cycle = ρ := by
  let r := rotationOfExposed hopt hμ hsole.1
  refine ⟨r, ?_, rfl⟩
  have hanchor := (eq_singletonRotationAnchor_iff hopt r ⟨μ, hμ⟩).mpr fun s ↦ by
    constructor
    · intro hs
      exact Subtype.ext (hs.2.symm.trans (congrArg (rotationLabel μ) (hsole.2 _ hs.1)))
    · rintro rfl
      exact ⟨hsole.1, rfl⟩
  exact (congrArg Subtype.val hanchor).symm
end StepC
end

-- PivotSharedReverse
section
open StableMarriage
namespace StepC
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n}
theorem menWeaklyPrefer_singletonRotationAnchor_iff
    (hopt : IsManOptimal p μ₀) (r s : Rotation p μ₀) :
    MenWeaklyPrefer p (singletonRotationAnchor hopt r).val (singletonRotationAnchor hopt s).val
      ↔ r ≤ s := by
  rw [← eliminatedRotations_subset_iff hopt (singletonRotationAnchor hopt r).property
      (singletonRotationAnchor hopt s).property,
    eliminatedRotations_singletonRotationAnchor, eliminatedRotations_singletonRotationAnchor]
  constructor
  · intro h
    by_contra hrs
    exact (h (show s ∈ (Set.Ici r)ᶜ from hrs)) (Set.mem_Ici.mpr le_rfl)
  · exact fun h _ ha hb ↦ ha (h.trans hb)
section MarkedChoices
variable {x : ScoreProfile n} {hopt : IsManOptimal (profileOfScores x) μ₀}
  {K L : ℕ} {t₁ t₂ : ℝ} {ρ η : Matching n}
  {flag₁ flag₂ : OffDiagonalCellIndex n → Bool}
end MarkedChoices
section GlobalMarkedPairs
variable {x : ScoreProfile n} {K L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}
private structure LongMarkedChoice (x : ScoreProfile n) (K L : ℕ)
    (flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool)
    (t : Matching n → Matching n → ℝ) where
  anchor : Matching n
  cycle : Matching n
  reverse : Matching n
  stable : IsStable (profileOfScores x) anchor
  sole : IsSoleForwardExposedRotation (profileOfScores x) anchor cycle
  long : K < cycle.support.card
  cutoff_nonneg : 0 ≤ t anchor cycle
  mem_choices : reverse ∈
    markedFilteredChoices anchor cycle (flag anchor cycle) K L (t anchor cycle) x
namespace LongMarkedChoice
variable (a : LongMarkedChoice x K L flag t) (hopt : IsManOptimal (profileOfScores x) μ₀)
private noncomputable def pivot : LongPivot (profileOfScores x) μ₀ K := by
  let h := exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole
  exact ⟨Classical.choose h,
    by simpa only [rotationLength, (Classical.choose_spec h).2] using a.long⟩
theorem pivot_anchor : (singletonRotationAnchor hopt (a.pivot hopt).val).val = a.anchor :=
  (Classical.choose_spec
    (exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole)).1
end LongMarkedChoice
private structure ResidualMarkedPair (x : ScoreProfile n) (K L : ℕ)
    (flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool)
    (t : Matching n → Matching n → ℝ) where
  early : LongMarkedChoice x K L flag t
  late : LongMarkedChoice x K L flag t
  prefer : MenWeaklyPrefer (profileOfScores x) early.anchor late.anchor
  ne : early.anchor ≠ late.anchor
  shared : ∃ w ∈ late.reverse.support, early.anchor.symm w = late.anchor.symm w
namespace ResidualMarkedPair
variable (a : ResidualMarkedPair x K L flag t) (hopt : IsManOptimal (profileOfScores x) μ₀)
private theorem pivot_lt : (a.early.pivot hopt).val < (a.late.pivot hopt).val := by
  apply lt_of_le_of_ne
  · apply (menWeaklyPrefer_singletonRotationAnchor_iff hopt _ _).mp
    rw [a.early.pivot_anchor hopt, a.late.pivot_anchor hopt]
    exact a.prefer
  · intro h
    have heq := congrArg (fun s ↦ (singletonRotationAnchor hopt s).val) h
    exact a.ne ((a.early.pivot_anchor hopt).symm.trans (heq.trans (a.late.pivot_anchor hopt)))
end ResidualMarkedPair
end GlobalMarkedPairs
end StepC
end

-- PivotResidualImageGeometry
section
open Filter MeasureTheory Set StableMarriage
open scoped Topology
namespace StepC
variable {n : ℕ}
private def InResidualEndpointScoreDomain (x : ScoreProfile n) (μ : Matching n) : Prop :=
  (n : ℝ) ^ (1 / 10 : ℝ) ≤ femaleSpouseTotal x μ ∧
  femaleSpouseTotal x μ ≤ 2 * (n : ℝ) ^ (2 / 5 : ℝ) ∧
  (∀ w, femaleSpouseScore x μ w / femaleSpouseTotal x μ ≤ 2060 * Real.log n / n) ∧
  ∀ m, maleSpouseScore x μ m ≤ 16 * Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)
theorem measurableSet_inResidualEndpointScoreDomain (μ : Matching n) :
    MeasurableSet {x : ScoreProfile n | InResidualEndpointScoreDomain x μ} := by
  unfold InResidualEndpointScoreDomain
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_le measurable_const (measurable_femaleSpouseTotal μ)).inter <|
    (measurableSet_le (measurable_femaleSpouseTotal μ) measurable_const).inter <|
    (MeasurableSet.iInter fun w ↦ measurableSet_le
      ((measurable_femaleSpouseScore μ w).div (measurable_femaleSpouseTotal μ))
      measurable_const).inter <|
    MeasurableSet.iInter fun m ↦ measurableSet_le (measurable_maleSpouseScore μ m) measurable_const
private def worsePartnerMen (p : Profile n) (μ ν : Matching n) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦ p.manRank m (ν m) < p.manRank m (μ m)
theorem mem_worsePartnerMen_iff_score_lt {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) (μ ν : Matching n) (m : Fin n) :
    m ∈ worsePartnerMen (profileOfScores x) μ ν ↔
      maleSpouseScore x ν m < maleSpouseScore x μ m := by
  rw [worsePartnerMen, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, profileOfScores, maleSpouseScore,
    rankPermutation_lt_iff (hties (.inl m))]
private def relativeMenPermutation (μ ν : Matching n) : Matching n := μ.trans ν.symm
theorem disjoint_worsePartnerMen (p : Profile n) (μ ν : Matching n) :
    Disjoint (worsePartnerMen p μ ν) (worsePartnerMen p ν μ) := by
  refine Finset.disjoint_left.mpr fun m hm hm' ↦ ?_
  exact (Finset.mem_filter.mp hm).2.not_gt (Finset.mem_filter.mp hm').2
theorem union_worsePartnerMen_eq_support (p : Profile n) (μ ν : Matching n) :
    worsePartnerMen p μ ν ∪ worsePartnerMen p ν μ = (relativeMenPermutation μ ν).support := by
  ext m
  simp only [worsePartnerMen, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.Perm.mem_support, relativeMenPermutation, Equiv.trans_apply, ← ne_iff_lt_or_gt]
  rw [(p.manRank m).injective.ne_iff]
  exact ne_comm.trans (not_congr ν.symm_apply_eq).symm
private noncomputable def exposedShortCycles (p : Profile n) (ν : Matching n) (L : ℕ) :
    Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun c ↦ IsExposedRotation p ν c ∧ c.support.card ≤ L
private abbrev IsResidualPairRankGeometry {n : ℕ} (b : ℝ) (K L : ℕ) (p : Profile n)
    (μ ν : Matching n) : Prop :=
  premiseOf (@CompLP.IsResidualPairRankGeometry.self_ n b K L p μ ν)
private theorem IsResidualPairRankGeometry.stable_early {n : ℕ} {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν) :
    IsStable p μ := by
  obtain ⟨hf, _, _, _, _, _, _, _⟩ := h
  exact hf
private theorem IsResidualPairRankGeometry.stable_late {n : ℕ} {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν) :
    IsStable p ν := by
  obtain ⟨_, hf, _, _, _, _, _, _⟩ := h
  exact hf
private theorem IsResidualPairRankGeometry.short_nonempty {n : ℕ} {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν) :
    (worsePartnerMen p μ ν).Nonempty := by
  obtain ⟨_, _, hf, _, _, _, _, _⟩ := h
  exact hf
private theorem IsResidualPairRankGeometry.long_nonempty {n : ℕ} {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν) :
    (worsePartnerMen p ν μ).Nonempty := by
  obtain ⟨_, _, _, hf, _, _, _, _⟩ := h
  exact hf
private theorem IsResidualPairRankGeometry.short_size {n : ℕ} {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν) :
    (worsePartnerMen p μ ν).card ≤ K := by
  obtain ⟨_, _, _, _, hf, _, _, _⟩ := h
  exact hf
private theorem IsResidualPairRankGeometry.long_size {n : ℕ} {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν) :
    b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen p ν μ).card : ℝ) := by
  obtain ⟨_, _, _, _, _, hf, _, _⟩ := h
  exact hf
private theorem IsResidualPairRankGeometry.cycle_partition {n : ℕ} {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν) :
    ∀ c ∈ (relativeMenPermutation μ ν).cycleFactorsFinset, (c.support ⊆ worsePartnerMen p μ ν ∧ IsExposedRotation p ν c) ∨ c.support ⊆ worsePartnerMen p ν μ := by
  obtain ⟨_, _, _, _, _, _, hf, _⟩ := h
  exact hf
private theorem IsResidualPairRankGeometry.short_exposure_cap {n : ℕ} {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν) :
    ((exposedShortCycles p ν L).card : ℝ) ≤ (3 / 2 : ℝ) * Real.log L := by
  obtain ⟨_, _, _, _, _, _, _, hf⟩ := h
  exact hf
private theorem IsResidualPairRankGeometry.mk {n : ℕ} {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n} (h0 : IsStable p μ) (h1 : IsStable p ν) (h2 : (worsePartnerMen p μ ν).Nonempty) (h3 : (worsePartnerMen p ν μ).Nonempty) (h4 : (worsePartnerMen p μ ν).card ≤ K) (h5 : b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen p ν μ).card : ℝ)) (h6 : ∀ c ∈ (relativeMenPermutation μ ν).cycleFactorsFinset, (c.support ⊆ worsePartnerMen p μ ν ∧ IsExposedRotation p ν c) ∨ c.support ⊆ worsePartnerMen p ν μ) (h7 : ((exposedShortCycles p ν L).card : ℝ) ≤ (3 / 2 : ℝ) * Real.log L) :
    IsResidualPairRankGeometry b K L p μ ν := by
  constructor
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
private def forcedShortCycles (p : Profile n) (μ ν : Matching n) (L : ℕ) : Finset (Matching n) :=
  (relativeMenPermutation μ ν).cycleFactorsFinset.filter fun c ↦
    c.support ⊆ worsePartnerMen p μ ν ∧ c.support.card ≤ L
private noncomputable def backgroundShortCycles (p : Profile n) (μ ν : Matching n) (L : ℕ) :
    Finset (Matching n) :=
  (exposedShortCycles p ν L).filter fun c ↦
    Disjoint c.support (relativeMenPermutation μ ν).support
namespace IsResidualPairRankGeometry
variable {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n}
theorem forcedShortCycles_subset (h : IsResidualPairRankGeometry b K L p μ ν) :
    forcedShortCycles p μ ν L ⊆ exposedShortCycles p ν L := by
  classical
  intro c hc
  obtain ⟨hc, hs, hL⟩ := Finset.mem_filter.mp hc
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, hL⟩
  rcases h.cycle_partition c hc with hshort | hlong
  · exact hshort.2
  · have hcyc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
    obtain ⟨m, hm⟩ := Finset.card_pos.mp
      ((by decide : 0 < 2).trans_le hcyc.two_le_card_support)
    exact (Finset.disjoint_left.mp (disjoint_worsePartnerMen p μ ν) (hs hm) (hlong hm)).elim
theorem forced_background_card_le (h : IsResidualPairRankGeometry b K L p μ ν) :
    ((forcedShortCycles p μ ν L).card : ℝ) + ((backgroundShortCycles p μ ν L).card : ℝ) ≤
      (3 / 2 : ℝ) * Real.log L := by
  classical
  have hd : Disjoint (forcedShortCycles p μ ν L) (backgroundShortCycles p μ ν L) := by
    refine Finset.disjoint_left.mpr fun c hc hb ↦ ?_
    have hf := (Finset.mem_filter.mp hc).1
    have hcyc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hf).1
    obtain ⟨m, hm⟩ := Finset.card_pos.mp
      ((by decide : 0 < 2).trans_le hcyc.two_le_card_support)
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp hb).2 hm
      (Equiv.Perm.mem_cycleFactorsFinset_support_le hf hm)
  have hsub : backgroundShortCycles p μ ν L ⊆ exposedShortCycles p ν L :=
    Finset.filter_subset _ _
  have hcard := Finset.card_le_card (Finset.union_subset h.forcedShortCycles_subset hsub)
  rw [Finset.card_union_of_disjoint hd] at hcard
  exact (by exact_mod_cast hcard :
    ((forcedShortCycles p μ ν L).card : ℝ) + ((backgroundShortCycles p μ ν L).card : ℝ) ≤
      ((exposedShortCycles p ν L).card : ℝ)).trans h.short_exposure_cap
end IsResidualPairRankGeometry
private abbrev IsResidualPairGeometry {n : ℕ} (b : ℝ) (K L : ℕ) (x : ScoreProfile n)
    (μ ν : Matching n) : Prop :=
  premiseOf (@CompLP.IsResidualPairGeometry.self_ n b K L x μ ν)
private theorem IsResidualPairGeometry.rank {n : ℕ} {b : ℝ} {K L : ℕ} {x : ScoreProfile n} {μ ν : Matching n} (h : IsResidualPairGeometry b K L x μ ν) :
    IsResidualPairRankGeometry b K L (profileOfScores x) μ ν := by
  obtain ⟨hf, _, _⟩ := h
  exact hf
private theorem IsResidualPairGeometry.early_scores {n : ℕ} {b : ℝ} {K L : ℕ} {x : ScoreProfile n} {μ ν : Matching n} (h : IsResidualPairGeometry b K L x μ ν) :
    InResidualEndpointScoreDomain x μ := by
  obtain ⟨_, hf, _⟩ := h
  exact hf
private theorem IsResidualPairGeometry.late_scores {n : ℕ} {b : ℝ} {K L : ℕ} {x : ScoreProfile n} {μ ν : Matching n} (h : IsResidualPairGeometry b K L x μ ν) :
    InResidualEndpointScoreDomain x ν := by
  obtain ⟨_, _, hf⟩ := h
  exact hf
private theorem IsResidualPairGeometry.mk {n : ℕ} {b : ℝ} {K L : ℕ} {x : ScoreProfile n} {μ ν : Matching n} (h0 : IsResidualPairRankGeometry b K L (profileOfScores x) μ ν) (h1 : InResidualEndpointScoreDomain x μ) (h2 : InResidualEndpointScoreDomain x ν) :
    IsResidualPairGeometry b K L x μ ν := by
  constructor
  · exact h0
  · exact h1
  · exact h2
theorem measurableSet_isResidualPairGeometry (b : ℝ) (K L : ℕ) (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IsResidualPairGeometry b K L x μ ν} := by
  have h : MeasurableSet {x : ScoreProfile n |
      IsResidualPairRankGeometry b K L (profileOfScores x) μ ν} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | IsResidualPairRankGeometry b K L p μ ν})
  exact (h.inter ((measurableSet_inResidualEndpointScoreDomain μ).inter
    (measurableSet_inResidualEndpointScoreDomain ν))).congr (Set.ext fun _ ↦
      ⟨fun h ↦ (IsResidualPairGeometry.mk (h.1) (h.2.1) (h.2.2)), fun h ↦ ⟨h.rank, h.early_scores, h.late_scores⟩⟩)
namespace ResidualPivotPair
variable {p : Profile n} {μ₀ : Matching n} {K : ℕ} {hopt : IsManOptimal p μ₀}
theorem cycle_partition (R : ResidualPivotPair hopt K)
    {c : Matching n} (hc : c ∈ R.relativePermutation.cycleFactorsFinset) :
    (c.support ⊆ R.shortOrientationMen ∧ IsExposedRotation p R.late.2.matching.val c) ∨
      c.support ⊆ R.longOrientationMen := by
  classical
  by_cases h : ∃ m ∈ c.support, m ∈ R.shortOrientationMen
  · obtain ⟨m, hm, hshort⟩ := h
    obtain ⟨s, hs, rfl⟩ := R.exists_shortLabel_of_cycleFactor hc hm hshort
    have hs' : s ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
        eliminatedRotations p μ₀ R.late.2.matching.val :=
      R.coe_shortOrientationLabels ▸ (Finset.mem_coe.mpr hs)
    have he := (R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late hs').1
    refine Or.inl ⟨fun m hm ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
    have hmove := Equiv.Perm.mem_support.mp hm
    have hp := R.relativePermutation_apply_of_mem_shortLabel hs hmove
    have heq : eliminateRotation R.late.2.matching.val s.val.cycle m =
        R.toggledEarly.2.matching.val m := by
      rw [eliminateRotation_apply, ← hp]
      exact R.late.2.matching.val.apply_symm_apply _
    exact heq ▸ he.manRank_lt_eliminate_of_moved hmove
  · right
    intro m hm
    have hs := Equiv.Perm.mem_cycleFactorsFinset_support_le hc hm
    change m ∈ (relativeMenPermutation R.toggledEarly.2.matching.val
      R.late.2.matching.val).support at hs
    rw [← union_worsePartnerMen_eq_support p R.toggledEarly.2.matching.val
      R.late.2.matching.val] at hs
    exact (Finset.mem_union.mp hs).resolve_left fun hms ↦ h ⟨m, hm, hms⟩
end ResidualPivotPair
namespace ResidualMarkedPair
variable {x : ScoreProfile n} {μ₀ : Matching n} {K L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}
end ResidualMarkedPair
end StepC
end

-- DeferredAcceptanceTranscript
section
open StableMarriage
open scoped BigOperators
namespace StepC
private structure DAState (n : ℕ) where
  
  count : Fin n → ℕ
  
  held : Fin n → Option (Fin n)
namespace DAState
variable {n : ℕ}
private def Free (s : DAState n) (m : Fin n) : Prop := ∀ w, s.held w ≠ some m
private def initial (n : ℕ) : DAState n := ⟨fun _ ↦ 0, fun _ ↦ none⟩
private def proposalTarget (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n)
    (m : Fin n) (h : s.count m < n) : Fin n := (rank m).symm ⟨s.count m, h⟩
private def chosenHolder (s : DAState n) (m w : Fin n) (accept : Bool) : Fin n :=
  if accept then m else (s.held w).getD m
private def applyDecision (s : DAState n) (m w : Fin n) (accept : Bool) : DAState n :=
  ⟨Function.update s.count m (s.count m + 1),
    Function.update s.held w (some (s.chosenHolder m w accept))⟩
private def proposalAccepted (p : Profile n) (s : DAState n) (m w : Fin n) : Bool :=
  (s.held w).elim true fun a ↦ decide (p.womanRank w m < p.womanRank w a)
private structure Valid (p : Profile n) (s : DAState n) : Prop where
  count_le : ∀ m, s.count m ≤ n
  held_unique : ∀ {u v m}, s.held u = some m → s.held v = some m → u = v
  held_last : ∀ {w m}, s.held w = some m → (p.manRank m w).val + 1 = s.count m
  preferred_holder : ∀ {m w}, (p.manRank m w).val < s.count m →
    ∃ a, s.held w = some a ∧ p.womanRank w a ≤ p.womanRank w m
  not_rejected : ∀ (ν : Matching n), IsStable p ν → ∀ m,
    (p.manRank m (ν m)).val < s.count m → s.held (ν m) = some m
theorem initial_valid (p : Profile n) : Valid p (initial n) := by
  constructor
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
private theorem chosenHolder_spec (p : Profile n) (s : DAState n) (m w : Fin n) :
    let b := s.chosenHolder m w (proposalAccepted p s m w)
    (b = m ∨ s.held w = some b) ∧ p.womanRank w b ≤ p.womanRank w m ∧
      ∀ a, s.held w = some a → p.womanRank w b ≤ p.womanRank w a := by
  cases h : s.held w with
  | none => simp [chosenHolder, proposalAccepted, h]
  | some a =>
    by_cases ha : p.womanRank w m < p.womanRank w a
    · simp [chosenHolder, proposalAccepted, h, ha, ha.le]
    · simp [chosenHolder, proposalAccepted, h, ha, le_of_not_gt ha]
theorem Valid.apply_proposal {p : Profile n} {s : DAState n}
    (hs : Valid p s) {m w : Fin n} (hm : s.Free m)
    (hnew : (p.manRank m w).val = s.count m) :
    Valid p (s.applyDecision m w (proposalAccepted p s m w)) := by
  let b := s.chosenHolder m w (proposalAccepted p s m w)
  let t := s.applyDecision m w (proposalAccepted p s m w)
  have hspec : (b = m ∨ s.held w = some b) ∧
      p.womanRank w b ≤ p.womanRank w m ∧
      ∀ a, s.held w = some a → p.womanRank w b ≤ p.womanRank w a :=
    chosenHolder_spec p s m w
  have htCount : t.count m = s.count m + 1 := by simp [t, applyDecision]
  have htCount' {i : Fin n} (hi : i ≠ m) : t.count i = s.count i := by
    simp [t, applyDecision, hi]
  have htHeld : t.held w = some b := by simp [t, b, applyDecision]
  have htHeld' {v : Fin n} (hv : v ≠ w) : t.held v = s.held v := by
    simp [t, applyDecision, hv]
  have hsHeld_ne {v i : Fin n} (hi : s.held v = some i) : i ≠ m := by
    rintro rfl
    exact hm v hi
  have no_other_hold {v : Fin n} (hv : v ≠ w) (h : s.held v = some b) : False := by
    rcases hspec.1 with hbm | hbw
    · exact hm v (hbm ▸ h)
    · exact hv (hs.held_unique h hbw)
  have old_proposal {i v : Fin n} (hv : v ≠ w)
      (hi : (p.manRank i v).val < t.count i) : (p.manRank i v).val < s.count i := by
    by_cases him : i = m
    · subst i
      rw [htCount, ← hnew] at hi
      have hne : (p.manRank m v).val ≠ (p.manRank m w).val :=
        fun h ↦ hv ((p.manRank m).injective (Fin.ext h))
      rw [← hnew]
      omega
    · exact htCount' him ▸ hi
  have winner_prefers {ν : Matching n} (hν : IsStable p ν) :
      p.manRank b w ≤ p.manRank b (ν b) := by
    by_contra! hlt
    have hlt' : (p.manRank b (ν b)).val < (p.manRank b w).val := hlt
    rcases hspec.1 with hbm | hbw
    · rw [hbm, hnew] at hlt'
      exact hm (ν m) (hs.not_rejected ν hν m hlt')
    · have hp : (p.manRank b (ν b)).val < s.count b := by
        have := hs.held_last hbw
        omega
      have heq := hs.held_unique (hs.not_rejected ν hν b hp) hbw
      exact (not_lt_of_ge (le_of_eq (congrArg (p.manRank b) heq.symm))) hlt
  have proposed_dominance {i : Fin n} (hi : (p.manRank i w).val < t.count i) :
      p.womanRank w b ≤ p.womanRank w i := by
    by_cases him : i = m
    · exact him ▸ hspec.2.1
    · have hprop : (p.manRank i w).val < s.count i := htCount' him ▸ hi
      obtain ⟨a, ha, hpref⟩ := hs.preferred_holder hprop
      exact (hspec.2.2 a ha).trans hpref
  change Valid p t
  constructor
  · intro i
    by_cases h : i = m
    · subst i
      rw [htCount, ← hnew]
      exact Nat.succ_le_of_lt (p.manRank m w).isLt
    · exact (htCount' h).trans_le (hs.count_le i)
  · intro u v i hu hv
    by_cases huw : u = w
    · subst u
      have hbi : b = i := Option.some.inj (htHeld.symm.trans hu)
      subst i
      by_contra hvw
      exact no_other_hold (Ne.symm hvw) ((htHeld' (Ne.symm hvw)).symm.trans hv)
    · by_cases hvw : v = w
      · subst v
        have hbi : b = i := Option.some.inj (htHeld.symm.trans hv)
        subst i
        exact False.elim (no_other_hold huw ((htHeld' huw).symm.trans hu))
      · exact hs.held_unique ((htHeld' huw).symm.trans hu) ((htHeld' hvw).symm.trans hv)
  · intro v i hvi
    by_cases hv : v = w
    · subst v
      have hbi : b = i := Option.some.inj (htHeld.symm.trans hvi)
      subst i
      rcases hspec.1 with hbm | hbw
      · rw [hbm, htCount, hnew]
      · exact (hs.held_last hbw).trans (htCount' (hsHeld_ne hbw)).symm
    · have h := (htHeld' hv).symm.trans hvi
      exact (hs.held_last h).trans (htCount' (hsHeld_ne h)).symm
  · intro i v hi
    by_cases hv : v = w
    · subst v
      exact ⟨b, htHeld, proposed_dominance hi⟩
    · obtain ⟨a, ha, hle⟩ := hs.preferred_holder (old_proposal hv hi)
      exact ⟨a, (htHeld' hv).trans ha, hle⟩
  · intro ν hν i hi
    by_cases hw : ν i = w
    · rw [hw] at hi ⊢
      by_contra h
      have hbi : b ≠ i := fun e ↦ h (e ▸ htHeld)
      have hbν : ν b ≠ w := fun e ↦ hbi (ν.injective (e.trans hw.symm))
      have hbPref : p.manRank b w < p.manRank b (ν b) :=
        lt_of_le_of_ne (winner_prefers hν) fun e ↦ hbν ((p.manRank b).injective e).symm
      have hwPref : p.womanRank w b < p.womanRank w (ν.symm w) := by
        rw [← hw, ν.symm_apply_apply, hw]
        exact lt_of_le_of_ne (proposed_dominance hi) fun e ↦ hbi ((p.womanRank w).injective e)
      exact hν b w ⟨hbν, hbPref, hwPref⟩
    · exact (htHeld' hw).trans (hs.not_rejected ν hν i (old_proposal hw hi))
theorem Valid.free_count_lt {p : Profile n} {s : DAState n} (hs : Valid p s)
    {m : Fin n} (hm : s.Free m) : s.count m < n := by
  classical
  by_contra! h
  have hheld (w : Fin n) : ∃ a, s.held w = some a := by
    obtain ⟨a, ha, _⟩ := hs.preferred_holder ((p.manRank m w).isLt.trans_le h)
    exact ⟨a, ha⟩
  let holder (w : Fin n) := Classical.choose (hheld w)
  have hholder (w : Fin n) : s.held w = some (holder w) := Classical.choose_spec (hheld w)
  have hi : Function.Injective holder := fun u v huv ↦
    hs.held_unique (hholder u) (by rw [huv]; exact hholder v)
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hi m
  exact hm w (hw ▸ hholder w)
private def Complete (s : DAState n) : Prop := ∀ m, ∃ w, s.held w = some m
private noncomputable def toMatching (s : DAState n) (hc : s.Complete) : Matching n := by
  let wife (m : Fin n) := Classical.choose (hc m)
  have hw (m : Fin n) : s.held (wife m) = some m := Classical.choose_spec (hc m)
  have hi : Function.Injective wife := by
    intro m a h
    exact Option.some.inj ((hw m).symm.trans (h ▸ hw a))
  exact Equiv.ofBijective wife ⟨hi, Finite.surjective_of_injective hi⟩
private def readyMen (s : DAState n) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦ (∀ w, s.held w ≠ some m) ∧ s.count m < n
theorem mem_readyMen {s : DAState n} {m : Fin n} :
    m ∈ s.readyMen ↔ s.Free m ∧ s.count m < n := by
  simp [readyMen, Free]
private def nextProposal (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n) :
    Option (Fin n × Fin n) :=
  if h : s.readyMen.Nonempty then
    let m := s.readyMen.min' h
    let hm := mem_readyMen.mp (Finset.min'_mem _ h)
    some (m, s.proposalTarget rank m hm.2)
  else none
theorem nextProposal_some {rank : Fin n → Equiv.Perm (Fin n)} {s : DAState n}
    {m w : Fin n} (h : s.nextProposal rank = some (m, w)) :
    s.Free m ∧ (rank m w).val = s.count m := by
  unfold nextProposal at h
  split at h
  · rename_i hne
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨(mem_readyMen.mp (Finset.min'_mem _ hne)).1, by simp [proposalTarget]⟩
  · contradiction
theorem Valid.complete_of_nextProposal_none {p : Profile n} {s : DAState n}
    (hs : Valid p s) (hd : s.nextProposal p.manRank = none) : s.Complete := by
  classical
  intro m
  by_contra! hm
  have hfree : s.Free m := hm
  have hne : s.readyMen.Nonempty := ⟨m, mem_readyMen.mpr ⟨hfree, hs.free_count_lt hfree⟩⟩
  simp [nextProposal, hne] at hd
private def advance (p : Profile n) (s : DAState n) : DAState n :=
  match s.nextProposal p.manRank with
  | none => s
  | some (m, w) => s.applyDecision m w (proposalAccepted p s m w)
theorem Valid.advance {p : Profile n} {s : DAState n} (hs : Valid p s) :
    Valid p (advance p s) := by
  cases h : s.nextProposal p.manRank with
  | none => simpa only [DAState.advance, h] using hs
  | some a =>
    obtain ⟨m, w⟩ := a
    have hp := nextProposal_some h
    simpa only [DAState.advance, h] using hs.apply_proposal hp.1 hp.2
private def proposalCount (s : DAState n) : ℕ := ∑ m, s.count m
private theorem proposalCount_applyDecision (s : DAState n) (m w : Fin n) (accept : Bool) :
    (s.applyDecision m w accept).proposalCount = s.proposalCount + 1 := by
  let t := s.applyDecision m w accept
  have hm : m ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have he :
      ∑ i ∈ Finset.univ.erase m, t.count i = ∑ i ∈ Finset.univ.erase m, s.count i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [t, applyDecision, (Finset.mem_erase.mp hi).1]
  change t.proposalCount = _
  unfold proposalCount
  rw [← Finset.sum_erase_add _ t.count hm, ← Finset.sum_erase_add _ s.count hm, he]
  simp [t, applyDecision, add_assoc]
theorem proposalCount_advance_of_some {p : Profile n} {s : DAState n} {a : Fin n × Fin n}
    (h : s.nextProposal p.manRank = some a) :
    (advance p s).proposalCount = s.proposalCount + 1 := by
  obtain ⟨m, w⟩ := a
  rw [advance, h]
  exact proposalCount_applyDecision s m w _
theorem Valid.proposalCount_le {p : Profile n} {s : DAState n} (hs : Valid p s) :
    s.proposalCount ≤ n * n := by
  calc
    _ ≤ ∑ _ : Fin n, n := Finset.sum_le_sum fun m _ ↦ hs.count_le m
    _ = _ := by simp
private def run (p : Profile n) : ℕ → DAState n
  | 0 => initial n
  | k + 1 => advance p (run p k)
theorem valid_run (p : Profile n) (k : ℕ) : Valid p (run p k) := by
  induction k with
  | zero => exact initial_valid p
  | succ k ih => exact ih.advance
private theorem le_proposalCount_run_of_next {p : Profile n} {k : ℕ}
    (h : (run p k).nextProposal p.manRank ≠ none) : k ≤ (run p k).proposalCount := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    cases hprev : (run p k).nextProposal p.manRank with
    | none =>
      have he : run p (k + 1) = run p k := by simp only [run, advance, hprev]
      exact False.elim (h (he ▸ hprev))
    | some a =>
      have hcount := proposalCount_advance_of_some hprev
      change k + 1 ≤ (advance p (run p k)).proposalCount
      rw [hcount]
      exact Nat.succ_le_succ (ih (by rw [hprev]; exact Option.some_ne_none _))
theorem nextProposal_run_sq_eq_none (p : Profile n) :
    (run p (n * n)).nextProposal p.manRank = none := by
  cases h : (run p (n * n)).nextProposal p.manRank with
  | none => rfl
  | some a =>
    have hl := le_proposalCount_run_of_next (p := p) (k := n * n)
      (by rw [h]; exact Option.some_ne_none _)
    have hu := (valid_run p (n * n + 1)).proposalCount_le
    change (advance p (run p (n * n))).proposalCount ≤ n * n at hu
    rw [proposalCount_advance_of_some h] at hu
    omega
theorem complete_run_sq (p : Profile n) : (run p (n * n)).Complete :=
  (valid_run p (n * n)).complete_of_nextProposal_none (nextProposal_run_sq_eq_none p)
private noncomputable def matching (p : Profile n) : Matching n :=
  (run p (n * n)).toMatching (complete_run_sq p)
end DAState
end StepC
end

-- DAStreamSimulation
section
open StableMarriage
namespace StepC
private structure DAStreamState (n : ℕ) where
  da : DAState n
  observed : Fin n → List (Fin n)
namespace DAStreamState
variable {n T : ℕ}
private def initial (n : ℕ) : DAStreamState n := ⟨DAState.initial n, fun _ ↦ []⟩
end DAStreamState
end StepC
end

-- CycleSupportCount
section
open Equiv.Perm Finset
open scoped BigOperators Classical
namespace StepC
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem cycleType_ofSubtype_eq_iff {S : Finset ι} (τ : Equiv.Perm S) :
    τ.cycleType = {S.card} ↔ (ofSubtype τ).IsCycle ∧ (ofSubtype τ).support = S := by
  have htype : (ofSubtype τ).cycleType = τ.cycleType :=
    cycleType_extendDomain (α := ↥S) (p := fun i ↦ i ∈ S) (Equiv.refl _) (g := τ)
  rw [← htype]
  constructor
  · intro h
    have hc : (ofSubtype τ).IsCycle := card_cycleType_eq_one.mp (by rw [h]; rfl)
    have hs : (ofSubtype τ).support.card = S.card := by
      rw [← sum_cycleType, h, Multiset.sum_singleton]
    refine ⟨hc, eq_of_subset_of_card_le ?_ hs.ge⟩
    intro i hi
    by_contra hn
    exact (mem_support.mp hi) (ofSubtype_apply_of_not_mem τ hn)
  · rintro ⟨hc, hs⟩
    rw [hc.cycleType, hs]
theorem card_cyclesWithSupport (S : Finset ι) (hS : 2 ≤ S.card) :
    (Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support = S)).card =
      (S.card - 1).factorial := by
  let A := Finset.univ.filter (fun τ : Equiv.Perm S ↦ τ.cycleType = {S.card})
  have hcount : A.card = (S.card - 1).factorial := by
    have hcard : Fintype.card S = S.card := Fintype.card_coe S
    simpa only [A, hcard, Nat.choose_self, mul_one] using
      (card_of_cycleType_singleton (α := S) hS hcard.ge)
  rw [← hcount]
  symm
  refine Finset.card_bij (fun τ _ ↦ ofSubtype τ) ?_ ?_ ?_
  · intro τ hτ
    exact mem_filter.mpr ⟨mem_univ _, (cycleType_ofSubtype_eq_iff τ).mp (mem_filter.mp hτ).2⟩
  · intro τ₁ _ τ₂ _ h
    exact ofSubtype_injective h
  · intro σ hσ
    obtain ⟨hc, hs⟩ := (mem_filter.mp hσ).2
    have hInv := isInvariant_of_support_le (show σ.support ⊆ S from hs.le)
    let τ := σ.subtypePerm hInv
    have heq : ofSubtype τ = σ :=
      (ofSubtype_eq_iff hInv).mpr ⟨hs.le, fun _ ↦ rfl⟩
    refine ⟨τ, mem_filter.mpr ⟨mem_univ _, (cycleType_ofSubtype_eq_iff τ).mpr ?_⟩, heq⟩
    rw [heq]
    exact ⟨hc, hs⟩
end StepC
end

-- PivotAggregateMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepC
variable {n : ℕ}
end StepC
end

-- PivotDecorationRevealInvariance
section
open MeasureTheory Set StableMarriage
namespace StepC
variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}
private structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2
theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩
end StepC
end

-- PivotLaterRevealReplay
section
open MeasureTheory Set StableMarriage
namespace StepC
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
end StepC
end

-- PivotMovedCenteredTest
section
open Filter MeasureTheory Set StableMarriage
namespace StepC
variable {n : ℕ}
end StepC
end

-- PivotComparableCentered
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
private structure PivotCountParameters where
  lowerLength : ℝ
  upperLength : ℝ
  geometryBudget : ℝ
  supportCap : ℕ
  shortCutoff : ℕ
private abbrev PivotMark (n : ℕ) := Matching n × Matching n
namespace PivotCountParameters
variable {n : ℕ}
private noncomputable def localCount (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  localFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff i.1 i.2
private noncomputable def onStableMark (i : PivotMark n) (f : ScoreProfile n → ℝ) :
    ScoreProfile n → ℝ :=
  {x | IsScoreStable x i.1}.indicator f
private noncomputable def count (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  onStableMark i (q.localCount i)
end PivotCountParameters
end StepC
end

-- PivotCenteredReduction
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepC
variable {n : ℕ}
private def IncomparableAnchors (p : Profile n) (μ ν : Matching n) : Prop :=
  ¬ MenWeaklyPrefer p μ ν ∧ ¬ MenWeaklyPrefer p ν μ
theorem measurableSet_incomparableAnchors (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IncomparableAnchors (profileOfScores x) μ ν} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | IncomparableAnchors p μ ν})
namespace PivotCountParameters
end PivotCountParameters
end StepC
end

-- PivotResidualCountBridge
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepC
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
end StepC
end

-- PivotIncomparableScoreCount
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepC
variable {n : ℕ}
private def scoreIncomparablePairEvent (Q : ScoreProfile n → Matching n → Matching n → Prop)
    (μ ν : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧
    IncomparableAnchors (profileOfScores x) μ ν ∧ Q x μ ν}
theorem measurableSet_scoreIncomparablePairEvent
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν}) (μ ν : Matching n) :
    MeasurableSet (scoreIncomparablePairEvent Q μ ν) :=
  (measurableSet_isScoreStable μ).inter ((measurableSet_isScoreStable ν).inter
    ((measurableSet_incomparableAnchors μ ν).inter (hQ μ ν)))
namespace PivotCountParameters
end PivotCountParameters
end StepC
end

-- PivotTwoCycleForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
theorem RealizesDirectedCycle.eq_of_mem_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → Option ι} {σ τ : Equiv.Perm ι} (hσ : RealizesDirectedCycle f σ)
    (hτ : RealizesDirectedCycle f τ) {i : ι} (hiσ : i ∈ σ.support)
    (hiτ : i ∈ τ.support) : σ = τ := by
  have hagree (j : ι) (hjσ : j ∈ σ.support) (hjτ : j ∈ τ.support) : σ j = τ j :=
    Option.some.inj ((hσ.2 j hjσ).symm.trans (hτ.2 j hjτ))
  have horbit (k : ℕ) : (σ ^ k) i = (τ ^ k) i ∧
      (σ ^ k) i ∈ σ.support ∧ (τ ^ k) i ∈ τ.support := by
    induction k with
    | zero => simpa using And.intro (rfl : i = i) (And.intro hiσ hiτ)
    | succ k ih =>
      obtain ⟨heq, hs, ht⟩ := ih
      simp only [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨(hagree _ hs (heq ▸ ht)).trans (congrArg τ heq),
        Equiv.Perm.apply_mem_support.mpr hs, Equiv.Perm.apply_mem_support.mpr ht⟩
  apply Equiv.ext
  intro j
  by_cases hj : j ∈ σ.support
  · obtain ⟨k, hk⟩ := hσ.1.exists_pow_eq
      (Equiv.Perm.mem_support.mp hiσ) (Equiv.Perm.mem_support.mp hj)
    apply hagree j hj
    rw [← hk, (horbit k).1]
    exact (horbit k).2.2
  · have hjτ : j ∉ τ.support := by
      intro hjτ
      obtain ⟨k, hk⟩ := hτ.1.exists_pow_eq
        (Equiv.Perm.mem_support.mp hiτ) (Equiv.Perm.mem_support.mp hjτ)
      apply hj
      rw [← hk, ← (horbit k).1]
      exact (horbit k).2.1
    exact (Equiv.Perm.notMem_support.mp hj).trans (Equiv.Perm.notMem_support.mp hjτ).symm
theorem RealizesDirectedCycle.disjoint_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → Option ι} {σ τ : Equiv.Perm ι} (hσ : RealizesDirectedCycle f σ)
    (hτ : RealizesDirectedCycle f τ) (hne : σ ≠ τ) : Disjoint σ.support τ.support :=
  Finset.disjoint_left.mpr fun _ hiσ hiτ ↦ hne (hσ.eq_of_mem_support hτ hiσ hiτ)
end StepC
end

-- CommonForwardCycleMoments
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepC
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private noncomputable def commonForwardCycles (C : Finset ι) (K : Finset ℕ) :
    Finset (Equiv.Perm ι) := by
  classical
  exact Finset.univ.filter fun σ ↦ σ.IsCycle ∧ σ.support ⊆ C ∧ σ.support.card ∈ K
theorem mem_commonForwardCycles {C : Finset ι} {K : Finset ℕ} {σ : Equiv.Perm ι} :
    σ ∈ commonForwardCycles C K ↔ σ.IsCycle ∧ σ.support ⊆ C ∧ σ.support.card ∈ K := by
  classical
  simp [commonForwardCycles]
private noncomputable def realizedForwardCycleCount (S : Finset (Equiv.Perm ι)) (f : ι → Option ι) :
    ℕ := by
  classical
  exact (S.filter (RealizesDirectedCycle f)).card
private noncomputable def commonForwardCycleCount (C : Finset ι) (L : ℕ) (f : ι → Option ι) :
    ℕ :=
  realizedForwardCycleCount (commonForwardCycles C (Finset.Icc 2 L)) f
private def forwardCycleEvent (σ : Equiv.Perm ι) : Set (ι → Option ι) :=
  {f | RealizesDirectedCycle f σ}
section RowLaws
variable [MeasurableSpace (Option ι)]
private theorem measureReal_pi_prescribed (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (s : Finset ι) (a : ι → Option ι) :
    (Measure.pi ν).real {f | ∀ i ∈ s, f i = a i} = ∏ i ∈ s, (ν i).real {a i} := by
  let B (i : ι) : Set (Option ι) := if i ∈ s then {a i} else univ
  have hB : {f | ∀ i ∈ s, f i = a i} = univ.pi B := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
    constructor
    · intro h i
      by_cases hi : i ∈ s <;> simp [B, hi, h]
    · intro h i hi
      simpa [B, hi] using h i
  rw [hB, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  have hp (i : ι) : ((ν i) (B i)).toReal = if i ∈ s then (ν i).real {a i} else 1 := by
    by_cases hi : i ∈ s <;> simp [B, hi, measureReal_def]
  simp_rw [hp]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
theorem measureReal_forwardCycleEvent (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] {σ : Equiv.Perm ι} (hσ : σ.IsCycle) :
    (Measure.pi ν).real (forwardCycleEvent σ) = ∏ i ∈ σ.support, (ν i).real {some (σ i)} := by
  simp only [forwardCycleEvent, RealizesDirectedCycle, hσ, true_and]
  exact measureReal_pi_prescribed ν _ _
theorem measureReal_inter_forwardCycleEvent_le (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] {σ τ : Equiv.Perm ι} (hσ : σ.IsCycle)
    (hτ : τ.IsCycle) (hne : σ ≠ τ) :
    (Measure.pi ν).real (forwardCycleEvent σ ∩ forwardCycleEvent τ) ≤
      (Measure.pi ν).real (forwardCycleEvent σ) * (Measure.pi ν).real (forwardCycleEvent τ) := by
  classical
  by_cases hd : Disjoint σ.support τ.support
  · let a (i : ι) := if i ∈ σ.support then some (σ i) else some (τ i)
    have he : forwardCycleEvent σ ∩ forwardCycleEvent τ =
        {f | ∀ i ∈ σ.support ∪ τ.support, f i = a i} := by
      ext f
      simp only [Set.mem_inter_iff, forwardCycleEvent, Set.mem_ofPred_eq, RealizesDirectedCycle,
        hσ, hτ, true_and]
      constructor
      · rintro ⟨hs, ht⟩ i hi
        by_cases hs' : i ∈ σ.support
        · simpa only [a, if_pos hs'] using hs i hs'
        · simpa only [a, if_neg hs'] using ht i ((Finset.mem_union.mp hi).resolve_left hs')
      · intro h
        exact ⟨fun i hi ↦ by simpa only [a, if_pos hi] using h i (Finset.mem_union_left _ hi),
          fun i hi ↦ by
            have hnot := fun hmem ↦ Finset.disjoint_left.mp hd hmem hi
            simpa only [a, if_neg hnot] using h i (Finset.mem_union_right _ hi)⟩
    rw [he, measureReal_pi_prescribed, Finset.prod_union hd,
      measureReal_forwardCycleEvent ν hσ, measureReal_forwardCycleEvent ν hτ]
    refine le_of_eq (congrArg₂ (· * ·) ?_ ?_)
    · exact Finset.prod_congr rfl fun i hi ↦ by simp only [a, if_pos hi]
    · exact Finset.prod_congr rfl fun i hi ↦ by
        simp only [a, if_neg (show i ∉ σ.support from fun h ↦ Finset.disjoint_left.mp hd h hi)]
  · have he : forwardCycleEvent σ ∩ forwardCycleEvent τ = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun f hf ↦ hd ?_
      exact hf.1.disjoint_support hf.2 hne
    rw [he, measureReal_empty]
    exact mul_nonneg measureReal_nonneg measureReal_nonneg
private noncomputable def cycleIndicator (σ : Equiv.Perm ι) (f : ι → Option ι) : ℝ :=
  (forwardCycleEvent σ).indicator (1 : (ι → Option ι) → ℝ) f
omit [MeasurableSpace (Option ι)] in
private theorem count_eq_sum_cycleIndicator (S : Finset (Equiv.Perm ι)) :
    (fun f ↦ (realizedForwardCycleCount S f : ℝ)) =
      fun f ↦ ∑ σ ∈ S, cycleIndicator σ f := by
  classical
  funext f
  simp only [realizedForwardCycleCount, cycleIndicator, Set.indicator_apply, forwardCycleEvent,
    Set.mem_ofPred_eq, Pi.one_apply, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
variable [MeasurableSingletonClass (Option ι)]
private theorem cycleIndicator_memLp (ν : Measure (ι → Option ι)) [IsFiniteMeasure ν]
    (σ : Equiv.Perm ι) : MemLp (cycleIndicator σ) 2 ν := by
  unfold cycleIndicator
  exact memLp_indicator_const (μ := ν) 2
    (MeasurableSet.of_discrete : MeasurableSet (forwardCycleEvent σ)) (1 : ℝ)
    (Or.inr (measure_ne_top ν _))
theorem realizedForwardCycleCount_memLp (ν : Measure (ι → Option ι)) [IsFiniteMeasure ν]
    (S : Finset (Equiv.Perm ι)) :
    MemLp (fun f ↦ (realizedForwardCycleCount S f : ℝ)) 2 ν := by
  rw [count_eq_sum_cycleIndicator]
  simpa only [← Finset.sum_apply] using memLp_finsetSum' S fun σ _ ↦ cycleIndicator_memLp ν σ
theorem integral_realizedForwardCycleCount (ν : Measure (ι → Option ι)) [IsFiniteMeasure ν]
    (S : Finset (Equiv.Perm ι)) :
    (∫ f, (realizedForwardCycleCount S f : ℝ) ∂ν) =
      ∑ σ ∈ S, ν.real (forwardCycleEvent σ) := by
  rw [count_eq_sum_cycleIndicator]
  rw [integral_finsetSum _ fun σ _ ↦ (cycleIndicator_memLp ν σ).integrable (by simp)]
  exact Finset.sum_congr rfl fun σ _ ↦ integral_indicator_one MeasurableSet.of_discrete
omit [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)] in
private theorem cycleIndicator_mul_eq_indicator (σ τ : Equiv.Perm ι) :
    cycleIndicator σ * cycleIndicator τ =
      (forwardCycleEvent σ ∩ forwardCycleEvent τ).indicator (1 : (ι → Option ι) → ℝ) := by
  classical
  funext f
  by_cases hσ : f ∈ forwardCycleEvent σ <;> by_cases hτ : f ∈ forwardCycleEvent τ <;>
    simp [cycleIndicator, hσ, hτ]
theorem variance_realizedForwardCycleCount_le (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (S : Finset (Equiv.Perm ι))
    (hS : ∀ σ ∈ S, σ.IsCycle) :
    Var[fun f ↦ (realizedForwardCycleCount S f : ℝ); Measure.pi ν] ≤
      ∫ f, (realizedForwardCycleCount S f : ℝ) ∂(Measure.pi ν) := by
  classical
  rw [integral_realizedForwardCycleCount, count_eq_sum_cycleIndicator,
    variance_fun_sum' (fun σ _ ↦ cycleIndicator_memLp (Measure.pi ν) σ)]
  apply Finset.sum_le_sum
  intro σ hσ
  calc
    _ ≤ ∑ τ ∈ S, if τ = σ then (Measure.pi ν).real (forwardCycleEvent σ) else 0 := by
      refine Finset.sum_le_sum fun τ hτ ↦ ?_
      rw [covariance_eq_sub (cycleIndicator_memLp (Measure.pi ν) σ)
        (cycleIndicator_memLp (Measure.pi ν) τ), cycleIndicator_mul_eq_indicator,
        integral_indicator_one MeasurableSet.of_discrete]
      simp only [cycleIndicator, integral_indicator_one MeasurableSet.of_discrete]
      by_cases he : τ = σ
      · subst τ
        simp only [Set.inter_self]
        exact sub_le_self _ (mul_nonneg measureReal_nonneg measureReal_nonneg)
      · rw [if_neg he]
        exact sub_nonpos.mpr (measureReal_inter_forwardCycleEvent_le ν (hS σ hσ) (hS τ hτ)
          (Ne.symm he))
    _ = _ := by simp [hσ]
end RowLaws
section ReferenceWeights
private noncomputable def injectiveCommonLabels (C : Finset ι) (k : ℕ) :
    Finset (Fin k → ι) := by
  classical
  exact Finset.univ.filter fun x ↦ Function.Injective x ∧ ∀ i, x i ∈ C
private theorem mem_injectiveCommonLabels {C : Finset ι} {k : ℕ} {x : Fin k → ι} :
    x ∈ injectiveCommonLabels C k ↔ Function.Injective x ∧ ∀ i, x i ∈ C := by
  classical
  simp [injectiveCommonLabels]
private theorem sum_injectiveCommonLabels_eq (C : Finset ι) (k : ℕ) (r : ι → ℝ≥0∞) :
    (∑ x ∈ injectiveCommonLabels C k, ∏ i, r (x i)) =
      (k.factorial : ℝ≥0∞) * ∑ s ∈ C.powersetCard k, ∏ i ∈ s, r i := by
  classical
  let G := injectiveCommonLabels C k
  let supp (x : Fin k → ι) := Finset.univ.image x
  have hm (x : Fin k → ι) (hx : x ∈ G) : supp x ∈ C.powersetCard k := by
    obtain ⟨hinj, hC⟩ := mem_injectiveCommonLabels.mp hx
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · rintro i hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact hC j
    · rw [show supp x = Finset.univ.image x from rfl,
        Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hcard (s : Finset ι) (hs : s ∈ C.powersetCard k) :
      (G.filter (fun x ↦ supp x = s)).card = k.factorial := by
    obtain ⟨hsC, hsk⟩ := Finset.mem_powersetCard.mp hs
    let E := G.filter (fun x ↦ supp x = s)
    let f (x : E) : Fin k ≃ s := by
      have hx := Finset.mem_filter.mp x.property
      have hxi := (mem_injectiveCommonLabels.mp hx.1).1
      let g (j : Fin k) : s := ⟨x.val j, hx.2 ▸ Finset.mem_image_of_mem x.val (Finset.mem_univ j)⟩
      exact Equiv.ofBijective g ⟨fun _ _ h ↦ hxi (congrArg Subtype.val h), fun i ↦ by
        have hi : i.val ∈ supp x.val := hx.2.symm ▸ i.property
        obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hi
        exact ⟨j, Subtype.ext hj⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · intro x y h
        exact Subtype.ext (funext fun i ↦ congrArg (fun e : Fin k ≃ s ↦ (e i).val) h)
      · intro e
        let g (i : Fin k) := (e i).val
        have hg : g ∈ G := mem_injectiveCommonLabels.mpr
          ⟨Subtype.val_injective.comp e.injective, fun i ↦ hsC (e i).property⟩
        have hgs : supp g = s := by
          ext i
          constructor
          · intro hi
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
            exact (e j).property
          · intro hi
            obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
            exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩
        refine ⟨⟨g, Finset.mem_filter.mpr ⟨hg, hgs⟩⟩, ?_⟩
        exact Equiv.ext fun i ↦ Subtype.ext rfl
    let t : Fin k ≃ s := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_fin, hsk])
    have h := Fintype.card_congr (Equiv.ofBijective f hf)
    rw [Fintype.card_coe, ← Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin k)) t),
      Fintype.card_perm, Fintype.card_fin] at h
    exact h
  calc
    _ = ∑ x ∈ G, ∏ i ∈ supp x, r i := by
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      exact (Finset.prod_image (mem_injectiveCommonLabels.mp hx).1.injOn).symm
    _ = ∑ s ∈ C.powersetCard k, ∑ x ∈ G.filter (fun x ↦ supp x = s), ∏ i ∈ s, r i :=
      (Finset.sum_fiberwise_of_maps_to' hm (fun s ↦ ∏ i ∈ s, r i)).symm
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs ↦ ?_
      simp only [Finset.sum_const, nsmul_eq_mul, hcard s hs]
private theorem sum_commonForwardCycles_singleton (C : Finset ι) {k : ℕ} (hk : 2 ≤ k)
    (p : ι → ℝ) :
    (∑ σ ∈ commonForwardCycles C {k}, ∏ i ∈ σ.support, p i) =
      ((k - 1).factorial : ℝ) * ∑ s ∈ C.powersetCard k, ∏ i ∈ s, p i := by
  classical
  let S := commonForwardCycles C {k}
  have hm (σ : Equiv.Perm ι) (hσ : σ ∈ S) : σ.support ∈ C.powersetCard k := by
    obtain ⟨-, hsub, hlen⟩ := mem_commonForwardCycles.mp hσ
    exact Finset.mem_powersetCard.mpr ⟨hsub, Finset.mem_singleton.mp hlen⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hm (fun s ↦ ∏ i ∈ s, p i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  obtain ⟨hsub, hlen⟩ := Finset.mem_powersetCard.mp hs
  have hfiber : S.filter (fun σ ↦ σ.support = s) =
      Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support = s) := by
    ext σ
    simp only [Finset.mem_filter, mem_commonForwardCycles, Finset.mem_singleton,
      Finset.mem_univ, true_and, S]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦
      ⟨⟨h.1, h.2.symm ▸ hsub, (congrArg Finset.card h.2).trans hlen⟩, h.2⟩⟩
  rw [hfiber, Finset.sum_const, nsmul_eq_mul, card_cyclesWithSupport s (hlen.symm ▸ hk), hlen]
private noncomputable def commonForwardLabelLoss (C : Finset ι) (p : ι → ℝ) (k : ℕ) : ℝ :=
  (k.choose 2 : ℝ) * (∑ i, (p i) ^ 2) + (k : ℝ) * ∑ i ∈ Cᶜ, p i
theorem commonForwardLabelLoss_le_of_weight_le (C : Finset ι) (p : ι → ℝ) (k : ℕ)
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) {q : ℝ} (hq : ∀ i, p i ≤ q) :
    commonForwardLabelLoss C p k ≤ ((k.choose 2 : ℝ) + k * (Cᶜ.card : ℝ)) * q := by
  have hsq : (∑ i, (p i) ^ 2) ≤ q := by
    calc
      _ ≤ ∑ i, p i * q := Finset.sum_le_sum fun i _ ↦ by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left (hq i) (hp i)
      _ = _ := by rw [← Finset.sum_mul, hp₁, one_mul]
  have hC : (∑ i ∈ Cᶜ, p i) ≤ (Cᶜ.card : ℝ) * q := by
    calc
      _ ≤ ∑ _i ∈ Cᶜ, q := Finset.sum_le_sum fun i _ ↦ hq i
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  unfold commonForwardLabelLoss
  calc
    _ ≤ (k.choose 2 : ℝ) * q + (k : ℝ) * ((Cᶜ.card : ℝ) * q) :=
      add_le_add (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _))
    _ = _ := by ring
theorem commonForwardCycleReferenceWeight_lower (C : Finset ι) {k : ℕ} (hk : 2 ≤ k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) :
    (1 - commonForwardLabelLoss C p k) / (k : ℝ) ≤
      ∑ σ ∈ commonForwardCycles C {k}, ∏ i ∈ σ.support, p i := by
  classical
  let r (i : ι) := ENNReal.ofReal (p i)
  let E : ℝ := ∑ s ∈ C.powersetCard k, ∏ i ∈ s, p i
  let B := ∑ x ∈ injectiveCommonLabels C k, ∏ i, r (x i)
  have hr : ∑ i, r i = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hp i), hp₁, ENNReal.ofReal_one]
  have hB : B = ENNReal.ofReal ((k.factorial : ℝ) * E) := by
    rw [show B = _ from sum_injectiveCommonLabels_eq C k r, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
    congr 1
    unfold E
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ Finset.prod_nonneg fun i _ ↦ hp i)]
    exact Finset.sum_congr rfl fun s _ ↦
      (ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hp i)).symm
  have hlow : ENNReal.ofReal (1 - commonForwardLabelLoss C p k) ≤ B := by
    
    
    let : NeZero k := ⟨by omega⟩
    have hne : (1 : Fin k) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (show 1 < k by omega)] at hv
      omega
    let e : Fin k → Fin k := fun i ↦ i + 1
    have he (i : Fin k) : e i ≠ i := by
      change i + 1 ≠ i
      intro hi
      have h := add_left_cancel (b := (1 : Fin k)) (c := 0) (hi.trans (add_zero i).symm)
      exact hne h
    have h := iidLabelGood_sum_weights_lower r hr Cᶜ (fun _ ↦ ∅) e he 0
      (fun _ ↦ by simp)
    simp only [Fintype.card_fin, mul_zero, add_zero] at h
    have hnonneg : 0 ≤ commonForwardLabelLoss C p k := add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ ↦ hp i))
    have hcast : ENNReal.ofReal (commonForwardLabelLoss C p k) =
        (k.choose 2 : ℝ≥0∞) * (∑ i, (r i) ^ 2) + (k : ℝ≥0∞) * ∑ i ∈ Cᶜ, r i := by
      rw [commonForwardLabelLoss, ENNReal.ofReal_add (by positivity)
          (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ ↦ hp i)),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ sq_nonneg (p i)),
        ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hp i)]
      simp only [r, ENNReal.ofReal_pow (hp _)]
    rw [ENNReal.ofReal_sub _ hnonneg, ENNReal.ofReal_one, hcast]
    refine h.trans_eq (Finset.sum_congr ?_ fun _ _ ↦ rfl)
    ext x
    simp [iidLabelGood, mem_injectiveCommonLabels]
  have hE0 : 0 ≤ (k.factorial : ℝ) * E :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ ↦
      Finset.prod_nonneg fun i _ ↦ hp i)
  have hlow' := (ENNReal.ofReal_le_ofReal_iff hE0).mp (hB ▸ hlow)
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hf : (k : ℝ) * ((k - 1).factorial : ℝ) = (k.factorial : ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred (show k ≠ 0 by omega)
  rw [sum_commonForwardCycles_singleton C hk p]
  apply (div_le_iff₀ hk0).mpr
  calc
    _ ≤ (k.factorial : ℝ) * E := hlow'
    _ = _ := by rw [← hf]; ring
end ReferenceWeights
section NearRankOne
variable [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
private def CommonForwardArcLower (ν : ι → Measure (Option ι)) (C : Finset ι) (p : ι → ℝ)
    (δ : ℝ) : Prop :=
  ∀ i ∈ C, ∀ j ∈ C, i ≠ j → (1 - δ) * p j ≤ (ν i).real {some j}
theorem integral_commonForwardCycles_singleton_lower (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (C : Finset ι) {k : ℕ} (hk : 2 ≤ k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    {δ : ℝ} (hδ : δ ≤ 1) (harc : CommonForwardArcLower ν C p δ) :
    (1 - δ) ^ k * ((1 - commonForwardLabelLoss C p k) / (k : ℝ)) ≤
      ∫ f, (realizedForwardCycleCount (commonForwardCycles C {k}) f : ℝ) ∂Measure.pi ν := by
  classical
  have h0 := sub_nonneg.mpr hδ
  rw [integral_realizedForwardCycleCount]
  calc
    _ ≤ (1 - δ) ^ k * ∑ σ ∈ commonForwardCycles C {k}, ∏ i ∈ σ.support, p i :=
      mul_le_mul_of_nonneg_left (commonForwardCycleReferenceWeight_lower C hk p hp hp₁)
        (pow_nonneg h0 k)
    _ = _ := Finset.mul_sum ..
    _ ≤ _ := by
      refine Finset.sum_le_sum fun σ hσ ↦ ?_
      obtain ⟨hcyc, hC, hlen⟩ := mem_commonForwardCycles.mp hσ
      rw [measureReal_forwardCycleEvent ν hcyc, ← Finset.mem_singleton.mp hlen,
        ← Finset.prod_const, ← σ.prod_comp σ.support p (fun _ hi ↦ Equiv.Perm.mem_support.mpr hi),
        ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun i _ ↦ mul_nonneg h0 (hp _)) fun i hi ↦
        harc i (hC hi) (σ i) (hC (Equiv.Perm.apply_mem_support.mpr hi))
          (Ne.symm (Equiv.Perm.mem_support.mp hi))
theorem integral_commonForwardCycleCount_eq_sum_lengths (ν : Measure (ι → Option ι))
    [IsFiniteMeasure ν] (C : Finset ι) (L : ℕ) :
    (∫ f, (commonForwardCycleCount C L f : ℝ) ∂ν) =
      ∑ k ∈ Finset.Icc 2 L,
        ∫ f, (realizedForwardCycleCount (commonForwardCycles C {k}) f : ℝ) ∂ν := by
  classical
  unfold commonForwardCycleCount
  simp only [integral_realizedForwardCycleCount]
  let S := commonForwardCycles C (Finset.Icc 2 L)
  have hm (σ : Equiv.Perm ι) (hσ : σ ∈ S) : σ.support.card ∈ Finset.Icc 2 L :=
    (mem_commonForwardCycles.mp hσ).2.2
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun σ ↦ ν.real (forwardCycleEvent σ))]
  refine Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext σ
  simp only [Finset.mem_filter, mem_commonForwardCycles, Finset.mem_singleton, S]
  constructor
  · rintro ⟨⟨hσ, hC, -⟩, hlen⟩
    exact ⟨hσ, hC, hlen⟩
  · rintro ⟨hσ, hC, rfl⟩
    exact ⟨⟨hσ, hC, hk⟩, rfl⟩
private noncomputable def commonForwardCycleHarmonic (L : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 L, (1 : ℝ) / k
omit [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)] in
theorem commonForwardLabelLoss_mono (C : Finset ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    Monotone (commonForwardLabelLoss C p) := by
  intro a b hab
  unfold commonForwardLabelLoss
  exact add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose 2 hab)
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (Finset.sum_nonneg fun i _ ↦ hp i))
omit [Fintype ι] [DecidableEq ι] [MeasurableSpace (Option ι)]
    [MeasurableSingletonClass (Option ι)] in
theorem commonForwardCycleHarmonic_lower {L : ℕ} (hL : 2 ≤ L) :
    Real.log (L : ℝ) - 1 ≤ commonForwardCycleHarmonic L := by
  have h₁ : 1 ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have he : (Finset.Icc 1 L).erase 1 = Finset.Icc 2 L := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hh := log_add_one_le_harmonic L
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  rw [← Finset.sum_erase_add (Finset.Icc 1 L) (fun j ↦ (j : ℝ)⁻¹) h₁, he,
    Nat.cast_one, inv_one] at hh
  have hlog : Real.log (L : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ L)
  unfold commonForwardCycleHarmonic
  simp only [one_div]
  linarith only [hh, hlog]
theorem integral_commonForwardCycleCount_lower_log (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (C : Finset ι) {L : ℕ} (hL : 2 ≤ L)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    {δ : ℝ} (hδ : δ ∈ Icc 0 1) (harc : CommonForwardArcLower ν C p δ)
    (harcLoss : (L : ℝ) * δ ≤ 1 / 100) (hlabelLoss : commonForwardLabelLoss C p L ≤ 1 / 100)
    (hlog : 100 ≤ Real.log (L : ℝ)) :
    (19 / 20 : ℝ) * Real.log (L : ℝ) ≤
      ∫ f, (commonForwardCycleCount C L f : ℝ) ∂Measure.pi ν := by
  let c : ℝ := 99 / 100
  have hc : 0 ≤ c := by norm_num [c]
  have hpow : c ≤ (1 - δ) ^ L := by
    have h := one_add_mul_le_pow (a := -δ) (by linarith only [hδ.2]) L
    simp only [← sub_eq_add_neg, mul_neg] at h
    dsimp [c]
    linarith only [h, harcLoss]
  rw [integral_commonForwardCycleCount_eq_sum_lengths]
  calc
    _ ≤ (c * c) * (Real.log (L : ℝ) - 1) := by dsimp [c]; linarith only [hlog]
    _ ≤ (c * c) * commonForwardCycleHarmonic L :=
      mul_le_mul_of_nonneg_left (commonForwardCycleHarmonic_lower hL) (mul_nonneg hc hc)
    _ ≤ _ := by
      rw [commonForwardCycleHarmonic, Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk ↦ ?_
      obtain ⟨hk₂, hkL⟩ := Finset.mem_Icc.mp hk
      refine le_trans ?_ (integral_commonForwardCycles_singleton_lower ν C hk₂ p hp hp₁ hδ.2 harc)
      rw [mul_assoc, mul_one_div]
      have hlabel := (commonForwardLabelLoss_mono C p hp hkL).trans hlabelLoss
      exact mul_le_mul (hpow.trans (pow_le_pow_of_le_one (sub_nonneg.mpr hδ.2)
        (sub_le_self _ hδ.1) hkL)) (div_le_div_of_nonneg_right (by dsimp [c]; linarith only [hlabel])
          (Nat.cast_nonneg k)) (div_nonneg hc (Nat.cast_nonneg k))
          (pow_nonneg (sub_nonneg.mpr hδ.2) _)
theorem measure_lt_commonForwardCycleCount_le (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (C : Finset ι) {L : ℕ} (hL : 2 ≤ L)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    {δ : ℝ} (hδ : δ ∈ Icc 0 1) (harc : CommonForwardArcLower ν C p δ)
    (harcLoss : (L : ℝ) * δ ≤ 1 / 100) (hlabelLoss : commonForwardLabelLoss C p L ≤ 1 / 100)
    (hlog : 100 ≤ Real.log (L : ℝ)) :
    (Measure.pi ν) {f | (commonForwardCycleCount C L f : ℝ) < (9 / 10 : ℝ) * Real.log L} ≤
      ENNReal.ofReal (1200 / Real.log (L : ℝ)) := by
  let B := Real.log (L : ℝ)
  let X (f : ι → Option ι) := (commonForwardCycleCount C L f : ℝ)
  let m := ∫ f, X f ∂Measure.pi ν
  have hm : (19 / 20 : ℝ) * B ≤ m :=
    integral_commonForwardCycleCount_lower_log ν C hL p hp hp₁ hδ harc harcLoss hlabelLoss hlog
  have hB : 0 < B := by linarith only [hlog]
  have hm₀ : 0 < m := by linarith only [hB, hm]
  have hsub : {f | X f < 9 / 10 * B} ⊆ {f | m / 19 ≤ |X f - m|} := by
    intro f hf
    change X f < 9 / 10 * B at hf
    change m / 19 ≤ |X f - m|
    rw [abs_sub_comm]
    exact le_trans (by linarith only [hf, hm] : m / 19 ≤ m - X f) (le_abs_self _)
  have hvar : Var[X; Measure.pi ν] ≤ m :=
    variance_realizedForwardCycleCount_le ν _ (fun _ hσ ↦ (mem_commonForwardCycles.mp hσ).1)
  refine (measure_mono hsub).trans ((meas_ge_le_variance_div_sq
    (realizedForwardCycleCount_memLp (Measure.pi ν) _) (by positivity : 0 < m / 19)).trans
    (ENNReal.ofReal_le_ofReal ((div_le_div_of_nonneg_right hvar (sq_nonneg _)).trans ?_)))
  calc
    m / (m / 19) ^ 2 = 361 / m := by field_simp; ring
    _ ≤ 380 / B := (div_le_div_iff₀ hm₀ hB).mpr (by linarith only [hm])
    _ ≤ 1200 / B := div_le_div_of_nonneg_right (by norm_num) hB.le
end NearRankOne
end StepC
end

-- TwoStablePairSizeSums
section
open Finset
namespace StepC
private def ValidPairSizes (n : ℕ) (p : ℕ × ℕ) : Prop :=
  2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 + p.2 ≤ n
private noncomputable def twoStablePairSizeKernel (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  (n : ℝ) ^ 3 / ((↑(n - p.1) : ℝ) * ↑(n - p.2)) *
    ((↑((n - p.1).descFactorial p.2) : ℝ) / ↑(n.descFactorial p.2))
theorem twoStablePairSizeKernel_nonneg (n : ℕ) (p : ℕ × ℕ) :
    0 ≤ twoStablePairSizeKernel n p := by
  unfold twoStablePairSizeKernel
  positivity
private theorem cast_descFactorial_eq_div {n k : ℕ} (hk : k ≤ n) :
    (n.descFactorial k : ℝ) = (↑n.factorial : ℝ) / ↑(n - k).factorial := by
  apply (eq_div_iff (by positivity)).2
  rw [mul_comm]
  exact_mod_cast Nat.factorial_mul_descFactorial hk
theorem twoStablePairSizeKernel_swap {n u v : ℕ} (h : u + v ≤ n) :
    twoStablePairSizeKernel n (v, u) = twoStablePairSizeKernel n (u, v) := by
  have hu : u ≤ n := by omega
  have hv : v ≤ n := by omega
  have huv : u ≤ n - v := by omega
  have hvu : v ≤ n - u := by omega
  have ht : n - v - u = n - u - v := by omega
  change (n : ℝ) ^ 3 / (↑(n - v) * ↑(n - u)) *
      (↑((n - v).descFactorial u) / ↑(n.descFactorial u)) =
    (n : ℝ) ^ 3 / (↑(n - u) * ↑(n - v)) *
      (↑((n - u).descFactorial v) / ↑(n.descFactorial v))
  rw [cast_descFactorial_eq_div hu, cast_descFactorial_eq_div hv,
    cast_descFactorial_eq_div huv, cast_descFactorial_eq_div hvu, ht]
  rw [mul_comm (↑(n - v) : ℝ) ↑(n - u)]
  congr 1
  field_simp
private noncomputable def pairSizeBetaFactor (n k : ℕ) : ℝ :=
  (↑(k - 1).factorial : ℝ) * ↑(n - k - 1).factorial / ↑(n - 1).factorial
private theorem cast_factorial_pred {k : ℕ} (hk : 0 < k) :
    (k.factorial : ℝ) = (k : ℝ) * ↑(k - 1).factorial := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp [Nat.factorial_succ]
theorem twoStablePairSizeKernel_eq_beta_factors {n u v : ℕ} (h : ValidPairSizes n (u, v)) :
    twoStablePairSizeKernel n (u, v) =
      ((n.factorial : ℝ) ^ 2 / ↑(n - u - v).factorial) *
        (pairSizeBetaFactor n u * pairSizeBetaFactor n v /
          ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial)) := by
  obtain ⟨hu, hv, huv⟩ := h
  have hvn : v ≤ n := by omega
  have hvu : v ≤ n - u := by omega
  have hnu : 0 < n - u := by omega
  have hnv : 0 < n - v := by omega
  have hn : 0 < n := by omega
  calc
    _ = (n : ℝ) ^ 3 * ↑(n - u - 1).factorial * ↑(n - v - 1).factorial /
        (↑(n - u - v).factorial * ↑n.factorial) := by
      change (n : ℝ) ^ 3 / (↑(n - u) * ↑(n - v)) *
        (↑((n - u).descFactorial v) / ↑(n.descFactorial v)) = _
      rw [cast_descFactorial_eq_div hvu, cast_descFactorial_eq_div hvn,
        cast_factorial_pred hnu, cast_factorial_pred hnv]
      field_simp
    _ = _ := by
      unfold pairSizeBetaFactor
      rw [cast_factorial_pred hn]
      field_simp
private theorem cast_choose_eq_factorial_div {a b : ℕ} (h : b ≤ a) :
    (a.choose b : ℝ) = (a.factorial : ℝ) / (b.factorial * ((a - b).factorial : ℝ)) := by
  apply (eq_div_iff (by positivity)).2
  rw [← mul_assoc]
  exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
theorem twoStablePairSizeKernel_eq_choose {n u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hs : u + v ≤ n) :
    twoStablePairSizeKernel n (u, v) =
      (n : ℝ) ^ 2 / (u : ℝ) / ((n - 1).choose u : ℝ) *
        ((n - v - 1).choose (u - 1) : ℝ) := by
  change (n : ℝ) ^ 3 / ((n - u : ℕ) * ((n - v : ℕ) : ℝ)) *
    (((n - u).descFactorial v : ℝ) / (n.descFactorial v : ℝ)) = _
  rw [cast_descFactorial_eq_div (show v ≤ n - u by omega),
    cast_descFactorial_eq_div (show v ≤ n by omega),
    cast_choose_eq_factorial_div (show u ≤ n - 1 by omega),
    cast_choose_eq_factorial_div (show u - 1 ≤ n - v - 1 by omega),
    show n - 1 - u = n - u - 1 by omega,
    show n - v - 1 - (u - 1) = n - u - v by omega,
    cast_factorial_pred (show 0 < n - u by omega),
    cast_factorial_pred (show 0 < n - v by omega),
    cast_factorial_pred (show 0 < n by omega),
    cast_factorial_pred hu]
  have hnu : 0 < n - u := by omega
  have hnv : 0 < n - v := by omega
  field_simp
private theorem sum_row_choose_from {n u a : ℕ} (hu : 1 ≤ u) (ha : a ≤ n - u)
    (hun : u ≤ n) :
    (∑ v ∈ Icc a (n - u), (n - v - 1).choose (u - 1)) = (n - a).choose u := by
  calc
    _ = ∑ j ∈ Icc (u - 1) (n - a - 1), j.choose (u - 1) := by
      refine sum_nbij' (fun v ↦ n - v - 1) (fun j ↦ n - j - 1) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl)
        <;> intro i hi <;> simp only [mem_Icc] at * <;> omega
    _ = _ := by rw [Nat.sum_Icc_choose]; congr 1 <;> omega
private theorem sum_row_choose {n u : ℕ} (hu : 1 ≤ u) (hun : u < n) :
    (∑ v ∈ Icc 1 (n - u), (n - v - 1).choose (u - 1)) = (n - 1).choose u :=
  sum_row_choose_from hu (by omega) hun.le
theorem sum_twoStablePairSizeKernel_row {n u : ℕ} (hu : 1 ≤ u) (hun : u < n) :
    (∑ v ∈ Icc 1 (n - u), twoStablePairSizeKernel n (u, v)) = (n : ℝ)^2 / u := by
  have hpos : 0 < ((n - 1).choose u : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : u ≤ n - 1)
  calc
    _ = ((n : ℝ)^2 / u / ((n - 1).choose u : ℝ)) *
        ∑ v ∈ Icc 1 (n-u), ((n-v-1).choose (u-1) : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl fun v hv ↦ twoStablePairSizeKernel_eq_choose hu (mem_Icc.mp hv).1
        (by have := (mem_Icc.mp hv).2; omega)
    _ = _ := by rw [← Nat.cast_sum, sum_row_choose hu hun, div_mul_cancel₀ _ hpos.ne']
private theorem sum_by_row_le {n : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) (t : Finset ℕ) (ht : ∀ p ∈ s, p.1 ∈ t)
    (g : ℕ → ℝ) (hg : ∀ u ∈ t, 0 ≤ g u)
    (hrow : ∀ u ∈ t, 2 ≤ u → u + 2 ≤ n →
      (∑ p ∈ s.filter (fun p ↦ p.1 = u), twoStablePairSizeKernel n p) ≤ g u) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ ∑ u ∈ t, g u := by
  rw [← sum_fiberwise_of_maps_to ht]
  refine sum_le_sum fun u hu ↦ ?_
  by_cases he : s.filter (fun p ↦ p.1 = u) = ∅
  · simpa [he] using hg u hu
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.mpr he
  obtain ⟨hps, hpu⟩ := mem_filter.mp hp
  obtain ⟨h₁,h₂,h₃⟩ := hs p hps
  subst u
  exact hrow _ hu h₁ (by omega)
private theorem sum_fiber_le_of_row {n u : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) (f : ℕ → ℝ) (hf : ∀ v, 0 ≤ f v)
    (h : ∀ p ∈ s, p.1 = u → twoStablePairSizeKernel n p ≤ f p.2) :
    (∑ p ∈ s.filter (fun p ↦ p.1 = u), twoStablePairSizeKernel n p) ≤
      ∑ v ∈ Icc 1 (n-u), f v := by
  let row := s.filter (fun p ↦ p.1 = u)
  have hbox : row ⊆ {u} ×ˢ Icc 1 (n-u) := by
    intro p hp
    obtain ⟨hps, hu⟩ := mem_filter.mp hp
    obtain ⟨_, hv, hn⟩ := hs p hps
    exact mem_product.mpr ⟨mem_singleton.mpr hu, mem_Icc.mpr ⟨by omega, by omega⟩⟩
  calc
    _ ≤ ∑ p ∈ row, f p.2 := sum_le_sum fun p hp ↦ h p (mem_filter.mp hp).1 (mem_filter.mp hp).2
    _ ≤ ∑ p ∈ {u} ×ˢ Icc 1 (n-u), f p.2 := sum_le_sum_of_subset_of_nonneg hbox (fun p _ _ ↦ hf p.2)
    _ = _ := by rw [sum_product, sum_singleton]
private theorem sum_inv_Icc_le_log (m : ℕ) :
    (∑ v ∈ Icc 1 m, (v : ℝ)⁻¹) ≤ 1 + Real.log m := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log m
theorem sum_twoStablePairSizeKernel_le_rows {n : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) (U : Finset ℕ) (hU : ∀ p ∈ s, p.1 ∈ U) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ (n : ℝ)^2 * ∑ u ∈ U, (u : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ u ∈ U, (n : ℝ)^2 / u := by
      apply sum_by_row_le s hs U hU _ (fun _ _ ↦ by positivity)
      intro u _ hu hun
      rw [← sum_twoStablePairSizeKernel_row (by omega : 1 ≤ u) (by omega : u < n)]
      exact sum_fiber_le_of_row s hs _ (fun v ↦ twoStablePairSizeKernel_nonneg n (u,v))
        (by rintro ⟨_,v⟩ _ rfl; exact le_rfl)
    _ = _ := by simp [div_eq_mul_inv, mul_sum]
theorem sum_twoStablePairSizeKernel_le_total {n : ℕ} (_hn : 0 < n) (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ (n : ℝ)^2 * (1 + Real.log n) := by
  calc
    _ ≤ (n : ℝ)^2 * ∑ u ∈ Icc 1 n, (u : ℝ)⁻¹ :=
      sum_twoStablePairSizeKernel_le_rows s hs _ fun p hp ↦
        mem_Icc.mpr ⟨by have := (hs p hp).1; omega, (Nat.le_add_right _ _).trans (hs p hp).2.2⟩
    _ ≤ (n : ℝ)^2 * (1 + Real.log n) :=
      mul_le_mul_of_nonneg_left (sum_inv_Icc_le_log n) (sq_nonneg _)
private theorem sum_le_filtered_cover {α : Type*} (s : Finset α) (f : α → ℝ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hf : ∀ p ∈ s, 0 ≤ f p) (hcov : ∀ p ∈ s, P p ∨ Q p) :
    (∑ p ∈ s, f p) ≤ (∑ p ∈ s.filter P, f p) + ∑ p ∈ s.filter Q, f p := by
  simp only [sum_filter, ← sum_add_distrib]
  refine sum_le_sum fun p hp ↦ ?_
  by_cases hP : P p
  · by_cases hQ : Q p
    · simp only [hP, hQ, ite_true]
      exact le_add_of_nonneg_right (hf p hp)
    · simp [hP, hQ]
  · have hQ := (hcov p hp).resolve_left hP
    simp [hP, hQ]
private def swapSizePairs (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  s.map (Equiv.prodComm ℕ ℕ).toEmbedding
private theorem mem_swapSizePairs {p : ℕ × ℕ} {s : Finset (ℕ × ℕ)} :
    p ∈ swapSizePairs s ↔ p.swap ∈ s := by
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := mem_map.mp hp
    change q.swap = p at hqp
    rw [← hqp, Prod.swap_swap]
    exact hq
  · intro hp
    exact mem_map.mpr ⟨p.swap, hp, Prod.swap_swap _⟩
private theorem sum_twoStablePairSizeKernel_swapSizePairs {n : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) :
    (∑ p ∈ swapSizePairs s, twoStablePairSizeKernel n p) =
      ∑ p ∈ s, twoStablePairSizeKernel n p := by
  rw [swapSizePairs, sum_map]
  exact sum_congr rfl fun p hp ↦ twoStablePairSizeKernel_swap (hs p hp).2.2
private theorem validPairSizes_swap {n : ℕ} {p : ℕ × ℕ} (h : ValidPairSizes n p) :
    ValidPairSizes n p.swap := by
  exact ⟨h.2.1, h.1, by simpa [add_comm] using h.2.2⟩
private theorem sum_inv_outside_orientation_interval_le {n L : ℕ}
    (ht : 1 ≤ Real.log (n : ℝ)) (hLt : (L : ℝ) ≤ Real.log (n : ℝ)) :
    (∑ u ∈ (Icc 1 n).filter (fun u : ℕ ↦ u < L ∨ n / (Real.log (n : ℝ)) ^ 3 < (u : ℝ)),
      (u : ℝ)⁻¹) ≤ 2 + 4 * Real.log (Real.log (n : ℝ)) := by
  classical
  let t := Real.log (n : ℝ)
  let y := (n : ℝ) / t ^ 3
  let S := (Icc 1 n).filter (fun u : ℕ ↦ u < L ∨ y < (u : ℝ))
  change (∑ u ∈ S, (u : ℝ)⁻¹) ≤ 2 + 4 * Real.log t
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hn : (n : ℝ) ≠ 0 := by
    intro h
    norm_num [h] at ht
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) (pow_nonneg ht0.le _)
  have hyn : y ≤ n := div_le_self (Nat.cast_nonneg _) (one_le_pow₀ ht)
  have hfloor : ⌊y⌋₊ ≤ n := by exact_mod_cast (Nat.floor_le hy0).trans hyn
  have hsub : Icc 1 ⌊y⌋₊ ⊆ Icc 1 n := Icc_subset_Icc_right hfloor
  have lown : S.filter (· < L) ⊆ Icc 1 ⌊t⌋₊ := by
    intro u hu
    obtain ⟨huS, huL⟩ := mem_filter.mp hu
    exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp huS).1).1,
      Nat.le_floor ((Nat.cast_le.mpr (Nat.le_of_lt huL)).trans hLt)⟩
  have highn : S.filter (fun u ↦ ¬u < L) ⊆ Icc 1 n \ Icc 1 ⌊y⌋₊ := by
    intro u hu
    obtain ⟨huS, huL⟩ := mem_filter.mp hu
    obtain ⟨hun, huy⟩ := mem_filter.mp huS
    exact mem_sdiff.mpr ⟨hun, fun h ↦ ((Nat.floor_lt hy0).mpr (huy.resolve_left huL)).not_ge
      (mem_Icc.mp h).2⟩
  have hlo := harmonic_floor_le_one_add_log t ht
  have hhi := harmonic_le_one_add_log n
  have hfloorlo := log_le_harmonic_floor y hy0
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlo hhi hfloorlo
  rw [show Real.log y = t - 3 * Real.log t by
    dsimp only [y]; rw [Real.log_div hn (pow_ne_zero _ ht0.ne'), Real.log_pow]; norm_num [t]] at hfloorlo
  rw [← sum_filter_add_sum_filter_not S (· < L)]
  calc
    _ ≤ (∑ u ∈ Icc 1 ⌊t⌋₊, (u : ℝ)⁻¹) + ∑ u ∈ Icc 1 n \ Icc 1 ⌊y⌋₊, (u : ℝ)⁻¹ :=
      add_le_add (sum_le_sum_of_subset_of_nonneg lown fun _ _ _ ↦ by positivity)
        (sum_le_sum_of_subset_of_nonneg highn fun _ _ _ ↦ by positivity)
    _ ≤ _ := by
      rw [sum_sdiff_eq_sub hsub]
      change _ ≤ 1 + t at hhi
      linarith only [hlo, hhi, hfloorlo]
private def RegularOrientationPair (n L : ℕ) (p : ℕ × ℕ) : Prop :=
  L ≤ p.1 ∧ L ≤ p.2 ∧ (p.1 : ℝ) ≤ n / (Real.log n)^3 ∧ (p.2 : ℝ) ≤ n / (Real.log n)^3
theorem sum_twoStablePairSizeKernel_le_not_regularOrientationPair {n L : ℕ}
    (ht : 1 ≤ Real.log (n : ℝ)) (hLt : (L : ℝ) ≤ Real.log (n : ℝ))
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p)
    (he : ∀ p ∈ s, ¬RegularOrientationPair n L p) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ 2 * (n : ℝ)^2 * (2 + 4 * Real.log (Real.log n)) := by
  classical
  let U := (Icc 1 n).filter fun u : ℕ ↦ u < L ∨ n / (Real.log (n : ℝ))^3 < (u : ℝ)
  have hcover (p) (hp : p ∈ s) : p.1 ∈ U ∨ p.2 ∈ U := by
    obtain ⟨hu, hv, huv⟩ := hs p hp
    have hor : (p.1 < L ∨ n / (Real.log (n : ℝ))^3 < (p.1 : ℝ)) ∨
        (p.2 < L ∨ n / (Real.log (n : ℝ))^3 < (p.2 : ℝ)) := by
      by_contra! h
      exact he p hp ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩
    exact hor.imp
      (fun h ↦ mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h⟩)
      (fun h ↦ mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h⟩)
  let A := s.filter fun p ↦ p.1 ∈ U
  let B := s.filter fun p ↦ p.2 ∈ U
  have hB (p) (hp : p ∈ B) : ValidPairSizes n p := hs p (mem_filter.mp hp).1
  have hA := sum_twoStablePairSizeKernel_le_rows A (fun p hp ↦ hs p (mem_filter.mp hp).1) U
    (fun p hp ↦ (mem_filter.mp hp).2)
  have hB' := sum_twoStablePairSizeKernel_le_rows (swapSizePairs B)
    (fun p hp ↦ by simpa using validPairSizes_swap (hB p.swap (mem_swapSizePairs.mp hp))) U
    (fun _ hp ↦ (mem_filter.mp (mem_swapSizePairs.mp hp)).2)
  rw [sum_twoStablePairSizeKernel_swapSizePairs B hB] at hB'
  calc
    _ ≤ (∑ p ∈ A, twoStablePairSizeKernel n p) + ∑ p ∈ B, twoStablePairSizeKernel n p :=
      sum_le_filtered_cover s _ _ _ (fun p _ ↦ twoStablePairSizeKernel_nonneg n p) hcover
    _ ≤ 2 * (n : ℝ)^2 * ∑ u ∈ U, (u : ℝ)⁻¹ := by linarith only [hA,hB']
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_outside_orientation_interval_le ht hLt)
      (by positivity)
theorem sum_twoStablePairSizeWeights_le {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) {C B : ℝ} (hC : 0 ≤ C)
    (hw : ∀ p ∈ s, w p ≤ C * (1 + Real.log n) * twoStablePairSizeKernel n p)
    (hB : (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ B) :
    (∑ p ∈ s, w p) ≤ C * (1 + Real.log n) * B := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  calc
    _ ≤ ∑ p ∈ s, (C * (1 + Real.log n)) * twoStablePairSizeKernel n p := sum_le_sum hw
    _ = (C * (1 + Real.log n)) * ∑ p ∈ s, twoStablePairSizeKernel n p := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
end StepC
end

-- PivotBackgroundGeometry
section
open Set StableMarriage
open scoped BigOperators
namespace StepC
private noncomputable def backgroundMaleCeiling (n : ℕ) : ℝ :=
  16 * Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)
private noncomputable def backgroundWeightCeiling (n : ℕ) : ℝ :=
  2060 * Real.log n / n
private noncomputable def backgroundLabelBudget (n L : ℕ) : ℝ :=
  ((L.choose 2 : ℝ) + L * (2 * n / (Real.log n) ^ 3)) * backgroundWeightCeiling n
theorem commonForwardLabelLoss_le_backgroundLabelBudget {n L : ℕ}
    (C : Finset (Fin n)) (p : Fin n → ℝ)
    (hC : (Cᶜ.card : ℝ) ≤ 2 * n / (Real.log n) ^ 3)
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    (hP : ∀ i, p i ≤ backgroundWeightCeiling n) :
    commonForwardLabelLoss C p L ≤ backgroundLabelBudget n L := by
  have hP₀ : 0 ≤ backgroundWeightCeiling n := by unfold backgroundWeightCeiling; positivity
  exact (commonForwardLabelLoss_le_of_weight_le C p L hp hp₁ hP).trans
    (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg L))) hP₀)
private abbrev BackgroundCycleBudget (n L : ℕ) : Prop :=
  premiseOf (@CompLP.BackgroundCycleBudget.self_ n L)
private theorem BackgroundCycleBudget.cutoff_two {n L : ℕ} (h : BackgroundCycleBudget n L) :
    2 ≤ L := by
  obtain ⟨hf, _, _, _⟩ := h
  exact hf
private theorem BackgroundCycleBudget.log_cutoff {n L : ℕ} (h : BackgroundCycleBudget n L) :
    100 ≤ Real.log (L : ℝ) := by
  obtain ⟨_, hf, _, _⟩ := h
  exact hf
private theorem BackgroundCycleBudget.arc {n L : ℕ} (h : BackgroundCycleBudget n L) :
    ∀ Y : ℝ, (n : ℝ) ^ (1 / 10 : ℝ) ≤ Y → (L : ℝ) * (backgroundMaleCeiling n + 1 / Y) ≤ 1 / 100 := by
  obtain ⟨_, _, hf, _⟩ := h
  exact hf
private theorem BackgroundCycleBudget.label {n L : ℕ} (h : BackgroundCycleBudget n L) :
    backgroundLabelBudget n L ≤ 1 / 100 := by
  obtain ⟨_, _, _, hf⟩ := h
  exact hf
private theorem BackgroundCycleBudget.mk {n L : ℕ} (h0 : 2 ≤ L) (h1 : 100 ≤ Real.log (L : ℝ)) (h2 : ∀ Y : ℝ, (n : ℝ) ^ (1 / 10 : ℝ) ≤ Y → (L : ℝ) * (backgroundMaleCeiling n + 1 / Y) ≤ 1 / 100) (h3 : backgroundLabelBudget n L ≤ 1 / 100) :
    BackgroundCycleBudget n L := by
  constructor
  · exact h0
  · exact h1
  · exact h2
  · exact h3
theorem commonLabels_compl_eq_relative_support {n : ℕ} (μ ν : Matching n) :
    (Finset.univ.filter fun i : Fin n ↦ μ i = ν i)ᶜ =
      (relativeMenPermutation μ ν).support := by
  classical
  ext i
  simp [relativeMenPermutation, Equiv.Perm.mem_support, Equiv.symm_apply_eq]
end StepC
end

-- LogarithmicCutoffs
section
open Filter
open scoped Topology BigOperators
namespace StepC
end StepC
end

-- PivotPairEnvelopeScale
section
open Filter
open scoped Topology
namespace StepC
end StepC
end

-- TwoStableScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
variable {n : ℕ}
private def JointSpouseCell (μ ν : Matching n) (q : ScorePairIndex n) : Prop :=
  μ q.1 = q.2 ∨ ν q.1 = q.2
private instance (μ ν : Matching n) (q : ScorePairIndex n) : Decidable (JointSpouseCell μ ν q) :=
  inferInstanceAs (Decidable (_ ∨ _))
private abbrev JointSpouseIndex (μ ν : Matching n) := {q : ScorePairIndex n // JointSpouseCell μ ν q}
private abbrev JointOffSpouseIndex (μ ν : Matching n) := {q : ScorePairIndex n // ¬ JointSpouseCell μ ν q}
private abbrev JointSpouseScores (μ ν : Matching n) := JointSpouseIndex μ ν → ℝ × ℝ
private abbrev JointOffSpouseScores (μ ν : Matching n) := JointOffSpouseIndex μ ν → ℝ × ℝ
private noncomputable def jointSpouseScoreLaw (μ ν : Matching n) : Measure (JointSpouseScores μ ν) :=
  Measure.pi fun _ ↦ unitScorePairLaw
private noncomputable def jointOffSpouseScoreLaw (μ ν : Matching n) :
    Measure (JointOffSpouseScores μ ν) :=
  Measure.pi fun _ ↦ unitScorePairLaw
private instance (μ ν : Matching n) : IsProbabilityMeasure (jointOffSpouseScoreLaw μ ν) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : JointOffSpouseIndex μ ν ↦
    unitScorePairLaw))
private def scoresByCell (n : ℕ) : ScoreProfile n ≃ᵐ (ScorePairIndex n → ℝ × ℝ) :=
  (splitScorePairs (Equiv.refl (Fin n))).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      fun q ↦ q.1 = q.2).symm
private theorem measurePreserving_scoresByCell (n : ℕ) :
    MeasurePreserving (scoresByCell n) (continuousScoreLaw n)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScorePairLaw) :=
  ((measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScorePairLaw)
    fun q : ScorePairIndex n ↦ q.1 = q.2).symm _).comp
    (measurePreserving_splitScorePairs (Equiv.refl (Fin n)))
private theorem scoresByCell_apply (x : ScoreProfile n) (q : ScorePairIndex n) :
    scoresByCell n x q = (x (.inl q.1) q.2, x (.inr q.2) q.1) := by
  classical
  by_cases h : q.1 = q.2
  · obtain ⟨i, j⟩ := q
    change i = j at h
    subst j
    simpa [scoresByCell, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, diagonalPairAt] using
      diagonalPairAt_splitScorePairs (Equiv.refl (Fin n)) x i
  · simpa [scoresByCell, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, h] using
      splitScorePairs_offDiagonal_apply (Equiv.refl (Fin n)) x ⟨q, h⟩
private def splitTwoMatchingScores (μ ν : Matching n) :
    ScoreProfile n ≃ᵐ JointSpouseScores μ ν × JointOffSpouseScores μ ν :=
  (scoresByCell n).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      (JointSpouseCell μ ν))
theorem measurePreserving_splitTwoMatchingScores (μ ν : Matching n) :
    MeasurePreserving (splitTwoMatchingScores μ ν) (continuousScoreLaw n)
      ((jointSpouseScoreLaw μ ν).prod (jointOffSpouseScoreLaw μ ν)) :=
  (measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScorePairLaw)
    (JointSpouseCell μ ν)).comp (measurePreserving_scoresByCell n)
theorem splitTwoMatchingScores_spouse_apply (μ ν : Matching n) (x : ScoreProfile n)
    (q : JointSpouseIndex μ ν) :
    (splitTwoMatchingScores μ ν x).1 q = (x (.inl q.val.1) q.val.2, x (.inr q.val.2) q.val.1) :=
  scoresByCell_apply x q.val
theorem splitTwoMatchingScores_offSpouse_apply (μ ν : Matching n) (x : ScoreProfile n)
    (q : JointOffSpouseIndex μ ν) :
    (splitTwoMatchingScores μ ν x).2 q = (x (.inl q.val.1) q.val.2, x (.inr q.val.2) q.val.1) :=
  scoresByCell_apply x q.val
private def jointManSpouseScoreLeft {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  (d ⟨(m, μ m), Or.inl rfl⟩).1
private def jointManSpouseScoreRight {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  (d ⟨(m, ν m), Or.inr rfl⟩).1
private def jointWomanSpouseScoreLeft {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  (d ⟨(μ.symm w, w), Or.inl (μ.apply_symm_apply w)⟩).2
private def jointWomanSpouseScoreRight {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  (d ⟨(ν.symm w, w), Or.inr (ν.apply_symm_apply w)⟩).2
@[simp] theorem jointManSpouseScoreLeft_split (μ ν : Matching n) (x : ScoreProfile n) (m : Fin n) :
    jointManSpouseScoreLeft (splitTwoMatchingScores μ ν x).1 m = x (.inl m) (μ m) := by
  rw [jointManSpouseScoreLeft, splitTwoMatchingScores_spouse_apply]
@[simp] theorem jointManSpouseScoreRight_split (μ ν : Matching n) (x : ScoreProfile n) (m : Fin n) :
    jointManSpouseScoreRight (splitTwoMatchingScores μ ν x).1 m = x (.inl m) (ν m) := by
  rw [jointManSpouseScoreRight, splitTwoMatchingScores_spouse_apply]
@[simp] theorem jointWomanSpouseScoreLeft_split (μ ν : Matching n) (x : ScoreProfile n) (w : Fin n) :
    jointWomanSpouseScoreLeft (splitTwoMatchingScores μ ν x).1 w = x (.inr w) (μ.symm w) := by
  rw [jointWomanSpouseScoreLeft, splitTwoMatchingScores_spouse_apply]
@[simp] theorem jointWomanSpouseScoreRight_split (μ ν : Matching n) (x : ScoreProfile n) (w : Fin n) :
    jointWomanSpouseScoreRight (splitTwoMatchingScores μ ν x).1 w = x (.inr w) (ν.symm w) := by
  rw [jointWomanSpouseScoreRight, splitTwoMatchingScores_spouse_apply]
private def jointNonblockingScoreCell (x₁ y₁ x₂ y₂ : ℝ) : Set (ℝ × ℝ) :=
  nonblockingScoreCell x₁ y₁ ∩ nonblockingScoreCell x₂ y₂
theorem measurableSet_jointNonblockingScoreCell (x₁ y₁ x₂ y₂ : ℝ) :
    MeasurableSet (jointNonblockingScoreCell x₁ y₁ x₂ y₂) :=
  (measurableSet_Iio.prod measurableSet_Iio).compl.inter
    (measurableSet_Iio.prod measurableSet_Iio).compl
private def jointNonblockingCellAt {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (q : ScorePairIndex n) : Set (ℝ × ℝ) :=
  jointNonblockingScoreCell (jointManSpouseScoreLeft d q.1) (jointWomanSpouseScoreLeft d q.2)
    (jointManSpouseScoreRight d q.1) (jointWomanSpouseScoreRight d q.2)
private def jointMarkedNonblocking (μ ν : Matching n) : Set (JointSpouseScores μ ν) :=
  {d | ∀ q : JointSpouseIndex μ ν, d q ∈ jointNonblockingCellAt d q.val}
private def jointOffSpouseNonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    Set (JointOffSpouseScores μ ν) :=
  univ.pi fun q ↦ jointNonblockingCellAt d q.val
theorem measurableSet_jointMarkedNonblocking (μ ν : Matching n) :
    MeasurableSet (jointMarkedNonblocking μ ν) := by
  unfold jointMarkedNonblocking
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun q ↦ ?_
  have hfst (i : JointSpouseIndex μ ν) : Measurable (fun d : JointSpouseScores μ ν ↦ (d i).1) :=
    measurable_fst.comp (measurable_pi_apply i)
  have hsnd (i : JointSpouseIndex μ ν) : Measurable (fun d : JointSpouseScores μ ν ↦ (d i).2) :=
    measurable_snd.comp (measurable_pi_apply i)
  simpa only [jointNonblockingCellAt, jointNonblockingScoreCell, nonblockingScoreCell,
    jointManSpouseScoreLeft, jointWomanSpouseScoreLeft, jointManSpouseScoreRight,
    jointWomanSpouseScoreRight, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
    ← Set.ofPred_and, Set.compl_ofPred] using
      (((measurableSet_lt (hfst q) (hfst ⟨(q.val.1, μ q.val.1), Or.inl rfl⟩)).inter
        (measurableSet_lt (hsnd q) (hsnd ⟨(μ.symm q.val.2, q.val.2),
          Or.inl (μ.apply_symm_apply q.val.2)⟩))).compl.inter
      ((measurableSet_lt (hfst q) (hfst ⟨(q.val.1, ν q.val.1), Or.inr rfl⟩)).inter
        (measurableSet_lt (hsnd q) (hsnd ⟨(ν.symm q.val.2, q.val.2),
          Or.inr (ν.apply_symm_apply q.val.2)⟩))).compl)
theorem measurableSet_jointOffSpouseNonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    MeasurableSet (jointOffSpouseNonblocking d) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_jointNonblockingScoreCell _ _ _ _
private theorem isScoreStable_iff_forall_nonblockingScoreCell (μ : Matching n)
    (x : ScoreProfile n) :
    IsScoreStable x μ ↔ ∀ q : ScorePairIndex n,
      (x (.inl q.1) q.2, x (.inr q.2) q.1) ∈
        nonblockingScoreCell (x (.inl q.1) (μ q.1)) (x (.inr q.2) (μ.symm q.2)) := by
  simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio]
  constructor
  · intro h q hlt
    have hne : μ q.1 ≠ q.2 := fun heq ↦ (lt_irrefl _) (heq ▸ hlt.1)
    exact h q.1 q.2 ⟨hne, hlt.1, hlt.2⟩
  · intro h m w hblock
    exact h (m, w) ⟨hblock.2.1, hblock.2.2⟩
theorem twoStable_iff_splitTwoMatchingScores (μ ν : Matching n) (x : ScoreProfile n) :
    IsScoreStable x μ ∧ IsScoreStable x ν ↔
      (splitTwoMatchingScores μ ν x).1 ∈ jointMarkedNonblocking μ ν ∧
      (splitTwoMatchingScores μ ν x).2 ∈
        jointOffSpouseNonblocking (splitTwoMatchingScores μ ν x).1 := by
  let d := (splitTwoMatchingScores μ ν x).1
  let v := (splitTwoMatchingScores μ ν x).2
  have hleft := isScoreStable_iff_forall_nonblockingScoreCell μ x
  have hright := isScoreStable_iff_forall_nonblockingScoreCell ν x
  have hall : IsScoreStable x μ ∧ IsScoreStable x ν ↔ ∀ q : ScorePairIndex n,
      (x (.inl q.1) q.2, x (.inr q.2) q.1) ∈ jointNonblockingCellAt d q := by
    simp only [d, jointNonblockingCellAt, jointNonblockingScoreCell, Set.mem_inter_iff,
      jointManSpouseScoreLeft_split, jointManSpouseScoreRight_split,
      jointWomanSpouseScoreLeft_split, jointWomanSpouseScoreRight_split, hleft, hright, forall_and]
  rw [hall]
  change _ ↔ d ∈ jointMarkedNonblocking μ ν ∧ v ∈ jointOffSpouseNonblocking d
  constructor
  · intro h
    constructor
    · intro q
      rw [show d q = _ from splitTwoMatchingScores_spouse_apply μ ν x q]
      exact h q.val
    · refine Set.mem_pi.mpr fun q _ ↦ ?_
      rw [show v q = _ from splitTwoMatchingScores_offSpouse_apply μ ν x q]
      exact h q.val
  · rintro ⟨hd, hv⟩ q
    by_cases hq : JointSpouseCell μ ν q
    · simpa only [d, splitTwoMatchingScores_spouse_apply] using hd ⟨q, hq⟩
    · have h := Set.mem_pi.mp hv ⟨q, hq⟩ (Set.mem_univ _)
      simpa only [v, splitTwoMatchingScores_offSpouse_apply] using h
private noncomputable def jointOffSpouseCellLaw {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (q : JointOffSpouseIndex μ ν) : Measure (ℝ × ℝ) :=
  unitScorePairLaw.restrict (jointNonblockingCellAt d q.val)
private instance {μ ν : Matching n} (d : JointSpouseScores μ ν) (q : JointOffSpouseIndex μ ν) :
    IsFiniteMeasure (jointOffSpouseCellLaw d q) :=
  inferInstanceAs (IsFiniteMeasure (unitScorePairLaw.restrict (jointNonblockingCellAt d q.val)))
theorem jointOffSpouseScoreLaw_restrict_nonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    (jointOffSpouseScoreLaw μ ν).restrict (jointOffSpouseNonblocking d) =
      Measure.pi (jointOffSpouseCellLaw d) :=
  Measure.restrict_pi_pi _ _
theorem jointOffSpouseScoreLaw_nonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) =
      ∏ q : JointOffSpouseIndex μ ν, unitScorePairLaw (jointNonblockingCellAt d q.val) :=
  Measure.pi_pi _ _
private noncomputable def normalizedJointOffSpouseCellLaw {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (q : JointOffSpouseIndex μ ν) : Measure (ℝ × ℝ) :=
  (jointOffSpouseCellLaw d q univ)⁻¹ • jointOffSpouseCellLaw d q
private instance {μ ν : Matching n} (d : JointSpouseScores μ ν) (q : JointOffSpouseIndex μ ν) :
    IsFiniteMeasure (normalizedJointOffSpouseCellLaw d q) := by
  constructor
  rw [normalizedJointOffSpouseCellLaw, Measure.smul_apply, smul_eq_mul, mul_comm]
  exact (ENNReal.mul_inv_ne_top _).lt_top
private noncomputable def jointOffSpouseProbabilityLaw {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    Measure (JointOffSpouseScores μ ν) :=
  (jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d))⁻¹ •
    (jointOffSpouseScoreLaw μ ν).restrict (jointOffSpouseNonblocking d)
theorem jointOffSpouseProbabilityLaw_eq_pi {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    jointOffSpouseProbabilityLaw d = Measure.pi (normalizedJointOffSpouseCellLaw d) := by
  symm
  refine Measure.pi_eq fun s _ ↦ ?_
  rw [jointOffSpouseProbabilityLaw, jointOffSpouseScoreLaw_nonblocking,
    jointOffSpouseScoreLaw_restrict_nonblocking, Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [normalizedJointOffSpouseCellLaw, jointOffSpouseCellLaw, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply_univ]
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ ↦ Or.inr (measure_ne_top unitScorePairLaw _)),
    Finset.prod_mul_distrib]
theorem jointOffSpouseScoreLaw_restrict_eq_smul_probabilityLaw {μ ν : Matching n}
    (d : JointSpouseScores μ ν)
    (hd : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0) :
    (jointOffSpouseScoreLaw μ ν).restrict (jointOffSpouseNonblocking d) =
      jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) • jointOffSpouseProbabilityLaw d := by
  rw [jointOffSpouseProbabilityLaw, smul_smul, ENNReal.mul_inv_cancel hd (measure_ne_top _ _),
    one_smul]
private theorem unitScoreLaw_Ioi_of_mem_Icc {x : ℝ} (hx : x ∈ Icc 0 1) :
    unitScoreLaw (Ioi x) = ENNReal.ofReal (1 - x) := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ioi]
  rw [show Ioi x ∩ Icc 0 1 = Ioc x 1 by
    ext u
    exact ⟨fun ⟨hlt, _, hle⟩ ↦ ⟨hlt, hle⟩, fun ⟨hlt, hle⟩ ↦ ⟨hlt, hx.1.trans hlt.le, hle⟩⟩]
  exact Real.volume_Ioc
theorem jointOffSpouseScoreLaw_nonblocking_pos {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (hL : ∀ m, jointManSpouseScoreLeft d m ∈ Ico 0 1)
    (hR : ∀ m, jointManSpouseScoreRight d m ∈ Ico 0 1) :
    0 < jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) := by
  rw [jointOffSpouseScoreLaw_nonblocking]
  refine pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun q _ ↦ ?_)
  let a := max (jointManSpouseScoreLeft d q.val.1) (jointManSpouseScoreRight d q.val.1)
  have ha : a ∈ Ico 0 1 := ⟨(hL q.val.1).1.trans (le_max_left _ _),
    max_lt (hL q.val.1).2 (hR q.val.1).2⟩
  have hsub : Ioi a ×ˢ (univ : Set ℝ) ⊆ jointNonblockingCellAt d q.val := by
    intro p hp
    have hap : a < p.1 := hp.1
    exact ⟨fun h ↦ ((le_max_left _ _).trans hap.le).not_gt (show p.1 < _ from h.1),
      fun h ↦ ((le_max_right _ _).trans hap.le).not_gt (show p.1 < _ from h.1)⟩
  have hm : unitScorePairLaw (Ioi a ×ˢ (univ : Set ℝ)) = ENNReal.ofReal (1 - a) := by
    rw [unitScorePairLaw, Measure.prod_prod, measure_univ, mul_one,
      unitScoreLaw_Ioi_of_mem_Icc ⟨ha.1, ha.2.le⟩]
  exact ((ENNReal.ofReal_pos.mpr (sub_pos.mpr ha.2)).trans_le
    (hm ▸ measure_mono hsub)).ne'
theorem jointManSpouseScoreLeft_eq_right {μ ν : Matching n} (d : JointSpouseScores μ ν)
    {m : Fin n} (hm : μ m = ν m) :
    jointManSpouseScoreLeft d m = jointManSpouseScoreRight d m := by
  unfold jointManSpouseScoreLeft jointManSpouseScoreRight
  exact congrArg (fun q : JointSpouseIndex μ ν ↦ (d q).1)
    (Subtype.ext (Prod.ext rfl hm))
theorem jointNonblockingScoreCell_same_male (x y₁ y₂ : ℝ) :
    jointNonblockingScoreCell x y₁ x y₂ = nonblockingScoreCell x (max y₁ y₂) := by
  ext p
  simp only [jointNonblockingScoreCell, nonblockingScoreCell, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_prod, Set.mem_Iio, lt_max_iff]
  tauto
theorem continuousScoreLaw_lintegral_twoStable (μ ν : Matching n)
    {C : Set (JointSpouseScores μ ν)} (hC : MeasurableSet C)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x in {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (splitTwoMatchingScores μ ν x).1 ∈ C},
      f x ∂continuousScoreLaw n) =
      ∫⁻ d in C ∩ jointMarkedNonblocking μ ν, ∫⁻ v, f ((splitTwoMatchingScores μ ν).symm (d, v))
        ∂(Measure.pi (jointOffSpouseCellLaw d)) ∂jointSpouseScoreLaw μ ν := by
  let e := splitTwoMatchingScores μ ν
  let S : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (e x).1 ∈ C}
  let T := C ∩ jointMarkedNonblocking μ ν
  let E : Set (JointSpouseScores μ ν × JointOffSpouseScores μ ν) :=
    {z | z.1 ∈ T ∧ z.2 ∈ jointOffSpouseNonblocking z.1}
  let f' := f ∘ e.symm
  have hS : MeasurableSet S := (measurableSet_isScoreStable μ).inter
    ((measurableSet_isScoreStable ν).inter ((measurable_fst.comp e.measurable) hC))
  have hT : MeasurableSet T := hC.inter (measurableSet_jointMarkedNonblocking μ ν)
  have hpre : e ⁻¹' E = S := by
    ext x
    simp only [Set.mem_preimage, E, S, T, Set.mem_ofPred_eq, Set.mem_inter_iff, e]
    have h := twoStable_iff_splitTwoMatchingScores μ ν x
    tauto
  have hE_pre : E = e.symm ⁻¹' S := by
    ext z
    have h := Set.ext_iff.mp hpre (e.symm z)
    simpa only [Set.mem_preimage, MeasurableEquiv.apply_symm_apply] using h
  have hE : MeasurableSet E := hE_pre ▸ hS.preimage e.symm.measurable
  have hf' : Measurable f' := hf.comp e.symm.measurable
  calc
    _ = ∫⁻ z in E, f' z ∂((jointSpouseScoreLaw μ ν).prod (jointOffSpouseScoreLaw μ ν)) := by
      rw [← (measurePreserving_splitTwoMatchingScores μ ν).setLIntegral_comp_preimage hE hf', hpre]
      simp [f', S, e]
    _ = _ := by
      rw [← lintegral_indicator hE, lintegral_prod _ (hf'.indicator hE).aemeasurable,
        ← lintegral_indicator hT]
      refine lintegral_congr fun d ↦ ?_
      by_cases hd : d ∈ T
      · rw [Set.indicator_of_mem hd, ← jointOffSpouseScoreLaw_restrict_nonblocking,
          ← lintegral_indicator (measurableSet_jointOffSpouseNonblocking d)]
        refine lintegral_congr fun v ↦ ?_
        by_cases hv : v ∈ jointOffSpouseNonblocking d <;> simp [E, f', hd, hv, e]
      · rw [Set.indicator_of_notMem hd]
        simp [E, hd]
end StepC
end

-- TwoStableCommonRows
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
private abbrev CommonMan {n : ℕ} (μ ν : Matching n) := {i : Fin n // μ i = ν i}
private abbrev CommonRowCandidate {n : ℕ} {μ ν : Matching n} (i : CommonMan μ ν) :=
  {j : Fin n // i.val ≠ j}
private def commonOffSpouseCell {n : ℕ} {μ ν : Matching n} (i : CommonMan μ ν)
    (j : CommonRowCandidate i) : JointOffSpouseIndex μ ν :=
  ⟨(i.val, ν j.val), by
    rintro (h | h)
    · exact j.property (ν.injective (i.property.symm.trans h))
    · exact j.property (ν.injective h)⟩
private def jointCommonRows {n : ℕ} {μ ν : Matching n} (v : JointOffSpouseScores μ ν)
    (i : CommonMan μ ν) (j : CommonRowCandidate i) : ℝ × ℝ :=
  v (commonOffSpouseCell i j)
private noncomputable def commonRowCellLaw (x b : ℝ) : Measure (ℝ × ℝ) :=
  (rowNonblockingLaw x b univ)⁻¹ • rowNonblockingLaw x b
private instance (x b : ℝ) : IsFiniteMeasure (commonRowCellLaw x b) := by
  constructor
  rw [commonRowCellLaw, Measure.smul_apply, smul_eq_mul, mul_comm]
  exact (ENNReal.mul_inv_ne_top _).lt_top
theorem jointCommonCellLaw_eq {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (i : CommonMan μ ν) (j : CommonRowCandidate i) :
    normalizedJointOffSpouseCellLaw d (commonOffSpouseCell i j) =
      commonRowCellLaw (jointManSpouseScoreRight d i.val)
        (max (jointWomanSpouseScoreLeft d (ν j.val))
          (jointWomanSpouseScoreRight d (ν j.val))) := by
  have h : jointOffSpouseCellLaw d (commonOffSpouseCell i j) =
      rowNonblockingLaw (jointManSpouseScoreRight d i.val)
        (max (jointWomanSpouseScoreLeft d (ν j.val))
          (jointWomanSpouseScoreRight d (ν j.val))) := by
    unfold jointOffSpouseCellLaw jointNonblockingCellAt
    change unitScorePairLaw.restrict (jointNonblockingScoreCell
      (jointManSpouseScoreLeft d i.val) (jointWomanSpouseScoreLeft d (ν j.val))
      (jointManSpouseScoreRight d i.val) (jointWomanSpouseScoreRight d (ν j.val))) = _
    rw [jointManSpouseScoreLeft_eq_right d i.property, jointNonblockingScoreCell_same_male]
    rfl
  simp only [normalizedJointOffSpouseCellLaw, commonRowCellLaw, h]
private noncomputable def jointCommonRowLaw {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (i : CommonMan μ ν) : Measure (CommonRowCandidate i → ℝ × ℝ) :=
  Measure.pi fun j ↦ normalizedJointOffSpouseCellLaw d (commonOffSpouseCell i j)
private theorem normalizedJointOffSpouseCellLaw_isProbabilityMeasure
    {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (hpos : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0)
    (q : JointOffSpouseIndex μ ν) :
    IsProbabilityMeasure (normalizedJointOffSpouseCellLaw d q) := by
  rw [jointOffSpouseScoreLaw_nonblocking] at hpos
  constructor
  rw [normalizedJointOffSpouseCellLaw, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel _ (measure_ne_top _ _)]
  rw [jointOffSpouseCellLaw, Measure.restrict_apply_univ]
  exact Finset.prod_ne_zero_iff.mp hpos q (Finset.mem_univ q)
theorem jointCommonRowLaw_isProbabilityMeasure {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν)
    (hpos : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0)
    (i : CommonMan μ ν) : IsProbabilityMeasure (jointCommonRowLaw d i) := by
  let (j : CommonRowCandidate i) :=
    normalizedJointOffSpouseCellLaw_isProbabilityMeasure d hpos (commonOffSpouseCell i j)
  exact inferInstanceAs (IsProbabilityMeasure
    (Measure.pi fun j ↦ normalizedJointOffSpouseCellLaw d (commonOffSpouseCell i j)))
private theorem measurePreserving_pi_comp_embedding {ι κ X : Type*}
    [Fintype ι] [Fintype κ] [MeasurableSpace X] (m : ι → Measure X)
    [∀ i, IsProbabilityMeasure (m i)] (e : κ ↪ ι) :
    MeasurePreserving (fun v : ι → X ↦ fun k ↦ v (e k)) (Measure.pi m)
      (Measure.pi fun k ↦ m (e k)) := by
  classical
  let : Fintype (Set.range e) := Subtype.fintype (· ∈ Set.range e)
  let E := Equiv.ofInjective e e.injective
  let m' : κ → Measure X := fun k ↦ m (e k)
  have hm (i : Set.range e) : m' (E.symm i) = m i.val := by
    change m ((E (E.symm i)).val) = m i.val
    rw [E.apply_symm_apply]
  have h₁ := measurePreserving_fst.comp
    (measurePreserving_piEquivPiSubtypeProd m (· ∈ Set.range e))
  have h₂ := measurePreserving_piCongrLeft m' E.symm
  simp only [hm] at h₂
  convert h₂.comp h₁ using 1
  funext v k
  change v (e k) = (MeasurableEquiv.piCongrLeft (fun _ : κ ↦ X) E.symm
    (fun i ↦ v i.val)) k
  have hk := (MeasurableEquiv.piCongrLeft_apply_apply E.symm (β := fun _ : κ ↦ X)
    (fun i ↦ v i.val) (E k)).symm
  rw [E.symm_apply_apply] at hk
  exact hk
private def regroupRows {ι X : Type*} {κ : ι → Type*} [MeasurableSpace X] :
    ((i : ι) × κ i → X) ≃ᵐ ((i : ι) → κ i → X) where
  toFun v i j := v ⟨i, j⟩
  invFun v q := v q.1 q.2
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_pi_iff.2 fun _ ↦
    measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 fun q ↦
    (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
private theorem measurePreserving_regroupRows {ι X : Type*} {κ : ι → Type*}
    [MeasurableSpace X] [Fintype ι] [∀ i, Fintype (κ i)]
    (m : ((i : ι) × κ i) → Measure X) [∀ q, SigmaFinite (m q)] :
    MeasurePreserving regroupRows (Measure.pi m)
      (Measure.pi fun i : ι ↦ Measure.pi fun j : κ i ↦ m ⟨i, j⟩) := by
  refine MeasurePreserving.symm regroupRows.symm ?_
  refine ⟨regroupRows.symm.measurable, (Measure.pi_eq fun s _ ↦ ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  have hpre : regroupRows.symm ⁻¹' (univ.pi s) =
      univ.pi (fun i ↦ univ.pi fun j ↦ s ⟨i, j⟩) := by
    ext v
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left]
    exact ⟨fun h i j ↦ h ⟨i, j⟩, fun h q ↦ h q.1 q.2⟩
  rw [hpre]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_sigma' _).symm
theorem measurePreserving_jointCommonRows {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν)
    (hpos : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0) :
    MeasurePreserving jointCommonRows (jointOffSpouseProbabilityLaw d)
      (Measure.pi (jointCommonRowLaw d)) := by
  let e : ((i : CommonMan μ ν) × CommonRowCandidate i) ↪ JointOffSpouseIndex μ ν :=
    ⟨fun q ↦ commonOffSpouseCell q.1 q.2, by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have hi : i = i' :=
        Subtype.ext (congrArg (fun q : JointOffSpouseIndex μ ν ↦ q.val.1) h)
      subst i'
      have hj : j = j' := Subtype.ext (ν.injective
        (congrArg (fun q : JointOffSpouseIndex μ ν ↦ q.val.2) h))
      rw [hj]⟩
  let (q : JointOffSpouseIndex μ ν) :
    IsProbabilityMeasure (normalizedJointOffSpouseCellLaw d q) :=
    normalizedJointOffSpouseCellLaw_isProbabilityMeasure d hpos q
  rw [jointOffSpouseProbabilityLaw_eq_pi]
  exact (measurePreserving_regroupRows (fun q ↦ normalizedJointOffSpouseCellLaw d (e q))).comp
    (measurePreserving_pi_comp_embedding _ e)
private noncomputable def commonEligibilityWeight (x y b : ℝ) : ℝ :=
  (1 - x) * y / (1 - x * b)
private theorem commonDen_pos {x b : ℝ} (hx : x ∈ Ico 0 1) (hb : b ∈ Icc 0 1) :
    0 < 1 - x * b :=
  sub_pos.mpr ((mul_le_of_le_one_right hx.1 hb.2).trans_lt hx.2)
private theorem commonRowCellLaw_isProbabilityMeasure {x b : ℝ}
    (hx : x ∈ Ico 0 1) (hb : b ∈ Icc 0 1) :
    IsProbabilityMeasure (commonRowCellLaw x b) := by
  constructor
  rw [commonRowCellLaw, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel]
  · rw [rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ hb]
    exact ENNReal.ofReal_ne_zero_iff.mpr (commonDen_pos hx hb)
  · exact measure_ne_top _ _
private theorem unitScoreLaw_Ico_of_mem_Icc {x u : ℝ} (hx : 0 ≤ x) (hu : u ≤ 1) :
    unitScoreLaw (Ico x u) = ENNReal.ofReal (u - x) := by
  have hsub : Ico x u ⊆ Icc 0 1 := fun _ h ↦ ⟨hx.trans h.1, h.2.le.trans hu⟩
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr hsub, Real.volume_Ico]
private theorem commonRowCellLaw_competitor_better {x y b u : ℝ} (hx : x ∈ Ico 0 1)
    (hy : y ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hyb : y ≤ b) (hu : u ∈ Icc x 1) :
    commonRowCellLaw x b (Iio u ×ˢ Iio y) = ENNReal.ofReal ((u - x) * y / (1 - x * b)) := by
  have hinter : (Iio u ×ˢ Iio y) ∩ (Iio x ×ˢ Iio b)ᶜ = Ico x u ×ˢ Iio y := by
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Iio, mem_Ico, mem_compl_iff]
    exact ⟨fun h ↦ ⟨⟨le_of_not_gt fun hp ↦ h.2 ⟨hp, h.1.2.trans_le hyb⟩, h.1.1⟩, h.1.2⟩,
      fun h ↦ ⟨⟨h.1.2, h.2⟩, fun hp ↦ h.1.1.not_gt hp.1⟩⟩
  rw [commonRowCellLaw, Measure.smul_apply, smul_eq_mul,
    rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ hb, rowNonblockingLaw,
    Measure.restrict_apply (measurableSet_Iio.prod measurableSet_Iio), hinter, Measure.prod_prod,
    unitScoreLaw_Ico_of_mem_Icc hx.1 hu.2, unitScoreLaw_Iio_of_mem_Icc hy,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hu.1),
    ENNReal.ofReal_div_of_pos (commonDen_pos hx hb), div_eq_mul_inv, mul_comm]
private theorem commonRowCellLaw_avoiding {x y b u : ℝ} (hx : x ∈ Ico 0 1)
    (hy : y ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hyb : y ≤ b) (hu : u ∈ Icc x 1) :
    commonRowCellLaw x b (Iio u ×ˢ Iio y)ᶜ =
      ENNReal.ofReal (1 - (u - x) * y / (1 - x * b)) := by
  let := commonRowCellLaw_isProbabilityMeasure hx hb
  rw [measure_compl (measurableSet_Iio.prod measurableSet_Iio) (measure_ne_top _ _),
    measure_univ, commonRowCellLaw_competitor_better hx hy hb hyb hu,
    ENNReal.ofReal_sub _ (div_nonneg (mul_nonneg (sub_nonneg.mpr hu.1) hy.1)
      (commonDen_pos hx hb).le), ENNReal.ofReal_one]
theorem commonEligibilityWeight_bounds {x y b : ℝ} (hx : x ∈ Ico 0 1)
    (hy : y ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    (1 - x) * y ≤ commonEligibilityWeight x y b ∧ commonEligibilityWeight x y b ≤ y := by
  have hnum : 0 ≤ (1 - x) * y := mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1
  have hden := commonDen_pos hx hb
  unfold commonEligibilityWeight
  constructor
  · rw [le_div_iff₀ hden]
    exact mul_le_of_le_one_right hnum (sub_le_self _ (mul_nonneg hx.1 hb.1))
  · rw [div_le_iff₀ hden, mul_comm y]
    exact mul_le_mul_of_nonneg_right
      (sub_le_sub_left (mul_le_of_le_one_right hx.1 hb.2) _) hy.1
theorem commonRowSuccessorPairEvent_mass {ι : Type*} [Fintype ι] {x v b₀ : ℝ}
    {y b : ι → ℝ} (hx : x ∈ Ico 0 1) (hv : v ∈ Icc 0 1) (hb₀ : b₀ ∈ Icc 0 1)
    (hy : ∀ k, y k ∈ Icc 0 1) (hb : ∀ k, b k ∈ Icc 0 1)
    (hyb : ∀ k, y k ≤ b k) :
    ((commonRowCellLaw x b₀).prod (Measure.pi fun k ↦ commonRowCellLaw x (b k)))
        (scoreSuccessorPairEvent x v y) =
      ENNReal.ofReal (commonEligibilityWeight x v b₀ *
        scoreRowMass Finset.univ (fun k ↦ commonEligibilityWeight x (y k) (b k)) 0 1) := by
  let T : Set (ℝ × ℝ) := Ioi x ×ˢ Iio v
  let m := commonRowCellLaw x b₀
  let m' := Measure.pi fun k ↦ commonRowCellLaw x (b k)
  let r (k : ι) := y k / (1 - x * b k)
  let F (u : ℝ) := scoreRowKernel Finset.univ r (u - x)
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Iio
  have hF : Continuous F := (continuous_scoreRowKernel Finset.univ r).comp
    (continuous_id.sub continuous_const)
  have hnonneg (u : ℝ) (hu : u ∈ Icc x 1) : ∀ k, 0 ≤ 1 - (u - x) * r k := by
    intro k
    apply sub_nonneg.mpr
    calc
      _ ≤ (1 - x) * r k := mul_le_mul_of_nonneg_right (sub_le_sub_right hu.2 _)
        (div_nonneg (hy k).1 (commonDen_pos hx (hb k)).le)
      _ = commonEligibilityWeight x (y k) (b k) := (mul_div_assoc ..).symm
      _ ≤ y k := (commonEligibilityWeight_bounds hx (hy k) (hb k)).2
      _ ≤ 1 := (hy k).2
  have hsupp : ∀ᵐ uv ∂m, uv ∈ Icc 0 1 ×ˢ Icc 0 1 := by
    apply Measure.ae_smul_measure
    unfold rowNonblockingLaw unitScoreLaw
    rw [Measure.prod_restrict]
    exact ae_restrict_of_ae (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))
  have hsection :
      (fun uv ↦ m' (Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y)) =ᵐ[m]
        T.indicator (fun uv ↦ ENNReal.ofReal (F uv.1)) := by
    filter_upwards [hsupp] with uv huv
    by_cases ht : uv ∈ T
    · have hu : uv.1 ∈ Icc x 1 := ⟨(show x < uv.1 from ht.1).le, huv.1.2⟩
      have hpre : Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y =
          univ.pi (fun k ↦ (Iio uv.1 ×ˢ Iio (y k))ᶜ) := by
        ext z
        simp only [mem_preimage, scoreSuccessorPairEvent, mem_ofPred_eq, mem_pi, mem_univ,
          true_implies, mem_compl_iff, mem_prod, mem_Iio]
        exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨ht.1, ht.2, h⟩⟩
      rw [hpre, Set.indicator_of_mem ht]
      change (Measure.pi _ _) = ENNReal.ofReal (F uv.1)
      rw [Measure.pi_pi]
      simp_rw [commonRowCellLaw_avoiding hx (hy _) (hb _) (hyb _) hu]
      unfold F scoreRowKernel r
      simp only [mul_div_assoc]
      exact (ENNReal.ofReal_prod_of_nonneg fun k _ ↦ hnonneg uv.1 hu k).symm
    · have hpre : Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        exact fun z hz ↦ ht ⟨hz.1, hz.2.1⟩
      rw [hpre, measure_empty, Set.indicator_of_notMem ht]
  change (m.prod m') (scoreSuccessorPairEvent x v y) = _
  rw [Measure.prod_apply (measurableSet_scoreSuccessorPairEvent x v y),
    lintegral_congr_ae hsection, lintegral_indicator hT]
  have hsub : T ⊆ (Iio x ×ˢ Iio b₀ : Set (ℝ × ℝ))ᶜ :=
    fun _ h h' ↦ (show x < _ from h.1).asymm (show _ < x from h'.1)
  have hleft : unitScoreLaw.restrict (Ioi x) = volume.restrict (Ioc x 1) := by
    rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext u
    change (x < u ∧ 0 ≤ u ∧ u ≤ 1) ↔ (x < u ∧ u ≤ 1)
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hx.1.trans h.1.le, h.2⟩⟩
  have hrestrict : m.restrict T =
      (ENNReal.ofReal (1 - x * b₀))⁻¹ •
        ((volume.restrict (Ioc x 1)).prod (unitScoreLaw.restrict (Iio v))) := by
    dsimp [m, commonRowCellLaw]
    rw [Measure.restrict_smul, rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ hb₀,
      rowNonblockingLaw, Measure.restrict_restrict_of_subset hsub]
    change _ • (unitScoreLaw.prod unitScoreLaw).restrict (Ioi x ×ˢ Iio v) = _
    rw [← Measure.prod_restrict, hleft]
  have hoff (t : ℝ) : F (x + (1 - x) * t) =
      scoreRowKernel Finset.univ (fun k ↦ commonEligibilityWeight x (y k) (b k)) t := by
    unfold F scoreRowKernel
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    unfold r commonEligibilityWeight
    ring
  have haff : (1 - x) *
      scoreRowMass Finset.univ (fun k ↦ commonEligibilityWeight x (y k) (b k)) 0 1 =
        ∫ u in x..1, F u := by
    have h := intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1)
      F (1 - x) x
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one, hoff] at h
    simpa only [show x + (1 - x) = 1 by ring, scoreRowMass] using h
  rw [hrestrict, lintegral_smul_measure]
  rw [show (fun uv : ℝ × ℝ ↦ ENNReal.ofReal (F uv.1)) =
      (fun uv : ℝ × ℝ ↦ ENNReal.ofReal (F uv.1) * (1 : ℝ≥0∞)) by simp only [mul_one]]
  rw [lintegral_prod_mul hF.measurable.ennreal_ofReal.aemeasurable measurable_const.aemeasurable,
    lintegral_const, one_mul, Measure.restrict_apply_univ, unitScoreLaw_Iio_of_mem_Icc hv,
    smul_eq_mul]
  have hmass :
      (∫⁻ u in Ioc x 1, ENNReal.ofReal (F u)) = ENNReal.ofReal (∫ u in x..1, F u) := by
    rw [intervalIntegral.integral_of_le hx.2.le, ofReal_integral_eq_lintegral_ofReal]
    · exact (hF.intervalIntegrable _ _).1
    · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc x 1))]
        with u hu
      exact Finset.prod_nonneg fun k _ ↦ hnonneg u ⟨hu.1.le, hu.2⟩ k
  rw [hmass, ← haff, ENNReal.ofReal_mul (sub_nonneg.mpr hx.2.le)]
  have hcoef :
      ENNReal.ofReal (commonEligibilityWeight x v b₀) =
        (ENNReal.ofReal (1 - x * b₀))⁻¹ * (ENNReal.ofReal (1 - x) * ENNReal.ofReal v) := by
    rw [commonEligibilityWeight, ENNReal.ofReal_div_of_pos (commonDen_pos hx hb₀),
      ENNReal.ofReal_mul (sub_nonneg.mpr hx.2.le), div_eq_mul_inv, mul_comm]
  rw [ENNReal.ofReal_mul ((mul_nonneg (sub_nonneg.mpr hx.2.le) hv.1).trans
    (commonEligibilityWeight_bounds hx hv hb₀).1), hcoef]
  ac_rfl
private def jointRightDiagonal {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    DiagonalScorePairs n :=
  fun q ↦ (jointManSpouseScoreRight d q.val.1, jointWomanSpouseScoreRight d (ν q.val.1))
@[simp] theorem diagonalPairAt_jointRightDiagonal {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (j : Fin n) :
    diagonalPairAt (jointRightDiagonal d) j =
      (jointManSpouseScoreRight d j, jointWomanSpouseScoreRight d (ν j)) :=
  rfl
@[simp] theorem jointRightDiagonal_split {n : ℕ} (μ ν : Matching n) (x : ScoreProfile n) :
    jointRightDiagonal (splitTwoMatchingScores μ ν x).1 = (splitScorePairs ν x).1 := by
  funext q
  obtain ⟨⟨i, j⟩, h⟩ := q
  change i = j at h
  subst j
  change diagonalPairAt (jointRightDiagonal (splitTwoMatchingScores μ ν x).1) i =
    diagonalPairAt (splitScorePairs ν x).1 i
  simp [diagonalPairAt_splitScorePairs]
theorem jointCommonRowSuccessorEvent_iff_isSuccessor {n : ℕ} (μ ν : Matching n)
    (x : ScoreProfile n) (hs : IsScoreStable x ν) (ht : ∀ r, Function.Injective (x r))
    (i : CommonMan μ ν) (j : CommonRowCandidate i) :
    jointCommonRows (splitTwoMatchingScores μ ν x).2 i ∈
        scoreRowSuccessorEvent (jointRightDiagonal (splitTwoMatchingScores μ ν x).1) i.val j ↔
      IsSuccessor (profileOfScores x) ν i.val (ν j.val) := by
  have hrow : jointCommonRows (splitTwoMatchingScores μ ν x).2 i =
      offDiagonalRowsEquiv n (splitScorePairs ν x).2 i.val := by
    funext k
    change (splitTwoMatchingScores μ ν x).2 (commonOffSpouseCell i k) =
      (splitScorePairs ν x).2 ⟨(i.val, k.val), k.property⟩
    rw [splitTwoMatchingScores_offSpouse_apply, splitScorePairs_offDiagonal_apply]
    rfl
  rw [hrow, jointRightDiagonal_split]
  exact ⟨isSuccessor_of_scoreRowSuccessorEvent ν x ht i.val j,
    scoreRowSuccessorEvent_of_isSuccessor ν x hs ht i.val j⟩
private noncomputable def jointCommonEligibility {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (i : CommonMan μ ν) (j : Fin n) : ℝ :=
  commonEligibilityWeight (jointManSpouseScoreRight d i.val)
    (jointWomanSpouseScoreRight d (ν j))
    (max (jointWomanSpouseScoreLeft d (ν j)) (jointWomanSpouseScoreRight d (ν j)))
theorem jointCommonRowSuccessorEvent_mass {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (i : CommonMan μ ν) (j : CommonRowCandidate i)
    (hx : jointManSpouseScoreRight d i.val ∈ Ico 0 1)
    (hL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    jointCommonRowLaw d i (scoreRowSuccessorEvent (jointRightDiagonal d) i.val j) =
      ENNReal.ofReal (jointCommonEligibility d i j.val *
        scoreRowMass Finset.univ
          (fun k : {k : CommonRowCandidate i // k ≠ j} ↦
            jointCommonEligibility d i k.val.val) 0 1) := by
  let x := jointManSpouseScoreRight d i.val
  let y (k : CommonRowCandidate i) := jointWomanSpouseScoreRight d (ν k.val)
  let b (k : CommonRowCandidate i) :=
    max (jointWomanSpouseScoreLeft d (ν k.val)) (y k)
  let m (k : CommonRowCandidate i) := commonRowCellLaw x (b k)
  have hb (k : CommonRowCandidate i) : b k ∈ Icc 0 1 :=
    ⟨(hL _).1.trans (le_max_left _ _), max_le (hL _).2 (hR _).2⟩
  have hrow : jointCommonRowLaw d i = Measure.pi m := by
    unfold jointCommonRowLaw
    congr 1
    funext k
    exact jointCommonCellLaw_eq d i k
  rw [hrow]
  have hmap := measurePreserving_rowTargetAndCompetitors m j
  have hevent : scoreRowSuccessorEvent (jointRightDiagonal d) i.val j =
      (fun r : CommonRowCandidate i → ℝ × ℝ ↦
        (r j, fun k : {k : CommonRowCandidate i // k ≠ j} ↦ r k.val)) ⁻¹'
        scoreSuccessorPairEvent x (y j)
          (fun k : {k : CommonRowCandidate i // k ≠ j} ↦ y k.val) := by
    ext r
    simp only [scoreRowSuccessorEvent, diagonalPairAt_jointRightDiagonal, mem_preimage,
      scoreSuccessorPairEvent, mem_ofPred_eq]
    rfl
  rw [hevent, hmap.measure_preimage
    (measurableSet_scoreSuccessorPairEvent _ _ _).nullMeasurableSet]
  exact commonRowSuccessorPairEvent_mass hx (hR _) (hb j) (fun _ ↦ hR _)
    (fun k ↦ hb k.val) (fun _ ↦ le_max_right _ _)
theorem ae_jointSpouse_ae_stableScoreProfile {n : ℕ} (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ᵐ v ∂jointOffSpouseProbabilityLaw d,
      d ∈ jointMarkedNonblocking μ ν →
      let x := (splitTwoMatchingScores μ ν).symm (d, v)
      (∀ row, Function.Injective (x row)) ∧ IsScoreStable x μ ∧ IsScoreStable x ν := by
  have ht : ∀ᵐ z ∂((jointSpouseScoreLaw μ ν).prod (jointOffSpouseScoreLaw μ ν)),
      ∀ row, Function.Injective ((splitTwoMatchingScores μ ν).symm z row) :=
    ((measurePreserving_splitTwoMatchingScores μ ν).symm).quasiMeasurePreserving.ae
      (ae_injective_rows n)
  filter_upwards [Measure.ae_ae_of_ae_prod ht] with d hd
  have hv : ∀ᵐ v ∂(jointOffSpouseScoreLaw μ ν).restrict (jointOffSpouseNonblocking d),
      (∀ row, Function.Injective ((splitTwoMatchingScores μ ν).symm (d, v) row)) ∧
        v ∈ jointOffSpouseNonblocking d :=
    (ae_restrict_of_ae hd).and (ae_restrict_mem (measurableSet_jointOffSpouseNonblocking d))
  have hv' := Measure.ae_smul_measure hv
    (jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d))⁻¹
  filter_upwards [hv'] with v hv'
  intro hm
  let x := (splitTwoMatchingScores μ ν).symm (d, v)
  exact ⟨hv'.1, (twoStable_iff_splitTwoMatchingScores μ ν x).2 (by
    simpa only [x, MeasurableEquiv.apply_symm_apply] using And.intro hm hv'.2)⟩
theorem ae_jointSpouse_ae_commonRowSuccessorEvent {n : ℕ} (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ᵐ v ∂jointOffSpouseProbabilityLaw d,
      d ∈ jointMarkedNonblocking μ ν →
      ∀ (i : CommonMan μ ν) (j : CommonRowCandidate i),
        let x := (splitTwoMatchingScores μ ν).symm (d, v)
        jointCommonRows v i ∈ scoreRowSuccessorEvent (jointRightDiagonal d) i.val j ↔
          IsSuccessor (profileOfScores x) ν i.val (ν j.val) := by
  filter_upwards [ae_jointSpouse_ae_stableScoreProfile μ ν] with d hd
  filter_upwards [hd] with v hv
  intro hm i j
  let x := (splitTwoMatchingScores μ ν).symm (d, v)
  obtain ⟨ht, -, hs⟩ := hv hm
  simpa only [x, MeasurableEquiv.apply_symm_apply] using
    jointCommonRowSuccessorEvent_iff_isSuccessor μ ν x hs ht i j
theorem ae_jointSpouse_thresholds {n : ℕ} (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν,
      (∀ i, jointManSpouseScoreLeft d i ∈ Ico 0 1) ∧
      (∀ i, jointManSpouseScoreRight d i ∈ Ico 0 1) ∧
      (∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1) ∧
      (∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) := by
  have hu : ∀ᵐ t ∂unitScoreLaw, t ∈ Icc 0 1 := ae_restrict_mem measurableSet_Icc
  have hne : ∀ᵐ t ∂unitScoreLaw, t ≠ 1 := ae_iff.mpr (by simp)
  have hu' : ∀ᵐ t ∂unitScoreLaw, t ∈ Ico 0 1 := by
    filter_upwards [hu, hne] with t ht ht'
    exact ⟨ht.1, lt_of_le_of_ne ht.2 ht'⟩
  have hp : ∀ᵐ z ∂unitScorePairLaw, z.1 ∈ Ico 0 1 ∧ z.2 ∈ Icc 0 1 :=
    ((Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw)
      (ν := unitScoreLaw)).ae hu').and
      ((Measure.quasiMeasurePreserving_snd (μ := unitScoreLaw)
        (ν := unitScoreLaw)).ae hu)
  have hd : ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ q, (d q).1 ∈ Ico 0 1 ∧ (d q).2 ∈ Icc 0 1 :=
    ae_all_iff.2 fun q ↦ (Measure.tendsto_eval_ae_ae
      (μ := fun _ : JointSpouseIndex μ ν ↦ unitScorePairLaw) (i := q)).eventually hp
  filter_upwards [hd] with d h
  exact ⟨fun i ↦ (h ⟨(i, μ i), Or.inl rfl⟩).1,
    fun i ↦ (h ⟨(i, ν i), Or.inr rfl⟩).1,
    fun w ↦ (h ⟨(μ.symm w, w), Or.inl (μ.apply_symm_apply w)⟩).2,
    fun w ↦ (h ⟨(ν.symm w, w), Or.inr (ν.apply_symm_apply w)⟩).2⟩
private def jointMaxDiagonal {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    DiagonalScorePairs n :=
  fun q ↦ (jointManSpouseScoreRight d q.val.1,
    max (jointWomanSpouseScoreLeft d (ν q.val.1)) (jointWomanSpouseScoreRight d (ν q.val.1)))
private theorem jointCommonRowLaw_eq_normalizedStableScoreRowLaw
    {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν) (i : CommonMan μ ν)
    (hx : jointManSpouseScoreRight d i.val ∈ Ico 0 1)
    (hL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    jointCommonRowLaw d i = normalizedStableScoreRowLaw (jointMaxDiagonal d) i.val := by
  let x := jointManSpouseScoreRight d i.val
  let b (j : CommonRowCandidate i) :=
    max (jointWomanSpouseScoreLeft d (ν j.val)) (jointWomanSpouseScoreRight d (ν j.val))
  let m (j : CommonRowCandidate i) := rowNonblockingLaw x (b j)
  have hbase : stableScoreRowLaw (jointMaxDiagonal d) i.val = Measure.pi m := rfl
  rw [jointCommonRowLaw, normalizedStableScoreRowLaw, hbase, Measure.pi_univ]
  simp_rw [jointCommonCellLaw_eq, commonRowCellLaw]
  change Measure.pi (fun j ↦ (m j univ)⁻¹ • m j) = (∏ j, m j univ)⁻¹ • Measure.pi m
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ ↦ Or.inr (measure_ne_top _ _))]
  refine pi_smul_coordinates m _ fun j ↦ ENNReal.inv_ne_top.mpr ?_
  have hb : b j ∈ Icc 0 1 :=
    ⟨(hL _).1.trans (le_max_left _ _), max_le (hL _).2 (hR _).2⟩
  change rowNonblockingLaw x (b j) univ ≠ 0
  rw [rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ hb]
  exact ENNReal.ofReal_ne_zero_iff.mpr (commonDen_pos hx hb)
section FiniteOutcomes
variable {n : ℕ} {μ ν : Matching n} [MeasurableSpace (Option (Fin n))]
private noncomputable def jointCommonSuccessors (d : JointSpouseScores μ ν)
    (v : JointOffSpouseScores μ ν) (i : Fin n) : Option (Fin n) :=
  if hi : μ i = ν i then forwardSuccessorOutcome (jointRightDiagonal d) i
    (jointCommonRows v ⟨i, hi⟩) else none
private noncomputable def jointCommonSuccessorLaw (d : JointSpouseScores μ ν) (i : Fin n) :
    Measure (Option (Fin n)) :=
  if hi : μ i = ν i then (jointCommonRowLaw d ⟨i, hi⟩).map
    (forwardSuccessorOutcome (jointRightDiagonal d) i) else Measure.dirac none
theorem jointCommonSuccessorLaw_isProbabilityMeasure (d : JointSpouseScores μ ν)
    (hpos : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0) (i : Fin n) :
    IsProbabilityMeasure (jointCommonSuccessorLaw d i) := by
  unfold jointCommonSuccessorLaw
  split
  · rename_i hi
    let := jointCommonRowLaw_isProbabilityMeasure d hpos (⟨i, hi⟩ : CommonMan μ ν)
    exact Measure.isProbabilityMeasure_map (measurable_forwardSuccessorOutcome _ _).aemeasurable
  · infer_instance
private theorem measurePreserving_extendNone {ι : Type*} [Fintype ι]
    [MeasurableSpace (Option ι)] (P : ι → Prop) [DecidablePred P]
    (m : Subtype P → Measure (Option ι)) [∀ i, IsProbabilityMeasure (m i)] :
    MeasurePreserving
      (fun v : Subtype P → Option ι ↦ fun i ↦ if hi : P i then v ⟨i, hi⟩ else none)
      (Measure.pi m)
      (Measure.pi fun i ↦ if hi : P i then m ⟨i, hi⟩ else Measure.dirac none) := by
  classical
  let f (v : Subtype P → Option ι) (i : ι) := if hi : P i then v ⟨i, hi⟩ else none
  let m' (i : ι) := if hi : P i then m ⟨i, hi⟩ else Measure.dirac none
  let (i : ι) : IsProbabilityMeasure (m' i) := by
    dsimp only [m']
    split <;> infer_instance
  have hf : Measurable f := by
    refine measurable_pi_iff.2 fun i ↦ ?_
    dsimp only [f]
    split
    · exact measurable_pi_apply _
    · exact measurable_const
  refine ⟨hf, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply hf (MeasurableSet.univ_pi hs),
    ← Fintype.prod_subtype_mul_prod_subtype P (fun i ↦ m' i (s i))]
  have hpos : (∏ i : Subtype P, m' i.val (s i.val)) = ∏ i : Subtype P, m i (s i.val) :=
    Finset.prod_congr rfl fun i _ ↦ by simp only [m', dif_pos i.property]
  rw [hpos]
  by_cases h : ∀ i : {i // ¬P i}, (none : Option ι) ∈ s i.val
  · have hpre : f ⁻¹' univ.pi s = univ.pi (fun i : Subtype P ↦ s i.val) := by
      ext v
      simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, f]
      exact ⟨fun hv i ↦ by simpa only [dif_pos i.property] using hv i.val,
        fun hv i ↦ by
          by_cases hi : P i
          · simpa only [dif_pos hi] using hv ⟨i, hi⟩
          · simpa only [dif_neg hi] using h ⟨i, hi⟩⟩
    have hc : (∏ i : {i // ¬P i}, m' i.val (s i.val)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp only [m', dif_neg i.property, Measure.dirac_apply' _ (hs i.val), indicator_of_mem (h i),
        Pi.one_apply]
    rw [hpre, Measure.pi_pi, hc, mul_one]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hpre : f ⁻¹' univ.pi s = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun v hv ↦ hi ?_
      simpa only [f, dif_neg i.property] using Set.mem_pi.mp hv i.val (Set.mem_univ _)
    have hc : (∏ i : {i // ¬P i}, m' i.val (s i.val)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [m', dif_neg i.property, Measure.dirac_apply' _ (hs i.val), indicator_of_notMem hi]
    rw [hpre, measure_empty, hc, mul_zero]
theorem measurePreserving_jointCommonSuccessors (d : JointSpouseScores μ ν)
    (hpos : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0) :
    MeasurePreserving (jointCommonSuccessors d) (jointOffSpouseProbabilityLaw d)
      (Measure.pi (jointCommonSuccessorLaw d)) := by
  let f (i : CommonMan μ ν) := forwardSuccessorOutcome (jointRightDiagonal d) i.val
  let m (i : CommonMan μ ν) := (jointCommonRowLaw d i).map (f i)
  let (i : CommonMan μ ν) := jointCommonRowLaw_isProbabilityMeasure d hpos i
  let (i : CommonMan μ ν) : IsProbabilityMeasure (m i) := by
    dsimp [m]
    exact Measure.isProbabilityMeasure_map (measurable_forwardSuccessorOutcome _ _).aemeasurable
  have hmap : MeasurePreserving (fun r i ↦ f i (r i)) (Measure.pi (jointCommonRowLaw d))
      (Measure.pi m) := by
    refine measurePreserving_pi _ _ fun i ↦ ⟨?_, rfl⟩
    exact measurable_forwardSuccessorOutcome _ _
  exact ((measurePreserving_extendNone (fun i ↦ μ i = ν i) m).comp hmap).comp
    (measurePreserving_jointCommonRows d hpos)
omit [MeasurableSpace (Option (Fin n))] in
theorem ae_jointSpouse_ae_commonSuccessors_eq_some_iff (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ᵐ v ∂jointOffSpouseProbabilityLaw d,
      d ∈ jointMarkedNonblocking μ ν →
      ∀ (i : CommonMan μ ν) (j : CommonRowCandidate i),
        let x := (splitTwoMatchingScores μ ν).symm (d, v)
        jointCommonSuccessors d v i.val = some j.val ↔
          IsSuccessor (profileOfScores x) ν i.val (ν j.val) := by
  filter_upwards [ae_jointSpouse_ae_stableScoreProfile μ ν,
    ae_jointSpouse_ae_commonRowSuccessorEvent μ ν] with d hd he
  filter_upwards [hd, he] with v hv hr
  intro hm i j
  let x := (splitTwoMatchingScores μ ν).symm (d, v)
  have ht := (hv hm).1
  have hinj : Function.Injective (fun k : CommonRowCandidate i ↦ (jointCommonRows v i k).1) := by
    intro k l h
    apply Subtype.ext
    apply ν.injective
    apply ht (Sum.inl i.val)
    have hval (a : CommonRowCandidate i) : (jointCommonRows v i a).1 =
        x (Sum.inl i.val) (ν a.val) := by
      change (v (commonOffSpouseCell i a)).1 = _
      rw [← show (splitTwoMatchingScores μ ν x).2 = v by
        simp only [x, MeasurableEquiv.apply_symm_apply]]
      rw [splitTwoMatchingScores_offSpouse_apply]
      rfl
    simpa only [hval] using h
  rw [jointCommonSuccessors, dif_pos i.property,
    forwardSuccessorOutcome_eq_some_iff _ _ _ j hinj]
  exact hr hm i j
variable [MeasurableSingletonClass (Option (Fin n))]
theorem jointCommonSuccessorLaw_some (d : JointSpouseScores μ ν)
    (i : CommonMan μ ν) (j : CommonRowCandidate i)
    (hx : jointManSpouseScoreRight d i.val ∈ Ico 0 1)
    (hL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    jointCommonSuccessorLaw d i.val {some j.val} =
      jointCommonRowLaw d i (scoreRowSuccessorEvent (jointRightDiagonal d) i.val j) := by
  rw [jointCommonSuccessorLaw, dif_pos i.property,
    Measure.map_apply (measurable_forwardSuccessorOutcome _ _) (measurableSet_singleton _)]
  apply measure_congr
  rw [jointCommonRowLaw_eq_normalizedStableScoreRowLaw d i hx hL hR]
  filter_upwards [ae_injective_fst_normalizedStableScoreRowLaw (jointMaxDiagonal d) i.val]
    with r hr
  exact propext (forwardSuccessorOutcome_eq_some_iff (jointRightDiagonal d) i.val r j hr)
theorem jointCommonSuccessorLaw_some_lower (d : JointSpouseScores μ ν)
    (i : CommonMan μ ν) (j : CommonRowCandidate i)
    (hx : jointManSpouseScoreRight d i.val ∈ Ico 0 1)
    (hL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) {X : ℝ}
    (hX : jointManSpouseScoreRight d i.val ≤ X) :
    let y := fun k : Fin n ↦ jointWomanSpouseScoreRight d (ν k)
    let Y := ∑ k, y k
    0 < Y → ENNReal.ofReal ((1 - (X + 1 / Y)) * (y j.val / Y)) ≤
      jointCommonSuccessorLaw d i.val {some j.val} := by
  intro y Y hY
  let x := jointManSpouseScoreRight d i.val
  let K := {k : CommonRowCandidate i // k ≠ j}
  let a (k : K) := jointCommonEligibility d i k.val.val
  have hw (k : Fin n) : (1 - x) * y k ≤ jointCommonEligibility d i k ∧
      jointCommonEligibility d i k ≤ y k :=
    commonEligibilityWeight_bounds hx (hR _) ⟨(hL _).1.trans (le_max_left _ _),
      max_le (hL _).2 (hR _).2⟩
  have h₀ (k : Fin n) : 0 ≤ jointCommonEligibility d i k :=
    (mul_nonneg (sub_nonneg.mpr hx.2.le) (hR _).1).trans (hw k).1
  have hsum : ∑ k : K, a k ≤ Y :=
    by
      have hinj : Function.Injective (fun k : K ↦ k.val.val) := fun _ _ h ↦ Subtype.ext (Subtype.ext h)
      calc ∑ k : K, a k ≤ ∑ k : K, y k.val.val := Finset.sum_le_sum fun k _ ↦ (hw _).2
        _ = ∑ k ∈ Finset.univ.map ⟨_, hinj⟩, y k := (Finset.sum_map Finset.univ ⟨_, hinj⟩ y).symm
        _ ≤ Y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ (hR _).1
  have hm := scoreRowMass_lower_reciprocal (J := Finset.univ) (a := a)
    (fun k _ ↦ ⟨h₀ _, (hw _).2.trans (hR _).2⟩) hsum
  have hcoef : 1 - (X + 1 / Y) ≤ (1 - x) * Y / (1 + Y) := by
    apply (le_div_iff₀ (by linarith only [hY])).mpr
    have hgap : 0 ≤ (X - x) * Y := mul_nonneg (sub_nonneg.mpr hX) hY.le
    nlinarith only [hgap, hx.1.trans hX, div_mul_cancel₀ (1 : ℝ) hY.ne',
      one_div_nonneg.mpr hY.le]
  rw [jointCommonSuccessorLaw_some d i j hx hL hR, jointCommonRowSuccessorEvent_mass d i j hx hL hR]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (1 - x) * Y / (1 + Y) * (y j.val / Y) :=
      mul_le_mul_of_nonneg_right hcoef (div_nonneg (hR _).1 hY.le)
    _ = ((1 - x) * y j.val) * (1 / (1 + Y)) := by field_simp [hY.ne']
    _ ≤ jointCommonEligibility d i j.val * scoreRowMass Finset.univ a 0 1 :=
      mul_le_mul (hw _).1 hm (by positivity) (h₀ _)
end FiniteOutcomes
theorem ae_jointSpouse_ae_commonCycle_iff_exposed {n : ℕ} (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ᵐ v ∂jointOffSpouseProbabilityLaw d,
      d ∈ jointMarkedNonblocking μ ν →
      ∀ σ : Equiv.Perm (Fin n), σ.IsCycle → (∀ i ∈ σ.support, μ i = ν i) →
        let x := (splitTwoMatchingScores μ ν).symm (d, v)
        (∀ i ∈ σ.support, jointCommonSuccessors d v i = some (σ i)) ↔
          IsExposedRotation (profileOfScores x) ν σ := by
  filter_upwards [ae_jointSpouse_ae_commonSuccessors_eq_some_iff μ ν] with d hd
  filter_upwards [hd] with v hv
  intro hm σ hσ hC
  have harc (i : Fin n) (hi : σ i ≠ i) :=
    hv hm ⟨i, hC i (Equiv.Perm.mem_support.mpr hi)⟩ ⟨σ i, hi.symm⟩
  exact ⟨fun h ↦ (IsExposedRotation.mk (hσ) (fun i hi ↦ (harc i hi).mp (h i (Equiv.Perm.mem_support.mpr hi)))),
    fun h i hi ↦ (harc i (Equiv.Perm.mem_support.mp hi)).mpr
      ((IsExposedRotation.successor h) i (Equiv.Perm.mem_support.mp hi))⟩
end StepC
end

-- PivotResidualEstimate
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepC
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
variable {n : ℕ}
private def forcedShortCycleException (μ ν : Matching n) (L : ℕ) : Set (ScoreProfile n) :=
  {x | ((forcedShortCycles (profileOfScores x) μ ν L).card : ℝ) <
    (9 / 10 : ℝ) * Real.log L}
private def backgroundShortCycleException (μ ν : Matching n) (L : ℕ) : Set (ScoreProfile n) :=
  {x | ((backgroundShortCycles (profileOfScores x) μ ν L).card : ℝ) <
    (9 / 10 : ℝ) * Real.log L}
theorem measurableSet_forcedShortCycleException (μ ν : Matching n) (L : ℕ) :
    MeasurableSet (forcedShortCycleException μ ν L) :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | ((forcedShortCycles p μ ν L).card : ℝ) <
      (9 / 10 : ℝ) * Real.log L})
theorem measurableSet_backgroundShortCycleException (μ ν : Matching n) (L : ℕ) :
    MeasurableSet (backgroundShortCycleException μ ν L) :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | ((backgroundShortCycles p μ ν L).card : ℝ) <
      (9 / 10 : ℝ) * Real.log L})
theorem scoreResidualPairEvent_subset_shortCycleExceptions {b : ℝ} {K L : ℕ}
    (hL : 2 ≤ L) (μ ν : Matching n) :
    scoreIncomparablePairEvent (IsResidualPairGeometry b K L) μ ν ⊆
      forcedShortCycleException μ ν L ∪ backgroundShortCycleException μ ν L := by
  intro x hx
  by_contra h
  have h1 := not_lt.mp (fun h1 ↦ h (Or.inl h1) :
    ¬ ((forcedShortCycles (profileOfScores x) μ ν L).card : ℝ) < (9 / 10 : ℝ) * Real.log L)
  have h2 := not_lt.mp (fun h2 ↦ h (Or.inr h2) :
    ¬ ((backgroundShortCycles (profileOfScores x) μ ν L).card : ℝ) < (9 / 10 : ℝ) * Real.log L)
  have hl : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  have hc := hx.2.2.2.rank.forced_background_card_le
  linarith
end StepC
end

-- TwoStableBackgroundCycleTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
variable {n : ℕ} {μ ν : Matching n}
private def jointBackgroundLabels (μ ν : Matching n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ μ i = ν i
@[simp] theorem mem_jointBackgroundLabels {i : Fin n} :
    i ∈ jointBackgroundLabels μ ν ↔ μ i = ν i := by
  simp [jointBackgroundLabels]
private def jointBackgroundFemaleTotal (d : JointSpouseScores μ ν) : ℝ :=
  ∑ j : Fin n, jointWomanSpouseScoreRight d (ν j)
private noncomputable def jointBackgroundWeight (d : JointSpouseScores μ ν) (j : Fin n) : ℝ :=
  jointWomanSpouseScoreRight d (ν j) / jointBackgroundFemaleTotal d
private noncomputable def jointBackgroundArcError (d : JointSpouseScores μ ν) (X : ℝ) : ℝ :=
  X + 1 / jointBackgroundFemaleTotal d
@[simp] theorem jointBackgroundFemaleTotal_split (μ ν : Matching n) (x : ScoreProfile n) :
    jointBackgroundFemaleTotal (splitTwoMatchingScores μ ν x).1 = femaleSpouseTotal x ν := by
  rw [femaleSpouseTotal_eq_sum_byHusband]
  unfold jointBackgroundFemaleTotal
  exact Finset.sum_congr rfl fun j _ ↦ jointWomanSpouseScoreRight_split μ ν x (ν j)
@[simp] theorem jointBackgroundWeight_split (μ ν : Matching n) (x : ScoreProfile n) (j : Fin n) :
    jointBackgroundWeight (splitTwoMatchingScores μ ν x).1 j =
      femaleSpouseScore x ν (ν j) / femaleSpouseTotal x ν := by
  rw [jointBackgroundWeight, jointBackgroundFemaleTotal_split,
    jointWomanSpouseScoreRight_split, femaleSpouseScore]
theorem measurable_jointBackgroundFemaleTotal (μ ν : Matching n) :
    Measurable (jointBackgroundFemaleTotal (μ := μ) (ν := ν)) :=
  Finset.measurable_sum _ fun _ _ ↦ measurable_snd.comp (measurable_pi_apply _)
theorem measurable_jointBackgroundWeight (μ ν : Matching n) (j : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointBackgroundWeight d j) :=
  (measurable_snd.comp (measurable_pi_apply _)).div (measurable_jointBackgroundFemaleTotal μ ν)
private structure HasJointBackgroundGeometry (d : JointSpouseScores μ ν) (L : ℕ) (X : ℝ) : Prop where
  total_pos : 0 < jointBackgroundFemaleTotal d
  male_le : ∀ i, jointManSpouseScoreRight d i ≤ X
  arc_loss : (L : ℝ) * jointBackgroundArcError d X ≤ 1 / 100
  label_loss : commonForwardLabelLoss (jointBackgroundLabels μ ν) (jointBackgroundWeight d) L ≤
    1 / 100
theorem jointBackgroundWeight_nonneg (d : JointSpouseScores μ ν)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1)
    (hY : 0 < jointBackgroundFemaleTotal d) (i : Fin n) :
    0 ≤ jointBackgroundWeight d i := div_nonneg (hR _).1 hY.le
theorem sum_jointBackgroundWeight (d : JointSpouseScores μ ν)
    (hY : 0 < jointBackgroundFemaleTotal d) : ∑ i, jointBackgroundWeight d i = 1 := by
  unfold jointBackgroundWeight
  rw [← Finset.sum_div]
  exact div_self hY.ne'
theorem HasJointBackgroundGeometry.arcError_mem {d : JointSpouseScores μ ν} {L : ℕ} {X : ℝ}
    (h : HasJointBackgroundGeometry d L X) (hL : 2 ≤ L) (hX : 0 ≤ X) :
    jointBackgroundArcError d X ∈ Icc 0 1 := by
  have hδ := add_nonneg hX (one_div_nonneg.mpr h.total_pos.le)
  have hL' : 1 ≤ (L : ℝ) := by exact_mod_cast (show 1 ≤ L by omega)
  exact ⟨hδ, (le_mul_of_one_le_left hδ hL').trans (h.arc_loss.trans (by norm_num))⟩
theorem HasJointBackgroundGeometry.arcLower
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    {d : JointSpouseScores μ ν} {L : ℕ} {X : ℝ} (h : HasJointBackgroundGeometry d L X)
    [∀ i, IsProbabilityMeasure (jointCommonSuccessorLaw d i)]
    (hmR : ∀ i, jointManSpouseScoreRight d i ∈ Ico 0 1)
    (hfL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hfR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    CommonForwardArcLower (jointCommonSuccessorLaw d) (jointBackgroundLabels μ ν)
      (jointBackgroundWeight d) (jointBackgroundArcError d X) := by
  intro i hi j _ hij
  let ic : CommonMan μ ν := ⟨i, mem_jointBackgroundLabels.mp hi⟩
  let jc : CommonRowCandidate ic := ⟨j, hij⟩
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
    (jointCommonSuccessorLaw_some_lower d ic jc (hmR i) hfL hfR (h.male_le i) h.total_pos)
theorem jointOffSpouseProbabilityLaw_fewCommonSuccessorCycles_le
    (d : JointSpouseScores μ ν) {L : ℕ} (hL : 2 ≤ L) (hlog : 100 ≤ Real.log (L : ℝ))
    {X : ℝ} (hX : 0 ≤ X)
    (hgeo : HasJointBackgroundGeometry d L X)
    (hmL : ∀ i, jointManSpouseScoreLeft d i ∈ Ico 0 1)
    (hmR : ∀ i, jointManSpouseScoreRight d i ∈ Ico 0 1)
    (hfL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hfR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    jointOffSpouseProbabilityLaw d {v |
      (commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) : ℝ) <
        (9 / 10 : ℝ) * Real.log (L : ℝ)} ≤ ENNReal.ofReal (1200 / Real.log (L : ℝ)) := by
  classical
  let : MeasurableSpace (Option (Fin n)) := ⊤
  let : DiscreteMeasurableSpace (Option (Fin n)) := ⟨fun _ ↦ trivial⟩
  let C := jointBackgroundLabels μ ν
  let p := jointBackgroundWeight d
  let r := jointCommonSuccessorLaw d
  have hpos := (jointOffSpouseScoreLaw_nonblocking_pos d hmL hmR).ne'
  let (i : Fin n) : IsProbabilityMeasure (r i) :=
    jointCommonSuccessorLaw_isProbabilityMeasure d hpos i
  have hp : ∀ i, 0 ≤ p i := jointBackgroundWeight_nonneg d hfR hgeo.total_pos
  let E : Set (Fin n → Option (Fin n)) := {f | (commonForwardCycleCount C L f : ℝ) <
    (9 / 10 : ℝ) * Real.log (L : ℝ)}
  change jointOffSpouseProbabilityLaw d (jointCommonSuccessors d ⁻¹' E) ≤ _
  rw [(measurePreserving_jointCommonSuccessors d hpos).measure_preimage
    (MeasurableSet.of_discrete : MeasurableSet E).nullMeasurableSet]
  exact measure_lt_commonForwardCycleCount_le r C hL p hp
    (sum_jointBackgroundWeight d hgeo.total_pos) (hgeo.arcError_mem hL hX) (hgeo.arcLower hmR hfL hfR)
    hgeo.arc_loss hgeo.label_loss hlog
theorem ae_jointSpouse_ae_commonForwardCycleCount_eq (μ ν : Matching n) (L : ℕ) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ᵐ v ∂jointOffSpouseProbabilityLaw d,
      d ∈ jointMarkedNonblocking μ ν →
        commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) =
          (backgroundShortCycles (profileOfScores ((splitTwoMatchingScores μ ν).symm
            (d, v))) μ ν L).card := by
  classical
  filter_upwards [ae_jointSpouse_ae_commonCycle_iff_exposed μ ν] with d hd
  filter_upwards [hd] with v hv
  intro hmark
  unfold commonForwardCycleCount realizedForwardCycleCount backgroundShortCycles exposedShortCycles
  congr 1
  ext σ
  simp only [Finset.mem_filter, mem_commonForwardCycles, Finset.mem_Icc, Finset.mem_univ, true_and]
  have hC : σ.support ⊆ jointBackgroundLabels μ ν ↔
      Disjoint σ.support (relativeMenPermutation μ ν).support := by
    rw [Finset.disjoint_left]
    refine ⟨fun h i hi hrel ↦ Equiv.Perm.mem_support.mp hrel ?_, fun h i hi ↦ ?_⟩
    · simpa only [relativeMenPermutation, Equiv.trans_apply, ν.symm_apply_eq] using
        mem_jointBackgroundLabels.mp (h hi)
    · simpa only [mem_jointBackgroundLabels, relativeMenPermutation, Equiv.trans_apply,
        ν.symm_apply_eq] using Equiv.Perm.notMem_support.mp (h hi)
  constructor
  · rintro ⟨⟨hcyc, hsub, -, hlen⟩, hreal⟩
    exact ⟨⟨(hv hmark σ hcyc (fun i hi ↦ mem_jointBackgroundLabels.mp (hsub hi))).mp hreal.2,
      hlen⟩, hC.mp hsub⟩
  · rintro ⟨⟨hexp, hlen⟩, hdis⟩
    have hsub := hC.mpr hdis
    exact ⟨⟨(IsExposedRotation.isCycle hexp), hsub, (IsExposedRotation.isCycle hexp).two_le_card_support, hlen⟩, (IsExposedRotation.isCycle hexp),
      (hv hmark σ (IsExposedRotation.isCycle hexp) (fun i hi ↦ mem_jointBackgroundLabels.mp (hsub hi))).mpr hexp⟩
theorem ae_jointOffSpouseProbabilityLaw_backgroundShortCycleException_le
    (μ ν : Matching n) {L : ℕ} (hL : 2 ≤ L) (hlog : 100 ≤ Real.log (L : ℝ))
    {X : ℝ} (hX : 0 ≤ X) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, d ∈ jointMarkedNonblocking μ ν →
      HasJointBackgroundGeometry d L X →
      jointOffSpouseProbabilityLaw d ((fun v ↦ (splitTwoMatchingScores μ ν).symm (d, v)) ⁻¹'
        backgroundShortCycleException μ ν L) ≤ ENNReal.ofReal (1200 / Real.log (L : ℝ)) := by
  filter_upwards [ae_jointSpouse_thresholds μ ν,
    ae_jointSpouse_ae_commonForwardCycleCount_eq μ ν L] with d hd hcount
  intro hmark hgeo
  have heq : ((fun v ↦ (splitTwoMatchingScores μ ν).symm (d, v)) ⁻¹'
        backgroundShortCycleException μ ν L) =ᵐ[jointOffSpouseProbabilityLaw d]
      {v | (commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) :
        ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ)} := by
    filter_upwards [hcount] with v hv
    apply propext
    change ((backgroundShortCycles (profileOfScores ((splitTwoMatchingScores μ ν).symm
      (d, v))) μ ν L).card : ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ) ↔
        (commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) :
          ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ)
    rw [hv hmark]
  rw [measure_congr heq]
  exact jointOffSpouseProbabilityLaw_fewCommonSuccessorCycles_le d hL hlog hX hgeo
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
theorem continuousScoreLaw_inter_backgroundShortCycleException_le
    (μ ν : Matching n) {L : ℕ} (hL : 2 ≤ L) (hlog : 100 ≤ Real.log (L : ℝ))
    {X : ℝ} (hX : 0 ≤ X)
    {D : Set (JointSpouseScores μ ν)} (hD : MeasurableSet D)
    (hgeo : ∀ᵐ d ∂jointSpouseScoreLaw μ ν, d ∈ D → HasJointBackgroundGeometry d L X) :
    let A := {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (splitTwoMatchingScores μ ν x).1 ∈ D}
    continuousScoreLaw n (A ∩ backgroundShortCycleException μ ν L) ≤
      ENNReal.ofReal (1200 / Real.log (L : ℝ)) * continuousScoreLaw n A := by
  let e := splitTwoMatchingScores μ ν
  let A := {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (e x).1 ∈ D}
  let E := backgroundShortCycleException μ ν L
  let g := E.indicator (1 : ScoreProfile n → ℝ≥0∞)
  let c := ENNReal.ofReal (1200 / Real.log (L : ℝ))
  let W (d : JointSpouseScores μ ν) := jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d)
  have hE : MeasurableSet E := measurableSet_backgroundShortCycleException μ ν L
  have hg : Measurable g := measurable_const.indicator hE
  have hW (d : JointSpouseScores μ ν) :
      (∫⁻ _v, (1 : ℝ≥0∞) ∂(Measure.pi (jointOffSpouseCellLaw d))) = W d := by
    rw [← jointOffSpouseScoreLaw_restrict_nonblocking, lintegral_const, one_mul,
      Measure.restrict_apply_univ]
  have hA : continuousScoreLaw n A =
      ∫⁻ d in D ∩ jointMarkedNonblocking μ ν, W d ∂jointSpouseScoreLaw μ ν := by
    calc
      _ = ∫⁻ _x in A, (1 : ℝ≥0∞) ∂continuousScoreLaw n := by
        rw [lintegral_const, one_mul, Measure.restrict_apply_univ]
      _ = ∫⁻ d in D ∩ jointMarkedNonblocking μ ν, ∫⁻ _v, (1 : ℝ≥0∞)
          ∂(Measure.pi (jointOffSpouseCellLaw d)) ∂jointSpouseScoreLaw μ ν :=
        continuousScoreLaw_lintegral_twoStable μ ν hD measurable_const
      _ = _ := lintegral_congr hW
  have hb : ∀ᵐ d ∂(jointSpouseScoreLaw μ ν).restrict (D ∩ jointMarkedNonblocking μ ν),
      (∫⁻ v, g (e.symm (d, v)) ∂(Measure.pi (jointOffSpouseCellLaw d))) ≤ c * W d := by
    rw [ae_restrict_iff' (hD.inter (measurableSet_jointMarkedNonblocking μ ν))]
    filter_upwards [ae_jointOffSpouseProbabilityLaw_backgroundShortCycleException_le μ ν
      hL hlog hX, ae_jointSpouse_thresholds μ ν, hgeo] with d hd hu hgd hmem
    have hpos := (jointOffSpouseScoreLaw_nonblocking_pos d hu.1 hu.2.1).ne'
    let F := (fun v ↦ e.symm (d, v)) ⁻¹' E
    have hF : MeasurableSet F := hE.preimage
      (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
    have hsec :
        (fun v ↦ g (e.symm (d, v))) =
          F.indicator (1 : JointOffSpouseScores μ ν → ℝ≥0∞) := by
      funext v
      change E.indicator (1 : ScoreProfile n → ℝ≥0∞) (e.symm (d, v)) =
        F.indicator (1 : JointOffSpouseScores μ ν → ℝ≥0∞) v
      by_cases h : v ∈ F
      · rw [Set.indicator_of_mem (show e.symm (d, v) ∈ E from h) _, Set.indicator_of_mem h]
        rfl
      · rw [Set.indicator_of_notMem (show e.symm (d, v) ∉ E from h) _, Set.indicator_of_notMem h]
    rw [← jointOffSpouseScoreLaw_restrict_nonblocking,
      jointOffSpouseScoreLaw_restrict_eq_smul_probabilityLaw d hpos,
      lintegral_smul_measure, smul_eq_mul, hsec, lintegral_indicator_one hF, mul_comm]
    exact mul_le_mul_left (hd hmem.2 (hgd hmem.1)) _
  change continuousScoreLaw n (A ∩ E) ≤ c * continuousScoreLaw n A
  calc
    _ = ∫⁻ x in A, g x ∂continuousScoreLaw n := by
      change continuousScoreLaw n (A ∩ E) =
        ∫⁻ x in A, E.indicator (1 : ScoreProfile n → ℝ≥0∞) x ∂continuousScoreLaw n
      rw [lintegral_indicator_one hE, Measure.restrict_apply hE, inter_comm]
    _ = ∫⁻ d in D ∩ jointMarkedNonblocking μ ν, ∫⁻ v, g (e.symm (d, v))
        ∂(Measure.pi (jointOffSpouseCellLaw d)) ∂jointSpouseScoreLaw μ ν :=
      continuousScoreLaw_lintegral_twoStable μ ν hD hg
    _ ≤ ∫⁻ d in D ∩ jointMarkedNonblocking μ ν, c * W d ∂jointSpouseScoreLaw μ ν :=
      lintegral_mono_ae hb
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hA]
end StepC
end

-- TwoStablePairDensity
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
private noncomputable def pairLaplace (s : ℝ) : ℝ :=
  ∫ t, Real.exp (-s * t) ∂unitScoreLaw
private theorem pairLaplace_integrable (s : ℝ) :
    Integrable (fun t ↦ Real.exp (-s * t)) unitScoreLaw :=
  (show Continuous (fun t : ℝ ↦ Real.exp (-s * t)) by fun_prop).integrableOn_Icc
theorem pairLaplace_nonneg (s : ℝ) : 0 ≤ pairLaplace s :=
  integral_nonneg fun _ ↦ (Real.exp_pos _).le
private theorem pairLaplace_of_ne_zero {s : ℝ} (hs : s ≠ 0) :
    pairLaplace s = (1 - Real.exp (-s)) / s := by
  have hderiv (t : ℝ) :
      HasDerivAt (fun x ↦ -(Real.exp (-s * x)) / s) (Real.exp (-s * t)) t := by
    exact (((Real.hasDerivAt_exp (-s * t)).comp t
      (hasDerivAt_const_mul (-s))).neg.div_const s).congr_deriv (by field_simp)
  unfold pairLaplace unitScoreLaw
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_one, mul_zero, Real.exp_zero]
  ring
theorem pairLaplace_of_pos {s : ℝ} (hs : 0 < s) :
    pairLaplace s = (1 - Real.exp (-s)) / s :=
  pairLaplace_of_ne_zero hs.ne'
private theorem measurable_pairLaplace : Measurable pairLaplace := by
  have heq : pairLaplace = ({0} : Set ℝ).piecewise (fun _ ↦ 1)
      (fun s ↦ (1 - Real.exp (-s)) / s) := by
    funext s
    by_cases h : s = 0
    · subst s
      simp [pairLaplace]
    · simpa [h] using pairLaplace_of_ne_zero h
  rw [heq]
  exact measurable_const.piecewise (measurableSet_singleton _) (by fun_prop)
theorem pairLaplace_le_exp_mul {s a : ℝ} (ha : 0 ≤ a) :
    pairLaplace (s - a) ≤ Real.exp a * pairLaplace s := by
  unfold pairLaplace
  rw [← integral_const_mul]
  refine integral_mono_ae (pairLaplace_integrable _) ((pairLaplace_integrable _).const_mul _) ?_
  have ht : ∀ᵐ t ∂unitScoreLaw, t ∈ Icc 0 1 := ae_restrict_mem measurableSet_Icc
  filter_upwards [ht] with t ht
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left ht.2 ha]
private theorem pairLaplace_le_exp_relative {s a : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) (hle : 2 * a ≤ s) :
    pairLaplace (s - a) ≤ Real.exp (2 * a / s) * pairLaplace s := by
  have hsa : 0 < s - a := by linarith
  have hnum : 1 - Real.exp (-(s - a)) ≤ 1 - Real.exp (-s) := by
    gcongr
    linarith
  have hrat : s / (s - a) ≤ 1 + 2 * a / s := by
    apply (div_le_iff₀ hsa).mpr
    rw [add_mul, one_mul, div_mul_eq_mul_div]
    have haux : a ≤ (2 * a * (s - a)) / s := by
      apply (le_div_iff₀ hs).mpr
      nlinarith only [mul_nonneg ha (sub_nonneg.mpr hle)]
    linarith
  rw [pairLaplace_of_pos hsa, pairLaplace_of_pos hs]
  calc
    _ ≤ (1 - Real.exp (-s)) / (s - a) := div_le_div_of_nonneg_right hnum hsa.le
    _ = (s / (s - a)) * ((1 - Real.exp (-s)) / s) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (hrat.trans (by simpa only [add_comm] using Real.add_one_le_exp (2 * a / s)))
      (div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))) hs.le)
theorem pairLaplace_omission_product {ι : Type*} (I : Finset ι) {s : ℝ}
    (a : ι → ℝ) (ha : ∀ i ∈ I, 0 ≤ a i) (hcap : ∀ i ∈ I, a i ≤ 6)
    (hsum : (∑ i ∈ I, a i) ≤ 2 * s) :
    (∏ i ∈ I, pairLaplace (s - a i)) ≤ Real.exp 24 * pairLaplace s ^ I.card := by
  by_cases h : s ≤ 12
  · calc
      _ ≤ ∏ i ∈ I, Real.exp (a i) * pairLaplace s :=
        Finset.prod_le_prod (fun _ _ ↦ pairLaplace_nonneg _)
          (fun i hi ↦ pairLaplace_le_exp_mul (ha i hi))
      _ = Real.exp (∑ i ∈ I, a i) * pairLaplace s ^ I.card := by
        rw [Finset.prod_mul_distrib, Real.exp_sum, Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        (pow_nonneg (pairLaplace_nonneg s) _)
  · have hs' : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 12) (le_of_not_ge h)
    calc
      _ ≤ ∏ i ∈ I, Real.exp (2 * a i / s) * pairLaplace s :=
        Finset.prod_le_prod (fun _ _ ↦ pairLaplace_nonneg _)
          (fun i hi ↦ pairLaplace_le_exp_relative hs' (ha i hi) (by linarith [hcap i hi]))
      _ = Real.exp (2 * (∑ i ∈ I, a i) / s) * pairLaplace s ^ I.card := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.mul_sum,
          Finset.sum_div]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          ((div_le_iff₀ hs').mpr (by linarith)))
        (pow_nonneg (pairLaplace_nonneg s) _)
private theorem unitScoreLaw_Ico_of_mem_Icc₂ {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    unitScoreLaw (Ico a b) = ENNReal.ofReal (b - a) := by
  have hsub : Ico a b ⊆ Icc 0 1 := fun _ ht ↦ ⟨ha.trans ht.1, ht.2.le.trans hb⟩
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ico, inter_eq_left.mpr hsub,
    Real.volume_Ico]
theorem unitScorePairLaw_jointNonblocking_of_le {x₁ y₁ x₂ y₂ : ℝ}
    (hx₁ : x₁ ∈ Icc 0 1) (hx₂ : x₂ ∈ Icc 0 1) (hy₁ : y₁ ∈ Icc 0 1)
    (hy₂ : y₂ ∈ Icc 0 1) (hx : x₁ ≤ x₂) :
    unitScorePairLaw (jointNonblockingScoreCell x₁ y₁ x₂ y₂) =
      1 - ENNReal.ofReal (x₁ * max y₁ y₂ + (x₂ - x₁) * y₂) := by
  let A := Iio x₁ ×ˢ Iio (max y₁ y₂)
  let B := Ico x₁ x₂ ×ˢ Iio y₂
  have hA : MeasurableSet A := measurableSet_Iio.prod measurableSet_Iio
  have hB : MeasurableSet B := measurableSet_Ico.prod measurableSet_Iio
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact (not_lt_of_ge (show x₁ ≤ p.1 from hq.1.1)) (show p.1 < x₁ from hp.1)
  have heq : jointNonblockingScoreCell x₁ y₁ x₂ y₂ = (A ∪ B)ᶜ := by
    ext p
    simp only [jointNonblockingScoreCell, nonblockingScoreCell, A, B, Set.mem_inter_iff,
      Set.mem_union, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio, Set.mem_Ico, lt_max_iff]
    constructor
    · rintro ⟨h₁, h₂⟩ (⟨hp, h₃ | h₄⟩ | ⟨⟨_, hq⟩, h₄⟩)
      · exact h₁ ⟨hp, h₃⟩
      · exact h₂ ⟨hp.trans_le hx, h₄⟩
      · exact h₂ ⟨hq, h₄⟩
    · intro h
      refine ⟨fun ⟨hp, hq⟩ ↦ h (Or.inl ⟨hp, Or.inl hq⟩), ?_⟩
      rintro ⟨hp, hq⟩
      rcases lt_or_ge p.1 x₁ with hlt | hge
      · exact h (Or.inl ⟨hlt, Or.inr hq⟩)
      · exact h (Or.inr ⟨⟨hge, hp⟩, hq⟩)
  have hymax : max y₁ y₂ ∈ Icc 0 1 := ⟨hy₁.1.trans (le_max_left _ _), max_le hy₁.2 hy₂.2⟩
  rw [heq, measure_compl (hA.union hB) (measure_ne_top _ _), measure_univ,
    measure_union hdisj hB]
  dsimp only [A, B]
  rw [unitScorePairLaw, Measure.prod_prod, Measure.prod_prod, unitScoreLaw_Iio_of_mem_Icc hx₁,
    unitScoreLaw_Iio_of_mem_Icc hymax, unitScoreLaw_Ico_of_mem_Icc₂ hx₁.1 hx₂.2,
    unitScoreLaw_Iio_of_mem_Icc hy₂, ← ENNReal.ofReal_mul hx₁.1,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hx), ← ENNReal.ofReal_add (mul_nonneg hx₁.1 hymax.1)
      (mul_nonneg (sub_nonneg.mpr hx) hy₂.1)]
theorem unitScorePairLaw_jointNonblocking_le_exp_of_le {x₁ y₁ x₂ y₂ : ℝ}
    (hx₁ : x₁ ∈ Icc 0 1) (hx₂ : x₂ ∈ Icc 0 1) (hy₁ : y₁ ∈ Icc 0 1)
    (hy₂ : y₂ ∈ Icc 0 1) (hx : x₁ ≤ x₂) :
    unitScorePairLaw (jointNonblockingScoreCell x₁ y₁ x₂ y₂) ≤
      ENNReal.ofReal (Real.exp (-(x₁ * max y₁ y₂ + (x₂ - x₁) * y₂))) := by
  rw [unitScorePairLaw_jointNonblocking_of_le hx₁ hx₂ hy₁ hy₂ hx,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub]
  · exact ENNReal.ofReal_le_ofReal (Real.one_sub_le_exp_neg _)
  · exact add_nonneg (mul_nonneg hx₁.1 (hy₁.1.trans (le_max_left _ _)))
      (mul_nonneg (sub_nonneg.mpr hx) hy₂.1)
private def jointSpouseOrientation {μ ν : Matching n} (A B : Finset (Fin n)) :
    Set (JointSpouseScores μ ν) :=
  {d | (∀ m, if m ∈ A then jointManSpouseScoreLeft d m ≤ jointManSpouseScoreRight d m
      else jointManSpouseScoreRight d m ≤ jointManSpouseScoreLeft d m) ∧
    ∀ w, if w ∈ B then jointWomanSpouseScoreRight d w ≤ jointWomanSpouseScoreLeft d w
      else jointWomanSpouseScoreLeft d w ≤ jointWomanSpouseScoreRight d w}
private def JointSpouseThresholdsUnit {μ ν : Matching n} (d : JointSpouseScores μ ν) : Prop :=
  (∀ m, jointManSpouseScoreLeft d m ∈ Icc 0 1 ∧ jointManSpouseScoreRight d m ∈ Icc 0 1) ∧
  (∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1 ∧ jointWomanSpouseScoreRight d w ∈ Icc 0 1)
private def jointBetterMaleScore {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  min (jointManSpouseScoreLeft d m) (jointManSpouseScoreRight d m)
private def jointMaleScoreGap {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  max (jointManSpouseScoreLeft d m) (jointManSpouseScoreRight d m) - jointBetterMaleScore d m
private def jointWorseFemaleScore {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  max (jointWomanSpouseScoreLeft d w) (jointWomanSpouseScoreRight d w)
private def jointExtraFemaleThreshold {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (A : Finset (Fin n)) (m w : Fin n) : ℝ :=
  if m ∈ A then jointWomanSpouseScoreRight d w else jointWomanSpouseScoreLeft d w
theorem jointNonblockingCellAt_mass_le_orientedExp {μ ν : Matching n}
    {d : JointSpouseScores μ ν} {A B : Finset (Fin n)}
    (hd : JointSpouseThresholdsUnit d) (ho : d ∈ jointSpouseOrientation A B)
    (q : ScorePairIndex n) :
    unitScorePairLaw (jointNonblockingCellAt d q) ≤ ENNReal.ofReal (Real.exp (-
      (jointBetterMaleScore d q.1 * jointWorseFemaleScore d q.2 +
        jointMaleScoreGap d q.1 * jointExtraFemaleThreshold d A q.1 q.2))) := by
  have hm := ho.1 q.1
  by_cases h : q.1 ∈ A
  · have hle : jointManSpouseScoreLeft d q.1 ≤ jointManSpouseScoreRight d q.1 := by
      simpa only [if_pos h] using hm
    simpa only [jointNonblockingCellAt, jointBetterMaleScore, jointWorseFemaleScore,
      jointMaleScoreGap, jointExtraFemaleThreshold, if_pos h, min_eq_left hle, max_eq_right hle]
      using unitScorePairLaw_jointNonblocking_le_exp_of_le (hd.1 q.1).1 (hd.1 q.1).2
        (hd.2 q.2).1 (hd.2 q.2).2 hle
  · have hle : jointManSpouseScoreRight d q.1 ≤ jointManSpouseScoreLeft d q.1 := by
      simpa only [if_neg h] using hm
    have hswap : jointNonblockingCellAt d q =
        jointNonblockingScoreCell (jointManSpouseScoreRight d q.1)
          (jointWomanSpouseScoreRight d q.2) (jointManSpouseScoreLeft d q.1)
          (jointWomanSpouseScoreLeft d q.2) := Set.inter_comm _ _
    rw [hswap]
    simpa only [jointBetterMaleScore, jointWorseFemaleScore, jointMaleScoreGap,
      jointExtraFemaleThreshold, if_neg h, min_eq_right hle, max_eq_left hle, max_comm]
      using unitScorePairLaw_jointNonblocking_le_exp_of_le (hd.1 q.1).2 (hd.1 q.1).1
        (hd.2 q.2).2 (hd.2 q.2).1 hle
private def pairOmittedWomen (μ ν : Matching n) (m : Fin n) : Finset (Fin n) := {μ m, ν m}
private def pairUnmarkedRowSum (μ ν : Matching n) (m : Fin n) (y : Fin n → ℝ) : ℝ :=
  ∑ w ∈ Finset.univ \ pairOmittedWomen μ ν m, y w
private def pairRowLoss (μ ν : Matching n) (m : Fin n) (y : Fin n → ℝ) : ℝ :=
  ∑ w ∈ pairOmittedWomen μ ν m, y w
theorem pairUnmarkedRowSum_eq_sub (μ ν : Matching n) (m : Fin n) (y : Fin n → ℝ) :
    pairUnmarkedRowSum μ ν m y = (∑ w, y w) - pairRowLoss μ ν m y := by
  rw [pairUnmarkedRowSum, pairRowLoss, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
private def jointOffSpouseByRow (μ ν : Matching n) :
    JointOffSpouseIndex μ ν ≃
      Σ m : Fin n, {w : Fin n // w ∈ Finset.univ \ pairOmittedWomen μ ν m} where
  toFun q := ⟨q.val.1, q.val.2, by
    simpa [JointSpouseCell, pairOmittedWomen, eq_comm] using q.property⟩
  invFun q := ⟨(q.1, q.2.val), by
    have h := (Finset.mem_sdiff.mp q.2.property).2
    simpa only [JointSpouseCell, pairOmittedWomen, Finset.mem_insert, Finset.mem_singleton,
      eq_comm] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl
private theorem sum_jointOffSpouseIndex (μ ν : Matching n) (f : Fin n → Fin n → ℝ) :
    (∑ q : JointOffSpouseIndex μ ν, f q.val.1 q.val.2) =
      ∑ m, pairUnmarkedRowSum μ ν m (f m) := by
  calc
    _ = ∑ q : Σ m : Fin n, {w : Fin n // w ∈ Finset.univ \ pairOmittedWomen μ ν m},
        f q.1 q.2.val :=
      Fintype.sum_equiv (jointOffSpouseByRow μ ν) _ _ (fun _ ↦ rfl)
    _ = _ := ?_
  rw [Fintype.sum_sigma]
  congr 1
  funext m
  exact (Finset.sum_subtype (Finset.univ \ pairOmittedWomen μ ν m)
    (fun _ ↦ Iff.rfl) (f m)).symm
theorem jointOffSpouseScoreLaw_nonblocking_le_rowExp {μ ν : Matching n}
    {d : JointSpouseScores μ ν} {A B : Finset (Fin n)}
    (hd : JointSpouseThresholdsUnit d) (ho : d ∈ jointSpouseOrientation A B) :
    jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≤ ENNReal.ofReal (Real.exp (-
      ∑ m, (jointBetterMaleScore d m * pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d) +
        jointMaleScoreGap d m * pairUnmarkedRowSum μ ν m (jointExtraFemaleThreshold d A m)))) := by
  let e (m w : Fin n) := jointBetterMaleScore d m * jointWorseFemaleScore d w +
    jointMaleScoreGap d m * jointExtraFemaleThreshold d A m w
  rw [jointOffSpouseScoreLaw_nonblocking]
  calc
    _ ≤ ∏ q : JointOffSpouseIndex μ ν, ENNReal.ofReal (Real.exp (-e q.val.1 q.val.2)) :=
      Finset.prod_le_prod' fun q _ ↦ jointNonblockingCellAt_mass_le_orientedExp hd ho q.val
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le), ← Real.exp_sum]
      simp only [Finset.sum_neg_distrib]
      rw [sum_jointOffSpouseIndex μ ν e]
      congr 3
      apply Finset.sum_congr rfl
      intro m _
      simp only [pairUnmarkedRowSum, e, Finset.sum_add_distrib, Finset.mul_sum]
private theorem pairRowLoss_le_two_scores (μ ν : Matching n) (m : Fin n)
    {y : Fin n → ℝ} (hy : ∀ w, 0 ≤ y w) :
    pairRowLoss μ ν m y ≤ y (μ m) + y (ν m) := by
  by_cases h : μ m = ν m
  · simp only [pairRowLoss, pairOmittedWomen, h, Finset.insert_eq_of_mem, Finset.mem_singleton,
      Finset.sum_singleton]
    linarith [hy (ν m)]
  · simp [pairRowLoss, pairOmittedWomen, h]
private theorem pairRowLoss_sum_le (μ ν : Matching n) (I : Finset (Fin n))
    {y : Fin n → ℝ} (hy : ∀ w, 0 ≤ y w) :
    (∑ m ∈ I, pairRowLoss μ ν m y) ≤ 2 * ∑ w, y w := by
  calc
    _ ≤ ∑ m ∈ I, (y (μ m) + y (ν m)) :=
      Finset.sum_le_sum fun m _ ↦ pairRowLoss_le_two_scores μ ν m hy
    _ ≤ ∑ m, (y (μ m) + y (ν m)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun m _ _ ↦
        add_nonneg (hy (μ m)) (hy (ν m))
    _ = _ := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp μ y, Equiv.sum_comp ν y, two_mul]
theorem pairLaplace_unmarkedRowSum_product (μ ν : Matching n) (I : Finset (Fin n))
    {y : Fin n → ℝ} (hy : ∀ w, y w ∈ Icc 0 1) :
    (∏ m ∈ I, pairLaplace (pairUnmarkedRowSum μ ν m y)) ≤
      Real.exp 24 * pairLaplace (∑ w, y w) ^ I.card := by
  simp_rw [pairUnmarkedRowSum_eq_sub]
  refine pairLaplace_omission_product I _ (fun m _ ↦ Finset.sum_nonneg fun w _ ↦ (hy w).1)
    (fun m _ ↦ ?_) (pairRowLoss_sum_le μ ν I (fun w ↦ (hy w).1))
  have hm := pairRowLoss_le_two_scores μ ν m (fun w ↦ (hy w).1)
  linarith [(hy (μ m)).2, (hy (ν m)).2]
private def jointBetterFemaleScore {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  min (jointWomanSpouseScoreLeft d w) (jointWomanSpouseScoreRight d w)
private def jointFemaleScoreGap {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  jointWorseFemaleScore d w - jointBetterFemaleScore d w
private def jointFemaleAggregate {μ ν : Matching n} (d : JointSpouseScores μ ν) (B : Finset (Fin n)) :
    ℝ × ℝ × ℝ :=
  (∑ w, jointBetterFemaleScore d w,
    ∑ w ∈ B, jointFemaleScoreGap d w,
    ∑ w ∈ Finset.univ \ B, jointFemaleScoreGap d w)
private theorem jointFemale_sum_left_right {μ ν : Matching n}
    {d : JointSpouseScores μ ν} {A B : Finset (Fin n)} (ho : d ∈ jointSpouseOrientation A B) :
    (∑ w, jointWomanSpouseScoreLeft d w) =
        (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.1 ∧
      (∑ w, jointWomanSpouseScoreRight d w) =
        (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.2 := by
  have hL (w : Fin n) : jointWomanSpouseScoreLeft d w = jointBetterFemaleScore d w +
      if w ∈ B then jointFemaleScoreGap d w else 0 := by
    have h := ho.2 w
    by_cases hw : w ∈ B
    · simp only [if_pos hw] at h ⊢
      simp [jointFemaleScoreGap, jointBetterFemaleScore, jointWorseFemaleScore,
        min_eq_right h, max_eq_left h]
    · simp only [if_neg hw] at h ⊢
      simp [jointBetterFemaleScore, min_eq_left h]
  have hR (w : Fin n) : jointWomanSpouseScoreRight d w = jointBetterFemaleScore d w +
      if w ∈ Finset.univ \ B then jointFemaleScoreGap d w else 0 := by
    have h := ho.2 w
    by_cases hw : w ∈ B
    · simp only [if_pos hw] at h
      simp [jointBetterFemaleScore, hw, min_eq_right h]
    · simp only [if_neg hw] at h
      simp [jointFemaleScoreGap, jointBetterFemaleScore, jointWorseFemaleScore, hw,
        min_eq_left h, max_eq_right h]
  constructor
  · simp_rw [hL, Finset.sum_add_distrib, ← Finset.sum_filter]
    simp [jointFemaleAggregate]
  · simp_rw [hR, Finset.sum_add_distrib, ← Finset.sum_filter]
    simp [jointFemaleAggregate, Finset.sdiff_eq_filter]
private theorem jointFemale_sum_worse {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (B : Finset (Fin n)) :
    (∑ w, jointWorseFemaleScore d w) =
      (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.1 +
        (jointFemaleAggregate d B).2.2 := by
  have h (w : Fin n) :
      jointWorseFemaleScore d w = jointBetterFemaleScore d w + jointFemaleScoreGap d w := by
    simp [jointFemaleScoreGap]
  simp only [h, Finset.sum_add_distrib, jointFemaleAggregate]
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ B)]
  ring
private noncomputable def pairAggregateLaplace (n u v : ℕ) (s : ℝ × ℝ × ℝ) : ℝ :=
  pairLaplace (s.1 + s.2.1 + s.2.2) ^ n *
    pairLaplace (s.1 + s.2.2) ^ u * pairLaplace (s.1 + s.2.1) ^ v
theorem pairLaplace_rows_le_aggregate {μ ν : Matching n} {d : JointSpouseScores μ ν}
    {A B : Finset (Fin n)} (hd : JointSpouseThresholdsUnit d)
    (ho : d ∈ jointSpouseOrientation A B) (I J : Finset (Fin n)) :
    (∏ m, pairLaplace (pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d))) *
        (∏ m ∈ I, pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreRight d))) *
        (∏ m ∈ J, pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreLeft d))) ≤
      Real.exp 72 * pairAggregateLaplace n I.card J.card (jointFemaleAggregate d B) := by
  have hW (w : Fin n) : jointWorseFemaleScore d w ∈ Icc 0 1 :=
    ⟨(hd.2 w).1.1.trans (le_max_left _ _), max_le (hd.2 w).1.2 (hd.2 w).2.2⟩
  have h₀ := pairLaplace_unmarkedRowSum_product μ ν Finset.univ hW
  have h₁ := pairLaplace_unmarkedRowSum_product μ ν I (fun w ↦ (hd.2 w).2)
  have h₂ := pairLaplace_unmarkedRowSum_product μ ν J (fun w ↦ (hd.2 w).1)
  rw [Finset.card_univ, Fintype.card_fin, jointFemale_sum_worse d B] at h₀
  rw [(jointFemale_sum_left_right ho).2] at h₁
  rw [(jointFemale_sum_left_right ho).1] at h₂
  have hle := mul_le_mul
    (mul_le_mul h₀ h₁ (Finset.prod_nonneg fun _ _ ↦ pairLaplace_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (pairLaplace_nonneg _) _)))
    h₂ (Finset.prod_nonneg fun _ _ ↦ pairLaplace_nonneg _)
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (pairLaplace_nonneg _) _))
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (pairLaplace_nonneg _) _)))
  apply hle.trans_eq
  rw [show (72 : ℝ) = 24 + 24 + 24 by norm_num, Real.exp_add, Real.exp_add,
    pairAggregateLaplace]
  ring
private theorem measurable_jointManSpouseScoreLeft (μ ν : Matching n) (m : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointManSpouseScoreLeft d m) :=
  measurable_fst.comp (measurable_pi_apply _)
private theorem measurable_jointManSpouseScoreRight (μ ν : Matching n) (m : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointManSpouseScoreRight d m) :=
  measurable_fst.comp (measurable_pi_apply _)
private theorem measurable_jointWomanSpouseScoreLeft (μ ν : Matching n) (w : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointWomanSpouseScoreLeft d w) :=
  measurable_snd.comp (measurable_pi_apply _)
private theorem measurable_jointWomanSpouseScoreRight (μ ν : Matching n) (w : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointWomanSpouseScoreRight d w) :=
  measurable_snd.comp (measurable_pi_apply _)
theorem measurableSet_jointSpouseOrientation (μ ν : Matching n) (A B : Finset (Fin n)) :
    MeasurableSet (jointSpouseOrientation (μ := μ) (ν := ν) A B) := by
  unfold jointSpouseOrientation
  rw [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun m ↦ ?_).inter (MeasurableSet.iInter fun w ↦ ?_)
  · by_cases hm : m ∈ A
    · simpa only [if_pos hm] using measurableSet_le (measurable_jointManSpouseScoreLeft μ ν m)
        (measurable_jointManSpouseScoreRight μ ν m)
    · simpa only [if_neg hm] using measurableSet_le (measurable_jointManSpouseScoreRight μ ν m)
        (measurable_jointManSpouseScoreLeft μ ν m)
  · by_cases hw : w ∈ B
    · simpa only [if_pos hw] using measurableSet_le (measurable_jointWomanSpouseScoreRight μ ν w)
        (measurable_jointWomanSpouseScoreLeft μ ν w)
    · simpa only [if_neg hw] using measurableSet_le (measurable_jointWomanSpouseScoreLeft μ ν w)
        (measurable_jointWomanSpouseScoreRight μ ν w)
theorem measurable_jointFemaleAggregate (μ ν : Matching n) (B : Finset (Fin n)) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointFemaleAggregate d B) := by
  have hL := measurable_jointWomanSpouseScoreLeft μ ν
  have hR := measurable_jointWomanSpouseScoreRight μ ν
  have hb (w : Fin n) : Measurable (fun d : JointSpouseScores μ ν ↦ jointBetterFemaleScore d w) :=
    (hL w).min (hR w)
  have hg (w : Fin n) : Measurable (fun d : JointSpouseScores μ ν ↦ jointFemaleScoreGap d w) :=
    ((hL w).max (hR w)).sub (hb w)
  exact (Finset.measurable_sum _ fun w _ ↦ hb w).prodMk
    ((Finset.measurable_sum _ fun w _ ↦ hg w).prodMk (Finset.measurable_sum _ fun w _ ↦ hg w))
theorem ae_jointSpouseThresholdsUnit (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, JointSpouseThresholdsUnit d := by
  have h : ∀ᵐ p ∂unitScorePairLaw, p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    have h₁ : ∀ᵐ t ∂unitScoreLaw, t ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
    exact (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Icc.prod measurableSet_Icc)).mpr
      (h₁.mono fun _ ht ↦ h₁.mono fun _ hs ↦ ⟨ht, hs⟩)
  have hd : ∀ᵐ d ∂jointSpouseScoreLaw μ ν,
      ∀ q, d q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ae_all_iff.mpr fun q ↦ (measurePreserving_eval (fun _ ↦ unitScorePairLaw) q).quasiMeasurePreserving.ae h
  filter_upwards [hd] with d h
  exact ⟨fun m ↦ ⟨(h ⟨(m, μ m), Or.inl rfl⟩).1, (h ⟨(m, ν m), Or.inr rfl⟩).1⟩,
    fun w ↦ ⟨(h ⟨(μ.symm w, w), Or.inl (μ.apply_symm_apply w)⟩).2,
      (h ⟨(ν.symm w, w), Or.inr (ν.apply_symm_apply w)⟩).2⟩⟩
private def twoStableOrientationEvent (μ ν : Matching n) (A B : Finset (Fin n)) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧
    (splitTwoMatchingScores μ ν x).1 ∈ jointSpouseOrientation A B}
private noncomputable def orientedPairRowExp {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (A : Finset (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-
    ∑ m, (jointBetterMaleScore d m * pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d) +
      jointMaleScoreGap d m * pairUnmarkedRowSum μ ν m (jointExtraFemaleThreshold d A m))))
theorem continuousScoreLaw_lintegral_twoStableOrientation_le_rowExp (μ ν : Matching n)
    (A B : Finset (Fin n)) {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in twoStableOrientationEvent μ ν A B,
      g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n) ≤
      ∫⁻ d in jointSpouseOrientation A B, g (jointFemaleAggregate d B) * orientedPairRowExp d A
        ∂jointSpouseScoreLaw μ ν := by
  let f (x : ScoreProfile n) := g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B)
  have hf : Measurable f := hg.comp ((measurable_jointFemaleAggregate μ ν B).comp
    (measurable_fst.comp (splitTwoMatchingScores μ ν).measurable))
  let C := jointSpouseOrientation (μ := μ) (ν := ν) A B
  have hC : MeasurableSet C := measurableSet_jointSpouseOrientation μ ν A B
  change (∫⁻ x in _, f x ∂continuousScoreLaw n) ≤ _
  rw [twoStableOrientationEvent, continuousScoreLaw_lintegral_twoStable μ ν hC hf]
  have heq (d : JointSpouseScores μ ν) :
      (∫⁻ v, f ((splitTwoMatchingScores μ ν).symm (d, v))
        ∂(Measure.pi (jointOffSpouseCellLaw d))) =
      g (jointFemaleAggregate d B) *
        jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) := by
    simp only [f, MeasurableEquiv.apply_symm_apply, lintegral_const]
    rw [← jointOffSpouseScoreLaw_restrict_nonblocking, Measure.restrict_apply_univ]
  simp_rw [heq]
  calc
    _ ≤ ∫⁻ d in C, g (jointFemaleAggregate d B) *
        jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ∂jointSpouseScoreLaw μ ν :=
      lintegral_mono_set Set.inter_subset_left
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae (ae_jointSpouseThresholdsUnit μ ν),
        ae_restrict_mem hC] with d hd ho
      exact mul_le_mul_right (jointOffSpouseScoreLaw_nonblocking_le_rowExp hd ho) _
private noncomputable def pairUnitArrayLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ ↦ unitScoreLaw
private instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (pairUnitArrayLaw ι) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : ι ↦ unitScoreLaw))
private def pairUnitCube (ι : Type*) : Set (ι → ℝ) :=
  univ.pi fun _ ↦ Icc 0 1
private theorem pairUnitArrayLaw_eq_restrict (ι : Type*) [Fintype ι] :
    pairUnitArrayLaw ι = (volume : Measure (ι → ℝ)).restrict (pairUnitCube ι) :=
  (Measure.restrict_pi_pi (fun _ : ι ↦ volume) _).symm
theorem pairUnitArrayLaw_lintegral_orderedGap_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (owner : κ → ι) {f : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p in {p : (ι → ℝ) × (κ → ℝ) | ∀ j, p.1 (owner j) ≤ p.2 j},
      f (p.1, fun j ↦ p.2 j - p.1 (owner j))
        ∂((pairUnitArrayLaw ι).prod (pairUnitArrayLaw κ))) ≤
      ∫⁻ p, f p ∂((pairUnitArrayLaw ι).prod (pairUnitArrayLaw κ)) := by
  let Ω := (ι → ℝ) × (κ → ℝ)
  let μ := (volume : Measure (ι → ℝ)).prod (volume : Measure (κ → ℝ))
  let S : Set Ω := {p | ∀ j, p.1 (owner j) ≤ p.2 j}
  let T : Set Ω := pairUnitCube ι ×ˢ pairUnitCube κ
  let F : Ω → Ω := fun p ↦ (p.1, p.2 - fun j ↦ p.1 (owner j))
  have hS : MeasurableSet S := by
    rw [show S = ⋂ j : κ, {p : Ω | p.1 (owner j) ≤ p.2 j} from Set.ofPred_forall _]
    exact MeasurableSet.iInter fun j ↦ measurableSet_le
      ((measurable_pi_apply _).comp measurable_fst) ((measurable_pi_apply _).comp measurable_snd)
  have hT : MeasurableSet T :=
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).prod
      (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)
  have hF : MeasurePreserving F μ μ := by
    have hm : Measurable (fun p : Ω ↦ p.2 - fun j ↦ p.1 (owner j)) :=
      measurable_snd.sub (measurable_pi_iff.2 fun _ ↦
        (measurable_pi_apply _).comp measurable_fst)
    exact (MeasurePreserving.id (volume : Measure (ι → ℝ))).skew_product hm
      (Filter.Eventually.of_forall fun x ↦ by
        simpa only [sub_eq_add_neg] using
          (measurePreserving_add_right (volume : Measure (κ → ℝ))
            (-(fun j ↦ x (owner j)))).map_eq)
  have hsub : S ∩ T ⊆ F ⁻¹' T := by
    rintro ⟨x, y⟩ ⟨hxy, hx, hy⟩
    refine ⟨hx, Set.mem_univ_pi.mpr fun j ↦ ?_⟩
    change y j - x (owner j) ∈ Icc 0 1
    exact ⟨sub_nonneg.mpr (hxy j), sub_le_self _ ((Set.mem_univ_pi.mp hx (owner j)).1)
      |>.trans ((Set.mem_univ_pi.mp hy j).2)⟩
  change (∫⁻ p in S, f (F p) ∂_) ≤ _
  rw [pairUnitArrayLaw_eq_restrict, pairUnitArrayLaw_eq_restrict, Measure.prod_restrict,
    Measure.restrict_restrict hS]
  change (∫⁻ p in S ∩ T, f (F p) ∂μ) ≤ ∫⁻ p in T, f p ∂μ
  exact (lintegral_mono_set hsub).trans_eq (hF.setLIntegral_comp_preimage hT hf)
private noncomputable def pairExpSum {α : Type*} [Fintype α] (r : α → ℝ) (x : α → ℝ) :=
  ENNReal.ofReal (Real.exp (-(∑ i, x i * r i)))
private theorem measurable_pairExpSum {α : Type*} [Fintype α] (r : α → ℝ) :
    Measurable (pairExpSum r) := by
  apply ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.neg ?_))
  exact Finset.measurable_sum _ fun i _ ↦ (measurable_pi_apply i).mul_const _
private theorem pairUnitArrayLaw_lintegral_exp_sum {α : Type*} [Fintype α] (r : α → ℝ) :
    (∫⁻ x, pairExpSum r x ∂pairUnitArrayLaw α) = ENNReal.ofReal (∏ i, pairLaplace (r i)) := by
  let k (i : α) (t : ℝ) := ENNReal.ofReal (Real.exp (-(t * r i)))
  have hk (i : α) : Measurable (k i) := by unfold k; fun_prop
  have heq (x : α → ℝ) : pairExpSum r x = ∏ i, k i (x i) := by
    rw [pairExpSum, ← Finset.sum_neg_distrib, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
    exact fun _ _ ↦ (Real.exp_pos _).le
  have hcoord (i : α) : (∫⁻ x : α → ℝ, k i (x i) ∂pairUnitArrayLaw α) =
      ENNReal.ofReal (pairLaplace (r i)) := by
    unfold pairUnitArrayLaw
    rw [(measurePreserving_eval (fun _ : α ↦ unitScoreLaw) i).lintegral_comp (hk i)]
    have hk' (t : ℝ) : k i t = ENNReal.ofReal (Real.exp (-r i * t)) := by
      dsimp only [k]
      ring_nf
    simp_rw [hk']
    exact (ofReal_integral_eq_lintegral_ofReal (pairLaplace_integrable _)
      (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)).symm
  simp_rw [heq]
  change (∫⁻ x : α → ℝ, ∏ i, k i (x i) ∂Measure.pi (fun _ : α ↦ unitScoreLaw)) = _
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
    (ProbabilityTheory.iIndepFun_pi fun i ↦ (hk i).aemeasurable)
    (fun i ↦ (hk i).comp (measurable_pi_apply i))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ pairLaplace_nonneg _)]
  exact Finset.prod_congr rfl fun i _ ↦ hcoord i
theorem pairUnitArrayLaw_lintegral_exp_sums {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) :
    (∫⁻ p : (ι → ℝ) × (κ → ℝ), ENNReal.ofReal (Real.exp
      (-(∑ i, p.1 i * a i) - ∑ j, p.2 j * b j))
      ∂((pairUnitArrayLaw ι).prod (pairUnitArrayLaw κ))) =
      ENNReal.ofReal ((∏ i, pairLaplace (a i)) * ∏ j, pairLaplace (b j)) := by
  have heq (p : (ι → ℝ) × (κ → ℝ)) : ENNReal.ofReal (Real.exp
      (-(∑ i, p.1 i * a i) - ∑ j, p.2 j * b j)) = pairExpSum a p.1 * pairExpSum b p.2 := by
    rw [pairExpSum, pairExpSum, sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [heq]
  rw [lintegral_prod_mul (measurable_pairExpSum a).aemeasurable (measurable_pairExpSum b).aemeasurable,
    pairUnitArrayLaw_lintegral_exp_sum, pairUnitArrayLaw_lintegral_exp_sum, ENNReal.ofReal_mul]
  exact Finset.prod_nonneg fun _ _ ↦ pairLaplace_nonneg _
private abbrev PairMovedMan (μ ν : Matching n) := {m : Fin n // μ m ≠ ν m}
private def pairBetterSpouseCell (μ ν : Matching n) (A : Finset (Fin n))
    (m : Fin n) : JointSpouseIndex μ ν :=
  if m ∈ A then ⟨(m, μ m), Or.inl rfl⟩ else ⟨(m, ν m), Or.inr rfl⟩
private def pairWorseSpouseCell (μ ν : Matching n) (A : Finset (Fin n))
    (m : Fin n) : JointSpouseIndex μ ν :=
  if m ∈ A then ⟨(m, ν m), Or.inr rfl⟩ else ⟨(m, μ m), Or.inl rfl⟩
private theorem pairBetterSpouseCell_row (μ ν : Matching n) (A : Finset (Fin n)) (m : Fin n) :
    (pairBetterSpouseCell μ ν A m).val.1 = m := by
  unfold pairBetterSpouseCell
  split <;> rfl
private theorem pairWorseSpouseCell_row (μ ν : Matching n) (A : Finset (Fin n)) (m : Fin n) :
    (pairWorseSpouseCell μ ν A m).val.1 = m := by
  unfold pairWorseSpouseCell
  split <;> rfl
private theorem pairBetterSpouseCell_ne_worse (μ ν : Matching n) (A : Finset (Fin n))
    {m : Fin n} (hm : μ m ≠ ν m) :
    pairBetterSpouseCell μ ν A m ≠ pairWorseSpouseCell μ ν A m := by
  by_cases hA : m ∈ A
  · intro h
    have h' := congrArg (fun q : JointSpouseIndex μ ν ↦ q.val.2) h
    exact hm (by simpa [pairBetterSpouseCell, pairWorseSpouseCell, hA] using h')
  · intro h
    have h' := congrArg (fun q : JointSpouseIndex μ ν ↦ q.val.2) h
    exact hm (by simpa [pairBetterSpouseCell, pairWorseSpouseCell, hA, eq_comm] using h')
private noncomputable def pairSpouseCellByRow (μ ν : Matching n) (A : Finset (Fin n)) :
    (Fin n ⊕ PairMovedMan μ ν) ≃ JointSpouseIndex μ ν := by
  let F : Fin n ⊕ PairMovedMan μ ν → JointSpouseIndex μ ν :=
    Sum.elim (pairBetterSpouseCell μ ν A) (fun m ↦ pairWorseSpouseCell μ ν A m.val)
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro i j hij
    have h := congrArg (fun q : JointSpouseIndex μ ν ↦ q.val.1) hij
    rcases i with i | i <;> rcases j with j | j
    · simpa only [F, Sum.elim_inl, pairBetterSpouseCell_row, Sum.inl.injEq] using h
    · have h' : i = j.val := by
        simpa only [F, Sum.elim_inl, Sum.elim_inr, pairBetterSpouseCell_row,
          pairWorseSpouseCell_row] using h
      subst i
      exact (pairBetterSpouseCell_ne_worse μ ν A j.property hij).elim
    · have h' : i.val = j := by
        simpa only [F, Sum.elim_inl, Sum.elim_inr, pairBetterSpouseCell_row,
          pairWorseSpouseCell_row] using h
      subst j
      exact (pairBetterSpouseCell_ne_worse μ ν A i.property hij.symm).elim
    · congr 1
      apply Subtype.ext
      simpa only [F, Sum.elim_inr, pairWorseSpouseCell_row] using h
  · rintro ⟨⟨m, w⟩, hw⟩
    rcases hw with (h : μ m = w) | (h : ν m = w)
    · subst w
      by_cases hm : m ∈ A
      · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm]⟩
      · by_cases heq : μ m = ν m
        · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm, heq]⟩
        · exact ⟨.inr ⟨m, heq⟩, by simp [F, pairWorseSpouseCell, hm]⟩
    · subst w
      by_cases hm : m ∈ A
      · by_cases heq : μ m = ν m
        · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm, heq]⟩
        · exact ⟨.inr ⟨m, heq⟩, by simp [F, pairWorseSpouseCell, hm]⟩
      · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm]⟩
private def pairSpouseCellTranspose (μ ν : Matching n) :
    JointSpouseIndex μ.symm ν.symm ≃ JointSpouseIndex μ ν where
  toFun q := ⟨q.val.swap, by
    rcases q.property with h | h
    · exact Or.inl ((μ.symm_apply_eq).mp h).symm
    · exact Or.inr ((ν.symm_apply_eq).mp h).symm⟩
  invFun q := ⟨q.val.swap, by
    rcases q.property with h | h
    · exact Or.inl ((μ.symm_apply_eq).mpr h.symm)
    · exact Or.inr ((ν.symm_apply_eq).mpr h.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl
private abbrev PairMovedWoman (μ ν : Matching n) := PairMovedMan μ.symm ν.symm
private noncomputable def pairSpouseCellByColumn (μ ν : Matching n) (B : Finset (Fin n)) :
    (Fin n ⊕ PairMovedWoman μ ν) ≃ JointSpouseIndex μ ν :=
  (pairSpouseCellByRow μ.symm ν.symm (Finset.univ \ B)).trans (pairSpouseCellTranspose μ ν)
private abbrev PairOrderedSpouseArrays (n : ℕ) (κ : Type*) := (Fin n → ℝ) × (κ → ℝ)
private noncomputable def pairSplitSpouseScores (μ ν : Matching n) (A B : Finset (Fin n)) :
    JointSpouseScores μ ν ≃ᵐ
      PairOrderedSpouseArrays n (PairMovedMan μ ν) ×
        PairOrderedSpouseArrays n (PairMovedWoman μ ν) :=
  let J := JointSpouseIndex μ ν
  (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ J).trans <|
    ((MeasurableEquiv.arrowCongr' (pairSpouseCellByRow μ ν A).symm (.refl ℝ)).trans
      (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ)).prodCongr
    ((MeasurableEquiv.arrowCongr' (pairSpouseCellByColumn μ ν B).symm (.refl ℝ)).trans
      (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ))
private noncomputable def pairOrderedSpouseLaw (n : ℕ) (κ : Type*) [Fintype κ] :
    Measure (PairOrderedSpouseArrays n κ) :=
  (pairUnitArrayLaw (Fin n)).prod (pairUnitArrayLaw κ)
private instance (n : ℕ) (κ : Type*) [Fintype κ] : IsProbabilityMeasure (pairOrderedSpouseLaw n κ) :=
  inferInstanceAs (IsProbabilityMeasure ((pairUnitArrayLaw (Fin n)).prod (pairUnitArrayLaw κ)))
theorem measurePreserving_pairSplitSpouseScores (μ ν : Matching n) (A B : Finset (Fin n)) :
    MeasurePreserving (pairSplitSpouseScores μ ν A B) (jointSpouseScoreLaw μ ν)
      ((pairOrderedSpouseLaw n (PairMovedMan μ ν)).prod
        (pairOrderedSpouseLaw n (PairMovedWoman μ ν))) := by
  let J := JointSpouseIndex μ ν
  have hM := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ PairMovedMan μ ν ↦ unitScoreLaw)).comp
      (measurePreserving_arrowCongr' (fun _ ↦ unitScoreLaw)
        (fun _ : Fin n ⊕ PairMovedMan μ ν ↦ unitScoreLaw)
        (pairSpouseCellByRow μ ν A).symm (.refl ℝ) (fun _ ↦ MeasurePreserving.id _))
  have hW := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ PairMovedWoman μ ν ↦ unitScoreLaw)).comp
      (measurePreserving_arrowCongr' (fun _ ↦ unitScoreLaw)
        (fun _ : Fin n ⊕ PairMovedWoman μ ν ↦ unitScoreLaw)
        (pairSpouseCellByColumn μ ν B).symm (.refl ℝ) (fun _ ↦ MeasurePreserving.id _))
  exact (hM.prod hW).comp (measurePreserving_arrowProdEquivProdArrow ℝ ℝ J
    (fun _ ↦ unitScoreLaw) (fun _ ↦ unitScoreLaw))
theorem pairSplitSpouseScores_male_first (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (m : Fin n) :
    (pairSplitSpouseScores μ ν A B d).1.1 m =
      if m ∈ A then jointManSpouseScoreLeft d m else jointManSpouseScoreRight d m := by
  change (d (pairBetterSpouseCell μ ν A m)).1 = _
  by_cases h : m ∈ A <;> simp [pairBetterSpouseCell, h, jointManSpouseScoreLeft,
    jointManSpouseScoreRight]
theorem pairSplitSpouseScores_male_second (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (m : PairMovedMan μ ν) :
    (pairSplitSpouseScores μ ν A B d).1.2 m =
      if m.val ∈ A then jointManSpouseScoreRight d m.val else jointManSpouseScoreLeft d m.val := by
  change (d (pairWorseSpouseCell μ ν A m.val)).1 = _
  by_cases h : m.val ∈ A <;> simp [pairWorseSpouseCell, h, jointManSpouseScoreLeft,
    jointManSpouseScoreRight]
theorem pairSplitSpouseScores_female_first (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (w : Fin n) :
    (pairSplitSpouseScores μ ν A B d).2.1 w =
      if w ∈ B then jointWomanSpouseScoreRight d w else jointWomanSpouseScoreLeft d w := by
  change (d (pairSpouseCellTranspose μ ν
    (pairBetterSpouseCell μ.symm ν.symm (Finset.univ \ B) w))).2 = _
  by_cases h : w ∈ B <;> simp [pairBetterSpouseCell, h, pairSpouseCellTranspose,
    jointWomanSpouseScoreLeft, jointWomanSpouseScoreRight]
theorem pairSplitSpouseScores_female_second (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (w : PairMovedWoman μ ν) :
    (pairSplitSpouseScores μ ν A B d).2.2 w =
      if w.val ∈ B then jointWomanSpouseScoreLeft d w.val else jointWomanSpouseScoreRight d w.val := by
  change (d (pairSpouseCellTranspose μ ν
    (pairWorseSpouseCell μ.symm ν.symm (Finset.univ \ B) w.val))).2 = _
  by_cases h : w.val ∈ B <;> simp [pairWorseSpouseCell, h, pairSpouseCellTranspose,
    jointWomanSpouseScoreLeft, jointWomanSpouseScoreRight]
private def pairOrderedArraySet {κ : Type*} (owner : κ → Fin n) :
    Set (PairOrderedSpouseArrays n κ) :=
  {p | ∀ j, p.1 (owner j) ≤ p.2 j}
private theorem measurableSet_pairOrderedArraySet {κ : Type*} [Fintype κ]
    (owner : κ → Fin n) : MeasurableSet (pairOrderedArraySet owner) := by
  unfold pairOrderedArraySet
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun _ ↦ measurableSet_le
    ((measurable_pi_apply _).comp measurable_fst) ((measurable_pi_apply _).comp measurable_snd)
private theorem jointWomanSpouseScoreLeft_eq_right {μ ν : Matching n} (d : JointSpouseScores μ ν)
    {w : Fin n} (hw : μ.symm w = ν.symm w) :
    jointWomanSpouseScoreLeft d w = jointWomanSpouseScoreRight d w := by
  unfold jointWomanSpouseScoreLeft jointWomanSpouseScoreRight
  exact congrArg (fun q : JointSpouseIndex μ ν ↦ (d q).2)
    (Subtype.ext (Prod.ext hw rfl))
private theorem jointSpouseOrientation_iff_pairOrdered {μ ν : Matching n}
    (A B : Finset (Fin n)) (d : JointSpouseScores μ ν) :
    d ∈ jointSpouseOrientation A B ↔
      (pairSplitSpouseScores μ ν A B d).1 ∈
        pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val) ∧
      (pairSplitSpouseScores μ ν A B d).2 ∈
        pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val) := by
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr
  · change (∀ m, _) ↔ ∀ m : PairMovedMan μ ν, _
    simp only [pairSplitSpouseScores_male_first, pairSplitSpouseScores_male_second]
    constructor
    · intro h m
      by_cases hm : m.val ∈ A <;> simpa only [hm, ite_true, ite_false] using h m.val
    · intro h m
      by_cases hne : μ m = ν m
      · simp [jointManSpouseScoreLeft_eq_right d hne]
      · by_cases hm : m ∈ A
        · simpa only [if_pos hm] using h ⟨m, hne⟩
        · simpa only [if_neg hm] using h ⟨m, hne⟩
  · change (∀ w, _) ↔ ∀ w : PairMovedWoman μ ν, _
    simp only [pairSplitSpouseScores_female_first, pairSplitSpouseScores_female_second]
    constructor
    · intro h w
      by_cases hw : w.val ∈ B <;> simpa only [hw, ite_true, ite_false] using h w.val
    · intro h w
      by_cases hne : μ.symm w = ν.symm w
      · simp [jointWomanSpouseScoreLeft_eq_right d hne]
      · by_cases hw : w ∈ B
        · simpa only [if_pos hw] using h ⟨w, hne⟩
        · simpa only [if_neg hw] using h ⟨w, hne⟩
private theorem jointBetterMaleScore_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (m : Fin n) :
    jointBetterMaleScore d m = (pairSplitSpouseScores μ ν A B d).1.1 m := by
  have h := ho.1 m
  rw [pairSplitSpouseScores_male_first, jointBetterMaleScore]
  by_cases hm : m ∈ A
  · simp only [if_pos hm] at h ⊢
    exact min_eq_left h
  · simp only [if_neg hm] at h ⊢
    exact min_eq_right h
private theorem jointMaleScoreGap_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (m : PairMovedMan μ ν) :
    jointMaleScoreGap d m.val =
      (pairSplitSpouseScores μ ν A B d).1.2 m - (pairSplitSpouseScores μ ν A B d).1.1 m.val := by
  have h := ho.1 m.val
  rw [jointMaleScoreGap, jointBetterMaleScore_pairSplit ho, pairSplitSpouseScores_male_second]
  by_cases hm : m.val ∈ A
  · simp only [if_pos hm] at h ⊢
    rw [max_eq_right h]
  · simp only [if_neg hm] at h ⊢
    rw [max_eq_left h]
private theorem jointMaleScoreGap_common {μ ν : Matching n}
    (d : JointSpouseScores μ ν) {m : Fin n} (hm : μ m = ν m) : jointMaleScoreGap d m = 0 := by
  simp [jointMaleScoreGap, jointBetterMaleScore, jointManSpouseScoreLeft_eq_right d hm]
private theorem jointWomanSpouseScores_inverse_congr {μ ν : Matching n}
    (A B : Finset (Fin n)) (p q : PairOrderedSpouseArrays n (PairMovedMan μ ν))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) (w : Fin n) :
    let d := (pairSplitSpouseScores μ ν A B).symm (p, y)
    let d' := (pairSplitSpouseScores μ ν A B).symm (q, y)
    jointWomanSpouseScoreLeft d w = jointWomanSpouseScoreLeft d' w ∧
      jointWomanSpouseScoreRight d w = jointWomanSpouseScoreRight d' w := by
  let e := pairSplitSpouseScores μ ν A B
  let d := e.symm (p, y)
  let d' := e.symm (q, y)
  have h₁ := pairSplitSpouseScores_female_first μ ν A B d w
  have h₁' := pairSplitSpouseScores_female_first μ ν A B d' w
  change (e (e.symm (p, y))).2.1 w = _ at h₁
  change (e (e.symm (q, y))).2.1 w = _ at h₁'
  rw [MeasurableEquiv.apply_symm_apply] at h₁ h₁'
  by_cases hw : μ.symm w = ν.symm w
  · rw [jointWomanSpouseScoreLeft_eq_right d hw] at h₁
    rw [jointWomanSpouseScoreLeft_eq_right d' hw] at h₁'
    simp only [ite_self] at h₁ h₁'
    exact ⟨(jointWomanSpouseScoreLeft_eq_right d hw).trans
      (h₁.symm.trans (h₁'.trans (jointWomanSpouseScoreLeft_eq_right d' hw).symm)),
      h₁.symm.trans h₁'⟩
  · let j : PairMovedWoman μ ν := ⟨w, hw⟩
    have h₂ := pairSplitSpouseScores_female_second μ ν A B d j
    have h₂' := pairSplitSpouseScores_female_second μ ν A B d' j
    change (e (e.symm (p, y))).2.2 j = _ at h₂
    change (e (e.symm (q, y))).2.2 j = _ at h₂'
    rw [MeasurableEquiv.apply_symm_apply] at h₂ h₂'
    by_cases hB : w ∈ B
    · simp only [j, if_pos hB] at h₁ h₁' h₂ h₂'
      exact ⟨h₂.symm.trans h₂', h₁.symm.trans h₁'⟩
    · simp only [j, if_neg hB] at h₁ h₁' h₂ h₂'
      exact ⟨h₁.symm.trans h₁', h₂.symm.trans h₂'⟩
private theorem sum_jointMaleScoreGap {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (f : Fin n → ℝ) :
    (∑ m, jointMaleScoreGap d m * f m) =
      ∑ m : PairMovedMan μ ν, jointMaleScoreGap d m.val * f m.val := by
  have h (m : Fin n) : jointMaleScoreGap d m * f m =
      if μ m ≠ ν m then jointMaleScoreGap d m * f m else 0 := by
    by_cases hm : μ m = ν m
    · simp [hm, jointMaleScoreGap_common d hm]
    · simp [hm]
  calc
    _ = ∑ m, if μ m ≠ ν m then jointMaleScoreGap d m * f m else 0 :=
      Finset.sum_congr rfl fun m _ ↦ h m
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) (fun m ↦ jointMaleScoreGap d m * f m)
private theorem pairOrderedSpouseLaw_inner_le {μ ν : Matching n}
    (A B : Finset (Fin n)) (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν))
    (hy : y ∈ pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val)) :
    let e := pairSplitSpouseScores μ ν A B
    let d₀ := e.symm ((fun _ ↦ 0, fun _ ↦ 0), y)
    let a m := pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d₀)
    let b (m : PairMovedMan μ ν) :=
      pairUnmarkedRowSum μ ν m.val (jointExtraFemaleThreshold d₀ A m.val)
    (∫⁻ p in pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val),
      orientedPairRowExp (e.symm (p, y)) A ∂pairOrderedSpouseLaw n (PairMovedMan μ ν)) ≤
      ENNReal.ofReal ((∏ m, pairLaplace (a m)) * ∏ m, pairLaplace (b m)) := by
  dsimp only
  let e := pairSplitSpouseScores μ ν A B
  let d₀ := e.symm ((fun _ ↦ 0, fun _ ↦ 0), y)
  let a m := pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d₀)
  let b (m : PairMovedMan μ ν) :=
    pairUnmarkedRowSum μ ν m.val (jointExtraFemaleThreshold d₀ A m.val)
  let f (p : PairOrderedSpouseArrays n (PairMovedMan μ ν)) :=
    ENNReal.ofReal (Real.exp (-(∑ m, p.1 m * a m) - ∑ m, p.2 m * b m))
  have hf : Measurable f := by
    unfold f
    apply ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.sub
      (Measurable.neg ?_) ?_))
    · exact Finset.measurable_sum _ fun _ _ ↦ ((measurable_pi_apply _).comp measurable_fst).mul_const _
    · exact Finset.measurable_sum _ fun _ _ ↦ ((measurable_pi_apply _).comp measurable_snd).mul_const _
  have hchange : (∫⁻ p in pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val),
      orientedPairRowExp (e.symm (p, y)) A ∂pairOrderedSpouseLaw n (PairMovedMan μ ν)) =
      ∫⁻ p in pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val),
        f (p.1, fun m ↦ p.2 m - p.1 m.val) ∂pairOrderedSpouseLaw n (PairMovedMan μ ν) := by
    apply setLIntegral_congr_fun (measurableSet_pairOrderedArraySet _)
    intro p hp
    let d := e.symm (p, y)
    have ho : d ∈ jointSpouseOrientation A B := (jointSpouseOrientation_iff_pairOrdered A B d).mpr
      (by simpa only [d, e, MeasurableEquiv.apply_symm_apply] using And.intro hp hy)
    have hW : jointWorseFemaleScore d = jointWorseFemaleScore d₀ := by
      funext w
      have h := jointWomanSpouseScores_inverse_congr A B p (fun _ ↦ 0, fun _ ↦ 0) y w
      exact congrArg₂ max h.1 h.2
    have hE (m : Fin n) : jointExtraFemaleThreshold d A m = jointExtraFemaleThreshold d₀ A m := by
      funext w
      have h := jointWomanSpouseScores_inverse_congr A B p (fun _ ↦ 0, fun _ ↦ 0) y w
      unfold jointExtraFemaleThreshold
      split
      · exact h.2
      · exact h.1
    change orientedPairRowExp d A = _
    unfold orientedPairRowExp f
    rw [Finset.sum_add_distrib, sum_jointMaleScoreGap]
    simp only [jointBetterMaleScore_pairSplit ho, jointMaleScoreGap_pairSplit ho,
      hW, hE, d, e, MeasurableEquiv.apply_symm_apply, a, b, neg_add_rev, sub_eq_add_neg]
    exact congrArg (fun s ↦ ENNReal.ofReal (Real.exp s)) (add_comm _ _)
  rw [hchange]
  exact (pairUnitArrayLaw_lintegral_orderedGap_le (fun m : PairMovedMan μ ν ↦ m.val) hf).trans_eq
    (pairUnitArrayLaw_lintegral_exp_sums a b)
private def pairOrientedMovedMen (μ ν : Matching n) (A : Finset (Fin n)) : Finset (Fin n) :=
  A.filter fun m ↦ μ m ≠ ν m
private theorem pairProd_moved_male_gap {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (A : Finset (Fin n)) :
    (∏ m : PairMovedMan μ ν,
      pairLaplace (pairUnmarkedRowSum μ ν m.val (jointExtraFemaleThreshold d A m.val))) =
      (∏ m ∈ pairOrientedMovedMen μ ν A,
        pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreRight d))) *
      (∏ m ∈ pairOrientedMovedMen μ ν (Finset.univ \ A),
        pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreLeft d))) := by
  let F m := pairLaplace (pairUnmarkedRowSum μ ν m (jointExtraFemaleThreshold d A m))
  have h₀ : (∏ m : PairMovedMan μ ν, F m.val) =
      ∏ m ∈ Finset.univ.filter (fun m ↦ μ m ≠ ν m), F m :=
    (Finset.prod_subtype _ (by simp) F).symm
  rw [h₀, ← Finset.prod_filter_mul_prod_filter_not _ (fun m ↦ m ∈ A) F]
  have h₁ : (Finset.univ.filter (fun m ↦ μ m ≠ ν m)).filter (fun m ↦ m ∈ A) =
      pairOrientedMovedMen μ ν A := by
    ext m
    simp [pairOrientedMovedMen, and_comm]
  have h₂ : (Finset.univ.filter (fun m ↦ μ m ≠ ν m)).filter (fun m ↦ m ∉ A) =
      pairOrientedMovedMen μ ν (Finset.univ \ A) := by
    ext m
    simp [pairOrientedMovedMen, and_comm]
  rw [h₁, h₂]
  congr 1
  · apply Finset.prod_congr rfl
    intro m hm
    have h := (Finset.mem_filter.mp hm).1
    have he : jointExtraFemaleThreshold d A m = jointWomanSpouseScoreRight d := by
      funext w
      simp only [jointExtraFemaleThreshold, if_pos h]
    simp only [F, he]
  · apply Finset.prod_congr rfl
    intro m hm
    have h := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hm).1).2
    have he : jointExtraFemaleThreshold d A m = jointWomanSpouseScoreLeft d := by
      funext w
      simp only [jointExtraFemaleThreshold, if_neg h]
    simp only [F, he]
private theorem pairSplitSpouseScores_thresholdsUnit {μ ν : Matching n}
    (A B : Finset (Fin n)) (d : JointSpouseScores μ ν)
    (hm₀ : ∀ m, (pairSplitSpouseScores μ ν A B d).1.1 m ∈ Icc 0 1)
    (hm₁ : ∀ m, (pairSplitSpouseScores μ ν A B d).1.2 m ∈ Icc 0 1)
    (hw₀ : ∀ w, (pairSplitSpouseScores μ ν A B d).2.1 w ∈ Icc 0 1)
    (hw₁ : ∀ w, (pairSplitSpouseScores μ ν A B d).2.2 w ∈ Icc 0 1) :
    JointSpouseThresholdsUnit d := by
  constructor
  · intro m
    have h₀ := hm₀ m
    rw [pairSplitSpouseScores_male_first] at h₀
    by_cases he : μ m = ν m
    · rw [jointManSpouseScoreLeft_eq_right d he, ite_self] at h₀
      simpa only [jointManSpouseScoreLeft_eq_right d he] using And.intro h₀ h₀
    · have h₁ := hm₁ ⟨m, he⟩
      rw [pairSplitSpouseScores_male_second] at h₁
      by_cases h : m ∈ A
      · exact ⟨by simpa only [if_pos h] using h₀, by simpa only [if_pos h] using h₁⟩
      · exact ⟨by simpa only [if_neg h] using h₁, by simpa only [if_neg h] using h₀⟩
  · intro w
    have h₀ := hw₀ w
    rw [pairSplitSpouseScores_female_first] at h₀
    by_cases he : μ.symm w = ν.symm w
    · rw [jointWomanSpouseScoreLeft_eq_right d he, ite_self] at h₀
      simpa only [jointWomanSpouseScoreLeft_eq_right d he] using And.intro h₀ h₀
    · have h₁ := hw₁ ⟨w, he⟩
      rw [pairSplitSpouseScores_female_second] at h₁
      by_cases h : w ∈ B
      · exact ⟨by simpa only [if_pos h] using h₁, by simpa only [if_pos h] using h₀⟩
      · exact ⟨by simpa only [if_neg h] using h₀, by simpa only [if_neg h] using h₁⟩
private theorem ae_pairOrderedSpouseLaw_unit (n : ℕ) (κ : Type*) [Fintype κ] :
    ∀ᵐ p ∂pairOrderedSpouseLaw n κ,
      (∀ i, p.1 i ∈ Icc 0 1) ∧ ∀ j, p.2 j ∈ Icc 0 1 := by
  rw [pairOrderedSpouseLaw, pairUnitArrayLaw_eq_restrict, pairUnitArrayLaw_eq_restrict,
    Measure.prod_restrict]
  exact (ae_restrict_mem ((MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).prod
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc))).mono fun _ h ↦
      ⟨Set.mem_univ_pi.mp h.1, Set.mem_univ_pi.mp h.2⟩
private theorem measurable_orientedPairRowExp (μ ν : Matching n) (A : Finset (Fin n)) :
    Measurable (fun d : JointSpouseScores μ ν ↦ orientedPairRowExp d A) := by
  have hx₁ := measurable_jointManSpouseScoreLeft μ ν
  have hx₂ := measurable_jointManSpouseScoreRight μ ν
  have hy₁ := measurable_jointWomanSpouseScoreLeft μ ν
  have hy₂ := measurable_jointWomanSpouseScoreRight μ ν
  apply ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.neg ?_))
  refine Finset.measurable_sum _ fun m _ ↦ Measurable.add (Measurable.mul
    ((hx₁ m).min (hx₂ m)) ?_) (Measurable.mul (((hx₁ m).max (hx₂ m)).sub
    ((hx₁ m).min (hx₂ m))) ?_)
  · exact Finset.measurable_sum _ fun w _ ↦ (hy₁ w).max (hy₂ w)
  · refine Finset.measurable_sum _ fun w _ ↦ ?_
    by_cases h : m ∈ A
    · simpa only [jointExtraFemaleThreshold, if_pos h] using hy₂ w
    · simpa only [jointExtraFemaleThreshold, if_neg h] using hy₁ w
private theorem jointFemaleAggregate_inverse_congr {μ ν : Matching n}
    (A B : Finset (Fin n)) (p q : PairOrderedSpouseArrays n (PairMovedMan μ ν))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) :
    jointFemaleAggregate ((pairSplitSpouseScores μ ν A B).symm (p, y)) B =
      jointFemaleAggregate ((pairSplitSpouseScores μ ν A B).symm (q, y)) B := by
  simp only [jointFemaleAggregate, jointBetterFemaleScore, jointFemaleScoreGap,
    jointWorseFemaleScore, (jointWomanSpouseScores_inverse_congr A B p q y _).1,
    (jointWomanSpouseScores_inverse_congr A B p q y _).2]
private noncomputable def pairFemaleAggregateFromOrdered {μ ν : Matching n} (A B : Finset (Fin n))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) : ℝ × ℝ × ℝ :=
  jointFemaleAggregate ((pairSplitSpouseScores μ ν A B).symm ((fun _ ↦ 0, fun _ ↦ 0), y)) B
theorem continuousScoreLaw_lintegral_twoStableOrientation_le_femaleAggregate (μ ν : Matching n)
    (A B : Finset (Fin n)) {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    let u := (pairOrientedMovedMen μ ν A).card
    let v := (pairOrientedMovedMen μ ν (Finset.univ \ A)).card
    (∫⁻ x in twoStableOrientationEvent μ ν A B,
      g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n) ≤
      ∫⁻ y in pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val),
        g (pairFemaleAggregateFromOrdered A B y) * ENNReal.ofReal
          (Real.exp 72 * pairAggregateLaplace n u v (pairFemaleAggregateFromOrdered A B y))
        ∂pairOrderedSpouseLaw n (PairMovedWoman μ ν) := by
  dsimp only
  let e := pairSplitSpouseScores μ ν A B
  let M := PairMovedMan μ ν
  let W := PairMovedWoman μ ν
  let p₀ : PairOrderedSpouseArrays n M := (fun _ ↦ 0, fun _ ↦ 0)
  let S := pairOrderedArraySet (fun m : M ↦ m.val)
  let T := pairOrderedArraySet (fun w : W ↦ w.val)
  let H (z : PairOrderedSpouseArrays n M × PairOrderedSpouseArrays n W) :=
    g (jointFemaleAggregate (e.symm z) B) * orientedPairRowExp (e.symm z) A
  have hH : Measurable H := ((hg.comp (measurable_jointFemaleAggregate μ ν B)).mul
    (measurable_orientedPairRowExp μ ν A)).comp e.symm.measurable
  have hST : e ⁻¹' (S ×ˢ T) = jointSpouseOrientation A B := by
    ext d
    exact (jointSpouseOrientation_iff_pairOrdered A B d).symm
  have hS : MeasurableSet S := measurableSet_pairOrderedArraySet _
  have hT : MeasurableSet T := measurableSet_pairOrderedArraySet _
  refine (continuousScoreLaw_lintegral_twoStableOrientation_le_rowExp μ ν A B hg).trans ?_
  have htransport := (measurePreserving_pairSplitSpouseScores μ ν A B).setLIntegral_comp_preimage
    (hS.prod hT) hH
  rw [hST] at htransport
  simp only [H, e, MeasurableEquiv.symm_apply_apply] at htransport
  rw [htransport]
  change (∫⁻ z in S ×ˢ T, H z
    ∂((pairOrderedSpouseLaw n M).prod (pairOrderedSpouseLaw n W))) ≤ _
  rw [← Measure.prod_restrict, lintegral_prod_symm' H hH]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hT,
    ae_restrict_of_ae (ae_pairOrderedSpouseLaw_unit n W)] with y hy hyu
  let d₀ := e.symm (p₀, y)
  have hunit : JointSpouseThresholdsUnit d₀ := by
    apply pairSplitSpouseScores_thresholdsUnit A B d₀
    · intro m
      simp [d₀, e, p₀]
    · intro m
      simp [d₀, e, p₀]
    · simpa only [d₀, e, MeasurableEquiv.apply_symm_apply] using hyu.1
    · simpa only [d₀, e, MeasurableEquiv.apply_symm_apply] using hyu.2
  have ho₀ : d₀ ∈ jointSpouseOrientation A B := by
    apply (jointSpouseOrientation_iff_pairOrdered A B d₀).mpr
    refine ⟨?_, by simpa only [d₀, e, MeasurableEquiv.apply_symm_apply] using hy⟩
    simp [d₀, e, p₀, pairOrderedArraySet]
  have hcongr (p : PairOrderedSpouseArrays n M) :
      H (p, y) = g (jointFemaleAggregate d₀ B) * orientedPairRowExp (e.symm (p, y)) A := by
    unfold H
    rw [jointFemaleAggregate_inverse_congr A B p p₀ y]
  simp_rw [hcongr]
  have hmeas : Measurable (fun p : PairOrderedSpouseArrays n M ↦
      orientedPairRowExp (e.symm (p, y)) A) :=
    (measurable_orientedPairRowExp μ ν A).comp
      (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  rw [lintegral_const_mul _ hmeas]
  apply mul_le_mul_right
  refine (pairOrderedSpouseLaw_inner_le A B y hy).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [pairProd_moved_male_gap d₀ A, ← mul_assoc]
  exact pairLaplace_rows_le_aggregate hunit ho₀ _ _
private def pairFemaleAggregateFromGaps {μ ν : Matching n} (B : Finset (Fin n))
    (z : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) : ℝ × ℝ × ℝ :=
  (∑ w, z.1 w,
    ∑ w : PairMovedWoman μ ν with w.val ∈ B, z.2 w,
    ∑ w : PairMovedWoman μ ν with w.val ∉ B, z.2 w)
theorem measurable_pairFemaleAggregateFromGaps (μ ν : Matching n) (B : Finset (Fin n)) :
    Measurable (pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B) := by
  exact (Finset.measurable_sum _ fun w _ ↦ (measurable_pi_apply w).comp measurable_fst).prodMk
    ((Finset.measurable_sum _ fun w _ ↦ (measurable_pi_apply w).comp measurable_snd).prodMk
      (Finset.measurable_sum _ fun w _ ↦ (measurable_pi_apply w).comp measurable_snd))
private theorem jointBetterFemaleScore_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (w : Fin n) :
    jointBetterFemaleScore d w = (pairSplitSpouseScores μ ν A B d).2.1 w := by
  have h := ho.2 w
  rw [pairSplitSpouseScores_female_first, jointBetterFemaleScore]
  by_cases hw : w ∈ B
  · simp only [if_pos hw] at h ⊢
    exact min_eq_right h
  · simp only [if_neg hw] at h ⊢
    exact min_eq_left h
private theorem jointFemaleScoreGap_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (w : PairMovedWoman μ ν) :
    jointFemaleScoreGap d w.val =
      (pairSplitSpouseScores μ ν A B d).2.2 w - (pairSplitSpouseScores μ ν A B d).2.1 w.val := by
  have h := ho.2 w.val
  rw [jointFemaleScoreGap, jointBetterFemaleScore_pairSplit ho, pairSplitSpouseScores_female_second,
    jointWorseFemaleScore]
  by_cases hw : w.val ∈ B
  · simp only [if_pos hw] at h ⊢
    rw [max_eq_left h]
  · simp only [if_neg hw] at h ⊢
    rw [max_eq_right h]
private theorem jointFemaleScoreGap_common {μ ν : Matching n}
    (d : JointSpouseScores μ ν) {w : Fin n} (hw : μ.symm w = ν.symm w) :
    jointFemaleScoreGap d w = 0 := by
  simp [jointFemaleScoreGap, jointBetterFemaleScore, jointWorseFemaleScore,
    jointWomanSpouseScoreLeft_eq_right d hw]
private theorem jointFemaleScoreGap_sum_filter {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (I : Finset (Fin n)) :
    (∑ w ∈ I, jointFemaleScoreGap d w) =
      ∑ w : PairMovedWoman μ ν with w.val ∈ I, jointFemaleScoreGap d w.val := by
  let f w := if w ∈ I then jointFemaleScoreGap d w else 0
  have h (w : Fin n) : f w = if μ.symm w ≠ ν.symm w then f w else 0 := by
    by_cases hw : μ.symm w = ν.symm w
    · simp [f, hw, jointFemaleScoreGap_common d hw]
    · simp [hw]
  have hI : Finset.univ.filter (fun w : Fin n ↦ w ∈ I) = I := by
    ext w
    simp
  calc
    _ = ∑ w, f w := by
      conv_lhs => rw [← hI, Finset.sum_filter]
    _ = ∑ w, if μ.symm w ≠ ν.symm w then f w else 0 :=
      Finset.sum_congr rfl fun w _ ↦ h w
    _ = ∑ w : PairMovedWoman μ ν, f w.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) f
    _ = _ := by rw [Finset.sum_filter]
private theorem pairFemaleAggregateFromOrdered_eq {μ ν : Matching n} (A B : Finset (Fin n))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν))
    (hy : y ∈ pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val)) :
    pairFemaleAggregateFromOrdered A B y =
      pairFemaleAggregateFromGaps B (y.1, fun w ↦ y.2 w - y.1 w.val) := by
  let e := pairSplitSpouseScores μ ν A B
  let d := e.symm ((fun _ ↦ 0, fun _ ↦ 0), y)
  have ho : d ∈ jointSpouseOrientation A B := by
    apply (jointSpouseOrientation_iff_pairOrdered A B d).mpr
    refine ⟨?_, by simpa only [d, e, MeasurableEquiv.apply_symm_apply] using hy⟩
    simp [d, e, pairOrderedArraySet]
  unfold pairFemaleAggregateFromOrdered pairFemaleAggregateFromGaps jointFemaleAggregate
  change (∑ w, jointBetterFemaleScore d w, ∑ w ∈ B, jointFemaleScoreGap d w,
    ∑ w ∈ Finset.univ \ B, jointFemaleScoreGap d w) = _
  rw [jointFemaleScoreGap_sum_filter d B, jointFemaleScoreGap_sum_filter d (Finset.univ \ B)]
  simp only [jointBetterFemaleScore_pairSplit ho, jointFemaleScoreGap_pairSplit ho, d, e,
    MeasurableEquiv.apply_symm_apply, Finset.mem_sdiff, Finset.mem_univ, true_and]
private theorem measurable_pairAggregateLaplace (n u v : ℕ) :
    Measurable (pairAggregateLaplace n u v) := by
  unfold pairAggregateLaplace
  let p : ℝ × ℝ × ℝ → ℝ := Prod.fst
  let q : ℝ × ℝ × ℝ → ℝ := fun x ↦ x.2.1
  let r : ℝ × ℝ × ℝ → ℝ := fun x ↦ x.2.2
  have hp : Measurable p := measurable_fst
  have hq : Measurable q := measurable_fst.comp measurable_snd
  have hr : Measurable r := measurable_snd.comp measurable_snd
  exact (((measurable_pairLaplace.comp ((hp.add hq).add hr)).pow_const _).mul
    ((measurable_pairLaplace.comp (hp.add hr)).pow_const _)).mul
    ((measurable_pairLaplace.comp (hp.add hq)).pow_const _)
theorem continuousScoreLaw_lintegral_twoStableOrientation_le_gapAggregate (μ ν : Matching n)
    (A B : Finset (Fin n)) {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    let u := (pairOrientedMovedMen μ ν A).card
    let v := (pairOrientedMovedMen μ ν (Finset.univ \ A)).card
    (∫⁻ x in twoStableOrientationEvent μ ν A B,
      g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n) ≤
      ∫⁻ z, g (pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B z) * ENNReal.ofReal
          (Real.exp 72 * pairAggregateLaplace n u v (pairFemaleAggregateFromGaps B z))
        ∂pairOrderedSpouseLaw n (PairMovedWoman μ ν) := by
  dsimp only
  let u := (pairOrientedMovedMen μ ν A).card
  let v := (pairOrientedMovedMen μ ν (Finset.univ \ A)).card
  let W := PairMovedWoman μ ν
  let T := pairOrderedArraySet (fun w : W ↦ w.val)
  let F (z : PairOrderedSpouseArrays n W) :=
    g (pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B z) * ENNReal.ofReal
      (Real.exp 72 * pairAggregateLaplace n u v (pairFemaleAggregateFromGaps B z))
  have hF : Measurable F :=
    (hg.mul (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (measurable_pairAggregateLaplace n u v)))).comp
        (measurable_pairFemaleAggregateFromGaps μ ν B)
  refine (continuousScoreLaw_lintegral_twoStableOrientation_le_femaleAggregate μ ν A B hg).trans ?_
  calc
    _ = ∫⁻ y in T, F (y.1, fun w ↦ y.2 w - y.1 w.val) ∂pairOrderedSpouseLaw n W := by
      apply setLIntegral_congr_fun (measurableSet_pairOrderedArraySet _)
      intro y hy
      simp only [F, pairFemaleAggregateFromOrdered_eq A B y hy, u, v]
      rfl
    _ ≤ _ := pairUnitArrayLaw_lintegral_orderedGap_le (fun w : W ↦ w.val) hF
private noncomputable def pairUniformSumLaw (ι : Type*) [Fintype ι] : Measure ℝ :=
  (pairUnitArrayLaw ι).map (fun z ↦ ∑ i, z i)
private instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (pairUniformSumLaw ι) :=
  Measure.isProbabilityMeasure_map
    (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i).aemeasurable
theorem pairUniformSumLaw_le_spouseRadialLaw (ι : Type*) [Fintype ι]
    (hι : 0 < Fintype.card ι) :
    pairUniformSumLaw ι ≤ spouseRadialLaw (Fintype.card ι) := by
  let k := Fintype.card ι
  let e := Fintype.equivFin ι
  let T := MeasurableEquiv.arrowCongr' e (.refl ℝ)
  have hT : MeasurePreserving T (pairUnitArrayLaw ι) (pairUnitArrayLaw (Fin k)) :=
    measurePreserving_arrowCongr' _ _ _ _ (fun _ ↦ MeasurePreserving.id unitScoreLaw)
  have hs : Measurable (fun x : Fin k → ℝ ↦ ∑ i, x i) :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  have hcomp : (fun x : Fin k → ℝ ↦ ∑ i, x i) ∘ T = (fun z : ι → ℝ ↦ ∑ i, z i) := by
    funext z
    change (∑ i : Fin k, z (e.symm i)) = ∑ i : ι, z i
    exact Equiv.sum_comp e.symm z
  have heq : pairUniformSumLaw ι = pairUniformSumLaw (Fin k) := by
    unfold pairUniformSumLaw
    rw [← hcomp, ← Measure.map_map hs hT.measurable, hT.map_eq]
  have hmap :
      ((volume : Measure (Fin k → ℝ)).restrict {z | ∀ i, 0 ≤ z i}).map
        (fun z ↦ ∑ i, z i) = spouseRadialLaw k := by
    ext s hS
    let f := s.indicator (1 : ℝ → ℝ≥0∞)
    have hf : Measurable f := measurable_const.indicator hS
    calc
      _ = ∫⁻ t, f t ∂((volume : Measure (Fin k → ℝ)).restrict {z | ∀ i, 0 ≤ z i}).map
          (fun z ↦ ∑ i, z i) := (lintegral_indicator_one hS).symm
      _ = ∫⁻ z, f (∑ i, z i) ∂((volume : Measure (Fin k → ℝ)).restrict {z | ∀ i, 0 ≤ z i}) :=
        lintegral_map hf hs
      _ = ∫⁻ t, ∫⁻ w, f (∑ i, t * w i) ∂spouseAngularLaw k ∂spouseRadialLaw k :=
        lintegral_spouseRadialAngular hι (hf.comp hs)
      _ = ∫⁻ t, f t ∂spouseRadialLaw k := by
        apply lintegral_congr
        intro t
        calc
          _ = ∫⁻ _w : Fin k → ℝ, f t ∂spouseAngularLaw k := by
            apply lintegral_congr_ae
            filter_upwards [ae_spouseAngularLaw hι] with w hw
            rw [← Finset.mul_sum, hw.2, mul_one]
          _ = _ := by rw [lintegral_const, measure_univ, mul_one]
      _ = _ := lintegral_indicator_one hS
  rw [heq, ← hmap, pairUniformSumLaw, pairUnitArrayLaw_eq_restrict]
  have hsub : pairUnitCube (Fin k) ⊆ {z : Fin k → ℝ | ∀ i, 0 ≤ z i} :=
    fun z hz ↦ show ∀ i, 0 ≤ z i from fun i ↦ (Set.mem_univ_pi.mp hz i).1
  exact Measure.map_mono (Measure.restrict_mono hsub le_rfl) hs
private abbrev PairFemaleGapClass (μ ν : Matching n) (B : Finset (Fin n)) :=
  {w : PairMovedWoman μ ν // w.val ∈ B}
private abbrev PairFemaleOtherGapClass (μ ν : Matching n) (B : Finset (Fin n)) :=
  {w : PairMovedWoman μ ν // w.val ∉ B}
theorem map_pairFemaleAggregateFromGaps (μ ν : Matching n) (B : Finset (Fin n)) :
    (pairOrderedSpouseLaw n (PairMovedWoman μ ν)).map (pairFemaleAggregateFromGaps B) =
      (pairUniformSumLaw (Fin n)).prod
        ((pairUniformSumLaw (PairFemaleGapClass μ ν B)).prod
          (pairUniformSumLaw (PairFemaleOtherGapClass μ ν B))) := by
  let W := PairMovedWoman μ ν
  let V := PairFemaleGapClass μ ν B
  let U := PairFemaleOtherGapClass μ ν B
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : W ↦ ℝ) (fun w ↦ w.val ∈ B)
  let E := (MeasurableEquiv.refl (Fin n → ℝ)).prodCongr e
  have hE : MeasurePreserving E (pairOrderedSpouseLaw n W)
      ((pairUnitArrayLaw (Fin n)).prod ((pairUnitArrayLaw V).prod (pairUnitArrayLaw U))) :=
    (MeasurePreserving.id _).prod (measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScoreLaw) _)
  let s₀ (x : Fin n → ℝ) := ∑ i, x i
  let s₁ (x : V → ℝ) := ∑ i, x i
  let s₂ (x : U → ℝ) := ∑ i, x i
  have hs₀ : Measurable s₀ := Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  have hs₁ : Measurable s₁ := Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  have hs₂ : Measurable s₂ := Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  let F := Prod.map s₀ (Prod.map s₁ s₂)
  have hF : Measurable F := hs₀.prodMap (hs₁.prodMap hs₂)
  have heq : F ∘ E = pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B := by
    funext p
    unfold pairFemaleAggregateFromGaps
    change (∑ w, p.1 w, ∑ w : V, p.2 w.val, ∑ w : U, p.2 w.val) = _
    congr 1
    exact Prod.ext
      ((Finset.sum_subtype (p := fun w : W ↦ w.val ∈ B)
        (Finset.univ.filter (fun w : W ↦ w.val ∈ B))
        (fun _ ↦ by simp) p.2).symm)
      ((Finset.sum_subtype (p := fun w : W ↦ w.val ∉ B)
        (Finset.univ.filter (fun w : W ↦ w.val ∉ B))
        (fun _ ↦ by simp) p.2).symm)
  rw [← heq, ← Measure.map_map hF hE.measurable, hE.map_eq]
  unfold F
  rw [← Measure.map_prod_map _ _ hs₀ (hs₁.prodMap hs₂), ← Measure.map_prod_map _ _ hs₁ hs₂]
  rfl
private def pairAggregateCutoff (n : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {s | s.1 + s.2.1 + s.2.2 ≤ (n : ℝ)}
private theorem measurableSet_pairAggregateCutoff (n : ℕ) :
    MeasurableSet (pairAggregateCutoff n) := by
  apply measurableSet_le _ measurable_const
  exact (measurable_fst.add (measurable_fst.comp measurable_snd)).add
    (measurable_snd.comp measurable_snd)
theorem jointFemaleAggregate_mem_cutoff {μ ν : Matching n} {d : JointSpouseScores μ ν}
    (hd : JointSpouseThresholdsUnit d) (B : Finset (Fin n)) :
    jointFemaleAggregate d B ∈ pairAggregateCutoff n := by
  change (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.1 +
    (jointFemaleAggregate d B).2.2 ≤ (n : ℝ)
  rw [← jointFemale_sum_worse d B]
  calc
    _ ≤ ∑ _w : Fin n, (1 : ℝ) := Finset.sum_le_sum fun w _ ↦ max_le (hd.2 w).1.2 (hd.2 w).2.2
    _ = _ := by simp
private noncomputable def pairRadialUpperKernel (n u v : ℕ) : ℝ × ℝ × ℝ → ℝ≥0∞ :=
  (pairAggregateCutoff n).indicator (fun s ↦ ENNReal.ofReal (pairAggregateLaplace n u v s))
theorem measurable_pairRadialUpperKernel (n u v : ℕ) : Measurable (pairRadialUpperKernel n u v) :=
  (ENNReal.measurable_ofReal.comp (measurable_pairAggregateLaplace n u v)).indicator
    (measurableSet_pairAggregateCutoff n)
theorem continuousScoreLaw_twoStableOrientation_le_radial (μ ν : Matching n)
    (A B : Finset (Fin n)) {u v : ℕ}
    (hu : (pairOrientedMovedMen μ ν A).card = u)
    (hv : (pairOrientedMovedMen μ ν (Finset.univ \ A)).card = v)
    (hB : Fintype.card (PairFemaleGapClass μ ν B) = u)
    (hBc : Fintype.card (PairFemaleOtherGapClass μ ν B) = v)
    (hn : 0 < n) (hu₀ : 0 < u) (hv₀ : 0 < v) :
    continuousScoreLaw n (twoStableOrientationEvent μ ν A B) ≤ ENNReal.ofReal (Real.exp 72) *
      ∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, pairRadialUpperKernel n u v (ξ, η, ζ)
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n := by
  let g := (pairAggregateCutoff n).indicator (1 : ℝ × ℝ × ℝ → ℝ≥0∞)
  have hg : Measurable g := measurable_const.indicator (measurableSet_pairAggregateCutoff n)
  let E := twoStableOrientationEvent μ ν A B
  let G := pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B
  let F := pairRadialUpperKernel n u v
  have hF : Measurable F := measurable_pairRadialUpperKernel n u v
  have hpres : MeasurePreserving (fun x ↦ (splitTwoMatchingScores μ ν x).1)
      (continuousScoreLaw n) (jointSpouseScoreLaw μ ν) :=
    measurePreserving_fst.comp (measurePreserving_splitTwoMatchingScores μ ν)
  have hL : continuousScoreLaw n E =
      ∫⁻ x in E, g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n := by
    rw [← setLIntegral_one]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (hpres.quasiMeasurePreserving.ae
      (ae_jointSpouseThresholdsUnit μ ν))] with x hx
    dsimp only [g]
    rw [Set.indicator_of_mem (jointFemaleAggregate_mem_cutoff hx B)]
    rfl
  have hmul (s : ℝ × ℝ × ℝ) :
      g s * ENNReal.ofReal (Real.exp 72 * pairAggregateLaplace n u v s) =
      ENNReal.ofReal (Real.exp 72) * F s := by
    by_cases hs : s ∈ pairAggregateCutoff n
    · simp only [g, F, pairRadialUpperKernel, Set.indicator_of_mem hs, Pi.one_apply,
        one_mul, ENNReal.ofReal_mul (Real.exp_pos _).le]
    · simp only [g, F, pairRadialUpperKernel, Set.indicator_of_notMem hs, zero_mul, mul_zero]
  rw [hL]
  have h := continuousScoreLaw_lintegral_twoStableOrientation_le_gapAggregate μ ν A B hg
  dsimp only at h
  rw [hu, hv] at h
  refine h.trans ?_
  simp_rw [hmul]
  have hmeas : Measurable (fun z ↦ F (G z)) :=
    hF.comp (measurable_pairFemaleAggregateFromGaps μ ν B)
  rw [lintegral_const_mul _ hmeas]
  apply mul_le_mul_right
  change (∫⁻ z, F (G z) ∂pairOrderedSpouseLaw n (PairMovedWoman μ ν)) ≤ _
  rw [← lintegral_map hF (measurable_pairFemaleAggregateFromGaps μ ν B),
    map_pairFemaleAggregateFromGaps]
  rw [lintegral_prod _ hF.aemeasurable]
  have h₀ := pairUniformSumLaw_le_spouseRadialLaw (Fin n) (by simpa using hn)
  have h₁ := pairUniformSumLaw_le_spouseRadialLaw (PairFemaleGapClass μ ν B) (hB ▸ hu₀)
  have h₂ := pairUniformSumLaw_le_spouseRadialLaw (PairFemaleOtherGapClass μ ν B) (hBc ▸ hv₀)
  rw [Fintype.card_fin] at h₀
  rw [hB] at h₁
  rw [hBc] at h₂
  refine lintegral_mono' h₀ fun ξ ↦ ?_
  have hξ : Measurable (fun t : ℝ × ℝ ↦ F (ξ, t)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hξ.aemeasurable]
  exact lintegral_mono' h₁ fun η ↦ lintegral_mono' h₂ le_rfl
private theorem pairMoved_iff_movedWoman (μ ν : Matching n) (m : Fin n) :
    μ m ≠ ν m ↔ μ.symm (μ m) ≠ ν.symm (μ m) := by
  constructor
  · intro hm h
    have he : ν m = μ m := by
      simpa only [μ.symm_apply_apply, ν.apply_symm_apply] using congrArg ν h
    exact hm he.symm
  · intro h he
    apply h
    simp only [μ.symm_apply_apply]
    rw [he, ν.symm_apply_apply]
private theorem pairCard_femaleGapClass (μ ν : Matching n) (A B : Finset (Fin n))
    (hAB : ∀ m, μ m ∈ B ↔ m ∈ A) :
    Fintype.card (PairFemaleGapClass μ ν B) = (pairOrientedMovedMen μ ν A).card := by
  let P (m : Fin n) := μ m ≠ ν m ∧ m ∈ A
  let Q (w : Fin n) := μ.symm w ≠ ν.symm w ∧ w ∈ B
  let e : Subtype P ≃ Subtype Q := μ.subtypeEquiv fun m ↦
    and_congr (pairMoved_iff_movedWoman μ ν m) (hAB m).symm
  let f : PairFemaleGapClass μ ν B ≃ Subtype Q :=
    Equiv.subtypeSubtypeEquivSubtypeInter _ _
  rw [Fintype.card_congr (f.trans e.symm), Fintype.card_subtype]
  congr 1
  ext m
  simp [pairOrientedMovedMen, and_comm]
private theorem pairCard_femaleOtherGapClass (μ ν : Matching n) (A B : Finset (Fin n))
    (hAB : ∀ m, μ m ∈ B ↔ m ∈ A) :
    Fintype.card (PairFemaleOtherGapClass μ ν B) =
      (pairOrientedMovedMen μ ν (Finset.univ \ A)).card := by
  let P (m : Fin n) := μ m ≠ ν m ∧ m ∉ A
  let Q (w : Fin n) := μ.symm w ≠ ν.symm w ∧ w ∉ B
  let e : Subtype P ≃ Subtype Q := μ.subtypeEquiv fun m ↦
    and_congr (pairMoved_iff_movedWoman μ ν m) (not_congr (hAB m).symm)
  let f : PairFemaleOtherGapClass μ ν B ≃ Subtype Q :=
    Equiv.subtypeSubtypeEquivSubtypeInter (fun w : Fin n ↦ μ.symm w ≠ ν.symm w)
      (fun w : Fin n ↦ w ∉ B)
  rw [Fintype.card_congr (f.trans e.symm), Fintype.card_subtype]
  congr 1
  ext m
  simp [pairOrientedMovedMen, and_comm]
theorem continuousScoreLaw_twoStableOrientation_image_le_radial (μ ν : Matching n)
    (A : Finset (Fin n)) {u v : ℕ}
    (hu : (pairOrientedMovedMen μ ν A).card = u)
    (hv : (pairOrientedMovedMen μ ν (Finset.univ \ A)).card = v)
    (hn : 0 < n) (hu₀ : 0 < u) (hv₀ : 0 < v) :
    continuousScoreLaw n (twoStableOrientationEvent μ ν A (A.image μ)) ≤
      ENNReal.ofReal (Real.exp 72) *
        ∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, pairRadialUpperKernel n u v (ξ, η, ζ)
          ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n := by
  have hA (m : Fin n) : μ m ∈ A.image μ ↔ m ∈ A := by
    rw [Finset.mem_image]
    exact ⟨fun ⟨m', hm', h⟩ ↦ μ.injective h ▸ hm', fun hm ↦ ⟨m, hm, rfl⟩⟩
  exact continuousScoreLaw_twoStableOrientation_le_radial μ ν A (A.image μ) hu hv
    ((pairCard_femaleGapClass μ ν A _ hA).trans hu)
    ((pairCard_femaleOtherGapClass μ ν A _ hA).trans hv) hn hu₀ hv₀
theorem lintegral_pairRadialUpperKernel_eq_closed (n u v : ℕ) :
    (∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, pairRadialUpperKernel n u v (ξ, η, ζ)
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n) =
      ∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, if ξ + η + ζ ≤ (n : ℝ) then
        ENNReal.ofReal (((1 - Real.exp (-(ξ + η + ζ))) / (ξ + η + ζ)) ^ n *
          ((1 - Real.exp (-(ξ + ζ))) / (ξ + ζ)) ^ u *
          ((1 - Real.exp (-(ξ + η))) / (ξ + η)) ^ v) else 0
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n := by
  apply lintegral_congr_ae
  filter_upwards [ae_spouseRadialLaw_pos n] with ξ hξ
  apply lintegral_congr_ae
  filter_upwards [ae_spouseRadialLaw_pos u] with η hη
  apply lintegral_congr_ae
  filter_upwards [ae_spouseRadialLaw_pos v] with ζ hζ
  have h₀ : 0 < ξ + η + ζ := by positivity
  have h₁ : 0 < ξ + ζ := by positivity
  have h₂ : 0 < ξ + η := by positivity
  simp only [pairRadialUpperKernel, Set.indicator, pairAggregateCutoff, Set.mem_ofPred_eq,
    pairAggregateLaplace, pairLaplace_of_pos h₀, pairLaplace_of_pos h₁, pairLaplace_of_pos h₂]
theorem twoStableOrientation_of_male_class {μ ν : Matching n} {x : ScoreProfile n}
    (hμ : IsScoreStable x μ) (hν : IsScoreStable x ν)
    (hx : ∀ r, Function.Injective (x r)) (A : Finset (Fin n))
    (hA : ∀ m, μ m ≠ ν m → (m ∈ A ↔ x (.inl m) (μ m) < x (.inl m) (ν m))) :
    x ∈ twoStableOrientationEvent μ ν A (A.image μ) ∧ A.image μ = A.image ν := by
  have hMleft (m : Fin n) (hm : m ∈ A) :
      x (.inl m) (μ m) ≤ x (.inl m) (ν m) := by
    by_cases he : μ m = ν m
    · rw [he]
    · exact ((hA m he).mp hm).le
  have hMright (m : Fin n) (hm : m ∉ A) :
      x (.inl m) (ν m) ≤ x (.inl m) (μ m) := by
    by_cases he : μ m = ν m
    · rw [he]
    · exact le_of_not_gt fun h ↦ hm ((hA m he).mpr h)
  have hWright (m : Fin n) (hm : m ∈ A) :
      x (.inr (μ m)) (ν.symm (μ m)) ≤ x (.inr (μ m)) m := by
    by_cases he : μ m = ν m
    · rw [he, ν.symm_apply_apply]
    · exact le_of_not_gt fun h ↦
        hν m (μ m) ⟨Ne.symm he, (hA m he).mp hm, h⟩
  have hWleft (m : Fin n) (hm : m ∉ A) :
      x (.inr (ν m)) (μ.symm (ν m)) ≤ x (.inr (ν m)) m := by
    by_cases he : μ m = ν m
    · rw [← he, μ.symm_apply_apply]
    · have hlt : x (.inl m) (ν m) < x (.inl m) (μ m) :=
        lt_of_le_of_ne (hMright m hm) fun h ↦ he ((hx (.inl m) h).symm)
      exact le_of_not_gt fun h ↦ hμ m (ν m) ⟨he, hlt, h⟩
  have hsub : A.image μ ⊆ A.image ν := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
    let j := ν.symm (μ m)
    have hj : ν j = μ m := ν.apply_symm_apply _
    refine Finset.mem_image.mpr ⟨j, ?_, hj⟩
    by_contra h
    have h₁ := hWright m hm
    have h₂ := hWleft j h
    rw [hj, μ.symm_apply_apply] at h₂
    have hmj : j = m := hx (.inr (μ m)) (le_antisymm h₁ h₂)
    exact h (hmj ▸ hm)
  have hImage : A.image μ = A.image ν := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ μ.injective, Finset.card_image_of_injective _ ν.injective]
  refine ⟨⟨hμ, hν, ?_⟩, hImage⟩
  constructor
  · intro m
    rw [jointManSpouseScoreLeft_split, jointManSpouseScoreRight_split]
    by_cases hm : m ∈ A
    · simpa only [if_pos hm] using hMleft m hm
    · simpa only [if_neg hm] using hMright m hm
  · intro w
    rw [jointWomanSpouseScoreLeft_split, jointWomanSpouseScoreRight_split]
    by_cases hw : w ∈ A.image μ
    · simp only [if_pos hw]
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
      simpa only [μ.symm_apply_apply] using hWright m hm
    · simp only [if_neg hw]
      let m := ν.symm w
      have hνm : ν m = w := ν.apply_symm_apply w
      have hm : m ∉ A := fun h ↦ hw (hImage ▸ Finset.mem_image.mpr ⟨m, h, hνm⟩)
      have h := hWleft m hm
      rwa [hνm] at h
end StepC
end

-- TwoStableBetaIntegral
section
open MeasureTheory Set
open scoped ENNReal
namespace StepC
private noncomputable def pairLaplaceClosed (x : ℝ) : ℝ :=
  (1 - Real.exp (-x)) / x
theorem measurable_pairLaplaceClosed : Measurable pairLaplaceClosed := by
  unfold pairLaplaceClosed
  fun_prop
private theorem pairLaplaceClosed_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ pairLaplaceClosed x := by
  apply div_nonneg _ hx.le
  linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)]
private theorem pairLaplaceClosed_le_one {x : ℝ} (hx : 0 < x) :
    pairLaplaceClosed x ≤ 1 := by
  apply (div_le_iff₀ hx).2
  linarith [Real.one_sub_le_exp_neg x]
private theorem pairLaplaceClosed_le_inv {x : ℝ} (hx : 0 < x) :
    pairLaplaceClosed x ≤ x⁻¹ := by
  rw [← one_div, pairLaplaceClosed]
  gcongr
  linarith [Real.exp_nonneg (-x)]
theorem lintegral_pairLaplaceClosed_le (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ x in Ioc (0 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x)) ≤
      ENNReal.ofReal (1 + Real.log n) := by
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn'
  have hlow : (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (pairLaplaceClosed x)) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro x hx
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (pairLaplaceClosed_le_one hx.1)
      _ = _ := by simp [Real.volume_Ioc]
  have hinv : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioc 1 n) := by
    have hc : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Icc 1 n) :=
      continuousOn_id.inv₀ fun x hx ↦ (zero_lt_one.trans_le hx.1).ne'
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hhigh : (∫⁻ x in Ioc (1 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x)) ≤
      ENNReal.ofReal (Real.log n) := by
    calc
      _ ≤ ∫⁻ x in Ioc (1 : ℝ) n, ENNReal.ofReal x⁻¹ := by
        exact setLIntegral_mono' measurableSet_Ioc fun x hx ↦
          ENNReal.ofReal_le_ofReal (pairLaplaceClosed_le_inv (zero_lt_one.trans hx.1))
      _ = ENNReal.ofReal (∫ x in Ioc (1 : ℝ) n, x⁻¹) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hinv
          ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx ↦
            inv_nonneg.mpr (zero_le_one.trans hx.1.le)))
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hn', integral_inv_of_pos zero_lt_one
          (zero_lt_one.trans_le hn'), div_one]
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 n) :=
    Set.disjoint_left.mpr fun _ h₁ h₂ ↦ (not_lt_of_ge h₁.2) h₂.1
  calc
    _ = (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (pairLaplaceClosed x)) +
          ∫⁻ x in Ioc (1 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x) := by
      rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hn',
        lintegral_union measurableSet_Ioc hdisj]
    _ ≤ 1 + ENNReal.ofReal (Real.log n) := add_le_add hlow hhigh
    _ = _ := by rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hlog]
private theorem intervalIntegral_beta_nat (i j : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ i * (1 - x) ^ j) =
      ((i.factorial : ℝ) * j.factorial) / (i + j + 1).factorial := by
  have hu : 0 < (((i : ℂ) + 1).re) := by simp; positivity
  have hv : 0 < (((j : ℂ) + 1).re) := by simp; positivity
  have hsum : ((i : ℂ) + 1) + ((j : ℂ) + 1) = ((i + j + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  have hc := Complex.betaIntegral_eq_Gamma_mul_div ((i : ℂ) + 1) ((j : ℂ) + 1) hu hv
  rw [hsum] at hc
  simp only [Complex.Gamma_nat_eq_factorial, Complex.betaIntegral, add_sub_cancel_right,
    Complex.cpow_natCast] at hc
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast] using hc
private noncomputable def pairBetaDensity (n k : ℕ) (s : ℝ) : ℝ :=
  s ^ (k - 1) * (1 - s) ^ (n - k - 1)
private theorem measurable_pairBetaDensity (n k : ℕ) : Measurable (pairBetaDensity n k) := by
  unfold pairBetaDensity
  fun_prop
theorem lintegral_pairBetaDensity (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (pairBetaDensity n k s)) =
      ENNReal.ofReal (pairSizeBetaFactor n k) := by
  have hi : IntegrableOn (pairBetaDensity n k) (Ioo 0 1) := by
    have hc : Continuous (pairBetaDensity n k) := by unfold pairBetaDensity; fun_prop
    exact hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    unfold pairBetaDensity pairSizeBetaFactor
    rw [intervalIntegral_beta_nat, show k - 1 + (n - k - 1) + 1 = n - 1 by omega]
  · exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun s hs ↦
      mul_nonneg (pow_nonneg hs.1.le _) (pow_nonneg (sub_nonneg.mpr hs.2.le) _))
private theorem map_restrict_Ioo_div {x : ℝ} (hx : 0 < x) :
    (volume.restrict (Ioo (0 : ℝ) x)).map (x⁻¹ * ·) =
      ENNReal.ofReal x • volume.restrict (Ioo (0 : ℝ) 1) := by
  have hpre : (x⁻¹ * ·) ⁻¹' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) x := by
    ext y
    change (0 < x⁻¹ * y ∧ x⁻¹ * y < 1) ↔ 0 < y ∧ y < x
    rw [← div_eq_inv_mul, div_lt_one hx]
    have hpos : 0 < y / x ↔ 0 < y := by
      rw [lt_div_iff₀ hx, zero_mul]
    rw [hpos]
  calc
    _ = ((volume : Measure ℝ).map (x⁻¹ * ·)).restrict (Ioo (0 : ℝ) 1) := by
      rw [Measure.restrict_map (measurable_const_mul _) measurableSet_Ioo, hpre]
    _ = _ := by
      rw [Real.map_volume_mul_left (inv_ne_zero hx.ne'), inv_inv, abs_of_pos hx,
        Measure.restrict_smul]
private noncomputable def pairBetaDilation (n k : ℕ) (x : ℝ) : ℝ → ℝ≥0∞ :=
  (Ioo 0 x).indicator (fun y ↦ ENNReal.ofReal (x⁻¹ * pairBetaDensity n k (x⁻¹ * y)))
private theorem measurable_pairBetaDilation (n k : ℕ) (x : ℝ) :
    Measurable (pairBetaDilation n k x) := by
  unfold pairBetaDilation
  refine Measurable.indicator ?_ measurableSet_Ioo
  unfold pairBetaDensity
  fun_prop
private theorem lintegral_pairBetaDilation {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    {x : ℝ} (hx : 0 < x) :
    (∫⁻ y, pairBetaDilation n k x y) = ENNReal.ofReal (pairSizeBetaFactor n k) := by
  have hf : Measurable (fun s ↦ ENNReal.ofReal (pairBetaDensity n k s)) :=
    (measurable_pairBetaDensity n k).ennreal_ofReal
  have hcomp : Measurable (fun y ↦ ENNReal.ofReal (pairBetaDensity n k (x⁻¹ * y))) :=
    hf.comp (measurable_const_mul _)
  rw [pairBetaDilation, lintegral_indicator measurableSet_Ioo]
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr hx.le)]
  rw [lintegral_const_mul _ hcomp]
  rw [← lintegral_map hf (measurable_const_mul x⁻¹), map_restrict_Ioo_div hx,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hx.le), inv_mul_cancel₀ hx.ne', ENNReal.ofReal_one,
    one_mul, lintegral_pairBetaDensity n k hk hkn]
private theorem lintegral_rotate_triple {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (μ ν ρ : Measure ℝ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    (∫⁻ y, ∫⁻ z, ∫⁻ x, F (x, y, z) ∂μ ∂ρ ∂ν) =
      ∫⁻ x, ∫⁻ y, ∫⁻ z, F (x, y, z) ∂ρ ∂ν ∂μ := by
  have hpair : Measurable (fun q : (ℝ × ℝ) × ℝ ↦ F (q.2, q.1)) :=
    hF.comp (measurable_snd.prodMk measurable_fst)
  have hinner : Measurable (fun q : ℝ × ℝ ↦ ∫⁻ x, F (x, q) ∂μ) :=
    hpair.lintegral_prod_right'
  calc
    _ = ∫⁻ q : ℝ × ℝ, (∫⁻ x, F (x, q) ∂μ) ∂ν.prod ρ :=
      (lintegral_prod _ hinner.aemeasurable).symm
    _ = ∫⁻ x, ∫⁻ q : ℝ × ℝ, F (x, q) ∂ν.prod ρ ∂μ :=
      lintegral_lintegral_swap hpair.aemeasurable
    _ = _ := by
      refine lintegral_congr fun x ↦ lintegral_prod _ ?_
      exact (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
private theorem lintegral_translate_triple {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y : ℝ, ∫⁻ z : ℝ, ∫⁻ w : ℝ, F (w + (y + z), y, z)) =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ, F (x, y, z) := by
  rw [← lintegral_rotate_triple hF volume volume volume]
  refine lintegral_congr fun y ↦ lintegral_congr fun z ↦ ?_
  exact lintegral_add_right_eq_self (fun x : ℝ ↦ F (x, y, z)) (y + z)
private noncomputable def twoStableClosedLaplaceAggregateKernel (n u v : ℕ) (w y z : ℝ) : ℝ :=
  pairLaplaceClosed (w + (y + z)) ^ n * pairLaplaceClosed (w + z) ^ u *
    pairLaplaceClosed (w + y) ^ v * (w ^ (n - 1) * y ^ (u - 1) * z ^ (v - 1))
private theorem scaled_pairBetaDensity_eq {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    x⁻¹ * pairBetaDensity n k (x⁻¹ * y) =
      y ^ (k - 1) * (x - y) ^ (n - k - 1) / x ^ (n - 1) := by
  have hdiv : 1 - x⁻¹ * y = (x - y) / x := by
    rw [← div_eq_inv_mul, sub_div, div_self hx.ne']
  unfold pairBetaDensity
  rw [hdiv, mul_pow, inv_pow, div_pow]
  calc
    _ = y ^ (k - 1) * (x - y) ^ (n - k - 1) / (x * (x ^ (k - 1) * x ^ (n - k - 1))) := by
      field_simp
    _ = _ := by
      rw [← pow_add, ← pow_succ', show k - 1 + (n - k - 1) + 1 = n - 1 by omega]
private theorem twoStableClosedLaplaceAggregateKernel_le_beta {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) {x y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hxyz : y + z < x) :
    twoStableClosedLaplaceAggregateKernel n u v (x - (y + z)) y z ≤
      pairLaplaceClosed x * (x⁻¹ * pairBetaDensity n u (x⁻¹ * y)) *
        (x⁻¹ * pairBetaDensity n v (x⁻¹ * z)) := by
  obtain ⟨hu, hv, huv⟩ := h
  have hup : 0 < u := by omega
  have hvp : 0 < v := by omega
  have hun : u < n := by omega
  have hvn : v < n := by omega
  have hn : 1 ≤ n := by omega
  have hx : 0 < x := by linarith
  have hxy : 0 < x - y := by linarith
  have hxz : 0 < x - z := by linarith
  have htriangle : 0 ≤ x - (y + z) := (sub_pos.mpr hxyz).le
  have htriangle' : x - (y + z) ≤ (x - y) * (x - z) / x := by
    apply (le_div_iff₀ hx).2
    nlinarith only [mul_nonneg hy.le hz.le]
  have hφ := pairLaplaceClosed_nonneg hx
  have hφyn := pairLaplaceClosed_nonneg hxy
  have hφzn := pairLaplaceClosed_nonneg hxz
  have hφx : pairLaplaceClosed x ^ n ≤ pairLaplaceClosed x * x⁻¹ ^ (n - 1) := calc
    _ = pairLaplaceClosed x * pairLaplaceClosed x ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hφ (pairLaplaceClosed_le_inv hx) _) hφ
  have hφy := pow_le_pow_left₀ hφyn (pairLaplaceClosed_le_inv hxy) u
  have hφz := pow_le_pow_left₀ hφzn (pairLaplaceClosed_le_inv hxz) v
  have hβu : (x - y) ^ (n - 1) = (x - y) ^ u * (x - y) ^ (n - u - 1) := by
    rw [← pow_add, show u + (n - u - 1) = n - 1 by omega]
  have hβv : (x - z) ^ (n - 1) = (x - z) ^ v * (x - z) ^ (n - v - 1) := by
    rw [← pow_add, show v + (n - v - 1) = n - 1 by omega]
  unfold twoStableClosedLaplaceAggregateKernel
  rw [sub_add_cancel, show x - (y + z) + z = x - y by ring,
    show x - (y + z) + y = x - z by ring]
  calc
    _ ≤ (pairLaplaceClosed x * x⁻¹ ^ (n - 1) * (x - y)⁻¹ ^ u * (x - z)⁻¹ ^ v) *
          ((x - (y + z)) ^ (n - 1) * y ^ (u - 1) * z ^ (v - 1)) := by
      gcongr
    _ ≤ (pairLaplaceClosed x * x⁻¹ ^ (n - 1) * (x - y)⁻¹ ^ u * (x - z)⁻¹ ^ v) *
          (((x - y) * (x - z) / x) ^ (n - 1) * y ^ (u - 1) * z ^ (v - 1)) := by
      gcongr
    _ = _ := by
      rw [scaled_pairBetaDensity_eq hup hun hx, scaled_pairBetaDensity_eq hvp hvn hx,
        div_pow, mul_pow, hβu, hβv]
      simp only [inv_pow]
      field_simp
private def translatedPairDomain (N : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2.1 + p.2.2 < p.1 ∧ p.1 ≤ N}
private theorem measurableSet_translatedPairDomain (N : ℝ) :
    MeasurableSet (translatedPairDomain N) := by
  have hy : Measurable (fun p : ℝ × ℝ × ℝ ↦ p.2.1) := by fun_prop
  have hz : Measurable (fun p : ℝ × ℝ × ℝ ↦ p.2.2) := by fun_prop
  exact (measurableSet_lt measurable_const hy).inter
    ((measurableSet_lt measurable_const hz).inter
      ((measurableSet_lt (hy.add hz) measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)))
private noncomputable def translatedPairKernel (n u v : ℕ) : ℝ × ℝ × ℝ → ℝ≥0∞ :=
  (translatedPairDomain n).indicator fun p ↦ ENNReal.ofReal
    (twoStableClosedLaplaceAggregateKernel n u v (p.1 - (p.2.1 + p.2.2)) p.2.1 p.2.2)
private theorem measurable_translatedPairKernel (n u v : ℕ) :
    Measurable (translatedPairKernel n u v) := by
  unfold translatedPairKernel twoStableClosedLaplaceAggregateKernel
  refine Measurable.indicator ?_ (measurableSet_translatedPairDomain n)
  unfold pairLaplaceClosed
  fun_prop
private theorem translatedPairKernel_eval (n u v : ℕ) (w y z : ℝ) :
    translatedPairKernel n u v (w + (y + z), y, z) =
      if 0 < y ∧ 0 < z ∧ 0 < w ∧ w + (y + z) ≤ n then
        ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z) else 0 := by
  have htri : y + z < w + (y + z) ↔ 0 < w := by
    constructor <;> intro hh <;> linarith
  simp [translatedPairKernel, translatedPairDomain, indicator_apply, htri]
private theorem lintegral_closedLaplace_eq_translated (n u v : ℕ) :
    (∫⁻ y in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ), ∫⁻ w in Ioi (0 : ℝ),
      if w + (y + z) ≤ n then
        ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z) else 0) =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ, translatedPairKernel n u v (x, y, z) := by
  rw [← lintegral_translate_triple (measurable_translatedPairKernel n u v)]
  simp_rw [← lintegral_indicator measurableSet_Ioi, indicator_apply, mem_Ioi,
    translatedPairKernel_eval]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : 0 < y
  · simp only [hy, ite_true, true_and]
    refine lintegral_congr fun z ↦ ?_
    by_cases hz : 0 < z
    · simp only [hz, ite_true, true_and]
      refine lintegral_congr fun w ↦ ?_
      by_cases hw : 0 < w <;> simp [hw]
    · simp [hz]
  · simp [hy]
private noncomputable def pairRadialFactor (n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ioc (0 : ℝ) n).indicator (fun x ↦ ENNReal.ofReal (pairLaplaceClosed x))
private theorem measurable_pairRadialFactor (n : ℕ) : Measurable (pairRadialFactor n) :=
  measurable_pairLaplaceClosed.ennreal_ofReal.indicator measurableSet_Ioc
private theorem translatedPairKernel_le {n u v : ℕ} (h : ValidPairSizes n (u, v))
    (x y z : ℝ) :
    translatedPairKernel n u v (x, y, z) ≤
      (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z := by
  by_cases hp : (x, y, z) ∈ translatedPairDomain n
  · have hp' := hp
    obtain ⟨hy, hz, htri, hn⟩ := hp'
    change 0 < y at hy
    change 0 < z at hz
    change y + z < x at htri
    have hx : 0 < x := by linarith
    have hyx : 0 < x - y := by linarith
    have hxD : x ∈ Ioc (0 : ℝ) n := ⟨hx, hn⟩
    have hyD : y ∈ Ioo 0 x := ⟨hy, by linarith⟩
    have hzD : z ∈ Ioo 0 x := ⟨hz, by linarith⟩
    have hφ := pairLaplaceClosed_nonneg hx
    have hβ : 0 ≤ x⁻¹ * pairBetaDensity n u (x⁻¹ * y) := by
      rw [scaled_pairBetaDensity_eq
        (show 0 < u by obtain ⟨hu, hv, huv⟩ := h; omega)
        (show u < n by obtain ⟨hu, hv, huv⟩ := h; omega) hx]
      positivity
    rw [translatedPairKernel, indicator_of_mem hp, pairRadialFactor, indicator_of_mem hxD,
      pairBetaDilation, pairBetaDilation, indicator_of_mem hyD, indicator_of_mem hzD,
      ← ENNReal.ofReal_mul hφ, ← ENNReal.ofReal_mul (mul_nonneg hφ hβ)]
    exact ENNReal.ofReal_le_ofReal
      (twoStableClosedLaplaceAggregateKernel_le_beta h hy hz htri)
  · rw [translatedPairKernel, indicator_of_notMem hp]
    exact zero_le
private theorem lintegral_pairRadialDilation {n u v : ℕ} (h : ValidPairSizes n (u, v)) :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
      (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z) =
    (∫⁻ x in Ioc (0 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x)) *
      ENNReal.ofReal (pairSizeBetaFactor n u) * ENNReal.ofReal (pairSizeBetaFactor n v) := by
  obtain ⟨hu, hv, huv⟩ := h
  have hup : 0 < u := by omega
  have hvp : 0 < v := by omega
  have hun : u < n := by omega
  have hvn : v < n := by omega
  have houter (x : ℝ) :
      (∫⁻ y : ℝ, ∫⁻ z : ℝ,
        (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z) =
      pairRadialFactor n x * ENNReal.ofReal (pairSizeBetaFactor n u) *
        ENNReal.ofReal (pairSizeBetaFactor n v) := by
    by_cases hx : x ∈ Ioc (0 : ℝ) n
    · have hm : Measurable (fun y ↦ pairRadialFactor n x * pairBetaDilation n u x y) :=
        measurable_const.mul (measurable_pairBetaDilation n u x)
      simp_rw [lintegral_const_mul _ (measurable_pairBetaDilation n v x),
        lintegral_pairBetaDilation hvp hvn hx.1]
      rw [lintegral_mul_const _ hm, lintegral_const_mul _ (measurable_pairBetaDilation n u x),
        lintegral_pairBetaDilation hup hun hx.1]
    · have hz : pairRadialFactor n x = 0 := indicator_of_notMem hx _
      simp [hz]
  simp_rw [houter]
  rw [lintegral_mul_const _ ((measurable_pairRadialFactor n).mul_const _),
    lintegral_mul_const _ (measurable_pairRadialFactor n), pairRadialFactor,
    lintegral_indicator measurableSet_Ioc]
theorem lintegral_twoStableClosedLaplaceAggregate_le {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) :
    (∫⁻ y in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ), ∫⁻ w in Ioi (0 : ℝ),
      if w + (y + z) ≤ n then
        ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z) else 0) ≤
      ENNReal.ofReal ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v) := by
  have hn : 1 ≤ n := by obtain ⟨hu, hv, huv⟩ := h; omega
  have hlog : 0 ≤ 1 + Real.log (n : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn))
  have hbu : 0 ≤ pairSizeBetaFactor n u := by unfold pairSizeBetaFactor; positivity
  rw [lintegral_closedLaplace_eq_translated]
  calc
    _ ≤ ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
          (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z :=
      lintegral_mono fun x ↦ lintegral_mono fun y ↦ lintegral_mono (translatedPairKernel_le h x y)
    _ = _ := lintegral_pairRadialDilation h
    _ ≤ (ENNReal.ofReal (1 + Real.log n) * ENNReal.ofReal (pairSizeBetaFactor n u)) *
          ENNReal.ofReal (pairSizeBetaFactor n v) := by
      gcongr
      exact lintegral_pairLaplaceClosed_le n hn
    _ = _ := by rw [← ENNReal.ofReal_mul hlog, ← ENNReal.ofReal_mul (mul_nonneg hlog hbu)]
private theorem lintegral_triple_prod {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (μ ν ρ : Measure ℝ) [SFinite ν] [SFinite ρ] :
    (∫⁻ p, F p ∂μ.prod (ν.prod ρ)) =
      ∫⁻ x, ∫⁻ y, ∫⁻ z, F (x, y, z) ∂ρ ∂ν ∂μ := by
  rw [lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr fun x ↦ lintegral_prod _ ?_
  exact (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
theorem lintegral_twoStableClosedLaplaceRadial_le {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) :
    (∫⁻ w, ∫⁻ y, ∫⁻ z, (if w + y + z ≤ n then ENNReal.ofReal
        (pairLaplaceClosed (w + y + z) ^ n * pairLaplaceClosed (w + z) ^ u *
          pairLaplaceClosed (w + y) ^ v) else 0)
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n) ≤
      ENNReal.ofReal ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v /
        ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial)) := by
  let R := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))
  let F (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
    if p.1 + p.2.1 + p.2.2 ≤ n then ENNReal.ofReal
      (pairLaplaceClosed (p.1 + p.2.1 + p.2.2) ^ n * pairLaplaceClosed (p.1 + p.2.2) ^ u *
        pairLaplaceClosed (p.1 + p.2.1) ^ v) else 0
  let G (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
    if p.1 + (p.2.1 + p.2.2) ≤ n then ENNReal.ofReal
      (twoStableClosedLaplaceAggregateKernel n u v p.1 p.2.1 p.2.2) else 0
  let D (k : ℕ) (s : ℝ) : ℝ := s ^ (k - 1) / ↑(k - 1).factorial
  let ρ (k : ℕ) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (D k s)
  let H (p : ℝ × ℝ × ℝ) : ℝ≥0∞ := ρ n p.1 * (ρ u p.2.1 * ρ v p.2.2)
  let C : ℝ := ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : Measurable F := by
    dsimp [F]
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    unfold pairLaplaceClosed
    fun_prop
  have hG : Measurable G := by
    dsimp [G]
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    unfold twoStableClosedLaplaceAggregateKernel pairLaplaceClosed
    fun_prop
  have hρ (k : ℕ) : Measurable (ρ k) := by
    dsimp [ρ, D]
    fun_prop
  have hH : Measurable H :=
    ((hρ n).comp measurable_fst).mul
      (((hρ u).comp (measurable_fst.comp measurable_snd)).mul
        ((hρ v).comp (measurable_snd.comp measurable_snd)))
  have hmeasure :
      (spouseRadialLaw n).prod ((spouseRadialLaw u).prod (spouseRadialLaw v)) =
        (R.prod (R.prod R)).withDensity H := by
    change (R.withDensity (ρ n)).prod ((R.withDensity (ρ u)).prod (R.withDensity (ρ v))) = _
    have hinner : Measurable (fun p : ℝ × ℝ ↦ ρ u p.1 * ρ v p.2) :=
      ((hρ u).comp measurable_fst).mul ((hρ v).comp measurable_snd)
    rw [prod_withDensity (hρ u) (hρ v), prod_withDensity (hρ n) hinner]
  have hpoint (w y z : ℝ) (hw : 0 < w) (hy : 0 < y) (hz : 0 < z) :
      (H * F) (w, y, z) = ENNReal.ofReal C * G (w, y, z) := by
    by_cases hcut : w + (y + z) ≤ n
    · have hcut' : w + y + z ≤ n := by simpa only [add_assoc] using hcut
      let P := pairLaplaceClosed (w + y + z) ^ n * pairLaplaceClosed (w + z) ^ u *
        pairLaplaceClosed (w + y) ^ v
      have hwn : 0 ≤ D n w := by dsimp [D]; positivity
      have hyn : 0 ≤ D u y := by dsimp [D]; positivity
      have hzn : 0 ≤ D v z := by dsimp [D]; positivity
      simp only [Pi.mul_apply, H, F, G, hcut, hcut', ite_true]
      change (ENNReal.ofReal (D n w) * (ENNReal.ofReal (D u y) * ENNReal.ofReal (D v z))) *
          ENNReal.ofReal P = ENNReal.ofReal C *
            ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z)
      rw [← ENNReal.ofReal_mul hyn, ← ENNReal.ofReal_mul hwn,
        ← ENNReal.ofReal_mul (mul_nonneg hwn (mul_nonneg hyn hzn)), ← ENNReal.ofReal_mul hC]
      congr 1
      dsimp [D, C, P, twoStableClosedLaplaceAggregateKernel]
      rw [add_assoc]
      ring
    · have hcut' : ¬w + y + z ≤ n := by simpa only [add_assoc] using hcut
      simp [F, G, hcut, hcut']
  change (∫⁻ w, ∫⁻ y, ∫⁻ z, F (w, y, z) ∂spouseRadialLaw v ∂spouseRadialLaw u
    ∂spouseRadialLaw n) ≤ _
  calc
    _ = ∫⁻ p, F p ∂(spouseRadialLaw n).prod ((spouseRadialLaw u).prod (spouseRadialLaw v)) :=
      (lintegral_triple_prod hF _ _ _).symm
    _ = ∫⁻ p, (H * F) p ∂(R.prod (R.prod R)) := by
      rw [hmeasure, lintegral_withDensity_eq_lintegral_mul _ hH hF]
    _ = ∫⁻ w, ∫⁻ y, ∫⁻ z, (H * F) (w, y, z) ∂ R ∂ R ∂ R := by
      exact lintegral_triple_prod (hH.mul hF) R R R
    _ = ∫⁻ w, ∫⁻ y, ∫⁻ z, ENNReal.ofReal C * G (w, y, z) ∂ R ∂ R ∂ R := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
      refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
      exact setLIntegral_congr_fun measurableSet_Ioi fun z hz ↦ hpoint w y z hw hy hz
    _ = ENNReal.ofReal C * (∫⁻ w, ∫⁻ y, ∫⁻ z, G (w, y, z) ∂ R ∂ R ∂ R) := by
      simp_rw [lintegral_const_mul' (ENNReal.ofReal C) _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal C * (∫⁻ y, ∫⁻ z, ∫⁻ w, G (w, y, z) ∂ R ∂ R ∂ R) := by
      rw [lintegral_rotate_triple hG R R R]
    _ ≤ ENNReal.ofReal C *
        ENNReal.ofReal ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v) := by
      gcongr
      exact lintegral_twoStableClosedLaplaceAggregate_le h
    _ = _ := by rw [← ENNReal.ofReal_mul hC, div_eq_inv_mul]
end StepC
end

-- TwoStableOrientationCounting
section
open Equiv Equiv.Perm Finset StableMarriage
open scoped BigOperators ENNReal
namespace StepC
variable {n : ℕ}
private structure LabeledPairOrientation (μ ν : Matching n) (U V : Finset (Fin n)) : Prop where
  disjoint : Disjoint U V
  union_support : U ∪ V = (relativeMenPermutation μ ν).support
  preserves_left : ∀ i, relativeMenPermutation μ ν i ∈ U ↔ i ∈ U
  preserves_right : ∀ i, relativeMenPermutation μ ν i ∈ V ↔ i ∈ V
namespace LabeledPairOrientation
variable {μ ν : Matching n} {U V : Finset (Fin n)}
private def leftPerm (h : LabeledPairOrientation μ ν U V) : Perm U :=
  (relativeMenPermutation μ ν).subtypePerm h.preserves_left
private def rightPerm (h : LabeledPairOrientation μ ν U V) : Perm V :=
  (relativeMenPermutation μ ν).subtypePerm h.preserves_right
theorem leftPerm_apply_ne (h : LabeledPairOrientation μ ν U V) (i : U) :
    h.leftPerm i ≠ i := by
  intro he
  apply mem_support.mp (h.union_support ▸ mem_union_left V i.property)
  exact congrArg Subtype.val he
theorem rightPerm_apply_ne (h : LabeledPairOrientation μ ν U V) (i : V) :
    h.rightPerm i ≠ i := by
  intro he
  apply mem_support.mp (h.union_support ▸ mem_union_right U i.property)
  exact congrArg Subtype.val he
end LabeledPairOrientation
private abbrev OrientationSideChoices (n u v : ℕ) :=
  Σ U : ↥((univ : Finset (Fin n)).powersetCard u), ↥(U.valᶜ.powersetCard v)
theorem card_orientationSideChoices (n u v : ℕ) :
    Nat.card (OrientationSideChoices n u v) = n.choose u * (n - u).choose v := by
  rw [Nat.card_sigma]
  have hcard (U : ↥((univ : Finset (Fin n)).powersetCard u)) : U.val.card = u :=
    (mem_powersetCard.mp U.property).2
  simp only [Nat.card_eq_finsetCard, card_powersetCard, card_compl, Fintype.card_fin, hcard,
    sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe]
  rfl
private abbrev RestrictedOrientationPerm (k : ℕ) (P : Multiset ℕ → Prop) :=
  {f : Perm (Fin k) // (∀ i, f i ≠ i) ∧ P f.cycleType}
private abbrev LabeledOrientationPairs (n u v : ℕ) (P Q : Multiset ℕ → Prop) :=
  {z : (Matching n × Matching n) × (Finset (Fin n) × Finset (Fin n)) //
    ∃ h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2,
      z.2.1.card = u ∧ z.2.2.card = v ∧ P h.leftPerm.cycleType ∧ Q h.rightPerm.cycleType}
private noncomputable def relabelOrientationSide {k : ℕ} {S : Finset (Fin n)}
    (hS : S.card = k) : Fin k ≃ S :=
  Fintype.equivOfCardEq (by simp [hS])
private theorem cycleType_ofSubtype_finset {S : Finset (Fin n)} (p : Perm S) :
    p.ofSubtype.cycleType = p.cycleType :=
  cycleType_ofSubtype (g := p)
private theorem relabelSide_cycleType {k : ℕ} {S : Finset (Fin n)}
    (e : Fin k ≃ S) (p : Perm S) : (e.permCongr.symm p).cycleType = p.cycleType := by
  rw [← cycleType_extendDomain e]
  change (ofSubtype (e.permCongr (e.permCongr.symm p))).cycleType = _
  rw [e.permCongr.apply_symm_apply, cycleType_ofSubtype_finset]
private theorem relabelSide_apply_ne {k : ℕ} {S : Finset (Fin n)}
    (e : Fin k ≃ S) {p : Perm S} (hp : ∀ i, p i ≠ i) (j : Fin k) :
    e.permCongr.symm p j ≠ j := by
  intro he
  apply hp (e j)
  simpa only [Equiv.permCongr_symm_apply, Equiv.apply_symm_apply] using congrArg e he
private noncomputable def labeledOrientationPairsEmbedding (n u v : ℕ) (P Q : Multiset ℕ → Prop) :
    LabeledOrientationPairs n u v P Q ↪
      Matching n × OrientationSideChoices n u v ×
        RestrictedOrientationPerm u P × RestrictedOrientationPerm v Q := by
  let encode (z : LabeledOrientationPairs n u v P Q) :
      Matching n × OrientationSideChoices n u v ×
        RestrictedOrientationPerm u P × RestrictedOrientationPerm v Q := by
    let h := z.property.choose
    have hU := z.property.choose_spec.1
    have hV := z.property.choose_spec.2.1
    have hP := z.property.choose_spec.2.2.1
    have hQ := z.property.choose_spec.2.2.2
    let eU := relabelOrientationSide hU
    let eV := relabelOrientationSide hV
    exact ⟨z.val.1.1, ⟨⟨z.val.2.1, mem_powersetCard.mpr ⟨subset_univ _, hU⟩⟩,
      ⟨z.val.2.2, mem_powersetCard.mpr
        ⟨fun _ hi ↦ mem_compl.mpr fun hU' ↦ disjoint_left.mp h.disjoint hU' hi, hV⟩⟩⟩,
      ⟨eU.permCongr.symm h.leftPerm, relabelSide_apply_ne eU h.leftPerm_apply_ne,
        (relabelSide_cycleType eU h.leftPerm).symm ▸ hP⟩,
      ⟨eV.permCongr.symm h.rightPerm, relabelSide_apply_ne eV h.rightPerm_apply_ne,
        (relabelSide_cycleType eV h.rightPerm).symm ▸ hQ⟩⟩
  refine ⟨encode, ?_⟩
  rintro ⟨⟨⟨μ, ν⟩, U, V⟩, hz⟩ ⟨⟨⟨μ', ν'⟩, U', V'⟩, hw⟩ he
  have hμ : μ = μ' := congrArg (fun z ↦ z.1) he
  have hU : U = U' := congrArg (fun z ↦ z.2.1.1.val) he
  have hV : V = V' := congrArg (fun z ↦ z.2.1.2.val) he
  subst μ' U' V'
  have hleft : hz.choose.leftPerm = hw.choose.leftPerm := by
    have hp := congrArg (fun z ↦ z.2.2.1.val) he
    exact (relabelOrientationSide hz.choose_spec.1).permCongr.symm.injective hp
  have hright : hz.choose.rightPerm = hw.choose.rightPerm := by
    have hp := congrArg (fun z ↦ z.2.2.2.val) he
    exact (relabelOrientationSide hz.choose_spec.2.1).permCongr.symm.injective hp
  have hrel : relativeMenPermutation μ ν = relativeMenPermutation μ ν' := by
    apply Equiv.ext
    intro i
    by_cases hiU : i ∈ U
    · exact congrArg (fun f : Perm U ↦ (f ⟨i, hiU⟩).val) hleft
    by_cases hiV : i ∈ V
    · exact congrArg (fun f : Perm V ↦ (f ⟨i, hiV⟩).val) hright
    have hi : i ∉ U ∪ V := fun h ↦ (mem_union.mp h).elim hiU hiV
    exact (notMem_support.mp (hz.choose.union_support ▸ hi)).trans
      (notMem_support.mp (hw.choose.union_support ▸ hi)).symm
  have hνsymm : ν.symm = ν'.symm := by
    apply Equiv.ext
    intro i
    simpa only [relativeMenPermutation, Equiv.trans_apply, Equiv.apply_symm_apply] using
      congrArg (fun f : Matching n ↦ f (μ.symm i)) hrel
  have hν : ν = ν' := congrArg Equiv.symm hνsymm
  exact Subtype.ext (congrArg (fun m ↦ ((μ, m), U, V)) hν)
theorem card_labeledOrientationPairs_le (n u v : ℕ) (P Q : Multiset ℕ → Prop) :
    Nat.card (LabeledOrientationPairs n u v P Q) ≤
      n.factorial * (n.choose u * (n - u).choose v) *
        (Nat.card (RestrictedOrientationPerm u P) * Nat.card (RestrictedOrientationPerm v Q)) := by
  have h := Nat.card_le_card_of_injective _ (labeledOrientationPairsEmbedding n u v P Q).injective
  refine h.trans_eq ?_
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, card_orientationSideChoices,
    Nat.card_eq_fintype_card (α := Matching n)]
  simp only [Matching, Fintype.card_perm, Fintype.card_fin, mul_assoc]
private theorem orientationChoices_mul_factorials {n u v : ℕ} :
    (n.choose u * (n - u).choose v) * u.factorial * v.factorial =
      n.descFactorial (u + v) := by
  calc
    _ = ((n - u).choose v * v.factorial) * (n.choose u * u.factorial) := by ring
    _ = (n - u).descFactorial v * n.descFactorial u := by
      simp only [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
    _ = _ := by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.descFactorial_mul_descFactorial (n := n) (Nat.le_add_right u v))
theorem card_labeledOrientationPairs_real_le {n u v : ℕ} (h : u + v ≤ n)
    (P Q : Multiset ℕ → Prop) :
    (Nat.card (LabeledOrientationPairs n u v P Q) : ℝ) ≤
      ((n.factorial : ℝ) ^ 2 / (n - u - v).factorial) *
        ((Nat.card (RestrictedOrientationPerm u P) : ℝ) / u.factorial) *
          ((Nat.card (RestrictedOrientationPerm v Q) : ℝ) / v.factorial) := by
  have hdesc : (n.factorial : ℝ) / (n - u - v).factorial =
      (n.descFactorial (u + v) : ℝ) := by
    apply (div_eq_iff (by positivity)).mpr
    rw [← Nat.sub_add_eq, mul_comm]
    exact_mod_cast (Nat.factorial_mul_descFactorial h).symm
  have hc : (n.choose u : ℝ) * (n - u).choose v * u.factorial * v.factorial =
      (n.descFactorial (u + v) : ℝ) := by exact_mod_cast orientationChoices_mul_factorials
  calc
    _ ≤ (n.factorial : ℝ) * ((n.choose u : ℝ) * (n - u).choose v) *
        ((Nat.card (RestrictedOrientationPerm u P) : ℝ) *
          Nat.card (RestrictedOrientationPerm v Q)) := by
      exact_mod_cast card_labeledOrientationPairs_le n u v P Q
    _ = _ := by
      rw [pow_two, mul_div_assoc, hdesc, ← hc]
      field_simp
private noncomputable def orientationCycleTypeFraction (k : ℕ) (P : Multiset ℕ → Prop) : ℝ≥0∞ :=
  (Nat.card {f : Perm (Fin k) // P f.cycleType} : ℝ≥0∞) / k.factorial
theorem card_labeledOrientationPairs_le_cycleTypeFractions {n u v : ℕ} (h : u + v ≤ n)
    (P Q : Multiset ℕ → Prop) :
    (Nat.card (LabeledOrientationPairs n u v P Q) : ℝ≥0∞) ≤
      ((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        orientationCycleTypeFraction u P * orientationCycleTypeFraction v Q := by
  let B (k : ℕ) (F : Multiset ℕ → Prop) := Nat.card {f : Perm (Fin k) // F f.cycleType}
  have hB (k : ℕ) (F : Multiset ℕ → Prop) : Nat.card (RestrictedOrientationPerm k F) ≤ B k F :=
    Nat.card_le_card_of_injective (fun f : RestrictedOrientationPerm k F ↦ ⟨f.val, f.property.2⟩)
      (fun _ _ he ↦ Subtype.ext (congrArg (fun f : {f : Perm (Fin k) // F f.cycleType} ↦ f.val) he))
  have hr := card_labeledOrientationPairs_real_le h P Q
  have ht : (Nat.card (LabeledOrientationPairs n u v P Q) : ℝ) ≤
      ((n.factorial : ℝ) ^ 2 / (n - u - v).factorial) *
        ((B u P : ℝ) / u.factorial) * ((B v Q : ℝ) / v.factorial) := by
    refine hr.trans ?_
    gcongr
    · exact_mod_cast hB u P
    · exact_mod_cast hB v Q
  have he := ENNReal.ofReal_le_ofReal ht
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity)] at he
  simpa only [ENNReal.ofReal_natCast, orientationCycleTypeFraction, B] using he
@[simp] theorem orientationCycleTypeFraction_true (k : ℕ) :
    orientationCycleTypeFraction k (fun _ ↦ True) = 1 := by
  unfold orientationCycleTypeFraction
  have e : {f : Perm (Fin k) // True} ≃ Perm (Fin k) :=
    Equiv.subtypeUnivEquiv (fun _ ↦ trivial)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  exact ENNReal.div_self (by positivity) (ENNReal.natCast_ne_top _)
theorem card_labeledOrientationPairs_unrestricted_le {n u v : ℕ} (h : u + v ≤ n) :
    (Nat.card (LabeledOrientationPairs n u v (fun _ ↦ True) (fun _ ↦ True)) : ℝ≥0∞) ≤
      (n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial := by
  simpa only [orientationCycleTypeFraction_true, mul_one] using
    card_labeledOrientationPairs_le_cycleTypeFractions h (fun _ ↦ True) (fun _ ↦ True)
theorem womanRank_second_lt_first_of_worsePartnerMen {p : Profile n} {μ ν : Matching n}
    (hν : IsStable p ν) {i : Fin n} (hi : i ∈ worsePartnerMen p ν μ) :
    p.womanRank (μ i) (ν.symm (μ i)) < p.womanRank (μ i) i := by
  have hm := (mem_filter.mp hi).2
  have hne : ν i ≠ μ i := fun h ↦ hm.ne (congrArg (p.manRank i) h).symm
  have hj : ν.symm (μ i) ≠ i := fun h ↦ hne (ν.symm_apply_eq.mp h).symm
  refine lt_of_le_of_ne (le_of_not_gt ?_) ((p.womanRank (μ i)).injective.ne hj)
  exact fun h ↦ hν i (μ i) ⟨hne, hm, h⟩
private theorem relativeMenPermutation_maps_worsePartnerMen {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) {i : Fin n} (hi : i ∈ worsePartnerMen p ν μ) :
    relativeMenPermutation μ ν i ∈ worsePartnerMen p ν μ := by
  let j := ν.symm (μ i)
  have hνj : ν j = μ i := ν.apply_symm_apply _
  have hw : p.womanRank (μ i) j < p.womanRank (μ i) i :=
    womanRank_second_lt_first_of_worsePartnerMen hν hi
  have hμj : μ j ≠ ν j := by
    intro h
    have hj : j = i := μ.injective (h.trans hνj)
    exact hw.ne (congrArg (p.womanRank (μ i)) hj)
  refine mem_filter.mpr ⟨mem_univ _, lt_of_le_of_ne (le_of_not_gt ?_)
    ((p.manRank j).injective.ne hμj)⟩
  intro h
  exact hμ j (μ i) ⟨fun h' ↦ hμj (h'.trans hνj.symm), hνj ▸ h,
    by simpa only [Equiv.symm_apply_apply] using hw⟩
private theorem perm_mem_iff_of_maps_finset (f : Matching n) (S : Finset (Fin n))
    (hf : ∀ i ∈ S, f i ∈ S) (i : Fin n) : f i ∈ S ↔ i ∈ S := by
  have he : S.image f = S := eq_of_subset_of_card_le (by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
    exact hf k hk) ((card_image_of_injective S f.injective).ge)
  refine ⟨fun h ↦ ?_, hf i⟩
  obtain ⟨k, hk, heq⟩ := mem_image.mp (he.symm ▸ h)
  exact f.injective heq ▸ hk
theorem labeledPairOrientation_of_stable {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    LabeledPairOrientation μ ν (worsePartnerMen p μ ν) (worsePartnerMen p ν μ) := by
  have hright := perm_mem_iff_of_maps_finset (relativeMenPermutation μ ν) (worsePartnerMen p ν μ)
    (fun _ hi ↦ relativeMenPermutation_maps_worsePartnerMen hμ hν hi)
  have hleft' := perm_mem_iff_of_maps_finset (relativeMenPermutation ν μ) (worsePartnerMen p μ ν)
    (fun _ hi ↦ relativeMenPermutation_maps_worsePartnerMen hν hμ hi)
  refine ⟨disjoint_worsePartnerMen p μ ν, union_worsePartnerMen_eq_support p μ ν, ?_, hright⟩
  intro i
  have hi := hleft' (relativeMenPermutation μ ν i)
  have he : relativeMenPermutation ν μ (relativeMenPermutation μ ν i) = i := by
    simp only [relativeMenPermutation, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply]
  rw [he] at hi
  exact hi.symm
theorem LabeledPairOrientation.cycleFactorsFinset_ofSubtype_leftPerm
    {μ ν : Matching n} {U V : Finset (Fin n)} (h : LabeledPairOrientation μ ν U V) :
    h.leftPerm.ofSubtype.cycleFactorsFinset =
      (relativeMenPermutation μ ν).cycleFactorsFinset.filter fun c ↦ c.support ⊆ U := by
  classical
  let f := relativeMenPermutation μ ν
  let g := h.leftPerm.ofSubtype
  have hsub : g.support ⊆ U := by
    intro i hi
    by_contra hn
    exact mem_support.mp hi (ofSubtype_apply_of_not_mem h.leftPerm hn)
  have hagree (i : Fin n) (hi : i ∈ U) : g i = f i :=
    ofSubtype_apply_of_mem h.leftPerm hi
  ext c
  rw [mem_filter]
  constructor
  · intro hc
    have hcu := (mem_cycleFactorsFinset_support_le hc).trans hsub
    obtain ⟨hcyc, hcg⟩ := mem_cycleFactorsFinset_iff.mp hc
    exact ⟨mem_cycleFactorsFinset_iff.mpr ⟨hcyc, fun i hi ↦
      (hcg i hi).trans (hagree i (hcu hi))⟩, hcu⟩
  · rintro ⟨hc, hcu⟩
    obtain ⟨hcyc, hcf⟩ := mem_cycleFactorsFinset_iff.mp hc
    exact mem_cycleFactorsFinset_iff.mpr ⟨hcyc, fun i hi ↦
      (hcf i hi).trans (hagree i (hcu hi)).symm⟩
theorem forcedShortCycles_card_eq_shortCycleCount_leftPerm
    {p : Profile n} {μ ν : Matching n} (L : ℕ)
    (h : LabeledPairOrientation μ ν (worsePartnerMen p μ ν) (worsePartnerMen p ν μ)) :
    (forcedShortCycles p μ ν L).card = shortCycleCount L h.leftPerm := by
  unfold shortCycleCount
  rw [← cycleType_ofSubtype_finset h.leftPerm]
  simp only [Equiv.Perm.cycleType, Multiset.filter_map, Multiset.card_map]
  change (forcedShortCycles p μ ν L).card =
    (h.leftPerm.ofSubtype.cycleFactorsFinset.filter (fun c ↦ c.support.card ≤ L)).card
  rw [h.cycleFactorsFinset_ofSubtype_leftPerm, filter_filter]
  apply congrArg Finset.card
  ext c
  simp only [forcedShortCycles, mem_filter]
private def forcedShortCycleTypeException (L : ℕ) (T : Multiset ℕ) : Prop :=
  (((T.filter (· ≤ L)).card : ℕ) : ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ)
theorem forcedShortCycleTypeException_leftPerm_iff
    {p : Profile n} {μ ν : Matching n} (L : ℕ)
    (h : LabeledPairOrientation μ ν (worsePartnerMen p μ ν) (worsePartnerMen p ν μ)) :
    forcedShortCycleTypeException L h.leftPerm.cycleType ↔
      ((forcedShortCycles p μ ν L).card : ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ) := by
  rw [forcedShortCycles_card_eq_shortCycleCount_leftPerm L h]
  rfl
open scoped Classical in
theorem finiteCountChebyshev_below {α : Type*} [Fintype α] [Nonempty α]
    (C : α → ℕ) {H T : ℝ} (hT : T < H)
    (hmean : (∑ i, (C i : ℝ)) = (Fintype.card α : ℝ) * H)
    (hpair : (∑ i, (C i : ℝ) * ((C i : ℝ) - 1)) ≤ (Fintype.card α : ℝ) * H ^ 2) :
    ((univ.filter (fun i ↦ (C i : ℝ) < T)).card : ℝ) / (Fintype.card α : ℝ) ≤
      H / (H - T) ^ 2 := by
  let S := univ.filter (fun i ↦ (C i : ℝ) < T)
  have hs : (∑ i, ((C i : ℝ) - H) ^ 2) ≤ (Fintype.card α : ℝ) * H := by
    calc
      _ = ∑ i, ((C i : ℝ) * ((C i : ℝ) - 1) + (C i : ℝ) -
          2 * H * (C i : ℝ) + H ^ 2) := sum_congr rfl fun i _ ↦ by ring
      _ = (∑ i, (C i : ℝ) * ((C i : ℝ) - 1)) + (∑ i, (C i : ℝ)) -
          2 * H * (∑ i, (C i : ℝ)) + (Fintype.card α : ℝ) * H ^ 2 := by
        simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
      _ ≤ _ := by rw [hmean]; nlinarith only [hpair]
  have ht : (S.card : ℝ) * (H - T) ^ 2 ≤ (Fintype.card α : ℝ) * H := by
    calc
      _ = ∑ i ∈ S, (H - T) ^ 2 := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, ((C i : ℝ) - H) ^ 2 := by
        refine sum_le_sum fun i hi ↦ ?_
        have hci := (mem_filter.mp hi).2
        rw [show ((C i : ℝ) - H) ^ 2 = (H - (C i : ℝ)) ^ 2 by ring]
        exact pow_le_pow_left₀ (sub_nonneg.mpr hT.le) (sub_le_sub_left hci.le H) 2
      _ ≤ ∑ i, ((C i : ℝ) - H) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _
      _ ≤ _ := hs
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  exact (div_le_div_iff₀ hc (pow_pos (sub_pos.mpr hT) _)).mpr (by simpa [mul_comm] using ht)
private theorem log_sub_one_le_shortCycleHarmonic {k L : ℕ} (hL : 2 ≤ L) (hk : L ≤ k) :
    Real.log (L : ℝ) - 1 ≤ ∑ j ∈ Icc 2 (min L k), (1 : ℝ) / j := by
  have h₁ : 1 ∈ Icc 1 L := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have he : (Icc 1 L).erase 1 = Icc 2 L := by
    ext j
    simp only [mem_erase, mem_Icc]
    omega
  have hh := log_le_harmonic_floor (L : ℝ) (by positivity)
  rw [Nat.floor_natCast] at hh
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  rw [← sum_erase_add (Icc 1 L) (fun j ↦ (j : ℝ)⁻¹) h₁, he, Nat.cast_one, inv_one] at hh
  rw [min_eq_left hk]
  simpa only [one_div] using (sub_le_iff_le_add.mpr hh)
theorem forcedShortCycleTypeException_fraction_le {k L : ℕ} (hL : 2 ≤ L) (hk : L ≤ k)
    (hlog : 100 ≤ Real.log (L : ℝ)) :
    orientationCycleTypeFraction k (forcedShortCycleTypeException L) ≤
      ENNReal.ofReal (400 / Real.log (L : ℝ)) := by
  classical
  let H := ∑ j ∈ Icc 2 (min L k), (1 : ℝ) / j
  let ell := Real.log (L : ℝ)
  let T := (9 / 10 : ℝ) * ell
  have hl : 0 < ell := by linarith
  have hHlo : ell - 1 ≤ H := log_sub_one_le_shortCycleHarmonic hL hk
  have hHhi : H ≤ ell := shortCycleHarmonic_le_log k L hL
  have hgap : ell / 20 ≤ H - T := by dsimp [T]; linarith
  have hT : T < H := by linarith
  have hc : Fintype.card (Perm (Fin k)) = k.factorial := by rw [Fintype.card_perm, Fintype.card_fin]
  have h := finiteCountChebyshev_below (shortCycleCount L) hT
    (by rw [hc]; exact sum_shortCycleCount k L)
    (by rw [hc]; exact sum_shortCycleCount_mul_sub_one_le k L)
  rw [hc] at h
  have hbound : H / (H - T) ^ 2 ≤ 400 / ell := calc
    _ ≤ ell / (H - T) ^ 2 :=
      div_le_div_of_nonneg_right hHhi (sq_nonneg _)
    _ ≤ ell / (ell / 20) ^ 2 :=
      div_le_div_of_nonneg_left hl.le (by positivity)
        (pow_le_pow_left₀ (by positivity) hgap 2)
    _ = _ := by field_simp; ring
  have hb := ENNReal.ofReal_le_ofReal (h.trans hbound)
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast] at hb
  unfold orientationCycleTypeFraction
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [ENNReal.ofReal_natCast, forcedShortCycleTypeException, shortCycleCount, T, ell] at hb ⊢
  exact hb
theorem card_labeledOrientationPairs_forcedShortException_le {n u v L : ℕ} (h : u + v ≤ n)
    (hL : 2 ≤ L) (hu : L ≤ u) (hlog : 100 ≤ Real.log (L : ℝ)) :
    (Nat.card (LabeledOrientationPairs n u v (forcedShortCycleTypeException L) (fun _ ↦ True)) :
      ℝ≥0∞) ≤ ((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        ENNReal.ofReal (400 / Real.log (L : ℝ)) := by
  have hc := card_labeledOrientationPairs_le_cycleTypeFractions h
    (forcedShortCycleTypeException L) (fun _ ↦ True)
  rw [orientationCycleTypeFraction_true, mul_one] at hc
  exact hc.trans (mul_le_mul_right (forcedShortCycleTypeException_fraction_le hL hu hlog) _)
end StepC
end

-- TwoStableFixedPairBound
section
open MeasureTheory Set StableMarriage
open scoped ENNReal
namespace StepC
private noncomputable def labeledStablePairMassBound (n u v : ℕ) : ℝ :=
  Real.exp 72 * ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v /
    ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial))
theorem measure_twoStableOrientationEvent_le_labeledStablePairMassBound
    {n u v : ℕ} (h : ValidPairSizes n (u, v)) (μ ν : Matching n) (A : Finset (Fin n))
    (hu : (pairOrientedMovedMen μ ν A).card = u)
    (hv : (pairOrientedMovedMen μ ν (Finset.univ \ A)).card = v) :
    continuousScoreLaw n (twoStableOrientationEvent μ ν A (A.image μ)) ≤
      ENNReal.ofReal (labeledStablePairMassBound n u v) := by
  have hn : 0 < n := by have := h.1; have := h.2.2; omega
  have hu₀ : 0 < u := by have := h.1; omega
  have hv₀ : 0 < v := by have := h.2.1; omega
  have hp := continuousScoreLaw_twoStableOrientation_image_le_radial μ ν A hu hv hn hu₀ hv₀
  rw [lintegral_pairRadialUpperKernel_eq_closed] at hp
  refine hp.trans ?_
  rw [labeledStablePairMassBound, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul_right
    (by simpa only [pairLaplaceClosed] using lintegral_twoStableClosedLaplaceRadial_le h) _
private theorem pairOrientedMovedMen_eq_sides {n : ℕ} {μ ν : Matching n}
    {U V : Finset (Fin n)} (hUV : LabeledPairOrientation μ ν U V) :
    pairOrientedMovedMen ν μ U = U ∧
      pairOrientedMovedMen ν μ (Finset.univ \ U) = V := by
  have hm (i : Fin n) : ν i ≠ μ i ↔ i ∈ U ∨ i ∈ V := by
    rw [← Finset.mem_union, hUV.union_support]
    simp only [relativeMenPermutation, Equiv.Perm.mem_support, Equiv.trans_apply]
    exact ne_comm.trans (not_congr ν.symm_apply_eq).symm
  constructor
  · ext i
    simp only [pairOrientedMovedMen, Finset.mem_filter, hm, and_iff_left_iff_imp]
    exact fun hi ↦ Or.inl hi
  · ext i
    simp only [pairOrientedMovedMen, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, hm]
    exact ⟨fun ⟨hi, h⟩ ↦ h.resolve_left hi,
      fun hi ↦ ⟨fun hj ↦ Finset.disjoint_left.mp hUV.disjoint hj hi, Or.inr hi⟩⟩
theorem measure_stablePairSector_le_labeledStablePairMassBound {n u v : ℕ}
    {μ ν : Matching n} {U V : Finset (Fin n)}
    (h : ValidPairSizes n (u, v)) (hUV : LabeledPairOrientation μ ν U V)
    (hu : U.card = u) (hv : V.card = v)
    {E : Set (ScoreProfile n)}
    (hE : ∀ᵐ x ∂continuousScoreLaw n, x ∈ E →
      IsScoreStable x μ ∧ IsScoreStable x ν ∧
        U = worsePartnerMen (profileOfScores x) μ ν) :
    continuousScoreLaw n E ≤ ENNReal.ofReal (labeledStablePairMassBound n u v) := by
  have hsub : continuousScoreLaw n E ≤
      continuousScoreLaw n (twoStableOrientationEvent ν μ U (U.image ν)) := by
    apply measure_mono_ae
    filter_upwards [ae_injective_rows n, hE] with x hx hs he
    obtain ⟨hμ, hν, hU⟩ := hs he
    exact (twoStableOrientation_of_male_class hν hμ hx U
      (fun m _ ↦ hU ▸ mem_worsePartnerMen_iff_score_lt hx μ ν m)).1
  exact hsub.trans (measure_twoStableOrientationEvent_le_labeledStablePairMassBound
    h ν μ U ((congrArg Finset.card (pairOrientedMovedMen_eq_sides hUV).1).trans hu)
    ((congrArg Finset.card (pairOrientedMovedMen_eq_sides hUV).2).trans hv))
theorem labeledStablePairMassBound_mul_factorials {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) :
    ((n.factorial : ℝ) ^ 2 / ↑(n - u - v).factorial) * labeledStablePairMassBound n u v =
      Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v) := by
  rw [twoStablePairSizeKernel_eq_beta_factors h, labeledStablePairMassBound]
  ring
end StepC
end

-- PivotBackgroundPairBound
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal
namespace StepC
variable {n : ℕ} {μ ν : Matching n}
private def rightBackgroundSector (U : Finset (Fin n)) :
    Set (JointSpouseScores μ ν) :=
  {d | (∀ i, if i ∈ U then jointManSpouseScoreRight d i ≤ jointManSpouseScoreLeft d i
      else jointManSpouseScoreLeft d i ≤ jointManSpouseScoreRight d i) ∧
    (n : ℝ) ^ (1 / 10 : ℝ) ≤ jointBackgroundFemaleTotal d ∧
    (∀ i, jointBackgroundWeight d i ≤ backgroundWeightCeiling n) ∧
    ∀ i, jointManSpouseScoreRight d i ≤ backgroundMaleCeiling n}
private theorem measurableSet_rightBackgroundSector (U : Finset (Fin n)) :
    MeasurableSet (rightBackgroundSector (μ := μ) (ν := ν) U) := by
  have hR (i : Fin n) : Measurable (fun d : JointSpouseScores μ ν ↦
      jointManSpouseScoreRight d i) := by unfold jointManSpouseScoreRight; fun_prop
  have hL (i : Fin n) : Measurable (fun d : JointSpouseScores μ ν ↦
      jointManSpouseScoreLeft d i) := by unfold jointManSpouseScoreLeft; fun_prop
  have hOrder : MeasurableSet {d : JointSpouseScores μ ν | ∀ i,
      if i ∈ U then jointManSpouseScoreRight d i ≤ jointManSpouseScoreLeft d i
      else jointManSpouseScoreLeft d i ≤ jointManSpouseScoreRight d i} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ U
    · simpa only [hi, ite_true] using measurableSet_le (hR i) (hL i)
    · simpa only [hi, ite_false] using measurableSet_le (hL i) (hR i)
  have hWeight : MeasurableSet {d : JointSpouseScores μ ν |
      ∀ i, jointBackgroundWeight d i ≤ backgroundWeightCeiling n} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦
      measurableSet_le (measurable_jointBackgroundWeight μ ν i) measurable_const
  have hMale : MeasurableSet {d : JointSpouseScores μ ν |
      ∀ i, jointManSpouseScoreRight d i ≤ backgroundMaleCeiling n} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le (hR i) measurable_const
  exact hOrder.inter ((measurableSet_le measurable_const
    (measurable_jointBackgroundFemaleTotal μ ν)).inter (hWeight.inter hMale))
private theorem split_mem_rightBackgroundSector {x : ScoreProfile n} {U : Finset (Fin n)}
    (ht : ∀ row, Function.Injective (x row))
    (hU : U = worsePartnerMen (profileOfScores x) μ ν)
    (hs : InResidualEndpointScoreDomain x ν) :
    (splitTwoMatchingScores μ ν x).1 ∈ rightBackgroundSector U := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hi := mem_worsePartnerMen_iff_score_lt ht μ ν i
    rw [← hU] at hi
    by_cases hm : i ∈ U
    · simp only [hm, ite_true, jointManSpouseScoreRight_split, jointManSpouseScoreLeft_split]
      exact (hi.mp hm).le
    · simp only [hm, ite_false, jointManSpouseScoreRight_split, jointManSpouseScoreLeft_split]
      exact le_of_not_gt (fun he ↦ hm (hi.mpr he))
  · rw [jointBackgroundFemaleTotal_split]
    exact hs.1
  · intro i
    rw [jointBackgroundWeight_split]
    exact hs.2.2.1 (ν i)
  · intro i
    rw [jointManSpouseScoreRight_split]
    exact hs.2.2.2 i
private theorem eq_worsePartnerMen_of_mem_rightBackgroundSector {x : ScoreProfile n}
    {U V : Finset (Fin n)} (hUV : LabeledPairOrientation μ ν U V)
    (ht : ∀ row, Function.Injective (x row))
    (hs : (splitTwoMatchingScores μ ν x).1 ∈ rightBackgroundSector U) :
    U = worsePartnerMen (profileOfScores x) μ ν := by
  ext i
  rw [mem_worsePartnerMen_iff_score_lt ht μ ν i]
  have hi := hs.1 i
  simp only [jointManSpouseScoreRight_split, jointManSpouseScoreLeft_split] at hi
  by_cases hm : i ∈ U
  · have hne : ν i ≠ μ i := by
      have hh := Equiv.Perm.mem_support.mp
        (hUV.union_support ▸ Finset.mem_union.mpr (Or.inl hm))
      exact Ne.symm ((not_congr ν.symm_apply_eq).mp (show ν.symm (μ i) ≠ i from hh))
    rw [if_pos hm] at hi
    exact iff_of_true hm (lt_of_le_of_ne hi fun he ↦ hne (ht (.inl i) he))
  · rw [if_neg hm] at hi
    exact iff_of_false hm (not_lt_of_ge hi)
theorem measure_backgroundException_le_labeledStablePairMassBound_regular
    {L : ℕ} (hn : 0 < n) (hbudget : BackgroundCycleBudget n L)
    {μ ν : Matching n} {U V : Finset (Fin n)}
    (hUV : LabeledPairOrientation μ ν U V)
    (hValid : ValidPairSizes n (U.card, V.card))
    (hreg : RegularOrientationPair n L (U.card, V.card))
    {E : Set (ScoreProfile n)}
    (hE : ∀ᵐ x ∂continuousScoreLaw n, x ∈ E → IsScoreStable x μ ∧ IsScoreStable x ν ∧
      U = worsePartnerMen (profileOfScores x) μ ν ∧ InResidualEndpointScoreDomain x ν) :
    continuousScoreLaw n (E ∩ backgroundShortCycleException μ ν L) ≤
      ENNReal.ofReal (1200 / Real.log (L : ℝ)) *
        ENNReal.ofReal (labeledStablePairMassBound n U.card V.card) := by
  let D := rightBackgroundSector (μ := μ) (ν := ν) U
  let A : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (splitTwoMatchingScores μ ν x).1 ∈ D}
  have hC : ((jointBackgroundLabels μ ν)ᶜ.card : ℝ) ≤
      2 * n / (Real.log n) ^ 3 := by
    rw [jointBackgroundLabels, commonLabels_compl_eq_relative_support, ← hUV.union_support,
      Finset.card_union_of_disjoint hUV.disjoint, Nat.cast_add]
    simpa only [two_mul, add_div] using add_le_add hreg.2.2.1 hreg.2.2.2
  have hGeom : ∀ᵐ d ∂jointSpouseScoreLaw μ ν, d ∈ D →
      HasJointBackgroundGeometry d L (backgroundMaleCeiling n) := by
    filter_upwards [ae_jointSpouse_thresholds μ ν] with d hd hD
    have hY := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) (1 / 10 : ℝ)).trans_le hD.2.1
    exact ⟨hY, hD.2.2.2, hbudget.arc _ hD.2.1,
      (commonForwardLabelLoss_le_backgroundLabelBudget _ _ hC
        (jointBackgroundWeight_nonneg d hd.2.2.2 hY)
        (sum_jointBackgroundWeight d hY) hD.2.2.1).trans hbudget.label⟩
  have hX : 0 ≤ backgroundMaleCeiling n := by unfold backgroundMaleCeiling; positivity
  have hA : continuousScoreLaw n A ≤
      ENNReal.ofReal (labeledStablePairMassBound n U.card V.card) := by
    apply measure_stablePairSector_le_labeledStablePairMassBound hValid hUV rfl rfl
    filter_upwards [ae_injective_rows n] with x ht hx
    exact ⟨hx.1, hx.2.1, eq_worsePartnerMen_of_mem_rightBackgroundSector hUV ht hx.2.2⟩
  calc
    _ ≤ continuousScoreLaw n (A ∩ backgroundShortCycleException μ ν L) := by
      apply measure_mono_ae
      filter_upwards [ae_injective_rows n, hE] with x ht hEx hx
      obtain ⟨hμ, hν, hU, hs⟩ := hEx hx.1
      exact ⟨⟨hμ, hν, split_mem_rightBackgroundSector ht hU hs⟩, hx.2⟩
    _ ≤ ENNReal.ofReal (1200 / Real.log (L : ℝ)) *
          continuousScoreLaw n A :=
      continuousScoreLaw_inter_backgroundShortCycleException_le μ ν hbudget.cutoff_two
        hbudget.log_cutoff hX
        (measurableSet_rightBackgroundSector U) hGeom
    _ ≤ _ := mul_le_mul_right hA _
end StepC
end

-- TwoStablePairMassSums
section
open Filter Finset MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepC
variable {n : ℕ}
private abbrev LabeledMatchingOrientation (n : ℕ) :=
  (Matching n × Matching n) × (Finset (Fin n) × Finset (Fin n))
private noncomputable def scorePairOrientationSides (x : ScoreProfile n) (μ ν : Matching n) :
    Finset (Fin n) × Finset (Fin n) :=
  (worsePartnerMen (profileOfScores x) μ ν, worsePartnerMen (profileOfScores x) ν μ)
private noncomputable def scorePairOrientationSizes (x : ScoreProfile n) (μ ν : Matching n) : ℕ × ℕ :=
  ((scorePairOrientationSides x μ ν).1.card, (scorePairOrientationSides x μ ν).2.card)
theorem measurableSet_scorePairOrientationSides_eq (μ ν : Matching n)
    (uv : Finset (Fin n) × Finset (Fin n)) :
    MeasurableSet {x : ScoreProfile n | scorePairOrientationSides x μ ν = uv} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | (worsePartnerMen p μ ν, worsePartnerMen p ν μ) = uv})
theorem measurable_scorePairOrientationSizes (μ ν : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ scorePairOrientationSizes x μ ν) :=
  (Measurable.of_discrete (f := fun p : Profile n ↦
    ((worsePartnerMen p μ ν).card, (worsePartnerMen p ν μ).card))).comp
      (measurable_profileOfScores n)
private def scoreFixedOrientationPairEvent (R : ScoreProfile n → Matching n → Matching n → Prop)
    (z : LabeledMatchingOrientation n) : Set (ScoreProfile n) :=
  scoreIncomparablePairEvent R z.1.1 z.1.2 ∩
    {x | scorePairOrientationSides x z.1.1 z.1.2 = z.2}
theorem scoreFixedOrientationPairEvent_data
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    {z : LabeledMatchingOrientation n} {x : ScoreProfile n}
    (hx : x ∈ scoreFixedOrientationPairEvent R z) :
    IsScoreStable x z.1.1 ∧ IsScoreStable x z.1.2 ∧
      z.2.1 = worsePartnerMen (profileOfScores x) z.1.1 z.1.2 ∧
      z.2.2 = worsePartnerMen (profileOfScores x) z.1.2 z.1.1 := by
  have he : scorePairOrientationSides x z.1.1 z.1.2 = z.2 := hx.2
  exact ⟨hx.1.1, hx.1.2.1, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
private noncomputable def scorePairSizeMass (R : ScoreProfile n → Matching n → Matching n → Prop)
    (s : ℕ × ℕ) : ℝ≥0∞ :=
  ∑ μ : Matching n, ∑ ν : Matching n, continuousScoreLaw n
    (scoreIncomparablePairEvent R μ ν ∩ {x | scorePairOrientationSizes x μ ν = s})
theorem scorePairSizeMass_ne_top (R : ScoreProfile n → Matching n → Matching n → Prop)
    (s : ℕ × ℕ) : scorePairSizeMass R s ≠ ⊤ :=
  ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _
private theorem measure_eq_sum_inter_fibers {Ω α : Type*} [MeasurableSpace Ω]
    {m : Measure Ω} {E : Set Ω} {f : Ω → α}
    (hE : MeasurableSet E) (hf : ∀ a, MeasurableSet {x | f x = a}) (s : Finset α)
    (hc : ∀ᵐ x ∂m, x ∈ E → f x ∈ s) :
    m E = ∑ a ∈ s, m (E ∩ {x | f x = a}) := by
  have hu : E =ᵐ[m] ⋃ a ∈ s, E ∩ {x | f x = a} := by
    filter_upwards [hc] with x hx
    apply propext
    change x ∈ E ↔ x ∈ ⋃ a ∈ s, E ∩ {x | f x = a}
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨f x, hx h, h, rfl⟩, fun ⟨_, _, h, _⟩ ↦ h⟩
  rw [measure_congr hu]
  refine measure_biUnion_finset (fun a _ b _ hab ↦ Set.disjoint_left.mpr ?_) fun a _ ↦
    hE.inter (hf a)
  exact fun _ ha hb ↦ hab (ha.2.symm.trans hb.2)
private noncomputable def orientationSupportsOfSizes (n : ℕ) (s : ℕ × ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) := by
  classical
  exact univ.filter fun uv ↦ (uv.1.card, uv.2.card) = s
private noncomputable def fixedOrientationSizeMarks (n : ℕ) (s : ℕ × ℕ) :
    Finset (LabeledMatchingOrientation n) :=
  (univ : Finset (Matching n × Matching n)).product (orientationSupportsOfSizes n s)
private theorem mem_fixedOrientationSizeMarks {z : LabeledMatchingOrientation n} {s : ℕ × ℕ} :
    z ∈ fixedOrientationSizeMarks n s ↔ (z.2.1.card, z.2.2.card) = s := by
  classical
  simp [fixedOrientationSizeMarks, orientationSupportsOfSizes, product_eq_sprod]
private theorem scorePairSizeMass_eq_sum_fixedMarks
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (s : ℕ × ℕ) :
    scorePairSizeMass R s =
      ∑ z ∈ fixedOrientationSizeMarks n s, continuousScoreLaw n
        (scoreFixedOrientationPairEvent R z) := by
  classical
  unfold scorePairSizeMass fixedOrientationSizeMarks
  rw [product_eq_sprod, sum_product, Fintype.sum_prod_type]
  refine sum_congr rfl fun μ _ ↦ sum_congr rfl fun ν _ ↦ ?_
  let E := scoreIncomparablePairEvent R μ ν
  let G := {x | scorePairOrientationSizes x μ ν = s}
  let f (x : ScoreProfile n) := scorePairOrientationSides x μ ν
  have hmG : MeasurableSet G :=
    (measurable_scorePairOrientationSizes μ ν) (measurableSet_singleton s)
  have hc : ∀ᵐ x ∂continuousScoreLaw n, x ∈ E ∩ G → f x ∈ orientationSupportsOfSizes n s :=
    Eventually.of_forall fun x hx ↦ mem_filter.mpr ⟨mem_univ _, hx.2⟩
  rw [measure_eq_sum_inter_fibers ((measurableSet_scoreIncomparablePairEvent hR μ ν).inter hmG)
    (measurableSet_scorePairOrientationSides_eq μ ν) _ hc]
  refine sum_congr rfl fun uv huv ↦ congrArg (continuousScoreLaw n) ?_
  have hsize := (mem_filter.mp huv).2
  ext x
  change (x ∈ E ∧ x ∈ G) ∧ f x = uv ↔ x ∈ E ∧ f x = uv
  refine ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, ?_⟩, h.2⟩⟩
  exact (congrArg (fun uv : Finset (Fin n) × Finset (Fin n) ↦ (uv.1.card, uv.2.card))
    h.2).trans hsize
theorem ae_scoreFixedOrientationPairEvent_labeled
    (R : ScoreProfile n → Matching n → Matching n → Prop) (z : LabeledMatchingOrientation n) :
    ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
      LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2 := by
  filter_upwards [ae_injective_rows n] with x ht hx
  have hs : IsStable (profileOfScores x) z.1.1 :=
    (isStable_profileOfScores_iff ht _).mpr hx.1.1
  have hs' : IsStable (profileOfScores x) z.1.2 :=
    (isStable_profileOfScores_iff ht _).mpr hx.1.2.1
  have h := labeledPairOrientation_of_stable hs hs'
  have he : scorePairOrientationSides x z.1.1 z.1.2 = z.2 := hx.2
  change LabeledPairOrientation z.1.1 z.1.2
    (scorePairOrientationSides x z.1.1 z.1.2).1 (scorePairOrientationSides x z.1.1 z.1.2).2 at h
  rwa [he] at h
private noncomputable def labeledOrientationBin (n : ℕ) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop) :
    Finset (LabeledMatchingOrientation n) := by
  classical
  exact univ.filter fun z ↦
    ∃ h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2,
      z.2.1.card = s.1 ∧ z.2.2.card = s.2 ∧ P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType
theorem mem_labeledOrientationBin {s : ℕ × ℕ} {P T : Multiset ℕ → Prop}
    {z : LabeledMatchingOrientation n} :
    z ∈ labeledOrientationBin n s P T ↔
      ∃ h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2,
        z.2.1.card = s.1 ∧ z.2.2.card = s.2 ∧ P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType := by
  classical
  simp [labeledOrientationBin]
theorem card_labeledOrientationBin (n : ℕ) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop) :
    (labeledOrientationBin n s P T).card = Nat.card (LabeledOrientationPairs n s.1 s.2 P T) := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_labeledOrientationBin)
theorem scorePairSizeMass_eq_sum_labeled
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop)
    (hcycle : ∀ (z : LabeledMatchingOrientation n)
      (h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2),
      ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
        P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType) :
    scorePairSizeMass R s = ∑ z ∈ labeledOrientationBin n s P T,
      continuousScoreLaw n (scoreFixedOrientationPairEvent R z) := by
  rw [scorePairSizeMass_eq_sum_fixedMarks hR]
  symm
  refine sum_subset (fun z hz ↦ ?_) fun z hz hnot ↦ ?_
  · obtain ⟨_, hu, hv, _, _⟩ := mem_labeledOrientationBin.mp hz
    exact mem_fixedOrientationSizeMarks.mpr (Prod.ext hu hv)
  have hsize := mem_fixedOrientationSizeMarks.mp hz
  rw [measure_eq_zero_iff_ae_notMem]
  by_cases h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2
  · filter_upwards [hcycle z h] with x hx he
    exact hnot (mem_labeledOrientationBin.mpr
      ⟨h, congrArg Prod.fst hsize, congrArg Prod.snd hsize, hx he⟩)
  · filter_upwards [ae_scoreFixedOrientationPairEvent_labeled R z] with x hx he
    exact h (hx he)
theorem scorePairSizeMass_le_card_mul
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop)
    (hcycle : ∀ (z : LabeledMatchingOrientation n)
      (h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2),
      ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
        P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType)
    {U : ℝ≥0∞}
    (hU : ∀ z : LabeledOrientationPairs n s.1 s.2 P T,
      continuousScoreLaw n (scoreFixedOrientationPairEvent R z.val) ≤ U) :
    scorePairSizeMass R s ≤ (Nat.card (LabeledOrientationPairs n s.1 s.2 P T) : ℝ≥0∞) * U := by
  rw [scorePairSizeMass_eq_sum_labeled hR s P T hcycle]
  calc
    _ ≤ ∑ _z ∈ labeledOrientationBin n s P T, U :=
      sum_le_sum fun z hz ↦ hU ⟨z, mem_labeledOrientationBin.mp hz⟩
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_labeledOrientationBin]
theorem forcedCycleTypeCoverage_of_scoreForcedException
    {R : ScoreProfile n → Matching n → Matching n → Prop} (L : ℕ)
    (hrare : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν →
        ((forcedShortCycles (profileOfScores x) μ ν L).card : ℝ) <
          (9 / 10 : ℝ) * Real.log (L : ℝ))
    (z : LabeledMatchingOrientation n) (h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2) :
    ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
      forcedShortCycleTypeException L h.leftPerm.cycleType ∧ True := by
  rcases z with ⟨⟨μ, ν⟩, U, V⟩
  filter_upwards [hrare μ ν] with x hx he
  obtain ⟨_, _, hU, hV⟩ := scoreFixedOrientationPairEvent_data he
  change U = worsePartnerMen (profileOfScores x) μ ν at hU
  change V = worsePartnerMen (profileOfScores x) ν μ at hV
  subst U V
  exact ⟨(forcedShortCycleTypeException_leftPerm_iff L h).mpr (hx he.1), trivial⟩
theorem scorePairSizeMass_le_add
    {R R₁ R₂ : ScoreProfile n → Matching n → Matching n → Prop} (s : ℕ × ℕ)
    (hcover : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν → scorePairOrientationSizes x μ ν = s →
        R₁ x μ ν ∨ R₂ x μ ν) :
    scorePairSizeMass R s ≤ scorePairSizeMass R₁ s + scorePairSizeMass R₂ s := by
  unfold scorePairSizeMass
  rw [← sum_add_distrib]
  refine sum_le_sum fun μ _ ↦ ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun ν _ ↦ ?_
  refine le_trans (measure_mono_ae ?_) (measure_union_le _ _)
  filter_upwards [hcover μ ν] with x hx he
  obtain ⟨he, hs⟩ := he
  rcases hx he hs with h | h
  · exact Or.inl ⟨⟨he.1, he.2.1, he.2.2.1, h⟩, hs⟩
  · exact Or.inr ⟨⟨he.1, he.2.1, he.2.2.1, h⟩, hs⟩
theorem scorePairSizeMass_toReal_le_add
    {R R₁ R₂ : ScoreProfile n → Matching n → Matching n → Prop} (s : ℕ × ℕ)
    (hcover : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν → scorePairOrientationSizes x μ ν = s →
        R₁ x μ ν ∨ R₂ x μ ν) :
    (scorePairSizeMass R s).toReal ≤ (scorePairSizeMass R₁ s).toReal +
      (scorePairSizeMass R₂ s).toReal := by
  rw [← ENNReal.toReal_add (scorePairSizeMass_ne_top R₁ s) (scorePairSizeMass_ne_top R₂ s)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨scorePairSizeMass_ne_top R₁ s, scorePairSizeMass_ne_top R₂ s⟩)
    (scorePairSizeMass_le_add s hcover)
private noncomputable def validPairSizeFinset (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((range (n + 1)).product (range (n + 1))).filter (ValidPairSizes n)
@[simp] theorem mem_validPairSizeFinset {s : ℕ × ℕ} :
    s ∈ validPairSizeFinset n ↔ ValidPairSizes n s := by
  classical
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    have hs := h.2.2
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega),
      mem_range.mpr (by omega)⟩, h⟩
private theorem two_le_finsetCard_of_fixedPointFree {α : Type*} {s : Finset α}
    (hs : s.Nonempty) (f : Equiv.Perm s) (hf : ∀ i, f i ≠ i) : 2 ≤ s.card := by
  obtain ⟨i, hi⟩ := hs
  exact one_lt_card.mpr ⟨(f ⟨i, hi⟩).val, (f ⟨i, hi⟩).property, i, hi,
    fun h ↦ hf _ (Subtype.ext h)⟩
private theorem worsePartnerMen_nonempty_of_not_menWeaklyPrefer {p : Profile n} {μ ν : Matching n}
    (h : ¬ MenWeaklyPrefer p μ ν) : (worsePartnerMen p μ ν).Nonempty := by
  by_contra h0
  apply h
  intro m
  exact le_of_not_gt fun hm ↦ h0 ⟨m, mem_filter.mpr ⟨mem_univ _, hm⟩⟩
theorem LabeledPairOrientation.validPairSizes_of_nonempty {μ ν : Matching n}
    {U V : Finset (Fin n)} (h : LabeledPairOrientation μ ν U V)
    (hU : U.Nonempty) (hV : V.Nonempty) : ValidPairSizes n (U.card, V.card) := by
  refine ⟨two_le_finsetCard_of_fixedPointFree hU h.leftPerm h.leftPerm_apply_ne,
    two_le_finsetCard_of_fixedPointFree hV h.rightPerm h.rightPerm_apply_ne, ?_⟩
  rw [← card_union_of_disjoint h.disjoint, h.union_support]
  exact (card_le_univ _).trans_eq (Fintype.card_fin n)
theorem ae_validPairSizes_of_scoreIncomparablePairEvent
    (R : ScoreProfile n → Matching n → Matching n → Prop) (μ ν : Matching n) :
    ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreIncomparablePairEvent R μ ν →
      ValidPairSizes n (scorePairOrientationSizes x μ ν) := by
  filter_upwards [ae_injective_rows n] with x ht hx
  have h := labeledPairOrientation_of_stable
    ((isStable_profileOfScores_iff ht μ).mpr hx.1)
    ((isStable_profileOfScores_iff ht ν).mpr hx.2.1)
  exact h.validPairSizes_of_nonempty
    (worsePartnerMen_nonempty_of_not_menWeaklyPrefer hx.2.2.1.1)
    (worsePartnerMen_nonempty_of_not_menWeaklyPrefer hx.2.2.1.2)
theorem scorePairMass_eq_sum_sizeMass
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (S : Finset (ℕ × ℕ))
    (hS : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν → scorePairOrientationSizes x μ ν ∈ S) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      continuousScoreLaw n (scoreIncomparablePairEvent R μ ν)) =
        ∑ s ∈ S, scorePairSizeMass R s := by
  let g (μ ν : Matching n) (s : ℕ × ℕ) :=
    continuousScoreLaw n (scoreIncomparablePairEvent R μ ν ∩
      {x | scorePairOrientationSizes x μ ν = s})
  calc
    _ = ∑ μ : Matching n, ∑ ν : Matching n, ∑ s ∈ S, g μ ν s := by
      refine sum_congr rfl fun μ _ ↦ sum_congr rfl fun ν _ ↦ ?_
      exact measure_eq_sum_inter_fibers (measurableSet_scoreIncomparablePairEvent hR μ ν)
        (fun s ↦ (measurable_scorePairOrientationSizes μ ν) (measurableSet_singleton s))
        S (hS μ ν)
    _ = ∑ μ : Matching n, ∑ s ∈ S, ∑ ν : Matching n, g μ ν s :=
      sum_congr rfl fun _ _ ↦ sum_comm
    _ = _ := sum_comm
theorem scorePairMass_real_eq_sum_sizeMass
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (S : Finset (ℕ × ℕ))
    (hS : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν → scorePairOrientationSizes x μ ν ∈ S) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      (continuousScoreLaw n).real (scoreIncomparablePairEvent R μ ν)) =
        ∑ s ∈ S, (scorePairSizeMass R s).toReal := by
  have h := congrArg ENNReal.toReal (scorePairMass_eq_sum_sizeMass hR S hS)
  rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _),
    ENNReal.toReal_sum (fun s _ ↦ scorePairSizeMass_ne_top R s)] at h
  simp_rw [ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)] at h
  exact h
theorem scorePairMass_real_eq_sum_validPairSizeMass
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      (continuousScoreLaw n).real (scoreIncomparablePairEvent R μ ν)) =
        ∑ s ∈ validPairSizeFinset n, (scorePairSizeMass R s).toReal :=
  scorePairMass_real_eq_sum_sizeMass hR _ fun μ ν ↦
    (ae_validPairSizes_of_scoreIncomparablePairEvent R μ ν).mono fun _ hx he ↦
      mem_validPairSizeFinset.mpr (hx he)
end StepC
end

-- TwoStablePairPerSizeBounds
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal
namespace StepC
variable {n : ℕ}
private theorem factorialEnvelope_mul_labeledMass {u v : ℕ}
    (hs : ValidPairSizes n (u, v)) :
    ((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        ENNReal.ofReal (labeledStablePairMassBound n u v) =
      ENNReal.ofReal (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v)) := by
  have he : (n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial =
      ENNReal.ofReal ((n.factorial : ℝ) ^ 2 / (n - u - v).factorial) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [he, ← ENNReal.ofReal_mul (by positivity), labeledStablePairMassBound_mul_factorials hs]
private theorem scorePairSizeMass_toReal_le_of_envelope
    {R : ScoreProfile n → Matching n → Matching n → Prop} {u v : ℕ}
    (hs : ValidPairSizes n (u, v)) {a : ℝ} (ha : 0 ≤ a)
    (h : scorePairSizeMass R (u, v) ≤ ENNReal.ofReal a *
      (((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        ENNReal.ofReal (labeledStablePairMassBound n u v))) :
    (scorePairSizeMass R (u, v)).toReal ≤
      a * (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v)) := by
  rw [factorialEnvelope_mul_labeledMass hs, ← ENNReal.ofReal_mul ha] at h
  have hlog := Real.log_natCast_nonneg n
  have hk := twoStablePairSizeKernel_nonneg n (u, v)
  have hn : 0 ≤ a * (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v)) := by
    positivity
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hn)
private theorem scoreFixedOrientationPairEvent_le_labeledMass
    {R : ScoreProfile n → Matching n → Matching n → Prop} {u v : ℕ}
    (hs : ValidPairSizes n (u, v)) {P T : Multiset ℕ → Prop}
    (z : LabeledOrientationPairs n u v P T) :
    continuousScoreLaw n (scoreFixedOrientationPairEvent R z.val) ≤
      ENNReal.ofReal (labeledStablePairMassBound n u v) := by
  obtain ⟨hor, hu, hv, _, _⟩ := z.property
  apply measure_stablePairSector_le_labeledStablePairMassBound hs hor hu hv
  exact Eventually.of_forall fun _ hx ↦
    ⟨(scoreFixedOrientationPairEvent_data hx).1, (scoreFixedOrientationPairEvent_data hx).2.1,
      (scoreFixedOrientationPairEvent_data hx).2.2.1⟩
theorem scorePairSizeMass_toReal_le_kernel
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) {s : ℕ × ℕ} (hs : ValidPairSizes n s) :
    (scorePairSizeMass R s).toReal ≤
      Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n s := by
  rcases s with ⟨u, v⟩
  have h := scorePairSizeMass_le_card_mul hR (u, v) (fun _ ↦ True) (fun _ ↦ True)
    (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ ⟨trivial, trivial⟩)
    (scoreFixedOrientationPairEvent_le_labeledMass hs)
  have hcount := card_labeledOrientationPairs_unrestricted_le hs.2.2
  have hmass := h.trans (mul_le_mul_left hcount _)
  exact (scorePairSizeMass_toReal_le_of_envelope hs (a := 1) zero_le_one
    (by simpa only [ENNReal.ofReal_one, one_mul] using hmass)).trans_eq (one_mul _)
theorem scorePairSizeMass_toReal_le_forced
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) {s : ℕ × ℕ} (hs : ValidPairSizes n s)
    {L : ℕ} (hL : 2 ≤ L) (hu : L ≤ s.1) (hlog : 100 ≤ Real.log (L : ℝ)) :
    (scorePairSizeMass (fun x μ ν ↦ R x μ ν ∧ x ∈ forcedShortCycleException μ ν L) s).toReal ≤
      (400 / Real.log (L : ℝ)) *
        (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n s) := by
  rcases s with ⟨u, v⟩
  let Q : ScoreProfile n → Matching n → Matching n → Prop :=
    fun x μ ν ↦ R x μ ν ∧ x ∈ forcedShortCycleException μ ν L
  have hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν} := fun μ ν ↦
    (hR μ ν).inter (measurableSet_forcedShortCycleException μ ν L)
  have hcycle := forcedCycleTypeCoverage_of_scoreForcedException (R := Q) L (fun _ _ ↦
    Eventually.of_forall fun _ hx ↦ hx.2.2.2.2)
  have h := scorePairSizeMass_le_card_mul hQ (u, v)
    (forcedShortCycleTypeException L) (fun _ ↦ True) hcycle
    (scoreFixedOrientationPairEvent_le_labeledMass hs)
  have hcount := card_labeledOrientationPairs_forcedShortException_le hs.2.2 hL hu hlog
  have hfactor : 0 ≤ (400 : ℝ) / Real.log (L : ℝ) := by
    exact div_nonneg (by norm_num) (by linarith)
  apply scorePairSizeMass_toReal_le_of_envelope hs hfactor
  exact (h.trans (mul_le_mul_left hcount _)).trans_eq (by ac_rfl)
theorem scorePairSizeMass_toReal_le_background_regular
    {L : ℕ} (hn : 0 < n) (hbudget : BackgroundCycleBudget n L)
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν})
    (hdom : ∀ x μ ν, R x μ ν → InResidualEndpointScoreDomain x ν)
    {s : ℕ × ℕ} (hs : ValidPairSizes n s) (hreg : RegularOrientationPair n L s) :
    (scorePairSizeMass
      (fun x μ ν ↦ R x μ ν ∧ x ∈ backgroundShortCycleException μ ν L) s).toReal ≤
      (1200 / Real.log (L : ℝ)) *
        (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n s) := by
  rcases s with ⟨u, v⟩
  let Q : ScoreProfile n → Matching n → Matching n → Prop :=
    fun x μ ν ↦ R x μ ν ∧ x ∈ backgroundShortCycleException μ ν L
  have hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν} := fun μ ν ↦
    (hR μ ν).inter (measurableSet_backgroundShortCycleException μ ν L)
  let a := (1200 : ℝ) / Real.log (L : ℝ)
  have hfixed (z : LabeledOrientationPairs n u v (fun _ ↦ True) (fun _ ↦ True)) :
      continuousScoreLaw n (scoreFixedOrientationPairEvent Q z.val) ≤
        ENNReal.ofReal a * ENNReal.ofReal (labeledStablePairMassBound n u v) := by
    obtain ⟨hor, hu, hv, _, _⟩ := z.property
    let E := scoreFixedOrientationPairEvent R z.val
    have hsub : scoreFixedOrientationPairEvent Q z.val ⊆ E ∩
        backgroundShortCycleException z.val.1.1 z.val.1.2 L := by
      intro x hx
      exact ⟨⟨⟨hx.1.1, hx.1.2.1, hx.1.2.2.1, hx.1.2.2.2.1⟩, hx.2⟩, hx.1.2.2.2.2⟩
    refine (measure_mono hsub).trans ?_
    have h := measure_backgroundException_le_labeledStablePairMassBound_regular hn hbudget hor
      (by simpa only [hu, hv] using hs)
      (by simpa only [hu, hv] using hreg) (E := E) (Eventually.of_forall fun _ hx ↦
        ⟨(scoreFixedOrientationPairEvent_data hx).1, (scoreFixedOrientationPairEvent_data hx).2.1,
          (scoreFixedOrientationPairEvent_data hx).2.2.1, hdom _ _ _ hx.1.2.2.2⟩)
    simpa only [hu, hv] using h
  have h := scorePairSizeMass_le_card_mul hQ (u, v) (fun _ ↦ True) (fun _ ↦ True)
    (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ ⟨trivial, trivial⟩) hfixed
  have hcount := card_labeledOrientationPairs_unrestricted_le hs.2.2
  have ha : 0 ≤ a := div_nonneg (by norm_num) (by have := hbudget.log_cutoff; linarith)
  apply scorePairSizeMass_toReal_le_of_envelope hs ha
  exact (h.trans (mul_le_mul_left hcount _)).trans_eq (mul_left_comm _ _ _)
end StepC
end

-- PivotPairEnvelopeBounds
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators
namespace StepC
variable {n : ℕ}
theorem sum_residualPairMass_le_regularOrientation {n L : ℕ} (hn : 0 < n)
    (hbudget : BackgroundCycleBudget n L) (hLt : (L : ℝ) ≤ Real.log n) (b : ℝ) (K : ℕ) :
    (∑ μ : Matching n, ∑ ν : Matching n, (continuousScoreLaw n).real
      (scoreIncomparablePairEvent (IsResidualPairGeometry b K L) μ ν)) ≤
      (Real.exp 72 * (1 + Real.log n)) *
        (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log (Real.log n)) +
          (1600 / Real.log (L : ℝ)) * ((n : ℝ) ^ 2 * (1 + Real.log n))) := by
  classical
  let R := IsResidualPairGeometry (n := n) b K L
  let w (s : ℕ × ℕ) := (scorePairSizeMass R s).toReal
  let S := validPairSizeFinset n
  let G := S.filter (RegularOrientationPair n L)
  let J := S.filter fun s ↦ ¬ RegularOrientationPair n L s
  have hR (μ ν : Matching n) : MeasurableSet {x | R x μ ν} :=
    measurableSet_isResidualPairGeometry b K L μ ν
  have hG (s : ℕ × ℕ) (hs : s ∈ G) : ValidPairSizes n s :=
    mem_validPairSizeFinset.mp (Finset.mem_filter.mp hs).1
  have hJ (s : ℕ × ℕ) (hs : s ∈ J) : ValidPairSizes n s :=
    mem_validPairSizeFinset.mp (Finset.mem_filter.mp hs).1
  have hgood (s : ℕ × ℕ) (hs : s ∈ G) :
      w s ≤ (Real.exp 72 * (1600 / Real.log (L : ℝ))) *
        (1 + Real.log n) * twoStablePairSizeKernel n s := by
    have hreg := (Finset.mem_filter.mp hs).2
    have hcut : L ≤ s.1 := hreg.1
    have hf := scorePairSizeMass_toReal_le_forced hR (hG s hs) hbudget.cutoff_two hcut
      hbudget.log_cutoff
    have hb := scorePairSizeMass_toReal_le_background_regular hn hbudget hR
      (fun _ _ _ h ↦ h.late_scores) (hG s hs) hreg
    calc
      _ ≤ (scorePairSizeMass (fun x μ ν ↦ R x μ ν ∧ x ∈ forcedShortCycleException μ ν L) s).toReal +
          (scorePairSizeMass
            (fun x μ ν ↦ R x μ ν ∧ x ∈ backgroundShortCycleException μ ν L) s).toReal := by
        apply scorePairSizeMass_toReal_le_add
        intro μ ν
        exact Eventually.of_forall fun x hx _ ↦
          (scoreResidualPairEvent_subset_shortCycleExceptions hbudget.cutoff_two μ ν hx).imp
            (fun h ↦ ⟨hx.2.2.2, h⟩) (fun h ↦ ⟨hx.2.2.2, h⟩)
      _ ≤ _ := (add_le_add hf hb).trans_eq (by ring)
  have hreg_sum : (∑ s ∈ G, w s) ≤
      (Real.exp 72 * (1 + Real.log n)) *
        ((1600 / Real.log (L : ℝ)) * ((n : ℝ) ^ 2 * (1 + Real.log n))) := by
    have hlog : 0 ≤ Real.log (L : ℝ) := by linarith [hbudget.log_cutoff]
    calc
      _ ≤ (Real.exp 72 * (1600 / Real.log (L : ℝ))) *
            (1 + Real.log n) * ((n : ℝ) ^ 2 * (1 + Real.log n)) :=
        sum_twoStablePairSizeWeights_le hn G w (by positivity) hgood
          (sum_twoStablePairSizeKernel_le_total hn G hG)
      _ = _ := by ring
  have ht : 1 ≤ Real.log (n : ℝ) :=
    (Nat.one_le_cast.mpr (Nat.le_trans (by decide : 1 ≤ 2) hbudget.cutoff_two)).trans hLt
  have hirreg_sum : (∑ s ∈ J, w s) ≤
      (Real.exp 72 * (1 + Real.log n)) * (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log (Real.log n))) :=
    sum_twoStablePairSizeWeights_le hn J w (Real.exp_pos 72).le
      (fun s hs ↦ scorePairSizeMass_toReal_le_kernel hR (hJ s hs))
      (sum_twoStablePairSizeKernel_le_not_regularOrientationPair ht hLt J hJ
        (fun s hs ↦ (Finset.mem_filter.mp hs).2))
  rw [scorePairMass_real_eq_sum_validPairSizeMass hR]
  change (∑ s ∈ S, w s) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S (RegularOrientationPair n L)]
  exact (add_le_add hreg_sum hirreg_sum).trans_eq (by ring)
end StepC
end

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 30000 in
theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H3_R1.H1 := by
  intro n L hn hbudget hLt b K
  exact StepC.sum_residualPairMass_le_regularOrientation hn hbudget hLt b K
