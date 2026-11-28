import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H3_R1
import Mathlib

/-! Port of part of the Lennon-Pittel lower-tail proof by Bo Cowgill,
https://github.com/bocowgill/lennon-pittel at commit cf950d0596591bba912b1568aa394f99986f8191,
Copyright 2026 Bo Cowgill, used under the Apache License 2.0.
Changes: modules flattened into one file, comments removed, declarations not needed here dropped,
names adapted to the pinned Mathlib, the marked model renamed and tied to the parent reduction's
definitions (after moon-4's port of the same model for the parent step).
This step is the source theorem eventually_logarithmic_cycle_budget. -/


-- IidScoreRanks
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace StepD
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
end StepD
end

-- MarkedCounting
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepD
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype A] [Nonempty A]
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
end StepD
end

-- ScoreRanks
section
open Function MeasureTheory Set
namespace StepD
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
private abbrev ScoreProfile (n : ℕ) := (Fin n ⊕ Fin n) → Fin n → ℝ
private noncomputable def profileOfScores {n : ℕ} (x : ScoreProfile n) : StableMarriage.Profile n :=
  ⟨fun m ↦ rankPermutation (x (.inl m)), fun w ↦ rankPermutation (x (.inr w))⟩
end StepD
end

-- ContinuousScoreBridge
section
open scoped BigOperators ENNReal StepD
open MeasureTheory Set
namespace StepD
end StepD
end

-- CoexposureGoodScores
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal StepD
namespace StepD
variable {n : ℕ}
private def maleSpouseScore (x : ScoreProfile n) (μ : Matching n) (i : Fin n) : ℝ :=
  x (.inl i) (μ i)
private def femaleSpouseScore (x : ScoreProfile n) (μ : Matching n) (j : Fin n) : ℝ :=
  x (.inr j) (μ.symm j)
private def femaleSpouseTotal (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ j, femaleSpouseScore x μ j
end StepD
end

-- CoexposureScoreEstimates
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepD
end StepD
end

-- PittelSimplexRadial
section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace StepD
end StepD
end

-- CoexposureScoreRow
section
open Set
open scoped BigOperators
namespace StepD
variable {ι : Type*}
section FiniteRows
variable [Fintype ι] [DecidableEq ι]
end FiniteRows
section SuccessorMass
open MeasureTheory
open scoped ENNReal
end SuccessorMass
end StepD
end

-- ExposedRotations
section
open StableMarriage
namespace StepD
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
end StepD
end

-- CoexposureScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
private abbrev ScorePairIndex (n : ℕ) := Fin n × Fin n
private abbrev DiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 = q.2} → ℝ × ℝ
private abbrev OffDiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2} → ℝ × ℝ
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
private def splitScorePairs {n : ℕ} (μ : Matching n) :
    ScoreProfile n ≃ᵐ DiagonalScorePairs n × OffDiagonalScorePairs n :=
  (scorePairEquiv μ).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      fun q ↦ q.1 = q.2)
private def diagonalPairAt {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ × ℝ :=
  d ⟨(i,i), rfl⟩
end StepD
end

-- CoexposureSpouseMarginal
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepD
end StepD
end

-- FiniteProductDensity
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepD
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
end StepD
end

-- PivotSpouseProductLower
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepD
end StepD
end

-- PivotForwardRevealCell
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepD
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
end StepD
end

-- ReverseSuccessorRotation
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
private def swapProfile (p : Profile n) : Profile n :=
  ⟨p.womanRank, p.manRank⟩
end StepD
end

-- FinitePrerequisites
section
namespace StepD
end StepD
end

-- RotationDiamond
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}
end StepD
end

-- ManOptimal
section
open StableMarriage
open scoped BigOperators
namespace StepD
variable {n : ℕ}
private def MenWeaklyPrefer (p : Profile n) (μ ν : Matching n) : Prop :=
  ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)
private def IsManOptimal (p : Profile n) (μ : Matching n) : Prop :=
  IsStable p μ ∧ ∀ ν, IsStable p ν → MenWeaklyPrefer p μ ν
end StepD
end

-- RotationCycle
section
namespace StepD
open Function
end StepD
end

-- TargetSuccessor
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
end StepD
end

-- RotationReachability
section
open scoped BigOperators
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n}
private inductive RotationSequence (p : Profile n) :
    Matching n → List (Equiv.Perm (Fin n)) → Matching n → Prop where
  | nil {μ : Matching n} (hμ : IsStable p μ) : RotationSequence p μ [] μ
  | cons {μ ν : Matching n} {ρ : Equiv.Perm (Fin n)} {rs : List (Equiv.Perm (Fin n))}
      (hμ : IsStable p μ) (hρ : IsExposedRotation p μ ρ)
      (rest : RotationSequence p (eliminateRotation μ ρ) rs ν) :
      RotationSequence p μ (ρ :: rs) ν
end StepD
end

-- RotationLabels
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n}
private structure RotationLabel (n : ℕ) where
  cycle : Equiv.Perm (Fin n)
  oldPartner : Fin n → Option (Fin n)
private def rotationLabel (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : RotationLabel n :=
  ⟨ρ, fun m ↦ if ρ m = m then none else some (μ m)⟩
private def rotationLabels : Matching n → List (Equiv.Perm (Fin n)) → List (RotationLabel n)
  | _, [] => []
  | μ, ρ :: rs => rotationLabel μ ρ :: rotationLabels (eliminateRotation μ ρ) rs
end StepD
end

-- RotationPathIndependence
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n}
end StepD
end

-- RotationTrace
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n}
namespace RotationSequence
variable {μ ν τ : Matching n} {rs ss : List (Equiv.Perm (Fin n))}
end RotationSequence
end StepD
end

-- RotationIdeals
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
private def Rotation (p : Profile n) (μ₀ : Matching n) :=
  {r : RotationLabel n // ∃ ν rs, RotationSequence p μ₀ rs ν ∧ r ∈ rotationLabels μ₀ rs}
end StepD
end

-- CoexposedRotations
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
end StepD
end

-- CoexposureCycleMoment
section
open StableMarriage MeasureTheory
open scoped BigOperators ENNReal
namespace StepD
private def RealizesSuccessorPermutation {n : ℕ} (p : Profile n) (M σ : Matching n) : Prop :=
  ∀ i ∈ σ.support, IsSuccessor p M i (M (σ i))
end StepD
end

-- RowCompetition
section
open Set
open scoped BigOperators
namespace StepD
variable {ι : Type*} {J : Finset ι} {a : ι → ℝ} {A b : ℝ}
end StepD
end

-- ReverseIIDLabelGood
section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StepD
section Measures
variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
variable [Fintype α] [DiscreteMeasurableSpace α]
end Measures
end StepD
end

-- PivotReverseMaskLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
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
end StepD
end

-- PivotReverseCompetitorMass
section
open StableMarriage
open scoped BigOperators ENNReal
namespace StepD
end StepD
end

-- PivotForwardMaskProbability
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepD
end StepD
end

-- PivotForwardRevealRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepD
private abbrev ForwardRevealedMaleScores {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  ForwardActiveCellIndex flag → ℝ
private abbrev ForwardInactiveColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  (i : Fin n) → ForwardInactiveColumnIndex flag i → ℝ × ℝ
private def forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    OffDiagonalScorePairs n → ForwardRevealedMaleScores flag × ForwardInactiveColumns flag :=
  Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag
end StepD
end

-- PivotForwardPivotReadout
section
open MeasureTheory Set StableMarriage
namespace StepD
end StepD
end

-- SingletonIdealAnchor
section
namespace StepD
variable {α : Type*} [PartialOrder α]
end StepD
end

-- SingletonRotationAnchor
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
end StepD
end

-- UndoableRotations
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
end StepD
end

-- ReverseRotationIdeals
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ : Equiv.Perm (Fin n)}
private def undoReverseRotation (ν : Matching n) (σ : Equiv.Perm (Fin n)) : Matching n :=
  (eliminateRotation ν.symm σ).symm
end StepD
end

-- PivotCrossBlocker
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}
end StepD
end

-- PivotReversePermutationCompatibility
section
open StableMarriage
namespace StepD
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
end StepD
end

-- UndoMaximalSubset
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n}
end StepD
end

-- PivotIdealExposure
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
end StepD
end

-- ReverseRotationPersistence
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ τ : Equiv.Perm (Fin n)}
end StepD
end

-- RotationUndoSequences
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {hopt : IsManOptimal p μ₀}
end StepD
end

-- PivotIncidenceCounting
section
open StableMarriage
open scoped BigOperators
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ ν μ : Matching n} {hopt : IsManOptimal p μ₀}
namespace PivotDecoration
variable {K : ℕ} {r : Rotation p μ₀}
end PivotDecoration
end StepD
end

-- PivotReversePermutationDecoration
section
open StableMarriage
open scoped BigOperators
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n}
end StepD
end

-- PivotCompatibleLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
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
end StepD
end

-- PivotReverseIncrementFilter
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
private def reverseScoreIncrement {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (w j : Fin n) : ℝ := x (.inr w) j - x (.inr w) (μ.symm w)
private noncomputable def reverseIncrementCutoff (n : ℕ) (X : ℝ) : ℝ := 16 * Real.log (n : ℝ) / X
end StepD
end

-- PivotReverseFilteredCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
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
end StepD
end

-- ShortCycleChebyshev
section
open scoped BigOperators ENNReal
namespace StepD
end StepD
end

-- UniformShortCycleMoments
section
open Equiv Equiv.Perm
open scoped BigOperators
namespace StepD
variable {α : Type*} [Fintype α] [DecidableEq α]
end StepD
end

-- PivotScoreLock
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
end StepD
end

-- PivotForwardExposureReveal
section
open MeasureTheory Set StableMarriage
namespace StepD
end StepD
end

-- PivotPairToggle
section
open StableMarriage
open scoped BigOperators
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n} {hopt : IsManOptimal p μ₀}
  {K : ℕ} {r : Rotation p μ₀}
namespace PivotDecoration
end PivotDecoration
namespace ResidualPivotPair
end ResidualPivotPair
end StepD
end

-- PivotFilteredDecoration
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
variable {n : ℕ} {x : ScoreProfile n} {μ₀ : Matching n}
  {hopt : IsManOptimal (profileOfScores x) μ₀} {K : ℕ}
  {r : Rotation (profileOfScores x) μ₀}
end StepD
end

-- PivotEligibleRevealControls
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
private def reverseDiagonalMaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).1
namespace ReverseMaskGeometry
variable {n : ℕ} {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
  {μ ρ : Matching n} {s u p : ℝ}
end ReverseMaskGeometry
end StepD
end

-- PivotSpouseBandMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
private def pivotDiagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).2
private def pivotBaseDiagonalBand (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | let X := reverseDiagonalMaleTotal d
       let Y := pivotDiagonalFemaleTotal d
       (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
       2 ≤ Y ∧ Y ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧ (n : ℝ) / 128 ≤ X * Y ∧
       (∀ i, (diagonalPairAt d i).2 / Y ≤ 12 * Real.log n / n) ∧
       ∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (Y - 1)}
end StepD
end

-- ForestDeterministic
section
open scoped BigOperators Classical
namespace StepD
end StepD
end

-- ForwardSuccessorRowLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
end StepD
end

-- ForwardSuccessorOutcome
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
end StepD
end

-- PivotForwardRowDeficit
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepD
end StepD
end

-- PivotForwardForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
private def IsSoleForwardExposedRotation {n : ℕ} (p : Profile n) (μ σ : Matching n) : Prop :=
  IsExposedRotation p μ σ ∧ ∀ τ, IsExposedRotation p μ τ → τ = σ
end StepD
end

-- PivotLocalEligibility
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepD
end StepD
end

-- PivotMarkedDecorationCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
variable {n : ℕ}
private noncomputable def markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun σ ↦ σ.support.card ≤ K ∧
    σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x
section MatchingEndpoints
variable {x : ScoreProfile n} {μ₀ μ ρ σ : Matching n}
  {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
end MatchingEndpoints
end StepD
end

-- PivotSharedReverse
section
open StableMarriage
namespace StepD
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n}
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
end ResidualMarkedPair
end GlobalMarkedPairs
end StepD
end

-- PivotResidualImageGeometry
section
open Filter MeasureTheory Set StableMarriage
open scoped Topology
namespace StepD
variable {n : ℕ}
private def InResidualEndpointScoreDomain (x : ScoreProfile n) (μ : Matching n) : Prop :=
  (n : ℝ) ^ (1 / 10 : ℝ) ≤ femaleSpouseTotal x μ ∧
  femaleSpouseTotal x μ ≤ 2 * (n : ℝ) ^ (2 / 5 : ℝ) ∧
  (∀ w, femaleSpouseScore x μ w / femaleSpouseTotal x μ ≤ 2060 * Real.log n / n) ∧
  ∀ m, maleSpouseScore x μ m ≤ 16 * Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)
namespace IsResidualPairRankGeometry
variable {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n}
end IsResidualPairRankGeometry
namespace ResidualPivotPair
variable {p : Profile n} {μ₀ : Matching n} {K : ℕ} {hopt : IsManOptimal p μ₀}
end ResidualPivotPair
namespace ResidualMarkedPair
variable {x : ScoreProfile n} {μ₀ : Matching n} {K L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}
end ResidualMarkedPair
end StepD
end

-- DeferredAcceptanceTranscript
section
open StableMarriage
open scoped BigOperators
namespace StepD
namespace DAState
variable {n : ℕ}
end DAState
end StepD
end

-- DAStreamSimulation
section
open StableMarriage
namespace StepD
namespace DAStreamState
variable {n T : ℕ}
end DAStreamState
end StepD
end

-- CycleSupportCount
section
open Equiv.Perm Finset
open scoped BigOperators Classical
namespace StepD
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end StepD
end

-- PivotAggregateMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepD
variable {n : ℕ}
end StepD
end

-- PivotDecorationRevealInvariance
section
open MeasureTheory Set StableMarriage
namespace StepD
variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}
private structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2
theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩
end StepD
end

-- PivotLaterRevealReplay
section
open MeasureTheory Set StableMarriage
namespace StepD
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
end StepD
end

-- PivotMovedCenteredTest
section
open Filter MeasureTheory Set StableMarriage
namespace StepD
variable {n : ℕ}
end StepD
end

-- PivotComparableCentered
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
end StepD
end

-- PivotCenteredReduction
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepD
variable {n : ℕ}
namespace PivotCountParameters
end PivotCountParameters
end StepD
end

-- PivotResidualCountBridge
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepD
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
end StepD
end

-- PivotIncomparableScoreCount
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepD
variable {n : ℕ}
namespace PivotCountParameters
end PivotCountParameters
end StepD
end

-- PivotTwoCycleForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
end StepD
end

-- CommonForwardCycleMoments
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepD
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
section RowLaws
variable [MeasurableSpace (Option ι)]
variable [MeasurableSingletonClass (Option ι)]
end RowLaws
section ReferenceWeights
end ReferenceWeights
section NearRankOne
variable [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
end NearRankOne
end StepD
end

-- TwoStablePairSizeSums
section
open Finset
namespace StepD
end StepD
end

-- PivotBackgroundGeometry
section
open Set StableMarriage
open scoped BigOperators
namespace StepD
private noncomputable def backgroundMaleCeiling (n : ℕ) : ℝ :=
  16 * Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)
private noncomputable def backgroundWeightCeiling (n : ℕ) : ℝ :=
  2060 * Real.log n / n
private noncomputable def backgroundLabelBudget (n L : ℕ) : ℝ :=
  ((L.choose 2 : ℝ) + L * (2 * n / (Real.log n) ^ 3)) * backgroundWeightCeiling n
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
end StepD
end

-- LogarithmicCutoffs
section
open Filter
open scoped Topology BigOperators
namespace StepD
private noncomputable def logarithmicCycleCutoff (n : ℕ) : ℕ := ⌊Real.log (n : ℝ)⌋₊
theorem logarithmicCycleCutoff_cast_le (n : ℕ) :
    (logarithmicCycleCutoff n : ℝ) ≤ Real.log (n : ℝ) :=
  Nat.floor_le (Real.log_natCast_nonneg n)
theorem tendsto_logarithmicCycleCutoff : Tendsto logarithmicCycleCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
theorem tendsto_log_logarithmicCycleCutoff :
    Tendsto (fun n : ℕ ↦ Real.log (logarithmicCycleCutoff n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_logarithmicCycleCutoff)
private theorem tendsto_log_natCast :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
theorem tendsto_log_pow_div_nat_rpow (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ k / (n : ℝ) ^ s) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Real.rpow_natCast] using h
theorem logarithmic_collision_label_bound {n : ℕ} (hn : 0 < n) :
    ((logarithmicCycleCutoff n).choose 2 : ℝ) * (2060 * Real.log (n : ℝ) / n) ≤
      2060 * (Real.log (n : ℝ)) ^ 3 / n := by
  have hL := logarithmicCycleCutoff_cast_le n
  have ht := Real.log_natCast_nonneg n
  have hc : ((logarithmicCycleCutoff n).choose 2 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
    rw [Nat.cast_choose_two]
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (logarithmicCycleCutoff n)) hL 2
    nlinarith only [hsq, Nat.cast_nonneg (α := ℝ) (logarithmicCycleCutoff n),
      sq_nonneg (logarithmicCycleCutoff n : ℝ)]
  calc
    _ ≤ (Real.log (n : ℝ)) ^ 2 * (2060 * Real.log (n : ℝ) / n) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring
theorem tendsto_logarithmic_label_envelope :
    Tendsto (fun n : ℕ ↦ 2060 * (Real.log (n : ℝ)) ^ 3 / n +
      4120 / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have h1 := (tendsto_log_pow_div_nat_rpow 3 (by norm_num : (0 : ℝ) < 1)).const_mul 2060
  have h2 := (tendsto_inv_atTop_zero.comp tendsto_log_natCast).const_mul 4120
  simpa only [Real.rpow_one, mul_zero, add_zero, Function.comp_def,
    ← div_eq_mul_inv, mul_div_assoc] using h1.add h2
theorem eventually_logarithmic_label_budget :
    ∀ᶠ n : ℕ in atTop, backgroundLabelBudget n (logarithmicCycleCutoff n) ≤ 1 / 100 := by
  filter_upwards [(tendsto_order.mp tendsto_logarithmic_label_envelope).2
    (1 / 100) (by norm_num), tendsto_log_natCast.eventually_gt_atTop 0,
    eventually_gt_atTop (0 : ℕ)] with n he ht hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmissing :
      (logarithmicCycleCutoff n : ℝ) * (2 * n / (Real.log n) ^ 3) * backgroundWeightCeiling n ≤
        4120 / Real.log n := by
    unfold backgroundWeightCeiling
    calc
      _ ≤ Real.log n * (2 * n / (Real.log n) ^ 3) * (2060 * Real.log n / n) := by
        gcongr
        exact logarithmicCycleCutoff_cast_le n
      _ = _ := by field_simp; ring
  unfold backgroundLabelBudget
  rw [add_mul]
  exact (add_le_add (logarithmic_collision_label_bound hn) hmissing).trans he.le
theorem tendsto_logarithmic_arc_envelope :
    Tendsto (fun n : ℕ ↦ 16 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ (1 / 10 : ℝ) +
      Real.log (n : ℝ) / (n : ℝ) ^ (1 / 10 : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_log_pow_div_nat_rpow 2 (by norm_num : (0 : ℝ) < 1 / 10)).const_mul 16
  simpa only [mul_zero, add_zero, pow_one, mul_div_assoc] using
    h.add (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1 / 10))
theorem eventually_logarithmic_arc_budget :
    ∀ᶠ n : ℕ in atTop, ∀ Y : ℝ, (n : ℝ) ^ (1 / 10 : ℝ) ≤ Y →
      (logarithmicCycleCutoff n : ℝ) * (backgroundMaleCeiling n + 1 / Y) ≤ 1 / 100 := by
  filter_upwards [(tendsto_order.mp tendsto_logarithmic_arc_envelope).2
    (1 / 100) (by norm_num), eventually_gt_atTop (0 : ℕ)] with n he hn Y hY
  have hU : 0 < (n : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  calc
    _ ≤ Real.log (n : ℝ) * (backgroundMaleCeiling n + 1 / (n : ℝ) ^ (1 / 10 : ℝ)) :=
      mul_le_mul (logarithmicCycleCutoff_cast_le n)
        (add_le_add_right (one_div_le_one_div_of_le hU hY) _)
        (add_nonneg (by unfold backgroundMaleCeiling; positivity)
          (one_div_nonneg.mpr (hU.trans_le hY).le)) (Real.log_natCast_nonneg n)
    _ = 16 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ (1 / 10 : ℝ) +
        Real.log (n : ℝ) / (n : ℝ) ^ (1 / 10 : ℝ) := by unfold backgroundMaleCeiling; ring
    _ ≤ _ := he.le
theorem eventually_logarithmic_cycle_budget :
    ∀ᶠ n : ℕ in atTop, BackgroundCycleBudget n (logarithmicCycleCutoff n) := by
  filter_upwards [tendsto_logarithmicCycleCutoff.eventually_ge_atTop 2,
    tendsto_log_logarithmicCycleCutoff.eventually_ge_atTop 100,
    eventually_logarithmic_arc_budget, eventually_logarithmic_label_budget] with n hL hlog ha hl
  exact (BackgroundCycleBudget.mk (hL) (hlog) (ha) (hl))
end StepD
end

-- PivotPairEnvelopeScale
section
open Filter
open scoped Topology
namespace StepD
end StepD
end

-- TwoStableScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
variable {n : ℕ}
end StepD
end

-- TwoStableCommonRows
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
section FiniteOutcomes
variable {n : ℕ} {μ ν : Matching n} [MeasurableSpace (Option (Fin n))]
variable [MeasurableSingletonClass (Option (Fin n))]
end FiniteOutcomes
end StepD
end

-- PivotResidualEstimate
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepD
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
variable {n : ℕ}
end StepD
end

-- TwoStableBackgroundCycleTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
variable {n : ℕ} {μ ν : Matching n}
end StepD
end

-- TwoStablePairDensity
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
end StepD
end

-- TwoStableBetaIntegral
section
open MeasureTheory Set
open scoped ENNReal
namespace StepD
end StepD
end

-- TwoStableOrientationCounting
section
open Equiv Equiv.Perm Finset StableMarriage
open scoped BigOperators ENNReal
namespace StepD
variable {n : ℕ}
namespace LabeledPairOrientation
variable {μ ν : Matching n} {U V : Finset (Fin n)}
end LabeledPairOrientation
end StepD
end

-- TwoStableFixedPairBound
section
open MeasureTheory Set StableMarriage
open scoped ENNReal
namespace StepD
end StepD
end

-- PivotBackgroundPairBound
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal
namespace StepD
variable {n : ℕ} {μ ν : Matching n}
end StepD
end

-- TwoStablePairMassSums
section
open Filter Finset MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepD
variable {n : ℕ}
end StepD
end

-- TwoStablePairPerSizeBounds
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal
namespace StepD
variable {n : ℕ}
end StepD
end

-- PivotPairEnvelopeBounds
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators
namespace StepD
variable {n : ℕ}
end StepD
end

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 30000 in
theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H3_R1.H2 :=
  StepD.eventually_logarithmic_cycle_budget
