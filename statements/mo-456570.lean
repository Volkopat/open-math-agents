import Mathlib

open MeasureTheory
open scoped ContDiff ENNReal

namespace OMA.S_mo_456570

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def parameterInterval : Set ℝ := Set.Icc 0 1

def IsUnitCurve {d : ℕ} (curve : ℝ → Space d) : Prop :=
  ContinuousOn curve parameterInterval ∧ eVariationOn curve parameterInterval = 1 ∧
    ∃ (m : ℕ) (breaks : Fin (m + 1) → ℝ),
      0 < m ∧ StrictMono breaks ∧ breaks 0 = 0 ∧ breaks (Fin.last m) = 1 ∧
        ∀ i : Fin m,
          ContDiffOn ℝ ∞ curve (Set.Icc (breaks i.castSucc) (breaks i.succ))

def IsSleepingBag {d : ℕ} (S : Set (Space d)) : Prop :=
  ∀ curve : ℝ → Space d, IsUnitCurve curve →
    ∃ (rotation : Space d ≃ₗᵢ[ℝ] Space d) (translation : Space d),
      LinearMap.det rotation.toLinearEquiv.toLinearMap = 1 ∧
        (fun t => rotation (curve t) + translation) '' parameterInterval ⊆ S

def HasPlanarSleepingBag (S : Set (Space 3)) : Prop :=
  ∃ (plane : Space 2 →ₗᵢ[ℝ] Space 3) (translation : Space 3),
    IsSleepingBag ((fun x => plane x + translation) ⁻¹' S)

noncomputable def infimumVolume : ℝ≥0∞ :=
  sInf ((fun S : Set (Space 3) => volume S) '' {S | IsSleepingBag S})

/-- Can three-dimensional sleeping bags without a planar sleeping-bag
section come arbitrarily close to the optimal volume? -/
theorem main :
    ∀ ε : NNReal, 0 < ε →
      ∃ S : Set (Space 3),
        IsSleepingBag S ∧ volume S ≤ infimumVolume + (ε : ℝ≥0∞) ∧
          ¬ HasPlanarSleepingBag S := by
  sorry

end OMA.S_mo_456570
