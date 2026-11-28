import Mathlib

/-!
# A centered ball minimizes Wasserstein distance to a smaller centered ball

Source: https://mathoverflow.net/questions/282627
Credit: @artnoage

We use normalized Lebesgue measure on a measurable region of the prescribed
volume. Wasserstein cost is the infimum of Lp norms of displacement over
couplings, in ℝ≥0∞ to include regions with infinite pth moment. The radii are
positive so the normalized ball measures are defined.
-/

namespace OMA.S_mo_282627

open MeasureTheory Metric
open scoped ENNReal

/-- Normalized Lebesgue measure on the given region. -/
noncomputable def uniform {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume A)⁻¹ • volume.restrict A

/-- Measures on the product with the two prescribed marginals. -/
def IsCoupling {n : ℕ} (μ ν : Measure (EuclideanSpace ℝ (Fin n)))
    (π : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) : Prop :=
  π.map Prod.fst = μ ∧ π.map Prod.snd = ν

/-- Wasserstein distance expressed as the infimum of displacement costs. -/
noncomputable def wasserstein {n : ℕ} (p : ℝ≥0∞)
    (μ ν : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ π : {π // IsCoupling μ ν π}, eLpNorm (fun z ↦ z.1 - z.2) p π.1

theorem main :
    ∀ (n : ℕ) (p : ℝ≥0∞) (r R : ℝ), 1 ≤ n → 1 ≤ p → p ≠ ∞ → 0 < r → r ≤ R →
      ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
        volume A = volume (ball 0 R : Set (EuclideanSpace ℝ (Fin n))) →
          wasserstein (n := n) p (uniform (ball 0 R)) (uniform (ball 0 r)) ≤
            wasserstein p (uniform A) (uniform (ball 0 r)) := by
  sorry

end OMA.S_mo_282627
