import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

namespace OMA.S_wp_weinstein_conjecture

open scoped ContDiff Manifold

universe u

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n + 1))

section Forms

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Model n) M]

abbrev OneForm (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M] :=
  (p : M) → TangentSpace (𝓘(ℝ, Model n)) p →L[ℝ] ℝ

/-- The pullback of a one-form by the inverse of the chart at p. -/
noncomputable def formInChart (α : OneForm n M) (p : M) :
    Model n → (Model n →L[ℝ] ℝ) :=
  let chart := extChartAt (𝓘(ℝ, Model n)) p
  fun y => (α (chart.symm y)).comp
    (mfderiv (𝓘(ℝ, Model n)) (𝓘(ℝ, Model n)) chart.symm y)

/-- The exterior derivative of a one-form evaluated on two tangent vectors at p. -/
noncomputable def exteriorDerivative (α : OneForm n M) (p : M)
    (v w : TangentSpace (𝓘(ℝ, Model n)) p) : ℝ :=
  let chart := extChartAt (𝓘(ℝ, Model n)) p
  let chartDerivative := mfderiv (𝓘(ℝ, Model n)) (𝓘(ℝ, Model n)) chart p
  let D := fderiv ℝ (formInChart α p) (chart p)
  D (chartDerivative v) (chartDerivative w) - D (chartDerivative w) (chartDerivative v)

/-- A smooth, nowhere-zero one-form with exterior derivative nondegenerate on its kernel. -/
def IsContactForm (α : OneForm n M) : Prop :=
  (∀ p, ContDiffOn ℝ ∞ (formInChart α p) (extChartAt (𝓘(ℝ, Model n)) p).target) ∧
  ∀ p, α p ≠ 0 ∧
    ∀ v, α p v = 0 →
      (∀ w, α p w = 0 → exteriorDerivative α p v w = 0) → v = 0

end Forms

/-- The Weinstein conjecture in its contact formulation. Every contact form on a
nonempty closed manifold admits a Reeb orbit of positive period. -/
theorem main :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
      [IsManifold (𝓘(ℝ, Model n)) ∞ M] [T2Space M] [SecondCountableTopology M]
      [CompactSpace M] [Nonempty M],
      ∀ α : OneForm n M, IsContactForm α →
        ∃ (X : (p : M) → TangentSpace (𝓘(ℝ, Model n)) p) (γ : ℝ → M) (T : ℝ),
          (∀ p, α p (X p) = 1 ∧ ∀ v, exteriorDerivative α p (X p) v = 0) ∧
          0 < T ∧ Function.Periodic γ T ∧ IsMIntegralCurve γ X := by
  sorry

end OMA.S_wp_weinstein_conjecture
