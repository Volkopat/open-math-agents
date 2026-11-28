import Mathlib

namespace OMA.S_wp_quantum_unique_ergodicity_conjecture

open scoped BigOperators ContDiff Manifold
open Filter Manifold MeasureTheory

noncomputable section

abbrev Coordinates (d : ℕ) := Fin d → ℝ
abbrev Ambient (e : ℕ) := EuclideanSpace ℝ (Fin e)

def coordinateVector {d : ℕ} (i : Fin d) : Coordinates d :=
  Pi.single i 1

/-- The tangent metric induced by a Euclidean immersion in a coordinate chart. -/
def metricMatrix {d e : ℕ} (F : Coordinates d → Ambient e) (z : Coordinates d) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    inner ℝ (fderiv ℝ F z (coordinateVector i)) (fderiv ℝ F z (coordinateVector j))

/-- The density of the induced volume relative to coordinate Lebesgue measure. -/
def volumeDensity {d e : ℕ} (F : Coordinates d → Ambient e) (z : Coordinates d) : ℝ :=
  Real.sqrt (metricMatrix F z).det

/-- The normal component of the second derivative of the immersion. -/
def secondFundamentalForm {d e : ℕ} (F : Coordinates d → Ambient e)
    (z u v : Coordinates d) : Ambient e :=
  let tangent := LinearMap.range (fderiv ℝ F z).toLinearMap
  let second := fderiv ℝ (fun w => fderiv ℝ F w v) z u
  second - tangent.starProjection second

/-- The divergence of the gradient in the induced metric. -/
def laplaceBeltrami {d e : ℕ} (F : Coordinates d → Ambient e)
    (f : Coordinates d → ℝ) (z : Coordinates d) : ℝ :=
  (volumeDensity F z)⁻¹ * ∑ i : Fin d,
    fderiv ℝ
      (fun w => volumeDensity F w * ∑ j : Fin d,
        ((metricMatrix F w)⁻¹) i j * fderiv ℝ f w (coordinateVector j))
      z (coordinateVector i)

section Manifold

variable {d e : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates d) M]

/-- The Gauss equation gives the numerator of sectional curvature at each tangent plane. -/
def NegativelyCurved (embed : M → Ambient e) : Prop :=
  ∀ x : M,
    let chart := chartAt (Coordinates d) x
    let B := secondFundamentalForm (embed ∘ chart.symm) (chart x)
    ∀ u v : Coordinates d, u ≠ 0 → v ∉ Submodule.span ℝ {u} →
      inner ℝ (B u u) (B v v) - ‖B u v‖ ^ 2 < 0

/-- The volume on every chart has the density from its induced metric matrix. -/
def IsInducedVolume [MeasurableSpace M] (embed : M → Ambient e)
    (μ : Measure M) : Prop :=
  ∀ x : M,
    let chart := chartAt (Coordinates d) x
    Measure.map chart (μ.restrict chart.source) =
      (volume.withDensity
        (fun z => ENNReal.ofReal (volumeDensity (embed ∘ chart.symm) z))).restrict
          chart.target

/-- Eigenfunctions are smooth and satisfy the eigenvalue equation in local coordinates. -/
def IsLaplaceEigenfunction (embed : M → Ambient e) (f : M → ℝ) (energy : ℝ) : Prop :=
  ContMDiff (𝓘(ℝ, Coordinates d)) (𝓘(ℝ, ℝ)) ∞ f ∧
    ∀ x : M,
      let chart := chartAt (Coordinates d) x
      laplaceBeltrami (embed ∘ chart.symm) (f ∘ chart.symm) (chart x) = -(energy * f x)

end Manifold

/-- The original Rudnick–Sarnak conjecture on position-space measures. -/
theorem main :
    ∀ (d e : ℕ), 2 ≤ d →
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [CompactSpace M] [ConnectedSpace M] [ChartedSpace (Coordinates d) M]
      [IsManifold (𝓘(ℝ, Coordinates d)) ∞ M] [MeasurableSpace M] [BorelSpace M],
    ∀ embed : M → Ambient e,
      IsSmoothEmbedding (𝓘(ℝ, Coordinates d)) (𝓘(ℝ, Ambient e)) ∞ embed →
      NegativelyCurved (d := d) embed →
    ∀ μ : Measure M,
      IsInducedVolume (d := d) embed μ →
      0 < μ Set.univ → μ Set.univ < ⊤ →
    ∀ (f : ℕ → M → ℝ) (energy : ℕ → ℝ),
      (∀ n, IsLaplaceEigenfunction (d := d) embed (f n) (energy n)) →
      Tendsto energy atTop atTop →
      (∀ n, ∫ x, (f n x) ^ 2 ∂((μ Set.univ)⁻¹ • μ) = 1) →
    ∀ a : M → ℝ, Continuous a →
      Tendsto (fun n => ∫ x, a x * (f n x) ^ 2 ∂((μ Set.univ)⁻¹ • μ))
        atTop (nhds (∫ x, a x ∂((μ Set.univ)⁻¹ • μ))) := by
  sorry

end

end OMA.S_wp_quantum_unique_ergodicity_conjecture
