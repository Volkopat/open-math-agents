import Mathlib

/-!
Binh Thuan Tran, "Minimax Rates for Estimating Powered Sliced Wasserstein
Functionals", arXiv:2610.12740, Sections 2 and 3 (the question following
Proposition 3.4). The critical case is r = 2p. The proposed answer is a
two-sided asymptotic rate for absolute estimation error, uniform in dimension.
-/

namespace OMA.S_arxiv_2610_12740

open MeasureTheory
open scoped ENNReal

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Direction (d : ℕ) := Metric.sphere (0 : Point d) 1

/-- Normalized surface measure on the Euclidean unit sphere in positive dimension. -/
noncomputable def directionLaw (d : ℕ) : Measure (Direction d) :=
  let surface := (volume : Measure (Point d)).toSphere
  (surface Set.univ)⁻¹ • surface

noncomputable def project {d : ℕ} (θ : Direction d) (x : Point d) : ℝ :=
  inner ℝ (θ : Point d) x

/-- On each projection take the square root of its (2p)-th absolute moment.
Extended integrals retain infinite moments. -/
noncomputable def criticalMoment {d : ℕ} (p : ℝ) (μ : ProbabilityMeasure (Point d)) : ℝ≥0∞ :=
  ∫⁻ θ, (∫⁻ x, (ENNReal.ofReal |project θ x|) ^ (2 * p)
    ∂(μ : Measure (Point d))) ^ (1 / 2 : ℝ) ∂directionLaw d

/-- Infimum of the p-th power transport cost over all couplings on the line. -/
noncomputable def transportPower (p : ℝ) (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ⨅ γ : {γ : Measure (ℝ × ℝ) // γ.fst = μ ∧ γ.snd = ν},
    ∫⁻ z, (ENNReal.ofReal |z.1 - z.2|) ^ p ∂(γ : Measure (ℝ × ℝ))

/-- Average the one-dimensional powered Wasserstein distances of the projections. -/
noncomputable def slicedPower {d : ℕ} (p : ℝ) (μ ν : ProbabilityMeasure (Point d)) : ℝ≥0∞ :=
  ∫⁻ θ, transportPower p
    ((μ : Measure (Point d)).map (project θ))
    ((ν : Measure (Point d)).map (project θ)) ∂directionLaw d

abbrev Sample (d n m : ℕ) := (Fin n → Point d) × (Fin m → Point d)

/-- Independent samples with laws μ^n and ν^m. -/
noncomputable def sampleLaw {d : ℕ} (n m : ℕ) (μ ν : ProbabilityMeasure (Point d)) :
    Measure (Sample d n m) :=
  (Measure.pi fun _ : Fin n => (μ : Measure (Point d))).prod
    (Measure.pi fun _ : Fin m => (ν : Measure (Point d)))

/-- Minimize over all measurable estimators and maximize over both laws in the
projected moment class. The target is finite on this class for p ≥ 1 and finite b. -/
noncomputable def minimaxRisk (d n m : ℕ) (p b : ℝ) : ℝ≥0∞ :=
  let Law := {μ : ProbabilityMeasure (Point d) // criticalMoment p μ ≤ ENNReal.ofReal b}
  ⨅ T : {T : Sample d n m → ℝ // Measurable T}, ⨆ μ : Law, ⨆ ν : Law,
    ∫⁻ z, ENNReal.ofReal |T.val z - (slicedPower p μ.val ν.val).toReal|
      ∂sampleLaw n m μ.val ν.val

noncomputable def rate (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) / ((N : ℝ) * Real.log (Real.log (N : ℝ))))

/-- Sharp critical minimax order for every fixed p ≥ 1. The two comparison
constants and the threshold are independent of d, n, m, and the moment budget. -/
theorem main :
    ∀ p : ℝ, 1 ≤ p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
      ∀ d n m : ℕ, 0 < d → 3 ≤ min n m → N₀ ≤ min n m → ∀ b : ℝ, 0 < b →
        ENNReal.ofReal (c * b * rate (min n m)) ≤ minimaxRisk d n m p b ∧
        minimaxRisk d n m p b ≤ ENNReal.ofReal (C * b * rate (min n m)) := by
  sorry

end OMA.S_arxiv_2610_12740
