import Mathlib

/-!
# Logarithmic moments of a mixture of products of its marginals

Source: Tom, https://mathoverflow.net/questions/466871 (CC BY-SA 4.0).
Credit: @connoranderson.

The product of the two orthogonal marginals, identified with a measure on the
ambient space, is the law obtained by independently sampling the two projections
and adding them. The weights of a probability mixture sum to one.
-/

namespace OMA.S_mo_466871

open MeasureTheory
open scoped ENNReal

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def proj {n : ℕ} (S : Submodule ℝ (E n)) : E n →L[ℝ] E n :=
  S.starProjection

noncomputable def recombine {n : ℕ} (S : Submodule ℝ (E n)) (xy : E n × E n) :
    E n := proj S xy.1 + proj Sᗮ xy.2

noncomputable def mix {n k : ℕ} (μ : Measure (E n)) (S : Fin k → Submodule ℝ (E n))
    (p : Fin k → ℝ) : Measure (E n) :=
  ∑ i, ENNReal.ofReal (p i) • Measure.map (recombine (S i)) (μ.prod μ)

theorem main : ∀ {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (S : Fin k → Submodule ℝ (E n)) (p : Fin k → ℝ),
    (∀ i, 0 < p i) → (∑ i, p i = 1) →
    (∀ x : E n, (∀ i, x ∈ S i ∨ x ∈ (S i)ᗮ) → x = 0) →
    μ = mix μ S p → Integrable (fun x : E n => Real.log (1 + ‖x‖)) μ := by
  sorry

end OMA.S_mo_466871
