import Mathlib

/-!
# Restriction conjecture for the sphere

Source: https://en.wikipedia.org/wiki/Restriction_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Stein): for the unit sphere `S^{n-1} ⊂ ℝⁿ` with surface measure `σ`, the extension
operator satisfies `‖(f dσ)^∨‖_{L^p(ℝⁿ)} ≤ C_p ‖f‖_{L^∞(S^{n-1})}` for every `p > 2n/(n-1)`.

Conventions:
* `n ≥ 2` (the source's statement concerns the sphere `S^{n-1}` in `ℝⁿ`; it is proved for `n = 2`
  and open for every `n ≥ 3`).
* Surface measure is Mathlib's `(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere`, which is
  a constant multiple of the standard surface measure; constants do not affect the statement.
* `(f dσ)^∨ (x) = ∫ f(ω) e^{2πi ⟨x, ω⟩} dσ(ω)`. The `L^∞` bound is taken as a pointwise bound
  `‖f ω‖ ≤ M` for a measurable `f`; changing `f` on a `σ`-null set does not change the extension,
  so this is the same as an essential-supremum bound.
-/

namespace OMA.S_wpc_restriction_conjecture

open MeasureTheory

/-- The extension operator `(f dσ)^∨`. -/
noncomputable def extension (n : ℕ) (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∫ ω, f ω * Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x (ω : EuclideanSpace ℝ (Fin n)) : ℂ))
    ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∀ p : ℝ, 2 * n / (n - 1) < p → ∃ C : ENNReal, C < ⊤ ∧
      ∀ (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℂ) (M : NNReal), Measurable f →
        (∀ ω, ‖f ω‖ ≤ M) →
          eLpNorm (extension n f) (ENNReal.ofReal p) volume ≤ C * M := by
  sorry

end OMA.S_wpc_restriction_conjecture
