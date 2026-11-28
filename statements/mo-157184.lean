import Mathlib

/-!
# Convergence in L² of iterated expectations

Source: https://mathoverflow.net/questions/157184
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

On a probability space take `X ∈ L²`, put `X₀ = X` and `X_k = E[X_{k-1} | 𝒢_k]`, where every
`𝒢_k` is one of finitely many sub-σ-algebras. Question: does `(X_k)` converge in `L²`?

Conventions:
* The finitely many σ-algebras are `G : Fin r → MeasurableSpace Ω`, each `≤` the ambient one,
  and the order in which they are used is an arbitrary sequence `s : ℕ → Fin r`. Conditional
  expectation is Mathlib's `condExp`. Convergence in `L²` means `‖X_k - Y‖₂ → 0` for some `Y`
  in `L²`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_157184

open MeasureTheory Filter Topology

/-- The iterated conditional expectations. -/
noncomputable def iter {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) {r : ℕ}
    (G : Fin r → MeasurableSpace Ω) (s : ℕ → Fin r) (X : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => X
  | k + 1 => μ[iter μ G s X k | G (s (k + 1))]

/-- The iterated conditional expectations converge in `L²`. -/
theorem main : ∀ (Ω : Type) [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : ℕ) (G : Fin r → MeasurableSpace Ω), (∀ i, G i ≤ m0) →
    ∀ (s : ℕ → Fin r) (X : Ω → ℝ), MemLp X 2 μ →
    ∃ Y : Ω → ℝ, MemLp Y 2 μ ∧
      Tendsto (fun k => eLpNorm (iter μ G s X k - Y) 2 μ) atTop (𝓝 0) := by
  sorry

end OMA.S_mo_157184
