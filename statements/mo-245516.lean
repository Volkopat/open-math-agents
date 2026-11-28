import Mathlib

/-!
# Does every separable Banach space have a Markushevich–Auerbach basis?

Source: https://mathoverflow.net/questions/245516
For a separable Banach space `X`, a sequence `(xᵢ)` with dense linear span and biorthogonal
functionals `xᵢ* ∈ X*` (`xᵢ*(xⱼ) = δᵢⱼ`) is a Markushevich–Auerbach basis if the span of the
`xᵢ*` is weak-* dense in `X*` and `‖xᵢ‖ = ‖xᵢ*‖ = 1`. `main` states that every
infinite-dimensional separable real Banach space has one.

Conventions. Weak-* density of the span of the `xᵢ*` is equivalent to its total-ness:
`x = 0` whenever `xᵢ*(x) = 0` for all `i`. Duals are `(X →L[ℝ] ℝ)`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_245516

theorem main :
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      [TopologicalSpace.SeparableSpace X], ¬ FiniteDimensional ℝ X →
      ∃ (x : ℕ → X) (f : ℕ → (X →L[ℝ] ℝ)),
        Dense (Submodule.span ℝ (Set.range x) : Set X) ∧
        (∀ i j, f i (x j) = if i = j then 1 else 0) ∧
        (∀ v : X, (∀ i, f i v = 0) → v = 0) ∧
        (∀ i, ‖x i‖ = 1 ∧ ‖f i‖ = 1) := by
  sorry

end OMA.S_mo_245516
