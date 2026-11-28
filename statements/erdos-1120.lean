import Mathlib

/-!
# Erdős Problem 1120

Source: https://www.erdosproblems.com/1120 (Problem 4.22 in Hayman's list, attributed to Erdős)

Let `f ∈ ℂ[z]` be monic of degree `n` with all roots in the closed unit disc, and let
`E = {z : |f z| ≤ 1}`. What is the shortest length of a path in `E` joining `0` to the unit
circle? Erdős wrote that presumably this tends to infinity with `n` (in the worst case over
`f`). `main` states that presumption: for every bound `M` there is `n₀` such that for every
`n ≥ n₀` some admissible `f` of degree `n` has every such path of length at least `M`.

Conventions. A path is a map `γ : ℝ → ℂ` continuous on `[0, 1]` with `γ 0 = 0`, `|γ 1| = 1`
and `γ t ∈ E` for `t ∈ [0, 1]`; its length is the total variation `eVariationOn γ [0, 1]`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_erdos_1120

open Polynomial Set

theorem main :
    ∀ M : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ f : ℂ[X],
      f.Monic ∧ f.natDegree = n ∧ (∀ z ∈ f.roots, ‖z‖ ≤ 1) ∧
      ∀ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) → γ 0 = 0 → ‖γ 1‖ = 1 →
        (∀ t ∈ Icc (0 : ℝ) 1, ‖f.eval (γ t)‖ ≤ 1) →
        ENNReal.ofReal M ≤ eVariationOn γ (Icc 0 1) := by
  sorry

end OMA.S_erdos_1120
