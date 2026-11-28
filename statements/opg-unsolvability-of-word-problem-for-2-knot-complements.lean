import Mathlib

/-!
# Unsolvability of word problem for 2-knot complements

Source: https://www.openproblemgarden.org/op/unsolvability_of_word_problem_for_2_knot_complements
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem (Gordon): does there exist a smooth/PL embedding of `S²` in `S⁴` such that the
fundamental group of the complement has an unsolvable word problem?

Conventions:
* We use smooth embeddings (an injective smooth immersion of the compact manifold `S²`) into
  `ℝ⁴`. Removing a point does not change the fundamental group of the complement of a surface
  in a 4-manifold, so `ℝ⁴` and `S⁴` give the same groups; the complement is path-connected, so
  the base point is irrelevant (we only ask for one).
* A group `H` has a solvable word problem if for some finite generating family
  `g : Fin k → H`, the set of words (lists of generators and inverses) equal to `1` in `H` is
  computable. Since 2-knot groups are finitely generated, "unsolvable" means: for no finite
  generating family is this set computable.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_opg_unsolvability_of_word_problem_for_2_knot_complements

open scoped Manifold ContDiff

/-- Euclidean 3-space, containing the round 2-sphere, and Euclidean 4-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E4 := EuclideanSpace ℝ (Fin 4)

instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

/-- The round 2-sphere. -/
abbrev S2 := Metric.sphere (0 : E3) 1

/-- A smooth embedding of `S²` in `ℝ⁴`: an injective smooth immersion (`S²` is compact). -/
def IsSmoothEmbedding (e : S2 → E4) : Prop :=
  Function.Injective e ∧ ContMDiff (𝓡 2) 𝓘(ℝ, E4) ∞ e ∧
    ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E4) e x)

/-- The word problem of `H` is solvable (with respect to some finite generating family). -/
def SolvableWordProblem (H : Type*) [Group H] : Prop :=
  ∃ (k : ℕ) (g : Fin k → H), Function.Surjective (FreeGroup.lift g) ∧
    ComputablePred (fun w : List (Fin k × Bool) => FreeGroup.lift g (FreeGroup.mk w) = 1)

theorem main :
    ∃ (e : S2 → E4) (x : ↥(Set.range e)ᶜ), IsSmoothEmbedding e ∧
      ¬ SolvableWordProblem (FundamentalGroup (↥(Set.range e)ᶜ) x) := by
  sorry

end OMA.S_opg_unsolvability_of_word_problem_for_2_knot_complements
