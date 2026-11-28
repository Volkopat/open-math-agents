import Mathlib

/-!
# Global maximizer of a strongly concave function of two variables

Source: https://mathoverflow.net/questions/462279
Asked by MathOverflow user Probabilist.

Let `f : ℝ² → ℝ` be strongly concave, such that for every `x` the function `y ↦ f(x, y)` has a
unique global maximizer, and for every `y` the function `x ↦ f(x, y)` has a unique global
maximizer. The asker asks for a sufficient condition for `f` to be maximized at a unique point
`(x₁, y₁) ∈ ℝ²`. This file formalizes the answer that no further condition is needed: under
these hypotheses `f` always has a unique global maximizer.

Translation choices.
* `ℝ²` is `ℝ × ℝ`, and strong concavity is Mathlib's `StrongConcaveOn Set.univ m f` with some
  modulus `m > 0`. On `ℝ × ℝ` Mathlib uses the sup norm; since the sup norm is at most the
  Euclidean norm, strong concavity with respect to the Euclidean norm implies this hypothesis,
  so the statement covers the usual Euclidean notion.
* The two hypotheses on the partial maximizers are kept as stated in the post.
-/

namespace OMA.S_mo_462279

theorem main :
    ∀ (f : ℝ × ℝ → ℝ) (m : ℝ), 0 < m → StrongConcaveOn Set.univ m f →
      (∀ x : ℝ, ∃! y : ℝ, ∀ y' : ℝ, f (x, y') ≤ f (x, y)) →
      (∀ y : ℝ, ∃! x : ℝ, ∀ x' : ℝ, f (x', y) ≤ f (x, y)) →
      ∃! p : ℝ × ℝ, ∀ q : ℝ × ℝ, f q ≤ f p := by
  sorry

end OMA.S_mo_462279
