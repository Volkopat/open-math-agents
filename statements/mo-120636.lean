import Mathlib

/-!
# Differentiating a binomial expectation

Josh asks for the derivative with respect to the success probability and
about the implicit equation E[f(X)] = p + y. The Bernstein weights are
the binomial masses on [0,1]. The expectation has a polynomial extension
to all real p. The last clause exhibits a positive convex payoff for which
every probability solves the same implicit equation.

Source: https://mathoverflow.net/questions/120636/binomial-expectation-of-convex-function
Credit: Josh (question, CC BY-SA); user39430 gave the derivative in a comment.
Formalization: @dwilfand-sys, using Codex.
-/

namespace OMA.S_mo_120636

theorem main :
    let E : ℕ → (ℕ → ℝ) → ℝ → ℝ := fun n f p =>
      ∑ j ∈ Finset.range (n + 1), f j * (bernsteinPolynomial ℝ n j).eval p
    (∀ (f : ℕ → ℝ) (n : ℕ) (p : ℝ),
      HasDerivAt (E n f) ((n : ℝ) * E (n - 1) (fun j => f (j + 1) - f j) p) p) ∧
    (∃ (g : ℝ → ℝ) (y : ℝ), (∀ x, 0 < g x) ∧ ConvexOn ℝ Set.univ g ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1, E 1 (fun j => g j) p = p + y) := by
  sorry

end OMA.S_mo_120636
