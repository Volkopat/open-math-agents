import Mathlib

/-!
# Is a Lipschitz continuous gradient equivalent to this condition?

Source: https://mathoverflow.net/questions/436948
Credit: @ivillar

Status: known result; the answer is yes, the converse holds without any convexity assumption.
If `|f(x) - f(x₀) - ∇f(x₀)ᵀ(x - x₀)| ≤ (L/2) ‖x - x₀‖²` for all `x, x₀`, then `∇f` is
`L`-Lipschitz, with the same constant `L`. The reason: the two one-sided bounds say that both
`(L/2)‖x‖² + f` and `(L/2)‖x‖² - f` are convex, and the standard co-coercivity argument for a
convex function with a quadratic upper bound then gives `‖∇f(x) - ∇f(y)‖ ≤ L ‖x - y‖`. Hence
there is no counterexample.

Question. I know if a function $f: \mathbb{R}^n \to \mathbb{R}$ is $L$-smooth, i.e. its gradient
$\nabla f$ is $L$-Lipschitz continuous, then it satisfies the following inequality for any
$x, x_0 \in \mathbb{R}^n$:
$$\left| f(x) - \left( f(x_0) + \nabla f(x_0)^\top (x - x_0)\right) \right|
  \leq \frac{L}{2} \lVert x - x_0 \rVert_2^2 .$$
Here's my question: is the converse true? I know that, provided $f$ is convex, then we can
conclude that $f$ satisfying the above inequality must be $L$-smooth. But what if $f$ is not
necessarily convex? If the converse is false, can you give some counterexamples?

Formalization notes:
* `ℝ^n` with the Euclidean norm is `EuclideanSpace ℝ (Fin n)`; `∇f` is Mathlib's `gradient f`,
  and `∇f(x₀)ᵀ(x - x₀)` is the inner product `inner ℝ (gradient f x₀) (x - x₀)`.
* `f` is assumed differentiable everywhere, so that the gradient in the inequality is the
  actual gradient (the question presupposes that `∇f` exists).
* The Lipschitz constant `L` is a nonnegative real (`NNReal`), and `L`-smoothness is
  `LipschitzWith L (gradient f)`.
* `main` states the converse asked about: the inequality for all `x, x₀` implies that `∇f` is
  `L`-Lipschitz.
-/

namespace OMA.S_mo_436948

theorem main :
    ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
      Differentiable ℝ f →
      (∀ x x₀ : EuclideanSpace ℝ (Fin n),
        |f x - (f x₀ + inner ℝ (gradient f x₀) (x - x₀))| ≤ (L : ℝ) / 2 * ‖x - x₀‖ ^ 2) →
      LipschitzWith L (gradient f) := by
  sorry

end OMA.S_mo_436948
