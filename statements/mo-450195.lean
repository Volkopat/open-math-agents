import Mathlib

/-!
# Is an almost-solvable linear equation with integer coefficients solvable?

Source: https://mathoverflow.net/questions/450195
Credit: @ivillar

Status: known result; the answer is yes, and `R` plays no role (any `R` works with a suitable
`ε`). The column space of `M` is a rational subspace, so there are finitely many integer
vectors `z_1, …, z_r` with `z_k · M = 0` such that an integer vector `b` lies in the column
space as soon as `z_k · b = 0` for all `k`. If `‖M x' - b‖ < ε` then
`|z_k · b| = |z_k · (b - M x')| ≤ ε ∑_i |z_{k,i}| < 1` for small `ε`, and `z_k · b` is an
integer, hence `0`. This is the mechanism behind the `m = 2`, `n = 1` computation in the
comments (a nonzero rational with bounded denominator is bounded away from `0`).

Question. Let $M$ be a fixed $m \times n$ rectangular matrix ($m > n$) with non-negative integer
coefficients. Does there exist a pair $(R, \epsilon)$ with the following properties: if $b$ is
an $m \times 1$ vector with non-negative integer coefficients such that $\| b \| > R$ and $x'$
an $n \times 1$ vector in $\mathbb{R}^n$ such that $\|Mx' - b\| < \epsilon$, i.e. $x'$ is almost
a solution to $My = b$, then there exists a vector $x \in \mathbb{R}^n$ which is an actual
solution, i.e. $Mx = b$.

Formalization notes:
* `M : Matrix (Fin m) (Fin n) ℕ` with `n < m`; it acts on real vectors through
  `M.map (fun a : ℕ => (a : ℝ))`.
* `ε` is required to be positive (with `ε ≤ 0` the property would hold vacuously); `R` is an
  arbitrary real.
* `‖·‖` is the norm of `Fin m → ℝ` in Mathlib, the sup norm. The question does not name the
  norm; since all norms on `ℝ^m` are equivalent, the existence of a pair `(R, ε)` does not
  depend on this choice.
* `main` states the positive answer: for every such `M` there is a pair `(R, ε)` with the
  stated property.
-/

namespace OMA.S_mo_450195

theorem main : ∀ (m n : ℕ), n < m → ∀ M : Matrix (Fin m) (Fin n) ℕ,
    ∃ R ε : ℝ, 0 < ε ∧ ∀ b : Fin m → ℕ, R < ‖fun i => (b i : ℝ)‖ →
      ∀ x' : Fin n → ℝ,
        ‖(M.map (fun a : ℕ => (a : ℝ))).mulVec x' - (fun i => (b i : ℝ))‖ < ε →
        ∃ x : Fin n → ℝ, (M.map (fun a : ℕ => (a : ℝ))).mulVec x = fun i => (b i : ℝ) := by
  sorry

end OMA.S_mo_450195
