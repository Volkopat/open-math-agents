import Mathlib

/-!
# A conjecture on the Lyapunov equation

Source: https://math.stackexchange.com/questions/2922967/a-conjecture-on-the-lyapunov-equation
Credit: @ZenimXD

Let $A \in \mathbb{R}^{n \times n}$ be a Hurwitz stable matrix (all complex eigenvalues of $A$
have strictly negative real part). For a positive semidefinite matrix $X \in \mathbb{R}^{n \times n}$
with $\mathrm{tr}(X) = 1$, let $P$ be the positive semidefinite solution of the Lyapunov equation
$A P + P A^\top = -X$. The conjecture asks whether there always exists such an $X$ for which
$\|P\|_2 = \frac{1}{-2\,\mathrm{tr}(A)}$, where $\|P\|_2$ is the matrix 2-norm (spectral /
induced Euclidean operator norm).

Conventions:
- $n \ge 1$ (`0 < n`), as standard for $\mathbb{R}^{n \times n}$ (for $n = 0$ no matrix has
  unit trace and $\mathrm{tr}(A) = 0$).
- Hurwitz stability is stated via `spectrum ℂ (A.map Complex.ofReal)`.
- Positive semidefiniteness is `Matrix.PosSemidef` (symmetric real matrix with $v^\top M v \ge 0$).
- Since $A$ is Hurwitz stable, the Lyapunov equation $A P + P A^\top = -X$ has a unique solution
  $P$ (which is automatically positive semidefinite when $X \succeq 0$), so quantifying
  `∃ X P, ...` is equivalent to taking $P$ as the unique solution associated to $X$.
-/

namespace OMA.S_mse_2922967

/-- A real square matrix is Hurwitz stable if all of its complex eigenvalues have strictly
negative real part. -/
def IsHurwitz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.re < 0

/-- The matrix 2-norm (induced Euclidean operator norm / spectral norm) of a real matrix. -/
noncomputable def matrixTwoNorm {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin P).toContinuousLinearMap‖

theorem main :
    ∀ (n : ℕ), 0 < n →
    ∀ (A : Matrix (Fin n) (Fin n) ℝ), IsHurwitz A →
      ∃ (X P : Matrix (Fin n) (Fin n) ℝ),
        X.PosSemidef ∧
        X.trace = 1 ∧
        P.PosSemidef ∧
        A * P + P * A.transpose = -X ∧
        matrixTwoNorm P = 1 / (-2 * A.trace) := by
  sorry

end OMA.S_mse_2922967
