import Mathlib

namespace OMA.S_arxiv_2608_20875

/-- Frobenius norm squared of a real `n × n` matrix `X`. -/
def frobSq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (X i j) ^ 2

/-- Continuous Lyapunov operator `L_A(X) = A X + X Aᵀ`. -/
def lyap {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A * X + X * A.transpose

/-- The symmetric-maximizer conjecture for Lyapunov operators (disproved in arXiv:2608.20875):
for every `n ≥ 1` and every real `n × n` matrix `A`, the Frobenius operator norm of `L_A` is
attained at a nonzero symmetric matrix `S`, i.e., there exists a nonzero symmetric `S` such that
`‖L_A(X)‖_F² · ‖S‖_F² ≤ ‖L_A(S)‖_F² · ‖X‖_F²` for all `X`. -/
theorem main :
    ∀ (n : ℕ), 0 < n → ∀ (A : Matrix (Fin n) (Fin n) ℝ),
      ∃ (S : Matrix (Fin n) (Fin n) ℝ),
        S.transpose = S ∧ frobSq S ≠ 0 ∧
        ∀ (X : Matrix (Fin n) (Fin n) ℝ),
          frobSq (lyap A X) * frobSq S ≤ frobSq (lyap A S) * frobSq X := by
  sorry

end OMA.S_arxiv_2608_20875
