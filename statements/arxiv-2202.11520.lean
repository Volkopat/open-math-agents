import Mathlib

namespace OMA.S_arxiv_2202_11520

/-- Squared Frobenius (Hilbert–Schmidt) norm `‖M‖_F^2 = ∑_{i,j} ‖M_{ij}‖^2` of a complex
`n × n` matrix. -/
noncomputable def frobNormSq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ ^ 2

/-- The `q`-deformed commutator `[A, B]_q := A B - q B A`. -/
def qComm {n : ℕ} (q : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * B - (q : ℂ) • (B * A)

/-- Conjecture (Chruściński–Kimura–Ohno–Singal, arXiv:2202.11520):
For every `n ≥ 1`, every `q > 0`, and all `n × n` complex matrices `A, B` such that either
`A` or `B` is traceless, the `q`-deformed Böttcher–Wenzel inequality
`‖A B - q B A‖_F^2 ≤ (1 + q^2) ‖A‖_F^2 ‖B‖_F^2` holds. -/
theorem main :
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (q : ℝ), 0 < q →
        ∀ (A B : Matrix (Fin n) (Fin n) ℂ),
          (Matrix.trace A = 0 ∨ Matrix.trace B = 0) →
          frobNormSq (qComm q A B) ≤ (1 + q ^ 2) * frobNormSq A * frobNormSq B := by
  sorry

end OMA.S_arxiv_2202_11520
