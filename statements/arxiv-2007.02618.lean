import Mathlib

namespace OMA.S_arxiv_2007_02618

/-- Spectral radius of a real `n × n` matrix `M`, defined as the supremum of `‖μ‖`
over all complex roots `μ : ℂ` of its characteristic polynomial. -/
noncomputable def spectralRadius {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup { r : ℝ | ∃ μ : ℂ, (M.charpoly.map (algebraMap ℝ ℂ)).IsRoot μ ∧ ‖μ‖ = r }

/-- A nonnegative `n × n` matrix `A` is irreducible if for every pair of indices `(i, j)`
there exists `k ≥ 1` such that `(A ^ k) i j > 0`. -/
def IsNonnegIrreducible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ (∀ i j, ∃ k : ℕ, 0 < k ∧ 0 < (A ^ k) i j)

/-- Levinger spectral radius concavity conjecture (disproved by Altenberg and Cohen,
arXiv:2007.02618): for every `n ≥ 1` and every nonnegative irreducible matrix `A ∈ ℝ^{n×n}`,
the Levinger homotopy function `t ↦ r((1 - t) A + t Aᵀ)` is concave on `(0, 1)`. -/
theorem main :
    ∀ (n : ℕ), 0 < n → ∀ (A : Matrix (Fin n) (Fin n) ℝ),
      IsNonnegIrreducible A →
      ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1)
        (fun t : ℝ => spectralRadius ((1 - t) • A + t • A.transpose)) := by
  sorry

end OMA.S_arxiv_2007_02618
