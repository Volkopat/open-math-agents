import Mathlib

/-!
# Can 4×4 matrices be multiplied with 47 multiplications in characteristic 0?

Source: https://arxiv.org/abs/2506.13131
Credit: @eltociear

The problem, as stated in the catalogue: is the tensor rank of the 4×4 matrix
multiplication tensor `⟨4,4,4⟩` over `ℚ` (or over `ℂ`) at most 47? Equivalently,
is there a bilinear algorithm using 47 multiplications for the product of two 4×4
matrices over a field of characteristic 0?

State of the art recorded by the source: Strassen's algorithm applied recursively
uses 49 multiplications; AlphaEvolve (arXiv:2506.13131, 2025) found 48 over `ℂ`,
and Dumas, Pernet and Sedoglavic (arXiv:2506.13242) gave a 48-multiplication
algorithm with rational coefficients; 47 is known only in characteristic 2
(AlphaTensor, 2022).

Conventions of this translation.
* `main` is the `ℚ` form of the question: a rank decomposition of the `⟨4,4,4⟩`
  tensor with rational coefficients, i.e. a bilinear algorithm with 47
  multiplications over `ℚ`. A rational decomposition works verbatim over every
  field of characteristic 0 (in particular over `ℂ`), which is the source's
  "over a field of characteristic 0" phrasing; the rational form is the strongest
  of these equivalent readings and the first one the source names.
* A bilinear algorithm with `R` multiplications is given by three coefficient
  families `α β γ : Fin R → Fin 4 → Fin 4 → ℚ`: the `r`-th multiplication is the
  product of the linear form `∑ i j, α r i j * A i j` in the entries of `A` and
  the linear form `∑ i j, β r i j * B i j` in the entries of `B`, and the output
  entry `(i, k)` is the linear combination `∑ r, γ r i k * (r-th product)`.
  The algorithm is correct when this computes `A * B` for all `A B`. This is the
  standard equivalence between bilinear algorithms and rank decompositions of
  the matrix multiplication tensor: `HasRankDecomposition R` holds exactly when
  the tensor rank of `⟨4,4,4⟩` over `ℚ` is at most `R`.
-/

namespace OMA.S_aist_rank_4x4_matrix_multiplication_char0

/-- A bilinear algorithm with `R` multiplications for 4×4 matrix multiplication
over `ℚ`: coefficient families `α β γ` such that for all `A B` and all `i k`,
the `γ`-combination of the `R` products of `α`- and `β`-linear forms equals
`(A * B) i k`. Equivalently, a rank-`R` decomposition of the `⟨4,4,4⟩` tensor. -/
def HasRankDecomposition (R : ℕ) : Prop :=
  ∃ α β γ : Fin R → Fin 4 → Fin 4 → ℚ,
    ∀ A B : Matrix (Fin 4) (Fin 4) ℚ, ∀ i k : Fin 4,
      (A * B) i k = ∑ r : Fin R, γ r i k *
        (∑ p : Fin 4 × Fin 4, α r p.1 p.2 * A p.1 p.2) *
        (∑ p : Fin 4 × Fin 4, β r p.1 p.2 * B p.1 p.2)

/-- The question of the source: can 4×4 matrices be multiplied with 47
multiplications in characteristic 0, i.e. is the tensor rank of `⟨4,4,4⟩`
over `ℚ` at most 47? -/
theorem main : HasRankDecomposition 47 := by
  sorry

end OMA.S_aist_rank_4x4_matrix_multiplication_char0
