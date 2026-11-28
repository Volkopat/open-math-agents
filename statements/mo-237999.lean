import Mathlib

/-!
# Weakly diagonally dominant matrices with zero row sums

Source: https://mathoverflow.net/questions/237999
Credit: @koolkao

Question (Skrodde, MathOverflow 237999, 2016; CC BY-SA 3.0). We are considering a matrix
`A = (a_ij) ∈ ℝ^{d×d}` with the following property: `a_ii = -∑_{j≠i} a_ij`, i.e., the matrix is
not only weak diagonal-dominant, but its rows also sum up to `0`. Note that the matrix is not
necessarily symmetric. Furthermore, the matrix has the property that there are no matrices
`B ∈ ℝ^{(d-k)×(d-k)}`, `C ∈ ℝ^{k×k}`, `k ∈ {1, …, d-1}`, `R ∈ GL(d, ℝ)` such that
`A = R · diag(B, C) · R^T`, i.e., we can not rearrange the matrix `A` by switching two rows and
the corresponding columns to obtain a decoupled version of `A`. Two questions arise: Is `A`
positive semi-definite in the sense that `x^T A x ≥ 0` for all `x ∈ ℝ^d \ {0}`? [...] Is
`dim ker(A) = 1` or is there another, linearly independent element?

`main` states that the answer to the first question is yes. A disproof is a matrix with the
three properties and a vector `x` with `x^T A x < 0`.

Translation choices:
* `A : Matrix (Fin d) (Fin d) ℝ`; weak diagonal dominance is `∑_{j ≠ i} |a_ij| ≤ |a_ii|` for
  every row `i`, and the zero row sums are `∑_j a_ij = 0`; both are assumed, as in the source;
* the "no decoupling" property is stated as written, with a general `R ∈ GL(d, ℝ)` (`IsUnit R`).
  A block-diagonal `diag(B, C)` with blocks of sizes `d - k` and `k`, `1 ≤ k ≤ d - 1`, is, up to
  a permutation of the basis (which is absorbed into `R`), a matrix `D` with `D i j = 0` whenever
  exactly one of `i, j` lies in a set `S` of indices with `S` nonempty and `S ≠ univ`. The
  permutation reading mentioned in the source ("switching two rows and the corresponding
  columns") is the special case where `R` is a permutation matrix, so the stated hypothesis is the
  stronger of the two;
* positive semi-definiteness is `0 ≤ x ⬝ᵥ (A *ᵥ x)` for every `x` (the case `x = 0` is trivial);
* the second question (`dim ker A = 1`) is not stated.
-/

namespace OMA.S_mo_237999

open Matrix

/-- A weakly diagonally dominant real matrix with zero row sums that admits no decoupling
`A = R · diag(B, C) · Rᵀ` is positive semi-definite. -/
theorem main :
    ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ),
      (∀ i, ∑ j, A i j = 0) →
      (∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ |A i i|) →
      (¬ ∃ (R D : Matrix (Fin d) (Fin d) ℝ) (S : Finset (Fin d)), IsUnit R ∧ S.Nonempty ∧
          S ≠ Finset.univ ∧ (∀ i j, (i ∈ S ↔ j ∉ S) → D i j = 0) ∧ A = R * D * Rᵀ) →
      ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  sorry

end OMA.S_mo_237999
