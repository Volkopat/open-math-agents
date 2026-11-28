import Mathlib

/-!
# Normalizing a cyclic tridiagonal matrix by a triangular similarity

Source: https://mathoverflow.net/questions/194396
Credit: @koolkao

Question (Ludwig, MathOverflow 194396, 2015; CC BY-SA 3.0). Consider the `n × n` real matrix `A`
with diagonal `α_1, …, α_n`, superdiagonal `β_1, …, β_{n-1}`, subdiagonal `γ_1, …, γ_{n-1}`,
and corner entries `A_{1,n} = γ_n`, `A_{n,1} = β_n` (all other entries `0`). Is there a
triangular matrix `T` such that `N = T⁻¹ A T` is a normal matrix (that is `N Nᵀ = Nᵀ N`)? The
answer is false if the choice of the coefficients `α_i`, `β_i` and `γ_i` is arbitrary. What can
we say if we make the additional assumption that `α_i ≠ 0`, `β_i ≠ 0` and `γ_i ≠ 0` for all `i`?

`main` states that, under the additional assumption, such a `T` always exists. A disproof is an
`n` and nonzero coefficients for which no triangular `T` makes `T⁻¹ A T` normal.

Translation choices:
* the size is `n = m + 3 ≥ 3`, indices are `Fin (m + 3)` with cyclic successor `i + 1`; for
  `n ≥ 3` the diagonal, the cyclic superdiagonal `(i, i + 1)` (entry `β_i`, including
  `(n, 1)`) and the cyclic subdiagonal `(i + 1, i)` (entry `γ_i`, including `(1, n)`) are
  disjoint, which is the source's pattern (for `n = 2` the corner entries would collide with
  `β_1`, `γ_1`);
* the matrices are real; "triangular" is upper or lower triangular, and `T` is invertible
  (`IsUnit T.det`), so `T⁻¹` is the usual inverse;
* `main` is the question under the source's additional assumption (all coefficients nonzero);
  it is weaker than the original question with arbitrary coefficients, which the source already
  answers negatively; the source's second question (the form of `T`) is not stated.
-/

namespace OMA.S_mo_194396

open Matrix

/-- For every `n ≥ 3` and all nonzero coefficients, the cyclic tridiagonal matrix is
similar to a normal matrix through a triangular matrix. -/
theorem main :
    ∀ (m : ℕ) (α β γ : Fin (m + 3) → ℝ), (∀ i, α i ≠ 0 ∧ β i ≠ 0 ∧ γ i ≠ 0) →
      ∃ T : Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ,
        ((∀ i j, j < i → T i j = 0) ∨ (∀ i j, i < j → T i j = 0)) ∧ IsUnit T.det ∧
        let A : Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ := fun i j =>
          if i = j then α i else if j = i + 1 then β i else if i = j + 1 then γ j else 0
        (T⁻¹ * A * T) * (T⁻¹ * A * T)ᵀ = (T⁻¹ * A * T)ᵀ * (T⁻¹ * A * T) := by
  sorry

end OMA.S_mo_194396
