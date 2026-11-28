import Mathlib

/-!
# Diagonalizable block upper triangular matrices with diagonal blocks of finite order

Source: https://mathoverflow.net/questions/151738
Credit: @koolkao

Question (user44128, MathOverflow 151738, 2013; CC BY-SA 3.0). If I take a diagonalizable block
upper triangular matrix whose diagonal blocks are of finite order, is it true that away from the
leading block diagonal, the matrix is zero?

`main` states that the answer is yes. A disproof is such a matrix with a nonzero entry outside
the diagonal blocks.

Translation choices:
* the field is `ℂ` (the source names none; "finite order" and "diagonalizable" are read in the
  usual complex setting);
* a block matrix with `k` diagonal blocks of sizes `s 0, …, s (k - 1)` is a matrix indexed by
  `Σ i : Fin k, Fin (s i)`, the block of an index `x` being `x.1`; block upper triangular means
  `M x y = 0` whenever `y.1 < x.1`;
* the `i`-th diagonal block is `M.submatrix (Sigma.mk i) (Sigma.mk i)`, and it has finite order
  when some positive power of it is the identity;
* diagonalizable means `P⁻¹ * M * P = diagonal d` for some invertible `P` (`IsUnit P`) and some
  `d`;
* "away from the leading block diagonal, the matrix is zero" is `M x y = 0` whenever
  `x.1 ≠ y.1`.
-/

namespace OMA.S_mo_151738

open Matrix

/-- A diagonalizable block upper triangular complex matrix whose diagonal blocks have finite
order is block diagonal. -/
theorem main :
    ∀ (k : ℕ) (s : Fin k → ℕ) (M : Matrix (Σ i, Fin (s i)) (Σ i, Fin (s i)) ℂ),
      (∀ x y : Σ i, Fin (s i), y.1 < x.1 → M x y = 0) →
      (∀ i : Fin k, ∃ m : ℕ, 0 < m ∧ (M.submatrix (Sigma.mk i) (Sigma.mk i)) ^ m = 1) →
      (∃ (P : Matrix (Σ i, Fin (s i)) (Σ i, Fin (s i)) ℂ) (d : (Σ i, Fin (s i)) → ℂ),
        IsUnit P ∧ P⁻¹ * M * P = diagonal d) →
      ∀ x y : Σ i, Fin (s i), x.1 ≠ y.1 → M x y = 0 := by
  sorry

end OMA.S_mo_151738
