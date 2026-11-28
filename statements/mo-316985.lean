import Mathlib

/-!
# An orthogonal basis of symmetric unitary matrices

For every positive size, does the complex vector space of symmetric matrices
have a Hilbert–Schmidt orthogonal basis consisting of unitary matrices?

[MathOverflow question](https://mathoverflow.net/questions/316985/existence-of-orthogonal-basis-of-symmetric-n-times-n-matrices-where-each-matr)
-/

namespace OMA.S_mo_316985

abbrev SquareMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ U : Fin ((n + 1).choose 2) → SquareMatrix n,
        (∀ i, U i ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
        LinearIndependent ℂ U ∧
        (∀ A : SquareMatrix n,
          A.IsSymm ↔ A ∈ Submodule.span ℂ (Set.range U)) ∧
        ∀ i j, i ≠ j → Matrix.trace (U i * (U j).conjTranspose) = 0 := by
  sorry

end OMA.S_mo_316985
