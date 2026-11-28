import Mathlib

/-!
# The permanent conjecture

Source: https://www.openproblemgarden.org/op/the_permanent_conjecture
Credit: @ishaanzee

**Conjecture** (J. Kahn). If `A` is an invertible `n × n` matrix, then there is an `n × n`
submatrix `B` of `[A A]` so that `perm(B)` is nonzero.

Formalization:
* The source does not fix the field; the conjecture is stated for invertible matrices over an
  arbitrary field `F` (the motivating applications use `ℤ₃` and other finite fields).
* `[A A]` is the `n × 2n` matrix `Matrix.fromCols A A`, whose columns are indexed by
  `Fin n ⊕ Fin n` (the left copy and the right copy of `A`).
* An `n × n` submatrix keeps all `n` rows and `n` distinct columns; it is given by an injective
  choice of columns `c : Fin n → Fin n ⊕ Fin n`. The order of the chosen columns does not affect
  the permanent, so this is the usual notion of submatrix.
* `Matrix.permanent` is Mathlib's permanent `∑ σ, ∏ i, B (σ i) i`.
-/

namespace OMA.S_opg_the_permanent_conjecture

universe u

/-- **Kahn's permanent conjecture**: for every invertible square matrix `A` over a field, some
square submatrix of `[A A]` using all rows has nonzero permanent. -/
theorem main : ∀ (F : Type u) [Field F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F), IsUnit A.det →
    ∃ c : Fin n → Fin n ⊕ Fin n, Function.Injective c ∧
      (Matrix.of fun i j => Matrix.fromCols A A i (c j)).permanent ≠ 0 := by
  sorry

end OMA.S_opg_the_permanent_conjecture
