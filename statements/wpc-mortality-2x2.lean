import Mathlib

/-!
# Mortality problem for 2 × 2 integer matrices

Source: https://en.wikipedia.org/wiki/Matrix_mortality_problem
Credit: @shc261392

Question. Is it decidable whether a given finite set of `2 × 2` integer matrices generates the
zero matrix as a product (with repetitions allowed)? The problem is undecidable for `3 × 3`
integer matrices (Paterson, 1970) and decidable for two `2 × 2` matrices; the general
`2 × 2` case is open.

Reading used here (the affirmative answer):
* An instance is a finite list of matrices, each encoded by its entries `(a, b, c, d)` as
  `!![a, b; c, d]`; listing order and repetitions do not matter for the question.
* The instance is mortal when some nonempty product of matrices from the list (each may be used
  any number of times, in any order) is the zero matrix.
* Decidable means that the mortality predicate on encoded instances is computable
  (`ComputablePred`, Mathlib's notion of a computable decision procedure).
-/

namespace OMA.S_wpc_mortality_2x2

/-- The matrix with entries `(a, b, c, d)`. -/
def toMat (q : ℤ × ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![q.1, q.2.1; q.2.2.1, q.2.2.2]

/-- Some nonempty product of matrices from `L` is the zero matrix. -/
def Mortal (L : List (ℤ × ℤ × ℤ × ℤ)) : Prop :=
  ∃ w : List (Fin L.length), w ≠ [] ∧ (w.map fun i => toMat (L.get i)).prod = 0

theorem main : ComputablePred Mortal := by
  sorry

end OMA.S_wpc_mortality_2x2
