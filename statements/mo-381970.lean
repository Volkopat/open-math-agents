import Mathlib

/-!
# Averaging determinants of cyclic block matrices over corner permutations

Source: Charles Cao, MathOverflow question 381970 (2021),
https://mathoverflow.net/questions/381970

This states the finite-average claim in the final edit of the source, using its
last displayed block matrix. The internal off-diagonal blocks are scalar
multiples of the identity; the upper-right block is a scalar multiple of an
arbitrary permutation matrix, and the lower-left block is its transpose.

The unspecified scalar coefficients are read as real numbers. The integer m is
at least 3, so the two corner blocks do not overlap the internal adjacent blocks;
the permutation size M satisfies 0 < M < 10, preserving the range of the source's
explicit finite-average claim. The average is uniform over all M! permutations.
No large-M limit is asserted. The linked MSE post's separate
asymptotic question is not part of this statement.

The source's original pointwise-invariance proposal is not asserted here: its
later edit already questions that proposal and advances the average claim.
-/

namespace OMA.S_mo_381970

open scoped BigOperators

noncomputable section

/-- The source's final cyclic block matrix, with zero-based block indices.
`d r` is the diagonal coefficient. `e r` is the coefficient joining block r to
block r+1 when r<m-1; `e (m-1)` is the coefficient of the two corner blocks. -/
def cyclicBlockMatrix (m M : ℕ) (d e : Fin m → ℝ)
    (σ : Equiv.Perm (Fin M)) :
    Matrix (Fin m × Fin M) (Fin m × Fin M) ℝ :=
  fun i j =>
    if i.1 = j.1 then
      d i.1 * (1 : Matrix (Fin M) (Fin M) ℝ) i.2 j.2
    else if i.1.val + 1 = j.1.val then
      e i.1 * (1 : Matrix (Fin M) (Fin M) ℝ) i.2 j.2
    else if j.1.val + 1 = i.1.val then
      e j.1 * (1 : Matrix (Fin M) (Fin M) ℝ) i.2 j.2
    else if i.1.val = 0 ∧ j.1.val + 1 = m then
      e j.1 * σ.permMatrix ℝ i.2 j.2
    else if j.1.val = 0 ∧ i.1.val + 1 = m then
      e i.1 * σ.permMatrix ℝ j.2 i.2
    else 0

/-- Uniform finite average over all choices of the corner permutation. -/
def averageDeterminant (m M : ℕ) (d e : Fin m → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin M), (cyclicBlockMatrix m M d e σ).det) /
    (Fintype.card (Equiv.Perm (Fin M)) : ℝ)

theorem main :
    ∀ (m M : ℕ), 3 ≤ m → 0 < M → M < 10 → ∀ (d e : Fin m → ℝ),
      averageDeterminant m M d e =
        (cyclicBlockMatrix m M d e 1).det := by
  sorry

end

end OMA.S_mo_381970
