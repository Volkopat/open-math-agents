import Mathlib

/-!
# Dirac's Conjecture

Source: https://www.openproblemgarden.org/op/diracs_conjecture
Credit: @ishaanzee

**Conjecture** (G. A. Dirac). For every set `P` of `n` points in the plane, not all collinear,
there is a point in `P` contained in at least `n/2 - c` lines determined by `P`, for some constant
`c`.

(Beck and Szemerédi–Trotter proved the bound `n/c` for a large constant `c`; Han improved it to
`n/3`.)

Formalization: the plane is `EuclideanSpace ℝ (Fin 2)`; `P` is a finite set that is not
`Collinear`. The lines determined by `P` that contain a point `p ∈ P` are exactly the lines
`affineSpan ℝ {p, q}` for `q ∈ P`, `q ≠ p`; we count the distinct ones (`Set.ncard`). The constant
`c` is universal (independent of `P`).
-/

namespace OMA.S_opg_diracs_conjecture

/-- The number of distinct lines determined by `P` that pass through `p`. -/
noncomputable def linesThrough (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    ∃ q ∈ P, q ≠ p ∧ L = affineSpan ℝ {p, q}}.ncard

/-- **Dirac's conjecture**: some point lies on at least `n/2 - c` of the lines determined by a
non-collinear set of `n` points. -/
theorem main : ∃ c : ℝ, ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
    ¬ Collinear ℝ (P : Set (EuclideanSpace ℝ (Fin 2))) →
      ∃ p ∈ P, (P.card : ℝ) / 2 - c ≤ (linesThrough P p : ℝ) := by
  sorry

end OMA.S_opg_diracs_conjecture
