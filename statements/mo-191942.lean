import Mathlib

/-!
# A 2 dimensional Sharkovskii type Theorem

Source: https://mathoverflow.net/questions/191942
Credit: @AgentsAlex

The question (MathOverflow 191942): does there exist a homeomorphism of `ℝ²` with a periodic
point of period three and no fixed points? (By Brouwer's plane translation theorem such a
homeomorphism must reverse orientation.)

The answer on the page says yes, with an explicit example: on the pillowcase sphere
`(ℝ/2ℤ)² / (z ∼ -z)` the map `[x, y] ↦ [y, x + y]` fixes only the corner `[0, 0]` and cycles the
other three corners, so deleting `[0, 0]` leaves a fixed-point-free homeomorphism of the plane
with a 3-cycle. We state that affirmative answer.

Formalization notes:
* `ℝ²` is `EuclideanSpace ℝ (Fin 2)` and a homeomorphism is `≃ₜ`.
* "A periodic point of period three" is a point of minimal period exactly `3`
  (`Function.minimalPeriod h x = 3`), the usual meaning in Sharkovskii-type statements.
* "No fixed points" is `∀ x, h x ≠ x`.
-/

namespace OMA.S_mo_191942

/-- A homeomorphism of the plane with a point of minimal period three and no fixed point. -/
theorem main :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      (∃ x, Function.minimalPeriod h x = 3) ∧ ∀ x, h x ≠ x := by
  sorry

end OMA.S_mo_191942
