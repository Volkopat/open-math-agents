import Mathlib

/-!
# A101364: In the interior of a regular n-gon with all diagonals drawn, the number of points where exactly four diagonals intersect.

Source: https://oeis.org/A101364
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: An `n`-gon with `n = 30 * k` has `5 * n` interior points (excluding the center)
where 6 or 7 diagonals meet, and no interior point other than the center where more than 7
diagonals meet. If `k` is odd, 6 diagonals meet in `4 * n` points and 7 diagonals meet in `n`
points; if `k` is even, 6 diagonals meet in 0 points and 7 diagonals meet in `5 * n` points.
-/

namespace OMA.S_oeis_a101364

/-- The `j`-th vertex of the regular `n`-gon inscribed in the unit circle. -/
noncomputable def vertex (n : ℕ) (j : ZMod n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / (n : ℂ))

/-- Predicate asserting that `z` lies on the open diagonal between vertices `i` and `j`. -/
def OnOpenDiagonal (n : ℕ) (i j : ZMod n) (z : ℂ) : Prop :=
  i ≠ j ∧ i + 1 ≠ j ∧ j + 1 ≠ i ∧
  ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z = (1 - t) • vertex n i + t • vertex n j

/-- The number of diagonals of the regular `n`-gon passing through `z`. -/
noncomputable def diagCount (n : ℕ) (z : ℂ) : ℕ :=
  Set.ncard {e : Sym2 (ZMod n) | ∃ i j : ZMod n, e = s(i, j) ∧ OnOpenDiagonal n i j z}

/-- Interior non-center points of the regular `n`-gon where exactly `m` diagonals meet. -/
def interiorPointsWithMult (n m : ℕ) : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ ‖z‖ < 1 ∧ diagCount n z = m}

theorem main :
    ∀ k : ℕ, 1 ≤ k →
      let n := 30 * k
      (∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → diagCount n z ≤ 7) ∧
      (Odd k →
        Set.encard (interiorPointsWithMult n 6) = (4 * n : ℕ∞) ∧
        Set.encard (interiorPointsWithMult n 7) = (n : ℕ∞)) ∧
      (Even k →
        interiorPointsWithMult n 6 = ∅ ∧
        Set.encard (interiorPointsWithMult n 7) = (5 * n : ℕ∞)) := by
  sorry

end OMA.S_oeis_a101364
