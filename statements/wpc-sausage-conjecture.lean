import Mathlib

/-!
# Fejes Tóth's sausage conjecture

Source: https://en.wikipedia.org/wiki/Sausage_conjecture
Credit: @mgv27

For n ≥ 5 and every k, the convex hull of k non-overlapping unit balls in ℝⁿ has the smallest
possible volume when the centres lie on a line (a sausage). Proved for n ≥ 42 by Betke and
Henk (1998); open for 5 ≤ n ≤ 41.

Formalization notes:
* ℝⁿ is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`.
* Non-overlapping closed unit balls: centres `c i` at pairwise distance `≥ 2`.
* The sausage has centres `2 i e₀` for `i < k` (consecutive balls touching), which is the
  minimal-volume collinear configuration.
* `main` states the full conjecture (all `n ≥ 5`, all `k ≥ 1`).
-/

namespace OMA.S_wpc_sausage_conjecture

open MeasureTheory Metric

/-- Volume of the convex hull of the closed unit balls centred at the points `c i`. -/
noncomputable def hullVolume {n k : ℕ} (c : Fin k → EuclideanSpace ℝ (Fin n)) : ENNReal :=
  volume (convexHull ℝ (⋃ i, closedBall (c i) 1))

/-- The sausage: centres `2 i e₀`, `i < k`, on a line (requires `n ≥ 1`). -/
noncomputable def sausage (n k : ℕ) (hn : 0 < n) : Fin k → EuclideanSpace ℝ (Fin n) :=
  fun i => EuclideanSpace.single ⟨0, hn⟩ (2 * (i : ℝ))

/-- Sausage conjecture: for `n ≥ 5`, the sausage minimizes the hull volume. -/
theorem main : ∀ (n : ℕ) (hn : 5 ≤ n) (k : ℕ), 1 ≤ k →
    ∀ c : Fin k → EuclideanSpace ℝ (Fin n), (Pairwise fun i j => 2 ≤ dist (c i) (c j)) →
    hullVolume (sausage n k (by omega)) ≤ hullVolume c := by
  sorry

end OMA.S_wpc_sausage_conjecture
