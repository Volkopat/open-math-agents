import Mathlib

/-!
# OEIS A000212: Interior crossings of region-maximizing cevians

Source: https://oeis.org/A000212
Reference: https://cs.uwaterloo.ca/journals/JIS/VOL29/Fried/fried21.pdf (Corollary 15)
Credit: @justusklocke-cloud
-/

namespace OMA.S_oeis_a000212

/-- A nondegenerate cevian joins a vertex to the relative interior of the opposite side. -/
structure Cevian (vertices : Fin 3 → ℝ × ℝ) where
  vertex : Fin 3
  endpoint : ℝ × ℝ
  endpoint_mem : endpoint ∈ openSegment ℝ (vertices (vertex + 1)) (vertices (vertex + 2))

def Cevian.points {vertices : Fin 3 → ℝ × ℝ} (c : Cevian vertices) : Set (ℝ × ℝ) :=
  segment ℝ (vertices c.vertex) c.endpoint

def triangleInterior (vertices : Fin 3 → ℝ × ℝ) : Set (ℝ × ℝ) :=
  interior (convexHull ℝ (Set.range vertices))

/-- A region is a connected component of the interior left after removing the cevians. -/
noncomputable def regionCount {vertices : Fin 3 → ℝ × ℝ} {n : ℕ}
    (c : Fin n → Cevian vertices) : ℕ∞ :=
  ENat.card (ConnectedComponents ↥(triangleInterior vertices \ ⋃ i, (c i).points))

/-- Count each interior point shared by two cevians once, even if more than two meet there. -/
noncomputable def crossingCount {vertices : Fin 3 → ℝ × ℝ} {n : ℕ}
    (c : Fin n → Cevian vertices) : ℕ∞ :=
  {p ∈ triangleInterior vertices |
    ∃ i j : Fin n, i ≠ j ∧ p ∈ (c i).points ∧ p ∈ (c j).points}.encard

def MaximizesRegions {vertices : Fin 3 → ℝ × ℝ} {n : ℕ}
    (c : Fin n → Cevian vertices) : Prop :=
  Function.Injective c ∧
    ∀ d : Fin n → Cevian vertices, Function.Injective d → regionCount d ≤ regionCount c

/-- Every arrangement maximizing the number of regions has `⌊n² / 3⌋` interior crossings. -/
theorem main : ∀ (n : ℕ) (vertices : Fin 3 → ℝ × ℝ), AffineIndependent ℝ vertices →
    (∃ c : Fin n → Cevian vertices, MaximizesRegions c) ∧
    (∀ c : Fin n → Cevian vertices, MaximizesRegions c → crossingCount c = ((n ^ 2 / 3 : ℕ) : ℕ∞)) := by
  sorry

end OMA.S_oeis_a000212
