import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

namespace OMA.S_oeis_a175769

/-- Squared Euclidean distance between two points in `ℝ^3`. -/
def distSq3 (p q : ℝ × ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2

/-- A finite set `S ⊆ ℝ^3` is an isosceles set if every three distinct points of `S`
determine at least two equal pairwise distances (equivalently, equal squared distances). -/
def IsIsoscelesSet3 (S : Finset (ℝ × ℝ × ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
    distSq3 p q = distSq3 p r ∨ distSq3 p q = distSq3 q r ∨ distSq3 p r = distSq3 q r

/-- Conjecture (H. S. M. Coxeter; OEIS A175769): Every isosceles set in Euclidean 3-space
`ℝ^3` has cardinality at most `7` (disproved by L. M. Kelly, 1947, who constructed an
8-point isosceles set). -/
theorem main : ∀ S : Finset (ℝ × ℝ × ℝ), IsIsoscelesSet3 S → S.card ≤ 7 := by
  sorry

end OMA.S_oeis_a175769
