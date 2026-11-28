import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# A conjecture on simplex

Source: https://mathoverflow.net/questions/304392
Credit: @Spinausore

Use affine coordinates in which the vertices are zero and the coordinate vectors.
The Euclidean metric in those coordinates is an arbitrary symmetric positive
definite form. A single parameter on each unoriented edge is encoded by using
complementary parameters in its two orientations. The reflected point is required
to lie in the affine hyperplane of the opposite face, as in the source.
-/

open scoped BigOperators

namespace OMA.S_mo_304392

def pairing {n : ℕ} (metric : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ j, ∑ k, x j * metric j k * y k

def vertex {n : ℕ} (i : Fin (n + 1)) (k : Fin n) : ℝ :=
  if k.castSucc = i then 1 else 0

def segmentPoint {n : ℕ} (i j : Fin (n + 1)) (t : ℝ) (k : Fin n) : ℝ :=
  (1 - t) * vertex i k + t * vertex j k

def faceCoordinate {n : ℕ} (i : Fin (n + 1)) (x : Fin n → ℝ) : ℝ :=
  if h : i.val < n then x ⟨i.val, h⟩ else 1 - ∑ k, x k

noncomputable def reflected {n : ℕ} (metric : Fin n → Fin n → ℝ) (normal : Fin n → ℝ)
    (offset : ℝ) (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  x k - (2 * (pairing metric normal x - offset) / pairing metric normal normal) * normal k

theorem main : ∀ (n : ℕ) (metric : Fin n → Fin n → ℝ),
    (∀ j k, metric j k = metric k j) →
    (∀ x : Fin n → ℝ, x ≠ 0 → 0 < pairing metric x x) →
    ∀ (t : Fin (n + 1) → Fin (n + 1) → ℝ)
      (normal : Fin (n + 1) → Fin n → ℝ) (offset : Fin (n + 1) → ℝ),
      (∀ i j, i ≠ j → 0 ≤ t i j ∧ t i j ≤ 1 ∧ t i j + t j i = 1) →
      (∀ i, normal i ≠ 0) →
      (∀ i j, i ≠ j → pairing metric (normal i) (segmentPoint i j (t i j)) = offset i) →
      (∀ i, faceCoordinate i (reflected metric (normal i) (offset i) (vertex i)) = 0) →
      ∀ i j, i ≠ j → t i j = 1 / 2 := by
  sorry

end OMA.S_mo_304392
