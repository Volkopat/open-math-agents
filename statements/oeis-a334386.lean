import Mathlib

/-!
# OEIS A334386: equilateral triangles meeting all four faces

Source: https://oeis.org/A334386 (Peter Kagey, OEIS Foundation, CC BY-SA 4.0).
Credit: @gdyan2022

Use the affine slice of four-dimensional Euclidean space whose nonnegative
coordinates sum to n-1. The integer points form the tetrahedral grid with
n points on each edge. The coordinate hyperplanes cut out its four faces.
-/

namespace OMA.S_oeis_a334386

/-- Four integer barycentric coordinates, each between zero and n-1. -/
abbrev Point (n : ℕ) := Fin 4 → Fin n

def grid (n : ℕ) : Finset (Point n) :=
  Finset.univ.filter fun x => ∑ i, (x i).val = n - 1

/-- Squared Euclidean distance in the affine slice, up to a common scale. -/
def squaredDist {n : ℕ} (x y : Point n) : ℕ :=
  ∑ i, (Nat.dist (x i).val (y i).val) ^ 2

/-- Unordered triples with all three side lengths equal, meeting each face.
A triangle in a closed half-space meets its boundary exactly when at least
one of the triangle's vertices is on that boundary. -/
def triangles (n : ℕ) : Finset (Finset (Point n)) :=
  ((grid n).powersetCard 3).filter fun t =>
    (∀ i : Fin 4, ∃ x ∈ t, (x i).val = 0) ∧
    ∀ x ∈ t, ∀ y ∈ t, ∀ z ∈ t, x ≠ y → y ≠ z → z ≠ x →
      squaredDist x y = squaredDist x z

theorem main : ∀ n : ℕ, 0 < n → (triangles n).card ≡ 4 * (n - 1) [MOD 12] := by
  sorry

end OMA.S_oeis_a334386
