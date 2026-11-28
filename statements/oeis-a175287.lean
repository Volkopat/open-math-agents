import Mathlib

/-!
# A175287: Partial sums of ceiling(n^2/4).

Source: https://oeis.org/A175287
Credit: @Squee451

Data (offset 0): 0, 1, 2, 5, 9, 16, 25, 38, 54, 75, 100, 131, 167, 210, 259, 316, 380, 453, 534, 625, 725, ...

The entry's comment: Conjecture: a(n) is the number of perimeter-magic (hollow) triangles of order 3
with magic sum n+2. Order 3 means each of the 3 edges has 3 elements >=1; the triangle has 6
elements. The elements do not need to be distinct, and triangles obtained by rotations are counted
only once. The triangle (read ccw) for magic sum 3 has elements 1 1 1 1 1 1. The 2 triangles with
magic sum 4 are 1 1 2 1 1 2 and 1 2 1 2 1 2.

Conventions.
* A triangle is its six elements read counterclockwise around the perimeter, `t 0, ..., t 5`, with
  the corners at positions 0, 2, 4, so that the three edges are `(t 0, t 1, t 2)`, `(t 2, t 3, t 4)`
  and `(t 4, t 5, t 0)`. It is perimeter-magic with magic sum `s` when every element is at least 1
  and every edge sums to `s`. Every element is then at most `s`, so the elements are taken in
  `Fin (s + 1)`.
* A rotation of the triangle shifts the reading by two positions; `orbit t` is the set of the three
  rotations of `t`, and the triangles are counted up to rotation by counting distinct orbits.
  Reflections are not identified (the entry only mentions rotations).
* `a n` is the sum of `ceiling(j^2/4)` for `j = 0, ..., n`, with `(j^2 + 3) / 4` (floor division)
  equal to that ceiling.
-/

namespace OMA.S_oeis_a175287

/-- A175287: partial sums of `ceiling(j^2/4)`. -/
def a (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), (j ^ 2 + 3) / 4

/-- The six elements, read around the perimeter, form a perimeter-magic triangle with magic sum `s`. -/
def Magic (s : ℕ) (t : Fin 6 → Fin (s + 1)) : Prop :=
  (∀ i, 1 ≤ (t i).val) ∧ (t 0).val + (t 1).val + (t 2).val = s ∧
    (t 2).val + (t 3).val + (t 4).val = s ∧ (t 4).val + (t 5).val + (t 0).val = s

instance (s : ℕ) : DecidablePred (Magic s) := fun t => by
  unfold Magic
  infer_instance

/-- The three rotations of a triangle. -/
def orbit {s : ℕ} (t : Fin 6 → Fin (s + 1)) : Finset (Fin 6 → Fin (s + 1)) :=
  {t, fun i => t (i + 2), fun i => t (i + 4)}

/-- The number of perimeter-magic triangles of order 3 with magic sum `s`, up to rotation. -/
def triangles (s : ℕ) : ℕ := ((Finset.univ.filter (Magic s)).image orbit).card

theorem main : ∀ n : ℕ, a n = triangles (n + 2) := by
  sorry

end OMA.S_oeis_a175287
