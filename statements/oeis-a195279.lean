import Mathlib

/-!
# OEIS A195279: Barker's generating function and recurrence

Source: https://oeis.org/A195279 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Sep 14 2011), offset 1: Number of lower triangles of a 3 X 3 integer array
with each element differing from all of its vertical and horizontal neighbors by n or less and
triangles differing by a constant counted only once. Data: 171, 2125, 11319, 39609, 107811, ...
The formula section states: Conjectures from Colin Barker, Mar 01 2018: (Start) G.f.:
x*(171 + 1099*x + 1134*x^2 + 150*x^3 + 7*x^4 - x^5) / (1 - x)^6. a(n) = 6*a(n-1) - 15*a(n-2) +
20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* The lower triangle of a 3 X 3 array is its six cells (i, j) with j ≤ i, counted from 0: rows of
  1, 2 and 3 elements, as in the entry's examples. A triangle is stored as an array
  x : Fin 3 → Fin 3 → ℤ whose three entries above the diagonal are 0, so that each triangle has
  exactly one array. Two cells of the triangle are vertical neighbors when they share a column and
  their rows are adjacent, and horizontal neighbors when they share a row and their columns are
  adjacent; `nbr` lists these pairs in both orders, and `good n x` says that every element differs
  from each of its neighbors by n or less.
* Adding a constant to all six elements keeps a triangle good, and each class of triangles
  differing by a constant has exactly one member whose top element x 0 0 is 0 (the representative
  shown in the entry's examples), so `a n` counts the good arrays with x 0 0 = 0. The set is
  finite, since every element is within 4n of the top one, and `a n` is its `Set.ncard`. This
  reading reproduces all 25 listed terms, and a brute-force count over all six elements agrees for
  n = 1, 2, 3.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as
  A(x) (1 - x)^6 = x (171 + 1099x + 1134x^2 + 150x^3 + 7x^4 - x^5) in Z[[x]], which is equivalent
  because (1 - x)^6 has constant term 1. The recurrence is stated in the integers for n > 6, where
  every index n - k is at least 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..25), all the entry's listed terms.
-/

namespace OMA.S_oeis_a195279

open PowerSeries

/-- The cells (i, j) and (i', j') of a 3 X 3 array both lie in its lower triangle (j ≤ i and
j' ≤ i') and are vertical neighbors (same column, adjacent rows) or horizontal neighbors (same
row, adjacent columns). -/
def nbr (i j i' j' : Fin 3) : Prop :=
  j ≤ i ∧ j' ≤ i' ∧
    ((j = j' ∧ (i'.val = i.val + 1 ∨ i.val = i'.val + 1)) ∨
      (i = i' ∧ (j'.val = j.val + 1 ∨ j.val = j'.val + 1)))

/-- x is a lower triangle of a 3 X 3 integer array, stored as a 3 X 3 array whose entries above
the diagonal are 0, in which every element differs from each of its vertical and horizontal
neighbors in the triangle by n or less. -/
def good (n : ℕ) (x : Fin 3 → Fin 3 → ℤ) : Prop :=
  (∀ i j : Fin 3, i < j → x i j = 0) ∧ ∀ i j i' j' : Fin 3, nbr i j i' j' → |x i j - x i' j'| ≤ n

/-- A195279(n): adding a constant to every element keeps a triangle good, and each class of
triangles differing by a constant contains exactly one triangle whose top element x 0 0 is 0, so
the classes are counted by those triangles. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 3 → Fin 3 → ℤ | good n x ∧ x 0 0 = 0}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (171 + 1099 * X + 1134 * X ^ 2 + 150 * X ^ 3 + 7 * X ^ 4 - X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a195279
