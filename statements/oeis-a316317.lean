import Mathlib

/-!
# A316317: Coordination sequence for trivalent node in chamfered version of square grid.

Source: https://oeis.org/A316317
Tiling: the chamfered square grid, see also https://oeis.org/A316316 (tetravalent node).

Conjectures stated here (OEIS A316317):
  Apparently, a(n + 12) = a(n) + 40 for any n > 0. - Rémy Sigrist, Jun 30 2018
  G.f. (assuming above conjecture): (1+x)^2*(1+3*x^2+x^4)/((1-x)^2*(1+x+x^2)*(1+x^2)). - Robert Israel, Jul 01 2018
  a(n) = (30*n - 9*A056594(n-1) + 6*A102283(n))/9 for n > 0. - Conjectured by Stefano Spezia, Jun 12 2021
  Here A056594 is the sequence with period 4: repeat [1, 0, -1, 0] (offset 0), and A102283 the
  sequence with period 3: repeat [0, 1, -1] (offset 0).

The chamfered square grid: start from the square grid Z^2 and chamfer it, so that every square
face shrinks to a smaller concentric square and every edge of the grid becomes a hexagon. The
nodes are the grid points (tetravalent) and the corners of the small squares (trivalent). A grid
point is joined to the nearest corner of each of the 4 small squares around it, and each small
square keeps its 4 sides. With t1 = (1, 0) and t2 = (0, 1), the vertex (x, y, i) is the point
(x + u, y + w), where (u, w) is:
  i = 0: (0, 0), grid point (tetravalent)
  i = 1: (7/20, 7/20), i = 2: (13/20, 7/20), i = 3: (13/20, 13/20), i = 4: (7/20, 13/20),
         the corners of the small square in the cell (trivalent)
Edges: grid point to corner at distance 7√2/20 (one corner of each of the 4 adjacent small
squares), and the 4 sides of length 3/10 of each small square. Any other square size in (0, 1)
gives the same graph. This graph also reproduces the data of A316316 (tetravalent node).
`adj i` lists the neighbours of (0, 0, i) as triples (dx, dy, j). The edge set is invariant
under the translations, so (x, y, i) is adjacent exactly to the (x + dx, y + dy, j).
From the base vertex (0, 0, 1) this graph reproduces all 59 terms of the OEIS data of A316317.
-/

namespace OMA.S_oeis_a316317

/-- `(x, y, i)` is the vertex `i` of the fundamental cell, translated by `x t1 + y t2`. -/
abbrev Vertex := ℤ × ℤ × Fin 5

/-- The neighbours of `(0, 0, i)`, as `(dx, dy, j)`. -/
def adj : Fin 5 → List (ℤ × ℤ × Fin 5) := ![
  [(-1, -1, 3), (-1, 0, 2), (0, -1, 4), (0, 0, 1)],
  [(0, 0, 0), (0, 0, 2), (0, 0, 4)],
  [(0, 0, 1), (0, 0, 3), (1, 0, 0)],
  [(0, 0, 2), (0, 0, 4), (1, 1, 0)],
  [(0, 0, 1), (0, 0, 3), (0, 1, 0)]]

def neighbors (v : Vertex) : Finset Vertex :=
  ((adj v.2.2).map (fun d => (v.1 + d.1, v.2.1 + d.2.1, d.2.2))).toFinset

/-- The vertices at graph distance at most `n` from the base vertex `(0, 0, 1)`. -/
def ball : ℕ → Finset Vertex
  | 0 => {(0, 0, 1)}
  | n + 1 => ball n ∪ (ball n).biUnion neighbors

/-- The coordination sequence: the number of vertices at distance exactly `n`. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => ((ball (n + 1)).card : ℤ) - (ball n).card

/-- A056594: period 4, repeat [1, 0, -1, 0], offset 0. -/
def A056594 (n : ℕ) : ℤ := if n % 4 = 0 then 1 else if n % 4 = 2 then -1 else 0

/-- A102283: period 3, repeat [0, 1, -1], offset 0. -/
def A102283 (n : ℕ) : ℤ := if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 0 < n → a (n + 12) = a n + 40) ∧
    mk a * ((1-X)^2*(1+X+X^2)*(1+X^2) : PowerSeries ℤ) = (1+X)^2*(1+3*X^2+X^4) ∧
    (∀ n : ℕ, 0 < n → a n = (30 * (n : ℤ) - 9 * A056594 (n - 1) + 6 * A102283 n) / 9) := by
  sorry

end OMA.S_oeis_a316317
