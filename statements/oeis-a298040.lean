import Mathlib

/-!
# A298040: Coordination sequence of Dual(4.6.12) tiling with respect to a tetravalent node.

Source: https://oeis.org/A298040
Tiling: Dual(4.6.12), see Grünbaum and Shephard, Tilings and Patterns (1987), Fig. 2.7.1, and
https://oeis.org/A296368/a296368_2.png (overview of the Laves tilings with their A-numbers).

Conjectures stated here (OEIS A298040):
  Conjectures from Colin Barker, Apr 01 2020: G.f.: (1 + 4*x + 18*x^2 + 16*x^3 + x^4 - 4*x^5) / ((1 - x)^2*(1 + x)^2).
  a(n) = (9 + (-1)^n)*n for n>1.
  a(n) = 2*a(n-2) - a(n-4) for n>5.

The tiling Dual(4.6.12) (the kisrhombille tiling, Laves tiling [4.6.12]) is the barycentric
subdivision of the regular hexagonal tiling. Its nodes are the centres of the hexagons (12-valent),
the vertices of the hexagons (hexavalent) and the midpoints of the hexagon edges (tetravalent).
Every triangle of the subdivision has one node of each kind, and its three sides are the edges:
a centre is joined to the 6 vertices and the 6 edge midpoints of its hexagon, and a hexagon vertex
is joined to the midpoints of the 3 hexagon edges through it.
Put the hexagon centres at the lattice spanned by t1 = (1, 0) and t2 = (1/2, √3/2). Then the
hexagon vertices are the centroids of the lattice triangles and the edge midpoints are the midpoints
of lattice edges. The vertex (x, y, i) is the point (x + u) t1 + (y + w) t2, where (u, w) is:
  i = 0: (0, 0), hexagon centre (12-valent)
  i = 1: (1/3, 1/3), hexagon vertex (hexavalent)
  i = 2: (2/3, 2/3), hexagon vertex (hexavalent)
  i = 3: (1/2, 0), edge midpoint (tetravalent)
  i = 4: (0, 1/2), edge midpoint (tetravalent)
  i = 5: (1/2, 1/2), edge midpoint (tetravalent)
Edges: centre to hexagon vertex at distance 1/√3, centre to midpoint at distance 1/2, hexagon
vertex to midpoint at distance 1/(2√3).
`adj i` lists the neighbours of (0, 0, i) as triples (dx, dy, j). The edge set is invariant
under the translations, so (x, y, i) is adjacent exactly to the (x + dx, y + dy, j).
From the base vertex (0, 0, 3) this graph reproduces all 55 terms of the OEIS data of A298040.
The FORMULA section also has Conjecture: For n>0, a(n)=10n if n even, otherwise 8n. As written it
fails at n = 1 (a(1) = 4); for n > 1 it is the closed form (9 + (-1)^n)*n stated here.
-/

namespace OMA.S_oeis_a298040

/-- `(x, y, i)` is the vertex `i` of the fundamental cell, translated by `x t1 + y t2`. -/
abbrev Vertex := ℤ × ℤ × Fin 6

/-- The neighbours of `(0, 0, i)`, as `(dx, dy, j)`. -/
def adj : Fin 6 → List (ℤ × ℤ × Fin 6) := ![
  [(-1, -1, 2), (-1, 0, 1), (-1, 0, 2), (-1, 0, 3), (-1, 0, 5), (0, -1, 1), (0, -1, 2), (0, -1, 4), (0, -1, 5), (0, 0, 1), (0, 0, 3), (0, 0, 4)],
  [(0, 0, 0), (0, 0, 3), (0, 0, 4), (0, 0, 5), (0, 1, 0), (1, 0, 0)],
  [(0, 0, 5), (0, 1, 0), (0, 1, 3), (1, 0, 0), (1, 0, 4), (1, 1, 0)],
  [(0, -1, 2), (0, 0, 0), (0, 0, 1), (1, 0, 0)],
  [(-1, 0, 2), (0, 0, 0), (0, 0, 1), (0, 1, 0)],
  [(0, 0, 1), (0, 0, 2), (0, 1, 0), (1, 0, 0)]]

def neighbors (v : Vertex) : Finset Vertex :=
  ((adj v.2.2).map (fun d => (v.1 + d.1, v.2.1 + d.2.1, d.2.2))).toFinset

/-- The vertices at graph distance at most `n` from the base vertex `(0, 0, 3)`. -/
def ball : ℕ → Finset Vertex
  | 0 => {(0, 0, 3)}
  | n + 1 => ball n ∪ (ball n).biUnion neighbors

/-- The coordination sequence: the number of vertices at distance exactly `n`. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => ((ball (n + 1)).card : ℤ) - (ball n).card

open PowerSeries in
theorem main :
    mk a * ((1 - X)^2*(1 + X)^2 : PowerSeries ℤ) = 1 + 4*X + 18*X^2 + 16*X^3 + X^4 - 4*X^5 ∧
    (∀ n : ℕ, 1 < n → a n = (9 + (-1) ^ n) * (n : ℤ)) ∧
    (∀ n : ℕ, 5 < n → a n = 2 * a (n - 2) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a298040
