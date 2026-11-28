import Mathlib

/-!
# OEIS A311101: Wu's conjectures for the coordination sequence Gal.3.47.1

Source: https://oeis.org/A311101 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311101 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.3.47.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 12, 15, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 24 2019: (Start)
a(n) = 3*a(n-1) - 4*a(n-2) + 3*a(n-3) - a(n-4) for n > 8.
G.f.: (-x^8 + 2*x^7 - 2*x^6 + 2*x^5 + x^3 + x + 1)/((x - 1)^2*(x^2 - x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 47 of Galebach's list of the 61 3-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/03/3/eu 4a 5c 6i 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.4.12, 3.3.3.4.4,
  3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and
  computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file only,
  from the base vertex below; and this is the only 3-uniform file that holds the listed terms of
  every entry Gal.3.47.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 24) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 3.3.4.12; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311101

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 24 × Fin 24 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 11, (-1), (-1)),
    (0, 12, 0, 0),
    (0, 19, (-1), 0),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 12, 0, 0),
    (1, 13, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 14, 0, 0),
    (2, 15, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 15, 0, 0),
    (3, 16, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 17, 0, 0),
    (4, 18, 0, 0),
    (5, 4, 0, 0),
    (5, 6, 0, (-1)),
    (5, 18, 0, 0),
    (5, 19, 0, 0),
    (6, 5, 0, 1),
    (6, 7, 0, 0),
    (6, 20, 0, 0),
    (6, 21, 0, 0),
    (7, 6, 0, 0),
    (7, 8, 0, 0),
    (7, 14, 0, 0),
    (7, 21, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 13, 0, 0),
    (8, 22, 0, 0),
    (9, 8, 0, 0),
    (9, 10, (-1), 0),
    (9, 17, (-1), 0),
    (9, 22, 0, 0),
    (10, 9, 1, 0),
    (10, 11, 0, 0),
    (10, 16, 0, 0),
    (10, 23, 0, 0),
    (11, 0, 1, 1),
    (11, 10, 0, 0),
    (11, 20, 0, 0),
    (11, 23, 0, 0),
    (12, 0, 0, 0),
    (12, 1, 0, 0),
    (12, 13, 0, 0),
    (12, 18, (-1), 0),
    (12, 19, (-1), 0),
    (12, 22, 0, 0),
    (13, 1, 0, 0),
    (13, 8, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, 0),
    (13, 22, 0, 0),
    (14, 2, 0, 0),
    (14, 7, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 0),
    (14, 21, 0, 0),
    (15, 2, 0, 0),
    (15, 3, 0, 0),
    (15, 14, 0, 0),
    (15, 16, 0, 0),
    (15, 21, 0, 0),
    (15, 23, 0, 0),
    (16, 3, 0, 0),
    (16, 10, 0, 0),
    (16, 15, 0, 0),
    (16, 17, 0, 0),
    (16, 23, 0, 0),
    (17, 4, 0, 0),
    (17, 9, 1, 0),
    (17, 16, 0, 0),
    (17, 18, 0, 0),
    (17, 22, 1, 0),
    (18, 4, 0, 0),
    (18, 5, 0, 0),
    (18, 12, 1, 0),
    (18, 17, 0, 0),
    (18, 19, 0, 0),
    (18, 22, 1, 0),
    (19, 0, 1, 0),
    (19, 5, 0, 0),
    (19, 12, 1, 0),
    (19, 18, 0, 0),
    (19, 20, 0, (-1)),
    (20, 6, 0, 0),
    (20, 11, 0, 0),
    (20, 19, 0, 1),
    (20, 21, 0, 0),
    (20, 23, 0, 0),
    (21, 6, 0, 0),
    (21, 7, 0, 0),
    (21, 14, 0, 0),
    (21, 15, 0, 0),
    (21, 20, 0, 0),
    (21, 23, 0, 0),
    (22, 8, 0, 0),
    (22, 9, 0, 0),
    (22, 12, 0, 0),
    (22, 13, 0, 0),
    (22, 17, (-1), 0),
    (22, 18, (-1), 0),
    (23, 10, 0, 0),
    (23, 11, 0, 0),
    (23, 15, 0, 0),
    (23, 16, 0, 0),
    (23, 20, 0, 0),
    (23, 21, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 24) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 24) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 24 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 24 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 8. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 - X + 1)) =
      -X ^ 8 + 2 * X ^ 7 - 2 * X ^ 6 + 2 * X ^ 5 + X ^ 3 + X + 1 ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 3 * a (n - 1) - 4 * a (n - 2) + 3 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a311101
