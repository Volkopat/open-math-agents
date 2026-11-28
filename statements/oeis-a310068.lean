import Mathlib

/-!
# OEIS A310068: Wu's conjectures for the coordination sequence Gal.4.25.1

Source: https://oeis.org/A310068 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A310068 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.25.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 3, 6, 10, 14, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 10 2018: (Start)
a(n) = a(n-1) - a(n-4) + 2*a(n-5) - a(n-6) + a(n-9) - a(n-10) for n > 10.
G.f.: (x + 1)^2*(x^2 - x + 1)^2*(x^2 + x + 1)^2/(x^10 - x^9 + x^6 - 2*x^5 + x^4 - x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 25 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 3c 4k2 4m 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 4.6.12, 3.4.4.6,
  3.4.6.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and
  computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file only,
  from the base vertex below; and this is the only 4-uniform file that holds the listed terms of
  every entry Gal.4.25.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 48) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 4.6.12; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a310068

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 48 × Fin 48 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 11, (-1), 0),
    (0, 13, (-1), (-1)),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 12, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 16, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 17, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 1),
    (4, 20, 0, 0),
    (5, 4, 0, (-1)),
    (5, 6, 0, 0),
    (5, 21, 0, (-1)),
    (6, 5, 0, 0),
    (6, 7, 0, 0),
    (6, 24, 0, 0),
    (7, 6, 0, 0),
    (7, 8, 0, 0),
    (7, 25, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 28, 0, 0),
    (9, 8, 0, 0),
    (9, 10, (-1), 0),
    (9, 29, (-1), 0),
    (10, 9, 1, 0),
    (10, 11, 0, 0),
    (10, 32, 0, 0),
    (11, 0, 1, 0),
    (11, 10, 0, 0),
    (11, 33, 0, 0),
    (12, 1, 0, 0),
    (12, 13, (-1), 0),
    (12, 14, 0, 0),
    (12, 37, (-1), 0),
    (13, 0, 1, 1),
    (13, 12, 1, 0),
    (13, 35, 0, 1),
    (13, 36, 0, 0),
    (14, 12, 0, 0),
    (14, 15, 0, 0),
    (14, 27, 0, 0),
    (14, 37, (-1), 0),
    (15, 14, 0, 0),
    (15, 16, 0, 0),
    (15, 26, 0, 0),
    (15, 38, 0, 0),
    (16, 2, 0, 0),
    (16, 15, 0, 0),
    (16, 17, 0, 0),
    (16, 38, 0, 0),
    (17, 3, 0, 0),
    (17, 16, 0, 0),
    (17, 18, 0, 0),
    (17, 39, 0, 0),
    (18, 17, 0, 0),
    (18, 19, 0, 0),
    (18, 31, 0, 0),
    (18, 39, 0, 0),
    (19, 18, 0, 0),
    (19, 20, 0, 0),
    (19, 30, 0, 0),
    (19, 40, 0, 0),
    (20, 4, 0, 0),
    (20, 19, 0, 0),
    (20, 21, 0, 0),
    (20, 40, 0, 0),
    (21, 5, 0, 1),
    (21, 20, 0, 0),
    (21, 22, 0, 1),
    (21, 41, 0, 0),
    (22, 21, 0, (-1)),
    (22, 23, 0, 0),
    (22, 35, 0, 0),
    (22, 41, 0, (-1)),
    (23, 22, 0, 0),
    (23, 24, 0, 0),
    (23, 34, 0, 0),
    (23, 42, 0, 0),
    (24, 6, 0, 0),
    (24, 23, 0, 0),
    (24, 25, 0, 0),
    (24, 42, 0, 0),
    (25, 7, 0, 0),
    (25, 24, 0, 0),
    (25, 26, 0, 0),
    (25, 43, 0, 0),
    (26, 15, 0, 0),
    (26, 25, 0, 0),
    (26, 27, 0, 0),
    (26, 43, 0, 0),
    (27, 14, 0, 0),
    (27, 26, 0, 0),
    (27, 28, 0, 0),
    (27, 44, (-1), 0),
    (28, 8, 0, 0),
    (28, 27, 0, 0),
    (28, 29, (-1), 0),
    (28, 44, (-1), 0),
    (29, 9, 1, 0),
    (29, 28, 1, 0),
    (29, 30, 0, 0),
    (29, 45, 0, 0),
    (30, 19, 0, 0),
    (30, 29, 0, 0),
    (30, 31, 0, 0),
    (30, 45, 0, 0),
    (31, 18, 0, 0),
    (31, 30, 0, 0),
    (31, 32, 0, 0),
    (31, 46, 0, 0),
    (32, 10, 0, 0),
    (32, 31, 0, 0),
    (32, 33, 0, 0),
    (32, 46, 0, 0),
    (33, 11, 0, 0),
    (33, 32, 0, 0),
    (33, 34, 0, 0),
    (33, 47, 0, 0),
    (34, 23, 0, 0),
    (34, 33, 0, 0),
    (34, 35, 0, 0),
    (34, 47, 0, 0),
    (35, 13, 0, (-1)),
    (35, 22, 0, 0),
    (35, 34, 0, 0),
    (35, 36, 0, (-1)),
    (36, 13, 0, 0),
    (36, 35, 0, 1),
    (36, 37, 0, 0),
    (36, 41, 0, 0),
    (37, 12, 1, 0),
    (37, 14, 1, 0),
    (37, 36, 0, 0),
    (37, 44, 0, 0),
    (38, 15, 0, 0),
    (38, 16, 0, 0),
    (38, 39, 0, 0),
    (38, 43, 0, 0),
    (39, 17, 0, 0),
    (39, 18, 0, 0),
    (39, 38, 0, 0),
    (39, 46, 0, 0),
    (40, 19, 0, 0),
    (40, 20, 0, 0),
    (40, 41, 0, 0),
    (40, 45, 0, 0),
    (41, 21, 0, 0),
    (41, 22, 0, 1),
    (41, 36, 0, 0),
    (41, 40, 0, 0),
    (42, 23, 0, 0),
    (42, 24, 0, 0),
    (42, 43, 0, 0),
    (42, 47, 0, 0),
    (43, 25, 0, 0),
    (43, 26, 0, 0),
    (43, 38, 0, 0),
    (43, 42, 0, 0),
    (44, 27, 1, 0),
    (44, 28, 1, 0),
    (44, 37, 0, 0),
    (44, 45, 0, 0),
    (45, 29, 0, 0),
    (45, 30, 0, 0),
    (45, 40, 0, 0),
    (45, 44, 0, 0),
    (46, 31, 0, 0),
    (46, 32, 0, 0),
    (46, 39, 0, 0),
    (46, 47, 0, 0),
    (47, 33, 0, 0),
    (47, 34, 0, 0),
    (47, 42, 0, 0),
    (47, 46, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 48) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 48) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 48 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 48 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 10. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - X ^ 9 + X ^ 6 - 2 * X ^ 5 + X ^ 4 - X + 1) =
      (X + 1) ^ 2 * (X ^ 2 - X + 1) ^ 2 * (X ^ 2 + X + 1) ^ 2 ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = a (n - 1) - a (n - 4) + 2 * a (n - 5) - a (n - 6) + a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a310068
