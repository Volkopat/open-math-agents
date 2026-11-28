import Mathlib

/-!
# OEIS A315832: Wu's conjectures for the coordination sequence Gal.5.207.4

Source: https://oeis.org/A315832 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315832 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.207.4 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 7, 11, 14, ...
Formula section:
Conjectures from Chai Wah Wu, Jan 10 2020: (Start)
a(n) = 2*a(n-5) - a(n-10) for n > 10.
G.f.: (x^10 + 6*x^9 + 7*x^8 + 11*x^7 + 14*x^6 + 18*x^5 + 14*x^4 + 11*x^3 + 7*x^2 + 6*x + 1)/(x^10 -
2*x^5 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 207 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/4 (2111)/eu 4a2 4l 5d 6i 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.4.12,
  3.4.6.4, 3.3.3.4.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed terms
  occur in this file only, from the base vertex below; and this is the only 5-uniform file that
  holds the listed terms of every entry Gal.5.207.v. The listed terms are proved as controls in the
  proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 48) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 12) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315832

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 48 × Fin 48 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 11, (-1), (-1)),
    (0, 12, 0, 0),
    (0, 29, 0, (-1)),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 12, 0, 0),
    (1, 13, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 14, 0, 0),
    (2, 15, 0, 0),
    (3, 2, 0, 0),
    (3, 4, (-1), 0),
    (3, 15, 0, 0),
    (3, 16, 0, 0),
    (4, 3, 1, 0),
    (4, 5, 0, 0),
    (4, 17, 0, 0),
    (4, 18, 0, 0),
    (5, 4, 0, 0),
    (5, 6, 0, 0),
    (5, 18, 0, 0),
    (5, 19, 0, 0),
    (6, 5, 0, 0),
    (6, 7, 0, 0),
    (6, 20, 0, 0),
    (6, 21, 0, 0),
    (7, 6, 0, 0),
    (7, 8, 0, (-1)),
    (7, 21, 0, 0),
    (7, 22, 0, (-1)),
    (8, 7, 0, 1),
    (8, 9, 0, 0),
    (8, 23, 0, 0),
    (8, 24, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 24, 0, 0),
    (9, 25, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 26, 0, 0),
    (10, 27, 0, 0),
    (11, 0, 1, 1),
    (11, 10, 0, 0),
    (11, 27, 0, 0),
    (11, 28, 0, 0),
    (12, 0, 0, 0),
    (12, 1, 0, 0),
    (12, 13, 0, 0),
    (12, 29, 0, (-1)),
    (12, 31, 0, 0),
    (12, 42, 0, 0),
    (13, 1, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, 0),
    (13, 31, 0, 0),
    (14, 2, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 0),
    (14, 30, 0, 0),
    (15, 2, 0, 0),
    (15, 3, 0, 0),
    (15, 14, 0, 0),
    (15, 16, 0, 0),
    (15, 30, 0, 0),
    (15, 47, 0, 0),
    (16, 3, 0, 0),
    (16, 15, 0, 0),
    (16, 17, (-1), 0),
    (16, 37, 0, 0),
    (16, 47, 0, 0),
    (17, 4, 0, 0),
    (17, 16, 1, 0),
    (17, 18, 0, 0),
    (17, 36, 1, 0),
    (17, 44, 0, 0),
    (18, 4, 0, 0),
    (18, 5, 0, 0),
    (18, 17, 0, 0),
    (18, 19, 0, 0),
    (18, 33, 0, 0),
    (18, 44, 0, 0),
    (19, 5, 0, 0),
    (19, 18, 0, 0),
    (19, 20, 0, 0),
    (19, 33, 0, 0),
    (20, 6, 0, 0),
    (20, 19, 0, 0),
    (20, 21, 0, 0),
    (20, 32, 0, 0),
    (21, 6, 0, 0),
    (21, 7, 0, 0),
    (21, 20, 0, 0),
    (21, 22, 0, (-1)),
    (21, 32, 0, 0),
    (21, 43, 0, 0),
    (22, 7, 0, 1),
    (22, 21, 0, 1),
    (22, 23, 0, 0),
    (22, 39, 0, 0),
    (22, 43, 0, 1),
    (23, 8, 0, 0),
    (23, 22, 0, 0),
    (23, 24, 0, 0),
    (23, 38, 0, 0),
    (23, 46, 0, 0),
    (24, 8, 0, 0),
    (24, 9, 0, 0),
    (24, 23, 0, 0),
    (24, 25, 0, 0),
    (24, 35, 0, 0),
    (24, 46, 0, 0),
    (25, 9, 0, 0),
    (25, 24, 0, 0),
    (25, 26, 0, 0),
    (25, 35, 0, 0),
    (26, 10, 0, 0),
    (26, 25, 0, 0),
    (26, 27, 0, 0),
    (26, 34, 0, 0),
    (27, 10, 0, 0),
    (27, 11, 0, 0),
    (27, 26, 0, 0),
    (27, 28, 0, 0),
    (27, 34, 0, 0),
    (27, 45, 0, 0),
    (28, 11, 0, 0),
    (28, 27, 0, 0),
    (28, 29, 1, 0),
    (28, 41, 1, 0),
    (28, 45, 0, 0),
    (29, 0, 0, 1),
    (29, 12, 0, 1),
    (29, 28, (-1), 0),
    (29, 40, 0, 0),
    (29, 42, 0, 1),
    (30, 14, 0, 0),
    (30, 15, 0, 0),
    (30, 35, 0, 0),
    (30, 47, 0, 0),
    (31, 12, 0, 0),
    (31, 13, 0, 0),
    (31, 32, 0, 0),
    (31, 42, 0, 0),
    (32, 20, 0, 0),
    (32, 21, 0, 0),
    (32, 31, 0, 0),
    (32, 43, 0, 0),
    (33, 18, 0, 0),
    (33, 19, 0, 0),
    (33, 34, 0, 0),
    (33, 44, 0, 0),
    (34, 26, 0, 0),
    (34, 27, 0, 0),
    (34, 33, 0, 0),
    (34, 45, 0, 0),
    (35, 24, 0, 0),
    (35, 25, 0, 0),
    (35, 30, 0, 0),
    (35, 46, 0, 0),
    (36, 17, (-1), 0),
    (36, 37, 0, 0),
    (36, 41, 0, 0),
    (36, 44, (-1), 0),
    (37, 16, 0, 0),
    (37, 36, 0, 0),
    (37, 38, 0, 0),
    (37, 47, 0, 0),
    (38, 23, 0, 0),
    (38, 37, 0, 0),
    (38, 39, 0, 0),
    (38, 46, 0, 0),
    (39, 22, 0, 0),
    (39, 38, 0, 0),
    (39, 40, 0, 0),
    (39, 43, 0, 1),
    (40, 29, 0, 0),
    (40, 39, 0, 0),
    (40, 41, 0, 0),
    (40, 42, 0, 1),
    (41, 28, (-1), 0),
    (41, 36, 0, 0),
    (41, 40, 0, 0),
    (41, 45, (-1), 0),
    (42, 12, 0, 0),
    (42, 29, 0, (-1)),
    (42, 31, 0, 0),
    (42, 40, 0, (-1)),
    (42, 43, 0, 0),
    (43, 21, 0, 0),
    (43, 22, 0, (-1)),
    (43, 32, 0, 0),
    (43, 39, 0, (-1)),
    (43, 42, 0, 0),
    (44, 17, 0, 0),
    (44, 18, 0, 0),
    (44, 33, 0, 0),
    (44, 36, 1, 0),
    (44, 45, 0, 0),
    (45, 27, 0, 0),
    (45, 28, 0, 0),
    (45, 34, 0, 0),
    (45, 41, 1, 0),
    (45, 44, 0, 0),
    (46, 23, 0, 0),
    (46, 24, 0, 0),
    (46, 35, 0, 0),
    (46, 38, 0, 0),
    (46, 47, 0, 0),
    (47, 15, 0, 0),
    (47, 16, 0, 0),
    (47, 30, 0, 0),
    (47, 37, 0, 0),
    (47, 46, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 48) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 48) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 48 := (0, 0, 12)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 48 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 10. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - 2 * X ^ 5 + 1) =
      X ^ 10 + 6 * X ^ 9 + 7 * X ^ 8 + 11 * X ^ 7 + 14 * X ^ 6 + 18 * X ^ 5 + 14 * X ^ 4 + 11 * X ^ 3 + 7 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 5) - a (n - 10) := by
  sorry

end OMA.S_oeis_a315832
