import Mathlib

/-!
# OEIS A315487: Wu's conjectures for the coordination sequence Gal.5.214.4

Source: https://oeis.org/A315487 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315487 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.214.4 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 11, 16, 22, ...
Formula section:
Conjectures from Chai Wah Wu, Apr 22 2024: (Start)
a(n) = a(n-1) + a(n-13) - a(n-14) for n > 14.
G.f.: (x^14 + 5*x^13 + 5*x^12 + 5*x^11 + 6*x^10 + 5*x^9 + 4*x^8 + 10*x^7 + 4*x^6 + 5*x^5 + 6*x^4 +
5*x^3 + 5*x^2 + 5*x + 1)/(x^14 - x^13 - x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 214 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/4 (2111)/eu 4l 5d 5f 6i2 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.6.4,
  3.3.3.4.4, 3.3.4.3.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed terms
  occur in this file only, from the base vertex below; and this is the only 5-uniform file that
  holds the listed terms of every entry Gal.5.214.v. The listed terms are proved as controls in the
  proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 42) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 18) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315487

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 42 × Fin 42 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, (-1), 0),
    (0, 6, 0, 0),
    (0, 17, (-1), 0),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 7, 0, 0),
    (1, 8, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 9, 0, 0),
    (2, 10, 0, 0),
    (3, 2, 0, 0),
    (3, 4, (-1), 0),
    (3, 11, 0, 0),
    (3, 12, (-1), 0),
    (4, 3, 1, 0),
    (4, 5, 0, 1),
    (4, 13, 0, 0),
    (4, 14, 0, 0),
    (5, 0, 1, 0),
    (5, 4, 0, (-1)),
    (5, 15, 0, 0),
    (5, 16, 0, 0),
    (6, 0, 0, 0),
    (6, 7, 0, (-1)),
    (6, 17, (-1), 0),
    (6, 18, 0, 0),
    (6, 24, 0, 0),
    (7, 1, 0, 0),
    (7, 6, 0, 1),
    (7, 8, 0, 0),
    (7, 18, 0, 1),
    (7, 26, 0, 0),
    (8, 1, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 19, 0, 0),
    (8, 27, 0, 0),
    (9, 2, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 19, 0, 0),
    (9, 28, 0, 0),
    (10, 2, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 20, 0, 0),
    (10, 29, 0, 0),
    (11, 3, 0, 0),
    (11, 10, 0, 0),
    (11, 12, (-1), 0),
    (11, 20, 0, 0),
    (11, 30, 0, 0),
    (12, 3, 1, 0),
    (12, 11, 1, 0),
    (12, 13, 0, 0),
    (12, 21, 0, 0),
    (12, 31, 0, 0),
    (13, 4, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, 0),
    (13, 21, 0, 0),
    (13, 32, 0, 0),
    (14, 4, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 1),
    (14, 22, 0, 1),
    (14, 33, 0, 0),
    (15, 5, 0, 0),
    (15, 14, 0, (-1)),
    (15, 16, 0, 0),
    (15, 22, 0, 0),
    (15, 34, 0, 0),
    (16, 5, 0, 0),
    (16, 15, 0, 0),
    (16, 17, 0, 0),
    (16, 23, 0, 0),
    (16, 35, 0, 0),
    (17, 0, 1, 0),
    (17, 6, 1, 0),
    (17, 16, 0, 0),
    (17, 23, 0, 0),
    (17, 25, 0, 0),
    (18, 6, 0, 0),
    (18, 7, 0, (-1)),
    (18, 24, 0, 0),
    (18, 26, 0, (-1)),
    (18, 36, 0, 0),
    (18, 37, 0, 0),
    (19, 8, 0, 0),
    (19, 9, 0, 0),
    (19, 27, 0, 0),
    (19, 28, 0, 0),
    (19, 38, 0, 0),
    (19, 39, 0, 0),
    (20, 10, 0, 0),
    (20, 11, 0, 0),
    (20, 29, 0, 0),
    (20, 30, 0, 0),
    (20, 36, 0, 0),
    (20, 40, 0, 0),
    (21, 12, 0, 0),
    (21, 13, 0, 0),
    (21, 31, 0, 0),
    (21, 32, 0, 0),
    (21, 38, 0, 0),
    (21, 41, 0, 0),
    (22, 14, 0, (-1)),
    (22, 15, 0, 0),
    (22, 33, 0, (-1)),
    (22, 34, 0, 0),
    (22, 37, 0, 0),
    (22, 40, 0, 0),
    (23, 16, 0, 0),
    (23, 17, 0, 0),
    (23, 25, 0, 0),
    (23, 35, 0, 0),
    (23, 39, 0, 0),
    (23, 41, 0, 0),
    (24, 6, 0, 0),
    (24, 18, 0, 0),
    (24, 25, (-1), 0),
    (24, 30, 0, 0),
    (24, 36, 0, 0),
    (25, 17, 0, 0),
    (25, 23, 0, 0),
    (25, 24, 1, 0),
    (25, 31, 0, 0),
    (25, 41, 0, 0),
    (26, 7, 0, 0),
    (26, 18, 0, 1),
    (26, 27, 0, 0),
    (26, 33, 0, 0),
    (26, 37, 0, 1),
    (27, 8, 0, 0),
    (27, 19, 0, 0),
    (27, 26, 0, 0),
    (27, 32, 0, 0),
    (27, 38, 0, 0),
    (28, 9, 0, 0),
    (28, 19, 0, 0),
    (28, 29, 0, 0),
    (28, 35, 0, 0),
    (28, 39, 0, 0),
    (29, 10, 0, 0),
    (29, 20, 0, 0),
    (29, 28, 0, 0),
    (29, 34, 0, 0),
    (29, 40, 0, 0),
    (30, 11, 0, 0),
    (30, 20, 0, 0),
    (30, 24, 0, 0),
    (30, 31, (-1), 0),
    (30, 36, 0, 0),
    (31, 12, 0, 0),
    (31, 21, 0, 0),
    (31, 25, 0, 0),
    (31, 30, 1, 0),
    (31, 41, 0, 0),
    (32, 13, 0, 0),
    (32, 21, 0, 0),
    (32, 27, 0, 0),
    (32, 33, 0, 0),
    (32, 38, 0, 0),
    (33, 14, 0, 0),
    (33, 22, 0, 1),
    (33, 26, 0, 0),
    (33, 32, 0, 0),
    (33, 37, 0, 1),
    (34, 15, 0, 0),
    (34, 22, 0, 0),
    (34, 29, 0, 0),
    (34, 35, 0, 0),
    (34, 40, 0, 0),
    (35, 16, 0, 0),
    (35, 23, 0, 0),
    (35, 28, 0, 0),
    (35, 34, 0, 0),
    (35, 39, 0, 0),
    (36, 18, 0, 0),
    (36, 20, 0, 0),
    (36, 24, 0, 0),
    (36, 30, 0, 0),
    (36, 37, 0, 0),
    (36, 40, 0, 0),
    (37, 18, 0, 0),
    (37, 22, 0, 0),
    (37, 26, 0, (-1)),
    (37, 33, 0, (-1)),
    (37, 36, 0, 0),
    (37, 40, 0, 0),
    (38, 19, 0, 0),
    (38, 21, 0, 0),
    (38, 27, 0, 0),
    (38, 32, 0, 0),
    (38, 39, 0, 0),
    (38, 41, 0, 0),
    (39, 19, 0, 0),
    (39, 23, 0, 0),
    (39, 28, 0, 0),
    (39, 35, 0, 0),
    (39, 38, 0, 0),
    (39, 41, 0, 0),
    (40, 20, 0, 0),
    (40, 22, 0, 0),
    (40, 29, 0, 0),
    (40, 34, 0, 0),
    (40, 36, 0, 0),
    (40, 37, 0, 0),
    (41, 21, 0, 0),
    (41, 23, 0, 0),
    (41, 25, 0, 0),
    (41, 31, 0, 0),
    (41, 38, 0, 0),
    (41, 39, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 42) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 42) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 42 := (0, 0, 18)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 42 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 14. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 - X ^ 13 - X + 1) =
      X ^ 14 + 5 * X ^ 13 + 5 * X ^ 12 + 5 * X ^ 11 + 6 * X ^ 10 + 5 * X ^ 9 + 4 * X ^ 8 + 10 * X ^ 7 + 4 * X ^ 6 + 5 * X ^ 5 + 6 * X ^ 4 + 5 * X ^ 3 + 5 * X ^ 2 + 5 * X + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = a (n - 1) + a (n - 13) - a (n - 14) := by
  sorry

end OMA.S_oeis_a315487
