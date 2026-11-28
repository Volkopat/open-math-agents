import Mathlib

/-!
# OEIS A310027: Wu's conjectures for the coordination sequence Gal.5.41.2

Source: https://oeis.org/A310027 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A310027 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.41.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 3, 5, 8, 11, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 10 2018: (Start)
a(n) = a(n-1) - a(n-2) + a(n-3) + a(n-19) - a(n-20) + a(n-21) - a(n-22) for n > 22.
G.f.: (x + 1)^2*(x^2 - x + 1)^2*(x^2 + x + 1)*(x^14 + x^13 + x^12 + x^11 - x^10 + x^8 + x^7 + x^6 -
x^4 + x^3 + x^2 + x + 1)/(x^22 - x^21 + x^20 - x^19 - x^3 + x^2 - x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 41 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/2 (32)/eu 3c3 4l 4m 10.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 4.6.12, 3.4.6.4,
  3.4.6.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and
  computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file only,
  from the base vertex below; and this is the only 5-uniform file that holds the listed terms of
  every entry Gal.5.41.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 54) in the cell (x, y) of the tiling's
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

namespace OMA.S_oeis_a310027

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 54 × Fin 54 × ℤ × ℤ) :=
  [(0, 1, (-1), (-1)),
    (0, 11, 0, 0),
    (0, 13, (-1), 0),
    (1, 0, 1, 1),
    (1, 2, 0, 0),
    (1, 12, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 1, 0),
    (2, 16, 0, 0),
    (3, 2, (-1), 0),
    (3, 4, 0, 0),
    (3, 17, (-1), 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 20, 0, 0),
    (5, 4, 0, 0),
    (5, 6, 0, 0),
    (5, 21, 0, 0),
    (6, 5, 0, 0),
    (6, 7, 0, 1),
    (6, 23, 0, 0),
    (7, 6, 0, (-1)),
    (7, 8, 0, 0),
    (7, 25, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 28, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 29, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 32, 0, 0),
    (11, 0, 0, 0),
    (11, 10, 0, 0),
    (11, 33, 0, 0),
    (12, 1, 0, 0),
    (12, 13, 0, 1),
    (12, 14, 0, 0),
    (13, 0, 1, 0),
    (13, 12, 0, (-1)),
    (13, 34, 0, 0),
    (14, 12, 0, 0),
    (14, 15, 0, 0),
    (14, 36, 0, 0),
    (15, 14, 0, 0),
    (15, 16, 0, 0),
    (15, 40, 0, 0),
    (16, 2, 0, 0),
    (16, 15, 0, 0),
    (16, 17, 0, 0),
    (17, 3, 1, 0),
    (17, 16, 0, 0),
    (17, 18, 0, 0),
    (18, 17, 0, 0),
    (18, 19, 1, 0),
    (18, 43, 0, 0),
    (19, 18, (-1), 0),
    (19, 20, 0, 0),
    (19, 44, (-1), 0),
    (19, 45, 0, 0),
    (20, 4, 0, 0),
    (20, 19, 0, 0),
    (20, 21, 0, 0),
    (20, 46, 0, 0),
    (21, 5, 0, 0),
    (21, 20, 0, 0),
    (21, 24, 0, 0),
    (21, 46, 0, 0),
    (22, 23, 0, 0),
    (22, 24, 0, 0),
    (22, 39, 0, 0),
    (23, 6, 0, 0),
    (23, 22, 0, 0),
    (23, 25, 0, 1),
    (24, 21, 0, 0),
    (24, 22, 0, 0),
    (24, 47, 0, 0),
    (24, 48, 0, 0),
    (25, 7, 0, 0),
    (25, 23, 0, (-1)),
    (25, 26, 0, 0),
    (26, 25, 0, 0),
    (26, 27, 0, 0),
    (26, 38, 0, 0),
    (27, 26, 0, 0),
    (27, 28, 0, 0),
    (27, 42, 0, 0),
    (28, 8, 0, 0),
    (28, 27, 0, 0),
    (28, 29, 0, 0),
    (29, 9, 0, 0),
    (29, 28, 0, 0),
    (29, 30, 0, 0),
    (30, 29, 0, 0),
    (30, 31, 0, 0),
    (30, 41, 0, 0),
    (31, 30, 0, 0),
    (31, 32, 0, 0),
    (31, 49, 0, 0),
    (31, 50, 0, 0),
    (32, 10, 0, 0),
    (32, 31, 0, 0),
    (32, 33, 0, 0),
    (32, 51, 0, 0),
    (33, 11, 0, 0),
    (33, 32, 0, 0),
    (33, 35, 0, 0),
    (33, 51, 0, 0),
    (34, 13, 0, 0),
    (34, 35, 1, 0),
    (34, 37, 0, 0),
    (35, 33, 0, 0),
    (35, 34, (-1), 0),
    (35, 52, 0, 0),
    (35, 53, (-1), 0),
    (36, 14, 0, 0),
    (36, 39, 0, 0),
    (36, 40, 0, 0),
    (37, 34, 0, 0),
    (37, 38, 0, 0),
    (37, 53, 0, 0),
    (38, 26, 0, 0),
    (38, 37, 0, 0),
    (38, 42, 0, 0),
    (39, 22, 0, 0),
    (39, 36, 0, 0),
    (39, 48, 0, 0),
    (40, 15, 0, 0),
    (40, 36, 0, 0),
    (40, 41, 0, 0),
    (41, 30, 0, 0),
    (41, 40, 0, 0),
    (41, 49, 0, 0),
    (42, 27, 0, 0),
    (42, 38, 0, 0),
    (42, 43, 0, 0),
    (43, 18, 0, 0),
    (43, 42, 0, 0),
    (43, 44, 0, 0),
    (44, 19, 1, 0),
    (44, 43, 0, 0),
    (44, 45, 1, 0),
    (44, 53, 0, 0),
    (45, 19, 0, 0),
    (45, 44, (-1), 0),
    (45, 46, 0, 0),
    (45, 52, 0, 0),
    (46, 20, 0, 0),
    (46, 21, 0, 0),
    (46, 45, 0, 0),
    (46, 47, 0, 0),
    (47, 24, 0, 0),
    (47, 46, 0, 0),
    (47, 48, 0, 0),
    (47, 50, 0, 0),
    (48, 24, 0, 0),
    (48, 39, 0, 0),
    (48, 47, 0, 0),
    (48, 49, 0, 0),
    (49, 31, 0, 0),
    (49, 41, 0, 0),
    (49, 48, 0, 0),
    (49, 50, 0, 0),
    (50, 31, 0, 0),
    (50, 47, 0, 0),
    (50, 49, 0, 0),
    (50, 51, 0, 0),
    (51, 32, 0, 0),
    (51, 33, 0, 0),
    (51, 50, 0, 0),
    (51, 52, 0, 0),
    (52, 35, 0, 0),
    (52, 45, 0, 0),
    (52, 51, 0, 0),
    (52, 53, (-1), 0),
    (53, 35, 1, 0),
    (53, 37, 0, 0),
    (53, 44, 0, 0),
    (53, 52, 1, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 54) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 54) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 54 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 54 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 22. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 22 - X ^ 21 + X ^ 20 - X ^ 19 - X ^ 3 + X ^ 2 - X + 1) =
      (X + 1) ^ 2 * (X ^ 2 - X + 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 14 + X ^ 13 + X ^ 12 + X ^ 11 - X ^ 10 + X ^ 8 + X ^ 7 + X ^ 6 - X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ∧
    ∀ n : ℕ, 22 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 19) - a (n - 20) + a (n - 21) - a (n - 22) := by
  sorry

end OMA.S_oeis_a310027
