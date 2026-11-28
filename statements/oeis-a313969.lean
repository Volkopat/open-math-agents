import Mathlib

/-!
# OEIS A313969: Wu's conjectures for the coordination sequence Gal.6.489.5

Source: https://oeis.org/A313969 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A313969 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.489.5 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 5, 10, 17, 21, ...
Formula section:
Conjectures from Chai Wah Wu, Mar 13 2021: (Start)
a(n) = 2*a(n-1) - a(n-2) - a(n-3) + a(n-4) + a(n-5) - 2*a(n-6) + 2*a(n-7) - 2*a(n-8) + a(n-9) +
a(n-10) - a(n-11) - a(n-12) + 2*a(n-13) - a(n-14) for n > 14.
G.f.: (x^14 + 3*x^13 + x^12 + 3*x^11 + x^10 + 7*x^9 + 3*x^8 + 3*x^6 + 7*x^5 + x^4 + 3*x^3 + x^2 +
3*x + 1)/((x - 1)^2*(x^2 - x + 1)*(x^4 - x^2 + 1)*(x^6 + x^5 + x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 489 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/3 (411)/eu 4l 5e3 5f 6c 2.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.6.4,
  3.3.4.3.4, 3.3.4.3.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, this is the only 6-uniform
  catalog file in which every entry Gal.6.489.w of this tiling occurs (6 entries), and the entry's
  50 listed terms are those of the base vertex below (no other catalog file has them). The listed
  terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 38) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 25) is a vertex of type 3.3.4.3.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a313969

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 38 × Fin 38 × ℤ × ℤ) :=
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
    (8, 26, 0, 0),
    (9, 2, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 19, 0, 0),
    (9, 29, 0, 0),
    (10, 2, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 20, 0, 0),
    (10, 29, 0, 0),
    (11, 3, 0, 0),
    (11, 10, 0, 0),
    (11, 12, (-1), 0),
    (11, 20, 0, 0),
    (11, 32, 0, 0),
    (12, 3, 1, 0),
    (12, 11, 1, 0),
    (12, 13, 0, 0),
    (12, 21, 0, 0),
    (12, 32, 1, 0),
    (13, 4, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, 0),
    (13, 21, 0, 0),
    (13, 34, 0, 0),
    (14, 4, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 1),
    (14, 22, 0, 1),
    (14, 34, 0, 0),
    (15, 5, 0, 0),
    (15, 14, 0, (-1)),
    (15, 16, 0, 0),
    (15, 22, 0, 0),
    (15, 35, 0, 0),
    (16, 5, 0, 0),
    (16, 15, 0, 0),
    (16, 17, 0, 0),
    (16, 23, 0, 0),
    (16, 35, 0, 0),
    (17, 0, 1, 0),
    (17, 6, 1, 0),
    (17, 16, 0, 0),
    (17, 23, 0, 0),
    (17, 24, 1, 0),
    (18, 6, 0, 0),
    (18, 7, 0, (-1)),
    (18, 25, 0, 0),
    (18, 27, 0, 0),
    (18, 36, 0, 0),
    (19, 8, 0, 0),
    (19, 9, 0, 0),
    (19, 28, 0, 0),
    (19, 30, 0, 0),
    (19, 37, 0, 0),
    (20, 10, 0, 0),
    (20, 11, 0, 0),
    (20, 25, 0, 0),
    (20, 31, 0, 0),
    (20, 36, 0, 0),
    (21, 12, 0, 0),
    (21, 13, 0, 0),
    (21, 28, 0, 0),
    (21, 33, 0, 0),
    (21, 37, 0, 0),
    (22, 14, 0, (-1)),
    (22, 15, 0, 0),
    (22, 27, 0, 0),
    (22, 31, 0, 0),
    (22, 36, 0, 0),
    (23, 16, 0, 0),
    (23, 17, 0, 0),
    (23, 30, 0, 0),
    (23, 33, 0, 0),
    (23, 37, 0, 0),
    (24, 6, 0, 0),
    (24, 17, (-1), 0),
    (24, 25, 0, 0),
    (24, 32, 0, 0),
    (24, 33, (-1), 0),
    (25, 18, 0, 0),
    (25, 20, 0, 0),
    (25, 24, 0, 0),
    (25, 32, 0, 0),
    (25, 36, 0, 0),
    (26, 7, 0, 0),
    (26, 8, 0, 0),
    (26, 27, 0, 1),
    (26, 28, 0, 0),
    (26, 34, 0, 0),
    (27, 18, 0, 0),
    (27, 22, 0, 0),
    (27, 26, 0, (-1)),
    (27, 34, 0, (-1)),
    (27, 36, 0, 0),
    (28, 19, 0, 0),
    (28, 21, 0, 0),
    (28, 26, 0, 0),
    (28, 34, 0, 0),
    (28, 37, 0, 0),
    (29, 9, 0, 0),
    (29, 10, 0, 0),
    (29, 30, 0, 0),
    (29, 31, 0, 0),
    (29, 35, 0, 0),
    (30, 19, 0, 0),
    (30, 23, 0, 0),
    (30, 29, 0, 0),
    (30, 35, 0, 0),
    (30, 37, 0, 0),
    (31, 20, 0, 0),
    (31, 22, 0, 0),
    (31, 29, 0, 0),
    (31, 35, 0, 0),
    (31, 36, 0, 0),
    (32, 11, 0, 0),
    (32, 12, (-1), 0),
    (32, 24, 0, 0),
    (32, 25, 0, 0),
    (32, 33, (-1), 0),
    (33, 21, 0, 0),
    (33, 23, 0, 0),
    (33, 24, 1, 0),
    (33, 32, 1, 0),
    (33, 37, 0, 0),
    (34, 13, 0, 0),
    (34, 14, 0, 0),
    (34, 26, 0, 0),
    (34, 27, 0, 1),
    (34, 28, 0, 0),
    (35, 15, 0, 0),
    (35, 16, 0, 0),
    (35, 29, 0, 0),
    (35, 30, 0, 0),
    (35, 31, 0, 0),
    (36, 18, 0, 0),
    (36, 20, 0, 0),
    (36, 22, 0, 0),
    (36, 25, 0, 0),
    (36, 27, 0, 0),
    (36, 31, 0, 0),
    (37, 19, 0, 0),
    (37, 21, 0, 0),
    (37, 23, 0, 0),
    (37, 28, 0, 0),
    (37, 30, 0, 0),
    (37, 33, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 38) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 38) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 38 := (0, 0, 25)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 38 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 14. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 4 - X ^ 2 + 1) * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 14 + 3 * X ^ 13 + X ^ 12 + 3 * X ^ 11 + X ^ 10 + 7 * X ^ 9 + 3 * X ^ 8 + 3 * X ^ 6 + 7 * X ^ 5 + X ^ 4 + 3 * X ^ 3 + X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) - a (n - 3) + a (n - 4) + a (n - 5) - 2 * a (n - 6) + 2 * a (n - 7) - 2 * a (n - 8) + a (n - 9) + a (n - 10) - a (n - 11) - a (n - 12) + 2 * a (n - 13) - a (n - 14) := by
  sorry

end OMA.S_oeis_a313969
