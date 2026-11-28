import Mathlib

/-!
# OEIS A311666: Wu's conjectures for the coordination sequence Gal.4.108.1

Source: https://oeis.org/A311666 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311666 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.108.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 13, 14, ...
Formula section:
Conjectures from Chai Wah Wu, Jun 06 2024: (Start)
a(n) = a(n-6) + a(n-7) - a(n-13) for n > 15.
G.f.: (-2*x^15 + 3*x^13 + 3*x^12 + 10*x^11 + 13*x^10 + 14*x^9 + 26*x^8 + 25*x^7 + 27*x^6 + 21*x^5 +
14*x^4 + 13*x^3 + 8*x^2 + 4*x + 1)/(x^13 - x^7 - x^6 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 108 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 4c 4l2 5e 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.3.12,
  3.4.6.4, 3.3.4.3.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this
  file only, from the base vertex below; and this is the only 4-uniform file that holds the listed
  terms of every entry Gal.4.108.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 30) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 13) is a vertex of type 3.4.6.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311666

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 30 × Fin 30 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 11, 0, (-1)),
    (0, 12, (-1), 0),
    (0, 23, (-1), 0),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 12, (-1), 0),
    (1, 13, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 13, 0, 0),
    (2, 14, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, (-1)),
    (3, 14, 0, 0),
    (3, 15, 0, 0),
    (4, 3, 0, 1),
    (4, 5, 0, 0),
    (4, 15, 0, 1),
    (4, 16, 0, 0),
    (5, 4, 0, 0),
    (5, 6, 0, 0),
    (5, 16, 0, 0),
    (5, 17, 0, 0),
    (6, 5, 0, 0),
    (6, 7, 0, 0),
    (6, 17, 0, 0),
    (6, 18, 0, 0),
    (7, 6, 0, 0),
    (7, 8, 0, 0),
    (7, 18, 0, 0),
    (7, 19, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 19, 0, 0),
    (8, 20, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 20, 0, 0),
    (9, 21, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 21, 0, 0),
    (10, 22, (-1), 0),
    (11, 0, 0, 1),
    (11, 10, 0, 0),
    (11, 22, (-1), 0),
    (11, 23, (-1), 1),
    (12, 0, 1, 0),
    (12, 1, 1, 0),
    (12, 18, 0, 0),
    (12, 24, 0, 0),
    (12, 25, 0, 0),
    (13, 1, 0, 0),
    (13, 2, 0, 0),
    (13, 24, (-1), 0),
    (13, 26, 0, 0),
    (14, 2, 0, 0),
    (14, 3, 0, 0),
    (14, 20, 0, 0),
    (14, 26, 0, 0),
    (14, 27, 0, 0),
    (15, 3, 0, 0),
    (15, 4, 0, (-1)),
    (15, 27, 0, 0),
    (15, 28, 0, (-1)),
    (16, 4, 0, 0),
    (16, 5, 0, 0),
    (16, 22, 0, 0),
    (16, 28, 0, 0),
    (16, 29, 0, 0),
    (17, 5, 0, 0),
    (17, 6, 0, 0),
    (17, 24, 0, 0),
    (17, 29, 0, 0),
    (18, 6, 0, 0),
    (18, 7, 0, 0),
    (18, 12, 0, 0),
    (18, 24, 0, 0),
    (18, 25, 0, 0),
    (19, 7, 0, 0),
    (19, 8, 0, 0),
    (19, 25, 0, 0),
    (19, 27, 0, 0),
    (20, 8, 0, 0),
    (20, 9, 0, 0),
    (20, 14, 0, 0),
    (20, 26, 0, 0),
    (20, 27, 0, 0),
    (21, 9, 0, 0),
    (21, 10, 0, 0),
    (21, 26, 0, 0),
    (21, 29, (-1), 0),
    (22, 10, 1, 0),
    (22, 11, 1, 0),
    (22, 16, 0, 0),
    (22, 28, 0, 0),
    (22, 29, 0, 0),
    (23, 0, 1, 0),
    (23, 11, 1, (-1)),
    (23, 25, 0, 0),
    (23, 28, 0, (-1)),
    (24, 12, 0, 0),
    (24, 13, 1, 0),
    (24, 17, 0, 0),
    (24, 18, 0, 0),
    (25, 12, 0, 0),
    (25, 18, 0, 0),
    (25, 19, 0, 0),
    (25, 23, 0, 0),
    (26, 13, 0, 0),
    (26, 14, 0, 0),
    (26, 20, 0, 0),
    (26, 21, 0, 0),
    (27, 14, 0, 0),
    (27, 15, 0, 0),
    (27, 19, 0, 0),
    (27, 20, 0, 0),
    (28, 15, 0, 1),
    (28, 16, 0, 0),
    (28, 22, 0, 0),
    (28, 23, 0, 1),
    (29, 16, 0, 0),
    (29, 17, 0, 0),
    (29, 21, 1, 0),
    (29, 22, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 30) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 30) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 30 := (0, 0, 13)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 30 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 15. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 13 - X ^ 7 - X ^ 6 + 1) =
      -2 * X ^ 15 + 3 * X ^ 13 + 3 * X ^ 12 + 10 * X ^ 11 + 13 * X ^ 10 + 14 * X ^ 9 + 26 * X ^ 8 + 25 * X ^ 7 + 27 * X ^ 6 + 21 * X ^ 5 + 14 * X ^ 4 + 13 * X ^ 3 + 8 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 15 < n → (a n : ℤ) = a (n - 6) + a (n - 7) - a (n - 13) := by
  sorry

end OMA.S_oeis_a311666
