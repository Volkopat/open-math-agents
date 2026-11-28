import Mathlib

/-!
# OEIS A314015: Wu's conjectures for the coordination sequence Gal.4.100.3

Source: https://oeis.org/A314015 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A314015 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.100.3 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 5, 11, 15, 19, ...
Formula section:
Conjectures from Chai Wah Wu, Apr 17 2024: (Start)
a(n) = 2*a(n-1) - 2*a(n-2) + 2*a(n-3) - 2*a(n-4) + 2*a(n-5) - a(n-6) for n > 6.
G.f.: (x^6 + 3*x^5 + 3*x^4 + x^3 + 3*x^2 + 3*x + 1)/((x - 1)^2*(x^2 - x + 1)*(x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 100 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 4l 5c 5d 6i 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.6.4,
  3.3.3.4.4, 3.3.3.4.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed terms
  occur in this file, from the base vertex below, and in 1 file of other tilings; and this is the
  only 4-uniform file that holds the listed terms of every entry Gal.4.100.v. The listed terms are
  proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 30) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 18) is a vertex of type 3.3.3.4.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a314015

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 30 × Fin 30 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, 0, 0),
    (0, 6, (-1), (-1)),
    (0, 17, (-1), 0),
    (1, 0, 0, 1),
    (1, 2, 0, 1),
    (1, 7, (-1), 0),
    (1, 8, 0, 0),
    (2, 1, 0, (-1)),
    (2, 3, 0, 0),
    (2, 9, 0, (-1)),
    (2, 10, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 11, 0, 0),
    (3, 12, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 13, 0, 0),
    (4, 14, 0, 0),
    (5, 0, 0, 0),
    (5, 4, 0, 0),
    (5, 15, 0, 0),
    (5, 16, (-1), 0),
    (6, 0, 1, 1),
    (6, 7, 0, 0),
    (6, 17, 0, 1),
    (6, 18, 0, 0),
    (6, 24, 0, 0),
    (7, 1, 1, 0),
    (7, 6, 0, 0),
    (7, 8, 1, 0),
    (7, 19, 0, 0),
    (7, 25, 0, 0),
    (8, 1, 0, 0),
    (8, 7, (-1), 0),
    (8, 9, 0, 0),
    (8, 20, 0, 0),
    (8, 25, (-1), 0),
    (9, 2, 0, 1),
    (9, 8, 0, 0),
    (9, 10, 0, 1),
    (9, 21, 0, 0),
    (9, 26, 0, 0),
    (10, 2, 0, 0),
    (10, 9, 0, (-1)),
    (10, 11, 0, 0),
    (10, 22, 0, 0),
    (10, 26, 0, (-1)),
    (11, 3, 0, 0),
    (11, 10, 0, 0),
    (11, 12, 0, 0),
    (11, 23, 0, 0),
    (11, 27, 0, 0),
    (12, 3, 0, 0),
    (12, 11, 0, 0),
    (12, 13, 0, 0),
    (12, 19, 0, 0),
    (12, 27, 0, 0),
    (13, 4, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, 0),
    (13, 18, 0, 0),
    (13, 28, 0, 0),
    (14, 4, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 0),
    (14, 21, 0, 0),
    (14, 28, 0, 0),
    (15, 5, 0, 0),
    (15, 14, 0, 0),
    (15, 16, (-1), 0),
    (15, 20, 0, 0),
    (15, 29, (-1), 0),
    (16, 5, 1, 0),
    (16, 15, 1, 0),
    (16, 17, 0, 0),
    (16, 23, 0, 0),
    (16, 29, 0, 0),
    (17, 0, 1, 0),
    (17, 6, 0, (-1)),
    (17, 16, 0, 0),
    (17, 22, 0, 0),
    (17, 24, 0, (-1)),
    (18, 6, 0, 0),
    (18, 13, 0, 0),
    (18, 19, 0, 0),
    (18, 24, 0, 0),
    (18, 28, 0, 0),
    (19, 7, 0, 0),
    (19, 12, 0, 0),
    (19, 18, 0, 0),
    (19, 25, 0, 0),
    (19, 27, 0, 0),
    (20, 8, 0, 0),
    (20, 15, 0, 0),
    (20, 21, 0, 0),
    (20, 25, (-1), 0),
    (20, 29, (-1), 0),
    (21, 9, 0, 0),
    (21, 14, 0, 0),
    (21, 20, 0, 0),
    (21, 26, 0, 0),
    (21, 28, 0, 0),
    (22, 10, 0, 0),
    (22, 17, 0, 0),
    (22, 23, 0, 0),
    (22, 24, 0, (-1)),
    (22, 26, 0, (-1)),
    (23, 11, 0, 0),
    (23, 16, 0, 0),
    (23, 22, 0, 0),
    (23, 27, 0, 0),
    (23, 29, 0, 0),
    (24, 6, 0, 0),
    (24, 17, 0, 1),
    (24, 18, 0, 0),
    (24, 22, 0, 1),
    (24, 26, 0, 0),
    (24, 28, 0, 0),
    (25, 7, 0, 0),
    (25, 8, 1, 0),
    (25, 19, 0, 0),
    (25, 20, 1, 0),
    (25, 27, 0, 0),
    (25, 29, 0, 0),
    (26, 9, 0, 0),
    (26, 10, 0, 1),
    (26, 21, 0, 0),
    (26, 22, 0, 1),
    (26, 24, 0, 0),
    (26, 28, 0, 0),
    (27, 11, 0, 0),
    (27, 12, 0, 0),
    (27, 19, 0, 0),
    (27, 23, 0, 0),
    (27, 25, 0, 0),
    (27, 29, 0, 0),
    (28, 13, 0, 0),
    (28, 14, 0, 0),
    (28, 18, 0, 0),
    (28, 21, 0, 0),
    (28, 24, 0, 0),
    (28, 26, 0, 0),
    (29, 15, 1, 0),
    (29, 16, 0, 0),
    (29, 20, 1, 0),
    (29, 23, 0, 0),
    (29, 25, 0, 0),
    (29, 27, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 30) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 30) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 30 := (0, 0, 18)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 30 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + X + 1)) =
      X ^ 6 + 3 * X ^ 5 + 3 * X ^ 4 + X ^ 3 + 3 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 2 * a (n - 4) + 2 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a314015
