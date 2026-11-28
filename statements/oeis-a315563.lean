import Mathlib

/-!
# OEIS A315563: Wu's conjectures for the coordination sequence Gal.5.320.2

Source: https://oeis.org/A315563 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315563 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.320.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 11, 18, 23, ...
Formula section:
Conjectures from Chai Wah Wu, Jun 11 2020: (Start)
a(n) = 2*a(n-3) - a(n-6) for n > 6.
G.f.: (x^6 + 6*x^5 + 11*x^4 + 16*x^3 + 11*x^2 + 6*x + 1)/(x^6 - 2*x^3 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 320 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/2 (41)/eu 5a 6c 6h2 6i 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.3.3.6,
  3.3.3.3.3.3, 3.3.3.3.3.3, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3-
  to 6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed terms
  occur in this file only, from the base vertex below; and this is the only 5-uniform file that
  holds the listed terms of every entry Gal.5.320.v. The listed terms are proved as controls in the
  proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 26) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 6) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315563

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 26 × Fin 26 × ℤ × ℤ) :=
  [(0, 1, (-1), (-1)),
    (0, 5, 0, 0),
    (0, 6, (-1), (-1)),
    (0, 11, 0, 0),
    (0, 12, (-1), 0),
    (1, 0, 1, 1),
    (1, 2, 1, 0),
    (1, 6, 0, 0),
    (1, 7, 0, 0),
    (1, 13, 0, 0),
    (2, 1, (-1), 0),
    (2, 3, 0, 0),
    (2, 7, (-1), 0),
    (2, 8, 0, 0),
    (2, 14, (-1), 0),
    (3, 2, 0, 0),
    (3, 4, 0, 1),
    (3, 8, 0, 0),
    (3, 9, 0, 0),
    (3, 15, 0, 0),
    (4, 3, 0, (-1)),
    (4, 5, 0, 0),
    (4, 9, 0, (-1)),
    (4, 10, 0, 0),
    (4, 16, 0, 0),
    (5, 0, 0, 0),
    (5, 4, 0, 0),
    (5, 10, 0, 0),
    (5, 11, 0, 0),
    (5, 17, 0, 0),
    (6, 0, 1, 1),
    (6, 1, 0, 0),
    (6, 12, 0, 1),
    (6, 13, 0, 0),
    (6, 18, 0, 1),
    (6, 19, 0, 0),
    (7, 1, 0, 0),
    (7, 2, 1, 0),
    (7, 13, 0, 0),
    (7, 14, 0, 0),
    (7, 20, 0, 0),
    (7, 21, 0, 0),
    (8, 2, 0, 0),
    (8, 3, 0, 0),
    (8, 14, (-1), 0),
    (8, 15, 0, 0),
    (8, 22, 0, 0),
    (8, 23, 0, 0),
    (9, 3, 0, 0),
    (9, 4, 0, 1),
    (9, 15, 0, 0),
    (9, 16, 0, 1),
    (9, 18, 0, 1),
    (9, 19, 0, 0),
    (10, 4, 0, 0),
    (10, 5, 0, 0),
    (10, 16, 0, 0),
    (10, 17, 0, 0),
    (10, 20, 0, 0),
    (10, 21, 0, 0),
    (11, 0, 0, 0),
    (11, 5, 0, 0),
    (11, 12, (-1), 0),
    (11, 17, 0, 0),
    (11, 22, 0, 0),
    (11, 23, 0, 0),
    (12, 0, 1, 0),
    (12, 6, 0, (-1)),
    (12, 11, 1, 0),
    (12, 18, 0, 0),
    (12, 22, 1, 0),
    (12, 24, 0, 0),
    (13, 1, 0, 0),
    (13, 6, 0, 0),
    (13, 7, 0, 0),
    (13, 19, 0, 0),
    (13, 20, 0, 0),
    (13, 25, 0, 0),
    (14, 2, 1, 0),
    (14, 7, 0, 0),
    (14, 8, 1, 0),
    (14, 21, 0, 0),
    (14, 22, 1, 0),
    (14, 24, 0, 0),
    (15, 3, 0, 0),
    (15, 8, 0, 0),
    (15, 9, 0, 0),
    (15, 19, 0, 0),
    (15, 23, 0, 0),
    (15, 25, 0, 0),
    (16, 4, 0, 0),
    (16, 9, 0, (-1)),
    (16, 10, 0, 0),
    (16, 18, 0, 0),
    (16, 21, 0, 0),
    (16, 24, 0, 0),
    (17, 5, 0, 0),
    (17, 10, 0, 0),
    (17, 11, 0, 0),
    (17, 20, 0, 0),
    (17, 23, 0, 0),
    (17, 25, 0, 0),
    (18, 6, 0, (-1)),
    (18, 9, 0, (-1)),
    (18, 12, 0, 0),
    (18, 16, 0, 0),
    (18, 19, 0, (-1)),
    (18, 24, 0, 0),
    (19, 6, 0, 0),
    (19, 9, 0, 0),
    (19, 13, 0, 0),
    (19, 15, 0, 0),
    (19, 18, 0, 1),
    (19, 25, 0, 0),
    (20, 7, 0, 0),
    (20, 10, 0, 0),
    (20, 13, 0, 0),
    (20, 17, 0, 0),
    (20, 21, 0, 0),
    (20, 25, 0, 0),
    (21, 7, 0, 0),
    (21, 10, 0, 0),
    (21, 14, 0, 0),
    (21, 16, 0, 0),
    (21, 20, 0, 0),
    (21, 24, 0, 0),
    (22, 8, 0, 0),
    (22, 11, 0, 0),
    (22, 12, (-1), 0),
    (22, 14, (-1), 0),
    (22, 23, 0, 0),
    (22, 24, (-1), 0),
    (23, 8, 0, 0),
    (23, 11, 0, 0),
    (23, 15, 0, 0),
    (23, 17, 0, 0),
    (23, 22, 0, 0),
    (23, 25, 0, 0),
    (24, 12, 0, 0),
    (24, 14, 0, 0),
    (24, 16, 0, 0),
    (24, 18, 0, 0),
    (24, 21, 0, 0),
    (24, 22, 1, 0),
    (25, 13, 0, 0),
    (25, 15, 0, 0),
    (25, 17, 0, 0),
    (25, 19, 0, 0),
    (25, 20, 0, 0),
    (25, 23, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 26) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 26) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 26 := (0, 0, 6)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 26 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 6 - 2 * X ^ 3 + 1) =
      X ^ 6 + 6 * X ^ 5 + 11 * X ^ 4 + 16 * X ^ 3 + 11 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 2 * a (n - 3) - a (n - 6) := by
  sorry

end OMA.S_oeis_a315563
