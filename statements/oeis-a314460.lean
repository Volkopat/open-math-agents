import Mathlib

/-!
# OEIS A314460: Wu's conjectures for the coordination sequence Gal.4.110.2

Source: https://oeis.org/A314460 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A314460 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.110.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 5, 8, 13, 20, ...
Formula section:
Conjectures from Chai Wah Wu, Jul 30 2022: (Start)
a(n) = a(n-2) + a(n-6) - a(n-8) for n > 16.
G.f.: (-2*x^16 - 2*x^14 + 2*x^12 + x^10 + x^9 + 3*x^8 + 8*x^7 + 6*x^6 + 10*x^5 + 12*x^4 + 8*x^3 +
7*x^2 + 5*x + 1)/(x^8 - x^6 - x^2 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 110 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 4e 5a2 6i 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6,
  3.3.3.3.6, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this
  file only, from the base vertex below; and this is the only 4-uniform file that holds the listed
  terms of every entry Gal.4.110.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 30) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 3.3.3.3.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a314460

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 30 × Fin 30 × ℤ × ℤ) :=
  [(0, 1, (-1), (-1)),
    (0, 5, 0, 0),
    (0, 6, 0, (-1)),
    (0, 17, 0, 0),
    (0, 18, 0, 0),
    (1, 0, 1, 1),
    (1, 2, 0, 0),
    (1, 6, 1, 0),
    (1, 7, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 1),
    (2, 10, 0, 0),
    (2, 11, 0, 0),
    (3, 2, 0, (-1)),
    (3, 4, 0, 0),
    (3, 11, 0, (-1)),
    (3, 12, 0, 0),
    (3, 24, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 1, 0),
    (4, 12, 0, 0),
    (4, 13, 0, 0),
    (5, 0, 0, 0),
    (5, 4, (-1), 0),
    (5, 16, 0, 0),
    (5, 17, 0, 0),
    (6, 0, 0, 1),
    (6, 1, (-1), 0),
    (6, 7, (-1), 0),
    (6, 18, 0, 1),
    (6, 20, 0, 0),
    (6, 26, 0, 0),
    (7, 1, 0, 0),
    (7, 6, 1, 0),
    (7, 8, 0, 0),
    (7, 20, 1, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 19, 0, 0),
    (8, 21, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 21, 0, 0),
    (9, 23, 0, 0),
    (10, 2, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 22, 0, 0),
    (11, 2, 0, 0),
    (11, 3, 0, 1),
    (11, 10, 0, 0),
    (11, 22, 0, 0),
    (11, 24, 0, 1),
    (11, 27, 0, 0),
    (12, 3, 0, 0),
    (12, 4, 0, 0),
    (12, 13, 0, 0),
    (12, 19, 0, 0),
    (12, 24, 0, 0),
    (12, 28, 0, 0),
    (13, 4, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 1, 0),
    (13, 19, 0, 0),
    (14, 13, (-1), 0),
    (14, 15, 0, 0),
    (14, 20, 0, 0),
    (14, 25, 0, 0),
    (15, 14, 0, 0),
    (15, 16, 0, 0),
    (15, 22, 0, 0),
    (15, 25, 0, 0),
    (16, 5, 0, 0),
    (16, 15, 0, 0),
    (16, 17, 0, 0),
    (16, 23, 0, 0),
    (17, 0, 0, 0),
    (17, 5, 0, 0),
    (17, 16, 0, 0),
    (17, 18, 0, 0),
    (17, 23, 0, 0),
    (17, 29, 0, 0),
    (18, 0, 0, 0),
    (18, 6, 0, (-1)),
    (18, 17, 0, 0),
    (18, 26, 0, (-1)),
    (18, 29, 0, 0),
    (19, 8, 0, 0),
    (19, 12, 0, 0),
    (19, 13, 0, 0),
    (19, 21, 0, 0),
    (19, 28, 0, 0),
    (20, 6, 0, 0),
    (20, 7, (-1), 0),
    (20, 14, 0, 0),
    (20, 25, 0, 0),
    (20, 26, 0, 0),
    (21, 8, 0, 0),
    (21, 9, 0, 0),
    (21, 19, 0, 0),
    (21, 23, 0, 0),
    (21, 28, 0, 0),
    (21, 29, 0, 0),
    (22, 10, 0, 0),
    (22, 11, 0, 0),
    (22, 15, 0, 0),
    (22, 25, 0, 0),
    (22, 27, 0, 0),
    (23, 9, 0, 0),
    (23, 16, 0, 0),
    (23, 17, 0, 0),
    (23, 21, 0, 0),
    (23, 29, 0, 0),
    (24, 3, 0, 0),
    (24, 11, 0, (-1)),
    (24, 12, 0, 0),
    (24, 27, 0, (-1)),
    (24, 28, 0, 0),
    (25, 14, 0, 0),
    (25, 15, 0, 0),
    (25, 20, 0, 0),
    (25, 22, 0, 0),
    (25, 26, 0, 0),
    (25, 27, 0, 0),
    (26, 6, 0, 0),
    (26, 18, 0, 1),
    (26, 20, 0, 0),
    (26, 25, 0, 0),
    (26, 27, 0, 0),
    (27, 11, 0, 0),
    (27, 22, 0, 0),
    (27, 24, 0, 1),
    (27, 25, 0, 0),
    (27, 26, 0, 0),
    (28, 12, 0, 0),
    (28, 19, 0, 0),
    (28, 21, 0, 0),
    (28, 24, 0, 0),
    (28, 29, 0, 0),
    (29, 17, 0, 0),
    (29, 18, 0, 0),
    (29, 21, 0, 0),
    (29, 23, 0, 0),
    (29, 28, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 30) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 30) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 30 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 30 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 16. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 8 - X ^ 6 - X ^ 2 + 1) =
      -2 * X ^ 16 - 2 * X ^ 14 + 2 * X ^ 12 + X ^ 10 + X ^ 9 + 3 * X ^ 8 + 8 * X ^ 7 + 6 * X ^ 6 + 10 * X ^ 5 + 12 * X ^ 4 + 8 * X ^ 3 + 7 * X ^ 2 + 5 * X + 1 ∧
    ∀ n : ℕ, 16 < n → (a n : ℤ) = a (n - 2) + a (n - 6) - a (n - 8) := by
  sorry

end OMA.S_oeis_a314460
