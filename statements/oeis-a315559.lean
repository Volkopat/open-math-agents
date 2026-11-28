import Mathlib

/-!
# OEIS A315559: Wu's conjectures for the coordination sequence Gal.4.149.2

Source: https://oeis.org/A315559 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315559 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.149.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 11, 18, 22, ...
Formula section:
Conjectures from Chai Wah Wu, Jun 09 2020: (Start)
a(n) = 2*a(n-5) - a(n-10) for n > 10.
G.f.: (x^10 + 6*x^9 + 11*x^8 + 18*x^7 + 22*x^6 + 28*x^5 + 22*x^4 + 18*x^3 + 11*x^2 + 6*x + 1)/(x^10
- 2*x^5 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 149 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/2 (31)/eu 5a 6h 6i2 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.3.3.6, 3.3.3.3.3.3,
  3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and
  computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file only,
  from the base vertex below; and this is the only 4-uniform file that holds the listed terms of
  every entry Gal.4.149.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 24) in the cell (x, y) of the tiling's
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

namespace OMA.S_oeis_a315559

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 24 × Fin 24 × ℤ × ℤ) :=
  [(0, 1, (-1), (-1)),
    (0, 5, 0, 0),
    (0, 6, (-1), 0),
    (0, 11, 0, 0),
    (0, 12, 0, 0),
    (1, 0, 1, 1),
    (1, 2, 0, 0),
    (1, 6, 0, 1),
    (1, 7, 0, 0),
    (1, 13, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 1, 0),
    (2, 7, 0, 0),
    (2, 8, 0, 0),
    (2, 14, 0, 0),
    (3, 2, (-1), 0),
    (3, 4, 0, 0),
    (3, 8, (-1), 0),
    (3, 9, 0, 0),
    (3, 15, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 1),
    (4, 9, 0, 0),
    (4, 10, 0, 1),
    (4, 16, 0, 0),
    (5, 0, 0, 0),
    (5, 4, 0, (-1)),
    (5, 10, 0, 0),
    (5, 11, 0, 0),
    (5, 17, 0, 0),
    (6, 0, 1, 0),
    (6, 1, 0, (-1)),
    (6, 12, 1, 0),
    (6, 13, 0, (-1)),
    (6, 18, 0, 0),
    (6, 19, 0, 0),
    (7, 1, 0, 0),
    (7, 2, 0, 0),
    (7, 13, 0, 0),
    (7, 14, 0, 0),
    (7, 20, 0, 0),
    (7, 21, 0, 0),
    (8, 2, 0, 0),
    (8, 3, 1, 0),
    (8, 14, 0, 0),
    (8, 15, 1, 0),
    (8, 18, 0, 0),
    (8, 22, 0, 0),
    (9, 3, 0, 0),
    (9, 4, 0, 0),
    (9, 15, 0, 0),
    (9, 16, 0, 0),
    (9, 20, 0, 0),
    (9, 23, 0, 0),
    (10, 4, 0, (-1)),
    (10, 5, 0, 0),
    (10, 16, 0, (-1)),
    (10, 17, 0, 0),
    (10, 19, 0, 0),
    (10, 22, 0, 0),
    (11, 0, 0, 0),
    (11, 5, 0, 0),
    (11, 12, 0, 0),
    (11, 17, 0, 0),
    (11, 21, 0, 0),
    (11, 23, 0, 0),
    (12, 0, 0, 0),
    (12, 6, (-1), 0),
    (12, 11, 0, 0),
    (12, 15, 0, 0),
    (12, 18, (-1), 0),
    (12, 23, 0, 0),
    (13, 1, 0, 0),
    (13, 6, 0, 1),
    (13, 7, 0, 0),
    (13, 16, 0, 0),
    (13, 19, 0, 1),
    (13, 20, 0, 0),
    (14, 2, 0, 0),
    (14, 7, 0, 0),
    (14, 8, 0, 0),
    (14, 17, 0, 0),
    (14, 21, 0, 0),
    (14, 22, 0, 0),
    (15, 3, 0, 0),
    (15, 8, (-1), 0),
    (15, 9, 0, 0),
    (15, 12, 0, 0),
    (15, 18, (-1), 0),
    (15, 23, 0, 0),
    (16, 4, 0, 0),
    (16, 9, 0, 0),
    (16, 10, 0, 1),
    (16, 13, 0, 0),
    (16, 19, 0, 1),
    (16, 20, 0, 0),
    (17, 5, 0, 0),
    (17, 10, 0, 0),
    (17, 11, 0, 0),
    (17, 14, 0, 0),
    (17, 21, 0, 0),
    (17, 22, 0, 0),
    (18, 6, 0, 0),
    (18, 8, 0, 0),
    (18, 12, 1, 0),
    (18, 15, 1, 0),
    (18, 19, 0, 0),
    (18, 22, 0, 0),
    (19, 6, 0, 0),
    (19, 10, 0, 0),
    (19, 13, 0, (-1)),
    (19, 16, 0, (-1)),
    (19, 18, 0, 0),
    (19, 22, 0, 0),
    (20, 7, 0, 0),
    (20, 9, 0, 0),
    (20, 13, 0, 0),
    (20, 16, 0, 0),
    (20, 21, 0, 0),
    (20, 23, 0, 0),
    (21, 7, 0, 0),
    (21, 11, 0, 0),
    (21, 14, 0, 0),
    (21, 17, 0, 0),
    (21, 20, 0, 0),
    (21, 23, 0, 0),
    (22, 8, 0, 0),
    (22, 10, 0, 0),
    (22, 14, 0, 0),
    (22, 17, 0, 0),
    (22, 18, 0, 0),
    (22, 19, 0, 0),
    (23, 9, 0, 0),
    (23, 11, 0, 0),
    (23, 12, 0, 0),
    (23, 15, 0, 0),
    (23, 20, 0, 0),
    (23, 21, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 24) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 24) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 24 := (0, 0, 6)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 24 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 10. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - 2 * X ^ 5 + 1) =
      X ^ 10 + 6 * X ^ 9 + 11 * X ^ 8 + 18 * X ^ 7 + 22 * X ^ 6 + 28 * X ^ 5 + 22 * X ^ 4 + 18 * X ^ 3 + 11 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 5) - a (n - 10) := by
  sorry

end OMA.S_oeis_a315559
