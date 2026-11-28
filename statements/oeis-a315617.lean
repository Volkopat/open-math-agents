import Mathlib

/-!
# OEIS A315617: Wu's conjectures for the coordination sequence Gal.3.37.3

Source: https://oeis.org/A315617 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315617 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.3.37.3 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 6, 12, 15, 18, ...
Formula section:
Conjectures from Chai Wah Wu, May 29 2025: (Start)
a(n) = a(n-1) + a(n-9) - a(n-10) for n > 10.
G.f.: (x^10 + 5*x^9 + 6*x^8 + 3*x^7 + 3*x^6 + 12*x^5 + 3*x^4 + 3*x^3 + 6*x^2 + 5*x + 1)/(x^10 - x^9
- x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 37 of Galebach's list of the 61 3-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/03/3/eu 4l 5f 6d 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.6.4, 3.3.4.3.4,
  3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and
  computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file only,
  from the base vertex below; and this is the only 3-uniform file that holds the listed terms of
  every entry Gal.3.37.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 20) in the cell (x, y) of the tiling's
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

namespace OMA.S_oeis_a315617

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 20 × Fin 20 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 5, 0, 0),
    (0, 6, (-1), (-1)),
    (0, 17, (-1), (-1)),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 7, (-1), 0),
    (1, 8, (-1), 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 9, 0, 0),
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
    (5, 15, 0, (-1)),
    (5, 16, 0, (-1)),
    (6, 0, 1, 1),
    (6, 7, 0, 1),
    (6, 11, 0, 0),
    (6, 17, 0, 0),
    (6, 18, 0, 0),
    (7, 1, 1, 0),
    (7, 6, 0, (-1)),
    (7, 8, 0, 0),
    (7, 14, 0, 0),
    (7, 18, 0, (-1)),
    (8, 1, 1, 0),
    (8, 7, 0, 0),
    (8, 9, 1, 0),
    (8, 13, 0, 0),
    (8, 19, 0, 0),
    (9, 2, 0, 0),
    (9, 8, (-1), 0),
    (9, 10, 0, 0),
    (9, 16, 0, 0),
    (9, 19, (-1), 0),
    (10, 2, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 15, 0, 0),
    (10, 18, 0, 0),
    (11, 3, 0, 0),
    (11, 6, 0, 0),
    (11, 10, 0, 0),
    (11, 12, 0, 0),
    (11, 18, 0, 0),
    (12, 3, 0, 0),
    (12, 11, 0, 0),
    (12, 13, 0, 0),
    (12, 17, 0, 0),
    (12, 19, 0, 0),
    (13, 4, 0, 0),
    (13, 8, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, 0),
    (13, 19, 0, 0),
    (14, 4, 0, 0),
    (14, 7, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, (-1)),
    (14, 18, 0, (-1)),
    (15, 5, 0, 1),
    (15, 10, 0, 0),
    (15, 14, 0, 1),
    (15, 16, 0, 0),
    (15, 18, 0, 0),
    (16, 5, 0, 1),
    (16, 9, 0, 0),
    (16, 15, 0, 0),
    (16, 17, (-1), 0),
    (16, 19, (-1), 0),
    (17, 0, 1, 1),
    (17, 6, 0, 0),
    (17, 12, 0, 0),
    (17, 16, 1, 0),
    (17, 19, 0, 0),
    (18, 6, 0, 0),
    (18, 7, 0, 1),
    (18, 10, 0, 0),
    (18, 11, 0, 0),
    (18, 14, 0, 1),
    (18, 15, 0, 0),
    (19, 8, 0, 0),
    (19, 9, 1, 0),
    (19, 12, 0, 0),
    (19, 13, 0, 0),
    (19, 16, 1, 0),
    (19, 17, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 20) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 20) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 20 := (0, 0, 18)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 20 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 10. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - X ^ 9 - X + 1) =
      X ^ 10 + 5 * X ^ 9 + 6 * X ^ 8 + 3 * X ^ 7 + 3 * X ^ 6 + 12 * X ^ 5 + 3 * X ^ 4 + 3 * X ^ 3 + 6 * X ^ 2 + 5 * X + 1 ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = a (n - 1) + a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a315617
