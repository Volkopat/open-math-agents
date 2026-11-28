import Mathlib

/-!
# OEIS A311647: Wu's conjectures for the coordination sequence Gal.4.85.1

Source: https://oeis.org/A311647 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311647 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.85.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 12, 19, ...
Formula section:
Conjectures from Chai Wah Wu, Mar 09 2023: (Start)
a(n) = a(n-3) + a(n-5) - a(n-8) for n > 10.
G.f.: (-x^10 - x^9 + 2*x^8 + 5*x^7 + 9*x^6 + 13*x^5 + 15*x^4 + 11*x^3 + 8*x^2 + 4*x + 1)/(x^8 - x^5
- x^3 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 85 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/4/eu 4d 4k 4m 5e 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6, 3.4.4.6, 3.4.6.4,
  3.3.4.3.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and
  computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file only,
  from the base vertex below; and this is the only 4-uniform file that holds the listed terms of
  every entry Gal.4.85.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 12) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 3.4.4.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311647

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 12 × Fin 12 × ℤ × ℤ) :=
  [(0, 1, (-1), 0),
    (0, 5, 0, (-1)),
    (0, 6, (-1), 0),
    (0, 7, (-1), (-1)),
    (1, 0, 1, 0),
    (1, 2, 1, 0),
    (1, 6, 0, 0),
    (1, 8, 0, 0),
    (2, 1, (-1), 0),
    (2, 3, 0, 0),
    (2, 7, (-1), 0),
    (2, 11, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 8, 0, 0),
    (3, 11, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, (-1)),
    (4, 6, 0, 0),
    (4, 10, 0, (-1)),
    (5, 0, 0, 1),
    (5, 4, 0, 1),
    (5, 9, 0, 0),
    (5, 11, 0, 0),
    (6, 0, 1, 0),
    (6, 1, 0, 0),
    (6, 4, 0, 0),
    (6, 8, 0, 0),
    (6, 10, 0, (-1)),
    (7, 0, 1, 1),
    (7, 2, 1, 0),
    (7, 10, 0, 0),
    (7, 11, 1, 0),
    (8, 1, 0, 0),
    (8, 3, 0, 0),
    (8, 6, 0, 0),
    (8, 9, 0, 0),
    (9, 5, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 11, 0, 0),
    (10, 4, 0, 1),
    (10, 6, 0, 1),
    (10, 7, 0, 0),
    (10, 9, 0, 0),
    (11, 2, 0, 0),
    (11, 3, 0, 0),
    (11, 5, 0, 0),
    (11, 7, (-1), 0),
    (11, 9, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 12) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 12) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 12 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 12 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 10. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 8 - X ^ 5 - X ^ 3 + 1) =
      -X ^ 10 - X ^ 9 + 2 * X ^ 8 + 5 * X ^ 7 + 9 * X ^ 6 + 13 * X ^ 5 + 15 * X ^ 4 + 11 * X ^ 3 + 8 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = a (n - 3) + a (n - 5) - a (n - 8) := by
  sorry

end OMA.S_oeis_a311647
