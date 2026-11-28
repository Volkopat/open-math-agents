import Mathlib

/-!
# OEIS A311686: Wu's conjectures for the coordination sequence Gal.5.182.1

Source: https://oeis.org/A311686 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311686 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.182.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 13, 16, ...
Formula section:
Conjectures from Chai Wah Wu, Mar 13 2021: (Start)
a(n) = a(n-1) - a(n-4) + a(n-5) + a(n-11) - a(n-12) + a(n-15) - a(n-16) for n > 16.
G.f.: (x^16 + 3*x^15 + 4*x^14 + 5*x^13 + 4*x^12 + 7*x^11 + 9*x^10 + 9*x^9 + 7*x^8 + 9*x^7 + 9*x^6 +
7*x^5 + 4*x^4 + 5*x^3 + 4*x^2 + 3*x + 1)/(x^16 - x^15 + x^12 - x^11 - x^5 + x^4 - x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 182 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/3 (221)/eu 4d 4f 4h 4k2 2.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6,
  3.6.3.6, 3.6.3.6, 3.4.4.6. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this
  file only, from the base vertex below; and this is the only 5-uniform file that holds the listed
  terms of every entry Gal.5.182.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 13) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 8) is a vertex of type 3.4.4.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311686

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 13 × Fin 13 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 2, (-1), 0),
    (0, 3, (-1), (-1)),
    (0, 4, 0, (-1)),
    (1, 0, 0, 0),
    (1, 2, (-1), 0),
    (1, 2, 0, 0),
    (1, 5, 0, 0),
    (2, 0, 1, 0),
    (2, 1, 0, 0),
    (2, 1, 1, 0),
    (2, 5, 1, 0),
    (3, 0, 1, 1),
    (3, 4, 0, 0),
    (3, 4, 1, 0),
    (3, 8, 0, 0),
    (4, 0, 0, 1),
    (4, 3, (-1), 0),
    (4, 3, 0, 0),
    (4, 9, 0, 0),
    (5, 1, 0, 0),
    (5, 2, (-1), 0),
    (5, 6, 0, 0),
    (5, 7, (-1), 0),
    (6, 5, 0, 0),
    (6, 7, (-1), 0),
    (6, 7, 0, 0),
    (6, 10, 0, 0),
    (7, 5, 1, 0),
    (7, 6, 0, 0),
    (7, 6, 1, 0),
    (7, 11, 0, 0),
    (8, 3, 0, 0),
    (8, 9, 0, 0),
    (8, 9, 1, 0),
    (8, 12, 1, 0),
    (9, 4, 0, 0),
    (9, 8, (-1), 0),
    (9, 8, 0, 0),
    (9, 12, 0, 0),
    (10, 6, 0, 0),
    (10, 11, (-1), 0),
    (10, 11, 0, 0),
    (10, 12, 0, 0),
    (11, 7, 0, 0),
    (11, 10, 0, 0),
    (11, 10, 1, 0),
    (11, 12, 1, 0),
    (12, 8, (-1), 0),
    (12, 9, 0, 0),
    (12, 10, 0, 0),
    (12, 11, (-1), 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 13) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 13) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 13 := (0, 0, 8)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 13 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 16. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 16 - X ^ 15 + X ^ 12 - X ^ 11 - X ^ 5 + X ^ 4 - X + 1) =
      X ^ 16 + 3 * X ^ 15 + 4 * X ^ 14 + 5 * X ^ 13 + 4 * X ^ 12 + 7 * X ^ 11 + 9 * X ^ 10 + 9 * X ^ 9 + 7 * X ^ 8 + 9 * X ^ 7 + 9 * X ^ 6 + 7 * X ^ 5 + 4 * X ^ 4 + 5 * X ^ 3 + 4 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 16 < n → (a n : ℤ) = a (n - 1) - a (n - 4) + a (n - 5) + a (n - 11) - a (n - 12) + a (n - 15) - a (n - 16) := by
  sorry

end OMA.S_oeis_a311686
