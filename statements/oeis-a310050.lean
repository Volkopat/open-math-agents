import Mathlib

/-!
# OEIS A310050: Wu's conjectures for the coordination sequence Gal.4.36.1

Source: https://oeis.org/A310050 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A310050 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.36.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 3, 6, 10, 13, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 24 2019: (Start)
a(n) = - a(n-2) + a(n-5) + 2*a(n-7) + a(n-9) - a(n-12) - a(n-14) for n > 16.
G.f.: (-2*x^16 + x^14 + 3*x^13 + 7*x^12 + 15*x^11 + 21*x^10 + 29*x^9 + 29*x^8 + 28*x^7 + 29*x^6 +
25*x^5 + 19*x^4 + 13*x^3 + 7*x^2 + 3*x + 1)/(x^14 + x^12 - x^9 - 2*x^7 - x^5 + x^2 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 36 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/4/eu 3a 4a 4c 5c 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.12.12, 3.3.4.12,
  3.4.3.12, 3.3.3.4.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this
  file only, from the base vertex below; and this is the only 4-uniform file that holds the listed
  terms of every entry Gal.4.36.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 12) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 1) is a vertex of type 3.12.12; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a310050

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 12 × Fin 12 × ℤ × ℤ) :=
  [(0, 1, (-1), 0),
    (0, 7, (-1), 0),
    (0, 9, 0, (-1)),
    (0, 10, 0, (-1)),
    (1, 0, 1, 0),
    (1, 2, 0, 0),
    (1, 7, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 1, 0),
    (2, 6, 0, 0),
    (3, 2, (-1), 0),
    (3, 4, 0, 0),
    (3, 6, (-1), 0),
    (3, 10, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 9, 0, 0),
    (4, 10, 0, 0),
    (5, 4, 0, 0),
    (5, 6, 0, 0),
    (5, 8, 0, 0),
    (5, 11, 0, 0),
    (6, 2, 0, 0),
    (6, 3, 1, 0),
    (6, 5, 0, 0),
    (6, 11, 0, 0),
    (7, 0, 1, 0),
    (7, 1, 0, 0),
    (7, 8, 0, (-1)),
    (7, 11, 0, (-1)),
    (8, 5, 0, 0),
    (8, 7, 0, 1),
    (8, 9, 0, 0),
    (8, 11, 0, 0),
    (9, 0, 0, 1),
    (9, 4, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (10, 0, 0, 1),
    (10, 3, 0, 0),
    (10, 4, 0, 0),
    (10, 9, 0, 0),
    (10, 11, (-1), 0),
    (11, 5, 0, 0),
    (11, 6, 0, 0),
    (11, 7, 0, 1),
    (11, 8, 0, 0),
    (11, 10, 1, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 12) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 12) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 12 := (0, 0, 1)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 12 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 16. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 + X ^ 12 - X ^ 9 - 2 * X ^ 7 - X ^ 5 + X ^ 2 + 1) =
      -2 * X ^ 16 + X ^ 14 + 3 * X ^ 13 + 7 * X ^ 12 + 15 * X ^ 11 + 21 * X ^ 10 + 29 * X ^ 9 + 29 * X ^ 8 + 28 * X ^ 7 + 29 * X ^ 6 + 25 * X ^ 5 + 19 * X ^ 4 + 13 * X ^ 3 + 7 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 16 < n → (a n : ℤ) = -a (n - 2) + a (n - 5) + 2 * a (n - 7) + a (n - 9) - a (n - 12) - a (n - 14) := by
  sorry

end OMA.S_oeis_a310050
