import Mathlib

/-!
# OEIS A310031: Wu's conjectures for the coordination sequence Gal.5.39.1

Source: https://oeis.org/A310031 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A310031 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.39.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 3, 5, 8, 12, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 10 2018: (Start)
a(n) = a(n-1) - a(n-2) + a(n-3) - a(n-4) + a(n-5) + a(n-13) - a(n-14) + a(n-15) - a(n-16) + a(n-17)
- a(n-18) for n > 18.
G.f.: (x^18 + 2*x^17 + 3*x^16 + 5*x^15 + 7*x^14 + 9*x^13 + 9*x^12 + 8*x^11 + 8*x^10 + 8*x^9 + 8*x^8
+ 8*x^7 + 9*x^6 + 9*x^5 + 7*x^4 + 5*x^3 + 3*x^2 + 2*x + 1)/(x^18 - x^17 + x^16 - x^15 + x^14 - x^13
- x^5 + x^4 - x^3 + x^2 - x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 39 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/2 (32)/eu 3c3 4l 4m 4.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 4.6.12, 3.4.6.4, 3.4.6.4.
  Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and computing 50
  terms from every vertex class, the entry's 50 listed terms occur in this file only, from the base
  vertex below; and this is the only 5-uniform file that holds the listed terms of every entry
  Gal.5.39.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 18) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 4.6.12; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a310031

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 18 × Fin 18 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 7, (-1), 0),
    (0, 11, 0, 0),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 6, (-1), 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 13, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 14, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 15, 0, 0),
    (5, 4, 0, 0),
    (5, 6, 0, 0),
    (5, 12, 0, 0),
    (6, 1, 1, 0),
    (6, 5, 0, 0),
    (6, 7, 0, 1),
    (7, 0, 1, 0),
    (7, 6, 0, (-1)),
    (7, 8, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 17, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 15, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 14, 0, 0),
    (11, 0, 0, 0),
    (11, 10, 0, 0),
    (11, 16, 0, 0),
    (12, 5, 0, 0),
    (12, 13, 1, 0),
    (12, 15, 0, 0),
    (12, 17, 0, 0),
    (13, 2, 0, 0),
    (13, 12, (-1), 0),
    (13, 14, 0, 0),
    (13, 16, 0, 0),
    (14, 3, 0, 0),
    (14, 10, 0, 0),
    (14, 13, 0, 0),
    (14, 16, 0, 0),
    (15, 4, 0, 0),
    (15, 9, 0, 0),
    (15, 12, 0, 0),
    (15, 17, 0, 0),
    (16, 11, 0, 0),
    (16, 13, 0, 0),
    (16, 14, 0, 0),
    (16, 17, (-1), 0),
    (17, 8, 0, 0),
    (17, 12, 0, 0),
    (17, 15, 0, 0),
    (17, 16, 1, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 18) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 18) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 18 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 18 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 18. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 18 - X ^ 17 + X ^ 16 - X ^ 15 + X ^ 14 - X ^ 13 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1) =
      X ^ 18 + 2 * X ^ 17 + 3 * X ^ 16 + 5 * X ^ 15 + 7 * X ^ 14 + 9 * X ^ 13 + 9 * X ^ 12 + 8 * X ^ 11 + 8 * X ^ 10 + 8 * X ^ 9 + 8 * X ^ 8 + 8 * X ^ 7 + 9 * X ^ 6 + 9 * X ^ 5 + 7 * X ^ 4 + 5 * X ^ 3 + 3 * X ^ 2 + 2 * X + 1 ∧
    ∀ n : ℕ, 18 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) - a (n - 4) + a (n - 5) + a (n - 13) - a (n - 14) + a (n - 15) - a (n - 16) + a (n - 17) - a (n - 18) := by
  sorry

end OMA.S_oeis_a310031
