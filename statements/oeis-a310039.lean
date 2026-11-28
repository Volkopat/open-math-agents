import Mathlib

/-!
# OEIS A310039: Wu's conjectures for the coordination sequence Gal.3.7.1

Source: https://oeis.org/A310039 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A310039 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.3.7.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 3, 5, 9, 12, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 24 2019: (Start)
a(n) = 3*a(n-1) - 5*a(n-2) + 6*a(n-3) - 5*a(n-4) + 3*a(n-5) - 2*a(n-6) + 3*a(n-7) - 5*a(n-8) +
6*a(n-9) - 5*a(n-10) + 3*a(n-11) - a(n-12) for n > 14.
G.f.: (-2*x^14 + 6*x^13 - 7*x^12 + 6*x^11 - x^10 + x^9 + x^8 + 4*x^7 - 4*x^6 + 6*x^5 - 3*x^4 + 3*x^3
+ x^2 + 1)/((x - 1)^2*(x^2 + 1)^2*(x^2 - x + 1)*(x^4 - x^2 + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 7 of Galebach's list of the 61 3-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/03/3/eu 3a 4a 4l 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.12.12, 3.3.4.12, 3.4.6.4.
  Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and computing 50
  terms from every vertex class, the entry's 50 listed terms occur in this file only, from the base
  vertex below; and this is the only 3-uniform file that holds the listed terms of every entry
  Gal.3.7.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 24) in the cell (x, y) of the tiling's
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

namespace OMA.S_oeis_a310039

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 24 × Fin 24 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 11, (-1), 0),
    (0, 12, 0, (-1)),
    (0, 23, (-1), (-1)),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 12, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 1),
    (2, 13, 0, 0),
    (3, 2, 0, (-1)),
    (3, 4, 0, 0),
    (3, 13, 0, (-1)),
    (3, 18, 0, (-1)),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 15, 0, 0),
    (4, 19, 0, 0),
    (5, 4, 0, 0),
    (5, 6, 0, 0),
    (5, 15, 0, 0),
    (6, 5, 0, 0),
    (6, 7, 0, 0),
    (6, 14, 0, 0),
    (7, 6, 0, 0),
    (7, 8, (-1), 0),
    (7, 14, 0, 0),
    (7, 20, (-1), 0),
    (8, 7, 1, 0),
    (8, 9, 0, 0),
    (8, 17, 0, 0),
    (8, 21, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 17, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 16, 0, 0),
    (11, 0, 1, 0),
    (11, 10, 0, 0),
    (11, 16, 0, 0),
    (11, 22, 0, 0),
    (12, 0, 0, 1),
    (12, 1, 0, 0),
    (12, 14, 0, 0),
    (12, 23, (-1), 0),
    (13, 2, 0, 0),
    (13, 3, 0, 1),
    (13, 17, 0, 0),
    (13, 18, 0, 0),
    (14, 6, 0, 0),
    (14, 7, 0, 0),
    (14, 12, 0, 0),
    (14, 20, (-1), 0),
    (15, 4, 0, 0),
    (15, 5, 0, 0),
    (15, 16, 0, 0),
    (15, 19, 0, 0),
    (16, 10, 0, 0),
    (16, 11, 0, 0),
    (16, 15, 0, 0),
    (16, 22, 0, 0),
    (17, 8, 0, 0),
    (17, 9, 0, 0),
    (17, 13, 0, 0),
    (17, 21, 0, 0),
    (18, 3, 0, 1),
    (18, 13, 0, 0),
    (18, 19, 0, 1),
    (18, 21, 0, 0),
    (19, 4, 0, 0),
    (19, 15, 0, 0),
    (19, 18, 0, (-1)),
    (19, 22, 0, 0),
    (20, 7, 1, 0),
    (20, 14, 1, 0),
    (20, 21, 0, 0),
    (20, 23, 0, 0),
    (21, 8, 0, 0),
    (21, 17, 0, 0),
    (21, 18, 0, 0),
    (21, 20, 0, 0),
    (22, 11, 0, 0),
    (22, 16, 0, 0),
    (22, 19, 0, 0),
    (22, 23, 0, (-1)),
    (23, 0, 1, 1),
    (23, 12, 1, 0),
    (23, 20, 0, 0),
    (23, 22, 0, 1)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 24) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 24) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 24 := (0, 0, 1)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 24 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 14. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 4 - X ^ 2 + 1)) =
      -2 * X ^ 14 + 6 * X ^ 13 - 7 * X ^ 12 + 6 * X ^ 11 - X ^ 10 + X ^ 9 + X ^ 8 + 4 * X ^ 7 - 4 * X ^ 6 + 6 * X ^ 5 - 3 * X ^ 4 + 3 * X ^ 3 + X ^ 2 + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = 3 * a (n - 1) - 5 * a (n - 2) + 6 * a (n - 3) - 5 * a (n - 4) + 3 * a (n - 5) - 2 * a (n - 6) + 3 * a (n - 7) - 5 * a (n - 8) + 6 * a (n - 9) - 5 * a (n - 10) + 3 * a (n - 11) - a (n - 12) := by
  sorry

end OMA.S_oeis_a310039
