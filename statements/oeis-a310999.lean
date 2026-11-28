import Mathlib

/-!
# OEIS A310999: Wu's conjectures for the coordination sequence Gal.4.7.3

Source: https://oeis.org/A310999 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A310999 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.7.3 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 10, 15, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 24 2019: (Start)
a(n) = 2*a(n-1) - 2*a(n-2) + 2*a(n-3) - 2*a(n-4) + 2*a(n-5) - 2*a(n-6) + 2*a(n-7) - 2*a(n-8) +
2*a(n-9) - a(n-10) for n > 13.
G.f.: (-2*x^13 + 2*x^12 + x^10 + 4*x^9 - 2*x^8 + 4*x^7 + 3*x^6 + 5*x^4 + 2*x^2 + 2*x + 1)/((x -
1)^2*(x^4 - x^3 + x^2 - x + 1)*(x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 7 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 3f 4d2 6c 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 6.6.6, 3.3.6.6,
  3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and
  computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file only,
  from the base vertex below; and this is the only 4-uniform file that holds the listed terms of
  every entry Gal.4.7.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 20) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 4) is a vertex of type 3.3.6.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a310999

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 20 × Fin 20 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, (-1), (-1)),
    (0, 8, (-1), 0),
    (0, 19, (-1), 0),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 7, 0, 1),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 12, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 15, 0, 0),
    (3, 16, 0, 0),
    (4, 3, 0, 0),
    (4, 5, (-1), 0),
    (4, 16, 0, 0),
    (4, 17, (-1), 0),
    (5, 0, 1, 1),
    (5, 4, 1, 0),
    (5, 18, 0, 1),
    (5, 19, 0, 1),
    (6, 7, 0, 0),
    (6, 9, 0, 0),
    (6, 15, 0, 0),
    (6, 16, 0, 0),
    (7, 1, 0, (-1)),
    (7, 6, 0, 0),
    (7, 10, 0, (-1)),
    (8, 0, 1, 0),
    (8, 9, 1, 0),
    (8, 13, 0, 0),
    (8, 19, 0, 0),
    (9, 6, 0, 0),
    (9, 8, (-1), 0),
    (9, 16, 0, 0),
    (9, 17, (-1), 0),
    (10, 7, 0, 1),
    (10, 11, 0, 0),
    (10, 18, 0, 1),
    (11, 10, 0, 0),
    (11, 12, 0, 0),
    (11, 17, 0, 0),
    (12, 2, 0, 0),
    (12, 11, 0, 0),
    (12, 13, 0, 0),
    (13, 8, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, 0),
    (13, 19, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 0),
    (14, 18, 0, 0),
    (14, 19, 0, 0),
    (15, 3, 0, 0),
    (15, 6, 0, 0),
    (15, 14, 0, 0),
    (15, 16, 0, 0),
    (16, 3, 0, 0),
    (16, 4, 0, 0),
    (16, 6, 0, 0),
    (16, 9, 0, 0),
    (16, 15, 0, 0),
    (16, 17, (-1), 0),
    (17, 4, 1, 0),
    (17, 9, 1, 0),
    (17, 11, 0, 0),
    (17, 16, 1, 0),
    (18, 5, 0, (-1)),
    (18, 10, 0, (-1)),
    (18, 14, 0, 0),
    (18, 19, 0, 0),
    (19, 0, 1, 0),
    (19, 5, 0, (-1)),
    (19, 8, 0, 0),
    (19, 13, 0, 0),
    (19, 14, 0, 0),
    (19, 18, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 20) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 20) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 20 := (0, 0, 4)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 20 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 13. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      -2 * X ^ 13 + 2 * X ^ 12 + X ^ 10 + 4 * X ^ 9 - 2 * X ^ 8 + 4 * X ^ 7 + 3 * X ^ 6 + 5 * X ^ 4 + 2 * X ^ 2 + 2 * X + 1 ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 2 * a (n - 4) + 2 * a (n - 5) - 2 * a (n - 6) + 2 * a (n - 7) - 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a310999
