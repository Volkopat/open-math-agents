import Mathlib

/-!
# OEIS A315532: Wu's conjectures for the coordination sequence Gal.6.662.3

Source: https://oeis.org/A315532 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315532 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.662.3 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 11, 17, 22, ...
Formula section:
Conjectures from Chai Wah Wu, May 07 2024: (Start)
a(n) = 2*a(n-1) - 3*a(n-2) + 4*a(n-3) - 5*a(n-4) + 6*a(n-5) - 6*a(n-6) + 6*a(n-7) - 6*a(n-8) +
6*a(n-9) - 5*a(n-10) + 4*a(n-11) - 3*a(n-12) + 2*a(n-13) - a(n-14) for n > 14.
G.f.: (x^14 + 4*x^13 + 2*x^12 + 9*x^11 + 2*x^10 + 17*x^9 - 3*x^8 + 20*x^7 - 3*x^6 + 17*x^5 + 2*x^4 +
9*x^3 + 2*x^2 + 4*x + 1)/((x - 1)^2*(x^2 - x + 1)*(x^2 + x + 1)*(x^4 - x^3 + x^2 - x + 1)*(x^4 + x^3
+ x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 662 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/3 (411)/eu 5c 5e3 5f 6h 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.3.4.4,
  3.3.4.3.4, 3.3.4.3.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, this is the only 6-uniform
  catalog file in which every entry Gal.6.662.w of this tiling occurs (6 entries), and the entry's
  50 listed terms are those of the base vertex below (no other catalog file has them). The listed
  terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 14) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 4) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315532

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 14 × Fin 14 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 3, 0, 0),
    (0, 4, (-1), 0),
    (0, 7, 0, (-1)),
    (0, 9, (-1), (-1)),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 4, (-1), 0),
    (1, 6, 0, 0),
    (1, 8, (-1), 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 4, 0, 0),
    (2, 5, 0, 0),
    (2, 8, 0, 0),
    (3, 0, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 7, 0, (-1)),
    (3, 9, 0, (-1)),
    (4, 0, 1, 0),
    (4, 1, 1, 0),
    (4, 2, 0, 0),
    (4, 3, 0, 0),
    (4, 8, 0, 0),
    (4, 9, 0, (-1)),
    (5, 2, 0, 0),
    (5, 6, 0, 0),
    (5, 8, 0, 0),
    (5, 10, 0, 0),
    (5, 13, 0, 0),
    (6, 1, 0, 0),
    (6, 5, 0, 0),
    (6, 8, (-1), 0),
    (6, 10, 0, 0),
    (6, 13, (-1), 0),
    (7, 0, 0, 1),
    (7, 3, 0, 1),
    (7, 10, 0, 0),
    (7, 11, (-1), 0),
    (7, 12, 0, 0),
    (8, 1, 1, 0),
    (8, 2, 0, 0),
    (8, 4, 0, 0),
    (8, 5, 0, 0),
    (8, 6, 1, 0),
    (8, 13, 0, 0),
    (9, 0, 1, 1),
    (9, 3, 0, 1),
    (9, 4, 0, 1),
    (9, 11, 0, 0),
    (9, 12, 0, 0),
    (10, 5, 0, 0),
    (10, 6, 0, 0),
    (10, 7, 0, 0),
    (10, 11, (-1), 0),
    (10, 12, 0, 0),
    (11, 7, 1, 0),
    (11, 9, 0, 0),
    (11, 10, 1, 0),
    (11, 12, 0, 0),
    (11, 13, 0, 0),
    (12, 7, 0, 0),
    (12, 9, 0, 0),
    (12, 10, 0, 0),
    (12, 11, 0, 0),
    (12, 13, 0, 0),
    (13, 5, 0, 0),
    (13, 6, 1, 0),
    (13, 8, 0, 0),
    (13, 11, 0, 0),
    (13, 12, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 14) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 14) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 14 := (0, 0, 4)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 14 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 14. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 14 + 4 * X ^ 13 + 2 * X ^ 12 + 9 * X ^ 11 + 2 * X ^ 10 + 17 * X ^ 9 - 3 * X ^ 8 + 20 * X ^ 7 - 3 * X ^ 6 + 17 * X ^ 5 + 2 * X ^ 4 + 9 * X ^ 3 + 2 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 6 * a (n - 6) + 6 * a (n - 7) - 6 * a (n - 8) + 6 * a (n - 9) - 5 * a (n - 10) + 4 * a (n - 11) - 3 * a (n - 12) + 2 * a (n - 13) - a (n - 14) := by
  sorry

end OMA.S_oeis_a315532
