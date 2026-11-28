import Mathlib

/-!
# OEIS A314259: Wu's conjectures for the coordination sequence Gal.3.60.1

Source: https://oeis.org/A314259 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A314259 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.3.60.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 5, 11, 18, 22, ...
Formula section:
Conjectures from Chai Wah Wu, Apr 13 2024: (Start)
a(n) = 2*a(n-1) - 2*a(n-2) + 2*a(n-3) - 2*a(n-4) + 2*a(n-5) - 3*a(n-6) + 4*a(n-7) - 3*a(n-8) +
2*a(n-9) - 2*a(n-10) + 2*a(n-11) - 2*a(n-12) + 2*a(n-13) - a(n-14) for n > 14.
G.f.: (x^2 + x + 1)*(x^12 + 2*x^11 + 2*x^9 - 2*x^8 + 6*x^7 - 3*x^6 + 6*x^5 - 2*x^4 + 2*x^3 + 2*x +
1)/((x - 1)^2*(x^2 + 1)^2*(x^4 + 1)*(x^4 - x^2 + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 60 of Galebach's list of the 61 3-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/03/2 (21)/eu 5b 6j2 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.3.3.6, 3.3.3.3.3.3.
  Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and computing 50
  terms from every vertex class, the entry's 50 listed terms occur in this file only, from the base
  vertex below; and this is the only 3-uniform file that holds the listed terms of every entry
  Gal.3.60.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 18) in the cell (x, y) of the tiling's
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

namespace OMA.S_oeis_a314259

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 18 × Fin 18 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, (-1), 0),
    (0, 6, 0, (-1)),
    (0, 11, (-1), 0),
    (0, 12, (-1), (-1)),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 6, 0, 0),
    (1, 7, 0, 0),
    (1, 13, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 1),
    (2, 7, 0, 0),
    (2, 8, 0, 1),
    (2, 14, 0, 0),
    (3, 2, 0, (-1)),
    (3, 4, 0, 0),
    (3, 8, 0, 0),
    (3, 9, 0, 0),
    (3, 15, 0, 0),
    (4, 3, 0, 0),
    (4, 5, (-1), 0),
    (4, 9, 0, 0),
    (4, 10, (-1), 0),
    (4, 16, (-1), 0),
    (5, 0, 1, 0),
    (5, 4, 1, 0),
    (5, 10, 0, 0),
    (5, 11, 0, 0),
    (5, 17, 0, 0),
    (6, 0, 0, 1),
    (6, 1, 0, 0),
    (6, 9, 0, 0),
    (6, 12, (-1), 0),
    (6, 13, 0, 0),
    (6, 16, (-1), 0),
    (7, 1, 0, 0),
    (7, 2, 0, 0),
    (7, 10, 0, 0),
    (7, 13, 0, 0),
    (7, 14, 0, 0),
    (7, 17, 0, 0),
    (8, 2, 0, (-1)),
    (8, 3, 0, 0),
    (8, 11, 0, 0),
    (8, 12, 0, (-1)),
    (8, 14, 0, (-1)),
    (8, 15, 0, 0),
    (9, 3, 0, 0),
    (9, 4, 0, 0),
    (9, 6, 0, 0),
    (9, 13, 0, 0),
    (9, 15, 0, 0),
    (9, 16, (-1), 0),
    (10, 4, 1, 0),
    (10, 5, 0, 0),
    (10, 7, 0, 0),
    (10, 14, 0, 0),
    (10, 16, 0, 0),
    (10, 17, 0, 0),
    (11, 0, 1, 0),
    (11, 5, 0, 0),
    (11, 8, 0, 0),
    (11, 12, 0, (-1)),
    (11, 15, 0, 0),
    (11, 17, 0, 0),
    (12, 0, 1, 1),
    (12, 6, 1, 0),
    (12, 8, 0, 1),
    (12, 11, 0, 1),
    (12, 14, 0, 0),
    (12, 16, 0, 0),
    (13, 1, 0, 0),
    (13, 6, 0, 0),
    (13, 7, 0, 0),
    (13, 9, 0, 0),
    (13, 15, 0, 0),
    (13, 17, 0, 0),
    (14, 2, 0, 0),
    (14, 7, 0, 0),
    (14, 8, 0, 1),
    (14, 10, 0, 0),
    (14, 12, 0, 0),
    (14, 16, 0, 0),
    (15, 3, 0, 0),
    (15, 8, 0, 0),
    (15, 9, 0, 0),
    (15, 11, 0, 0),
    (15, 13, 0, 0),
    (15, 17, 0, 0),
    (16, 4, 1, 0),
    (16, 6, 1, 0),
    (16, 9, 1, 0),
    (16, 10, 0, 0),
    (16, 12, 0, 0),
    (16, 14, 0, 0),
    (17, 5, 0, 0),
    (17, 7, 0, 0),
    (17, 10, 0, 0),
    (17, 11, 0, 0),
    (17, 13, 0, 0),
    (17, 15, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 18) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 18) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 18 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 18 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 14. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) ^ 2 * (X ^ 4 + 1) * (X ^ 4 - X ^ 2 + 1)) =
      (X ^ 2 + X + 1) * (X ^ 12 + 2 * X ^ 11 + 2 * X ^ 9 - 2 * X ^ 8 + 6 * X ^ 7 - 3 * X ^ 6 + 6 * X ^ 5 - 2 * X ^ 4 + 2 * X ^ 3 + 2 * X + 1) ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 2 * a (n - 4) + 2 * a (n - 5) - 3 * a (n - 6) + 4 * a (n - 7) - 3 * a (n - 8) + 2 * a (n - 9) - 2 * a (n - 10) + 2 * a (n - 11) - 2 * a (n - 12) + 2 * a (n - 13) - a (n - 14) := by
  sorry

end OMA.S_oeis_a314259
