import Mathlib

/-!
# OEIS A314219: Wu's conjectures for the coordination sequence Gal.5.314.1

Source: https://oeis.org/A314219 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A314219 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.314.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 5, 11, 17, 22, ...
Formula section:
Conjectures from Chai Wah Wu, Sep 12 2025: (Start)
a(n) = 2*a(n-1) - 2*a(n-2) + a(n-3) + a(n-11) - 2*a(n-12) + 2*a(n-13) - a(n-14) for n > 14.
G.f.: (x^2 + x + 1)*(x^12 + 2*x^11 + 2*x^9 + 3*x^8 + 2*x^7 + 2*x^5 + 3*x^4 + 2*x^3 + 2*x + 1)/(x^14
- 2*x^13 + 2*x^12 - x^11 - x^3 + 2*x^2 - 2*x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 314 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/3 (221)/eu 5a 5c2 5e2 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.3.3.6,
  3.3.3.4.4, 3.3.4.3.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this
  file only, from the base vertex below; and this is the only 5-uniform file that holds the listed
  terms of every entry Gal.5.314.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 30) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 18) is a vertex of type 3.3.3.4.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a314219

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 30 × Fin 30 × ℤ × ℤ) :=
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
    (7, 1, 0, 0),
    (7, 2, 0, 0),
    (7, 13, 0, 0),
    (7, 14, 0, 0),
    (7, 21, 0, 0),
    (8, 2, 0, 0),
    (8, 3, 1, 0),
    (8, 14, 0, 0),
    (8, 15, 1, 0),
    (8, 24, 0, 0),
    (9, 3, 0, 0),
    (9, 4, 0, 0),
    (9, 15, 0, 0),
    (9, 16, 0, 0),
    (9, 26, 0, 0),
    (10, 4, 0, (-1)),
    (10, 5, 0, 0),
    (10, 16, 0, (-1)),
    (10, 17, 0, 0),
    (10, 28, 0, 0),
    (11, 0, 0, 0),
    (11, 5, 0, 0),
    (11, 12, 0, 0),
    (11, 17, 0, 0),
    (11, 29, 0, 0),
    (12, 0, 0, 0),
    (12, 6, (-1), 0),
    (12, 11, 0, 0),
    (12, 19, (-1), 0),
    (12, 27, 0, 0),
    (13, 1, 0, 0),
    (13, 6, 0, 1),
    (13, 7, 0, 0),
    (13, 20, 0, 0),
    (13, 22, 0, 0),
    (14, 2, 0, 0),
    (14, 7, 0, 0),
    (14, 8, 0, 0),
    (14, 23, 0, 0),
    (14, 25, 0, 0),
    (15, 3, 0, 0),
    (15, 8, (-1), 0),
    (15, 9, 0, 0),
    (15, 19, (-1), 0),
    (15, 27, 0, 0),
    (16, 4, 0, 0),
    (16, 9, 0, 0),
    (16, 10, 0, 1),
    (16, 20, 0, 0),
    (16, 22, 0, 0),
    (17, 5, 0, 0),
    (17, 10, 0, 0),
    (17, 11, 0, 0),
    (17, 23, 0, 0),
    (17, 25, 0, 0),
    (18, 6, 0, 0),
    (18, 19, 0, 0),
    (18, 20, 0, (-1)),
    (18, 24, 0, 0),
    (18, 28, 0, 0),
    (19, 12, 1, 0),
    (19, 15, 1, 0),
    (19, 18, 0, 0),
    (19, 24, 0, 0),
    (19, 27, 1, 0),
    (20, 13, 0, 0),
    (20, 16, 0, 0),
    (20, 18, 0, 1),
    (20, 22, 0, 0),
    (20, 28, 0, 1),
    (21, 7, 0, 0),
    (21, 22, 0, 0),
    (21, 23, 0, 0),
    (21, 26, 0, 0),
    (21, 29, 0, 0),
    (22, 13, 0, 0),
    (22, 16, 0, 0),
    (22, 20, 0, 0),
    (22, 21, 0, 0),
    (22, 26, 0, 0),
    (23, 14, 0, 0),
    (23, 17, 0, 0),
    (23, 21, 0, 0),
    (23, 25, 0, 0),
    (23, 29, 0, 0),
    (24, 8, 0, 0),
    (24, 18, 0, 0),
    (24, 19, 0, 0),
    (24, 25, 0, 0),
    (24, 28, 0, 0),
    (25, 14, 0, 0),
    (25, 17, 0, 0),
    (25, 23, 0, 0),
    (25, 24, 0, 0),
    (25, 28, 0, 0),
    (26, 9, 0, 0),
    (26, 21, 0, 0),
    (26, 22, 0, 0),
    (26, 27, 0, 0),
    (26, 29, 0, 0),
    (27, 12, 0, 0),
    (27, 15, 0, 0),
    (27, 19, (-1), 0),
    (27, 26, 0, 0),
    (27, 29, 0, 0),
    (28, 10, 0, 0),
    (28, 18, 0, 0),
    (28, 20, 0, (-1)),
    (28, 24, 0, 0),
    (28, 25, 0, 0),
    (29, 11, 0, 0),
    (29, 21, 0, 0),
    (29, 23, 0, 0),
    (29, 26, 0, 0),
    (29, 27, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 30) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 30) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 30 := (0, 0, 18)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 30 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 14. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 - 2 * X ^ 13 + 2 * X ^ 12 - X ^ 11 - X ^ 3 + 2 * X ^ 2 - 2 * X + 1) =
      (X ^ 2 + X + 1) * (X ^ 12 + 2 * X ^ 11 + 2 * X ^ 9 + 3 * X ^ 8 + 2 * X ^ 7 + 2 * X ^ 5 + 3 * X ^ 4 + 2 * X ^ 3 + 2 * X + 1) ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + a (n - 3) + a (n - 11) - 2 * a (n - 12) + 2 * a (n - 13) - a (n - 14) := by
  sorry

end OMA.S_oeis_a314219
