import Mathlib

/-!
# OEIS A315575: Wu's conjectures for the coordination sequence Gal.4.84.4

Source: https://oeis.org/A315575 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315575 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.84.4 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 6, 12, 12, 18, ...
Formula section:
Conjectures from Chai Wah Wu, Sep 14 2025: (Start)
a(n) = a(n-3) + a(n-11) - a(n-14) for n > 14.
G.f.: (x^14 + 6*x^13 + 12*x^12 + 11*x^11 + 12*x^10 + 6*x^9 + 18*x^8 + 18*x^7 + 18*x^6 + 6*x^5 +
12*x^4 + 11*x^3 + 12*x^2 + 6*x + 1)/(x^14 - x^11 - x^3 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 84 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/4/eu 4k 4l 5e 6a 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.4.6, 3.4.6.4,
  3.3.4.3.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this
  file only, from the base vertex below; and this is the only 4-uniform file that holds the listed
  terms of every entry Gal.4.84.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 25) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 24) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315575

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 25 × Fin 25 × ℤ × ℤ) :=
  [(0, 1, (-1), 0),
    (0, 5, (-1), (-1)),
    (0, 6, 0, 0),
    (0, 15, 0, (-1)),
    (1, 0, 1, 0),
    (1, 2, 0, 0),
    (1, 6, 1, 0),
    (1, 7, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 8, 0, 0),
    (2, 9, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 10, 0, 0),
    (3, 11, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, (-1)),
    (4, 11, 0, 0),
    (4, 12, 0, (-1)),
    (5, 0, 1, 1),
    (5, 4, 0, 1),
    (5, 13, 0, 0),
    (5, 14, 1, 0),
    (6, 0, 0, 0),
    (6, 1, (-1), 0),
    (6, 16, 0, 0),
    (6, 17, 0, (-1)),
    (6, 24, 0, 0),
    (7, 1, 0, 0),
    (7, 8, 0, 0),
    (7, 16, 1, 0),
    (7, 19, 1, 0),
    (8, 2, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 18, 0, 0),
    (9, 2, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 21, 0, 0),
    (10, 3, 0, 0),
    (10, 9, 0, 0),
    (10, 20, 0, 0),
    (10, 22, 0, 0),
    (11, 3, 0, 0),
    (11, 4, 0, 0),
    (11, 22, 0, 0),
    (11, 23, 0, (-1)),
    (11, 24, 0, 0),
    (12, 4, 0, 1),
    (12, 13, 0, 0),
    (12, 18, 0, 0),
    (12, 23, 0, 0),
    (13, 5, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 1, 0),
    (13, 19, 1, 0),
    (14, 5, (-1), 0),
    (14, 13, (-1), 0),
    (14, 15, 0, 0),
    (14, 20, 0, 0),
    (15, 0, 0, 1),
    (15, 14, 0, 0),
    (15, 17, 0, 0),
    (15, 21, 0, 0),
    (16, 6, 0, 0),
    (16, 7, (-1), 0),
    (16, 19, 0, 0),
    (16, 22, 0, 0),
    (16, 24, 0, 0),
    (17, 6, 0, 1),
    (17, 15, 0, 0),
    (17, 21, 0, 0),
    (17, 23, 0, 0),
    (17, 24, 0, 1),
    (18, 8, 0, 0),
    (18, 12, 0, 0),
    (18, 21, 0, 0),
    (18, 23, 0, 0),
    (19, 7, (-1), 0),
    (19, 13, (-1), 0),
    (19, 16, 0, 0),
    (19, 20, 0, 0),
    (20, 10, 0, 0),
    (20, 14, 0, 0),
    (20, 19, 0, 0),
    (20, 22, 0, 0),
    (21, 9, 0, 0),
    (21, 15, 0, 0),
    (21, 17, 0, 0),
    (21, 18, 0, 0),
    (22, 10, 0, 0),
    (22, 11, 0, 0),
    (22, 16, 0, 0),
    (22, 20, 0, 0),
    (22, 24, 0, 0),
    (23, 11, 0, 1),
    (23, 12, 0, 0),
    (23, 17, 0, 0),
    (23, 18, 0, 0),
    (23, 24, 0, 1),
    (24, 6, 0, 0),
    (24, 11, 0, 0),
    (24, 16, 0, 0),
    (24, 17, 0, (-1)),
    (24, 22, 0, 0),
    (24, 23, 0, (-1))]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 25) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 25) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 25 := (0, 0, 24)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 25 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 14. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 - X ^ 11 - X ^ 3 + 1) =
      X ^ 14 + 6 * X ^ 13 + 12 * X ^ 12 + 11 * X ^ 11 + 12 * X ^ 10 + 6 * X ^ 9 + 18 * X ^ 8 + 18 * X ^ 7 + 18 * X ^ 6 + 6 * X ^ 5 + 12 * X ^ 4 + 11 * X ^ 3 + 12 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = a (n - 3) + a (n - 11) - a (n - 14) := by
  sorry

end OMA.S_oeis_a315575
