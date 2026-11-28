import Mathlib

/-!
# OEIS A315628: Wu's conjectures for the coordination sequence Gal.4.104.4

Source: https://oeis.org/A315628 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315628 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.104.4 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 12, 16, 18, ...
Formula section:
Conjectures from Chai Wah Wu, Jun 09 2022: (Start)
a(n) = a(n-6) + a(n-10) - a(n-16) for n > 21.
G.f.: (-2*x^21 - 2*x^20 + 2*x^18 + x^16 + 6*x^15 + 14*x^14 + 18*x^13 + 18*x^12 + 28*x^11 + 35*x^10 +
32*x^9 + 32*x^8 + 28*x^7 + 33*x^6 + 28*x^5 + 18*x^4 + 16*x^3 + 12*x^2 + 6*x + 1)/(x^16 - x^10 - x^6
+ 1). (End)

Formalization notes:
* The tiling. The entry names tiling 104 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 4l 5e 5f 6f 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.6.4,
  3.3.4.3.4, 3.3.4.3.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed terms
  occur in this file only, from the base vertex below; and this is the only 4-uniform file that
  holds the listed terms of every entry Gal.4.104.v. The listed terms are proved as controls in the
  proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 27) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 18) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315628

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 27 × Fin 27 × ℤ × ℤ) :=
  [(0, 1, (-1), (-1)),
    (0, 5, 0, (-1)),
    (0, 6, 0, 0),
    (0, 17, 0, 0),
    (1, 0, 1, 1),
    (1, 2, 0, 0),
    (1, 7, 0, 1),
    (1, 8, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 9, 0, 0),
    (2, 10, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 1, 0),
    (3, 11, 0, 0),
    (3, 12, 0, 0),
    (4, 3, (-1), 0),
    (4, 5, 0, 0),
    (4, 13, 0, 0),
    (4, 14, 0, 0),
    (5, 0, 0, 1),
    (5, 4, 0, 0),
    (5, 15, 0, 0),
    (5, 16, 0, 1),
    (6, 0, 0, 0),
    (6, 7, (-1), 0),
    (6, 17, 0, 0),
    (6, 18, (-1), 0),
    (6, 21, 0, 0),
    (7, 1, 0, (-1)),
    (7, 6, 1, 0),
    (7, 8, 0, (-1)),
    (7, 18, 0, 0),
    (7, 23, 0, 0),
    (8, 1, 0, 0),
    (8, 7, 0, 1),
    (8, 9, 0, 0),
    (8, 19, 0, 0),
    (8, 24, 0, 1),
    (9, 2, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 19, 0, 0),
    (9, 25, 0, 0),
    (10, 2, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 20, 0, 0),
    (10, 22, 0, 0),
    (11, 3, 0, 0),
    (11, 10, 0, 0),
    (11, 12, 0, 0),
    (11, 20, 0, 0),
    (11, 26, 0, 0),
    (12, 3, 0, 0),
    (12, 11, 0, 0),
    (12, 13, 1, 0),
    (12, 18, 0, 0),
    (12, 23, 0, 0),
    (13, 4, 0, 0),
    (13, 12, (-1), 0),
    (13, 14, 0, 0),
    (13, 18, (-1), 0),
    (13, 21, 0, 0),
    (14, 4, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 0),
    (14, 19, 0, 0),
    (14, 25, 0, 0),
    (15, 5, 0, 0),
    (15, 14, 0, 0),
    (15, 16, 0, 1),
    (15, 19, 0, 0),
    (15, 24, 0, 1),
    (16, 5, 0, (-1)),
    (16, 15, 0, (-1)),
    (16, 17, 0, 0),
    (16, 20, 0, 0),
    (16, 26, 0, 0),
    (17, 0, 0, 0),
    (17, 6, 0, 0),
    (17, 16, 0, 0),
    (17, 20, 0, 0),
    (17, 22, 0, 0),
    (18, 6, 1, 0),
    (18, 7, 0, 0),
    (18, 12, 0, 0),
    (18, 13, 1, 0),
    (18, 21, 1, 0),
    (18, 23, 0, 0),
    (19, 8, 0, 0),
    (19, 9, 0, 0),
    (19, 14, 0, 0),
    (19, 15, 0, 0),
    (19, 24, 0, 1),
    (19, 25, 0, 0),
    (20, 10, 0, 0),
    (20, 11, 0, 0),
    (20, 16, 0, 0),
    (20, 17, 0, 0),
    (20, 22, 0, 0),
    (20, 26, 0, 0),
    (21, 6, 0, 0),
    (21, 13, 0, 0),
    (21, 18, (-1), 0),
    (21, 22, 0, 0),
    (21, 25, 0, 0),
    (22, 10, 0, 0),
    (22, 17, 0, 0),
    (22, 20, 0, 0),
    (22, 21, 0, 0),
    (22, 25, 0, 0),
    (23, 7, 0, 0),
    (23, 12, 0, 0),
    (23, 18, 0, 0),
    (23, 24, 0, 0),
    (23, 26, 0, 0),
    (24, 8, 0, (-1)),
    (24, 15, 0, (-1)),
    (24, 19, 0, (-1)),
    (24, 23, 0, 0),
    (24, 26, 0, 0),
    (25, 9, 0, 0),
    (25, 14, 0, 0),
    (25, 19, 0, 0),
    (25, 21, 0, 0),
    (25, 22, 0, 0),
    (26, 11, 0, 0),
    (26, 16, 0, 0),
    (26, 20, 0, 0),
    (26, 23, 0, 0),
    (26, 24, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 27) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 27) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 27 := (0, 0, 18)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 27 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 21. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 16 - X ^ 10 - X ^ 6 + 1) =
      -2 * X ^ 21 - 2 * X ^ 20 + 2 * X ^ 18 + X ^ 16 + 6 * X ^ 15 + 14 * X ^ 14 + 18 * X ^ 13 + 18 * X ^ 12 + 28 * X ^ 11 + 35 * X ^ 10 + 32 * X ^ 9 + 32 * X ^ 8 + 28 * X ^ 7 + 33 * X ^ 6 + 28 * X ^ 5 + 18 * X ^ 4 + 16 * X ^ 3 + 12 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 21 < n → (a n : ℤ) = a (n - 6) + a (n - 10) - a (n - 16) := by
  sorry

end OMA.S_oeis_a315628
