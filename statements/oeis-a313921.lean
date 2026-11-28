import Mathlib

/-!
# OEIS A313921: Wu's conjectures for the coordination sequence Gal.5.313.2

Source: https://oeis.org/A313921 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A313921 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.313.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 5, 10, 16, 22, ...
Formula section:
Conjectures from Chai Wah Wu, Feb 09 2023: (Start)
a(n) = 2*a(n-1) - 3*a(n-2) + 4*a(n-3) - 5*a(n-4) + 6*a(n-5) - 6*a(n-6) + 6*a(n-7) - 6*a(n-8) +
6*a(n-9) - 5*a(n-10) + 4*a(n-11) - 3*a(n-12) + 2*a(n-13) - a(n-14) for n > 14.
G.f.: (x^14 + 3*x^13 + 3*x^12 + 7*x^11 + 5*x^10 + 10*x^9 + 8*x^8 + 10*x^7 + 8*x^6 + 10*x^5 + 5*x^4 +
7*x^3 + 3*x^2 + 3*x + 1)/((x - 1)^2*(x^2 - x + 1)*(x^2 + x + 1)*(x^4 - x^3 + x^2 - x + 1)*(x^4 + x^3
+ x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 313 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/3 (221)/eu 5d 5e2 6a 6f 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.3.4.4,
  3.3.4.3.4, 3.3.3.3.3.3, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed terms
  occur in this file only, from the base vertex below; and this is the only 5-uniform file that
  holds the listed terms of every entry Gal.5.313.v. The listed terms are proved as controls in the
  proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 28) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 3.3.4.3.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a313921

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 28 × Fin 28 × ℤ × ℤ) :=
  [(0, 1, (-1), 0),
    (0, 3, (-1), (-1)),
    (0, 4, 0, 0),
    (0, 8, 0, (-1)),
    (0, 10, 0, 0),
    (1, 0, 1, 0),
    (1, 2, 0, (-1)),
    (1, 4, 1, 0),
    (1, 5, 0, 0),
    (1, 9, 1, 0),
    (2, 1, 0, 1),
    (2, 3, 0, 0),
    (2, 6, 0, 1),
    (2, 7, 0, 0),
    (2, 13, 0, 0),
    (3, 0, 1, 1),
    (3, 2, 0, 0),
    (3, 7, 0, 0),
    (3, 8, 1, 0),
    (3, 15, 0, 0),
    (4, 0, 0, 0),
    (4, 1, (-1), 0),
    (4, 9, 0, 0),
    (4, 11, 0, 0),
    (4, 16, 0, 0),
    (5, 1, 0, 0),
    (5, 6, 0, 0),
    (5, 9, 1, 0),
    (5, 12, 0, 0),
    (5, 19, 0, 0),
    (6, 2, 0, (-1)),
    (6, 5, 0, 0),
    (6, 12, 0, 0),
    (6, 13, 0, (-1)),
    (6, 21, 0, (-1)),
    (7, 2, 0, 0),
    (7, 3, 0, 0),
    (7, 13, 0, 0),
    (7, 14, 0, 0),
    (7, 22, 0, 0),
    (8, 0, 0, 1),
    (8, 3, (-1), 0),
    (8, 10, 0, 1),
    (8, 15, (-1), 0),
    (8, 23, 0, 0),
    (8, 24, 0, 0),
    (9, 1, (-1), 0),
    (9, 4, 0, 0),
    (9, 5, (-1), 0),
    (9, 16, 0, 0),
    (9, 19, (-1), 0),
    (9, 25, 0, 0),
    (10, 0, 0, 0),
    (10, 8, 0, (-1)),
    (10, 11, 0, 0),
    (10, 17, 0, 0),
    (10, 24, 0, (-1)),
    (11, 4, 0, 0),
    (11, 10, 0, 0),
    (11, 17, 0, 0),
    (11, 18, 0, 0),
    (11, 26, 0, 0),
    (12, 5, 0, 0),
    (12, 6, 0, 0),
    (12, 17, 0, 0),
    (12, 20, 0, 0),
    (12, 26, 0, 0),
    (13, 2, 0, 0),
    (13, 6, 0, 1),
    (13, 7, 0, 0),
    (13, 21, 0, 0),
    (13, 22, 0, 0),
    (13, 27, 0, 0),
    (14, 7, 0, 0),
    (14, 15, 0, 0),
    (14, 18, 0, 0),
    (14, 20, 0, 0),
    (14, 26, 0, 0),
    (15, 3, 0, 0),
    (15, 8, 1, 0),
    (15, 14, 0, 0),
    (15, 20, 0, 0),
    (15, 23, 1, 0),
    (16, 4, 0, 0),
    (16, 9, 0, 0),
    (16, 18, 0, 0),
    (16, 22, 0, 0),
    (16, 25, 0, 0),
    (17, 10, 0, 0),
    (17, 11, 0, 0),
    (17, 12, 0, 0),
    (17, 21, 0, (-1)),
    (17, 26, 0, 0),
    (18, 11, 0, 0),
    (18, 14, 0, 0),
    (18, 16, 0, 0),
    (18, 22, 0, 0),
    (18, 26, 0, 0),
    (19, 5, 0, 0),
    (19, 9, 1, 0),
    (19, 20, 0, 0),
    (19, 23, 1, 0),
    (19, 25, 1, 0),
    (20, 12, 0, 0),
    (20, 14, 0, 0),
    (20, 15, 0, 0),
    (20, 19, 0, 0),
    (20, 26, 0, 0),
    (21, 6, 0, 1),
    (21, 13, 0, 0),
    (21, 17, 0, 1),
    (21, 24, 0, 0),
    (21, 27, 0, 0),
    (22, 7, 0, 0),
    (22, 13, 0, 0),
    (22, 16, 0, 0),
    (22, 18, 0, 0),
    (22, 27, 0, 0),
    (23, 8, 0, 0),
    (23, 15, (-1), 0),
    (23, 19, (-1), 0),
    (23, 24, 0, 0),
    (23, 25, 0, 0),
    (24, 8, 0, 0),
    (24, 10, 0, 1),
    (24, 21, 0, 0),
    (24, 23, 0, 0),
    (24, 27, 0, 0),
    (25, 9, 0, 0),
    (25, 16, 0, 0),
    (25, 19, (-1), 0),
    (25, 23, 0, 0),
    (25, 27, 0, 0),
    (26, 11, 0, 0),
    (26, 12, 0, 0),
    (26, 14, 0, 0),
    (26, 17, 0, 0),
    (26, 18, 0, 0),
    (26, 20, 0, 0),
    (27, 13, 0, 0),
    (27, 21, 0, 0),
    (27, 22, 0, 0),
    (27, 24, 0, 0),
    (27, 25, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 28) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 28) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 28 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 28 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 14. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 14 + 3 * X ^ 13 + 3 * X ^ 12 + 7 * X ^ 11 + 5 * X ^ 10 + 10 * X ^ 9 + 8 * X ^ 8 + 10 * X ^ 7 + 8 * X ^ 6 + 10 * X ^ 5 + 5 * X ^ 4 + 7 * X ^ 3 + 3 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 6 * a (n - 6) + 6 * a (n - 7) - 6 * a (n - 8) + 6 * a (n - 9) - 5 * a (n - 10) + 4 * a (n - 11) - 3 * a (n - 12) + 2 * a (n - 13) - a (n - 14) := by
  sorry

end OMA.S_oeis_a313921
