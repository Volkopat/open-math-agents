import Mathlib

/-!
# OEIS A311824: Wu's conjectures for the coordination sequence Gal.5.158.5

Source: https://oeis.org/A311824 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311824 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.158.5 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 13, 17, ...
Formula section:
Conjectures from Chai Wah Wu, Nov 19 2025: (Start)
a(n) = 2*a(n-1) - 3*a(n-2) + 4*a(n-3) - 5*a(n-4) + 6*a(n-5) - 7*a(n-6) + 8*a(n-7) - 8*a(n-8) +
8*a(n-9) - 8*a(n-10) + 8*a(n-11) - 8*a(n-12) + 8*a(n-13) - 7*a(n-14) + 6*a(n-15) - 5*a(n-16) +
4*a(n-17) - 3*a(n-18) + 2*a(n-19) - a(n-20) for n > 20.
G.f.: (x^2 + x + 1)^2*(x^16 + 3*x^13 - 3*x^12 + 5*x^11 - 2*x^10 + 4*x^9 - 2*x^8 + 4*x^7 - 2*x^6 +
5*x^5 - 3*x^4 + 3*x^3 + 1)/((x - 1)^2*(x^2 + 1)*(x^4 + 1)*(x^6 - x^5 + x^4 - x^3 + x^2 - x + 1)*(x^6
+ x^5 + x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 158 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/4 (2111)/eu 4d 4k 4l 4m 5e 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6,
  3.4.4.6, 3.4.6.4, 3.4.6.4, 3.3.4.3.4. Identification: unfolding the catalog files of all 1217 3-
  to 6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed terms
  occur in this file only, from the base vertex below; and this is the only 5-uniform file that
  holds the listed terms of every entry Gal.5.158.v. The listed terms are proved as controls in the
  proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 42) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 14) is a vertex of type 3.4.6.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311824

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 42 × Fin 42 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 5, 0, (-1)),
    (0, 6, (-1), 0),
    (0, 17, (-1), (-1)),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 6, (-1), 0),
    (1, 8, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 7, 0, 0),
    (2, 11, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 11, 0, 0),
    (3, 12, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, (-1)),
    (4, 13, 0, 0),
    (4, 14, 0, (-1)),
    (5, 0, 0, 1),
    (5, 4, 0, 1),
    (5, 15, 0, 0),
    (5, 16, (-1), 0),
    (6, 0, 1, 0),
    (6, 1, 1, 0),
    (6, 8, 1, 0),
    (6, 18, 0, (-1)),
    (6, 36, 0, 0),
    (7, 2, 0, 0),
    (7, 10, 0, 0),
    (7, 11, 0, 0),
    (7, 24, 0, 0),
    (8, 1, 0, 0),
    (8, 6, (-1), 0),
    (8, 9, 0, 0),
    (8, 19, (-1), 0),
    (9, 8, 0, 0),
    (9, 10, 0, 0),
    (9, 20, (-1), 0),
    (9, 21, 0, 0),
    (10, 7, 0, 0),
    (10, 9, 0, 0),
    (10, 22, 0, 0),
    (10, 23, 0, 0),
    (11, 2, 0, 0),
    (11, 3, 0, 0),
    (11, 7, 0, 0),
    (11, 25, 0, 0),
    (11, 37, 0, 0),
    (12, 3, 0, 0),
    (12, 13, 0, 0),
    (12, 25, 0, 0),
    (12, 26, 0, 0),
    (13, 4, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, (-1)),
    (13, 29, 0, (-1)),
    (14, 4, 0, 1),
    (14, 13, 0, 1),
    (14, 15, 0, 0),
    (14, 30, 0, 0),
    (15, 5, 0, 0),
    (15, 14, 0, 0),
    (15, 16, (-1), 0),
    (15, 31, 0, 0),
    (16, 5, 1, 0),
    (16, 15, 1, 0),
    (16, 17, 0, 0),
    (16, 35, 0, 0),
    (17, 0, 1, 1),
    (17, 16, 0, 0),
    (17, 18, 0, 0),
    (17, 34, 0, 0),
    (18, 6, 0, 1),
    (18, 17, 0, 0),
    (18, 34, 0, 0),
    (18, 36, 0, 1),
    (18, 40, 0, 0),
    (19, 8, 1, 0),
    (19, 20, 0, 0),
    (19, 27, 0, 0),
    (19, 36, 0, 0),
    (20, 9, 1, 0),
    (20, 19, 0, 0),
    (20, 21, 1, 0),
    (20, 39, 0, 0),
    (21, 9, 0, 0),
    (21, 20, (-1), 0),
    (21, 22, 0, 0),
    (21, 31, 0, 0),
    (22, 10, 0, 0),
    (22, 21, 0, 0),
    (22, 23, 0, 0),
    (22, 30, 0, 0),
    (23, 10, 0, 0),
    (23, 22, 0, 0),
    (23, 24, 0, 0),
    (23, 41, 0, 0),
    (24, 7, 0, 0),
    (24, 23, 0, 0),
    (24, 33, 0, 0),
    (24, 37, 0, 0),
    (25, 11, 0, 0),
    (25, 12, 0, 0),
    (25, 26, 0, 0),
    (25, 37, 0, 0),
    (25, 38, 0, 0),
    (26, 12, 0, 0),
    (26, 25, 0, 0),
    (26, 27, 0, 0),
    (26, 38, 0, 0),
    (27, 19, 0, 0),
    (27, 26, 0, 0),
    (27, 28, 0, 0),
    (27, 36, 0, 0),
    (28, 27, 0, 0),
    (28, 29, 0, (-1)),
    (28, 36, 0, 0),
    (28, 40, 0, (-1)),
    (29, 13, 0, 1),
    (29, 28, 0, 1),
    (29, 30, 0, 0),
    (29, 41, 0, 0),
    (30, 14, 0, 0),
    (30, 22, 0, 0),
    (30, 29, 0, 0),
    (30, 41, 0, 0),
    (31, 15, 0, 0),
    (31, 21, 0, 0),
    (31, 35, (-1), 0),
    (31, 39, (-1), 0),
    (32, 33, 0, 0),
    (32, 35, 0, 0),
    (32, 37, 0, 0),
    (32, 38, 0, 0),
    (33, 24, 0, 0),
    (33, 32, 0, 0),
    (33, 34, 0, 0),
    (33, 37, 0, 0),
    (34, 17, 0, 0),
    (34, 18, 0, 0),
    (34, 33, 0, 0),
    (34, 40, 0, 0),
    (35, 16, 0, 0),
    (35, 31, 1, 0),
    (35, 32, 0, 0),
    (35, 39, 0, 0),
    (36, 6, 0, 0),
    (36, 18, 0, (-1)),
    (36, 19, 0, 0),
    (36, 27, 0, 0),
    (36, 28, 0, 0),
    (37, 11, 0, 0),
    (37, 24, 0, 0),
    (37, 25, 0, 0),
    (37, 32, 0, 0),
    (37, 33, 0, 0),
    (38, 25, 0, 0),
    (38, 26, 0, 0),
    (38, 32, 0, 0),
    (38, 39, 0, 0),
    (39, 20, 0, 0),
    (39, 31, 1, 0),
    (39, 35, 0, 0),
    (39, 38, 0, 0),
    (40, 18, 0, 0),
    (40, 28, 0, 1),
    (40, 34, 0, 0),
    (40, 41, 0, 0),
    (41, 23, 0, 0),
    (41, 29, 0, 0),
    (41, 30, 0, 0),
    (41, 40, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 42) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 42) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 42 := (0, 0, 14)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 42 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 20. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      (X ^ 2 + X + 1) ^ 2 * (X ^ 16 + 3 * X ^ 13 - 3 * X ^ 12 + 5 * X ^ 11 - 2 * X ^ 10 + 4 * X ^ 9 - 2 * X ^ 8 + 4 * X ^ 7 - 2 * X ^ 6 + 5 * X ^ 5 - 3 * X ^ 4 + 3 * X ^ 3 + 1) ∧
    ∀ n : ℕ, 20 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 7 * a (n - 6) + 8 * a (n - 7) - 8 * a (n - 8) + 8 * a (n - 9) - 8 * a (n - 10) + 8 * a (n - 11) - 8 * a (n - 12) + 8 * a (n - 13) - 7 * a (n - 14) + 6 * a (n - 15) - 5 * a (n - 16) + 4 * a (n - 17) - 3 * a (n - 18) + 2 * a (n - 19) - a (n - 20) := by
  sorry

end OMA.S_oeis_a311824
