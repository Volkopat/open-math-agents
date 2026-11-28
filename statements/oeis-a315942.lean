import Mathlib

/-!
# OEIS A315942: Wu's conjectures for the coordination sequence Gal.6.507.5

Source: https://oeis.org/A315942 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315942 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.507.5 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 8, 18, 18, ...
Formula section:
Conjectures from Chai Wah Wu, Jan 09 2020: (Start)
a(n) = 2*a(n-6) - a(n-12) for n > 12.
G.f.: (x^12 + 6*x^11 + 8*x^10 + 18*x^9 + 18*x^8 + 22*x^7 + 34*x^6 + 22*x^5 + 18*x^4 + 18*x^3 + 8*x^2
+ 6*x + 1)/(x^12 - 2*x^6 + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 507 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/3 (321)/eu 4d2 5b 6a 6d 6f 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6,
  3.3.3.3.6, 3.3.3.3.3.3, 3.3.3.3.3.3, 3.3.3.3.3.3. Identification: unfolding the catalog files of
  all 1217 3- to 6-uniform tilings and computing 50 terms from every vertex class, this is the only
  6-uniform catalog file in which every entry Gal.6.507.w of this tiling occurs (6 entries), and the
  entry's 50 listed terms are those of the base vertex below (no other catalog file has them). The
  listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 30) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 11) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315942

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 30 × Fin 30 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 5, (-1), 0),
    (0, 6, 0, 0),
    (0, 14, 0, (-1)),
    (1, 0, 0, 0),
    (1, 2, (-1), 0),
    (1, 6, 0, 0),
    (1, 7, 0, 0),
    (2, 1, 1, 0),
    (2, 3, 0, 0),
    (2, 10, 0, 0),
    (2, 11, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 11, 0, 0),
    (3, 12, 0, 0),
    (3, 24, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 12, 0, 0),
    (4, 13, 0, 0),
    (4, 20, 0, 0),
    (5, 0, 1, 0),
    (5, 4, 0, 0),
    (5, 13, 0, 0),
    (5, 15, 0, (-1)),
    (6, 0, 0, 0),
    (6, 1, 0, 0),
    (6, 7, 0, 0),
    (6, 14, 0, (-1)),
    (6, 18, 0, 0),
    (6, 25, 0, (-1)),
    (7, 1, 0, 0),
    (7, 6, 0, 0),
    (7, 8, 0, 0),
    (7, 18, 0, 0),
    (8, 7, 0, 0),
    (8, 9, 0, 0),
    (8, 21, 0, 0),
    (8, 22, 0, 0),
    (9, 8, 0, 0),
    (9, 10, (-1), 0),
    (9, 16, 0, 0),
    (9, 22, 0, 0),
    (9, 23, (-1), 0),
    (10, 2, 0, 0),
    (10, 9, 1, 0),
    (10, 11, 0, 0),
    (10, 23, 0, 0),
    (10, 28, 0, 0),
    (11, 2, 0, 0),
    (11, 3, 0, 0),
    (11, 10, 0, 0),
    (11, 24, 0, 0),
    (11, 27, 0, 0),
    (11, 28, 0, 0),
    (12, 3, 0, 0),
    (12, 4, 0, 0),
    (12, 20, 0, 0),
    (12, 21, 0, 0),
    (12, 24, 0, 0),
    (12, 26, 0, 0),
    (13, 4, 0, 0),
    (13, 5, 0, 0),
    (13, 15, 0, (-1)),
    (13, 19, 0, 0),
    (13, 20, 0, 0),
    (13, 29, 0, (-1)),
    (14, 0, 0, 1),
    (14, 6, 0, 1),
    (14, 17, 0, 0),
    (14, 25, 0, 0),
    (15, 5, 0, 1),
    (15, 13, 0, 1),
    (15, 16, 1, 0),
    (15, 23, 0, 0),
    (15, 29, 0, 0),
    (16, 9, 0, 0),
    (16, 15, (-1), 0),
    (16, 17, 0, 0),
    (16, 22, 0, 0),
    (16, 23, (-1), 0),
    (17, 14, 0, 0),
    (17, 16, 0, 0),
    (17, 22, 0, 0),
    (17, 26, 0, 0),
    (18, 6, 0, 0),
    (18, 7, 0, 0),
    (18, 19, 0, 0),
    (18, 25, 0, (-1)),
    (19, 13, 0, 0),
    (19, 18, 0, 0),
    (19, 20, 0, 0),
    (19, 29, 0, (-1)),
    (20, 4, 0, 0),
    (20, 12, 0, 0),
    (20, 13, 0, 0),
    (20, 19, 0, 0),
    (20, 21, 0, 0),
    (21, 8, 0, 0),
    (21, 12, 0, 0),
    (21, 20, 0, 0),
    (21, 22, 0, 0),
    (21, 26, 0, 0),
    (22, 8, 0, 0),
    (22, 9, 0, 0),
    (22, 16, 0, 0),
    (22, 17, 0, 0),
    (22, 21, 0, 0),
    (22, 26, 0, 0),
    (23, 9, 1, 0),
    (23, 10, 0, 0),
    (23, 15, 0, 0),
    (23, 16, 1, 0),
    (23, 28, 0, 0),
    (23, 29, 0, 0),
    (24, 3, 0, 0),
    (24, 11, 0, 0),
    (24, 12, 0, 0),
    (24, 26, 0, 0),
    (24, 27, 0, 0),
    (25, 6, 0, 1),
    (25, 14, 0, 0),
    (25, 18, 0, 1),
    (25, 27, 0, 0),
    (26, 12, 0, 0),
    (26, 17, 0, 0),
    (26, 21, 0, 0),
    (26, 22, 0, 0),
    (26, 24, 0, 0),
    (27, 11, 0, 0),
    (27, 24, 0, 0),
    (27, 25, 0, 0),
    (27, 28, 0, 0),
    (28, 10, 0, 0),
    (28, 11, 0, 0),
    (28, 23, 0, 0),
    (28, 27, 0, 0),
    (28, 29, 0, 0),
    (29, 13, 0, 1),
    (29, 15, 0, 0),
    (29, 19, 0, 1),
    (29, 23, 0, 0),
    (29, 28, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 30) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 30) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 30 := (0, 0, 11)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 30 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 12. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 12 - 2 * X ^ 6 + 1) =
      X ^ 12 + 6 * X ^ 11 + 8 * X ^ 10 + 18 * X ^ 9 + 18 * X ^ 8 + 22 * X ^ 7 + 34 * X ^ 6 + 22 * X ^ 5 + 18 * X ^ 4 + 18 * X ^ 3 + 8 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 2 * a (n - 6) - a (n - 12) := by
  sorry

end OMA.S_oeis_a315942
