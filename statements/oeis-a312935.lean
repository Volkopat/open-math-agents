import Mathlib

/-!
# OEIS A312935: Wu's conjectures for the coordination sequence Gal.4.105.1

Source: https://oeis.org/A312935 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A312935 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.105.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 9, 13, 18, ...
Formula section:
Conjectures from Chai Wah Wu, Feb 14 2020: (Start)
a(n) = a(n-1) + a(n-11) - a(n-12) for n > 12.
G.f.: (x^12 + 3*x^11 + 5*x^10 + 4*x^9 + 5*x^8 + 4*x^7 + 6*x^6 + 4*x^5 + 5*x^4 + 4*x^3 + 5*x^2 + 3*x
+ 1)/(x^12 - x^11 - x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 105 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 4l 4m 5e 6a 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.6.4,
  3.4.6.4, 3.3.4.3.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed terms
  occur in this file, from the base vertex below, and in 1 file of other tilings; and this is the
  only 4-uniform file that holds the listed terms of every entry Gal.4.105.v. The listed terms are
  proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 25) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 3.4.6.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a312935

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 25 × Fin 25 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, (-1), (-1)),
    (0, 6, 0, 0),
    (0, 16, 0, 0),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 7, 0, 1),
    (1, 8, 0, 0),
    (2, 1, 0, 0),
    (2, 3, (-1), 0),
    (2, 9, 0, 0),
    (2, 11, 0, 0),
    (3, 2, 1, 0),
    (3, 4, 0, 0),
    (3, 10, 0, 0),
    (3, 12, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 0),
    (4, 13, 0, 0),
    (4, 14, 0, 0),
    (5, 0, 1, 1),
    (5, 4, 0, 0),
    (5, 15, 0, 0),
    (5, 17, 0, 1),
    (6, 0, 0, 0),
    (6, 7, 0, 0),
    (6, 16, 0, 0),
    (6, 19, 0, 0),
    (7, 1, 0, (-1)),
    (7, 6, 0, 0),
    (7, 8, 0, (-1)),
    (7, 18, 0, 0),
    (8, 1, 0, 0),
    (8, 7, 0, 1),
    (8, 9, 0, 0),
    (8, 20, 0, 1),
    (9, 2, 0, 0),
    (9, 8, 0, 0),
    (9, 11, 0, 0),
    (9, 21, 0, 0),
    (10, 3, 0, 0),
    (10, 11, 1, 0),
    (10, 12, 0, 0),
    (10, 22, 0, 0),
    (10, 24, 0, 0),
    (11, 2, 0, 0),
    (11, 9, 0, 0),
    (11, 10, (-1), 0),
    (11, 22, (-1), 0),
    (11, 23, 0, 0),
    (12, 3, 0, 0),
    (12, 10, 0, 0),
    (12, 13, 0, 0),
    (12, 18, 0, 0),
    (13, 4, 0, 0),
    (13, 12, 0, 0),
    (13, 14, 0, 0),
    (13, 19, 0, 0),
    (14, 4, 0, 0),
    (14, 13, 0, 0),
    (14, 15, 0, 0),
    (14, 21, 0, 0),
    (15, 5, 0, 0),
    (15, 14, 0, 0),
    (15, 17, 0, 1),
    (15, 20, 0, 1),
    (16, 0, 0, 0),
    (16, 6, 0, 0),
    (16, 17, (-1), 0),
    (16, 22, (-1), 0),
    (16, 23, 0, 0),
    (17, 5, 0, (-1)),
    (17, 15, 0, (-1)),
    (17, 16, 1, 0),
    (17, 22, 0, 0),
    (17, 24, 0, 0),
    (18, 7, 0, 0),
    (18, 12, 0, 0),
    (18, 20, 0, 0),
    (18, 24, 0, 0),
    (19, 6, 0, 0),
    (19, 13, 0, 0),
    (19, 21, 0, 0),
    (19, 23, 0, 0),
    (20, 8, 0, (-1)),
    (20, 15, 0, (-1)),
    (20, 18, 0, 0),
    (20, 24, 0, 0),
    (21, 9, 0, 0),
    (21, 14, 0, 0),
    (21, 19, 0, 0),
    (21, 23, 0, 0),
    (22, 10, 0, 0),
    (22, 11, 1, 0),
    (22, 16, 1, 0),
    (22, 17, 0, 0),
    (22, 23, 1, 0),
    (22, 24, 0, 0),
    (23, 11, 0, 0),
    (23, 16, 0, 0),
    (23, 19, 0, 0),
    (23, 21, 0, 0),
    (23, 22, (-1), 0),
    (24, 10, 0, 0),
    (24, 17, 0, 0),
    (24, 18, 0, 0),
    (24, 20, 0, 0),
    (24, 22, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 25) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 25) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 25 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 25 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 12. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 12 - X ^ 11 - X + 1) =
      X ^ 12 + 3 * X ^ 11 + 5 * X ^ 10 + 4 * X ^ 9 + 5 * X ^ 8 + 4 * X ^ 7 + 6 * X ^ 6 + 4 * X ^ 5 + 5 * X ^ 4 + 4 * X ^ 3 + 5 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = a (n - 1) + a (n - 11) - a (n - 12) := by
  sorry

end OMA.S_oeis_a312935
