import Mathlib

/-!
# OEIS A311553: Wu's conjectures for the coordination sequence Gal.6.133.1

Source: https://oeis.org/A311553 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311553 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.133.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 12, 17, ...
Formula section:
Conjectures from Chai Wah Wu, Jan 24 2020: (Start)
a(n) = a(n-1) + a(n-11) - a(n-12) for n > 12.
G.f.: (x^12 + 3*x^11 + 4*x^10 + 4*x^9 + 5*x^8 + 6*x^7 + 6*x^6 + 6*x^5 + 5*x^4 + 4*x^3 + 4*x^2 + 3*x
+ 1)/(x^12 - x^11 - x + 1). (End)

Formalization notes:
* The tiling. The entry names tiling 133 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/3 (321)/eu 4s3 5c 6f 6i 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 4.4.4.4,
  3.3.3.4.4, 3.3.3.3.3.3, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, this is the only 6-uniform
  catalog file in which every entry Gal.6.133.w of this tiling occurs (6 entries), and the entry's
  50 listed terms are those of the base vertex below (no other catalog file has them). The listed
  terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 11) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 4.4.4.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311553

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 11 × Fin 11 × ℤ × ℤ) :=
  [(0, 0, (-1), 0),
    (0, 0, 1, 0),
    (0, 1, 0, 0),
    (0, 3, 0, (-1)),
    (1, 0, 0, 0),
    (1, 1, (-1), 0),
    (1, 1, 1, 0),
    (1, 2, 0, 0),
    (2, 1, 0, 0),
    (2, 2, (-1), 0),
    (2, 2, 1, 0),
    (2, 4, 0, 0),
    (3, 0, 0, 1),
    (3, 3, (-1), 0),
    (3, 3, 1, 0),
    (3, 5, 0, 0),
    (4, 2, 0, 0),
    (4, 4, (-1), 0),
    (4, 4, 1, 0),
    (4, 6, 0, 0),
    (5, 3, 0, 0),
    (5, 5, (-1), 0),
    (5, 5, 1, 0),
    (5, 7, 0, 0),
    (6, 4, 0, 0),
    (6, 6, (-1), 0),
    (6, 6, 1, 0),
    (6, 8, (-1), 0),
    (6, 8, 0, 0),
    (7, 5, 0, 0),
    (7, 7, (-1), 0),
    (7, 7, 1, 0),
    (7, 9, (-1), 0),
    (7, 9, 0, 0),
    (8, 6, 0, 0),
    (8, 6, 1, 0),
    (8, 8, (-1), 0),
    (8, 8, 1, 0),
    (8, 10, 0, 0),
    (8, 10, 1, 0),
    (9, 7, 0, 0),
    (9, 7, 1, 0),
    (9, 9, (-1), 0),
    (9, 9, 1, 0),
    (9, 10, 0, 0),
    (9, 10, 1, 0),
    (10, 8, (-1), 0),
    (10, 8, 0, 0),
    (10, 9, (-1), 0),
    (10, 9, 0, 0),
    (10, 10, (-1), 0),
    (10, 10, 1, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 11) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 11) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 11 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 11 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 12. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 12 - X ^ 11 - X + 1) =
      X ^ 12 + 3 * X ^ 11 + 4 * X ^ 10 + 4 * X ^ 9 + 5 * X ^ 8 + 6 * X ^ 7 + 6 * X ^ 6 + 6 * X ^ 5 + 5 * X ^ 4 + 4 * X ^ 3 + 4 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = a (n - 1) + a (n - 11) - a (n - 12) := by
  sorry

end OMA.S_oeis_a311553
