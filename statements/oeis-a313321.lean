import Mathlib

/-!
# OEIS A313321: Wu's conjectures for the coordination sequence Gal.3.42.1

Source: https://oeis.org/A313321 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A313321 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.3.42.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 4, 9, 16, 18, ...
Formula section:
Conjectures from Chai Wah Wu, Apr 16 2025: (Start)
a(n) = 2*a(n-4) - a(n-8) for n > 9.
G.f.: (-2*x^9 + 3*x^8 + 2*x^7 + 13*x^6 + 16*x^5 + 16*x^4 + 16*x^3 + 9*x^2 + 4*x + 1)/(x^8 - 2*x^4 +
1). (End)

Formalization notes:
* The tiling. The entry names tiling 42 of Galebach's list of the 61 3-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/03/3/eu 4h 5a 6a 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.6.3.6, 3.3.3.3.6,
  3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and
  computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file, from
  the base vertex below, and in 1 file of other tilings; and this is the only 3-uniform file that
  holds the listed terms of every entry Gal.3.42.v. The listed terms are proved as controls in the
  proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 13) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 1) is a vertex of type 3.6.3.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a313321

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 13 × Fin 13 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, 0, 0),
    (0, 6, (-1), 0),
    (0, 11, 0, 0),
    (0, 12, (-1), 0),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 6, (-1), 1),
    (1, 7, 0, 0),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 7, 0, 0),
    (2, 8, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 8, 0, 0),
    (3, 9, 0, 0),
    (3, 12, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 1),
    (4, 9, 0, 0),
    (4, 10, 0, 1),
    (5, 0, 0, 0),
    (5, 4, 0, (-1)),
    (5, 10, 0, 0),
    (5, 11, 0, 0),
    (6, 0, 1, 0),
    (6, 1, 1, (-1)),
    (6, 8, 0, 0),
    (6, 10, 0, 0),
    (6, 12, 0, 0),
    (7, 1, 0, 0),
    (7, 2, 0, 0),
    (7, 9, (-1), 0),
    (7, 11, 0, 0),
    (8, 2, 0, 0),
    (8, 3, 0, 0),
    (8, 6, 0, 0),
    (8, 10, 0, 0),
    (8, 12, 0, 0),
    (9, 3, 0, 0),
    (9, 4, 0, 0),
    (9, 7, 1, 0),
    (9, 11, 1, 0),
    (9, 12, 0, 0),
    (10, 4, 0, (-1)),
    (10, 5, 0, 0),
    (10, 6, 0, 0),
    (10, 8, 0, 0),
    (11, 0, 0, 0),
    (11, 5, 0, 0),
    (11, 7, 0, 0),
    (11, 9, (-1), 0),
    (11, 12, (-1), 0),
    (12, 0, 1, 0),
    (12, 3, 0, 0),
    (12, 6, 0, 0),
    (12, 8, 0, 0),
    (12, 9, 0, 0),
    (12, 11, 1, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 13) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 13) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 13 := (0, 0, 1)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 13 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 9. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 8 - 2 * X ^ 4 + 1) =
      -2 * X ^ 9 + 3 * X ^ 8 + 2 * X ^ 7 + 13 * X ^ 6 + 16 * X ^ 5 + 16 * X ^ 4 + 16 * X ^ 3 + 9 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 2 * a (n - 4) - a (n - 8) := by
  sorry

end OMA.S_oeis_a313321
