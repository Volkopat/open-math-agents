import Mathlib

/-!
# OEIS A313799: Wu's conjectures for the coordination sequence Gal.3.53.3

Source: https://oeis.org/A313799 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A313799 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.3.53.3 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 5, 10, 15, 21, ...
Formula section:
Conjectures from Chai Wah Wu, Jun 12 2025: (Start)
a(n) = 2*a(n-1) - a(n-2) - a(n-3) + 2*a(n-4) - a(n-5) - a(n-6) + 2*a(n-7) - a(n-8) for n > 8.
G.f.: (x + 1)^2*(x^6 + x^5 - 2*x^4 + 4*x^3 - 2*x^2 + x + 1)/((x - 1)^2*(x^6 + x^3 + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 53 of Galebach's list of the 61 3-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/03/2 (21)/eu 5d2 5f 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.3.4.4, 3.3.4.3.4.
  Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and computing 50
  terms from every vertex class, the entry's 50 listed terms occur in this file, from the base
  vertex below, and in 5 files of other tilings; and this is the only 3-uniform file that holds the
  listed terms of every entry Gal.3.53.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 12) in the cell (x, y) of the tiling's
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

namespace OMA.S_oeis_a313799

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 12 × Fin 12 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 2, (-1), (-1)),
    (0, 3, (-1), 0),
    (0, 3, 0, 0),
    (0, 6, 0, 0),
    (1, 0, 0, 1),
    (1, 2, (-1), 0),
    (1, 2, 0, 0),
    (1, 4, 0, 0),
    (1, 5, (-1), 0),
    (2, 0, 1, 1),
    (2, 1, 0, 0),
    (2, 1, 1, 0),
    (2, 3, 0, 1),
    (2, 5, 0, 0),
    (3, 0, 0, 0),
    (3, 0, 1, 0),
    (3, 2, 0, (-1)),
    (3, 6, 0, 0),
    (3, 9, 0, 0),
    (4, 1, 0, 0),
    (4, 5, (-1), 0),
    (4, 5, 0, 0),
    (4, 7, (-1), 0),
    (4, 8, 0, 0),
    (5, 1, 1, 0),
    (5, 2, 0, 0),
    (5, 4, 0, 0),
    (5, 4, 1, 0),
    (5, 7, 0, 0),
    (6, 0, 0, 0),
    (6, 3, 0, 0),
    (6, 9, (-1), 0),
    (6, 9, 0, 0),
    (6, 11, 0, 0),
    (7, 4, 1, 0),
    (7, 5, 0, 0),
    (7, 8, 0, 0),
    (7, 8, 1, 0),
    (7, 10, 0, 0),
    (8, 4, 0, 0),
    (8, 7, (-1), 0),
    (8, 7, 0, 0),
    (8, 10, 0, 0),
    (8, 11, 0, 0),
    (9, 3, 0, 0),
    (9, 6, 0, 0),
    (9, 6, 1, 0),
    (9, 10, 0, 0),
    (9, 11, 0, 0),
    (10, 7, 0, 0),
    (10, 8, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 0, 0),
    (10, 11, 1, 0),
    (11, 6, 0, 0),
    (11, 8, 0, 0),
    (11, 9, 0, 0),
    (11, 10, (-1), 0),
    (11, 10, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 12) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 12) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 12 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 12 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 8. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 6 + X ^ 3 + 1)) =
      (X + 1) ^ 2 * (X ^ 6 + X ^ 5 - 2 * X ^ 4 + 4 * X ^ 3 - 2 * X ^ 2 + X + 1) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) - a (n - 3) + 2 * a (n - 4) - a (n - 5) - a (n - 6) + 2 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a313799
