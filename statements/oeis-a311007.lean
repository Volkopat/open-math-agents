import Mathlib

/-!
# OEIS A311007: Wu's conjectures for the coordination sequence Gal.4.19.3

Source: https://oeis.org/A311007 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311007 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.19.3 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 10, 16, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 24 2019: (Start)
a(n) = a(n-1) - a(n-2) + a(n-3) + a(n-5) - a(n-6) + a(n-7) - a(n-8) for n > 11.
G.f.: (-2*x^11 + x^8 + 7*x^7 + 5*x^6 + 7*x^5 + 10*x^4 + 5*x^3 + 5*x^2 + 3*x + 1)/((x - 1)^2*(x^2 +
1)*(x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 19 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 3f 4d 4e 6f 2.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 6.6.6, 3.3.6.6,
  3.3.6.6, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this
  file only, from the base vertex below; and this is the only 4-uniform file that holds the listed
  terms of every entry Gal.4.19.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 9) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 3) is a vertex of type 3.3.6.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311007

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 9 × Fin 9 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 5, (-1), (-1)),
    (0, 6, (-1), 0),
    (1, 0, 0, 0),
    (1, 2, 0, (-1)),
    (1, 7, 0, 0),
    (2, 1, 0, 1),
    (2, 3, 0, 0),
    (2, 5, 0, 0),
    (2, 8, 0, 0),
    (3, 2, 0, 0),
    (3, 4, 0, 0),
    (3, 7, 0, 0),
    (3, 8, 0, 0),
    (4, 3, 0, 0),
    (4, 5, (-1), 0),
    (4, 6, (-1), 0),
    (4, 8, (-1), 0),
    (5, 0, 1, 1),
    (5, 2, 0, 0),
    (5, 4, 1, 0),
    (5, 8, 0, 0),
    (6, 0, 1, 0),
    (6, 4, 1, 0),
    (6, 7, 0, 0),
    (6, 8, 0, 0),
    (7, 1, 0, 0),
    (7, 3, 0, 0),
    (7, 6, 0, 0),
    (7, 8, 0, 0),
    (8, 2, 0, 0),
    (8, 3, 0, 0),
    (8, 4, 1, 0),
    (8, 5, 0, 0),
    (8, 6, 0, 0),
    (8, 7, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 9) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 9) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 9 := (0, 0, 3)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 9 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 11. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      -2 * X ^ 11 + X ^ 8 + 7 * X ^ 7 + 5 * X ^ 6 + 7 * X ^ 5 + 10 * X ^ 4 + 5 * X ^ 3 + 5 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 5) - a (n - 6) + a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a311007
