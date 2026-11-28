import Mathlib

/-!
# OEIS A311888: Wu's conjectures for the coordination sequence Gal.4.45.2

Source: https://oeis.org/A311888 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311888 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.45.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 13, 17, ...
Formula section:
Conjectures from Chai Wah Wu, Jun 12 2026: (Start)
a(n) = 2*a(n-1) - 3*a(n-2) + 4*a(n-3) - 5*a(n-4) + 6*a(n-5) - 7*a(n-6) + 8*a(n-7) - 7*a(n-8) +
6*a(n-9) - 5*a(n-10) + 4*a(n-11) - 3*a(n-12) + 2*a(n-13) - a(n-14) for n > 18.
G.f.: (-x^18 + 2*x^17 - 3*x^16 + 3*x^15 - x^14 + 2*x^13 + 6*x^12 + x^11 + 8*x^10 + 6*x^9 + 8*x^8 +
9*x^7 + 7*x^6 + 8*x^5 + 4*x^4 + 5*x^3 + 3*x^2 + 2*x + 1)/((x - 1)^2*(x^2 + 1)^2*(x^4 + 1)^2). (End)

Formalization notes:
* The tiling. The entry names tiling 45 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 4h 4k2 4u 4.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.6.3.6,
  3.4.4.6, 4.4.4.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings
  and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file
  only, from the base vertex below; and this is the only 4-uniform file that holds the listed terms
  of every entry Gal.4.45.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 14) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 0) is a vertex of type 3.4.4.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311888

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 14 × Fin 14 × ℤ × ℤ) :=
  [(0, 1, (-1), 0),
    (0, 4, (-1), 0),
    (0, 4, 0, 0),
    (0, 8, 0, (-1)),
    (1, 0, 1, 0),
    (1, 2, 1, 0),
    (1, 3, 0, 0),
    (1, 4, 0, 0),
    (2, 1, (-1), 0),
    (2, 3, (-1), 0),
    (2, 3, 0, 0),
    (2, 5, 0, 0),
    (3, 1, 0, 0),
    (3, 2, 0, 0),
    (3, 2, 1, 0),
    (3, 6, 0, 0),
    (4, 0, 0, 0),
    (4, 0, 1, 0),
    (4, 1, 0, 0),
    (4, 7, 0, (-1)),
    (5, 2, 0, 0),
    (5, 6, (-1), 0),
    (5, 6, 0, 0),
    (5, 9, 0, 0),
    (6, 3, 0, 0),
    (6, 5, 0, 0),
    (6, 5, 1, 0),
    (6, 9, 0, 0),
    (7, 4, 0, 1),
    (7, 8, 0, 0),
    (7, 8, 1, 0),
    (7, 10, 0, 0),
    (8, 0, 0, 1),
    (8, 7, (-1), 0),
    (8, 7, 0, 0),
    (8, 11, 0, 0),
    (9, 5, 0, 0),
    (9, 6, 0, 0),
    (9, 12, 0, 0),
    (9, 13, 0, 0),
    (10, 7, 0, 0),
    (10, 11, 0, 0),
    (10, 11, 1, 0),
    (10, 13, 0, 0),
    (11, 8, 0, 0),
    (11, 10, (-1), 0),
    (11, 10, 0, 0),
    (11, 12, 0, 0),
    (12, 9, 0, 0),
    (12, 11, 0, 0),
    (12, 13, (-1), 0),
    (12, 13, 0, 0),
    (13, 9, 0, 0),
    (13, 10, 0, 0),
    (13, 12, 0, 0),
    (13, 12, 1, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 14) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 14) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 14 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 14 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 18. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) ^ 2 * (X ^ 4 + 1) ^ 2) =
      -X ^ 18 + 2 * X ^ 17 - 3 * X ^ 16 + 3 * X ^ 15 - X ^ 14 + 2 * X ^ 13 + 6 * X ^ 12 + X ^ 11 + 8 * X ^ 10 + 6 * X ^ 9 + 8 * X ^ 8 + 9 * X ^ 7 + 7 * X ^ 6 + 8 * X ^ 5 + 4 * X ^ 4 + 5 * X ^ 3 + 3 * X ^ 2 + 2 * X + 1 ∧
    ∀ n : ℕ, 18 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 7 * a (n - 6) + 8 * a (n - 7) - 7 * a (n - 8) + 6 * a (n - 9) - 5 * a (n - 10) + 4 * a (n - 11) - 3 * a (n - 12) + 2 * a (n - 13) - a (n - 14) := by
  sorry

end OMA.S_oeis_a311888
