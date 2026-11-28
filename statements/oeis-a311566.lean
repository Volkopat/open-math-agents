import Mathlib

/-!
# OEIS A311566: Wu's conjectures for the coordination sequence Gal.4.93.3

Source: https://oeis.org/A311566 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311566 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.93.3 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 12, 18, ...
Formula section:
Conjectures from Chai Wah Wu, Apr 15 2025: (Start)
a(n) = - 2*a(n-1) - 3*a(n-2) - 3*a(n-3) - 3*a(n-4) - a(n-5) + a(n-6) + 4*a(n-7) + 5*a(n-8) +
6*a(n-9) + 5*a(n-10) + 4*a(n-11) + a(n-12) - a(n-13) - 3*a(n-14) - 3*a(n-15) - 3*a(n-16) - 2*a(n-17)
- a(n-18) for n > 18.
G.f.: (x + 1)*(x^17 + 5*x^16 + 14*x^15 + 30*x^14 + 52*x^13 + 79*x^12 + 106*x^11 + 129*x^10 + 141*x^9
+ 141*x^8 + 128*x^7 + 106*x^6 + 78*x^5 + 52*x^4 + 29*x^3 + 14*x^2 + 5*x + 1)/((x - 1)^2*(x^2 + x +
1)*(x^4 + x^3 + x^2 + x + 1)^2*(x^6 + x^5 + x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 93 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 4f 4k 4l 4m 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.6.3.6,
  3.4.4.6, 3.4.6.4, 3.4.6.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this
  file only, from the base vertex below; and this is the only 4-uniform file that holds the listed
  terms of every entry Gal.4.93.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 11) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 3) is a vertex of type 3.4.6.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311566

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 11 × Fin 11 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 2, (-1), 0),
    (0, 5, (-1), (-1)),
    (0, 6, 0, 0),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 6, 0, 0),
    (1, 7, 0, 0),
    (2, 0, 1, 0),
    (2, 1, 0, 0),
    (2, 3, 0, (-1)),
    (2, 7, 0, 0),
    (3, 2, 0, 1),
    (3, 4, 0, 0),
    (3, 5, 0, 0),
    (3, 8, 0, 0),
    (4, 3, 0, 0),
    (4, 5, (-1), 0),
    (4, 9, 0, 0),
    (4, 10, (-1), 0),
    (5, 0, 1, 1),
    (5, 3, 0, 0),
    (5, 4, 1, 0),
    (5, 8, 0, 0),
    (6, 0, 0, 0),
    (6, 1, 0, 0),
    (6, 7, (-1), 0),
    (6, 9, 0, 0),
    (7, 1, 0, 0),
    (7, 2, 0, 0),
    (7, 6, 1, 0),
    (7, 10, 0, 0),
    (8, 3, 0, 0),
    (8, 5, 0, 0),
    (8, 9, 0, 0),
    (8, 10, 0, 0),
    (9, 4, 0, 0),
    (9, 6, 0, 0),
    (9, 8, 0, 0),
    (9, 10, (-1), 0),
    (10, 4, 1, 0),
    (10, 7, 0, 0),
    (10, 8, 0, 0),
    (10, 9, 1, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 11) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 11) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 11 := (0, 0, 3)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 11 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 18. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2 * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      (X + 1) * (X ^ 17 + 5 * X ^ 16 + 14 * X ^ 15 + 30 * X ^ 14 + 52 * X ^ 13 + 79 * X ^ 12 + 106 * X ^ 11 + 129 * X ^ 10 + 141 * X ^ 9 + 141 * X ^ 8 + 128 * X ^ 7 + 106 * X ^ 6 + 78 * X ^ 5 + 52 * X ^ 4 + 29 * X ^ 3 + 14 * X ^ 2 + 5 * X + 1) ∧
    ∀ n : ℕ, 18 < n → (a n : ℤ) = -2 * a (n - 1) - 3 * a (n - 2) - 3 * a (n - 3) - 3 * a (n - 4) - a (n - 5) + a (n - 6) + 4 * a (n - 7) + 5 * a (n - 8) + 6 * a (n - 9) + 5 * a (n - 10) + 4 * a (n - 11) + a (n - 12) - a (n - 13) - 3 * a (n - 14) - 3 * a (n - 15) - 3 * a (n - 16) - 2 * a (n - 17) - a (n - 18) := by
  sorry

end OMA.S_oeis_a311566
