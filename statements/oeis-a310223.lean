import Mathlib

/-!
# OEIS A310223: Wu's conjectures for the coordination sequence Gal.6.12.3

Source: https://oeis.org/A310223 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A310223 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.12.3 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 3, 7, 12, 15, ...
Formula section:
Conjectures from Chai Wah Wu, Apr 18 2024: (Start)
a(n) = a(n-1) - a(n-2) + a(n-3) - a(n-4) + 2*a(n-5) - 2*a(n-6) + 2*a(n-7) - 2*a(n-8) + 2*a(n-9) -
a(n-10) + a(n-11) - a(n-12) + a(n-13) - a(n-14) for n > 14.
G.f.: (x^14 + 2*x^13 + 5*x^12 + 7*x^11 + 8*x^10 + 9*x^9 + 9*x^8 + 12*x^7 + 9*x^6 + 9*x^5 + 8*x^4 +
7*x^3 + 5*x^2 + 2*x + 1)/((x - 1)^2*(x^4 - x^3 + x^2 - x + 1)*(x^4 + x^3 + x^2 + x + 1)^2). (End)

Formalization notes:
* The tiling. The entry names tiling 12 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/4 (3111)/eu 3f3 4d 5a 6h 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 6.6.6, 3.3.6.6,
  3.3.3.3.6, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, this is the only 6-uniform catalog file in
  which every entry Gal.6.12.w of this tiling occurs (6 entries), and the entry's 50 listed terms
  are those of the base vertex below (no other catalog file has them). The listed terms are proved
  as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 12) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 2) is a vertex of type 6.6.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a310223

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 12 × Fin 12 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 3, (-1), 0),
    (0, 3, 0, 0),
    (1, 0, 0, 1),
    (1, 2, (-1), 0),
    (1, 2, 0, 0),
    (2, 1, 0, 0),
    (2, 1, 1, 0),
    (2, 4, 0, 0),
    (3, 0, 0, 0),
    (3, 0, 1, 0),
    (3, 6, 0, 0),
    (4, 2, 0, 0),
    (4, 5, 0, 0),
    (4, 5, 1, 0),
    (4, 8, 0, 0),
    (5, 4, (-1), 0),
    (5, 4, 0, 0),
    (5, 8, (-1), 0),
    (5, 8, 0, 0),
    (5, 11, 0, 0),
    (6, 3, 0, 0),
    (6, 7, 0, 0),
    (6, 7, 1, 0),
    (7, 6, (-1), 0),
    (7, 6, 0, 0),
    (7, 9, 0, 0),
    (8, 4, 0, 0),
    (8, 5, 0, 0),
    (8, 5, 1, 0),
    (8, 10, 0, 0),
    (8, 11, 0, 0),
    (8, 11, 1, 0),
    (9, 7, 0, 0),
    (9, 10, (-1), 0),
    (9, 10, 0, 0),
    (9, 11, 0, 0),
    (10, 8, 0, 0),
    (10, 9, 0, 0),
    (10, 9, 1, 0),
    (10, 11, 0, 0),
    (10, 11, 1, 0),
    (11, 5, 0, 0),
    (11, 8, (-1), 0),
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
def v0 : ℤ × ℤ × Fin 12 := (0, 0, 2)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 12 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 14. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      X ^ 14 + 2 * X ^ 13 + 5 * X ^ 12 + 7 * X ^ 11 + 8 * X ^ 10 + 9 * X ^ 9 + 9 * X ^ 8 + 12 * X ^ 7 + 9 * X ^ 6 + 9 * X ^ 5 + 8 * X ^ 4 + 7 * X ^ 3 + 5 * X ^ 2 + 2 * X + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) - a (n - 4) + 2 * a (n - 5) - 2 * a (n - 6) + 2 * a (n - 7) - 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) + a (n - 11) - a (n - 12) + a (n - 13) - a (n - 14) := by
  sorry

end OMA.S_oeis_a310223
