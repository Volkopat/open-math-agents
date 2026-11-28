import Mathlib

/-!
# OEIS A311714: Wu's conjectures for the coordination sequence Gal.6.435.5

Source: https://oeis.org/A311714 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311714 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.6.435.5 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 13, 16, ...
Formula section:
Conjectures from Chai Wah Wu, Dec 29 2021: (Start)
a(n) = 2*a(n-1) - 3*a(n-2) + 4*a(n-3) - 5*a(n-4) + 6*a(n-5) - 7*a(n-6) + 8*a(n-7) - 9*a(n-8) +
10*a(n-9) - 10*a(n-10) + 10*a(n-11) - 10*a(n-12) + 10*a(n-13) - 9*a(n-14) + 8*a(n-15) - 7*a(n-16) +
6*a(n-17) - 5*a(n-18) + 4*a(n-19) - 3*a(n-20) + 2*a(n-21) - a(n-22) for n > 22.
G.f.: (x^22 + 2*x^21 + 3*x^20 + 5*x^19 + 3*x^18 + 10*x^17 + 3*x^16 + 13*x^15 + 4*x^14 + 16*x^13 +
4*x^12 + 16*x^11 + 4*x^10 + 16*x^9 + 4*x^8 + 13*x^7 + 3*x^6 + 10*x^5 + 3*x^4 + 5*x^3 + 3*x^2 + 2*x +
1)/((x - 1)^2*(x^4 - x^3 + x^2 - x + 1)*(x^4 + x^3 + x^2 + x + 1)*(x^6 - x^5 + x^4 - x^3 + x^2 - x +
1)*(x^6 + x^5 + x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 435 of Galebach's list of the 673 6-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/06/3 (321)/eu 4e 4f2 4h 4k2 2.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6,
  3.6.3.6, 3.6.3.6, 3.4.4.6. Identification: unfolding the catalog files of all 1217 3- to 6-uniform
  tilings and computing 50 terms from every vertex class, this is the only 6-uniform catalog file in
  which every entry Gal.6.435.w of this tiling occurs (6 entries), and the entry's 50 listed terms
  are those of the base vertex below (no other catalog file has them). The listed terms are proved
  as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 16) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 1) is a vertex of type 3.3.6.6; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311714

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 16 × Fin 16 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 2, (-1), 0),
    (0, 3, (-1), (-1)),
    (0, 4, 0, (-1)),
    (1, 0, 0, 0),
    (1, 2, (-1), 0),
    (1, 2, 0, 0),
    (1, 5, 0, 0),
    (2, 0, 1, 0),
    (2, 1, 0, 0),
    (2, 1, 1, 0),
    (2, 5, 1, 0),
    (3, 0, 1, 1),
    (3, 4, 0, 0),
    (3, 4, 1, 0),
    (3, 8, 0, 0),
    (4, 0, 0, 1),
    (4, 3, (-1), 0),
    (4, 3, 0, 0),
    (4, 9, 0, 0),
    (5, 1, 0, 0),
    (5, 2, (-1), 0),
    (5, 6, 0, 0),
    (5, 7, (-1), 0),
    (6, 5, 0, 0),
    (6, 7, (-1), 0),
    (6, 7, 0, 0),
    (6, 10, 0, 0),
    (7, 5, 1, 0),
    (7, 6, 0, 0),
    (7, 6, 1, 0),
    (7, 10, 1, 0),
    (8, 3, 0, 0),
    (8, 9, 0, 0),
    (8, 9, 1, 0),
    (8, 13, 1, 0),
    (9, 4, 0, 0),
    (9, 8, (-1), 0),
    (9, 8, 0, 0),
    (9, 13, 0, 0),
    (10, 6, 0, 0),
    (10, 7, (-1), 0),
    (10, 11, 0, 0),
    (10, 12, (-1), 0),
    (11, 10, 0, 0),
    (11, 12, (-1), 0),
    (11, 12, 0, 0),
    (11, 15, 0, 0),
    (12, 10, 1, 0),
    (12, 11, 0, 0),
    (12, 11, 1, 0),
    (12, 14, 0, 0),
    (13, 8, (-1), 0),
    (13, 9, 0, 0),
    (13, 14, (-1), 0),
    (13, 15, 0, 0),
    (14, 12, 0, 0),
    (14, 13, 1, 0),
    (14, 15, 0, 0),
    (14, 15, 1, 0),
    (15, 11, 0, 0),
    (15, 13, 0, 0),
    (15, 14, (-1), 0),
    (15, 14, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 16) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 16) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 16 := (0, 0, 1)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 16 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 22. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 22 + 2 * X ^ 21 + 3 * X ^ 20 + 5 * X ^ 19 + 3 * X ^ 18 + 10 * X ^ 17 + 3 * X ^ 16 + 13 * X ^ 15 + 4 * X ^ 14 + 16 * X ^ 13 + 4 * X ^ 12 + 16 * X ^ 11 + 4 * X ^ 10 + 16 * X ^ 9 + 4 * X ^ 8 + 13 * X ^ 7 + 3 * X ^ 6 + 10 * X ^ 5 + 3 * X ^ 4 + 5 * X ^ 3 + 3 * X ^ 2 + 2 * X + 1 ∧
    ∀ n : ℕ, 22 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 7 * a (n - 6) + 8 * a (n - 7) - 9 * a (n - 8) + 10 * a (n - 9) - 10 * a (n - 10) + 10 * a (n - 11) - 10 * a (n - 12) + 10 * a (n - 13) - 9 * a (n - 14) + 8 * a (n - 15) - 7 * a (n - 16) + 6 * a (n - 17) - 5 * a (n - 18) + 4 * a (n - 19) - 3 * a (n - 20) + 2 * a (n - 21) - a (n - 22) := by
  sorry

end OMA.S_oeis_a311714
