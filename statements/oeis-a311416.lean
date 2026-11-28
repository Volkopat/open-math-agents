import Mathlib

/-!
# OEIS A311416: Wu's and Spezia's conjectures for the coordination sequence Gal.4.48.1

Source: https://oeis.org/A311416 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A311416 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.48.1 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 4, 8, 12, 17, ...
Formula section:
Conjectures from Chai Wah Wu, Mar 05 2024: (Start)
a(n) = 2*a(n-1) - 3*a(n-2) + 4*a(n-3) - 5*a(n-4) + 6*a(n-5) - 7*a(n-6) + 8*a(n-7) - 8*a(n-8) +
8*a(n-9) - 7*a(n-10) + 6*a(n-11) - 5*a(n-12) + 4*a(n-13) - 3*a(n-14) + 2*a(n-15) - a(n-16) for n >
16.
G.f.: (x^16 + 2*x^15 + 3*x^14 + 4*x^13 + 6*x^12 + 5*x^11 + 8*x^10 + 8*x^9 + 10*x^8 + 8*x^7 + 8*x^6 +
5*x^5 + 6*x^4 + 4*x^3 + 3*x^2 + 2*x + 1)/((x - 1)^2*(x^2 + 1)*(x^4 + 1)*(x^4 - x^3 + x^2 - x +
1)*(x^4 + x^3 + x^2 + x + 1)). (End)
Conjecture: a(n) ~ 21*n/5. - Stefano Spezia, Mar 05 2024 after Chai Wah Wu

Formalization notes:
* The tiling. The entry names tiling 48 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 4h 4k2 4u 7.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.6.3.6,
  3.4.4.6, 4.4.4.4. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings
  and computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file
  only, from the base vertex below; and this is the only 4-uniform file that holds the listed terms
  of every entry Gal.4.48.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 14) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 7) is a vertex of type 4.4.4.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* a(n) ~ c n is stated as Asymptotics.IsEquivalent Filter.atTop of a n and c n as functions from the
  naturals to the reals.
* main is the conjunction of every conjecture the entry states: the block's and the one on a line of
  its own.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a311416

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 14 × Fin 14 × ℤ × ℤ) :=
  [(0, 1, (-1), (-1)),
    (0, 4, (-1), 0),
    (0, 4, 0, 0),
    (0, 8, 0, 0),
    (1, 0, 1, 1),
    (1, 2, 1, 0),
    (1, 3, 0, 0),
    (1, 4, 0, 1),
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
    (4, 1, 0, (-1)),
    (4, 7, 0, 0),
    (5, 2, 0, 0),
    (5, 6, (-1), 0),
    (5, 6, 0, 0),
    (5, 10, (-1), 0),
    (6, 3, 0, 0),
    (6, 5, 0, 0),
    (6, 5, 1, 0),
    (6, 10, 0, 0),
    (7, 4, 0, 0),
    (7, 8, 0, 0),
    (7, 8, 1, 0),
    (7, 12, 0, 0),
    (8, 0, 0, 0),
    (8, 7, (-1), 0),
    (8, 7, 0, 0),
    (8, 13, 0, 0),
    (9, 10, 0, 0),
    (9, 11, 0, 0),
    (9, 11, 1, 0),
    (9, 12, 0, 0),
    (10, 5, 1, 0),
    (10, 6, 0, 0),
    (10, 9, 0, 0),
    (10, 11, 1, 0),
    (11, 9, (-1), 0),
    (11, 9, 0, 0),
    (11, 10, (-1), 0),
    (11, 13, 0, 0),
    (12, 7, 0, 0),
    (12, 9, 0, 0),
    (12, 13, 0, 0),
    (12, 13, 1, 0),
    (13, 8, 0, 0),
    (13, 11, 0, 0),
    (13, 12, (-1), 0),
    (13, 12, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 14) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 14) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 14 := (0, 0, 7)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 14 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 16; Stefano Spezia's conjecture a(n) ~ 21 n/5. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 16 + 2 * X ^ 15 + 3 * X ^ 14 + 4 * X ^ 13 + 6 * X ^ 12 + 5 * X ^ 11 + 8 * X ^ 10 + 8 * X ^ 9 + 10 * X ^ 8 + 8 * X ^ 7 + 8 * X ^ 6 + 5 * X ^ 5 + 6 * X ^ 4 + 4 * X ^ 3 + 3 * X ^ 2 + 2 * X + 1 ∧
    (∀ n : ℕ, 16 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 7 * a (n - 6) + 8 * a (n - 7) - 8 * a (n - 8) + 8 * a (n - 9) - 7 * a (n - 10) + 6 * a (n - 11) - 5 * a (n - 12) + 4 * a (n - 13) - 3 * a (n - 14) + 2 * a (n - 15) - a (n - 16)) ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ)) (fun n : ℕ => 21 * (n : ℝ) / 5) := by
  sorry

end OMA.S_oeis_a311416
