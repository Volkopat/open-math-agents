import Mathlib

/-!
# OEIS A316068: Wu's conjectures for the coordination sequence Gal.5.296.4

Source: https://oeis.org/A316068 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A316068 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.5.296.4 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 6, 9, 17, 20, ...
Formula section:
Conjectures from Chai Wah Wu, Nov 18 2025: (Start)
a(n) = - 2*a(n-2) + a(n-3) - 3*a(n-4) + 3*a(n-5) - 3*a(n-6) + 5*a(n-7) - 4*a(n-8) + 6*a(n-9) -
4*a(n-10) + 6*a(n-11) - 4*a(n-12) + 5*a(n-13) - 3*a(n-14) + 3*a(n-15) - 3*a(n-16) + a(n-17) -
2*a(n-18) - a(n-20) for n > 20.
G.f.: (x^20 + 6*x^19 + 11*x^18 + 28*x^17 + 35*x^16 + 64*x^15 + 67*x^14 + 102*x^13 + 91*x^12 +
126*x^11 + 100*x^10 + 126*x^9 + 91*x^8 + 102*x^7 + 67*x^6 + 64*x^5 + 35*x^4 + 28*x^3 + 11*x^2 + 6*x
+ 1)/((x - 1)^2*(x^2 - x + 1)*(x^2 + x + 1)^2*(x^4 - x^3 + x^2 - x + 1)*(x^4 + x^3 + x^2 + x +
1)^2). (End)

Formalization notes:
* The tiling. The entry names tiling 296 of Galebach's list of the 332 5-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/05/3 (221)/eu 5a 5b 5c 5d 6i 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.3.3.6,
  3.3.3.3.6, 3.3.3.4.4, 3.3.3.4.4, 3.3.3.3.3.3. Identification: unfolding the catalog files of all
  1217 3- to 6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed
  terms occur in this file only, from the base vertex below; and this is the only 5-uniform file
  that holds the listed terms of every entry Gal.5.296.v. The listed terms are proved as controls in
  the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 14) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 6) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a316068

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 14 × Fin 14 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, (-1), 0),
    (0, 6, 0, 0),
    (0, 9, (-1), 0),
    (0, 10, 0, 0),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 4, 0, 0),
    (1, 6, 0, 1),
    (1, 7, 0, 0),
    (2, 1, 0, 0),
    (2, 3, (-1), 0),
    (2, 7, 0, 0),
    (2, 8, (-1), 0),
    (2, 11, 0, 0),
    (3, 2, 1, 0),
    (3, 4, 0, 0),
    (3, 7, 0, 0),
    (3, 8, 0, 0),
    (3, 12, 0, 0),
    (4, 1, 0, 0),
    (4, 3, 0, 0),
    (4, 5, 0, 1),
    (4, 6, 0, 1),
    (4, 7, 0, 0),
    (5, 0, 1, 0),
    (5, 4, 0, (-1)),
    (5, 6, 0, 0),
    (5, 9, 0, 0),
    (5, 13, 0, 0),
    (6, 0, 0, 0),
    (6, 1, 0, (-1)),
    (6, 4, 0, (-1)),
    (6, 5, 0, 0),
    (6, 10, 0, 0),
    (6, 13, 0, 0),
    (7, 1, 0, 0),
    (7, 2, 0, 0),
    (7, 3, 0, 0),
    (7, 4, 0, 0),
    (7, 11, 0, 0),
    (7, 12, 0, 0),
    (8, 2, 1, 0),
    (8, 3, 0, 0),
    (8, 9, 0, 0),
    (8, 11, 1, 0),
    (8, 12, 0, 0),
    (9, 0, 1, 0),
    (9, 5, 0, 0),
    (9, 8, 0, 0),
    (9, 10, 1, 0),
    (9, 13, 0, 0),
    (10, 0, 0, 0),
    (10, 6, 0, 0),
    (10, 9, (-1), 0),
    (10, 11, 0, 0),
    (10, 13, 0, 0),
    (11, 2, 0, 0),
    (11, 7, 0, 0),
    (11, 8, (-1), 0),
    (11, 10, 0, 0),
    (11, 12, 0, 0),
    (12, 3, 0, 0),
    (12, 7, 0, 0),
    (12, 8, 0, 0),
    (12, 11, 0, 0),
    (12, 13, 0, 0),
    (13, 5, 0, 0),
    (13, 6, 0, 0),
    (13, 9, 0, 0),
    (13, 10, 0, 0),
    (13, 12, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 14) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 14) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 14 := (0, 0, 6)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 14 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 20. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) ^ 2 * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      X ^ 20 + 6 * X ^ 19 + 11 * X ^ 18 + 28 * X ^ 17 + 35 * X ^ 16 + 64 * X ^ 15 + 67 * X ^ 14 + 102 * X ^ 13 + 91 * X ^ 12 + 126 * X ^ 11 + 100 * X ^ 10 + 126 * X ^ 9 + 91 * X ^ 8 + 102 * X ^ 7 + 67 * X ^ 6 + 64 * X ^ 5 + 35 * X ^ 4 + 28 * X ^ 3 + 11 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 20 < n → (a n : ℤ) = -2 * a (n - 2) + a (n - 3) - 3 * a (n - 4) + 3 * a (n - 5) - 3 * a (n - 6) + 5 * a (n - 7) - 4 * a (n - 8) + 6 * a (n - 9) - 4 * a (n - 10) + 6 * a (n - 11) - 4 * a (n - 12) + 5 * a (n - 13) - 3 * a (n - 14) + 3 * a (n - 15) - 3 * a (n - 16) + a (n - 17) - 2 * a (n - 18) - a (n - 20) := by
  sorry

end OMA.S_oeis_a316068
