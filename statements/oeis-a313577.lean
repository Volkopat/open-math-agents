import Mathlib

/-!
# OEIS A313577: Wu's conjectures for the coordination sequence Gal.4.97.3

Source: https://oeis.org/A313577 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A313577 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.97.3 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 5, 10, 14, 19, ...
Formula section:
Conjectures from Chai Wah Wu, Apr 16 2024: (Start)
a(n) = - a(n-1) - a(n-2) - a(n-3) - a(n-4) + a(n-5) + a(n-6) + a(n-7) + a(n-8) + 2*a(n-9) + a(n-10)
+ a(n-11) + a(n-12) + a(n-13) - a(n-14) - a(n-15) - a(n-16) - a(n-17) - a(n-18) for n > 18.
G.f.: (x + 1)^2*(x^16 + 4*x^15 + 7*x^14 + 12*x^13 + 18*x^12 + 24*x^11 + 25*x^10 + 32*x^9 + 28*x^8 +
32*x^7 + 25*x^6 + 24*x^5 + 18*x^4 + 12*x^3 + 7*x^2 + 4*x + 1)/((x - 1)^2*(x^2 + x + 1)*(x^6 + x^3 +
1)*(x^4 + x^3 + x^2 + x + 1)^2). (End)

Formalization notes:
* The tiling. The entry names tiling 97 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 4k 5a 5e 5f 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.4.4.6,
  3.3.3.3.6, 3.3.4.3.4, 3.3.4.3.4. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed terms
  occur in this file only, from the base vertex below; and this is the only 4-uniform file that
  holds the listed terms of every entry Gal.4.97.v. The listed terms are proved as controls in the
  proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 12) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 6) is a vertex of type 3.3.4.3.4; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a313577

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 12 × Fin 12 × ℤ × ℤ) :=
  [(0, 1, 0, (-1)),
    (0, 5, (-1), (-1)),
    (0, 6, 0, 0),
    (0, 9, (-1), 0),
    (0, 10, (-1), 0),
    (1, 0, 0, 1),
    (1, 2, 0, 0),
    (1, 5, 0, 0),
    (1, 6, 0, 1),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 4, 0, 0),
    (2, 7, 0, 0),
    (3, 2, 0, 0),
    (3, 4, (-1), 0),
    (3, 7, 0, 0),
    (3, 8, (-1), 0),
    (3, 11, 0, 0),
    (4, 2, 0, 0),
    (4, 3, 1, 0),
    (4, 5, 0, 0),
    (4, 8, 0, 0),
    (5, 0, 1, 1),
    (5, 1, 0, 0),
    (5, 4, 0, 0),
    (5, 9, 0, 1),
    (6, 0, 0, 0),
    (6, 1, 0, (-1)),
    (6, 9, 0, 0),
    (6, 10, (-1), 0),
    (6, 11, 0, 0),
    (7, 2, 0, 0),
    (7, 3, 0, 0),
    (7, 8, 0, 0),
    (7, 10, 0, 0),
    (7, 11, 0, 0),
    (8, 3, 1, 0),
    (8, 4, 0, 0),
    (8, 7, 0, 0),
    (8, 10, 0, 0),
    (8, 11, 1, 0),
    (9, 0, 1, 0),
    (9, 5, 0, (-1)),
    (9, 6, 0, 0),
    (9, 10, 0, 0),
    (9, 11, 0, 0),
    (10, 0, 1, 0),
    (10, 6, 1, 0),
    (10, 7, 0, 0),
    (10, 8, 0, 0),
    (10, 9, 0, 0),
    (11, 3, 0, 0),
    (11, 6, 0, 0),
    (11, 7, 0, 0),
    (11, 8, (-1), 0),
    (11, 9, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 12) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 12) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 12 := (0, 0, 6)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 12 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 18. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 6 + X ^ 3 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      (X + 1) ^ 2 * (X ^ 16 + 4 * X ^ 15 + 7 * X ^ 14 + 12 * X ^ 13 + 18 * X ^ 12 + 24 * X ^ 11 + 25 * X ^ 10 + 32 * X ^ 9 + 28 * X ^ 8 + 32 * X ^ 7 + 25 * X ^ 6 + 24 * X ^ 5 + 18 * X ^ 4 + 12 * X ^ 3 + 7 * X ^ 2 + 4 * X + 1) ∧
    ∀ n : ℕ, 18 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) - a (n - 3) - a (n - 4) + a (n - 5) + a (n - 6) + a (n - 7) + a (n - 8) + 2 * a (n - 9) + a (n - 10) + a (n - 11) + a (n - 12) + a (n - 13) - a (n - 14) - a (n - 15) - a (n - 16) - a (n - 17) - a (n - 18) := by
  sorry

end OMA.S_oeis_a313577
