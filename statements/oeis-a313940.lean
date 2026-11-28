import Mathlib

/-!
# OEIS A313940: Wu's conjectures for the coordination sequence Gal.4.138.2

Source: https://oeis.org/A313940 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A313940 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.4.138.2 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling
number t in the Galebach list of u-uniform tilings. Data: 1, 5, 10, 16, 23, ...
Formula section:
Conjectures from Chai Wah Wu, Apr 19 2024: (Start)
a(n) = a(n-1) - a(n-3) + a(n-4) + a(n-5) - 2*a(n-6) + a(n-7) + a(n-8) - a(n-9) + a(n-11) - a(n-12)
for n > 12.
G.f.: (x + 1)^2*(x^10 + 2*x^9 + 5*x^7 + x^6 + 3*x^5 + x^4 + 5*x^3 + 2*x + 1)/((x - 1)^2*(x^6 + x^3 +
1)*(x^4 + x^3 + x^2 + x + 1)). (End)

Formalization notes:
* The tiling. The entry names tiling 138 of Galebach's list of the 151 4-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/04/3 (211)/eu 5d 5e 6a 6d 1.tes of the tessellation catalog of M. Čtrnáct and E.
  Kopczyński (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.3.4.4,
  3.3.4.3.4, 3.3.3.3.3.3, 3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to
  6-uniform tilings and computing 50 terms from every vertex class, the entry's 50 listed terms
  occur in this file only, from the base vertex below; and this is the only 4-uniform file that
  holds the listed terms of every entry Gal.4.138.v. The listed terms are proved as controls in the
  proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 21) in the cell (x, y) of the tiling's
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

namespace OMA.S_oeis_a313940

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 21 × Fin 21 × ℤ × ℤ) :=
  [(0, 1, 0, 0),
    (0, 3, 0, (-1)),
    (0, 4, (-1), 0),
    (0, 8, 0, (-1)),
    (0, 10, (-1), (-1)),
    (1, 0, 0, 0),
    (1, 2, 0, 0),
    (1, 4, (-1), 0),
    (1, 5, 0, 0),
    (1, 9, (-1), 0),
    (2, 1, 0, 0),
    (2, 3, 0, (-1)),
    (2, 6, 0, 0),
    (2, 7, 0, (-1)),
    (2, 14, 0, 0),
    (3, 0, 0, 1),
    (3, 2, 0, 1),
    (3, 7, 0, 0),
    (3, 8, 0, 0),
    (3, 16, 0, 0),
    (4, 0, 1, 0),
    (4, 1, 1, 0),
    (4, 9, 0, 0),
    (4, 11, 0, 0),
    (4, 17, 0, 0),
    (5, 1, 0, 0),
    (5, 6, 0, 0),
    (5, 9, (-1), 0),
    (5, 13, 0, 0),
    (5, 20, (-1), 0),
    (6, 2, 0, 0),
    (6, 5, 0, 0),
    (6, 12, 0, 0),
    (6, 14, 0, 0),
    (6, 19, 0, 0),
    (7, 2, 0, 1),
    (7, 3, 0, 0),
    (7, 14, 0, 1),
    (7, 15, 0, 0),
    (7, 18, 0, 0),
    (8, 0, 0, 1),
    (8, 3, 0, 0),
    (8, 10, (-1), 0),
    (8, 12, 0, 0),
    (8, 13, 0, 0),
    (8, 16, 0, 0),
    (9, 1, 1, 0),
    (9, 4, 0, 0),
    (9, 5, 1, 0),
    (9, 15, 0, 0),
    (9, 17, 0, 0),
    (9, 20, 0, 0),
    (10, 0, 1, 1),
    (10, 8, 1, 0),
    (10, 11, 0, 1),
    (10, 13, 1, 0),
    (10, 18, 0, 0),
    (11, 4, 0, 0),
    (11, 10, 0, (-1)),
    (11, 14, 0, 0),
    (11, 18, 0, (-1)),
    (11, 19, 0, 0),
    (12, 6, 0, 0),
    (12, 8, 0, 0),
    (12, 13, 0, 0),
    (12, 16, 0, 0),
    (12, 19, 0, 0),
    (13, 5, 0, 0),
    (13, 8, 0, 0),
    (13, 10, (-1), 0),
    (13, 12, 0, 0),
    (13, 20, (-1), 0),
    (14, 2, 0, 0),
    (14, 6, 0, 0),
    (14, 7, 0, (-1)),
    (14, 11, 0, 0),
    (14, 18, 0, (-1)),
    (14, 19, 0, 0),
    (15, 7, 0, 0),
    (15, 9, 0, 0),
    (15, 16, 0, 0),
    (15, 17, 0, 0),
    (15, 20, 0, 0),
    (16, 3, 0, 0),
    (16, 8, 0, 0),
    (16, 12, 0, 0),
    (16, 15, 0, 0),
    (16, 17, 0, 0),
    (17, 4, 0, 0),
    (17, 9, 0, 0),
    (17, 15, 0, 0),
    (17, 16, 0, 0),
    (17, 19, 0, 0),
    (18, 7, 0, 0),
    (18, 10, 0, 0),
    (18, 11, 0, 1),
    (18, 14, 0, 1),
    (18, 20, 0, 0),
    (19, 6, 0, 0),
    (19, 11, 0, 0),
    (19, 12, 0, 0),
    (19, 14, 0, 0),
    (19, 17, 0, 0),
    (20, 5, 1, 0),
    (20, 9, 0, 0),
    (20, 13, 1, 0),
    (20, 15, 0, 0),
    (20, 18, 0, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 21) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 21) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 21 := (0, 0, 0)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 21 | G.dist v0 v = n}

/-- Chai Wah Wu's conjectures: the g.f. and the recurrence for n > 12. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 6 + X ^ 3 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      (X + 1) ^ 2 * (X ^ 10 + 2 * X ^ 9 + 5 * X ^ 7 + X ^ 6 + 3 * X ^ 5 + X ^ 4 + 5 * X ^ 3 + 2 * X + 1) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = a (n - 1) - a (n - 3) + a (n - 4) + a (n - 5) - 2 * a (n - 6) + a (n - 7) + a (n - 8) - a (n - 9) + a (n - 11) - a (n - 12) := by
  sorry

end OMA.S_oeis_a313940
