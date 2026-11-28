import Mathlib

/-!
# OEIS A315907: Mathar's conjectures for the coordination sequence Gal.3.40.3

Source: https://oeis.org/A315907 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A315907 (Brian Galebach and N. J. A. Sloane, Jun 18 2018), offset 0: Coordination sequence
Gal.3.40.3 where Gal.u.t.v denotes the coordination sequence for a vertex of type v in tiling number
t in the Galebach list of u-uniform tilings. Data: 1, 6, 8, 14, 20, ...
Formula section:
Conjectures from R. J. Mathar, May 02 2023: (Start)
G.f.: 1 + 2*x*(3+x+3*x^2) / ( (1+x+x^2)*(x-1)^2 ).
a(n) = a(n-1) + a(n-3) - a(n-4) for n > 4.
a(n) = 2*A047342(n+1) for n > 0. (End)

Formalization notes:
* The tiling. The entry names tiling 40 of Galebach's list of the 61 3-uniform tilings (drawn at
  probabilitysports.com/tilings.html) and defines nothing more. The graph below is the tiling
  k-uniform/03/3/eu 4d 5a 6f 1.tes of the tessellation catalog of M. Čtrnáct and E. Kopczyński
  (github.com/zenorogue/tes-catalog), whose vertex orbits have the types 3.3.6.6, 3.3.3.3.6,
  3.3.3.3.3.3. Identification: unfolding the catalog files of all 1217 3- to 6-uniform tilings and
  computing 50 terms from every vertex class, the entry's 50 listed terms occur in this file only,
  from the base vertex below; and this is the only 3-uniform file that holds the listed terms of
  every entry Gal.3.40.v. The listed terms are proved as controls in the proof file.
* Vertices: (x, y, s) is the vertex of class s (one of 5) in the cell (x, y) of the tiling's
  translation lattice. E lists the edges leaving one cell: (s, s', dx, dy) joins (x, y, s) to (x +
  dx, y + dy, s'), and G is SimpleGraph.fromRel of all their translates.
* v0 = (0, 0, 4) is a vertex of type 3.3.3.3.3.3; its coordination sequence is the entry's.
* a n = Set.ncard {v | G.dist v0 v = n}, the number of vertices at graph distance n from v0. The
  graph is connected (shown in the proof), so SimpleGraph.dist is the length of a shortest path.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A(x) D(x) = N(x) in the formal power series
  ring over the rationals, with N and D the entry's numerator and denominator as written; D has
  constant term 1 or -1, so this is the entry's quotient. Recurrences are stated in the integers.
* main is the conjunction of the conjectures in the entry's block.
* Controls proved in the proof file: a(0..49), all the entry's listed terms.
-/

namespace OMA.S_oeis_a315907

open PowerSeries

/-- The directed edges of one cell of the translation lattice: (s, s', dx, dy) joins the vertex
(x, y, s) of class s in cell (x, y) to (x + dx, y + dy, s'). -/
def E : List (Fin 5 × Fin 5 × ℤ × ℤ) :=
  [(0, 1, (-1), (-1)),
    (0, 1, 0, (-1)),
    (0, 3, 0, 0),
    (0, 4, (-1), 0),
    (0, 4, 0, 0),
    (1, 0, 0, 1),
    (1, 0, 1, 1),
    (1, 2, 0, 0),
    (1, 4, 0, 1),
    (2, 1, 0, 0),
    (2, 3, 0, 0),
    (2, 3, 1, 0),
    (2, 4, 0, 0),
    (3, 0, 0, 0),
    (3, 2, (-1), 0),
    (3, 2, 0, 0),
    (3, 4, (-1), 0),
    (3, 4, 0, 0),
    (4, 0, 0, 0),
    (4, 0, 1, 0),
    (4, 1, 0, (-1)),
    (4, 2, 0, 0),
    (4, 3, 0, 0),
    (4, 3, 1, 0)]

/-- The edge relation of the periodic graph. -/
def R (u v : ℤ × ℤ × Fin 5) : Prop :=
  ∃ e ∈ E, u.2.2 = e.1 ∧ v.2.2 = e.2.1 ∧ v.1 = u.1 + e.2.2.1 ∧ v.2.1 = u.2.1 + e.2.2.2

/-- The graph of the tiling: its vertices and edges. -/
def G : SimpleGraph (ℤ × ℤ × Fin 5) := SimpleGraph.fromRel R

/-- The base vertex. -/
def v0 : ℤ × ℤ × Fin 5 := (0, 0, 4)

/-- The coordination sequence: the number of vertices at graph distance n from v0. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {v : ℤ × ℤ × Fin 5 | G.dist v0 v = n}

/-- Mathar's conjectures: the g.f., the recurrence for n > 4 and a(n) = 2 A047342(n+1) for n > 0 (A047342 lists the numbers congruent to 0, 3 or 4 mod 7, from offset 1). -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X + X ^ 2) * (X - 1) ^ 2) =
      (1 + X + X ^ 2) * (X - 1) ^ 2 + 2 * X * (3 + X + 3 * X ^ 2) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + a (n - 3) - a (n - 4)) ∧
    ∀ n : ℕ, 0 < n → a n = 2 * Nat.nth (fun m => m % 7 = 0 ∨ m % 7 = 3 ∨ m % 7 = 4) n := by
  sorry

end OMA.S_oeis_a315907
