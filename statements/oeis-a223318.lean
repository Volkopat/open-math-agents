import Mathlib

/-!
# OEIS A223318: Barker's g.f. and closed form for rolling icosahedron footprints, n X 5

Source: https://oeis.org/A223318 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A223318 (R. H. Hardin, Mar 19 2013), offset 1: Rolling icosahedron footprints: number of n X 5
0..11 arrays starting with 0 where 0..11 label vertices of an icosahedron and every array movement
to a horizontal or antidiagonal neighbor moves along an icosahedral edge. Column 5 of A223321.
Formula section:
Empirical: a(n) = 479*a(n-1) - 15210*a(n-2).
Conjectures from Colin Barker, Aug 19 2018: (Start)
G.f.: 125*x*(5 - 198*x) / (1 - 479*x + 15210*x^2).
a(n) = (25*2^(-1-n)*((479-sqrt(168601))^n*(-3181+11*sqrt(168601)) + (479+sqrt(168601))^n*(3181+11*sqrt(168601)))) / (169*sqrt(168601)).
(End)

Formalization notes:
* The labels 0..11 are the vertices of the icosahedron, with the adjacency given by the entry's own
  table (Vertex neighbors, in the example section), copied into `nbrs`; a movement along an
  icosahedral edge joins a label to one of its listed neighbors. The table is symmetric, loop free
  and 5-regular, as the proof file checks.
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2), x(i,3), x(i,4)). The neighbor pairs
  that must move along an icosahedral edge are the horizontal pairs (x(i,j), x(i,j+1)) and the
  antidiagonal pairs (x(i,j+1), x(i+1,j)); vertical and diagonal neighbors are not constrained.
  Starting at 0 means x(0,0) = 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x)
  (1 - 479x + 15210x^2) = 125x(5 - 198x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  reals for every n >= 1, with sqrt(168601) as Real.sqrt 168601 and 2^(-1-n) as an integer power.
* Controls proved in the proof file: the definition gives 625, 274625, 122039125, 54279694625,
  24143758634125, 10739266230499625, 4776881955584279125, 2124782217358970404625,
  945114307570509938324125, 420391815800244320602909625, 186992491150169573406883769125 for
  n = 1..11, the entry's data; the neighbor table is symmetric, loop free and 5-regular.
-/

namespace OMA.S_oeis_a223318

open PowerSeries Finset

/-- The neighbors of the vertices 0..11 of the icosahedron, as tabulated in the entry
(Vertex neighbors): entry x of the list holds the neighbors of x. -/
def nbrs : List (List ℕ) :=
  [[1, 2, 5, 6, 7], [0, 2, 3, 7, 8], [0, 1, 4, 6, 8], [1, 7, 8, 9, 11], [2, 6, 8, 9, 10],
  [0, 6, 7, 10, 11], [0, 2, 4, 5, 10], [0, 1, 3, 5, 11], [1, 2, 3, 4, 9], [3, 4, 8, 10, 11],
  [4, 5, 6, 9, 11], [3, 5, 7, 9, 10]]

/-- Two labels are adjacent, joined by an icosahedral edge, when the second is a listed neighbor of
the first. -/
def adj (x y : Fin 12) : Prop := y.val ∈ nbrs.getD x.val []

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- The horizontal movements inside the row (x(i,0), x(i,1), x(i,2), x(i,3), x(i,4)) are between adjacent labels. -/
def hrow (r : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : Prop :=
  adj r.1 r.2.1 ∧ adj r.2.1 r.2.2.1 ∧ adj r.2.2.1 r.2.2.2.1 ∧ adj r.2.2.2.1 r.2.2.2.2

/-- The row `s` may lie directly below the row `r`: the antidiagonal pairs (x(i,j+1), x(i+1,j)) hold
adjacent labels. -/
def ok (r s : Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) : Prop :=
  adj r.2.1 s.1 ∧ adj r.2.2.1 s.2.1 ∧ adj r.2.2.2.1 s.2.2.1 ∧ adj r.2.2.2.2 s.2.2.2.1

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A223318: the number of n X 5 arrays of labels 0..11, given by their rows f i = (x(i,0), x(i,1),
x(i,2), x(i,3), x(i,4)), starting with x(0,0) = 0, in which every movement to a horizontal or
antidiagonal neighbor moves along an icosahedral edge. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 479 * X + 15210 * X ^ 2) = 125 * X * (5 - 198 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (25 * 2 ^ (-1 - (n : ℤ)) *
        ((479 - Real.sqrt 168601) ^ n * (-3181 + 11 * Real.sqrt 168601) +
        (479 + Real.sqrt 168601) ^ n * (3181 + 11 * Real.sqrt 168601))) /
        (169 * Real.sqrt 168601) := by
  sorry

end OMA.S_oeis_a223318
