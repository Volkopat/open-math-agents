import Mathlib

/-!
# OEIS A223258: Barker's g.f. and closed form for rolling icosahedron footprints, n X 3

Source: https://oeis.org/A223258 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A223258 (R. H. Hardin, Mar 19 2013), offset 1: Rolling icosahedron footprints: number of n X 3
0..11 arrays starting with 0 where 0..11 label vertices of an icosahedron and every array movement
to a horizontal or vertical neighbor moves along an icosahedral edge. Column 3 of A223263.
Formula section:
Conjectures from Colin Barker, Aug 18 2018:
G.f.: 5*x*(5 - 21*x) / (1 - 38*x + 129*x^2).
a(n) = (5*((19-2*sqrt(58))^n*(-41+7*sqrt(58)) + (19+2*sqrt(58))^n*(41+7*sqrt(58)))) / (86*sqrt(58)).

Formalization notes:
* The labels 0..11 are the vertices of the icosahedron, numbered as in `edges`: 0 is the top vertex,
  1..5 the upper pentagon in cyclic order, 6..10 the lower pentagon in cyclic order and 11 the
  bottom vertex, the upper vertex 1 + i being joined to the lower vertices 6 + i and 6 + (i + 4) mod
  5. A movement along an icosahedral edge joins two adjacent labels. The rotation group of the
  icosahedron is transitive on vertices, so the count of arrays starting with 0 does not depend on
  the numbering.
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2)). The neighbor pairs that must move
  along an icosahedral edge are the horizontal pairs (x(i,j), x(i,j+1)) and the vertical pairs
  (x(i,j), x(i+1,j)). Starting with 0 means x(0,0) = 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x)
  (1 - 38x + 129x^2) = 5x(5 - 21x) in the formal power series ring over the rationals, with A(x) =
  Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the reals for
  every n >= 1.
* Controls proved in the proof file: the definition gives 25, 845, 28885, 988625, 33841585,
  1158447605, 39655444525, 1357467150905, 46468199390665, 1590678314378525 for n = 1..10, the
  entry's data; the edge list is that of a 5-regular graph on 12 vertices with 30 edges.
-/

namespace OMA.S_oeis_a223258

open PowerSeries Finset

/-- The 30 edges of the icosahedron on the vertex numbering 0 = top vertex, 1..5 = upper pentagon in
cyclic order, 6..10 = lower pentagon in cyclic order, 11 = bottom vertex, where the upper vertex
1 + i is joined to the lower vertices 6 + i and 6 + (i + 4) mod 5. -/
def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (1, 6), (1, 10), (2, 3), (2, 6), (2, 7),
  (3, 4), (3, 7), (3, 8), (4, 5), (4, 8), (4, 9), (5, 9), (5, 10), (6, 7), (6, 10), (6, 11), (7, 8),
  (7, 11), (8, 9), (8, 11), (9, 10), (9, 11), (10, 11)]

/-- Two vertex labels are adjacent when they are joined by an edge. -/
def adj (x y : Fin 12) : Prop := (x.val, y.val) ∈ edges ∨ (y.val, x.val) ∈ edges

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- The horizontal movements inside the row (x(i,0), x(i,1), x(i,2)) are between adjacent
labels. -/
def hrow (r : Fin 12 × Fin 12 × Fin 12) : Prop := adj r.1 r.2.1 ∧ adj r.2.1 r.2.2

/-- The row `s` may lie directly below the row `r`: the vertical pairs (x(i,j), x(i+1,j)) hold
adjacent labels. -/
def ok (r s : Fin 12 × Fin 12 × Fin 12) : Prop :=
  adj r.1 s.1 ∧ adj r.2.1 s.2.1 ∧ adj r.2.2 s.2.2

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A223258: the number of n X 3 arrays of labels 0..11, given by their rows
f i = (x(i,0), x(i,1), x(i,2)), starting with x(0,0) = 0, in which every movement to a
horizontal or vertical neighbor moves along an icosahedral edge. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 12 × Fin 12 × Fin 12)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. 5x(5 - 21x)/(1 - 38x + 129x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 38 * X + 129 * X ^ 2) =
      5 * X * (5 - 21 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (5 * ((19 - 2 * Real.sqrt 58) ^ n * (-41 + 7 * Real.sqrt 58) +
        (19 + 2 * Real.sqrt 58) ^ n * (41 + 7 * Real.sqrt 58))) / (86 * Real.sqrt 58) := by
  sorry

end OMA.S_oeis_a223258
