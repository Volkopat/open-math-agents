import Mathlib

/-!
# OEIS A223277: Barker's g.f. and closed form for rolling icosahedron face footprints, n X 3

Source: https://oeis.org/A223277 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A223277 (R. H. Hardin, Mar 19 2013), offset 1: Rolling icosahedron face footprints: number of
n X 3 0..19 arrays starting with 0 where 0..19 label faces of an icosahedron and every array
movement to a horizontal, diagonal or antidiagonal neighbor moves across an icosahedral edge. Column
3 of A223282.
Formula section:
Conjectures from Colin Barker, Aug 18 2018:
G.f.: 3*x*(3 - 4*x) / (1 - 11*x + 12*x^2).
a(n) = (2^(-1-n)*((11-sqrt(73))^n*(-7+sqrt(73)) + (7+sqrt(73))*(11+sqrt(73))^n)) / sqrt(73).

Formalization notes:
* The labels 0..19 are the faces of the icosahedron, listed in `faces` as vertex triples on the
  vertex numbering 0 = top vertex, 1..5 = upper pentagon in cyclic order, 6..10 = lower pentagon in
  cyclic order, 11 = bottom vertex (the upper vertex 1 + i joined to the lower vertices 6 + i and
  6 + (i + 4) mod 5); the list is the 20 triangles of this graph, sorted. A movement across an
  icosahedral edge joins two faces that share an edge, that is two vertices. The rotation group of
  the icosahedron is transitive on faces, so the count of arrays starting with 0 does not depend on
  the numbering.
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2)). The neighbor pairs that must move
  across an icosahedral edge are the horizontal pairs (x(i,j), x(i,j+1)) and the diagonal pairs
  (x(i,j), x(i+1,j+1)) and the antidiagonal pairs (x(i,j+1), x(i+1,j)); vertical neighbors are not
  constrained. Starting with 0 means x(0,0) = 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x)
  (1 - 11x + 12x^2) = 3x(3 - 4x) in the formal power series ring over the rationals, with A(x) =
  Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the reals for
  every n >= 1, with 2^(-1-n) as an integer power.
* Controls proved in the proof file: the definition gives 9, 87, 849, 8295, 81057, 792087, 7740273,
  75637959, 739134273, 7222821495 for n = 1..10, the entry's data; every listed triple is a triangle
  of the icosahedron graph and every face is adjacent to exactly 3 faces.
-/

namespace OMA.S_oeis_a223277

open PowerSeries Finset

/-- The 20 faces of the icosahedron as vertex triples, on the vertex numbering 0 = top vertex,
1..5 = upper pentagon in cyclic order, 6..10 = lower pentagon in cyclic order, 11 = bottom vertex,
where the upper vertex 1 + i is joined to the lower vertices 6 + i and 6 + (i + 4) mod 5: these are
the 20 triangles of that graph, sorted. Face k is the k-th triple. -/
def faces : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 2), (0, 1, 5), (0, 2, 3), (0, 3, 4), (0, 4, 5), (1, 2, 6), (1, 5, 10), (1, 6, 10),
  (2, 3, 7), (2, 6, 7), (3, 4, 8), (3, 7, 8), (4, 5, 9), (4, 8, 9), (5, 9, 10), (6, 7, 11),
  (6, 10, 11), (7, 8, 11), (8, 9, 11), (9, 10, 11)]

/-- The three vertices of face k. -/
def verts (k : Fin 20) : List ℕ :=
  [(faces.getD k.val (0, 0, 0)).1, (faces.getD k.val (0, 0, 0)).2.1,
    (faces.getD k.val (0, 0, 0)).2.2]

/-- Two face labels are adjacent, so that a move between them crosses an icosahedral edge, when
the faces share two vertices, that is an edge. -/
def adj (x y : Fin 20) : Prop := ((verts x).filter (fun v => decide (v ∈ verts y))).length = 2

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- The horizontal movements inside the row (x(i,0), x(i,1), x(i,2)) are between adjacent
labels. -/
def hrow (r : Fin 20 × Fin 20 × Fin 20) : Prop := adj r.1 r.2.1 ∧ adj r.2.1 r.2.2

/-- The row `s` may lie directly below the row `r`: the diagonal pairs (x(i,j), x(i+1,j+1)) and the
antidiagonal pairs (x(i,j+1), x(i+1,j)) hold adjacent labels. -/
def ok (r s : Fin 20 × Fin 20 × Fin 20) : Prop :=
  adj r.1 s.2.1 ∧ adj r.2.1 s.2.2 ∧ adj r.2.1 s.1 ∧ adj r.2.2 s.2.1

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A223277: the number of n X 3 arrays of labels 0..19, given by their rows
f i = (x(i,0), x(i,1), x(i,2)), starting with x(0,0) = 0, in which every movement to a
horizontal, diagonal or antidiagonal neighbor moves across an icosahedral edge. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 20 × Fin 20 × Fin 20)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. 3x(3 - 4x)/(1 - 11x + 12x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 11 * X + 12 * X ^ 2) =
      3 * X * (3 - 4 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-1 - (n : ℤ)) *
        ((11 - Real.sqrt 73) ^ n * (-7 + Real.sqrt 73) +
          (7 + Real.sqrt 73) * (11 + Real.sqrt 73) ^ n)) / Real.sqrt 73 := by
  sorry

end OMA.S_oeis_a223277
