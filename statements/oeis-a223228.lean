import Mathlib

/-!
# OEIS A223228: Barker's g.f. and closed form for rolling icosahedron footprints on n X 3 arrays

Source: https://oeis.org/A223228 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Mar 18 2013), offset 1: Rolling icosahedron footprints: number of n X 3
0..11 arrays starting with 0 where 0..11 label vertices of an icosahedron and every array movement
to a horizontal, diagonal or antidiagonal neighbor moves along an icosahedral edge. Column 3 of
A223233. Data: 25, 785, 25225, 812225, 26157625, ... Formula: Empirical: a(n) = 35*a(n-1) -
90*a(n-2). Conjectures from Colin Barker, Aug 17 2018: G.f.: 5*x*(5 - 18*x) / (1 - 35*x +
90*x^2). a(n) = (2^(-1-n)*((35-sqrt(865))^n*(-15+sqrt(865)) + (15+sqrt(865))*(35+sqrt(865))^n))
/ sqrt(865).

Formalization notes:
* The icosahedron is given by an explicit labelling: 0 is the top vertex, 1..5 the upper ring,
  6..10 the lower ring and 11 the bottom vertex (30 edges, every vertex of degree 5). Any other
  labelling gives the same count: a relabelling is a graph isomorphism and the icosahedron is
  vertex-transitive, so the condition starting with 0 is equivalent to starting with any fixed
  vertex.
* An n X 3 array is f : Fin n -> Fin 3 -> Fin 12 with f i j in row i and column j; starting with
  0 means that the top left entry f 0 0 is 0. Its horizontal neighbours are (i, j), (i, j + 1),
  its diagonal neighbours (i, j), (i + 1, j + 1) and its antidiagonal neighbours (i, j + 1),
  (i + 1, j); each such pair must carry adjacent vertices. With this reading the count reproduces
  all twelve terms of the entry's data, which the proof file checks.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x)*D(x) = N(x) in Q[[x]], which is
  equivalent to A = N/D because D has constant term 1.
* The closed form is stated in the reals for every n >= 1 (the entry's offset), with 2^(-1-n)
  the real power.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..12) = 25, 785, 25225, 812225, 26157625, 842416625,
  27130395625, 873746350625, 28139386665625, 906241361740625, 29185902861015625,
  939944877578890625, the entry's data.
-/

namespace OMA.S_oeis_a223228

open PowerSeries Finset

/-- The 30 edges of the icosahedron on 0..11: 0 is the top vertex, 1..5 the upper ring, 6..10
the lower ring and 11 the bottom vertex; upper vertex 1 + i is joined to lower vertices 6 + i and
6 + ((i + 1) mod 5). -/
def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (1, 6), (1, 7), (2, 3), (2, 7), (2, 8),
    (3, 4), (3, 8), (3, 9), (4, 5), (4, 9), (4, 10), (5, 6), (5, 10), (6, 7), (6, 10), (6, 11),
    (7, 8), (7, 11), (8, 9), (8, 11), (9, 10), (9, 11), (10, 11)]

/-- Two labels are adjacent when they are joined by an edge of the icosahedron. -/
def adj (x y : Fin 12) : Prop := (x.val, y.val) ∈ edges ∨ (y.val, x.val) ∈ edges

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- A223228: the number of n X 3 arrays f (f i j in row i, column j) with entries 0..11 whose
top left entry is 0 and in which every pair of horizontal neighbours (i, j), (i, j + 1), every pair
of diagonal neighbours (i, j), (i + 1, j + 1) and every pair of antidiagonal neighbours
(i, j + 1), (i + 1, j) carries adjacent vertices of the icosahedron. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 3 → Fin 12)).filter (fun f =>
    (∀ i : Fin n, i.val = 0 → f i 0 = 0) ∧
    (∀ i : Fin n, ∀ j j' : Fin 3, j'.val = j.val + 1 → adj (f i j) (f i j')) ∧
    (∀ i i' : Fin n, i'.val = i.val + 1 → ∀ j j' : Fin 3, j'.val = j.val + 1 →
      adj (f i j) (f i' j') ∧ adj (f i j') (f i' j)))).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 35 * X + 90 * X ^ 2) = 5 * X * (5 - 18 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 : ℝ) ^ ((-1 : ℝ) - n) * ((35 - Real.sqrt 865) ^ n * (-15 + Real.sqrt 865) +
        (15 + Real.sqrt 865) * (35 + Real.sqrt 865) ^ n) / Real.sqrt 865 := by
  sorry

end OMA.S_oeis_a223228
