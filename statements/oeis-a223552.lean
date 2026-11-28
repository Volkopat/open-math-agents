import Mathlib

/-!
# OEIS A223552: Barker's g.f. and closed form for n X 4 colorings by the Petersen graph (3,1)

Source: https://oeis.org/A223552 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A223552 (R. H. Hardin, Mar 22 2013), offset 1: Petersen graph (3,1) coloring a rectangular
array: number of n X 4 0..5 arrays where 0..5 label nodes of a graph with edges 0,1 0,3 3,5 3,4 1,2
1,4 4,5 2,0 2,5 and every array movement to a horizontal or antidiagonal neighbor moves along an edge
of this graph, with the array starting at 0. Column 4 of A223556.
Formula section:
Conjectures from Colin Barker, Aug 21 2018:
G.f.: 9*x*(3 - 2*x) / (1 - 41*x + 16*x^2).
a(n) = 3*sqrt(3/11)*2^(-4-n)*((41-7*sqrt(33))^n*(-1+sqrt(33)) + (1+sqrt(33))*(41+7*sqrt(33))^n).

Formalization notes:
* The labels 0..5 are the nodes of the graph with the nine listed edges (`edges`); two labels are
  adjacent when they are joined by an edge, in either order.
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2), x(i,3)). The neighbor pairs that
  must move along an edge are the horizontal pairs (x(i,j), x(i,j+1)) and the antidiagonal pairs
  (x(i,j+1), x(i+1,j)); vertical and diagonal neighbors are not constrained. Starting at 0 means
  x(0,0) = 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - 41x + 16x^2) = 9x(3 - 2x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  reals for every n >= 1, with 2^(-4-n) as an integer power and sqrt(3/11) as Real.sqrt (3 / 11).
* Controls proved in the proof file: the definition gives 27, 1089, 44217, 1795473, 72906921, 2960456193, 120212193177, 4881332621169, 198211242377097, 8048559615522273, 326819564358379641, 13270825184845208913 for
  n = 1..12, the entry's data; the graph has 9 edges and every label has 3 neighbors.
-/

namespace OMA.S_oeis_a223552

open PowerSeries Finset

/-- The edges of the graph on the labels 0..5, as listed in the entry. -/
def edges : List (ℕ × ℕ) := [(0, 1), (0, 3), (3, 5), (3, 4), (1, 2), (1, 4), (4, 5), (2, 0), (2, 5)]

/-- Two labels are adjacent when they are joined by an edge. -/
def adj (x y : Fin 6) : Prop := (x.val, y.val) ∈ edges ∨ (y.val, x.val) ∈ edges

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- The horizontal movements inside the row (x(i,0), x(i,1), x(i,2), x(i,3)) are between adjacent labels. -/
def hrow (r : Fin 6 × Fin 6 × Fin 6 × Fin 6) : Prop :=
  adj r.1 r.2.1 ∧ adj r.2.1 r.2.2.1 ∧ adj r.2.2.1 r.2.2.2

/-- The row `s` may lie directly below the row `r`: the antidiagonal pairs (x(i,j+1), x(i+1,j)) hold
adjacent labels. -/
def ok (r s : Fin 6 × Fin 6 × Fin 6 × Fin 6) : Prop :=
  adj r.2.1 s.1 ∧ adj r.2.2.1 s.2.1 ∧ adj r.2.2.2 s.2.2.1

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A223552: the number of n X 4 arrays of labels 0..5, given by their rows
f i = (x(i,0), x(i,1), x(i,2), x(i,3)), starting with x(0,0) = 0, in which every movement to a
horizontal or antidiagonal neighbor moves along an edge of this graph. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 6 × Fin 6 × Fin 6 × Fin 6)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 41 * X + 16 * X ^ 2) = 9 * X * (3 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      3 * Real.sqrt (3 / 11) * 2 ^ (-4 - (n : ℤ)) *
        ((41 - 7 * Real.sqrt 33) ^ n * (-1 + Real.sqrt 33) +
        (1 + Real.sqrt 33) * (41 + 7 * Real.sqrt 33) ^ n) := by
  sorry

end OMA.S_oeis_a223552
