import Mathlib

/-!
# OEIS A223499: Barker's g.f. and closed form for n X 3 colorings by the Petersen graph (3,1)

Source: https://oeis.org/A223499 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A223499 (R. H. Hardin, Mar 21 2013), offset 1: Petersen graph (3,1) coloring a rectangular
array: number of n X 3 0..5 arrays where 0..5 label nodes of a graph with edges 0,1 0,3 3,5 3,4 1,2
1,4 4,5 2,0 2,5 and every array movement to a horizontal, diagonal or antidiagonal neighbor moves
along an edge of this graph, with the array starting at 0. Column 3 of A223504.
Formula section:
Conjectures from Colin Barker, Aug 21 2018:
G.f.: x*(9 - 20*x + 10*x^2) / ((1 - x)*(1 - 14*x + 10*x^2)).
a(n) = (13 + (13-2*sqrt(39))*(7-sqrt(39))^n + (7+sqrt(39))^n*(13+2*sqrt(39))) / 39.

Formalization notes:
* The labels 0..5 are the nodes of the graph with the nine listed edges (`edges`); two labels are
  adjacent when they are joined by an edge, in either order.
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2)). The neighbor pairs that must move
  along an edge are the horizontal pairs (x(i,j), x(i,j+1)), the diagonal pairs (x(i,j),
  x(i+1,j+1)) and the antidiagonal pairs (x(i,j+1), x(i+1,j)); vertical neighbors are not
  constrained. Starting at 0 means x(0,0) = 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - x)(1 - 14x + 10x^2) = x(9 - 20x + 10x^2) in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the
  closed form in the reals for every n >= 1.
* Controls proved in the proof file: the definition gives 9, 115, 1519, 20115, 266419, 3528715, 46737819, 619042315, 8199214219, 108598575915, 1438387920619, 19051445129515 for
  n = 1..12, the entry's data; the graph has 9 edges and every label has 3 neighbors.
-/

namespace OMA.S_oeis_a223499

open PowerSeries Finset

/-- The edges of the graph on the labels 0..5, as listed in the entry. -/
def edges : List (ℕ × ℕ) := [(0, 1), (0, 3), (3, 5), (3, 4), (1, 2), (1, 4), (4, 5), (2, 0), (2, 5)]

/-- Two labels are adjacent when they are joined by an edge. -/
def adj (x y : Fin 6) : Prop := (x.val, y.val) ∈ edges ∨ (y.val, x.val) ∈ edges

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- The horizontal movements inside the row (x(i,0), x(i,1), x(i,2)) are between adjacent
labels. -/
def hrow (r : Fin 6 × Fin 6 × Fin 6) : Prop := adj r.1 r.2.1 ∧ adj r.2.1 r.2.2

/-- The row `s` may lie directly below the row `r`: the diagonal pairs (x(i,j), x(i+1,j+1)) and
the antidiagonal pairs (x(i,j+1), x(i+1,j)) hold adjacent labels. -/
def ok (r s : Fin 6 × Fin 6 × Fin 6) : Prop :=
  adj r.1 s.2.1 ∧ adj r.2.1 s.2.2 ∧ adj r.2.1 s.1 ∧ adj r.2.2 s.2.1

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A223499: the number of n X 3 arrays of labels 0..5, given by their rows, starting with
x(0,0) = 0, in which every movement to a horizontal, diagonal or antidiagonal neighbor moves along
an edge of the graph. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 6 × Fin 6 × Fin 6)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 14 * X + 10 * X ^ 2)) = X * (9 - 20 * X + 10 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (13 + (13 - 2 * Real.sqrt 39) * (7 - Real.sqrt 39) ^ n +
        (7 + Real.sqrt 39) ^ n * (13 + 2 * Real.sqrt 39)) / 39 := by
  sorry

end OMA.S_oeis_a223499
