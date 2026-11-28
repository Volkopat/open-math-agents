import Mathlib

/-!
# OEIS A223211: Barker's g.f. and closed form for n X 1 colorings by a six-vertex graph

Source: https://oeis.org/A223211 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Mar 18 2013), offset 1: 3 X 3 X 3 triangular graph coloring a rectangular
array: number of n X 1 0..5 arrays where 0..5 label nodes of a graph with edges 0,1 0,2 1,2 1,3
1,4 2,4 3,4 2,5 4,5 and every array movement to a horizontal or vertical neighbor moves along an
edge of this graph. Data: 6, 18, 60, 192, 624, ... Formula: Empirical: a(n) = 2*a(n-1) +
4*a(n-2). Conjectures from Colin Barker, Aug 17 2018: G.f.: 6*x*(1 + x) / (1 - 2*x - 4*x^2).
a(n) = (3*((1-sqrt(5))^n*(-3+sqrt(5)) + (1+sqrt(5))^n*(3+sqrt(5)))) / (4*sqrt(5)).

Formalization notes:
* An n X 1 array is a function from the n rows to the labels 0..5; its only neighbours are
  vertical, rows i and i + 1, and a move along an edge means that the two labels are joined by
  one of the nine listed edges (in either direction).
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1). The identity A(x) = N(x)/D(x) is stated as
  A(x)*D(x) = N(x) in Q[[x]], which is equivalent because D has constant term 1.
* `main` is the conjunction of Barker's two conjectures; the closed form is stated in the reals
  for every n >= 1.
* Controls proved in the proof file: a(1) = 6, a(2) = 18.
-/

namespace OMA.S_oeis_a223211

open PowerSeries Finset

/-- The edges of the graph on 0..5. -/
def edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (2, 4), (3, 4), (2, 5), (4, 5)]

/-- Two labels are adjacent when they are joined by an edge of the graph. -/
def adj (x y : Fin 6) : Prop := (x.val, y.val) ∈ edges ∨ (y.val, x.val) ∈ edges

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- A223211: the number of n X 1 arrays f with entries 0..5 in which every move to the vertical
neighbour (row i to row i + 1) is along an edge. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 6)).filter
    (fun f => ∀ i j : Fin n, j.val = i.val + 1 → adj (f i) (f j))).card

/-- Barker's conjectures: the g.f. 6x(1 + x)/(1 - 2x - 4x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 2 * X - 4 * X ^ 2) =
      6 * X * (1 + X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      3 * ((1 - Real.sqrt 5) ^ n * (-3 + Real.sqrt 5) + (1 + Real.sqrt 5) ^ n * (3 + Real.sqrt 5)) /
        (4 * Real.sqrt 5) := by
  sorry

end OMA.S_oeis_a223211
