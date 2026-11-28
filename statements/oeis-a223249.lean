import Mathlib

/-!
# OEIS A223249: Barker's generating function and closed form for two-loop graph colorings

Source: https://oeis.org/A223249 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Mar 18 2013), offset 1: Two-loop graph coloring a rectangular array: number
of n X 2 0..4 arrays where 0..4 label nodes of a graph with edges 0,1 1,2 2,0 0,3 3,4 4,0 and every
array movement to a horizontal or vertical neighbor moves along an edge of this graph. Data: 12,
52, 236, 1076, 4908, ... Formula: Empirical: a(n) = 5*a(n-1) - 2*a(n-2). Conjectures from Colin
Barker, Mar 16 2018: (Start) G.f.: 4*x*(3 - 2*x) / (1 - 5*x + 2*x^2).
a(n) = (2^(1-n)*((5-sqrt(17))^n*(-1+sqrt(17)) + (1+sqrt(17))*(5+sqrt(17))^n)) / sqrt(17). (End)

Formalization notes:
* An n X 2 array is a function f from the n rows to functions from the 2 columns to the labels
  0..4. The horizontal neighbors are the two entries of a row, the vertical neighbors are the
  entries in one column of rows i and i + 1; a move along an edge means the two labels are joined
  by one of the six listed edges (in either direction; the graph has no loops).
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1). The identity A(x) = N(x)/D(x) is stated as
  A(x) D(x) = N(x) in Q[[x]], which is equivalent because D has constant term 1.
* The closed form is stated in the reals for every n >= 1, with 2^(1-n) an integer power
  (zpow), since 1 - n is negative for n >= 2.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..4) = 12, 52, 236, 1076.
-/

namespace OMA.S_oeis_a223249

open PowerSeries Finset

/-- The edges of the graph on 0..4. -/
def edges : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)]

/-- Two labels are adjacent when they are joined by an edge of the graph. -/
def adj (x y : Fin 5) : Prop := (x.val, y.val) ∈ edges ∨ (y.val, x.val) ∈ edges

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- A223249(n): the number of n X 2 arrays f (f i j is the entry in row i, column j) with entries
0..4 in which the two entries of every row, and every two vertically neighboring entries, are
joined by an edge. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 2 → Fin 5)).filter
    (fun f => (∀ i : Fin n, adj (f i 0) (f i 1)) ∧
      ∀ i i' : Fin n, i'.val = i.val + 1 → ∀ j : Fin 2, adj (f i j) (f i' j))).card

/-- Barker's conjectures: the g.f. 4x(3 - 2x)/(1 - 5x + 2x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 5 * X + 2 * X ^ 2) =
      4 * X * (3 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ ((1 : ℤ) - n) * ((5 - Real.sqrt 17) ^ n * (-1 + Real.sqrt 17) +
        (1 + Real.sqrt 17) * (5 + Real.sqrt 17) ^ n)) / Real.sqrt 17 := by
  sorry

end OMA.S_oeis_a223249
