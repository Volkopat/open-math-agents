import Mathlib

/-!
# OEIS A223443: Barker's g.f. and closed form for n X 2 colorings by the 4-level binary fanout graph

Source: https://oeis.org/A223443 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A223443 (R. H. Hardin, Mar 20 2013), offset 1: 4-level binary fanout graph coloring a
rectangular array: number of n X 2 0..14 arrays where 0..14 label nodes of a graph with edges 0,1
1,3 3,5 3,6 1,4 4,7 4,8 0,2 2,9 9,11 9,12 2,10 10,13 10,14 and every array movement to a horizontal
or vertical neighbor moves along an edge of this graph. Column 2 of A223449.
Formula section:
Empirical: a(n) = 6*a(n-1) - 8*a(n-2) for n>3.
Conjectures from Colin Barker, Aug 20 2018: (Start)
G.f.: 4*x*(7 - 16*x + 2*x^2) / ((1 - 2*x)*(1 - 4*x)).
a(n) = 2^(n-2) * (4+25*2^n) for n>1.
(End)

Formalization notes:
* The labels 0..14 are the nodes of the graph with the 14 edges listed in the entry, kept in the
  entry's order in `edges`; two labels are adjacent when they are joined by an edge, in either
  order.
* An array is given by its n rows f i = (x(i,0), x(i,1)). The neighbor pairs that must move along an
  edge are the horizontal pairs (x(i,j), x(i,j+1)) and the vertical pairs (x(i,j), x(i+1,j));
  diagonal and antidiagonal neighbors are not constrained. The entry has no condition on the first
  entry, so every labeling is counted.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x)
  ((1 - 2x)(1 - 4x)) = 4x(7 - 16x + 2x^2) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form for every
  n > 1 as an identity of natural numbers (for n >= 2 the exponent n - 2 is exact).
* Controls proved in the proof file: the definition gives 28, 104, 408, 1616, 6432, 25664, 102528,
  409856, 1638912, 6554624, 26216448, 104861696, 419438592, 1677737984, 6710919168 for n = 1..15,
  the entry's data; the graph has 14 edges, with the listed number of neighbors for each label.
-/

namespace OMA.S_oeis_a223443

open PowerSeries Finset

/-- The edges of the graph on the labels 0..14, as listed in the entry. -/
def edges : List (ℕ × ℕ) :=
  [(0, 1), (1, 3), (3, 5), (3, 6), (1, 4), (4, 7), (4, 8), (0, 2), (2, 9), (9, 11), (9, 12),
  (2, 10), (10, 13), (10, 14)]

/-- Two labels are adjacent when they are joined by an edge. -/
def adj (x y : Fin 15) : Prop := (x.val, y.val) ∈ edges ∨ (y.val, x.val) ∈ edges

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- The horizontal movements inside the row (x(i,0), x(i,1)) are between adjacent labels. -/
def hrow (r : Fin 15 × Fin 15) : Prop :=
  adj r.1 r.2

/-- The row `s` may lie directly below the row `r`: the vertical pairs (x(i,j), x(i+1,j)) hold
adjacent labels. -/
def ok (r s : Fin 15 × Fin 15) : Prop :=
  adj r.1 s.1 ∧ adj r.2 s.2

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A223443: the number of n X 2 arrays of labels 0..14, given by their rows f i = (x(i,0), x(i,1)),
in which every movement to a horizontal or vertical neighbor moves along an edge of the graph. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 15 × Fin 15)).filter
    (fun f => (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j))).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - 2 * X) * (1 - 4 * X)) = 4 * X * (7 - 16 * X + 2 * X ^ 2) ∧
    ∀ n : ℕ, 1 < n → a n = 2 ^ (n - 2) * (4 + 25 * 2 ^ n) := by
  sorry

end OMA.S_oeis_a223443
