import Mathlib

/-!
# OEIS A205354: Barker's g.f. and closed form for (n+1) X 2 0..2 arrays, values introduced in row major order, every 2 X 2 subblock with the same number of equal diagonal or antidiagonal elements

Source: https://oeis.org/A205354 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A205354 (R. H. Hardin, Jan 26 2012), offset 1: Number of (n+1) X 2 0..2 arrays with every 2 X
2 subblock having the same number of equal diagonal or antidiagonal elements, and new values 0..2
introduced in row major order. Column 1 of A205361.
Formula section:
Conjectures from Colin Barker, Mar 03 2018:
G.f.: 2*x*(7 - 10*x) / ((1 - x)*(1 - 4*x)).
a(n) = 2 + 3*4^n.

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 2 -> Fin 3, x i j being the entry in row i and
  column j.
* For the 2 X 2 subblock in rows i, i' = i + 1 and columns j, j' = j + 1, `blockNum x i i' j j'` is
  the number of its equal diagonal pairs (x(i,j), x(i',j')) and equal antidiagonal pairs (x(i,j'),
  x(i',j)), 0, 1 or 2. `Cond` asks that all subblocks have the same number; this reading reproduces
  the entry's data.
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..2 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 - x)(1 - 4x)) = 2x(7 - 10x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  natural numbers for every n >= 1.
* Controls proved in the proof file: the definition gives 14, 50, 194, 770, 3074, 12290, 49154,
  196610, 786434, 3145730 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a205354

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The number of equal diagonal pairs and equal antidiagonal pairs of the 2 X 2 subblock of x in
rows i, i' and columns j, j': [x(i,j) = x(i',j')] + [x(i,j') = x(i',j)]. -/
def blockNum {R C K : ℕ} (x : Fin R → Fin C → Fin K) (i i' : Fin R) (j j' : Fin C) : ℕ :=
  (if x i j = x i' j' then 1 else 0) + (if x i j' = x i' j then 1 else 0)

/-- Every 2 X 2 subblock of x, in rows i, i + 1 and columns j, j + 1, has the same number of equal
diagonal or antidiagonal elements: any two subblocks have the same `blockNum`. -/
def Cond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i i' k k' : Fin R, ∀ j j' l l' : Fin C, i'.val = i.val + 1 → j'.val = j.val + 1 →
    k'.val = k.val + 1 → l'.val = l.val + 1 → blockNum x i i' j j' = blockNum x k k' l l'

instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance

/-- A205354(n): the number of (n+1) X 2 arrays with entries 0..2, x i j being the entry in row i and
column j, in which every 2 X 2 subblock has the same number of equal diagonal or antidiagonal
elements (`Cond`) and the values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 3)).filter
    (fun x => Cond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 4 * X)) = 2 * X * (7 - 10 * X) ∧
    ∀ n : ℕ, 1 ≤ n → a n = 2 + 3 * 4 ^ n := by
  sorry

end OMA.S_oeis_a205354
