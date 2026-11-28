import Mathlib

/-!
# OEIS A205220: Barker's g.f. and closed form for (n+1) X 3 0..1 arrays, values introduced in row major order, subblock counts of equal diagonal and antidiagonal pairs differing from each neighbor subblock

Source: https://oeis.org/A205220 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A205220 (R. H. Hardin, Jan 23 2012), offset 1: Number of (n+1) X 3 0..1 arrays with the number
of equal 2 X 2 subblock diagonal pairs and equal antidiagonal pairs differing from each horizontal
or vertical neighbor, and new values 0..1 introduced in row major order. Column 2 of A205226.
Formula section:
Conjectures from Colin Barker, Jun 11 2018:
G.f.: 4*x*(5 + 8*x) / (1 - x - 4*x^2).
a(n) = (2^(2-n)*((1-sqrt(17))^n*(-4+sqrt(17)) + (1+sqrt(17))^n*(4+sqrt(17)))) / sqrt(17).

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 3 -> Fin 2, x i j being the entry in row i and
  column j.
* For the 2 X 2 subblock in rows i, i' = i + 1 and columns j, j' = j + 1, `blockNum x i i' j j'` is
  the number of its equal diagonal pairs (x(i,j), x(i',j')) and equal antidiagonal pairs (x(i,j'),
  x(i',j)), 0, 1 or 2. `Cond` asks that this number differ from the number of the subblock to the
  right (columns j + 1, j + 2) and of the subblock below (rows i + 1, i + 2); since differing is
  symmetric, this is each horizontal or vertical neighbor subblock. This reading reproduces the
  entry's data.
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..1 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - x - 4x^2) = 4x(5 + 8x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  reals for every n >= 1.
* Controls proved in the proof file: the definition gives 20, 52, 132, 340, 868, 2228, 5700, 14612,
  37412, 95860 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a205220

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

/-- The number `blockNum` of every 2 X 2 subblock of x (rows i, i + 1 and columns j, j + 1) differs
from that of each horizontal neighbor subblock (rows i, i + 1 and columns j + 1, j + 2) and each
vertical neighbor subblock (rows i + 1, i + 2 and columns j, j + 1). -/
def Cond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  (∀ i i' : Fin R, ∀ j j' j'' : Fin C, i'.val = i.val + 1 → j'.val = j.val + 1 →
      j''.val = j'.val + 1 → blockNum x i i' j j' ≠ blockNum x i i' j' j'') ∧
    ∀ i i' i'' : Fin R, ∀ j j' : Fin C, i'.val = i.val + 1 → i''.val = i'.val + 1 →
      j'.val = j.val + 1 → blockNum x i i' j j' ≠ blockNum x i' i'' j j'

instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance

/-- A205220(n): the number of (n+1) X 3 arrays with entries 0..1, x i j being the entry in row i and
column j, in which the number of equal diagonal and equal antidiagonal pairs of every 2 X 2 subblock
differs from that of each horizontal or vertical neighbor subblock (`Cond`) and the values are
introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 3 → Fin 2)).filter
    (fun x => Cond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X - 4 * X ^ 2) = 4 * X * (5 + 8 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (2 - (n : ℤ)) * ((1 - Real.sqrt 17) ^ n * (-4 + Real.sqrt 17) +
        (1 + Real.sqrt 17) ^ n * (4 + Real.sqrt 17))) / Real.sqrt 17 := by
  sorry

end OMA.S_oeis_a205220
