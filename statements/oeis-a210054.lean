import Mathlib

/-!
# OEIS A210054: Barker's g.f. and closed form for (n+1) X 2 0..3 arrays, values introduced in row major order, every 2 X 2 subblock with one, two or four distinct values

Source: https://oeis.org/A210054 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A210054 (R. H. Hardin, Mar 16 2012), offset 1: Number of (n+1) X 2 0..3 arrays with every 2 X
2 subblock having one, two or four distinct values, and new values 0..3 introduced in row major
order. Column 1 of A210061.
Formula section:
Conjectures from Colin Barker, Jul 14 2018:
G.f.: x*(9 - 66*x + 92*x^2 - 32*x^3) / ((1 - x)*(1 - 4*x)*(1 - 8*x + 4*x^2)).
a(n) = (1/3) + 4^n - (1/6)*(4-2*sqrt(3))^n*(-2+sqrt(3)) + (1/3)*2^(-1+n)*(2+sqrt(3))^(1+n).

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 2 -> Fin 4, x i j being the entry in row i and
  column j.
* The 2 X 2 subblocks are the blocks in rows i, i + 1 and columns j, j + 1; `blockCount` is the
  number of distinct values among the four entries of a block, and every block must have one, two or
  four distinct values (`BlocksOK`).
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..3 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 - x)(1 - 4x)(1 - 8x + 4x^2)) = x(9 - 66x + 92x^2 - 32x^3) in the formal power series ring
  over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the closed form in the reals for every n >= 1, with the powers of 2 of negative exponent as
  integer powers (zpow).
* Controls proved in the proof file: the definition gives 9, 51, 323, 2187, 15435, 111659, 819243,
  6058155, 44991659, 334914219 for n = 1..10, the entry's data, and a direct enumeration of all
  arrays with two rows gives a(1) = 9.
-/

namespace OMA.S_oeis_a210054

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The number of distinct values in the 2 X 2 subblock of x in rows i, i' and columns j, j'. -/
def blockCount {R C K : ℕ} (x : Fin R → Fin C → Fin K) (i i' : Fin R) (j j' : Fin C) : ℕ :=
  ({x i j, x i j', x i' j, x i' j'} : Finset (Fin K)).card

/-- Every 2 X 2 subblock of x, in rows i, i + 1 and columns j, j + 1, has one, two or four distinct values. -/
def BlocksOK {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i i' : Fin R, ∀ j j' : Fin C, i'.val = i.val + 1 → j'.val = j.val + 1 →
    blockCount x i i' j j' = 1 ∨ blockCount x i i' j j' = 2 ∨ blockCount x i i' j j' = 4

instance {R C K : ℕ} : DecidablePred (@BlocksOK R C K) := fun x => by
  unfold BlocksOK; infer_instance

/-- A210054(n): the number of (n+1) X 2 arrays with entries 0..3, x i j being the entry in row i and
column j, in which every 2 X 2 subblock has one, two or four distinct values (`BlocksOK`) and the
values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter
    (fun x => BlocksOK x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 4 * X) * (1 - 8 * X + 4 * X ^ 2)) = X * (9 - 66 * X + 92 * X ^ 2 - 32 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (1 / 3) + 4 ^ n -
        (1 / 6) * (4 - 2 * Real.sqrt 3) ^ n * (-2 + Real.sqrt 3) +
        (1 / 3) * 2 ^ (-1 + (n : ℤ)) * (2 + Real.sqrt 3) ^ (1 + n) := by
  sorry

end OMA.S_oeis_a210054
