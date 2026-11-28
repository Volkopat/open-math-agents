import Mathlib

/-!
# OEIS A206170: Barker's g.f. and closed form for 2 X (n+1) 0..3 arrays, values introduced in row major order, every 2 X 2 subblock in a row with an equal number of equal diagonal or antidiagonal elements, adjacent rows differing

Source: https://oeis.org/A206170 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A206170 (R. H. Hardin, Feb 04 2012), offset 1: Number of 2 X (n+1) 0..3 arrays with every 2 X
2 subblock in a row having an equal number of equal diagonal or equal antidiagonal elements,
adjacent rows differing in this number, and new values 0..3 introduced in row major order. Row 1 of
A206169.
Formula section:
Conjectures from Colin Barker, Mar 04 2018:
G.f.: x*(15 - 185*x + 626*x^2 - 576*x^3) / ((1 - x)*(1 - 2*x)*(1 - 6*x)*(1 - 9*x)).
a(n) = (9 + 3*2^n + 2^(1+n)*3^n + 2*9^n) / 3.

Formalization notes:
* An array is a function x : Fin 2 -> Fin (n + 1) -> Fin 4, x i j being the entry in row i and
  column j (2 rows and n + 1 columns).
* `blockNum x i i' j j'` is the number of equal diagonal or equal antidiagonal pairs of the 2 X 2
  subblock in rows i, i' and columns j, j': [x(i,j) = x(i',j')] + [x(i,j') = x(i',j)]. `Cond` asks
  that it be equal for horizontally neighboring subblocks (so equal along each row of subblocks) and
  different for vertically neighboring ones (adjacent rows of subblocks differ); with 2 rows there
  is one row of subblocks and the second part is vacuous. The proof shows that, the condition not
  depending on the names of the values, the count is the same when the values are introduced in
  column major order, and then counts the transposed arrays. This reading reproduces the entry's
  data.
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..3 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 - x)(1 - 2x)(1 - 6x)(1 - 9x)) = x(15 - 185x + 626x^2 - 576x^3) in the formal power series
  ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0),
  and the closed form in the reals for every n >= 1.
* Controls proved in the proof file: the definition gives 15, 85, 641, 5257, 44585, 385465, 3375401,
  29817817, 264999305, 2364834745 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a206170

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

/-- Every 2 X 2 subblock of x (rows i, i + 1, columns j, j + 1) has the same `blockNum` as its
horizontal neighbor subblock (columns j + 1, j + 2), and a different one from its vertical neighbor
subblock (rows i + 1, i + 2). -/
def Cond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  (∀ i i' : Fin R, ∀ j j' j'' : Fin C, i'.val = i.val + 1 → j'.val = j.val + 1 →
      j''.val = j'.val + 1 → blockNum x i i' j j' = blockNum x i i' j' j'') ∧
    ∀ i i' i'' : Fin R, ∀ j j' : Fin C, i'.val = i.val + 1 → i''.val = i'.val + 1 →
      j'.val = j.val + 1 → blockNum x i i' j j' ≠ blockNum x i' i'' j j'

instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance

/-- A206170(n): the number of 2 X (n+1) arrays with entries 0..3, x i j being the entry in row i and
column j, in which every 2 X 2 subblock in a row has the same number of equal diagonal or equal
antidiagonal elements and vertically adjacent subblocks differ in this number (`Cond`), and the
values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin 2 → Fin (n + 1) → Fin 4)).filter
    (fun x => Cond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 6 * X) * (1 - 9 * X)) = X * (15 - 185 * X + 626 * X ^ 2 - 576 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (9 + 3 * 2 ^ n + 2 ^ (1 + n) * 3 ^ n + 2 * 9 ^ n) / 3 := by
  sorry

end OMA.S_oeis_a206170
