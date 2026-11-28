import Mathlib

/-!
# OEIS A208089: Barker's g.f. and closed form for 8 X (n+1) 0..1 arrays, values introduced in row major order, every 2 X 2 subblock with the same number of equal edges as its horizontal neighbors and a different number from its vertical neighbors

Source: https://oeis.org/A208089 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A208089 (R. H. Hardin, Feb 23 2012), offset 1: Number of 8 X (n+1) 0..1 arrays with every 2 X
2 subblock having the same number of equal edges as its horizontal neighbors and a different number
from its vertical neighbors, and new values 0..1 introduced in row major order. Row 7 of A208085.
Formula section:
Conjectures from Colin Barker, Jun 28 2018:
G.f.: 18*x*(12 - 8*x - 17*x^2 + 7*x^3) / ((1 - x)*(1 + x)*(1 - 3*x + x^2)).
a(n) = (9/5)*2^(1-n)*(2^n*(15+2*(-1)^n) + (9-4*sqrt(5))*(3-sqrt(5))^n + (3+sqrt(5))^n*(9+4*sqrt(5))).

Formalization notes:
* An array is a function x : Fin 8 -> Fin (n + 1) -> Fin 2, x i j being the entry in row i and
  column j (8 rows and n + 1 columns).
* `edgeNum x i i' j j'` is the number of the four edges of the 2 X 2 subblock in rows i, i' and
  columns j, j' (the pairs (x(i,j), x(i,j')), (x(i',j), x(i',j')), (x(i,j), x(i',j)), (x(i,j'),
  x(i',j')) of neighboring entries) whose two entries are equal. `Cond` asks that this number be
  equal to that of the subblock to the right and different from that of the subblock below; both
  relations are symmetric, so these are the horizontal and vertical neighbors. With values 0..1,
  introducing the values in row major order means x(0,0) = 0. The proof transposes the array (its
  columns become the rows of the transfer). This reading reproduces the entry's data.
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..1 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 - x)(1 + x)(1 - 3x + x^2)) = 18x(12 - 8x - 17x^2 + 7x^3) in the formal power series ring
  over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the closed form in the reals for every n >= 1.
* Controls proved in the proof file: the definition gives 216, 504, 1206, 3096, 7992, 20862, 54504,
  142632, 373302, 977256 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a208089

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The number of equal edges of the 2 X 2 subblock of x in rows i, i' and columns j, j': the
neighbor pairs (x(i,j), x(i,j')), (x(i',j), x(i',j')), (x(i,j), x(i',j)), (x(i,j'), x(i',j')) with
equal values. -/
def edgeNum {R C K : ℕ} (x : Fin R → Fin C → Fin K) (i i' : Fin R) (j j' : Fin C) : ℕ :=
  (if x i j = x i j' then 1 else 0) + (if x i' j = x i' j' then 1 else 0) +
    (if x i j = x i' j then 1 else 0) + (if x i j' = x i' j' then 1 else 0)

/-- Every 2 X 2 subblock of x (rows i, i + 1, columns j, j + 1) has the same number of equal edges
as its horizontal neighbor subblock (columns j + 1, j + 2) and a different number from its vertical
neighbor subblock (rows i + 1, i + 2). -/
def Cond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  (∀ i i' : Fin R, ∀ j j' j'' : Fin C, i'.val = i.val + 1 → j'.val = j.val + 1 →
      j''.val = j'.val + 1 → edgeNum x i i' j j' = edgeNum x i i' j' j'') ∧
    ∀ i i' i'' : Fin R, ∀ j j' : Fin C, i'.val = i.val + 1 → i''.val = i'.val + 1 →
      j'.val = j.val + 1 → edgeNum x i i' j j' ≠ edgeNum x i' i'' j j'

instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance

/-- A208089(n): the number of 8 X (n+1) arrays with entries 0..1, x i j being the entry in row i and
column j, in which every 2 X 2 subblock has the same number of equal edges as its horizontal
neighbors and a different number from its vertical neighbors (`Cond`) and the values are introduced
in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin 8 → Fin (n + 1) → Fin 2)).filter
    (fun x => Cond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 + X) * (1 - 3 * X + X ^ 2)) = 18 * X * (12 - 8 * X - 17 * X ^ 2 + 7 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      9 / 5 * 2 ^ (1 - (n : ℤ)) * (2 ^ n * (15 + 2 * (-1) ^ n) +
        (9 - 4 * Real.sqrt 5) * (3 - Real.sqrt 5) ^ n +
        (3 + Real.sqrt 5) ^ n * (9 + 4 * Real.sqrt 5)) := by
  sorry

end OMA.S_oeis_a208089
