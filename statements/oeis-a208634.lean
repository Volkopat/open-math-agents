import Mathlib

/-!
# OEIS A208634: Barker's generating function and closed form

Source: https://oeis.org/A208634 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A208634 (R. H. Hardin, Feb 29 2012), offset 1: Number of n X 5 0..1 arrays with new values 0..1 introduced in row major order and no element equal to more than one of its immediate leftward or upward or right-upward antidiagonal neighbors.
Data: 16, 47, 150, 494, 1652, 5572, ...
Formula section:
Empirical: a(n) = 6*a(n-1) - 10*a(n-2) + 4*a(n-3).
Conjectures from Colin Barker, Jul 05 2018: (Start)
G.f.: x*(16 - 49*x + 28*x^2) / ((1 - 2*x)*(1 - 4*x + 2*x^2)).
a(n) = (3*2^(1+n) + (11-2*sqrt(2))*(2-sqrt(2))^n + (2+sqrt(2))^n*(11+2*sqrt(2))) / 4.
(End)

Formalization notes:
* An array is a function x : Fin n → Fin 5 → Fin 2, x i j being the entry in row i (top to
  bottom) and column j (left to right), with values 0..1.
* New values introduced in row major order (`RowMajorNew`, the definition of the merged sibling
  statements of R. H. Hardin's row major order arrays, e.g. A205220): reading the array row by row,
  each row from left to right, every value smaller than an entry occurs before that entry.
  Equivalently the first entry is 0 and every entry is at most 1 + the largest entry before it, so
  that each array stands for one pattern of equal entries. Not every value has to occur.
* The immediate leftward neighbor of x(i,j) is x(i,j-1), its upward neighbor x(i-1,j) and its
  right-upward antidiagonal neighbor x(i-1,j+1), when they lie inside the array. `eqNbrs x i j`
  counts those of them equal to x(i,j), each neighbor being unique when it exists, and the
  condition is that no element is equal to more than one of them: `eqNbrs x i j ≤ 1`.
* With these readings the definition reproduces the entry's data: checked by brute force for
  n = 1, 2, 3 and by a transfer-matrix evaluation of this exact definition for every listed term.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) ((1 - 2X)(1 - 4X + 2X ^ 2)) = N(x) in
  Q[[x]], which is equivalent to the quotient form because the denominator has constant term 1.
* The entry gives no range for the closed form; it is stated in the reals for every n >= 1, the range of the sequence (offset 1).
* `main` is the conjunction of Barker's two conjectures; Hardin's empirical recurrence is not part
  of it.
-/

namespace OMA.S_oeis_a208634

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The number of the immediate leftward neighbor x(i,j-1), upward neighbor x(i-1,j) and
right-upward antidiagonal neighbor x(i-1,j+1) of the entry x(i,j), among those inside the array,
that are equal to x(i,j). -/
def eqNbrs {R C K : ℕ} (x : Fin R → Fin C → Fin K) (i : Fin R) (j : Fin C) : ℕ :=
  (if ∃ j' : Fin C, j'.val + 1 = j.val ∧ x i j' = x i j then 1 else 0) +
  (if ∃ i' : Fin R, i'.val + 1 = i.val ∧ x i' j = x i j then 1 else 0) +
  (if ∃ i' : Fin R, ∃ j' : Fin C, i'.val + 1 = i.val ∧ j'.val = j.val + 1 ∧ x i' j' = x i j then 1 else 0)

/-- No element is equal to more than one of its immediate leftward, upward or right-upward
antidiagonal neighbors. -/
def NbrCond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, eqNbrs x i j ≤ 1

instance {R C K : ℕ} : DecidablePred (@NbrCond R C K) := fun x => by
  unfold NbrCond; infer_instance

/-- A208634(n): the number of n X 5 arrays with entries 0..1, new values introduced in row major
order, and no element equal to more than one of its immediate leftward, upward or right-upward
antidiagonal neighbors. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 5 → Fin 2)).filter (fun x => NbrCond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - 2 * X) * (1 - 4 * X + 2 * X ^ 2)) =
      X * (16 - 49 * X + 28 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (3 * 2 ^ (1 + n) + (11 - 2 * Real.sqrt 2) * (2 - Real.sqrt 2) ^ n + (2 + Real.sqrt 2) ^ n * (11 + 2 * Real.sqrt 2)) / 4 := by
  sorry

end OMA.S_oeis_a208634
