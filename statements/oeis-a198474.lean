import Mathlib

/-!
# OEIS A198474: Barker's g.f. and closed form for 2n X 2 0..2 arrays, values introduced in row major order, each element equal to an odd number of horizontal and vertical neighbors

Source: https://oeis.org/A198474 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A198474 (R. H. Hardin, Oct 25 2011), offset 1: Number of 2n X 2 0..2 arrays with values 0..2
introduced in row major order and each element equal to an odd number of horizontal and vertical
neighbors. Column 1 of A198477.
Formula section:
Conjectures from Colin Barker, Mar 02 2018:
G.f.: 2*x*(1 - 3*x) / (1 - 9*x + 16*x^2).
a(n) = (2^(-4-n)*((9-sqrt(17))^n*(-5+3*sqrt(17)) + (9+sqrt(17))^n*(5+3*sqrt(17)))) / sqrt(17).

Formalization notes:
* An array is a function x : Fin (2 * n) -> Fin 2 -> Fin 3, x i j being the entry in row i and
  column j.
* For an element x(i,j), `eqNbrs x i j` counts its horizontal neighbors x(i,j-1), x(i,j+1) and
  vertical neighbors x(i-1,j), x(i+1,j) that lie inside the array and have the value x(i,j); every
  element must have an odd count (`Cond`).
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..2 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - 9x + 16x^2) = 2x(1 - 3x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  reals for every n >= 1, with the powers of 2 of negative exponent as integer powers (zpow).
* Controls proved in the proof file: the definition gives 2, 12, 76, 492, 3212, 21036, 137932,
  904812, 5936396, 38950572 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a198474

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The number of horizontal and vertical neighbors of x(i,j) whose value is equal to x(i,j):
the entries x(i,j') with j' = j - 1 or j' = j + 1 and the entries x(i',j) with i' = i - 1 or
i' = i + 1, inside the array. -/
def eqNbrs {R C K : ℕ} (x : Fin R → Fin C → Fin K) (i : Fin R) (j : Fin C) : ℕ :=
  ((univ : Finset (Fin C)).filter
      (fun j' => (j'.val + 1 = j.val ∨ j.val + 1 = j'.val) ∧ x i j' = x i j)).card +
    ((univ : Finset (Fin R)).filter
      (fun i' => (i'.val + 1 = i.val ∨ i.val + 1 = i'.val) ∧ x i' j = x i j)).card

/-- Every element of x is equal to an odd number of its horizontal and vertical neighbors. -/
def Cond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, eqNbrs x i j % 2 = 1

instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance

/-- A198474(n): the number of 2n X 2 arrays with entries 0..2, x i j being the entry in row i and
column j, in which every element is equal to an odd number of its horizontal and vertical neighbors
(`Cond`) and the values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (2 * n) → Fin 2 → Fin 3)).filter
    (fun x => Cond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 9 * X + 16 * X ^ 2) = 2 * X * (1 - 3 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-4 - (n : ℤ)) * ((9 - Real.sqrt 17) ^ n * (-5 + 3 * Real.sqrt 17) +
        (9 + Real.sqrt 17) ^ n * (5 + 3 * Real.sqrt 17))) / Real.sqrt 17 := by
  sorry

end OMA.S_oeis_a198474
