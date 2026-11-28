import Mathlib

/-!
# OEIS A223381: Barker's g.f. and closed form for n X 2 0..2 arrays, values introduced in row major order, all horizontally or vertically connected equal values in a straight line

Source: https://oeis.org/A223381 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A223381 (R. H. Hardin, Mar 19 2013), offset 1: Number of n X 2 0..2 arrays with all
horizontally or vertically connected equal values in a straight line, and new values 0..2 introduced
in row major order. Column 2 of A223387.
Formula section:
Conjectures from Colin Barker, Aug 20 2018:
G.f.: x*(1 - x)*(2 - 5*x) / (1 - 8*x + 10*x^2).
a(n) = (-(4-sqrt(6))^n*(-6+sqrt(6)) + (4+sqrt(6))^n*(6+sqrt(6))) / 40 for n>1.

Formalization notes:
* An array is a function x : Fin n -> Fin 2 -> Fin 3, x i j being the entry in row i and column j.
* `eqNbr x p q` says that the cells p and q are horizontal or vertical neighbors with equal values;
  two cells are connected when a chain of such steps joins them (`Relation.ReflTransGen`). `Cond`
  asks that any two connected cells lie in one row or in one column, which is the same as every
  connected group of equal values lying in a single row or a single column (a straight line); a set
  of cells in which any two share a row or a column lies in one row or one column. The filter in `a`
  uses classical decidability of `Cond`. The proof file shows that `Cond` is equivalent to: no
  element has both an equal horizontal neighbor and an equal vertical neighbor; this reading
  reproduces the entry's data.
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..2 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - 8x + 10x^2) = x(1 - x)(2 - 5x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  reals for every n >= 2.
* Controls proved in the proof file: the definition gives 2, 9, 57, 366, 2358, 15204, 98052, 632376,
  4078488, 26304144 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a223381

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The cells p and q of x are horizontal or vertical neighbors holding equal values. -/
def eqNbr {R C K : ℕ} (x : Fin R → Fin C → Fin K) (p q : Fin R × Fin C) : Prop :=
  ((p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
    (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))) ∧ x p.1 p.2 = x q.1 q.2

/-- All horizontally or vertically connected equal values of x lie in a straight line: two cells
joined by a chain of horizontally or vertically neighboring equal values lie in one row or in one
column. -/
def Cond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ p q : Fin R × Fin C, Relation.ReflTransGen (eqNbr x) p q → p.1 = q.1 ∨ p.2 = q.2

noncomputable instance {R C K : ℕ} : DecidablePred (@Cond R C K) := Classical.decPred _

/-- A223381(n): the number of n X 2 arrays with entries 0..2, x i j being the entry in row i and
column j, in which all horizontally or vertically connected equal values lie in a straight line
(`Cond`) and the values are introduced in row major order. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 2 → Fin 3)).filter
    (fun x => Cond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 8 * X + 10 * X ^ 2) = X * (1 - X) * (2 - 5 * X) ∧
    ∀ n : ℕ, 1 < n → (a n : ℝ) =
      (-(4 - Real.sqrt 6) ^ n * (-6 + Real.sqrt 6) + (4 + Real.sqrt 6) ^ n * (6 + Real.sqrt 6)) /
        40 := by
  sorry

end OMA.S_oeis_a223381
