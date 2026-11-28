import Mathlib

/-!
# OEIS A206687: Barker's g.f. and closed form for n X 2 0..3 arrays, values introduced in row major order, no element equal to another within two positions in the same row or column

Source: https://oeis.org/A206687 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A206687 (R. H. Hardin, Feb 11 2012), offset 1: Number of n X 2 0..3 arrays with no element
equal to another within two positions in the same row or column, and new values 0..3 introduced in
row major order. Column 2 of A206692.
Formula section:
Conjectures from Colin Barker, Feb 23 2018:
G.f.: x*(1 - x)*(1 + x)*(1 + 2*x) / (1 - 2*x - 4*x^2).
a(n) = ((1-sqrt(5))^n*(-5+3*sqrt(5)) + (1+sqrt(5))^n*(5+3*sqrt(5))) / (16*sqrt(5)) for n>2.

Formalization notes:
* An array is a function x : Fin n -> Fin 2 -> Fin 4, x i j being the entry in row i and column j.
* Two distinct positions are within two positions in the same row when they lie in one row at most
  two columns apart, and in the same column when they lie in one column at most two rows apart;
  `Cond` asks that the entries at any two such positions differ.
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..3 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - 2x - 4x^2) = x(1 - x)(1 + x)(1 + 2x) in the formal power series ring over the rationals,
  with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in
  the reals for every n >= 3.
* Controls proved in the proof file: the definition gives 1, 4, 11, 36, 116, 376, 1216, 3936, 12736,
  41216 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a206687

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- No element of x is equal to another within two positions in the same row or column: x(i,j)
differs from x(i',j') whenever the two positions are distinct and lie in the same row at most two
columns apart or in the same column at most two rows apart. -/
def Cond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i i' : Fin R, ∀ j j' : Fin C,
    ((i = i' ∧ j ≠ j' ∧ j.val ≤ j'.val + 2 ∧ j'.val ≤ j.val + 2) ∨
      (j = j' ∧ i ≠ i' ∧ i.val ≤ i'.val + 2 ∧ i'.val ≤ i.val + 2)) → x i j ≠ x i' j'

instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance

/-- A206687(n): the number of n X 2 arrays with entries 0..3, x i j being the entry in row i and
column j, in which no element is equal to another within two positions in the same row or column
(`Cond`) and the values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 2 → Fin 4)).filter
    (fun x => Cond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 2 * X - 4 * X ^ 2) = X * (1 - X) * (1 + X) * (1 + 2 * X) ∧
    ∀ n : ℕ, 2 < n → (a n : ℝ) =
      ((1 - Real.sqrt 5) ^ n * (-5 + 3 * Real.sqrt 5) +
        (1 + Real.sqrt 5) ^ n * (5 + 3 * Real.sqrt 5)) / (16 * Real.sqrt 5) := by
  sorry

end OMA.S_oeis_a206687
