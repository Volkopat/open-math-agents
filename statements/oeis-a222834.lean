import Mathlib

/-!
# OEIS A222834: Barker's g.f. and closed form for n X 4 0..3 arrays, values introduced in row major order, no element equal to another at city block distance exactly two

Source: https://oeis.org/A222834 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A222834 (R. H. Hardin, Mar 06 2013), offset 1: Number of n X 4 0..3 arrays with no element
equal to another at a city block distance of exactly two, and new values 0..3 introduced in row
major order. Column 4 of A222838.
Formula section:
Conjectures from Colin Barker, Aug 16 2018:
G.f.: x*(7 + 82*x + 10*x^2 - 17*x^3) / ((1 + x)*(1 - 3*x + x^2)).
a(n) = (3/5)*2^(2-n)*((-1)^n*2^(2+n) + (3-sqrt(5))^(1+n) + (3+sqrt(5))^(1+n)) for n>1.

Formalization notes:
* An array is a function x : Fin n -> Fin 4 -> Fin 4, x i j being the entry in row i and column j.
* The city block distance of positions (i,j) and (i',j') is |i - i'| + |j - j'|, written with
  truncated subtraction as (i - i') + (i' - i) + ((j - j') + (j' - j)); `Cond` asks that x(i,j)
  differ from x(i',j') whenever this distance is exactly 2.
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..3 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 + x)(1 - 3x + x^2)) = x(7 + 82x + 10x^2 - 17x^3) in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed
  form in the reals for every n >= 2.
* Controls proved in the proof file: the definition gives 7, 96, 216, 600, 1536, 4056, 10584, 27744,
  72600, 190104 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a222834

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- No element of x is equal to another at city block distance exactly two: whenever
|i - i'| + |j - j'| = 2 (written with truncated subtraction), x(i,j) differs from x(i',j'). -/
def Cond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i i' : Fin R, ∀ j j' : Fin C,
    (i.val - i'.val) + (i'.val - i.val) + ((j.val - j'.val) + (j'.val - j.val)) = 2 →
      x i j ≠ x i' j'

instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance

/-- A222834(n): the number of n X 4 arrays with entries 0..3, x i j being the entry in row i and
column j, in which no element is equal to another at a city block distance of exactly two (`Cond`)
and the values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 4 → Fin 4)).filter
    (fun x => Cond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 + X) * (1 - 3 * X + X ^ 2)) = X * (7 + 82 * X + 10 * X ^ 2 - 17 * X ^ 3) ∧
    ∀ n : ℕ, 1 < n → (a n : ℝ) =
      3 / 5 * 2 ^ (2 - (n : ℤ)) * ((-1) ^ n * 2 ^ (2 + n) + (3 - Real.sqrt 5) ^ (1 + n) +
        (3 + Real.sqrt 5) ^ (1 + n)) := by
  sorry

end OMA.S_oeis_a222834
