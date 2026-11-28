import Mathlib

/-!
# OEIS A214160: Barker's g.f. and closed form for n X 3 0..5 arrays, values introduced in row major order, colorings circular in the 3 direction

Source: https://oeis.org/A214160 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A214160 (R. H. Hardin, Jul 05 2012), offset 1: Number of 0..5 colorings of an n X 3 array
circular in the 3 direction with new values 0..5 introduced in row major order. Column 2 of A214166.
Formula section:
Conjectures from Colin Barker, Jul 22 2018:
G.f.: x*(1 - 66*x + 335*x^2) / ((1 - 2*x)*(1 - 11*x)*(1 - 71*x)).
a(n) = (781*2^n + 213*11^n + 11*71^n)/4686.

Formalization notes:
* An array is a function x : Fin n -> Fin 3 -> Fin 6, x i j being the entry in row i and column j.
* A coloring is an array with adjacent entries of different colors; the array is circular in the 3
  direction, so in row i the entries x(i,0), x(i,1), x(i,2) are pairwise adjacent (j and j + 1 mod
  3), and x(i,j) is adjacent to x(i+1,j) (`Proper`).
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..5 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 - 2x)(1 - 11x)(1 - 71x)) = x(1 - 66x + 335x^2) in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed
  form in the reals for every n >= 1.
* Controls proved in the proof file: the definition gives 1, 18, 902, 60320, 4242606, 300785428,
  21350933122, 1515863103360, 107625695720486, 7641417965382188 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a214160

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- x is a coloring of the array circular in the 3 direction: horizontally adjacent entries x(i,j)
and x(i,j'), j' = j + 1 mod 3 (so x(i,2) and x(i,0) are adjacent too), and vertically adjacent
entries x(i,j), x(i+1,j) have different colors. -/
def Proper {R K : ℕ} (x : Fin R → Fin 3 → Fin K) : Prop :=
  (∀ i, ∀ j j' : Fin 3, j'.val = (j.val + 1) % 3 → x i j ≠ x i j') ∧
    ∀ i i' : Fin R, i'.val = i.val + 1 → ∀ j, x i j ≠ x i' j

instance {R K : ℕ} : DecidablePred (@Proper R K) := fun x => by
  unfold Proper; infer_instance

/-- A214160(n): the number of n X 3 arrays with entries 0..5, x i j being the entry in row i and
column j, in which adjacent entries have different colors, the rows being circular (`Proper`) and
the values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 3 → Fin 6)).filter
    (fun x => Proper x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - 2 * X) * (1 - 11 * X) * (1 - 71 * X)) = X * (1 - 66 * X + 335 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (781 * 2 ^ n + 213 * 11 ^ n + 11 * 71 ^ n) / 4686 := by
  sorry

end OMA.S_oeis_a214160
