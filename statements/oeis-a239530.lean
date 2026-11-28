import Mathlib

/-!
# OEIS A239530: Barker's g.f. and closed form for (n+1) X 2 0..2 arrays, values introduced in row major order, no element equal to all horizontal neighbors or unequal to all vertical neighbors

Source: https://oeis.org/A239530 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A239530 (R. H. Hardin, Mar 21 2014), offset 1: Number of (n+1) X (1+1) 0..2 arrays with no
element equal to all horizontal neighbors or unequal to all vertical neighbors, and new values 0..2
introduced in row major order.
Formula section:
Conjectures from Colin Barker, Oct 26 2018:
G.f.: x*(1 - x) / ((1 - 3*x)*(1 + x - x^2)).
a(n) = (10*3^n + 2^(-n)*((-1+sqrt(5))^n*(-5+4*sqrt(5)) - (-1-sqrt(5))^n*(5+4*sqrt(5)))) / 55.

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 2 -> Fin 3, x i j being the entry in row i and
  column j.
* The horizontal neighbors of x(i,j) are x(i,j-1) and x(i,j+1), the vertical ones x(i-1,j) and
  x(i+1,j), when inside the array. `Cond` excludes an element equal to all its horizontal neighbors
  and an element unequal to all its vertical neighbors. With two columns every element has one
  horizontal neighbor, and with n + 1 >= 2 rows at least one vertical neighbor, so neither condition
  is vacuous for n >= 1.
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..2 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 - 3x)(1 + x - x^2)) = x(1 - x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  reals for every n >= 1, with the powers of 2 of negative exponent as integer powers (zpow).
* Controls proved in the proof file: the definition gives 1, 1, 6, 13, 47, 128, 405, 1181, 3598,
  10705 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a239530

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- No element of x is equal to all its horizontal neighbors or unequal to all its vertical
neighbors: the horizontal neighbors of x(i,j) are x(i,j') with j' = j - 1 or j' = j + 1, the
vertical ones x(i',j) with i' = i - 1 or i' = i + 1, inside the array. -/
def Cond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ¬ (∀ j' : Fin C, (j'.val + 1 = j.val ∨ j.val + 1 = j'.val) → x i j' = x i j) ∧
    ¬ (∀ i' : Fin R, (i'.val + 1 = i.val ∨ i.val + 1 = i'.val) → x i' j ≠ x i j)

instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance

/-- A239530(n): the number of (n+1) X 2 arrays with entries 0..2, x i j being the entry in row i and
column j, in which no element is equal to all its horizontal neighbors or unequal to all its
vertical neighbors (`Cond`) and the values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 3)).filter
    (fun x => Cond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - 3 * X) * (1 + X - X ^ 2)) = X * (1 - X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (10 * 3 ^ n + 2 ^ (-(n : ℤ)) * ((-1 + Real.sqrt 5) ^ n * (-5 + 4 * Real.sqrt 5) -
        (-1 - Real.sqrt 5) ^ n * (5 + 4 * Real.sqrt 5))) / 55 := by
  sorry

end OMA.S_oeis_a239530
