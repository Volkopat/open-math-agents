import Mathlib

/-!
# OEIS A275229: Barker's conjectures for 3 X n 0..2 arrays with no element equal to any value at offset (-2,-1) (-2,1) or (-1,0), new values introduced in order 0..2

Source: https://oeis.org/A275229 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @ppleskov.

Entry A275229 (R. H. Hardin, Jul 20 2016), offset 1: Number of 3 X n 0..2 arrays with no element equal to
any value at offset (-2,-1) (-2,1) or (-1,0) and new values introduced in order 0..2.
Formula section:
Conjectures from Colin Barker, Feb 02 2019:
G.f.: x*(2 - 3*x) / (1 - 7*x + 8*x^2).
a(n) = (2^(-4-n) * ((7-sqrt(17))^n * (-11+3*sqrt(17)) + (7+sqrt(17))^n*(11+3*sqrt(17)))) / sqrt(17).

Formalization notes:
* An array is a function x : Fin 3 -> Fin n -> Fin 3, x i j being the entry in row i and
  column j (rows numbered from the top, columns from the left).
* An offset (di,dj) refers, for the element x(i,j), to the element x(i+di, j+dj) (row offset first,
  column offset second); `Cond` asks that for every element and each of the offsets (-2,-1) (-2,1) or (-1,0) the
  element at that offset, when it lies inside the array, has a different value.
* New values introduced in order 0..2 (`RowMajorNew`): reading the array row by row, each row from
  left to right, every value smaller than an entry occurs before that entry (so the first entry is
  0 and each array stands for one coloring up to renaming of the colors; not every value of 0..2
  has to occur).
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - 7x + 8x^2) = x (2 - 3x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  reals for every n >= 1, with the power of 2 of negative exponent as an integer power (zpow).
* A direct enumeration of this definition gives 2, 11, 61, 339 for n = 1..4, the entry's data.
-/

namespace OMA.S_oeis_a275229

open PowerSeries Finset

/-- No element of x is equal to the value at any of the given offsets: for every element x(i,j)
and every offset (di,dj) in `offs` such that (i+di, j+dj) lies inside the array,
x(i+di, j+dj) differs from x(i,j). -/
def Cond {R C : ℕ} (offs : List (ℤ × ℤ)) (x : Fin R → Fin C → Fin 3) : Prop :=
  ∀ (i i' : Fin R) (j j' : Fin C), ((i' : ℤ) - i, (j' : ℤ) - j) ∈ offs → x i' j' ≠ x i j

instance {R C : ℕ} (offs : List (ℤ × ℤ)) : DecidablePred (@Cond R C offs) := fun x => by
  unfold Cond; infer_instance

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The offsets of the entry. -/
def offs : List (ℤ × ℤ) := [(-2, -1), (-2, 1), (-1, 0)]

/-- A275229(n): the number of 3 X n arrays with entries 0..2, x i j being the entry in row i and
column j, with no element equal to the value at any of the offsets and the values introduced in
row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin 3 → Fin n → Fin 3)).filter (fun x => Cond offs x ∧ RowMajorNew x)).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 7 * X + 8 * X ^ 2) =
      X * (2 - 3 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (2 ^ (-4 - (n : ℤ)) * ((7 - Real.sqrt 17) ^ n * (-11 + 3 * Real.sqrt 17) +
      (7 + Real.sqrt 17) ^ n * (11 + 3 * Real.sqrt 17))) / Real.sqrt 17 := by
  sorry

end OMA.S_oeis_a275229
