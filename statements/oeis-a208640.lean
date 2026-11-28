import Mathlib

/-!
# OEIS A208640: Barker's g.f. and closed form for 5 X n 0..1 arrays, values introduced in row major order, no element equal to more than one of its leftward, upward or right-upward neighbors

Source: https://oeis.org/A208640 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @ppleskov.

Entry A208640 (R. H. Hardin, Feb 29 2012), offset 1: Number of 5 X n 0..1 arrays with new values
0..1 introduced in row major order and no element equal to more than one of its immediate leftward
or upward or right-upward antidiagonal neighbors.
Formula section:
Conjectures from Colin Barker, Jul 05 2018:
G.f.: x*(16 - 7*x - 26*x^2 + 8*x^3 + 16*x^4 - 2*x^5 - 4*x^6) / ((1 - x)^4*(1 - 2*x)).
a(n) = -84 + 63*2^n - (191*n)/6 - 4*n^2 - n^3/6 for n>2.

Formalization notes:
* An array is a function x : Fin 5 -> Fin n -> Fin 2, x i j being the entry in row i and column j
  (rows numbered from the top, columns from the left).
* For an element x(i,j), `eqNbrs x i j` counts its immediate leftward neighbor x(i,j-1), its
  upward neighbor x(i-1,j) and its right-upward antidiagonal neighbor x(i-1,j+1) that lie inside
  the array and have the value x(i,j); `Cond` asks that this count is at most 1 for every element.
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry (for 0..1 arrays:
  the first entry x(0,0) is 0).
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 - x)^4 (1 - 2x)) = x (16 - 7x - 26x^2 + 8x^3 + 16x^4 - 2x^5 - 4x^6) in the formal power
  series ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term
  is 0), and the closed form a(n) = -84 + 63*2^n - 191n/6 - 4n^2 - n^3/6 over the rationals for
  every n > 2.
* A direct enumeration of this definition gives 16, 89, 284, 722, 1652 for n = 1..5, the entry's
  data.
-/

namespace OMA.S_oeis_a208640

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The number of neighbors of x(i,j) among its leftward neighbor x(i,j-1), its upward neighbor
x(i-1,j) and its right-upward antidiagonal neighbor x(i-1,j+1), inside the array, whose value is
equal to x(i,j). -/
def eqNbrs {R C K : ℕ} (x : Fin R → Fin C → Fin K) (i : Fin R) (j : Fin C) : ℕ :=
  ((univ : Finset (Fin R × Fin C)).filter (fun p =>
    ((p.1 = i ∧ p.2.val + 1 = j.val) ∨ (p.1.val + 1 = i.val ∧ p.2 = j) ∨
      (p.1.val + 1 = i.val ∧ p.2.val = j.val + 1)) ∧ x p.1 p.2 = x i j)).card

/-- No element of x is equal to more than one of its leftward, upward and right-upward
antidiagonal neighbors. -/
def Cond {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, eqNbrs x i j ≤ 1

instance {R C K : ℕ} : DecidablePred (@Cond R C K) := fun x => by
  unfold Cond; infer_instance

/-- A208640(n): the number of 5 X n arrays with entries 0..1 with the values introduced in row
major order and no element equal to more than one of its leftward, upward and right-upward
antidiagonal neighbors. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin 5 → Fin n → Fin 2)).filter (fun x => Cond x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 4 * (1 - 2 * X)) =
      X * (16 - 7 * X - 26 * X ^ 2 + 8 * X ^ 3 + 16 * X ^ 4 - 2 * X ^ 5 - 4 * X ^ 6) ∧
    ∀ n : ℕ, 2 < n → (a n : ℚ) = -84 + 63 * 2 ^ n - 191 * n / 6 - 4 * n ^ 2 - n ^ 3 / 6 := by
  sorry

end OMA.S_oeis_a208640
