import Mathlib

/-!
# A223840: Number of 4 X n 0..1 arrays with rows, diagonals and antidiagonals unimodal and columns nondecreasing.

Source: https://oeis.org/A223840
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(5 - 20*x + 44*x^2 - 72*x^3 + 89*x^4 - 70*x^5 + 28*x^6 - 4*x^7 + 4*x^8 - 4*x^9 + x^10) / (1 - x)^9 (Colin Barker, Aug 24 2018).
* a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>11 (Colin Barker, Aug 24 2018).

Conventions:
* A 4 X n array is the list of its n columns from left to right; a column is a function
  `Fin 4 → Fin 2` giving its entries from top to bottom (entry `i` lies in row `i`).
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms).
* Every column, read from top to bottom, is nondecreasing.
* Every row, read from left to right, is unimodal.
* Every antidiagonal is unimodal; the antidiagonals are the ones starting in the first column
  (`adiagFrom l i`) and the ones starting in the bottom row (`adiagFrom (l.drop j) 3`),
  each read from left to right (unimodality does not depend on the direction).
* Every diagonal is unimodal; the diagonals are the ones starting in the first column
  (`diagFrom l i`) and the ones starting in the top row (`diagFrom (l.drop j) 0`), each read
  from left to right.
* This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a223840

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The antidiagonal through the cell in row `i` of the first column of a list of columns, read
from left to right: x(i, 0), x(i - 1, 1), ..., x(0, i) (shorter when the columns run out). -/
def adiagFrom : List (Fin 4 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | c :: l, i => if h : i < 4 then (c ⟨i, h⟩ : ℕ) :: (if i = 0 then [] else adiagFrom l (i - 1)) else []

/-- The diagonal through the cell in row `i` of the first column of a list of columns, read from
left to right: x(i, 0), x(i + 1, 1), x(i + 2, 2), ... (shorter when the rows or columns run out). -/
def diagFrom : List (Fin 4 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | c :: l, i => if h : i < 4 then (c ⟨i, h⟩ : ℕ) :: diagFrom l (i + 1) else []

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 4 → Fin 2)) : Prop :=
  (∀ c ∈ l, ∀ i : Fin 3, c i.castSucc ≤ c i.succ) ∧
  (∀ i : Fin 4, Unimodal (l.map fun c => (c i : ℕ))) ∧
  (∀ i < 4, Unimodal (adiagFrom l i)) ∧
  (∀ j, Unimodal (adiagFrom (l.drop j) 3)) ∧
  (∀ i < 4, Unimodal (diagFrom l i)) ∧
  (∀ j, Unimodal (diagFrom (l.drop j) 0))

/-- A223840(n): the number of such 4 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 4 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      5 - 20 * X + 44 * X ^ 2 - 72 * X ^ 3 + 89 * X ^ 4 - 70 * X ^ 5 + 28 * X ^ 6 - 4 * X ^ 7 + 4 * X ^ 8 - 4 * X ^ 9 + X ^ 10) ∧
    (∀ n > 11, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a223840
