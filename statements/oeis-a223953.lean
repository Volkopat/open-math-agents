import Mathlib

/-!
# A223953: Number of 6 X n 0..1 arrays with diagonals and antidiagonals unimodal and rows nondecreasing.

Source: https://oeis.org/A223953
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(64 + 281*x - 1735*x^2 + 2546*x^3 - 335*x^4 - 1862*x^5 + 787*x^6 + 767*x^7 - 426*x^8 - 148*x^9 + 93*x^10) / (1 - x)^7 (Colin Barker, Aug 24 2018).
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>11 (Colin Barker, Aug 24 2018).

Conventions:
* A 6 X n array is the list of its n columns from left to right; a column is a function
  `Fin 6 → Fin 2` giving its entries from top to bottom (entry `i` lies in row `i`).
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms).
* Every row, read from left to right, is nondecreasing: x(i, j) <= x(i, j+1).
* Every antidiagonal is unimodal; the antidiagonals are the ones starting in the first column
  (`adiagFrom l i`) and the ones starting in the bottom row (`adiagFrom (l.drop j) 5`),
  each read from left to right (unimodality does not depend on the direction).
* Every diagonal is unimodal; the diagonals are the ones starting in the first column
  (`diagFrom l i`) and the ones starting in the top row (`diagFrom (l.drop j) 0`), each read
  from left to right.
* This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a223953

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The antidiagonal through the cell in row `i` of the first column of a list of columns, read
from left to right: x(i, 0), x(i - 1, 1), ..., x(0, i) (shorter when the columns run out). -/
def adiagFrom : List (Fin 6 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | c :: l, i => if h : i < 6 then (c ⟨i, h⟩ : ℕ) :: (if i = 0 then [] else adiagFrom l (i - 1)) else []

/-- The diagonal through the cell in row `i` of the first column of a list of columns, read from
left to right: x(i, 0), x(i + 1, 1), x(i + 2, 2), ... (shorter when the rows or columns run out). -/
def diagFrom : List (Fin 6 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | c :: l, i => if h : i < 6 then (c ⟨i, h⟩ : ℕ) :: diagFrom l (i + 1) else []

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 6 → Fin 2)) : Prop :=
  l.IsChain (fun u v => (∀ i : Fin 6, u i ≤ v i)) ∧
  (∀ i < 6, Unimodal (adiagFrom l i)) ∧
  (∀ j, Unimodal (adiagFrom (l.drop j) 5)) ∧
  (∀ i < 6, Unimodal (diagFrom l i)) ∧
  (∀ j, Unimodal (diagFrom (l.drop j) 0))

/-- A223953(n): the number of such 6 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 6 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      64 + 281 * X - 1735 * X ^ 2 + 2546 * X ^ 3 - 335 * X ^ 4 - 1862 * X ^ 5 + 787 * X ^ 6 + 767 * X ^ 7 - 426 * X ^ 8 - 148 * X ^ 9 + 93 * X ^ 10) ∧
    (∀ n > 11, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a223953
