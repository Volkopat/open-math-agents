import Mathlib

/-!
# A223633: Number of n X 4 0..1 arrays with rows, antidiagonals and columns unimodal.

Source: https://oeis.org/A223633
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(11 + 22*x + 108*x^2 - 65*x^3 + 249*x^4 - 74*x^5 + 92*x^6 + 18*x^7 + 9*x^8 - 11*x^9 + x^10) / (1 - x)^9 (Colin Barker, Aug 21 2018).
* a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>11 (Colin Barker, Aug 21 2018).

Conventions:
* An n X 4 array is the list of its n rows from top to bottom; a row is a function
  `Fin 4 → Fin 2` giving its entries from left to right.
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms).
* Every row, read from left to right, is unimodal.
* Every column, read from top to bottom, is unimodal.
* Every antidiagonal is unimodal; the antidiagonals are the ones starting in the top row
  (`adiagFrom l j`) and the ones starting in the last column (`adiagFrom (l.drop i) 3`),
  each read with increasing row index (unimodality does not depend on the direction).
* This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a223633

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The antidiagonal through the cell in row 0 and column `j` of a list of rows, read downwards:
x(0, j), x(1, j - 1), ..., x(j, 0) (shorter when the rows run out). -/
def adiagFrom : List (Fin 4 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | r :: l, j => if h : j < 4 then (r ⟨j, h⟩ : ℕ) :: (if j = 0 then [] else adiagFrom l (j - 1)) else []

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 4 → Fin 2)) : Prop :=
  (∀ r ∈ l, Unimodal (List.ofFn fun j => (r j : ℕ))) ∧
  (∀ j : Fin 4, Unimodal (l.map fun r => (r j : ℕ))) ∧
  (∀ j < 4, Unimodal (adiagFrom l j)) ∧
  (∀ i, Unimodal (adiagFrom (l.drop i) 3))

/-- A223633(n): the number of such n X 4 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 4 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      11 + 22 * X + 108 * X ^ 2 - 65 * X ^ 3 + 249 * X ^ 4 - 74 * X ^ 5 + 92 * X ^ 6 + 18 * X ^ 7 + 9 * X ^ 8 - 11 * X ^ 9 + X ^ 10) ∧
    (∀ n > 11, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a223633
