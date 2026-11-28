import Mathlib

/-!
# A223632: Number of n X 3 0..1 arrays with rows, antidiagonals and columns unimodal.

Source: https://oeis.org/A223632
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(7 + 33*x^2 - 18*x^3 + 29*x^4 - 6*x^5 + x^6) / (1 - x)^7 (Colin Barker, Aug 21 2018).
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7 (Colin Barker, Aug 21 2018).

Conventions:
* An n X 3 array is the list of its n rows from top to bottom; a row is a function
  `Fin 3 → Fin 2` giving its entries from left to right.
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms).
* Every row, read from left to right, is unimodal.
* Every column, read from top to bottom, is unimodal.
* Every antidiagonal is unimodal; the antidiagonals are the ones starting in the top row
  (`adiagFrom l j`) and the ones starting in the last column (`adiagFrom (l.drop i) 2`),
  each read with increasing row index (unimodality does not depend on the direction).
* This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a223632

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The antidiagonal through the cell in row 0 and column `j` of a list of rows, read downwards:
x(0, j), x(1, j - 1), ..., x(j, 0) (shorter when the rows run out). -/
def adiagFrom : List (Fin 3 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | r :: l, j => if h : j < 3 then (r ⟨j, h⟩ : ℕ) :: (if j = 0 then [] else adiagFrom l (j - 1)) else []

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 3 → Fin 2)) : Prop :=
  (∀ r ∈ l, Unimodal (List.ofFn fun j => (r j : ℕ))) ∧
  (∀ j : Fin 3, Unimodal (l.map fun r => (r j : ℕ))) ∧
  (∀ j < 3, Unimodal (adiagFrom l j)) ∧
  (∀ i, Unimodal (adiagFrom (l.drop i) 2))

/-- A223632(n): the number of such n X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      7 + 33 * X ^ 2 - 18 * X ^ 3 + 29 * X ^ 4 - 6 * X ^ 5 + X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a223632
