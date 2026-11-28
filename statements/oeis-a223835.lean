import Mathlib

/-!
# A223835: Number of n X 5 0..1 arrays with rows, diagonals and antidiagonals unimodal and columns nondecreasing.

Source: https://oeis.org/A223835
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(16 - 10*x - 21*x^2 + 36*x^3 + 9*x^4 - 18*x^5 + 2*x^6 + 2*x^7) / (1 - x)^6 (Colin Barker, Aug 23 2018).
* a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - 1*a(n-6) for n>8 (Colin Barker, Aug 23 2018).

Conventions:
* An n X 5 array is the list of its n rows from top to bottom; a row is a function
  `Fin 5 → Fin 2` giving its entries from left to right.
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms).
* Every row, read from left to right, is unimodal.
* Every column, read from top to bottom, is nondecreasing.
* Every antidiagonal is unimodal; the antidiagonals are the ones starting in the top row
  (`adiagFrom l j`) and the ones starting in the last column (`adiagFrom (l.drop i) 4`),
  each read with increasing row index (unimodality does not depend on the direction).
* Every diagonal is unimodal; the diagonals are the ones starting in the top row
  (`diagFrom l j`) and the ones starting in the first column (`diagFrom (l.drop i) 0`),
  each read with increasing row index.
* This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a223835

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The antidiagonal through the cell in row 0 and column `j` of a list of rows, read downwards:
x(0, j), x(1, j - 1), ..., x(j, 0) (shorter when the rows run out). -/
def adiagFrom : List (Fin 5 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | r :: l, j => if h : j < 5 then (r ⟨j, h⟩ : ℕ) :: (if j = 0 then [] else adiagFrom l (j - 1)) else []

/-- The diagonal through the cell in row 0 and column `j` of a list of rows, read downwards:
x(0, j), x(1, j + 1), x(2, j + 2), ... (shorter when the rows or the columns run out). -/
def diagFrom : List (Fin 5 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | r :: l, j => if h : j < 5 then (r ⟨j, h⟩ : ℕ) :: diagFrom l (j + 1) else []

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 5 → Fin 2)) : Prop :=
  (∀ r ∈ l, Unimodal (List.ofFn fun j => (r j : ℕ))) ∧
  l.IsChain (fun r s => ∀ j : Fin 5, r j ≤ s j) ∧
  (∀ j < 5, Unimodal (adiagFrom l j)) ∧
  (∀ i, Unimodal (adiagFrom (l.drop i) 4)) ∧
  (∀ j < 5, Unimodal (diagFrom l j)) ∧
  (∀ i, Unimodal (diagFrom (l.drop i) 0))

/-- A223835(n): the number of such n X 5 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 5 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 6 =
      16 - 10 * X - 21 * X ^ 2 + 36 * X ^ 3 + 9 * X ^ 4 - 18 * X ^ 5 + 2 * X ^ 6 + 2 * X ^ 7) ∧
    (∀ n > 8, (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - 1 * a (n - 6)) := by
  sorry

end OMA.S_oeis_a223835
