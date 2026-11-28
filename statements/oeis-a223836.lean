import Mathlib

/-!
# A223836: Number of n X 6 0..1 arrays with rows, diagonals and antidiagonals unimodal and columns nondecreasing.

Source: https://oeis.org/A223836
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(22 - 6*x - 71*x^2 + 103*x^3 + 35*x^4 - 77*x^5 + 10*x^6 + 22*x^7 - 4*x^8 - 2*x^9) / (1 - x)^7 (Colin Barker, Aug 23 2018).
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>10 (Colin Barker, Aug 23 2018).

Conventions:
* An n X 6 array is the list of its n rows from top to bottom; a row is a function
  `Fin 6 → Fin 2` giving its entries from left to right.
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms).
* Every row, read from left to right, is unimodal.
* Every column, read from top to bottom, is nondecreasing.
* Every antidiagonal is unimodal; the antidiagonals are the ones starting in the top row
  (`adiagFrom l j`) and the ones starting in the last column (`adiagFrom (l.drop i) 5`),
  each read with increasing row index (unimodality does not depend on the direction).
* Every diagonal is unimodal; the diagonals are the ones starting in the top row
  (`diagFrom l j`) and the ones starting in the first column (`diagFrom (l.drop i) 0`),
  each read with increasing row index.
* This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a223836

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The antidiagonal through the cell in row 0 and column `j` of a list of rows, read downwards:
x(0, j), x(1, j - 1), ..., x(j, 0) (shorter when the rows run out). -/
def adiagFrom : List (Fin 6 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | r :: l, j => if h : j < 6 then (r ⟨j, h⟩ : ℕ) :: (if j = 0 then [] else adiagFrom l (j - 1)) else []

/-- The diagonal through the cell in row 0 and column `j` of a list of rows, read downwards:
x(0, j), x(1, j + 1), x(2, j + 2), ... (shorter when the rows or the columns run out). -/
def diagFrom : List (Fin 6 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | r :: l, j => if h : j < 6 then (r ⟨j, h⟩ : ℕ) :: diagFrom l (j + 1) else []

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 6 → Fin 2)) : Prop :=
  (∀ r ∈ l, Unimodal (List.ofFn fun j => (r j : ℕ))) ∧
  l.IsChain (fun r s => ∀ j : Fin 6, r j ≤ s j) ∧
  (∀ j < 6, Unimodal (adiagFrom l j)) ∧
  (∀ i, Unimodal (adiagFrom (l.drop i) 5)) ∧
  (∀ j < 6, Unimodal (diagFrom l j)) ∧
  (∀ i, Unimodal (diagFrom (l.drop i) 0))

/-- A223836(n): the number of such n X 6 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 6 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      22 - 6 * X - 71 * X ^ 2 + 103 * X ^ 3 + 35 * X ^ 4 - 77 * X ^ 5 + 10 * X ^ 6 + 22 * X ^ 7 - 4 * X ^ 8 - 2 * X ^ 9) ∧
    (∀ n > 10, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a223836
