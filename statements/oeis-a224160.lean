import Mathlib

/-!
# A224160: Number of 4 X n 0..1 arrays with diagonals and rows unimodal and antidiagonals nondecreasing.

Source: https://oeis.org/A224160
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(16 - 36*x - 115*x^2 + 589*x^3 - 950*x^4 + 519*x^5 + 442*x^6 - 977*x^7 + 817*x^8 - 436*x^9 + 178*x^10 - 55*x^11 + 9*x^12) / (1 - x)^9 (Colin Barker, Aug 28 2018).
* a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>13 (Colin Barker, Aug 28 2018).

Conventions:
* A 4 X n array is the list of its n columns from left to right; a column is a function
  `Fin 4 → Fin 2` giving its entries from top to bottom (entry `i` lies in row `i`).
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms).
* Every row, read from left to right, is unimodal.
* Every antidiagonal, read with increasing row index, is nondecreasing: x(i, j+1) <= x(i+1, j)
  (reading the antidiagonals the other way gives the same counts, by turning the array
  through 180 degrees).
* Every diagonal is unimodal; the diagonals are the ones starting in the first column
  (`diagFrom l i`) and the ones starting in the top row (`diagFrom (l.drop j) 0`), each read
  from left to right.
* This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a224160

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The diagonal through the cell in row `i` of the first column of a list of columns, read from
left to right: x(i, 0), x(i + 1, 1), x(i + 2, 2), ... (shorter when the rows or columns run out). -/
def diagFrom : List (Fin 4 → Fin 2) → ℕ → List ℕ
  | [], _ => []
  | c :: l, i => if h : i < 4 then (c ⟨i, h⟩ : ℕ) :: diagFrom l (i + 1) else []

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 4 → Fin 2)) : Prop :=
  (∀ i : Fin 4, Unimodal (l.map fun c => (c i : ℕ))) ∧
  l.IsChain (fun u v => (∀ i : Fin 3, v i.castSucc ≤ u i.succ)) ∧
  (∀ i < 4, Unimodal (diagFrom l i)) ∧
  (∀ j, Unimodal (diagFrom (l.drop j) 0))

/-- A224160(n): the number of such 4 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 4 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      16 - 36 * X - 115 * X ^ 2 + 589 * X ^ 3 - 950 * X ^ 4 + 519 * X ^ 5 + 442 * X ^ 6 - 977 * X ^ 7 + 817 * X ^ 8 - 436 * X ^ 9 + 178 * X ^ 10 - 55 * X ^ 11 + 9 * X ^ 12) ∧
    (∀ n > 13, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a224160
