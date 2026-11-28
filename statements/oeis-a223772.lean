import Mathlib

/-!
# A223772: Number of n X 3 0..1 arrays with rows and columns unimodal and antidiagonals nondecreasing.

Source: https://oeis.org/A223772
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(7 - 21*x + 29*x^2 - 23*x^3 + 14*x^4 - 7*x^5 + 2*x^6) / (1 - x)^7 (Colin Barker, Aug 23 2018).
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7 (Colin Barker, Aug 23 2018).

Conventions:
* An n X 3 array is the list of its n rows from top to bottom; a row is a function
  `Fin 3 → Fin 2` giving its entries from left to right.
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms). Every row, read from
  left to right, and every column, read from top to bottom, is unimodal.
* An antidiagonal is read with increasing row index: x(i, j+1) is followed by x(i+1, j), and the
  condition is x(i, j+1) <= x(i+1, j) for all consecutive rows i, i+1 and columns j, j+1. (Reading
  the antidiagonals the other way gives the same counts, by turning the array through 180
  degrees.) This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a223772

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 3 → Fin 2)) : Prop :=
  (∀ r ∈ l, Unimodal (List.ofFn fun j => (r j : ℕ))) ∧
  (∀ j : Fin 3, Unimodal (l.map fun r => (r j : ℕ))) ∧
  l.IsChain (fun r s => ∀ j : Fin 2, r j.succ ≤ s j.castSucc)

/-- A223772(n): the number of such n X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      7 - 21 * X ^ 1 + 29 * X ^ 2 - 23 * X ^ 3 + 14 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a223772
