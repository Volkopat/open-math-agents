import Mathlib

/-!
# A223774: Number of n X 5 0..1 arrays with rows and columns unimodal and antidiagonals nondecreasing.

Source: https://oeis.org/A223774
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(16 - 75*x + 140*x^2 - 126*x^3 + 96*x^4 - 180*x^5 + 272*x^6 - 200*x^7 + 65*x^8 - 20*x^9 + 27*x^10 - 18*x^11 + 4*x^12) / (1 - x)^11 (Colin Barker, Aug 23 2018).
* a(n) = 11*a(n-1) - 55*a(n-2) + 165*a(n-3) - 330*a(n-4) + 462*a(n-5) - 462*a(n-6) + 330*a(n-7) - 165*a(n-8) + 55*a(n-9) - 11*a(n-10) + a(n-11) for n>13 (Colin Barker, Aug 23 2018).

Conventions:
* An n X 5 array is the list of its n rows from top to bottom; a row is a function
  `Fin 5 → Fin 2` giving its entries from left to right.
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

namespace OMA.S_oeis_a223774

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 5 → Fin 2)) : Prop :=
  (∀ r ∈ l, Unimodal (List.ofFn fun j => (r j : ℕ))) ∧
  (∀ j : Fin 5, Unimodal (l.map fun r => (r j : ℕ))) ∧
  l.IsChain (fun r s => ∀ j : Fin 4, r j.succ ≤ s j.castSucc)

/-- A223774(n): the number of such n X 5 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 5 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 11 =
      16 - 75 * X + 140 * X ^ 2 - 126 * X ^ 3 + 96 * X ^ 4 - 180 * X ^ 5 + 272 * X ^ 6 - 200 * X ^ 7 + 65 * X ^ 8 - 20 * X ^ 9 + 27 * X ^ 10 - 18 * X ^ 11 + 4 * X ^ 12) ∧
    (∀ n > 13, (a n : ℤ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11)) := by
  sorry

end OMA.S_oeis_a223774
