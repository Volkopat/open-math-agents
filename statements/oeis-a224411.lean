import Mathlib

/-!
# A224411: Number of 4 X n 0..1 arrays with rows unimodal and antidiagonals nondecreasing.

Source: https://oeis.org/A224411
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: x*(16 - 36*x - 38*x^2 + 206*x^3 - 196*x^4 - 106*x^5 + 368*x^6 - 334*x^7 + 155*x^8 - 38*x^9 + 4*x^10) / (1 - x)^9 (Colin Barker, Aug 30 2018).
* a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>11 (Colin Barker, Aug 30 2018).

Conventions:
* A 4 X n array is the list of its n columns from left to right; a column is a function
  `Fin 4 → Fin 2` giving its entries from top to bottom (entry `i` lies in row `i`).
* A finite sequence is unimodal when it is weakly increasing up to some position and weakly
  decreasing from that position on (`Unimodal`, on the list of its terms). Every row, read from
  left to right, is unimodal.
* An antidiagonal is read with increasing row index: x(i, j+1) is followed by x(i+1, j), and the
  condition is x(i, j+1) <= x(i+1, j) for all consecutive rows i, i+1 and columns j, j+1. (Reading
  the antidiagonals the other way gives the same counts, by turning the array through 180
  degrees.) This reading reproduces the OEIS data.
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a224411

open PowerSeries

/-- A list is unimodal: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def Unimodal (s : List ℕ) : Prop :=
  ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 4 → Fin 2)) : Prop :=
  (∀ i : Fin 4, Unimodal (l.map fun c => (c i : ℕ))) ∧
  l.IsChain (fun u v => ∀ i : Fin 3, v i.castSucc ≤ u i.succ)

/-- A224411(n): the number of such 4 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 4 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      16 - 36 * X - 38 * X ^ 2 + 206 * X ^ 3 - 196 * X ^ 4 - 106 * X ^ 5 + 368 * X ^ 6 - 334 * X ^ 7 + 155 * X ^ 8 - 38 * X ^ 9 + 4 * X ^ 10) ∧
    (∀ n > 11, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a224411
