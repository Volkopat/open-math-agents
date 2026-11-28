import Mathlib

/-!
# A229440: Number of n X 3 0..2 arrays with horizontal differences mod 3 never 1, vertical differences mod 3 never -1, and rows and columns lexicographically nondecreasing.

Source: https://oeis.org/A229440
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/360)*n^6 + (1/120)*n^5 + (1/36)*n^4 + (5/24)*n^3 - (11/360)*n^2 + (167/60)*n + 2.
* G.f.: x*(5 - 25*x + 57*x^2 - 66*x^3 + 44*x^4 - 15*x^5 + 2*x^6) / (1 - x)^7 (Colin Barker).
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + 1*a(n-7) for n>7 (Colin Barker).

Conventions:
* An n X 3 array is the list of its rows from top to bottom; a row is a function
  `Fin 3 → Fin 3` giving its entries from left to right, each in `0..2`.
* Horizontal difference: right entry minus left entry in the same row; vertical difference:
  lower entry minus upper entry in the same column. Differences are taken mod 3 (`-1` mod 3 is
  `2`).
* Rows lexicographically nondecreasing: each row is lexicographically `≤` the row below it
  (`toLex` on functions `Fin 3 → Fin 3`).
* Columns lexicographically nondecreasing: column `j`, read top to bottom, is lexicographically
  `≤` column `j + 1` (`≤` on lists is lexicographic).
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a229440

open PowerSeries

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 3 → Fin 3)) : Prop :=
  (∀ r ∈ l, ∀ j : Fin 2, ((r j.succ : ℤ) - r j.castSucc) % 3 ≠ 1) ∧
  l.IsChain (fun r s => (∀ j, ((s j : ℤ) - r j) % 3 ≠ 2) ∧ toLex r ≤ toLex s) ∧
  ∀ j : Fin 2, l.map (fun r => r j.castSucc) ≤ l.map (fun r => r j.succ)

/-- A229440(n): the number of such n X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 3) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 360) * n ^ 6 + (1 / 120) * n ^ 5 + (1 / 36) * n ^ 4 + (5 / 24) * n ^ 3 - (11 / 360) * n ^ 2 + (167 / 60) * n + 2) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      5 - 25 * X + 57 * X ^ 2 - 66 * X ^ 3 + 44 * X ^ 4 - 15 * X ^ 5 + 2 * X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + 1 * a (n - 7)) := by
  sorry

end OMA.S_oeis_a229440
