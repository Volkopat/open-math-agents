import Mathlib

/-!
# A229446: Number of 3 X n 0..2 arrays with horizontal differences mod 3 never 1, vertical differences mod 3 never -1, and rows and columns lexicographically nondecreasing.

Source: https://oeis.org/A229446
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/3)*n^3 + (8/3)*n + 5.
* G.f.: x*(8 - 19*x + 18*x^2 - 5*x^3) / (1 - x)^4 (Colin Barker).
* a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - 1*a(n-4) for n>4 (Colin Barker).

Conventions:
* A 3 X n array is the list of its columns from left to right; a column is a function
  `Fin 3 → Fin 3` giving its entries from top to bottom, each in `0..2`.
* Horizontal difference: right entry minus left entry in the same row; vertical difference:
  lower entry minus upper entry in the same column. Differences are taken mod 3 (`-1` mod 3 is
  `2`).
* Columns lexicographically nondecreasing: each column is lexicographically `≤` the column to its
  right (`toLex` on functions `Fin 3 → Fin 3`, top entry most significant).
* Rows lexicographically nondecreasing: row `i`, read left to right, is lexicographically `≤`
  row `i + 1` (`≤` on lists is lexicographic).
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a229446

open PowerSeries

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 3 → Fin 3)) : Prop :=
  (∀ r ∈ l, ∀ j : Fin 2, ((r j.succ : ℤ) - r j.castSucc) % 3 ≠ 2) ∧
  l.IsChain (fun r s => (∀ j, ((s j : ℤ) - r j) % 3 ≠ 1) ∧ toLex r ≤ toLex s) ∧
  ∀ j : Fin 2, l.map (fun r => r j.castSucc) ≤ l.map (fun r => r j.succ)

/-- A229446(n): the number of such 3 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 3) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 3) * n ^ 3 + (8 / 3) * n + 5) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 4 =
      8 - 19 * X + 18 * X ^ 2 - 5 * X ^ 3) ∧
    (∀ n > 4, (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - 1 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a229446
