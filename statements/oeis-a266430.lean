import Mathlib

/-!
# A266430: Number of 4 X n binary arrays with rows and columns lexicographically nondecreasing and column sums nondecreasing.

Source: https://oeis.org/A266430
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/9979200)*n^11 + (1/201600)*n^10 + (1/12096)*n^9 + (1/1344)*n^8 + (1271/302400)*n^7 + (479/28800)*n^6 + (12797/181440)*n^5 + (97/504)*n^4 + (1779/2800)*n^3 + (2032/1575)*n^2 + (8269/4620)*n + 1.
* G.f.: x*(5 - 38*x + 162*x^2 - 396*x^3 + 679*x^4 - 833*x^5 + 737*x^6 - 471*x^7 + 213*x^8 - 65*x^9 + 12*x^10 - 1*x^11) / (1 - x)^12 (Colin Barker).
* a(n) = 12*a(n-1) - 66*a(n-2) + 220*a(n-3) - 495*a(n-4) + 792*a(n-5) - 924*a(n-6) + 792*a(n-7) - 495*a(n-8) + 220*a(n-9) - 66*a(n-10) + 12*a(n-11) - 1*a(n-12) for n>12 (Colin Barker).

Conventions:
* A 4 X n array is the list of its columns from left to right; a column is a function
  `Fin 4 → Fin 2` giving its entries from top to bottom.
* Columns lexicographically nondecreasing: each column is lexicographically `≤` the column to its
  right (`toLex` on functions `Fin 4 → Fin 2`, top entry most significant).
* Column sums nondecreasing: the sum of the entries of each column is at most the sum of the
  entries of the column to its right.
* Rows lexicographically nondecreasing: row `i`, read left to right, is lexicographically `≤`
  row `i + 1` (`≤` on lists is lexicographic).
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a266430

open PowerSeries

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 4 → Fin 2)) : Prop :=
  l.IsChain (fun c d => toLex c ≤ toLex d ∧ ∑ i, (c i : ℕ) ≤ ∑ i, (d i : ℕ)) ∧
  ∀ j : Fin 3, l.map (fun r => r j.castSucc) ≤ l.map (fun r => r j.succ)

/-- A266430(n): the number of such 4 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 4 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 9979200) * n ^ 11 + (1 / 201600) * n ^ 10 + (1 / 12096) * n ^ 9 + (1 / 1344) * n ^ 8 + (1271 / 302400) * n ^ 7 + (479 / 28800) * n ^ 6 + (12797 / 181440) * n ^ 5 + (97 / 504) * n ^ 4 + (1779 / 2800) * n ^ 3 + (2032 / 1575) * n ^ 2 + (8269 / 4620) * n + 1) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 12 =
      5 - 38 * X + 162 * X ^ 2 - 396 * X ^ 3 + 679 * X ^ 4 - 833 * X ^ 5 + 737 * X ^ 6 - 471 * X ^ 7 + 213 * X ^ 8 - 65 * X ^ 9 + 12 * X ^ 10 - 1 * X ^ 11) ∧
    (∀ n > 12, (a n : ℤ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - 1 * a (n - 12)) := by
  sorry

end OMA.S_oeis_a266430
