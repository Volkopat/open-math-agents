import Mathlib

/-!
# A266429: Number of 3 X n binary arrays with rows and columns lexicographically nondecreasing and column sums nondecreasing.

Source: https://oeis.org/A266429
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/360)*n^6 + (1/40)*n^5 + (1/9)*n^4 + (7/24)*n^3 + (319/360)*n^2 + (101/60)*n + 1.
* G.f.: x*(4 - 15*x + 32*x^2 - 34*x^3 + 21*x^4 - 7*x^5 + 1*x^6) / (1 - x)^7 (Colin Barker).
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + 1*a(n-7) for n>7 (Colin Barker).

Conventions:
* A 3 X n array is the list of its columns from left to right; a column is a function
  `Fin 3 → Fin 2` giving its entries from top to bottom.
* Columns lexicographically nondecreasing: each column is lexicographically `≤` the column to its
  right (`toLex` on functions `Fin 3 → Fin 2`, top entry most significant).
* Column sums nondecreasing: the sum of the entries of each column is at most the sum of the
  entries of the column to its right.
* Rows lexicographically nondecreasing: row `i`, read left to right, is lexicographically `≤`
  row `i + 1` (`≤` on lists is lexicographic).
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a266429

open PowerSeries

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 3 → Fin 2)) : Prop :=
  l.IsChain (fun c d => toLex c ≤ toLex d ∧ ∑ i, (c i : ℕ) ≤ ∑ i, (d i : ℕ)) ∧
  ∀ j : Fin 2, l.map (fun r => r j.castSucc) ≤ l.map (fun r => r j.succ)

/-- A266429(n): the number of such 3 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 360) * n ^ 6 + (1 / 40) * n ^ 5 + (1 / 9) * n ^ 4 + (7 / 24) * n ^ 3 + (319 / 360) * n ^ 2 + (101 / 60) * n + 1) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      4 - 15 * X + 32 * X ^ 2 - 34 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + 1 * X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + 1 * a (n - 7)) := by
  sorry

end OMA.S_oeis_a266429
