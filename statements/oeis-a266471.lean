import Mathlib

/-!
# A266471: Number of 4 X n binary arrays with rows and columns lexicographically nondecreasing and column sums nonincreasing.

Source: https://oeis.org/A266471
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/120)*n^5 + (1/24)*n^4 + (17/24)*n^3 - (25/24)*n^2 + (257/60)*n + 1.
* G.f.: x*(5 - 18*x + 32*x^2 - 28*x^3 + 11*x^4 - 1*x^5) / (1 - x)^6 (Colin Barker).
* a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - 1*a(n-6) for n>6 (Colin Barker).

Conventions:
* A 4 X n array is the list of its columns from left to right; a column is a function
  `Fin 4 → Fin 2` giving its entries from top to bottom.
* Columns lexicographically nondecreasing: each column is lexicographically `≤` the column to its
  right (`toLex` on functions `Fin 4 → Fin 2`, top entry most significant).
* Column sums nonincreasing: the sum of the entries of each column is at least the sum of the
  entries of the column to its right.
* Rows lexicographically nondecreasing: row `i`, read left to right, is lexicographically `≤`
  row `i + 1` (`≤` on lists is lexicographic).
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a266471

open PowerSeries

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 4 → Fin 2)) : Prop :=
  l.IsChain (fun c d => toLex c ≤ toLex d ∧ ∑ i, (d i : ℕ) ≤ ∑ i, (c i : ℕ)) ∧
  ∀ j : Fin 3, l.map (fun r => r j.castSucc) ≤ l.map (fun r => r j.succ)

/-- A266471(n): the number of such 4 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 4 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 120) * n ^ 5 + (1 / 24) * n ^ 4 + (17 / 24) * n ^ 3 - (25 / 24) * n ^ 2 + (257 / 60) * n + 1) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 6 =
      5 - 18 * X + 32 * X ^ 2 - 28 * X ^ 3 + 11 * X ^ 4 - 1 * X ^ 5) ∧
    (∀ n > 6, (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - 1 * a (n - 6)) := by
  sorry

end OMA.S_oeis_a266471
