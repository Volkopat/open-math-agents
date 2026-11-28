import Mathlib

/-!
# A266472: Number of 5 X n binary arrays with rows and columns lexicographically nondecreasing and column sums nonincreasing.

Source: https://oeis.org/A266472
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/181440)*n^9 + (1/8064)*n^8 + (29/15120)*n^7 + (13/960)*n^6 + (301/8640)*n^5 + (101/384)*n^4 - (34619/90720)*n^3 + (37531/10080)*n^2 - (4171/2520)*n + 4.
* G.f.: x*(6 - 41*x + 147*x^2 - 303*x^3 + 410*x^4 - 382*x^5 + 248*x^6 - 109*x^7 + 30*x^8 - 4*x^9) / (1 - x)^10 (Colin Barker).
* a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - 1*a(n-10) for n>10 (Colin Barker).

Conventions:
* A 5 X n array is the list of its columns from left to right; a column is a function
  `Fin 5 → Fin 2` giving its entries from top to bottom.
* Columns lexicographically nondecreasing: each column is lexicographically `≤` the column to its
  right (`toLex` on functions `Fin 5 → Fin 2`, top entry most significant).
* Column sums nonincreasing: the sum of the entries of each column is at least the sum of the
  entries of the column to its right.
* Rows lexicographically nondecreasing: row `i`, read left to right, is lexicographically `≤`
  row `i + 1` (`≤` on lists is lexicographic).
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a266472

open PowerSeries

/-- The conditions on an array, given as the list of its columns from left to right. -/
def IsSolution (l : List (Fin 5 → Fin 2)) : Prop :=
  l.IsChain (fun c d => toLex c ≤ toLex d ∧ ∑ i, (d i : ℕ) ≤ ∑ i, (c i : ℕ)) ∧
  ∀ j : Fin 4, l.map (fun r => r j.castSucc) ≤ l.map (fun r => r j.succ)

/-- A266472(n): the number of such 5 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 5 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 181440) * n ^ 9 + (1 / 8064) * n ^ 8 + (29 / 15120) * n ^ 7 + (13 / 960) * n ^ 6 + (301 / 8640) * n ^ 5 + (101 / 384) * n ^ 4 - (34619 / 90720) * n ^ 3 + (37531 / 10080) * n ^ 2 - (4171 / 2520) * n + 4) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 10 =
      6 - 41 * X + 147 * X ^ 2 - 303 * X ^ 3 + 410 * X ^ 4 - 382 * X ^ 5 + 248 * X ^ 6 - 109 * X ^ 7 + 30 * X ^ 8 - 4 * X ^ 9) ∧
    (∀ n > 10, (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - 1 * a (n - 10)) := by
  sorry

end OMA.S_oeis_a266472
