import Mathlib

/-!
# A267240: Number of n X 3 binary arrays with row sums nondecreasing and columns lexicographically nondecreasing.

Source: https://oeis.org/A267240
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = 10*a(n-1) - 39*a(n-2) + 76*a(n-3) - 79*a(n-4) + 42*a(n-5) -
  9*a(n-6), for n > 6.
* G.f.: x*(4 - 27*x + 68*x^2 - 76*x^3 + 42*x^4 - 9*x^5) / ((1 - x)^4*(1 - 3*x)^2) (Colin Barker).
* a(n) = (24 + (31+3^(2+n))*n + 12*n^2 + 2*n^3) / 24 (Colin Barker).

Conventions:
* An n X 3 array is the list of its rows from top to bottom; a row is a function `Fin 3 → Fin 2`
  giving its entries from left to right.
* Row sums nondecreasing: the sum of the entries of each row is at most the sum of the entries of
  the row below it.
* Columns lexicographically nondecreasing: column `j`, read top to bottom, is lexicographically
  `≤` column `j + 1` (`≤` on lists is lexicographic).
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a267240

open PowerSeries

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 3 → Fin 2)) : Prop :=
  l.IsChain (fun r s => ∑ i, (r i : ℕ) ≤ ∑ i, (s i : ℕ)) ∧
  ∀ j : Fin 2, l.map (fun r => r j.castSucc) ≤ l.map (fun r => r j.succ)

/-- A267240(n): the number of such n X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 → Fin 2) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n > 6, (a n : ℤ) = 10 * a (n - 1) - 39 * a (n - 2) + 76 * a (n - 3) - 79 * a (n - 4) +
      42 * a (n - 5) - 9 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - X) ^ 4 * (1 - 3 * X) ^ 2) =
      4 - 27 * X + 68 * X ^ 2 - 76 * X ^ 3 + 42 * X ^ 4 - 9 * X ^ 5) ∧
    (∀ n ≥ 1, (a n : ℚ) = (24 + (31 + 3 ^ (2 + n)) * n + 12 * n ^ 2 + 2 * n ^ 3) / 24) := by
  sorry

end OMA.S_oeis_a267240
