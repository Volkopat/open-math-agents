import Mathlib

/-!
# A229439: Number of n X 2 0..2 arrays with horizontal differences mod 3 never 1, vertical differences mod 3 never -1, and rows and columns lexicographically nondecreasing.

Source: https://oeis.org/A229439
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = (1/24)*n^4 + (1/12)*n^3 - (1/24)*n^2 + (23/12)*n + 2.
* G.f.: x*(4 - 13*x + 18*x^2 - 10*x^3 + 2*x^4) / (1 - x)^5 (Colin Barker).
* a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5 (Colin Barker).

Conventions:
* An n X 2 array is the list of its rows from top to bottom; a row `(x, y)` holds the left
  entry `x` and the right entry `y`, both in `0..2`.
* Horizontal difference of a row: `y - x`; vertical difference: lower entry minus upper entry,
  in the same column. Differences are taken mod 3 (`-1` mod 3 is `2`).
* Rows lexicographically nondecreasing: each row is lexicographically `≤` the row below it
  (`toLex` on pairs). Columns lexicographically nondecreasing: the left column, read top to
  bottom, is lexicographically `≤` the right column (`≤` on lists is lexicographic).
* Offset 1 as in the OEIS; the generating function is written after dividing by `x`, i.e. as the
  series `Sum_{n>=0} a(n+1) x^n`.
-/

namespace OMA.S_oeis_a229439

open PowerSeries

/-- The conditions on an array, given as the list of its rows from top to bottom. -/
def IsSolution (l : List (Fin 3 × Fin 3)) : Prop :=
  (∀ r ∈ l, ((r.2 : ℤ) - r.1) % 3 ≠ 1) ∧
  l.IsChain (fun r s => ((s.1 : ℤ) - r.1) % 3 ≠ 2 ∧ ((s.2 : ℤ) - r.2) % 3 ≠ 2 ∧
    toLex r ≤ toLex s) ∧
  l.map Prod.fst ≤ l.map Prod.snd

/-- A229439(n): the number of such n X 2 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {l : List (Fin 3 × Fin 3) // l.length = n ∧ IsSolution l}

theorem main :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 24) * n ^ 4 + (1 / 12) * n ^ 3 - (1 / 24) * n ^ 2 +
      (23 / 12) * n + 2) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
      4 - 13 * X + 18 * X ^ 2 - 10 * X ^ 3 + 2 * X ^ 4) ∧
    (∀ n > 5, (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) +
      a (n - 5)) := by
  sorry

end OMA.S_oeis_a229439
