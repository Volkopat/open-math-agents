import Mathlib

/-!
# A282502: Expansion of 1/(1 - Sum_{k>=0} x^(3*k*(k+1)/2+1)).

Source: https://oeis.org/A282502
Credit: @luciusacarr

a(n) is the number of compositions (ordered partitions) of n into centered triangular numbers
(A005448: 1, 4, 10, 19, 31, ...).

Conjecture (from the entry): every number > 1 is the sum of at most 5 centered triangular
numbers. `main` states it.

Reading of the source:
* The centered triangular numbers are `3k(k+1)/2 + 1` for `k ≥ 0`.
* "Sum of at most 5" means a sum of `j` such numbers with `j ≤ 5`, repetitions allowed (the
  summands are indexed by `Fin j`).
* Checked numerically for every n from 2 to 20000.

Note: a sum of `j` centered triangular numbers is `j + 3 * (sum of j triangular numbers)`, so the
claim appears to follow from Gauss's Eureka theorem (every natural number is a sum of three
triangular numbers) by taking `j ∈ {3, 4, 5}` according to `n mod 3` (and `j = 2` for `n = 2`).
It is stated here as the entry states it.
-/

namespace OMA.S_oeis_a282502

/-- `m` is a centered triangular number (A005448). -/
def IsCenteredTriangular (m : ℕ) : Prop := ∃ k : ℕ, m = 3 * k * (k + 1) / 2 + 1

theorem main :
    -- Every number > 1 is the sum of at most 5 centered triangular numbers.
    ∀ n : ℕ, 1 < n → ∃ (j : ℕ) (b : Fin j → ℕ), j ≤ 5 ∧
      (∀ i, IsCenteredTriangular (b i)) ∧ ∑ i, b i = n := by
  sorry

end OMA.S_oeis_a282502
