import Mathlib

/-!
# A282906: Expansion of 1/(1 - Sum_{j>=1} x^(Sum_{i=1..j} prime(i))).

Source: https://oeis.org/A282906
Credit: @luciusacarr

a(n) is the number of compositions (ordered partitions) of n into partial sums of primes
(A007504: 2, 5, 10, 17, 28, ...).

Conjecture (from the entry): every number > 3 is the sum of at most 5 partial sums of primes.
`main` states it.

Reading of the source:
* The partial sums of primes are `prime(1) + ... + prime(j)` for `j ≥ 1` (the generating function
  uses `j ≥ 1`, so 0 is not a part). With Mathlib's 0-indexed `Nat.nth Nat.Prime`, this is
  `∑ i ∈ Finset.range j, Nat.nth Nat.Prime i` with `j ≥ 1`.
* "Sum of at most 5" means a sum of `r ≤ 5` such numbers, repetitions allowed (the summands are
  indexed by `Fin r`).
* Checked numerically for every n from 4 to 20000 (1 and 3 are not such sums).
-/

namespace OMA.S_oeis_a282906

/-- `m` is a partial sum of primes, `prime(1) + ... + prime(j)` with `j ≥ 1` (A007504). -/
def IsPrimePartialSum (m : ℕ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ m = ∑ i ∈ Finset.range j, Nat.nth Nat.Prime i

theorem main :
    -- Every number > 3 is the sum of at most 5 partial sums of primes.
    ∀ n : ℕ, 3 < n → ∃ (r : ℕ) (b : Fin r → ℕ), r ≤ 5 ∧
      (∀ i, IsPrimePartialSum (b i)) ∧ ∑ i, b i = n := by
  sorry

end OMA.S_oeis_a282906
