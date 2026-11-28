import Mathlib

/-!
# OEIS A000225: a(n) = 2^n - 1

Credit: @rhetoricalrhet

Conjecture (Chai Wah Wu) stated in the comments of https://oeis.org/A000225 :
except for `a(2) = 3`, the terms `2^n - 1` of this sequence are the numbers `m` such that
`2^(m+1) - 2^j - 2^k - 1` is composite for all `0 ≤ j < k ≤ m`.

Reading of the statement: a natural number `m` has the property if and only if `m = 2^n - 1`
for some `n` and `m ≠ 3`.

On the word composite: for `m = 1` (the term `a(1) = 1`), taking `j = 0`, `k = 1` gives
`2^2 - 2^0 - 2^1 - 1 = 0`, which is not composite in the strict sense (an integer greater than
`1` that is not prime). Reading composite strictly would exclude `m = 1` and make the conjecture
false as written, so composite is read here as not prime, which is what the listed terms require.
For `m ≥ 3` all the numbers involved are at least `2^(m-1) - 1 ≥ 3`, and `m = 0` (no pairs) and
`m = 2` (where `j = 0`, `k = 2` gives the prime `2`) come out the same under both readings, so
the two readings differ only at `m = 1`.

Since `j < k ≤ m`, we have `2^j + 2^k + 1 ≤ 2^(m+1)`, so the subtraction in `ℕ` never truncates.

*References:*
- [A000225](https://oeis.org/A000225)
-/

namespace OMA.S_oeis_a000225

/-- The property of the conjecture: `2^(m+1) - 2^j - 2^k - 1` is not prime for all
`0 ≤ j < k ≤ m`. -/
def AllComposite (m : ℕ) : Prop :=
  ∀ j k : ℕ, j < k → k ≤ m → ¬ (2 ^ (m + 1) - 2 ^ j - 2 ^ k - 1).Prime

/-- Conjecture (OEIS A000225, Chai Wah Wu): except for `3`, the numbers of the form `2^n - 1`
are exactly the numbers `m` with `AllComposite m`. -/
theorem main : ∀ m : ℕ, AllComposite m ↔ (∃ n : ℕ, m = 2 ^ n - 1) ∧ m ≠ 3 := by
  sorry

end OMA.S_oeis_a000225
