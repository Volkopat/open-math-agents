import Mathlib

/-!
# A111441: Numbers k such that the sum of the squares of the first k primes is divisible by k

Source: https://oeis.org/A111441
Credit: @jrflga (agent: Claude Code, model claude-fable-5-2)

OEIS comment (Daniel Bamberger, Dec 03 2020): Conjecture: There are no terms that are 3 or 9
modulo 12. This seems to hold for all related sequences with even powers of primes, not just
squares. Compare *sums of powers of primes divisibility sequences*, linked below.

The entry has offset 1 and begins `1, 19, 37, 455, 509, 575, 20597, ...`; for instance
`2^2 + 3^2 + 5^2 + ... + 67^2 = 19 * 1314`, so `19` is a term.

## Encoding

* `primePowerSum m k` is the sum of the `m`-th powers of the first `k` primes,
  `2^m + 3^m + 5^m + ...` (`k` summands); `Nat.nth Nat.Prime i` is the `i`-th prime, counted
  from `Nat.nth Nat.Prime 0 = 2`.
* `IsTerm m k` says that `k` is a term of the sequence built with the `m`-th power: `k` is a
  positive integer and `k` divides `primePowerSum m k`. A111441 is the case `m = 2`.
* `main` is the conjunction of the two sentences of the comment. The first conjunct is the
  conjecture for A111441 itself. The second conjunct is the remark about the related sequences:
  the same property for every even power `m`; the exponent is positive (`m = 2, 4, 6, ...`),
  because for `m = 0` every positive integer would be a term.
-/

namespace OMA.S_oeis_a111441

/-- The sum of the `m`-th powers of the first `k` primes. -/
noncomputable def primePowerSum (m k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (Nat.nth Nat.Prime i) ^ m

/-- `k` is a term of the sequence built with the `m`-th power: `k` is positive and divides the
sum of the `m`-th powers of the first `k` primes. -/
def IsTerm (m k : ℕ) : Prop :=
  0 < k ∧ k ∣ primePowerSum m k

theorem main :
    (∀ k : ℕ, IsTerm 2 k → k % 12 ≠ 3 ∧ k % 12 ≠ 9) ∧
    (∀ m : ℕ, 0 < m → Even m → ∀ k : ℕ, IsTerm m k → k % 12 ≠ 3 ∧ k % 12 ≠ 9) := by
  sorry

end OMA.S_oeis_a111441
