import Mathlib

/-!
# A051179: a(n) = 2^(2^n) - 1

Source: https://oeis.org/A051179
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

OEIS comment (Sergey Pavlov, 2017): it seems that the largest prime divisor `p(n+1)` of `a(n+1)`
is always bigger than the largest prime divisor `p(n)` of `a(n)`.

## Encoding

* `a(n) = 2^(2^n) - 1` (offset `0`); `a(0) = 1` has no prime divisor, so the statement is for
  `n ≥ 1`.
* The largest prime divisor is `(Nat.primeFactors m).max'`, written as: some prime factor of
  `a(n+1)` exceeds every prime factor of `a(n)`.
* The other conjecture in the same comment (`ω(a(n)) > ω(a(n-1)) > n` for `n > 7`) follows from
  known factorisations of Fermat numbers and is not stated here.
-/

namespace OMA.S_oeis_a051179

/-- `a(n) = 2^(2^n) - 1`. -/
def a (n : ℕ) : ℕ := 2 ^ 2 ^ n - 1

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ q ∈ (a (n + 1)).primeFactors, ∀ p ∈ (a n).primeFactors, p < q := by
  sorry

end OMA.S_oeis_a051179
