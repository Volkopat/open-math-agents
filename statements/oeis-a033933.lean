import Mathlib

/-!
# A033933: Least nonnegative m such that n! - m is prime

Source: https://oeis.org/A033933
Credit: @sntntHb

Conjecture (in the comments of A033933): for n >= 3, a(n) is 1 or a prime.

Conventions:
* `a(n)` is the least `m ≥ 0` such that `n! - m` is prime; it is written with `IsLeast`. For
  `n ≥ 2` such an `m` exists (`m = n! - 2` works), and `m ≤ n!` for every candidate, so natural
  number subtraction is exact on the relevant range.
* The conjecture is stated for every `n ≥ 3`: the least such `m` is `1` or a prime.
-/

namespace OMA.S_oeis_a033933

/-- For `n ≥ 3`, the least `m` with `n! - m` prime is `1` or a prime. -/
theorem main : ∀ n m : ℕ, 3 ≤ n → IsLeast {k : ℕ | (n.factorial - k).Prime} m →
    m = 1 ∨ m.Prime := by
  sorry

end OMA.S_oeis_a033933
