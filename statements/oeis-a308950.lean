import Mathlib

/-!
# OEIS A308950: 6n + r = p + 2^k 3^m for r = 1 and r = -1

Source: https://oeis.org/A308950
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A308950(n) is the number of ways to write `n` as `(p-1)/6 + 2^a 3^b`, where `p` is a prime, and
`a` and `b` are nonnegative integers.

Conjecture: let `r` be `1` or `-1`. Then any integer `n > 1` can be written as
`(p-r)/6 + 2^a 3^b`, where `p` is a prime and `a, b` are nonnegative integers; in other words,
`6n + r` can be written as `p + 2^k 3^m`, where `p` is a prime and `k, m` are positive integers.

Formalization notes:
* The second ("in other words") form is stated, in `ℤ`: `6n + r = p + 2^k 3^m` with `k, m ≥ 1`.
  It is equivalent to the first, since `6 * 2^a 3^b = 2^(a+1) 3^(b+1)`.
-/

namespace OMA.S_oeis_a308950

/-- For `r = ±1` and every integer `n > 1`, `6n + r = p + 2^k 3^m` with `p` prime and
`k, m ≥ 1`. -/
theorem main :
    ∀ r : ℤ, (r = 1 ∨ r = -1) → ∀ n : ℕ, 1 < n →
      ∃ p k m : ℕ, p.Prime ∧ 1 ≤ k ∧ 1 ≤ m ∧ 6 * (n : ℤ) + r = p + 2 ^ k * 3 ^ m := by
  sorry

end OMA.S_oeis_a308950
