import Mathlib

/-!
# A390118: least m such that m*n + 1 is the square of a prime

Source: https://oeis.org/A390118

A390118 (offset 1): `a(n)` is the least positive integer `m` such that `m*n + 1 = p^2` for some
prime number `p`: 3, 4, 1, 2, 24, 4, 24, 1, 32, 12, …  For example `a(1) = 3` since
`3*1 + 1 = 2^2`, and `a(2) = 4` since `4*2 + 1 = 3^2`. The entry notes that `a(n)` always
exists, since there are primes congruent to 1 modulo `n`.

Conjecture (Zhi-Wei Sun, Oct 25 2025): `a(n) ≤ (n+5)*(n-1)` for all `n > 1` (verified for
`n ≤ 12000`).

Since `a(n)` is the least positive `m` with `m*n + 1` the square of a prime, the bound
`a(n) ≤ (n+5)*(n-1)` holds exactly when some such `m` is at most `(n+5)*(n-1)`, and the
conjecture is stated in that form.

Conventions: everything is in `ℕ`; `n - 1` is an exact subtraction because `n > 1`.
-/

namespace OMA.S_oeis_a390118

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ m p : ℕ, 0 < m ∧ m ≤ (n + 5) * (n - 1) ∧ Nat.Prime p ∧ m * n + 1 = p ^ 2 := by
  sorry

end OMA.S_oeis_a390118
