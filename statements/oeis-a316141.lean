import Mathlib

/-!
# A316141: n = p + F(k)*L(m) with p an odd prime

Source: https://oeis.org/A316141

A316141 (offset 1): `a(n)` is the number of ordered pairs `(k, m)` with `k > 1` and `m > 0` such
that `n - F(k)*L(m)` is an odd prime, where `F(k)` is the `k`-th Fibonacci number (A000045) and
`L(m)` is the `m`-th Lucas number (A000204): 0, 0, 0, 1, 1, 3, 2, 4, 3, 4, …  For example
`a(4) = 1` with `4 - F(2)*L(1) = 4 - 1*1 = 3` an odd prime.

Conjecture (Zhi-Wei Sun, Jun 25 2018): `a(n) > 0` for all `n > 3`. In other words, any integer
`n > 3` can be written as `p + F(k)*L(m)`, where `p` is an odd prime, and `k` and `m` are
positive integers. The entry notes that this has been verified for all `n = 4..5*10^9`.

The conjecture is stated in the entry's own in-other-words form. (The sequence counts pairs with
`k > 1`; since `F(1) = F(2) = 1`, allowing `k = 1` does not change which `n` are representable.)

Conventions:
- `F(k)` is `Nat.fib k`. The Lucas numbers A000204 are `L(1) = 1`, `L(2) = 3`, `L(3) = 4`,
  `L(4) = 7`, …, and satisfy `L(m) = F(m-1) + F(m+1)` for `m ≥ 1`; this formula is used as the
  definition, and it is only applied with `m > 0`.
- An odd prime is a prime different from 2. Everything is in `ℕ`.
-/

namespace OMA.S_oeis_a316141

/-- The Lucas numbers A000204 for `m ≥ 1`: `L(m) = F(m-1) + F(m+1)` (1, 3, 4, 7, 11, 18, …). -/
def lucas (m : ℕ) : ℕ := Nat.fib (m - 1) + Nat.fib (m + 1)

theorem main :
    ∀ n : ℕ, 3 < n →
      ∃ p k m : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ 0 < k ∧ 0 < m ∧ p + Nat.fib k * lucas m = n := by
  sorry

end OMA.S_oeis_a316141
