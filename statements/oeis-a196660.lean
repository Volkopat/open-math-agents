import Mathlib

/-!
# A196660: smallest k > 0 such that k*n + (n-1) is prime

Source: https://oeis.org/A196660

A196660 (offset 1): `a(n)` is the smallest `k > 0` such that `k*n + (n-1)` is prime:
2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 7, …

Conjecture (Frank M Jackson, Oct 05 2011): for every `n` there exists `k < n` (apart from
`a(1)`) such that `k*n + (n-1)` is prime. That is, `a(n) < n` for every `n ≥ 2`; the case
`n = 1` is excluded by the source because `a(1) = 2`.

Conventions:
- `a(n)` is the least positive `k` with `k*n + (n-1)` prime, so `a(n) < n` holds exactly when
  some `k` with `0 < k < n` makes `k*n + (n-1)` prime. The statement is given in that
  existential form, which also carries the claim that `a(n)` exists.
- Everything is in `ℕ`; `n - 1` is an exact subtraction because `n ≥ 2`.
-/

namespace OMA.S_oeis_a196660

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (k * n + (n - 1)) := by
  sorry

end OMA.S_oeis_a196660
