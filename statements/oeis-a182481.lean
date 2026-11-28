import Mathlib

/-!
# A182481: least k such that 6*k*n - 1 and 6*k*n + 1 are twin primes

Source: https://oeis.org/A182481

A182481 (offset 1): `a(n)` is the least `k` such that `6*k*n - 1` and `6*k*n + 1` are twin
primes, and `a(n) = 0` if such `k` does not exist: 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 4, 5, …

Conjecture (Vladimir Shevelev, May 01 2012): `a(n) > 0`. That is, for every `n ≥ 1` there is a
`k ≥ 1` such that `6*k*n - 1` and `6*k*n + 1` are both prime. (The entry adds that,
equivalently, for every `n` the arithmetic progression `{6*k*n - 1}` contains infinitely many
lesser twin primes; the statement here is the form `a(n) > 0`.)

Conventions:
- `a(n) > 0` means that some admissible `k` exists; the value 0 is only the entry's marker for
  the case that none does.
- `n` and `k` are positive integers and everything is in `ℕ`; `6*k*n - 1` is an exact
  subtraction because `6*k*n ≥ 6`.
-/

namespace OMA.S_oeis_a182481

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ k : ℕ, 0 < k ∧ Nat.Prime (6 * k * n - 1) ∧ Nat.Prime (6 * k * n + 1) := by
  sorry

end OMA.S_oeis_a182481
