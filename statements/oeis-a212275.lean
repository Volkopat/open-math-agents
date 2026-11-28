import Mathlib

/-!
# A212275: least k such that 4*n*k + 1 is a prime of the form m^2 + 1

Source: https://oeis.org/A212275

A212275 (offset 1): `a(n)` is the least `k` such that `4*n*k + 1` is a prime of the form
`m^2 + 1`, or 0 if no such `k` exists: 1, 2, 3, 1, 5, 24, 7, 8, 1, 10, 99, …

Conjecture (Vladimir Shevelev, May 13 2012): `a(n) > 0`. That is, for every `n ≥ 1` there is a
`k` such that `4*n*k + 1` is a prime of the form `m^2 + 1`. (The entry remarks that this would
imply that there are infinitely many primes of the form `m^2 + 1`.)

Conventions:
- `a(n) > 0` means that some admissible `k` exists; the value 0 is only the entry's marker for
  the case that none does. The statement is therefore the existence of `k` and `m`.
- `k` is required to be positive. This loses nothing: for `k = 0` the number `4*n*k + 1 = 1` is
  not prime.
- `n` ranges over the positive integers (offset 1); everything is in `ℕ`.
-/

namespace OMA.S_oeis_a212275

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ k m : ℕ, 0 < k ∧ 4 * n * k + 1 = m ^ 2 + 1 ∧ Nat.Prime (4 * n * k + 1) := by
  sorry

end OMA.S_oeis_a212275
