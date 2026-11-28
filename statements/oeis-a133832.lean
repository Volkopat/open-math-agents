import Mathlib

/-!
# A133832: least k > n such that the binary trinomial 1 + 2^n + 2^k is prime

Source: https://oeis.org/A133832

A133832 (offset 1): `a(n)` is the least number `k > n` such that the binary trinomial
`1 + 2^n + 2^k` is prime, or 0 if there is no such `k`: 2, 3, 5, 13, 6, 7, 9, 9, 18, 19, …

Conjecture (T. D. Noe, Sep 26 2007): `a(n)` is nonzero for all `n`. That is, for every `n ≥ 1`
there is a `k > n` with `1 + 2^n + 2^k` prime. (The entry remarks that this is equivalent to
there being no Sierpinski numbers of the form `2^m + 1`.)

Conventions: `a(n)` nonzero means that some `k > n` with `1 + 2^n + 2^k` prime exists; the value
0 is only the entry's marker for the case that none does. `n` ranges over the positive integers
(offset 1); everything is in `ℕ`.
-/

namespace OMA.S_oeis_a133832

theorem main :
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, n < k ∧ Nat.Prime (1 + 2 ^ n + 2 ^ k) := by
  sorry

end OMA.S_oeis_a133832
