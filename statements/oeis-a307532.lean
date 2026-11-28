import Mathlib

/-!
# A307532: smallest k > 2^(2^n) + 1 with 2^(k-1) ≡ 1 (mod (2^(2^n) - 1)*k)

Source: https://oeis.org/A307532

A307532 (offset 0): `a(n)` is the smallest `k > 2^(2^n) + 1` such that
`2^(k-1) ≡ 1 (mod (2^(2^n) - 1)*k)`: 5, 7, 29, 281, 65617, 4294967681, 18446744073709552577, …
The entry notes that `a(n)` is an odd prime or a Fermat pseudoprime to base 2.

Conjecture (Amiram Eldar and Thomas Ordowski, Apr 13 2019): `a(n)` is prime for all `n ≥ 0`.

Conventions:
- The congruence `2^(k-1) ≡ 1 (mod M*k)` with `M = 2^(2^n) - 1` is written as the divisibility
  `M*k ∣ 2^(k-1) - 1`. Everything is in `ℕ`; all the subtractions are exact (`2^(2^n) ≥ 2`,
  `k ≥ 1` and `2^(k-1) ≥ 1`).
- `a(n)` is the least element of the set of admissible `k`. The statement is: for every `n`,
  any `k` that is the least element of this set (`IsLeast`) is prime. This does not assert that
  the set is nonempty; that `a(n)` exists is taken from the sequence definition.
-/

namespace OMA.S_oeis_a307532

theorem main :
    ∀ n k : ℕ,
      IsLeast {k : ℕ | 2 ^ (2 ^ n) + 1 < k ∧ (2 ^ (2 ^ n) - 1) * k ∣ 2 ^ (k - 1) - 1} k →
      Nat.Prime k := by
  sorry

end OMA.S_oeis_a307532
