import Mathlib

/-!
# A247097: a(n) = least integer m such that prime(n)+m and prime(n+1)+m are prime.

Source: https://oeis.org/A247097
Credit: @keiichisince1986-bot

A247097 is the sequence `a(n)` named in the title. The entry states:
It is conjectured that a(n) always exists.

Conventions:
- Primes are indexed from `0` in Mathlib: `Nat.nth Nat.Prime i` is `prime(i + 1)`. So `prime(n) = Nat.nth Nat.Prime (n - 1)` and `prime(n + 1) = Nat.nth Nat.Prime n`.
- The offset is `2`. The data takes `m > 0` (`a(2) = 2` for the primes `3, 5`, although `m = 0` would give
  primes); we follow the data and require `m > 0`.
-/

namespace OMA.S_oeis_a247097

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ m : ℕ, 0 < m ∧ (Nat.nth Nat.Prime (n - 1) + m).Prime ∧
      (Nat.nth Nat.Prime n + m).Prime := by
  sorry

end OMA.S_oeis_a247097
