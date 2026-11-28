import Mathlib

/-!
# Does Morley's congruence characterize primes greater than 3?

Source: https://mathoverflow.net/questions/342353 (Zhi-Wei Sun, CC BY-SA 4.0).

Morley (1895): `binom(p-1, (p-1)/2) ≡ (-1)^((p-1)/2) 4^(p-1) (mod p³)` for every prime `p > 3`.
Conjecture (Sun, 2009): if `n > 1` is an odd integer satisfying
`binom(n-1, (n-1)/2) ≡ (-1)^((n-1)/2) 4^(n-1) (mod n³)`, then `n` is prime.
The congruence is taken in `ℤ`.
-/

namespace OMA.S_mo_342353

theorem main : ∀ n : ℕ, 1 < n → Odd n →
    ((Nat.choose (n - 1) ((n - 1) / 2) : ℤ) ≡ (-1) ^ ((n - 1) / 2) * 4 ^ (n - 1) [ZMOD (n : ℤ) ^ 3]) →
      n.Prime := by
  sorry

end OMA.S_mo_342353
