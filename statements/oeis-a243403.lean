import Mathlib

/-!
# A243403: Number of primes p < n such that p*(n-p) is a primitive root modulo prime(n).

Source: https://oeis.org/A243403
Credit: @keiichisince1986-bot

A243403 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 6.

Conventions:
- `prime(n)` is the `n`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (n - 1)`.
- A primitive root modulo a prime `q` is an integer whose residue has multiplicative order `q - 1`:
  `IsPrimitiveRoot (x : ZMod q) (q - 1)`.
- `n - p` is exact since `p < n`.
-/

namespace OMA.S_oeis_a243403

theorem main :
    ∀ n : ℕ, 6 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧
      IsPrimitiveRoot ((p * (n - p) : ℕ) : ZMod (Nat.nth Nat.Prime (n - 1))) (Nat.nth Nat.Prime (n - 1) - 1) := by
  sorry

end OMA.S_oeis_a243403
