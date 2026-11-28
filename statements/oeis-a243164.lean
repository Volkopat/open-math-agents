import Mathlib

/-!
# A243164: Number of primes p < n such that p*n is a primitive root modulo prime(n).

Source: https://oeis.org/A243164
Credit: @keiichisince1986-bot

A243164 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 6. [Further parts of the entry are not formalized here.]

Conventions:
- `prime(n)` is the `n`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (n - 1)`.
- A primitive root modulo a prime `q` is an integer whose residue has multiplicative order `q - 1`:
  `IsPrimitiveRoot (x : ZMod q) (q - 1)`.
-/

namespace OMA.S_oeis_a243164

theorem main :
    ∀ n : ℕ, 6 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧
      IsPrimitiveRoot ((p * n : ℕ) : ZMod (Nat.nth Nat.Prime (n - 1))) (Nat.nth Nat.Prime (n - 1) - 1) := by
  sorry

end OMA.S_oeis_a243164
