import Mathlib

/-!
# A282355: Expansion of (Sum_{i>=1} x^prime(prime(i)))*(Sum_{j = p*q, p prime, q prime} x^j).

Source: https://oeis.org/A282355
Credit: @keiichisince1986-bot

A282355 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 527 (addition: only 18 positive integers cannot be represented as a
sum of a prime number with prime subscript and a semiprime). [Only the main claim, a(n) > 0 for
n > 527, is formalized here.]

Conventions:
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)`. The exponents `prime(prime(i))` are the primes `prime(j)` with `j` prime.
- The exponents `p q` with `p, q` prime are the semiprimes. `a(n) > 0` means that `n = prime(j) + p q` with
  `j`, `p`, `q` prime.
-/

namespace OMA.S_oeis_a282355

theorem main :
    ∀ n : ℕ, 527 < n → ∃ j p q : ℕ, j.Prime ∧ p.Prime ∧ q.Prime ∧ n = Nat.nth Nat.Prime (j - 1) + p * q := by
  sorry

end OMA.S_oeis_a282355
