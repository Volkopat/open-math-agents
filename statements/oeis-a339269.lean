import Mathlib

/-!
# A339269: a(n) is the least number that is the product of n primes (not necessarily distinct) and is the sum of n consecutive primes, or 0 if there are none.

Source: https://oeis.org/A339269
Credit: @keiichisince1986-bot

A339269 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for every n > 2.

Conventions:
- A sum of `n` consecutive primes is `p_i + p_(i+1) + … + p_(i+n-1)`, where
  `p_i = Nat.nth Nat.Prime i` is the `i`-th prime counting from `p_0 = 2`.
- A product of `n` primes, not necessarily distinct, is a number whose prime factorization,
  counted with multiplicity, has length `n`.
- `a(n) > 0` means that some number is both.
-/

namespace OMA.S_oeis_a339269

theorem main :
    ∀ n : ℕ, 2 < n → ∃ i : ℕ,
        (∑ j ∈ Finset.range n, Nat.nth Nat.Prime (i + j)).primeFactorsList.length = n := by
  sorry

end OMA.S_oeis_a339269
