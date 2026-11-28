import Mathlib

/-!
# A234388: Primes of the form 2^k*(2^{phi(m)} - 1) + 1, where k and m are positive integers, and phi(.) is Euler's totient function.

Source: https://oeis.org/A234388
Credit: @keiichisince1986-bot

A234388 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) Any integer n > 1 can be written as k + m with k > 0 and m > 0 such that
2^k*(2^{phi(m)} - 1) + 1 is prime.
(ii) Each integer n > 2 can be written as k + m with k > 0 and m > 0 such that
2^k*(2^{phi(m)} - 1) - 1 is prime.

Conventions:
- `phi` is Euler's totient function `Nat.totient`.
- `2^phi(m) ≥ 2`, so `2^phi(m) - 1 ≥ 1` and `2^k (2^phi(m) - 1) ≥ 2`; both natural-number subtractions are
  exact.
- Both parts are formalized, as a conjunction.
-/

namespace OMA.S_oeis_a234388

theorem main :
    (∀ n : ℕ, 1 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
        (2 ^ k * (2 ^ Nat.totient m - 1) + 1).Prime) ∧
      ∀ n : ℕ, 2 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
        (2 ^ k * (2 ^ Nat.totient m - 1) - 1).Prime := by
  sorry

end OMA.S_oeis_a234388
