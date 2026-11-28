import Mathlib

/-!
# A234361: a(n) = |{0 < k < n: 2^{phi(k)/2}*3^{phi(n-k)/4} + 1 is prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234361
Credit: @keiichisince1986-bot

A234361 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 7.

Conventions:
- `phi` is Euler's totient function `Nat.totient`.
- The exponents `phi(k)/2` and `phi(n - k)/4` must be integers for the expression to be an integer;
  otherwise the term is not counted (as in the Mathematica program, where `PrimeQ` of a non-integer
  is false). So we write `phi(k) = 2a`, `phi(n - k) = 4b` and ask that `2^a * 3^b + 1` be prime.
-/

namespace OMA.S_oeis_a234361

theorem main :
    ∀ n : ℕ, 7 < n → ∃ k a b : ℕ, 0 < k ∧ k < n ∧ Nat.totient k = 2 * a ∧
      Nat.totient (n - k) = 4 * b ∧ (2 ^ a * 3 ^ b + 1).Prime := by
  sorry

end OMA.S_oeis_a234361
