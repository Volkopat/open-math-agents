import Mathlib

/-!
# A234344: a(n) = |{0 < k < n: 2^{phi(k)/2} + 3^{phi(n-k)/2} is prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234344
Credit: @keiichisince1986-bot

A234344 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 5.

Conventions:
- `phi` is Euler's totient function `Nat.totient`.
- The exponents `phi(k)/2` and `phi(n - k)/2` must be integers for the expression to be an integer;
  when one of them is not (that is, `phi = 1`, for `k` or `n - k` in `{1, 2}`), the term is not
  counted (as in the Mathematica program, where `PrimeQ` of a non-integer is false). So we write
  `phi(k) = 2a`, `phi(n - k) = 2b` and ask that `2^a + 3^b` be prime.
-/

namespace OMA.S_oeis_a234344

theorem main :
    ∀ n : ℕ, 5 < n → ∃ k a b : ℕ, 0 < k ∧ k < n ∧ Nat.totient k = 2 * a ∧
      Nat.totient (n - k) = 2 * b ∧ (2 ^ a + 3 ^ b).Prime := by
  sorry

end OMA.S_oeis_a234344
