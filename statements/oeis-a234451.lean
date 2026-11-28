import Mathlib

/-!
# A234451: Number of ways to write n = k + m with k > 0 and m > 0 such that 2^(phi(k)/2 + phi(m)/6) + 3 is prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234451
Credit: @keiichisince1986-bot

A234451 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 9. [The entry continues with variants (2^(...) - 3, 3*2^(...) + 1,
3*2^(...) - 1); only the first claim of part (i), about a(n) itself, is formalized here.]

Conventions:
- `phi` is Euler's totient function `Nat.totient`.
- The exponent `phi(k)/2 + phi(m)/6 = (3 phi(k) + phi(m))/6` must be an integer for `2^(...) + 3` to be an
  integer; otherwise the term is not counted (as in the Mathematica program, where `PrimeQ` of a
  non-integer is false). So we write `3 phi(k) + phi(m) = 6e` and ask that `2^e + 3` be prime.
-/

namespace OMA.S_oeis_a234451

theorem main :
    ∀ n : ℕ, 9 < n → ∃ k m e : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
      3 * Nat.totient k + Nat.totient m = 6 * e ∧ (2 ^ e + 3).Prime := by
  sorry

end OMA.S_oeis_a234451
