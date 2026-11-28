import Mathlib

/-!
# A234504: Number of ways to write n = k + m with k > 0 and m > 0 such that 2^(phi(k) + phi(m)/4) - 5 is prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234504
Credit: @keiichisince1986-bot

A234504 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 10.

Conventions:
- `phi` is Euler's totient function `Nat.totient`.
- The exponent `phi(k) + phi(m)/4` must be an integer; otherwise the term is not counted (as in the
  Mathematica program). So we write `4 phi(k) + phi(m) = 4e` and ask that `2^e - 5` be prime.
- Since `phi(k) ≥ 1` and `phi(m) ≥ 4` when `4` divides `phi(m)`, we have `e ≥ 2`. For `e = 2` the value is
  `-1` (not prime) and the truncated natural-number value `0` is not prime either; for `e ≥ 3` the
  subtraction is exact.
-/

namespace OMA.S_oeis_a234504

theorem main :
    ∀ n : ℕ, 10 < n → ∃ k m e : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
      4 * Nat.totient k + Nat.totient m = 4 * e ∧ (2 ^ e - 5).Prime := by
  sorry

end OMA.S_oeis_a234504
