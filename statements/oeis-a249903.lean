import Mathlib

/-!
# A249903: Numbers n such that 2n+1 and sigma(n) are both noncomposite numbers.

Source: https://oeis.org/A249903
Credit: @luciusacarr

Data: 1, 2, 9, 729.

The entry's comment: Conjecture: 2 and 9 are the only numbers n such that 2n - 1, 2n + 1 and
sigma(n) are all primes. `main` states that conjecture.

Reading of the source:
* `n` ranges over the natural numbers; `sigma(n)` is the sum of the divisors of `n`.
* "2 and 9 are the only numbers" is stated as: `2n - 1`, `2n + 1` and `sigma(n)` are all prime
  if and only if `n = 2` or `n = 9`. (For n = 0, `2n - 1` is 0 in ℕ and is not prime, matching
  the fact that -1 is not prime.) The numbers below 3000 with this property are exactly 2 and 9
  (checked numerically).
-/

namespace OMA.S_oeis_a249903

theorem main :
    -- 2 and 9 are the only numbers n with 2n - 1, 2n + 1 and sigma(n) all prime.
    ∀ n : ℕ, ((2 * n - 1).Prime ∧ (2 * n + 1).Prime ∧ (ArithmeticFunction.sigma 1 n).Prime) ↔
      (n = 2 ∨ n = 9) := by
  sorry

end OMA.S_oeis_a249903
