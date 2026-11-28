import Mathlib

/-!
# A074777: Integers n such that sigma(phi(n))/n = 1/2.

Source: https://oeis.org/A074777
Credit: @sntntHb

Known terms: 2, 6, 30, 510, 131070, 8589934590.

Conjecture (Farideh Firoozbakht, Sep 14 2004): there are no further terms, i.e. the positive
integers `n` with `sigma(phi(n)) / n = 1/2` are exactly these six numbers.

Conventions: `sigma(phi(n)) / n = 1/2` is written without division as `2 * sigma(phi(n)) = n`
(for `n > 0` the two are equivalent).
-/

namespace OMA.S_oeis_a074777

theorem main :
    {n : ℕ | 0 < n ∧ 2 * ArithmeticFunction.sigma 1 (Nat.totient n) = n} =
      {2, 6, 30, 510, 131070, 8589934590} := by
  sorry

end OMA.S_oeis_a074777
