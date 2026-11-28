import Mathlib

/-!
# OEIS A285796: positive counts above 82

Source: https://oeis.org/A285796
Conjecture by Ilya Gutkovskiy (2017).
Credit: @ovolee37

The sequence counts ordered pairs of positive integers whose sum is n and
whose entries are products of an even number of distinct primes, including 1.
The source's program characterizes those entries by their Mobius value being 1.
A positive count is equivalent to the existence of such a pair; equal summands
are allowed. The conjecture asserts positivity for every n strictly above 82.

This file states the conjecture; it does not prove it.
-/

namespace OMA.S_oeis_a285796

theorem main :
    ∀ n : ℕ, 82 < n →
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = n ∧
        ArithmeticFunction.moebius a = 1 ∧
        ArithmeticFunction.moebius b = 1 := by
  sorry

end OMA.S_oeis_a285796
