import Mathlib

/-!
# A328959: sigma_0(n) - 2 - (bigomega(n) - 1) * omega(n) is nonnegative for n >= 2

Source: https://oeis.org/A328959 (conjecture stated in the comments of A328959)

`a(n) = sigma_0(n) - 2 - (Omega(n) - 1) * nu(n)` (offset 1), where `sigma_0 = A000005` is the
number of divisors, `Omega = A001222` the number of prime factors counted with multiplicity
(Mathlib's `ArithmeticFunction.cardFactors`), and `nu = A001221` the number of distinct prime
factors (Mathlib's `ArithmeticFunction.cardDistinctFactors`). Values are taken in `ℤ`.

The conjecture: all terms are nonnegative except for `a(1) = -1`.
-/

namespace OMA.S_oeis_a328959

/-- OEIS A328959. -/
def a (n : ℕ) : ℤ :=
  (n.divisors.card : ℤ) - 2 -
    ((ArithmeticFunction.cardFactors n : ℤ) - 1) * (ArithmeticFunction.cardDistinctFactors n : ℤ)

theorem main : a 1 = -1 ∧ ∀ n : ℕ, 2 ≤ n → 0 ≤ a n := by
  sorry

end OMA.S_oeis_a328959
