import Mathlib

/-!
# A220290: 4-hyperperfect numbers: n = 4*(sigma(n)-n-1) + 1.

Source: https://oeis.org/A220290
Credit: @prasledi

Conjecture (Alexander Violette, Jul 10 2026, in the COMMENTS of A220290): an infinite amount of
terms not of the form (5^k-4)*5^(k-1) exist.

Formalization notes:
* n is 4-hyperperfect when n = 4 * (sigma(n) - n - 1) + 1, with sigma the sum of divisors
  (`ArithmeticFunction.sigma 1`). The equation is stated in the integers: in natural numbers
  the truncated subtraction would make n = 1 a solution (sigma(1) - 1 - 1 = 0), but 1 is not a
  term (the data starts 1950625). In the integers n = 1 gives 1 = -3, false, as it should.
  Terms are positive integers.
* The family (5^k - 4) * 5^(k-1) is taken over k >= 1 (for k = 0, 5^k - 4 is negative). The
  comment notes that it gives a term whenever 5^k - 4 is prime (k in A059613), e.g.
  k = 5 gives 1950625.
* The conjecture: the set of 4-hyperperfect n that are not (5^k - 4) * 5^(k-1) for any k >= 1
  is infinite.
-/

namespace OMA.S_oeis_a220290

/-- `n` is 4-hyperperfect: `n = 4 * (σ(n) - n - 1) + 1`, computed in `ℤ`. -/
def IsFourHyperperfect (n : ℕ) : Prop :=
  0 < n ∧ (n : ℤ) = 4 * ((ArithmeticFunction.sigma 1 n : ℤ) - n - 1) + 1

/-- Violette's conjecture on A220290. -/
theorem main :
    {n : ℕ | IsFourHyperperfect n ∧ ∀ k : ℕ, 1 ≤ k → n ≠ (5 ^ k - 4) * 5 ^ (k - 1)}.Infinite := by
  sorry

end OMA.S_oeis_a220290
