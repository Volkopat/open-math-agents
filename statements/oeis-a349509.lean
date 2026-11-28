import Mathlib

/-!
# A349509: the denominators of binomial(n^3 + 6n^2 - 6n + 2, n^3 - 1)/n^3 are 1 or 3

Source: https://oeis.org/A349509
Credit: @ivillar

Status: known result: the entry records that the conjecture is correct (Kevin Ryde, Jul 01 2023).

A349509 (offset 1): a(n) is the denominator of binomial(n^3 + 6*n^2 - 6*n + 2, n^3 - 1)/n^3;
data 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, ... (the fraction is an upper bound for the number of vertices
of the polytope of n X n X n stochastic tensors).

Conjecture (in the comments of A349509): 1 and 3 are the only terms that appear in this sequence.
Kevin Ryde (Jul 01 2023) records in the entry that the conjecture is correct.

Formalization: the fraction is formed in ℚ and `Rat.den` is its denominator in lowest terms. The
top index is written n^3 + 6*n^2 + 2 - 6*n in ℕ, where the subtraction is exact for every n. The
statement is that a(n) is 1 or 3 for every n ≥ 1.
-/

namespace OMA.S_oeis_a349509

/-- a(n): the denominator of binomial(n^3 + 6n^2 - 6n + 2, n^3 - 1) / n^3 in lowest terms. -/
def a (n : ℕ) : ℕ :=
  ((Nat.choose (n ^ 3 + 6 * n ^ 2 + 2 - 6 * n) (n ^ 3 - 1) : ℚ) / (n : ℚ) ^ 3).den

/-- Every term of A349509 is 1 or 3. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 1 ∨ a n = 3 := by
  sorry

end OMA.S_oeis_a349509
