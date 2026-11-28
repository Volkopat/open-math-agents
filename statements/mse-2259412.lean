import Mathlib

/-!
# Infinitely many primes divide some $\sum_{k=1}^n k!$

Source: https://math.stackexchange.com/questions/2259412/infinitely-many-primes-divide-some-sum-k-1n-k
Credit: @ivillar

For a positive integer $n$ define $a_n=\sum_{k=1}^n k!$. Prove that the set of primes that
divide some $a_n$ is infinite.

Formalization notes:
* `a n` is the sum `1! + 2! + ... + n!`, taken over `Finset.Icc 1 n`, so `a 0 = 0` is an
  auxiliary value; the index `n` in the statement ranges over the positive integers, as in the
  source.
* "The set of primes that divide some `a_n`" is the set of primes `p` such that `p ∣ a n` for
  some `n ≥ 1`.
-/

namespace OMA.S_mse_2259412

/-- `a n = 1! + 2! + ... + n!`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, k.factorial

/-- The set of primes dividing `a n` for some positive integer `n` is infinite. -/
theorem main : {p : ℕ | p.Prime ∧ ∃ n : ℕ, 1 ≤ n ∧ p ∣ a n}.Infinite := by
  sorry

end OMA.S_mse_2259412
