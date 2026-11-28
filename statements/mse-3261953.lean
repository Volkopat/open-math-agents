import Mathlib

/-!
# Refinement of Bertrand's Postulate

Source: https://math.stackexchange.com/questions/3261953 (2019).
Credit: @jagraj28

Let `δ(1) = 0` and `δ(n) = p₁ + ⋯ + p_r` when `n = p₁ ⋯ p_r` is the prime factorization of `n`
(with multiplicity; OEIS A001414). The post calls `n` refined if there is a prime in the open
interval `(n, n + δ(n))`, and unrefined otherwise; the first unrefined number is `5120`. It asks
whether the unrefined numbers are finite, and the author conjectures that they are infinite.
The post has no answer.

Formalization notes:
* `δ n` is the sum of `Nat.primeFactorsList n` (the prime factors with multiplicity), which is
  `0` for `n = 1`.
* The numbers considered are `n ≥ 2`: the post says the first unrefined number is `5120`,
  although `n = 1` (with `δ(1) = 0`) has no prime in the empty interval `(1, 1)`.
* `main` states the author's conjecture: there are infinitely many unrefined numbers.
* A direct search finds 21 unrefined numbers in `[2, 200000]`, the first being `5120`, as in
  the post.
-/

namespace OMA.S_mse_3261953

/-- `δ(n)`: the sum of the prime factors of `n`, with multiplicity. -/
def δ (n : ℕ) : ℕ := n.primeFactorsList.sum

/-- `n` is unrefined: no prime lies strictly between `n` and `n + δ(n)`. -/
def Unrefined (n : ℕ) : Prop := ¬ ∃ p : ℕ, p.Prime ∧ n < p ∧ p < n + δ n

/-- The author's conjecture: there are infinitely many unrefined numbers `n ≥ 2`. -/
theorem main : {n : ℕ | 2 ≤ n ∧ Unrefined n}.Infinite := by
  sorry

end OMA.S_mse_3261953
