import Mathlib

/-!
# Are there only finitely many $n\in\mathbb{N}$ that equal the sum of squares of its smallest $k$ divisors?

Source: https://mathoverflow.net/questions/509919
Credit: @luciusacarr

The source: for given `k ∈ ℕ`, is it true that there are only finitely many `n ∈ ℕ` such that
`k ≤ τ(n)` and `n = d₁² + ⋯ + d_k²`, where `τ(n)` is the number of divisors of `n` and
`d₁ < d₂ < ⋯ < d_k` are the smallest `k` divisors of `n`?

The divisors of `n` are sorted increasingly and the first `k` are taken. For `n = 0` Mathlib's
`Nat.divisors 0` is empty, so `0` satisfies the condition only for `k = 0`; for `k = 0` the set
is `{0}`, which is finite, so that case is harmless. The source's example: `k = 11`, `n = 1860`.
-/

namespace OMA.S_mo_509919

/-- The sum of the squares of the `k` smallest divisors of `n`. -/
def sumSqSmallestDivisors (k n : ℕ) : ℕ :=
  (((n.divisors.sort (· ≤ ·)).take k).map (fun d => d ^ 2)).sum

theorem main : ∀ k : ℕ, {n : ℕ | k ≤ n.divisors.card ∧ n = sumSqSmallestDivisors k n}.Finite := by
  sorry

end OMA.S_mo_509919
