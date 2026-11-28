import Mathlib

/-!
# OEIS A178536: First column of matrix inverse of A178534

Source: https://oeis.org/A178536 (OEIS Foundation, CC BY-SA 4.0).
OEIS A178534 is the lower-triangular integer matrix `T(n, k)` (`1 ≤ k ≤ n`) defined by
`T(n, 1) = Fib(n + 1)` and, for `k > 1`,
`T(n, k) = ∑_{i=1}^{k-1} T(n - i, k - 1) - ∑_{i=1}^{k-1} T(n - i, k)` (with `T(m, j) = 0` for
`m < j`).
OEIS A178535 is the matrix inverse of A178534, and OEIS A178536 is its first column `a(n)` (`n ≥ 1`),
uniquely determined by `∑_{k=1}^n T(n, k) * a(k) = if n = 1 then 1 else 0` for all `n ≥ 1`.

Conjecture (Mats Granvik, Jan 24 2021): for every `n ≥ 1`,
`a(n) = ∑_{k ∣ n} μ(n / k) * ([k = 1] - [2 ∣ k])`.
-/

namespace OMA.S_oeis_a178536

/-- The lower-triangular matrix `A178534(n, k)` defined by `T(n, 1) = Fib(n + 1)` and
`T(n, k) = ∑_{i=1}^{k-1} T(n - i, k - 1) - ∑_{i=1}^{k-1} T(n - i, k)` for `k ≥ 2`
(with `T(n, k) = 0` when `k = 0` or `n < k`). -/
def T (n k : ℕ) : ℤ :=
  if k = 0 ∨ n < k then 0
  else if k = 1 then (Nat.fib (n + 1) : ℤ)
  else
    (∑ i ∈ Finset.range (k - 1), T (n - (i + 1)) (k - 1)) -
    (∑ i ∈ Finset.range (k - 1), T (n - (i + 1)) k)
termination_by (n, k)
decreasing_by
  · left; omega
  · left; omega

/-- Conjecture (Mats Granvik, OEIS A178536): the first column `a` of the inverse of `T` satisfies
`a(n) = ∑_{k ∣ n} μ(n / k) * ([k = 1] - [2 ∣ k])` for all `n ≥ 1`. -/
theorem main :
    ∀ a : ℕ → ℤ,
      (∀ n : ℕ, 1 ≤ n →
        ∑ k ∈ Finset.Icc 1 n, T n k * a k = if n = 1 then 1 else 0) →
      ∀ n : ℕ, 1 ≤ n →
        a n = ∑ k ∈ n.divisors,
          (ArithmeticFunction.moebius (n / k) : ℤ) *
            ((if k = 1 then 1 else 0) - (if 2 ∣ k then 1 else 0)) := by
  sorry

end OMA.S_oeis_a178536
