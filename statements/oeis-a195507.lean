import Mathlib

/-!
# A195507: Smallest integer m greater than n such that m (mod k) == n (mod k) for k = 1..n-1

Source: https://oeis.org/A195507
Credit: @xor2k

Formalizes the OEIS A195507 conjecture (offset 1):
Conjecture: The sequence (a(n): n >= 1) satisfies the following recurrence. Write a(n)/n in lowest
terms as num/d. Then a(n+1) = d*a(n) - (d-1)*n + 1.

Conventions: `a n` is the infimum of the set of natural numbers `m > n` with `m % k = n % k` for
every `k` with `1 ≤ k ≤ n - 1` (this set is nonempty, e.g. it contains `n + (n-1)!`, so the infimum
is its least element). The lowest-terms denominator `d` of `a(n)/n` is `Rat.den` of the rational
number `a n / n`. The recurrence is stated in `ℤ`, so no truncated subtraction occurs; it is claimed
for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a195507

/-- Smallest `m > n` with `m ≡ n (mod k)` for all `k = 1, ..., n-1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | n < m ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 → m % k = n % k}

/-- With `d` the denominator of `a(n)/n` in lowest terms, `a(n+1) = d*a(n) - (d-1)*n + 1`
for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a (n + 1) : ℤ) =
      (((a n : ℚ) / n).den : ℤ) * a n - ((((a n : ℚ) / n).den : ℤ) - 1) * n + 1 := by
  sorry

end OMA.S_oeis_a195507
