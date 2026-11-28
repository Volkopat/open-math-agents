import Mathlib

/-!
# A335901: a(n) = 2*a(floor((n-1)/a(n-1))) with a(1) = 1.

Source: https://oeis.org/A335901 (Altug Alkan, following a suggestion from Andrew R. Booker,
29 June 2020). Related: https://oeis.org/A117261
Credit: @Squee451

Data (offset 1): 1, 2, 2, 2, 4, 2, 4, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 4, 8, 4, 4, 4, ...

The entry's comment: least k such that a(k) = 2^n are 1, 2, 5, 21, 169, 2705, ...
(Conjecture: This sequence is A117261).

A117261 (offset 0) is 1, 2, 5, 21, 169, 2705, 86561, ...; its formula in the OEIS is
a(n) = Sum_{k=0..n} 2^(n*(n-1)/2 - k*(k-1)/2). The listed values start at 2^0 = 1 (reached first at
k = 1), so the conjecture says: for every n >= 0, the least k with a(k) = 2^n is A117261(n).

Conventions.
* The sequence has offset 1. `a 0 = 0` below is a placeholder that is not part of the sequence, and
  the statement only speaks about indices `k ≥ 1`. For `n ≥ 2` the recurrence never reads the
  placeholder: `1 ≤ a (n-1) ≤ n-1`, so the index `(n-1) / a (n-1)` is at least 1.
* `a (n+2) = 2 * a ((n+1) / a (n+1))` is the source's recurrence at index `n+2`, with `/` the floor
  division of natural numbers.
* In `A117261`, `n*(n-1)/2` and `k*(k-1)/2` are exact divisions (triangular numbers), and the
  subtraction of exponents does not truncate because `k ≤ n` in the sum.
* The definition of `a` is the literal recurrence by well-founded recursion, so evaluating it is slow
  beyond about `n = 40`.
-/

namespace OMA.S_oeis_a335901

/-- A335901: `a 1 = 1` and `a n = 2 * a (⌊(n-1) / a (n-1)⌋)` for `n ≥ 2`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * a ((n + 1) / a (n + 1))
termination_by n => n
decreasing_by
  · omega
  · exact Nat.lt_succ_of_le (Nat.div_le_self _ _)

/-- A117261: `Sum_{k=0..n} 2^(n*(n-1)/2 - k*(k-1)/2)`. -/
def A117261 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), 2 ^ (n * (n - 1) / 2 - k * (k - 1) / 2)

/-- For every `n`, the least index `k ≥ 1` with `a k = 2 ^ n` is `A117261 n`. -/
theorem main : ∀ n : ℕ, IsLeast {k : ℕ | 1 ≤ k ∧ a k = 2 ^ n} (A117261 n) := by
  sorry

end OMA.S_oeis_a335901
