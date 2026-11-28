import Mathlib

/-!
# A335925: a(n) = a(floor((n-1)/a(n-1))) + 1 with a(1) = 1.

Source: https://oeis.org/A335925 (Altug Alkan, 30 June 2020). Related: https://oeis.org/A000522
Credit: @Squee451

Data (offset 1): 1, 2, 2, 2, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 3, 4, 3, 3, 3, 4, 4, 4, 3, 4, ...

The entry's comment: least k such that a(k) = n are 1, 2, 5, 16, 65, 326, 1957, ...
(Conjecture: This sequence is A000522).

A000522 (offset 0) is 1, 2, 5, 16, 65, 326, 1957, ...: the number of arrangements of a set with n
elements, Sum_{k=0..n} n!/k!. So the conjecture says: for every n >= 1, the least k with a(k) = n is
A000522(n-1).

Conventions.
* The sequence has offset 1. `a 0 = 0` below is a placeholder that is not part of the sequence, and
  the statement only speaks about indices `k ≥ 1`. For `n ≥ 2` the recurrence never reads the
  placeholder: `1 ≤ a (n-1) ≤ n-1`, so the index `(n-1) / a (n-1)` is at least 1.
* `a (n+2) = a ((n+1) / a (n+1)) + 1` is the source's recurrence at index `n+2`, with `/` the floor
  division of natural numbers.
* `n.factorial / k.factorial` is an exact division for `k ≤ n`.
-/

namespace OMA.S_oeis_a335925

/-- A335925: `a 1 = 1` and `a n = a (⌊(n-1) / a (n-1)⌋) + 1` for `n ≥ 2`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => a ((n + 1) / a (n + 1)) + 1
termination_by n => n
decreasing_by
  · omega
  · exact Nat.lt_succ_of_le (Nat.div_le_self _ _)

/-- A000522: the number of arrangements of a set with `n` elements, `Sum_{k=0..n} n!/k!`. -/
def A000522 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.factorial / k.factorial

/-- For every `n ≥ 1`, the least index `k ≥ 1` with `a k = n` is `A000522 (n - 1)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → IsLeast {k : ℕ | 1 ≤ k ∧ a k = n} (A000522 (n - 1)) := by
  sorry

end OMA.S_oeis_a335925
