import Mathlib

/-!
# A359507: a(n) is the least integer k such that there exists a strictly increasing integer sequence n = b_1 < b_2 < ... < b_t = n + k with the property that b_1 XOR b_2 XOR ... XOR b_t = 0.

Source: https://oeis.org/A359507
Credit: @agchua

Comment of A359507 (the entry is by Peter Kagey, Jan 03 2023; the comment is unsigned):
  Conjecture: a(n) is of the form 2^k + 1 for all n > 0.

Offset 0, data 0, 2, 3, 3, 3, 5, 3, 5, ... (a(0) = 0 by the one-term sequence b_1 = 0).
A strictly increasing sequence n = b_1 < ... < b_t is a list of numbers that is strictly
increasing, starts with n and ends with n + k; all its terms are at least n >= 0, so it is a
list of natural numbers, and XOR is the bitwise exclusive or `^^^` of natural numbers.
The exponent in 2^k + 1 is a natural number (a(1) = 2 = 2^0 + 1); the claim is for n > 0.
-/

namespace OMA.S_oeis_a359507

/-- There is a strictly increasing sequence `n = b_1 < b_2 < ... < b_t = n + k` whose XOR
`b_1 XOR b_2 XOR ... XOR b_t` is `0`. -/
def Good (n k : ℕ) : Prop :=
  ∃ l : List ℕ, l.Pairwise (· < ·) ∧ l.head? = some n ∧ l.getLast? = some (n + k) ∧
    l.foldl (· ^^^ ·) 0 = 0

/-- A359507: the least `k` such that `Good n k`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | Good n k}

/-- The conjecture: for every `n > 0`, `a(n)` is of the form `2^j + 1`. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ j : ℕ, a n = 2 ^ j + 1 := by
  sorry

end OMA.S_oeis_a359507
