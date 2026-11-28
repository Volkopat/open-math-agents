import Mathlib

/-!
# A359508: a(n) = log_2(A359507(n) - 1).

Source: https://oeis.org/A359508
Credit: @agchua

Comment of A359508 (the entry is by Peter Kagey, Jan 03 2023; the comment is unsigned):
  Conjecture: A359507(n) is always of the form 2^m + 1.
A359508 has offset 1 (data 0, 1, 1, 1, 2, 1, ... for n = 1, 2, ...), so always means for every
n >= 1, the indices of A359508; A359507(0) = 0 is outside that range.
A359507(n) is the least integer k such that there exists a strictly increasing integer sequence
n = b_1 < b_2 < ... < b_t = n + k with b_1 XOR b_2 XOR ... XOR b_t = 0 (offset 0, data 0, 2, 3,
3, 3, 5, ...). Such a sequence is a strictly increasing list of numbers >= n >= 0, so a list of
natural numbers, and XOR is the bitwise exclusive or `^^^` of natural numbers. The exponent m is
a natural number (A359507(1) = 2 = 2^0 + 1).
-/

namespace OMA.S_oeis_a359508

/-- There is a strictly increasing sequence `n = b_1 < b_2 < ... < b_t = n + k` whose XOR
`b_1 XOR b_2 XOR ... XOR b_t` is `0`. -/
def Good (n k : ℕ) : Prop :=
  ∃ l : List ℕ, l.Pairwise (· < ·) ∧ l.head? = some n ∧ l.getLast? = some (n + k) ∧
    l.foldl (· ^^^ ·) 0 = 0

/-- A359507: the least `k` such that `Good n k`. -/
noncomputable def A359507 (n : ℕ) : ℕ := sInf {k : ℕ | Good n k}

/-- The comment's conjecture: for every `n >= 1`, `A359507(n)` is of the form `2^m + 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, A359507 n = 2 ^ m + 1 := by
  sorry

end OMA.S_oeis_a359508
