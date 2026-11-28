import Mathlib

/-!
# A267632: Triangle T(n, k) read by rows: the k-th column of the n-th row lists the number of ways to select k distinct numbers (k >= 1) from [1..n] so that their sum is divisible by n.

Source: https://oeis.org/A267632
Credit: @agchua

Comment of A267632 (unsigned; the entry is by Dimitri Papadopoulos, Jan 18 2016):
  Row less the last element is palindrome for n=odd or n=power of 2 where n is the row number
  (observation-conjecture).
Offset of A267632: 1 (rows n >= 1, columns 1 <= k <= n; data 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, ...).

T(n, k) is the number of k-element subsets of {1, ..., n} whose sum is divisible by n. Row n
without its last element is T(n, 1), ..., T(n, n - 1); it is a palindrome iff
T(n, k) = T(n, n - k) for 1 <= k <= n - 1. The statement says this for every n >= 1 that is odd
or a power of 2.
-/

namespace OMA.S_oeis_a267632

/-- T(n, k): the number of k-element subsets of [1..n] whose sum is divisible by n. -/
def T (n k : ℕ) : ℕ :=
  (((Finset.Icc 1 n).powersetCard k).filter (fun S => n ∣ ∑ x ∈ S, x)).card

/-- The comment's claim: for n odd or a power of 2, row n without its last element is a
palindrome. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (Odd n ∨ ∃ m : ℕ, n = 2 ^ m) →
    ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 → T n k = T n (n - k) := by
  sorry

end OMA.S_oeis_a267632
