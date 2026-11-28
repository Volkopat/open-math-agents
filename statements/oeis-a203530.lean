import Mathlib

/-!
# A203530: a(n) = Product_{1 <= i < j <= n} (c(i) + c(j)); c = A002808 = composite numbers.

Source: https://oeis.org/A203530
Credit: @agchua

Comment of A203530 (unsigned; the entry is by Clark Kimberling, Jan 03 2012):
  It is conjectured that each term is divisible by the corresponding superfactorial, A000178(n);
  as in A203533.
A203530 has offset 1 (data 1, 10, 1680, 5569200, ...) and A000178 has offset 0, so the
conjecture is stated as printed: A000178(n) divides A203530(n) for every n >= 1, where
A000178(n) = Product_{k=0..n} k! (1, 1, 2, 12, 288, ...). c(i) is the i-th composite number
(A002808: 4, 6, 8, 9, 10, ...), the numbers k > 1 that are not prime; below the indices are
shifted to start at 0, so c 0 = 4 and a(n) is the product of c(i) + c(j) over 0 <= i < j < n
(a(1) = 1, the empty product, a(2) = 10, a(3) = 1680).
-/

namespace OMA.S_oeis_a203530

/-- A002808, the composite numbers, with 0-based index: c 0 = 4, c 1 = 6, c 2 = 8, ... -/
noncomputable def c (i : ℕ) : ℕ := Nat.nth (fun k => 1 < k ∧ ¬ Nat.Prime k) i

/-- A203530(n) = Product_{1 <= i < j <= n} (c(i) + c(j)), with 0-based indices. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (c i + c j)

/-- A000178(n) = Product_{k=0..n} k!, the superfactorial. -/
def sf (n : ℕ) : ℕ := ∏ k ∈ Finset.range (n + 1), k.factorial

/-- The comment's conjecture: A000178(n) divides A203530(n) for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → sf n ∣ a n := by
  sorry

end OMA.S_oeis_a203530
