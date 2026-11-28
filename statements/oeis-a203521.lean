import Mathlib

/-!
# A203521: a(n) = Product_{1 <= i < j <= n} (prime(i) + prime(j)).

Source: https://oeis.org/A203521
Credit: @agchua

Comment of A203521 (unsigned; the entry is by Clark Kimberling, Jan 03 2012):
  Each term divides its successor, as in A203511. It is conjectured that each term is divisible by
  the corresponding superfactorial, A000178(n). See A093883 for a guide to related sequences.
Both sequences have offset 0, and the conjecture is stated as printed: A000178(n) divides
A203521(n) for every n >= 0. A000178(n) = Product_{k=0..n} k! (1, 1, 2, 12, 288, ...).
prime(i) is the i-th prime, Nat.nth Nat.Prime (i - 1); below the indices are shifted to start at
0, so a(n) is the product of prime(i+1) + prime(j+1) over 0 <= i < j < n (a(0) = a(1) = 1, the
empty product, a(2) = 5, a(3) = 280).
-/

namespace OMA.S_oeis_a203521

/-- A203521(n) = Product_{1 <= i < j <= n} (prime(i) + prime(j)), with 0-based indices. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (Nat.nth Nat.Prime i + Nat.nth Nat.Prime j)

/-- A000178(n) = Product_{k=0..n} k!, the superfactorial. -/
def sf (n : ℕ) : ℕ := ∏ k ∈ Finset.range (n + 1), k.factorial

/-- The comment's conjecture: A000178(n) divides A203521(n) for every n >= 0. -/
theorem main : ∀ n : ℕ, sf n ∣ a n := by
  sorry

end OMA.S_oeis_a203521
