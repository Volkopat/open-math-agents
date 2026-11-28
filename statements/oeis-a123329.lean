import Mathlib

/-!
# A123329: Let M be the matrix defined in A111490. Sequence gives M(2,1)-M(1,2),
M(2,1)+M(3,1)+M(3,2)-M(1,2)-M(1,3)-M(2,3), etc.

Source: https://oeis.org/A123329
Credit: @esracummings31-blip

The matrix of A111490 is M(n, k) = 1 + (k-1) mod n (row n is 1, 2, ..., n repeated), and
a(n) = Sum_{i=2..n+2} Sum_{j=1..i-1} (M(i,j) - M(j,i)) for n >= 0 (offset 0; this is the
OEIS program of M. S. Branicky and gives the listed data 0, 1, 3, 8, 14, 26, ...).

Conjectures (Omar E. Pol, Jan 20 2021), "assuming here that the offset is 1", i.e. for the
shifted sequence b(n) = a(n-1), n >= 1:
1. b is the convolution of A001065 and A000027:
   b(n) = Sum_{k=1..n} A001065(k) * A000027(n+1-k);
2. b is the sequence of partial sums of A153485;
3. b(n) = A175254(n) - A000292(n).
(Conjecture 3 is stated through the volumes; the pyramid description is the geometric reading of
A175254(n) and A000292(n).)
-/

namespace OMA.S_oeis_a123329

/-- The matrix of A111490: M(n, k) = 1 + (k-1) mod n. -/
def M (n k : ℕ) : ℕ := 1 + (k - 1) % n

/-- A123329 (offset 0). -/
def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 2 (n + 2), ∑ j ∈ Finset.Ico 1 i, ((M i j : ℤ) - M j i)

/-- A001065: sum of proper divisors (aliquot parts) of n. -/
def A001065 (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- A000027: the positive integers. -/
def A000027 (n : ℕ) : ℕ := n

/-- A153485: sum of all aliquot divisors of all positive integers <= n. -/
def A153485 (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, A001065 k

/-- A175254: Sum_{k<=n} sigma(k) * (n-k+1). -/
def A175254 (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.sigma 1 k * (n - k + 1)

/-- A000292: tetrahedral numbers n(n+1)(n+2)/6. -/
def A000292 (n : ℕ) : ℕ := n * (n + 1) * (n + 2) / 6

theorem main : ∀ n : ℕ, 1 ≤ n →
    a (n - 1) = ∑ k ∈ Finset.Icc 1 n, (A001065 k : ℤ) * A000027 (n + 1 - k) ∧
    a (n - 1) = ∑ k ∈ Finset.Icc 1 n, (A153485 k : ℤ) ∧
    a (n - 1) = (A175254 n : ℤ) - A000292 n := by
  sorry

end OMA.S_oeis_a123329
