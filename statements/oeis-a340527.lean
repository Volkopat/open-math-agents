import Mathlib

/-!
# A340527: Triangle read by rows: T(n,k) = A024916(n-k+1)*A000041(k-1), 1 <= k <= n.

Source: https://oeis.org/A340527
Credit: @esracummings31-blip

Conjecture 1 (Omar E. Pol): T(n,k) is the sum of divisors of the terms that are in the k-th
blocks of the first n rows of triangle A176206.
Conjecture 2 (Omar E. Pol): the sum of row n equals A182738(n), the sum of all parts of all
partitions of all positive integers <= n.

Only Conjectures 1 and 2 are formalized here. Conjecture 3 of the entry (the volume of blocks
of a symmetric tower built from the symmetric representation of sigma) is not addressed.

Conventions.
* A000203(m) = sigma(m), the sum of the divisors of m; A024916(m) = Sum_{i=1..m} sigma(i).
* A000041(j) is the number of partitions of j.
* Row m of A176206 is the nonincreasing list in which m-k+1 is repeated A000041(k-1) times,
  k = 1..m; its k-th block is that run of A000041(k-1) copies of m-k+1. The k-th blocks of the
  first n rows are the k-th blocks of rows m = k..n (rows m < k have no k-th block).
  "The sum of divisors of the terms" adds sigma(t) for every term t of those blocks.
* A182738(n) = Sum_{m=1..n} A066186(m), where A066186(m) is the sum of all parts of all
  partitions of m.
-/

namespace OMA.S_oeis_a340527

/-- A000041: the number of partitions of j. -/
def A000041 (j : ℕ) : ℕ := Fintype.card (Nat.Partition j)

/-- A000203: the sum of the divisors of m. -/
def A000203 (m : ℕ) : ℕ := ∑ d ∈ Nat.divisors m, d

/-- A024916: Sum_{i=1..m} sigma(i). -/
def A024916 (m : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 m, A000203 i

/-- A066186: the sum of all parts of all partitions of m. -/
def A066186 (m : ℕ) : ℕ := ∑ p : Nat.Partition m, p.parts.sum

/-- A182738: the sum of all parts of all partitions of all positive integers <= n. -/
def A182738 (n : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 n, A066186 m

/-- The k-th block of row m of A176206: A000041(k-1) copies of m-k+1. -/
def block (m k : ℕ) : List ℕ := List.replicate (A000041 (k - 1)) (m - k + 1)

/-- T(n,k) = A024916(n-k+1) * A000041(k-1). -/
def T (n k : ℕ) : ℕ := A024916 (n - k + 1) * A000041 (k - 1)

theorem main :
    (∀ n k : ℕ, 1 ≤ k → k ≤ n →
      T n k = ∑ m ∈ Finset.Icc k n, ((block m k).map A000203).sum) ∧
    (∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, T n k = A182738 n) := by
  sorry

end OMA.S_oeis_a340527
