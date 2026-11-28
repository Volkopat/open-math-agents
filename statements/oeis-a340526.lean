import Mathlib

/-!
# A340526: Triangle read by rows: T(n,k) = A006218(n-k+1)*A000041(k-1), 1 <= k <= n.

Source: https://oeis.org/A340526
Credit: @esracummings31-blip

Conjecture 1 (Omar E. Pol): T(n,k) is the total number of divisors of the terms that are in the
k-th blocks of the first n rows of triangle A176206.
Conjecture 2 (Omar E. Pol): the sum of row n equals A284870(n), the total number of parts in all
partitions of all positive integers <= n.

Conventions.
* A006218(m) = Sum_{i=1..m} d(i), where d(i) is the number of divisors of i.
* A000041(j) is the number of partitions of j.
* Row m of A176206 is the nonincreasing list in which m-k+1 is repeated A000041(k-1) times,
  k = 1..m; its k-th block is that run of A000041(k-1) copies of m-k+1. The k-th blocks of the
  first n rows are the k-th blocks of rows m = k..n (rows m < k have no k-th block).
* A284870(n) = Sum_{m=1..n} A006128(m), where A006128(m) is the total number of parts in all
  partitions of m.
-/

namespace OMA.S_oeis_a340526

/-- A000041: the number of partitions of j. -/
def A000041 (j : ℕ) : ℕ := Fintype.card (Nat.Partition j)

/-- A006218: Sum_{i=1..m} d(i). -/
def A006218 (m : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 m, (Nat.divisors i).card

/-- A006128: the total number of parts in all partitions of m. -/
def A006128 (m : ℕ) : ℕ := ∑ p : Nat.Partition m, Multiset.card p.parts

/-- A284870: the total number of parts in all partitions of all positive integers <= n. -/
def A284870 (n : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 n, A006128 m

/-- The k-th block of row m of A176206: A000041(k-1) copies of m-k+1. -/
def block (m k : ℕ) : List ℕ := List.replicate (A000041 (k - 1)) (m - k + 1)

/-- T(n,k) = A006218(n-k+1) * A000041(k-1). -/
def T (n k : ℕ) : ℕ := A006218 (n - k + 1) * A000041 (k - 1)

theorem main :
    (∀ n k : ℕ, 1 ≤ k → k ≤ n →
      T n k = ∑ m ∈ Finset.Icc k n, ((block m k).map (fun t => (Nat.divisors t).card)).sum) ∧
    (∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, T n k = A284870 n) := by
  sorry

end OMA.S_oeis_a340526
