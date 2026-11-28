import Mathlib

/-!
# A337209: Triangle read by rows T(n,k), (n >= 1, k >= 1), in which row n has length
A000070(n-1) and every column gives A000203, the sum of divisors function.

Source: https://oeis.org/A337209
Credit: @esracummings31-blip

Conjecture (Omar E. Pol): the sum of row n equals A066186(n), the sum of all parts of all
partitions of n.

Conventions.
* The entry gives T(n,k) = A000203(A176206(n,k)). Row n of A176206 is the nonincreasing list in
  which n-k is repeated A000041(k) times, k = 0..n-1 (as stated in A176206); its length is
  A000070(n-1). So row n of this triangle is the list of sigma(t) over the terms t of that row.
* A000041(j) is the number of partitions of j; A000203(t) = sigma(t) is the sum of the divisors
  of t; A066186(n) is the sum of all parts of all partitions of n.
-/

namespace OMA.S_oeis_a337209

/-- A000041: the number of partitions of j. -/
def A000041 (j : ℕ) : ℕ := Fintype.card (Nat.Partition j)

/-- Row n of A176206: n-k repeated A000041(k) times, k = 0..n-1. -/
def rowA176206 (n : ℕ) : List ℕ :=
  (List.range n).flatMap (fun k => List.replicate (A000041 k) (n - k))

/-- A000203: the sum of the divisors of t. -/
def A000203 (t : ℕ) : ℕ := ∑ d ∈ Nat.divisors t, d

/-- Row n of A337209: T(n,k) = A000203(A176206(n,k)). -/
def row (n : ℕ) : List ℕ := (rowA176206 n).map A000203

/-- A066186: the sum of all parts of all partitions of n. -/
def A066186 (n : ℕ) : ℕ := ∑ p : Nat.Partition n, p.parts.sum

theorem main : ∀ n : ℕ, 1 ≤ n → (row n).sum = A066186 n := by
  sorry

end OMA.S_oeis_a337209
