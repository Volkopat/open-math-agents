import Mathlib

/-!
# A339304: Irregular triangle read by rows T(n,k) in which row n has length the partition number
A000041(n-1) and columns k give the number of divisors function A000005, 1 <= k <= n.

Source: https://oeis.org/A339304
Credit: @esracummings31-blip

Conjecture (Omar E. Pol): the sum of row n equals A138137(n), the total number of parts in the
last section of the set of partitions of n.

Conventions.
* The entry gives T(n,k) = A000005(A336811(n,k)).
* A336811 is the irregular triangle in which row n (n >= 1) has length A000041(n-1) and every
  column k lists the positive integers 1, 2, 3, ... starting from the first row that has a k-th
  term. Row n has a k-th term iff k <= A000041(n-1); since A000041 is nondecreasing, column k
  starts at row c(k) + 1, where c(k) is the least j with k <= A000041(j). Hence
  A336811(n,k) = n - c(k) for 1 <= k <= A000041(n-1).
* A138137 is defined in the OEIS as the first differences of A006128, where A006128(n) is the
  total number of parts in all partitions of n; this is the definition used here.
-/

namespace OMA.S_oeis_a339304

/-- A000041: the number of partitions of j. -/
def A000041 (j : ℕ) : ℕ := Fintype.card (Nat.Partition j)

/-- c(k): the least j with k <= A000041(j); column k of A336811 starts at row c(k) + 1. -/
noncomputable def c (k : ℕ) : ℕ := sInf {j | k ≤ A000041 j}

/-- Row n of A336811: the terms n - c(k), k = 1..A000041(n-1). -/
noncomputable def rowA336811 (n : ℕ) : List ℕ :=
  (List.range (A000041 (n - 1))).map (fun i => n - c (i + 1))

/-- Row n of A339304: T(n,k) = A000005(A336811(n,k)). -/
noncomputable def row (n : ℕ) : List ℕ := (rowA336811 n).map (fun t => (Nat.divisors t).card)

/-- A006128: the total number of parts in all partitions of n. -/
def A006128 (n : ℕ) : ℕ := ∑ p : Nat.Partition n, Multiset.card p.parts

/-- A138137: first differences of A006128 (for n >= 1). -/
def A138137 (n : ℕ) : ℤ := (A006128 n : ℤ) - A006128 (n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → (((row n).sum : ℕ) : ℤ) = A138137 n := by
  sorry

end OMA.S_oeis_a339304
