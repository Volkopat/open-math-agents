import Mathlib

/-!
# A340581: Irregular triangle read by rows in which row n has length A014153(n-1) and every
column k lists the positive integers A000027, n >= 1, k >= 1.

Source: https://oeis.org/A340581
Credit: @esracummings31-blip

Conjecture (Omar E. Pol): all divisors of all terms in row n are also all parts of all partitions
of all positive integers <= n.

Conventions.
* A000041(j) = number of partitions of j; A000070(m) = Sum_{i=0..m} A000041(i);
  A014153(m) = Sum_{i=0..m} A000070(i). Row n has length L(n) = A014153(n-1).
* Column k starts in the first row r with L(r) >= k and lists 1, 2, 3, ... downward, so
  T(n,k) = n - r + 1.
* "All divisors of all terms in row n" is the multiset obtained by listing all positive divisors
  of every term of row n (with repetition); "all parts of all partitions of all positive integers
  <= n" is the multiset of all parts of all partitions of j, over j = 1..n. The conjecture is the
  equality of these multisets.
* The further remarks in the entry ("in accordance with the conjectures in A336811 and A176206")
  are cross-references, not separate statements.
-/

namespace OMA.S_oeis_a340581

/-- A000041. -/
def A000041 (j : ℕ) : ℕ := Fintype.card (Nat.Partition j)

/-- A000070: partial sums of A000041. -/
def A000070 (m : ℕ) : ℕ := ∑ i ∈ Finset.range (m + 1), A000041 i

/-- A014153: partial sums of A000070. -/
def A014153 (m : ℕ) : ℕ := ∑ i ∈ Finset.range (m + 1), A000070 i

/-- Length of row n (n >= 1); length 0 for the empty row 0. -/
def L (n : ℕ) : ℕ := if n = 0 then 0 else A014153 (n - 1)

/-- The row in which column k starts. -/
noncomputable def start (k : ℕ) : ℕ := sInf {r : ℕ | k ≤ L r}

/-- A340581: T(n,k) for 1 <= k <= L(n). -/
noncomputable def T (n k : ℕ) : ℕ := n - start k + 1

/-- Row n as a multiset. -/
noncomputable def row (n : ℕ) : Multiset ℕ := (Finset.Icc 1 (L n)).val.map (T n)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (row n).bind (fun t => (Nat.divisors t).val) =
      ∑ j ∈ Finset.Icc 1 n, (Finset.univ : Finset (Nat.Partition j)).val.bind (fun p => p.parts) := by
  sorry

end OMA.S_oeis_a340581
