import Mathlib

/-!
# A286014: Sum of smallest parts of all partitions of n into consecutive parts

Source: https://oeis.org/A286014
Credit: @jagong-cmu

Formalizes the conjecture in the OEIS entry (offset 1):
this is also the row sums of A211343, for every n >= 1.

Conventions:
* A partition of n into consecutive parts is a list of k >= 1 parts m+1, m+2, ..., m+k with
  m >= 0 (all parts positive) and sum n. Its smallest part is m+1. Such a partition has
  k <= n and m + 1 <= n, so the pairs (m, k) range over `0..n` and `1..n`.
* A211343 is the triangle (n >= 1, k >= 1) in which column k lists the positive integers
  1, 2, 3, ... interleaved with k-1 zeros, and the first element of column k is in row
  k(k+1)/2. So for k(k+1)/2 <= n, its entry is (n - k(k+1)/2)/k + 1 if k divides
  n - k(k+1)/2, and 0 otherwise. Row n has length A003056(n): its entries are the k with
  1 <= k and k(k+1)/2 <= n (all such k are at most n).
* The division by 2 and the subtraction on `ℕ` are exact where they are used.
-/

namespace OMA.S_oeis_a286014

/-- The `k` consecutive parts `m+1, m+2, ..., m+k`. -/
def consecParts (m k : ℕ) : List ℕ := (List.range k).map (fun i => m + 1 + i)

/-- A286014: the sum of the smallest parts `m+1` over all partitions of `n` into `k >= 1`
consecutive parts `m+1, ..., m+k`. -/
def a (n : ℕ) : ℕ :=
  ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.Icc 1 n).filter (fun p => (consecParts p.1 p.2).sum = n),
    (p.1 + 1)

/-- A211343(n,k): column `k` lists `1, 2, 3, ...` interleaved with `k-1` zeros, from row
`k(k+1)/2`. -/
def A211343 (n k : ℕ) : ℕ :=
  if k * (k + 1) / 2 ≤ n ∧ (n - k * (k + 1) / 2) % k = 0 then
    (n - k * (k + 1) / 2) / k + 1 else 0

/-- The sum of row `n` of A211343 (the row has the entries `k` with `k(k+1)/2 <= n`). -/
def rowSum (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k * (k + 1) / 2 ≤ n), A211343 n k

theorem main : ∀ n : ℕ, 1 ≤ n → a n = rowSum n := by
  sorry

end OMA.S_oeis_a286014
