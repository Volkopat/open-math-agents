import Mathlib

/-!
# A285891: Triangle read by rows: T(n,k) = n*A237048(n,k)

Source: https://oeis.org/A285891
Credit: @jagong-cmu

Formalizes the conjecture in the OEIS entry (Omar E. Pol):
T(n,k) = n, is also the sum of the parts of the partition of n into k consecutive parts,
if such a partition exists, otherwise T(n,k) = 0.

Conventions:
* A237048 is the irregular triangle (n >= 1, k >= 1) in which column k lists 1's interleaved
  with k-1 zeros, and the first element of column k is in row k(k+1)/2. So
  A237048(n,k) = 1 if n >= k(k+1)/2 and k divides n - k(k+1)/2, and 0 otherwise. Row n has
  length A003056(n), so the entries of row n are the k with 1 <= k and k(k+1)/2 <= n. The
  statement is for every n >= 1 and every such k. The division by 2 and the subtraction on
  `ℕ` are exact here.
* A partition of n into k consecutive parts is a list of parts m+1, m+2, ..., m+k with
  m >= 0 (all parts positive) and sum n. Such a part list has m + 1 <= n, so m ranges over
  `0..n`. The right side is the sum, over all such partitions, of the sum of their parts.
  This is the sum of the parts of the partition if one exists (it is then unique), and 0 if
  none exists.
-/

namespace OMA.S_oeis_a285891

/-- A237048(n,k): column `k` lists 1's interleaved with `k-1` zeros, from row `k(k+1)/2`. -/
def A237048 (n k : ℕ) : ℕ :=
  if k * (k + 1) / 2 ≤ n ∧ (n - k * (k + 1) / 2) % k = 0 then 1 else 0

/-- A285891: T(n,k) = n*A237048(n,k). -/
def T (n k : ℕ) : ℕ := n * A237048 n k

/-- The `k` consecutive parts `m+1, m+2, ..., m+k`. -/
def consecParts (m k : ℕ) : List ℕ := (List.range k).map (fun i => m + 1 + i)

theorem main : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k * (k + 1) / 2 ≤ n →
    T n k = ∑ m ∈ Finset.range (n + 1),
      (if (consecParts m k).sum = n then (consecParts m k).sum else 0) := by
  sorry

end OMA.S_oeis_a285891
