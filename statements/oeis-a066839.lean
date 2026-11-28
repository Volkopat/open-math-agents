import Mathlib

/-!
# A066839: the divisors up to sqrt(n) count the parts of partitions into parts differing by 2

Source: https://oeis.org/A066839
Credit: @ivillar

Status: known result: the entry records that the conjecture is true (N. J. A. Sloane, Dec 02 2020).

A066839 (offset 1): a(n) is the sum of the positive divisors k of n with k ≤ sqrt(n);
data 1, 1, 1, 3, 1, 3, 1, 3, 4, 3, 1, 6, ...

Conjecture (Omar E. Pol, May 03 2020): a(n) is the total number of parts in all partitions of n
into consecutive parts that differ by 2. N. J. A. Sloane (Dec 02 2020) records in the entry that
the conjecture is true.

Formalization: k ≤ sqrt(n) is written k * k ≤ n. A partition of n into consecutive parts that
differ by 2 is a sum m + (m+2) + ... + (m + 2(k-1)) = n with k ≥ 1 parts and least part m ≥ 1 (one
part is allowed); it is determined by the pair (k, m), and both k and m are at most n. The total
number of parts is the sum of k over all such pairs.
-/

namespace OMA.S_oeis_a066839

/-- a(n): the sum of the divisors k of n with k * k ≤ n. -/
def a (n : ℕ) : ℕ := ∑ k ∈ n.divisors.filter (fun k => k * k ≤ n), k

/-- The total number of parts in all partitions of n into consecutive parts that differ by 2:
the sum of k over the pairs (k, m) with m + (m+2) + ... + (m + 2(k-1)) = n. -/
def totalParts (n : ℕ) : ℕ :=
  ∑ p ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
      (fun p : ℕ × ℕ => ∑ i ∈ Finset.range p.1, (p.2 + 2 * i) = n), p.1

/-- Pol's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = totalParts n := by
  sorry

end OMA.S_oeis_a066839
