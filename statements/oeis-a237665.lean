import Mathlib

/-!
# A237665: Number of partitions of n such that the distinct terms arranged in increasing order form a string of two or more consecutive integers.

Source: https://oeis.org/A237665
Credit: @maaaakks

Conjecture (George Beck, May 06 2017), from the OEIS comments:
"a(n) = sum of smallest parts in the distinct partitions of n with an even number of parts."
A later comment states: "The preceding conjecture is correct (see Chern, 2019)."

Reading and indexing.
* The OEIS offset is 0 and the data begins `0, 0, 0, 1, 1, 3, 3, 6, ...` (a(0) = 0).
* `a n` counts partitions `p` of `n` (Mathlib's `Nat.Partition n`) whose set of distinct
  parts is `{m, m+1, ..., m+r}` for some `m` and some `r ≥ 1` ("two or more consecutive
  integers"). Since parts are positive, `m ≥ 1` automatically.
* The right-hand side sums, over the partitions of `n` into distinct parts
  (`p.parts.Nodup`) with a positive even number of parts, the smallest part of `p`.
  The empty partition of `0` has `0` parts (even) but no smallest part; we exclude it
  explicitly (`p.parts ≠ 0`). With this convention the right-hand side at `n = 0` is `0`,
  matching a(0) = 0, so the identity is stated for every `n ≥ 0` (the full OEIS range).
  (Including the empty partition with smallest part `0` would give the same value.)
-/

namespace OMA.S_oeis_a237665

/-- The distinct parts of `p` form a string `{m, m+1, …, m+r}` of at least two
consecutive integers. -/
def ConsecutiveDistinctParts {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∃ m r : ℕ, 1 ≤ r ∧ p.parts.toFinset = Finset.Icc m (m + r)

open Classical in
/-- A237665(n): the number of partitions of `n` whose distinct parts form a string of two
or more consecutive integers. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n => ConsecutiveDistinctParts p)).card

/-- The smallest part of a partition (`0` for the empty partition, a case never used). -/
def smallestPart {n : ℕ} (p : Nat.Partition n) : ℕ :=
  if h : p.parts.toFinset.Nonempty then p.parts.toFinset.min' h else 0

/-- Sum of the smallest parts over the partitions of `n` into distinct parts having a
positive even number of parts. -/
def sumSmallestEvenDistinct (n : ℕ) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter
      (fun p => p.parts.Nodup ∧ p.parts ≠ 0 ∧ Even (Multiset.card p.parts)),
    smallestPart p

theorem main : ∀ n : ℕ, a n = sumSmallestEvenDistinct n := by
  sorry

end OMA.S_oeis_a237665
