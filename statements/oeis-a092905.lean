import Mathlib

/-!
# A092905: Triangle, read by rows, such that the partial sums of the n-th row form the n-th diagonal, for n>=0, where each row begins with 1.

Source: https://oeis.org/A092905
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

## The conjecture

OEIS A092905, offset 0, COMMENTS line (Wolfdieter Lang, Dec 03 2012):

> The triangle with entry a(n,m) = T(n-1,m-1), n >= 1, m = 1, ..., n, is obtained from the
> partition array A103921 when in row n all entries belonging to part number m are summed
> (a conjecture).

with the example

> T(5,3) = a(6,4) = 4 because the partitions of 6 with 4 parts are 1113 and 1122, with the
> number of distinct parts 2 and 2, respectively, summing to 4 (see the array A103921).

A103921 is the irregular triangle whose row `n` lists the numbers of distinct parts of the
partitions of `n` (in Abramowitz-Stegun order, which groups the partitions of `n` by their
number of parts). So the conjecture says: for `n ≥ 1` and `1 ≤ m ≤ n`, the sum, over the
partitions of `n` into exactly `m` parts, of the number of distinct parts equals `T(n-1, m-1)`.

## Modelling choices

* `T` is the triangle A092905 given by its FORMULA line
  `T(n, k) = sum_{j=0..k} T(n-k, j), with T(n, 0) = 1 for all n>=0`, for `0 ≤ k ≤ n`.
  Entries outside the triangle (`k > n`), which occur in that sum when `j > n - k`, are `0`.
  This definition reproduces the DATA line of the entry
  (`1, 1,1, 1,2,1, 1,3,2,1, 1,4,4,2,1, ...`).
* Partitions are Mathlib's `Nat.Partition n` (multisets of positive integers summing to `n`);
  "part number m" means the partition has exactly `m` parts (counted with multiplicity,
  `Multiset.card p.parts = m`, as in the example: 1113 and 1122 have 4 parts), and the number
  of distinct parts is `p.parts.toFinset.card`. The order of the partitions inside a row of
  A103921 plays no role in the sum.
* The identity is stated in `ℕ` on exactly the range of the source: `n ≥ 1`, `1 ≤ m ≤ n`.
-/

namespace OMA.S_oeis_a092905

/-- The triangle A092905: `T n 0 = 1`, `T n k = ∑_{j=0..k} T (n-k) j` for `1 ≤ k ≤ n`,
and `T n k = 0` outside the triangle (`k > n`). -/
def T : ℕ → ℕ → ℕ
  | _, 0 => 1
  | n, k + 1 =>
    if h : k + 1 ≤ n then ∑ j ∈ Finset.range (k + 2), T (n - (k + 1)) j else 0
termination_by n => n
decreasing_by omega

/-- Row `n` of A103921 summed over the partitions with exactly `m` parts: the total number of
distinct parts of the partitions of `n` into exactly `m` parts. -/
def a (n m : ℕ) : ℕ :=
  ∑ p ∈ Finset.univ.filter (fun p : Nat.Partition n => Multiset.card p.parts = m),
    p.parts.toFinset.card

/-- Wolfdieter Lang's conjecture (Dec 03 2012): `a(n,m) = T(n-1,m-1)` for `n ≥ 1`,
`m = 1, ..., n`. -/
theorem main : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ n → a n m = T (n - 1) (m - 1) := by
  sorry

end OMA.S_oeis_a092905
