import Mathlib

/-!
# A365658: strictly positive rows of the triangle of partitions by number of distinct subsums

Source: https://oeis.org/A365658
Credit: @avivorly

A365658 (%N): Triangle read by rows where T(n,k) is the number of integer partitions of n with k distinct possible
sums of nonempty submultisets.

A048166 (%N): Numbers k that are divisible by the number of unitary divisors of k (A034444).

Conjecture (in the entry, %C): Positions of strictly positive rows are given by A048166.

Conventions:
- An integer partition of `n` is a `Nat.Partition n`: a multiset `p.parts` of positive integers with sum `n`.
- A submultiset of `p.parts` is a member of `p.parts.powerset` (`Multiset.powerset` lists each submultiset once per
  choice of positions, as the entry's `Subsets` does; only the set of sums is kept, so repetitions do not matter).
  The empty submultiset is the multiset `0`, so filtering `(· ≠ 0)` keeps exactly the nonempty submultisets (the
  entry's `Rest[Subsets[#]]`). Since all parts are positive, a submultiset is empty if and only if its sum is `0`;
  so this is the same as removing the sum `0` from the set of all submultiset sums.
- `subsums p` is the finite set of these sums, and `T n k` is the number of partitions `p` of `n` with exactly `k`
  distinct such sums. Row `n` (offset 1) consists of `T n k` for `k = 1, ..., n`, as in the entry's `%e` and `%t`
  (for `n ≥ 1` every partition of `n` has at least `1` and at most `n` distinct sums, all in `1, ..., n`).
- Row `n` is strictly positive when `0 < T n k` for every `1 ≤ k ≤ n`; its position is `n`.
- A unitary divisor of `n` is a divisor `d` of `n` with `gcd(d, n / d) = 1`; A034444(n) is their number (it equals
  `2 ^ omega(n)`). `Nat.divisors n` is the set of positive divisors of `n` (for `n ≥ 1`), and `n / d` is exact there.
- The conjecture says that for every `n ≥ 1`, row `n` is strictly positive if and only if `n` is a term of A048166.
-/

namespace OMA.S_oeis_a365658

/-- The distinct sums of the nonempty submultisets of the parts of the partition `p`. -/
def subsums {n : ℕ} (p : Nat.Partition n) : Finset ℕ :=
  ((p.parts.powerset.filter (· ≠ 0)).map Multiset.sum).toFinset

/-- `T n k`: the number of partitions of `n` with exactly `k` distinct sums of nonempty submultisets. -/
def T (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n => (subsums p).card = k)).card

/-- The number of unitary divisors of `n` (A034444): divisors `d` of `n` with `gcd(d, n / d) = 1`. -/
def unitaryDivisorCount (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter (fun d => Nat.Coprime d (n / d))).card

theorem main :
    ∀ n : ℕ, 1 ≤ n → ((∀ k : ℕ, 1 ≤ k → k ≤ n → 0 < T n k) ↔ unitaryDivisorCount n ∣ n) := by
  sorry

end OMA.S_oeis_a365658
