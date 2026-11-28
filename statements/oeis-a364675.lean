import Mathlib

/-!
# A364675: the strict version is A154402

Source: https://oeis.org/A364675
Credit: @avivorly

A364675 (Gus Wiseman, Aug 2023): Number of integer partitions of n whose nonzero first differences are a
submultiset of the parts. The entry's example: the partition y = (3,2,1,1) has first differences (1,1,0), and
(1,1) is a submultiset of y, so y is counted under a(7).

Conjecture (in the entry): The strict version is A154402.
(Also in the entry: The strict case (no differences of 0) appears to be A154402.)

A154402: Inverse Moebius transform of Fredholm-Rueppel sequence, cf. A036987.
A036987 (the Fredholm-Rueppel sequence): `A036987 m = 1` if `m = 2^k - 1` for some `k ≥ 0`, else `0`.
So `A154402 n = ∑_{d ∣ n} A036987 d`, with offset 1.

This file states only the second conjecture of the entry. The first one (Conjecture: For subsets of {1..n}
instead of partitions of n we have A101925) is not part of this statement.

Conventions:
- First differences are taken of the parts in decreasing order: with `l` the parts sorted in decreasing order,
  the differences are `l[i] - l[i+1]` (all `≥ 0`), that is `List.zipWith (· - ·) l l.tail`.
- Submultiset is multiset inclusion `≤`. `Good p` keeps the filter to the nonzero differences, so it is
  A364675's own predicate; the strict version adds that the parts are distinct (`p.parts.Nodup`), in which case
  no difference is `0`.
- The claim is for `n ≥ 1`, the offset of A154402. (At `n = 0` the empty partition is counted once, while the
  sum over the divisors of `0` is empty.)
-/

namespace OMA.S_oeis_a364675

/-- `p` is counted by A364675: with `l` the parts of `p` in decreasing order and `d` the first differences
`l[i] - l[i+1]`, the multiset of the nonzero entries of `d` is a submultiset of the parts of `p`. -/
def Good {n : ℕ} (p : Nat.Partition n) : Prop :=
  let l := p.parts.sort (· ≥ ·)
  let d := List.zipWith (· - ·) l l.tail
  ((d.filter (· ≠ 0) : List ℕ) : Multiset ℕ) ≤ p.parts

/-- `Good` is decidable: multiset inclusion is decidable. -/
instance decGood {n : ℕ} : DecidablePred (Good (n := n)) := fun p => by
  dsimp only [Good]
  infer_instance

/-- The strict version of A364675: the number of partitions of `n` into distinct parts that satisfy `Good`. -/
def strictCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n => p.parts.Nodup ∧ Good p)).card

open scoped Classical in
/-- A036987, the Fredholm-Rueppel sequence: `1` if `m = 2^k - 1` for some `k ≥ 0`, else `0`. -/
noncomputable def A036987 (m : ℕ) : ℕ := if ∃ k : ℕ, m = 2 ^ k - 1 then 1 else 0

/-- A154402: the inverse Moebius transform of A036987, `A154402 n = ∑_{d ∣ n} A036987 d`. -/
noncomputable def A154402 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, A036987 d

/-- The strict version of A364675 is A154402 (for `n ≥ 1`). -/
theorem main : ∀ n : ℕ, 1 ≤ n → strictCount n = A154402 n := by
  sorry

end OMA.S_oeis_a364675
