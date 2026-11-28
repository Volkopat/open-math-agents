import Mathlib

/-!
# A008319: Smallest number that is sum of squares of distinct earlier terms.

Source: https://oeis.org/A008319
Credit: @maaaakks

Sequence (offset 1): 1, 1, 2, 4, 5, 6, 16, 17, 18, 20, 21, 22, 25, 26, 27, 29, 30, 31, 36, ...

The sequence starts with `a(1) = a(2) = 1`; for `n ≥ 2`, `a(n+1)` is the smallest number greater
than `a(n)` that is a sum of squares of distinct earlier terms `a(1), …, a(n)`. "Distinct" refers
to distinct positions, so the two initial 1's may both be used (e.g. `a(3) = 2 = 1² + 1²`).
Equivalently, `a(n+1)` is the least `m > a(n)` such that `m = ∑_{i ∈ S} a(i)²` for some
`S ⊆ {1, …, n}`; this is encoded below by summing the squares of a sublist of `[a(1), …, a(n)]`.

Comment by Giovanni Resta (Oct 06 2011):
"Up to a(99999680)=10^8, the largest number not in the sequence is 892."

Resta's conjecture is that 892 is the largest positive integer not in the sequence, i.e. 892 is
not a term and every integer greater than 892 is a term. (Charles R Greathouse IV, Oct 06 2011:
"Resta's conjecture is correct. ... all numbers greater than 1935 (and hence greater than 892)
are in this sequence.")
-/

namespace OMA.S_oeis_a008319

/-- `m` is a sum of squares of distinct entries (distinct positions) of the list `l`,
i.e. `m` is the sum of the squares of the entries of some sublist of `l`. -/
def IsSumSqOf (l : List ℕ) (m : ℕ) : Prop :=
  ∃ s ∈ l.sublists, (s.map (· ^ 2)).sum = m

instance (l : List ℕ) (m : ℕ) : Decidable (IsSumSqOf l m) := by
  unfold IsSumSqOf; infer_instance

/-- Any such sum is at most the sum of the squares of all entries of `l`, so the search for
a candidate can be bounded; this makes the existence of a candidate decidable. -/
instance (l : List ℕ) (p : ℕ) : Decidable (∃ m, p < m ∧ IsSumSqOf l m) :=
  decidable_of_iff (∃ m < (l.map (· ^ 2)).sum + 1, p < m ∧ IsSumSqOf l m) <| by
    constructor
    · rintro ⟨m, -, hm⟩
      exact ⟨m, hm⟩
    · rintro ⟨m, hpm, s, hs, rfl⟩
      refine ⟨_, Nat.lt_succ_of_le ?_, hpm, s, hs, rfl⟩
      exact ((List.mem_sublists.mp hs).map _).sum_le_sum (fun _ _ => Nat.zero_le _)

/-- The least `m > p` that is a sum of squares of distinct entries of `l`
(the junk value `0` is never used for the actual sequence). -/
def next (l : List ℕ) (p : ℕ) : ℕ :=
  if h : ∃ m, p < m ∧ IsSumSqOf l m then Nat.find h else 0

/-- `terms n = [a(1), a(2), …, a(n)]`. -/
def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 1]
  | n + 3 => terms (n + 2) ++ [next (terms (n + 2)) ((terms (n + 2)).getLast?.getD 0)]

/-- `a n` is the `n`-th term of A008319 (offset 1; `a 0 = 0` is a junk value). -/
def a (n : ℕ) : ℕ := (terms n).getLast?.getD 0

/-- Resta's conjecture: 892 is the largest number not in the sequence. -/
theorem main :
    (¬ ∃ n, 1 ≤ n ∧ a n = 892) ∧ ∀ m : ℕ, 892 < m → ∃ n, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a008319
