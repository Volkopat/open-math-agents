import Mathlib

/-!
# OEIS A292510: the first k with an equal-sum split of the first k n-gonal numbers is 7 for n > 5

Source: https://oeis.org/A292510 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Seiichi Manyama, Sep 2017), offset 3: a(n) = smallest k >= 1 such that {1, p(n,2), p(n,3),
..., p(n,k)} can be partitioned into two sets with equal sums, where p(n,m) is m-th n-gonal number.
Comment: Conjecture: a(n) = 7 for n > 5. The formula section notes p(n,1) + p(n,2) + p(n,4) +
p(n,7) = p(n,3) + p(n,5) + p(n,6), so a(n) <= 7.

Formalization notes:
* p(n,m) = (n - 2) * C(m,2) + m, the standard m-th n-gonal number (n - 2) m (m - 1)/2 + m; it
  equals the entry's program formula m((n - 2)m - n + 4)/2, and p(n,1) = 1.
* A partition of {p(n,1), ..., p(n,k)} into two sets is given by the set A of indices in the first
  part; the second part is the rest of {1, ..., k}. For n >= 3 the map m -> p(n,m) is strictly
  increasing, so this is the same as partitioning the set of values. Equal sums of positive
  numbers force both parts to be nonempty.
* a(n) is the infimum of the k >= 1 that admit such a split; `main` says it is 7 for every n > 5
  (in particular such k exist).
* Controls proved in the proof file: the splits for a(3) = 4, a(4) = 7 and a(5) = 6.
-/

namespace OMA.S_oeis_a292510

/-- The m-th n-gonal number, (n - 2) * m * (m - 1) / 2 + m. -/
def p (n m : ℕ) : ℕ := (n - 2) * Nat.choose m 2 + m

/-- The numbers p(n,1), ..., p(n,k) can be split into two sets with equal sums. -/
def Splits (n k : ℕ) : Prop :=
  ∃ A ⊆ Finset.Icc 1 k, ∑ m ∈ A, p n m = ∑ m ∈ Finset.Icc 1 k \ A, p n m

/-- a(n): the smallest k >= 1 such that {1, p(n,2), ..., p(n,k)} splits into two equal sums. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ Splits n k}

/-- The conjecture: a(n) = 7 for every n > 5. -/
theorem main : ∀ n : ℕ, 5 < n → a n = 7 := by
  sorry

end OMA.S_oeis_a292510
