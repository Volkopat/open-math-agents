import Mathlib

/-!
# A084760: Squarefree numbers in ascending order such that the difference of successive
terms is unique.

Source: https://oeis.org/A084760
Credit: @cjchaffin

Conjecture (stated on the OEIS page): every number is a term of the sequence of first
differences. For every number `r` there exists some `k` such that `a(k) - a(k-1) = r`.

Conventions:
- The sequence has offset 1 and begins `a 1 = 2` (1 is squarefree but is not a term). Each
  later term is the least squarefree integer larger than the previous term whose difference
  from that previous term has not already occurred, as in the example: after 5 the next term
  is 10, not 6 or 7, because those differences 1 and 2 were already used.
- First differences of a strictly increasing sequence are positive, so `r` runs over the
  positive integers.
-/

namespace OMA.S_oeis_a084760

/-- Differences `a 2 - a 1, …, a n - a (n-1)` already used after `n` terms (`n ≥ 1`). -/
def usedDiffs (a : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).image (fun k => a k - a (k - 1))

/-- A squarefree integer `m > a n` is eligible as `a (n+1)` if the new difference is fresh. -/
def eligible (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  a n < m ∧ Squarefree m ∧ (m - a n) ∉ usedDiffs a n

/-- `a` is the greedy listing defined on the OEIS page, starting at `a 1 = 2`. -/
def IsGreedy (a : ℕ → ℕ) : Prop :=
  a 1 = 2 ∧
    ∀ n : ℕ, 1 ≤ n →
      eligible a n (a (n + 1)) ∧ ∀ m : ℕ, eligible a n m → a (n + 1) ≤ m

theorem main :
    ∃ a : ℕ → ℕ, IsGreedy a ∧ ∀ r : ℕ, 0 < r → ∃ k : ℕ, 2 ≤ k ∧ a k - a (k - 1) = r := by
  sorry

end OMA.S_oeis_a084760
