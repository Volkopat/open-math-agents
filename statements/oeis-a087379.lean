import Mathlib

/-!
# A087379: Primes with distinct composite successive differences

Source: https://oeis.org/A087379
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Beginning with 2, primes such that the difference between two successive terms
is a distinct composite number (greedily choosing the smallest such prime at
each step). Conjecture: Let a(m+1) - a(m) be composite(k). Then there exists a
constant C such that m < C * k.
-/

namespace OMA.S_oeis_a087379

/-- A natural number is composite if it is greater than 1 and not prime. -/
def IsComposite (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime

/-- The `k`-th composite number (1-indexed: `composite 1 = 4`, `composite 2 = 6`, ...). -/
noncomputable def composite (k : ℕ) : ℕ :=
  Nat.nth IsComposite (k - 1)

/-- Successive differences of a list of natural numbers. -/
def diffs : List ℕ → List ℕ
  | a :: b :: rest => (b - a) :: diffs (b :: rest)
  | _ => []

/-- The list `[a(1), ..., a(m)]` of the first `m` terms of A087379. -/
noncomputable def seqList : ℕ → List ℕ
  | 0 => []
  | 1 => [2]
  | n + 2 =>
      let prev := seqList (n + 1)
      let last := prev.getLastD 2
      let used := diffs prev
      let next := sInf {p : ℕ | last < p ∧ p.Prime ∧ IsComposite (p - last) ∧ (p - last) ∉ used}
      prev ++ [next]

/-- The `m`-th term `a(m)` of A087379 (1-indexed, with `a 1 = 2`). -/
noncomputable def a (m : ℕ) : ℕ :=
  (seqList m).getLastD 0

theorem main :
    ∃ C : ℝ, 0 < C ∧ ∀ m k : ℕ, 1 ≤ m → 1 ≤ k →
      a (m + 1) - a m = composite k → (m : ℝ) < C * (k : ℝ) := by
  sorry

end OMA.S_oeis_a087379
