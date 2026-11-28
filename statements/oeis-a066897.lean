import Mathlib

/-!
# OEIS A066897: Alternating Sum of Partition Parts Equals Total Number of Odd Parts

Source: https://oeis.org/A066897
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

For a partition $p = [p_1, p_2, p_3, \ldots]$ of $n$ with parts sorted in nonincreasing order
$p_1 \ge p_2 \ge p_3 \ge \cdots$, let $f(p) = p_1 - p_2 + p_3 - \cdots$ be the alternating
sum of its parts, and let $F(n) = \sum_{p \vdash n} f(p)$.

Conjecture: For every $n \ge 1$, $F(n)$ equals the total number of odd parts across all
partitions of $n$.
-/

namespace OMA.S_oeis_a066897

/-- Alternating sum `l[0] - l[1] + l[2] - ...` of a list of natural numbers. -/
def altSum : List ℕ → ℤ
  | [] => 0
  | x :: xs => (x : ℤ) - altSum xs

/-- Parts of a partition `p` sorted in nonincreasing order. -/
def sortedParts {n : ℕ} (p : Nat.Partition n) : List ℕ :=
  p.parts.sort (· ≥ ·)

/-- Total number of odd parts in all partitions of `n`. -/
def totalOddParts (n : ℕ) : ℕ :=
  ∑ p : Nat.Partition n, (p.parts.filter (fun k => k % 2 = 1)).card

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (∑ p : Nat.Partition n, altSum (sortedParts p)) = (totalOddParts n : ℤ) := by
  sorry

end OMA.S_oeis_a066897
