import Mathlib

/-!
# A089708: a(n) = a(n-1) + sum of absolute differences of all pairs of previous terms

Source: https://oeis.org/A089708
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(1) = 1, a(2) = 2, a(n) = a(n-1) + d where d is the sum of the absolute
differences between all pairs of previous terms.
Conjecture: a(n) = c * n! * (1 + 2/n + (5/2)/n^2 + (31/6)/n^3 + (317/24)/n^4 + O(1/n^5)),
where c is about 0.1289432494744.
-/

namespace OMA.S_oeis_a089708

/-- Sum of |y - x| over all unordered pairs (x, y) in a list. -/
def pairDiffSum : List ℕ → ℕ
  | [] => 0
  | x :: xs => (xs.map (fun y => Int.natAbs ((y : ℤ) - (x : ℤ)))).sum + pairDiffSum xs

/-- List of the first n terms [a(1), ..., a(n)] of A089708. -/
def aList : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 2]
  | n + 1 =>
    let prev := aList n
    prev ++ [prev.getLastD 0 + pairDiffSum prev]

/-- The n-th term a(n) of A089708 (1-indexed). -/
def a (n : ℕ) : ℕ :=
  (aList n).getLastD 0

theorem main :
    ∃ c : ℝ, 0 < c ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ =>
          (a n : ℝ) / (Nat.factorial n : ℝ) -
          c * (1 + 2 / (n : ℝ) + (5 / 2 : ℝ) / (n : ℝ) ^ 2 +
            (31 / 6 : ℝ) / (n : ℝ) ^ 3 + (317 / 24 : ℝ) / (n : ℝ) ^ 4))
        (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 5) := by
  sorry

end OMA.S_oeis_a089708
