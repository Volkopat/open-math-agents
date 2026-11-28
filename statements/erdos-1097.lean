import Mathlib

/-!
# Erdős Problem 1097

Source: https://www.erdosproblems.com/1097
Credit: @mgv27

Let $A$ be a set of $n$ integers. How many distinct $d$ can occur as the common difference of a
three-term arithmetic progression in $A$? In particular, are there always $O(n^{3/2})$ many such
$d$?

Formalization notes:
* `main` states the specific question: there is a constant `C` such that every finite `A ⊆ ℤ`
  has at most `C * |A| ^ (3/2)` common differences of three-term progressions in `A`.
  The general question (the correct order of magnitude) asks for no specific statement.
* A common difference is counted as `d > 0`: `a, a + d, a + 2d ∈ A`. Counting `d ≠ 0` instead
  would exactly double the count, which does not change an `O(·)` bound.
* The source page records that this specific question has been answered negatively (Lemm, via
  the equivalence with a sums-differences question of Bourgain), so `main` is expected to be
  refutable; the order of magnitude itself remains open.
-/

namespace OMA.S_erdos_1097

/-- The positive common differences `d` of three-term arithmetic progressions `a, a + d, a + 2d`
contained in `A`. Every such `d` lies in `A - A`, so this is a finite set. -/
def apDiffs (A : Finset ℤ) : Finset ℤ :=
  ((A ×ˢ A).image (fun p => p.2 - p.1)).filter
    (fun d => 0 < d ∧ ∃ a ∈ A, a + d ∈ A ∧ a + 2 * d ∈ A)

/-- Erdős Problem 1097: are there always `O(n ^ (3/2))` such common differences? -/
theorem main : ∃ C : ℝ, ∀ A : Finset ℤ,
    ((apDiffs A).card : ℝ) ≤ C * (A.card : ℝ) ^ ((3 : ℝ) / 2) := by
  sorry

end OMA.S_erdos_1097
