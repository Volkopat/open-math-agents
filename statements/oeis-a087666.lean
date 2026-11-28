import Mathlib

/-!
# A087666: Steps to reach an integer under b(0) = n/3, b(k+1) = b(k) * floor(b(k))

Source: https://oeis.org/A087666
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Consider the recurrence b(0) = n/3, b(k+1) = b(k) * floor(b(k)); a(n) is the
least k such that b(k) is an integer, or -1 if no integer is ever reached.
Conjectures:
(1) An integer is always reached if n/3 >= 2 (i.e. n >= 6).
(2) a(6) + a(7) + ... + a(n) = 2*n + O(sqrt(n)).
-/

namespace OMA.S_oeis_a087666

/-- The rational recurrence `b(0) = n/3`, `b(k+1) = b(k) * floor(b(k))`. -/
def b (n : ℕ) : ℕ → ℚ
  | 0 => (n : ℚ) / 3
  | k + 1 => b n k * (⌊b n k⌋ : ℚ)

/-- The least `k` such that `b n k` is an integer (or `0` if none exists). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | (b n k).den = 1}

theorem main :
    (∀ n : ℕ, 6 ≤ n → ∃ k : ℕ, (b n k).den = 1) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 6 ≤ n →
      |(∑ m ∈ Finset.Icc 6 n, (a m : ℝ)) - 2 * (n : ℝ)| ≤ C * Real.sqrt (n : ℝ)) := by
  sorry

end OMA.S_oeis_a087666
