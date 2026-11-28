import Mathlib

/-!
# OEIS A027619: Hofstadter Q(k) = k/2, quadratic growth

Source: https://oeis.org/A027619
`a n` lists the `k` such that the Hofstadter `Q`-sequence satisfies `Q(k) = k/2`
(2, 50, 56, 128, …). Conjecture: `a(n)/n²` is bounded.

Conventions. `Q 1 = Q 2 = 1` and `Q n = Q (n - Q (n-1)) + Q (n - Q (n-2))` for `n ≥ 3`;
`QList` builds the values (`Q 0 = 0` is a placeholder; the recursion only reads indices
`≥ 1` as long as the sequence is defined, which is the standard expectation). `Q k = k/2` is
read as `2 Q k = k`. `a n` is indexed from `1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a027619

/-- `[Q 0, Q 1, …, Q n]` with the placeholder `Q 0 = 0`. -/
def QList : ℕ → List ℕ
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 1, 1]
  | n + 3 =>
      let l := QList (n + 2)
      l ++ [l.getD (n + 3 - l.getD (n + 2) 0) 0 + l.getD (n + 3 - l.getD (n + 1) 0) 0]

/-- The Hofstadter `Q`-sequence. -/
def Q (n : ℕ) : ℕ := (QList n).getD n 0

/-- A027619, indexed from `1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => 1 ≤ k ∧ 2 * Q k = k) (n - 1)

theorem main : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → (a n : ℝ) ≤ C * (n : ℝ) ^ 2 := by
  sorry

end OMA.S_oeis_a027619
