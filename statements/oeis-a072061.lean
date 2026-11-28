import Mathlib

/-!
# A072061: Generalization of Beatty-like sequence a(2n)/a(2n-1) -> k + sqrt(k^2 + 1)

Source: https://oeis.org/A072061
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
For any real `k > 0`, define `{a(n)}_{n ≥ 1}` by `a(1) = 1` and, for `n > 1`:
- if `n` is even, `a(n) = a(n - 1) + ⌊k * n⌋`;
- if `n` is odd, `a(n)` is the smallest positive integer not yet appearing in `{a(1), ..., a(n - 1)}`.
Then `a(2*n) / a(2*n - 1) → k + sqrt(k^2 + 1)` as `n → ∞`.

Conventions:
- `IsGenSeq k a` characterizes the 1-indexed sequence `a : ℕ → ℕ`.
-/

namespace OMA.S_oeis_a072061

def IsGenSeq (k : ℝ) (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧
  (∀ m : ℕ, m ≥ 1 → a (2 * m) = a (2 * m - 1) + Nat.floor (k * (2 * m : ℝ))) ∧
  (∀ m : ℕ, m ≥ 1 →
    a (2 * m + 1) ≥ 1 ∧
    (∀ j ∈ Finset.Icc 1 (2 * m), a j ≠ a (2 * m + 1)) ∧
    (∀ v : ℕ, 1 ≤ v → v < a (2 * m + 1) → ∃ j ∈ Finset.Icc 1 (2 * m), a j = v))

theorem main :
    ∀ k : ℝ, k > 0 →
      ∀ a : ℕ → ℕ, IsGenSeq k a →
        Filter.Tendsto
          (fun n : ℕ => (a (2 * n) : ℝ) / (a (2 * n - 1) : ℝ))
          Filter.atTop (nhds (k + Real.sqrt (k ^ 2 + 1))) := by
  sorry

end OMA.S_oeis_a072061
