import Mathlib

/-!
# A000705: ratios of consecutive superior highly composite numbers

Source: https://oeis.org/A000705
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Ramanujan asserted (listed in A000705) that the ratio of consecutive superior highly composite
numbers is always prime; the argument depends on an unproved transcendence statement.

Conventions:
* `n ≥ 1` is superior highly composite if for some `ε > 0`, `d(n)/n^ε ≥ d(k)/k^ε` for every
  `k ≥ 1`, where `d` is the number of divisors (Ramanujan's definition, as in A002201).
* Consecutive: `m < n` both superior highly composite with none strictly between. The ratio is
  prime means `n = p m` for a prime `p`.
-/

namespace OMA.S_oeis_a000705

/-- Superior highly composite numbers. -/
def IsSHC (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, 1 ≤ k →
    (k.divisors.card : ℝ) / (k : ℝ) ^ ε ≤ (n.divisors.card : ℝ) / (n : ℝ) ^ ε

theorem main :
    ∀ m n : ℕ, IsSHC m → IsSHC n → m < n → (∀ k, m < k → k < n → ¬ IsSHC k) →
      ∃ p : ℕ, p.Prime ∧ n = p * m := by
  sorry

end OMA.S_oeis_a000705
