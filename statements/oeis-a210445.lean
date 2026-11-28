import Mathlib

/-!
# A210445: least `k` with `k n` practical

Source: https://oeis.org/A210445
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A210445): `a(n) < n` for all `n > 1`, and `a(n) < n/2` for all `n > 47`,
where `a(n)` is the least positive integer `k` with `k n` practical.

Conventions:
* `m` is practical if every positive integer `≤ m` is a sum of distinct divisors of `m`.
* `a(n) < n` is stated as: some `1 ≤ k < n` has `k n` practical; `a(n) < n/2` as: some `k ≥ 1`
  with `2k < n` has `k n` practical (real `n/2`).
-/

namespace OMA.S_oeis_a210445

/-- Practical numbers. -/
def IsPractical (m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ t : ℕ, 1 ≤ t → t ≤ m → ∃ s ⊆ m.divisors, ∑ d ∈ s, d = t

theorem main :
    (∀ n : ℕ, 1 < n → ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ IsPractical (k * n)) ∧
    (∀ n : ℕ, 47 < n → ∃ k : ℕ, 1 ≤ k ∧ 2 * k < n ∧ IsPractical (k * n)) := by
  sorry

end OMA.S_oeis_a210445
