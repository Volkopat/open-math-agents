import Mathlib

/-!
# A011541: taxicab numbers and their distinct prime factors

Source: https://oeis.org/A011541
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A011541): the number of distinct prime factors of `Ta(n)` is strictly
increasing as `n` grows, but never exceeds `2n`, where `Ta(n)` is the smallest number that is
the sum of 2 positive integral cubes in `n` ways.

Conventions:
* "In `n` ways": at least `n` unordered representations `x³ + y³` with `1 ≤ x ≤ y` (the usual
  definition of the taxicab numbers `Ta(n)`; `Ta(1) = 2`, `Ta(2) = 1729`).
* `Ta(n)` exists for every `n ≥ 1` (Hardy–Wright); the statement is for `n ≥ 1`.
-/

namespace OMA.S_oeis_a011541

/-- The number of representations `m = x³ + y³` with `1 ≤ x ≤ y`. -/
def reps (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => p.1 ≤ p.2 ∧ p.1 ^ 3 + p.2 ^ 3 = m)).card

/-- `Ta(n)`: the least `m` with at least `n` representations. -/
noncomputable def Ta (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ n ≤ reps m}

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (Ta n).primeFactors.card < (Ta (n + 1)).primeFactors.card ∧
        (Ta n).primeFactors.card ≤ 2 * n := by
  sorry

end OMA.S_oeis_a011541
