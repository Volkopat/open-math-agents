import Mathlib

/-!
# OEIS A059992: records of the number of nonprime divisors and highly composite numbers

Source: https://oeis.org/A059992
`A059992` lists the numbers with an increasing number of nonprime divisors (each has more
nonprime divisors than every smaller positive integer). Conjecture: this sequence includes
all highly composite numbers (A002182) except `2` and `6`.

Conventions. A divisor is nonprime if it is not a prime (`1` counts as nonprime). Highly
composite: `n ≥ 1` with more divisors than every smaller positive integer.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a059992

/-- Number of nonprime divisors of `n`. -/
def np (n : ℕ) : ℕ := (n.divisors.filter fun d => ¬ d.Prime).card

/-- `n` is highly composite. -/
def IsHighlyComposite (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → m.divisors.card < n.divisors.card

theorem main :
    ∀ n : ℕ, IsHighlyComposite n → n ≠ 2 → n ≠ 6 → ∀ m, 1 ≤ m → m < n → np m < np n := by
  sorry

end OMA.S_oeis_a059992
