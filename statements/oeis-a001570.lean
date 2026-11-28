import Mathlib

/-!
# A001570: Perfect Powers Whose Squares Are Centered Hexagonal

Source: https://oeis.org/A001570
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A001570 consists of positive integers `k` such that `k^2` is a centered hexagonal number, i.e.,
`k^2 = 3 * n * (n + 1) + 1` for some `n : ℕ`.

Conjecture (implied by Beal's conjecture): The only perfect power `k = a^b` (`b ≥ 2`) in A001570
is `k = 1`.
-/

namespace OMA.S_oeis_a001570

/-- A natural number `m` is centered hexagonal if `m = 3 * n * (n + 1) + 1` for some `n : ℕ`. -/
def IsCenteredHexagonal (m : ℕ) : Prop :=
  ∃ n : ℕ, m = 3 * n * (n + 1) + 1

/-- A natural number `k` is a perfect power if `k = a ^ b` for some `a : ℕ` and `b ≥ 2`. -/
def IsPerfectPower (k : ℕ) : Prop :=
  ∃ a b : ℕ, 2 ≤ b ∧ k = a ^ b

theorem main :
    ∀ k : ℕ, 0 < k → IsCenteredHexagonal (k ^ 2) → IsPerfectPower k → k = 1 := by
  sorry

end OMA.S_oeis_a001570
