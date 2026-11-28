import OMAStatements.S_mo_315770
import Mathlib

-- Reduction mo-315770.R1 of MathOverflow 315770 (Zhi-Wei Sun)
-- Credit: @marcusbuffett

/-!
# MathOverflow 315770: prime powers, and the open rest

Sun conjectured that `∑_{d ∣ n} 1/(d+1)` is never an integer. This splits off the case where `n`
is a prime power `p^k` (including `n = 1 = p^0`), where elementary arguments settle it. This is
a partial case, not progress on the conjecture for numbers with two or more prime factors.

* `H1`: for a prime `p` and any `k`, the sum over the divisors `1, p, …, p^k` is not an integer.
  For `p = 2` only the divisor `1` contributes an even denominator, so the sum is `1/2` plus a
  fraction with odd denominator. For odd `p` the sum lies strictly between `0` and `1`, by the
  bound `∑_{i ≤ k} 1/(p^i+1) ≤ 1 - 1/(2 p^k)` (induction on `k`).
* `H2`: `n` with at least two distinct prime factors. This is the open conjecture.
-/

namespace OMA.R_mo_315770_R1

/-- Prime powers: the divisor sum is not an integer. -/
def H1 : Prop :=
  ∀ p k : ℕ, p.Prime → ∀ z : ℤ, ∑ d ∈ (p ^ k).divisors, (1 : ℚ) / ((d : ℚ) + 1) ≠ z

/-- The open part: `n` is not a prime power. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → (∀ p k : ℕ, p.Prime → n ≠ p ^ k) →
    ∀ z : ℤ, ∑ d ∈ n.divisors, (1 : ℚ) / ((d : ℚ) + 1) ≠ z

theorem main : H1 → H2 → type_of% @OMA.S_mo_315770.main := by
  intro h1 h2 n hn z
  by_cases hpp : ∃ p k : ℕ, p.Prime ∧ n = p ^ k
  · obtain ⟨p, k, hp, rfl⟩ := hpp
    exact h1 p k hp z
  · push_neg at hpp
    exact h2 n hn hpp z

end OMA.R_mo_315770_R1
