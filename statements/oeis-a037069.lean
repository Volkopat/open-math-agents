import Mathlib

/-!
# OEIS A037069: Smallest Prime Containing Exactly n 8's

Source: https://oeis.org/A037069
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Let $a(n)$ be the smallest prime whose base-10 representation contains exactly $n$
occurrences of the digit $8$.

Conjecture: For every $n \ge 0$, $a(n)$ equals $\lfloor 10^{n+1}/9 \rfloor \cdot 80 + b$
with $1 \le b \le 9$ and one of the first $n+1$ digits $8$ replaced by a digit in $\{0, \ldots, 7\}$.
-/

namespace OMA.S_oeis_a037069

/-- Number of occurrences of digit `d` in the base-10 representation of `p`. -/
def countDigit (d p : ℕ) : ℕ :=
  (Nat.digits 10 p).count d

/-- `IsLeastPrimeWithDigits d n p` holds when `p` is the smallest prime with exactly `n`
occurrences of base-10 digit `d`. -/
def IsLeastPrimeWithDigits (d n p : ℕ) : Prop :=
  Nat.Prime p ∧ countDigit d p = n ∧
    ∀ q < p, Nat.Prime q → countDigit d q ≠ n

theorem main :
    ∀ n p : ℕ, IsLeastPrimeWithDigits 8 n p →
      ∃ b k c : ℕ, 1 ≤ b ∧ b ≤ 9 ∧ 1 ≤ k ∧ k ≤ n + 1 ∧ c < 8 ∧
        p + (8 - c) * 10 ^ k = (10 ^ (n + 1) / 9) * 80 + b := by
  sorry

end OMA.S_oeis_a037069
