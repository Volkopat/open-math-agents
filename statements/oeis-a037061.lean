import Mathlib

/-!
# OEIS A037061: Smallest Prime Containing Exactly n 4's

Source: https://oeis.org/A037061
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $a(n)$ be the smallest prime whose base-10 representation contains exactly $n$
occurrences of the digit $4$.

Conjecture: For every $n \ge 0$, $a(n)$ equals $\lfloor 10^{n+1}/9 \rfloor \cdot 40 + b$
with $1 \le b \le 9$ and one of the first $n+1$ digits $4$ replaced by a digit in $\{0, 1, 2, 3\}$.
-/

namespace OMA.S_oeis_a037061

/-- Number of occurrences of digit `d` in the base-10 representation of `p`. -/
def countDigit (d p : ℕ) : ℕ :=
  (Nat.digits 10 p).count d

/-- `IsLeastPrimeWithDigits d n p` holds when `p` is the smallest prime with exactly `n`
occurrences of base-10 digit `d`. -/
def IsLeastPrimeWithDigits (d n p : ℕ) : Prop :=
  Nat.Prime p ∧ countDigit d p = n ∧
    ∀ q < p, Nat.Prime q → countDigit d q ≠ n

theorem main :
    ∀ n p : ℕ, IsLeastPrimeWithDigits 4 n p →
      ∃ b k c : ℕ, 1 ≤ b ∧ b ≤ 9 ∧ 1 ≤ k ∧ k ≤ n + 1 ∧ c < 4 ∧
        p + (4 - c) * 10 ^ k = (10 ^ (n + 1) / 9) * 40 + b := by
  sorry

end OMA.S_oeis_a037061
