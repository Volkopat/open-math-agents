import Mathlib

/-!
# OEIS A037059: Smallest Prime Containing Exactly n 3's

Source: https://oeis.org/A037059
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Let $a(n)$ be the smallest prime whose base-10 representation contains exactly $n$
occurrences of the digit $3$.

Conjecture: For every $n \ge 0$ with $n \ne 1$, $a(n)$ equals $\lfloor 10^{n+1}/3 \rfloor$
with one of its $n+1$ digits $3$ replaced by a digit in $\{1, 2, 4, 5, 7, 8\}$.
-/

namespace OMA.S_oeis_a037059

/-- Number of occurrences of digit `d` in the base-10 representation of `p`. -/
def countDigit (d p : ℕ) : ℕ :=
  (Nat.digits 10 p).count d

/-- `IsLeastPrimeWithDigits d n p` holds when `p` is the smallest prime with exactly `n`
occurrences of base-10 digit `d`. -/
def IsLeastPrimeWithDigits (d n p : ℕ) : Prop :=
  Nat.Prime p ∧ countDigit d p = n ∧
    ∀ q < p, Nat.Prime q → countDigit d q ≠ n

theorem main :
    ∀ n p : ℕ, n ≠ 1 → IsLeastPrimeWithDigits 3 n p →
      ∃ k c : ℕ, k ≤ n ∧ c ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ) ∧
        (p : ℤ) = ((10 ^ (n + 1) / 3 : ℕ) : ℤ) + ((c : ℤ) - 3) * (10 : ℤ) ^ k := by
  sorry

end OMA.S_oeis_a037059
