import Mathlib

/-!
# OEIS A037071: Smallest Prime Containing Exactly n 9's

Source: https://oeis.org/A037071
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $a(n)$ be the smallest prime whose base-10 representation contains exactly $n$
occurrences of the digit $9$.

Conjecture: For every $n \ge 0$, $a(n)$ equals $\lfloor 10^{n+1}/9 \rfloor \cdot 9 = 10^{n+1} - 1$
with one of its $n+1$ digits $9$ replaced by a digit in $\{1, 2, 4, 5, 7, 8\}$.
-/

namespace OMA.S_oeis_a037071

/-- Number of occurrences of digit `d` in the base-10 representation of `p`. -/
def countDigit (d p : ℕ) : ℕ :=
  (Nat.digits 10 p).count d

/-- `IsLeastPrimeWithDigits d n p` holds when `p` is the smallest prime with exactly `n`
occurrences of base-10 digit `d`. -/
def IsLeastPrimeWithDigits (d n p : ℕ) : Prop :=
  Nat.Prime p ∧ countDigit d p = n ∧
    ∀ q < p, Nat.Prime q → countDigit d q ≠ n

theorem main :
    ∀ n p : ℕ, IsLeastPrimeWithDigits 9 n p →
      ∃ k c : ℕ, k ≤ n ∧ c ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ) ∧
        p + (9 - c) * 10 ^ k = (10 ^ (n + 1) / 9) * 9 := by
  sorry

end OMA.S_oeis_a037071
