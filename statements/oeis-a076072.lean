import Mathlib

/-!
# A076072: Largest multiple of n that can be formed by using the digits of the next n numbers, or 0 if no such number exists.

Source: https://oeis.org/A076072
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: No entry is zero. (At least one multiple of n can be formed by using the digits of the next n numbers.)
-/

namespace OMA.S_oeis_a076072

/-- Multiset of base-10 digits of the next `n` integers `n + 1, ..., 2 * n`. -/
def nextDigits (n : ℕ) : Multiset ℕ :=
  (Finset.Icc (n + 1) (2 * n)).sum (fun k => (Nat.digits 10 k : Multiset ℕ))

/-- Largest positive multiple of `n` whose base-10 digits form the multiset `nextDigits n`, or 0. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {m : ℕ | 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m : Multiset ℕ) = nextDigits n}

/-- Conjecture: no entry of A076072 is zero. -/
theorem main : ∀ n : ℕ, 0 < n → a n ≠ 0 := by sorry

end OMA.S_oeis_a076072
