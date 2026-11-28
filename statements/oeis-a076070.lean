import Mathlib

/-!
A076070: Smallest multiple of n that can be formed by using the digits of the next n numbers, or 0 if no such number exists.

Source: https://oeis.org/A076070
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: No entry is zero. (At least one multiple of n can be formed by using the digits of the next n numbers).
-/

namespace OMA.S_oeis_a076070

/-- Multiset of base-10 digits of the `n`-th block of consecutive integers `n(n-1)/2 + 1, ..., n(n+1)/2` (the entry uses 1 | 2, 3 | 4, 5, 6 | 7, ..., 10 | ...: a(2) = 32, a(3) = 456, a(4) = 17908). -/
def nextDigits (n : ℕ) : Multiset ℕ :=
  (Finset.Icc (n * (n - 1) / 2 + 1) (n * (n + 1) / 2)).sum (fun k => (Nat.digits 10 k : Multiset ℕ))

/-- Smallest positive multiple of `n` whose base-10 digits form the multiset `nextDigits n`, or 0. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m : Multiset ℕ) = nextDigits n}

/-- Conjecture: no entry of A076070 is zero. -/
theorem main : ∀ n : ℕ, 0 < n → a n ≠ 0 := by sorry

end OMA.S_oeis_a076070
