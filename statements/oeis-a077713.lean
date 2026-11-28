import Mathlib

/-!
# A077713: a(1) = 3; thereafter a(n) = the smallest prime of the form d0...0a(n-1), where d is a single digit, or 0 if no such prime exists.

Source: https://oeis.org/A077713
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the smallest prime obtained by prefixing a(n-1) with a number of the form d*10^k
where d is a single digit, 0 < d < 10, and k >= 0. Conjecture: d*10^k always exists.
-/

namespace OMA.S_oeis_a077713

/-- Smallest prime obtained by prefixing `x` with a nonzero digit `d` and zero or more `0`s. -/
noncomputable def nextPrimePrefix (x : ℕ) : ℕ :=
  sInf { p : ℕ | p.Prime ∧ ∃ d k : ℕ,
    1 ≤ d ∧ d ≤ 9 ∧ (Nat.digits 10 x).length ≤ k ∧ p = d * 10 ^ k + x }

/-- The `n`-th term of A077713 (0-indexed, with `a 0 = 3`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.iterate nextPrimePrefix n 3

theorem main :
    ∀ n : ℕ, ∃ d k : ℕ, 1 ≤ d ∧ d ≤ 9 ∧
      (Nat.digits 10 (a n)).length ≤ k ∧ (d * 10 ^ k + a n).Prime := by sorry

end OMA.S_oeis_a077713
