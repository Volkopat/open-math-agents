import Mathlib

/-!
A076980: Leyland numbers: 3, together with numbers expressible as n^k + k^n nontrivially, i.e., n,k > 1 (to avoid n = (n-1)^1 + 1^(n-1)).

Source: https://oeis.org/A076980
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: For d > 11, 10^(d-1)+(d-1)^10 is the smallest (base ten) d-digit term. · Conjecture from Zhi-Wei Sun, Feb 26 2022: (i) For each n > 0, we have a(n) <= p+1 < a(n+1) for some prime p. (ii) a(n) < p < a(n+1) for some prime p, except that the interval (a(5), a(6)) = (54, 57) contains no prime.
-/

namespace OMA.S_oeis_a076980

/-- Predicate for Leyland numbers (including 3). -/
def IsLeyland (m : ℕ) : Prop :=
  m = 3 ∨ ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ m = x ^ y + y ^ x

/-- The `n`-th Leyland number (1-indexed: `a 1 = 3`, `a 2 = 8`, ...). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth IsLeyland (n - 1)

/-- Conjectures on Leyland numbers: smallest `d`-digit term for `d > 11`, and Zhi-Wei Sun's
prime-between-consecutive-Leyland-numbers conjectures (i) and (ii). -/
theorem main :
    (∀ d : ℕ, 11 < d →
      sInf {m : ℕ | IsLeyland m ∧ 10 ^ (d - 1) ≤ m ∧ m < 10 ^ d} = 10 ^ (d - 1) + (d - 1) ^ 10) ∧
    (∀ n : ℕ, 0 < n → ∃ p : ℕ, Nat.Prime p ∧ a n ≤ p + 1 ∧ p + 1 < a (n + 1)) ∧
    (∀ n : ℕ, 0 < n → n ≠ 5 → ∃ p : ℕ, Nat.Prime p ∧ a n < p ∧ p < a (n + 1)) := by sorry

end OMA.S_oeis_a076980
