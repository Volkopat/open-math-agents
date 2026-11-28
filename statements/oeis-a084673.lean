import Mathlib

/-!
# A084673: Smallest prime in which a digit appears n times.

Source: https://oeis.org/A084673
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

For n > 1, conjectured to be equal to A037055(n), the smallest prime in { R-10^n, R-10^(n-1), ..., R-10; R+a*10^b, a = 1, ..., 8, b = 0, 1, 2, ..., n }, where R = (10^(n+1)-1)/9 is the (n+1)-digit repunit.
-/

namespace OMA.S_oeis_a084673

def repunit (m : ℕ) : ℕ :=
  (10 ^ m - 1) / 9

def candidateSet (n : ℕ) : Set ℕ :=
  {m : ℕ | (∃ b : ℕ, 1 ≤ b ∧ b ≤ n ∧ m = repunit (n + 1) - 10 ^ b) ∨
    (∃ a b : ℕ, 1 ≤ a ∧ a ≤ 8 ∧ b ≤ n ∧ m = repunit (n + 1) + a * 10 ^ b)}

noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ ∃ d : ℕ, d < 10 ∧ (Nat.digits 10 p).count d = n}

theorem main :
    ∀ n : ℕ, 1 < n → a n = sInf {p : ℕ | Nat.Prime p ∧ p ∈ candidateSet n} := by
  sorry

end OMA.S_oeis_a084673
