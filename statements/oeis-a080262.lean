import Mathlib

/-!
# A080262: Cunningham numbers of the form a^b +- 1, where a, b >= 2

Source: https://oeis.org/A080262
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Cunningham numbers: of the form a^b +- 1, where a, b >= 2.
Conjecture: a(2n) = A001597(n+2) - 1 and a(2n+1) = A001597(n+2) + 1 for n >= 5,
where A001597 is the sequence of perfect powers (equivalent to (25, 27) being the
only pair of perfect powers that differ by 2).
-/

namespace OMA.S_oeis_a080262

def IsPerfectPower (m : ℕ) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 2 ≤ b ∧ a ^ b = m

def IsCunningham (m : ℕ) : Prop :=
  ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ (m = a ^ b + 1 ∨ m + 1 = a ^ b)

noncomputable def perfectPower (k : ℕ) : ℕ :=
  Nat.nth IsPerfectPower (k - 1)

noncomputable def cunningham (k : ℕ) : ℕ :=
  Nat.nth IsCunningham (k - 1)

theorem main :
    ∀ n : ℕ, 5 ≤ n →
      cunningham (2 * n) = perfectPower (n + 2) - 1 ∧
      cunningham (2 * n + 1) = perfectPower (n + 2) + 1 := by
  sorry

end OMA.S_oeis_a080262
