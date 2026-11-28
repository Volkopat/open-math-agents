import Mathlib

/-!
# OEIS A086097: semiprime pairs with semiprime binary weight

Source: https://oeis.org/A086097
Numbers `n` such that `n` and `n + 1` are semiprimes with a semiprime number of `1`s in their
binary representations. Conjecture: the sequence is infinite.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a086097

/-- `m` is a semiprime. -/
def IsSemiprime (m : ℕ) : Prop := m.primeFactorsList.length = 2

/-- Number of ones in the binary expansion of `m`. -/
def ones (m : ℕ) : ℕ := (Nat.digits 2 m).count 1

theorem main :
    {n : ℕ | IsSemiprime n ∧ IsSemiprime (n + 1) ∧ IsSemiprime (ones n) ∧
      IsSemiprime (ones (n + 1))}.Infinite := by
  sorry

end OMA.S_oeis_a086097
