import Mathlib

/-!
# A091680: Smallest number whose base-4 Reverse and Add! trajectory contains exactly n base-4 palindromes.

Source: https://oeis.org/A091680
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture 2: There is no k > 0 such that the trajectory of k contains more than twelve
palindromes, i.e., a(n) = -1 for n > 12.
-/

namespace OMA.S_oeis_a091680

def revAdd4 (x : ℕ) : ℕ :=
  x + Nat.ofDigits 4 (Nat.digits 4 x).reverse

def IsPalin4 (x : ℕ) : Prop :=
  (Nat.digits 4 x).reverse = Nat.digits 4 x

theorem main :
    ∀ k : ℕ, 0 < k →
      ∀ s : Finset ℕ, (∀ t ∈ s, IsPalin4 (revAdd4^[t] k)) → s.card ≤ 12 := by
  sorry

end OMA.S_oeis_a091680
