import Mathlib

/-!
# A092215: Smallest number whose base-2 Reverse and Add! trajectory contains exactly n base-2 palindromes.

Source: https://oeis.org/A092215
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture 2: There is no k > 0 such that the trajectory of k contains more than eleven
base 2 palindromes, i.e., a(n) = -1 for n > 11.
-/

namespace OMA.S_oeis_a092215

def revAdd2 (x : ℕ) : ℕ :=
  x + Nat.ofDigits 2 (Nat.digits 2 x).reverse

def IsPalin2 (x : ℕ) : Prop :=
  (Nat.digits 2 x).reverse = Nat.digits 2 x

theorem main :
    ∀ k : ℕ, 0 < k →
      ∀ s : Finset ℕ, (∀ t ∈ s, IsPalin2 (revAdd2^[t] k)) → s.card ≤ 11 := by
  sorry

end OMA.S_oeis_a092215
