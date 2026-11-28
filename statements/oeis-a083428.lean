import Mathlib

/-!
# A083428: Smallest prime that can be formed using the digits of first 3n+1 numbers, or 0 if no such number exists.

Source: https://oeis.org/A083428
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

The digits of first 3n and first 3n-1 numbers yield a composite number which is a multiple of 3. Conjecture: No entry is zero.
-/

namespace OMA.S_oeis_a083428

def digitsMultisetUpTo (m : ℕ) : Multiset ℕ :=
  (Finset.Icc 1 m).val.bind (fun k => Multiset.ofList (Nat.digits 10 k))

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ p : ℕ, Nat.Prime p ∧ Multiset.ofList (Nat.digits 10 p) = digitsMultisetUpTo (3 * n + 1) := by
  sorry

end OMA.S_oeis_a083428
