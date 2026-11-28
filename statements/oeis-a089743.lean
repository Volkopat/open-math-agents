import Mathlib

/-!
# A089743: Numbers that are the leading digits of a palindromic prime

Source: https://oeis.org/A089743
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Numbers that are the leading digits of a palindromic prime.
Conjecture: every number beginning with 1, 3, 7 or 9 begins infinitely many
palindromic primes.
-/

namespace OMA.S_oeis_a089743

theorem main :
    ∀ m : ℕ, 0 < m →
      (Nat.digits 10 m).getLastD 0 ∈ ({1, 3, 7, 9} : Finset ℕ) →
      Set.Infinite
        {p : ℕ |
          Nat.Prime p ∧
          (Nat.digits 10 p).reverse = Nat.digits 10 p ∧
          ∃ rest : List ℕ, (Nat.digits 10 p).reverse = (Nat.digits 10 m).reverse ++ rest} := by
  sorry

end OMA.S_oeis_a089743
