import Mathlib

/-!
# OEIS A069567: Smaller of two consecutive primes that are base-10 anagrams

Source: https://oeis.org/A069567
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (implied by Dickson's conjecture): There are infinitely many pairs of
consecutive primes `(p, q)` whose base-10 digit expansions are anagrams of each other.
-/

namespace OMA.S_oeis_a069567

def IsConsecPrimes (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ ∀ m : ℕ, p < m → m < q → ¬ Nat.Prime m

def IsAnagram10 (p q : ℕ) : Prop :=
  (Nat.digits 10 p).Perm (Nat.digits 10 q)

theorem main :
    { p : ℕ | ∃ q : ℕ, IsConsecPrimes p q ∧ IsAnagram10 p q }.Infinite := by
  sorry

end OMA.S_oeis_a069567
