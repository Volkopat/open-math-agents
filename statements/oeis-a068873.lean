import Mathlib

/-!
# A068873: Conjectured values a(50)..a(76) for smallest prime sum of n distinct primes

Source: https://oeis.org/A068873
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A068873: Smallest prime which is a sum of n distinct primes.

Statement:
Conjectured terms a(50)-a(76): 5147, 5623, 5591, 6079, 6101, 6599, 6607, 7151, 7151, 7699,
7699, 8273, 8293, 8893, 8893, 9521, 9547, 10211, 10223, 10889, 10891, 11597, 11617, 12343,
12373, 13099, 13127.
-/

namespace OMA.S_oeis_a068873

/-- Smallest prime that can be written as the sum of `n` distinct primes. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧
    ∃ S : Finset ℕ, S.card = n ∧ (∀ q ∈ S, Nat.Prime q) ∧ S.sum id = p}

/-- The conjectured values `a(50), ..., a(76)`. -/
def conjecturedValues : List ℕ :=
  [5147, 5623, 5591, 6079, 6101, 6599, 6607, 7151, 7151, 7699,
   7699, 8273, 8293, 8893, 8893, 9521, 9547, 10211, 10223, 10889,
   10891, 11597, 11617, 12343, 12373, 13099, 13127]

theorem main :
    ∀ i : Fin conjecturedValues.length, a (50 + i.val) = conjecturedValues[i] := by
  sorry

end OMA.S_oeis_a068873
