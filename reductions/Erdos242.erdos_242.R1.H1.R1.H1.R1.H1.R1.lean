import OMAReductions.R_Erdos242_erdos_242_R1_H1_R1_H1_R1
import Mathlib

/-!
Split the remaining six Mordell classes by the residue modulo thirteen.
The classes 6, 8 and 11 modulo thirteen have explicit strict three-term
identities.  Zero modulo thirteen is impossible for the relevant primes.
-/

namespace OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    (p%11 = 1 ∨ p%11 = 2 ∨ p%11 = 3 ∨ p%11 = 4 ∨ p%11 = 5 ∨ p%11 = 6 ∨ p%11 = 9) →
    (p%13 = 1 ∨ p%13 = 2 ∨ p%13 = 3 ∨ p%13 = 4 ∨ p%13 = 5 ∨
      p%13 = 7 ∨ p%13 = 9 ∨ p%13 = 10 ∨ p%13 = 12) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    (p%11 = 1 ∨ p%11 = 2 ∨ p%11 = 3 ∨ p%11 = 4 ∨ p%11 = 5 ∨ p%11 = 6 ∨ p%11 = 9) →
    (p%13 = 0 ∨ p%13 = 6 ∨ p%13 = 8 ∨ p%13 = 11) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

theorem main : H1 → H2 → OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1.H1 := by
  intro hRemaining hCovered p hp h24 h840 h11
  by_cases h13 : p%13 = 0 ∨ p%13 = 6 ∨ p%13 = 8 ∨ p%13 = 11
  · exact hCovered p hp h24 h840 h11 h13
  · apply hRemaining p hp h24 h840 h11
    have hlt := Nat.mod_lt p (by decide : 0 < 13)
    omega

end OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1
