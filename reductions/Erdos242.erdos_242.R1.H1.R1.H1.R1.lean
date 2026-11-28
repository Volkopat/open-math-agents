import OMAReductions.R_Erdos242_erdos_242_R1_H1_R1
import Mathlib

/-!
Split Mordell's six residue classes using the modulus eleven.  The classes
7, 8 and 10 modulo eleven have explicit identities; zero is impossible for
the relevant primes, leaving only 1, 2, 3, 4, 5, 6 and 9.
-/

namespace OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    (p%11 = 1 ∨ p%11 = 2 ∨ p%11 = 3 ∨ p%11 = 4 ∨ p%11 = 5 ∨ p%11 = 6 ∨ p%11 = 9) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    (p%11 = 7 ∨ p%11 = 8 ∨ p%11 = 10) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

theorem main : H1 → H2 → OMA.R_Erdos242_erdos_242_R1_H1_R1.H1 := by
  intro hRemaining hCovered p hp h24 h840
  by_cases h : p%11 = 7 ∨ p%11 = 8 ∨ p%11 = 10
  · exact hCovered p hp h24 h840 h
  · apply hRemaining p hp h24 h840
    have h0 : p%11 ≠ 0 := by
      intro h0
      rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h0) with he | he
      · omega
      · subst p
        norm_num at h840
    have hlt := Nat.mod_lt p (by decide : 0 < 11)
    omega

end OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1
