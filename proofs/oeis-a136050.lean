import OMAStatements.S_oeis_a136050
import Mathlib

-- Problem: A136050: Sum of digits of product of twin primes A037074.
-- Upstream: formal-conjectures statements/oeis-a136050.lean:0 (declaration OMA.S_oeis_a136050.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof.  If p and p + 2 are prime and p is not 3, then p = 2 (mod 3): otherwise 3 divides p or
-- p + 2, which forces p = 3 or p + 2 = 3.  Write p = 3k + 2.  Then
-- p (p + 2) = 9 (k^2 + 2k) + 8, so p (p + 2) = 8 (mod 9).  A number is congruent to its digit sum
-- modulo 9, so the digit sum is 8 (mod 9), one less than a multiple of 9.

theorem OMA.solution : type_of% @OMA.S_oeis_a136050.main := by
  intro p hp hp2 h3
  have hmod : p % 3 = 2 := by
    have h1 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h1 with h | h | h
    · have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      have he : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hd
      omega
    · have hd : 3 ∣ p + 2 := Nat.dvd_of_mod_eq_zero (by omega)
      have he : 3 = p + 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp2).1 hd
      have h1' : p = 1 := by omega
      rw [h1'] at hp
      exact absurd hp Nat.not_prime_one
    · exact h
  have h9 : p * (p + 2) % 9 = 8 := by
    obtain ⟨k, rfl⟩ : ∃ k, p = 3 * k + 2 := ⟨p / 3, by omega⟩
    have e : (3 * k + 2) * (3 * k + 2 + 2) = 9 * (k * k + 2 * k) + 8 := by ring
    rw [e]
    omega
  have hd : p * (p + 2) % 9 = (Nat.digits 10 (p * (p + 2))).sum % 9 :=
    Nat.modEq_nine_digits_sum (p * (p + 2))
  unfold OMA.S_oeis_a136050.term
  omega
