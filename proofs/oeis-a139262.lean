import OMAStatements.S_oeis_a139262
import Mathlib

-- Problem: A139262: Total number of two-element anti-chains over all ordered trees on n edges.
-- Upstream: formal-conjectures statements/oeis-a139262.lean:0 (declaration OMA.S_oeis_a139262.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! With c(n) = binomial(2n, n) and 2 a(n) = (n+1) c(n) - 4^n, twice the left side of the
recurrence is a combination of the two instances n c(n) = 2 (2n-1) c(n-1) and
(n-1) c(n-1) = 2 (2n-3) c(n-2) of the central binomial recurrence; the powers of 4 cancel. -/

namespace A139262Aux

open OMA.S_oeis_a139262

theorem two_mul_a (n : ℕ) :
    2 * a n = ((n : ℤ) + 1) * (Nat.centralBinom n : ℤ) - 4 ^ n := by
  unfold a
  apply Int.mul_ediv_cancel'
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have h1 : (2 : ℤ) ∣ (Nat.centralBinom n : ℤ) := by
      exact_mod_cast Nat.two_dvd_centralBinom_of_one_le h
    have h2 : (2 : ℤ) ∣ 4 ^ n := dvd_pow (by norm_num) (by omega)
    exact dvd_sub (Dvd.dvd.mul_left h1 _) h2

theorem rec_central (n : ℕ) :
    ((n : ℤ) + 1) * (Nat.centralBinom (n + 1) : ℤ) = 2 * (2 * (n : ℤ) + 1) * (Nat.centralBinom n : ℤ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ n

theorem main_aux (m : ℕ) :
    ((m + 2 : ℕ) : ℤ) * (((m + 2 : ℕ) : ℤ) - 2) * a (m + 2) +
      2 * (-4 * ((m + 2 : ℕ) : ℤ) ^ 2 + 9 * ((m + 2 : ℕ) : ℤ) - 3) * a (m + 1) +
      8 * (((m + 2 : ℕ) : ℤ) - 1) * (2 * ((m + 2 : ℕ) : ℤ) - 3) * a m = 0 := by
  have hA2 := two_mul_a (m + 2)
  have hA1 := two_mul_a (m + 1)
  have hA0 := two_mul_a m
  have h1 := rec_central (m + 1)
  have h2 := rec_central m
  push_cast at hA2 hA1 h1 ⊢
  have h : 2 * (((m : ℤ) + 2) * ((m : ℤ) + 2 - 2) * a (m + 2) +
      2 * (-4 * ((m : ℤ) + 2) ^ 2 + 9 * ((m : ℤ) + 2) - 3) * a (m + 1) +
      8 * ((m : ℤ) + 2 - 1) * (2 * ((m : ℤ) + 2) - 3) * a m) = 0 := by
    have e2 : (4 : ℤ) ^ (m + 2) = 16 * 4 ^ m := by ring
    have e1 : (4 : ℤ) ^ (m + 1) = 4 * 4 ^ m := by ring
    rw [e2] at hA2
    rw [e1] at hA1
    linear_combination ((m : ℤ) + 2) * (m : ℤ) * hA2 +
      2 * (-4 * ((m : ℤ) + 2) ^ 2 + 9 * ((m : ℤ) + 2) - 3) * hA1 +
      8 * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) * hA0 +
      (m : ℤ) * ((m : ℤ) + 3) * h1 - 4 * ((m : ℤ) + 1) ^ 2 * h2
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

end A139262Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a139262.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h := A139262Aux.main_aux m
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  exact h
