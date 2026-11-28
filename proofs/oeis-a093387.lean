import OMAStatements.S_oeis_a093387
import Mathlib

/-!
Credit: @ivillar
Proof: the powers of 2 cancel in the recurrence. For the binomial part write c(m) for the
central binomial coefficient binomial(2m, m). Then binomial(2m, m) = c(m),
2 binomial(2m+1, m) = c(m+1) (Pascal's rule and symmetry) and (m+1) c(m+1) = 2 (2m+1) c(m).
Splitting n = 2m+4 and n = 2m+5, the binomial part of the recurrence is a linear combination
of these identities.
-/

namespace OMAA093387Helpers

theorem key1 (m : ℕ) : ((2 * m).choose m : ℤ) = (Nat.centralBinom m : ℤ) := by
  rw [Nat.centralBinom_eq_two_mul_choose]

theorem key2 (m : ℕ) : 2 * ((2 * m + 1).choose m : ℤ) = (Nat.centralBinom (m + 1) : ℤ) := by
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = (2 * m + 1) + 1 by ring,
    Nat.choose_succ_succ, Nat.choose_symm_half]
  push_cast
  ring

theorem rec (m : ℕ) : ((m : ℤ) + 1) * (Nat.centralBinom (m + 1) : ℤ) =
    2 * (2 * (m : ℤ) + 1) * (Nat.centralBinom m : ℤ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ m

end OMAA093387Helpers

open OMAA093387Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a093387.main := by
  intro n hn
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 4 ∨ n = 2 * m + 5 := ⟨(n - 4) / 2, by omega⟩
  · rw [show 2 * m + 4 - 1 = 2 * m + 3 by omega, show 2 * m + 4 - 2 = 2 * m + 2 by omega,
      show 2 * m + 4 - 3 = 2 * m + 1 by omega]
    unfold OMA.S_oeis_a093387.a
    rw [show 2 * m + 4 - 1 = 2 * m + 3 by omega, show 2 * m + 3 - 1 = 2 * m + 2 by omega,
      show 2 * m + 2 - 1 = 2 * m + 1 by omega, show 2 * m + 1 - 1 = 2 * m by omega,
      show (2 * m + 4) / 2 = m + 2 by omega, show (2 * m + 3) / 2 = m + 1 by omega,
      show (2 * m + 2) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega]
    have hb0 : ((2 * m + 4).choose (m + 2) : ℤ) = (Nat.centralBinom (m + 2) : ℤ) := by
      rw [show 2 * m + 4 = 2 * (m + 2) by ring]
      exact key1 (m + 2)
    have hb1 : 2 * ((2 * m + 3).choose (m + 1) : ℤ) = (Nat.centralBinom (m + 2) : ℤ) := by
      rw [show 2 * m + 3 = 2 * (m + 1) + 1 by ring]
      exact key2 (m + 1)
    have hb2 : ((2 * m + 2).choose (m + 1) : ℤ) = (Nat.centralBinom (m + 1) : ℤ) := by
      rw [show 2 * m + 2 = 2 * (m + 1) by ring]
      exact key1 (m + 1)
    have hb3 : 2 * ((2 * m + 1).choose m : ℤ) = (Nat.centralBinom (m + 1) : ℤ) := key2 m
    push_cast
    linear_combination (-(2 * (m : ℤ) + 5)) * hb0 + (2 * (m : ℤ) + 5) * hb1 +
      (4 * (2 * (m : ℤ) + 2)) * hb2 - (4 * (2 * (m : ℤ) + 2)) * hb3
  · rw [show 2 * m + 5 - 1 = 2 * m + 4 by omega, show 2 * m + 5 - 2 = 2 * m + 3 by omega,
      show 2 * m + 5 - 3 = 2 * m + 2 by omega]
    unfold OMA.S_oeis_a093387.a
    rw [show 2 * m + 5 - 1 = 2 * m + 4 by omega, show 2 * m + 4 - 1 = 2 * m + 3 by omega,
      show 2 * m + 3 - 1 = 2 * m + 2 by omega, show 2 * m + 2 - 1 = 2 * m + 1 by omega,
      show (2 * m + 5) / 2 = m + 2 by omega, show (2 * m + 4) / 2 = m + 2 by omega,
      show (2 * m + 3) / 2 = m + 1 by omega, show (2 * m + 2) / 2 = m + 1 by omega]
    have h0 : 2 * ((2 * m + 5).choose (m + 2) : ℤ) = (Nat.centralBinom (m + 3) : ℤ) := by
      rw [show 2 * m + 5 = 2 * (m + 2) + 1 by ring]
      exact key2 (m + 2)
    have h1 : ((2 * m + 4).choose (m + 2) : ℤ) = (Nat.centralBinom (m + 2) : ℤ) := by
      rw [show 2 * m + 4 = 2 * (m + 2) by ring]
      exact key1 (m + 2)
    have h2 : 2 * ((2 * m + 3).choose (m + 1) : ℤ) = (Nat.centralBinom (m + 2) : ℤ) := by
      rw [show 2 * m + 3 = 2 * (m + 1) + 1 by ring]
      exact key2 (m + 1)
    have h3 : ((2 * m + 2).choose (m + 1) : ℤ) = (Nat.centralBinom (m + 1) : ℤ) := by
      rw [show 2 * m + 2 = 2 * (m + 1) by ring]
      exact key1 (m + 1)
    have r2 : ((m : ℤ) + 2 + 1) * (Nat.centralBinom (m + 2 + 1) : ℤ) =
        2 * (2 * ((m : ℤ) + 2) + 1) * (Nat.centralBinom (m + 2) : ℤ) := by
      have := rec (m + 2)
      push_cast at this
      exact this
    have r1 : ((m : ℤ) + 1 + 1) * (Nat.centralBinom (m + 1 + 1) : ℤ) =
        2 * (2 * ((m : ℤ) + 1) + 1) * (Nat.centralBinom (m + 1) : ℤ) := by
      have := rec (m + 1)
      push_cast at this
      exact this
    push_cast
    linear_combination (-((m : ℤ) + 3)) * h0 + (2 * (2 * (m : ℤ) + 6)) * h1 +
      (2 * (2 * (m : ℤ) + 3)) * h2 - (8 * (2 * (m : ℤ) + 3)) * h3 - r2 + 4 * r1
