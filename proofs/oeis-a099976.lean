import OMAStatements.S_oeis_a099976
import Mathlib

-- Problem: A099976, a(n) = binomial(4n+2, 2n+1); Mathar's D-finite recurrence.
-- Upstream: formal-conjectures statements/oeis-a099976.lean (declaration OMA.S_oeis_a099976.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: two applications of (k+1) C(2k+2, k+1) = 2 (2k+1) C(2k, k) (k = 2m+1, 2m+2) relate
-- a(m+1) to a(m); the recurrence is a linear combination of the two identities.

namespace OMA.P_oeis_a099976

open OMA.S_oeis_a099976

theorem main' : ∀ n : ℕ, 1 ≤ n →
    (n : ℤ) * (2 * n + 1) * a n - 2 * (4 * (n : ℤ) - 1) * (4 * n + 1) * a (n - 1) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hA : a (m + 1) = Nat.centralBinom (2 * m + 3) := by
    unfold a; rw [Nat.centralBinom_eq_two_mul_choose]; congr 1; ring
  have hB : a (m + 1 - 1) = Nat.centralBinom (2 * m + 1) := by
    unfold a; rw [Nat.centralBinom_eq_two_mul_choose, Nat.add_sub_cancel]; congr 1; ring
  rw [hA, hB]
  have h1 := Nat.succ_mul_centralBinom_succ (2 * m + 1)
  have h2 := Nat.succ_mul_centralBinom_succ (2 * m + 2)
  rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring] at h1
  rw [show 2 * m + 2 + 1 = 2 * m + 3 by ring] at h2
  have h1' : ((2 * m + 2 : ℕ) : ℤ) * ((2 * m + 2).centralBinom : ℤ) =
      2 * (2 * ((2 * m + 1 : ℕ) : ℤ) + 1) * ((2 * m + 1).centralBinom : ℤ) := by exact_mod_cast h1
  have h2' : ((2 * m + 3 : ℕ) : ℤ) * ((2 * m + 3).centralBinom : ℤ) =
      2 * (2 * ((2 * m + 2 : ℕ) : ℤ) + 1) * ((2 * m + 2).centralBinom : ℤ) := by exact_mod_cast h2
  push_cast at h1' h2' ⊢
  linear_combination ((m : ℤ) + 1) * h2' + (4 * (m : ℤ) + 5) * h1'

end OMA.P_oeis_a099976

theorem OMA.solution : type_of% @OMA.S_oeis_a099976.main := OMA.P_oeis_a099976.main'
