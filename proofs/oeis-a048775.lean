import OMAStatements.S_oeis_a048775
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: write a(n) = B(n) − (n+1) with B(n) = C(2n+1, n+1). Pascal-type identities give
-- R(n) := (n+1)·B(n) − 2(2n+1)·B(n−1) = 0. The B-part of the conjectured recurrence equals
-- R(n) − 3R(n−1) + 3R(n−2) − R(n−3), and the polynomial part −(n+1) cancels identically.

namespace OMAProofA048775

theorem keyNat (m : ℕ) :
    (m + 2) * (2 * m + 3).choose (m + 2) = 2 * (2 * m + 3) * (2 * m + 1).choose (m + 1) := by
  have h1 := Nat.add_one_mul_choose_eq (2 * m + 2) (m + 1)
  have h2 := Nat.add_one_mul_choose_eq (2 * m + 1) m
  have h3 : (2 * m + 1).choose m = (2 * m + 1).choose (m + 1) := by
    rw [← Nat.choose_symm (by omega : m ≤ 2 * m + 1)]
    congr 1
    omega
  rw [h3] at h2
  have h4 : (2 * m + 2).choose (m + 1) = 2 * (2 * m + 1).choose (m + 1) := by
    have : (m + 1) * (2 * m + 2).choose (m + 1) = (m + 1) * (2 * (2 * m + 1).choose (m + 1)) := by
      have e : 2 * m + 1 + 1 = 2 * m + 2 := by ring
      rw [e] at h2
      nlinarith [h2]
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have e1 : 2 * m + 2 + 1 = 2 * m + 3 := by ring
  rw [e1] at h1
  nlinarith [h1, h4]

theorem key (m : ℕ) :
    ((m : ℤ) + 2) * (((2 * (m + 1) + 1).choose (m + 1 + 1) : ℕ) : ℤ)
      = 2 * (2 * (m : ℤ) + 3) * (((2 * m + 1).choose (m + 1) : ℕ) : ℤ) := by
  have h := keyNat m
  have e : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
  rw [e]
  exact_mod_cast h

end OMAProofA048775

theorem OMA.solution : type_of% @OMA.S_oeis_a048775.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have h1 : m + 5 - 1 = m + 4 := by omega
  have h2 : m + 5 - 2 = m + 3 := by omega
  have h3 : m + 5 - 3 = m + 2 := by omega
  have h4 : m + 5 - 4 = m + 1 := by omega
  rw [h1, h2, h3, h4]
  have r4 := OMAProofA048775.key (m + 4)
  have r3 := OMAProofA048775.key (m + 3)
  have r2 := OMAProofA048775.key (m + 2)
  have r1 := OMAProofA048775.key (m + 1)
  simp only [OMA.S_oeis_a048775.a]
  push_cast at r1 r2 r3 r4 ⊢
  linear_combination r4 - 3 * r3 + 3 * r2 - r1
