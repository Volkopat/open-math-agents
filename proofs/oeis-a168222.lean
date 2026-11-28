import OMAStatements.S_oeis_a168222
import Mathlib

-- Problem: A168222 = A006369(A006369(n)): the g.f. with denominator (1-x)^2(1+x+x^2)^2(1+x^3+x^6)^2
-- and the recurrence a(n) = 2a(n-9) - a(n-18) for n > 17.
-- Upstream: formal-conjectures statements/oeis-a168222.lean (declaration OMA.S_oeis_a168222.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (both conjectured parts hold).
-- Proof: A006369(n) = 2n/3 for 3 | n and floor((4n+1)/3) otherwise; then a(n+9) - a(n) depends
-- only on n mod 9, which gives the recurrence; the denominator equals (1-x^9)^2.

namespace OMA.P_oeis_a168222

open OMA.S_oeis_a168222 PowerSeries

/-- The integer form of A006369. -/
def B (n : ℕ) : ℕ := if n % 3 = 0 then 2 * n / 3 else (4 * n + 1) / 3

theorem round_43 (n : ℕ) (h : n % 3 ≠ 0) :
    (round ((4 * n : ℚ) / 3)).toNat = (4 * n + 1) / 3 := by
  have hr : round ((4 * n : ℚ) / 3) = (((4 * n + 1) / 3 : ℕ) : ℤ) := by
    rw [round_eq, Int.floor_eq_iff]
    have h1 : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h1 with h1 | h1
    · obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 1 := ⟨n / 3, by omega⟩
      rw [show (4 * (3 * j + 1) + 1) / 3 = 4 * j + 1 by omega]
      push_cast
      constructor <;> linarith
    · obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j + 2 := ⟨n / 3, by omega⟩
      rw [show (4 * (3 * j + 2) + 1) / 3 = 4 * j + 3 by omega]
      push_cast
      constructor <;> linarith
  rw [hr, Int.toNat_natCast]

theorem A_eq (n : ℕ) : A006369 n = B n := by
  unfold A006369 B
  split_ifs with h
  · rfl
  · exact round_43 n h

theorem a_eq (n : ℕ) : a n = B (B n) := by
  rw [a, A_eq, A_eq]

theorem B_add (x k : ℕ) : B (x + 3 * k) = B x + (if x % 3 = 0 then 2 * k else 4 * k) := by
  unfold B
  split_ifs <;> omega

theorem rec18 (n : ℕ) : (a (n + 18) : ℤ) = 2 * (a (n + 9) : ℤ) - (a n : ℤ) := by
  simp only [a_eq]
  have h9 := B_add n 3
  have h18 := B_add n 6
  rw [show n + 3 * 3 = n + 9 by ring] at h9
  rw [show n + 3 * 6 = n + 18 by ring] at h18
  rw [h9, h18]
  by_cases hn : n % 3 = 0
  · rw [if_pos hn, if_pos hn, show B n + 2 * 3 = B n + 3 * 2 by ring,
      show B n + 2 * 6 = B n + 3 * 4 by ring, B_add, B_add]
    split_ifs <;> omega
  · rw [if_neg hn, if_neg hn, show B n + 4 * 3 = B n + 3 * 4 by ring,
      show B n + 4 * 6 = B n + 3 * 8 by ring, B_add, B_add]
    split_ifs <;> omega

theorem key (f : PowerSeries ℤ) :
    f * ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2 * (1 + X ^ 3 + X ^ 6) ^ 2) =
      C (1 : ℤ) * (X ^ 0 * f) + C (-2 : ℤ) * (X ^ 9 * f) + C (1 : ℤ) * (X ^ 18 * f) := by
  simp only [map_one, map_neg, map_ofNat]
  ring

theorem rhs :
    (X * (1 + 2 * X + 3 * X ^ 2 + 7 * X ^ 3 + 9 * X ^ 4 + 5 * X ^ 5 + 6 * X ^ 6 +
        15 * X ^ 7 + 4 * X ^ 8 + 15 * X ^ 9 + 6 * X ^ 10 + 5 * X ^ 11 + 9 * X ^ 12 +
        7 * X ^ 13 + 3 * X ^ 14 + 2 * X ^ 15 + X ^ 16) : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 1 + C (2 : ℤ) * X ^ 2 + C (3 : ℤ) * X ^ 3 + C (7 : ℤ) * X ^ 4 + C (9 : ℤ) * X ^ 5 + C (5 : ℤ) * X ^ 6 + C (6 : ℤ) * X ^ 7 + C (15 : ℤ) * X ^ 8 + C (4 : ℤ) * X ^ 9 + C (15 : ℤ) * X ^ 10 + C (6 : ℤ) * X ^ 11 + C (5 : ℤ) * X ^ 12 + C (9 : ℤ) * X ^ 13 + C (7 : ℤ) * X ^ 14 + C (3 : ℤ) * X ^ 15 + C (2 : ℤ) * X ^ 16 + C (1 : ℤ) * X ^ 17 := by
  simp only [map_one, map_ofNat]
  ring

theorem main' :
    (PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2 * (1 + X ^ 3 + X ^ 6) ^ 2) =
      X * (1 + 2 * X + 3 * X ^ 2 + 7 * X ^ 3 + 9 * X ^ 4 + 5 * X ^ 5 + 6 * X ^ 6 +
        15 * X ^ 7 + 4 * X ^ 8 + 15 * X ^ 9 + 6 * X ^ 10 + 5 * X ^ 11 + 9 * X ^ 12 +
        7 * X ^ 13 + 3 * X ^ 14 + 2 * X ^ 15 + X ^ 16)) ∧
    ∀ n : ℕ, 18 ≤ n → (a n : ℤ) = 2 * (a (n - 9) : ℤ) - (a (n - 18) : ℤ) := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [key, rhs]
    ext n
    simp only [map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    rcases lt_or_ge n 18 with h | h
    · interval_cases n <;> simp [a_eq, B]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 18 := ⟨n - 18, by omega⟩
      have hr := rec18 m
      simp only [show 0 ≤ m + 18 by omega, show 9 ≤ m + 18 by omega, show 18 ≤ m + 18 by omega,
        show m + 18 - 0 = m + 18 by omega, show m + 18 - 9 = m + 9 by omega,
        show m + 18 - 18 = m by omega,
        show m + 18 ≠ 1 by omega,
        show m + 18 ≠ 2 by omega,
        show m + 18 ≠ 3 by omega,
        show m + 18 ≠ 4 by omega,
        show m + 18 ≠ 5 by omega,
        show m + 18 ≠ 6 by omega,
        show m + 18 ≠ 7 by omega,
        show m + 18 ≠ 8 by omega,
        show m + 18 ≠ 9 by omega,
        show m + 18 ≠ 10 by omega,
        show m + 18 ≠ 11 by omega,
        show m + 18 ≠ 12 by omega,
        show m + 18 ≠ 13 by omega,
        show m + 18 ≠ 14 by omega,
        show m + 18 ≠ 15 by omega,
        show m + 18 ≠ 16 by omega,
        show m + 18 ≠ 17 by omega,
        if_true, if_false]
      linear_combination hr
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 18 := ⟨n - 18, by omega⟩
    rw [show m + 18 - 9 = m + 9 by omega, show m + 18 - 18 = m by omega]
    exact rec18 m

end OMA.P_oeis_a168222

theorem OMA.solution : type_of% @OMA.S_oeis_a168222.main := OMA.P_oeis_a168222.main'
