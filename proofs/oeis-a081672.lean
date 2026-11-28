import OMAStatements.S_oeis_a081672

-- Problem: A081672, a recurrence for exp(2x) - exp(0) + BesselI_0(2x).
-- Credit: @GarnetCullet
-- For n >= 1, a(n) = 2^n + c(n) with c(n) = binomial(n, n/2) for even n and 0 for odd n.
-- The 2^n part cancels: n - (n-1) - (n-1) + (n-2) = 0. The binomial part reduces to
-- (m+2) * C(2m+4, m+2) = 2 * (2m+3) * C(2m+2, m+1), i.e. Nat.succ_mul_centralBinom_succ.

namespace OMA.P_oeis_a081672

open OMA.S_oeis_a081672

theorem a_even (k : ℕ) : a (2 * k + 2) = 2 ^ (2 * k + 2) + ((2 * k + 2).choose (k + 1) : ℤ) := by
  rw [a, if_neg (by omega), if_pos (by omega), show (2 * k + 2) / 2 = k + 1 by omega]

theorem a_odd (k : ℕ) : a (2 * k + 1) = 2 ^ (2 * k + 1) := by
  rw [a, if_neg (by omega), if_neg (by omega), add_zero]

theorem cb (m : ℕ) :
    ((m + 2 : ℕ) * (2 * m + 4).choose (m + 2) : ℤ) =
      2 * (2 * m + 3) * ((2 * m + 2).choose (m + 1) : ℤ) := by
  have h := Nat.succ_mul_centralBinom_succ (m + 1)
  simp only [Nat.centralBinom_eq_two_mul_choose] at h
  rw [show 2 * (m + 1 + 1) = 2 * m + 4 by ring, show 2 * (m + 1) = 2 * m + 2 by ring] at h
  exact_mod_cast h

end OMA.P_oeis_a081672

open OMA.P_oeis_a081672 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081672.main := by
  intro n hn
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 4 ∨ n = 2 * m + 5 := ⟨(n - 4) / 2, by omega⟩
  · rw [show 2 * m + 4 = 2 * (m + 1) + 2 by ring, show 2 * (m + 1) + 2 - 1 = 2 * (m + 1) + 1 by omega,
      show 2 * (m + 1) + 2 - 2 = 2 * m + 2 by omega, show 2 * (m + 1) + 2 - 3 = 2 * m + 1 by omega,
      a_even, a_odd, a_even, a_odd]
    have h := cb m
    rw [show 2 * (m + 1) + 2 = 2 * m + 4 by ring] at *
    push_cast at h ⊢
    linear_combination 2 * h
  · rw [show 2 * m + 5 - 1 = 2 * (m + 1) + 2 by omega, show 2 * m + 5 - 2 = 2 * (m + 1) + 1 by omega,
      show 2 * m + 5 - 3 = 2 * m + 2 by omega, show 2 * m + 5 = 2 * (m + 2) + 1 by ring,
      a_even, a_odd, a_even, a_odd]
    have h := cb m
    rw [show 2 * (m + 1) + 2 = 2 * m + 4 by ring] at *
    push_cast at h ⊢
    linear_combination -4 * h
