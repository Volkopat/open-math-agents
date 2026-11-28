import OMAStatements.S_oeis_a207118
import Mathlib

open OMA.S_oeis_a207118

namespace OMA.P_oeis_a207118

def Q (k : ℕ) : ℤ := (k : ℤ) ^ 3 + 6 * (k : ℤ) ^ 2 + 8 * k + 3

theorem o0 : options 0 = [0] := by decide
theorem o3 : options 3 = [0, 3] := by decide
theorem o4 : options 4 = [0, 4] := by decide
theorem o5 : options 5 = [0, 4, 5] := by decide
theorem o6 : options 6 = [0, 4, 6] := by decide
theorem o7 : options 7 = [0, 3, 4, 5, 6, 7] := by decide

theorem ch (m : ℕ) : chains m 0 = 1 ∧ chains m 3 = m + 1 ∧ chains m 4 = m + 1 ∧
    2 * chains m 5 = (m + 1) * (m + 2) ∧ 2 * chains m 6 = (m + 1) * (m + 2) ∧
    3 * chains m 7 = Q m := by
  induction m with
  | zero => refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ m ih =>
    obtain ⟨h0, h3, h4, h5, h6, h7⟩ := ih
    simp only [chains, o0, o3, o4, o5, o6, o7, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Q] at *
    push_cast at *
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem A_even (k : ℕ) (hk : 0 < k) : 9 * arrays (2 * k) = Q k ^ 2 := by
  unfold arrays
  rw [if_neg (by omega), show (2 * k + 1) / 2 = k by omega, show 2 * k / 2 = k by omega]
  have := (ch k).2.2.2.2.2
  rw [← this]; ring

theorem A_odd (k : ℕ) : 9 * arrays (2 * k + 1) = Q (k + 1) * Q k := by
  unfold arrays
  rw [if_neg (by omega), show (2 * k + 1 + 1) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega]
  have h1 := (ch (k + 1)).2.2.2.2.2
  have h2 := (ch k).2.2.2.2.2
  rw [← h1, ← h2]; ring

end OMA.P_oeis_a207118

open OMA.P_oeis_a207118 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a207118.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have h := A_even k hk
    unfold evenPoly Q at *
    push_cast at *
    linear_combination 64 * h
  · intro k
    have h := A_odd k
    unfold oddPoly Q at *
    push_cast at *
    linear_combination 64 * h
  · intro n
    rcases Nat.lt_or_ge n 13 with h | h
    · interval_cases n <;> decide +kernel
    · obtain ⟨q, rfl | rfl⟩ : ∃ q, n = 2 * q + 13 ∨ n = 2 * q + 14 := ⟨(n - 13) / 2, by omega⟩
      · have e0 : 2 * q + 13 - 0 = 2 * (q + 6) + 1 := by omega
        have a0 := A_odd (q + 6)
        have e1 : 2 * q + 13 - 1 = 2 * (q + 6) := by omega
        have a1 := A_even (q + 6) (by omega)
        have e2 : 2 * q + 13 - 2 = 2 * (q + 5) + 1 := by omega
        have a2 := A_odd (q + 5)
        have e3 : 2 * q + 13 - 3 = 2 * (q + 5) := by omega
        have a3 := A_even (q + 5) (by omega)
        have e4 : 2 * q + 13 - 4 = 2 * (q + 4) + 1 := by omega
        have a4 := A_odd (q + 4)
        have e5 : 2 * q + 13 - 5 = 2 * (q + 4) := by omega
        have a5 := A_even (q + 4) (by omega)
        have e7 : 2 * q + 13 - 7 = 2 * (q + 3) := by omega
        have a7 := A_even (q + 3) (by omega)
        have e8 : 2 * q + 13 - 8 = 2 * (q + 2) + 1 := by omega
        have a8 := A_odd (q + 2)
        have e9 : 2 * q + 13 - 9 = 2 * (q + 2) := by omega
        have a9 := A_even (q + 2) (by omega)
        have e10 : 2 * q + 13 - 10 = 2 * (q + 1) + 1 := by omega
        have a10 := A_odd (q + 1)
        have e11 : 2 * q + 13 - 11 = 2 * (q + 1) := by omega
        have a11 := A_even (q + 1) (by omega)
        have e12 : 2 * q + 13 - 12 = 2 * (q + 0) + 1 := by omega
        have a12 := A_odd (q + 0)
        have hz : numerator (2 * q + 13) = 0 := by
          unfold numerator
          simp only [show 2 * q + 13 ≠ 1 by omega, show 2 * q + 13 ≠ 2 by omega, show 2 * q + 13 ≠ 3 by omega, show 2 * q + 13 ≠ 4 by omega, show 2 * q + 13 ≠ 5 by omega, show 2 * q + 13 ≠ 6 by omega, show 2 * q + 13 ≠ 7 by omega, show 2 * q + 13 ≠ 8 by omega, show 2 * q + 13 ≠ 9 by omega, show 2 * q + 13 ≠ 10 by omega, show 2 * q + 13 ≠ 11 by omega, show 2 * q + 13 ≠ 12 by omega, if_false]
        rw [hz]
        have key : 9 * denTimesSeries (2 * q + 13) = 0 := by
          unfold denTimesSeries delayed
          simp only [show 0 ≤ 2 * q + 13 by omega, show 1 ≤ 2 * q + 13 by omega, show 2 ≤ 2 * q + 13 by omega, show 3 ≤ 2 * q + 13 by omega, show 4 ≤ 2 * q + 13 by omega, show 5 ≤ 2 * q + 13 by omega, show 7 ≤ 2 * q + 13 by omega, show 8 ≤ 2 * q + 13 by omega, show 9 ≤ 2 * q + 13 by omega, show 10 ≤ 2 * q + 13 by omega, show 11 ≤ 2 * q + 13 by omega, show 12 ≤ 2 * q + 13 by omega, if_true, e0, e1, e2, e3, e4, e5, e7, e8, e9, e10, e11, e12]
          simp only [Q] at *
          push_cast at *
          linear_combination (1) * a0 + (-2) * a1 + (-4) * a2 + (10) * a3 + (5) * a4 + (-20) * a5 + (20) * a7 + (-5) * a8 + (-10) * a9 + (4) * a10 + (2) * a11 + (-1) * a12
        linarith
      · have e0 : 2 * q + 14 - 0 = 2 * (q + 7) := by omega
        have a0 := A_even (q + 7) (by omega)
        have e1 : 2 * q + 14 - 1 = 2 * (q + 6) + 1 := by omega
        have a1 := A_odd (q + 6)
        have e2 : 2 * q + 14 - 2 = 2 * (q + 6) := by omega
        have a2 := A_even (q + 6) (by omega)
        have e3 : 2 * q + 14 - 3 = 2 * (q + 5) + 1 := by omega
        have a3 := A_odd (q + 5)
        have e4 : 2 * q + 14 - 4 = 2 * (q + 5) := by omega
        have a4 := A_even (q + 5) (by omega)
        have e5 : 2 * q + 14 - 5 = 2 * (q + 4) + 1 := by omega
        have a5 := A_odd (q + 4)
        have e7 : 2 * q + 14 - 7 = 2 * (q + 3) + 1 := by omega
        have a7 := A_odd (q + 3)
        have e8 : 2 * q + 14 - 8 = 2 * (q + 3) := by omega
        have a8 := A_even (q + 3) (by omega)
        have e9 : 2 * q + 14 - 9 = 2 * (q + 2) + 1 := by omega
        have a9 := A_odd (q + 2)
        have e10 : 2 * q + 14 - 10 = 2 * (q + 2) := by omega
        have a10 := A_even (q + 2) (by omega)
        have e11 : 2 * q + 14 - 11 = 2 * (q + 1) + 1 := by omega
        have a11 := A_odd (q + 1)
        have e12 : 2 * q + 14 - 12 = 2 * (q + 1) := by omega
        have a12 := A_even (q + 1) (by omega)
        have hz : numerator (2 * q + 14) = 0 := by
          unfold numerator
          simp only [show 2 * q + 14 ≠ 1 by omega, show 2 * q + 14 ≠ 2 by omega, show 2 * q + 14 ≠ 3 by omega, show 2 * q + 14 ≠ 4 by omega, show 2 * q + 14 ≠ 5 by omega, show 2 * q + 14 ≠ 6 by omega, show 2 * q + 14 ≠ 7 by omega, show 2 * q + 14 ≠ 8 by omega, show 2 * q + 14 ≠ 9 by omega, show 2 * q + 14 ≠ 10 by omega, show 2 * q + 14 ≠ 11 by omega, show 2 * q + 14 ≠ 12 by omega, if_false]
        rw [hz]
        have key : 9 * denTimesSeries (2 * q + 14) = 0 := by
          unfold denTimesSeries delayed
          simp only [show 0 ≤ 2 * q + 14 by omega, show 1 ≤ 2 * q + 14 by omega, show 2 ≤ 2 * q + 14 by omega, show 3 ≤ 2 * q + 14 by omega, show 4 ≤ 2 * q + 14 by omega, show 5 ≤ 2 * q + 14 by omega, show 7 ≤ 2 * q + 14 by omega, show 8 ≤ 2 * q + 14 by omega, show 9 ≤ 2 * q + 14 by omega, show 10 ≤ 2 * q + 14 by omega, show 11 ≤ 2 * q + 14 by omega, show 12 ≤ 2 * q + 14 by omega, if_true, e0, e1, e2, e3, e4, e5, e7, e8, e9, e10, e11, e12]
          simp only [Q] at *
          push_cast at *
          linear_combination (1) * a0 + (-2) * a1 + (-4) * a2 + (10) * a3 + (5) * a4 + (-20) * a5 + (20) * a7 + (-5) * a8 + (-10) * a9 + (4) * a10 + (2) * a11 + (-1) * a12
        linarith
