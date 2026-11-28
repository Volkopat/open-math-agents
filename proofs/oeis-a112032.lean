import OMAStatements.S_oeis_a112032
import Mathlib

-- Proof of Colin Barker's conjectures in OEIS A112032 (statement by @ivillar).
-- Idea: by induction, s(2j) = M/2^(j+2) and s(2j+1) = M'/2^j with M, M' odd, so
-- a(2j) = 2^(j+2) and a(2j+1) = 2^j; the recurrence and the g.f. follow.

namespace OMAA112032Helpers

open PowerSeries OMA.S_oeis_a112032

theorem den_odd (M : ℤ) (hM : Odd M) (k : ℕ) : ((M : ℚ) / 2 ^ k).den = 2 ^ k := by
  have hcop : Nat.Coprime M.natAbs ((2 : ℤ) ^ k).natAbs := by
    rw [Int.natAbs_pow]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hM))
  have := Rat.den_div_eq_of_coprime (a := M) (b := 2 ^ k) (by positivity) hcop
  push_cast at this
  exact_mod_cast this

theorem s_succ (n : ℕ) : s (n + 1) = s n + c (n + 1) := by
  unfold s
  rw [Finset.sum_range_succ]

theorem c_even (j : ℕ) : c (2 * j) = 3 * (-1) ^ j / 2 ^ (j + 2) := by
  unfold c
  rw [if_pos (by exact ⟨j, by ring⟩), show 2 * j / 2 = j by omega]
  ring

theorem c_odd (j : ℕ) : c (2 * j + 1) = (-1) ^ j / 2 ^ (j + 2) := by
  unfold c
  rw [if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨j, rfl⟩), show (2 * j + 1) / 2 = j by omega]
  ring

theorem s_form (j : ℕ) : (∃ M : ℤ, Odd M ∧ s (2 * j) = M / 2 ^ (j + 2)) ∧
    (∃ M : ℤ, Odd M ∧ s (2 * j + 1) = M / 2 ^ j) := by
  induction j with
  | zero =>
    refine ⟨⟨3, by decide, ?_⟩, ⟨1, by decide, ?_⟩⟩
    · simp [s, c]
    · simp [s, c, Finset.sum_range_succ]; norm_num
  | succ j ih =>
    obtain ⟨M, hM, hs⟩ := ih.2
    have h1 : s (2 * (j + 1)) = (8 * M + 3 * (-1) ^ (j + 1) : ℤ) / 2 ^ (j + 1 + 2) := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, s_succ, hs,
        show 2 * j + 1 + 1 = 2 * (j + 1) by ring, c_even]
      push_cast
      field_simp
      ring
    have h2 : s (2 * (j + 1) + 1) = (2 * M + (-1) ^ (j + 1) : ℤ) / 2 ^ (j + 1) := by
      rw [s_succ, h1, c_odd]
      push_cast
      field_simp
      ring
    refine ⟨⟨_, ?_, h1⟩, ⟨_, ?_, h2⟩⟩
    · rcases neg_one_pow_eq_or ℤ (j + 1) with h | h <;> rw [h] <;>
        exact Even.add_odd (by exact ⟨4 * M, by ring⟩) (by decide)
    · rcases neg_one_pow_eq_or ℤ (j + 1) with h | h <;> rw [h] <;>
        exact Even.add_odd (by exact ⟨M, by ring⟩) (by decide)

theorem a_even (j : ℕ) : a (2 * j) = 2 ^ (j + 2) := by
  obtain ⟨M, hM, hs⟩ := (s_form j).1
  unfold a; rw [hs]; exact den_odd M hM _

theorem a_odd (j : ℕ) : a (2 * j + 1) = 2 ^ j := by
  obtain ⟨M, hM, hs⟩ := (s_form j).2
  unfold a; rw [hs]; exact den_odd M hM _

theorem rec2 (n : ℕ) (hn : 2 ≤ n) : a n = 2 * a (n - 2) := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j, n = 2 * (j + 1) ∨ n = 2 * (j + 1) + 1 := ⟨n / 2 - 1, by omega⟩
  · rw [show 2 * (j + 1) - 2 = 2 * j by omega, a_even, a_even]; ring
  · rw [show 2 * (j + 1) + 1 - 2 = 2 * j + 1 by omega, a_odd, a_odd]; ring

theorem key : mk (fun n => (a n : ℚ)) * (1 - 2 * X ^ 2) = X + 4 := by
  have e1 : mk (fun n => (a n : ℚ)) * (1 - 2 * X ^ 2) =
      mk (fun n => (a n : ℚ)) - C (2 : ℚ) * (mk (fun n => (a n : ℚ)) * X ^ 2) := by
    rw [map_ofNat C 2]; ring
  have e2 : (X + 4 : ℚ⟦X⟧) = X ^ 1 + C (4 : ℚ) := by rw [map_ofNat C 4]; ring
  rw [e1, e2]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_C, coeff_X_pow]
  rcases n with _ | _ | n
  · simp [show a 0 = 4 by simpa using a_even 0]
  · simp [show a 1 = 1 by simpa using a_odd 0]
  · simp [rec2 (n + 2) (by omega)]

end OMAA112032Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a112032.main := by
  refine ⟨OMAA112032Helpers.rec2, ?_⟩
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp), OMAA112032Helpers.key]
