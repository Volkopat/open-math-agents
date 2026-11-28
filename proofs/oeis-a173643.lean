import OMAStatements.S_oeis_a173643

-- Problem: A173643: Positive numbers of form 2^m - 2^l - 3*2^k (A172233) divisible by 9, divided by 9.
-- Upstream: formal-conjectures statements/oeis-a173643.lean:0 (declaration OMA.S_oeis_a173643.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: 27 = 2^5 - 2^1 - 3*2^0 is a term of A172233 and 27/9 = 3 = 2^0 * 3, so the odd part
-- 3 would have to equal [(1/6)*(8^m - (-1)^m - 3)*4^k - 1]/3 with k, m > 0, that is
-- (8^m - (-1)^m - 3) * 4^k = 60. But 8^m - (-1)^m - 3 is even and 4 divides 4^k, so 8 would
-- divide 60.

namespace L05A173643

open OMA.S_oeis_a173643

theorem no_three (k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (h : ((3 : ℕ) : ℚ) = ((1 / 6) * ((8 : ℚ) ^ m - (-1) ^ m - 3) * 4 ^ k - 1) / 3) : False := by
  have h' : ((3 : ℕ) : ℚ) = 3 := by norm_num
  have h2 : ((8 : ℚ) ^ m - (-1) ^ m - 3) * 4 ^ k = 60 := by
    linear_combination -18 * h + 18 * h'
  have h3 : ((((8 : ℤ) ^ m - (-1) ^ m - 3) * 4 ^ k : ℤ) : ℚ) = ((60 : ℤ) : ℚ) := by
    push_cast
    exact h2
  have h4 : ((8 : ℤ) ^ m - (-1) ^ m - 3) * 4 ^ k = 60 := by exact_mod_cast h3
  have hP : (2 : ℤ) ∣ (8 : ℤ) ^ m - (-1) ^ m - 3 := by
    have h0 : (2 : ℤ) ∣ 8 := ⟨4, by norm_num⟩
    have h1 : (2 : ℤ) ∣ (8 : ℤ) ^ m := dvd_pow h0 (by omega)
    have h5 : (2 : ℤ) ∣ (-1) ^ m + 3 := by
      rcases neg_one_pow_eq_or ℤ m with hs | hs
      · rw [hs]
        exact ⟨2, by norm_num⟩
      · rw [hs]
        exact ⟨1, by norm_num⟩
    have e : (8 : ℤ) ^ m - (-1) ^ m - 3 = (8 : ℤ) ^ m - ((-1) ^ m + 3) := by ring
    rw [e]
    exact dvd_sub h1 h5
  have h6 : (4 : ℤ) ∣ 4 ^ k := dvd_pow_self 4 (by omega)
  have h8 : (8 : ℤ) ∣ ((8 : ℤ) ^ m - (-1) ^ m - 3) * 4 ^ k := by
    have h9 := mul_dvd_mul hP h6
    rw [show (2 : ℤ) * 4 = 8 by norm_num] at h9
    exact h9
  rw [h4] at h8
  omega

end L05A173643

open OMA.S_oeis_a173643 L05A173643 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a173643.main) := by
  intro H
  have hx : InA172233 27 := ⟨by norm_num, 5, 1, 0, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨k, m, hk, hm, h⟩ := H 27 0 3 hx (by norm_num) (by norm_num) ⟨1, by norm_num⟩
  exact no_three k m hk hm h
