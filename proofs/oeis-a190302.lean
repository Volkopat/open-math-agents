import OMAStatements.S_oeis_a190302
import Mathlib

-- Problem: OEIS A190302, the least positive multiplier m such that m * n begins with the
-- digit one is always below six.
-- Proof. Take k with 10^k <= n < 10^(k+1). If n < 2 * 10^k then m = 1 works; if
-- 2 * 10^k <= n < 4 * 10^k then m = 5 works; if 4 * 10^k <= n < 5 * 10^k then m = 4 works;
-- otherwise m = 2 works. So the set of good multipliers contains an element below six, and
-- its least element (well-ordering of the naturals) is below six as well.

open OMA.S_oeis_a190302

lemma OMA.exists_small (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, (0 < m ∧ BeginsWithOne (m * n)) ∧ m < 6 := by
  obtain ⟨k, hk1, hk2⟩ : ∃ k, 10 ^ k ≤ n ∧ n < 10 ^ (k + 1) :=
    ⟨Nat.log 10 n, Nat.pow_log_le_self 10 hn.ne', Nat.lt_pow_succ_log_self (by norm_num) n⟩
  have h10 : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
  rw [h10] at hk2
  by_cases h1 : n < 2 * 10 ^ k
  · refine ⟨1, ⟨by norm_num, k, ?_, ?_⟩, by norm_num⟩
    · omega
    · omega
  by_cases h2 : n < 4 * 10 ^ k
  · refine ⟨5, ⟨by norm_num, k + 1, ?_, ?_⟩, by norm_num⟩
    · rw [h10]
      omega
    · rw [h10]
      omega
  by_cases h3 : n < 5 * 10 ^ k
  · refine ⟨4, ⟨by norm_num, k + 1, ?_, ?_⟩, by norm_num⟩
    · rw [h10]
      omega
    · rw [h10]
      omega
  · refine ⟨2, ⟨by norm_num, k + 1, ?_, ?_⟩, by norm_num⟩
    · rw [h10]
      omega
    · rw [h10]
      omega

theorem OMA.solution : type_of% @OMA.S_oeis_a190302.main := by
  intro n hn
  classical
  obtain ⟨m0, hm0, hlt⟩ := OMA.exists_small n hn
  have hex : ∃ m : ℕ, 0 < m ∧ BeginsWithOne (m * n) := ⟨m0, hm0⟩
  refine ⟨Nat.find hex, ⟨Nat.find_spec hex, fun m hm => Nat.find_min' hex hm⟩, ?_⟩
  exact lt_of_le_of_lt (Nat.find_min' hex hm0) hlt
