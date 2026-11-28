import OMAStatements.S_oeis_a136809

-- Problem: A136809: Numbers k such that k and k^2 use only the digits 0, 1, 2 and 3.
-- Upstream: formal-conjectures statements/oeis-a136809.lean:0 (declaration OMA.S_oeis_a136809.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: the counterexample of Michael S. Branicky (Nov 04 2020, in the entry):
-- k = 110010000010100001010000010011 and
-- k^2 = 12102200102222202222322212223022221222322220222220100220121 use only the digits 0 to 3,
-- but k has two runs of 11 (positions 0, 1 and 28, 29, with a 0 at position 2).

open OMA.S_oeis_a136809 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a136809.main) := by
  intro H
  have hsq : (110010000010100001010000010011 : ℕ) ^ 2 =
      12102200102222202222322212223022221222322220222220100220121 := by norm_num
  have small : ∀ N B : ℕ, N < 10 ^ B → (∀ i : ℕ, i < B → N / 10 ^ i % 10 ≤ 3) →
      ∀ i : ℕ, N / 10 ^ i % 10 ≤ 3 := by
    intro N B hN hlow i
    rcases Nat.lt_or_ge i B with h | h
    · exact hlow i h
    · have h0 : N / 10 ^ i = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) h))
      simp [h0]
  have low1 : ∀ i : ℕ, i < 30 → (110010000010100001010000010011 : ℕ) / 10 ^ i % 10 ≤ 3 := by
    intro i hi
    interval_cases i <;> norm_num
  have low2 : ∀ i : ℕ, i < 60 →
      (12102200102222202222322212223022221222322220222220100220121 : ℕ) / 10 ^ i % 10 ≤ 3 := by
    intro i hi
    interval_cases i <;> norm_num
  have hK : IsTerm 110010000010100001010000010011 := by
    refine ⟨fun i => ?_, fun i => ?_⟩
    · unfold digit
      exact small _ 30 (by norm_num) low1 i
    · unfold digit
      rw [hsq]
      exact small _ 60 (by norm_num) low2 i
  have hneg := (H _ hK).2.2
  exact hneg ⟨0, 2, 28, by norm_num, by norm_num, by norm_num [digit], by norm_num [digit],
    by norm_num [digit], by norm_num [digit], by norm_num [digit]⟩
