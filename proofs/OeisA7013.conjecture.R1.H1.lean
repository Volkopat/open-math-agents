import OMAReductions.R_OeisA7013_conjecture_R1

-- Step OeisA7013.conjecture.R1.H1: hypothesis H1 of reduction OeisA7013.conjecture.R1
-- Credit: @JamesSlash. a 0..a 3 = 2, 3, 7, 127 by norm_num; a 4 = mersenne 127 by the
-- Lucas-Lehmer test (Mathlib's lucas_lehmer_sufficiency with its norm_num extension).

theorem OMA.solution : OMA.R_OeisA7013_conjecture_R1.H1 := by
  intro n hn
  have h4 : OeisA7013.a 4 = mersenne 127 := rfl
  interval_cases n
  · exact Nat.prime_two
  · exact Nat.prime_three
  · show (7 : ℕ).Prime
    norm_num
  · show (127 : ℕ).Prime
    norm_num
  · rw [h4]
    exact lucas_lehmer_sufficiency 127 (by norm_num) (by norm_num)
