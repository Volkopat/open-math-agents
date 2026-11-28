import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R1

-- Step CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R1.H1: hypothesis H1 of reduction CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R1
-- Credit: @Raimo33 (first proof); shorter proof by @conormcfarland

/-! For each 0 < o < 41 let E be the least exponent with 3^o < 2^E. Any 2^e above 3^o is at
least 2^E, and 3001^o < 1000^o * 2^E is checked numerically case by case
(tightest case o = 29, E = 46, margin about 1.5%). -/

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R1.H1 := by
  intro o e ho ho41 h
  have H (E : ℕ) (h1 : 2 ^ E ≤ 2 * 3 ^ o) (h2 : 3001 ^ o < 1000 ^ o * 2 ^ E) :
      3001 ^ o < 1000 ^ o * 2 ^ e := by
    have hE : E ≤ e := by
      by_contra hc
      have h3 : 2 ^ (e + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at h3
      omega
    exact lt_of_lt_of_le h2 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hE))
  interval_cases o
  · exact H 2 (by norm_num) (by norm_num)
  · exact H 4 (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num)
  · exact H 7 (by norm_num) (by norm_num)
  · exact H 8 (by norm_num) (by norm_num)
  · exact H 10 (by norm_num) (by norm_num)
  · exact H 12 (by norm_num) (by norm_num)
  · exact H 13 (by norm_num) (by norm_num)
  · exact H 15 (by norm_num) (by norm_num)
  · exact H 16 (by norm_num) (by norm_num)
  · exact H 18 (by norm_num) (by norm_num)
  · exact H 20 (by norm_num) (by norm_num)
  · exact H 21 (by norm_num) (by norm_num)
  · exact H 23 (by norm_num) (by norm_num)
  · exact H 24 (by norm_num) (by norm_num)
  · exact H 26 (by norm_num) (by norm_num)
  · exact H 27 (by norm_num) (by norm_num)
  · exact H 29 (by norm_num) (by norm_num)
  · exact H 31 (by norm_num) (by norm_num)
  · exact H 32 (by norm_num) (by norm_num)
  · exact H 34 (by norm_num) (by norm_num)
  · exact H 35 (by norm_num) (by norm_num)
  · exact H 37 (by norm_num) (by norm_num)
  · exact H 39 (by norm_num) (by norm_num)
  · exact H 40 (by norm_num) (by norm_num)
  · exact H 42 (by norm_num) (by norm_num)
  · exact H 43 (by norm_num) (by norm_num)
  · exact H 45 (by norm_num) (by norm_num)
  · exact H 46 (by norm_num) (by norm_num)
  · exact H 48 (by norm_num) (by norm_num)
  · exact H 50 (by norm_num) (by norm_num)
  · exact H 51 (by norm_num) (by norm_num)
  · exact H 53 (by norm_num) (by norm_num)
  · exact H 54 (by norm_num) (by norm_num)
  · exact H 56 (by norm_num) (by norm_num)
  · exact H 58 (by norm_num) (by norm_num)
  · exact H 59 (by norm_num) (by norm_num)
  · exact H 61 (by norm_num) (by norm_num)
  · exact H 62 (by norm_num) (by norm_num)
  · exact H 64 (by norm_num) (by norm_num)
