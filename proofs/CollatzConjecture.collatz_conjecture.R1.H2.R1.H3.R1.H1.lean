import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R1
import Mathlib

-- Step CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R1.H1: hypothesis H1 of reduction CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R1
-- Credit: @Raimo33

namespace OMAE_Col

lemma aux (o E : ℕ) (h1 : 2 ^ E ≤ 3 ^ o) (h2 : 3001 ^ o < 1000 ^ o * 2 ^ (E + 1)) (e : ℕ)
    (h : 3 ^ o < 2 ^ e) : 3001 ^ o < 1000 ^ o * 2 ^ e := by
  have hE : E < e := by
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hc
    omega
  calc 3001 ^ o < 1000 ^ o * 2 ^ (E + 1) := h2
    _ ≤ 1000 ^ o * 2 ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hE)

end OMAE_Col

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R1.H1 := by
  intro o e ho ho41 h
  interval_cases o
  · exact OMAE_Col.aux _ 1 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 3 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 4 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 6 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 7 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 9 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 11 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 12 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 14 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 15 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 17 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 19 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 20 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 22 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 23 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 25 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 26 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 28 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 30 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 31 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 33 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 34 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 36 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 38 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 39 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 41 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 42 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 44 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 45 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 47 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 49 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 50 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 52 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 53 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 55 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 57 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 58 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 60 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 61 (by norm_num) (by norm_num) e h
  · exact OMAE_Col.aux _ 63 (by norm_num) (by norm_num) e h
