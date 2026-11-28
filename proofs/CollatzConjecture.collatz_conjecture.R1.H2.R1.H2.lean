import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1

/-! A trajectory minimum cannot be even (one step descends), or be 1 modulo 4
(three steps descend when the starting value exceeds 1). -/

open CollatzConjecture

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1.H2 := by
  intro n hn hmin
  have h1 := hmin 1
  have h3 := hmin 3
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at h1 h3
  simp only [collatzStep, Nat.even_iff] at h1 h3
  split_ifs at h1 h3 <;> omega
