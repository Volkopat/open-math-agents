import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2

-- Step CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R2.H2: hypothesis H2 of reduction CollatzConjecture.collatz_conjecture.R1.H2.R1.H3.R2
-- Credit: @Raimo33

namespace OMAStepCollatzH2

theorem check : ∀ o < 200, 0 < o → 30001 ^ o < 2 ^ (Nat.log2 (3 ^ o) + 1) * 10000 ^ o := by
  decide +kernel

end OMAStepCollatzH2

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2.H2 := by
  intro o e ho ho2 h
  have h3 : 3 ^ o ≠ 0 := by positivity
  have hl : Nat.log2 (3 ^ o) < e := (Nat.log2_lt h3).2 h
  have hle : 2 ^ (Nat.log2 (3 ^ o) + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hl
  have := OMAStepCollatzH2.check o ho2 ho
  calc 30001 ^ o < 2 ^ (Nat.log2 (3 ^ o) + 1) * 10000 ^ o := this
    _ ≤ 2 ^ e * 10000 ^ o := Nat.mul_le_mul_right _ hle
