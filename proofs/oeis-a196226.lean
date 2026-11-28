import OMAStatements.S_oeis_a196226
import Mathlib

-- Counterexample m = 690 = 2 * 3 * 5 * 23 (the refutation the statement cites): sigma(690) = 1728 and
-- 1728 mod 690 = 348 = 3 + 690/2, so 690 is a term, but sigma_2(690) = 689000 = 380 mod 690, while
-- 5 + 690/2 = 350, so the first congruence fails (the other two fail at 690 as well).

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a196226.main) := by
  intro h
  have h1 : ArithmeticFunction.sigma 1 690 = 1728 := by
    rw [ArithmeticFunction.sigma_apply]
    decide +kernel
  have h2 : ArithmeticFunction.sigma 2 690 = 689000 := by
    rw [ArithmeticFunction.sigma_apply]
    decide +kernel
  have hm := h.1 690 (by norm_num) ⟨by norm_num, by rw [h1]⟩
  rw [h2] at hm
  unfold Nat.ModEq at hm
  norm_num at hm
