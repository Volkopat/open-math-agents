import OMAStatements.S_oeis_a172507
import Mathlib

namespace OMA.S_oeis_a172507

theorem den_eq (n : ℕ) : (repeatedDecimal n).den = clearingFactor n := by
  unfold repeatedDecimal clearingFactor
  rw [Rat.natCast_add_den, Rat.den_mkRat]
  have hs : scale n ≠ 0 := by unfold scale; positivity
  by_cases h : n = 0
  · subst h; simp [scale, Nat.gcd_zero_left]
  · simp [h, hs, Int.gcd, Nat.gcd_comm]

end OMA.S_oeis_a172507

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a172507.main) := by
  rintro ⟨n, -, h⟩
  exact h (OMA.S_oeis_a172507.den_eq n)
