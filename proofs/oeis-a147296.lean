import OMAStatements.S_oeis_a147296

-- Problem: A147296: a(n) = n*(9*n+2).
-- Upstream: formal-conjectures statements/oeis-a147296.lean:0 (declaration OMA.S_oeis_a147296.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(n) = A061039(27n+3) is the numerator of 1/9 - 1/(27n+3)^2, and
-- 1/9 - 1/(9(9n+1)^2) = n(9n+2)/(9n+1)^2. Since 9n+1 - 9n = 1 and (9n+2) - (9n+1) = 1, the
-- numerator n(9n+2) is coprime to (9n+1)^2, so it is the numerator in lowest terms.

namespace R10A147296

open OMA.S_oeis_a147296

theorem key (n : ℕ) :
    (1 : ℚ) / 9 - 1 / ((3 * (9 * n + 1) : ℕ) : ℚ) ^ 2 =
      (((n : ℤ) * (9 * n + 2) : ℤ) : ℚ) / (((9 * (n : ℤ) + 1) ^ 2 : ℤ) : ℚ) := by
  have hB : (3 * (9 * (n : ℚ) + 1)) ^ 2 ≠ 0 := by positivity
  have hBD : 9 * (3 * (9 * (n : ℚ) + 1)) ^ 2 ≠ 0 := by positivity
  have hD : (9 * (n : ℚ) + 1) ^ 2 ≠ 0 := by positivity
  push_cast
  rw [div_sub_div 1 1 (by norm_num : (9 : ℚ) ≠ 0) hB, div_eq_div_iff hBD hD]
  ring

theorem cop (n : ℕ) : IsCoprime ((n : ℤ) * (9 * n + 2)) ((9 * (n : ℤ) + 1) ^ 2) := by
  apply IsCoprime.pow_right
  apply IsCoprime.mul_left
  · exact ⟨-9, 1, by ring⟩
  · exact ⟨1, -1, by ring⟩

end R10A147296

open OMA.S_oeis_a147296 R10A147296 in
theorem OMA.solution : type_of% @OMA.S_oeis_a147296.main := by
  intro n
  have hb : (0 : ℤ) < (9 * (n : ℤ) + 1) ^ 2 := by positivity
  have hc : Nat.Coprime ((n : ℤ) * (9 * n + 2)).natAbs ((9 * (n : ℤ) + 1) ^ 2).natAbs :=
    Int.isCoprime_iff_gcd_eq_one.mp (cop n)
  unfold a A144454 A061039
  rw [key n]
  exact Rat.num_div_eq_of_coprime hb hc
