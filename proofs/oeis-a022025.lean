import OMAStatements.S_oeis_a022025

/-!
Bruno Berselli and M. F. Hasler identified the discrepancy at index 272 in OEIS A022025.
The original Lean disproof by @agchua is recorded in lefttosolve2/open-math-agents#18893.
We evaluate the defining floor recurrence directly on consecutive natural numbers.
-/

namespace OMA.A022025

open S_oeis_a022025 PowerSeries

/-- Keep consecutive terms together so that each division is computed once. -/
private def consecutive : ℕ → ℕ × ℕ
  | 0 => (6, 102)
  | n + 1 =>
    let (x, y) := consecutive n
    (y, y^2 / x + 1)

private theorem consecutive_terms (n : ℕ) :
    a n = (consecutive n).1 ∧ a (n+1) = (consecutive n).2 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rcases h : consecutive n with ⟨x, y⟩
    rw [h] at ih
    rcases ih with ⟨hx, hy⟩
    simp only [consecutive, h]
    refine ⟨hy, ?_⟩
    rw [a, hx, hy]
    simp only [Int.cast_natCast, ← Nat.cast_pow, Rat.floor_natCast_div_natCast,
      Nat.cast_add, Nat.cast_one, Int.natCast_ediv]

private theorem discrepancy :
    (consecutive 272).1 + 14 * (consecutive 269).1 ≠
      17 * (consecutive 271).1 + (consecutive 270).1 := by
  set_option maxRecDepth 4096 in
  norm_num [consecutive]

end OMA.A022025

open OMA.S_oeis_a022025 OMA.A022025 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a022025.main) := by
  intro H
  let F := mk fun n => (a n : ℚ)
  change F * (1 - 17 * X - X^2 + 14 * X^3) = 6 - 5 * X^2 at H
  have leftSide : F * (1 - 17 * X - X^2 + 14 * X^3) =
      F - C (17:ℚ) * (F * X^1) - F * X^2 + C (14:ℚ) * (F * X^3) := by
    simp only [map_ofNat]
    ring
  have rightSide : (6 - 5 * X^2 : PowerSeries ℚ) = C (6:ℚ) - C (5:ℚ) * X^2 := by
    simp only [map_ofNat]
  rw [leftSide, rightSide] at H
  have h := congrArg (coeff 272) H
  norm_num [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, F] at h
  have heq : (a 272 : ℚ) + 14 * a 269 = 17 * a 271 + a 270 := by linarith
  simp_rw [(consecutive_terms _).1, Int.cast_natCast] at heq
  exact discrepancy (by exact_mod_cast heq)
