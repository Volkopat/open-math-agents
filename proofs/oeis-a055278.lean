import OMAStatements.S_oeis_a055278
import Mathlib

open PowerSeries OMA.S_oeis_a055278 in
theorem OMA.solution : type_of% @OMA.S_oeis_a055278.main := by
  have h (n : ℕ) : A055278 (4 + (n + 12)) = A055278 (4 + n) + (n ^ 3 + 25 * n ^ 2 + 245 * n + 885) := by
    rw [A055278, A055278, ← Int.add_mul_ediv_right _ _ (by decide : (144 : ℤ) ≠ 0)]
    push_cast
    ring_nf
  ring_nf
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 20 with g | g
    · interval_cases n <;> simp [coeff_mul_X_pow', coeff_X_pow, ← map_ofNat C, coeff_mul_C, coeff_succ_mul_X] <;> norm_num [A055278]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 20 := ⟨n - 20, by omega⟩
      have := ih (m + 8) (by omega)
      simp [coeff_mul_X_pow', coeff_X_pow, ← map_ofNat C, coeff_mul_C, coeff_succ_mul_X, h] at this ⊢
      linear_combination this
