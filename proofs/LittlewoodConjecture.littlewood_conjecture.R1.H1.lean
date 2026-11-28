import OMAReductions.R_LittlewoodConjecture_littlewood_conjecture_R1
import Mathlib

-- Step LittlewoodConjecture.littlewood_conjecture.R1.H1: hypothesis H1 of reduction LittlewoodConjecture.littlewood_conjecture.R1
-- Credit: @ivillar

/-!
The rational case of the Littlewood conjecture: along the multiples of the denominator of `α`
the factor `‖n α‖` vanishes, and all terms are nonnegative, so the liminf is zero.
-/
namespace F2LW
open Filter

theorem liminf_zero (u : ℕ → ℝ) (h0 : ∀ n, 0 ≤ u n)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, u n < ε) : liminf u atTop = 0 := by
  have hb : IsBoundedUnder (· ≥ ·) atTop u := isBoundedUnder_of ⟨0, fun n => h0 n⟩
  have hc : IsCoboundedUnder (· ≥ ·) atTop u :=
    IsCoboundedUnder.of_frequently_le (a := 1) ((hf 1 one_pos).mono fun n h => h.le)
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    rw [zero_add]
    exact liminf_le_of_frequently_le ((hf ε hε).mono fun n h => h.le) hb
  · exact le_liminf_of_le hc (Eventually.of_forall h0)

theorem rational : ∀ α β : ℝ, (∃ q : ℚ, α = q) →
    atTop.liminf (fun (n : ℕ) ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) = 0 := by
  rintro α β ⟨q, rfl⟩
  apply liminf_zero
  · intro n
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (distToNearestInt_nonneg _))
      (distToNearestInt_nonneg _)
  · intro ε hε
    rw [frequently_atTop]
    intro N
    refine ⟨(N + 1) * q.den, ?_, ?_⟩
    · have := q.den_pos
      nlinarith
    · have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
      have hint : (((N + 1) * q.den : ℕ) : ℝ) * (q : ℝ) = (((N + 1 : ℕ) * q.num : ℤ) : ℝ) := by
        rw [Rat.cast_def]
        push_cast
        field_simp
      have hz : distToNearestInt ((((N + 1) * q.den : ℕ) : ℝ) * (q : ℝ)) = 0 := by
        rw [hint, distToNearestInt, round_intCast, sub_self, abs_zero]
      rw [hz, mul_zero, zero_mul]
      exact hε

end F2LW

theorem OMA.solution : OMA.R_LittlewoodConjecture_littlewood_conjecture_R1.H1 :=
  F2LW.rational
