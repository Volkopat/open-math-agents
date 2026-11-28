import OMAReductions.R_LittlewoodConjecture_padic_littlewood_conjecture_R1
import Mathlib

-- Step LittlewoodConjecture.padic_littlewood_conjecture.R1.H1: hypothesis H1 of reduction LittlewoodConjecture.padic_littlewood_conjecture.R1
-- Credit: @ivillar

/-!
If `n ‖n α‖` is frequently below every `ε > 0`, then so is `n |n|_p ‖n α‖` (as `|n|_p ≤ 1`),
and all terms are nonnegative, so the liminf is zero.
-/
namespace F2PLW
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

theorem notBad : ∀ (α : ℝ) (p : ℕ), p.Prime →
    (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, n * distToNearestInt (n * α) < ε) →
    atTop.liminf (fun (n : ℕ) ↦ n * padicNorm p n * distToNearestInt (n * α)) = 0 := by
  intro α p hp h
  have : Fact p.Prime := ⟨hp⟩
  have hle : ∀ n : ℕ, ((padicNorm p n : ℚ) : ℝ) ≤ 1 := by
    intro n
    exact_mod_cast padicNorm.of_nat (p := p) n
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ ((padicNorm p n : ℚ) : ℝ) := by
    intro n
    exact_mod_cast padicNorm.nonneg (p := p) (n : ℚ)
  apply liminf_zero
  · intro n
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (hnn n)) (distToNearestInt_nonneg _)
  · intro ε hε
    refine (h ε hε).mono fun n hn => lt_of_le_of_lt ?_ hn
    have h1 : (n : ℝ) * ((padicNorm p n : ℚ) : ℝ) ≤ (n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (hle n) (Nat.cast_nonneg n)
    calc (n : ℝ) * ((padicNorm p n : ℚ) : ℝ) * distToNearestInt (n * α)
        ≤ (n : ℝ) * 1 * distToNearestInt (n * α) :=
          mul_le_mul_of_nonneg_right h1 (distToNearestInt_nonneg _)
      _ = n * distToNearestInt (n * α) := by ring

end F2PLW

theorem OMA.solution : OMA.R_LittlewoodConjecture_padic_littlewood_conjecture_R1.H1 :=
  F2PLW.notBad
