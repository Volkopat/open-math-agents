import OMAReductions.R_Bugeaud08_problem_10_8_R1
import Mathlib

-- Step Bugeaud08.problem_10_8.R1.H1: hypothesis H1 of reduction Bugeaud08.problem_10_8.R1
-- Credit: @ivillar

/-!
If `q ‖q ξ‖` gets below every `ε > 0`, then so does `q |q|_p ‖q ξ‖` (as `|q|_p ≤ 1`), and all
elements of the set are nonnegative, so the infimum is zero.
-/
namespace F2Bug

theorem notBad : ∀ (ξ : ℝ) (p : ℕ), p.Prime →
    (∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) * distToNearestInt (q * ξ) < ε) →
    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0 := by
  intro ξ p hp h
  have : Fact p.Prime := ⟨hp⟩
  have hle : ∀ n : ℕ, ((padicNorm p n : ℚ) : ℝ) ≤ 1 := by
    intro n
    exact_mod_cast padicNorm.of_nat (p := p) n
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ ((padicNorm p n : ℚ) : ℝ) := by
    intro n
    exact_mod_cast padicNorm.nonneg (p := p) (n : ℚ)
  have hpos : ∀ x ∈ {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)}, 0 ≤ x := by
    rintro x ⟨q, _, rfl⟩
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (hnn q)) (distToNearestInt_nonneg _)
  have hbdd : BddBelow {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} := ⟨0, hpos⟩
  have hne : {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)}.Nonempty := ⟨_, 1, le_refl 1, rfl⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    rw [zero_add]
    obtain ⟨q, hq1, hq⟩ := h ε hε
    refine (csInf_le hbdd ⟨q, hq1, rfl⟩).trans (le_trans ?_ hq.le)
    have h1 : (q : ℝ) * ((padicNorm p q : ℚ) : ℝ) ≤ (q : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (hle q) (Nat.cast_nonneg q)
    calc (q : ℝ) * ((padicNorm p q : ℚ) : ℝ) * distToNearestInt (q * ξ)
        ≤ (q : ℝ) * 1 * distToNearestInt (q * ξ) :=
          mul_le_mul_of_nonneg_right h1 (distToNearestInt_nonneg _)
      _ = q * distToNearestInt (q * ξ) := by ring
  · exact le_csInf hne hpos

end F2Bug

theorem OMA.solution : OMA.R_Bugeaud08_problem_10_8_R1.H1 :=
  F2Bug.notBad
