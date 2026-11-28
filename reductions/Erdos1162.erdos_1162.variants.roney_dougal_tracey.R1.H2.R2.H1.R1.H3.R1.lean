import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1
import Mathlib.Tactic.NormNum


/-!
Roney-Dougal and Tracey, *Subgroups of symmetric groups: enumeration and
asymptotic properties*, Theorem 2 and its proof in §7.
https://arxiv.org/html/2503.05416#S7

Proposition 7.8 gives the coefficient 3/2 for primes at least 11. The
remaining part of the proof allows a separate constant for each smaller prime.
-/

namespace OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H3_R1

private theorem bound_mono {p m : ℕ} {a b : ℝ}
    (hm : 2 ≤ m) (hab : a ≤ b) :
    (2 : ℝ) ^ (Real.logb 2 (p : ℝ) * (m : ℝ)^2 / (4 * (p : ℝ)^2) +
        a * (m : ℝ) * Real.logb 2 (m : ℝ)) ≤
      (2 : ℝ) ^ (Real.logb 2 (p : ℝ) * (m : ℝ)^2 / (4 * (p : ℝ)^2) +
        b * (m : ℝ) * Real.logb 2 (m : ℝ)) := by
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hlog : 0 ≤ Real.logb 2 (m : ℝ) := Real.logb_nonneg (by norm_num) hm₁
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg m)) hlog))

private theorem small_prime {p : ℕ} (hp : p.Prime) (h : p < 11) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have hsmall : ∀ n : Fin 11, n.val.Prime → n.val = 2 ∨
      n.val = 3 ∨ n.val = 5 ∨ n.val = 7 := by decide
  exact hsmall ⟨p, h⟩ hp

/-- The uniform large-prime bound of Proposition 7.8. -/
def H1 : Prop :=
  ∀ (p m : ℕ), p.Prime → 11 ≤ p → p ≤ m →
    (Nat.card {P : Subgroup (Equiv.Perm (Fin m)) // IsPGroup p P} : ℝ) ≤
      (2 : ℝ) ^ (Real.logb 2 (p : ℝ) * (m : ℝ)^2 / (4 * (p : ℝ)^2) +
        (3 / 2 : ℝ) * (m : ℝ) * Real.logb 2 (m : ℝ))

/-- The fixed-prime upper bound for each of the four smaller primes. -/
def H2 : Prop :=
  ∀ (p : ℕ), p.Prime → p < 11 → ∃ γ : ℝ, 0 ≤ γ ∧ ∀ m : ℕ, p ≤ m →
    (Nat.card {P : Subgroup (Equiv.Perm (Fin m)) // IsPGroup p P} : ℝ) ≤
      (2 : ℝ) ^ (Real.logb 2 (p : ℝ) * (m : ℝ)^2 / (4 * (p : ℝ)^2) +
        γ * (m : ℝ) * Real.logb 2 (m : ℝ))

theorem main : H1 → H2 →
    OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1.H3 := by
  intro hlarge hsmall
  obtain ⟨γ₂, _, h₂⟩ := hsmall 2 (by decide) (by decide)
  obtain ⟨γ₃, _, h₃⟩ := hsmall 3 (by decide) (by decide)
  obtain ⟨γ₅, _, h₅⟩ := hsmall 5 (by decide) (by decide)
  obtain ⟨γ₇, _, h₇⟩ := hsmall 7 (by decide) (by decide)
  let γ := max (3 / 2 : ℝ) (max (max γ₂ γ₃) (max γ₅ γ₇))
  have hlargeγ : (3 / 2 : ℝ) ≤ γ := le_max_left _ _
  have h₂₃ : max γ₂ γ₃ ≤ γ := (le_max_left _ _).trans (le_max_right _ _)
  have h₅₇ : max γ₅ γ₇ ≤ γ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨γ, (by norm_num : (0 : ℝ) ≤ 3 / 2).trans hlargeγ, ?_⟩
  intro p m hp hpm
  have hm : 2 ≤ m := hp.two_le.trans hpm
  by_cases h : 11 ≤ p
  · exact (hlarge p m hp h hpm).trans (bound_mono hm hlargeγ)
  · rcases small_prime hp (by omega) with rfl | rfl | rfl | rfl
    · exact (h₂ m hpm).trans (bound_mono hm ((le_max_left _ _).trans h₂₃))
    · exact (h₃ m hpm).trans (bound_mono hm ((le_max_right _ _).trans h₂₃))
    · exact (h₅ m hpm).trans (bound_mono hm ((le_max_left _ _).trans h₅₇))
    · exact (h₇ m hpm).trans (bound_mono hm ((le_max_right _ _).trans h₅₇))

end OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H3_R1
