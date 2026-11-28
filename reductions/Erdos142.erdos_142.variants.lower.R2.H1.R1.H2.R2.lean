import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2
-- Credit: @TomsBack

/-!
# Summable 4-term densities from a relative comparison with 3-term densities

The target is step H2 of reduction R2.H1.R1 of Erdős 142: for every k at least four the
normalized extremal numbers r_k(4^j) / 4^j are summable. This reduction separates the length
four from the longer lengths and reduces the length four to a comparison between the extremal
numbers of 4-term and 3-term progressions.

H1 asserts that the density of an extremal 4-AP-free set is eventually at most a constant times
the density of an extremal 3-AP-free set raised to a fixed power θ > 1/2. H2 is the bound
r_3(N) at most N / (log N)^2, which follows from the Kelley–Meka theorem (it is proved in this
repository as Erdos142KM.logSquare, which is not importable here). H3 is the summability for
every length at least five.

Combining H1 and H2 gives r_4(N) / N at most C (log N)^(-2θ) with 2θ > 1. At N = 4^j this
reads r_4(4^j) / 4^j at most C (log 4)^(-2θ) j^(-2θ), and the p-series test concludes.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2

open Erdos142 Filter

/-- The 4-term extremal density is eventually at most a constant times the 3-term extremal
density raised to a power θ > 1/2. -/
def H1 : Prop :=
  ∃ θ C : ℝ, 1 / 2 < θ ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    (r 4 N : ℝ) ≤ C * (N : ℝ) * ((r 3 N : ℝ) / (N : ℝ)) ^ θ

/-- The Kelley–Meka strength bound r_3(N) at most N / (log N)^2. -/
def H2 : Prop :=
  ∀ᶠ N : ℕ in atTop, (r 3 N : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ)

/-- The extremal densities on the scales 4^j are summable for every length at least five. -/
def H3 : Prop :=
  ∀ k : ℕ, 5 ≤ k → Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j)

/-- The pointwise density bound for 4-term progressions at the scale 4^j. -/
lemma dens_bound {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C) {j : ℕ} (hj : 0 < j)
    (h4 : (r 4 (4 ^ j) : ℝ) ≤
      C * ((4 ^ j : ℕ) : ℝ) * ((r 3 (4 ^ j) : ℝ) / ((4 ^ j : ℕ) : ℝ)) ^ θ)
    (h3 : (r 3 (4 ^ j) : ℝ) ≤ ((4 ^ j : ℕ) : ℝ) / Real.log ((4 ^ j : ℕ) : ℝ) ^ (2 : ℝ)) :
    (r 4 (4 ^ j) : ℝ) / (4 : ℝ) ^ j ≤
      C * (Real.log 4 ^ (2 * θ))⁻¹ * ((j : ℝ) ^ (2 * θ))⁻¹ := by
  have hx : ((4 ^ j : ℕ) : ℝ) = (4 : ℝ) ^ j := by norm_num
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hL : Real.log ((4 ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log 4 := by
    rw [hx, Real.log_pow]
  have hLpos : 0 < (j : ℝ) * Real.log 4 := mul_pos hjpos hl4
  rw [hL, hx] at h3
  rw [hx] at h4
  have hP : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
  have ht0 : (0 : ℝ) ≤ (r 3 (4 ^ j) : ℝ) / (4 : ℝ) ^ j := by positivity
  have ht : (r 3 (4 ^ j) : ℝ) / (4 : ℝ) ^ j ≤ (((j : ℝ) * Real.log 4) ^ (2 : ℝ))⁻¹ := by
    rw [div_le_iff₀ hP]
    calc (r 3 (4 ^ j) : ℝ) ≤ (4 : ℝ) ^ j / ((j : ℝ) * Real.log 4) ^ (2 : ℝ) := h3
      _ = (((j : ℝ) * Real.log 4) ^ (2 : ℝ))⁻¹ * (4 : ℝ) ^ j := by ring
  have htθ : ((r 3 (4 ^ j) : ℝ) / (4 : ℝ) ^ j) ^ θ ≤
      ((j : ℝ) ^ (2 * θ))⁻¹ * (Real.log 4 ^ (2 * θ))⁻¹ := by
    calc ((r 3 (4 ^ j) : ℝ) / (4 : ℝ) ^ j) ^ θ
        ≤ ((((j : ℝ) * Real.log 4) ^ (2 : ℝ))⁻¹) ^ θ := Real.rpow_le_rpow ht0 ht hθ
      _ = (((j : ℝ) * Real.log 4) ^ (2 * θ))⁻¹ := by
          rw [Real.inv_rpow (Real.rpow_nonneg hLpos.le _), ← Real.rpow_mul hLpos.le]
      _ = ((j : ℝ) ^ (2 * θ))⁻¹ * (Real.log 4 ^ (2 * θ))⁻¹ := by
          rw [Real.mul_rpow hjpos.le hl4.le]
          ring
  have hCP : (0 : ℝ) ≤ C * (4 : ℝ) ^ j := mul_nonneg hC hP.le
  rw [div_le_iff₀ hP]
  calc (r 4 (4 ^ j) : ℝ) ≤ C * (4 : ℝ) ^ j * ((r 3 (4 ^ j) : ℝ) / (4 : ℝ) ^ j) ^ θ := h4
    _ ≤ C * (4 : ℝ) ^ j * (((j : ℝ) ^ (2 * θ))⁻¹ * (Real.log 4 ^ (2 * θ))⁻¹) :=
        mul_le_mul_of_nonneg_left htθ hCP
    _ = C * (Real.log 4 ^ (2 * θ))⁻¹ * ((j : ℝ) ^ (2 * θ))⁻¹ * (4 : ℝ) ^ j := by ring

/-- The relative comparison together with the Kelley–Meka strength bound makes the normalized
4-term extremal numbers summable. -/
lemma summable_four {θ C : ℝ} (hθ : 1 / 2 < θ) (hC : 0 < C)
    (h4 : ∀ᶠ N : ℕ in atTop, (r 4 N : ℝ) ≤ C * (N : ℝ) * ((r 3 N : ℝ) / (N : ℝ)) ^ θ)
    (h3 : ∀ᶠ N : ℕ in atTop, (r 3 N : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ)) :
    Summable (fun j : ℕ ↦ (r 4 (4 ^ j) : ℝ) / (4 : ℝ) ^ j) := by
  have hp : Summable (fun j : ℕ ↦ C * (Real.log 4 ^ (2 * θ))⁻¹ * ((j : ℝ) ^ (2 * θ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _
  have hT : Tendsto (fun j : ℕ ↦ 4 ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hp ?_
  filter_upwards [hT.eventually h4, hT.eventually h3, eventually_gt_atTop 0] with j hj4 hj3 hj0
  rw [Real.norm_of_nonneg (by positivity)]
  exact dens_bound (by linarith) hC.le hj0 hj4 hj3

theorem main : H1 → H2 → H3 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1.H2 := by
  intro h1 h2 h3 k hk
  rcases eq_or_lt_of_le hk with rfl | hk5
  · obtain ⟨θ, C, hθ, hC, h4⟩ := h1
    exact summable_four hθ hC h4 h2
  · exact h3 k hk5

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2
