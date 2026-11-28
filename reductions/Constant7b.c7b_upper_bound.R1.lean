import FormalConjectures.OptimizationConstants.«7b»
import Mathlib

-- Reduction Constant7b.c7b_upper_bound.R1 of c7b upper bound
-- Credit: @arindale
-- Bruiltet's explicit rational-approximation lower bound for Gamma(1/4) is the deep input;
-- the elimination from it to an irrationality-exponent bound is the elementary part.

namespace OMA.R_Constant7b_c7b_upper_bound_R1
open Real ENNReal Filter
open scoped ENNReal NNReal Topology

/-- Bruiltet's explicit lower bound: rationals cannot approximate `Gamma(1/4)` better than
`c / n ^ (10 ^ 143)` for large denominators. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ (m : ℤ) (n : ℕ), N ≤ n →
    c / (n : ℝ) ^ ((10 : ℝ) ^ 143) < |Real.Gamma (1 / 4) - m / n|

/-- Elementary comparison: once `p > 10 ^ 143`, `C / n ^ p` is eventually smaller than
`c / n ^ (10 ^ 143)`. -/
def H2 : Prop :=
  ∀ c C : ℝ, 0 < c → 0 < C → ∀ p : ℝ, (10 : ℝ) ^ 143 < p →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C / (n : ℝ) ^ p < c / (n : ℝ) ^ ((10 : ℝ) ^ 143)

theorem main : H1 → H2 → type_of% @Constant7b.c7b_upper_bound := by
  intro h1 h2
  obtain ⟨c, hc, N, hN⟩ := h1
  unfold Constant7b.C7b Constant7a.irrationalityExponent
  apply sSup_le_iff.mpr
  rintro a ⟨p, hp, rfl⟩
  have hp_le : p ≤ (10 : ℝ≥0) ^ 143 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    by_contra hle
    have hgt : (10 : ℝ) ^ 143 < (p : ℝ) := lt_of_not_ge hle
    obtain ⟨C, hC, hfreq⟩ := hp.exists_pos
    obtain ⟨N2, hN2⟩ := h2 c C hc hC (p : ℝ) hgt
    obtain ⟨n, ⟨hn1, m, hne, hlt⟩, hnmax⟩ :=
      (hfreq.and_eventually (eventually_ge_atTop (max N N2))).exists
    have hNle : N ≤ n := le_trans (le_max_left _ _) hnmax
    have hN2le : N2 ≤ n := le_trans (le_max_right _ _) hnmax
    have hlow := hN m n hNle
    have hhigh := hN2 n hN2le
    linarith
  calc (p : ℝ≥0∞) ≤ ((10 : ℝ≥0) ^ 143 : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hp_le
    _ = (10 : ℝ≥0∞) ^ 143 := by norm_num

end OMA.R_Constant7b_c7b_upper_bound_R1
