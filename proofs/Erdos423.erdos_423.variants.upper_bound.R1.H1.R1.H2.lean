import OMAReductions.R_Erdos423_erdos_423_variants_upper_bound_R1_H1_R1
import Mathlib

-- Step H2 of reduction Erdos423.erdos_423.variants.upper_bound.R1.H1.R1: pass a power lower bound
-- from k to m / 2 (m at most 3 * (m / 2), and m / 2 at most m), losing a factor 3 ^ |r|.

open Filter

namespace OMAE423

theorem step : ∀ b d : ℕ → ℕ,
    (∀ m, b (m / 2) ≤ d m) →
    ∀ r : ℝ,
      (∃ C : ℝ, 0 < C ∧
        ∀ᶠ k : ℕ in atTop,
          (k : ℝ) ^ r ≤ C * (b k : ℝ)) →
      ∃ D : ℝ, 0 < D ∧
        ∀ᶠ m : ℕ in atTop,
          (m : ℝ) ^ r ≤ D * (d m : ℝ) := by
  intro b d hbd r ⟨C, hC, hev⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨(3 : ℝ) ^ |r| * C, by positivity, eventually_atTop.2 ⟨2 * K + 2, fun m hm => ?_⟩⟩
  have hk1 : 1 ≤ m / 2 := by omega
  have hkK : K ≤ m / 2 := by omega
  have hm3 : m ≤ 3 * (m / 2) := by omega
  have hkm : m / 2 ≤ m := Nat.div_le_self m 2
  have hkpos : (0 : ℝ) < ((m / 2 : ℕ) : ℝ) := by exact_mod_cast hk1
  have hkm' : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  have hm3' : (m : ℝ) ≤ 3 * ((m / 2 : ℕ) : ℝ) := by exact_mod_cast hm3
  have hpow : (m : ℝ) ^ r ≤ (3 : ℝ) ^ |r| * ((m / 2 : ℕ) : ℝ) ^ r := by
    rcases le_or_gt 0 r with hr | hr
    · rw [abs_of_nonneg hr, ← Real.mul_rpow (by norm_num) hkpos.le]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hm3' hr
    · have h1 : (m : ℝ) ^ r ≤ ((m / 2 : ℕ) : ℝ) ^ r :=
        Real.rpow_le_rpow_of_nonpos hkpos hkm' hr.le
      have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ |r| := Real.one_le_rpow (by norm_num) (abs_nonneg r)
      have h0 : (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) ^ r := Real.rpow_nonneg hkpos.le r
      nlinarith
  have hb := hK (m / 2) hkK
  have hd : ((b (m / 2) : ℕ) : ℝ) ≤ (d m : ℝ) := by exact_mod_cast hbd m
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ |r| := by positivity
  calc (m : ℝ) ^ r ≤ (3 : ℝ) ^ |r| * ((m / 2 : ℕ) : ℝ) ^ r := hpow
    _ ≤ (3 : ℝ) ^ |r| * (C * (b (m / 2) : ℝ)) := mul_le_mul_of_nonneg_left hb h3
    _ ≤ (3 : ℝ) ^ |r| * (C * (d m : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hC.le) h3
    _ = (3 : ℝ) ^ |r| * C * (d m : ℝ) := by ring

end OMAE423

theorem OMA.solution : OMA.R_Erdos423_erdos_423_variants_upper_bound_R1_H1_R1.H2 := OMAE423.step
