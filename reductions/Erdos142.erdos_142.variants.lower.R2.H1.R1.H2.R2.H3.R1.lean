import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R1 of step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3
-- Credit: @joshuadc11

/-!
# Dyadic quasipolynomial reduction for k >= 5 extremal densities

By subadditivity (`r k (2 * M) ≤ 2 * r k M`), summability of `r k (4 ^ j) / 4 ^ j` is
equivalent to summability of the dyadic series `r k (2 ^ m) / 2 ^ m`. This separates the
combinatorial density estimate `H1` (matching `OAI.Erdos3.QuantitativeDensityBound` for `k ≥ 5`
with `(log log N)^(1 + η)` saving) from the self-contained dyadic summability `H2`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1

open Erdos142 Filter

/-- Quasipolynomial `(log log N)^(1 + η)` saving for every progression length at least five. -/
def H1 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) ≤ C * (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ (1 + η))

/-- The `(log log (2 ^ m))^(1 + η)` saving is summable along dyadic scales. -/
def H2 : Prop :=
  ∀ c η : ℝ, 0 < c → 0 < η →
    Summable (fun m : ℕ ↦ Real.exp (-c * Real.log (Real.log ((2 : ℝ) ^ m)) ^ (1 + η)))

lemma r_two_mul_le (k M : ℕ) : r k (2 * M) ≤ 2 * r k M := by
  have h := OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_add_le k M M
  simpa [r, two_mul] using h

lemma summable_four_pow_iff_dyadic (k : ℕ) :
    Summable (fun j : ℕ => (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) ↔
      Summable (fun m : ℕ => (r k (2 ^ m) : ℝ) / (2 : ℝ) ^ m) := by
  constructor
  · intro hs
    have heven : Summable (fun j : ℕ => (r k (2 ^ (2 * j)) : ℝ) / (2 : ℝ) ^ (2 * j)) := by
      simpa only [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num,
        show (2 : ℝ) ^ 2 = 4 by norm_num] using hs
    have hodd_bound : ∀ j : ℕ,
        ‖(r k (2 ^ (2 * j + 1)) : ℝ) / (2 : ℝ) ^ (2 * j + 1)‖ ≤
          (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j := by
      intro j
      rw [Real.norm_of_nonneg (by positivity)]
      have hmul := r_two_mul_le k (4 ^ j)
      have hpow : 2 ^ (2 * j + 1) = 2 * 4 ^ j := by
        rw [pow_succ', pow_mul]; norm_num
      have hpowR : (2 : ℝ) ^ (2 * j + 1) = 2 * (4 : ℝ) ^ j := by
        rw [pow_succ', pow_mul]; norm_num
      rw [hpow, hpowR, div_le_div_iff₀ (by positivity) (by positivity)]
      have hmulR : (r k (2 * 4 ^ j) : ℝ) ≤ 2 * (r k (4 ^ j) : ℝ) := by exact_mod_cast hmul
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) j]
    have hodd : Summable (fun j : ℕ => (r k (2 ^ (2 * j + 1)) : ℝ) / (2 : ℝ) ^ (2 * j + 1)) :=
      Summable.of_norm_bounded hs hodd_bound
    exact Summable.even_add_odd heven hodd
  · intro hs
    have hinj : Function.Injective (fun j : ℕ => 2 * j) := fun a b h => by dsimp only at h; omega
    have hsub := hs.comp_injective hinj
    simpa only [Function.comp_def, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num,
      show (2 : ℝ) ^ 2 = 4 by norm_num] using hsub

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2.H3 := by
  intro h1 h2 k hk
  obtain ⟨C, c, η, hC, hc, hη, hb⟩ := h1 k hk
  have hs : Summable (fun m : ℕ =>
      C * Real.exp (-c * Real.log (Real.log ((2 : ℝ) ^ m)) ^ (1 + η))) :=
    (h2 c η hc hη).mul_left C
  have hT : Tendsto (fun m : ℕ => (2 : ℕ) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hdyad : Summable (fun m : ℕ => (r k (2 ^ m) : ℝ) / (2 : ℝ) ^ m) := by
    refine Summable.of_norm_bounded_eventually_nat hs ?_
    filter_upwards [hT.eventually hb] with m hm
    rw [Real.norm_of_nonneg (by positivity)]
    have hx : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by norm_num
    rw [hx] at hm
    rw [div_le_iff₀ (by positivity)]
    calc (r k (2 ^ m) : ℝ)
        ≤ C * (2 : ℝ) ^ m * Real.exp (-c * Real.log (Real.log ((2 : ℝ) ^ m)) ^ (1 + η)) := hm
      _ = C * Real.exp (-c * Real.log (Real.log ((2 : ℝ) ^ m)) ^ (1 + η)) * (2 : ℝ) ^ m := by ring
  exact (summable_four_pow_iff_dyadic k).mpr hdyad

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1
