import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2
import Mathlib

/-!
# Condensation of the extremal densities

Partitioning an interval into four equal intervals suggests the finite extremal
inequality H1. It makes the normalized densities antitone on powers of four.
Thus H2 needs a quantitative estimate only on the sparse sizes N = 4^(2^m).
The bound there has order 1 / (log N (log log N)^p) for p > 1.
Multiplication by the condensation weight 2^m leaves a convergent p-series.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3

open Erdos142 Filter

/-- The four equal subintervals of [1, 4N] each have extremal size at most r k N. -/
def H1 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∀ N : ℕ, r k (4 * N) ≤ 4 * r k N

/-- A density estimate at the doubly exponential sizes, with constants depending on k. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ C p : ℝ, 0 < C ∧ 1 < p ∧ ∀ᶠ m : ℕ in atTop,
    (r k (4 ^ (2 ^ m)) : ℝ) / (4 : ℝ) ^ (2 ^ m : ℕ) ≤
      (C * ((m : ℝ) ^ p)⁻¹) / (2 : ℝ) ^ m

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2.H3 := by
  intro h1 h2 k hk
  let d (j : ℕ) : ℝ := (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j
  have hd (j : ℕ) : 0 ≤ d j := by dsimp [d]; positivity
  have hmono : Antitone d := by
    apply antitone_nat_of_succ_le
    intro j
    have hcard : (r k (4 * 4 ^ j) : ℝ) ≤ 4 * (r k (4 ^ j) : ℝ) := by
      exact_mod_cast h1 k hk (4 ^ j)
    dsimp [d]
    rw [pow_succ' (4 : ℕ), pow_succ' (4 : ℝ)]
    calc
      _ ≤ (4 * (r k (4 ^ j) : ℝ)) / (4 * (4 : ℝ) ^ j) := by gcongr
      _ = _ := by field_simp
  obtain ⟨C, p, _, hp, hs⟩ := h2 k hk
  have hseries : Summable (fun m : ℕ ↦ C * ((m : ℝ) ^ p)⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr hp).mul_left C
  change Summable d
  apply (summable_condensed_iff_of_nonneg hd (fun ⦃_ _⦄ _ h ↦ hmono h)).mp
  refine Summable.of_norm_bounded_eventually_nat hseries ?_
  filter_upwards [hs] with m hm
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hd _)), mul_comm]
  exact (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ m)).mp hm

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3
