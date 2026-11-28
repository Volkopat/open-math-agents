import OMAReductions.R_Erdos114_erdos_114_variants_large_n_R1

import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Reduction Erdos114.erdos_114.variants.large_n.R1.H2.R1 of step Erdos114.erdos_114.variants.large_n.R1.H2
-- Credit: @luciusacarr

namespace OMA.R_Erdos114_erdos_114_variants_large_n_R1_H2_R1

open Polynomial Erdos114 Filter

-- The total size in Tao's equation (1.6) tends uniformly to zero for normalized
-- maximizing polynomials as their degree tends to infinity.
def H1 : Prop :=
  let size (n : ℕ) (p : ℂ[X]) : ℝ :=
    (p.derivative.roots.map fun z => ‖z‖).sum + (n : ℝ) * ‖1 + p.eval 0‖ ^ (1 / (n : ℝ))
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ p : ℂ[X],
    p.Monic → p.natDegree = n → p.coeff (n - 1) = 0 →
    (p.eval 0).im = 0 → (p.eval 0).re ≤ 0 → IsConnected (lemniscate p) →
    (∀ z : ℂ, p.derivative.eval z = 0 → z ∈ lemniscate p) →
    (∀ q : ℂ[X], q.Monic → q.natDegree = n → lemniscateLength q ≤ lemniscateLength p) →
    size n p ≤ δ

-- The comparison at small total size in Section 12 forces it to vanish.
def H2 : Prop :=
  let size (n : ℕ) (p : ℂ[X]) : ℝ :=
    (p.derivative.roots.map fun z => ‖z‖).sum + (n : ℝ) * ‖1 + p.eval 0‖ ^ (1 / (n : ℝ))
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ p : ℂ[X],
    p.Monic → p.natDegree = n → p.coeff (n - 1) = 0 →
    (p.eval 0).im = 0 → (p.eval 0).re ≤ 0 → IsConnected (lemniscate p) →
    (∀ z : ℂ, p.derivative.eval z = 0 → z ∈ lemniscate p) →
    (∀ q : ℂ[X], q.Monic → q.natDegree = n → lemniscateLength q ≤ lemniscateLength p) →
    size n p ≤ δ → size n p = 0

lemma eq_standard_of_size_zero {p : ℂ[X]} {n : ℕ} (hn : 1 ≤ n) (hp : p.Monic)
    (hdeg : p.natDegree = n)
    (hsize : (p.derivative.roots.map fun z => ‖z‖).sum +
      (n : ℝ) * ‖1 + p.eval 0‖ ^ (1 / (n : ℝ)) = 0) :
    p = X ^ n - 1 := by
  have hnorms : ∀ t ∈ p.derivative.roots.map (fun z => ‖z‖), 0 ≤ t := by
    intro t ht
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp ht
    exact norm_nonneg z
  have hsum := Multiset.sum_nonneg hnorms
  have hpow : 0 ≤ (n : ℝ) * ‖1 + p.eval 0‖ ^ (1 / (n : ℝ)) := by positivity
  have hsum0 : (p.derivative.roots.map fun z => ‖z‖).sum = 0 := by linarith
  have hpow0 : (n : ℝ) * ‖1 + p.eval 0‖ ^ (1 / (n : ℝ)) = 0 := by linarith
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hvalue : p.eval 0 = -1 := by
    have h := (mul_eq_zero.mp hpow0).resolve_left hnreal
    rw [Real.rpow_eq_zero (norm_nonneg _) (div_ne_zero one_ne_zero hnreal),
      norm_eq_zero] at h
    linear_combination h
  have hs : p.derivative.Splits := IsAlgClosed.splits _
  have hall : ∀ z ∈ p.derivative.roots, z = 0 := by
    intro z hz
    exact norm_eq_zero.mp (Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hnorms hsum0 _
      (Multiset.mem_map.mpr ⟨z, hz, rfl⟩))
  have hroots := Multiset.eq_replicate_of_mem hall
  have hD : p.derivative = C (n : ℂ) * X ^ (n - 1) := by
    calc
      p.derivative = C p.derivative.leadingCoeff *
          (p.derivative.roots.map fun z => X - C z).prod := hs.eq_prod_roots
      _ = C (n : ℂ) * X ^ (n - 1) := by
        rw [hroots, Multiset.map_replicate, Multiset.prod_replicate,
          ← hs.natDegree_eq_card_roots, natDegree_derivative, leadingCoeff_derivative,
          hp.leadingCoeff, hdeg]
        simp
  have hconst : p - X ^ n = C ((p - X ^ n).coeff 0) :=
    eq_C_of_derivative_eq_zero (by rw [derivative_sub, derivative_X_pow, hD, sub_self])
  have hc : (p - X ^ n).coeff 0 = -1 := by
    rw [coeff_zero_eq_eval_zero]
    simp [hvalue, zero_pow (show n ≠ 0 by omega)]
  have heq : p - X ^ n = -(1 : ℂ[X]) := by simpa [hc] using hconst
  linear_combination heq

theorem main : H1 → H2 → OMA.R_Erdos114_erdos_114_variants_large_n_R1.H2 := by
  intro hSmall hZero
  obtain ⟨δ, hδ, hZero⟩ := hZero
  have hPositive : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  filter_upwards [hSmall δ hδ, hZero, hPositive] with n hSmallAt hZeroAt hn
  intro p hm hd hc him hre hconn hcrit hmax
  exact eq_standard_of_size_zero hn hm hd
    (hZeroAt p hm hd hc him hre hconn hcrit hmax
      (hSmallAt p hm hd hc him hre hconn hcrit hmax))

end OMA.R_Erdos114_erdos_114_variants_large_n_R1_H2_R1
