import FormalConjectures.ErdosProblems.«287»
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- Credit: @Alewawa

/-!
The circle method separates the expected positive contribution near rationals of small
denominator from a one-sided bound on the complementary integral. Fourier orthogonality
identifies the complete integral with the log-weighted count of prime pairs p + 1 = 2q.
-/

open Filter MeasureTheory
open scoped BigOperators Interval

namespace OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1

private theorem integral_cos_int (k : ℤ) :
    (∫ θ in (0 : ℝ)..1, Real.cos (2 * Real.pi * (k : ℝ) * θ)) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hcoef : 2 * Real.pi * (k : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left Real.cos hcoef, integral_cos]
  rw [mul_one, mul_zero, Real.sin_zero, sub_zero, if_neg hk]
  have hsin : Real.sin (2 * Real.pi * (k : ℝ)) = 0 := by
    convert Real.sin_int_mul_pi (2 * k) using 2
    push_cast
    ring
  rw [hsin, smul_zero]

/-- Orthogonality leaves exactly the pairs that satisfy the affine linear equation. -/
private theorem orthogonality (N : ℕ) :
    (∫ θ in (0 : ℝ)..1,
      ∑ p ∈ (Finset.Icc N (2 * N)).filter Nat.Prime,
        ∑ q ∈ (Finset.Icc 1 N).filter Nat.Prime,
          Real.log p * Real.log q * Real.cos (2 * Real.pi * ((p : ℝ) + 1 - 2 * q) * θ)) =
      ∑ p ∈ (Finset.Icc N (2 * N)).filter Nat.Prime,
        ∑ q ∈ (Finset.Icc 1 N).filter Nat.Prime,
          if p + 1 = 2 * q then Real.log p * Real.log q else 0 := by
  classical
  rw [intervalIntegral.integral_finsetSum (fun p _ => by
    apply Continuous.intervalIntegrable
    fun_prop)]
  apply Finset.sum_congr rfl
  intro p _
  rw [intervalIntegral.integral_finsetSum (fun q _ => by
    apply Continuous.intervalIntegrable
    fun_prop)]
  apply Finset.sum_congr rfl
  intro q _
  rw [intervalIntegral.integral_const_mul]
  have hcast : ((p : ℝ) + 1 - 2 * q) = (((p : ℤ) + 1 - 2 * q : ℤ) : ℝ) := by
    push_cast
    rfl
  have heq : ((p : ℤ) + 1 - 2 * q = 0) ↔ p + 1 = 2 * q := by omega
  rw [hcast, integral_cos_int]
  simp only [heq]
  split <;> simp

/-- Positive contribution of the major arcs around reduced fractions of denominator at most
log(N)^2. Their width on each side is log(N)^2/N. The classical major-arc calculation
using Siegel–Walfisz gives a main term of C₂ N, where C₂ is the twin-prime constant. -/
def H1 : Prop :=
  let F (N : ℕ) (θ : ℝ) :=
    ∑ p ∈ (Finset.Icc N (2 * N)).filter Nat.Prime,
      ∑ q ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log p * Real.log q * Real.cos (2 * Real.pi * ((p : ℝ) + 1 - 2 * q) * θ)
  let A (N : ℕ) : Set ℝ :=
    Set.Icc 0 1 ∩ ⋃ b : ℕ, ⋃ a : ℕ,
      ⋃ (_ : 0 < b ∧ (b : ℝ) ≤ Real.log N ^ 2 ∧ a ≤ b ∧ Nat.Coprime a b),
        Set.Icc ((a : ℝ) / b - Real.log N ^ 2 / N) ((a : ℝ) / b + Real.log N ^ 2 / N)
  ∀ᶠ N : ℕ in atTop, (N : ℝ) / 2 ≤ ∫ θ in A N, F N θ

/-- The minor arcs cannot cancel the positive major-arc contribution. -/
def H2 : Prop :=
  let F (N : ℕ) (θ : ℝ) :=
    ∑ p ∈ (Finset.Icc N (2 * N)).filter Nat.Prime,
      ∑ q ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log p * Real.log q * Real.cos (2 * Real.pi * ((p : ℝ) + 1 - 2 * q) * θ)
  let A (N : ℕ) : Set ℝ :=
    Set.Icc 0 1 ∩ ⋃ b : ℕ, ⋃ a : ℕ,
      ⋃ (_ : 0 < b ∧ (b : ℝ) ≤ Real.log N ^ 2 ∧ a ≤ b ∧ Nat.Coprime a b),
        Set.Icc ((a : ℝ) / b - Real.log N ^ 2 / N) ((a : ℝ) / b + Real.log N ^ 2 / N)
  ∀ᶠ N : ℕ in atTop, -(N : ℝ) / 2 < ∫ θ in Set.Icc 0 1 \ A N, F N θ

theorem main : H1 → H2 → type_of% @Erdos287.erdos_287.variants.prime_conjecture := by
  intro hmajor hminor
  let F (N : ℕ) (θ : ℝ) :=
    ∑ p ∈ (Finset.Icc N (2 * N)).filter Nat.Prime,
      ∑ q ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log p * Real.log q * Real.cos (2 * Real.pi * ((p : ℝ) + 1 - 2 * q) * θ)
  let A (N : ℕ) : Set ℝ :=
    Set.Icc 0 1 ∩ ⋃ b : ℕ, ⋃ a : ℕ,
      ⋃ (_ : 0 < b ∧ (b : ℝ) ≤ Real.log N ^ 2 ∧ a ≤ b ∧ Nat.Coprime a b),
        Set.Icc ((a : ℝ) / b - Real.log N ^ 2 / N) ((a : ℝ) / b + Real.log N ^ 2 / N)
  change ∀ᶠ N : ℕ in atTop, (N : ℝ) / 2 ≤ ∫ θ in A N, F N θ at hmajor
  change ∀ᶠ N : ℕ in atTop, -(N : ℝ) / 2 < ∫ θ in Set.Icc 0 1 \ A N, F N θ at hminor
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hmajor.and hminor)
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hM, hm⟩ := hN₀ N hN
  have hA : MeasurableSet (A N) := by
    apply measurableSet_Icc.inter
    exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun a =>
      MeasurableSet.iUnion fun _ => measurableSet_Icc
  have hAsub : A N ⊆ Set.Icc 0 1 := Set.inter_subset_left
  have hcont : Continuous (F N) := by
    unfold F
    fun_prop
  have hint := setIntegral_sdiff (μ := volume) hA hcont.integrableOn_Icc hAsub
  have htotal : 0 < ∫ θ in (0 : ℝ)..1, F N θ := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    linarith
  by_contra! hno
  have hzero : ∫ θ in (0 : ℝ)..1, F N θ = 0 := by
    rw [show (∫ θ in (0 : ℝ)..1, F N θ) = _ from orthogonality N]
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q hq
    refine if_neg fun h => ?_
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    obtain ⟨hpN, hp2N⟩ := Finset.mem_Icc.mp hp'.1
    have hhalf : (p + 1) / 2 = q := by omega
    exact hno p hp'.2 hpN hp2N (by simpa only [hhalf] using hq'.2)
  linarith

end OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1
