import OMAStatements.S_mo_427161
import Mathlib

-- Problem: mo-427161, is every discrete compound Poisson distribution a mixed Poisson
-- distribution (with a rate density on [0, infinity))?
-- Retains the counterexample and measure argument by @ivillar (PR #26551).
-- Uses finite antidiagonal evaluation and the standard exponential maximum bound.
--
-- No. Take rate 1 and jumps always equal to 2. The compound sum is then even, so its mass at
-- k = 1 is 0. For a mixed Poisson law with density rho the mass at 1 is the integral of
-- e^{-x} x rho(x) over [0, infinity); if it vanishes, rho = 0 almost everywhere on
-- (0, infinity), contradicting that rho integrates to 1.

open MeasureTheory

namespace MO427161

open OMA.S_mo_427161

noncomputable def q : ℕ → ℝ := fun j => if j = 2 then 1 else 0

theorem q_nonneg : ∀ j, 0 ≤ q j := by
  intro j
  unfold q
  split_ifs <;> norm_num

theorem q_sum : HasSum q 1 := hasSum_ite_eq 2 (1 : ℝ)

theorem conv_zero (n : ℕ) : convPow q n 1 = 0 := by
  cases n <;> simp [convPow, q, Finset.Nat.antidiagonal_succ]

theorem compound_zero : compoundPMF 1 q 1 = 0 := by
  unfold compoundPMF
  simp [conv_zero]

theorem exp_bound (x : ℝ) (_hx : 0 < x) : Real.exp (-x) * x ≤ 1 := by
  simpa only [mul_comm] using
    (Real.mul_exp_neg_le_exp_neg_one x).trans (Real.exp_le_one_iff.mpr (by norm_num))

end MO427161

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_427161.main) := by
  intro h
  obtain ⟨ρ, ⟨hρ, hnn, hint, h1⟩, hk⟩ := h 1 one_pos MO427161.q MO427161.q_nonneg MO427161.q_sum
  have hk1 := hk 1
  rw [MO427161.compound_zero] at hk1
  have hI : ∫ x in Set.Ici (0 : ℝ), Real.exp (-x) * x * ρ x = 0 := by
    simpa [OMA.S_mo_427161.mixedPMF] using hk1
  rw [integral_Ici_eq_integral_Ioi] at hI h1
  have hint' : Integrable ρ (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hint.mono_set Set.Ioi_subset_Ici_self
  have hmeas : Measurable (fun x : ℝ => Real.exp (-x) * x * ρ x) :=
    ((Real.measurable_exp.comp measurable_neg).mul measurable_id).mul hρ
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Real.exp (-x) * x * ρ x‖ ≤ ρ x := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx0 : 0 < x := hx
    have hρx : 0 ≤ ρ x := hnn x hx0.le
    have h0 : 0 ≤ Real.exp (-x) * x := mul_nonneg (Real.exp_pos _).le hx0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hρx)]
    have h2 := mul_le_mul_of_nonneg_right (MO427161.exp_bound x hx0) hρx
    linarith
  have hgint : Integrable (fun x : ℝ => Real.exp (-x) * x * ρ x)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.mono' hint' hmeas.aestronglyMeasurable hbound
  have hgnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun x : ℝ => Real.exp (-x) * x * ρ x) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx0 : 0 < x := hx
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hx0.le) (hnn x hx0.le)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hgnn hgint).mp hI
  have hρ0 : ρ =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] 0 := by
    filter_upwards [hzero, ae_restrict_mem measurableSet_Ioi] with x hx hmem
    have hx0 : 0 < x := hmem
    have hx' : Real.exp (-x) * x * ρ x = 0 := hx
    exact (mul_eq_zero.mp hx').resolve_left (mul_pos (Real.exp_pos _) hx0).ne'
  rw [integral_congr_ae hρ0] at h1
  simp at h1
