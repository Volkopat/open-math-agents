import OMAReductions.R_Erdos704_erdos_704_variants_davies_lower_R1
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Reduction of `Erdos704.erdos_704.variants.davies_lower.R1.H1` (Davies's Base-2 Polynomial Certificate)

Following Section 9 (lines 2694–2905) of J. Davies, *Measurable obstructions to the chromatic
number of Euclidean space* (2026), we reduce `OMA.R_Erdos704_erdos_704_variants_davies_lower_R1.H1`
(existence of a polynomial `P` with `P(0) = 1` and `P(s²) Ω_d(s/(2π)) ≥ -B` where
`B ≤ 2^{-d + o(d)}`) to its two classical analytic pillars:

1. (`H1`) **Bessel representation and zero-distribution asymptotic** (Davies eq. (9.1) &
   Lemma `lem:base-two-bessel`): for sufficiently large `d` (`ν = d/2 - 1`), the spherical average
   `Ω_d(s/(2π))` has `L` positive zeros `j_1, ..., j_L ∈ (ν, 2ν]` cancelling its sign changes on
   `[0, 2ν]`, satisfies `|Ω_d(s/(2π))| ≤ Γ(ν + 1) (2/s)^ν` for `s > 0`, and has limiting zero
   distribution `(1/ν) ∑ f(ν² / j_ℓ²) → ∫_{1/4}^1 f(t) √(1-t)/(2π t^{3/2}) dt`.
2. (`H2`) **Logarithmic potential of the averaged arcsine measure** (Davies eqs.
   `eq:base-two-arcsine`–`eq:base-two-constant-potential`): there exists a finite Borel measure `μ`
   supported on `[0, 1]` of total mass `1/2`, agreeing with `√(1-t)/(2π t^{3/2}) dt` on `[1/4, 1]`,
   having continuous strictly increasing CDF on `[0, 1/4]` with slope `≥ 1/(2π)`, and satisfying
   `∫ max(log |y - t|, -M) dμ ≤ 1 - 3 log 2 + ε` for every `y ∈ [0, 1/4]` and large `M`.

Inside `main`, we prove all remaining steps of Davies's Section 9 completely from scratch:
- Elementary self-contained Stirling upper bound `Γ(ν + 1) (2/ν)^ν ≤ 2 e² (ν + 1)² (2/e)^ν` for
  every integer or half-integer `ν = d/2 - 1 ≥ 2`.
- Quantile placement of the `k = ⌊ν/2⌋ - L` free roots `t_1, ..., t_k ∈ (0, 1/4)` via the
  intermediate value theorem, with explicit mesh bound `t_{i+1} - t_i ≤ 2π F(1/4)/(k+1)`.
- Weak convergence `(1/ν) ∑ f(t_i) → ∫_{[0, 1/4]} f dμ` and uniform logarithmic upper bound on
  `max_{y ∈ [0, 1/4]} |R(y)|` via compactness / finite `ε`-net and truncated logarithms
  (Davies Lemma `lem:base-two-root-placement`).
- Construction of `P(z) = ∏ (1 - z/j_ℓ²) ∏ (1 - t_i z/ν²)` with `P(0) = 1`, sign cancellation on
  `[0, 2ν]`, the `y = ν²/s²` factorization on `[2ν, ∞)`, and the final bound `c^d ≤ 1 + 1/B`.
-/

-- Reduction Erdos704.erdos_704.variants.davies_lower.R1.H1.R1 of Erdos704.erdos_704.variants.davies_lower.R1.H1
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

open Filter Finset MeasureTheory Polynomial
open scoped Topology Classical BigOperators

namespace OMA.R_Erdos704_erdos_704_variants_davies_lower_R1_H1_R1

/- ### Helper 1: Elementary Stirling upper bound for `Γ(ν + 1)` at integer and half-integer `ν` -/

private lemma factorial_le_exp_mul (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial : ℝ) ≤ Real.exp 1 * (m : ℝ) * ((m : ℝ) / Real.exp 1) ^ m := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp only [Nat.factorial_one, Nat.cast_one, pow_one, mul_one]
    have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    have : Real.exp 1 * (1 / Real.exp 1) = 1 := by field_simp [he]
    linarith
  | succ k hk ih =>
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hlog : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
      have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hk1_pos hk_pos)
      have hinv : 1 - (((k + 1 : ℕ) : ℝ) / (k : ℝ))⁻¹ = 1 / ((k + 1 : ℕ) : ℝ) := by
        push_cast; field_simp [hk_pos.ne', (by positivity : (k : ℝ) + 1 ≠ 0)]; ring
      rw [hinv] at h1
      have hmul := mul_le_mul_of_nonneg_left h1 hk1_pos.le
      rwa [mul_one_div_cancel hk1_pos.ne'] at hmul
    have hexp_le : Real.exp 1 ≤ (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ (k + 1) := by
      calc Real.exp 1 ≤ Real.exp (((k + 1 : ℕ) : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ))) :=
            Real.exp_le_exp.mpr hlog
        _ = ((((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ ((k + 1 : ℕ) : ℝ)) := by
            rw [Real.rpow_def_of_pos (div_pos hk1_pos hk_pos), mul_comm]
        _ = (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ (k + 1) := Real.rpow_natCast _ _
    have hstep : (k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k ≤
        (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by
      have h1 : Real.exp 1 * (k : ℝ) ^ (k + 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by
        rw [div_pow, le_div_iff₀ (pow_pos hk_pos _)] at hexp_le
        exact hexp_le
      rw [div_pow, div_pow, le_div_iff₀ (pow_pos he_pos _)]
      have h2 : (k : ℝ) * ((k : ℝ) ^ k / Real.exp 1 ^ k) * Real.exp 1 ^ (k + 1) =
          Real.exp 1 * (k : ℝ) ^ (k + 1) := by
        rw [pow_succ (Real.exp 1), pow_succ (k : ℝ)]
        field_simp [(pow_pos he_pos k).ne']
      linarith
    calc ((k + 1).factorial : ℝ)
        = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul]
      _ ≤ ((k + 1 : ℕ) : ℝ) * (Real.exp 1 * (k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k) :=
            mul_le_mul_of_nonneg_left ih hk1_pos.le
      _ = Real.exp 1 * ((k + 1 : ℕ) : ℝ) * ((k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k) := by ring
      _ ≤ Real.exp 1 * ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)

private lemma gamma_nat_add_half_le (m : ℕ) :
    Real.Gamma ((m : ℝ) + 1 / 2) ≤ 2 * (m.factorial : ℝ) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one, mul_one,
      Real.Gamma_one_half_eq]
    have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
    calc Real.sqrt Real.pi ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hpi
      _ = 2 := by norm_num
  | succ k ih =>
    have hpos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
    have hrec : Real.Gamma (((k + 1 : ℕ) : ℝ) + 1 / 2) =
        ((k : ℝ) + 1 / 2) * Real.Gamma ((k : ℝ) + 1 / 2) := by
      have : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
      rw [this, Real.Gamma_add_one hpos.ne']
    rw [hrec, Nat.factorial_succ, Nat.cast_mul]
    have hle : (k : ℝ) + 1 / 2 ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hGnn : 0 ≤ Real.Gamma ((k : ℝ) + 1 / 2) := Real.Gamma_nonneg_of_nonneg hpos.le
    calc ((k : ℝ) + 1 / 2) * Real.Gamma ((k : ℝ) + 1 / 2)
        ≤ ((k + 1 : ℕ) : ℝ) * Real.Gamma ((k : ℝ) + 1 / 2) := mul_le_mul_of_nonneg_right hle hGnn
      _ ≤ ((k + 1 : ℕ) : ℝ) * (2 * (k.factorial : ℝ)) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = 2 * (((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ)) := by ring

private lemma gamma_prefactor_le (d : ℕ) (hd : 6 ≤ d) :
    let ν : ℝ := (d : ℝ) / 2 - 1
    Real.Gamma (ν + 1) * (2 / ν) ^ ν ≤
      2 * Real.exp 2 * (ν + 1) ^ 2 * Real.exp ((Real.log 2 - 1) * ν) := by
  intro ν
  have hν_ge2 : (2 : ℝ) ≤ ν := by
    have : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    dsimp [ν]; linarith
  have hν_pos : 0 < ν := by linarith
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase_eq : (ν / Real.exp 1) ^ ν * (2 / ν) ^ ν = Real.exp ((Real.log 2 - 1) * ν) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have hmul : ν / Real.exp 1 * (2 / ν) = 2 / Real.exp 1 := by field_simp [hν_pos.ne', he_pos.ne']
    rw [hmul, Real.rpow_def_of_pos (by positivity), Real.log_div (by norm_num) he_pos.ne',
      Real.log_exp]
  rcases Nat.even_or_odd d with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm3 : 3 ≤ m := by omega
    have hν_nat : ν = ((m - 1 : ℕ) : ℝ) := by
      dsimp [ν]
      have : (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega)]; simp
      push_cast; linarith
    have hG_eq : Real.Gamma (ν + 1) = ((m - 1).factorial : ℝ) := by
      rw [hν_nat, Real.Gamma_nat_eq_factorial]
    have hfac := factorial_le_exp_mul (m - 1) (by omega)
    rw [← hν_nat, ← hG_eq] at hfac
    have hpow_eq : (ν / Real.exp 1) ^ (m - 1) = (ν / Real.exp 1) ^ ν := by
      rw [hν_nat, Real.rpow_natCast]
    rw [hpow_eq] at hfac
    have hstep1 : Real.Gamma (ν + 1) * (2 / ν) ^ ν ≤
        Real.exp 1 * ν * Real.exp ((Real.log 2 - 1) * ν) := by
      calc Real.Gamma (ν + 1) * (2 / ν) ^ ν
          ≤ (Real.exp 1 * ν * (ν / Real.exp 1) ^ ν) * (2 / ν) ^ ν :=
            mul_le_mul_of_nonneg_right hfac (by positivity)
        _ = Real.exp 1 * ν * ((ν / Real.exp 1) ^ ν * (2 / ν) ^ ν) := by ring
        _ = Real.exp 1 * ν * Real.exp ((Real.log 2 - 1) * ν) := by rw [hbase_eq]
    have hcoeff : Real.exp 1 * ν ≤ 2 * Real.exp 2 * (ν + 1) ^ 2 := by
      have he12 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      have h1 : ν ≤ (ν + 1) ^ 2 := by nlinarith
      nlinarith [Real.exp_pos 1, Real.exp_pos 2]
    exact hstep1.trans (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le)
  · have hm3 : 3 ≤ m := by omega
    have hν_eq : ν + 1 = (m : ℝ) + 1 / 2 := by dsimp [ν]; push_cast; ring
    have hm_eq : (m : ℝ) = ν + 1 / 2 := by linarith
    have hG_le : Real.Gamma (ν + 1) ≤ 2 * (m.factorial : ℝ) := by
      rw [hν_eq]; exact gamma_nat_add_half_le m
    have hfac := factorial_le_exp_mul m (by omega)
    have hpow_m : ((m : ℝ) / Real.exp 1) ^ m ≤
        Real.exp 1 * (ν + 1) * (ν / Real.exp 1) ^ ν := by
      have h1 : ((m : ℝ) / Real.exp 1) ^ m = ((m : ℝ) / Real.exp 1) ^ (m : ℝ) :=
        (Real.rpow_natCast _ _).symm
      rw [h1, hm_eq, Real.rpow_add (by positivity),
        show (ν + 1 / 2) / Real.exp 1 = (ν / Real.exp 1) * (1 + 1 / (2 * ν)) by
          field_simp [hν_pos.ne', he_pos.ne'],
        Real.mul_rpow (by positivity) (by positivity)]
      have hterm1 : (1 + 1 / (2 * ν)) ^ ν ≤ Real.exp 1 := by
        have hle := Real.add_one_le_exp (1 / (2 * ν))
        have h1' : 1 + 1 / (2 * ν) ≤ Real.exp (1 / (2 * ν)) := by linarith
        calc (1 + 1 / (2 * ν)) ^ ν
            ≤ (Real.exp (1 / (2 * ν))) ^ ν := Real.rpow_le_rpow (by positivity) h1' hν_pos.le
          _ = Real.exp (1 / (2 * ν) * ν) := (Real.exp_mul _ _).symm
          _ = Real.exp (1 / 2) := by congr 1; field_simp [hν_pos.ne']
          _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      have hterm2 : ((ν / Real.exp 1) * (1 + 1 / (2 * ν))) ^ ((1 : ℝ) / 2) ≤ ν + 1 := by
        have hrew : (ν / Real.exp 1) * (1 + 1 / (2 * ν)) = (ν + 1 / 2) / Real.exp 1 := by
          field_simp [hν_pos.ne', he_pos.ne']
        rw [hrew]
        have hle1 : (ν + 1 / 2) / Real.exp 1 ≤ ν + 1 := by
          have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
          calc (ν + 1 / 2) / Real.exp 1 ≤ (ν + 1 / 2) / 1 :=
                div_le_div_of_nonneg_left (by positivity) zero_lt_one he1
            _ ≤ ν + 1 := by linarith
        have hle2 : (ν + 1) ^ ((1 : ℝ) / 2) ≤ ν + 1 := by
          calc (ν + 1) ^ ((1 : ℝ) / 2) ≤ (ν + 1) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ = ν + 1 := Real.rpow_one _
        exact (Real.rpow_le_rpow (by positivity) hle1 (by norm_num)).trans hle2
      calc (ν / Real.exp 1) ^ ν * (1 + 1 / (2 * ν)) ^ ν *
              ((ν / Real.exp 1) * (1 + 1 / (2 * ν))) ^ ((1 : ℝ) / 2)
          ≤ (ν / Real.exp 1) ^ ν * Real.exp 1 * (ν + 1) := by gcongr
        _ = Real.exp 1 * (ν + 1) * (ν / Real.exp 1) ^ ν := by ring
    have he2 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
      rw [← Real.exp_add]; norm_num
    have hG_final : Real.Gamma (ν + 1) ≤ 2 * Real.exp 2 * (ν + 1) ^ 2 * (ν / Real.exp 1) ^ ν := by
      have hmr : (m : ℝ) ≤ ν + 1 := by linarith
      calc Real.Gamma (ν + 1)
          ≤ 2 * (m.factorial : ℝ) := hG_le
        _ ≤ 2 * (Real.exp 1 * (m : ℝ) * ((m : ℝ) / Real.exp 1) ^ m) := by gcongr
        _ ≤ 2 * (Real.exp 1 * (ν + 1) * (Real.exp 1 * (ν + 1) * (ν / Real.exp 1) ^ ν)) := by gcongr
        _ = 2 * (Real.exp 1 * Real.exp 1) * (ν + 1) ^ 2 * (ν / Real.exp 1) ^ ν := by ring
        _ = 2 * Real.exp 2 * (ν + 1) ^ 2 * (ν / Real.exp 1) ^ ν := by rw [he2]
    calc Real.Gamma (ν + 1) * (2 / ν) ^ ν
        ≤ (2 * Real.exp 2 * (ν + 1) ^ 2 * (ν / Real.exp 1) ^ ν) * (2 / ν) ^ ν :=
          mul_le_mul_of_nonneg_right hG_final (by positivity)
      _ = 2 * Real.exp 2 * (ν + 1) ^ 2 * ((ν / Real.exp 1) ^ ν * (2 / ν) ^ ν) := by ring
      _ = 2 * Real.exp 2 * (ν + 1) ^ 2 * Real.exp ((Real.log 2 - 1) * ν) := by rw [hbase_eq]

/- ### Helper 2: Quantile root placement on `(0, 1/4)` and Riemann–Stieltjes bound -/

private lemma quantile_root_placement (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hF_cont : ContinuousOn (fun t : ℝ => (μ (Set.Icc 0 t)).toReal) (Set.Icc 0 (1 / 4)))
    (hF_zero : (μ (Set.Icc 0 0)).toReal = 0)
    (hF_pos : 0 < (μ (Set.Icc 0 (1 / 4))).toReal)
    (hF_slope : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 / 4 →
      (b - a) / (2 * Real.pi) ≤ (μ (Set.Icc 0 b)).toReal - (μ (Set.Icc 0 a)).toReal)
    (k : ℕ) :
    ∃ t : Fin k → ℝ,
      (∀ i : Fin k, 0 < t i ∧ t i < 1 / 4) ∧
      ∀ (g : ℝ → ℝ) (B_g η_g : ℝ), ContinuousOn g (Set.Icc 0 (1 / 4)) → 0 ≤ B_g → 0 ≤ η_g →
        (∀ x ∈ Set.Icc (0 : ℝ) (1 / 4), |g x| ≤ B_g) →
        (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) (1 / 4) → y ∈ Set.Icc (0 : ℝ) (1 / 4) →
          |x - y| ≤ 2 * Real.pi * (μ (Set.Icc 0 (1 / 4))).toReal / ((k + 1 : ℕ) : ℝ) →
          |g x - g y| ≤ η_g) →
        |(μ (Set.Icc 0 (1 / 4))).toReal / ((k + 1 : ℕ) : ℝ) * (∑ i : Fin k, g (t i)) -
          ∫ x in Set.Icc (0 : ℝ) (1 / 4), g x ∂μ| ≤
          η_g * (μ (Set.Icc 0 (1 / 4))).toReal +
          B_g * ((μ (Set.Icc 0 (1 / 4))).toReal / ((k + 1 : ℕ) : ℝ)) := by
  let F : ℝ → ℝ := fun x => (μ (Set.Icc 0 x)).toReal
  let M₀ : ℝ := F (1 / 4)
  have hM₀_pos : 0 < M₀ := hF_pos
  have hF_mono : MonotoneOn F (Set.Icc 0 (1 / 4)) := by
    intro a ha b hb hab
    have := hF_slope a b ha.1 hab hb.2
    have hnn : 0 ≤ (b - a) / (2 * Real.pi) := div_nonneg (by linarith) (by positivity)
    linarith
  have hex_tau : ∀ r : ℕ, r ≤ k + 1 →
      ∃ x ∈ Set.Icc (0 : ℝ) (1 / 4), F x = (r : ℝ) / ((k + 1 : ℕ) : ℝ) * M₀ := by
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0; exact ⟨0, ⟨le_rfl, by norm_num⟩, by simp [F, hF_zero]⟩
    by_cases hrk : r = k + 1
    · subst hrk
      refine ⟨1 / 4, ⟨by norm_num, le_rfl⟩, ?_⟩
      have hne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hne]; rfl
    have hmem : (r : ℝ) / ((k + 1 : ℕ) : ℝ) * M₀ ∈ Set.Icc (F 0) (F (1 / 4)) := by
      have hF0 : F 0 = 0 := hF_zero
      rw [hF0]
      refine ⟨by positivity, ?_⟩
      have hle1 : (r : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast hr
      calc (r : ℝ) / ((k + 1 : ℕ) : ℝ) * M₀ ≤ 1 * M₀ := mul_le_mul_of_nonneg_right hle1 hM₀_pos.le
        _ = F (1 / 4) := one_mul _
    exact intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 4) hF_cont hmem
  choose τ_raw hτ_mem hτ_val using hex_tau
  let τ : Fin (k + 2) → ℝ := fun r =>
    if r.1 = 0 then 0 else if r.1 = k + 1 then 1 / 4 else τ_raw r.1 (by omega)
  have hτ_Icc : ∀ r : Fin (k + 2), τ r ∈ Set.Icc (0 : ℝ) (1 / 4) := by
    intro r; dsimp [τ]; split_ifs
    · exact ⟨le_rfl, by norm_num⟩
    · exact ⟨by norm_num, le_rfl⟩
    · exact hτ_mem r.1 (by omega)
  have hτ_F : ∀ r : Fin (k + 2), F (τ r) = (r.1 : ℝ) / ((k + 1 : ℕ) : ℝ) * M₀ := by
    intro r; dsimp [τ]; split_ifs with h0 hk1
    · rw [h0]; simp [F, hF_zero]
    · rw [hk1]; have hne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hne]; rfl
    · exact hτ_val r.1 (by omega)
  have hτ_strict : ∀ r₁ r₂ : Fin (k + 2), r₁ < r₂ → τ r₁ < τ r₂ := by
    intro r₁ r₂ hlt
    by_contra hge; push Not at hge
    have hF_le := hF_mono (hτ_Icc r₂) (hτ_Icc r₁) hge
    rw [hτ_F r₁, hτ_F r₂] at hF_le
    have hltR : (r₁.1 : ℝ) < (r₂.1 : ℝ) := by exact_mod_cast hlt
    have hdiv : (r₁.1 : ℝ) / ((k + 1 : ℕ) : ℝ) < (r₂.1 : ℝ) / ((k + 1 : ℕ) : ℝ) :=
      div_lt_div_of_pos_right hltR (by positivity)
    nlinarith
  have hτ_step : ∀ j : Fin (k + 1),
      τ j.succ - τ j.castSucc ≤ 2 * Real.pi * M₀ / ((k + 1 : ℕ) : ℝ) := by
    intro j
    have hlt : τ j.castSucc < τ j.succ := hτ_strict _ _ Fin.castSucc_lt_succ
    have h1 := hF_slope (τ j.castSucc) (τ j.succ) (hτ_Icc _).1 hlt.le (hτ_Icc _).2
    change (τ j.succ - τ j.castSucc) / (2 * Real.pi) ≤ F (τ j.succ) - F (τ j.castSucc) at h1
    rw [hτ_F j.succ, hτ_F j.castSucc] at h1
    have hdiff : ((j.succ.1 : ℝ) / ((k + 1 : ℕ) : ℝ) * M₀) -
        ((j.castSucc.1 : ℝ) / ((k + 1 : ℕ) : ℝ) * M₀) = M₀ / ((k + 1 : ℕ) : ℝ) := by
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      have hne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hne]; ring
    rw [hdiff, div_le_iff₀ (by positivity)] at h1
    linarith [show M₀ / ((k + 1 : ℕ) : ℝ) * (2 * Real.pi) = 2 * Real.pi * M₀ / ((k + 1 : ℕ) : ℝ) by ring]
  have hmeas_Ioc : ∀ j : Fin (k + 1),
      (μ (Set.Ioc (τ j.castSucc) (τ j.succ))).toReal = M₀ / ((k + 1 : ℕ) : ℝ) := by
    intro j
    have hlt : τ j.castSucc < τ j.succ := hτ_strict _ _ Fin.castSucc_lt_succ
    have hdisj : Disjoint (Set.Icc (0 : ℝ) (τ j.castSucc)) (Set.Ioc (τ j.castSucc) (τ j.succ)) :=
      Set.disjoint_left.mpr fun x h1 h2 => not_lt_of_ge h1.2 h2.1
    have hunion : Set.Icc (0 : ℝ) (τ j.castSucc) ∪ Set.Ioc (τ j.castSucc) (τ j.succ) =
        Set.Icc (0 : ℝ) (τ j.succ) :=
      Set.Icc_union_Ioc_eq_Icc (hτ_Icc _).1 hlt.le
    have hadd : μ (Set.Icc (0 : ℝ) (τ j.succ)) =
        μ (Set.Icc (0 : ℝ) (τ j.castSucc)) + μ (Set.Ioc (τ j.castSucc) (τ j.succ)) := by
      rw [← hunion, measure_union hdisj measurableSet_Ioc]
    have htoReal := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at htoReal
    have hF1 : (μ (Set.Icc (0 : ℝ) (τ j.castSucc))).toReal = F (τ j.castSucc) := rfl
    have hF2 : (μ (Set.Icc (0 : ℝ) (τ j.succ))).toReal = F (τ j.succ) := rfl
    rw [hF1, hF2, hτ_F j.castSucc, hτ_F j.succ] at htoReal
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at htoReal
    have hne : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hdiff : ((j.1 : ℝ) + 1) / ((k : ℝ) + 1) * M₀ - (j.1 : ℝ) / ((k : ℝ) + 1) * M₀ =
        M₀ / ((k : ℝ) + 1) := by field_simp [hne]; ring
    push_cast
    linarith
  let t : Fin k → ℝ := fun i => τ ⟨i.1 + 1, by omega⟩
  refine ⟨t, fun i => ?_, ?_⟩
  · have h0 : τ ⟨0, by omega⟩ = 0 := by simp [τ]
    have h1 : τ ⟨k + 1, by omega⟩ = 1 / 4 := by simp [τ]
    refine ⟨?_, ?_⟩
    · rw [← h0]; exact hτ_strict ⟨0, by omega⟩ ⟨i.1 + 1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
    · rw [← h1]; exact hτ_strict ⟨i.1 + 1, by omega⟩ ⟨k + 1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
  · intro g B_g η_g hg_cont hBg hηg hg_bd hg_osc
    have hμ0 : μ ({(0 : ℝ)}) = 0 := by
      have : Set.Icc (0 : ℝ) 0 = {0} := Set.Icc_self 0
      rw [← this]
      exact (ENNReal.toReal_eq_zero_iff _).mp hF_zero |>.resolve_right (measure_ne_top μ _)
    have hIcc_eq_Ioc : ∫ x in Set.Icc (0 : ℝ) (1 / 4), g x ∂μ =
        ∫ x in Set.Ioc (0 : ℝ) (1 / 4), g x ∂μ := by
      have hae : (Set.Icc (0 : ℝ) (1 / 4) : Set ℝ) =ᵐ[μ] Set.Ioc (0 : ℝ) (1 / 4) := by
        rw [ae_eq_set]
        refine ⟨measure_mono_null (fun x hx => ?_) hμ0, measure_mono_null (fun x hx => ?_) measure_empty⟩
        · simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc, Set.mem_singleton_iff] at hx ⊢
          by_contra hne; exact hx.2 ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hne), hx.1.2⟩
        · simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc, Set.mem_empty_iff_false] at hx ⊢
          exact hx.2 ⟨hx.1.1.le, hx.1.2⟩
      exact setIntegral_congr_set hae
    have hpart_union : (⋃ j ∈ (Finset.univ : Finset (Fin (k + 1))),
        Set.Ioc (τ j.castSucc) (τ j.succ)) = Set.Ioc (0 : ℝ) (1 / 4) := by
      have h0 : τ ⟨0, by omega⟩ = 0 := by simp [τ]
      have h1 : τ ⟨k + 1, by omega⟩ = 1 / 4 := by simp [τ]
      ext x; simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_Ioc]
      constructor
      · rintro ⟨j, hj1, hj2⟩
        exact ⟨lt_of_le_of_lt (hτ_Icc _).1 hj1, hj2.trans (hτ_Icc _).2⟩
      · rintro ⟨hx0, hx1⟩
        let S : Finset (Fin (k + 1)) := Finset.univ.filter fun j => x ≤ τ j.succ
        have hS_ne : S.Nonempty := ⟨⟨k, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          change x ≤ τ ⟨k + 1, by omega⟩; rw [h1]; exact hx1⟩⟩
        let j₀ := S.min' hS_ne
        have hj₀_mem := Finset.mem_filter.mp (Finset.min'_mem S hS_ne)
        refine ⟨j₀, ?_, hj₀_mem.2⟩
        by_cases hj0 : j₀.1 = 0
        · have : j₀.castSucc = ⟨0, by omega⟩ := Fin.ext hj0
          rw [this, h0]; exact hx0
        · let jprev : Fin (k + 1) := ⟨j₀.1 - 1, by omega⟩
          have hlt : jprev < j₀ := Fin.lt_def.mpr (by dsimp [jprev]; omega)
          have hnot : jprev ∉ S := fun hm => not_le_of_gt hlt (Finset.min'_le S jprev hm)
          have hgt : τ jprev.succ < x := by
            by_contra hle; push Not at hle
            exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
          have heq : jprev.succ = j₀.castSucc := Fin.ext (by simp [jprev]; omega)
          rwa [heq] at hgt
    have hdisj_all : ((Finset.univ : Finset (Fin (k + 1))) : Set (Fin (k + 1))).PairwiseDisjoint
        (fun j : Fin (k + 1) => Set.Ioc (τ j.castSucc) (τ j.succ)) := by
      intro j₁ _ j₂ _ hne
      wlog hlt : j₁ < j₂ generalizing j₁ j₂
      · exact (this (Finset.mem_coe.mpr (Finset.mem_univ _)) (Finset.mem_coe.mpr (Finset.mem_univ _)) hne.symm
          (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)).symm
      refine Set.disjoint_left.mpr fun x h1 h2 => ?_
      have hle : τ j₁.succ ≤ τ j₂.castSucc := by
        rcases eq_or_lt_of_le (show j₁.succ ≤ j₂.castSucc by simp [Fin.le_def]; omega) with heq | hlt'
        · rw [heq]
        · exact (hτ_strict _ _ hlt').le
      linarith [h1.2, h2.1]
    have hg_int_Icc : IntegrableOn g (Set.Icc (0 : ℝ) (1 / 4)) μ :=
      hg_cont.integrableOn_compact isCompact_Icc
    have hg_int : ∀ j ∈ (Finset.univ : Finset (Fin (k + 1))),
        IntegrableOn g (Set.Ioc (τ j.castSucc) (τ j.succ)) μ := fun j _ =>
      hg_int_Icc.mono_set fun x hx => ⟨(hτ_Icc _).1.trans hx.1.le, hx.2.trans (hτ_Icc _).2⟩
    have hsum_int : ∫ x in Set.Icc (0 : ℝ) (1 / 4), g x ∂μ =
        ∑ j : Fin (k + 1), ∫ x in Set.Ioc (τ j.castSucc) (τ j.succ), g x ∂μ := by
      rw [hIcc_eq_Ioc, ← hpart_union]
      exact integral_biUnion_finset Finset.univ (fun _ _ => measurableSet_Ioc) hdisj_all hg_int
    rw [hsum_int, Fin.sum_univ_castSucc, Finset.mul_sum]
    have hdiff_eq : (∑ i : Fin k, M₀ / ((k + 1 : ℕ) : ℝ) * g (t i)) -
        ((∑ i : Fin k, ∫ x in Set.Ioc (τ i.castSucc.castSucc) (τ i.castSucc.succ), g x ∂μ) +
          ∫ x in Set.Ioc (τ (Fin.last k).castSucc) (τ (Fin.last k).succ), g x ∂μ) =
        (∑ i : Fin k, (M₀ / ((k + 1 : ℕ) : ℝ) * g (t i) -
          ∫ x in Set.Ioc (τ i.castSucc.castSucc) (τ i.castSucc.succ), g x ∂μ)) -
        ∫ x in Set.Ioc (τ (Fin.last k).castSucc) (τ (Fin.last k).succ), g x ∂μ := by
      rw [Finset.sum_sub_distrib]; ring
    rw [hdiff_eq]
    have hterm_bd : ∀ i : Fin k,
        |M₀ / ((k + 1 : ℕ) : ℝ) * g (t i) -
          ∫ x in Set.Ioc (τ i.castSucc.castSucc) (τ i.castSucc.succ), g x ∂μ| ≤
        η_g * (M₀ / ((k + 1 : ℕ) : ℝ)) := by
      intro i
      let s := Set.Ioc (τ i.castSucc.castSucc) (τ i.castSucc.succ)
      have hti : τ i.castSucc.succ = t i := rfl
      have hconst : M₀ / ((k + 1 : ℕ) : ℝ) * g (t i) = ∫ _x in s, g (t i) ∂μ := by
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, hmeas_Ioc i.castSucc]
      have hconst_int : IntegrableOn (fun _x : ℝ => g (t i)) s μ := integrableOn_const (measure_ne_top μ s)
      rw [hconst, ← integral_sub hconst_int (hg_int i.castSucc (Finset.mem_univ _))]
      calc |∫ x in s, (g (t i) - g x) ∂μ|
          ≤ ∫ x in s, |g (t i) - g x| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ _x in s, η_g ∂μ := by
            refine setIntegral_mono_on (hconst_int.sub
                (hg_int i.castSucc (Finset.mem_univ _))).abs
              (integrableOn_const (measure_ne_top μ s)) measurableSet_Ioc fun x hx => ?_
            have hx_Icc : x ∈ Set.Icc (0 : ℝ) (1 / 4) :=
              ⟨(hτ_Icc _).1.trans hx.1.le, hx.2.trans (hτ_Icc _).2⟩
            have ht_Icc : t i ∈ Set.Icc (0 : ℝ) (1 / 4) := hτ_Icc _
            have hdist : |t i - x| ≤ 2 * Real.pi * M₀ / ((k + 1 : ℕ) : ℝ) := by
              rw [← hti, abs_of_nonneg (by linarith [hx.2])]
              linarith [hx.1, hτ_step i.castSucc]
            exact hg_osc (t i) x ht_Icc hx_Icc hdist
        _ = η_g * (M₀ / ((k + 1 : ℕ) : ℝ)) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def, hmeas_Ioc i.castSucc, mul_comm]
    have hlast_bd : |∫ x in Set.Ioc (τ (Fin.last k).castSucc) (τ (Fin.last k).succ), g x ∂μ| ≤
        B_g * (M₀ / ((k + 1 : ℕ) : ℝ)) := by
      let s := Set.Ioc (τ (Fin.last k).castSucc) (τ (Fin.last k).succ)
      calc |∫ x in s, g x ∂μ|
          ≤ ∫ x in s, |g x| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ _x in s, B_g ∂μ := by
            refine setIntegral_mono_on (hg_int (Fin.last k) (Finset.mem_univ _)).abs
              (integrableOn_const (measure_ne_top μ s)) measurableSet_Ioc fun x hx =>
              hg_bd x ⟨(hτ_Icc _).1.trans hx.1.le, hx.2.trans (hτ_Icc _).2⟩
        _ = B_g * (M₀ / ((k + 1 : ℕ) : ℝ)) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def, hmeas_Ioc (Fin.last k), mul_comm]
    have hsum_bd : |∑ i : Fin k, (M₀ / ((k + 1 : ℕ) : ℝ) * g (t i) -
          ∫ x in Set.Ioc (τ i.castSucc.castSucc) (τ i.castSucc.succ), g x ∂μ)| ≤
        η_g * M₀ := by
      calc |∑ i : Fin k, _|
          ≤ ∑ i : Fin k, |M₀ / ((k + 1 : ℕ) : ℝ) * g (t i) -
              ∫ x in Set.Ioc (τ i.castSucc.castSucc) (τ i.castSucc.succ), g x ∂μ| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin k, (η_g * (M₀ / ((k + 1 : ℕ) : ℝ))) := Finset.sum_le_sum fun i _ => hterm_bd i
        _ = (k : ℝ) / ((k + 1 : ℕ) : ℝ) * (η_g * M₀) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ 1 * (η_g * M₀) := by
            gcongr; rw [div_le_one (by positivity)]; exact_mod_cast Nat.le_succ k
        _ = η_g * M₀ := one_mul _
    calc |(∑ i : Fin k, _) - ∫ x in Set.Ioc (τ (Fin.last k).castSucc) (τ (Fin.last k).succ), g x ∂μ|
        ≤ |∑ i : Fin k, _| + |∫ x in Set.Ioc (τ (Fin.last k).castSucc) (τ (Fin.last k).succ), g x ∂μ| :=
          abs_sub _ _
      _ ≤ η_g * M₀ + B_g * (M₀ / ((k + 1 : ℕ) : ℝ)) := add_le_add hsum_bd hlast_bd

/- ### Helper 3: Exponential domination and polynomial certificate assembly -/

private lemma exp_domination_eventually {c ε : ℝ} (hc_pos : 0 < c)
    (hgap : 0 < Real.log 2 - Real.log c - 2 * ε) :
    ∀ᶠ d : ℕ in atTop,
      let ν : ℝ := (d : ℝ) / 2 - 1
      2 * Real.exp 2 * (ν + 1) ^ 2 * Real.exp ((-2 * Real.log 2 + 4 * ε) * ν) ≤ (c ^ d)⁻¹ := by
  let a : ℝ := Real.log 2 - Real.log c - 2 * ε
  have ha_pos : 0 < a := hgap
  have hpoly_zero : Tendsto (fun d : ℕ =>
      2 * Real.exp 2 * ((d : ℝ) / 2) ^ 2 * Real.exp (2 * Real.log 2 - 4 * ε) *
        Real.exp (-(a * (d : ℝ)))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have hdom : Tendsto (fun x : ℝ => (27 / a ^ 3) / x) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      refine squeeze_zero' (eventually_atTop.mpr ⟨1, fun x _ => by positivity⟩) ?_ hdom
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx_pos : 0 < x := by linarith
      have hexp_lb : (a * x / 3) ^ 3 ≤ Real.exp (a * x) := by
        have h1 : a * x / 3 ≤ Real.exp (a * x / 3) := by linarith [Real.add_one_le_exp (a * x / 3)]
        calc (a * x / 3) ^ 3 ≤ (Real.exp (a * x / 3)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) h1 3
          _ = Real.exp ((3 : ℕ) * (a * x / 3)) := (Real.exp_nat_mul _ 3).symm
          _ = Real.exp (a * x) := by congr 1; push_cast; ring
      rw [Real.exp_neg, ← div_eq_mul_inv]
      rw [div_le_div_iff₀ (Real.exp_pos _) hx_pos]
      have hmul : (27 / a ^ 3) * (a * x / 3) ^ 3 = x ^ 3 := by field_simp [ha_pos.ne']; ring
      have hle : x ^ 3 ≤ (27 / a ^ 3) * Real.exp (a * x) := by
        rw [← hmul]
        exact mul_le_mul_of_nonneg_left hexp_lb (by positivity)
      nlinarith
    have hcomp := hbase.comp tendsto_natCast_atTop_atTop
    have hmul := hcomp.const_mul (2 * Real.exp 2 * (1 / 4) * Real.exp (2 * Real.log 2 - 4 * ε))
    rw [mul_zero] at hmul
    refine hmul.congr fun d => ?_
    simp only [Function.comp_apply]
    ring_nf
  filter_upwards [hpoly_zero.eventually (Iio_mem_nhds zero_lt_one)] with d hd
  have hc_pow : (c ^ d)⁻¹ = Real.exp (-(Real.log c * (d : ℝ))) := by
    rw [Real.exp_neg, Real.exp_mul, Real.exp_log hc_pos, Real.rpow_natCast]
  rw [hc_pow]
  have hprod_eq : 2 * Real.exp 2 * ((d : ℝ) / 2 - 1 + 1) ^ 2 *
      Real.exp ((-2 * Real.log 2 + 4 * ε) * ((d : ℝ) / 2 - 1)) * Real.exp (Real.log c * (d : ℝ)) =
      2 * Real.exp 2 * ((d : ℝ) / 2) ^ 2 * Real.exp (2 * Real.log 2 - 4 * ε) *
        Real.exp (-(a * (d : ℝ))) := by
    have h1 : (d : ℝ) / 2 - 1 + 1 = (d : ℝ) / 2 := by ring
    rw [h1]
    have h2 : Real.exp ((-2 * Real.log 2 + 4 * ε) * ((d : ℝ) / 2 - 1)) * Real.exp (Real.log c * (d : ℝ)) =
        Real.exp (2 * Real.log 2 - 4 * ε) * Real.exp (-(a * (d : ℝ))) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [a]; ring
    calc 2 * Real.exp 2 * ((d : ℝ) / 2) ^ 2 *
            Real.exp ((-2 * Real.log 2 + 4 * ε) * ((d : ℝ) / 2 - 1)) * Real.exp (Real.log c * (d : ℝ))
        = 2 * Real.exp 2 * ((d : ℝ) / 2) ^ 2 *
            (Real.exp ((-2 * Real.log 2 + 4 * ε) * ((d : ℝ) / 2 - 1)) * Real.exp (Real.log c * (d : ℝ))) := by ring
      _ = _ := by rw [h2]; ring
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
  linarith [hprod_eq, hd]

private lemma polynomial_certificate_step {d Ld kd : ℕ} {c ε : ℝ}
    (hd6 : 6 ≤ d) (hc_pos : 0 < c)
    (hm_eq : Ld + kd = Nat.floor (((d : ℝ) / 2 - 1) / 2))
    (hexp : 2 * Real.exp 2 * (((d : ℝ) / 2 - 1) + 1) ^ 2 *
      Real.exp ((-2 * Real.log 2 + 4 * ε) * ((d : ℝ) / 2 - 1)) ≤ (c ^ d)⁻¹)
    (jd : Fin Ld → ℝ) (td : Fin kd → ℝ)
    (hj_range : ∀ ℓ : Fin Ld, (d : ℝ) / 2 - 1 < jd ℓ ∧ jd ℓ ≤ 2 * ((d : ℝ) / 2 - 1))
    (ht_mem : ∀ i : Fin kd, 0 < td i ∧ td i < 1 / 4)
    (hj_sign : ∀ s ∈ Set.Icc (0 : ℝ) (2 * ((d : ℝ) / 2 - 1)),
      0 ≤ (∏ ℓ : Fin Ld, (1 - s ^ 2 / (jd ℓ) ^ 2)) *
        ((∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * (s / (2 * Real.pi)) * u) *
            (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
          (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))))
    (hΩ_bd : ∀ s : ℝ, 0 < s →
      |(∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * (s / (2 * Real.pi)) * u) *
          (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
        (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))| ≤
        Real.Gamma (((d : ℝ) / 2 - 1) + 1) * (2 / s) ^ ((d : ℝ) / 2 - 1))
    (hR_bd : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 4),
      |(∏ ℓ : Fin Ld, (y - ((d : ℝ) / 2 - 1) ^ 2 / (jd ℓ) ^ 2)) * (∏ i : Fin kd, (y - td i))| ≤
      Real.exp ((1 - 3 * Real.log 2 + 4 * ε) * ((d : ℝ) / 2 - 1))) :
    ∃ (P : Polynomial ℝ) (B : ℝ),
      P.eval 0 = 1 ∧ 0 < B ∧ c ^ d ≤ 1 + 1 / B ∧
      ∀ s : ℝ, 0 ≤ s →
        -B ≤ P.eval (s ^ 2) *
          ((∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * (s / (2 * Real.pi)) * u) *
              (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
            (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))) := by
  let ν : ℝ := (d : ℝ) / 2 - 1
  have hν_ge2 : (2 : ℝ) ≤ ν := by
    have h6 : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd6
    dsimp [ν]; linarith
  have hν_pos : 0 < ν := by linarith
  let m : ℕ := Nat.floor (ν / 2)
  have hm_le : (m : ℝ) ≤ ν / 2 := Nat.floor_le (by linarith)
  let P : Polynomial ℝ :=
    (∏ ℓ : Fin Ld, (1 - Polynomial.C (((jd ℓ) ^ 2)⁻¹) * Polynomial.X)) *
    (∏ i : Fin kd, (1 - Polynomial.C (td i / ν ^ 2) * Polynomial.X))
  let B : ℝ := 2 * Real.exp 2 * (ν + 1) ^ 2 * Real.exp ((-2 * Real.log 2 + 4 * ε) * ν)
  have hB_pos : 0 < B := by dsimp [B]; positivity
  refine ⟨P, B, ?_, hB_pos, ?_, ?_⟩
  · simp [P, Polynomial.eval_prod]
  · have hexp' : B * c ^ d ≤ 1 := by
      have h1 : B ≤ 1 / c ^ d := by simpa [one_div, B, ν] using hexp
      exact (le_div_iff₀ (pow_pos hc_pos d)).mp h1
    have hinv : c ^ d ≤ 1 / B := (le_div_iff₀ hB_pos).mpr (by linarith)
    linarith
  · intro s hs
    have hPeval : P.eval (s ^ 2) =
        (∏ ℓ : Fin Ld, (1 - s ^ 2 / (jd ℓ) ^ 2)) *
        (∏ i : Fin kd, (1 - td i * s ^ 2 / ν ^ 2)) := by
      simp only [P, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X]
      congr 1
      · refine Finset.prod_congr rfl fun ℓ _ => by ring
      · refine Finset.prod_congr rfl fun i _ => by ring
    rw [hPeval]
    by_cases hs2 : s ≤ 2 * ν
    · have hfree_nn : 0 ≤ ∏ i : Fin kd, (1 - td i * s ^ 2 / ν ^ 2) := by
        refine Finset.prod_nonneg fun i _ => ?_
        have hti_le : td i ≤ 1 / 4 := (ht_mem i).2.le
        have hs_sq : s ^ 2 ≤ 4 * ν ^ 2 := by nlinarith
        have hmul : td i * s ^ 2 ≤ ν ^ 2 := by nlinarith [(ht_mem i).1]
        have hdiv : td i * s ^ 2 / ν ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hmul
        linarith
      have hsign := hj_sign s ⟨hs, hs2⟩
      have hprod_nn : 0 ≤ (∏ ℓ : Fin Ld, (1 - s ^ 2 / (jd ℓ) ^ 2)) *
          (∏ i : Fin kd, (1 - td i * s ^ 2 / ν ^ 2)) *
          ((∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * (s / (2 * Real.pi)) * u) *
              (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
            (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))) := by
        have hrew : (∏ ℓ : Fin Ld, (1 - s ^ 2 / (jd ℓ) ^ 2)) *
            (∏ i : Fin kd, (1 - td i * s ^ 2 / ν ^ 2)) *
            ((∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * (s / (2 * Real.pi)) * u) *
                (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
              (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))) =
            (∏ i : Fin kd, (1 - td i * s ^ 2 / ν ^ 2)) *
            ((∏ ℓ : Fin Ld, (1 - s ^ 2 / (jd ℓ) ^ 2)) *
              ((∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * (s / (2 * Real.pi)) * u) *
                  (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
                (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)))) := by ring
        rw [hrew]
        exact mul_nonneg hfree_nn hsign
      linarith
    · push Not at hs2
      have hs_pos : 0 < s := by linarith
      let y : ℝ := ν ^ 2 / s ^ 2
      have hy_pos : 0 < y := by dsimp [y]; positivity
      have hy_le : y ≤ 1 / 4 := by
        dsimp [y]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have hP_y : (∏ ℓ : Fin Ld, (1 - s ^ 2 / (jd ℓ) ^ 2)) *
          (∏ i : Fin kd, (1 - td i * s ^ 2 / ν ^ 2)) =
          y⁻¹ ^ m * ((∏ ℓ : Fin Ld, (y - ν ^ 2 / (jd ℓ) ^ 2)) *
            (∏ i : Fin kd, (y - td i))) := by
        have h1 : ∏ ℓ : Fin Ld, (1 - s ^ 2 / (jd ℓ) ^ 2) =
            y⁻¹ ^ Ld * ∏ ℓ : Fin Ld, (y - ν ^ 2 / (jd ℓ) ^ 2) := by
          calc ∏ ℓ : Fin Ld, (1 - s ^ 2 / (jd ℓ) ^ 2)
              = ∏ ℓ : Fin Ld, (y⁻¹ * (y - ν ^ 2 / (jd ℓ) ^ 2)) := by
                refine Finset.prod_congr rfl fun ℓ _ => ?_
                dsimp [y]
                have hjne : jd ℓ ≠ 0 := by dsimp [ν] at hν_pos; linarith [(hj_range ℓ).1]
                field_simp [hν_pos.ne', hs_pos.ne', hjne]
            _ = (∏ _ℓ : Fin Ld, y⁻¹) * ∏ ℓ : Fin Ld, (y - ν ^ 2 / (jd ℓ) ^ 2) := Finset.prod_mul_distrib
            _ = y⁻¹ ^ Ld * ∏ ℓ : Fin Ld, (y - ν ^ 2 / (jd ℓ) ^ 2) := by simp
        have h2 : ∏ i : Fin kd, (1 - td i * s ^ 2 / ν ^ 2) =
            y⁻¹ ^ kd * ∏ i : Fin kd, (y - td i) := by
          calc ∏ i : Fin kd, (1 - td i * s ^ 2 / ν ^ 2)
              = ∏ i : Fin kd, (y⁻¹ * (y - td i)) := by
                refine Finset.prod_congr rfl fun i _ => ?_
                dsimp [y]; field_simp [hν_pos.ne', hs_pos.ne']
            _ = (∏ _i : Fin kd, y⁻¹) * ∏ i : Fin kd, (y - td i) := Finset.prod_mul_distrib
            _ = y⁻¹ ^ kd * ∏ i : Fin kd, (y - td i) := by simp
        change Ld + kd = m at hm_eq
        rw [h1, h2, ← hm_eq, pow_add]; ring
      have h2s_eq : (2 / s) ^ ν = (2 / ν) ^ ν * y ^ (ν / 2) := by
        have hy_rpow : y ^ (ν / 2) = (ν / s) ^ ν := by
          dsimp [y]
          rw [← div_pow, ← Real.rpow_natCast (ν / s) 2, ← Real.rpow_mul (by positivity)]
          congr 1; push_cast; ring
        rw [hy_rpow, ← Real.mul_rpow (by positivity) (by positivity)]
        congr 1; field_simp [hν_pos.ne', hs_pos.ne']
      have hy_pow_le : y⁻¹ ^ m * y ^ (ν / 2) ≤ 1 := by
        rw [← Real.rpow_natCast y⁻¹ m, Real.inv_rpow hy_pos.le, ← Real.rpow_neg hy_pos.le,
          ← Real.rpow_add hy_pos]
        have hexp_nn : 0 ≤ -(m : ℝ) + ν / 2 := by linarith
        exact Real.rpow_le_one hy_pos.le (by linarith) hexp_nn
      have hpre := gamma_prefactor_le d hd6
      have hR := hR_bd y ⟨hy_pos.le, hy_le⟩
      have habs_le : |(∏ ℓ : Fin Ld, (1 - s ^ 2 / (jd ℓ) ^ 2)) *
          (∏ i : Fin kd, (1 - td i * s ^ 2 / ν ^ 2)) *
          ((∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * (s / (2 * Real.pi)) * u) *
              (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
            (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)))| ≤ B := by
        rw [abs_mul, hP_y, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hy_pos) m)]
        calc y⁻¹ ^ m * |(∏ ℓ : Fin Ld, (y - ν ^ 2 / (jd ℓ) ^ 2)) * (∏ i : Fin kd, (y - td i))| *
              |(∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * (s / (2 * Real.pi)) * u) *
                  (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
                (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))|
            ≤ y⁻¹ ^ m * |(∏ ℓ : Fin Ld, (y - ν ^ 2 / (jd ℓ) ^ 2)) * (∏ i : Fin kd, (y - td i))| *
                (Real.Gamma (ν + 1) * (2 / s) ^ ν) :=
              mul_le_mul_of_nonneg_left (hΩ_bd s hs_pos) (by positivity)
          _ = (Real.Gamma (ν + 1) * (2 / ν) ^ ν) * (y⁻¹ ^ m * y ^ (ν / 2)) *
                |(∏ ℓ : Fin Ld, (y - ν ^ 2 / (jd ℓ) ^ 2)) * (∏ i : Fin kd, (y - td i))| := by
              rw [h2s_eq]; ring
          _ ≤ (2 * Real.exp 2 * (ν + 1) ^ 2 * Real.exp ((Real.log 2 - 1) * ν)) * 1 *
                Real.exp ((1 - 3 * Real.log 2 + 4 * ε) * ν) := by
              gcongr
          _ = B := by
              dsimp [B]
              rw [mul_one, mul_assoc, ← Real.exp_add]
              congr 2; ring
      linarith [neg_abs_le ((∏ ℓ : Fin Ld, (1 - s ^ 2 / (jd ℓ) ^ 2)) *
        (∏ i : Fin kd, (1 - td i * s ^ 2 / ν ^ 2)) *
        ((∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * (s / (2 * Real.pi)) * u) *
            (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
          (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))))]

/- ### Hypotheses -/

/-- **Hypothesis 1 (Bessel representation and zero distribution for the spherical average `Ω_d`)**:
for all sufficiently large `d` (`ν = d/2 - 1`), the spherical average `Ω_d(s/(2π))` has `L(d)`
positive zeros `j_ℓ ∈ (ν, 2ν]` cancelling its sign changes on `[0, 2ν]`, satisfies the Bessel
amplitude bound `|Ω_d(s/(2π))| ≤ Γ(ν + 1) (2/s)^ν` for `s > 0`, and satisfies Davies's limiting
zero distribution `(1/ν) ∑ f(ν² / j_ℓ²) → ∫_{1/4}^1 f(t) √(1-t)/(2π t^{3/2}) dt` for every
continuous `f : ℝ → ℝ` (Davies 2026, eq. (9.1) and Lemma `lem:base-two-bessel`). -/
def H1 : Prop :=
  ∃ (d₀ : ℕ) (L : ℕ → ℕ) (j : ∀ d : ℕ, Fin (L d) → ℝ),
    (∀ d : ℕ, d₀ ≤ d →
      let ν : ℝ := (d : ℝ) / 2 - 1
      let Ω : ℝ → ℝ := fun t =>
        (∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * t * u) * (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
        (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))
      (∀ ℓ : Fin (L d), ν < j d ℓ ∧ j d ℓ ≤ 2 * ν) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (2 * ν),
        0 ≤ (∏ ℓ : Fin (L d), (1 - s ^ 2 / (j d ℓ) ^ 2)) * Ω (s / (2 * Real.pi))) ∧
      (∀ s : ℝ, 0 < s → |Ω (s / (2 * Real.pi))| ≤ Real.Gamma (ν + 1) * (2 / s) ^ ν)) ∧
    ∀ f : ℝ → ℝ, Continuous f →
      Tendsto (fun d : ℕ => (((d : ℝ) / 2 - 1)⁻¹) * ∑ ℓ : Fin (L d),
          f (((d : ℝ) / 2 - 1) ^ 2 / (j d ℓ) ^ 2))
        atTop (𝓝 (∫ t in (1 / 4 : ℝ)..1, f t * (Real.sqrt (1 - t) / (2 * Real.pi * t ^ ((3 : ℝ) / 2)))))

/-- **Hypothesis 2 (Averaged arcsine measure and logarithmic potential)**:
there exists a finite Borel measure `μ` supported on `[0, 1]` of total mass `1/2` that agrees with
`(√(1-t) / (2π t^{3/2})) dt` on `[1/4, 1]`, has continuous CDF on `[0, 1/4]` with `μ({0}) = 0`,
`μ([0, 1/4]) > 0`, and slope `≥ 1/(2π)`, and has truncated logarithmic potential
`∫ max(log |y - t|, -M) dμ ≤ 1 - 3 log 2 + ε` for every `y ∈ [0, 1/4]` and sufficiently large `M`
(Davies 2026, eqs. `eq:base-two-arcsine`–`eq:base-two-constant-potential`). -/
def H2 : Prop :=
  ∃ (μ : Measure ℝ), IsFiniteMeasure μ ∧
    μ (Set.Icc (0 : ℝ) 1) = ENNReal.ofReal (1 / 2) ∧
    μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
    (∀ f : ℝ → ℝ, Continuous f →
      ∫ t in Set.Icc (1 / 4 : ℝ) 1, f t ∂μ =
        ∫ t in (1 / 4 : ℝ)..1, f t * (Real.sqrt (1 - t) / (2 * Real.pi * t ^ ((3 : ℝ) / 2)))) ∧
    ContinuousOn (fun t : ℝ => (μ (Set.Icc 0 t)).toReal) (Set.Icc 0 (1 / 4)) ∧
    (μ (Set.Icc (0 : ℝ) 0)).toReal = 0 ∧
    0 < (μ (Set.Icc (0 : ℝ) (1 / 4))).toReal ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 / 4 →
      (b - a) / (2 * Real.pi) ≤ (μ (Set.Icc 0 b)).toReal - (μ (Set.Icc 0 a)).toReal) ∧
    (∀ y ∈ Set.Icc (0 : ℝ) (1 / 4), ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 < M ∧
        ∫ t in Set.Icc (0 : ℝ) 1, Real.log (max |y - t| (Real.exp (-M))) ∂μ ≤ 1 - 3 * Real.log 2 + ε)

/- ### Main Reduction Theorem -/

theorem main : H1 → H2 → OMA.R_Erdos704_erdos_704_variants_davies_lower_R1.H1 := by
  intro hBessel hArcsine
  dsimp only [OMA.R_Erdos704_erdos_704_variants_davies_lower_R1.H1]
  intro c hc
  obtain ⟨d₀, L, j, hBes_d, hBes_lim⟩ := hBessel
  obtain ⟨μ, hμ_fin, hμ_mass, _, hμ_right, hF_cont, hF_zero, hF_pos, hF_slope, hμ_pot⟩ :=
    hArcsine
  have : IsFiniteMeasure μ := hμ_fin
  have hc_pos : 0 < c := hc.1
  have hc_lt2 : c < 2 := hc.2
  have hlogc_lt : Real.log c < Real.log 2 := Real.log_lt_log hc_pos hc_lt2
  set ε : ℝ := (Real.log 2 - Real.log c) / 12
  have hε_pos : 0 < ε := by dsimp [ε]; linarith
  have hμ_quarter : μ ({(1 / 4 : ℝ)}) = 0 := by
    by_contra hne
    have hpos : 0 < (μ ({(1 / 4 : ℝ)})).toReal :=
      ENNReal.toReal_pos hne (measure_ne_top μ _)
    have hcont_left := hF_cont (1 / 4) ⟨by norm_num, le_rfl⟩
    rw [Metric.continuousWithinAt_iff] at hcont_left
    obtain ⟨δ, hδ_pos, hδ⟩ := hcont_left (μ ({(1 / 4 : ℝ)})).toReal hpos
    let a : ℝ := max 0 (1 / 4 - δ / 2)
    have ha_lt : a < 1 / 4 := max_lt (by norm_num) (by linarith)
    have ha_Icc : a ∈ Set.Icc (0 : ℝ) (1 / 4) := ⟨le_max_left _ _, ha_lt.le⟩
    have hdist : dist a (1 / 4) < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have : 1 / 4 - δ / 2 ≤ a := le_max_right _ _
      linarith
    have hclose := hδ ha_Icc hdist
    rw [Real.dist_eq] at hclose
    have hdisj : Disjoint (Set.Icc (0 : ℝ) a) {(1 / 4 : ℝ)} :=
      Set.disjoint_singleton_right.mpr fun h => not_lt_of_ge h.2 ha_lt
    have hsub : Set.Icc (0 : ℝ) a ∪ {(1 / 4 : ℝ)} ⊆ Set.Icc (0 : ℝ) (1 / 4) :=
      Set.union_subset (Set.Icc_subset_Icc_right ha_lt.le) (Set.singleton_subset_iff.mpr ⟨by norm_num, le_rfl⟩)
    have hle : μ (Set.Icc (0 : ℝ) a) + μ {(1 / 4 : ℝ)} ≤ μ (Set.Icc (0 : ℝ) (1 / 4)) := by
      rw [← measure_union hdisj (measurableSet_singleton _)]
      exact measure_mono hsub
    have hleR := ENNReal.toReal_mono (measure_ne_top μ _) hle
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hleR
    rw [abs_of_nonpos (by linarith)] at hclose
    linarith
  have hint_split : ∀ g : ℝ → ℝ, Continuous g →
      ∫ t in Set.Icc (0 : ℝ) 1, g t ∂μ =
        (∫ t in Set.Icc (0 : ℝ) (1 / 4), g t ∂μ) + (∫ t in Set.Icc (1 / 4 : ℝ) 1, g t ∂μ) := by
    intro g hg
    have hunion : Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) (1 / 4) ∪ Set.Ioc (1 / 4 : ℝ) 1 :=
      (Set.Icc_union_Ioc_eq_Icc (by norm_num) (by norm_num)).symm
    have hdisj : Disjoint (Set.Icc (0 : ℝ) (1 / 4)) (Set.Ioc (1 / 4 : ℝ) 1) :=
      Set.disjoint_left.mpr fun x h1 h2 => not_lt_of_ge h1.2 h2.1
    have hae_eq : (Set.Ioc (1 / 4 : ℝ) 1 : Set ℝ) =ᵐ[μ] Set.Icc (1 / 4 : ℝ) 1 := by
      rw [ae_eq_set]
      refine ⟨measure_mono_null (fun x hx => ?_) measure_empty, measure_mono_null (fun x hx => ?_) hμ_quarter⟩
      · simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_Icc, Set.mem_empty_iff_false] at hx ⊢
        exact hx.2 ⟨hx.1.1.le, hx.1.2⟩
      · simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc, Set.mem_singleton_iff] at hx ⊢
        by_contra hne; exact hx.2 ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hne), hx.1.2⟩
    rw [hunion, setIntegral_union hdisj measurableSet_Ioc
      (hg.continuousOn.integrableOn_compact isCompact_Icc)
      ((hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self),
      setIntegral_congr_set hae_eq]
  let M₀ : ℝ := (μ (Set.Icc (0 : ℝ) (1 / 4))).toReal
  let L_lim : ℝ := ∫ t in (1 / 4 : ℝ)..1, (1 : ℝ) * (Real.sqrt (1 - t) / (2 * Real.pi * t ^ ((3 : ℝ) / 2)))
  have hmass_sum : M₀ + L_lim = 1 / 2 := by
    have h1 := hint_split (fun _ => (1 : ℝ)) continuous_const
    rw [setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      Measure.real_def, Measure.real_def, hμ_mass, ENNReal.toReal_ofReal (by norm_num),
      hμ_right (fun _ => (1 : ℝ)) continuous_const] at h1
    linarith
  have hcover_pt : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 4),
      ∃ (M δ : ℝ), 0 < M ∧ 0 < δ ∧
        (∫ t in Set.Icc (0 : ℝ) 1, Real.log (max |y - t| (Real.exp (-M))) ∂μ ≤ 1 - 3 * Real.log 2 + ε) ∧
        ∀ y' ∈ Set.Icc (0 : ℝ) (1 / 4), |y' - y| < δ → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          Real.log (max |y' - t| (Real.exp (-M))) ≤ Real.log (max |y - t| (Real.exp (-M))) + ε := by
    intro y hy
    obtain ⟨M, hM_pos, hM_pot⟩ := hμ_pot y hy ε hε_pos
    let Φ : ℝ × ℝ → ℝ := fun p => Real.log (max |p.1 - p.2| (Real.exp (-M)))
    have hΦ_cont : Continuous Φ :=
      Continuous.log (((continuous_fst.sub continuous_snd).abs).max continuous_const) fun p =>
        ne_of_gt (lt_of_lt_of_le (Real.exp_pos (-M)) (le_max_right _ _))
    have huc := ((isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).prod
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))).uniformContinuousOn_of_continuous hΦ_cont.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ_pos, hδ⟩ := huc ε hε_pos
    refine ⟨M, δ, hM_pos, hδ_pos, hM_pot, fun y' hy' hdist t ht => ?_⟩
    have hpair_dist : dist (y', t) (y, t) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
      exact hdist
    have hclose := hδ (y', t) ⟨hy', ht⟩ (y, t) ⟨hy, ht⟩ hpair_dist
    rw [Real.dist_eq] at hclose
    dsimp [Φ] at hclose
    linarith [le_abs_self (Real.log (max |y' - t| (Real.exp (-M))) - Real.log (max |y - t| (Real.exp (-M))))]
  choose M_fn δ_fn hM_pos_fn hδ_pos_fn hM_pot_fn hδ_osc_fn using hcover_pt
  have hcov_open : Set.Icc (0 : ℝ) (1 / 4) ⊆
      ⋃ (y : Set.Icc (0 : ℝ) (1 / 4)), Metric.ball y.1 (δ_fn y.1 y.2) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hδ_pos_fn y hy)⟩
  obtain ⟨S_net, hS_cov⟩ := isCompact_Icc.elim_finite_subcover
    (fun y : Set.Icc (0 : ℝ) (1 / 4) => Metric.ball y.1 (δ_fn y.1 y.2))
    (fun _ => Metric.isOpen_ball) hcov_open
  let g_net : Set.Icc (0 : ℝ) (1 / 4) → ℝ → ℝ := fun p t =>
    Real.log (max |p.1 - t| (Real.exp (-(M_fn p.1 p.2))))
  have hg_net_cont : ∀ p : Set.Icc (0 : ℝ) (1 / 4), Continuous (g_net p) := fun p =>
    Continuous.log (((continuous_const.sub continuous_id).abs).max continuous_const) fun t =>
      ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _))
  have hν_top : Tendsto (fun d : ℕ => (d : ℝ) / 2 - 1) atTop atTop := by
    have h1 : Tendsto (fun d : ℕ => (d : ℝ) / 2) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop
    exact h1.atTop_add tendsto_const_nhds
  have hL_lim : Tendsto (fun d : ℕ => (L d : ℝ) / ((d : ℝ) / 2 - 1)) atTop (𝓝 L_lim) := by
    have h1 := hBes_lim (fun _ => (1 : ℝ)) continuous_const
    refine h1.congr fun d => ?_
    simp [div_eq_inv_mul]
  have hfloor_lim : Tendsto (fun d : ℕ => ((Nat.floor (((d : ℝ) / 2 - 1) / 2) : ℕ) : ℝ) / ((d : ℝ) / 2 - 1))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have hinv0 : Tendsto (fun d : ℕ => ((d : ℝ) / 2 - 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hν_top
    have hlo : Tendsto (fun d : ℕ => (1 / 2 : ℝ) - ((d : ℝ) / 2 - 1)⁻¹) atTop (𝓝 (1 / 2 : ℝ)) := by
      simpa using tendsto_const_nhds.sub hinv0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 6] with d hd
      have hν_pos : (0 : ℝ) < (d : ℝ) / 2 - 1 := by
        have h6 : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      have hlt := Nat.lt_floor_add_one (((d : ℝ) / 2 - 1) / 2)
      rw [le_div_iff₀ hν_pos]
      have hrew : (1 / 2 - ((d : ℝ) / 2 - 1)⁻¹) * ((d : ℝ) / 2 - 1) = ((d : ℝ) / 2 - 1) / 2 - 1 := by
        rw [sub_mul, inv_mul_cancel₀ hν_pos.ne']; ring
      linarith
    · filter_upwards [eventually_ge_atTop 6] with d hd
      have hν_pos : (0 : ℝ) < (d : ℝ) / 2 - 1 := by
        have h6 : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      have hle := Nat.floor_le (by linarith : (0 : ℝ) ≤ ((d : ℝ) / 2 - 1) / 2)
      rw [div_le_iff₀ hν_pos]; linarith
  let k_fn : ℕ → ℕ := fun d => Nat.floor (((d : ℝ) / 2 - 1) / 2) - L d
  have hk_pos_ev : ∀ᶠ d : ℕ in atTop, L d < Nat.floor (((d : ℝ) / 2 - 1) / 2) := by
    have hdiff : Tendsto (fun d : ℕ => ((Nat.floor (((d : ℝ) / 2 - 1) / 2) : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) -
        (L d : ℝ) / ((d : ℝ) / 2 - 1)) atTop (𝓝 M₀) := by
      have : (1 / 2 : ℝ) - L_lim = M₀ := by linarith [hmass_sum]
      rw [← this]; exact hfloor_lim.sub hL_lim
    filter_upwards [hdiff.eventually (Ioi_mem_nhds hF_pos), eventually_ge_atTop 6] with d hd_pos hd6
    have hν_pos : (0 : ℝ) < (d : ℝ) / 2 - 1 := by
      have h6 : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd6
      linarith
    have hltR : (L d : ℝ) < ((Nat.floor (((d : ℝ) / 2 - 1) / 2) : ℕ) : ℝ) := by
      rw [← sub_pos] at hd_pos ⊢
      have := mul_pos hd_pos hν_pos
      have hrew : (((Nat.floor (((d : ℝ) / 2 - 1) / 2) : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) -
          (L d : ℝ) / ((d : ℝ) / 2 - 1)) * ((d : ℝ) / 2 - 1) =
          ((Nat.floor (((d : ℝ) / 2 - 1) / 2) : ℕ) : ℝ) - (L d : ℝ) := by
        rw [sub_mul, div_mul_cancel₀ _ hν_pos.ne', div_mul_cancel₀ _ hν_pos.ne']
      linarith
    exact_mod_cast hltR
  have hk_ratio : Tendsto (fun d : ℕ => ((k_fn d + 1 : ℕ) : ℝ) / ((d : ℝ) / 2 - 1)) atTop (𝓝 M₀) := by
    have h1 : Tendsto (fun d : ℕ => ((Nat.floor (((d : ℝ) / 2 - 1) / 2) : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) -
        (L d : ℝ) / ((d : ℝ) / 2 - 1) + ((d : ℝ) / 2 - 1)⁻¹) atTop (𝓝 (M₀ + 0)) := by
      have hsub : (1 / 2 : ℝ) - L_lim = M₀ := by linarith [hmass_sum]
      exact (hsub ▸ hfloor_lim.sub hL_lim).add (tendsto_inv_atTop_zero.comp hν_top)
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hk_pos_ev, eventually_ge_atTop 6] with d hlt hd6
    have hν_pos : (0 : ℝ) < (d : ℝ) / 2 - 1 := by
      have h6 : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd6
      linarith
    dsimp [k_fn]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hlt.le]
    field_simp [hν_pos.ne']
  have hnet_ev : ∀ p ∈ S_net, ∀ᶠ d : ℕ in atTop,
      let ν : ℝ := (d : ℝ) / 2 - 1
      (ν⁻¹ * ∑ ℓ : Fin (L d), g_net p (ν ^ 2 / (j d ℓ) ^ 2) ≤
        (∫ t in Set.Icc (1 / 4 : ℝ) 1, g_net p t ∂μ) + ε) ∧
      ∀ (t : Fin (k_fn d) → ℝ),
        (∀ i : Fin (k_fn d), 0 < t i ∧ t i < 1 / 4) →
        (∀ (g : ℝ → ℝ) (B_g η_g : ℝ), ContinuousOn g (Set.Icc 0 (1 / 4)) → 0 ≤ B_g → 0 ≤ η_g →
          (∀ x ∈ Set.Icc (0 : ℝ) (1 / 4), |g x| ≤ B_g) →
          (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) (1 / 4) → y ∈ Set.Icc (0 : ℝ) (1 / 4) →
            |x - y| ≤ 2 * Real.pi * M₀ / ((k_fn d + 1 : ℕ) : ℝ) → |g x - g y| ≤ η_g) →
          |M₀ / ((k_fn d + 1 : ℕ) : ℝ) * (∑ i : Fin (k_fn d), g (t i)) -
            ∫ x in Set.Icc (0 : ℝ) (1 / 4), g x ∂μ| ≤
            η_g * M₀ + B_g * (M₀ / ((k_fn d + 1 : ℕ) : ℝ))) →
        ν⁻¹ * ∑ i : Fin (k_fn d), g_net p (t i) ≤
          (∫ x in Set.Icc (0 : ℝ) (1 / 4), g_net p x ∂μ) + ε := by
    intro p _
    have hB_lim := hBes_lim (g_net p) (hg_net_cont p)
    rw [← hμ_right (g_net p) (hg_net_cont p)] at hB_lim
    have h1 := hB_lim.eventually (Iio_mem_nhds (by linarith : ∫ t in Set.Icc (1 / 4 : ℝ) 1, g_net p t ∂μ <
      (∫ t in Set.Icc (1 / 4 : ℝ) 1, g_net p t ∂μ) + ε))
    obtain ⟨B_p, hBp⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg_net_cont p).continuousOn
    let B_g : ℝ := max B_p 1
    have hBg_pos : 0 < B_g := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hgp_bd : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 4), |g_net p x| ≤ B_g := fun x hx =>
      (hBp x hx).trans (le_max_left _ _)
    have huc := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).uniformContinuousOn_of_continuous
      (hg_net_cont p).continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    have hM₀_pos : 0 < M₀ := hF_pos
    have hη_pos' : 0 < ε / (4 * M₀) := by positivity
    obtain ⟨δ_g, hδg_pos, hδg⟩ := huc (ε / (4 * M₀)) hη_pos'
    have hk_top : Tendsto (fun d : ℕ => ((k_fn d + 1 : ℕ) : ℝ)) atTop atTop := by
      have hmul : Tendsto (fun d : ℕ => (((k_fn d + 1 : ℕ) : ℝ) / ((d : ℝ) / 2 - 1)) * ((d : ℝ) / 2 - 1))
          atTop atTop := Tendsto.pos_mul_atTop hM₀_pos hk_ratio hν_top
      refine hmul.congr' ?_
      filter_upwards [eventually_ge_atTop 6] with d hd6
      have hν_pos : (0 : ℝ) < (d : ℝ) / 2 - 1 := by
        have h6 : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd6
        linarith
      exact div_mul_cancel₀ _ hν_pos.ne'
    have hmesh_ev : ∀ᶠ d : ℕ in atTop,
        2 * Real.pi * M₀ / ((k_fn d + 1 : ℕ) : ℝ) < δ_g ∧
        B_g * (M₀ / ((k_fn d + 1 : ℕ) : ℝ)) ≤ ε / 4 := by
      have h1' : Tendsto (fun d : ℕ => 2 * Real.pi * M₀ / ((k_fn d + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hk_top
      have h2' : Tendsto (fun d : ℕ => B_g * (M₀ / ((k_fn d + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.div_atTop hk_top).const_mul B_g
      exact (h1'.eventually (Iio_mem_nhds hδg_pos)).and
        (h2'.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 4))) |>.mono fun d hd =>
          ⟨hd.1, hd.2.le⟩
    have hscale_ev : ∀ᶠ d : ℕ in atTop,
        |((k_fn d + 1 : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) - M₀| * B_g ≤ ε / 4 := by
      have hsub : Tendsto (fun d : ℕ => |((k_fn d + 1 : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) - M₀| * B_g)
          atTop (𝓝 0) := by
        have : Tendsto (fun d : ℕ => |((k_fn d + 1 : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) - M₀|) atTop (𝓝 0) := by
          simpa [sub_self] using (hk_ratio.sub (tendsto_const_nhds (x := M₀))).abs
        simpa using this.mul_const B_g
      exact (hsub.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).mono fun _ h => h.le
    filter_upwards [h1, hmesh_ev, hscale_ev, eventually_ge_atTop 6] with d h1d ⟨hmesh, hBerr⟩ hscale hd6
    refine ⟨h1d.le, fun t ht_mem ht_rs => ?_⟩
    have hν_pos : (0 : ℝ) < (d : ℝ) / 2 - 1 := by
      have h6 : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd6
      linarith
    have hrs := ht_rs (g_net p) B_g (ε / (4 * M₀)) (hg_net_cont p).continuousOn hBg_pos.le hη_pos'.le
      hgp_bd fun x y hx hy hxy => by
        have hlt : dist x y < δ_g := by rw [Real.dist_eq]; exact lt_of_le_of_lt hxy hmesh
        have hcl := hδg x hx y hy hlt
        rw [Real.dist_eq] at hcl; exact hcl.le
    have hη_simp : ε / (4 * M₀) * M₀ = ε / 4 := by field_simp [hM₀_pos.ne']
    have hrs' : M₀ / ((k_fn d + 1 : ℕ) : ℝ) * (∑ i : Fin (k_fn d), g_net p (t i)) ≤
        (∫ x in Set.Icc (0 : ℝ) (1 / 4), g_net p x ∂μ) + ε / 2 := by
      have := le_abs_self (M₀ / ((k_fn d + 1 : ℕ) : ℝ) * (∑ i : Fin (k_fn d), g_net p (t i)) -
        ∫ x in Set.Icc (0 : ℝ) (1 / 4), g_net p x ∂μ)
      linarith
    have hsum_abs : |∑ i : Fin (k_fn d), g_net p (t i)| ≤ ((k_fn d + 1 : ℕ) : ℝ) * B_g := by
      calc |∑ i : Fin (k_fn d), g_net p (t i)|
          ≤ ∑ i : Fin (k_fn d), |g_net p (t i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin (k_fn d), B_g := Finset.sum_le_sum fun i _ =>
            hgp_bd (t i) ⟨(ht_mem i).1.le, (ht_mem i).2.le⟩
        _ = (k_fn d : ℝ) * B_g := by simp
        _ ≤ ((k_fn d + 1 : ℕ) : ℝ) * B_g := by gcongr; exact_mod_cast Nat.le_succ _
    have hdiff_scale :
        ((d : ℝ) / 2 - 1)⁻¹ * (∑ i : Fin (k_fn d), g_net p (t i)) -
          M₀ / ((k_fn d + 1 : ℕ) : ℝ) * (∑ i : Fin (k_fn d), g_net p (t i)) ≤ ε / 4 := by
      have hk1_pos : (0 : ℝ) < ((k_fn d + 1 : ℕ) : ℝ) := by positivity
      have hfactor : ((d : ℝ) / 2 - 1)⁻¹ * (∑ i : Fin (k_fn d), g_net p (t i)) -
          M₀ / ((k_fn d + 1 : ℕ) : ℝ) * (∑ i : Fin (k_fn d), g_net p (t i)) =
          (((k_fn d + 1 : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) - M₀) *
            ((∑ i : Fin (k_fn d), g_net p (t i)) / ((k_fn d + 1 : ℕ) : ℝ)) := by
        field_simp [hν_pos.ne', hk1_pos.ne']
      rw [hfactor]
      calc (((k_fn d + 1 : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) - M₀) *
              ((∑ i : Fin (k_fn d), g_net p (t i)) / ((k_fn d + 1 : ℕ) : ℝ))
          ≤ |(((k_fn d + 1 : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) - M₀) *
              ((∑ i : Fin (k_fn d), g_net p (t i)) / ((k_fn d + 1 : ℕ) : ℝ))| := le_abs_self _
        _ = |((k_fn d + 1 : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) - M₀| *
              (|∑ i : Fin (k_fn d), g_net p (t i)| / ((k_fn d + 1 : ℕ) : ℝ)) := by
            rw [abs_mul, abs_div, abs_of_pos hk1_pos]
        _ ≤ |((k_fn d + 1 : ℕ) : ℝ) / ((d : ℝ) / 2 - 1) - M₀| * B_g := by
            gcongr; rw [div_le_iff₀ hk1_pos]; linarith
        _ ≤ ε / 4 := hscale
    linarith
  have hall_net_ev : ∀ᶠ d : ℕ in atTop, ∀ p ∈ S_net,
      let ν : ℝ := (d : ℝ) / 2 - 1
      (ν⁻¹ * ∑ ℓ : Fin (L d), g_net p (ν ^ 2 / (j d ℓ) ^ 2) ≤
        (∫ t in Set.Icc (1 / 4 : ℝ) 1, g_net p t ∂μ) + ε) ∧
      ∀ (t : Fin (k_fn d) → ℝ),
        (∀ i : Fin (k_fn d), 0 < t i ∧ t i < 1 / 4) →
        (∀ (g : ℝ → ℝ) (B_g η_g : ℝ), ContinuousOn g (Set.Icc 0 (1 / 4)) → 0 ≤ B_g → 0 ≤ η_g →
          (∀ x ∈ Set.Icc (0 : ℝ) (1 / 4), |g x| ≤ B_g) →
          (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) (1 / 4) → y ∈ Set.Icc (0 : ℝ) (1 / 4) →
            |x - y| ≤ 2 * Real.pi * M₀ / ((k_fn d + 1 : ℕ) : ℝ) → |g x - g y| ≤ η_g) →
          |M₀ / ((k_fn d + 1 : ℕ) : ℝ) * (∑ i : Fin (k_fn d), g (t i)) -
            ∫ x in Set.Icc (0 : ℝ) (1 / 4), g x ∂μ| ≤
            η_g * M₀ + B_g * (M₀ / ((k_fn d + 1 : ℕ) : ℝ))) →
        ν⁻¹ * ∑ i : Fin (k_fn d), g_net p (t i) ≤
          (∫ x in Set.Icc (0 : ℝ) (1 / 4), g_net p x ∂μ) + ε :=
    Filter.eventually_all_finset S_net |>.mpr hnet_ev
  have hexp_ev := exp_domination_eventually (c := c) (ε := ε) hc_pos (by dsimp [ε]; linarith)
  filter_upwards [eventually_ge_atTop (max d₀ 6), hk_pos_ev, hall_net_ev, hexp_ev] with
    d hd hLk hnet hexp
  have hd₀ : d₀ ≤ d := le_trans (le_max_left _ _) hd
  have hd6 : 6 ≤ d := le_trans (le_max_right _ _) hd
  let ν : ℝ := (d : ℝ) / 2 - 1
  have hν_ge2 : (2 : ℝ) ≤ ν := by
    have h6 : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd6
    dsimp [ν]; linarith
  have hν_pos : 0 < ν := by linarith
  obtain ⟨hj_range, hj_sign, hΩ_bd⟩ := hBes_d d hd₀
  obtain ⟨t, ht_mem, ht_rs⟩ := quantile_root_placement μ hF_cont hF_zero hF_pos hF_slope (k_fn d)
  let m : ℕ := Nat.floor (ν / 2)
  have hm_eq : L d + k_fn d = m := Nat.add_sub_of_le hLk.le
  have hm_le : (m : ℝ) ≤ ν / 2 := Nat.floor_le (by linarith)
  have hR_bd : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 4),
      |(∏ ℓ : Fin (L d), (y - ν ^ 2 / (j d ℓ) ^ 2)) * (∏ i : Fin (k_fn d), (y - t i))| ≤
      Real.exp ((1 - 3 * Real.log 2 + 4 * ε) * ν) := by
    intro y hy
    by_cases h0 : (∏ ℓ : Fin (L d), (y - ν ^ 2 / (j d ℓ) ^ 2)) * (∏ i : Fin (k_fn d), (y - t i)) = 0
    · rw [h0, abs_zero]; exact (Real.exp_pos _).le
    have h1_ne : ∏ ℓ : Fin (L d), (y - ν ^ 2 / (j d ℓ) ^ 2) ≠ 0 := (mul_ne_zero_iff.mp h0).1
    have h2_ne : ∏ i : Fin (k_fn d), (y - t i) ≠ 0 := (mul_ne_zero_iff.mp h0).2
    have hℓ_ne : ∀ ℓ : Fin (L d), |y - ν ^ 2 / (j d ℓ) ^ 2| ≠ 0 := fun ℓ h =>
      h1_ne (Finset.prod_eq_zero (Finset.mem_univ ℓ) (abs_eq_zero.mp h))
    have hi_ne : ∀ i : Fin (k_fn d), |y - t i| ≠ 0 := fun i h =>
      h2_ne (Finset.prod_eq_zero (Finset.mem_univ i) (abs_eq_zero.mp h))
    have hcov_y := hS_cov hy
    simp only [Set.mem_iUnion, exists_prop] at hcov_y
    obtain ⟨p, hp_mem, hy_ball⟩ := hcov_y
    have hy_dist : |y - p.1| < δ_fn p.1 p.2 := by simpa [Metric.mem_ball, Real.dist_eq] using hy_ball
    obtain ⟨hB_p, hQ_p⟩ := hnet p hp_mem
    have hQ_t := hQ_p t ht_mem ht_rs
    have hlog_eq : Real.log |(∏ ℓ : Fin (L d), (y - ν ^ 2 / (j d ℓ) ^ 2)) * (∏ i : Fin (k_fn d), (y - t i))| =
        (∑ ℓ : Fin (L d), Real.log |y - ν ^ 2 / (j d ℓ) ^ 2|) +
        (∑ i : Fin (k_fn d), Real.log |y - t i|) := by
      rw [abs_mul, Real.log_mul (abs_ne_zero.mpr h1_ne) (abs_ne_zero.mpr h2_ne),
        Finset.abs_prod, Finset.abs_prod,
        Real.log_prod (fun ℓ _ => hℓ_ne ℓ), Real.log_prod (fun i _ => hi_ne i)]
    have hlog_le : ν⁻¹ * Real.log |(∏ ℓ : Fin (L d), (y - ν ^ 2 / (j d ℓ) ^ 2)) *
        (∏ i : Fin (k_fn d), (y - t i))| ≤ 1 - 3 * Real.log 2 + 4 * ε := by
      rw [hlog_eq, mul_add]
      have hterm1 : ∀ ℓ : Fin (L d), Real.log |y - ν ^ 2 / (j d ℓ) ^ 2| ≤
          g_net p (ν ^ 2 / (j d ℓ) ^ 2) + ε := by
        intro ℓ
        have hj1 := (hj_range ℓ).1
        have hj_pos : 0 < j d ℓ := by dsimp [ν] at hν_pos; linarith
        have hIcc : ν ^ 2 / (j d ℓ) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
          refine ⟨by positivity, ?_⟩
          rw [div_le_one (by positivity)]
          exact pow_le_pow_left₀ hν_pos.le (by dsimp [ν]; linarith) 2
        have hpos_abs : 0 < |y - ν ^ 2 / (j d ℓ) ^ 2| :=
          lt_of_le_of_ne (abs_nonneg _) (Ne.symm (hℓ_ne ℓ))
        exact (Real.log_le_log hpos_abs (le_max_left _ _)).trans
          (hδ_osc_fn p.1 p.2 y hy hy_dist _ hIcc)
      have hterm2 : ∀ i : Fin (k_fn d), Real.log |y - t i| ≤ g_net p (t i) + ε := by
        intro i
        have hIcc : t i ∈ Set.Icc (0 : ℝ) 1 := ⟨(ht_mem i).1.le, by linarith [(ht_mem i).2]⟩
        have hpos_abs : 0 < |y - t i| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm (hi_ne i))
        exact (Real.log_le_log hpos_abs (le_max_left _ _)).trans
          (hδ_osc_fn p.1 p.2 y hy hy_dist _ hIcc)
      have hsum_le : (∑ ℓ : Fin (L d), Real.log |y - ν ^ 2 / (j d ℓ) ^ 2|) +
            (∑ i : Fin (k_fn d), Real.log |y - t i|) ≤
          (∑ ℓ : Fin (L d), g_net p (ν ^ 2 / (j d ℓ) ^ 2)) +
          (∑ i : Fin (k_fn d), g_net p (t i)) + (m : ℝ) * ε := by
        have hs1 := Finset.sum_le_sum (s := Finset.univ) fun ℓ _ => hterm1 ℓ
        have hs2 := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm2 i
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul] at hs1 hs2
        have hcast : (L d : ℝ) + (k_fn d : ℝ) = (m : ℝ) := by exact_mod_cast hm_eq
        linarith [show (L d : ℝ) * ε + (k_fn d : ℝ) * ε = (m : ℝ) * ε by rw [← add_mul, hcast]]
      have hm_div : ν⁻¹ * ((m : ℝ) * ε) ≤ ε := by
        have h1 : ν⁻¹ * (m : ℝ) ≤ 1 / 2 := by
          rw [inv_mul_le_iff₀ hν_pos]; linarith
        nlinarith
      have hcomb_int : (∫ t in Set.Icc (1 / 4 : ℝ) 1, g_net p t ∂μ) +
          (∫ t in Set.Icc (0 : ℝ) (1 / 4), g_net p t ∂μ) ≤ 1 - 3 * Real.log 2 + ε := by
        linarith [hint_split (g_net p) (hg_net_cont p), hM_pot_fn p.1 p.2]
      calc ν⁻¹ * (∑ ℓ : Fin (L d), Real.log |y - ν ^ 2 / (j d ℓ) ^ 2|) +
              ν⁻¹ * (∑ i : Fin (k_fn d), Real.log |y - t i|)
          = ν⁻¹ * ((∑ ℓ : Fin (L d), Real.log |y - ν ^ 2 / (j d ℓ) ^ 2|) +
              (∑ i : Fin (k_fn d), Real.log |y - t i|)) := (mul_add _ _ _).symm
        _ ≤ ν⁻¹ * ((∑ ℓ : Fin (L d), g_net p (ν ^ 2 / (j d ℓ) ^ 2)) +
              (∑ i : Fin (k_fn d), g_net p (t i)) + (m : ℝ) * ε) :=
            mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hν_pos.le)
        _ = (ν⁻¹ * ∑ ℓ : Fin (L d), g_net p (ν ^ 2 / (j d ℓ) ^ 2)) +
            (ν⁻¹ * ∑ i : Fin (k_fn d), g_net p (t i)) + ν⁻¹ * ((m : ℝ) * ε) := by ring
        _ ≤ ((∫ t in Set.Icc (1 / 4 : ℝ) 1, g_net p t ∂μ) + ε) +
            ((∫ t in Set.Icc (0 : ℝ) (1 / 4), g_net p t ∂μ) + ε) + ε := by linarith
        _ ≤ 1 - 3 * Real.log 2 + 4 * ε := by linarith
    have hlog_mul : Real.log |(∏ ℓ : Fin (L d), (y - ν ^ 2 / (j d ℓ) ^ 2)) *
        (∏ i : Fin (k_fn d), (y - t i))| ≤ (1 - 3 * Real.log 2 + 4 * ε) * ν := by
      have := mul_le_mul_of_nonneg_right hlog_le hν_pos.le
      rwa [inv_mul_eq_div, div_mul_cancel₀ _ hν_pos.ne'] at this
    rw [← Real.exp_log (abs_pos.mpr h0)]
    exact Real.exp_le_exp.mpr hlog_mul
  exact polynomial_certificate_step hd6 hc_pos hm_eq hexp (j d) t hj_range ht_mem hj_sign hΩ_bd hR_bd

end OMA.R_Erdos704_erdos_704_variants_davies_lower_R1_H1_R1
