import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1
import Mathlib

/-!
# The density increment from an amplified patch source and a structured density step

The target is step H1 of reduction R1.H2.R1 of Erdős 142. For each length k at least four, a
sparse k-progression-free set S in [1, N] with log-density p = max 2 (log (2N / |S|)) and budget
p^β + R ≤ log log N passes to a progression of length M on which its log-density p' satisfies
p' + 1 ≤ p while the budget p'^β + R ≤ log log M survives.

This is the descent subquadratic_patch_descent of the openai/math library (commit 3344da5, file
lean/OAI/Combinatorics/Progressions/Estimates/UniformRelativePatchSource.lean). Its proof has two
deep inputs and a budget computation. The reduction keeps the two inputs as hypotheses and proves
the computation.

The structured objects are the polynomial patches of that library (PolynomialPatch Unit s d),
written out in full: weights w with 1 ≤ w i ≤ s, monotone; centre polynomials P i in the time
variable and the earlier slots, of weighted degree at most w i (the time variable has weight 1,
slot j has weight w j); a kernel Φ with values in [0, 1], supported in the cube of radius 1/4,
Lipschitz with constant L. The patch at time n is the lattice sum over b of
Φ (b - centre (n, b)), a nilsequence in triangular coordinates.

H1 (source: inverse theorem with amplification). A sparse progression-free set inside its budget
has a gain G with log G ≥ c p^ν such that 1_S - G α (α = |S| / N) correlates with a patch of
dimension d, log (d + 1) ≤ B log (2 + p), on a progression of length M ≥ N exp (-U). In the
library this is SubquadraticPatchSource (s + 2) s κ H₀ K 1 1 B D pmin (log 2), given by
exists_subquadratic_patch_source_of_uniform_relative_lifting with
exists_manuscriptRelativePatchPower (Results/Conclusions.lean), together with the gain bound
exists_selected_density_drop (Probability/RelativeSourceDensityParameter.lean). There A₀ = 1 and
q = 1, so β = 1 - ν / 2 with ν = gainExponent K in (0, 1/4].

H2 (structured density step). Such a correlation yields a progression on which the density of S
exceeds G α, so the log-density drops by any δ ≤ log G, while log log of the length drops by at
most L₀ + 2 s² R. This is scored_patch_density_step (Sampling/ScoredPatchDensityStep.lean) for
the indicator of S shifted by one, with L₀ = log (4 P (log (2 C) + 3)).

The glue below takes δ = c p^ν. Concavity of x ↦ x^β gives p^β - p'^β ≥ β c p^(ν/2), which pays
L₀ + 2 s² B log (2 + p) once p is large, and the two resources fit under p^β because β > 1/4.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R3

open Erdos142 Filter Real
open scoped Topology

/-- Source: a sparse progression-free set has an amplified correlation with a polynomial patch. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ (s : ℕ) (ν c B D p₀ C₁ : ℝ), 0 < ν ∧ ν < 1 ∧ 0 < c ∧ 0 ≤ B ∧ 0 ≤ D ∧
    ∀ (N : ℕ) (S : Finset ℕ) (p : ℝ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      p = max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) →
      p₀ ≤ p → p ^ (1 - ν / 2) + C₁ ≤ Real.log (Real.log (N : ℝ)) →
      ∃ (d M a q : ℕ) (U G : ℝ) (w : Fin d → ℕ)
        (P : (i : Fin d) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
        (Φ : (Fin d → ℝ) → ℝ) (L : NNReal),
        (∀ i, 1 ≤ w i ∧ w i ≤ s) ∧ Monotone w ∧
        (∀ i, P i ∈ MvPolynomial.restrictSupport ℝ
          {m | Finsupp.weight (Sum.elim (fun _ : Unit ↦ (1 : ℕ))
            (fun j : Fin i.val ↦ w ⟨j.val, lt_trans j.isLt i.isLt⟩)) m ≤ w i}) ∧
        (∀ x, 0 ≤ Φ x ∧ Φ x ≤ 1) ∧ (∀ x, Φ x ≠ 0 → ∀ i, |x i| ≤ 1 / 4) ∧
        LipschitzWith L Φ ∧
        0 < q ∧ (∀ n < M, a + q * n ∈ Finset.Icc 1 N) ∧ 1 ≤ U ∧
        Real.log (N : ℝ) - U ≤ Real.log (M : ℝ) ∧ (L : ℝ) + 1 ≤ Real.exp U ∧
        Real.log ((d : ℝ) + 1) ≤ B * Real.log (2 + p) ∧
        Real.log U ≤ D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) ∧
        0 < G ∧ c * p ^ ν ≤ Real.log G ∧
        Real.exp (-U) ≤ (∑ n ∈ Finset.range M,
          ((if a + q * n ∈ S then (1 : ℝ) else 0) - G * ((S.card : ℝ) / (N : ℝ))) *
            ∑' b : Fin d → ℤ, Φ (fun i ↦ (b i : ℝ) - MvPolynomial.aeval
              (Sum.elim (fun _ : Unit ↦ (n : ℝ))
                (fun j : Fin i.val ↦ (b ⟨j.val, lt_trans j.isLt i.isLt⟩ : ℝ))) (P i))) /
          (M : ℝ)

/-- Structured density step: a correlation with a patch gives a denser progression. -/
def H2 : Prop :=
  ∀ s : ℕ, ∃ L₀ : ℝ, ∀ (N : ℕ) (S : Finset ℕ) (p : ℝ) (d M a q : ℕ) (U R V G δ : ℝ)
      (w : Fin d → ℕ) (P : (i : Fin d) → MvPolynomial (Unit ⊕ Fin i.val) ℝ)
      (Φ : (Fin d → ℝ) → ℝ) (L : NNReal),
    (∀ i, 1 ≤ w i ∧ w i ≤ s) → Monotone w →
    (∀ i, P i ∈ MvPolynomial.restrictSupport ℝ
      {m | Finsupp.weight (Sum.elim (fun _ : Unit ↦ (1 : ℕ))
        (fun j : Fin i.val ↦ w ⟨j.val, lt_trans j.isLt i.isLt⟩)) m ≤ w i}) →
    (∀ x, 0 ≤ Φ x ∧ Φ x ≤ 1) → (∀ x, Φ x ≠ 0 → ∀ i, |x i| ≤ 1 / 4) →
    LipschitzWith L Φ →
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    p = max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) →
    0 < q → (∀ n < M, a + q * n ∈ Finset.Icc 1 N) → 1 ≤ U →
    Real.log (N : ℝ) - U ≤ Real.log (M : ℝ) → (L : ℝ) + 1 ≤ Real.exp U →
    Real.log ((d : ℝ) + 1) ≤ R → Real.log U ≤ V →
    L₀ + ((2 * s * s + 1 : ℕ) : ℝ) * R + V ≤ Real.log (Real.log (N : ℝ)) →
    0 < G → δ ≤ Real.log G → 2 ≤ p - δ →
    Real.exp (-U) ≤ (∑ n ∈ Finset.range M,
      ((if a + q * n ∈ S then (1 : ℝ) else 0) - G * ((S.card : ℝ) / (N : ℝ))) *
        ∑' b : Fin d → ℤ, Φ (fun i ↦ (b i : ℝ) - MvPolynomial.aeval
          (Sum.elim (fun _ : Unit ↦ (n : ℝ))
            (fun j : Fin i.val ↦ (b ⟨j.val, lt_trans j.isLt i.isLt⟩ : ℝ))) (P i))) /
      (M : ℝ) →
    ∃ a' q' M' : ℕ, 0 < q' ∧ 2 ≤ M' ∧
      (∀ i ∈ Finset.Icc 1 M', a' + (i - 1) * q' ∈ Finset.Icc 1 N) ∧
      Real.log (Real.log (N : ℝ)) - (L₀ + ((2 * s * s : ℕ) : ℝ) * R) ≤
        Real.log (Real.log (M' : ℝ)) ∧
      G * ((S.card : ℝ) / (N : ℝ)) <
        (((Finset.Icc 1 M').filter (fun i ↦ a' + (i - 1) * q' ∈ S)).card : ℝ) / (M' : ℝ) ∧
      max 2 (Real.log (2 * (M' : ℝ) /
        (((Finset.Icc 1 M').filter (fun i ↦ a' + (i - 1) * q' ∈ S)).card : ℝ))) ≤ p - δ

/-- Concavity of x ↦ x^β for 0 ≤ β ≤ 1, in tangent-line form at p. -/
lemma concave_drop {p δ β : ℝ} (hp : 0 < p) (hδ0 : 0 ≤ δ) (hδp : δ ≤ p) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) : (p - δ) ^ β ≤ p ^ β - β * p ^ (β - 1) * δ := by
  have hs : -1 ≤ -δ / p := by
    rw [neg_div, neg_le_neg_iff, div_le_one hp]
    exact hδp
  have h := rpow_one_add_le_one_add_mul_self hs hβ0 hβ1
  have h1 : 0 ≤ 1 + -δ / p := by linarith
  have e1 : p - δ = p * (1 + -δ / p) := by
    field_simp
    ring
  have e2 : p ^ (β - 1) = p ^ β / p := Real.rpow_sub_one hp.ne' β
  have hpβ : 0 ≤ p ^ β := Real.rpow_nonneg hp.le β
  calc (p - δ) ^ β = p ^ β * (1 + -δ / p) ^ β := by rw [e1, Real.mul_rpow hp.le h1]
    _ ≤ p ^ β * (1 + β * (-δ / p)) := mul_le_mul_of_nonneg_left h hpβ
    _ = p ^ β - β * p ^ (β - 1) * δ := by
      rw [e2]
      field_simp
      ring

/-- A power bound for log (2 + p). -/
lemma log_two_add_le {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    Real.log (2 + p) ≤ 2 ^ ε / ε * p ^ ε := by
  have h := Real.log_le_rpow_div (show (0 : ℝ) ≤ 2 + p by linarith) hε
  have h2 : (2 + p) ^ ε ≤ (2 * p) ^ ε := Real.rpow_le_rpow (by linarith) (by linarith) hε.le
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h2
  calc Real.log (2 + p) ≤ (2 + p) ^ ε / ε := h
    _ ≤ (2 ^ ε * p ^ ε) / ε := div_le_div_of_nonneg_right h2 hε.le
    _ = 2 ^ ε / ε * p ^ ε := by ring

/-- Logarithmic resources are eventually dominated by a larger power. -/
lemma ev_budget (K₁ K₂ K₃ K₄ a γ : ℝ) (h1 : 0 ≤ K₁) (h2 : 0 ≤ K₂) (h4 : 0 < K₄) (ha : 0 ≤ a)
    (haγ : a < γ) :
    ∀ᶠ p : ℝ in atTop,
      K₁ * Real.log (2 + p) + K₂ * p ^ a * Real.log (2 + p) + K₃ ≤ K₄ * p ^ γ := by
  have hε0 : 0 < (γ - a) / 2 := by linarith
  have hA0 : 0 ≤ 2 ^ ((γ - a) / 2) / ((γ - a) / 2) := by positivity
  have hev : ∀ᶠ p : ℝ in atTop,
      ((K₁ + K₂) * (2 ^ ((γ - a) / 2) / ((γ - a) / 2)) + |K₃|) / K₄ ≤ p ^ ((γ - a) / 2) :=
    (tendsto_rpow_atTop hε0).eventually_ge_atTop _
  filter_upwards [hev, eventually_ge_atTop (2 : ℝ)] with p hpε hp2
  set ε : ℝ := (γ - a) / 2 with hε
  set A : ℝ := 2 ^ ε / ε with hA
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hlog : Real.log (2 + p) ≤ A * p ^ ε := log_two_add_le hp2 hε0
  have hpa : 0 ≤ p ^ a := Real.rpow_nonneg hp0.le a
  have e1 : p ^ a * p ^ ε = p ^ (a + ε) := (Real.rpow_add hp0 a ε).symm
  have hq1 : p ^ ε ≤ p ^ (a + ε) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hq0 : 1 ≤ p ^ (a + ε) := Real.one_le_rpow hp1 (by linarith)
  have e2 : p ^ γ = p ^ (a + ε) * p ^ ε := by
    rw [← Real.rpow_add hp0]
    congr 1
    rw [hε]
    ring
  have t1 : K₁ * Real.log (2 + p) ≤ K₁ * A * p ^ (a + ε) := by
    calc K₁ * Real.log (2 + p) ≤ K₁ * (A * p ^ ε) := mul_le_mul_of_nonneg_left hlog h1
      _ ≤ K₁ * (A * p ^ (a + ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq1 hA0) h1
      _ = K₁ * A * p ^ (a + ε) := by ring
  have t2 : K₂ * p ^ a * Real.log (2 + p) ≤ K₂ * A * p ^ (a + ε) := by
    calc K₂ * p ^ a * Real.log (2 + p) ≤ K₂ * p ^ a * (A * p ^ ε) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg h2 hpa)
      _ = K₂ * A * (p ^ a * p ^ ε) := by ring
      _ = K₂ * A * p ^ (a + ε) := by rw [e1]
  have t3 : K₃ ≤ |K₃| * p ^ (a + ε) := by
    calc K₃ ≤ |K₃| := le_abs_self K₃
      _ = |K₃| * 1 := (mul_one _).symm
      _ ≤ |K₃| * p ^ (a + ε) := mul_le_mul_of_nonneg_left hq0 (abs_nonneg _)
  have t4 : (K₁ + K₂) * A + |K₃| ≤ K₄ * p ^ ε := by
    rw [div_le_iff₀ h4] at hpε
    linarith
  have hq : 0 ≤ p ^ (a + ε) := by linarith
  have e3 : ((K₁ + K₂) * A + |K₃|) * p ^ (a + ε) =
      K₁ * A * p ^ (a + ε) + K₂ * A * p ^ (a + ε) + |K₃| * p ^ (a + ε) := by ring
  calc K₁ * Real.log (2 + p) + K₂ * p ^ a * Real.log (2 + p) + K₃
      ≤ ((K₁ + K₂) * A + |K₃|) * p ^ (a + ε) := by linarith
    _ ≤ K₄ * p ^ ε * p ^ (a + ε) := mul_le_mul_of_nonneg_right t4 hq
    _ = K₄ * p ^ γ := by rw [e2]; ring

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.H1 := by
  intro h1 h2 k hk
  obtain ⟨s, ν, c, B, D, p₀, C₁, hν, hν1, hc, hB, hD, hsrc⟩ := h1 k hk
  obtain ⟨L₀, hstep⟩ := h2 s
  set β : ℝ := 1 - ν / 2 with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hβ1 : β < 1 := by rw [hβdef]; linarith
  have hβq : 1 / 4 < β := by rw [hβdef]; linarith
  have hK1 : (0 : ℝ) ≤ ((2 * s * s + 1 : ℕ) : ℝ) * B := by positivity
  have hK1' : (0 : ℝ) ≤ ((2 * s * s : ℕ) : ℝ) * B := by positivity
  have hE2 := ev_budget (((2 * s * s + 1 : ℕ) : ℝ) * B) D L₀ 1 (1 / 4) β hK1 hD one_pos
    (by norm_num) hβq
  have hE4 := ev_budget (((2 * s * s : ℕ) : ℝ) * B) 0 L₀ (β * c) 0 (ν / 2) hK1' le_rfl
    (mul_pos hβ0 hc) le_rfl (by linarith)
  have hE3a : ∀ᶠ p : ℝ in atTop, 1 ≤ c * p ^ ν := by
    filter_upwards [(tendsto_rpow_atTop hν).eventually_ge_atTop (1 / c)] with p hp
    rw [div_le_iff₀ hc] at hp
    linarith
  have hE3b : ∀ᶠ p : ℝ in atTop, c * p ^ ν + 2 ≤ p := by
    filter_upwards [(tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ν)).eventually_ge_atTop
      (2 * c), eventually_ge_atTop (4 : ℝ)] with p hp1 hp4
    have hp0 : 0 < p := by linarith
    have e : p ^ ν * p ^ (1 - ν) = p := by
      rw [← Real.rpow_add hp0, show ν + (1 - ν) = 1 by ring, Real.rpow_one]
    have hpν : 0 ≤ p ^ ν := Real.rpow_nonneg hp0.le ν
    have h2c : c * p ^ ν * 2 ≤ p := by
      calc c * p ^ ν * 2 = p ^ ν * (2 * c) := by ring
        _ ≤ p ^ ν * p ^ (1 - ν) := mul_le_mul_of_nonneg_left hp1 hpν
        _ = p := e
    linarith
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop p₀).and (hE2.and (hE4.and (hE3a.and hE3b))))
  refine ⟨β, 1, max T₀ 2, max C₁ 0, hβ0, hβ1, one_pos, ?_⟩
  intro R hR N S hN hS hcard hfree p hTp hinv
  have hpT : T₀ ≤ p := le_trans (le_max_left _ _) hTp.le
  obtain ⟨hp₀, hb2, hb4, hc1, hc2⟩ := hT₀ p hpT
  have hp2 : (2 : ℝ) ≤ p := le_max_left _ _
  have hp0 : 0 < p := by linarith
  have hRC : C₁ ≤ R := le_trans (le_max_left _ _) hR
  have hR0 : 0 ≤ R := le_trans (le_max_right _ _) hR
  have hinv' : p ^ β + R ≤ Real.log (Real.log (N : ℝ)) := by linarith
  obtain ⟨d, M, a, q, U, G, w, P, Φ, L, hw, hmono, hP, hΦ, hsupp, hlip, hq, hprog, hU, hM, hL,
    hd, hUV, hG, hGc, hcorr⟩ := hsrc N S p hN hS hcard hfree rfl hp₀ (by linarith)
  have e5 : ((2 * s * s + 1 : ℕ) : ℝ) * (B * Real.log (2 + p)) =
      ((2 * s * s + 1 : ℕ) : ℝ) * B * Real.log (2 + p) := by ring
  have hsize : L₀ + ((2 * s * s + 1 : ℕ) : ℝ) * (B * Real.log (2 + p)) +
      D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) ≤ Real.log (Real.log (N : ℝ)) := by
    linarith
  obtain ⟨a', q', M', hq', hM', hprog', hll, hdens, hp'⟩ :=
    hstep N S p d M a q U (B * Real.log (2 + p)) (D * p ^ (1 / 4 : ℝ) * Real.log (2 + p)) G
      (c * p ^ ν) w P Φ L hw hmono hP hΦ hsupp hlip hN hS hcard rfl hq hprog hU hM hL hd hUV
      hsize hG hGc (by linarith) hcorr
  refine ⟨a', q', M', hq', hM', hprog', ?_⟩
  intro U' p'
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hScard : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcard
  have hα : 0 < (S.card : ℝ) / (N : ℝ) := div_pos hScard hNpos
  have hGα : 0 < G * ((S.card : ℝ) / (N : ℝ)) := mul_pos hG hα
  have hdens' : G * ((S.card : ℝ) / (N : ℝ)) < (U'.card : ℝ) / (M' : ℝ) := hdens
  have hM'pos : (0 : ℝ) < (M' : ℝ) := by
    have : (2 : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hM'
    linarith
  have hpos : 0 < U'.card := by
    have h0 : 0 < (U'.card : ℝ) / (M' : ℝ) := lt_trans hGα hdens'
    have h0' : (0 : ℝ) < (U'.card : ℝ) := by
      by_contra hcon
      push Not at hcon
      have : (U'.card : ℝ) / (M' : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcon hM'pos.le
      linarith
    exact_mod_cast h0'
  have hp'le : p' ≤ p - c * p ^ ν := hp'
  have hp'2 : (2 : ℝ) ≤ p' := le_max_left _ _
  refine ⟨hpos, by linarith, ?_⟩
  have hδ0 : 0 ≤ c * p ^ ν := by
    have := Real.rpow_nonneg hp0.le ν
    positivity
  have hconc := concave_drop hp0 hδ0 (by linarith) hβ0.le hβ1.le
  have hmono' : p' ^ β ≤ (p - c * p ^ ν) ^ β := Real.rpow_le_rpow (by linarith) hp'le hβ0.le
  have hexp : p ^ (β - 1) * (c * p ^ ν) = c * p ^ (ν / 2) := by
    rw [mul_left_comm, ← Real.rpow_add hp0]
    congr 2
    rw [hβdef]
    ring
  have e3 : β * p ^ (β - 1) * (c * p ^ ν) = β * c * p ^ (ν / 2) := by
    rw [mul_assoc, hexp]
    ring
  have e4 : ((2 * s * s : ℕ) : ℝ) * (B * Real.log (2 + p)) =
      ((2 * s * s : ℕ) : ℝ) * B * Real.log (2 + p) := by ring
  have e6 : (0 : ℝ) * p ^ (0 : ℝ) * Real.log (2 + p) = 0 := by ring
  linarith

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R3
