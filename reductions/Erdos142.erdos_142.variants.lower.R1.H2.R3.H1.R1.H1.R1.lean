import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R1 of step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1
-- Credit: @DPS0340

/-!
# Varnavides supersaturation reduction for cyclic k-AP counting in ZMod p

We reduce the cyclic ordered k-AP counting bound (`#solutions > p` above a stretched-exponential
density threshold in `ZMod p`) to two independent components:
- `H1`: existence of a single nontrivial k-term arithmetic progression in dense subsets of `[1, M]`
  above a stretched-exponential density threshold;
- `H2`: Varnavides's affine-window supersaturation inequality in `ZMod p`, turning any interval
  threshold at scale `M < p` into at least `(α / 2) * p * (p - 1) / M^2` nontrivial ordered k-APs.

Choosing `M = ⌊p^(1/4)⌋` and halving the exponent `ε₁ = min ε₀ 1` to `ε = ε₁ / 2` makes `H1`
applicable on `[1, M]` and forces the Varnavides lower bound strictly above `p` for all large `p`,
while raising `C` makes all finitely many smaller primes vacuous.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R1

open Finset Filter Real
open scoped Topology

/-- Existence of a single nontrivial k-term arithmetic progression in any subset of [1, M]
exceeding a stretched-exponential density threshold. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
    ∀ (M : ℕ) (S : Finset ℕ), 2 ≤ M → S ⊆ Finset.Icc 1 M →
      C * (M : ℝ) * Real.exp (-c * Real.log (M : ℝ) ^ ε) < (S.card : ℝ) →
      ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- Varnavides supersaturation on ZMod p: an interval k-AP threshold at length M < p yields
at least (α / 2) * p * (p - 1) / M^2 nontrivial ordered k-APs in any subset A of ZMod p
of density at least α. -/
def H2 : Prop :=
  ∀ (k M p : ℕ) (hp : p.Prime), have : NeZero p := ⟨hp.ne_zero⟩
    2 ≤ k → 2 ≤ M → M < p → ∀ (α : ℝ) (A : Finset (ZMod p)),
      0 < α → α * (p : ℝ) ≤ (A.card : ℝ) →
      (∀ S : Finset ℕ, S ⊆ Finset.Icc 1 M → (α / 2) * (M : ℝ) < (S.card : ℝ) →
        ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      (α / 2) * (p : ℝ) * ((p : ℝ) - 1) ≤ (M : ℝ) ^ 2 *
        ((Finset.univ.filter fun u : ZMod p × ZMod p =>
          u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card : ℝ)

lemma eventually_params (C₀ c₀ ε₁ : ℝ) (hC₀ : 0 < C₀) (hc₀ : 0 < c₀) (hε₁ : 0 < ε₁)
    (hε₁_le : ε₁ ≤ 1) :
    ∃ P₀ : ℕ, 256 ≤ P₀ ∧ ∀ p : ℕ, P₀ ≤ p →
      let M := ⌊(p : ℝ) ^ (1 / 4 : ℝ)⌋₊
      3 ≤ M ∧ M < p ∧
      (1 : ℝ) ≤ Real.log (M : ℝ) ∧
      (1 / 8 : ℝ) * Real.log (p : ℝ) ≤ Real.log (M : ℝ) ∧
      Real.log (2 * C₀) + Real.log (p : ℝ) ^ (ε₁ / 2) ≤
        c₀ * ((1 / 8 : ℝ) * Real.log (p : ℝ)) ^ ε₁ ∧
      Real.log 4 + Real.log (p : ℝ) ^ (ε₁ / 2) < (1 / 2 : ℝ) * Real.log (p : ℝ) := by
  have hlog : Tendsto (fun p : ℕ => Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hεhalf : 0 < ε₁ / 2 := half_pos hε₁
  have hdiff1 : 0 < ε₁ - ε₁ / 2 := by linarith
  have hdiff2 : 0 < 1 - ε₁ / 2 := by linarith
  have hlim1 : Tendsto (fun x : ℝ => Real.log (2 * C₀) * x ^ (-ε₁) + x ^ (-(ε₁ - ε₁ / 2)))
      atTop (𝓝 0) := by
    have ha := (tendsto_rpow_neg_atTop hε₁).const_mul (Real.log (2 * C₀))
    have hb := tendsto_rpow_neg_atTop hdiff1
    simpa using ha.add hb
  have hlim2 : Tendsto (fun x : ℝ => Real.log 4 * x ^ (-(1 : ℝ)) + x ^ (-(1 - ε₁ / 2)))
      atTop (𝓝 0) := by
    have ha := (tendsto_rpow_neg_atTop zero_lt_one).const_mul (Real.log 4)
    have hb := tendsto_rpow_neg_atTop hdiff2
    simpa using ha.add hb
  have hc8 : 0 < c₀ * (1 / 8 : ℝ) ^ ε₁ := mul_pos hc₀ (Real.rpow_pos_of_pos (by norm_num) ε₁)
  have hev : ∀ᶠ p : ℕ in atTop,
      256 ≤ p ∧
      8 ≤ Real.log (p : ℝ) ∧
      Real.log (2 * C₀) * Real.log (p : ℝ) ^ (-ε₁) +
        Real.log (p : ℝ) ^ (-(ε₁ - ε₁ / 2)) < c₀ * (1 / 8 : ℝ) ^ ε₁ ∧
      Real.log 4 * Real.log (p : ℝ) ^ (-(1 : ℝ)) +
        Real.log (p : ℝ) ^ (-(1 - ε₁ / 2)) < (1 / 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop (256 : ℕ),
      hlog.eventually (eventually_ge_atTop (8 : ℝ)),
      (hlim1.comp hlog).eventually (gt_mem_nhds hc8),
      (hlim2.comp hlog).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hev
  refine ⟨max P₀ 256, le_max_right _ _, fun p hp => ?_⟩
  obtain ⟨hp256, hlog8, hineq1, hineq2⟩ := hP₀ p ((le_max_left _ _).trans hp)
  have hpR : (256 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp256
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogpos : 0 < Real.log (p : ℝ) := by linarith
  set M := ⌊(p : ℝ) ^ (1 / 4 : ℝ)⌋₊ with hMdef
  have hp18 : (2 : ℝ) ≤ (p : ℝ) ^ (1 / 8 : ℝ) := by
    have h28 : (2 : ℝ) ^ (8 : ℝ) = (256 : ℝ) := by norm_num
    have hle : (2 : ℝ) ^ (8 : ℝ) ≤ (p : ℝ) := by linarith
    calc (2 : ℝ) = ((2 : ℝ) ^ (8 : ℝ)) ^ (1 / 8 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (p : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (by positivity) hle (by norm_num)
  have hp14 : (4 : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) := by
    have hsq : (p : ℝ) ^ (1 / 4 : ℝ) = ((p : ℝ) ^ (1 / 8 : ℝ)) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hppos.le]; norm_num
    rw [hsq]
    nlinarith
  have hMge3 : 3 ≤ M := by
    rw [hMdef]
    exact Nat.le_floor (by linarith)
  have hMlt : M < p := by
    have hle1 : (M : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) := Nat.floor_le (by positivity)
    have hlt2 : (p : ℝ) ^ (1 / 4 : ℝ) < (p : ℝ) := by
      calc (p : ℝ) ^ (1 / 4 : ℝ) < (p : ℝ) ^ (1 : ℝ) :=
            Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
        _ = (p : ℝ) := Real.rpow_one _
    exact_mod_cast (hle1.trans_lt hlt2)
  have hp18_le_M : (p : ℝ) ^ (1 / 8 : ℝ) ≤ (M : ℝ) := by
    have hlt_floor : (p : ℝ) ^ (1 / 4 : ℝ) - 1 < (M : ℝ) := by
      linarith [Nat.lt_floor_add_one ((p : ℝ) ^ (1 / 4 : ℝ))]
    have hsq : (p : ℝ) ^ (1 / 4 : ℝ) = ((p : ℝ) ^ (1 / 8 : ℝ)) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hppos.le]; norm_num
    nlinarith
  have hlogM_ge : (1 / 8 : ℝ) * Real.log (p : ℝ) ≤ Real.log (M : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hppos (1 / 8 : ℝ)) hp18_le_M
    rwa [Real.log_rpow hppos] at h
  have hlogM1 : (1 : ℝ) ≤ Real.log (M : ℝ) := by linarith
  have hgoal1 : Real.log (2 * C₀) + Real.log (p : ℝ) ^ (ε₁ / 2) ≤
      c₀ * ((1 / 8 : ℝ) * Real.log (p : ℝ)) ^ ε₁ := by
    have hxe : 0 < Real.log (p : ℝ) ^ ε₁ := Real.rpow_pos_of_pos hlogpos ε₁
    have hmul := mul_le_mul_of_nonneg_right hineq1.le hxe.le
    have hlhs : (Real.log (2 * C₀) * Real.log (p : ℝ) ^ (-ε₁) +
        Real.log (p : ℝ) ^ (-(ε₁ - ε₁ / 2))) * Real.log (p : ℝ) ^ ε₁ =
        Real.log (2 * C₀) + Real.log (p : ℝ) ^ (ε₁ / 2) := by
      rw [add_mul, mul_assoc, ← Real.rpow_add hlogpos, ← Real.rpow_add hlogpos]
      have h1 : -ε₁ + ε₁ = 0 := by ring
      have h2 : -(ε₁ - ε₁ / 2) + ε₁ = ε₁ / 2 := by ring
      rw [h1, h2, Real.rpow_zero, mul_one]
    have hrhs : c₀ * (1 / 8 : ℝ) ^ ε₁ * Real.log (p : ℝ) ^ ε₁ =
        c₀ * ((1 / 8 : ℝ) * Real.log (p : ℝ)) ^ ε₁ := by
      rw [Real.mul_rpow (by norm_num) hlogpos.le, mul_assoc]
    linarith
  have hgoal2 : Real.log 4 + Real.log (p : ℝ) ^ (ε₁ / 2) < (1 / 2 : ℝ) * Real.log (p : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hineq2 hlogpos
    have hlhs : (Real.log 4 * Real.log (p : ℝ) ^ (-(1 : ℝ)) +
        Real.log (p : ℝ) ^ (-(1 - ε₁ / 2))) * Real.log (p : ℝ) =
        Real.log 4 + Real.log (p : ℝ) ^ (ε₁ / 2) := by
      conv_lhs =>
        arg 2
        rw [← Real.rpow_one (Real.log (p : ℝ))]
      rw [add_mul, mul_assoc, ← Real.rpow_add hlogpos, ← Real.rpow_add hlogpos]
      have h1 : -(1 : ℝ) + 1 = 0 := by ring
      have h2 : -(1 - ε₁ / 2) + 1 = ε₁ / 2 := by ring
      rw [h1, h2, Real.rpow_zero, mul_one]
    linarith
  exact ⟨hMge3, hMlt, hlogM1, hlogM_ge, hgoal1, hgoal2⟩

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H1 := by
  intro h1 h2 k hk
  obtain ⟨C₀, c₀, ε₀, hC₀, hc₀, hε₀, hInt⟩ := h1 k hk
  set ε₁ : ℝ := min ε₀ 1 with hε₁def
  have hε₁_pos : 0 < ε₁ := lt_min hε₀ zero_lt_one
  have hε₁_le1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁_le0 : ε₁ ≤ ε₀ := min_le_left _ _
  set ε : ℝ := ε₁ / 2 with hεdef
  have hε_pos : 0 < ε := half_pos hε₁_pos
  obtain ⟨P₀, hP₀256, hP₀⟩ := eventually_params C₀ c₀ ε₁ hC₀ hc₀ hε₁_pos hε₁_le1
  set C : ℝ := max 1 (Real.exp (Real.log (P₀ : ℝ) ^ ε)) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  refine ⟨C, 1, ε, hC_pos, zero_lt_one, hε_pos, ?_⟩
  intro p hp
  have : NeZero p := ⟨hp.ne_zero⟩
  intro A hA
  have hp2 : 2 ≤ p := hp.two_le
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  by_cases hlt : p < P₀
  · exfalso
    have hlog_le : Real.log (p : ℝ) ≤ Real.log (P₀ : ℝ) :=
      Real.log_le_log hp_pos (by exact_mod_cast hlt.le)
    have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    have hpow_le : Real.log (p : ℝ) ^ ε ≤ Real.log (P₀ : ℝ) ^ ε :=
      Real.rpow_le_rpow hlog_nn hlog_le hε_pos.le
    have hexp_le : Real.exp (Real.log (p : ℝ) ^ ε) ≤ C :=
      (Real.exp_le_exp.mpr hpow_le).trans (le_max_right _ _)
    have hge1 : 1 ≤ C * Real.exp (-1 * Real.log (p : ℝ) ^ ε) := by
      have hpos := Real.exp_pos (Real.log (p : ℝ) ^ ε)
      have hmul := mul_le_mul_of_nonneg_right hexp_le (Real.exp_pos (-Real.log (p : ℝ) ^ ε)).le
      have hcan : Real.exp (Real.log (p : ℝ) ^ ε) * Real.exp (-Real.log (p : ℝ) ^ ε) = 1 := by
        rw [← Real.exp_add]; simp
      have hneg : -1 * Real.log (p : ℝ) ^ ε = -Real.log (p : ℝ) ^ ε := by ring
      rw [hneg]
      linarith
    have hA_le : (A.card : ℝ) ≤ (p : ℝ) := by
      have hcard : A.card ≤ Fintype.card (ZMod p) := Finset.card_le_univ A
      rw [ZMod.card] at hcard
      exact_mod_cast hcard
    have hp_le : (p : ℝ) ≤ C * (p : ℝ) * Real.exp (-1 * Real.log (p : ℝ) ^ ε) := by
      have := mul_le_mul_of_nonneg_left hge1 hp_pos.le
      linarith
    linarith
  · push_neg at hlt
    obtain ⟨hMge3, hMlt, hlogM1, hlogM_ge, hgoal1, hgoal2⟩ := hP₀ p hlt
    set M := ⌊(p : ℝ) ^ (1 / 4 : ℝ)⌋₊ with hMdef
    set α : ℝ := (A.card : ℝ) / (p : ℝ) with hαdef
    have hα_gt : C * Real.exp (-Real.log (p : ℝ) ^ ε) < α := by
      rw [hαdef, lt_div_iff₀ hp_pos]
      have hneg : -1 * Real.log (p : ℝ) ^ ε = -Real.log (p : ℝ) ^ ε := by ring
      rw [hneg] at hA
      linarith
    have hα_exp : Real.exp (-Real.log (p : ℝ) ^ ε) < α := by
      have : Real.exp (-Real.log (p : ℝ) ^ ε) ≤ C * Real.exp (-Real.log (p : ℝ) ^ ε) := by
        nlinarith [Real.exp_pos (-Real.log (p : ℝ) ^ ε)]
      linarith
    have hα_pos : 0 < α := (Real.exp_pos _).trans hα_exp
    have hαp : α * (p : ℝ) ≤ (A.card : ℝ) := by
      rw [hαdef, div_mul_cancel₀ _ hp_pos.ne']
    have hthresh : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 M → (α / 2) * (M : ℝ) < (S.card : ℝ) →
        ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
      intro S hS hScard
      apply hInt M S (by omega) hS
      have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
      have hpow0 : Real.log (M : ℝ) ^ ε₁ ≤ Real.log (M : ℝ) ^ ε₀ :=
        Real.rpow_le_rpow_of_exponent_le hlogM1 hε₁_le0
      have hpow1 : ((1 / 8 : ℝ) * Real.log (p : ℝ)) ^ ε₁ ≤ Real.log (M : ℝ) ^ ε₁ :=
        Real.rpow_le_rpow (by positivity) hlogM_ge hε₁_pos.le
      have hexp1 : 2 * C₀ * Real.exp (-c₀ * Real.log (M : ℝ) ^ ε₀) ≤
          Real.exp (-Real.log (p : ℝ) ^ ε) := by
        have h2C : 0 < 2 * C₀ := by positivity
        rw [← Real.exp_log h2C, ← Real.exp_add, Real.exp_le_exp]
        have h1 : c₀ * ((1 / 8 : ℝ) * Real.log (p : ℝ)) ^ ε₁ ≤ c₀ * Real.log (M : ℝ) ^ ε₀ :=
          mul_le_mul_of_nonneg_left (hpow1.trans hpow0) hc₀.le
        linarith
      have hC0_le : C₀ * Real.exp (-c₀ * Real.log (M : ℝ) ^ ε₀) < α / 2 := by linarith
      calc C₀ * (M : ℝ) * Real.exp (-c₀ * Real.log (M : ℝ) ^ ε₀)
          = (C₀ * Real.exp (-c₀ * Real.log (M : ℝ) ^ ε₀)) * (M : ℝ) := by ring
        _ < (α / 2) * (M : ℝ) := mul_lt_mul_of_pos_right hC0_le hMpos
        _ < (S.card : ℝ) := hScard
    have hvar := h2 k M p hp (by omega) (by omega) hMlt α A hα_pos hαp hthresh
    have hMsq : (M : ℝ) ^ 2 ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
      have hMle : (M : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) := Nat.floor_le (by positivity)
      calc (M : ℝ) ^ 2 ≤ ((p : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg M) hMle 2
        _ = (p : ℝ) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]; norm_num
    have hhalf_lt : (p : ℝ) ^ (1 / 2 : ℝ) < (α / 2) * ((p : ℝ) - 1) := by
      have hp_half : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
        linarith
      have h4exp : 4 * Real.exp (Real.log (p : ℝ) ^ ε) < (p : ℝ) ^ (1 / 2 : ℝ) := by
        have h4 : (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
        rw [h4, ← Real.exp_add, Real.rpow_def_of_pos hp_pos, mul_comm (Real.log (p : ℝ))]
        exact Real.exp_lt_exp.mpr hgoal2
      have h1 : (p : ℝ) ^ (1 / 2 : ℝ) * (4 * Real.exp (Real.log (p : ℝ) ^ ε)) <
          (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_left h4exp (Real.rpow_pos_of_pos hp_pos _)
      have hsq : (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) = (p : ℝ) := by
        rw [← Real.rpow_add hp_pos]; norm_num
      rw [hsq] at h1
      have h2 : (p : ℝ) ^ (1 / 2 : ℝ) < (p : ℝ) / 4 * Real.exp (-Real.log (p : ℝ) ^ ε) := by
        have hcan : Real.exp (Real.log (p : ℝ) ^ ε) * Real.exp (-Real.log (p : ℝ) ^ ε) = 1 := by
          rw [← Real.exp_add]; simp
        have hmul := mul_lt_mul_of_pos_right h1 (Real.exp_pos (-Real.log (p : ℝ) ^ ε))
        have hmul4 : 4 * ((p : ℝ) ^ (1 / 2 : ℝ)) < (p : ℝ) * Real.exp (-Real.log (p : ℝ) ^ ε) := by
          calc 4 * ((p : ℝ) ^ (1 / 2 : ℝ))
              = (p : ℝ) ^ (1 / 2 : ℝ) * (4 * (Real.exp (Real.log (p : ℝ) ^ ε) *
                  Real.exp (-Real.log (p : ℝ) ^ ε))) := by rw [hcan]; ring
            _ = (p : ℝ) ^ (1 / 2 : ℝ) * (4 * Real.exp (Real.log (p : ℝ) ^ ε)) *
                  Real.exp (-Real.log (p : ℝ) ^ ε) := by ring
            _ < (p : ℝ) * Real.exp (-Real.log (p : ℝ) ^ ε) := hmul
        linarith
      calc (p : ℝ) ^ (1 / 2 : ℝ)
          < (p : ℝ) / 4 * Real.exp (-Real.log (p : ℝ) ^ ε) := h2
        _ < (p : ℝ) / 4 * α := mul_lt_mul_of_pos_left hα_exp (by positivity)
        _ = (α / 2) * ((p : ℝ) / 2) := by ring
        _ ≤ (α / 2) * ((p : ℝ) - 1) := mul_le_mul_of_nonneg_left hp_half (by positivity)
    have hMsq_pos : (0 : ℝ) < (M : ℝ) ^ 2 := by
      have : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
      positivity
    have hlt_nontriv : (p : ℝ) <
        ((Finset.univ.filter fun u : ZMod p × ZMod p =>
          u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card : ℝ) := by
      have h1 : (M : ℝ) ^ 2 * (p : ℝ) < (M : ℝ) ^ 2 *
          ((Finset.univ.filter fun u : ZMod p × ZMod p =>
            u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card : ℝ) := by
        calc (M : ℝ) ^ 2 * (p : ℝ)
            ≤ (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) := mul_le_mul_of_nonneg_right hMsq hp_pos.le
          _ < (α / 2) * ((p : ℝ) - 1) * (p : ℝ) := mul_lt_mul_of_pos_right hhalf_lt hp_pos
          _ = (α / 2) * (p : ℝ) * ((p : ℝ) - 1) := by ring
          _ ≤ (M : ℝ) ^ 2 * ((Finset.univ.filter fun u : ZMod p × ZMod p =>
                u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card : ℝ) := hvar
      exact lt_of_mul_lt_mul_left h1 hMsq_pos.le
    have hnat : p < (Finset.univ.filter fun u : ZMod p × ZMod p =>
        u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card := by
      exact_mod_cast hlt_nontriv
    have hsub : (Finset.univ.filter fun u : ZMod p × ZMod p =>
          u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A) ⊆
        (Finset.univ.filter fun u : ZMod p × ZMod p =>
          ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.2⟩
    exact lt_of_lt_of_le hnat (Finset.card_le_card hsub)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R1
