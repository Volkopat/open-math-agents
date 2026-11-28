import OMAReductions.R_Erdos360_erdos_360_R1_H4_R1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SelbergSieve

/-! Proof of `Erdos360.erdos_360.R1.H4.R1.H1`. -/

section -- Erdos360_H1_part1.lean
open Finset Filter Real Nat ArithmeticFunction
open scoped BigOperators Chebyshev Classical

namespace Erdos360H1Part1

/- ### Section 1: Basic bounds on `Nat.nth Nat.Prime` -/

lemma nth_prime_ge_add_two (k : ℕ) : k + 2 ≤ Nat.nth Nat.Prime k := by
  induction k with
  | zero =>
    rw [Nat.nth_prime_zero_eq_two]
  | succ k ih =>
    have hlt : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self k)
    omega

lemma nth_prime_gt_of_pos {r : ℕ} (hr : 1 ≤ r) : r < Nat.nth Nat.Prime (r - 1) := by
  have h := nth_prime_ge_add_two (r - 1)
  omega

lemma mem_first_primes_iff {r p : ℕ} (hr : 1 ≤ r) (hp : p.Prime) :
    p ∈ (Finset.range r).image (Nat.nth Nat.Prime) ↔ p ≤ Nat.nth Nat.Prime (r - 1) := by
  constructor
  · intro hmem
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
    have hir : i ≤ r - 1 := by
      rw [Finset.mem_range] at hi; omega
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hir
  · intro hle
    have hcnt : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
    have hlt : Nat.count Nat.Prime p < r := by
      by_contra hge
      have hge' : r - 1 < Nat.count Nat.Prime p := by omega
      have hlt_p : Nat.nth Nat.Prime (r - 1) < Nat.nth Nat.Prime (Nat.count Nat.Prime p) :=
        Nat.nth_strictMono Nat.infinite_setOfPred_prime hge'
      rw [hcnt] at hlt_p
      omega
    exact Finset.mem_image.mpr ⟨Nat.count Nat.Prime p, Finset.mem_range.mpr hlt, hcnt⟩

lemma first_primes_eq_filter_Icc {r : ℕ} (hr : 1 ≤ r) :
    (Finset.range r).image (Nat.nth Nat.Prime) =
      (Finset.Icc 1 (Nat.nth Nat.Prime (r - 1))).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    have hp := Nat.prime_nth_prime i
    refine ⟨⟨hp.one_le, ?_⟩, hp⟩
    exact (mem_first_primes_iff hr hp).mp h
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact (mem_first_primes_iff hr hp).mpr hle

private lemma tendsto_log_div_id : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
  (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero.congr' (by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x _; rw [Real.rpow_one])

private lemma tendsto_log_div_rpow_half :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (nhds 0) :=
  (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero

private lemma tendsto_log_sq_div_id :
    Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (nhds 0) := by
  have hsq : Tendsto (fun x : ℝ => (Real.log x / x ^ (1 / 2 : ℝ)) ^ 2) atTop (nhds 0) := by
    simpa using tendsto_log_div_rpow_half.pow 2
  refine hsq.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  rw [div_pow, ← Real.rpow_natCast (x ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hx.le]
  norm_num

lemma nth_prime_le_four_mul_log :
    ∀ᶠ r : ℕ in atTop, (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ 4 * (r : ℝ) * Real.log (r : ℝ) := by
  have hlog : ∀ᶠ r : ℕ in atTop, Real.log (r : ℝ) ≤ (r : ℝ) ∧ (10 : ℝ) ≤ (r : ℝ) ∧
      Real.log (4 * (r : ℝ) * Real.log (r : ℝ) + 1) ≤ (r : ℝ) * Real.log 2 := by
    have h1 : ∀ᶠ r : ℕ in atTop, (10 : ℝ) ≤ (r : ℝ) :=
      Filter.eventually_atTop.mpr ⟨10, fun n hn => by exact_mod_cast hn⟩
    have h3 : ∀ᶠ r : ℕ in atTop, Real.log (4 * (r : ℝ) ^ 2 + 1) ≤ (r : ℝ) * Real.log 2 := by
      have hlim : Tendsto (fun x : ℝ => Real.log (4 * x ^ 2 + 1) / x) atTop (nhds 0) := by
        have h_eq : ∀ᶠ x : ℝ in atTop,
            Real.log (4 * x ^ 2 + 1) / x ≤ (Real.log (5 * x ^ 2)) / x := by
          filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
          exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (by nlinarith)) (by linarith)
        have h_top : Tendsto (fun x : ℝ => Real.log (5 * x ^ 2) / x) atTop (nhds 0) := by
          have hlog5 : Tendsto (fun x : ℝ => Real.log 5 / x) atTop (nhds 0) :=
            tendsto_const_nhds.div_atTop tendsto_id
          have hlogx : Tendsto (fun x : ℝ => 2 * (Real.log x / x)) atTop (nhds 0) := by
            simpa using tendsto_log_div_id.const_mul 2
          have hsum : Tendsto (fun x : ℝ => Real.log 5 / x + 2 * (Real.log x / x)) atTop (nhds 0) := by
            simpa using hlog5.add hlogx
          refine hsum.congr' ?_
          filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          push_cast; ring
        have h_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log (4 * x ^ 2 + 1) / x := by
          filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
          exact div_nonneg (Real.log_nonneg (by nlinarith)) (by linarith)
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_top h_nonneg h_eq
      have hev := (hlim.comp tendsto_natCast_atTop_atTop).eventually
        (gt_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
      filter_upwards [hev, Filter.eventually_ge_atTop 1] with r hr hr1
      have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
      exact ((div_lt_iff₀ hrpos).mp hr).le.trans (by ring_nf; exact le_rfl)
    filter_upwards [h1, h3] with r hr10 hr3
    have hrpos : (0 : ℝ) < r := by linarith
    have hlog_le : Real.log (r : ℝ) ≤ (r : ℝ) := (Real.log_le_sub_one_of_pos hrpos).trans (by linarith)
    refine ⟨hlog_le, hr10, ?_⟩
    have hlog_nonneg : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by linarith)
    have hle : 4 * (r : ℝ) * Real.log (r : ℝ) + 1 ≤ 4 * (r : ℝ) ^ 2 + 1 := by nlinarith
    exact (Real.log_le_log (by positivity) hle).trans hr3
  have hlog2 : ∀ᶠ r : ℕ in atTop,
      Real.log (4 * (r : ℝ) * Real.log (r : ℝ)) ≤ 2 * Real.log (r : ℝ) := by
    have hlim : Tendsto (fun r : ℕ => Real.log (4 * Real.log (r : ℝ)) / Real.log (r : ℝ)) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℝ => Real.log (4 * x) / x) atTop (nhds 0) := by
        have h4 : Tendsto (fun x : ℝ => Real.log 4 / x) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have hsum : Tendsto (fun x : ℝ => Real.log 4 / x + Real.log x / x) atTop (nhds 0) := by
          simpa using h4.add tendsto_log_div_id
        refine hsum.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
        rw [Real.log_mul (by norm_num) hx.ne']; ring
      exact h1.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hev := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hev, Filter.eventually_ge_atTop 10] with r hr hr10
    have hr1 : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
    have hlogr_pos : 0 < Real.log (r : ℝ) := Real.log_pos hr1
    have h1 := (div_lt_iff₀ hlogr_pos).mp hr
    rw [show 4 * (r : ℝ) * Real.log (r : ℝ) = (r : ℝ) * (4 * Real.log (r : ℝ)) by ring,
      Real.log_mul (by linarith) (by positivity)]
    linarith
  filter_upwards [hlog, hlog2, Filter.eventually_ge_atTop 100] with r ⟨_, hr10, hlog_big⟩ hlog_2 hr100
  set X : ℝ := 4 * (r : ℝ) * Real.log (r : ℝ)
  set N : ℕ := ⌊X⌋₊
  have hrpos : (0 : ℝ) < r := by linarith
  have hlogr_ge : (1 : ℝ) ≤ Real.log (r : ℝ) := by
    have : Real.exp 1 ≤ (r : ℝ) := (Real.exp_one_lt_d9.le).trans (by linarith)
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
  have hlogr_ne : Real.log (r : ℝ) ≠ 0 := by linarith
  have hX_ge : 4 * (r : ℝ) ≤ X := by dsimp [X]; nlinarith
  have hN_le_X : (N : ℝ) ≤ X := Nat.floor_le (by positivity)
  have hX_lt_N1 : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
  have hN_ge : 3 * (r : ℝ) ≤ (N : ℝ) := by linarith
  have hN_ge2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN_le : Real.log (N : ℝ) ≤ 2 * Real.log (r : ℝ) :=
    (Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) hN_le_X).trans hlog_2
  have hpi := Chebyshev.pi_ge N
  have hlog2_gt : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hnum : (2 : ℝ) * (r : ℝ) * Real.log (r : ℝ) ≤ (N : ℝ) * Real.log 2 - Real.log ((N : ℝ) + 1) := by
    have hlogN1 : Real.log ((N : ℝ) + 1) ≤ (r : ℝ) * Real.log 2 := by
      have : (N : ℝ) + 1 ≤ X + 1 := by linarith
      exact (Real.log_le_log (by positivity) this).trans hlog_big
    have hN_gt : 3.9 * (r : ℝ) * Real.log (r : ℝ) ≤ (N : ℝ) := by
      have : (1 : ℝ) ≤ 0.1 * (r : ℝ) * Real.log (r : ℝ) := by nlinarith
      linarith
    have h1 : 3.9 * 0.69 * (r : ℝ) * Real.log (r : ℝ) ≤ (N : ℝ) * Real.log 2 := by nlinarith
    have h2 : (r : ℝ) * Real.log 2 ≤ 0.69 * (r : ℝ) * Real.log (r : ℝ) + 0.01 * (r : ℝ) * Real.log (r : ℝ) := by
      have : Real.log 2 < 0.70 := by have := Real.log_two_lt_d9; linarith
      nlinarith
    nlinarith
  have hpi_ge_r : (r : ℝ) ≤ (Nat.primeCounting N : ℝ) := by
    calc (r : ℝ) = (2 * (r : ℝ) * Real.log (r : ℝ)) / (2 * Real.log (r : ℝ)) := by
            field_simp [hlogr_ne]
      _ ≤ ((N : ℝ) * Real.log 2 - Real.log ((N : ℝ) + 1)) / (2 * Real.log (r : ℝ)) :=
            div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ ((N : ℝ) * Real.log 2 - Real.log ((N : ℝ) + 1)) / Real.log (N : ℝ) := by
            apply div_le_div_of_nonneg_left (by nlinarith) hlogN_pos hlogN_le
      _ ≤ (Nat.primeCounting N : ℝ) := hpi
  have hpi_nat : r ≤ Nat.primeCounting N := by exact_mod_cast hpi_ge_r
  have hcnt_lt : r - 1 < Nat.count Nat.Prime (N + 1) := by
    change r ≤ Nat.count Nat.Prime (N + 1) at hpi_nat
    omega
  have hnth_le : Nat.nth Nat.Prime (r - 1) ≤ N := by
    by_contra hgt
    have hleN1 : N + 1 ≤ Nat.nth Nat.Prime (r - 1) := by omega
    have hmono := Nat.count_monotone Nat.Prime hleN1
    rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at hmono
    omega
  exact (by exact_mod_cast hnth_le : (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ (N : ℝ)).trans hN_le_X

/- ### Section 2: Chebyshev 5-term Identity & Sharp Dyadic Prime Lower Bound -/

private noncomputable def T_nat (N : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 N, Real.log (k : ℝ)

private lemma T_nat_eq_sum_vonMangoldt (N : ℕ) :
    T_nat N = ∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) := by
  unfold T_nat
  have h1 : ∀ k ∈ Finset.Icc 1 N, Real.log (k : ℝ) = ∑ d ∈ k.divisors, Λ d := fun k _ =>
    (ArithmeticFunction.vonMangoldt_sum (n := k)).symm
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors, Λ d =
      ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, if d ∣ k then Λ d else 0 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    constructor
    · rintro ⟨hdvd, _⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hdN : d ≤ N := (Nat.le_of_dvd (by omega) hdvd).trans hkN
      exact ⟨⟨hd1, hdN⟩, hdvd⟩
    · rintro ⟨_, hdvd⟩
      exact ⟨hdvd, by omega⟩
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hcard : ((Finset.Icc 1 N).filter (fun k => d ∣ k)).card = N / d := by
    have heq : (Finset.Icc 1 N).filter (fun k => d ∣ k) =
        (Finset.Icc 1 (N / d)).image (fun m => d * m) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hk1, hkN⟩, m, rfl⟩
        refine ⟨m, ⟨?_, ?_⟩, rfl⟩
        · by_contra hm0; simp [show m = 0 by omega] at hk1
        · exact (Nat.le_div_iff_mul_le hd1).mpr (by linarith)
      · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
        refine ⟨⟨Nat.mul_pos hd1 hm1, ?_⟩, m, rfl⟩
        have := (Nat.le_div_iff_mul_le hd1).mp hmN
        linarith
    rw [heq, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hd1 h)]
    simp
  exact_mod_cast hcard

private def chebG (t : ℕ) : ℤ :=
  (t : ℤ) - (t / 2 : ℕ) - (t / 3 : ℕ) - (t / 5 : ℕ) + (t / 30 : ℕ)

private lemma chebG_periodic (t : ℕ) : chebG (t + 30) = chebG t := by
  unfold chebG; omega

private lemma chebG_mod (t : ℕ) : chebG t = chebG (t % 30) := by
  have h : ∀ q r : ℕ, chebG (30 * q + r) = chebG r := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show 30 * (q + 1) + r = (30 * q + r) + 30 by ring, chebG_periodic, ih]
  have hdiv := Nat.div_add_mod t 30
  conv_lhs => rw [← hdiv]
  exact h (t / 30) (t % 30)

private lemma chebG_bounds (t : ℕ) : 0 ≤ chebG t ∧ chebG t ≤ 1 := by
  rw [chebG_mod]
  have hfin : ∀ r : Fin 30, 0 ≤ chebG r.1 ∧ chebG r.1 ≤ 1 := by decide
  exact hfin ⟨t % 30, Nat.mod_lt t (by decide)⟩

private lemma chebG_eq_one_of_lt_six {t : ℕ} (ht1 : 1 ≤ t) (ht6 : t < 6) : chebG t = 1 := by
  unfold chebG; omega

private lemma T_nat_le_integral (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - N ≤ T_nat N ∧
      T_nat N ≤ (N : ℝ) * Real.log N - N + Real.log N + 1 := by
  have hstep_lo : ∀ k : ℕ, 1 ≤ k →
      ((k + 1 : ℕ) : ℝ) * Real.log (k + 1 : ℕ) - (k + 1 : ℕ) -
        ((k : ℝ) * Real.log k - k) ≤ Real.log (k + 1 : ℕ) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hlog : Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ 1 / (k : ℝ) := by
      rw [← Real.log_div (by positivity) hkpos.ne']
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / k by positivity)
      have h2 : ((k + 1 : ℕ) : ℝ) / k - 1 = 1 / k := by push_cast; field_simp; ring
      linarith
    push_cast at hlog ⊢
    have hmul := mul_le_mul_of_nonneg_left hlog hkpos.le
    rw [mul_one_div_cancel hkpos.ne'] at hmul
    linarith
  have hstep_hi : ∀ k : ℕ, 1 ≤ k →
      Real.log (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.log (k + 1 : ℕ) - (k + 1 : ℕ) -
        ((k : ℝ) * Real.log k - k) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hlog : 1 / ((k : ℝ) + 1) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) / ((k : ℝ) + 1) by positivity)
      rw [Real.log_div hkpos.ne' hk1pos.ne'] at h1
      have h2 : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by field_simp; ring
      push_cast; linarith
    push_cast at hlog ⊢
    have hmul := mul_le_mul_of_nonneg_left hlog hk1pos.le
    rw [mul_one_div_cancel hk1pos.ne'] at hmul
    linarith
  constructor
  · induction N, hN using Nat.le_induction with
    | base => simp [T_nat]
    | succ k hk ih =>
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      unfold T_nat at ih ⊢
      rw [hIcc, Finset.sum_insert (by simp)]
      linarith [hstep_lo k hk]
  · induction N, hN using Nat.le_induction with
    | base => simp [T_nat]
    | succ k hk ih =>
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      unfold T_nat at ih ⊢
      rw [hIcc, Finset.sum_insert (by simp)]
      linarith [hstep_hi k hk]

private noncomputable def A_cheb : ℝ :=
  (7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 + (1 / 6 : ℝ) * Real.log 5

private lemma log_three_bounds :
    (19 / 12 : ℝ) * Real.log 2 ≤ Real.log 3 ∧ Real.log 3 ≤ (27 / 17 : ℝ) * Real.log 2 := by
  constructor
  · have h : (2 : ℝ) ^ 19 ≤ (3 : ℝ) ^ 12 := by norm_num
    have hlog := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_pow] at hlog; push_cast at hlog; linarith
  · have h : (3 : ℝ) ^ 17 ≤ (2 : ℝ) ^ 27 := by norm_num
    have hlog := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_pow] at hlog; push_cast at hlog; linarith

private lemma log_five_bounds :
    (30 / 13 : ℝ) * Real.log 2 ≤ Real.log 5 ∧ Real.log 5 ≤ (7 / 3 : ℝ) * Real.log 2 := by
  constructor
  · have h : (2 : ℝ) ^ 30 ≤ (5 : ℝ) ^ 13 := by norm_num
    have hlog := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_pow] at hlog; push_cast at hlog; linarith
  · have h : (5 : ℝ) ^ 3 ≤ (2 : ℝ) ^ 7 := by norm_num
    have hlog := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_pow] at hlog; push_cast at hlog; linarith

private lemma A_cheb_bounds : (0.918 : ℝ) ≤ A_cheb ∧ A_cheb ≤ (0.924 : ℝ) := by
  unfold A_cheb
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3 := log_three_bounds
  have h5 := log_five_bounds
  constructor <;> linarith

private lemma div_term_approx (N d : ℕ) (hd : 1 ≤ d) (hNd : d ≤ N) :
    let m := N / d
    |(m : ℝ) * Real.log (m : ℝ) - (m : ℝ) -
        ((N : ℝ) / d * Real.log ((N : ℝ) / d) - (N : ℝ) / d)| ≤ Real.log (N : ℝ) + 1 := by
  intro m
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hm1 : 1 ≤ m := Nat.div_pos hNd hd
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (hd.trans hNd)
  set x : ℝ := (N : ℝ) / d
  have hxpos : 0 < x := by positivity
  have hmx : (m : ℝ) ≤ x := by
    dsimp [x, m]; rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self N d
  have hxm : x ≤ (m : ℝ) + 1 := by
    dsimp [x, m]; rw [div_le_iff₀ hdpos]
    have := Nat.lt_div_mul_add (a := N) (b := d) hd
    have hcast : (N : ℝ) ≤ ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast (show N ≤ N / d * d + d by omega)
    linarith
  have hxleN : x ≤ N := div_le_self hNpos.le (by exact_mod_cast hd)
  have hm_ge1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hlogx_le : Real.log x ≤ Real.log N := Real.log_le_log hxpos hxleN
  have hlogm_nonneg : 0 ≤ Real.log m := Real.log_nonneg hm_ge1
  have hlog_xm_ub : Real.log x - Real.log m ≤ (x - m) / m := by
    rw [← Real.log_div hxpos.ne' hmpos.ne']
    have h1 := Real.log_le_sub_one_of_pos (show 0 < x / m by positivity)
    have h2 : x / m - 1 = (x - m) / m := by field_simp [hmpos.ne']
    linarith
  have hlog_xm_lb : (x - m) / x ≤ Real.log x - Real.log m := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (m : ℝ) / x by positivity)
    rw [Real.log_div hmpos.ne' hxpos.ne'] at h1
    have h2 : (m : ℝ) / x - 1 = -((x - m) / x) := by field_simp [hxpos.ne']; ring
    linarith
  have hident : x * Real.log x - x - ((m : ℝ) * Real.log m - m) =
      (x - m) * Real.log x + (m : ℝ) * (Real.log x - Real.log m) - (x - m) := by ring
  have hident2 : x * Real.log x - x - ((m : ℝ) * Real.log m - m) =
      (x - m) * Real.log m + x * (Real.log x - Real.log m) - (x - m) := by ring
  have hlog_diff : 0 ≤ x * Real.log x - x - ((m : ℝ) * Real.log m - m) ∧
      x * Real.log x - x - ((m : ℝ) * Real.log m - m) ≤ Real.log N + 1 := by
    constructor
    · rw [hident2]
      have hmul : x - m ≤ x * (Real.log x - Real.log m) := by
        have := mul_le_mul_of_nonneg_left hlog_xm_lb hxpos.le
        rwa [mul_div_cancel₀ _ hxpos.ne'] at this
      have hnonneg : 0 ≤ (x - m) * Real.log m := mul_nonneg (by linarith) hlogm_nonneg
      linarith
    · rw [hident]
      have hmul : (m : ℝ) * (Real.log x - Real.log m) ≤ x - m := by
        have := mul_le_mul_of_nonneg_left hlog_xm_ub hmpos.le
        rwa [mul_div_cancel₀ _ hmpos.ne'] at this
      have h1 : (x - m) * Real.log x ≤ Real.log N := by
        have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
        calc (x - m) * Real.log x ≤ 1 * Real.log x := mul_le_mul_of_nonneg_right (by linarith) hlogx_nonneg
          _ = Real.log x := one_mul _
          _ ≤ Real.log N := hlogx_le
      linarith
  rw [abs_le]
  constructor <;> linarith

private lemma psi_eq_sum_Icc (N : ℕ) :
    ψ (N : ℝ) = ∑ d ∈ Finset.Icc 1 N, Λ d := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_left (Nat.zero_le 1))]
  intro d hd hnot
  have hd0 : d = 0 := by
    simp only [Finset.mem_Icc] at hd hnot; omega
  subst hd0; simp

private lemma chebyshev_five_term_bounds (N : ℕ) (hN : 30 ≤ N) :
    A_cheb * (N : ℝ) - 10 * Real.log (N : ℝ) - 10 ≤ ψ (N : ℝ) ∧
      ψ (N : ℝ) - ψ ((N / 6 : ℕ) : ℝ) ≤ A_cheb * (N : ℝ) + 10 * Real.log (N : ℝ) + 10 := by
  set E : ℝ := T_nat N - T_nat (N / 2) - T_nat (N / 3) - T_nat (N / 5) + T_nat (N / 30)
  have hE_eq : E = ∑ d ∈ Finset.Icc 1 N, Λ d * (chebG (N / d) : ℝ) := by
    have hsplit : ∀ k : ℕ, 1 ≤ k →
        T_nat (N / k) = ∑ d ∈ Finset.Icc 1 N, Λ d * (((N / d) / k : ℕ) : ℝ) := by
      intro k hk
      rw [T_nat_eq_sum_vonMangoldt (N / k)]
      have hsub : Finset.Icc 1 (N / k) ⊆ Finset.Icc 1 N :=
        Finset.Icc_subset_Icc_right (Nat.div_le_self N k)
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun d _ => ?_
        congr 2
        rw [Nat.div_div_eq_div_mul, mul_comm k d, ← Nat.div_div_eq_div_mul]
      · intro d hd hnot
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hgt : N / k < d := by
          simp only [Finset.mem_Icc] at hnot; omega
        have hzero : (N / d) / k = 0 := by
          rw [Nat.div_div_eq_div_mul, Nat.div_eq_zero_iff]
          right
          have hlt : N < d * k := (Nat.div_lt_iff_lt_mul hk).mp hgt
          linarith
        simp [hzero]
    dsimp [E]
    rw [T_nat_eq_sum_vonMangoldt N, hsplit 2 (by decide), hsplit 3 (by decide),
      hsplit 5 (by decide), hsplit 30 (by decide)]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hG : (chebG (N / d) : ℝ) = ((N / d : ℕ) : ℝ) - (((N / d) / 2 : ℕ) : ℝ) -
        (((N / d) / 3 : ℕ) : ℝ) - (((N / d) / 5 : ℕ) : ℝ) + (((N / d) / 30 : ℕ) : ℝ) := by
      unfold chebG
      simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
    rw [hG]; ring
  have hE_le_psi : E ≤ ψ (N : ℝ) := by
    rw [hE_eq, psi_eq_sum_Icc]
    refine Finset.sum_le_sum fun d _ => ?_
    have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
    have hG : (chebG (N / d) : ℝ) ≤ 1 := by exact_mod_cast (chebG_bounds (N / d)).2
    nlinarith
  have hpsi_sub_le_E : ψ (N : ℝ) - ψ ((N / 6 : ℕ) : ℝ) ≤ E := by
    rw [hE_eq, psi_eq_sum_Icc, psi_eq_sum_Icc]
    have hsub : Finset.Icc 1 (N / 6) ⊆ Finset.Icc 1 N :=
      Finset.Icc_subset_Icc_right (Nat.div_le_self N 6)
    have hdiff : ∑ d ∈ Finset.Icc 1 N, Λ d - ∑ d ∈ Finset.Icc 1 (N / 6), Λ d =
        ∑ d ∈ Finset.Icc 1 N, if N / 6 < d then Λ d else 0 := by
      rw [← Finset.sum_sdiff hsub]
      simp only [add_sub_cancel_right]
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext d; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hdiff]
    refine Finset.sum_le_sum fun d hd => ?_
    have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
    split_ifs with hgt
    · have h1 : 1 ≤ N / d := Nat.div_pos (Finset.mem_Icc.mp hd).2 (Finset.mem_Icc.mp hd).1
      have h6 : N / d < 6 := by
        rw [Nat.div_lt_iff_lt_mul (Finset.mem_Icc.mp hd).1]
        have := (Nat.div_lt_iff_lt_mul (by decide : 0 < 6)).mp hgt
        linarith
      rw [chebG_eq_one_of_lt_six h1 h6]; push_cast; linarith
    · have hG0 : (0 : ℝ) ≤ (chebG (N / d) : ℝ) := by exact_mod_cast (chebG_bounds (N / d)).1
      exact mul_nonneg hΛ hG0
  have hT_approx : ∀ k : ℕ, 1 ≤ k → k ≤ 30 →
      |T_nat (N / k) - ((N : ℝ) / k * Real.log ((N : ℝ) / k) - (N : ℝ) / k)| ≤
        2 * Real.log (N : ℝ) + 2 := by
    intro k hk1 hk30
    have hm1 : 1 ≤ N / k := Nat.div_pos (by omega) hk1
    have hT := T_nat_le_integral (N / k) hm1
    have hd := div_term_approx N k hk1 (by omega)
    have hlogm_le : Real.log ((N / k : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast Nat.div_le_self N k)
    rw [abs_le] at hd ⊢
    constructor <;> linarith
  have h1 := hT_approx 1 (by decide) (by decide)
  have h2 := hT_approx 2 (by decide) (by decide)
  have h3 := hT_approx 3 (by decide) (by decide)
  have h5 := hT_approx 5 (by decide) (by decide)
  have h30 := hT_approx 30 (by decide) (by decide)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have halg : ((N : ℝ) / 1 * Real.log ((N : ℝ) / 1) - (N : ℝ) / 1) -
      ((N : ℝ) / 2 * Real.log ((N : ℝ) / 2) - (N : ℝ) / 2) -
      ((N : ℝ) / 3 * Real.log ((N : ℝ) / 3) - (N : ℝ) / 3) -
      ((N : ℝ) / 5 * Real.log ((N : ℝ) / 5) - (N : ℝ) / 5) +
      ((N : ℝ) / 30 * Real.log ((N : ℝ) / 30) - (N : ℝ) / 30) = A_cheb * (N : ℝ) := by
    rw [div_one, Real.log_div hNpos.ne' (by norm_num), Real.log_div hNpos.ne' (by norm_num),
      Real.log_div hNpos.ne' (by norm_num), Real.log_div hNpos.ne' (by norm_num)]
    have h30log : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
    rw [h30log]; unfold A_cheb; ring
  simp only [Nat.div_one] at h1
  rw [abs_le] at h1 h2 h3 h5 h30
  have hE_lo : A_cheb * (N : ℝ) - 10 * Real.log (N : ℝ) - 10 ≤ E := by dsimp [E]; linarith
  have hE_hi : E ≤ A_cheb * (N : ℝ) + 10 * Real.log (N : ℝ) + 10 := by dsimp [E]; linarith
  exact ⟨hE_lo.trans hE_le_psi, hpsi_sub_le_E.trans hE_hi⟩

private lemma psi_upper_sharp :
    ∀ᶠ N : ℕ in atTop, ψ (N : ℝ) ≤ (1.11 : ℝ) * (N : ℝ) := by
  have hglob : ∀ N : ℕ, 1 ≤ N →
      ψ (N : ℝ) ≤ (6 / 5 : ℝ) * A_cheb * (N : ℝ) + 20 * (Real.log (N : ℝ) + 2) ^ 2 + 100 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro hN1
      by_cases h30 : N < 30
      · have hle := Chebyshev.psi_le (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
        have hN30 : (N : ℝ) ≤ 30 := by exact_mod_cast (by omega : N ≤ 30)
        have hlog2 : Real.log 4 ≤ 1.4 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
          have := Real.log_two_lt_d9; linarith
        have hsq : Real.sqrt (N : ℝ) ≤ 6 := by
          rw [Real.sqrt_le_iff]; constructor <;> linarith
        have hlogN : Real.log (N : ℝ) ≤ 4 := by
          have : (N : ℝ) ≤ Real.exp 4 := by
            have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
            have he4 : (2.7 : ℝ) ^ 4 ≤ Real.exp 4 := by
              have hm4 : (4 : ℝ) = ((4 : ℕ) : ℝ) * (1 : ℝ) := by norm_num
              rw [hm4, Real.exp_nat_mul]
              exact pow_le_pow_left₀ (by norm_num) he 4
            linarith [show (30 : ℝ) ≤ (2.7 : ℝ) ^ 4 by norm_num]
          simpa [Real.log_exp] using Real.log_le_log (by exact_mod_cast hN1) this
        have hApos : 0 ≤ A_cheb := by linarith [A_cheb_bounds.1]
        have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
        nlinarith
      · have h30' : 30 ≤ N := by omega
        have h5 := (chebyshev_five_term_bounds N h30').2
        have hN6_pos : 1 ≤ N / 6 := by omega
        have hN6_lt : N / 6 < N := by omega
        have hrec := ih (N / 6) hN6_lt hN6_pos
        have hN6_le : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
          rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self N 6
        have hNne : (N : ℝ) ≠ 0 := (show (0 : ℝ) < N by exact_mod_cast (by omega : 0 < N)).ne'
        have hlog_sub : Real.log ((N / 6 : ℕ) : ℝ) ≤ Real.log (N : ℝ) - Real.log 6 := by
          rw [← Real.log_div hNne (by norm_num)]
          exact Real.log_le_log (by exact_mod_cast hN6_pos) hN6_le
        have hlog6_ge : (1 : ℝ) ≤ Real.log 6 := by
          have : Real.exp 1 ≤ 6 := by have := Real.exp_one_lt_d9; linarith
          simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
        have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
        have hlogN6_nonneg : 0 ≤ Real.log ((N / 6 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hN6_pos)
        have hsq_diff : (Real.log ((N / 6 : ℕ) : ℝ) + 2) ^ 2 ≤ (Real.log (N : ℝ) + 2) ^ 2 -
            2 * Real.log (N : ℝ) - 3 := by
          have h1 : Real.log ((N / 6 : ℕ) : ℝ) + 2 ≤ Real.log (N : ℝ) + 1 := by linarith
          have h2 : (Real.log ((N / 6 : ℕ) : ℝ) + 2) ^ 2 ≤ (Real.log (N : ℝ) + 1) ^ 2 :=
            pow_le_pow_left₀ (by linarith) h1 2
          nlinarith
        have hApos : 0 ≤ A_cheb := by linarith [A_cheb_bounds.1]
        have hmulA : (6 / 5 : ℝ) * A_cheb * ((N / 6 : ℕ) : ℝ) ≤ (1 / 5 : ℝ) * A_cheb * (N : ℝ) := by
          have := mul_le_mul_of_nonneg_left hN6_le (show 0 ≤ (6 / 5 : ℝ) * A_cheb by positivity)
          linarith
        linarith
  have hlim : Tendsto (fun N : ℕ => (20 * (Real.log (N : ℝ) + 2) ^ 2 + 100) / (N : ℝ)) atTop (nhds 0) := by
    have h3 : Tendsto (fun x : ℝ => (180 : ℝ) / x) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hcomb : Tendsto (fun x : ℝ => 20 * ((Real.log x) ^ 2 / x) + 80 * (Real.log x / x) + 180 / x) atTop (nhds 0) := by
      simpa using ((tendsto_log_sq_div_id.const_mul 20).add (tendsto_log_div_id.const_mul 80)).add h3
    refine (hcomb.comp tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    dsimp only [Function.comp_apply]
    field_simp [hNpos.ne']; ring
  have hev := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.001))
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with N hN_err hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have herr : 20 * (Real.log (N : ℝ) + 2) ^ 2 + 100 ≤ 0.001 * (N : ℝ) :=
    ((div_lt_iff₀ hNpos).mp hN_err).le
  have hA := A_cheb_bounds.2
  have hg := hglob N hN1
  nlinarith

lemma dyadic_primes_lower :
    ∀ᶠ Y : ℝ in atTop,
      (0.68 : ℝ) * Y / Real.log Y ≤ (((Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime).card : ℝ) := by
  have h_psi_hi : ∀ᶠ Y : ℝ in atTop, ψ ((⌈Y⌉₊ - 1 : ℕ) : ℝ) ≤ 1.11 * Y := by
    have hfloor : Tendsto (fun Y : ℝ => ⌈Y⌉₊ - 1) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨(b : ℝ) + 2, fun Y hY => ?_⟩
      have h1 : ((b + 2 : ℕ) : ℝ) ≤ (⌈Y⌉₊ : ℝ) := by
        push_cast; exact hY.trans (Nat.le_ceil Y)
      have h2 : b + 2 ≤ ⌈Y⌉₊ := by exact_mod_cast h1
      omega
    filter_upwards [hfloor.eventually psi_upper_sharp, Filter.eventually_ge_atTop (10 : ℝ)] with Y hY hY10
    have hpos : 1 ≤ ⌈Y⌉₊ := by
      have h1 : (1 : ℝ) ≤ (⌈Y⌉₊ : ℝ) := (by linarith : (1 : ℝ) ≤ Y).trans (Nat.le_ceil Y)
      exact_mod_cast h1
    have hle : ((⌈Y⌉₊ - 1 : ℕ) : ℝ) ≤ Y := by
      have hlt : (⌈Y⌉₊ : ℝ) < Y + 1 := Nat.ceil_lt_add_one (by linarith)
      rw [Nat.cast_sub hpos]; push_cast; linarith
    have h1 : ψ ((⌈Y⌉₊ - 1 : ℕ) : ℝ) ≤ 1.11 * ((⌈Y⌉₊ - 1 : ℕ) : ℝ) := hY
    linarith
  have h_psi_lo : ∀ᶠ Y : ℝ in atTop, 1.83 * Y ≤ ψ ((⌈2 * Y⌉₊ - 1 : ℕ) : ℝ) := by
    have hlim : Tendsto (fun Y : ℝ => (10 * Real.log (2 * Y + 1) + 12) / Y) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℝ => Real.log (2 * x + 1) / x) atTop (nhds 0) := by
        have hle : ∀ᶠ x : ℝ in atTop, Real.log (2 * x + 1) / x ≤ Real.log (3 * x) / x := by
          filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
          exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) (by linarith)
        have htop : Tendsto (fun x : ℝ => Real.log (3 * x) / x) atTop (nhds 0) := by
          have h3 : Tendsto (fun x : ℝ => Real.log 3 / x) atTop (nhds 0) :=
            tendsto_const_nhds.div_atTop tendsto_id
          have hsum : Tendsto (fun x : ℝ => Real.log 3 / x + Real.log x / x) atTop (nhds 0) := by
            simpa using h3.add tendsto_log_div_id
          refine hsum.congr' ?_
          filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
          rw [Real.log_mul (by norm_num) hx.ne']; ring
        have hnn : ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log (2 * x + 1) / x := by
          filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
          exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop hnn hle
      have h2 : Tendsto (fun x : ℝ => (12 : ℝ) / x) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hsum : Tendsto (fun x : ℝ => 10 * (Real.log (2 * x + 1) / x) + 12 / x) atTop (nhds 0) := by
        simpa using (h1.const_mul 10).add h2
      refine hsum.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp [hx.ne']
    have hev := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.005))
    filter_upwards [hev, Filter.eventually_ge_atTop (100 : ℝ)] with Y hYerr hY100
    set M := ⌈2 * Y⌉₊ - 1
    have hpos : 1 ≤ ⌈2 * Y⌉₊ := by
      have h1 : (1 : ℝ) ≤ (⌈2 * Y⌉₊ : ℝ) := (by linarith : (1 : ℝ) ≤ 2 * Y).trans (Nat.le_ceil _)
      exact_mod_cast h1
    have hM_ge : 2 * Y - 1 ≤ (M : ℝ) := by
      dsimp [M]; rw [Nat.cast_sub hpos]; push_cast; linarith [Nat.le_ceil (2 * Y)]
    have hM_le : (M : ℝ) ≤ 2 * Y := by
      dsimp [M]; rw [Nat.cast_sub hpos]; push_cast; linarith [Nat.ceil_lt_add_one (show 0 ≤ 2 * Y by linarith)]
    have hM30 : 30 ≤ M := by
      have : (30 : ℝ) ≤ (M : ℝ) := by linarith
      exact_mod_cast this
    have h5 := (chebyshev_five_term_bounds M hM30).1
    have hlogM : Real.log (M : ℝ) ≤ Real.log (2 * Y + 1) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) (by linarith)
    have herr : 10 * Real.log (2 * Y + 1) + 12 ≤ 0.005 * Y :=
      ((div_lt_iff₀ (by linarith)).mp hYerr).le
    have hA := A_cheb_bounds.1
    nlinarith
  have h_sqrt : ∀ᶠ Y : ℝ in atTop,
      2 * Real.sqrt (2 * Y) * Real.log (2 * Y) ≤ 0.01 * Y ∧ Real.log (2 * Y) ≤ 1.04 * Real.log Y := by
    have h1 : Tendsto (fun Y : ℝ => 2 * Real.sqrt (2 * Y) * Real.log (2 * Y) / Y) atTop (nhds 0) := by
      have hcomp : Tendsto (fun Y : ℝ => Real.log (2 * Y) / (2 * Y) ^ (1 / 2 : ℝ)) atTop (nhds 0) :=
        tendsto_log_div_rpow_half.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
      have hmul4 : Tendsto (fun Y : ℝ => 4 * (Real.log (2 * Y) / (2 * Y) ^ (1 / 2 : ℝ))) atTop (nhds 0) := by
        simpa using hcomp.const_mul 4
      refine hmul4.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Y hY
      rw [Real.sqrt_eq_rpow]
      have hsq : ((2 * Y) ^ (1 / 2 : ℝ)) ^ 2 = 2 * Y := by
        rw [sq, ← Real.rpow_add (by positivity)]; norm_num
      have hpos : (2 * Y) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
      field_simp [hY.ne', hpos]
      rw [hsq]; ring
    have h2 : Tendsto (fun Y : ℝ => Real.log 2 / Real.log Y) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    filter_upwards [h1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.01)),
      h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.04)),
      Filter.eventually_ge_atTop (10 : ℝ)] with Y hY1 hY2 hY10
    have hlogY_pos : 0 < Real.log Y := Real.log_pos (by linarith)
    constructor
    · exact ((div_lt_iff₀ (by linarith)).mp hY1).le
    · rw [Real.log_mul (by norm_num) (by linarith)]
      have := (div_lt_iff₀ hlogY_pos).mp hY2
      linarith
  filter_upwards [h_psi_hi, h_psi_lo, h_sqrt, Filter.eventually_ge_atTop (100 : ℝ)] with Y hhi hlo ⟨hsq, hlog2Y⟩ hY100
  set A := ⌈Y⌉₊ - 1
  set B := ⌈2 * Y⌉₊ - 1
  have hA_pos : 1 ≤ ⌈Y⌉₊ := by
    have : (1 : ℝ) ≤ (⌈Y⌉₊ : ℝ) := (by linarith : (1 : ℝ) ≤ Y).trans (Nat.le_ceil _)
    exact_mod_cast this
  have hB_pos : 1 ≤ ⌈2 * Y⌉₊ := by
    have : (1 : ℝ) ≤ (⌈2 * Y⌉₊ : ℝ) := (by linarith : (1 : ℝ) ≤ 2 * Y).trans (Nat.le_ceil _)
    exact_mod_cast this
  have hB_le : (B : ℝ) ≤ 2 * Y := by
    dsimp [B]; rw [Nat.cast_sub hB_pos]; push_cast; linarith [Nat.ceil_lt_add_one (show 0 ≤ 2 * Y by linarith)]
  have hB_ge1 : (1 : ℝ) ≤ (B : ℝ) := by
    dsimp [B]; rw [Nat.cast_sub hB_pos]; push_cast; linarith [Nat.le_ceil (2 * Y)]
  have htheta_diff : 0.71 * Y ≤ θ (B : ℝ) - θ (A : ℝ) := by
    have h1 := Chebyshev.psi_sub_theta_le hB_ge1
    have h2 := Chebyshev.theta_le_psi (A : ℝ)
    have hsqB : 2 * Real.sqrt (B : ℝ) * Real.log (B : ℝ) ≤ 2 * Real.sqrt (2 * Y) * Real.log (2 * Y) := by
      gcongr
    linarith
  have htheta_eq : θ (B : ℝ) - θ (A : ℝ) =
      ∑ p ∈ (Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [Chebyshev.theta, Chebyshev.theta]
    simp only [Nat.floor_natCast]
    have hAB : A ≤ B := by
      have : ⌈Y⌉₊ ≤ ⌈2 * Y⌉₊ := Nat.ceil_mono (by linarith)
      omega
    have hsub : (Finset.Ioc 0 A).filter Nat.Prime ⊆ (Finset.Ioc 0 B).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans hAB⟩, hp.2⟩
    rw [← Finset.sum_sdiff hsub]
    simp only [add_sub_cancel_right]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
    have hA_eq : A + 1 = ⌈Y⌉₊ := by omega
    have hB_eq : B + 1 = ⌈2 * Y⌉₊ := by omega
    constructor
    · rintro ⟨⟨⟨_, hpB⟩, hp⟩, hnot⟩
      have hpA : A < p := by
        by_contra hle
        exact hnot ⟨⟨hp.pos, by omega⟩, hp⟩
      exact ⟨⟨by omega, by omega⟩, hp⟩
    · rintro ⟨⟨hp1, hp2⟩, hp⟩
      exact ⟨⟨⟨hp.pos, by omega⟩, hp⟩, fun ⟨⟨_, hle⟩, _⟩ => by omega⟩
  have hsum_ub : ∑ p ∈ (Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime, Real.log (p : ℝ) ≤
      (((Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime).card : ℝ) * Real.log (2 * Y) := by
    calc ∑ p ∈ (Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime, Real.log (p : ℝ)
        ≤ ∑ _p ∈ (Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime, Real.log (2 * Y) := by
          refine Finset.sum_le_sum fun p hp => ?_
          simp only [Finset.mem_filter, Finset.mem_Ico] at hp
          have hp_lt : (p : ℝ) < 2 * Y := Nat.lt_ceil.mp hp.1.2
          exact Real.log_le_log (by exact_mod_cast hp.2.pos) hp_lt.le
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [htheta_eq] at htheta_diff
  have hlogY_pos : 0 < Real.log Y := Real.log_pos (by linarith)
  rw [div_le_iff₀ hlogY_pos]
  nlinarith

/- ### Section 3: Mertens' First Theorem & Abel Summation -/

private lemma sum_biUnion_le_nonneg {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion : ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      have := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hnn : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := Finset.sum_nonneg fun x _ => hf x
      linarith
    linarith

private lemma sum_primePow_tail_le (N : ℕ) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ d.Prime), Λ d / (d : ℝ) ≤ 16 := by
  have hsub : (Finset.Icc 1 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0) ⊆
      ((Finset.Icc 2 N).filter Nat.Prime).biUnion (fun p => (Finset.Icc 2 (Nat.log 2 N + 2)).image (fun k => p ^ k)) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_image] at hd ⊢
    have hpp : IsPrimePow d := by
      by_contra hnot
      exact hd.2.2 (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot)
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k = 1 := by omega
      subst hk1; simp at hd; exact hd.2.1 hp
    refine ⟨p, ⟨⟨hp.two_le, ?_⟩, hp⟩, k, ⟨hk2, ?_⟩, rfl⟩
    · exact (Nat.le_self_pow (by omega) p).trans hd.1.2
    · have h2k : 2 ^ k ≤ N := (Nat.pow_le_pow_left hp.two_le k).trans hd.1.2
      have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2) h2k
      omega
  have hsub_f : (Finset.Icc 1 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0) ⊆
      (Finset.Icc 1 N).filter (fun d => ¬ d.Prime) := by
    intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
  have h1 : ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ d.Prime), Λ d / (d : ℝ) =
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), Λ d / (d : ℝ) := by
    rw [← Finset.sum_subset hsub_f]
    intro x hx hnot
    rw [Finset.mem_filter] at hx hnot
    have h0 : Λ x = 0 := by tauto
    simp [h0]
  rw [h1]
  have hle_biU : ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ d.Prime ∧ Λ d ≠ 0), Λ d / (d : ℝ) ≤
      ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
        ∑ k ∈ Finset.Icc 2 (Nat.log 2 N + 2), Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) := by
    calc _ ≤ ∑ d ∈ ((Finset.Icc 2 N).filter Nat.Prime).biUnion
            (fun p => (Finset.Icc 2 (Nat.log 2 N + 2)).image (fun k => p ^ k)), Λ d / (d : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))
      _ ≤ ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
            ∑ d ∈ (Finset.Icc 2 (Nat.log 2 N + 2)).image (fun k => p ^ k), Λ d / (d : ℝ) :=
            sum_biUnion_le_nonneg _ _ _ (fun d => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))
      _ = _ := by
            refine Finset.sum_congr rfl fun p hp => ?_
            have hp_pr := (Finset.mem_filter.mp hp).2
            rw [Finset.sum_image]
            intro a _ b _ hab
            exact Nat.pow_right_injective hp_pr.two_le hab
  have hinner : ∀ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
      ∑ k ∈ Finset.Icc 2 (Nat.log 2 N + 2), Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) ≤
        2 * Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hp_pr := (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
    have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have hterm : ∀ k ∈ Finset.Icc 2 (Nat.log 2 N + 2),
        Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) = Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ k := by
      intro k hk
      have hkpos : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
      rw [ArithmeticFunction.vonMangoldt_apply_pow hkpos, ArithmeticFunction.vonMangoldt_apply_prime hp_pr]
      push_cast; rw [div_eq_mul_inv, inv_pow]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hgeom : ∑ k ∈ Finset.Icc 2 (Nat.log 2 N + 2), ((p : ℝ)⁻¹) ^ k ≤
        1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      set r : ℝ := (p : ℝ)⁻¹
      have hr0 : 0 ≤ r := by positivity
      have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (by linarith)
      set K := Nat.log 2 N + 1
      have hshift : ∑ k ∈ Finset.Icc 2 (Nat.log 2 N + 2), r ^ k =
          r ^ 2 * ∑ j ∈ Finset.range K, r ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun k _ => k - 2) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
        · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
        · intro j hj; refine ⟨j + 2, ?_, by omega⟩; simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢; omega
        · intro k hk
          have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
          rw [← pow_add, show 2 + (k - 2) = k by omega]
      rw [hshift, geom_sum_eq hr1.ne]
      have hnum : (r ^ K - 1) / (r - 1) ≤ 1 / (1 - r) := by
        have h1 : (r ^ K - 1) / (r - 1) = (1 - r ^ K) / (1 - r) := by
          rw [← neg_div_neg_eq]; ring_nf
        rw [h1]
        exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 K]) (by linarith)
      calc r ^ 2 * ((r ^ K - 1) / (r - 1)) ≤ r ^ 2 * (1 / (1 - r)) :=
            mul_le_mul_of_nonneg_left hnum (sq_nonneg r)
        _ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
            dsimp [r]; field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
    have hden_pos : 0 < (p : ℝ) * ((p : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    calc Real.log (p : ℝ) * ∑ k ∈ Finset.Icc 2 (Nat.log 2 N + 2), ((p : ℝ)⁻¹) ^ k
        ≤ Real.log (p : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := mul_le_mul_of_nonneg_left hgeom hlogp_nn
      _ = Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by ring
      _ ≤ 2 * Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
          div_le_div_of_nonneg_right (by linarith) hden_pos.le
  have hlog_sqrt : ∀ m : ℕ, 2 ≤ m →
      2 * Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) ≤
        16 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
    intro m hm
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hm1_pos : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast (by omega : 0 < m - 1)
    have hsm_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hsm1_pos : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hm1_pos
    have hlogm : Real.log (m : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hsm_pos
      have hsq : Real.log (m : ℝ) = 2 * Real.log (Real.sqrt (m : ℝ)) := by
        rw [Real.log_sqrt (by linarith)]; ring
      linarith
    have hdiff : 1 / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤
        2 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have hrat : Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ) =
          1 / (Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ)) := by
        rw [eq_div_iff (by positivity)]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ m by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (m - 1 : ℕ) by linarith), hcast]
      have hsum_le : Real.sqrt (m : ℝ) + Real.sqrt ((m - 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
        have : Real.sqrt ((m - 1 : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by linarith)
        linarith
      have h1 : 1 / (2 * Real.sqrt (m : ℝ)) ≤ Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ) := by
        rw [hrat]; exact one_div_le_one_div_of_le (by positivity) hsum_le
      have h2 : 1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ) =
          (Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) /
            (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ)) := by
        field_simp [hsm_pos.ne', hsm1_pos.ne']
      rw [h2]
      have hden : Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
        have : Real.sqrt ((m - 1 : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by linarith)
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ m by linarith)]
      calc 1 / ((m : ℝ) * Real.sqrt (m : ℝ))
          = 2 * ((1 / (2 * Real.sqrt (m : ℝ))) / (m : ℝ)) := by field_simp [hsm_pos.ne', (show (m : ℝ) ≠ 0 by linarith)]
        _ ≤ 2 * ((Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) / (m : ℝ)) := by gcongr
        _ ≤ 2 * ((Real.sqrt (m : ℝ) - Real.sqrt ((m - 1 : ℕ) : ℝ)) /
              (Real.sqrt ((m - 1 : ℕ) : ℝ) * Real.sqrt (m : ℝ))) := by
            gcongr
            exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    calc 2 * Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))
        ≤ 4 * Real.sqrt (m : ℝ) / ((m : ℝ) * ((m : ℝ) / 2)) := by
          apply div_le_div₀ (by positivity) (by linarith) (by positivity) (by nlinarith)
      _ = 8 * (1 / ((m : ℝ) * Real.sqrt (m : ℝ))) := by
          have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt (by linarith)
          field_simp [hsm_pos.ne', (show (m : ℝ) ≠ 0 by linarith)]
          nlinarith
      _ ≤ 16 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by linarith
  have htele : ∀ K : ℕ, ∑ m ∈ Finset.Icc 2 K,
      (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) ≤ 1 := by
    intro K
    induction K with
    | zero => simp
    | succ K _ =>
      by_cases hK : K = 0
      · subst hK; simp
      · have hK1 : 1 ≤ K := by omega
        have hIcc : Finset.Icc 2 (K + 1) = insert (K + 1) (Finset.Icc 2 K) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp)]
        have hexact : ∀ M : ℕ, 1 ≤ M → ∑ m ∈ Finset.Icc 2 M,
            (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) =
              1 - 1 / Real.sqrt (M : ℝ) := by
          intro M hM
          induction M, hM using Nat.le_induction with
          | base => simp
          | succ m hm ih2 =>
            have hI : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hI, Finset.sum_insert (by simp), ih2]
            simp only [Nat.add_sub_cancel]; ring
        rw [hexact K hK1]
        simp only [Nat.add_sub_cancel]
        have hpos : 0 ≤ 1 / Real.sqrt ((K + 1 : ℕ) : ℝ) := by positivity
        linarith
  calc _ ≤ ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
            2 * Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
          hle_biU.trans (Finset.sum_le_sum hinner)
    _ ≤ ∑ m ∈ Finset.Icc 2 N, 2 * Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun m hm _ => by
            have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
            have h1 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
            have h2 : 0 < (m : ℝ) * ((m : ℝ) - 1) := mul_pos (by linarith) (by linarith)
            exact div_nonneg (by linarith) h2.le)
    _ ≤ ∑ m ∈ Finset.Icc 2 N, 16 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) :=
          Finset.sum_le_sum fun m hm => hlog_sqrt m (Finset.mem_Icc.mp hm).1
    _ = 16 * ∑ m ∈ Finset.Icc 2 N, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
          rw [← Finset.mul_sum]
    _ ≤ 16 * 1 := mul_le_mul_of_nonneg_left (htele N) (by norm_num)
    _ = 16 := mul_one 16

lemma mertens_first (N : ℕ) (hN : 2 ≤ N) :
    Real.log (N : ℝ) - 20 ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ∧
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (N : ℝ) + 20 := by
  have hT_eq := T_nat_eq_sum_vonMangoldt N
  have hT_int := T_nat_le_integral N (by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdiff_floor : (N : ℝ) * (∑ d ∈ Finset.Icc 1 N, Λ d / (d : ℝ)) - ψ (N : ℝ) ≤ T_nat N ∧
      T_nat N ≤ (N : ℝ) * (∑ d ∈ Finset.Icc 1 N, Λ d / (d : ℝ)) := by
    rw [hT_eq, psi_eq_sum_Icc, Finset.mul_sum, ← Finset.sum_sub_distrib]
    constructor
    · refine Finset.sum_le_sum fun d hd => ?_
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
      have hfl : (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := by
        have hlt := Nat.lt_div_mul_add (a := N) (b := d) hd1
        have hle : (N : ℝ) ≤ ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast (show N ≤ N / d * d + d by omega)
        rw [sub_le_iff_le_add, div_le_iff₀ hdpos]; linarith
      have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
      have h1 : (N : ℝ) * (Λ d / (d : ℝ)) - Λ d = Λ d * ((N : ℝ) / d - 1) := by ring
      rw [h1]; exact mul_le_mul_of_nonneg_left hfl hΛ
    · refine Finset.sum_le_sum fun d hd => ?_
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
      have hfl : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
        rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self N d
      have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
      have h1 : (N : ℝ) * (Λ d / (d : ℝ)) = Λ d * ((N : ℝ) / d) := by ring
      rw [h1]; exact mul_le_mul_of_nonneg_left hfl hΛ
  have hsplit : ∑ d ∈ Finset.Icc 1 N, Λ d / (d : ℝ) =
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) +
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ d.Prime), Λ d / (d : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  have htail_le := sum_primePow_tail_le N
  have htail_nn : 0 ≤ ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ d.Prime), Λ d / (d : ℝ) :=
    Finset.sum_nonneg fun d _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
  have hpsi_le : ψ (N : ℝ) ≤ 6 * (N : ℝ) := by
    have h1 := Chebyshev.psi_le_const_mul_self (show (0 : ℝ) ≤ N by linarith)
    have hlog4 : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
      have := Real.log_two_lt_d9; linarith
    nlinarith
  have hlogN_le_N : Real.log (N : ℝ) + 1 ≤ (N : ℝ) := by
    have := Real.log_le_sub_one_of_pos hNpos; linarith
  constructor
  · have h1 : (N : ℝ) * Real.log N - N ≤ (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, Λ d / (d : ℝ) :=
      hT_int.1.trans hdiff_floor.2
    have h2 : Real.log N - 1 ≤ ∑ d ∈ Finset.Icc 1 N, Λ d / (d : ℝ) := by nlinarith
    linarith
  · have h1 : (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, Λ d / (d : ℝ) - ψ (N : ℝ) ≤
        (N : ℝ) * Real.log N - N + Real.log N + 1 :=
      hdiff_floor.1.trans hT_int.2
    have h2 : ∑ d ∈ Finset.Icc 1 N, Λ d / (d : ℝ) ≤ Real.log N + 7 := by nlinarith
    linarith

private lemma sum_Ioc_telescope (W : ℕ) (f : ℕ → ℝ) :
    ∀ K : ℕ, W < K → ∑ m ∈ Finset.Ioc W (K - 1), (f m - f (m + 1)) = f (W + 1) - f K := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Finset.Ioc_self, Finset.sum_empty, sub_self]
  | succ K hWK ih =>
    have hWK' : W < K := hWK
    have hI : Finset.Ioc W K = insert K (Finset.Ioc W (K - 1)) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
    rw [Nat.add_sub_cancel, hI, Finset.sum_insert (by simp; omega), ih]
    ring

/-- Discrete Abel summation lower bound on `∑_{W < p ≤ B} 1 / (p * log p)`. -/
lemma sum_inv_prime_log_ge {W B : ℕ} (hW : 3 ≤ W) (hWB : W ≤ B) :
    1 / Real.log (W : ℝ) - 1 / Real.log (B : ℝ) - 100 / (Real.log (W : ℝ)) ^ 2 ≤
      ∑ p ∈ (Finset.Ioc W B).filter Nat.Prime, 1 / ((p : ℝ) * Real.log (p : ℝ)) := by
  by_cases heq : W = B
  · subst heq
    have hnn : (0 : ℝ) ≤ 100 / (Real.log (W : ℝ)) ^ 2 := by positivity
    simp only [Finset.Ioc_self, Finset.filter_empty, Finset.sum_empty, sub_self]
    linarith
  have hWltB : W < B := lt_of_le_of_ne hWB heq
  let a : ℕ → ℝ := fun m => if m.Prime then Real.log (m : ℝ) / (m : ℝ) else 0
  let M : ℕ → ℝ := fun k => ∑ m ∈ Finset.Icc 1 k, a m
  let g : ℕ → ℝ := fun m => 1 / (Real.log (m : ℝ)) ^ 2
  have hM_eq : ∀ k, M k = ∑ p ∈ (Finset.Icc 1 k).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
    intro k; dsimp [M, a]; rw [Finset.sum_filter]
  have hsum_eq : ∑ p ∈ (Finset.Ioc W B).filter Nat.Prime, 1 / ((p : ℝ) * Real.log (p : ℝ)) =
      ∑ m ∈ Finset.Ioc W B, a m * g m := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    dsimp [a, g]
    split_ifs with hp
    · have hm1 : (1 : ℝ) < m := by exact_mod_cast hp.one_lt
      have hlog : Real.log (m : ℝ) ≠ 0 := (Real.log_pos hm1).ne'
      have hm0 : (m : ℝ) ≠ 0 := by linarith
      field_simp [hlog, hm0]
    · simp
  have hsbp : ∀ K : ℕ, W < K →
      ∑ m ∈ Finset.Ioc W K, a m * g m =
        M K * g K - M W * g (W + 1) +
          ∑ m ∈ Finset.Ioc W (K - 1), M m * (g m - g (m + 1)) := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base =>
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      have hI : Finset.Ioc W (W + 1) = {W + 1} := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
      rw [hI, Finset.Ioc_self, Finset.sum_singleton, Finset.sum_empty, add_zero]
      have hdiff : M (W + 1) - M W = a (W + 1) := by
        dsimp [M]
        have hIcc : Finset.Icc 1 (W + 1) = insert (W + 1) (Finset.Icc 1 W) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp)]; ring
      linarith [show a (W + 1) * g (W + 1) = (M (W + 1) - M W) * g (W + 1) by rw [hdiff]]
    | succ K hWK ih =>
      have hWK' : W < K := hWK
      have hI1 : Finset.Ioc W (K + 1) = insert (K + 1) (Finset.Ioc W K) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hI2 : Finset.Ioc W K = insert K (Finset.Ioc W (K - 1)) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      rw [hI1, Finset.sum_insert (by simp), ih, Nat.add_sub_cancel, hI2, Finset.sum_insert (by simp; omega)]
      have hdiff : M (K + 1) - M K = a (K + 1) := by
        dsimp [M]
        have hIcc : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp)]; ring
      have ha : a (K + 1) * g (K + 1) = (M (K + 1) - M K) * g (K + 1) := by rw [hdiff]
      linarith
  rw [hsum_eq, hsbp B hWltB]
  have hg_anti : ∀ m : ℕ, 3 ≤ m → g (m + 1) ≤ g m := by
    intro m hm
    dsimp [g]
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hle : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast (by omega : m ≤ m + 1))
    exact one_div_le_one_div_of_le (sq_pos_of_pos hlogm) (pow_le_pow_left₀ hlogm.le hle 2)
  have hMB := (mertens_first B (by omega)).1
  have hMW := (mertens_first W (by omega)).2
  rw [← hM_eq B] at hMB
  rw [← hM_eq W] at hMW
  have hlogW_pos : 0 < Real.log (W : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  have hstep : ∀ m ∈ Finset.Ioc W (B - 1),
      2 * (1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ)) -
        2 * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) - 20 * (g m - g (m + 1)) ≤
        M m * (g m - g (m + 1)) := by
    intro m hm
    have hmW : W < m := (Finset.mem_Ioc.mp hm).1
    have hm3 : 3 ≤ m := by omega
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hlogm1_pos : 0 < Real.log ((m + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m + 1))
    have hMm := (mertens_first m (by omega)).1
    rw [← hM_eq m] at hMm
    have hdg_nn : 0 ≤ g m - g (m + 1) := sub_nonneg.mpr (hg_anti m hm3)
    have h1 : (Real.log (m : ℝ) - 20) * (g m - g (m + 1)) ≤ M m * (g m - g (m + 1)) :=
      mul_le_mul_of_nonneg_right hMm hdg_nn
    set lm := Real.log (m : ℝ)
    set lm1 := Real.log ((m + 1 : ℕ) : ℝ)
    have hlm_ge1 : 1 ≤ lm := by
      have h3m : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
      have : Real.exp 1 ≤ (m : ℝ) := (Real.exp_one_lt_d9.le).trans (by linarith)
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
    have hlm_le : lm ≤ lm1 := Real.log_le_log hmpos (by exact_mod_cast (by omega : m ≤ m + 1))
    have hlm1_ge1 : 1 ≤ lm1 := hlm_ge1.trans hlm_le
    have hdiff_le : lm1 - lm ≤ 1 / (m : ℝ) := by
      dsimp [lm, lm1]
      rw [← Real.log_div (by positivity) hmpos.ne']
      have h := Real.log_le_sub_one_of_pos (show 0 < ((m + 1 : ℕ) : ℝ) / m by positivity)
      have h2 : ((m + 1 : ℕ) : ℝ) / m - 1 = 1 / m := by push_cast; field_simp; ring
      linarith
    have hdiff_nn : 0 ≤ lm1 - lm := sub_nonneg.mpr hlm_le
    have hident : lm * (1 / lm ^ 2 - 1 / lm1 ^ 2) =
        2 * (1 / lm - 1 / lm1) - (lm1 - lm) ^ 2 / (lm * lm1 ^ 2) := by
      field_simp [hlogm_pos.ne', hlogm1_pos.ne']; ring
    have herr_sq : (lm1 - lm) ^ 2 / (lm * lm1 ^ 2) ≤ 2 * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) := by
      have hden : 1 ≤ lm * lm1 ^ 2 := by nlinarith
      have hsq : (lm1 - lm) ^ 2 ≤ 1 / (m : ℝ) ^ 2 := by
        calc (lm1 - lm) ^ 2 ≤ (1 / (m : ℝ)) ^ 2 := pow_le_pow_left₀ hdiff_nn hdiff_le 2
          _ = 1 / (m : ℝ) ^ 2 := by ring
      have hfrac : 1 / (m : ℝ) ^ 2 ≤ 2 * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) := by
        have hsub : 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) = 1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp [hmpos.ne', (show (m : ℝ) + 1 ≠ 0 by linarith)]; ring
        rw [hsub]
        have : (m : ℝ) * ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by
          push_cast; nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast (by omega : 1 ≤ m)]
        rw [show 2 * (1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) = 2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) by ring]
        rw [div_le_div_iff₀ (sq_pos_of_pos hmpos) (by positivity)]
        linarith
      calc (lm1 - lm) ^ 2 / (lm * lm1 ^ 2) ≤ (lm1 - lm) ^ 2 / 1 :=
            div_le_div_of_nonneg_left (sq_nonneg _) zero_lt_one hden
        _ = (lm1 - lm) ^ 2 := div_one _
        _ ≤ 1 / (m : ℝ) ^ 2 := hsq
        _ ≤ 2 * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) := hfrac
    have hmain : 2 * (1 / lm - 1 / lm1) - 2 * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) ≤
        lm * (g m - g (m + 1)) := by
      dsimp [g]; linarith
    linarith
  have hsum_lb := Finset.sum_le_sum hstep
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_lb
  rw [sum_Ioc_telescope W (fun m => 1 / Real.log (m : ℝ)) B hWltB,
    sum_Ioc_telescope W (fun m => 1 / (m : ℝ)) B hWltB,
    sum_Ioc_telescope W g B hWltB] at hsum_lb
  have hgB_nn : 0 ≤ g B := by dsimp [g]; positivity
  have hgW1_nn : 0 ≤ g (W + 1) := by dsimp [g]; positivity
  have hMB_term : (Real.log (B : ℝ) - 20) * g B ≤ M B * g B :=
    mul_le_mul_of_nonneg_right hMB hgB_nn
  have hMW_term : M W * g (W + 1) ≤ (Real.log (W : ℝ) + 20) * g (W + 1) :=
    mul_le_mul_of_nonneg_right hMW hgW1_nn
  have hB_simp : Real.log (B : ℝ) * g B = 1 / Real.log (B : ℝ) := by
    dsimp [g]; field_simp [hlogB_pos.ne']
  have hg_le_W : g (W + 1) ≤ g W := hg_anti W hW
  have hgB_le_W : g B ≤ g W := by
    dsimp [g]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hlogW_pos)
      (pow_le_pow_left₀ hlogW_pos.le (Real.log_le_log (by exact_mod_cast (by omega : 0 < W)) (by exact_mod_cast hWB)) 2)
  have hW_step : 1 / Real.log (W : ℝ) - 1 / Real.log ((W + 1 : ℕ) : ℝ) ≤ 1 / ((W : ℝ) * (Real.log (W : ℝ)) ^ 2) := by
    have hlogW1_pos : 0 < Real.log ((W + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < W + 1))
    have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
    have hle : Real.log (W : ℝ) ≤ Real.log ((W + 1 : ℕ) : ℝ) :=
      Real.log_le_log hWpos (by exact_mod_cast (by omega : W ≤ W + 1))
    have hdiff : Real.log ((W + 1 : ℕ) : ℝ) - Real.log (W : ℝ) ≤ 1 / (W : ℝ) := by
      rw [← Real.log_div (by positivity) hWpos.ne']
      have h := Real.log_le_sub_one_of_pos (show 0 < ((W + 1 : ℕ) : ℝ) / W by positivity)
      have h2 : ((W + 1 : ℕ) : ℝ) / W - 1 = 1 / W := by push_cast; field_simp; ring
      linarith
    have heq' : 1 / Real.log (W : ℝ) - 1 / Real.log ((W + 1 : ℕ) : ℝ) =
        (Real.log ((W + 1 : ℕ) : ℝ) - Real.log (W : ℝ)) / (Real.log (W : ℝ) * Real.log ((W + 1 : ℕ) : ℝ)) := by
      field_simp [hlogW_pos.ne', hlogW1_pos.ne']
    rw [heq']
    calc (Real.log ((W + 1 : ℕ) : ℝ) - Real.log (W : ℝ)) / (Real.log (W : ℝ) * Real.log ((W + 1 : ℕ) : ℝ))
        ≤ (1 / (W : ℝ)) / (Real.log (W : ℝ) * Real.log (W : ℝ)) := by
          apply div_le_div₀ (by positivity) hdiff (by positivity) (by gcongr)
      _ = 1 / ((W : ℝ) * (Real.log (W : ℝ)) ^ 2) := by ring
  have hlogW_mul_gW1 : Real.log (W : ℝ) * g (W + 1) ≤ 1 / Real.log (W : ℝ) := by
    calc Real.log (W : ℝ) * g (W + 1) ≤ Real.log (W : ℝ) * g W :=
          mul_le_mul_of_nonneg_left hg_le_W hlogW_pos.le
      _ = 1 / Real.log (W : ℝ) := by dsimp [g]; field_simp [hlogW_pos.ne']
  have hW_inv_le : 1 / ((W + 1 : ℕ) : ℝ) ≤ 1 / (Real.log (W : ℝ)) ^ 2 := by
    have hWpos : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
    have hsq : (Real.log (W : ℝ)) ^ 2 ≤ ((W + 1 : ℕ) : ℝ) := by
      have hsqW : 0 < Real.sqrt (W : ℝ) := Real.sqrt_pos.mpr hWpos
      have h1 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt (W : ℝ) / Real.exp 1 by positivity)
      rw [Real.log_div hsqW.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
      have h2 : Real.log (W : ℝ) = 2 * Real.log (Real.sqrt (W : ℝ)) := by
        rw [Real.log_sqrt hWpos.le]; ring
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have hlog_le_sqrt : Real.log (W : ℝ) ≤ Real.sqrt (W : ℝ) := by
        have hdiv : Real.sqrt (W : ℝ) / Real.exp 1 ≤ Real.sqrt (W : ℝ) / 2 :=
          div_le_div_of_nonneg_left hsqW.le (by norm_num) he2
        linarith
      calc (Real.log (W : ℝ)) ^ 2 ≤ (Real.sqrt (W : ℝ)) ^ 2 :=
            pow_le_pow_left₀ hlogW_pos.le hlog_le_sqrt 2
        _ = (W : ℝ) := Real.sq_sqrt hWpos.le
        _ ≤ ((W + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact one_div_le_one_div_of_le (sq_pos_of_pos hlogW_pos) hsq
  have hB_inv_nn : (0 : ℝ) ≤ 1 / (B : ℝ) := by positivity
  have hW_step_g : 1 / ((W : ℝ) * (Real.log (W : ℝ)) ^ 2) ≤ 1 / (Real.log (W : ℝ)) ^ 2 := by
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
    have hpos : 0 < (Real.log (W : ℝ)) ^ 2 := sq_pos_of_pos hlogW_pos
    exact one_div_le_one_div_of_le hpos (by nlinarith)
  have hMB_term' : 1 / Real.log (B : ℝ) - 20 * g B ≤ M B * g B := by
    have : (Real.log (B : ℝ) - 20) * g B = Real.log (B : ℝ) * g B - 20 * g B := by ring
    linarith
  have hMW_term' : M W * g (W + 1) ≤ 1 / Real.log (W : ℝ) + 20 * g (W + 1) := by
    have : (Real.log (W : ℝ) + 20) * g (W + 1) = Real.log (W : ℝ) * g (W + 1) + 20 * g (W + 1) := by ring
    linarith
  have hgW_eq : g W = 1 / (Real.log (W : ℝ)) ^ 2 := rfl
  have h100 : 100 / (Real.log (W : ℝ)) ^ 2 = 100 * g W := by dsimp [g]; ring
  linarith

/- ### Section 4: Mertens' Third Theorem Bounds (`V(z) ≤ 1/log z` and `1/(3 log z) ≤ V(z)`) -/

lemma prod_one_sub_inv_le_inv_log (z : ℕ) (hz : 2 ≤ z) :
    ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) ≤ 1 / Real.log (z : ℝ) := by
  set P := (Finset.Icc 1 z).filter Nat.Prime
  have hprod_pos : 0 < ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)) := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hlog_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlog_le_harm : Real.log (z : ℝ) ≤ ∑ m ∈ Finset.Icc 1 z, (1 : ℝ) / (m : ℝ) := by
    have hstep : ∀ k : ℕ, 1 ≤ k → Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ 1 / (k : ℝ) := by
      intro k hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
      rw [← Real.log_div (by positivity) hkpos.ne']
      have h := Real.log_le_sub_one_of_pos (show 0 < ((k + 1 : ℕ) : ℝ) / k by positivity)
      have h2 : ((k + 1 : ℕ) : ℝ) / k - 1 = 1 / k := by push_cast; field_simp; ring
      linarith
    have hprev : ∀ M : ℕ, 1 ≤ M → Real.log (M : ℝ) ≤ ∑ m ∈ Finset.Icc 1 (M - 1), (1 : ℝ) / (m : ℝ) := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ j hj ihj =>
        have hI : Finset.Icc 1 j = insert j (Finset.Icc 1 (j - 1)) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        simp only [Nat.add_sub_cancel]
        rw [hI, Finset.sum_insert (by simp; omega)]
        linarith [hstep j hj]
    calc Real.log (z : ℝ) ≤ ∑ m ∈ Finset.Icc 1 (z - 1), (1 : ℝ) / (m : ℝ) := hprev z (by omega)
      _ ≤ ∑ m ∈ Finset.Icc 1 z, (1 : ℝ) / (m : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega)) (fun _ _ _ => by positivity)
  have hharm_le_prod : ∑ m ∈ Finset.Icc 1 z, (1 : ℝ) / (m : ℝ) ≤
      ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
    have hgeom_p : ∀ p ∈ P, ∑ e ∈ Finset.range (z + 1), (1 / (p : ℝ)) ^ e ≤ (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      set r : ℝ := 1 / (p : ℝ)
      have hr0 : 0 ≤ r := by positivity
      have hr1 : r < 1 := by dsimp [r]; rw [div_lt_one (by linarith)]; linarith
      rw [geom_sum_eq hr1.ne]
      have h1 : (r ^ (z + 1) - 1) / (r - 1) = (1 - r ^ (z + 1)) / (1 - r) := by
        rw [← neg_div_neg_eq]; ring_nf
      rw [h1, inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 (z + 1)]) (by linarith)
    have hprod_ge : ∏ p ∈ P, (∑ e ∈ Finset.range (z + 1), (1 / (p : ℝ)) ^ e) ≤
        ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ))⁻¹ :=
      Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun e _ => by positivity) hgeom_p
    have h_fintype : ∏ p ∈ P, (∑ e ∈ Finset.range (z + 1), (1 / (p : ℝ)) ^ e) =
        ∑ f : (P → Fin (z + 1)), ∏ p : P, (1 / (p.1 : ℝ)) ^ (f p).1 := by
      rw [← Finset.prod_coe_sort P]
      have hfin : ∏ p : P, ∑ e ∈ Finset.range (z + 1), (1 / (p.1 : ℝ)) ^ e =
          ∏ p : P, ∑ e : Fin (z + 1), (1 / (p.1 : ℝ)) ^ e.1 :=
        Finset.prod_congr rfl fun p _ => (Fin.sum_univ_eq_sum_range (fun e => (1 / (p.1 : ℝ)) ^ e) (z + 1)).symm
      rw [hfin, Fintype.prod_sum]
    have hmap : ∑ m ∈ Finset.Icc 1 z, (1 : ℝ) / (m : ℝ) ≤
        ∑ f : (P → Fin (z + 1)), ∏ p : P, (1 / (p.1 : ℝ)) ^ (f p).1 := by
      let facMap : (m : ℕ) → (m ∈ Finset.Icc 1 z) → (P → Fin (z + 1)) := fun m hm p =>
        ⟨m.factorization p.1, by
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hmz : m ≤ z := (Finset.mem_Icc.mp hm).2
          have hp_pr := (Finset.mem_filter.mp p.2).2
          have hpow : p.1 ^ (m.factorization p.1) ≤ m :=
            Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p.1)
          have hlt : m.factorization p.1 < p.1 ^ (m.factorization p.1) :=
            Nat.lt_pow_self hp_pr.one_lt
          omega⟩
      have hInj : ∀ m1 hm1 m2 hm2, facMap m1 hm1 = facMap m2 hm2 → m1 = m2 := by
        intro a ha b hb hab
        have ha0 : a ≠ 0 := by have := (Finset.mem_Icc.mp ha).1; omega
        have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp hb).1; omega
        have hfac : a.factorization = b.factorization := by
          ext p
          by_cases hp : p.Prime
          · by_cases hpz : p ≤ z
            · have hpP : p ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hpz⟩, hp⟩
              exact congrArg Fin.val (congrFun hab ⟨p, hpP⟩)
            · have ha_not : ¬ p ∣ a := fun hd => hpz ((Nat.le_of_dvd (by omega) hd).trans (Finset.mem_Icc.mp ha).2)
              have hb_not : ¬ p ∣ b := fun hd => hpz ((Nat.le_of_dvd (by omega) hd).trans (Finset.mem_Icc.mp hb).2)
              rw [Nat.factorization_eq_zero_of_not_dvd ha_not, Nat.factorization_eq_zero_of_not_dvd hb_not]
          · rw [Nat.factorization_eq_zero_of_not_prime a hp, Nat.factorization_eq_zero_of_not_prime b hp]
        exact Nat.factorization_inj ha0 hb0 hfac
      have hVal : ∀ m hm, ∏ p : P, (1 / (p.1 : ℝ)) ^ (facMap m hm p).1 = (1 : ℝ) / (m : ℝ) := by
        intro m hm
        have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
        have hmz : m ≤ z := (Finset.mem_Icc.mp hm).2
        have hsub : m.primeFactors ⊆ P := by
          intro p hp
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).one_le, ?_⟩,
            Nat.prime_of_mem_primeFactors hp⟩
          exact (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hmz
        have hprod_m : ∏ p ∈ P, p ^ (m.factorization p) = m := by
          rw [← Finset.prod_subset hsub]
          · exact Nat.prod_factorization_pow_eq_self hm0
          · intro p _ hnot
            have hz0 : m.factorization p = 0 := Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
            rw [hz0, pow_zero]
        dsimp [facMap]
        rw [Finset.prod_attach P (fun p => (1 / (p : ℝ)) ^ (m.factorization p))]
        simp only [one_div, inv_pow, Finset.prod_inv_distrib]
        congr 1
        exact_mod_cast hprod_m
      calc ∑ m ∈ Finset.Icc 1 z, (1 : ℝ) / (m : ℝ)
          = ∑ m ∈ (Finset.Icc 1 z).attach, ∏ p : P, (1 / (p.1 : ℝ)) ^ (facMap m.1 m.2 p).1 := by
              rw [← Finset.sum_attach (Finset.Icc 1 z)]
              exact Finset.sum_congr rfl fun m _ => (hVal m.1 m.2).symm
        _ = ∑ f ∈ (Finset.Icc 1 z).attach.image (fun m => facMap m.1 m.2),
              ∏ p : P, (1 / (p.1 : ℝ)) ^ (f p).1 := by
              rw [Finset.sum_image]
              intro a _ b _ hab
              exact Subtype.ext (hInj a.1 a.2 b.1 b.2 hab)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun f _ _ => Finset.prod_nonneg fun p _ => by positivity)
    exact hmap.trans (h_fintype ▸ hprod_ge)
  rw [le_div_iff₀ hlog_pos, mul_comm]
  have hcomb : Real.log (z : ℝ) ≤ (∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact hlog_le_harm.trans hharm_le_prod
  calc Real.log (z : ℝ) * ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ))
      ≤ (∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)))⁻¹ * ∏ p ∈ P, (1 - (1 : ℝ) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hcomb hprod_pos.le
    _ = 1 := inv_mul_cancel₀ hprod_pos.ne'

/- ### Section 5: Explicit Mertens Third Lower Bound (`1 / (3 * log z) ≤ ∏_{p ≤ z} (1 - 1/p)`) -/

private noncomputable def Sm (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)

private noncomputable def Lm (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, -Real.log (1 - (1 : ℝ) / (p : ℝ))

private noncomputable def Qm (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))

private noncomputable def cM : ℝ := 1 / 2

private noncomputable def Hm (n : ℕ) : ℝ :=
  Lm n - Real.log (Real.log (n : ℝ)) + (Real.log (n : ℝ) + cM - Sm n) / Real.log (n : ℝ) + 1 / (n : ℝ)

private lemma Qm_eq_exp (n : ℕ) : Qm n = Real.exp (-Lm n) := by
  unfold Qm Lm
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
  rw [neg_neg, Real.exp_log]
  rw [sub_pos, div_lt_one (by linarith)]; linarith

private lemma filter_range_succ_prime (n : ℕ) :
    (Finset.range (n + 2)).filter Nat.Prime =
      if (n + 1).Prime then insert (n + 1) ((Finset.range (n + 1)).filter Nat.Prime)
      else (Finset.range (n + 1)).filter Nat.Prime := by
  rw [Finset.range_add_one, Finset.filter_insert]

private lemma Sm_succ (n : ℕ) :
    Sm (n + 1) = Sm n + if (n + 1).Prime then Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) else 0 := by
  unfold Sm
  rw [filter_range_succ_prime]
  split_ifs with hp
  · rw [Finset.sum_insert (by simp)]; ring
  · ring

private lemma Lm_succ (n : ℕ) :
    Lm (n + 1) = Lm n + if (n + 1).Prime then -Real.log (1 - (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) else 0 := by
  unfold Lm
  rw [filter_range_succ_prime]
  split_ifs with hp
  · rw [Finset.sum_insert (by simp)]; ring
  · ring

private lemma sum_div_log_le_mertens (t : ℕ) :
    (t : ℝ) * Sm t - θ (t : ℝ) ≤ T_nat t := by
  have h1 := T_nat_eq_sum_vonMangoldt t
  have hsub : (Finset.range (t + 1)).filter Nat.Prime ⊆ Finset.Icc 1 t := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    exact ⟨hp.2.one_le, by omega⟩
  have hle : ∑ p ∈ (Finset.range (t + 1)).filter Nat.Prime, Λ p * ((t / p : ℕ) : ℝ) ≤ T_nat t := by
    rw [h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
  have htheta : θ (t : ℝ) = ∑ p ∈ (Finset.range (t + 1)).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [Chebyshev.theta]; simp only [Nat.floor_natCast]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hle⟩, hp⟩; exact ⟨by omega, hp⟩
    · rintro ⟨hlt, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩
  rw [htheta, Sm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.sum_le_sum fun p hp => ?_) hle
  have hp_pr := (Finset.mem_filter.mp hp).2
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp_pr]
  have hfl : (t : ℝ) / (p : ℝ) - 1 ≤ ((t / p : ℕ) : ℝ) := by
    have hlt := Nat.lt_div_mul_add (a := t) (b := p) hp_pr.pos
    have hle' : (t : ℝ) ≤ ((t / p : ℕ) : ℝ) * p + p := by exact_mod_cast (show t ≤ t / p * p + p by omega)
    rw [sub_le_iff_le_add, div_le_iff₀ hp_pos]; linarith
  have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.one_le)
  have h2 : (t : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ) = Real.log (p : ℝ) * ((t : ℝ) / p - 1) := by ring
  rw [h2]; exact mul_le_mul_of_nonneg_left hfl hlog_nn

private lemma Sm_le_log_add_cM (t : ℕ) (ht : 64 ≤ t) : Sm t ≤ Real.log (t : ℝ) + cM := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have h1 := sum_div_log_le_mertens t
  have h2 := (T_nat_le_integral t (by omega)).2
  have htheta := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ t by linarith)
  have hlog4 : Real.log 4 ≤ 1.387 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    have := Real.log_two_lt_d9; linarith
  have hlogt : Real.log (t : ℝ) + 1 ≤ (t : ℝ) / 10 := by
    have h64 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (t : ℝ) / 64 by positivity)
    rw [Real.log_div htpos.ne' (by norm_num)] at h64
    have hlog64 : Real.log (64 : ℝ) ≤ 4.16 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast
      have := Real.log_two_lt_d9; linarith
    have ht64 : (64 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hcomb : (t : ℝ) * Sm t ≤ (t : ℝ) * (Real.log (t : ℝ) + cM) := by
    unfold cM; nlinarith
  exact le_of_mul_le_mul_left hcomb htpos

private lemma Hm_step (m : ℕ) (hm : 64 ≤ m) : Hm (m + 1) ≤ Hm m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1pos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  set a : ℝ := Real.log (m : ℝ)
  set b : ℝ := Real.log ((m + 1 : ℕ) : ℝ)
  have ha_ge : (4 : ℝ) ≤ a := by
    dsimp [a]
    have h64 : (2 : ℝ) ^ 6 ≤ (m : ℝ) := by exact_mod_cast hm
    have hlog := Real.log_le_log (by positivity) h64
    rw [Real.log_pow] at hlog; push_cast at hlog
    have := Real.log_two_gt_d9; linarith
  have hab : a < b := Real.log_lt_log hmpos (by exact_mod_cast (by omega : m < m + 1))
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  have hS : Sm m ≤ a + cM := Sm_le_log_add_cM m hm
  have hdiff_Hm : Hm (m + 1) - Hm m =
      ((Lm (m + 1) - Lm m) - (Sm (m + 1) - Sm m) / b + (1 / ((m + 1 : ℕ) : ℝ) - 1 / (m : ℝ))) +
      (-(Real.log b - Real.log a) + (b - a) / b) +
      (a + cM - Sm m) * (1 / b - 1 / a) := by
    unfold Hm; dsimp only [a, b]
    field_simp [ha_pos.ne', hb_pos.ne']; ring
  have hterm1 : (Lm (m + 1) - Lm m) - (Sm (m + 1) - Sm m) / b +
      (1 / ((m + 1 : ℕ) : ℝ) - 1 / (m : ℝ)) ≤ 0 := by
    rw [Lm_succ, Sm_succ]
    simp only [add_sub_cancel_left]
    have hsub_inv : 1 / ((m + 1 : ℕ) : ℝ) - 1 / (m : ℝ) = -(1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) := by
      push_cast; field_simp [hmpos.ne', (show (m : ℝ) + 1 ≠ 0 by linarith)]; ring
    split_ifs with hp
    · have hdiv : (b / ((m + 1 : ℕ) : ℝ)) / b = 1 / ((m + 1 : ℕ) : ℝ) := by
        field_simp [hb_pos.ne', hm1pos.ne']
      rw [hdiv]
      have hlog_ub : -Real.log (1 - 1 / ((m + 1 : ℕ) : ℝ)) ≤ 1 / (m : ℝ) := by
        have hpos1 : (0 : ℝ) < 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
          rw [sub_pos, div_lt_one hm1pos]; push_cast; linarith
        have hinv : (1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ = 1 + 1 / (m : ℝ) := by
          push_cast; field_simp [hmpos.ne', (show (m : ℝ) + 1 ≠ 0 by linarith)]; ring
        rw [← Real.log_inv, hinv]
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (m : ℝ) by positivity)
        linarith
      linarith
    · simp only [zero_div, sub_zero, zero_add]
      rw [hsub_inv]
      have : (0 : ℝ) ≤ 1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by positivity
      linarith
  have hterm2 : -(Real.log b - Real.log a) + (b - a) / b ≤ 0 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < a / b by positivity)
    rw [Real.log_div ha_pos.ne' hb_pos.ne'] at h1
    have h2 : a / b - 1 = -((b - a) / b) := by field_simp [hb_pos.ne']; ring
    linarith
  have hterm3 : (a + cM - Sm m) * (1 / b - 1 / a) ≤ 0 := by
    have hr : 0 ≤ a + cM - Sm m := by linarith
    have hinv : 1 / b - 1 / a ≤ 0 := sub_nonpos.mpr (one_div_le_one_div_of_le ha_pos hab.le)
    exact mul_nonpos_of_nonneg_of_nonpos hr hinv
  linarith

private lemma Hm_le_Hm64 (n : ℕ) (hn : 64 ≤ n) : Hm n ≤ Hm 64 := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (Hm_step k hk).trans ih

private lemma filt64_eq :
    (Finset.range 65).filter Nat.Prime =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by
  decide

private lemma Qm64_val : Qm 64 = (770527199232000 : ℝ) / 5855632691117327 := by
  unfold Qm; rw [filt64_eq]; norm_num

private lemma log_ge_of_pow {p q m : ℕ} (hq : 0 < q) (h : (2 : ℝ) ^ m ≤ (p : ℝ) ^ q) :
    ((m : ℝ) / (q : ℝ)) * Real.log 2 ≤ Real.log (p : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hlog
  rw [div_mul_eq_mul_div, div_le_iff₀ hqpos]
  linarith

private lemma Sm64_ge : (2.80 : ℝ) ≤ Sm 64 := by
  unfold Sm
  rw [filt64_eq]
  repeat (rw [Finset.sum_insert (by decide)])
  rw [Finset.sum_singleton]
  have h2 : Real.log 2 ≥ 0.6931 := by have := Real.log_two_gt_d9; linarith
  have h3 : (19 / 12 : ℝ) * Real.log 2 ≤ Real.log 3 := log_three_bounds.1
  have h5 : (30 / 13 : ℝ) * Real.log 2 ≤ Real.log 5 := log_five_bounds.1
  have h7 : (28 / 10 : ℝ) * Real.log 2 ≤ Real.log 7 :=
    log_ge_of_pow (p := 7) (q := 10) (m := 28) (by decide) (by norm_num)
  have h11 : (34 / 10 : ℝ) * Real.log 2 ≤ Real.log 11 :=
    log_ge_of_pow (p := 11) (q := 10) (m := 34) (by decide) (by norm_num)
  have h13 : (37 / 10 : ℝ) * Real.log 2 ≤ Real.log 13 :=
    log_ge_of_pow (p := 13) (q := 10) (m := 37) (by decide) (by norm_num)
  have h17 : (40 / 10 : ℝ) * Real.log 2 ≤ Real.log 17 :=
    log_ge_of_pow (p := 17) (q := 10) (m := 40) (by decide) (by norm_num)
  have h19 : (42 / 10 : ℝ) * Real.log 2 ≤ Real.log 19 :=
    log_ge_of_pow (p := 19) (q := 10) (m := 42) (by decide) (by norm_num)
  have h23 : (45 / 10 : ℝ) * Real.log 2 ≤ Real.log 23 :=
    log_ge_of_pow (p := 23) (q := 10) (m := 45) (by decide) (by norm_num)
  have h29 : (48 / 10 : ℝ) * Real.log 2 ≤ Real.log 29 :=
    log_ge_of_pow (p := 29) (q := 10) (m := 48) (by decide) (by norm_num)
  have h31 : (49 / 10 : ℝ) * Real.log 2 ≤ Real.log 31 :=
    log_ge_of_pow (p := 31) (q := 10) (m := 49) (by decide) (by norm_num)
  have h37 : (52 / 10 : ℝ) * Real.log 2 ≤ Real.log 37 :=
    log_ge_of_pow (p := 37) (q := 10) (m := 52) (by decide) (by norm_num)
  have h41 : (53 / 10 : ℝ) * Real.log 2 ≤ Real.log 41 :=
    log_ge_of_pow (p := 41) (q := 10) (m := 53) (by decide) (by norm_num)
  have h43 : (54 / 10 : ℝ) * Real.log 2 ≤ Real.log 43 :=
    log_ge_of_pow (p := 43) (q := 10) (m := 54) (by decide) (by norm_num)
  have h47 : (55 / 10 : ℝ) * Real.log 2 ≤ Real.log 47 :=
    log_ge_of_pow (p := 47) (q := 10) (m := 55) (by decide) (by norm_num)
  have h53 : (57 / 10 : ℝ) * Real.log 2 ≤ Real.log 53 :=
    log_ge_of_pow (p := 53) (q := 10) (m := 57) (by decide) (by norm_num)
  have h59 : (58 / 10 : ℝ) * Real.log 2 ≤ Real.log 59 :=
    log_ge_of_pow (p := 59) (q := 10) (m := 58) (by decide) (by norm_num)
  have h61 : (59 / 10 : ℝ) * Real.log 2 ≤ Real.log 61 :=
    log_ge_of_pow (p := 61) (q := 10) (m := 59) (by decide) (by norm_num)
  push_cast
  linarith

private lemma Hm64_le_log_three : Hm 64 ≤ Real.log 3 := by
  unfold Hm cM
  have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; ring
  have hlog64_lo : (4.158 : ℝ) ≤ Real.log (64 : ℝ) := by
    rw [hlog64]; have := Real.log_two_gt_d9; linarith
  have hlog64_hi : Real.log (64 : ℝ) ≤ (4.16 : ℝ) := by
    rw [hlog64]; have := Real.log_two_lt_d9; linarith
  have hQpos : 0 < Qm 64 := by rw [Qm64_val]; norm_num
  have hLm64 : Lm 64 = -Real.log (Qm 64) := by
    rw [Qm_eq_exp, Real.log_exp, neg_neg]
  have hfrac : (Real.log (64 : ℝ) + 1 / 2 - Sm 64) / Real.log (64 : ℝ) ≤ (0.45 : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    linarith [Sm64_ge]
  have hexp_le : Real.exp (Lm 64 - Real.log (Real.log (64 : ℝ)) + 0.45 + 1 / 64) ≤ 3 := by
    rw [hLm64, show -Real.log (Qm 64) - Real.log (Real.log (64 : ℝ)) + 0.45 + 1 / 64 =
      (-Real.log (Qm 64) + -Real.log (Real.log (64 : ℝ))) + (0.45 + 1 / 64) by ring,
      Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_neg,
      Real.exp_log hQpos, Real.exp_log (by linarith)]
    have hinv_le : (Qm 64)⁻¹ * (Real.log (64 : ℝ))⁻¹ ≤ (1.83 : ℝ) := by
      rw [← mul_inv, inv_le_comm₀ (by positivity) (by norm_num)]
      rw [Qm64_val]; nlinarith
    have hexp162 : Real.exp (0.45 + 1 / 64 : ℝ) ≤ 1.62 := by
      have h1 : Real.exp ((0.45 + 1 / 64 : ℝ) / 8) ≤ (1 - (0.45 + 1 / 64 : ℝ) / 8)⁻¹ := by
        have hsub : 0 < 1 - (0.45 + 1 / 64 : ℝ) / 8 := by norm_num
        have hle := Real.add_one_le_exp (-((0.45 + 1 / 64 : ℝ) / 8))
        rw [Real.exp_neg] at hle
        rw [le_inv_comm₀ (Real.exp_pos _) hsub]; linarith
      rw [show (0.45 + 1 / 64 : ℝ) = ((8 : ℕ) : ℝ) * ((0.45 + 1 / 64 : ℝ) / 8) by push_cast; ring,
        Real.exp_nat_mul]
      calc (Real.exp ((0.45 + 1 / 64 : ℝ) / 8)) ^ 8
          ≤ ((1 - (0.45 + 1 / 64 : ℝ) / 8)⁻¹) ^ 8 := pow_le_pow_left₀ (Real.exp_pos _).le h1 8
        _ ≤ 1.62 := by norm_num
    nlinarith [Real.exp_pos (0.45 + 1 / 64 : ℝ)]
  have hle_exp : Real.exp (Lm 64 - Real.log (Real.log (64 : ℝ)) +
      (Real.log (64 : ℝ) + 1 / 2 - Sm 64) / Real.log (64 : ℝ) + 1 / 64) ≤ 3 :=
    (Real.exp_le_exp.mpr (by linarith)).trans hexp_le
  have hlog := Real.log_le_log (Real.exp_pos _) hle_exp
  rwa [Real.log_exp] at hlog

lemma prod_one_sub_inv_ge_inv_three_log (z : ℕ) (hz : 64 ≤ z) :
    1 / (3 * Real.log (z : ℝ)) ≤ ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) := by
  have heq_set : (Finset.Icc 1 z).filter Nat.Prime = (Finset.range (z + 1)).filter Nat.Prime := by
    ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hle⟩, hp⟩; exact ⟨by omega, hp⟩
    · rintro ⟨hlt, hp⟩; exact ⟨⟨hp.one_le, by omega⟩, hp⟩
  rw [heq_set]
  change 1 / (3 * Real.log (z : ℝ)) ≤ Qm z
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hH : Hm z ≤ Real.log 3 := (Hm_le_Hm64 z hz).trans Hm64_le_log_three
  have hS : 0 ≤ (Real.log (z : ℝ) + cM - Sm z) / Real.log (z : ℝ) :=
    div_nonneg (by linarith [Sm_le_log_add_cM z hz]) hlogz_pos.le
  have hinv_nn : (0 : ℝ) ≤ 1 / (z : ℝ) := by positivity
  have hLm : Lm z ≤ Real.log (3 * Real.log (z : ℝ)) := by
    rw [Real.log_mul (by norm_num) hlogz_pos.ne']
    unfold Hm at hH; linarith
  have hexp : Real.exp (-Real.log (3 * Real.log (z : ℝ))) ≤ Real.exp (-Lm z) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg, Real.exp_log (by positivity), ← one_div] at hexp
  rwa [Qm_eq_exp]

/-- Mertens second-type upper bound on `∑_{w < p ≤ z} 1 / p` for Brun's sieve. -/
lemma sum_inv_prime_Ioc_le {w z : ℕ} (hw : 64 ≤ w) (hwz : w ≤ z) :
    ∑ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      Real.log (Real.log (z : ℝ) / Real.log (w : ℝ)) + 2 := by
  have hw_pos : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
  have hz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  -- 1/p ≤ -log(1 - 1/p), so ∑_{w < p ≤ z} 1/p ≤ -log(V(z) / V(w))
  -- And V(z) ≥ 1 / (3 log z), V(w) ≤ 1 / log w ⇒ V(w) / V(z) ≤ 3 log z / log w!
  -- Taking log: ∑_{w < p ≤ z} 1/p ≤ log(3 * log z / log w) = log(log z / log w) + log 3 ≤ ... + 2!!
  have hterm : ∀ p ∈ (Finset.Ioc w z).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ) ≤ -Real.log (1 - (1 : ℝ) / (p : ℝ)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hpos : 0 < 1 - (1 : ℝ) / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hV_w := prod_one_sub_inv_le_inv_log w (by omega)
  have hV_z := prod_one_sub_inv_ge_inv_three_log z (by omega)
  have hsub : (Finset.Icc 1 w).filter Nat.Prime ⊆ (Finset.Icc 1 z).filter Nat.Prime := by
    intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢; exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
  have hsdiff : ((Finset.Icc 1 z).filter Nat.Prime) \ ((Finset.Icc 1 w).filter Nat.Prime) =
      (Finset.Ioc w z).filter Nat.Prime := by
    ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨_, hpz⟩, hp⟩, hnot⟩
      have hgt : w < p := by by_contra hle; exact hnot ⟨⟨hp.one_le, by omega⟩, hp⟩
      exact ⟨⟨hgt, hpz⟩, hp⟩
    · rintro ⟨⟨hpw, hpz⟩, hp⟩
      exact ⟨⟨⟨hp.one_le, hpz⟩, hp⟩, fun ⟨⟨_, hle⟩, _⟩ => by omega⟩
  have hprod_split : ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) =
      (∏ p ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))) *
        (∏ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))) := by
    rw [← hsdiff, mul_comm, Finset.prod_sdiff hsub]
  have hVw_pos : 0 < ∏ p ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) :=
    Finset.prod_pos fun p hp => by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hVz_pos : 0 < ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) :=
    Finset.prod_pos fun p hp => by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hV_Ioc_pos : 0 < ∏ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) :=
    Finset.prod_pos fun p hp => by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hV_Ioc_ge : Real.log (w : ℝ) / (3 * Real.log (z : ℝ)) ≤
      ∏ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) := by
    have h1 : ∏ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) =
        (∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))) /
          (∏ p ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))) := by
      rw [eq_div_iff hVw_pos.ne', mul_comm, ← hprod_split]
    rw [h1]
    calc Real.log (w : ℝ) / (3 * Real.log (z : ℝ))
        = (1 / (3 * Real.log (z : ℝ))) / (1 / Real.log (w : ℝ)) := by
            field_simp [hw_pos.ne', hz_pos.ne']
      _ ≤ (∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))) /
            (∏ p ∈ (Finset.Icc 1 w).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))) :=
            div_le_div₀ (by positivity) hV_z hVw_pos hV_w
  have hlog_Ioc : -Real.log (∏ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))) ≤
      Real.log (Real.log (z : ℝ) / Real.log (w : ℝ)) + 2 := by
    have h1 := Real.log_le_log (by positivity) hV_Ioc_ge
    rw [Real.log_div hw_pos.ne' (by positivity), Real.log_mul (by norm_num) hz_pos.ne'] at h1
    rw [Real.log_div hz_pos.ne' hw_pos.ne']
    have hlog3 : Real.log 3 ≤ 2 := by
      have : (3 : ℝ) ≤ Real.exp 2 := by
        have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
        have hm2 : (2 : ℝ) = ((2 : ℕ) : ℝ) * (1 : ℝ) := by norm_num
        rw [hm2, Real.exp_nat_mul]
        nlinarith
      simpa [Real.log_exp] using Real.log_le_log (by norm_num) this
    linarith
  have hlog_prod : ∑ p ∈ (Finset.Ioc w z).filter Nat.Prime, -Real.log (1 - (1 : ℝ) / (p : ℝ)) =
      -Real.log (∏ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))) := by
    rw [Finset.sum_neg_distrib, Real.log_prod]
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have : 0 < 1 - (1 : ℝ) / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
    exact this.ne'
  exact (Finset.sum_le_sum hterm).trans (hlog_prod ▸ hlog_Ioc)

end Erdos360H1Part1
end -- Erdos360_H1_part1.lean

section -- Erdos360_H1_part2.lean
open Finset Filter Real Nat
open scoped BigOperators Classical

namespace Erdos360H1Part2

lemma sum_divisors_rpow_eq_prod {n : ℕ} (hn : 1 ≤ n) (s : ℝ) :
    ∑ u ∈ n.divisors, (u : ℝ) ^ s =
      ∏ p ∈ n.primeFactors, ∑ j ∈ Finset.range (n.factorization p + 1), ((p : ℝ) ^ s) ^ j := by
  have hn0 : n ≠ 0 := by omega
  set P := n.primeFactors
  have hfin : ∏ p ∈ P, ∑ j ∈ Finset.range (n.factorization p + 1), ((p : ℝ) ^ s) ^ j =
      ∏ p : P, ∑ j : Fin (n.factorization p.1 + 1), ((p.1 : ℝ) ^ s) ^ j.1 := by
    rw [← Finset.prod_coe_sort P]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => ((p.1 : ℝ) ^ s) ^ j)]
  rw [hfin, Fintype.prod_sum]
  let facBij : (u : ℕ) → (u ∈ n.divisors) → ((p : P) → Fin (n.factorization p.1 + 1)) := fun u hu p =>
    ⟨u.factorization p.1, by
      have hudvd : u ∣ n := (Nat.mem_divisors.mp hu).1
      have hle := (Nat.factorization_le_iff_dvd (Nat.pos_of_dvd_of_pos hudvd (by omega)).ne' hn0).mpr hudvd p.1
      omega⟩
  refine Finset.sum_bij (fun u hu => facBij u hu) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro u1 hu1 u2 hu2 heq
    have hu1_ne : u1 ≠ 0 := (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hu1).1 (by omega)).ne'
    have hu2_ne : u2 ≠ 0 := (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hu2).1 (by omega)).ne'
    have hfac : u1.factorization = u2.factorization := by
      ext p
      by_cases hp : p ∈ P
      · exact congrArg Fin.val (congrFun heq ⟨p, hp⟩)
      · have h1 : p ∉ u1.primeFactors := fun h => hp (Nat.primeFactors_mono (Nat.mem_divisors.mp hu1).1 hn0 h)
        have h2 : p ∉ u2.primeFactors := fun h => hp (Nat.primeFactors_mono (Nat.mem_divisors.mp hu2).1 hn0 h)
        have hz1 : u1.factorization p = 0 := Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
        have hz2 : u2.factorization p = 0 := Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
        rw [hz1, hz2]
    exact Nat.factorization_inj hu1_ne hu2_ne hfac
  · intro e _
    let u := ∏ p : P, p.1 ^ (e p).1
    have hu_dvd : u ∣ n := by
      have hn_prod : n = ∏ p : P, p.1 ^ (n.factorization p.1) := by
        rw [Finset.prod_coe_sort P (fun p => p ^ (n.factorization p))]
        exact (Nat.prod_factorization_pow_eq_self hn0).symm
      rw [hn_prod]
      refine Finset.prod_dvd_prod_of_dvd _ _ fun p _ => ?_
      exact Nat.pow_dvd_pow p.1 (by have := (e p).2; omega)
    refine ⟨u, Nat.mem_divisors.mpr ⟨hu_dvd, hn0⟩, ?_⟩
    funext p
    apply Fin.ext
    dsimp [facBij, u]
    rw [Nat.factorization_prod (fun q _ => pow_ne_zero _ (Nat.prime_of_mem_primeFactors q.2).ne_zero)]
    simp only [Finsupp.finsetSum_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single p]
    · rw [(Nat.prime_of_mem_primeFactors p.2).factorization_self, mul_one]
    · intro q _ hqp
      have hne : q.1 ≠ p.1 := fun h => hqp (Subtype.ext h)
      have hndvd : ¬ p.1 ∣ q.1 := fun hd =>
        hne ((Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors p.2)
          (Nat.prime_of_mem_primeFactors q.2)).mp hd).symm
      rw [Nat.factorization_eq_zero_of_not_dvd hndvd, mul_zero]
    · intro h; exact absurd (Finset.mem_univ p) h
  · intro u hu
    have hu_pos : 0 < u := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hu).1 (by omega)
    have hsub : u.primeFactors ⊆ P := Nat.primeFactors_mono (Nat.mem_divisors.mp hu).1 hn0
    have hu_eq : u = ∏ p ∈ P, p ^ (u.factorization p) := by
      rw [← Finset.prod_subset hsub]
      · exact (Nat.prod_factorization_pow_eq_self hu_pos.ne').symm
      · intro p _ hnot
        have hz0 : u.factorization p = 0 := Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
        rw [hz0, pow_zero]
    conv_lhs => rw [hu_eq]
    rw [Nat.cast_prod, ← Real.finsetProd_rpow P (fun p => ((p ^ u.factorization p : ℕ) : ℝ))
      (fun p _ => Nat.cast_nonneg _)]
    rw [← Finset.prod_coe_sort P (fun p => ((p ^ u.factorization p : ℕ) : ℝ) ^ s)]
    refine Finset.prod_congr rfl fun p _ => ?_
    dsimp [facBij]
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm,
      Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]

lemma n_div_totient_eq_prod {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) / (n.totient : ℝ) = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
  have htot := Nat.totient_eq_mul_prod_factors n
  have hcast : (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
    have hq := congrArg (fun x : ℚ => (x : ℝ)) htot
    push_cast at hq
    simpa [one_div] using hq
  have hprod_pos : 0 < ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hcast, Finset.prod_inv_distrib]
  field_simp [hn_pos.ne', hprod_pos.ne']

lemma sum_divisors_inv_le {n : ℕ} (hn : 1 ≤ n) :
    ∑ u ∈ n.divisors, (1 : ℝ) / (u : ℝ) ≤ (n : ℝ) / (n.totient : ℝ) := by
  have heq := sum_divisors_rpow_eq_prod hn (-1 : ℝ)
  have hlhs : ∑ u ∈ n.divisors, (1 : ℝ) / (u : ℝ) = ∑ u ∈ n.divisors, (u : ℝ) ^ (-1 : ℝ) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Real.rpow_neg_one, one_div]
  rw [hlhs, heq, n_div_totient_eq_prod hn]
  refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun j _ => by positivity) fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  set r : ℝ := (p : ℝ) ^ (-1 : ℝ)
  have hr_eq : r = 1 / (p : ℝ) := by dsimp [r]; rw [Real.rpow_neg_one, one_div]
  have hr0 : 0 ≤ r := by rw [hr_eq]; positivity
  have hr1 : r < 1 := by rw [hr_eq, div_lt_one (by linarith)]; linarith
  rw [geom_sum_eq hr1.ne, ← hr_eq, inv_eq_one_div]
  have h1 : (r ^ (n.factorization p + 1) - 1) / (r - 1) = (1 - r ^ (n.factorization p + 1)) / (1 - r) := by
    rw [← neg_div_neg_eq]; ring_nf
  rw [h1]
  exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 (n.factorization p + 1)]) (by linarith)

private lemma prod_one_sub_inv_sq_ge (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (0.601 : ℝ) ≤ ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ) ^ 2) := by
  let P0 : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}
  have hP0_pos : ∀ p ∈ P0, (0 : ℝ) ≤ 1 - 1 / (p : ℝ) ^ 2 := by
    intro p hp
    have hp2 : 2 ≤ p := by fin_cases hp <;> decide
    have hp2r : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  have hS_sub : S = (S ∩ P0) ∪ (S \ P0) := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hdisj : Disjoint (S ∩ P0) (S \ P0) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).2
  rw [hS_sub, Finset.prod_union hdisj]
  have hpart1 : ∏ p ∈ P0, (1 - (1 : ℝ) / (p : ℝ) ^ 2) ≤ ∏ p ∈ S ∩ P0, (1 - (1 : ℝ) / (p : ℝ) ^ 2) := by
    have hsub : S ∩ P0 ⊆ P0 := Finset.inter_subset_right
    rw [← Finset.prod_sdiff hsub]
    have hle1 : ∏ p ∈ P0 \ (S ∩ P0), (1 - (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 :=
      Finset.prod_le_one (fun p hp => hP0_pos p (Finset.mem_sdiff.mp hp).1) (fun p _ => by
        have : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 := by positivity
        linarith)
    have hnn : 0 ≤ ∏ p ∈ S ∩ P0, (1 - (1 : ℝ) / (p : ℝ) ^ 2) :=
      Finset.prod_nonneg fun p hp => hP0_pos p (Finset.mem_inter.mp hp).2
    nlinarith
  have hP0_val : (0.6114 : ℝ) ≤ ∏ p ∈ P0, (1 - (1 : ℝ) / (p : ℝ) ^ 2) := by
    dsimp [P0]
    repeat (rw [Finset.prod_insert (by decide)])
    rw [Finset.prod_singleton]
    norm_num
  have hweier : ∀ (T : Finset ℕ), (∀ p ∈ T, (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 ∧ 1 / (p : ℝ) ^ 2 ≤ 1) →
      1 - ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ^ 2 ≤ ∏ p ∈ T, (1 - (1 : ℝ) / (p : ℝ) ^ 2) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert a T ha ih =>
      intro hT
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have haB := hT a (Finset.mem_insert_self a T)
      have hih := ih fun p hp => hT p (Finset.mem_insert_of_mem hp)
      have hprod_nn : 0 ≤ ∏ p ∈ T, (1 - (1 : ℝ) / (p : ℝ) ^ 2) :=
        Finset.prod_nonneg fun p hp => by linarith [(hT p (Finset.mem_insert_of_mem hp)).2]
      have hsum_nn : 0 ≤ ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ^ 2 :=
        Finset.sum_nonneg fun p hp => (hT p (Finset.mem_insert_of_mem hp)).1
      nlinarith
  have hT_cond : ∀ p ∈ S \ P0, 31 ≤ p ∧ Odd p := by
    intro p hp
    have hp_pr := hS p (Finset.mem_sdiff.mp hp).1
    have hp_not := (Finset.mem_sdiff.mp hp).2
    have hge31 : 31 ≤ p := by
      by_contra hlt
      push Not at hlt
      have h30 : p ∈ (Finset.range 31).filter Nat.Prime :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hp_pr⟩
      have hfilt30 : (Finset.range 31).filter Nat.Prime = P0 := by decide
      rw [hfilt30] at h30
      exact hp_not h30
    have hodd : Odd p := hp_pr.odd_of_ne_two (by omega)
    exact ⟨hge31, hodd⟩
  have hsum_tail : ∑ p ∈ S \ P0, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / 60 := by
    set M := (S \ P0).sup id + 31
    have hsub_map : S \ P0 ⊆ (Finset.Icc 15 M).image (fun k => 2 * k + 1) := by
      intro p hp
      obtain ⟨h31, k, rfl⟩ := hT_cond p hp
      refine Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, rfl⟩
      have hle : 2 * k + 1 ≤ (S \ P0).sup id := Finset.le_sup (f := id) hp
      omega
    have h1 : ∑ p ∈ S \ P0, (1 : ℝ) / (p : ℝ) ^ 2 ≤
        ∑ k ∈ Finset.Icc 15 M, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
      calc ∑ p ∈ S \ P0, (1 : ℝ) / (p : ℝ) ^ 2
          ≤ ∑ p ∈ (Finset.Icc 15 M).image (fun k : ℕ => 2 * k + 1), (1 : ℝ) / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_map (fun _ _ _ => by positivity)
        _ = ∑ k ∈ Finset.Icc 15 M, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 :=
            Finset.sum_image (fun a _ b _ hab => by omega)
    have h2 : ∀ k ∈ Finset.Icc 15 M,
        (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 ≤ (1 / 4 : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
      intro k hk
      have hk15 : 15 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsub : (1 / 4 : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) =
          1 / (4 * (k : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp [hkpos.ne', (show (k : ℝ) + 1 ≠ 0 by linarith)]; ring
      rw [hsub]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; nlinarith
    have htele : ∑ k ∈ Finset.Icc 15 M, (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) ≤ 1 / 15 := by
      have hM15 : 15 ≤ M := by omega
      have hexact : ∀ K : ℕ, 15 ≤ K →
          ∑ k ∈ Finset.Icc 15 K, (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) = 1 / 15 - 1 / ((K + 1 : ℕ) : ℝ) := by
        intro K hK
        induction K, hK using Nat.le_induction with
        | base => simp; norm_num
        | succ K hK ih =>
          have hI : Finset.Icc 15 (K + 1) = insert (K + 1) (Finset.Icc 15 K) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hI, Finset.sum_insert (by simp), ih]; ring
      rw [hexact M hM15]
      have : (0 : ℝ) ≤ 1 / ((M + 1 : ℕ) : ℝ) := by positivity
      linarith
    calc _ ≤ ∑ k ∈ Finset.Icc 15 M, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := h1
      _ ≤ ∑ k ∈ Finset.Icc 15 M, (1 / 4 : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) :=
            Finset.sum_le_sum h2
      _ = (1 / 4 : ℝ) * ∑ k ∈ Finset.Icc 15 M, (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
            rw [← Finset.mul_sum]
      _ ≤ (1 / 4 : ℝ) * (1 / 15) := mul_le_mul_of_nonneg_left htele (by norm_num)
      _ = 1 / 60 := by norm_num
  have hpart2 : (59 / 60 : ℝ) ≤ ∏ p ∈ S \ P0, (1 - (1 : ℝ) / (p : ℝ) ^ 2) := by
    have hw := hweier (S \ P0) (fun p hp => by
      have h31 := (hT_cond p hp).1
      have hpr : (31 : ℝ) ≤ p := by exact_mod_cast h31
      constructor
      · positivity
      · rw [div_le_one (by positivity)]; nlinarith)
    linarith
  nlinarith

lemma sum_divisors_inv_ge {n : ℕ} (hn : 1 ≤ n) :
    (0.601 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) ≤ ∑ u ∈ n.divisors, (1 : ℝ) / (u : ℝ) := by
  have heq := sum_divisors_rpow_eq_prod hn (-1 : ℝ)
  have hlhs : ∑ u ∈ n.divisors, (1 : ℝ) / (u : ℝ) = ∑ u ∈ n.divisors, (u : ℝ) ^ (-1 : ℝ) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Real.rpow_neg_one, one_div]
  rw [hlhs, heq, n_div_totient_eq_prod hn]
  have hprod_ge : ∏ p ∈ n.primeFactors, ((1 - (1 : ℝ) / (p : ℝ) ^ 2) * (1 - (1 : ℝ) / (p : ℝ))⁻¹) ≤
      ∏ p ∈ n.primeFactors, ∑ j ∈ Finset.range (n.factorization p + 1), ((p : ℝ) ^ (-1 : ℝ)) ^ j := by
    refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have h1 : (0 : ℝ) ≤ 1 - 1 / (p : ℝ) ^ 2 := by rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
      have h2 : (0 : ℝ) < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
      positivity
    · have hp_pr := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
      have hk1 : 1 ≤ n.factorization p := Nat.Prime.factorization_pos_of_dvd hp_pr (by omega) (Nat.dvd_of_mem_primeFactors hp)
      have hsub : {0, 1} ⊆ Finset.range (n.factorization p + 1) := by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hj ⊢; omega
      have hge01 : 1 + 1 / (p : ℝ) ≤ ∑ j ∈ Finset.range (n.factorization p + 1), ((p : ℝ) ^ (-1 : ℝ)) ^ j := by
        calc 1 + 1 / (p : ℝ) = ∑ j ∈ ({0, 1} : Finset ℕ), ((p : ℝ) ^ (-1 : ℝ)) ^ j := by
              rw [Finset.sum_pair (by decide), pow_zero, pow_one, Real.rpow_neg_one, one_div]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      have halg : (1 - (1 : ℝ) / (p : ℝ) ^ 2) * (1 - (1 : ℝ) / (p : ℝ))⁻¹ = 1 + 1 / (p : ℝ) := by
        have hne : 1 - (1 : ℝ) / (p : ℝ) ≠ 0 := by
          have : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
          linarith
        rw [mul_inv_eq_iff_eq_mul₀ hne]; ring
      linarith
  rw [Finset.prod_mul_distrib] at hprod_ge
  have hsq := prod_one_sub_inv_sq_ge n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have htot_nn : 0 ≤ ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))⁻¹ :=
    Finset.prod_nonneg fun p hp => by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (0 : ℝ) < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
      positivity
  exact (mul_le_mul_of_nonneg_right hsq htot_nn).trans hprod_ge

lemma sum_divisors_inv_tail_le :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℝ, (n : ℝ) ^ (1 / 64 : ℝ) ≤ U →
      ∑ u ∈ n.divisors.filter (fun u : ℕ => U < (u : ℝ)), (1 : ℝ) / (u : ℝ) ≤ (0.001 : ℝ) := by
  have hlog_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexp_lim : ∀ᶠ n : ℕ in atTop,
      Real.log (Real.log (n : ℝ)) ≥ 4 ∧
      Real.sqrt (Real.log (n : ℝ)) ≥ 2 ∧
      3 * Real.sqrt (Real.log (n : ℝ)) +
        6 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) / Real.log (Real.log (n : ℝ)) + 10 ≤
        Real.log (n : ℝ) / (64 * Real.log (Real.log (n : ℝ))) := by
    have h1 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
      (Real.tendsto_log_atTop.comp hlog_atTop).eventually (Filter.eventually_ge_atTop 4)
    have h2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := by
      filter_upwards [hlog_atTop.eventually (Filter.eventually_ge_atTop 4)] with n hn
      rw [Real.le_sqrt (by norm_num) (by linarith)]; norm_num; linarith
    have h3 : ∀ᶠ x : ℝ in atTop,
        3 * x ^ (1 / 2 : ℝ) * Real.log x + 6 * x ^ (5 / 8 : ℝ) + 10 * Real.log x ≤ x / 64 := by
      have ha : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (nhds 0) :=
        (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
      have hb : Tendsto (fun x : ℝ => x ^ (5 / 8 : ℝ) / x) atTop (nhds 0) := by
        have h := tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 8 by norm_num)
        refine h.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
        have h1 : x ^ (5 / 8 : ℝ) / x ^ (1 : ℝ) = x ^ ((5 / 8 : ℝ) - 1) := (Real.rpow_sub hx _ _).symm
        rw [Real.rpow_one] at h1
        rw [h1]; congr 1; norm_num
      have hc : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
        (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero.congr' (by
          filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x _; rw [Real.rpow_one])
      filter_upwards [ha.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000)),
        hb.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000)),
        hc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10000)),
        Filter.eventually_ge_atTop (1 : ℝ)] with x hxa hxb hxc hx1
      have hxpos : 0 < x := by linarith
      have h1' : 3 * x ^ (1 / 2 : ℝ) * Real.log x ≤ (3 / 1000) * x := by
        have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hxpos _)).mp hxa
        have hmul : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
          rw [← Real.rpow_add hxpos]; norm_num
        nlinarith [Real.rpow_pos_of_pos hxpos (1 / 2 : ℝ)]
      have h2' : 6 * x ^ (5 / 8 : ℝ) ≤ (6 / 1000) * x := by
        have h := (div_lt_iff₀ hxpos).mp hxb; linarith
      have h3' : 10 * Real.log x ≤ (10 / 10000) * x := by
        have h := (div_lt_iff₀ hxpos).mp hxc; linarith
      linarith
    filter_upwards [h1, h2, hlog_atTop.eventually h3] with n hn1 hn2 hn3
    refine ⟨hn1, hn2, ?_⟩
    have hll_pos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
    rw [Real.sqrt_eq_rpow]
    have hmul : (3 * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) +
        6 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) / Real.log (Real.log (n : ℝ)) + 10) *
        Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 64 := by
      have hsimp : (6 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) / Real.log (Real.log (n : ℝ))) *
          Real.log (Real.log (n : ℝ)) = 6 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) :=
        div_mul_cancel₀ _ hll_pos.ne'
      have hgoal : (3 * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) +
          6 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) / Real.log (Real.log (n : ℝ)) + 10) *
          Real.log (Real.log (n : ℝ)) =
          3 * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) +
            6 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) + 10 * Real.log (Real.log (n : ℝ)) := by
        field_simp [hll_pos.ne']
      rw [hgoal]
      exact hn3
    rw [show Real.log (n : ℝ) / (64 * Real.log (Real.log (n : ℝ))) =
      (Real.log (n : ℝ) / 64) / Real.log (Real.log (n : ℝ)) by ring, le_div_iff₀ hll_pos]
    exact hmul
  filter_upwards [hexp_lim, Filter.eventually_ge_atTop 100] with n ⟨hll4, hsq2, hineq⟩ hn100 U hU
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hll_pos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  set α : ℝ := 1 / Real.log (Real.log (n : ℝ))
  have hα_pos : 0 < α := by dsimp [α]; positivity
  have hα_le : α ≤ 1 / 4 := by dsimp [α]; rw [div_le_div_iff₀ hll_pos (by norm_num)]; linarith
  have hU_pos : 0 < U := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hU
  have hrankin : ∑ u ∈ n.divisors.filter (fun u : ℕ => U < (u : ℝ)), (1 : ℝ) / (u : ℝ) ≤
      U ^ (-α) * ∑ u ∈ n.divisors, (u : ℝ) ^ (α - 1) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ u ∈ n.divisors.filter (fun u : ℕ => U < (u : ℝ)), U ^ (-α) * (u : ℝ) ^ (α - 1) := by
          refine Finset.sum_le_sum fun u hu => ?_
          have hu_gt : U < (u : ℝ) := (Finset.mem_filter.mp hu).2
          have hu_pos : (0 : ℝ) < u := lt_trans hU_pos hu_gt
          have hpow : (1 : ℝ) ≤ ((u : ℝ) / U) ^ α :=
            Real.one_le_rpow ((one_le_div hU_pos).mpr hu_gt.le) hα_pos.le
          have hident : U ^ (-α) * (u : ℝ) ^ (α - 1) = ((u : ℝ) / U) ^ α * (1 / (u : ℝ)) := by
            rw [Real.div_rpow hu_pos.le hU_pos.le, Real.rpow_sub hu_pos, Real.rpow_neg hU_pos.le,
              Real.rpow_one]
            field_simp [hu_pos.ne', (Real.rpow_pos_of_pos hU_pos α).ne']
          rw [hident]
          calc (1 : ℝ) / (u : ℝ) = 1 * (1 / (u : ℝ)) := (one_mul _).symm
            _ ≤ ((u : ℝ) / U) ^ α * (1 / (u : ℝ)) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun u _ _ =>
          mul_nonneg (Real.rpow_nonneg hU_pos.le _) (Real.rpow_nonneg (Nat.cast_nonneg u) _))
  have heuler : ∑ u ∈ n.divisors, (u : ℝ) ^ (α - 1) ≤
      Real.exp (3 * ∑ p ∈ n.primeFactors, (p : ℝ) ^ (α - 1)) := by
    rw [sum_divisors_rpow_eq_prod (by omega) (α - 1), Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun j _ => by positivity) fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    set r : ℝ := (p : ℝ) ^ (α - 1)
    have hr_pos : 0 < r := Real.rpow_pos_of_pos (by linarith) _
    have hr_le : r ≤ 0.6 := by
      dsimp [r]
      have h1 : (p : ℝ) ^ (α - 1) ≤ (2 : ℝ) ^ (α - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      have h2 : (2 : ℝ) ^ (α - 1) ≤ (2 : ℝ) ^ (-3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h3 : (2 : ℝ) ^ (-3 / 4 : ℝ) ≤ 0.6 := by
        have hpow4 : ((2 : ℝ) ^ (-3 / 4 : ℝ)) ^ (4 : ℕ) ≤ (0.6 : ℝ) ^ (4 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
        exact le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (by norm_num) hpow4
      linarith
    have hgeom : ∑ j ∈ Finset.range (n.factorization p + 1), r ^ j ≤ 1 / (1 - r) := by
      rw [geom_sum_eq (by linarith)]
      have h1 : (r ^ (n.factorization p + 1) - 1) / (r - 1) = (1 - r ^ (n.factorization p + 1)) / (1 - r) := by
        rw [← neg_div_neg_eq]; ring_nf
      rw [h1]
      exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr_pos.le (n.factorization p + 1)]) (by linarith)
    have hexp : 1 / (1 - r) ≤ Real.exp (3 * r) := by
      rw [div_le_iff₀ (by linarith)]
      have h1 := Real.add_one_le_exp (3 * r)
      nlinarith
    exact hgeom.trans hexp
  set B : ℝ := Real.sqrt (Real.log (n : ℝ))
  have hB2 : 2 ≤ B := hsq2
  have hsum_split : ∑ p ∈ n.primeFactors, (p : ℝ) ^ (α - 1) ≤
      B + 2 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) / Real.log (Real.log (n : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not n.primeFactors (fun p : ℕ => (p : ℝ) ≤ B)]
    have hsmall : ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ B), (p : ℝ) ^ (α - 1) ≤ B := by
      have hterm : ∀ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ B), (p : ℝ) ^ (α - 1) ≤ 1 := by
        intro p hp
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_le
        exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
      have hsub : n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ B) ⊆ Finset.Icc 1 ⌊B⌋₊ := by
        intro p hp
        have hp1 := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_le
        have hple := (Finset.mem_filter.mp hp).2
        exact Finset.mem_Icc.mpr ⟨hp1, Nat.le_floor hple⟩
      calc _ ≤ ∑ _p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ B), (1 : ℝ) := Finset.sum_le_sum hterm
        _ = ((n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ B)).card : ℝ) := by simp
        _ ≤ ((Finset.Icc 1 ⌊B⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        _ = (⌊B⌋₊ : ℝ) := by simp
        _ ≤ B := Nat.floor_le (by linarith)
    have hbig : ∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ B), (p : ℝ) ^ (α - 1) ≤
        2 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) / Real.log (Real.log (n : ℝ)) := by
      set Big : Finset ℕ := n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ B)
      have hcard_bound : (Big.card : ℝ) ≤ 2 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) := by
        have hprod_le : ∏ p ∈ Big, (p : ℝ) ≤ (n : ℝ) := by
          have hdvd1 : ∏ p ∈ Big, p ∣ ∏ p ∈ n.primeFactors, p :=
            Finset.prod_dvd_prod_of_subset Big n.primeFactors (fun p : ℕ => p) (Finset.filter_subset _ _)
          have hdvd : ∏ p ∈ Big, p ∣ n := dvd_trans hdvd1 (Nat.prod_primeFactors_dvd n)
          have hle_nat : ∏ p ∈ Big, p ≤ n := Nat.le_of_dvd (by omega) hdvd
          rw [← Nat.cast_prod]; exact_mod_cast hle_nat
        have hBpow : B ^ Big.card ≤ ∏ p ∈ Big, (p : ℝ) := by
          calc B ^ Big.card = ∏ _p ∈ Big, B := by rw [Finset.prod_const]
            _ ≤ ∏ p ∈ Big, (p : ℝ) := Finset.prod_le_prod (fun _ _ => by linarith) (fun p hp => by
                have := (Finset.mem_filter.mp hp).2; linarith)
        have hlog := Real.log_le_log (by positivity) (hBpow.trans hprod_le)
        rw [Real.log_pow, Real.log_sqrt hlogn_pos.le] at hlog
        rw [le_div_iff₀ hll_pos]; linarith
      have hterm_big : ∀ p ∈ Big, (p : ℝ) ^ (α - 1) ≤ (Real.log (n : ℝ)) ^ (-3 / 8 : ℝ) := by
        intro p hp
        have hp_gt : B < (p : ℝ) := by have := (Finset.mem_filter.mp hp).2; linarith
        calc (p : ℝ) ^ (α - 1) ≤ B ^ (α - 1) :=
              Real.rpow_le_rpow_of_nonpos (by linarith) hp_gt.le (by linarith)
          _ = ((Real.log (n : ℝ)) ^ (1 / 2 : ℝ)) ^ (α - 1) := by dsimp [B]; rw [Real.sqrt_eq_rpow]
          _ = (Real.log (n : ℝ)) ^ ((1 / 2 : ℝ) * (α - 1)) := by rw [← Real.rpow_mul hlogn_pos.le]
          _ ≤ (Real.log (n : ℝ)) ^ (-3 / 8 : ℝ) := by
              have hlogn_ge1 : 1 ≤ Real.log (n : ℝ) := by
                have h3n : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
                have : Real.exp 1 ≤ (n : ℝ) := (Real.exp_one_lt_d9.le).trans (by linarith)
                simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
              exact Real.rpow_le_rpow_of_exponent_le hlogn_ge1 (by linarith)
      calc _ ≤ ∑ _p ∈ Big, (Real.log (n : ℝ)) ^ (-3 / 8 : ℝ) := Finset.sum_le_sum hterm_big
        _ = (Big.card : ℝ) * (Real.log (n : ℝ)) ^ (-3 / 8 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) * (Real.log (n : ℝ)) ^ (-3 / 8 : ℝ) :=
              mul_le_mul_of_nonneg_right hcard_bound (by positivity)
        _ = 2 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) / Real.log (Real.log (n : ℝ)) := by
              have hrp : Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-3 / 8 : ℝ) = (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) := by
                have h1 : (Real.log (n : ℝ)) ^ (1 : ℝ) * (Real.log (n : ℝ)) ^ (-3 / 8 : ℝ) =
                    (Real.log (n : ℝ)) ^ (1 + (-3 / 8 : ℝ)) := (Real.rpow_add hlogn_pos 1 (-3 / 8)).symm
                rw [Real.rpow_one] at h1
                convert h1 using 2; norm_num
              rw [mul_div_right_comm, mul_assoc, hrp]; ring
    linarith
  have hU_pow : U ^ (-α) ≤ Real.exp (-(Real.log (n : ℝ) / (64 * Real.log (Real.log (n : ℝ))))) := by
    have h1 : U ^ (-α) ≤ ((n : ℝ) ^ (1 / 64 : ℝ)) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hnpos _) hU (by linarith)
    rw [← Real.rpow_mul hnpos.le, Real.rpow_def_of_pos hnpos] at h1
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    dsimp [α]; ring_nf; exact le_rfl
  have hexp_10 : Real.exp (-10 : ℝ) ≤ (0.001 : ℝ) := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 10) (by norm_num)]
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have he10 : (2 : ℝ) ^ 10 ≤ Real.exp 10 := by
      have hmul : (10 : ℝ) = ((10 : ℕ) : ℝ) * (1 : ℝ) := by norm_num
      rw [hmul, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) he2 10
    linarith [show (1000 : ℝ) ≤ (2 : ℝ) ^ 10 by norm_num]
  have hineq_exp : 3 * ∑ p ∈ n.primeFactors, (p : ℝ) ^ (α - 1) -
      Real.log (n : ℝ) / (64 * Real.log (Real.log (n : ℝ))) ≤ -10 := by
    change 3 * B + 6 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) / Real.log (Real.log (n : ℝ)) + 10 ≤
      Real.log (n : ℝ) / (64 * Real.log (Real.log (n : ℝ))) at hineq
    have hmul3 : 3 * (2 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) / Real.log (Real.log (n : ℝ))) =
        6 * (Real.log (n : ℝ)) ^ (5 / 8 : ℝ) / Real.log (Real.log (n : ℝ)) := by ring
    linarith
  calc ∑ u ∈ n.divisors.filter (fun u : ℕ => U < (u : ℝ)), (1 : ℝ) / (u : ℝ)
      ≤ U ^ (-α) * ∑ u ∈ n.divisors, (u : ℝ) ^ (α - 1) := hrankin
    _ ≤ Real.exp (-(Real.log (n : ℝ) / (64 * Real.log (Real.log (n : ℝ))))) *
          Real.exp (3 * ∑ p ∈ n.primeFactors, (p : ℝ) ^ (α - 1)) :=
          mul_le_mul hU_pow heuler (Finset.sum_nonneg fun _ _ => by positivity) (Real.exp_pos _).le
    _ = Real.exp (3 * ∑ p ∈ n.primeFactors, (p : ℝ) ^ (α - 1) -
          Real.log (n : ℝ) / (64 * Real.log (Real.log (n : ℝ)))) := by
          rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-10 : ℝ) := Real.exp_le_exp.mpr hineq_exp
    _ ≤ 0.001 := hexp_10

lemma sum_divisors_inv_small_ge :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℝ, (n : ℝ) ^ (1 / 64 : ℝ) ≤ U →
      (0.60 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) ≤
        ∑ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ U), (1 : ℝ) / (u : ℝ) := by
  filter_upwards [sum_divisors_inv_tail_le, Filter.eventually_ge_atTop 1] with n htail hn1 U hU
  have hfull := sum_divisors_inv_ge hn1
  have hsplit : ∑ u ∈ n.divisors, (1 : ℝ) / (u : ℝ) =
      (∑ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ U), (1 : ℝ) / (u : ℝ)) +
        (∑ u ∈ n.divisors.filter (fun u : ℕ => U < (u : ℝ)), (1 : ℝ) / (u : ℝ)) := by
    have heq : n.divisors.filter (fun u : ℕ => U < (u : ℝ)) = n.divisors.filter (fun u : ℕ => ¬ (u : ℝ) ≤ U) := by
      ext u; simp only [Finset.mem_filter, not_le]
    rw [heq, Finset.sum_filter_add_sum_filter_not]
  have htot_ge1 : (1 : ℝ) ≤ (n : ℝ) / (n.totient : ℝ) := by
    have hpos : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    rw [one_le_div hpos]
    exact_mod_cast Nat.totient_le n
  have ht := htail U hU
  linarith

end Erdos360H1Part2
end -- Erdos360_H1_part2.lean

section -- Erdos360_H1_part3a.lean
open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped BigOperators ArithmeticFunction.Moebius Classical

namespace Erdos360H1Part3a

private lemma squarefree_prod_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Squarefree (∏ p ∈ P, p) := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert p P hp ih =>
    rw [Finset.prod_insert hp]
    have hp_pr := hP p (Finset.mem_insert_self p P)
    have hP_pr : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ P, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq_pr := hP_pr q hq
      have hne : p ≠ q := fun h => hp (h ▸ hq)
      exact (hp_pr.coprime_iff_not_dvd).mpr (fun hd => hne ((Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp hd))
    exact (Nat.squarefree_mul hcop).mpr ⟨hp_pr.squarefree, ih hP_pr⟩

private noncomputable def invId : ArithmeticFunction ℝ where
  toFun d := if d = 0 then 0 else (d : ℝ)⁻¹
  map_zero' := by simp

private lemma invId_mult : invId.IsMultiplicative := by
  constructor
  · simp [invId]
  · intro m n _
    dsimp [invId]
    by_cases hm : m = 0
    · simp [hm]
    · by_cases hn : n = 0
      · simp [hn]
      · have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
        simp only [hm, hn, hmn, ↓reduceIte, Nat.cast_mul, mul_inv]

private lemma invId_apply_of_ne_zero {d : ℕ} (hd : d ≠ 0) : invId d = (d : ℝ)⁻¹ := by
  simp [invId, hd]

private lemma sum_moebius_dvd_of_squarefree {P l m : ℕ} (hP : Squarefree P) (hmP : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hm0 : m ≠ 0 := ne_zero_of_dvd_ne_zero hP0 hmP
  have hm_sq : Squarefree m := Squarefree.squarefree_of_dvd hmP hP
  by_cases hlm : l ∣ m
  · have hl0 : l ≠ 0 := ne_zero_of_dvd_ne_zero hm0 hlm
    have hcop : Nat.Coprime l (m / l) :=
      Nat.coprime_of_squarefree_mul (by rwa [Nat.mul_div_cancel' hlm])
    have hbij : (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
        ∑ k ∈ (m / l).divisors, (μ (l * k) : ℝ) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun d _ => d / l) ?_ ?_ ?_ ?_
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
        refine ⟨?_, Nat.div_ne_zero_iff.mpr ⟨hl0, Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hlm⟩⟩
        obtain ⟨c, hc⟩ := hd.2.2
        refine ⟨c, ?_⟩
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hl0)
        rw [Nat.mul_div_cancel' hlm, ← mul_assoc, Nat.mul_div_cancel' hd.2.1, hc]
      · intro d1 hd1 d2 hd2 heq
        simp only [Finset.mem_filter] at hd1 hd2
        rw [← Nat.mul_div_cancel' hd1.2.1, ← Nat.mul_div_cancel' hd2.2.1, heq]
      · intro k hk
        rw [Nat.mem_divisors] at hk
        refine ⟨l * k, ?_, Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hl0)⟩
        simp only [Finset.mem_filter, Nat.mem_divisors]
        have hlk_dvd_m : l * k ∣ m := by
          have := mul_dvd_mul_left l hk.1
          rwa [Nat.mul_div_cancel' hlm] at this
        exact ⟨⟨hlk_dvd_m.trans hmP, hP0⟩, dvd_mul_right l k, hlk_dvd_m⟩
      · intro d hd
        simp only [Finset.mem_filter] at hd
        rw [Nat.mul_div_cancel' hd.2.1]
    rw [hbij]
    have hmul : ∀ k ∈ (m / l).divisors, (μ (l * k) : ℝ) = (μ l : ℝ) * (μ k : ℝ) := by
      intro k hk
      have hcop_lk : Nat.Coprime l k := hcop.coprime_dvd_right (Nat.mem_divisors.mp hk).1
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_lk]
      push_cast; rfl
    rw [Finset.sum_congr rfl hmul, ← Finset.mul_sum]
    have hzeta : ∑ k ∈ (m / l).divisors, (μ k : ℝ) = if m / l = 1 then 1 else 0 := by
      have h1 : (∑ k ∈ (m / l).divisors, μ k : ℤ) = if m / l = 1 then 1 else 0 := by
        have h := congrArg (fun f : ArithmeticFunction ℤ => f (m / l)) ArithmeticFunction.moebius_mul_coe_zeta
        rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
        exact h
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at h2
      simpa using h2
    rw [hzeta]
    have heq_iff : m / l = 1 ↔ l = m := by
      constructor
      · intro h1; have := Nat.mul_div_cancel' hlm; rw [h1, mul_one] at this; exact this
      · intro rfl; exact Nat.div_self (Nat.pos_of_ne_zero hl0)
    by_cases h : l = m
    · rw [if_pos (heq_iff.mpr h), if_pos h, mul_one]
    · rw [if_neg (mt heq_iff.mp h), if_neg h, mul_zero]
  · rw [if_neg (fun h => hlm (by rw [h]))]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [if_neg]
    rintro ⟨hld, hdm⟩
    exact hlm (hld.trans hdm)

private lemma moebius_sq_of_squarefree {l : ℕ} (hl : Squarefree l) : ((μ l : ℝ) ^ 2) = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hl]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

private lemma card_Ioc_filter_dvd (a b d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Ioc a b).filter (fun q => d ∣ q)).card = b / d - a / d := by
  have hsub : ∀ n : ℕ, ((Finset.Ioc 0 n).filter (fun q => d ∣ q)).card = n / d := by
    intro n
    have heq : (Finset.Ioc 0 n).filter (fun q => d ∣ q) = (Finset.Icc 1 (n / d)).image (fun m => d * m) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hq0, hqn⟩, m, rfl⟩
        refine ⟨m, ⟨?_, ?_⟩, rfl⟩
        · by_contra hm0; simp [show m = 0 by omega] at hq0
        · exact (Nat.le_div_iff_mul_le hd).mpr (by linarith)
      · rintro ⟨m, ⟨hm1, hmn⟩, rfl⟩
        refine ⟨⟨Nat.mul_pos hd hm1, ?_⟩, m, rfl⟩
        have := (Nat.le_div_iff_mul_le hd).mp hmn; linarith
    rw [heq, Finset.card_image_of_injective _ (fun x y h => Nat.eq_of_mul_eq_mul_left hd h)]
    simp
  by_cases hab : a ≤ b
  · have hsdiff : (Finset.Ioc a b).filter (fun q => d ∣ q) =
        ((Finset.Ioc 0 b).filter (fun q => d ∣ q)) \ ((Finset.Ioc 0 a).filter (fun q => d ∣ q)) := by
      ext q; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff]; omega
    have hsub' : (Finset.Ioc 0 a).filter (fun q => d ∣ q) ⊆ (Finset.Ioc 0 b).filter (fun q => d ∣ q) := by
      intro q hq; simp only [Finset.mem_filter, Finset.mem_Ioc] at hq ⊢; exact ⟨⟨hq.1.1, by omega⟩, hq.2⟩
    rw [hsdiff, Finset.card_sdiff_of_subset hsub', hsub b, hsub a]
  · have h1 : Finset.Ioc a b = ∅ := Finset.Ioc_eq_empty (by omega)
    have h2 : b / d ≤ a / d := Nat.div_le_div_right (by omega)
    rw [h1, Finset.filter_empty, Finset.card_empty]
    omega

private lemma log_succ_le_harmonic (K : ℕ) (hK : 1 ≤ K) :
    Real.log ((K + 1 : ℕ) : ℝ) ≤ ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) := by
  induction K, hK using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one]
    have := Real.log_two_lt_d9; push_cast; linarith
  | succ k hk ih =>
    have hI : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hI, Finset.sum_insert (by simp)]
    have hk1pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hstep : Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
      rw [← Real.log_div (by positivity) hk1pos.ne']
      have h := Real.log_le_sub_one_of_pos (show 0 < ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) by positivity)
      have h2 : ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = 1 / ((k + 1 : ℕ) : ℝ) := by
        push_cast; field_simp [show (k : ℝ) + 1 ≠ 0 by linarith]; ring
      linarith
    linarith

set_option maxHeartbeats 800000 in
/-- Selberg upper bound on an interval `Ioc a b` sifted by all primes `p ≤ √w`. -/
lemma selberg_interval_upper {a b : ℕ} (hab : a ≤ b) {w : ℝ} (hw : 4 ≤ w) :
    (((Finset.Ioc a b).filter (fun q => ∀ p ∈ (Finset.Icc 1 ⌊Real.sqrt w⌋₊).filter Nat.Prime, ¬ p ∣ q)).card : ℝ) ≤
      ((b - a : ℕ) : ℝ) / Real.log (Real.sqrt w) + w := by
  set y : ℝ := Real.sqrt w
  have hy2 : 2 ≤ y := by
    dsimp [y]; rw [Real.le_sqrt (by norm_num) (by linarith)]; norm_num; linarith
  have hy1 : 1 ≤ y := by linarith
  have hy_pos : 0 < y := by linarith
  set K : ℕ := ⌊y⌋₊
  have hK2 : 2 ≤ K := Nat.le_floor hy2
  have hK_le : (K : ℝ) ≤ y := Nat.floor_le hy_pos.le
  have hy_lt_K1 : y < (K : ℝ) + 1 := Nat.lt_floor_add_one y
  set P : Finset ℕ := (Finset.Icc 1 K).filter Nat.Prime
  set prodP : ℕ := ∏ p ∈ P, p
  have hP_prime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hprodP_sq : Squarefree prodP := squarefree_prod_primes P hP_prime
  have hprodP_ne : prodP ≠ 0 := hprodP_sq.ne_zero
  let s : SelbergSieve := {
    support := Finset.Ioc a b
    prodPrimes := prodP
    prodPrimes_squarefree := hprodP_sq
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one
    totalMass := ((b - a : ℕ) : ℝ)
    nu := invId
    nu_mult := invId_mult
    nu_pos_of_prime := fun p hp _ => by
      rw [invId_apply_of_ne_zero hp.ne_zero]
      exact inv_pos.mpr (by exact_mod_cast hp.pos)
    nu_lt_one_of_prime := fun p hp _ => by
      rw [invId_apply_of_ne_zero hp.ne_zero]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    level := y
    one_le_level := hy1
  }
  -- Identify siftedSum with the filtered cardinality
  have hsifted_eq : s.toBoundingSieve.siftedSum =
      (((Finset.Ioc a b).filter (fun q => ∀ p ∈ P, ¬ p ∣ q)).card : ℝ) := by
    unfold BoundingSieve.siftedSum
    dsimp only [s]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hq, hcop⟩
      refine ⟨hq, fun p hp hdvd => ?_⟩
      have hpd : p ∣ prodP := Finset.dvd_prod_of_mem id hp
      have hp_pr := hP_prime p hp
      exact (hp_pr.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hpd)) hdvd
    · rintro ⟨hq, hndvd⟩
      refine ⟨hq, Nat.Coprime.prod_left fun p hp => ?_⟩
      exact (hP_prime p hp).coprime_iff_not_dvd.mpr (hndvd p hp)
  -- Selberg denominator G
  let Lset (d : ℕ) : Finset ℕ := prodP.divisors.filter (fun l : ℕ => d ∣ l ∧ (l : ℝ) ≤ y)
  let G : ℝ := ∑ l ∈ Lset 1, s.toBoundingSieve.selbergTerms l
  -- Step 1: Lower bound G ≥ log y
  have hG_ge_log : Real.log y ≤ G := by
    have hlog_le : Real.log y ≤ ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) :=
      (Real.log_le_log hy_pos (by push_cast; exact hy_lt_K1.le)).trans (log_succ_le_harmonic K (by omega))
    -- Group m ∈ Icc 1 K by radical rad(m) = ∏ p ∈ m.primeFactors, p
    let rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p
    have hrad_mem : ∀ m ∈ Finset.Icc 1 K, rad m ∈ Lset 1 := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmK : m ≤ K := (Finset.mem_Icc.mp hm).2
      have hsub_P : m.primeFactors ⊆ P := by
        intro p hp
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).one_le, ?_⟩,
          Nat.prime_of_mem_primeFactors hp⟩
        exact (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hmK
      have hrad_dvd_P : rad m ∣ prodP := Finset.prod_dvd_prod_of_subset m.primeFactors P (fun p : ℕ => p) hsub_P
      have hrad_dvd_m : rad m ∣ m := Nat.prod_primeFactors_dvd m
      have hrad_le_K : rad m ≤ K := (Nat.le_of_dvd (by omega) hrad_dvd_m).trans hmK
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hrad_dvd_P, hprodP_ne⟩, one_dvd _, ?_⟩
      exact (by exact_mod_cast hrad_le_K : (rad m : ℝ) ≤ (K : ℝ)).trans hK_le
    have hgroup : ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) =
        ∑ l ∈ Lset 1, ∑ m ∈ (Finset.Icc 1 K).filter (fun m => rad m = l), (1 : ℝ) / (m : ℝ) := by
      rw [← Finset.sum_fiberwise_of_maps_to hrad_mem]
    have hfiber : ∀ l ∈ Lset 1,
        ∑ m ∈ (Finset.Icc 1 K).filter (fun m => rad m = l), (1 : ℝ) / (m : ℝ) ≤
          s.toBoundingSieve.selbergTerms l := by
      intro l hl
      have hlP : l ∣ prodP := (Nat.mem_divisors.mp (Finset.mem_filter.mp hl).1).1
      have hl_sq : Squarefree l := Squarefree.squarefree_of_dvd hlP hprodP_sq
      have hl_ne : l ≠ 0 := hl_sq.ne_zero
      -- selbergTerms l = ∏ p ∈ l.primeFactors, (1 / (p - 1))
      have hsel_eq : s.toBoundingSieve.selbergTerms l =
          ∏ p ∈ l.primeFactors, (1 / ((p : ℝ) - 1)) := by
        rw [BoundingSieve.selbergTerms_apply]
        have hnu_eq : s.toBoundingSieve.nu l = ∏ p ∈ l.primeFactors, (1 / (p : ℝ)) := by
          rw [← BoundingSieve.prod_primeFactors_nu hlP]
          refine Finset.prod_congr rfl fun p hp => ?_
          dsimp [s]; rw [invId_apply_of_ne_zero (Nat.prime_of_mem_primeFactors hp).ne_zero, one_div]
        rw [hnu_eq, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hp_pr := Nat.prime_of_mem_primeFactors hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
        dsimp [s]; rw [invId_apply_of_ne_zero hp_pr.ne_zero]
        field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
      rw [hsel_eq]
      -- Each p ∈ l.primeFactors has ∑_{e=1}^K (1/p)^e ≤ 1/(p-1)
      have hgeom_p : ∀ p ∈ l.primeFactors,
          ∑ e : Fin K, (1 / (p : ℝ)) ^ (e.1 + 1) ≤ 1 / ((p : ℝ) - 1) := by
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        set r : ℝ := 1 / (p : ℝ)
        have hr0 : 0 ≤ r := by positivity
        have hr1 : r < 1 := by dsimp [r]; rw [div_lt_one (by linarith)]; linarith
        have hsum_eq : ∑ e : Fin K, r ^ (e.1 + 1) = r * ∑ e ∈ Finset.range K, r ^ e := by
          rw [Fin.sum_univ_eq_sum_range (fun e => r ^ (e + 1)), Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => by ring
        rw [hsum_eq, geom_sum_eq hr1.ne]
        have h1 : (r ^ K - 1) / (r - 1) = (1 - r ^ K) / (1 - r) := by
          rw [← neg_div_neg_eq]; ring_nf
        rw [h1]
        calc r * ((1 - r ^ K) / (1 - r)) ≤ r * (1 / (1 - r)) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 K]) (by linarith)) hr0
          _ = 1 / ((p : ℝ) - 1) := by dsimp [r]; field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
      have hprod_le : ∏ p ∈ l.primeFactors, (∑ e : Fin K, (1 / (p : ℝ)) ^ (e.1 + 1)) ≤
          ∏ p ∈ l.primeFactors, (1 / ((p : ℝ) - 1)) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hgeom_p
      set Ql := l.primeFactors
      have hexpand : ∏ p ∈ Ql, (∑ e : Fin K, (1 / (p : ℝ)) ^ (e.1 + 1)) =
          ∑ f : (Ql → Fin K), ∏ p : Ql, (1 / (p.1 : ℝ)) ^ ((f p).1 + 1) := by
        rw [← Finset.prod_coe_sort Ql, Fintype.prod_sum]
      rw [hexpand] at hprod_le
      -- Inject fiber into (Ql → Fin K) via m ↦ (fun p => ⟨m.factorization p - 1, ...⟩)
      set Fib := (Finset.Icc 1 K).filter (fun m => rad m = l)
      have hpf_eq : ∀ m ∈ Fib, m.primeFactors = Ql := by
        intro m hm
        have hrad_eq : rad m = l := (Finset.mem_filter.mp hm).2
        have h1 : (rad m).primeFactors = m.primeFactors := by
          ext p
          simp only [Nat.mem_primeFactors, ne_eq]
          have hrad0 : rad m ≠ 0 := hrad_eq ▸ hl_ne
          have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1; omega
          constructor
          · rintro ⟨hp, hpdvd, _⟩
            have hmem := (hp.prime.dvd_finsetProd_iff id).mp hpdvd
            obtain ⟨q, hq, hpq⟩ := hmem
            have hq_pr := Nat.prime_of_mem_primeFactors hq
            have heq := (Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hpq
            subst heq; exact ⟨hp, Nat.dvd_of_mem_primeFactors hq, hm0⟩
          · rintro ⟨hp, hpdvd, _⟩
            exact ⟨hp, Finset.dvd_prod_of_mem id (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hm0⟩), hrad0⟩
        rw [← h1, hrad_eq]
      let fMap : (m : ℕ) → (m ∈ Fib) → (Ql → Fin K) := fun m hm p =>
        ⟨m.factorization p.1 - 1, by
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
          have hmK : m ≤ K := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
          have hp_m : p.1 ∈ m.primeFactors := by rw [hpf_eq m hm]; exact p.2
          have hp_pr := Nat.prime_of_mem_primeFactors hp_m
          have hpos : 1 ≤ m.factorization p.1 :=
            hp_pr.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp_m)
          have hpow : p.1 ^ (m.factorization p.1) ≤ m :=
            Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p.1)
          have hlt : m.factorization p.1 < p.1 ^ (m.factorization p.1) :=
            Nat.lt_pow_self hp_pr.one_lt
          omega⟩
      have hInj : ∀ m1 hm1 m2 hm2, fMap m1 hm1 = fMap m2 hm2 → m1 = m2 := by
        intro m1 hm1 m2 hm2 heq
        have hm10 : m1 ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm1).1).1; omega
        have hm20 : m2 ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm2).1).1; omega
        have hfac : m1.factorization = m2.factorization := by
          ext p
          by_cases hp : p ∈ Ql
          · have h1 : p ∈ m1.primeFactors := by rw [hpf_eq m1 hm1]; exact hp
            have h2 : p ∈ m2.primeFactors := by rw [hpf_eq m2 hm2]; exact hp
            have hpos1 : 1 ≤ m1.factorization p :=
              (Nat.prime_of_mem_primeFactors h1).factorization_pos_of_dvd hm10 (Nat.dvd_of_mem_primeFactors h1)
            have hpos2 : 1 ≤ m2.factorization p :=
              (Nat.prime_of_mem_primeFactors h2).factorization_pos_of_dvd hm20 (Nat.dvd_of_mem_primeFactors h2)
            have hsub := congrArg Fin.val (congrFun heq ⟨p, hp⟩)
            dsimp [fMap] at hsub; omega
          · have h1 : p ∉ m1.primeFactors := fun h => hp ((hpf_eq m1 hm1) ▸ h)
            have h2 : p ∉ m2.primeFactors := fun h => hp ((hpf_eq m2 hm2) ▸ h)
            have hz1 : m1.factorization p = 0 := Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
            have hz2 : m2.factorization p = 0 := Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
            rw [hz1, hz2]
        exact Nat.factorization_inj hm10 hm20 hfac
      have hVal : ∀ m hm, ∏ p : Ql, (1 / (p.1 : ℝ)) ^ ((fMap m hm p).1 + 1) = (1 : ℝ) / (m : ℝ) := by
        intro m hm
        have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1; omega
        have hprod_m : ∏ p ∈ Ql, p ^ (m.factorization p) = m := by
          rw [← hpf_eq m hm]; exact Nat.prod_factorization_pow_eq_self hm0
        have hexp_eq : ∀ p : Ql, (fMap m hm p).1 + 1 = m.factorization p.1 := by
          intro p
          have h1 : p.1 ∈ m.primeFactors := by rw [hpf_eq m hm]; exact p.2
          have hpos : 1 ≤ m.factorization p.1 :=
            (Nat.prime_of_mem_primeFactors h1).factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors h1)
          dsimp [fMap]; omega
        simp_rw [hexp_eq]
        rw [Finset.prod_coe_sort Ql (fun p => (1 / (p : ℝ)) ^ (m.factorization p))]
        simp only [one_div, inv_pow, Finset.prod_inv_distrib]
        congr 1; exact_mod_cast hprod_m
      have hfib_le : ∑ m ∈ Fib, (1 : ℝ) / (m : ℝ) ≤
          ∑ f : (Ql → Fin K), ∏ p : Ql, (1 / (p.1 : ℝ)) ^ ((f p).1 + 1) := by
        calc ∑ m ∈ Fib, (1 : ℝ) / (m : ℝ)
            = ∑ m ∈ Fib.attach, ∏ p : Ql, (1 / (p.1 : ℝ)) ^ ((fMap m.1 m.2 p).1 + 1) := by
                rw [← Finset.sum_attach Fib]
                exact Finset.sum_congr rfl fun m _ => (hVal m.1 m.2).symm
          _ = ∑ f ∈ Fib.attach.image (fun m => fMap m.1 m.2),
                ∏ p : Ql, (1 / (p.1 : ℝ)) ^ ((f p).1 + 1) := by
                rw [Finset.sum_image]
                intro a _ b _ h; exact Subtype.ext (hInj a.1 a.2 b.1 b.2 h)
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
      exact hfib_le.trans hprod_le
    exact hlog_le.trans (hgroup.trans_le (Finset.sum_le_sum hfiber))
  have hlog_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hG_pos : 0 < G := lt_of_lt_of_le hlog_pos hG_ge_log
  -- Step 2: Optimal Selberg weights
  let w_sel (d : ℕ) : ℝ :=
    if d ∣ prodP ∧ (d : ℝ) ≤ y then
      (μ d : ℝ) / (s.toBoundingSieve.nu d * G) * (∑ l ∈ Lset d, s.toBoundingSieve.selbergTerms l)
    else 0
  have hw1 : w_sel 1 = 1 := by
    dsimp [w_sel]
    rw [if_pos ⟨one_dvd prodP, by push_cast; exact hy1⟩]
    have hnu1 : s.toBoundingSieve.nu 1 = 1 := s.toBoundingSieve.nu_mult.map_one
    rw [hnu1, ArithmeticFunction.moebius_apply_one, Int.cast_one]
    change (1 : ℝ) / (1 * G) * G = 1
    field_simp [hG_pos.ne']
  -- Step 3: Diagonalized mainSum = 1 / G
  have hmain : s.toBoundingSieve.mainSum (lambdaSquared w_sel) = 1 / G := by
    rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq w_sel]
    have hinner : ∀ l ∈ prodP.divisors,
        (∑ d ∈ prodP.divisors, if l ∣ d then s.toBoundingSieve.nu d * w_sel d else 0) =
          if (l : ℝ) ≤ y then (μ l : ℝ) * s.toBoundingSieve.selbergTerms l / G else 0 := by
      intro l hl
      have hlP : l ∣ prodP := (Nat.mem_divisors.mp hl).1
      have hterm : ∀ d ∈ prodP.divisors,
          (if l ∣ d then s.toBoundingSieve.nu d * w_sel d else 0) =
            ∑ m ∈ Lset 1, if l ∣ d ∧ d ∣ m then (μ d : ℝ) * s.toBoundingSieve.selbergTerms m / G else 0 := by
        intro d hd
        have hdP : d ∣ prodP := (Nat.mem_divisors.mp hd).1
        have hnu_ne : s.toBoundingSieve.nu d ≠ 0 := BoundingSieve.nu_ne_zero hdP
        by_cases hld : l ∣ d
        · rw [if_pos hld]
          dsimp [w_sel]
          by_cases hdy : (d : ℝ) ≤ y
          · rw [if_pos ⟨hdP, hdy⟩]
            have hsimp : s.toBoundingSieve.nu d * ((μ d : ℝ) / (s.toBoundingSieve.nu d * G) *
                ∑ m ∈ Lset d, s.toBoundingSieve.selbergTerms m) =
                ∑ m ∈ Lset d, (μ d : ℝ) * s.toBoundingSieve.selbergTerms m / G := by
              rw [← mul_assoc, Finset.mul_sum]
              refine Finset.sum_congr rfl fun m _ => ?_
              field_simp [hnu_ne, hG_pos.ne']
            rw [hsimp, ← Finset.sum_filter]
            refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext m
            simp only [Lset, Finset.mem_filter, one_dvd, true_and]
            exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h3⟩, hld, h2⟩, fun ⟨⟨h1, h3⟩, _, h2⟩ => ⟨h1, h2, h3⟩⟩
          · rw [if_neg (fun h => hdy h.2), mul_zero]
            symm
            refine Finset.sum_eq_zero fun m hm => ?_
            rw [if_neg]
            rintro ⟨_, hdm⟩
            have hm_le : (m : ℝ) ≤ y := (Finset.mem_filter.mp hm).2.2
            have hm_pos : 0 < m := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hprodP_ne (Nat.mem_divisors.mp (Finset.mem_filter.mp hm).1).1)
            have hd_le_m : (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.le_of_dvd hm_pos hdm
            exact hdy (hd_le_m.trans hm_le)
        · rw [if_neg hld]
          symm
          refine Finset.sum_eq_zero fun m _ => ?_
          rw [if_neg]; rintro ⟨h, _⟩; exact hld h
      rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
      have hswap : ∀ m ∈ Lset 1,
          (∑ d ∈ prodP.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) * s.toBoundingSieve.selbergTerms m / G else 0) =
            if l = m then (μ l : ℝ) * s.toBoundingSieve.selbergTerms l / G else 0 := by
        intro m hm
        have hmP : m ∣ prodP := (Nat.mem_divisors.mp (Finset.mem_filter.mp hm).1).1
        have hpull : (∑ d ∈ prodP.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) * s.toBoundingSieve.selbergTerms m / G else 0) =
            (∑ d ∈ prodP.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) * (s.toBoundingSieve.selbergTerms m / G) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => ?_
          split_ifs <;> ring
        rw [hpull, sum_moebius_dvd_of_squarefree hprodP_sq hmP]
        split_ifs with heq
        · subst heq; ring
        · ring
      rw [Finset.sum_congr rfl hswap]
      by_cases hly : (l : ℝ) ≤ y
      · rw [if_pos hly]
        have hlL : l ∈ Lset 1 := Finset.mem_filter.mpr ⟨hl, one_dvd l, hly⟩
        rw [Finset.sum_eq_single l]
        · rw [if_pos rfl]
        · intro m _ hml; rw [if_neg (Ne.symm hml)]
        · intro h; exact absurd hlL h
      · rw [if_neg hly]
        refine Finset.sum_eq_zero fun m hm => ?_
        rw [if_neg]
        rintro rfl
        exact hly (Finset.mem_filter.mp hm).2.2
    have hsum_eq : ∑ l ∈ prodP.divisors, (s.toBoundingSieve.selbergTerms l)⁻¹ *
          (∑ d ∈ prodP.divisors, if l ∣ d then s.toBoundingSieve.nu d * w_sel d else 0) ^ 2 =
        ∑ l ∈ Lset 1, s.toBoundingSieve.selbergTerms l / G ^ 2 := by
      have h1 : ∀ l ∈ prodP.divisors,
          (s.toBoundingSieve.selbergTerms l)⁻¹ *
            (∑ d ∈ prodP.divisors, if l ∣ d then s.toBoundingSieve.nu d * w_sel d else 0) ^ 2 =
          if (l : ℝ) ≤ y then s.toBoundingSieve.selbergTerms l / G ^ 2 else 0 := by
        intro l hl
        rw [hinner l hl]
        split_ifs with hly
        · have hlP : l ∣ prodP := (Nat.mem_divisors.mp hl).1
          have hl_sq : Squarefree l := Squarefree.squarefree_of_dvd hlP hprodP_sq
          have hpos : s.toBoundingSieve.selbergTerms l ≠ 0 := (BoundingSieve.selbergTerms_pos hlP).ne'
          have hμ2 := moebius_sq_of_squarefree hl_sq
          have hcalc : (s.toBoundingSieve.selbergTerms l)⁻¹ * ((μ l : ℝ) * s.toBoundingSieve.selbergTerms l / G) ^ 2 =
              ((μ l : ℝ) ^ 2) * (s.toBoundingSieve.selbergTerms l / G ^ 2) := by
            field_simp [hpos, hG_pos.ne']
          rw [hcalc, hμ2, one_mul]
        · simp
      rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext l; simp only [Lset, Finset.mem_filter, one_dvd, true_and]
    rw [hsum_eq]
    have hdiv : ∑ l ∈ Lset 1, s.toBoundingSieve.selbergTerms l / G ^ 2 = G / G ^ 2 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]; rfl
    rw [hdiv]
    field_simp [hG_pos.ne']
  -- Step 4: Bound |w_sel d| ≤ 1 for all d
  have hw_abs : ∀ d : ℕ, |w_sel d| ≤ 1 := by
    intro d
    dsimp [w_sel]
    split_ifs with hcond
    · obtain ⟨hdP, hdy⟩ := hcond
      have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP hprodP_sq
      have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_sq.ne_zero
      have hnu_pos : 0 < s.toBoundingSieve.nu d := BoundingSieve.nu_pos_of_dvd_prodPrimes hdP
      have hμ_abs : |(μ d : ℝ)| = 1 := by
        have hsq := moebius_sq_of_squarefree hd_sq
        nlinarith [sq_abs (μ d : ℝ), abs_nonneg (μ d : ℝ)]
      have hsum_nn : 0 ≤ ∑ l ∈ Lset d, s.toBoundingSieve.selbergTerms l :=
        Finset.sum_nonneg fun l hl => (BoundingSieve.selbergTerms_pos (Nat.mem_divisors.mp (Finset.mem_filter.mp hl).1).1).le
      rw [abs_mul, abs_div, hμ_abs, abs_of_pos (mul_pos hnu_pos hG_pos), abs_of_nonneg hsum_nn]
      -- Show (s.nu d)⁻¹ * ∑ l ∈ Lset d, g l ≤ G
      let Kset := prodP.divisors.filter (fun k : ℕ => Nat.Coprime d k ∧ (d * k : ℝ) ≤ y)
      have hL_eq : ∑ l ∈ Lset d, s.toBoundingSieve.selbergTerms l =
          s.toBoundingSieve.selbergTerms d * ∑ k ∈ Kset, s.toBoundingSieve.selbergTerms k := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun l _ => l / d) ?_ ?_ ?_ ?_
        · intro l hl
          simp only [Lset, Kset, Finset.mem_filter, Nat.mem_divisors] at hl ⊢
          have hl_sq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 hprodP_sq
          have hcop : Nat.Coprime d (l / d) :=
            Nat.coprime_of_squarefree_mul (by rwa [Nat.mul_div_cancel' hl.2.1])
          refine ⟨⟨(Nat.div_dvd_of_dvd hl.2.1).trans hl.1.1, hprodP_ne⟩, hcop, ?_⟩
          have hmul : d * (l / d) = l := Nat.mul_div_cancel' hl.2.1
          have hcast : (d : ℝ) * ((l / d : ℕ) : ℝ) = (l : ℝ) := by exact_mod_cast hmul
          linarith [hl.2.2]
        · intro l1 hl1 l2 hl2 heq
          have h1 := (Finset.mem_filter.mp hl1).2.1
          have h2 := (Finset.mem_filter.mp hl2).2.1
          rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
        · intro k hk
          simp only [Kset, Lset, Finset.mem_filter, Nat.mem_divisors] at hk ⊢
          refine ⟨d * k, ?_, Nat.mul_div_cancel_left k hd_pos⟩
          have hdk_dvd : d * k ∣ prodP := hk.2.1.mul_dvd_of_dvd_of_dvd hdP hk.1.1
          refine ⟨⟨hdk_dvd, hprodP_ne⟩, dvd_mul_right d k, ?_⟩
          have hcast : ((d * k : ℕ) : ℝ) = (d : ℝ) * (k : ℝ) := by push_cast; rfl
          linarith [hk.2.2]
        · intro l hl
          have hld := (Finset.mem_filter.mp hl).2.1
          have hl_sq : Squarefree l := Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp (Finset.mem_filter.mp hl).1).1 hprodP_sq
          have hcop : Nat.Coprime d (l / d) :=
            Nat.coprime_of_squarefree_mul (by rwa [Nat.mul_div_cancel' hld])
          rw [← s.toBoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime hcop,
            Nat.mul_div_cancel' hld]
      have hgd_nu := BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv (s := s.toBoundingSieve) hdP
      have hprod_le_G : (s.toBoundingSieve.selbergTerms d * (s.toBoundingSieve.nu d)⁻¹) *
          ∑ k ∈ Kset, s.toBoundingSieve.selbergTerms k ≤ G := by
        rw [← hgd_nu, ← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hprodP_ne hdP,
          Finset.sum_mul]
        have hstep : ∑ e ∈ d.divisors, s.toBoundingSieve.selbergTerms e *
              ∑ k ∈ Kset, s.toBoundingSieve.selbergTerms k =
            ∑ p ∈ d.divisors ×ˢ Kset, s.toBoundingSieve.selbergTerms (p.1 * p.2) := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl fun e he => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hed : e ∣ d := (Nat.mem_divisors.mp he).1
          have hcop_dk : Nat.Coprime d k := (Finset.mem_filter.mp hk).2.1
          exact (s.toBoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime
            (hcop_dk.coprime_dvd_left hed)).symm
        rw [hstep]
        have hInj : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (d.divisors ×ˢ Kset : Finset (ℕ × ℕ)) := by
          intro p1 hp1 p2 hp2 heq
          dsimp only at heq
          simp only [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors, Kset, Finset.mem_filter] at hp1 hp2
          have he1 : Nat.gcd (p1.1 * p1.2) d = p1.1 := by
            rw [Nat.Coprime.gcd_mul_right_cancel p1.1 hp1.2.2.1.symm, Nat.gcd_eq_left hp1.1.1]
          have he2 : Nat.gcd (p2.1 * p2.2) d = p2.1 := by
            rw [Nat.Coprime.gcd_mul_right_cancel p2.1 hp2.2.2.1.symm, Nat.gcd_eq_left hp2.1.1]
          have hf1 : p1.1 = p2.1 := by rw [← he1, heq, he2]
          have hp1_pos : 0 < p1.1 := Nat.pos_of_dvd_of_pos hp1.1.1 hd_pos
          have hf2 : p1.2 = p2.2 := Nat.eq_of_mul_eq_mul_left hp1_pos (hf1 ▸ heq)
          exact Prod.ext hf1 hf2
        have hsub : (d.divisors ×ˢ Kset).image (fun p => p.1 * p.2) ⊆ Lset 1 := by
          intro m hm
          obtain ⟨⟨e, k⟩, hmem, rfl⟩ := Finset.mem_image.mp hm
          simp only [Finset.mem_product, Nat.mem_divisors, Kset, Finset.mem_filter] at hmem
          have hed : e ∣ d := hmem.1.1
          have hcop_ek : Nat.Coprime e k := hmem.2.2.1.coprime_dvd_left hed
          have hek_dvd : e * k ∣ prodP := hcop_ek.mul_dvd_of_dvd_of_dvd (hed.trans hdP) hmem.2.1.1
          have he_le_d : (e : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.le_of_dvd hd_pos hed
          have hle_y : ((e * k : ℕ) : ℝ) ≤ y := by
            push_cast
            calc (e : ℝ) * (k : ℝ) ≤ (d : ℝ) * (k : ℝ) := mul_le_mul_of_nonneg_right he_le_d (Nat.cast_nonneg k)
              _ ≤ y := hmem.2.2.2
          exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hek_dvd, hprodP_ne⟩, one_dvd _, hle_y⟩
        rw [← Finset.sum_image (fun a ha b hb h => hInj ha hb h)]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l hl _ =>
          (BoundingSieve.selbergTerms_pos (Nat.mem_divisors.mp (Finset.mem_filter.mp hl).1).1).le)
      rw [hL_eq]
      have hrearr : 1 / (s.toBoundingSieve.nu d * G) *
          (s.toBoundingSieve.selbergTerms d * ∑ k ∈ Kset, s.toBoundingSieve.selbergTerms k) =
          ((s.toBoundingSieve.selbergTerms d * (s.toBoundingSieve.nu d)⁻¹) *
            ∑ k ∈ Kset, s.toBoundingSieve.selbergTerms k) / G := by
        field_simp [hnu_pos.ne', hG_pos.ne']
      rw [hrearr, div_le_one hG_pos]
      exact hprod_le_G
    · norm_num
  -- Step 5: Remainder bound |s.rem d| ≤ 1 for d ∣ prodP
  have hrem_le : ∀ d ∈ prodP.divisors, |s.toBoundingSieve.rem d| ≤ 1 := by
    intro d hd
    have hdP : d ∣ prodP := (Nat.mem_divisors.mp hd).1
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hprodP_ne hdP)
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    dsimp [BoundingSieve.rem, BoundingSieve.multSum, s]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, card_Ioc_filter_dvd a b d hd1,
      invId_apply_of_ne_zero (by omega)]
    have ha_lo : (a : ℝ) / d - 1 < ((a / d : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := a) (b := d) hd1
      have hcast : (a : ℝ) < ((a / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hdpos]; linarith
    have ha_hi : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := by
      rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self a d
    have hb_lo : (b : ℝ) / d - 1 < ((b / d : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := b) (b := d) hd1
      have hcast : (b : ℝ) < ((b / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hdpos]; linarith
    have hb_hi : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / d := by
      rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self b d
    have hdiv_le : a / d ≤ b / d := Nat.div_le_div_right hab
    rw [Nat.cast_sub hdiv_le, Nat.cast_sub hab, abs_le]
    have hinv_eq : (d : ℝ)⁻¹ * ((b : ℝ) - (a : ℝ)) = (b : ℝ) / d - (a : ℝ) / d := by
      field_simp [hdpos.ne']
    rw [hinv_eq]
    constructor <;> linarith
  -- Step 6: Error sum bound errSum ≤ w
  have herr_le : s.toBoundingSieve.errSum (lambdaSquared w_sel) ≤ w := by
    unfold BoundingSieve.errSum
    have h1 : ∑ d ∈ prodP.divisors, |lambdaSquared w_sel d| * |s.toBoundingSieve.rem d| ≤
        ∑ d ∈ prodP.divisors, |lambdaSquared w_sel d| :=
      Finset.sum_le_sum fun d hd => by
        calc |lambdaSquared w_sel d| * |s.toBoundingSieve.rem d|
            ≤ |lambdaSquared w_sel d| * 1 := mul_le_mul_of_nonneg_left (hrem_le d hd) (abs_nonneg _)
          _ = |lambdaSquared w_sel d| := mul_one _
    have h2 : ∀ d ∈ prodP.divisors, |lambdaSquared w_sel d| ≤
        ∑ d1 ∈ prodP.divisors, ∑ d2 ∈ prodP.divisors,
          if d = Nat.lcm d1 d2 then |w_sel d1| * |w_sel d2| else 0 := by
      intro d hd
      unfold lambdaSquared
      calc |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w_sel d1 * w_sel d2 else 0|
          ≤ ∑ d1 ∈ d.divisors, |∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then w_sel d1 * w_sel d2 else 0| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |if d = Nat.lcm d1 d2 then w_sel d1 * w_sel d2 else 0| :=
            Finset.sum_le_sum fun d1 _ => Finset.abs_sum_le_sum_abs _ _
        _ = ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then |w_sel d1| * |w_sel d2| else 0 := by
            refine Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ => ?_
            split_ifs <;> simp [abs_mul]
        _ ≤ ∑ d1 ∈ prodP.divisors, ∑ d2 ∈ prodP.divisors,
              if d = Nat.lcm d1 d2 then |w_sel d1| * |w_sel d2| else 0 := by
            have hsub_d : d.divisors ⊆ prodP.divisors :=
              Nat.divisors_subset_of_dvd hprodP_ne (Nat.mem_divisors.mp hd).1
            refine (Finset.sum_le_sum fun d1 _ => Finset.sum_le_sum_of_subset_of_nonneg hsub_d
              (fun _ _ _ => by split_ifs <;> positivity)).trans ?_
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub_d
              (fun _ _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity)
    have h3 : ∑ d ∈ prodP.divisors, ∑ d1 ∈ prodP.divisors, ∑ d2 ∈ prodP.divisors,
          (if d = Nat.lcm d1 d2 then |w_sel d1| * |w_sel d2| else 0) =
        (∑ d1 ∈ prodP.divisors, |w_sel d1|) ^ 2 := by
      rw [Finset.sum_comm]
      have hinner : ∀ d1 ∈ prodP.divisors,
          (∑ d ∈ prodP.divisors, ∑ d2 ∈ prodP.divisors,
            if d = Nat.lcm d1 d2 then |w_sel d1| * |w_sel d2| else 0) =
          |w_sel d1| * ∑ d2 ∈ prodP.divisors, |w_sel d2| := by
        intro d1 hd1
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d2 hd2 => ?_
        have hlcm_mem : Nat.lcm d1 d2 ∈ prodP.divisors :=
          Nat.mem_divisors.mpr ⟨Nat.lcm_dvd (Nat.mem_divisors.mp hd1).1 (Nat.mem_divisors.mp hd2).1, hprodP_ne⟩
        rw [Finset.sum_ite_eq' prodP.divisors (Nat.lcm d1 d2), if_pos hlcm_mem]
      rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, sq]
    have h4 : ∑ d1 ∈ prodP.divisors, |w_sel d1| ≤ y := by
      have hsub : Lset 1 ⊆ Finset.Icc 1 K := by
        intro d hd
        simp only [Lset, Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at hd ⊢
        exact ⟨Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hprodP_ne hd.1.1), Nat.le_floor hd.2.2⟩
      have hsupp : ∑ d1 ∈ prodP.divisors, |w_sel d1| = ∑ d1 ∈ Lset 1, |w_sel d1| := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun l : ℕ => 1 ∣ l ∧ (l : ℝ) ≤ y) prodP.divisors)]
        intro d hd hnot
        have hgt : ¬ (d : ℝ) ≤ y := by
          intro hle; exact hnot (Finset.mem_filter.mpr ⟨hd, one_dvd d, hle⟩)
        have h0 : w_sel d = 0 := by dsimp [w_sel]; rw [if_neg (fun h => hgt h.2)]
        simp [h0]
      rw [hsupp]
      calc ∑ d1 ∈ Lset 1, |w_sel d1| ≤ ∑ _d1 ∈ Lset 1, (1 : ℝ) := Finset.sum_le_sum fun d1 _ => hw_abs d1
        _ = ((Lset 1).card : ℝ) := by simp
        _ ≤ ((Finset.Icc 1 K).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        _ = (K : ℝ) := by simp
        _ ≤ y := hK_le
    calc _ ≤ ∑ d ∈ prodP.divisors, |lambdaSquared w_sel d| := h1
      _ ≤ (∑ d1 ∈ prodP.divisors, |w_sel d1|) ^ 2 := (Finset.sum_le_sum h2).trans_eq h3
      _ ≤ y ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) h4 2
      _ = w := Real.sq_sqrt (by linarith)
  -- Step 7: Combine via Mathlib's Selberg main inequality!
  have hsel := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius (s := s.toBoundingSieve)
    (lambdaSquared w_sel) (BoundingSieve.upperMoebius_lambdaSquared w_sel hw1)
  rw [hsifted_eq, hmain] at hsel
  have hmass_nn : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmain_le : ((b - a : ℕ) : ℝ) * (1 / G) ≤ ((b - a : ℕ) : ℝ) / Real.log y := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hmass_nn hlog_pos hG_ge_log
  dsimp only [s] at hsel
  have hgoal : (((Finset.Ioc a b).filter (fun q => ∀ p ∈ P, ¬ p ∣ q)).card : ℝ) ≤
      ((b - a : ℕ) : ℝ) / Real.log y + w := by linarith
  convert hgoal

end Erdos360H1Part3a
end -- Erdos360_H1_part3a.lean

section -- Erdos360_H1_part3b.lean
open Finset Filter Real Nat
open scoped BigOperators Classical

namespace Erdos360H1Part3b

/- ### Section 1: Brun's Combinatorial Sieve Pointwise Inequality -/

private lemma alternating_choose_sum {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    ∑ j ∈ Finset.range (K + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) =
      (-1 : ℝ) ^ K * ((n - 1).choose K : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have hpas : n.choose (K + 1) = (n - 1).choose K + (n - 1).choose (K + 1) := by
      have h := Nat.choose_succ_succ (n - 1) K
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hn] at h
      exact h
    have hpas_r : (n.choose (K + 1) : ℝ) = ((n - 1).choose K : ℝ) + ((n - 1).choose (K + 1) : ℝ) := by
      exact_mod_cast hpas
    rw [hpas_r, pow_succ (-1 : ℝ) K]
    ring

private lemma alternating_powerset_le (M : Finset ℕ) (hM : M.Nonempty) (K : ℕ) :
    ∑ D ∈ M.powerset.filter (fun D => D.card ≤ K), (-1 : ℝ) ^ D.card =
      (-1 : ℝ) ^ K * ((M.card - 1).choose K : ℝ) := by
  have hpart : M.powerset.filter (fun D => D.card ≤ K) =
      (Finset.range (K + 1)).biUnion (fun j => M.powersetCard j) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hDM, hcard⟩; exact ⟨D.card, by omega, hDM, rfl⟩
    · rintro ⟨j, hj, hDM, rfl⟩; exact ⟨hDM, by omega⟩
  have hpw : (Finset.range (K + 1) : Set ℕ).PairwiseDisjoint (fun j => M.powersetCard j) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro D hi hj
    rw [Finset.mem_powersetCard] at hi hj
    exact hij (hi.2.symm.trans hj.2)
  rw [hpart, Finset.sum_biUnion hpw]
  have hterm : ∀ j ∈ Finset.range (K + 1),
      ∑ D ∈ M.powersetCard j, (-1 : ℝ) ^ D.card = (-1 : ℝ) ^ j * (M.card.choose j : ℝ) := by
    intro j _
    have hcongr : ∑ D ∈ M.powersetCard j, (-1 : ℝ) ^ D.card =
        ∑ _D ∈ M.powersetCard j, (-1 : ℝ) ^ j :=
      Finset.sum_congr rfl fun D hD => by rw [(Finset.mem_powersetCard.mp hD).2]
    rw [hcongr, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl hterm]
  exact alternating_choose_sum (Finset.card_pos.mpr hM) K

private def blockUnion (B : ℕ → Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range k).biUnion B

private abbrev brunAdm (B : ℕ → Finset ℕ) (b : ℕ → ℕ) (k : ℕ) (D : Finset ℕ) : Prop :=
  ∀ i < k, (D ∩ blockUnion B (i + 1)).card ≤ 2 * b i - 1

private lemma brun_pointwise_lower (B : ℕ → Finset ℕ) (b : ℕ → ℕ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hb_pos : ∀ i, 1 ≤ b i) (hb_mono : Monotone b) :
    ∀ k : ℕ, ∀ M ⊆ blockUnion B k,
      ∑ D ∈ M.powerset.filter (brunAdm B b k), (-1 : ℝ) ^ D.card ≤
        if M = ∅ then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro M hM
    have hU0 : blockUnion B 0 = ∅ := by simp [blockUnion]
    rw [hU0, Finset.subset_empty] at hM
    subst hM
    have hfilt : ({∅} : Finset (Finset ℕ)).filter (brunAdm B b 0) = {∅} := by
      ext D; simp [brunAdm]
    rw [Finset.powerset_empty, hfilt]; simp
  | succ k ih =>
    intro M hM
    have hU_succ : blockUnion B (k + 1) = blockUnion B k ∪ B k := by
      unfold blockUnion; rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
    have hdisj_k : Disjoint (blockUnion B k) (B k) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx1
      have hik : i ≠ k := by rw [Finset.mem_range] at hi; omega
      exact Finset.disjoint_left.mp (hdisj i k hik) hxi hx2
    set M1 := M ∩ blockUnion B k
    set M2 := M ∩ B k
    have hM_eq : M = M1 ∪ M2 := by
      ext x
      simp only [M1, M2, Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        have hU := hU_succ ▸ hM hx
        rcases Finset.mem_union.mp hU with h1 | h2
        · exact Or.inl ⟨hx, h1⟩
        · exact Or.inr ⟨hx, h2⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have hM12_disj : Disjoint M1 M2 := Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisj_k
    have hsplit_sum : ∑ D ∈ M.powerset.filter (brunAdm B b (k + 1)), (-1 : ℝ) ^ D.card =
        ∑ D1 ∈ M1.powerset.filter (brunAdm B b k),
          (-1 : ℝ) ^ D1.card *
            ∑ D2 ∈ M2.powerset.filter (fun D2 => D1.card + D2.card ≤ 2 * b k - 1), (-1 : ℝ) ^ D2.card := by
      -- Biject D ↦ (D ∩ U k, D ∩ B k)
      have hprod : ∑ D1 ∈ M1.powerset.filter (brunAdm B b k),
            (-1 : ℝ) ^ D1.card *
              ∑ D2 ∈ M2.powerset.filter (fun D2 => D1.card + D2.card ≤ 2 * b k - 1), (-1 : ℝ) ^ D2.card =
          ∑ p ∈ (M1.powerset.filter (brunAdm B b k) ×ˢ M2.powerset).filter
              (fun p => p.1.card + p.2.card ≤ 2 * b k - 1),
            (-1 : ℝ) ^ (p.1.card + p.2.card) := by
        conv_rhs => rw [Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun D1 _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun D2 _ => ?_
        split_ifs
        · rw [pow_add]
        · ring
      rw [hprod]
      refine Finset.sum_bij (fun D _ => (D ∩ blockUnion B k, D ∩ B k)) ?_ ?_ ?_ ?_
      · intro D hD
        rw [Finset.mem_filter, Finset.mem_powerset] at hD
        have hD_sub : D ⊆ blockUnion B (k + 1) := hD.1.trans hM
        have hD_split : D = (D ∩ blockUnion B k) ∪ (D ∩ B k) := by
          ext x; simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · intro hx
            rcases Finset.mem_union.mp (hU_succ ▸ hD_sub hx) with h1 | h2
            · exact Or.inl ⟨hx, h1⟩
            · exact Or.inr ⟨hx, h2⟩
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        have hD_disj : Disjoint (D ∩ blockUnion B k) (D ∩ B k) :=
          Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisj_k
        have hcard_eq : D.card = (D ∩ blockUnion B k).card + (D ∩ B k).card := by
          conv_lhs => rw [hD_split]
          exact Finset.card_union_of_disjoint hD_disj
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
        refine ⟨⟨⟨Finset.inter_subset_inter_right hD.1, fun i hi => ?_⟩,
            Finset.inter_subset_inter_right hD.1⟩, ?_⟩
        · have hsub_U : blockUnion B (i + 1) ⊆ blockUnion B k := by
            intro x hx
            obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
            exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega), hxj⟩
          have heq_inter : (D ∩ blockUnion B k) ∩ blockUnion B (i + 1) = D ∩ blockUnion B (i + 1) := by
            rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hsub_U]
          rw [heq_inter]; exact hD.2 i (by omega)
        · have hD_inter : D ∩ blockUnion B (k + 1) = D := Finset.inter_eq_left.mpr hD_sub
          rw [← hcard_eq, ← hD_inter]; exact hD.2 k (Nat.lt_succ_self k)
      · intro D1 hD1 D2 hD2 heq
        have hD1_sub : D1 ⊆ blockUnion B (k + 1) := (Finset.mem_powerset.mp (Finset.mem_filter.mp hD1).1).trans hM
        have hD2_sub : D2 ⊆ blockUnion B (k + 1) := (Finset.mem_powerset.mp (Finset.mem_filter.mp hD2).1).trans hM
        have hf1 : D1 ∩ blockUnion B k = D2 ∩ blockUnion B k := congrArg Prod.fst heq
        have hf2 : D1 ∩ B k = D2 ∩ B k := congrArg Prod.snd heq
        ext x
        have h1 : x ∈ D1 ↔ x ∈ D1 ∩ blockUnion B k ∨ x ∈ D1 ∩ B k := by
          simp only [Finset.mem_inter]
          constructor
          · intro hx
            rcases Finset.mem_union.mp (hU_succ ▸ hD1_sub hx) with ha | hb
            · exact Or.inl ⟨hx, ha⟩
            · exact Or.inr ⟨hx, hb⟩
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        have h2 : x ∈ D2 ↔ x ∈ D2 ∩ blockUnion B k ∨ x ∈ D2 ∩ B k := by
          simp only [Finset.mem_inter]
          constructor
          · intro hx
            rcases Finset.mem_union.mp (hU_succ ▸ hD2_sub hx) with ha | hb
            · exact Or.inl ⟨hx, ha⟩
            · exact Or.inr ⟨hx, hb⟩
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        rw [h1, h2, hf1, hf2]
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hp
        obtain ⟨⟨⟨hp1M, hp1Adm⟩, hp2M⟩, hcard⟩ := hp
        have hp1U : p.1 ⊆ blockUnion B k := hp1M.trans Finset.inter_subset_right
        have hp2B : p.2 ⊆ B k := hp2M.trans Finset.inter_subset_right
        have hp_disj : Disjoint p.1 p.2 := Disjoint.mono hp1U hp2B hdisj_k
        refine ⟨p.1 ∪ p.2, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.union_subset (hp1M.trans Finset.inter_subset_left) (hp2M.trans Finset.inter_subset_left),
            fun i hi => ?_⟩
          by_cases hik : i < k
          · have hsub_U : blockUnion B (i + 1) ⊆ blockUnion B k := by
              intro x hx
              obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
              exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega), hxj⟩
            have hdisj2 : Disjoint p.2 (blockUnion B (i + 1)) :=
              (Disjoint.mono hp2B hsub_U hdisj_k.symm)
            have heq : (p.1 ∪ p.2) ∩ blockUnion B (i + 1) = p.1 ∩ blockUnion B (i + 1) := by
              rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.union_empty]
            rw [heq]; exact hp1Adm i hik
          · have heqk : i = k := by omega
            rw [heqk]
            have hsub1 : p.1 ∪ p.2 ⊆ blockUnion B (k + 1) := by
              rw [hU_succ]; exact Finset.union_subset_union hp1U hp2B
            rw [Finset.inter_eq_left.mpr hsub1, Finset.card_union_of_disjoint hp_disj]
            exact hcard
        · apply Prod.ext <;> dsimp only
          · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp1U,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hp2B hdisj_k.symm), Finset.union_empty]
          · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp2B,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hp1U hdisj_k), Finset.empty_union]
      · intro D hD
        have hD_sub : D ⊆ blockUnion B (k + 1) := (Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1).trans hM
        have hD_split : D = (D ∩ blockUnion B k) ∪ (D ∩ B k) := by
          ext x; simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · intro hx
            rcases Finset.mem_union.mp (hU_succ ▸ hD_sub hx) with ha | hb
            · exact Or.inl ⟨hx, ha⟩
            · exact Or.inr ⟨hx, hb⟩
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        have hD_disj : Disjoint (D ∩ blockUnion B k) (D ∩ B k) :=
          Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisj_k
        congr 1
        conv_lhs => rw [hD_split]
        exact Finset.card_union_of_disjoint hD_disj
    rw [hsplit_sum]
    by_cases hM2 : M2 = ∅
    · have hM_eq_M1 : M = M1 := by rw [hM_eq, hM2, Finset.union_empty]
      rw [hM_eq_M1]
      have hinner_one : ∀ D1 ∈ M1.powerset.filter (brunAdm B b k),
          (∑ D2 ∈ M2.powerset.filter (fun D2 => D1.card + D2.card ≤ 2 * b k - 1), (-1 : ℝ) ^ D2.card) = 1 := by
        intro D1 hD1
        rw [hM2, Finset.powerset_empty]
        have hD1_le : D1.card ≤ 2 * b k - 1 := by
          by_cases hk0 : k = 0
          · subst hk0
            have hM1_e : M1 = ∅ := by
              have : M1 ⊆ blockUnion B 0 := Finset.inter_subset_right
              simpa [blockUnion] using this
            have hD1_e : D1 = ∅ := Finset.subset_empty.mp (hM1_e ▸ (Finset.mem_powerset.mp (Finset.mem_filter.mp hD1).1))
            simp [hD1_e]
          · have hAdm := (Finset.mem_filter.mp hD1).2 (k - 1) (by omega)
            have hD1_sub : D1 ⊆ blockUnion B ((k - 1) + 1) := by
              rw [Nat.sub_add_cancel (by omega)]
              exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hD1).1).trans Finset.inter_subset_right
            rw [Finset.inter_eq_left.mpr hD1_sub] at hAdm
            have hb_le : b (k - 1) ≤ b k := hb_mono (by omega)
            omega
        have hfilt : ({∅} : Finset (Finset ℕ)).filter (fun D2 => D1.card + D2.card ≤ 2 * b k - 1) = {∅} := by
          ext X; simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · exact And.left
          · rintro rfl; exact ⟨rfl, by simpa using hD1_le⟩
        rw [hfilt]; simp
      have hsimp : ∑ D1 ∈ M1.powerset.filter (brunAdm B b k),
            (-1 : ℝ) ^ D1.card *
              ∑ D2 ∈ M2.powerset.filter (fun D2 => D1.card + D2.card ≤ 2 * b k - 1), (-1 : ℝ) ^ D2.card =
          ∑ D1 ∈ M1.powerset.filter (brunAdm B b k), (-1 : ℝ) ^ D1.card := by
        refine Finset.sum_congr rfl fun D1 hD1 => by rw [hinner_one D1 hD1, mul_one]
      rw [hsimp]
      exact ih M1 Finset.inter_subset_right
    · have hM2_ne : M2.Nonempty := Finset.nonempty_iff_ne_empty.mpr hM2
      have hM_ne : M ≠ ∅ := by
        intro h0; apply hM2; rw [hM_eq] at h0; exact (Finset.union_eq_empty.mp h0).2
      rw [if_neg hM_ne]
      refine Finset.sum_nonpos fun D1 hD1 => ?_
      have hD1_le : D1.card ≤ 2 * b k - 1 := by
        by_cases hk0 : k = 0
        · subst hk0
          have hM1_e : M1 = ∅ := by
            have : M1 ⊆ blockUnion B 0 := Finset.inter_subset_right
            simpa [blockUnion] using this
          have hD1_e : D1 = ∅ := Finset.subset_empty.mp (hM1_e ▸ (Finset.mem_powerset.mp (Finset.mem_filter.mp hD1).1))
          simp [hD1_e]
        · have hAdm := (Finset.mem_filter.mp hD1).2 (k - 1) (by omega)
          have hD1_sub : D1 ⊆ blockUnion B ((k - 1) + 1) := by
            rw [Nat.sub_add_cancel (by omega)]
            exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hD1).1).trans Finset.inter_subset_right
          rw [Finset.inter_eq_left.mpr hD1_sub] at hAdm
          have hb_le : b (k - 1) ≤ b k := hb_mono (by omega)
          omega
      set K := 2 * b k - 1 - D1.card
      have hfilt_eq : M2.powerset.filter (fun D2 => D1.card + D2.card ≤ 2 * b k - 1) =
          M2.powerset.filter (fun D2 => D2.card ≤ K) := by
        ext D2; simp only [Finset.mem_filter]; constructor <;> (rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩)
      rw [hfilt_eq, alternating_powerset_le M2 hM2_ne K, ← mul_assoc, ← pow_add]
      have hodd : D1.card + K = 2 * (b k - 1) + 1 := by have := hb_pos k; omega
      rw [hodd, pow_succ, pow_mul]
      norm_num

/- ### Section 2: Helper Lemmas for Brun's Sieve Main & Error Terms -/

private lemma card_powerset_filter_le {α : Type*} [DecidableEq α] (S : Finset α) (k : ℕ) :
    (S.powerset.filter (fun T => T.card ≤ k)).card ≤ (S.card + 1) ^ k := by
  induction k with
  | zero =>
    have heq : S.powerset.filter (fun T => T.card ≤ 0) = {∅} := by
      ext T; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h0⟩; exact Finset.card_eq_zero.mp (Nat.le_zero.mp h0)
      · rintro rfl; simp
    rw [heq]; simp
  | succ k ih =>
    set Fk := S.powerset.filter (fun T => T.card ≤ k)
    have hsub : S.powerset.filter (fun T => T.card ≤ k + 1) ⊆
        Fk ∪ (S ×ˢ Fk).image (fun p => insert p.1 p.2) := by
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      by_cases hk : T.card ≤ k
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT.1, hk⟩)
      · apply Finset.mem_union_right
        have hne : T.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨a, haT⟩ := hne
        refine Finset.mem_image.mpr ⟨(a, T.erase a), ?_, Finset.insert_erase haT⟩
        refine Finset.mem_product.mpr ⟨hT.1 haT, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
          ((Finset.erase_subset a T).trans hT.1), ?_⟩⟩
        rw [Finset.card_erase_of_mem haT]; omega
    calc (S.powerset.filter (fun T => T.card ≤ k + 1)).card
        ≤ (Fk ∪ (S ×ˢ Fk).image (fun p => insert p.1 p.2)).card := Finset.card_le_card hsub
      _ ≤ Fk.card + ((S ×ˢ Fk).image (fun p => insert p.1 p.2)).card := Finset.card_union_le _ _
      _ ≤ Fk.card + (S ×ˢ Fk).card := Nat.add_le_add_left Finset.card_image_le _
      _ = Fk.card + S.card * Fk.card := by rw [Finset.card_product]
      _ = (S.card + 1) * Fk.card := by ring
      _ ≤ (S.card + 1) * (S.card + 1) ^ k := Nat.mul_le_mul_left _ ih
      _ = (S.card + 1) ^ (k + 1) := by ring

private lemma prod_one_sub_eq_powerset_sum (S : Finset ℕ) (f : ℕ → ℝ) :
    ∏ p ∈ S, (1 - f p) = ∑ D ∈ S.powerset, (-1 : ℝ) ^ D.card * ∏ p ∈ D, f p := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · have h2 : ∑ D ∈ S.powerset, (-1 : ℝ) ^ (insert a D).card * ∏ p ∈ insert a D, f p =
            -(f a) * ∑ D ∈ S.powerset, (-1 : ℝ) ^ D.card * ∏ p ∈ D, f p := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun D hD => ?_
          have haD : a ∉ D := fun h => ha (Finset.mem_powerset.mp hD h)
          rw [Finset.card_insert_of_notMem haD, Finset.prod_insert haD, pow_succ]
          ring
        rw [h2]; ring
      · intro D1 hD1 D2 hD2 heq
        have ha1 : a ∉ D1 := fun h => ha (Finset.mem_powerset.mp hD1 h)
        have ha2 : a ∉ D2 := fun h => ha (Finset.mem_powerset.mp hD2 h)
        have := congrArg (fun X => X.erase a) heq
        simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
    · rw [Finset.disjoint_left]
      intro X hX1 hX2
      obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hX2
      exact ha (Finset.mem_powerset.mp hX1 (Finset.mem_insert_self a D))

private lemma prod_one_add_eq_powerset_sum (S : Finset ℕ) (f : ℕ → ℝ) :
    ∏ p ∈ S, (1 + f p) = ∑ D ∈ S.powerset, ∏ p ∈ D, f p := by
  have h := prod_one_sub_eq_powerset_sum S (fun p => -f p)
  simp only [sub_neg_eq_add, Finset.prod_neg] at h
  rw [h]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [← mul_assoc, ← mul_pow]
  norm_num

private lemma card_Ioc_filter_dvd_sub (a b d : ℕ) (hab : a ≤ b) (hd : 1 ≤ d) :
    |(((Finset.Ioc a b).filter (fun q => d ∣ q)).card : ℝ) - ((b - a : ℕ) : ℝ) / (d : ℝ)| ≤ 1 := by
  have hcard : ((Finset.Ioc a b).filter (fun q => d ∣ q)).card = b / d - a / d := by
    have hsub : ∀ n : ℕ, ((Finset.Ioc 0 n).filter (fun q => d ∣ q)).card = n / d := by
      intro n
      have heq : (Finset.Ioc 0 n).filter (fun q => d ∣ q) = (Finset.Icc 1 (n / d)).image (fun m => d * m) := by
        ext q; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hq0, hqn⟩, m, rfl⟩
          refine ⟨m, ⟨?_, ?_⟩, rfl⟩
          · by_contra hm0; simp [show m = 0 by omega] at hq0
          · exact (Nat.le_div_iff_mul_le hd).mpr (by linarith)
        · rintro ⟨m, ⟨hm1, hmn⟩, rfl⟩
          refine ⟨⟨Nat.mul_pos hd hm1, ?_⟩, m, rfl⟩
          have := (Nat.le_div_iff_mul_le hd).mp hmn; linarith
      rw [heq, Finset.card_image_of_injective _ (fun x y h => Nat.eq_of_mul_eq_mul_left hd h)]
      simp
    have hsdiff : (Finset.Ioc a b).filter (fun q => d ∣ q) =
        ((Finset.Ioc 0 b).filter (fun q => d ∣ q)) \ ((Finset.Ioc 0 a).filter (fun q => d ∣ q)) := by
      ext q; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff]; omega
    have hsub' : (Finset.Ioc 0 a).filter (fun q => d ∣ q) ⊆ (Finset.Ioc 0 b).filter (fun q => d ∣ q) := by
      intro q hq; simp only [Finset.mem_filter, Finset.mem_Ioc] at hq ⊢; exact ⟨⟨hq.1.1, by omega⟩, hq.2⟩
    rw [hsdiff, Finset.card_sdiff_of_subset hsub', hsub b, hsub a]
  rw [hcard]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have ha_lo : (a : ℝ) / d - 1 < ((a / d : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := a) (b := d) hd
    have hcast : (a : ℝ) < ((a / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hdpos]; linarith
  have ha_hi : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := by
    rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self a d
  have hb_lo : (b : ℝ) / d - 1 < ((b / d : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := b) (b := d) hd
    have hcast : (b : ℝ) < ((b / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hdpos]; linarith
  have hb_hi : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / d := by
    rw [le_div_iff₀ hdpos]; exact_mod_cast Nat.div_mul_le_self b d
  have hdiv_le : a / d ≤ b / d := Nat.div_le_div_right hab
  rw [Nat.cast_sub hdiv_le, Nat.cast_sub hab, sub_div, abs_le]
  constructor <;> linarith

private lemma sum_inv_primes_le_64 :
    ∑ p ∈ (Finset.Icc 1 64).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ 2 := by
  have hf : (Finset.Icc 1 64).filter Nat.Prime =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by decide
  rw [hf]
  repeat (rw [Finset.sum_insert (by decide)])
  rw [Finset.sum_singleton]
  norm_num

private lemma sum_geom_series_inv_two (R : ℕ) :
    ∑ i ∈ Finset.range R, (1 : ℝ) / (2 : ℝ) ^ i ≤ 2 ∧
      ∑ i ∈ Finset.range R, (i : ℝ) / (2 : ℝ) ^ i ≤ 2 := by
  have h1 : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1 : ℝ) / (2 : ℝ) ^ i = 2 - 2 / (2 : ℝ) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]; ring
  have h2 : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), (i : ℝ) / (2 : ℝ) ^ i =
      2 - ((N : ℝ) + 2) / (2 : ℝ) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast; field_simp; ring
  constructor
  · rw [h1 R]
    have hnn : (0 : ℝ) ≤ 2 / (2 : ℝ) ^ R := by positivity
    linarith
  · cases R with
    | zero => simp
    | succ R' =>
      rw [h2 R']
      have hnn : (0 : ℝ) ≤ ((R' : ℝ) + 2) / (2 : ℝ) ^ R' := by positivity
      linarith

/- ### Section 3: Brun Combinatorial Sieve Lower Bound for `b - a ≥ z ^ 100` -/

set_option maxHeartbeats 1200000 in
lemma brun_interval_lower
    (h_sum_inv_Ioc : ∀ {w z : ℕ}, 64 ≤ w → w ≤ z →
      ∑ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log (z : ℝ) / Real.log (w : ℝ)) + 2)
    (h_V_ge : ∀ z : ℕ, 64 ≤ z →
      1 / (3 * Real.log (z : ℝ)) ≤ ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))) :
    ∀ᶠ z : ℕ in atTop, ∀ a b : ℕ, a ≤ b → (z : ℝ) ^ 100 ≤ ((b - a : ℕ) : ℝ) →
      (0.90 : ℝ) * ((b - a : ℕ) : ℝ) * ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) ≤
        (((Finset.Ioc a b).filter (fun q => ∀ p ∈ (Finset.Icc 1 z).filter Nat.Prime, ¬ p ∣ q)).card : ℝ) := by
  -- Eventual growth condition on z so remainder z^90 ≪ z^100 / (3 log z)
  have hz_big : ∀ᶠ z : ℕ in atTop,
      1000 ≤ z ∧
      (2 : ℝ) ^ (100 * (Nat.log 2 (Nat.log 2 z + 1) + 2) ^ 2 + 80) * (z : ℝ) ^ 80 ≤
        0.01 * ((z : ℝ) ^ 100 / (3 * Real.log (z : ℝ))) := by
    -- Show (2 ^ (100 * (log2(log2 z + 1) + 2)^2 + 80)) * (3 log z) ≤ 0.01 * z^20
    -- Take log: (100 * (log2(log2 z + 1) + 2)^2 + 80) * log 2 + log(3 log z) ≤ 20 log z - log 100
    -- Since log2(log2 z + 1) + 2 ≤ 2 * (log z)^(1/4) for large z, LHS = O((log z)^(1/2)) ≪ 20 log z!
    have hlog_lim : ∀ᶠ x : ℝ in atTop,
        10 ≤ x ∧ (100 * (2 * Real.log x + 10) ^ 2 + 100) + Real.log (3 * x) + 10 ≤ 20 * x := by
      have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (nhds 0) := by
        have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
        have hsq : Tendsto (fun x : ℝ => (Real.log x / x ^ (1 / 2 : ℝ)) ^ 2) atTop (nhds 0) := by
          simpa using h.pow 2
        refine hsq.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
        rw [div_pow, ← Real.rpow_natCast (x ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hx.le]; norm_num
      have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
        (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero.congr' (by
          filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x _; rw [Real.rpow_one])
      have h3 : Tendsto (fun x : ℝ => (100000 : ℝ) / x) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      filter_upwards [h1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000)),
        h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000)),
        h3.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
        Filter.eventually_ge_atTop (10 : ℝ)] with x hx1 hx2 hx3 hx10
      have hxpos : 0 < x := by linarith
      have ha : (Real.log x) ^ 2 ≤ x / 1000 := by
        have := (div_lt_iff₀ hxpos).mp hx1; linarith
      have hb : Real.log x ≤ x / 1000 := by
        have := (div_lt_iff₀ hxpos).mp hx2; linarith
      have hc : (100000 : ℝ) ≤ x := by
        have := (div_lt_iff₀ hxpos).mp hx3; linarith
      have hlog3x : Real.log (3 * x) ≤ Real.log x + 2 := by
        rw [Real.log_mul (by norm_num) hxpos.ne']
        have : Real.log 3 ≤ 2 := by
          have : (3 : ℝ) ≤ Real.exp 2 := by
            have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]; nlinarith
          simpa [Real.log_exp] using Real.log_le_log (by norm_num) this
        linarith
      refine ⟨hx10, ?_⟩
      nlinarith
    have hcomp := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hlog_lim
    filter_upwards [hcomp, Filter.eventually_ge_atTop 1000] with z ⟨hlogz10, hineq⟩ hz1000
    dsimp only [Function.comp_apply] at hlogz10 hineq
    refine ⟨hz1000, ?_⟩
    set L := Nat.log 2 z + 1
    set R := Nat.log 2 L + 1
    have hL_le : (L : ℝ) ≤ 2 * Real.log (z : ℝ) := by
      have h2L : (2 : ℝ) ^ (Nat.log 2 z) ≤ (z : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have hlog := Real.log_le_log (by positivity) h2L
      rw [Real.log_pow] at hlog
      have hlog2_gt : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
      dsimp [L]; push_cast; nlinarith
    have hR_le : (R : ℝ) + 1 ≤ 2 * Real.log (Real.log (z : ℝ)) + 10 := by
      have h2R : (2 : ℝ) ^ (Nat.log 2 L) ≤ (L : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by dsimp [L]; omega)
      have hlog := Real.log_le_log (by positivity) (h2R.trans hL_le)
      rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at hlog
      have hlog2_gt : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have hlog2_lt : Real.log 2 < (0.70 : ℝ) := by have := Real.log_two_lt_d9; linarith
      dsimp [R]; push_cast; nlinarith
    have hzpos : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
    have hlogz_pos : 0 < Real.log (z : ℝ) := by linarith
    have hLHS_pos : 0 < (2 : ℝ) ^ (100 * (R + 1) ^ 2 + 80) * (z : ℝ) ^ 80 := by positivity
    have hRHS_pos : 0 < 0.01 * ((z : ℝ) ^ 100 / (3 * Real.log (z : ℝ))) := by positivity
    rw [← Real.log_le_log_iff hLHS_pos hRHS_pos]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num) (by positivity), Real.log_div (by positivity) (by positivity), Real.log_pow]
    have hlog2_lt : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have hlog001 : -10 ≤ Real.log (0.01 : ℝ) := by
      rw [show (0.01 : ℝ) = (100 : ℝ)⁻¹ by norm_num, Real.log_inv]
      have : (100 : ℝ) ≤ Real.exp 10 := by
        have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
        rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
        calc (100 : ℝ) ≤ (2 : ℝ) ^ 10 := by norm_num
          _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he 10
      have hlog := Real.log_le_log (by norm_num) this
      rw [Real.log_exp] at hlog; linarith
    have hR2 : ((R + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * Real.log (Real.log (z : ℝ)) + 10) ^ 2 := by
      push_cast
      exact pow_le_pow_left₀ (by positivity) hR_le 2
    have hcast_exp : ((100 * (R + 1) ^ 2 + 80 : ℕ) : ℝ) ≤ 100 * (2 * Real.log (Real.log (z : ℝ)) + 10) ^ 2 + 100 := by
      push_cast at hR2 ⊢; linarith
    have hmul_log2 : ((100 * (R + 1) ^ 2 + 80 : ℕ) : ℝ) * Real.log 2 ≤
        100 * (2 * Real.log (Real.log (z : ℝ)) + 10) ^ 2 + 100 := by
      calc _ ≤ ((100 * (R + 1) ^ 2 + 80 : ℕ) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hlog2_lt.le (Nat.cast_nonneg _)
        _ = _ := mul_one _
        _ ≤ _ := hcast_exp
    push_cast at hmul_log2 ⊢
    linarith
  filter_upwards [hz_big] with z ⟨hz1000, hz_rem⟩ a b hab hba
  set Pz := (Finset.Icc 1 z).filter Nat.Prime
  set L := Nat.log 2 z + 1
  set R := Nat.log 2 L + 1
  let cut (i : ℕ) : ℕ := if i = 0 then z else min z (2 ^ (L / 2 ^ i))
  let B (i : ℕ) : Finset ℕ := (Finset.Ioc (cut (i + 1)) (cut i)).filter Nat.Prime
  let b_cap (i : ℕ) : ℕ := 18 + 2 * i
  have hL_pos : 1 ≤ L := by dsimp [L]; omega
  have hz_lt_2L : z < 2 ^ L := Nat.lt_pow_succ_log_self (by decide : 1 < 2) z
  have h2L_le : 2 ^ (L - 1) ≤ z := by
    have : L - 1 = Nat.log 2 z := Nat.add_sub_cancel _ 1
    rw [this]; exact Nat.pow_log_le_self 2 (by omega)
  have hcut_anti : Antitone cut := by
    apply antitone_nat_of_succ_le
    intro i
    dsimp [cut]
    by_cases hi : i = 0
    · subst hi; simp
    · rw [if_neg hi]
      apply min_le_min_left
      exact Nat.pow_le_pow_right (by decide) (Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) (Nat.le_succ i)) (by positivity))
  have hcut0 : cut 0 = z := rfl
  have hcutR : cut R = 1 := by
    have hL_lt : L < 2 ^ R := Nat.lt_pow_succ_log_self (by decide : 1 < 2) L
    have hdiv0 : L / 2 ^ R = 0 := Nat.div_eq_of_lt hL_lt
    dsimp [cut]; rw [hdiv0, pow_zero]; exact min_eq_right (by omega)
  have hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro p hi hj
    simp only [B, Finset.mem_filter, Finset.mem_Ioc] at hi hj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hle : cut j ≤ cut (i + 1) := hcut_anti (by omega)
      omega
    · have hle : cut i ≤ cut (j + 1) := hcut_anti (by omega)
      omega
  have hU_eq : ∀ k : ℕ, 1 ≤ k → blockUnion B k = (Finset.Ioc (cut k) z).filter Nat.Prime := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      unfold blockUnion
      have h1 : Finset.range 1 = {0} := by decide
      rw [h1, Finset.singleton_biUnion]; dsimp [B]; rw [hcut0]
    | succ k hk ih =>
      unfold blockUnion at ih ⊢
      rw [Finset.range_add_one, Finset.biUnion_insert, ih]
      ext p
      simp only [B, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
      have h1 : cut (k + 1) ≤ cut k := hcut_anti (Nat.le_succ k)
      have h2 : cut k ≤ z := hcut0 ▸ hcut_anti (Nat.zero_le k)
      constructor
      · rintro (⟨⟨hgt, hle⟩, hp⟩ | ⟨⟨hgt, hle⟩, hp⟩) <;> exact ⟨⟨by omega, by omega⟩, hp⟩
      · rintro ⟨⟨hgt, hle⟩, hp⟩
        by_cases hpk : p ≤ cut k
        · exact Or.inl ⟨⟨hgt, hpk⟩, hp⟩
        · exact Or.inr ⟨⟨by omega, hle⟩, hp⟩
  have hUR_eq : blockUnion B R = Pz := by
    have hR1 : 1 ≤ R := by dsimp [R]; omega
    rw [hU_eq R hR1, hcutR]
    ext p; simp only [Pz, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, hz⟩, hp⟩; exact ⟨⟨by omega, hz⟩, hp⟩
    · rintro ⟨⟨_, hz⟩, hp⟩; exact ⟨⟨hp.one_lt, hz⟩, hp⟩
  -- Step 1: Apply Brun pointwise lower bound to every q ∈ Ioc a b
  set AdmSet := Pz.powerset.filter (brunAdm B b_cap R)
  have hpointwise : ∀ q ∈ Finset.Ioc a b,
      (∑ D ∈ AdmSet, if (∏ p ∈ D, p) ∣ q then (-1 : ℝ) ^ D.card else 0) ≤
        if ∀ p ∈ Pz, ¬ p ∣ q then 1 else 0 := by
    intro q _
    set M := Pz.filter (fun p => p ∣ q)
    have hM_sub : M ⊆ blockUnion B R := hUR_eq ▸ Finset.filter_subset _ _
    have hfilt_eq : AdmSet.filter (fun D => (∏ p ∈ D, p) ∣ q) = M.powerset.filter (brunAdm B b_cap R) := by
      ext D
      simp only [AdmSet, M, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨hDP, hAdm⟩, hprod_dvd⟩
        refine ⟨fun p hpD => Finset.mem_filter.mpr ⟨hDP hpD, (Finset.dvd_prod_of_mem id hpD).trans hprod_dvd⟩, hAdm⟩
      · rintro ⟨hDM, hAdm⟩
        have hDP : D ⊆ Pz := fun p hp => (Finset.mem_filter.mp (hDM hp)).1
        refine ⟨⟨hDP, hAdm⟩, ?_⟩
        -- D consists of distinct primes all dividing q ⇒ ∏ p ∈ D, p ∣ q
        have hD_pr : ∀ p ∈ D, p.Prime ∧ p ∣ q := fun p hp =>
          ⟨(Finset.mem_filter.mp (hDP hp)).2, (Finset.mem_filter.mp (hDM hp)).2⟩
        clear hDM hAdm hDP
        induction D using Finset.induction_on with
        | empty => simp
        | insert p D hp ih =>
          rw [Finset.prod_insert hp]
          have h1 := hD_pr p (Finset.mem_insert_self p D)
          have h2 : ∏ r ∈ D, r ∣ q := ih fun r hr => hD_pr r (Finset.mem_insert_of_mem hr)
          have hcop : Nat.Coprime p (∏ r ∈ D, r) :=
            Nat.Coprime.prod_right fun r hr =>
              h1.1.coprime_iff_not_dvd.mpr fun hd =>
                hp (((Nat.prime_dvd_prime_iff_eq h1.1 (hD_pr r (Finset.mem_insert_of_mem hr)).1).mp hd) ▸ hr)
          exact hcop.mul_dvd_of_dvd_of_dvd h1.2 h2
    rw [← Finset.sum_filter, hfilt_eq]
    have hbr := brun_pointwise_lower B b_cap hB_disj (fun i => by dsimp [b_cap]; omega)
      (fun i j hij => by dsimp [b_cap]; omega) R M hM_sub
    have hM_iff : M = ∅ ↔ ∀ p ∈ Pz, ¬ p ∣ q := by
      simp only [M, Finset.filter_eq_empty_iff]
    by_cases h : ∀ p ∈ Pz, ¬ p ∣ q
    · rw [if_pos h]; rwa [if_pos (hM_iff.mpr h)] at hbr
    · rw [if_neg h]; rwa [if_neg (mt hM_iff.mp h)] at hbr
  -- Sum pointwise bound over q ∈ Ioc a b
  have hsum_Ioc : ((b - a : ℕ) : ℝ) * (∑ D ∈ AdmSet, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ)) -
      (AdmSet.card : ℝ) ≤
      (((Finset.Ioc a b).filter (fun q => ∀ p ∈ Pz, ¬ p ∣ q)).card : ℝ) := by
    have h1 := Finset.sum_le_sum hpointwise
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    rw [Finset.sum_comm] at h1
    have h2 : ∀ D ∈ AdmSet,
        ((b - a : ℕ) : ℝ) * ((-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ)) - 1 ≤
          ∑ q ∈ Finset.Ioc a b, if (∏ p ∈ D, p) ∣ q then (-1 : ℝ) ^ D.card else 0 := by
      intro D hD
      have hDP : D ⊆ Pz := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
      have hd_pos : 1 ≤ ∏ p ∈ D, p :=
        Finset.prod_pos fun p hp => (Finset.mem_filter.mp (hDP hp)).2.pos
      have hcard_eq : (∑ q ∈ Finset.Ioc a b, if (∏ p ∈ D, p) ∣ q then (-1 : ℝ) ^ D.card else 0) =
          (-1 : ℝ) ^ D.card * (((Finset.Ioc a b).filter (fun q => (∏ p ∈ D, p) ∣ q)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [hcard_eq]
      have herr := card_Ioc_filter_dvd_sub a b (∏ p ∈ D, p) hab hd_pos
      have hneg1 : |(-1 : ℝ) ^ D.card| = 1 := by simp
      have hdiff : |(-1 : ℝ) ^ D.card * (((Finset.Ioc a b).filter (fun q => (∏ p ∈ D, p) ∣ q)).card : ℝ) -
          ((b - a : ℕ) : ℝ) * ((-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ))| ≤ 1 := by
        have hfac : (-1 : ℝ) ^ D.card * (((Finset.Ioc a b).filter (fun q => (∏ p ∈ D, p) ∣ q)).card : ℝ) -
            ((b - a : ℕ) : ℝ) * ((-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ)) =
            (-1 : ℝ) ^ D.card * ((((Finset.Ioc a b).filter (fun q => (∏ p ∈ D, p) ∣ q)).card : ℝ) -
              ((b - a : ℕ) : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)) := by ring
        rw [hfac, abs_mul, hneg1, one_mul]; exact herr
      linarith [(abs_le.mp hdiff).1]
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one] at h3
    exact h3.trans h1
  -- Step 2: Bound ∑_{p ∈ U (i + 1)} 1/p ≤ i * log 2 + 6 for all i < R
  have hU_inv_sum : ∀ i < R,
      ∑ p ∈ blockUnion B (i + 1), (1 : ℝ) / (p : ℝ) ≤ (i : ℝ) * Real.log 2 + 6 := by
    intro i hi
    rw [hU_eq (i + 1) (by omega)]
    set w := cut (i + 1)
    have hw_le_z : w ≤ z := hcut0 ▸ hcut_anti (Nat.zero_le (i + 1))
    by_cases hw64 : 64 ≤ w
    · have hM := h_sum_inv_Ioc hw64 hw_le_z
      -- Show log z / log w ≤ 2^(i + 2)
      have hlogw_pos : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
      have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
      have hdiv_ge6 : 6 ≤ L / 2 ^ (i + 1) := by
        have hle_pow : w ≤ 2 ^ (L / 2 ^ (i + 1)) := by
          dsimp [w, cut]; exact min_le_right _ _
        have h64_le : 2 ^ 6 ≤ 2 ^ (L / 2 ^ (i + 1)) := (by decide : 2 ^ 6 = 64).symm ▸ (hw64.trans hle_pow)
        exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h64_le
      have hratio : Real.log (z : ℝ) / Real.log (w : ℝ) ≤ (2 : ℝ) ^ (i + 2) := by
        rw [div_le_iff₀ hlogw_pos]
        by_cases hwz : w = z
        · rw [hwz]
          have : (1 : ℝ) ≤ (2 : ℝ) ^ (i + 2) := one_le_pow₀ (by norm_num)
          nlinarith
        · have hw_eq : w = 2 ^ (L / 2 ^ (i + 1)) := by
            dsimp [w, cut] at hwz ⊢
            rcases le_total z (2 ^ (L / 2 ^ (i + 1))) with hle | hge
            · exfalso; exact hwz (min_eq_left hle)
            · exact min_eq_right hge
          have hlogw_eq : Real.log (w : ℝ) = ((L / 2 ^ (i + 1) : ℕ) : ℝ) * Real.log 2 := by
            rw [hw_eq]; push_cast; rw [Real.log_pow]
          have hlogz_lt : Real.log (z : ℝ) ≤ (L : ℝ) * Real.log 2 := by
            have h1 := Real.log_le_log (by exact_mod_cast (by omega : 0 < z))
              (by exact_mod_cast hz_lt_2L.le : (z : ℝ) ≤ ((2 ^ L : ℕ) : ℝ))
            push_cast at h1; rwa [Real.log_pow] at h1
          have hL_le_mul : L ≤ 2 * 2 ^ (i + 1) * (L / 2 ^ (i + 1)) := by
            have hmod := Nat.div_add_mod L (2 ^ (i + 1))
            have hlt := Nat.mod_lt L (by positivity : 0 < 2 ^ (i + 1))
            have h1 : 2 ^ (i + 1) ≤ 2 ^ (i + 1) * (L / 2 ^ (i + 1)) :=
              Nat.le_mul_of_pos_right _ (by omega)
            linarith
          have hL_r : (L : ℝ) ≤ (2 : ℝ) ^ (i + 2) * ((L / 2 ^ (i + 1) : ℕ) : ℝ) := by
            have h1 : (L : ℝ) ≤ (2 * 2 ^ (i + 1) * (L / 2 ^ (i + 1)) : ℕ) := by exact_mod_cast hL_le_mul
            push_cast at h1
            have h2pow : (2 : ℝ) * (2 : ℝ) ^ (i + 1) = (2 : ℝ) ^ (i + 2) := by rw [pow_succ]; ring
            rwa [h2pow] at h1
          rw [hlogw_eq]
          have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          calc Real.log (z : ℝ) ≤ (L : ℝ) * Real.log 2 := hlogz_lt
            _ ≤ ((2 : ℝ) ^ (i + 2) * ((L / 2 ^ (i + 1) : ℕ) : ℝ)) * Real.log 2 :=
                mul_le_mul_of_nonneg_right hL_r hlog2_nn
            _ = (2 : ℝ) ^ (i + 2) * (((L / 2 ^ (i + 1) : ℕ) : ℝ) * Real.log 2) := by ring
      have hlog_rat := Real.log_le_log (by positivity) hratio
      rw [Real.log_pow] at hlog_rat
      push_cast at hlog_rat
      have hlog2_lt : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    · -- Case w < 64: split (w, z] into (w, 64] and (64, z]
      have hw_lt : w < 64 := by omega
      have hsub_split : (Finset.Ioc w z).filter Nat.Prime ⊆
          ((Finset.Icc 1 64).filter Nat.Prime) ∪ ((Finset.Ioc 64 z).filter Nat.Prime) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_union, Finset.mem_Icc] at hp ⊢
        by_cases h64 : p ≤ 64
        · exact Or.inl ⟨⟨hp.2.one_le, h64⟩, hp.2⟩
        · exact Or.inr ⟨⟨by omega, hp.1.2⟩, hp.2⟩
      have hsplit_le : ∑ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
          (∑ p ∈ (Finset.Icc 1 64).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) +
            (∑ p ∈ (Finset.Ioc 64 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) := by
        calc _ ≤ ∑ p ∈ ((Finset.Icc 1 64).filter Nat.Prime) ∪ ((Finset.Ioc 64 z).filter Nat.Prime),
                (1 : ℝ) / (p : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_split (fun _ _ _ => by positivity)
          _ ≤ _ := by
              have hdisj : Disjoint ((Finset.Icc 1 64).filter Nat.Prime) ((Finset.Ioc 64 z).filter Nat.Prime) := by
                rw [Finset.disjoint_left]; intro p h1 h2
                simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
              rw [Finset.sum_union hdisj]
      have hM64 := h_sum_inv_Ioc (w := 64) (z := z) le_rfl (by omega)
      have hL_lt6 : L < 6 * 2 ^ (i + 1) := by
        have hw_eq : w = 2 ^ (L / 2 ^ (i + 1)) := by
          dsimp [w, cut] at hw_lt ⊢
          exact min_eq_right (by omega)
        have hdiv_lt6 : L / 2 ^ (i + 1) < 6 := by
          by_contra hge
          have : 64 ≤ 2 ^ (L / 2 ^ (i + 1)) :=
            (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) (by omega)
          omega
        have := Nat.lt_div_mul_add (a := L) (b := 2 ^ (i + 1)) (by positivity)
        have : L < (L / 2 ^ (i + 1) + 1) * 2 ^ (i + 1) := by linarith
        have : L / 2 ^ (i + 1) + 1 ≤ 6 := by omega
        calc L < (L / 2 ^ (i + 1) + 1) * 2 ^ (i + 1) := by assumption
          _ ≤ 6 * 2 ^ (i + 1) := Nat.mul_le_mul_right _ this
      have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
        rw [show (64 : ℝ) = (2 : ℝ) ^ 6 by norm_num, Real.log_pow]; push_cast; ring
      have hlogz_lt : Real.log (z : ℝ) ≤ (6 * 2 ^ (i + 1) : ℝ) * Real.log 2 := by
        have h1 := Real.log_le_log (by exact_mod_cast (by omega : 0 < z))
          (by exact_mod_cast hz_lt_2L.le : (z : ℝ) ≤ ((2 ^ L : ℕ) : ℝ))
        push_cast at h1; rw [Real.log_pow] at h1
        have hLr : (L : ℝ) ≤ 6 * (2 : ℝ) ^ (i + 1) := by exact_mod_cast hL_lt6.le
        have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        exact h1.trans (mul_le_mul_of_nonneg_right hLr hlog2_nn)
      have hratio64 : Real.log (z : ℝ) / Real.log (64 : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
        rw [hlog64, div_le_iff₀ (by positivity)]
        linarith
      have hlogz_pos' : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
      have hlog64_pos' : 0 < Real.log (64 : ℝ) := Real.log_pos (by norm_num)
      have hlog_rat := Real.log_le_log (div_pos hlogz_pos' hlog64_pos') hratio64
      rw [Real.log_pow] at hlog_rat; push_cast at hlog_rat
      have hlog2_lt : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      linarith [sum_inv_primes_le_64]
  -- Step 3: Bound Main Term Error: ∑_{D ∈ AdmSet} (-1)^|D| / ∏ D ≥ 0.99 * V(z)
  set Vz := ∏ p ∈ Pz, (1 - (1 : ℝ) / (p : ℝ))
  have hVz_pos : 0 < Vz := Finset.prod_pos fun p hp => by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hmain_lower : (0.99 : ℝ) * Vz ≤ ∑ D ∈ AdmSet, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ) := by
    have hfull : Vz = ∑ D ∈ Pz.powerset, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ) := by
      dsimp [Vz]
      rw [prod_one_sub_eq_powerset_sum Pz (fun p => (1 : ℝ) / (p : ℝ))]
      refine Finset.sum_congr rfl fun D _ => ?_
      rw [div_eq_mul_inv, Nat.cast_prod, ← Finset.prod_inv_distrib]
      congr 1; exact Finset.prod_congr rfl fun _ _ => one_div _
    set Bad := Pz.powerset.filter (fun D => ¬ brunAdm B b_cap R D)
    have hsplit_full : ∑ D ∈ Pz.powerset, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ) =
        (∑ D ∈ AdmSet, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ)) +
          (∑ D ∈ Bad, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ)) :=
      (Finset.sum_filter_add_sum_filter_not Pz.powerset (brunAdm B b_cap R) _).symm
    -- Partition Bad by smallest violation index i < R
    let BadAt (i : ℕ) : Finset (Finset ℕ) :=
      Pz.powerset.filter (fun D => brunAdm B b_cap i D ∧ 2 * b_cap i ≤ (D ∩ blockUnion B (i + 1)).card)
    have hBad_eq : Bad = (Finset.range R).biUnion BadAt := by
      classical
      ext D
      simp only [Bad, BadAt, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
      constructor
      · rintro ⟨hDP, hnot⟩
        unfold brunAdm at hnot
        push Not at hnot
        let i := Nat.find hnot
        have hi_spec := Nat.find_spec hnot
        refine ⟨i, hi_spec.1, hDP, ?_, ?_⟩
        · intro j hj
          by_contra hgt
          have hmin := Nat.find_min hnot hj
          push Not at hmin
          exact absurd (hmin (lt_trans hj hi_spec.1)) hgt
        · have h2 := hi_spec.2
          dsimp only [i, b_cap] at h2 ⊢
          omega
      · rintro ⟨i, hiR, hDP, _, hviol⟩
        refine ⟨hDP, fun hAdm => ?_⟩
        have h2 := hAdm i hiR
        dsimp only [b_cap] at h2 hviol
        omega
    have hBad_pw : (Finset.range R : Set ℕ).PairwiseDisjoint BadAt := by
      intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro D hDi hDj
      simp only [BadAt, Finset.mem_filter] at hDi hDj
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have h1 := hDj.2.1 i hlt
        have h2 := hDi.2.2
        dsimp only [b_cap] at h1 h2
        omega
      · have h1 := hDi.2.1 j hgt
        have h2 := hDj.2.2
        dsimp only [b_cap] at h1 h2
        omega
    -- Bound |∑_{D ∈ BadAt i} (-1)^|D| / ∏ D| ≤ Vz * exp(-7 - 0.7 * i)
    have hBadAt_bound : ∀ i ∈ Finset.range R,
        |∑ D ∈ BadAt i, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ)| ≤
          Vz * Real.exp (-7 - 0.7 * (i : ℝ)) := by
      intro i hiR
      have hiR' : i < R := Finset.mem_range.mp hiR
      set Ui := blockUnion B (i + 1)
      set Rest := Pz \ Ui
      have hUi_sub : Ui ⊆ Pz := by
        rw [← hUR_eq]; intro x hx
        obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega), hxj⟩
      have hdisj_UR : Disjoint Ui Rest := Finset.disjoint_sdiff
      have hunion_UR : Ui ∪ Rest = Pz := Finset.union_sdiff_of_subset hUi_sub
      -- Factor sum over BadAt i into (E ⊆ Ui) × (F ⊆ Rest)
      set Eset := Ui.powerset.filter (fun E => brunAdm B b_cap i E ∧ 2 * b_cap i ≤ E.card)
      have hfactor : ∑ D ∈ BadAt i, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ) =
          (∑ E ∈ Eset, (-1 : ℝ) ^ E.card / ((∏ p ∈ E, p : ℕ) : ℝ)) *
            (∏ p ∈ Rest, (1 - (1 : ℝ) / (p : ℝ))) := by
        rw [prod_one_sub_eq_powerset_sum Rest (fun p => (1 : ℝ) / (p : ℝ)), Finset.sum_mul_sum,
          ← Finset.sum_product']
        refine Finset.sum_bij (fun D _ => (D ∩ Ui, D ∩ Rest)) ?_ ?_ ?_ ?_
        · intro D hD
          simp only [BadAt, Eset, Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hD ⊢
          refine ⟨⟨Finset.inter_subset_right, fun j hj => ?_, hD.2.2⟩, Finset.inter_subset_right⟩
          have hsub_j : blockUnion B (j + 1) ⊆ Ui := by
            intro x hx
            obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.mp hx
            exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (by rw [Finset.mem_range] at hm; omega), hxm⟩
          rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hsub_j]
          exact hD.2.1 j hj
        · intro D1 hD1 D2 hD2 heq
          have h1 : D1 ⊆ Ui ∪ Rest := hunion_UR.symm ▸ Finset.mem_powerset.mp (Finset.mem_filter.mp hD1).1
          have h2 : D2 ⊆ Ui ∪ Rest := hunion_UR.symm ▸ Finset.mem_powerset.mp (Finset.mem_filter.mp hD2).1
          have hf1 : D1 ∩ Ui = D2 ∩ Ui := congrArg Prod.fst heq
          have hf2 : D1 ∩ Rest = D2 ∩ Rest := congrArg Prod.snd heq
          have hD1_eq : D1 = (D1 ∩ Ui) ∪ (D1 ∩ Rest) := by
            rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr h1]
          have hD2_eq : D2 = (D2 ∩ Ui) ∪ (D2 ∩ Rest) := by
            rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr h2]
          rw [hD1_eq, hD2_eq, hf1, hf2]
        · intro p hp
          simp only [Finset.mem_product, Eset, Finset.mem_filter, Finset.mem_powerset] at hp
          obtain ⟨⟨hp1U, hp1Adm, hp1c⟩, hp2R⟩ := hp
          refine ⟨p.1 ∪ p.2, ?_, ?_⟩
          · simp only [BadAt, Finset.mem_filter, Finset.mem_powerset]
            have hdisj2 : Disjoint p.2 Ui := Disjoint.mono_left hp2R hdisj_UR.symm
            have hinterU : (p.1 ∪ p.2) ∩ Ui = p.1 := by
              rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp1U,
                Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.union_empty]
            refine ⟨Finset.union_subset (hp1U.trans hUi_sub) (hp2R.trans Finset.sdiff_subset),
              fun j hj => ?_, by rw [hinterU]; exact hp1c⟩
            have hsub_j : blockUnion B (j + 1) ⊆ Ui := by
              intro x hx
              obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.mp hx
              exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (by rw [Finset.mem_range] at hm; omega), hxm⟩
            have hdisj2j : Disjoint p.2 (blockUnion B (j + 1)) := Disjoint.mono_right hsub_j hdisj2
            rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj2j, Finset.union_empty]
            exact hp1Adm j hj
          · apply Prod.ext <;> dsimp only
            · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp1U,
                Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hp2R hdisj_UR.symm), Finset.union_empty]
            · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp2R,
                Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hp1U hdisj_UR), Finset.empty_union]
        · intro D hD
          have hD_sub : D ⊆ Ui ∪ Rest := hunion_UR.symm ▸ Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
          have hD_eq : D = (D ∩ Ui) ∪ (D ∩ Rest) := by
            rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hD_sub]
          have hD_disj : Disjoint (D ∩ Ui) (D ∩ Rest) :=
            Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisj_UR
          conv_lhs => rw [hD_eq]
          rw [Finset.card_union_of_disjoint hD_disj, Finset.prod_union hD_disj, pow_add, Nat.cast_mul]
          simp only [Nat.cast_prod, div_eq_mul_inv, one_mul, mul_inv]
          rw [Finset.prod_inv_distrib]
          ring
      rw [hfactor, abs_mul]
      have hRest_pos : 0 < ∏ p ∈ Rest, (1 - (1 : ℝ) / (p : ℝ)) :=
        Finset.prod_pos fun p hp => by
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp (Finset.sdiff_subset hp)).2.two_le
          rw [sub_pos, div_lt_one (by linarith)]; linarith
      have hUi_prod_pos : 0 < ∏ p ∈ Ui, (1 - (1 : ℝ) / (p : ℝ)) :=
        Finset.prod_pos fun p hp => by
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp (hUi_sub hp)).2.two_le
          rw [sub_pos, div_lt_one (by linarith)]; linarith
      have hRest_eq : ∏ p ∈ Rest, (1 - (1 : ℝ) / (p : ℝ)) = Vz / ∏ p ∈ Ui, (1 - (1 : ℝ) / (p : ℝ)) := by
        rw [eq_div_iff hUi_prod_pos.ne', mul_comm]
        dsimp [Vz]; rw [← hunion_UR, Finset.prod_union hdisj_UR]
      -- Bound (∏_{p ∈ Ui} (1 - 1/p))⁻¹ ≤ exp(2 * ∑_{p ∈ Ui} 1/p)
      have hUi_inv : (∏ p ∈ Ui, (1 - (1 : ℝ) / (p : ℝ)))⁻¹ ≤
          Real.exp (2 * ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ)) := by
        rw [← Finset.prod_inv_distrib, Finset.mul_sum, Real.exp_sum]
        refine Finset.prod_le_prod (fun p hp => by
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp (hUi_sub hp)).2.two_le
          have : 0 < 1 - (1 : ℝ) / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
          positivity) fun p hp => ?_
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp (hUi_sub hp)).2.two_le
        have hpos : 0 < 1 - (1 : ℝ) / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
        have h1 : (1 - (1 : ℝ) / (p : ℝ))⁻¹ ≤ 1 + 2 / (p : ℝ) := by
          rw [inv_le_comm₀ hpos (by positivity)]
          have : (1 - (1 : ℝ) / (p : ℝ)) * (1 + 2 / (p : ℝ)) = 1 + ((p : ℝ) - 2) / (p : ℝ) ^ 2 := by
            field_simp [show (p : ℝ) ≠ 0 by linarith]; ring
          have hnn : 0 ≤ ((p : ℝ) - 2) / (p : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
          rw [inv_le_iff_one_le_mul₀ (by positivity)]
          linarith
        exact h1.trans (by rw [mul_one_div]; simpa [add_comm] using Real.add_one_le_exp (2 / (p : ℝ)))
      -- Rankin bound on |∑_{E ∈ Eset} (-1)^|E| / ∏ E| ≤ exp(-2 b_i + e * ∑_{p ∈ Ui} 1/p)
      have hE_rankin : |∑ E ∈ Eset, (-1 : ℝ) ^ E.card / ((∏ p ∈ E, p : ℕ) : ℝ)| ≤
          Real.exp (-(2 * (b_cap i : ℝ)) + Real.exp 1 * ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ)) := by
        have htri : |∑ E ∈ Eset, (-1 : ℝ) ^ E.card / ((∏ p ∈ E, p : ℕ) : ℝ)| ≤
            ∑ E ∈ Eset, (1 : ℝ) / ((∏ p ∈ E, p : ℕ) : ℝ) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun E _ => ?_)
          rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg (Nat.cast_nonneg _)]
        have hterm_rk : ∀ E ∈ Eset, (1 : ℝ) / ((∏ p ∈ E, p : ℕ) : ℝ) ≤
            Real.exp (-(2 * (b_cap i : ℝ))) * ∏ p ∈ E, (Real.exp 1 / (p : ℝ)) := by
          intro E hE
          have hEc : 2 * b_cap i ≤ E.card := (Finset.mem_filter.mp hE).2.2
          have hpow_le : (Real.exp 1) ^ (2 * b_cap i) ≤ (Real.exp 1) ^ E.card :=
            pow_le_pow_right₀ (by linarith [Real.exp_one_gt_d9]) hEc
          have hexp_eq : Real.exp (-(2 * (b_cap i : ℝ))) = ((Real.exp 1) ^ (2 * b_cap i))⁻¹ := by
            rw [Real.exp_neg, show (2 * (b_cap i : ℝ)) = ((2 * b_cap i : ℕ) : ℝ) * (1 : ℝ) by push_cast; ring,
              Real.exp_nat_mul]
          have hprod_eq : ∏ p ∈ E, (Real.exp 1 / (p : ℝ)) = (Real.exp 1) ^ E.card / ((∏ p ∈ E, p : ℕ) : ℝ) := by
            rw [Finset.prod_div_distrib, Finset.prod_const, Nat.cast_prod]
          rw [hexp_eq, hprod_eq, inv_mul_eq_div, div_div, mul_comm]
          have hpos_e : 0 < (Real.exp 1) ^ (2 * b_cap i) := by positivity
          have hprod_nn : (0 : ℝ) ≤ ((∏ p ∈ E, p : ℕ) : ℝ) := Nat.cast_nonneg _
          by_cases h0 : ((∏ p ∈ E, p : ℕ) : ℝ) = 0
          · simp [h0]
          · have hpos_p : 0 < ((∏ p ∈ E, p : ℕ) : ℝ) := lt_of_le_of_ne hprod_nn (Ne.symm h0)
            rw [div_le_div_iff₀ hpos_p (mul_pos hpos_e hpos_p)]
            nlinarith
        have hsum_all : ∑ E ∈ Ui.powerset, ∏ p ∈ E, (Real.exp 1 / (p : ℝ)) ≤
            Real.exp (Real.exp 1 * ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ)) := by
          rw [← prod_one_add_eq_powerset_sum Ui (fun p => Real.exp 1 / (p : ℝ)),
            Finset.mul_sum, Real.exp_sum]
          refine Finset.prod_le_prod (fun _ _ => by positivity) fun p _ => ?_
          rw [mul_one_div]; simpa [add_comm] using Real.add_one_le_exp (Real.exp 1 / (p : ℝ))
        calc |∑ E ∈ Eset, (-1 : ℝ) ^ E.card / ((∏ p ∈ E, p : ℕ) : ℝ)|
            ≤ ∑ E ∈ Eset, (1 : ℝ) / ((∏ p ∈ E, p : ℕ) : ℝ) := htri
          _ ≤ ∑ E ∈ Eset, Real.exp (-(2 * (b_cap i : ℝ))) * ∏ p ∈ E, (Real.exp 1 / (p : ℝ)) :=
                Finset.sum_le_sum hterm_rk
          _ = Real.exp (-(2 * (b_cap i : ℝ))) * ∑ E ∈ Eset, ∏ p ∈ E, (Real.exp 1 / (p : ℝ)) := by
                rw [← Finset.mul_sum]
          _ ≤ Real.exp (-(2 * (b_cap i : ℝ))) * ∑ E ∈ Ui.powerset, ∏ p ∈ E, (Real.exp 1 / (p : ℝ)) :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)) (Real.exp_pos _).le
          _ ≤ Real.exp (-(2 * (b_cap i : ℝ))) * Real.exp (Real.exp 1 * ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ)) :=
                mul_le_mul_of_nonneg_left hsum_all (Real.exp_pos _).le
          _ = _ := (Real.exp_add _ _).symm
      rw [abs_of_pos hRest_pos, hRest_eq, div_eq_mul_inv]
      have hcomb_exp : -(2 * (b_cap i : ℝ)) + (Real.exp 1 + 2) * ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ) ≤
          -7 - 0.7 * (i : ℝ) := by
        have hUi := hU_inv_sum i hiR'
        have he_lt : Real.exp 1 ≤ 2.72 := by have := Real.exp_one_lt_d9; linarith
        have hlog2_lt : Real.log 2 ≤ 0.694 := by have := Real.log_two_lt_d9; linarith
        have hsum_nn : 0 ≤ ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
        have hb_eq : (b_cap i : ℝ) = 18 + 2 * (i : ℝ) := by dsimp [b_cap]; push_cast; ring
        rw [hb_eq]
        have h1 : (Real.exp 1 + 2) * ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ) ≤ 4.72 * ((i : ℝ) * 0.694 + 6) := by
          have hi_nn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
          have h2 : ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ) ≤ (i : ℝ) * 0.694 + 6 := by nlinarith
          nlinarith
        linarith
      calc |∑ E ∈ Eset, (-1 : ℝ) ^ E.card / ((∏ p ∈ E, p : ℕ) : ℝ)| *
              (Vz * (∏ p ∈ Ui, (1 - (1 : ℝ) / (p : ℝ)))⁻¹)
          = Vz * (|∑ E ∈ Eset, (-1 : ℝ) ^ E.card / ((∏ p ∈ E, p : ℕ) : ℝ)| *
              (∏ p ∈ Ui, (1 - (1 : ℝ) / (p : ℝ)))⁻¹) := by ring
        _ ≤ Vz * (Real.exp (-(2 * (b_cap i : ℝ)) + Real.exp 1 * ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ)) *
              Real.exp (2 * ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hE_rankin hUi_inv (by positivity) (Real.exp_pos _).le) hVz_pos.le
        _ = Vz * Real.exp (-(2 * (b_cap i : ℝ)) + (Real.exp 1 + 2) * ∑ p ∈ Ui, (1 : ℝ) / (p : ℝ)) := by
              rw [← Real.exp_add]; congr 2; ring
        _ ≤ Vz * Real.exp (-7 - 0.7 * (i : ℝ)) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcomb_exp) hVz_pos.le
    -- Sum |BadAt i| over i ∈ range R ≤ 0.01 * Vz
    have hBad_sum_le : |∑ D ∈ Bad, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ)| ≤ 0.01 * Vz := by
      rw [hBad_eq, Finset.sum_biUnion hBad_pw]
      have hgeom : ∑ i ∈ Finset.range R, Real.exp (-7 - 0.7 * (i : ℝ)) ≤ 0.01 := by
        have hrew : ∀ i : ℕ, Real.exp (-7 - 0.7 * (i : ℝ)) = Real.exp (-7) * (Real.exp (-0.7)) ^ i := by
          intro i
          rw [show -7 - 0.7 * (i : ℝ) = -7 + (i : ℝ) * (-0.7) by ring, Real.exp_add, Real.exp_nat_mul]
        simp_rw [hrew, ← Finset.mul_sum]
        set q : ℝ := Real.exp (-0.7)
        have hq0 : 0 ≤ q := (Real.exp_pos _).le
        have hq_le : q ≤ 0.5 := by
          dsimp [q]; rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num),
            show (0.5 : ℝ)⁻¹ = 2 by norm_num]
          -- e^0.7 ≥ 2? Check: e^7 = (2.71828)^7 = 1096.6 > 128 = 2^7!
          have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
          have hpow10 : (2 : ℝ) ^ 10 ≤ (Real.exp 0.7) ^ 10 := by
            rw [← Real.exp_nat_mul, show ((10 : ℕ) : ℝ) * 0.7 = ((7 : ℕ) : ℝ) * (1 : ℝ) by norm_num,
              Real.exp_nat_mul]
            calc (2 : ℝ) ^ 10 ≤ (2.7 : ℝ) ^ 7 := by norm_num
              _ ≤ (Real.exp 1) ^ 7 := pow_le_pow_left₀ (by norm_num) he 7
          exact le_of_pow_le_pow_left₀ (by decide : 10 ≠ 0) (Real.exp_pos _).le hpow10
        have he7 : Real.exp (-7 : ℝ) ≤ 0.002 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 7) (by norm_num),
            show (0.002 : ℝ)⁻¹ = 500 by norm_num]
          have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
          rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
          calc (500 : ℝ) ≤ (2.7 : ℝ) ^ 7 := by norm_num
            _ ≤ (Real.exp 1) ^ 7 := pow_le_pow_left₀ (by norm_num) he 7
        rw [geom_sum_eq (by linarith)]
        have hgs : (q ^ R - 1) / (q - 1) ≤ 2 := by
          rw [show (q ^ R - 1) / (q - 1) = (1 - q ^ R) / (1 - q) by rw [← neg_div_neg_eq]; ring_nf]
          rw [div_le_iff₀ (by linarith)]
          linarith [pow_nonneg hq0 R]
        nlinarith [Real.exp_pos (-7 : ℝ)]
      calc |∑ i ∈ Finset.range R, ∑ D ∈ BadAt i, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ)|
          ≤ ∑ i ∈ Finset.range R, |∑ D ∈ BadAt i, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range R, Vz * Real.exp (-7 - 0.7 * (i : ℝ)) :=
            Finset.sum_le_sum hBadAt_bound
        _ = Vz * ∑ i ∈ Finset.range R, Real.exp (-7 - 0.7 * (i : ℝ)) := by rw [← Finset.mul_sum]
        _ ≤ Vz * 0.01 := mul_le_mul_of_nonneg_left hgeom hVz_pos.le
        _ = 0.01 * Vz := mul_comm _ _
    linarith [(abs_le.mp hBad_sum_le).2]
  -- Step 4: Bound |AdmSet| ≤ 0.01 * (b - a) * Vz
  have hAdm_card : (AdmSet.card : ℝ) ≤ 0.01 * ((b - a : ℕ) : ℝ) * Vz := by
    -- Inject AdmSet into ∏ i : Fin R, (B i).powerset.filter (·.card ≤ 2 * b_cap i)
    let fPart (i : Fin R) : Finset (Finset ℕ) := (B i.1).powerset.filter (fun T => T.card ≤ 2 * b_cap i.1)
    let splitMap : Finset ℕ → ((i : Fin R) → Finset ℕ) := fun D i => D ∩ B i.1
    have hmap_mem : ∀ D ∈ AdmSet, splitMap D ∈ Fintype.piFinset fPart := by
      intro D hD
      rw [Fintype.mem_piFinset]
      intro i
      simp only [fPart, splitMap, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.inter_subset_right, ?_⟩
      have hAdm := (Finset.mem_filter.mp hD).2 i.1 i.2
      have hBsub : B i.1 ⊆ blockUnion B (i.1 + 1) := by
        intro x hx; exact Finset.mem_biUnion.mpr ⟨i.1, Finset.mem_range.mpr (Nat.lt_succ_self _), hx⟩
      have hle := Finset.card_le_card (Finset.inter_subset_inter_left (s := D) hBsub)
      omega
    have hmap_inj : Set.InjOn splitMap (AdmSet : Set (Finset ℕ)) := by
      intro D1 hD1 D2 hD2 heq
      have h1 : D1 ⊆ blockUnion B R := hUR_eq.symm ▸ Finset.mem_powerset.mp (Finset.mem_filter.mp hD1).1
      have h2 : D2 ⊆ blockUnion B R := hUR_eq.symm ▸ Finset.mem_powerset.mp (Finset.mem_filter.mp hD2).1
      ext x
      have hx_iff : ∀ D, D ⊆ blockUnion B R → (x ∈ D ↔ ∃ i : Fin R, x ∈ D ∩ B i.1) := by
        intro D hD
        constructor
        · intro hxD
          obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (hD hxD)
          exact ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_inter.mpr ⟨hxD, hxi⟩⟩
        · rintro ⟨i, hxi⟩; exact (Finset.mem_inter.mp hxi).1
      rw [hx_iff D1 h1, hx_iff D2 h2]
      constructor
      · rintro ⟨i, hi⟩
        have hEq : D1 ∩ B i.1 = D2 ∩ B i.1 := congrFun heq i
        exact ⟨i, hEq ▸ hi⟩
      · rintro ⟨i, hi⟩
        have hEq : D1 ∩ B i.1 = D2 ∩ B i.1 := congrFun heq i
        exact ⟨i, hEq.symm ▸ hi⟩
    have hcard_prod : AdmSet.card ≤ ∏ i : Fin R, (fPart i).card := by
      calc AdmSet.card = (AdmSet.image splitMap).card := (Finset.card_image_of_injOn hmap_inj).symm
        _ ≤ (Fintype.piFinset fPart).card := Finset.card_le_card (Finset.image_subset_iff.mpr hmap_mem)
        _ = ∏ i : Fin R, (fPart i).card := Fintype.card_piFinset fPart
    have hcard_r : (AdmSet.card : ℝ) ≤ ∏ i ∈ Finset.range R, ((cut i + 1 : ℕ) : ℝ) ^ (2 * b_cap i) := by
      have h1 : (AdmSet.card : ℝ) ≤ ∏ i : Fin R, ((fPart i).card : ℝ) := by
        rw [← Nat.cast_prod]; exact_mod_cast hcard_prod
      rw [Fin.prod_univ_eq_prod_range (fun i => (((B i).powerset.filter (fun T => T.card ≤ 2 * b_cap i)).card : ℝ)) R] at h1
      refine h1.trans (Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ => ?_)
      have hcf := card_powerset_filter_le (B i) (2 * b_cap i)
      have hB_card : (B i).card ≤ cut i := by
        have hsub : B i ⊆ Finset.Icc 1 (cut i) := by
          intro p hp; simp only [B, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
          exact ⟨hp.2.one_le, hp.1.2⟩
        calc (B i).card ≤ (Finset.Icc 1 (cut i)).card := Finset.card_le_card hsub
          _ = cut i := by simp
      have hle_nat : ((B i).powerset.filter (fun T => T.card ≤ 2 * b_cap i)).card ≤ (cut i + 1) ^ (2 * b_cap i) :=
        hcf.trans (Nat.pow_le_pow_left (Nat.add_le_add_right hB_card 1) _)
      exact_mod_cast hle_nat
    -- Bound ∏_{i < R} (cut i + 1)^(2 b_cap i) ≤ 2^(100 (R+1)^2 + 80) * z^80
    have hcut_pow : ∀ i ∈ Finset.range R,
        ((cut i + 1 : ℕ) : ℝ) ^ (2 * b_cap i) ≤
          (2 : ℝ) ^ (2 * b_cap i) * ((2 : ℝ) ^ ((L : ℝ) / (2 : ℝ) ^ i)) ^ (2 * b_cap i) := by
      intro i _
      have hcut_le : (cut i : ℝ) ≤ (2 : ℝ) ^ ((L : ℝ) / (2 : ℝ) ^ i) := by
        by_cases hi0 : i = 0
        · subst hi0; rw [hcut0, pow_zero, div_one]
          have : (z : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hz_lt_2L.le
          rwa [← Real.rpow_natCast] at this
        · have h1 : cut i ≤ 2 ^ (L / 2 ^ i) := by dsimp [cut]; rw [if_neg hi0]; exact min_le_right _ _
          have h2 : (cut i : ℝ) ≤ (2 : ℝ) ^ ((L / 2 ^ i : ℕ) : ℝ) := by
            rw [Real.rpow_natCast]; exact_mod_cast h1
          refine h2.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
          rw [le_div_iff₀ (by positivity)]
          exact_mod_cast Nat.div_mul_le_self L (2 ^ i)
      have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ ((L : ℝ) / (2 : ℝ) ^ i) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have hbase : ((cut i + 1 : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ ((L : ℝ) / (2 : ℝ) ^ i) := by
        push_cast; linarith
      calc ((cut i + 1 : ℕ) : ℝ) ^ (2 * b_cap i)
          ≤ (2 * (2 : ℝ) ^ ((L : ℝ) / (2 : ℝ) ^ i)) ^ (2 * b_cap i) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
        _ = _ := mul_pow _ _ _
    have hprod_le := hcard_r.trans (Finset.prod_le_prod (fun _ _ => by positivity) hcut_pow)
    rw [Finset.prod_mul_distrib] at hprod_le
    -- Bound first factor ∏_{i < R} 2^(2 * b_cap i) ≤ 2^(100 * (R + 1)^2)
    have hfac1 : ∏ i ∈ Finset.range R, (2 : ℝ) ^ (2 * b_cap i) ≤ (2 : ℝ) ^ (100 * (R + 1) ^ 2) := by
      rw [Finset.prod_pow_eq_pow_sum]
      refine pow_le_pow_right₀ (by norm_num) ?_
      have hsum : ∑ i ∈ Finset.range R, 2 * b_cap i ≤ 100 * (R + 1) ^ 2 := by
        calc ∑ i ∈ Finset.range R, 2 * b_cap i
            ≤ ∑ _i ∈ Finset.range R, (36 + 4 * R) := Finset.sum_le_sum fun i hi => by
                have := Finset.mem_range.mp hi; dsimp [b_cap]; omega
          _ = R * (36 + 4 * R) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
          _ ≤ 100 * (R + 1) ^ 2 := by
              have : R * (36 + 4 * R) + (164 * R + 96 * R ^ 2 + 100) = 100 * (R + 1) ^ 2 := by ring
              omega
      exact hsum
    -- Bound second factor ∏_{i < R} (2^(L / 2^i))^(2 * b_cap i) ≤ (2 * z)^80 = 2^80 * z^80
    have hfac2 : ∏ i ∈ Finset.range R, ((2 : ℝ) ^ ((L : ℝ) / (2 : ℝ) ^ i)) ^ (2 * b_cap i) ≤
        (2 : ℝ) ^ 80 * (z : ℝ) ^ 80 := by
      have hrew : ∀ i ∈ Finset.range R,
          ((2 : ℝ) ^ ((L : ℝ) / (2 : ℝ) ^ i)) ^ (2 * b_cap i) =
            (2 : ℝ) ^ ((L : ℝ) * (2 * (b_cap i : ℝ) / (2 : ℝ) ^ i)) := by
        intro i _
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1; push_cast; ring
      rw [Finset.prod_congr rfl hrew, ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hexp_le : ∑ i ∈ Finset.range R, (L : ℝ) * (2 * (b_cap i : ℝ) / (2 : ℝ) ^ i) ≤ 80 * (L : ℝ) := by
        rw [← Finset.mul_sum]
        have hinner : ∑ i ∈ Finset.range R, 2 * (b_cap i : ℝ) / (2 : ℝ) ^ i ≤ 80 := by
          have hterm : ∀ i ∈ Finset.range R,
              2 * (b_cap i : ℝ) / (2 : ℝ) ^ i = 36 * (1 / (2 : ℝ) ^ i) + 4 * ((i : ℝ) / (2 : ℝ) ^ i) := by
            intro i _; dsimp [b_cap]; push_cast; ring
          rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          linarith [(sum_geom_series_inv_two R).1, (sum_geom_series_inv_two R).2]
        nlinarith [Nat.cast_nonneg (α := ℝ) L]
      have h2L_le_2z : (2 : ℝ) ^ (L : ℝ) ≤ 2 * (z : ℝ) := by
        rw [Real.rpow_natCast]
        have h1 : 2 ^ L = 2 * 2 ^ (L - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hL_pos, pow_succ]
          ring
        have h2 : 2 ^ L ≤ 2 * z := h1 ▸ Nat.mul_le_mul_left 2 h2L_le
        exact_mod_cast h2
      calc (2 : ℝ) ^ (∑ i ∈ Finset.range R, (L : ℝ) * (2 * (b_cap i : ℝ) / (2 : ℝ) ^ i))
          ≤ (2 : ℝ) ^ (80 * (L : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
        _ = ((2 : ℝ) ^ (L : ℝ)) ^ (80 : ℕ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring
        _ ≤ (2 * (z : ℝ)) ^ (80 : ℕ) := pow_le_pow_left₀ (by positivity) h2L_le_2z 80
        _ = (2 : ℝ) ^ 80 * (z : ℝ) ^ 80 := mul_pow _ _ _
    have hcard_le_rem : (AdmSet.card : ℝ) ≤
        (2 : ℝ) ^ (100 * (R + 1) ^ 2 + 80) * (z : ℝ) ^ 80 := by
      calc (AdmSet.card : ℝ)
          ≤ (2 : ℝ) ^ (100 * (R + 1) ^ 2) * ((2 : ℝ) ^ 80 * (z : ℝ) ^ 80) :=
            hprod_le.trans (mul_le_mul hfac1 hfac2 (by positivity) (by positivity))
        _ = (2 : ℝ) ^ (100 * (R + 1) ^ 2 + 80) * (z : ℝ) ^ 80 := by rw [pow_add]; ring
    have hV_lb := h_V_ge z (by omega)
    have hgoal_eq : (Nat.log 2 L + 2 : ℕ) = R + 1 := rfl
    rw [hgoal_eq] at hz_rem
    calc (AdmSet.card : ℝ)
        ≤ (2 : ℝ) ^ (100 * (R + 1) ^ 2 + 80) * (z : ℝ) ^ 80 := hcard_le_rem
      _ ≤ 0.01 * ((z : ℝ) ^ 100 / (3 * Real.log (z : ℝ))) := hz_rem
      _ = 0.01 * (z : ℝ) ^ 100 * (1 / (3 * Real.log (z : ℝ))) := by ring
      _ ≤ 0.01 * ((b - a : ℕ) : ℝ) * Vz := by
          gcongr
  -- Step 5: Combine!
  have h1 : (0.99 : ℝ) * ((b - a : ℕ) : ℝ) * Vz ≤
      ((b - a : ℕ) : ℝ) * ∑ D ∈ AdmSet, (-1 : ℝ) ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hmain_lower (Nat.cast_nonneg (b - a))
    linarith
  have hnn : 0 ≤ ((b - a : ℕ) : ℝ) * Vz := mul_nonneg (Nat.cast_nonneg _) hVz_pos.le
  have hmargin : (0.90 : ℝ) * ((b - a : ℕ) : ℝ) * Vz ≤
      (0.99 : ℝ) * ((b - a : ℕ) : ℝ) * Vz - 0.01 * ((b - a : ℕ) : ℝ) * Vz := by
    have hrew : (0.99 : ℝ) * ((b - a : ℕ) : ℝ) * Vz - 0.01 * ((b - a : ℕ) : ℝ) * Vz -
        (0.90 : ℝ) * ((b - a : ℕ) : ℝ) * Vz = 0.08 * (((b - a : ℕ) : ℝ) * Vz) := by ring
    linarith
  have hgoal_Ioc : (0.90 : ℝ) * ((b - a : ℕ) : ℝ) * Vz ≤
      (((Finset.Ioc a b).filter (fun q => ∀ p ∈ Pz, ¬ p ∣ q)).card : ℝ) := by linarith
  convert hgoal_Ioc

/- ### Section 4: Buchstab-Primes Induction for `w < Y ≤ w ^ 101` -/

noncomputable def siftedDyad (Y : ℝ) (w : ℕ) : Finset ℕ :=
  (Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter (fun q => ∀ p ∈ (Finset.Icc 1 w).filter Nat.Prime, ¬ p ∣ q)

private lemma mem_siftedDyad_iff {Y : ℝ} {w q : ℕ} :
    q ∈ siftedDyad Y w ↔
      q ∈ Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊ ∧ ∀ p ∈ (Finset.Icc 1 w).filter Nat.Prime, ¬ p ∣ q := by
  unfold siftedDyad
  exact @Finset.mem_filter _ _ (Classical.decPred _) _ _

set_option maxHeartbeats 800000 in
lemma buchstab_primes_lower
    (h_dyad : ∀ᶠ Y : ℝ in atTop,
      (0.68 : ℝ) * Y / Real.log Y ≤ (((Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime).card : ℝ))
    (h_sum_inv_log : ∀ {W B : ℕ}, 3 ≤ W → W ≤ B →
      1 / Real.log (W : ℝ) - 1 / Real.log (B : ℝ) - 100 / (Real.log (W : ℝ)) ^ 2 ≤
        ∑ p ∈ (Finset.Ioc W B).filter Nat.Prime, 1 / ((p : ℝ) * Real.log (p : ℝ))) :
    ∃ w0 : ℕ, 1000 ≤ w0 ∧ ∀ k : ℕ, 2 ≤ k → k ≤ 101 →
      ∀ w : ℕ, w0 ≤ w → ∀ Y : ℝ, (w : ℝ) < Y → Y ≤ (w : ℝ) ^ k →
        (0.24 : ℝ) * Y / Real.log (w : ℝ) ≤ ((siftedDyad Y w).card : ℝ) := by
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.mp h_dyad
  -- Pick w0 large enough: w0 ≥ 1000, w0 ≥ Y0, log w0 ≥ 200000
  obtain ⟨W1, hW1⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop (200000 : ℝ)))
  refine ⟨max (max 1000 W1) (⌈Y0⌉₊ + 100), le_trans (le_max_left 1000 W1) (le_max_left _ _), ?_⟩
  set w0 := max (max 1000 W1) (⌈Y0⌉₊ + 100)
  have hw0_1000 : 1000 ≤ w0 := le_trans (le_max_left 1000 W1) (le_max_left _ _)
  have hw0_W1 : W1 ≤ w0 := le_trans (le_max_right 1000 W1) (le_max_left _ _)
  have hw0_Y0 : Y0 ≤ (w0 : ℝ) := by
    have h1 : (⌈Y0⌉₊ : ℝ) ≤ (w0 : ℝ) := by exact_mod_cast (le_trans (Nat.le_add_right _ 100) (le_max_right _ _))
    exact (Nat.le_ceil Y0).trans h1
  intro k hk2
  induction k, hk2 using Nat.le_induction with
  | base =>
    intro _ w hw Y hYw hYle
    have hY_ge_Y0 : Y0 ≤ Y := hw0_Y0.trans ((by exact_mod_cast hw : (w0 : ℝ) ≤ w).trans hYw.le)
    have hpr := hY0 Y hY_ge_Y0
    have hsub : (Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime ⊆ siftedDyad Y w := by
      intro q hq
      simp only [siftedDyad, Finset.mem_filter, Finset.mem_Ico] at hq ⊢
      refine ⟨hq.1, fun p hp hdvd => ?_⟩
      have hp_pr := hp.2
      have hpw : p ≤ w := (Finset.mem_Icc.mp hp.1).2
      have hq_ge : Y ≤ (q : ℝ) := (Nat.le_ceil Y).trans (by exact_mod_cast hq.1.1)
      have hq_gt_w : w < q := by
        have : (w : ℝ) < (q : ℝ) := lt_of_lt_of_le hYw hq_ge
        exact_mod_cast this
      have heq := (Nat.prime_dvd_prime_iff_eq hp_pr hq.2).mp hdvd
      omega
    have hlogw_pos : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
    have hlogY_pos : 0 < Real.log Y := Real.log_pos (lt_trans (by exact_mod_cast (by omega : 1 < w)) hYw)
    have hlogY_le : Real.log Y ≤ 2 * Real.log (w : ℝ) := by
      have h := Real.log_le_log (lt_trans (by exact_mod_cast (by omega : 0 < w)) hYw) hYle
      rwa [Real.log_pow] at h
    have hY_pos : 0 < Y := lt_trans (by exact_mod_cast (by omega : 0 < w)) hYw
    calc (0.24 : ℝ) * Y / Real.log (w : ℝ)
        ≤ (0.68 : ℝ) * Y / (2 * Real.log (w : ℝ)) := by
          rw [div_le_div_iff₀ hlogw_pos (by positivity)]; nlinarith
      _ ≤ (0.68 : ℝ) * Y / Real.log Y :=
          div_le_div_of_nonneg_left (by positivity) hlogY_pos hlogY_le
      _ ≤ (((Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime).card : ℝ) := hpr
      _ ≤ ((siftedDyad Y w).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  | succ k hk2 ih =>
    intro hk101 w hw Y hYw hYle
    by_cases hsmall : Y ≤ 2 * (w : ℝ) ^ 2
    · -- Primes alone suffice when Y ≤ 2 * w^2 (since log Y ≤ 2.1 log w and 0.68 / 2.1 > 0.24)
      have hY_ge_Y0 : Y0 ≤ Y := hw0_Y0.trans ((by exact_mod_cast hw : (w0 : ℝ) ≤ w).trans hYw.le)
      have hpr := hY0 Y hY_ge_Y0
      have hsub : (Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime ⊆ siftedDyad Y w := by
        intro q hq
        simp only [siftedDyad, Finset.mem_filter, Finset.mem_Ico] at hq ⊢
        refine ⟨hq.1, fun p hp hdvd => ?_⟩
        have hp_pr := hp.2
        have hpw : p ≤ w := (Finset.mem_Icc.mp hp.1).2
        have hq_ge : Y ≤ (q : ℝ) := (Nat.le_ceil Y).trans (by exact_mod_cast hq.1.1)
        have hq_gt_w : w < q := by exact_mod_cast (lt_of_lt_of_le hYw hq_ge)
        have heq := (Nat.prime_dvd_prime_iff_eq hp_pr hq.2).mp hdvd
        omega
      have hw_pos : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
      have hlogw_ge : (200000 : ℝ) ≤ Real.log (w : ℝ) := hW1 w (hw0_W1.trans hw)
      have hlogw_pos : 0 < Real.log (w : ℝ) := by linarith
      have hY_pos : 0 < Y := lt_trans hw_pos hYw
      have hlogY_pos : 0 < Real.log Y := Real.log_pos (lt_trans (by exact_mod_cast (by omega : 1 < w)) hYw)
      have hlogY_le : Real.log Y ≤ 2.1 * Real.log (w : ℝ) := by
        have h := Real.log_le_log hY_pos hsmall
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
        push_cast at h
        have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
        linarith
      calc (0.24 : ℝ) * Y / Real.log (w : ℝ)
          ≤ (0.68 : ℝ) * Y / (2.1 * Real.log (w : ℝ)) := by
            rw [div_le_div_iff₀ hlogw_pos (by positivity)]; nlinarith
        _ ≤ (0.68 : ℝ) * Y / Real.log Y :=
            div_le_div_of_nonneg_left (by positivity) hlogY_pos hlogY_le
        _ ≤ (((Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime).card : ℝ) := hpr
        _ ≤ ((siftedDyad Y w).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    · push Not at hsmall
      have hY_ge_Y0 : Y0 ≤ Y := hw0_Y0.trans ((by exact_mod_cast hw : (w0 : ℝ) ≤ w).trans hYw.le)
      have hw_pos : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
      have hw1000 : 1000 ≤ w := hw0_1000.trans hw
      have hY_pos : 0 < Y := lt_trans hw_pos hYw
      have hlogw_ge : (200000 : ℝ) ≤ Real.log (w : ℝ) := hW1 w (hw0_W1.trans hw)
      have hlogw_pos : 0 < Real.log (w : ℝ) := by linarith
      have hlogY_pos : 0 < Real.log Y := Real.log_pos (lt_trans (by exact_mod_cast (by omega : 1 < w)) hYw)
      set B : ℕ := ⌊Real.sqrt Y⌋₊ - 1
      have hsqY_gt : (1.4 : ℝ) * (w : ℝ) < Real.sqrt Y := by
        rw [Real.lt_sqrt (by positivity)]
        nlinarith
      have hB_ge_sqrt : 0.99 * Real.sqrt Y ≤ (B : ℝ) := by
        have hfl_ge : Real.sqrt Y - 1 ≤ (⌊Real.sqrt Y⌋₊ : ℝ) := by
          linarith [Nat.lt_floor_add_one (Real.sqrt Y)]
        have hfl_pos : 1 ≤ ⌊Real.sqrt Y⌋₊ := by
          have : (1000 : ℝ) ≤ Real.sqrt Y := by linarith [show (1000 : ℝ) ≤ w by exact_mod_cast hw1000]
          have : 1000 ≤ ⌊Real.sqrt Y⌋₊ := Nat.le_floor this
          omega
        have hB_ge : Real.sqrt Y - 2 ≤ (B : ℝ) := by
          dsimp [B]; rw [Nat.cast_sub hfl_pos]; push_cast; linarith
        have hsq_big : (1000 : ℝ) ≤ Real.sqrt Y := by linarith [show (1000 : ℝ) ≤ w by exact_mod_cast hw1000]
        linarith
      have hB_lt_sqrt : (B : ℝ) < Real.sqrt Y := by
        have hfl_pos : 1 ≤ ⌊Real.sqrt Y⌋₊ := by
          have : (1000 : ℝ) ≤ Real.sqrt Y := by linarith [show (1000 : ℝ) ≤ w by exact_mod_cast hw1000]
          have : 1000 ≤ ⌊Real.sqrt Y⌋₊ := Nat.le_floor this
          omega
        dsimp [B]; rw [Nat.cast_sub hfl_pos]; push_cast
        linarith [Nat.floor_le (Real.sqrt_nonneg Y)]
      have hw_le_B : w ≤ B := by
        have hw_r : (w : ℝ) ≤ (B : ℝ) := by
          have : (1000 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw1000
          nlinarith
        exact_mod_cast hw_r
      -- Disjoint subsets of siftedDyad Y w:
      -- 1) Primes P_dyad = (Ico ⌈Y⌉₊ ⌈2*Y⌉₊).filter Nat.Prime
      -- 2) For each prime p ∈ (Ioc w B).filter Nat.Prime, C p = (siftedDyad (Y / p) p).image (fun t => p * t)
      set P_dyad := (Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter Nat.Prime
      set PrB := (Finset.Ioc w B).filter Nat.Prime
      let C (p : ℕ) : Finset ℕ := (siftedDyad (Y / (p : ℝ)) p).image (fun t => p * t)
      have hP_sub : P_dyad ⊆ siftedDyad Y w := by
        intro q hq
        simp only [P_dyad, siftedDyad, Finset.mem_filter, Finset.mem_Ico] at hq ⊢
        refine ⟨hq.1, fun p hp hdvd => ?_⟩
        have hp_pr := hp.2
        have hpw : p ≤ w := (Finset.mem_Icc.mp hp.1).2
        have hq_ge : Y ≤ (q : ℝ) := (Nat.le_ceil Y).trans (by exact_mod_cast hq.1.1)
        have hq_gt_w : w < q := by exact_mod_cast (lt_of_lt_of_le hYw hq_ge)
        have heq := (Nat.prime_dvd_prime_iff_eq hp_pr hq.2).mp hdvd
        omega
      have hC_prop : ∀ p ∈ PrB, ∀ m ∈ C p,
          m ∈ siftedDyad Y w ∧ ¬ m.Prime ∧ m.minFac = p := by
        intro p hp m hm
        obtain ⟨hp_Ioc, hp_pr⟩ := Finset.mem_filter.mp hp
        have hpw : w < p := (Finset.mem_Ioc.mp hp_Ioc).1
        have hpB : p ≤ B := (Finset.mem_Ioc.mp hp_Ioc).2
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
        have hp_lt_sq : (p : ℝ) < Real.sqrt Y := lt_of_le_of_lt (by exact_mod_cast hpB) hB_lt_sqrt
        have hp2_lt_Y : (p : ℝ) ^ 2 < Y := by
          have := pow_lt_pow_left₀ hp_lt_sq hp_pos.le (by decide : 2 ≠ 0)
          rwa [Real.sq_sqrt hY_pos.le] at this
        have hp_lt_Yp : (p : ℝ) < Y / (p : ℝ) := by
          rw [lt_div_iff₀ hp_pos]; nlinarith
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
        obtain ⟨ht_Ico, ht_ndvd⟩ := mem_siftedDyad_iff.mp ht
        have ht_ge : Y / (p : ℝ) ≤ (t : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (Finset.mem_Ico.mp ht_Ico).1)
        have ht_lt : (t : ℝ) < 2 * (Y / (p : ℝ)) := Nat.lt_ceil.mp (Finset.mem_Ico.mp ht_Ico).2
        have hpt_ge : Y ≤ ((p * t : ℕ) : ℝ) := by
          push_cast
          have := mul_le_mul_of_nonneg_left ht_ge hp_pos.le
          rwa [mul_div_cancel₀ _ hp_pos.ne'] at this
        have hpt_lt : ((p * t : ℕ) : ℝ) < 2 * Y := by
          push_cast
          have := mul_lt_mul_of_pos_left ht_lt hp_pos
          have h2 : (p : ℝ) * (2 * (Y / (p : ℝ))) = 2 * Y := by field_simp [hp_pos.ne']
          linarith
        have hpt_Ico : p * t ∈ Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊ :=
          Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr hpt_ge, Nat.lt_ceil.mpr hpt_lt⟩
        have ht_gt_p : p < t := by exact_mod_cast (lt_of_lt_of_le hp_lt_Yp ht_ge)
        have hnot_pr : ¬ (p * t).Prime := Nat.not_prime_mul hp_pr.one_lt.ne' (by omega)
        have hminFac : (p * t).minFac = p := by
          have hmf_le : (p * t).minFac ≤ p := Nat.minFac_le_of_dvd hp_pr.two_le (dvd_mul_right p t)
          have hmf_pr : (p * t).minFac.Prime := Nat.minFac_prime (by have := hp_pr.two_le; nlinarith)
          have hmf_dvd : (p * t).minFac ∣ p * t := Nat.minFac_dvd (p * t)
          rcases hmf_pr.dvd_mul.mp hmf_dvd with hdp | hdt
          · exact (Nat.prime_dvd_prime_iff_eq hmf_pr hp_pr).mp hdp
          · exfalso
            exact ht_ndvd (p * t).minFac (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmf_pr.one_le, hmf_le⟩, hmf_pr⟩) hdt
        refine ⟨?_, hnot_pr, hminFac⟩
        rw [mem_siftedDyad_iff]
        refine ⟨hpt_Ico, fun r hr hdvd => ?_⟩
        have hr_pr := (Finset.mem_filter.mp hr).2
        have hrw : r ≤ w := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).2
        rcases hr_pr.dvd_mul.mp hdvd with hdp | hdt
        · have := (Nat.prime_dvd_prime_iff_eq hr_pr hp_pr).mp hdp; omega
        · exact ht_ndvd r (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr_pr.one_le, by omega⟩, hr_pr⟩) hdt
      have hC_pw : (PrB : Set ℕ).PairwiseDisjoint C := by
        intro p1 hp1 p2 hp2 hne
        rw [Function.onFun, Finset.disjoint_left]
        intro m hm1 hm2
        have h1 := (hC_prop p1 hp1 m hm1).2.2
        have h2 := (hC_prop p2 hp2 m hm2).2.2
        exact hne (h1.symm.trans h2)
      have hdisj_PC : Disjoint P_dyad (PrB.biUnion C) := by
        rw [Finset.disjoint_left]
        intro m hmP hmC
        obtain ⟨p, hp, hmp⟩ := Finset.mem_biUnion.mp hmC
        exact (hC_prop p hp m hmp).2.1 (Finset.mem_filter.mp hmP).2
      have hunion_sub : P_dyad ∪ PrB.biUnion C ⊆ siftedDyad Y w := by
        refine Finset.union_subset hP_sub (Finset.biUnion_subset.mpr fun p hp m hm => (hC_prop p hp m hm).1)
      have hcard_ge : ((P_dyad.card : ℝ) + ∑ p ∈ PrB, ((siftedDyad (Y / (p : ℝ)) p).card : ℝ)) ≤
          ((siftedDyad Y w).card : ℝ) := by
        have h1 : P_dyad.card + ∑ p ∈ PrB, (C p).card ≤ (siftedDyad Y w).card := by
          rw [← Finset.card_biUnion hC_pw, ← Finset.card_union_of_disjoint hdisj_PC]
          exact Finset.card_le_card hunion_sub
        have hC_card : ∀ p ∈ PrB, (C p).card = (siftedDyad (Y / (p : ℝ)) p).card := fun p hp =>
          Finset.card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left (Finset.mem_filter.mp hp).2.pos hab)
        rw [Finset.sum_congr rfl hC_card] at h1
        exact_mod_cast h1
      -- Apply IH to every p ∈ PrB!
      have hC_lb : ∀ p ∈ PrB,
          (0.24 : ℝ) * (Y / (p : ℝ)) / Real.log (p : ℝ) ≤ ((siftedDyad (Y / (p : ℝ)) p).card : ℝ) := by
        intro p hp
        obtain ⟨hp_Ioc, hp_pr⟩ := Finset.mem_filter.mp hp
        have hpw : w < p := (Finset.mem_Ioc.mp hp_Ioc).1
        have hpB : p ≤ B := (Finset.mem_Ioc.mp hp_Ioc).2
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
        have hp_lt_sq : (p : ℝ) < Real.sqrt Y := lt_of_le_of_lt (by exact_mod_cast hpB) hB_lt_sqrt
        have hp2_lt_Y : (p : ℝ) ^ 2 < Y := by
          have := pow_lt_pow_left₀ hp_lt_sq hp_pos.le (by decide : 2 ≠ 0)
          rwa [Real.sq_sqrt hY_pos.le] at this
        have hp_lt_Yp : (p : ℝ) < Y / (p : ℝ) := by rw [lt_div_iff₀ hp_pos]; nlinarith
        have hYp_le : Y / (p : ℝ) ≤ (p : ℝ) ^ k := by
          rw [div_le_iff₀ hp_pos]
          have hwp : (w : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpw.le
          calc Y ≤ (w : ℝ) ^ (k + 1) := hYle
            _ = (w : ℝ) ^ k * (w : ℝ) := pow_succ _ _
            _ ≤ (p : ℝ) ^ k * (p : ℝ) := mul_le_mul (pow_le_pow_left₀ hw_pos.le hwp k) hwp hw_pos.le (by positivity)
        exact ih (by omega) p (by omega) (Y / (p : ℝ)) hp_lt_Yp hYp_le
      have hsum_C : (0.24 : ℝ) * Y * ∑ p ∈ PrB, 1 / ((p : ℝ) * Real.log (p : ℝ)) ≤
          ∑ p ∈ PrB, ((siftedDyad (Y / (p : ℝ)) p).card : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun p hp => ?_
        have h := hC_lb p hp
        have hrew : (0.24 : ℝ) * Y * (1 / ((p : ℝ) * Real.log (p : ℝ))) = (0.24 : ℝ) * (Y / (p : ℝ)) / Real.log (p : ℝ) := by ring
        linarith
      have hP_lb := hY0 Y hY_ge_Y0
      have hAbel := h_sum_inv_log (by omega : 3 ≤ w) hw_le_B
      -- Lower bound log B ≥ (1/2) log Y - 0.02 ⇒ 1 / log B ≤ 2 / log Y + 1 / (log w)^2
      have hlogB_ge : Real.log Y / 2 - 0.02 ≤ Real.log (B : ℝ) := by
        have h1 := Real.log_le_log (by positivity) hB_ge_sqrt
        rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hY_pos).ne', Real.log_sqrt hY_pos.le] at h1
        have hlog099 : -0.02 ≤ Real.log (0.99 : ℝ) := by
          have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (0.99 : ℝ)⁻¹ by norm_num)
          rw [Real.log_inv] at h
          linarith [show ((0.99 : ℝ)⁻¹ - 1) ≤ 0.02 by norm_num]
        linarith
      have hlogY_ge : 2 * Real.log (w : ℝ) ≤ Real.log Y := by
        have h1 : (w : ℝ) ^ 2 ≤ Y := by linarith
        have h2 := Real.log_le_log (by positivity) h1
        rw [Real.log_pow] at h2; push_cast at h2; linarith
      have hlogY_le_101 : Real.log Y ≤ 101 * Real.log (w : ℝ) := by
        have h1 : Y ≤ (w : ℝ) ^ 101 := hYle.trans (pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ w)) hk101)
        have h2 := Real.log_le_log hY_pos h1
        rw [Real.log_pow] at h2; push_cast at h2; exact h2
      have hinvB_le : 1 / Real.log (B : ℝ) ≤ 2 / Real.log Y + 1 / (Real.log (w : ℝ)) ^ 2 := by
        have hlogB_pos : 0 < Real.log (B : ℝ) := by linarith
        have hden : Real.log Y / 4 ≤ Real.log (B : ℝ) := by linarith
        have hdiff : 1 / Real.log (B : ℝ) - 2 / Real.log Y =
            (Real.log Y - 2 * Real.log (B : ℝ)) / (Real.log (B : ℝ) * Real.log Y) := by
          field_simp [hlogB_pos.ne', hlogY_pos.ne']
        have hnum_le : Real.log Y - 2 * Real.log (B : ℝ) ≤ 0.04 := by linarith
        have hprod_ge : (Real.log (w : ℝ)) ^ 2 ≤ Real.log (B : ℝ) * Real.log Y := by nlinarith
        have hstep1 : (Real.log Y - 2 * Real.log (B : ℝ)) / (Real.log (B : ℝ) * Real.log Y) ≤
            1 / (Real.log (w : ℝ)) ^ 2 := by
          rw [div_le_div_iff₀ (mul_pos hlogB_pos hlogY_pos) (sq_pos_of_pos hlogw_pos)]
          nlinarith
        linarith
      have hsum_inv_lb : 1 / Real.log (w : ℝ) - 2 / Real.log Y - 101 / (Real.log (w : ℝ)) ^ 2 ≤
          ∑ p ∈ PrB, 1 / ((p : ℝ) * Real.log (p : ℝ)) := by
        have : 100 / (Real.log (w : ℝ)) ^ 2 + 1 / (Real.log (w : ℝ)) ^ 2 = 101 / (Real.log (w : ℝ)) ^ 2 := by ring
        linarith
      have hcomb_Y : (0.68 : ℝ) / Real.log Y +
          (0.24 : ℝ) * (1 / Real.log (w : ℝ) - 2 / Real.log Y - 101 / (Real.log (w : ℝ)) ^ 2) ≥
          (0.24 : ℝ) / Real.log (w : ℝ) := by
        have h1 : (0.20 : ℝ) / Real.log Y ≥ (0.0019 : ℝ) / Real.log (w : ℝ) := by
          rw [ge_iff_le, div_le_div_iff₀ hlogw_pos hlogY_pos]
          linarith
        have h2 : (24.24 : ℝ) / (Real.log (w : ℝ)) ^ 2 ≤ (0.0019 : ℝ) / Real.log (w : ℝ) := by
          rw [div_le_div_iff₀ (sq_pos_of_pos hlogw_pos) hlogw_pos]
          nlinarith
        have hrew : (0.68 : ℝ) / Real.log Y +
            (0.24 : ℝ) * (1 / Real.log (w : ℝ) - 2 / Real.log Y - 101 / (Real.log (w : ℝ)) ^ 2) -
            (0.24 : ℝ) / Real.log (w : ℝ) =
            (0.20 : ℝ) / Real.log Y - (24.24 : ℝ) / (Real.log (w : ℝ)) ^ 2 := by ring
        linarith
      have hfinal : (0.24 : ℝ) * Y / Real.log (w : ℝ) ≤
          (0.68 : ℝ) * Y / Real.log Y + (0.24 : ℝ) * Y * ∑ p ∈ PrB, 1 / ((p : ℝ) * Real.log (p : ℝ)) := by
        have hm1 : (0.24 : ℝ) * Y * (1 / Real.log (w : ℝ) - 2 / Real.log Y - 101 / (Real.log (w : ℝ)) ^ 2) ≤
            (0.24 : ℝ) * Y * ∑ p ∈ PrB, 1 / ((p : ℝ) * Real.log (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum_inv_lb (by positivity)
        have hm2 := mul_le_mul_of_nonneg_left hcomb_Y hY_pos.le
        have ha : Y * ((0.24 : ℝ) / Real.log (w : ℝ)) = (0.24 : ℝ) * Y / Real.log (w : ℝ) := by ring
        have hb : Y * ((0.68 : ℝ) / Real.log Y + (0.24 : ℝ) * (1 / Real.log (w : ℝ) - 2 / Real.log Y - 101 / (Real.log (w : ℝ)) ^ 2)) =
            (0.68 : ℝ) * Y / Real.log Y + (0.24 : ℝ) * Y * (1 / Real.log (w : ℝ) - 2 / Real.log Y - 101 / (Real.log (w : ℝ)) ^ 2) := by ring
        linarith
      linarith

end Erdos360H1Part3b
end -- Erdos360_H1_part3b.lean

section -- Erdos360_H1_part4.lean
open Finset Filter Real Nat
open scoped BigOperators Classical

namespace Erdos360H1Part4

noncomputable def siftedDyad4 (Y : ℝ) (w : ℕ) : Finset ℕ :=
  (Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊).filter (fun q => ∀ p ∈ (Finset.Icc 1 w).filter Nat.Prime, ¬ p ∣ q)

private lemma mem_siftedDyad4_iff {Y : ℝ} {w q : ℕ} :
    q ∈ siftedDyad4 Y w ↔
      q ∈ Finset.Ico ⌈Y⌉₊ ⌈2 * Y⌉₊ ∧ ∀ p ∈ (Finset.Icc 1 w).filter Nat.Prime, ¬ p ∣ q := by
  unfold siftedDyad4
  exact @Finset.mem_filter _ _ (Classical.decPred _) _ _

private lemma Ico_eq_Ioc_pred {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Finset.Ico a b = Finset.Ioc (a - 1) (b - 1) := by
  ext q; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega

private lemma card_Ico_filter_dvd_le (a b p : ℕ) (hp : 1 ≤ p) :
    (((Finset.Ico a b).filter (fun q => p ∣ q)).card : ℝ) ≤ ((b - a : ℕ) : ℝ) / (p : ℝ) + 2 := by
  by_cases hab : a ≤ b
  · by_cases ha : a = 0
    · subst ha
      have hsub : (Finset.Ico 0 b).filter (fun q => p ∣ q) ⊆
          insert 0 ((Finset.Icc 1 (b / p)).image (fun m => p * m)) := by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc] at hq ⊢
        rcases eq_or_ne q 0 with rfl | hq0
        · exact Or.inl rfl
        · right
          obtain ⟨m, rfl⟩ := hq.2
          refine ⟨m, ⟨?_, ?_⟩, rfl⟩
          · by_contra hm0; simp [show m = 0 by omega] at hq0
          · exact (Nat.le_div_iff_mul_le hp).mpr (by linarith)
      have hc : ((Finset.Ico 0 b).filter (fun q => p ∣ q)).card ≤ 1 + b / p := by
        calc _ ≤ (insert 0 ((Finset.Icc 1 (b / p)).image (fun m => p * m))).card := Finset.card_le_card hsub
          _ ≤ 1 + ((Finset.Icc 1 (b / p)).image (fun m => p * m)).card := by
              have := Finset.card_insert_le 0 ((Finset.Icc 1 (b / p)).image (fun m => p * m)); omega
          _ ≤ 1 + (Finset.Icc 1 (b / p)).card := Nat.add_le_add_left Finset.card_image_le 1
          _ = 1 + b / p := by simp
      have hdiv : ((b / p : ℕ) : ℝ) ≤ (b : ℝ) / (p : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hp)]; exact_mod_cast Nat.div_mul_le_self b p
      have hc_r : (((Finset.Ico 0 b).filter (fun q => p ∣ q)).card : ℝ) ≤ 1 + ((b / p : ℕ) : ℝ) := by exact_mod_cast hc
      simp only [Nat.sub_zero]; linarith
    · have ha1 : 1 ≤ a := by omega
      rw [Ico_eq_Ioc_pred ha1 hab]
      have hsub : ((Finset.Ioc (a - 1) (b - 1)).filter (fun q => p ∣ q)).card = (b - 1) / p - (a - 1) / p := by
        have h0 : ∀ n : ℕ, ((Finset.Ioc 0 n).filter (fun q => p ∣ q)).card = n / p := by
          intro n
          have heq : (Finset.Ioc 0 n).filter (fun q => p ∣ q) = (Finset.Icc 1 (n / p)).image (fun m => p * m) := by
            ext q; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
            constructor
            · rintro ⟨⟨hq0, hqn⟩, m, rfl⟩
              refine ⟨m, ⟨?_, ?_⟩, rfl⟩
              · by_contra hm0; simp [show m = 0 by omega] at hq0
              · exact (Nat.le_div_iff_mul_le hp).mpr (by linarith)
            · rintro ⟨m, ⟨hm1, hmn⟩, rfl⟩
              refine ⟨⟨Nat.mul_pos hp hm1, ?_⟩, m, rfl⟩
              have := (Nat.le_div_iff_mul_le hp).mp hmn; linarith
          rw [heq, Finset.card_image_of_injective _ (fun x y h => Nat.eq_of_mul_eq_mul_left hp h)]; simp
        have hsdiff : (Finset.Ioc (a - 1) (b - 1)).filter (fun q => p ∣ q) =
            ((Finset.Ioc 0 (b - 1)).filter (fun q => p ∣ q)) \ ((Finset.Ioc 0 (a - 1)).filter (fun q => p ∣ q)) := by
          ext q; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff]; omega
        have hsub' : (Finset.Ioc 0 (a - 1)).filter (fun q => p ∣ q) ⊆ (Finset.Ioc 0 (b - 1)).filter (fun q => p ∣ q) := by
          intro q hq; simp only [Finset.mem_filter, Finset.mem_Ioc] at hq ⊢; exact ⟨⟨hq.1.1, by omega⟩, hq.2⟩
        rw [hsdiff, Finset.card_sdiff_of_subset hsub', h0 (b - 1), h0 (a - 1)]
      rw [hsub]
      have hppos : (0 : ℝ) < p := by exact_mod_cast hp
      have hdiv_le : (a - 1) / p ≤ (b - 1) / p := Nat.div_le_div_right (by omega)
      rw [Nat.cast_sub hdiv_le]
      have h1 : (((b - 1) / p : ℕ) : ℝ) ≤ ((b - 1 : ℕ) : ℝ) / (p : ℝ) := by
        rw [le_div_iff₀ hppos]; exact_mod_cast Nat.div_mul_le_self (b - 1) p
      have h2 : ((a - 1 : ℕ) : ℝ) / (p : ℝ) - 1 < (((a - 1) / p : ℕ) : ℝ) := by
        have := Nat.lt_div_mul_add (a := a - 1) (b := p) hp
        have hcast : ((a - 1 : ℕ) : ℝ) < (((a - 1) / p : ℕ) : ℝ) * p + p := by exact_mod_cast this
        rw [sub_lt_iff_lt_add, div_lt_iff₀ hppos]; linarith
      have hba_eq : ((b - 1 : ℕ) : ℝ) - ((a - 1 : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) := by
        have h1 : b - 1 ≥ a - 1 := by omega
        rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_sub ha1, Nat.cast_sub hab]; push_cast; ring
      have hdiff_div : ((b - 1 : ℕ) : ℝ) / (p : ℝ) - ((a - 1 : ℕ) : ℝ) / (p : ℝ) = ((b - a : ℕ) : ℝ) / (p : ℝ) := by
        rw [← sub_div, hba_eq]
      linarith
  · have he : Finset.Ico a b = ∅ := Finset.Ico_eq_empty (by omega)
    rw [he, Finset.filter_empty, Finset.card_empty]
    have : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) / (p : ℝ) := by positivity
    simp; linarith

set_option maxHeartbeats 1200000 in
theorem main_H1
    (h_nth_gt : ∀ {r : ℕ}, 1 ≤ r → r < Nat.nth Nat.Prime (r - 1))
    (h_first_eq : ∀ {r : ℕ}, 1 ≤ r →
      (Finset.range r).image (Nat.nth Nat.Prime) = (Finset.Icc 1 (Nat.nth Nat.Prime (r - 1))).filter Nat.Prime)
    (h_nth_le : ∀ᶠ r : ℕ in atTop, (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ 4 * (r : ℝ) * Real.log (r : ℝ))
    (h_V_le : ∀ z : ℕ, 2 ≤ z →
      ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) ≤ 1 / Real.log (z : ℝ))
    (h_V_ge : ∀ z : ℕ, 64 ≤ z →
      1 / (3 * Real.log (z : ℝ)) ≤ ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)))
    (h_div_le : ∀ {n : ℕ}, 1 ≤ n → ∑ u ∈ n.divisors, (1 : ℝ) / (u : ℝ) ≤ (n : ℝ) / (n.totient : ℝ))
    (h_div_small_ge : ∀ᶠ n : ℕ in atTop, ∀ U : ℝ, (n : ℝ) ^ (1 / 64 : ℝ) ≤ U →
      (0.60 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) ≤
        ∑ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ U), (1 : ℝ) / (u : ℝ))
    (h_selberg : ∀ {a b : ℕ}, a ≤ b → ∀ {w : ℝ}, 4 ≤ w →
      (((Finset.Ioc a b).filter (fun q => ∀ p ∈ (Finset.Icc 1 ⌊Real.sqrt w⌋₊).filter Nat.Prime, ¬ p ∣ q)).card : ℝ) ≤
        ((b - a : ℕ) : ℝ) / Real.log (Real.sqrt w) + w)
    (h_brun : ∀ᶠ z : ℕ in atTop, ∀ a b : ℕ, a ≤ b → (z : ℝ) ^ 100 ≤ ((b - a : ℕ) : ℝ) →
      (0.90 : ℝ) * ((b - a : ℕ) : ℝ) * ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ)) ≤
        (((Finset.Ioc a b).filter (fun q => ∀ p ∈ (Finset.Icc 1 z).filter Nat.Prime, ¬ p ∣ q)).card : ℝ))
    (h_buchstab : ∃ w0 : ℕ, 1000 ≤ w0 ∧ ∀ k : ℕ, 2 ≤ k → k ≤ 101 →
      ∀ w : ℕ, w0 ≤ w → ∀ Y : ℝ, (w : ℝ) < Y → Y ≤ (w : ℝ) ^ k →
        (0.24 : ℝ) * Y / Real.log (w : ℝ) ≤ ((siftedDyad4 Y w).card : ℝ)) :
    OMA.R_Erdos360_erdos_360_R1_H4_R1.H1 := by
  unfold OMA.R_Erdos360_erdos_360_R1_H4_R1.H1
  obtain ⟨r0, hr0⟩ := Filter.eventually_atTop.mp h_nth_le
  obtain ⟨z0, hz0⟩ := Filter.eventually_atTop.mp h_brun
  obtain ⟨w0, hw0_1000, hbuch⟩ := h_buchstab
  -- Collect all asymptotic thresholds on n
  have hX_asymp : ∀ᶠ X : ℝ in atTop,
      10000 ≤ X ∧
      20 ≤ Real.log X ∧
      Real.log (Real.log X) + Real.log 2 ≤ 0.01 * Real.log X ∧
      100 ≤ X / (Real.log X) ^ 2 := by
    have h1 : ∀ᶠ X : ℝ in atTop, 10000 ≤ X := Filter.eventually_ge_atTop 10000
    have h2 : ∀ᶠ X : ℝ in atTop, 20 ≤ Real.log X :=
      Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 20)
    have h3 : ∀ᶠ X : ℝ in atTop, Real.log (Real.log X) + Real.log 2 ≤ 0.01 * Real.log X := by
      have hl : Tendsto (fun t : ℝ => (Real.log t + Real.log 2) / t) atTop (nhds 0) := by
        have ha : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) :=
          (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero.congr' (by
            filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t _; rw [Real.rpow_one])
        have hb : Tendsto (fun t : ℝ => Real.log 2 / t) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have hsum : Tendsto (fun t : ℝ => Real.log t / t + Real.log 2 / t) atTop (nhds 0) := by
          simpa using ha.add hb
        refine hsum.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t _; rw [add_div]
      filter_upwards [(hl.comp Real.tendsto_log_atTop).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.01)),
        Real.tendsto_log_atTop.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with X hX hpos
      exact ((div_lt_iff₀ hpos).mp hX).le
    have h4 : ∀ᶠ X : ℝ in atTop, 100 ≤ X / (Real.log X) ^ 2 := by
      have hsq : Tendsto (fun X : ℝ => (Real.log X) ^ 2 / X) atTop (nhds 0) := by
        have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
        have h2' : Tendsto (fun X : ℝ => (Real.log X / X ^ (1 / 2 : ℝ)) ^ 2) atTop (nhds 0) := by
          simpa using h.pow 2
        refine h2'.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
        rw [div_pow, ← Real.rpow_natCast (X ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hX.le]; norm_num
      filter_upwards [hsq.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)),
        Real.tendsto_log_atTop.eventually (Filter.eventually_gt_atTop (0 : ℝ)),
        Filter.eventually_gt_atTop (0 : ℝ)] with X hX hlog hXpos
      have hlt := (div_lt_iff₀ hXpos).mp hX
      rw [le_div_iff₀ (sq_pos_of_pos hlog)]
      linarith
    filter_upwards [h1, h2, h3, h4] with X h1 h2 h3 h4; exact ⟨h1, h2, h3, h4⟩
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hX_asymp
  have hr_asymp : ∀ᶠ r : ℝ in atTop, 4 * r * Real.log r < r ^ (15 / 8 : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 7 / 8 by norm_num)).tendsto_div_nhds_zero
    filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      Filter.eventually_gt_atTop (1 : ℝ)] with r hr hr1
    have hrpos : 0 < r := by linarith
    have hlt := (div_lt_iff₀ (Real.rpow_pos_of_pos hrpos _)).mp hr
    have hmul : r * r ^ (7 / 8 : ℝ) = r ^ (15 / 8 : ℝ) := by
      have h1 : r ^ (1 : ℝ) * r ^ (7 / 8 : ℝ) = r ^ (1 + (7 / 8 : ℝ)) := (Real.rpow_add hrpos _ _).symm
      rw [Real.rpow_one] at h1; convert h1 using 2; norm_num
    nlinarith
  obtain ⟨R0, hR0⟩ := Filter.eventually_atTop.mp hr_asymp
  have hn_asymp : ∀ᶠ n : ℕ in atTop,
      (max (max (max r0 z0) w0) 1000 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) ∧
      R0 ≤ (n : ℝ) ^ (1 / 10 : ℝ) ∧
      X0 ≤ (n : ℝ) ^ (3 / 16 : ℝ) ∧
      9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) * (3 * Real.log (4 * (n : ℝ) * Real.log (n : ℝ))) ≤ 0.005 ∧
      Real.log (4 * (n : ℝ) * Real.log (n : ℝ)) ≤ 2 * Real.log (n : ℝ) ∧
      2 ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by
    have hp10 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 10 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    have hp316 : Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 16 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    have hlog4 : ∀ᶠ n : ℕ in atTop, Real.log (4 * (n : ℝ) * Real.log (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
      have h1 : Tendsto (fun x : ℝ => Real.log (4 * x) / x) atTop (nhds 0) := by
        have ha : Tendsto (fun x : ℝ => Real.log 4 / x) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have hb : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
          (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero.congr' (by
            filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x _; rw [Real.rpow_one])
        have hsum : Tendsto (fun x : ℝ => Real.log 4 / x + Real.log x / x) atTop (nhds 0) := by
          simpa using ha.add hb
        refine hsum.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
        rw [Real.log_mul (by norm_num) hx.ne']; ring
      filter_upwards [(h1.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
        Filter.eventually_ge_atTop 10] with n hn hn10
      have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hlt := (div_lt_iff₀ hlogn).mp hn
      dsimp only [Function.comp_apply] at hlt
      rw [show 4 * (n : ℝ) * Real.log (n : ℝ) = (n : ℝ) * (4 * Real.log (n : ℝ)) by ring,
        Real.log_mul (by exact_mod_cast (by omega : n ≠ 0)) (by positivity)]
      linarith
    have hE_err : ∀ᶠ n : ℕ in atTop,
        9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) * (6 * Real.log (n : ℝ)) ≤ 0.005 := by
      have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 10 : ℝ)) atTop (nhds 0) :=
        (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).tendsto_div_nhds_zero
      have h2 : Tendsto (fun x : ℝ => Real.log x / x ^ (3 / 16 : ℝ)) atTop (nhds 0) :=
        (isLittleO_log_rpow_atTop (show (0 : ℝ) < 3 / 16 by norm_num)).tendsto_div_nhds_zero
      filter_upwards [(h1.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100000)),
        (h2.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000000))] with n hn1 hn2
      dsimp only [Function.comp_apply] at hn1 hn2
      have hrew : 9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) * (6 * Real.log (n : ℝ)) =
          54 * (Real.log (n : ℝ) / (n : ℝ) ^ (1 / 10 : ℝ)) + 216 * (Real.log (n : ℝ) / (n : ℝ) ^ (3 / 16 : ℝ)) := by ring
      rw [hrew]; linarith
    filter_upwards [hp10.eventually (Filter.eventually_ge_atTop (max (max (max r0 z0) w0) 1000 : ℝ)),
      hp10.eventually (Filter.eventually_ge_atTop R0),
      hp316.eventually (Filter.eventually_ge_atTop X0),
      hE_err, hlog4, hp10.eventually (Filter.eventually_ge_atTop 2)] with n h1 h2 h3 h4 h5 h6
    refine ⟨h1, h2, h3, ?_, h5, h6⟩
    have hnn : 0 ≤ 9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) := by positivity
    calc 9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) * (3 * Real.log (4 * (n : ℝ) * Real.log (n : ℝ)))
        ≤ 9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) * (6 * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hnn
      _ ≤ 0.005 := h4
  filter_upwards [h_div_small_ge, hn_asymp, Filter.eventually_ge_atTop 10000] with
      n hdiv_sm ⟨hn_max, hn_R0, hn_X0, hn_Eerr, hn_log4, hn_2⟩ hn10000
  intro r x hrn hr_lo hx_lo
  dsimp only
  set P_r := (Finset.range r).image (Nat.nth Nat.Prime)
  set S := n.primeFactors ∪ P_r
  set tau := ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ))
  have hr_ge_max : max (max (max r0 z0) w0) 1000 ≤ r := by
    have : (max (max (max r0 z0) w0) 1000 : ℝ) ≤ (r : ℝ) := hn_max.trans hr_lo
    exact_mod_cast this
  have hr1000 : 1000 ≤ r := by omega
  have hr_r0 : r0 ≤ r := by omega
  have hr_z0 : z0 ≤ r := by omega
  have hr_w0 : w0 ≤ r := by omega
  set z := Nat.nth Nat.Prime (r - 1)
  have hz_gt_r : r < z := h_nth_gt (by omega)
  have hz_z0 : z0 ≤ z := by omega
  have hz_w0 : w0 ≤ z := by omega
  have hz1000 : 1000 ≤ z := by omega
  have hPr_eq : P_r = (Finset.Icc 1 z).filter Nat.Prime := h_first_eq (by omega)
  have hz_le_4rlog : (z : ℝ) ≤ 4 * (r : ℝ) * Real.log (r : ℝ) := hr0 r hr_r0
  have hz_le_4nlog : (z : ℝ) ≤ 4 * (n : ℝ) * Real.log (n : ℝ) := by
    have hrn_r : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
    have hlog_le : Real.log (r : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < r)) hrn_r
    have hlogr_nn : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
    calc (z : ℝ) ≤ 4 * (r : ℝ) * Real.log (r : ℝ) := hz_le_4rlog
      _ ≤ 4 * (n : ℝ) * Real.log (n : ℝ) := by gcongr
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  -- Extra primes E = n.primeFactors \ P_r
  set E := n.primeFactors \ P_r
  have hS_eq : S = P_r ∪ E := by
    ext p; simp only [S, E, Finset.mem_union, Finset.mem_sdiff]; tauto
  have hdisj_PE : Disjoint P_r E := Finset.disjoint_sdiff
  have hE_gt : ∀ p ∈ E, (n : ℝ) ^ (1 / 10 : ℝ) < (p : ℝ) := by
    intro p hp
    have hp_n := (Finset.mem_sdiff.mp hp).1
    have hp_not := (Finset.mem_sdiff.mp hp).2
    have hp_pr := Nat.prime_of_mem_primeFactors hp_n
    have hz_lt_p : z < p := by
      by_contra hle
      exact hp_not (hPr_eq ▸ Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_pr.one_le, by omega⟩, hp_pr⟩)
    have hr_lt_p : (r : ℝ) < (p : ℝ) := by exact_mod_cast (lt_trans hz_gt_r hz_lt_p)
    exact lt_of_le_of_lt hr_lo hr_lt_p
  have hE_card : E.card ≤ 9 := by
    by_contra hge
    have h10 : 10 ≤ E.card := by omega
    have hprod_le : (∏ p ∈ E, (p : ℝ)) ≤ (n : ℝ) := by
      have hdvd1 : ∏ p ∈ E, p ∣ ∏ p ∈ n.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset E n.primeFactors (fun p : ℕ => p) Finset.sdiff_subset
      have hdvd : ∏ p ∈ E, p ∣ n := dvd_trans hdvd1 (Nat.prod_primeFactors_dvd n)
      have hle : ∏ p ∈ E, p ≤ n := Nat.le_of_dvd (by omega) hdvd
      rw [← Nat.cast_prod]; exact_mod_cast hle
    have hprod_gt : ((n : ℝ) ^ (1 / 10 : ℝ)) ^ E.card < ∏ p ∈ E, (p : ℝ) := by
      rw [← Finset.prod_const]
      exact Finset.prod_lt_prod_of_nonempty (fun _ _ => by positivity) hE_gt (Finset.card_pos.mp (by omega))
    have h10_le : (n : ℝ) ≤ ((n : ℝ) ^ (1 / 10 : ℝ)) ^ E.card := by
      have hge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by linarith
      calc (n : ℝ) = ((n : ℝ) ^ (1 / 10 : ℝ)) ^ (10 : ℕ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]; norm_num
        _ ≤ ((n : ℝ) ^ (1 / 10 : ℝ)) ^ E.card := pow_le_pow_right₀ hge1 h10
    linarith
  set Vz := ∏ p ∈ P_r, (1 - (1 : ℝ) / (p : ℝ))
  have hVz_pos : 0 < Vz := Finset.prod_pos fun p hp => by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp (hPr_eq ▸ hp)).2.two_le
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have htau_eq : tau = Vz * ∏ p ∈ E, (1 - (1 : ℝ) / (p : ℝ)) := by
    dsimp [tau, Vz]; rw [hS_eq, Finset.prod_union hdisj_PE]
  have htau_le_Vz : tau ≤ Vz := by
    rw [htau_eq]
    have hE_le1 : ∏ p ∈ E, (1 - (1 : ℝ) / (p : ℝ)) ≤ 1 :=
      Finset.prod_le_one (fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).two_le
        rw [sub_nonneg, div_le_one (by linarith)]; linarith) (fun p _ => by
        have hnn : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith)
    nlinarith
  have htau_ge_Vz : 0.99 * Vz ≤ tau := by
    rw [htau_eq]
    have hE_ge : (0.99 : ℝ) ≤ ∏ p ∈ E, (1 - (1 : ℝ) / (p : ℝ)) := by
      have hterm : ∀ p ∈ E, (0.999 : ℝ) ≤ 1 - (1 : ℝ) / (p : ℝ) := by
        intro p hp
        have hp1000 : (1000 : ℝ) < (p : ℝ) :=
          lt_of_le_of_lt (le_trans (by exact_mod_cast (le_max_right (max (max r0 z0) w0) 1000)) hn_max) (hE_gt p hp)
        have h1 : (1 : ℝ) / (p : ℝ) ≤ 0.001 := by rw [div_le_iff₀ (by linarith)]; linarith
        linarith
      calc (0.99 : ℝ) ≤ (0.999 : ℝ) ^ (9 : ℕ) := by norm_num
        _ ≤ (0.999 : ℝ) ^ E.card := pow_le_pow_of_le_one (by norm_num) (by norm_num) hE_card
        _ = ∏ _p ∈ E, (0.999 : ℝ) := (Finset.prod_const _).symm
        _ ≤ ∏ p ∈ E, (1 - (1 : ℝ) / (p : ℝ)) := Finset.prod_le_prod (fun _ _ => by norm_num) hterm
    nlinarith
  have htau_pos : 0 < tau := lt_of_lt_of_le (by positivity) htau_ge_Vz
  -- Disjoint union decomposition lemma for Y_set U
  have hY_decomp : ∀ U : ℝ,
      (((Finset.Ico x (2 * x)).filter (fun m => ∃ u q : ℕ,
        m = q * u ∧ u ∣ n ∧ (u : ℝ) ≤ U ∧ ∀ p ∈ S, ¬ p ∣ q)).card : ℝ) =
      ∑ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ U),
        (((Finset.Ico ⌈(x : ℝ) / (u : ℝ)⌉₊ ⌈2 * ((x : ℝ) / (u : ℝ))⌉₊).filter
          (fun q => ∀ p ∈ S, ¬ p ∣ q)).card : ℝ) := by
    intro U
    let D_U := n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ U)
    let Q_u (u : ℕ) := (Finset.Ico ⌈(x : ℝ) / (u : ℝ)⌉₊ ⌈2 * ((x : ℝ) / (u : ℝ))⌉₊).filter
      (fun q => ∀ p ∈ S, ¬ p ∣ q)
    have hbiU : (Finset.Ico x (2 * x)).filter (fun m => ∃ u q : ℕ,
        m = q * u ∧ u ∣ n ∧ (u : ℝ) ≤ U ∧ ∀ p ∈ S, ¬ p ∣ q) =
        D_U.biUnion (fun u => (Q_u u).image (fun q => q * u)) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_biUnion, Finset.mem_image,
        D_U, Q_u, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hxm, hm2x⟩, u, q, rfl, hudvd, huU, hqS⟩
        have hu_pos : 0 < u := Nat.pos_of_dvd_of_pos hudvd (by omega)
        have hu_r : (0 : ℝ) < u := by exact_mod_cast hu_pos
        refine ⟨u, ⟨⟨hudvd, by omega⟩, huU⟩, q, ⟨⟨?_, ?_⟩, hqS⟩, rfl⟩
        · rw [Nat.ceil_le, div_le_iff₀ hu_r]; exact_mod_cast hxm
        · rw [Nat.lt_ceil, show 2 * ((x : ℝ) / (u : ℝ)) = (2 * (x : ℝ)) / (u : ℝ) by ring, lt_div_iff₀ hu_r]
          exact_mod_cast hm2x
      · rintro ⟨u, ⟨⟨hudvd, _⟩, huU⟩, q, ⟨⟨hq1, hq2⟩, hqS⟩, rfl⟩
        have hu_pos : 0 < u := Nat.pos_of_dvd_of_pos hudvd (by omega)
        have hu_r : (0 : ℝ) < u := by exact_mod_cast hu_pos
        have h1 : (x : ℝ) / (u : ℝ) ≤ (q : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hq1)
        have h2 : (q : ℝ) < 2 * ((x : ℝ) / (u : ℝ)) := Nat.lt_ceil.mp hq2
        have hxqu : (x : ℝ) ≤ ((q * u : ℕ) : ℝ) := by
          push_cast; exact (div_le_iff₀ hu_r).mp h1
        have hqu2x : ((q * u : ℕ) : ℝ) < ((2 * x : ℕ) : ℝ) := by
          push_cast
          have := (lt_div_iff₀ hu_r).mp (by rwa [show 2 * ((x : ℝ) / (u : ℝ)) = (2 * (x : ℝ)) / (u : ℝ) by ring] at h2)
          linarith
        exact ⟨⟨by exact_mod_cast hxqu, by exact_mod_cast hqu2x⟩, u, q, rfl, hudvd, huU, hqS⟩
    have hpw : (D_U : Set ℕ).PairwiseDisjoint (fun u => (Q_u u).image (fun q => q * u)) := by
      intro u1 hu1 u2 hu2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro m hm1 hm2
      obtain ⟨q1, hq1, rfl⟩ := Finset.mem_image.mp hm1
      obtain ⟨q2, hq2, heq⟩ := Finset.mem_image.mp hm2
      have hu1_dvd : u1 ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hu1).1).1
      have hu2_dvd : u2 ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hu2).1).1
      have hq1S := (Finset.mem_filter.mp hq1).2
      have hq2S := (Finset.mem_filter.mp hq2).2
      have hcop12 : Nat.Coprime u1 q2 := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne1
        set p := (Nat.gcd u1 q2).minFac
        have hp_pr : p.Prime := Nat.minFac_prime hne1
        have hp_u1 : p ∣ u1 := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
        have hp_q2 : p ∣ q2 := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
        have hp_S : p ∈ S := Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp_pr, hp_u1.trans hu1_dvd, by omega⟩)
        exact hq2S p hp_S hp_q2
      have hcop21 : Nat.Coprime u2 q1 := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne1
        set p := (Nat.gcd u2 q1).minFac
        have hp_pr : p.Prime := Nat.minFac_prime hne1
        have hp_u2 : p ∣ u2 := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
        have hp_q1 : p ∣ q1 := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
        have hp_S : p ∈ S := Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp_pr, hp_u2.trans hu2_dvd, by omega⟩)
        exact hq1S p hp_S hp_q1
      have hdvd12 : u1 ∣ u2 := hcop12.dvd_of_dvd_mul_left ⟨q1, by linarith⟩
      have hdvd21 : u2 ∣ u1 := hcop21.dvd_of_dvd_mul_left ⟨q2, by linarith⟩
      exact hne (Nat.dvd_antisymm hdvd12 hdvd21)
    rw [hbiU, Finset.card_biUnion hpw, Nat.cast_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu_pos : 0 < u := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (Finset.mem_filter.mp hu).1).1 (by omega)
    rw [Finset.card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_right hu_pos hab)]
  have hVz_ge : 1 / (3 * Real.log (z : ℝ)) ≤ Vz := by
    dsimp [Vz]; rw [hPr_eq]; exact h_V_ge z (by omega)
  have hVz_le : Vz ≤ 1 / Real.log (z : ℝ) := by
    dsimp [Vz]; rw [hPr_eq]; exact h_V_le z (by omega)
  constructor
  · -- PART A: UPPER BOUND
    rw [hY_decomp ((n : ℝ) ^ (1 / 16 : ℝ))]
    have hterm_up : ∀ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ)),
        (((Finset.Ico ⌈(x : ℝ) / (u : ℝ)⌉₊ ⌈2 * ((x : ℝ) / (u : ℝ))⌉₊).filter
          (fun q => ∀ p ∈ S, ¬ p ∣ q)).card : ℝ) ≤ 8 * tau * ((x : ℝ) / (u : ℝ)) := by
      intro u hu
      have hu_dvd : u ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hu).1).1
      have hu_pos : 0 < u := Nat.pos_of_dvd_of_pos hu_dvd (by omega)
      have hu_r : (0 : ℝ) < u := by exact_mod_cast hu_pos
      have hu_le : (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) := (Finset.mem_filter.mp hu).2
      set X : ℝ := (x : ℝ) / (u : ℝ)
      have hX_ge_n316 : (n : ℝ) ^ (3 / 16 : ℝ) ≤ X := by
        dsimp [X]; rw [le_div_iff₀ hu_r]
        have hmul : (n : ℝ) ^ (3 / 16 : ℝ) * (n : ℝ) ^ (1 / 16 : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < n))]; norm_num
        calc (n : ℝ) ^ (3 / 16 : ℝ) * (u : ℝ)
            ≤ (n : ℝ) ^ (3 / 16 : ℝ) * (n : ℝ) ^ (1 / 16 : ℝ) :=
              mul_le_mul_of_nonneg_left hu_le (by positivity)
          _ = (n : ℝ) ^ (1 / 4 : ℝ) := hmul
          _ ≤ (x : ℝ) := hx_lo
      have ⟨hX10000, hlogX20, hloglogX, hXdivlog2⟩ := hX0 X (hn_X0.trans hX_ge_n316)
      have hX_pos : 0 < X := by linarith
      have hdrop : ((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => ∀ p ∈ S, ¬ p ∣ q)).card ≤
          (siftedDyad4 X z).card := by
        refine Finset.card_le_card fun q hq => ?_
        rw [Finset.mem_filter] at hq
        rw [mem_siftedDyad4_iff]
        refine ⟨hq.1, fun p hp => hq.2 p (Finset.mem_union_right _ (hPr_eq ▸ hp))⟩
      by_cases hsmall : 2 * X ≤ (z : ℝ)
      · have hempty : siftedDyad4 X z = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro q hq
          rw [mem_siftedDyad4_iff, Finset.mem_Ico] at hq
          have hq_ge : X ≤ (q : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hq.1.1)
          have hq_lt : (q : ℝ) < 2 * X := Nat.lt_ceil.mp hq.1.2
          have hq2 : 2 ≤ q := by
            have : (2 : ℝ) ≤ (q : ℝ) := by linarith
            exact_mod_cast this
          have hqz : q ≤ z := by
            have : (q : ℝ) ≤ (z : ℝ) := by linarith
            exact_mod_cast this
          have hmf_pr : q.minFac.Prime := Nat.minFac_prime (by omega)
          have hmf_le : q.minFac ≤ z := (Nat.minFac_le (by omega)).trans hqz
          exact hq.2 q.minFac (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmf_pr.one_le, hmf_le⟩, hmf_pr⟩)
            (Nat.minFac_dvd q)
        rw [hempty, Finset.card_empty] at hdrop
        have h0 : ((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => ∀ p ∈ S, ¬ p ∣ q)).card = 0 := Nat.eq_zero_of_le_zero hdrop
        rw [h0]; simp only [Nat.cast_zero]; positivity
      · push Not at hsmall
        set w : ℝ := min ((z : ℝ) ^ 2) (X / (Real.log X) ^ 2)
        have hw4 : 4 ≤ w := by
          dsimp [w]; apply le_min
          · have : (1000 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1000
            nlinarith
          · linarith
        have hsqw_le_z : Real.sqrt w ≤ (z : ℝ) := by
          rw [Real.sqrt_le_iff]
          exact ⟨Nat.cast_nonneg z, min_le_left _ _⟩
        have ha1 : 1 ≤ ⌈X⌉₊ := by
          have : (1 : ℝ) ≤ (⌈X⌉₊ : ℝ) := (by linarith : (1 : ℝ) ≤ X).trans (Nat.le_ceil X)
          exact_mod_cast this
        have hab : ⌈X⌉₊ ≤ ⌈2 * X⌉₊ := Nat.ceil_mono (by linarith)
        have hsub_sel : siftedDyad4 X z ⊆
            (Finset.Ioc (⌈X⌉₊ - 1) (⌈2 * X⌉₊ - 1)).filter
              (fun q => ∀ p ∈ (Finset.Icc 1 ⌊Real.sqrt w⌋₊).filter Nat.Prime, ¬ p ∣ q) := by
          intro q hq
          rw [mem_siftedDyad4_iff] at hq
          rw [@Finset.mem_filter _ _ (Classical.decPred _), ← Ico_eq_Ioc_pred ha1 hab]
          refine ⟨hq.1, fun p hp => hq.2 p ?_⟩
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          have hpz : p ≤ z := by
            have : (p : ℝ) ≤ (z : ℝ) :=
              (by exact_mod_cast hp.1.2 : (p : ℝ) ≤ (⌊Real.sqrt w⌋₊ : ℝ)).trans
                ((Nat.floor_le (Real.sqrt_nonneg w)).trans hsqw_le_z)
            exact_mod_cast this
          exact ⟨⟨hp.1.1, hpz⟩, hp.2⟩
        have hsel := h_selberg (Nat.sub_le_sub_right hab 1) hw4
        have hlen_le : (((⌈2 * X⌉₊ - 1) - (⌈X⌉₊ - 1) : ℕ) : ℝ) ≤ 1.001 * X := by
          have heq : (⌈2 * X⌉₊ - 1) - (⌈X⌉₊ - 1) = ⌈2 * X⌉₊ - ⌈X⌉₊ := by omega
          rw [heq, Nat.cast_sub hab]
          have h1 := Nat.ceil_lt_add_one (show 0 ≤ 2 * X by linarith)
          have h2 := Nat.le_ceil X
          linarith
        have hlogw_ge : 0.48 * Real.log (z : ℝ) ≤ Real.log (Real.sqrt w) := by
          rw [Real.log_sqrt (by linarith)]
          have hlog_min : Real.log w = min (2 * Real.log (z : ℝ)) (Real.log X - 2 * Real.log (Real.log X)) := by
            dsimp [w]
            rcases le_total ((z : ℝ) ^ 2) (X / (Real.log X) ^ 2) with hle | hge
            · rw [min_eq_left hle, Real.log_pow]; push_cast
              have hle_log := Real.log_le_log (by positivity) hle
              rw [Real.log_pow, Real.log_div hX_pos.ne' (by positivity), Real.log_pow] at hle_log
              push_cast at hle_log
              rw [min_eq_left hle_log]
            · rw [min_eq_right hge, Real.log_div hX_pos.ne' (by positivity), Real.log_pow]; push_cast
              have hge_log := Real.log_le_log (by positivity) hge
              rw [Real.log_pow, Real.log_div hX_pos.ne' (by positivity), Real.log_pow] at hge_log
              push_cast at hge_log
              rw [min_eq_right hge_log]
          rw [hlog_min]
          apply le_div_iff₀ (by norm_num : (0 : ℝ) < 2) |>.mpr
          apply le_min
          · linarith
          · have hlogz_lt : Real.log (z : ℝ) ≤ Real.log X + Real.log 2 := by
              have h := Real.log_le_log (by exact_mod_cast (by omega : 0 < z)) hsmall.le
              rwa [Real.log_mul (by norm_num) hX_pos.ne', add_comm] at h
            have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            linarith
        have hw_le_err : w ≤ 0.1 * X / Real.log (z : ℝ) := by
          have hw_le2 : w ≤ X / (Real.log X) ^ 2 := min_le_right _ _
          have hlogz_le2 : Real.log (z : ℝ) ≤ 2 * Real.log X := by
            have h := Real.log_le_log (by exact_mod_cast (by omega : 0 < z)) hsmall.le
            rw [Real.log_mul (by norm_num) hX_pos.ne'] at h
            have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
            linarith
          have h1 : X / (Real.log X) ^ 2 ≤ 0.1 * X / Real.log (z : ℝ) := by
            rw [div_le_div_iff₀ (sq_pos_of_pos (by linarith)) hlogz_pos]
            have h1' : Real.log (z : ℝ) ≤ 0.1 * (Real.log X) ^ 2 := by nlinarith
            nlinarith
          exact hw_le2.trans h1
        have hcard_sel : ((siftedDyad4 X z).card : ℝ) ≤ 2.2 * X / Real.log (z : ℝ) := by
          have hsub_r : ((siftedDyad4 X z).card : ℝ) ≤
              (((Finset.Ioc (⌈X⌉₊ - 1) (⌈2 * X⌉₊ - 1)).filter
                (fun q => ∀ p ∈ (Finset.Icc 1 ⌊Real.sqrt w⌋₊).filter Nat.Prime, ¬ p ∣ q)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub_sel
          have h1 : ((siftedDyad4 X z).card : ℝ) ≤
              (((⌈2 * X⌉₊ - 1) - (⌈X⌉₊ - 1) : ℕ) : ℝ) / Real.log (Real.sqrt w) + w :=
            hsub_r.trans hsel
          have h2 : (((⌈2 * X⌉₊ - 1) - (⌈X⌉₊ - 1) : ℕ) : ℝ) / Real.log (Real.sqrt w) ≤
              (1.001 * X) / (0.48 * Real.log (z : ℝ)) :=
            div_le_div₀ (by positivity) hlen_le (by positivity) hlogw_ge
          have h3 : (1.001 * X) / (0.48 * Real.log (z : ℝ)) + 0.1 * X / Real.log (z : ℝ) ≤
              2.2 * X / Real.log (z : ℝ) := by
            rw [show (1.001 * X) / (0.48 * Real.log (z : ℝ)) = (1.001 / 0.48) * (X / Real.log (z : ℝ)) by ring,
              show 0.1 * X / Real.log (z : ℝ) = 0.1 * (X / Real.log (z : ℝ)) by ring,
              show 2.2 * X / Real.log (z : ℝ) = 2.2 * (X / Real.log (z : ℝ)) by ring]
            have hnn : 0 ≤ X / Real.log (z : ℝ) := by positivity
            nlinarith
          linarith
        have htau_big : 2.2 / Real.log (z : ℝ) ≤ 8 * tau := by
          have h1 : 8 * 0.99 * (1 / (3 * Real.log (z : ℝ))) ≤ 8 * tau := by nlinarith
          have h2 : 8 * 0.99 * (1 / (3 * Real.log (z : ℝ))) = (7.92 / 3) / Real.log (z : ℝ) := by ring
          have h3 : (2.2 : ℝ) / Real.log (z : ℝ) ≤ (7.92 / 3) / Real.log (z : ℝ) :=
            div_le_div_of_nonneg_right (by norm_num) hlogz_pos.le
          linarith
        have hmul_tau : 2.2 * X / Real.log (z : ℝ) ≤ 8 * tau * X := by
          rw [show 2.2 * X / Real.log (z : ℝ) = (2.2 / Real.log (z : ℝ)) * X by ring]
          exact mul_le_mul_of_nonneg_right htau_big hX_pos.le
        have hdrop_r : (((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => ∀ p ∈ S, ¬ p ∣ q)).card : ℝ) ≤
            ((siftedDyad4 X z).card : ℝ) := by exact_mod_cast hdrop
        exact (hdrop_r.trans hcard_sel).trans hmul_tau
    calc ∑ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ)),
            (((Finset.Ico ⌈(x : ℝ) / (u : ℝ)⌉₊ ⌈2 * ((x : ℝ) / (u : ℝ))⌉₊).filter
              (fun q => ∀ p ∈ S, ¬ p ∣ q)).card : ℝ)
        ≤ ∑ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ)),
            8 * tau * ((x : ℝ) / (u : ℝ)) := Finset.sum_le_sum hterm_up
      _ = (8 * tau * (x : ℝ)) *
            ∑ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ)), (1 : ℝ) / (u : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => by ring
      _ ≤ (8 * tau * (x : ℝ)) * ∑ u ∈ n.divisors, (1 : ℝ) / (u : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)) (by positivity)
      _ ≤ (8 * tau * (x : ℝ)) * ((n : ℝ) / (n.totient : ℝ)) :=
          mul_le_mul_of_nonneg_left (h_div_le (by omega)) (by positivity)
      _ = 8 * ((n : ℝ) / (n.totient : ℝ)) * tau * (x : ℝ) := by ring
  · -- PART B: LOWER BOUND
    intro hr2x
    rw [hY_decomp ((x : ℝ) ^ (1 / 16 : ℝ))]
    have hterm_lo : ∀ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ (x : ℝ) ^ (1 / 16 : ℝ)),
        0.23 * tau * ((x : ℝ) / (u : ℝ)) ≤
          (((Finset.Ico ⌈(x : ℝ) / (u : ℝ)⌉₊ ⌈2 * ((x : ℝ) / (u : ℝ))⌉₊).filter
            (fun q => ∀ p ∈ S, ¬ p ∣ q)).card : ℝ) := by
      intro u hu
      have hu_dvd : u ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hu).1).1
      have hu_pos : 0 < u := Nat.pos_of_dvd_of_pos hu_dvd (by omega)
      have hu_r : (0 : ℝ) < u := by exact_mod_cast hu_pos
      have hu_le : (u : ℝ) ≤ (x : ℝ) ^ (1 / 16 : ℝ) := (Finset.mem_filter.mp hu).2
      set X : ℝ := (x : ℝ) / (u : ℝ)
      have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hx_lo
      have hX_ge_x1516 : (x : ℝ) ^ (15 / 16 : ℝ) ≤ X := by
        dsimp [X]; rw [le_div_iff₀ hu_r]
        have hmul : (x : ℝ) ^ (15 / 16 : ℝ) * (x : ℝ) ^ (1 / 16 : ℝ) = (x : ℝ) := by
          rw [← Real.rpow_add hx_pos]; norm_num
        calc (x : ℝ) ^ (15 / 16 : ℝ) * (u : ℝ)
            ≤ (x : ℝ) ^ (15 / 16 : ℝ) * (x : ℝ) ^ (1 / 16 : ℝ) :=
              mul_le_mul_of_nonneg_left hu_le (by positivity)
          _ = (x : ℝ) := hmul
      have hX_ge_r158 : (r : ℝ) ^ (15 / 8 : ℝ) ≤ X := by
        have hr2_r : (r : ℝ) ^ (2 : ℝ) ≤ (x : ℝ) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact_mod_cast hr2x
        calc (r : ℝ) ^ (15 / 8 : ℝ) = ((r : ℝ) ^ (2 : ℝ)) ^ (15 / 16 : ℝ) := by
              rw [← Real.rpow_mul (Nat.cast_nonneg r)]; norm_num
          _ ≤ (x : ℝ) ^ (15 / 16 : ℝ) := Real.rpow_le_rpow (by positivity) hr2_r (by norm_num)
          _ ≤ X := hX_ge_x1516
      have hX_ge_n316 : (n : ℝ) ^ (3 / 16 : ℝ) ≤ X := by
        calc (n : ℝ) ^ (3 / 16 : ℝ) = ((n : ℝ) ^ (1 / 10 : ℝ)) ^ (15 / 8 : ℝ) := by
              rw [← Real.rpow_mul (Nat.cast_nonneg n)]; norm_num
          _ ≤ (r : ℝ) ^ (15 / 8 : ℝ) := Real.rpow_le_rpow (by positivity) hr_lo (by norm_num)
          _ ≤ X := hX_ge_r158
      have ⟨hX10000, _, _, _⟩ := hX0 X (hn_X0.trans hX_ge_n316)
      have hX_pos : 0 < X := by linarith
      have hz_lt_X : (z : ℝ) < X := by
        have hr_R0 : R0 ≤ (r : ℝ) := hn_R0.trans hr_lo
        exact (hz_le_4rlog.trans_lt (hR0 (r : ℝ) hr_R0)).trans_le hX_ge_r158
      -- Remove multiples of E from siftedDyad4 X z
      have hdiff_sub : siftedDyad4 X z ⊆
          ((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => ∀ p ∈ S, ¬ p ∣ q)) ∪
            E.biUnion (fun p => (Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => p ∣ q)) := by
        intro q hq
        rw [mem_siftedDyad4_iff] at hq
        by_cases hE : ∀ p ∈ E, ¬ p ∣ q
        · apply Finset.mem_union_left
          refine Finset.mem_filter.mpr ⟨hq.1, fun p hp => ?_⟩
          rw [hS_eq] at hp
          rcases Finset.mem_union.mp hp with hpP | hpE
          · exact hq.2 p (hPr_eq ▸ hpP)
          · exact hE p hpE
        · apply Finset.mem_union_right
          push Not at hE
          obtain ⟨p, hpE, hpdvd⟩ := hE
          exact Finset.mem_biUnion.mpr ⟨p, hpE, Finset.mem_filter.mpr ⟨hq.1, hpdvd⟩⟩
      have hE_loss : (∑ p ∈ E, (((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => p ∣ q)).card : ℝ)) ≤
          0.005 * X * Vz := by
        have hlen : ((⌈2 * X⌉₊ - ⌈X⌉₊ : ℕ) : ℝ) ≤ 2 * X := by
          have hab : ⌈X⌉₊ ≤ ⌈2 * X⌉₊ := Nat.ceil_mono (by linarith)
          rw [Nat.cast_sub hab]
          linarith [Nat.ceil_lt_add_one (show 0 ≤ 2 * X by linarith), Nat.le_ceil X]
        have hterm_E : ∀ p ∈ E,
            (((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => p ∣ q)).card : ℝ) ≤
              X * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) := by
          intro p hp
          have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
          have hle := card_Ico_filter_dvd_le ⌈X⌉₊ ⌈2 * X⌉₊ p hp_pr.one_le
          have hp_gt := hE_gt p hp
          have h1' : ((⌈2 * X⌉₊ - ⌈X⌉₊ : ℕ) : ℝ) / (p : ℝ) ≤ X / (n : ℝ) ^ (1 / 10 : ℝ) + 1 := by
            have hab : ⌈X⌉₊ ≤ ⌈2 * X⌉₊ := Nat.ceil_mono (by linarith)
            have hX1 : ((⌈2 * X⌉₊ - ⌈X⌉₊ : ℕ) : ℝ) ≤ X + 1 := by
              rw [Nat.cast_sub hab]
              linarith [Nat.ceil_lt_add_one (show 0 ≤ 2 * X by linarith), Nat.le_ceil X]
            have hdiv1 : ((⌈2 * X⌉₊ - ⌈X⌉₊ : ℕ) : ℝ) / (p : ℝ) ≤ (X + 1) / (n : ℝ) ^ (1 / 10 : ℝ) :=
              div_le_div₀ (by positivity) hX1 (by positivity) hp_gt.le
            have h1_p : 1 / (n : ℝ) ^ (1 / 10 : ℝ) ≤ 1 := by
              rw [div_le_one (by positivity)]; linarith
            rw [add_div] at hdiv1; linarith
          have h3_le : (3 : ℝ) ≤ X * (4 / (n : ℝ) ^ (3 / 16 : ℝ)) := by
            rw [mul_div_assoc', le_div_iff₀ (by positivity)]
            linarith
          have hrew : X * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) =
              X / (n : ℝ) ^ (1 / 10 : ℝ) + X * (4 / (n : ℝ) ^ (3 / 16 : ℝ)) := by ring
          linarith
        have hsum_E : ∑ p ∈ E, (((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => p ∣ q)).card : ℝ) ≤
            9 * X * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) := by
          calc _ ≤ ∑ _p ∈ E, X * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) := Finset.sum_le_sum hterm_E
            _ = (E.card : ℝ) * (X * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ))) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 9 * (X * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ))) := by
                have hE9 : (E.card : ℝ) ≤ 9 := by exact_mod_cast hE_card
                exact mul_le_mul_of_nonneg_right hE9 (by positivity)
            _ = _ := by ring
        have hlogz_le : Real.log (z : ℝ) ≤ Real.log (4 * (n : ℝ) * Real.log (n : ℝ)) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < z)) hz_le_4nlog
        have h9_le : 9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) ≤ 0.005 * Vz := by
          have h1 : 9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) * (3 * Real.log (z : ℝ)) ≤ 0.005 := by
            calc _ ≤ 9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) *
                    (3 * Real.log (4 * (n : ℝ) * Real.log (n : ℝ))) := by
                  gcongr
              _ ≤ 0.005 := hn_Eerr
          have h2 : 9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) ≤ 0.005 / (3 * Real.log (z : ℝ)) := by
            rw [le_div_iff₀ (by positivity)]; exact h1
          have h3 : 0.005 / (3 * Real.log (z : ℝ)) = 0.005 * (1 / (3 * Real.log (z : ℝ))) := by ring
          nlinarith
        calc _ ≤ 9 * X * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ)) := hsum_E
          _ = X * (9 * (1 / (n : ℝ) ^ (1 / 10 : ℝ) + 4 / (n : ℝ) ^ (3 / 16 : ℝ))) := by ring
          _ ≤ X * (0.005 * Vz) := mul_le_mul_of_nonneg_left h9_le hX_pos.le
          _ = 0.005 * X * Vz := by ring
      have hcard_sub : ((siftedDyad4 X z).card : ℝ) -
          ∑ p ∈ E, (((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => p ∣ q)).card : ℝ) ≤
          (((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => ∀ p ∈ S, ¬ p ∣ q)).card : ℝ) := by
        have h1 : (siftedDyad4 X z).card ≤
            ((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => ∀ p ∈ S, ¬ p ∣ q)).card +
              ∑ p ∈ E, ((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => p ∣ q)).card := by
          calc (siftedDyad4 X z).card
              ≤ (((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => ∀ p ∈ S, ¬ p ∣ q)) ∪
                  E.biUnion (fun p => (Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => p ∣ q))).card :=
                Finset.card_le_card hdiff_sub
            _ ≤ ((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => ∀ p ∈ S, ¬ p ∣ q)).card +
                  (E.biUnion (fun p => (Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => p ∣ q))).card :=
                Finset.card_union_le _ _
            _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _
        have h1r : ((siftedDyad4 X z).card : ℝ) ≤
            (((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => ∀ p ∈ S, ¬ p ∣ q)).card : ℝ) +
              ∑ p ∈ E, (((Finset.Ico ⌈X⌉₊ ⌈2 * X⌉₊).filter (fun q => p ∣ q)).card : ℝ) := by
          rw [← Nat.cast_sum, ← Nat.cast_add]; exact_mod_cast h1
        linarith
      -- Lower bound (siftedDyad4 X z).card ≥ 0.24 * X * Vz (splitting at X ≤ z^101 vs X > z^101)
      have hsifted_lb : 0.24 * X * Vz ≤ ((siftedDyad4 X z).card : ℝ) := by
        by_cases hX_le : X ≤ (z : ℝ) ^ (101 : ℕ)
        · have hb := hbuch 101 (by decide) (by decide) z hz_w0 X hz_lt_X hX_le
          have h1 : 0.24 * X * Vz ≤ 0.24 * X / Real.log (z : ℝ) := by
            rw [show 0.24 * X / Real.log (z : ℝ) = 0.24 * X * (1 / Real.log (z : ℝ)) by ring]
            exact mul_le_mul_of_nonneg_left hVz_le (by positivity)
          exact h1.trans hb
        · push Not at hX_le
          have ha1 : 1 ≤ ⌈X⌉₊ := by
            have : (1 : ℝ) ≤ (⌈X⌉₊ : ℝ) := (by linarith : (1 : ℝ) ≤ X).trans (Nat.le_ceil X)
            exact_mod_cast this
          have hab : ⌈X⌉₊ ≤ ⌈2 * X⌉₊ := Nat.ceil_mono (by linarith)
          have hlen_ge : (z : ℝ) ^ 100 ≤ (((⌈2 * X⌉₊ - 1) - (⌈X⌉₊ - 1) : ℕ) : ℝ) := by
            have heq : (⌈2 * X⌉₊ - 1) - (⌈X⌉₊ - 1) = ⌈2 * X⌉₊ - ⌈X⌉₊ := by omega
            rw [heq, Nat.cast_sub hab]
            have h1 := Nat.le_ceil (2 * X)
            have h2 := Nat.ceil_lt_add_one hX_pos.le
            have hz100_le : (z : ℝ) ^ 100 + 1 ≤ (z : ℝ) ^ 101 := by
              have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 2 ≤ z)
              have hp : (z : ℝ) ^ 101 = (z : ℝ) ^ 100 * (z : ℝ) := pow_succ _ 100
              have hp1 : (1 : ℝ) ≤ (z : ℝ) ^ 100 := one_le_pow₀ (by linarith)
              nlinarith
            linarith
          have hbr := hz0 z hz_z0 (⌈X⌉₊ - 1) (⌈2 * X⌉₊ - 1) (Nat.sub_le_sub_right hab 1) hlen_ge
          have heq_set : siftedDyad4 X z = (Finset.Ioc (⌈X⌉₊ - 1) (⌈2 * X⌉₊ - 1)).filter
              (fun q => ∀ p ∈ (Finset.Icc 1 z).filter Nat.Prime, ¬ p ∣ q) := by
            unfold siftedDyad4; rw [Ico_eq_Ioc_pred ha1 hab]
          rw [← heq_set, ← hPr_eq] at hbr
          have hlen_ge_X : 0.99 * X ≤ (((⌈2 * X⌉₊ - 1) - (⌈X⌉₊ - 1) : ℕ) : ℝ) := by
            have heq : (⌈2 * X⌉₊ - 1) - (⌈X⌉₊ - 1) = ⌈2 * X⌉₊ - ⌈X⌉₊ := by omega
            rw [heq, Nat.cast_sub hab]
            linarith [Nat.le_ceil (2 * X), Nat.ceil_lt_add_one hX_pos.le]
          have hmul : 0.24 * X * Vz ≤ 0.90 * (((⌈2 * X⌉₊ - 1) - (⌈X⌉₊ - 1) : ℕ) : ℝ) * Vz := by
            nlinarith
          exact hmul.trans hbr
      have htau_le_X : 0.23 * tau * X ≤ 0.235 * X * Vz := by nlinarith
      linarith
    have hU_ge : (n : ℝ) ^ (1 / 64 : ℝ) ≤ (x : ℝ) ^ (1 / 16 : ℝ) := by
      calc (n : ℝ) ^ (1 / 64 : ℝ) = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (1 / 16 : ℝ) := by
            rw [← Real.rpow_mul (Nat.cast_nonneg n)]; norm_num
        _ ≤ (x : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by positivity) hx_lo (by norm_num)
    have hsum_u := hdiv_sm ((x : ℝ) ^ (1 / 16 : ℝ)) hU_ge
    have hsum_lo : (0.23 * tau * (x : ℝ)) *
        ∑ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ (x : ℝ) ^ (1 / 16 : ℝ)), (1 : ℝ) / (u : ℝ) ≤
        ∑ u ∈ n.divisors.filter (fun u : ℕ => (u : ℝ) ≤ (x : ℝ) ^ (1 / 16 : ℝ)),
          (((Finset.Ico ⌈(x : ℝ) / (u : ℝ)⌉₊ ⌈2 * ((x : ℝ) / (u : ℝ))⌉₊).filter
            (fun q => ∀ p ∈ S, ¬ p ∣ q)).card : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun u hu => ?_
      have h := hterm_lo u hu
      have hrew : 0.23 * tau * (x : ℝ) * (1 / (u : ℝ)) = 0.23 * tau * ((x : ℝ) / (u : ℝ)) := by ring
      linarith
    have hfinal : ((n : ℝ) / (n.totient : ℝ)) * tau * (x : ℝ) / 8 ≤
        (0.23 * tau * (x : ℝ)) * ((0.60 : ℝ) * ((n : ℝ) / (n.totient : ℝ))) := by
      have hnn : 0 ≤ ((n : ℝ) / (n.totient : ℝ)) * tau * (x : ℝ) := by positivity
      linarith [show (0.23 * tau * (x : ℝ)) * ((0.60 : ℝ) * ((n : ℝ) / (n.totient : ℝ))) =
        0.138 * (((n : ℝ) / (n.totient : ℝ)) * tau * (x : ℝ)) by ring]
    exact hfinal.trans ((mul_le_mul_of_nonneg_left hsum_u (by positivity)).trans hsum_lo)

end Erdos360H1Part4
end -- Erdos360_H1_part4.lean

theorem OMA.solution : OMA.R_Erdos360_erdos_360_R1_H4_R1.H1 := by
  refine Erdos360H1Part4.main_H1
    Erdos360H1Part1.nth_prime_gt_of_pos
    Erdos360H1Part1.first_primes_eq_filter_Icc
    Erdos360H1Part1.nth_prime_le_four_mul_log
    Erdos360H1Part1.prod_one_sub_inv_le_inv_log
    Erdos360H1Part1.prod_one_sub_inv_ge_inv_three_log
    Erdos360H1Part2.sum_divisors_inv_le
    Erdos360H1Part2.sum_divisors_inv_small_ge
    Erdos360H1Part3a.selberg_interval_upper
    (Erdos360H1Part3b.brun_interval_lower
      Erdos360H1Part1.sum_inv_prime_Ioc_le
      Erdos360H1Part1.prod_one_sub_inv_ge_inv_three_log)
    ?_
  simpa only [Erdos360H1Part4.siftedDyad4, Erdos360H1Part3b.siftedDyad] using
    Erdos360H1Part3b.buchstab_primes_lower
      Erdos360H1Part1.dyadic_primes_lower
      Erdos360H1Part1.sum_inv_prime_log_ge
