import OMAReductions.R_Erdos360_erdos_360_R1_H4_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

-- Reduction Erdos360.erdos_360.R1.H4.R1.H4.R1 of step Erdos360.erdos_360.R1.H4.R1.H4
-- Credit: @KevinBigham

namespace OMA.R_Erdos360_erdos_360_R1_H4_R1_H4_R1

open scoped BigOperators Pointwise

def H1 : Prop :=
  ∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 / 100 ∧
    ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)),
      A.Nonempty →
      (A.card : ℝ) ≤ ξ * (m : ℝ) →
      ((A + A).card : ℝ) ≤ 2.04 * (A.card : ℝ) →
      ∃ H : AddSubgroup (ZMod m), H ≠ ⊤ ∧
        ((∃ (x d : ZMod m) (L : ℕ), 2 ≤ L ∧
            (∀ a ∈ A, ∃ k < L, a - (x + (k : ZMod m) * d) ∈ H) ∧
            ((L - 1 : ℕ) : ℝ) * (Nat.card H : ℝ) ≤ ((A + A).card : ℝ) - (A.card : ℝ)) ∨
         (∃ (c₁ c₂ c₃ : ZMod m),
            (∀ a ∈ A, a - c₁ ∈ H ∨ a - c₂ ∈ H ∨ a - c₃ ∈ H) ∧
            (Nat.card H : ℝ) ≤ ((A + A).card : ℝ) - (A.card : ℝ)) ∨
         (∃ x : ZMod m, ∀ a ∈ A, a - x ∈ H))

def H2 : Prop :=
  ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (k : ℕ),
    1 ≤ k →
    (∀ H : AddSubgroup (ZMod m), H ≠ ⊤ → ¬ ∃ x : ZMod m, ∀ a ∈ A, a - x ∈ H) →
    min (m : ℝ) (((k + 1 : ℕ) : ℝ) * (A.card : ℝ) / 2) ≤
      ((((Fintype.piFinset (fun _ : Fin k => A)).image (fun f => ∑ i : Fin k, f i)).card : ℕ) : ℝ)

section Part1
open Finset Filter Real Nat ArithmeticFunction
open scoped BigOperators Chebyshev Classical

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

/- ### Section 6: Lower Bound on `tau(r, n)` for `r ≥ n^(1/4)` -/

lemma tau_ge_inv_four_log_r :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, (n : ℝ) ^ (1 / 4 : ℝ) ≤ (r : ℝ) → r ≤ n →
      1 / (4 * Real.log (r : ℝ)) ≤
        ∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
          (1 - (1 : ℝ) / (p : ℝ)) := by
  obtain ⟨r0, hr0⟩ := Filter.eventually_atTop.mp nth_prime_le_four_mul_log
  have hlog_r : ∀ᶠ r : ℕ in atTop, 1000 ≤ r ∧ Real.log (4 * (r : ℝ) * Real.log (r : ℝ)) ≤ 1.1 * Real.log (r : ℝ) := by
    have h1 : Tendsto (fun x : ℝ => Real.log (4 * x) / x) atTop (nhds 0) := by
      have ha : Tendsto (fun x : ℝ => Real.log 4 / x) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hb : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := tendsto_log_div_id
      have hsum : Tendsto (fun x : ℝ => Real.log 4 / x + Real.log x / x) atTop (nhds 0) := by
        simpa using ha.add hb
      refine hsum.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.log_mul (by norm_num) hx.ne']; ring
    filter_upwards [(h1.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.1)),
      Filter.eventually_ge_atTop 1000] with r hr hr1000
    refine ⟨hr1000, ?_⟩
    have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
    have hlt := (div_lt_iff₀ hlogr).mp hr
    dsimp only [Function.comp_apply] at hlt
    rw [show 4 * (r : ℝ) * Real.log (r : ℝ) = (r : ℝ) * (4 * Real.log (r : ℝ)) by ring,
      Real.log_mul (by exact_mod_cast (by omega : r ≠ 0)) (by positivity)]
    linarith
  obtain ⟨r1, hr1⟩ := Filter.eventually_atTop.mp hlog_r
  have hp4 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hp4.eventually (Filter.eventually_ge_atTop (max (max r0 r1) 1000 : ℝ)),
    Filter.eventually_ge_atTop 10000] with n hn hn10000
  intro r hr_lo hrn
  have hr_ge : max (max r0 r1) 1000 ≤ r := by
    have : (max (max r0 r1) 1000 : ℝ) ≤ (r : ℝ) := hn.trans hr_lo
    exact_mod_cast this
  have hr1000 : 1000 ≤ r := by omega
  have hr_r0 : r0 ≤ r := by omega
  have hr_r1 : r1 ≤ r := by omega
  set P_r := (Finset.range r).image (Nat.nth Nat.Prime)
  set z := Nat.nth Nat.Prime (r - 1)
  have hz_gt_r : r < z := nth_prime_gt_of_pos (by omega)
  have hPr_eq : P_r = (Finset.Icc 1 z).filter Nat.Prime := first_primes_eq_filter_Icc (by omega)
  have hz_le : (z : ℝ) ≤ 4 * (r : ℝ) * Real.log (r : ℝ) := hr0 r hr_r0
  have hlogz_le : Real.log (z : ℝ) ≤ 1.1 * Real.log (r : ℝ) :=
    (Real.log_le_log (by exact_mod_cast (by omega : 0 < z)) hz_le).trans (hr1 r hr_r1).2
  set E := n.primeFactors \ P_r
  have hS_eq : n.primeFactors ∪ P_r = P_r ∪ E := by
    ext p; simp only [E, Finset.mem_union, Finset.mem_sdiff]; tauto
  have hdisj : Disjoint P_r E := Finset.disjoint_sdiff
  have hE_gt : ∀ p ∈ E, (n : ℝ) ^ (1 / 4 : ℝ) < (p : ℝ) := by
    intro p hp
    have hp_n := (Finset.mem_sdiff.mp hp).1
    have hp_not := (Finset.mem_sdiff.mp hp).2
    have hp_pr := Nat.prime_of_mem_primeFactors hp_n
    have hz_lt_p : z < p := by
      by_contra hle
      exact hp_not (hPr_eq ▸ Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_pr.one_le, by omega⟩, hp_pr⟩)
    have hr_lt_p : (r : ℝ) < (p : ℝ) := by exact_mod_cast (lt_trans hz_gt_r hz_lt_p)
    exact lt_of_le_of_lt hr_lo hr_lt_p
  have hE_card : E.card ≤ 3 := by
    by_contra hge
    have h4 : 4 ≤ E.card := by omega
    have hprod_le : (∏ p ∈ E, (p : ℝ)) ≤ (n : ℝ) := by
      have hdvd1 : ∏ p ∈ E, p ∣ ∏ p ∈ n.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset E n.primeFactors (fun p : ℕ => p) Finset.sdiff_subset
      have hdvd : ∏ p ∈ E, p ∣ n := dvd_trans hdvd1 (Nat.prod_primeFactors_dvd n)
      have hle : ∏ p ∈ E, p ≤ n := Nat.le_of_dvd (by omega) hdvd
      rw [← Nat.cast_prod]; exact_mod_cast hle
    have hprod_gt : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ E.card < ∏ p ∈ E, (p : ℝ) := by
      rw [← Finset.prod_const]
      exact Finset.prod_lt_prod_of_nonempty (fun _ _ => by positivity) hE_gt (Finset.card_pos.mp (by omega))
    have h1_le : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    have h4_le : (n : ℝ) ≤ ((n : ℝ) ^ (1 / 4 : ℝ)) ^ E.card := by
      calc (n : ℝ) = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]; norm_num
        _ ≤ ((n : ℝ) ^ (1 / 4 : ℝ)) ^ E.card := pow_le_pow_right₀ h1_le h4
    linarith
  have hVz_ge : 1 / (3 * Real.log (z : ℝ)) ≤ ∏ p ∈ P_r, (1 - (1 : ℝ) / (p : ℝ)) := by
    rw [hPr_eq]; exact prod_one_sub_inv_ge_inv_three_log z (by omega)
  have hE_ge : (0.99 : ℝ) ≤ ∏ p ∈ E, (1 - (1 : ℝ) / (p : ℝ)) := by
    have hterm : ∀ p ∈ E, (0.999 : ℝ) ≤ 1 - (1 : ℝ) / (p : ℝ) := by
      intro p hp
      have hp1000 : (1000 : ℝ) < (p : ℝ) := by
        have h1 : (1000 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
          le_trans (by exact_mod_cast (le_max_right (max r0 r1) 1000)) hn
        exact lt_of_le_of_lt h1 (hE_gt p hp)
      have h1 : (1 : ℝ) / (p : ℝ) ≤ 0.001 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    calc (0.99 : ℝ) ≤ (0.999 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ (0.999 : ℝ) ^ E.card := pow_le_pow_of_le_one (by norm_num) (by norm_num) hE_card
      _ = ∏ _p ∈ E, (0.999 : ℝ) := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ E, (1 - (1 : ℝ) / (p : ℝ)) := Finset.prod_le_prod (fun _ _ => by norm_num) hterm
  have hlogr_pos : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  rw [hS_eq, Finset.prod_union hdisj]
  calc 1 / (4 * Real.log (r : ℝ))
      ≤ 0.99 / (3.3 * Real.log (r : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    _ ≤ 0.99 * (1 / (3 * Real.log (z : ℝ))) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    _ ≤ (∏ p ∈ P_r, (1 - (1 : ℝ) / (p : ℝ))) * ∏ p ∈ E, (1 - (1 : ℝ) / (p : ℝ)) := by
        rw [mul_comm (0.99 : ℝ)]
        exact mul_le_mul hVz_ge hE_ge (by norm_num) (by
          exact Finset.prod_nonneg fun p hp => by
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp (hPr_eq ▸ hp)).2.two_le
            rw [sub_nonneg, div_le_one (by linarith)]; linarith)

/- ### Section 7: Elementary MGF Chernoff Bound & Diverse Partition (CFP21 Lemma 5.3) -/

private lemma mgf_bucket_sum {Q : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (X : Finset ℕ) (hXQ : X ⊆ Q)
    (j : Fin M) (lam : ℝ) :
    ∑ f : (Q → Fin M), Real.exp (lam * (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ)) =
      ((M : ℝ) ^ (Q.card - X.card)) * ((M : ℝ) - 1 + Real.exp lam) ^ X.card := by
  have hrew : ∀ f : (Q → Fin M),
      Real.exp (lam * (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ)) =
        ∏ x : Q, if x.1 ∈ X ∧ f x = j then Real.exp lam else 1 := by
    intro f
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, ← Real.exp_nat_mul]
    congr 1; ring
  simp_rw [hrew]
  have hps := Fintype.prod_sum (fun (x : Q) (c : Fin M) => if x.1 ∈ X ∧ c = j then Real.exp lam else (1 : ℝ))
  rw [← hps]
  have hinner : ∀ x : Q,
      (∑ c : Fin M, if x.1 ∈ X ∧ c = j then Real.exp lam else (1 : ℝ)) =
        if x.1 ∈ X then ((M : ℝ) - 1 + Real.exp lam) else (M : ℝ) := by
    intro x
    by_cases hx : x.1 ∈ X
    · simp only [hx, true_and, ↓reduceIte]
      have hsplit : (∑ c : Fin M, if c = j then Real.exp lam else (1 : ℝ)) =
          (∑ c ∈ Finset.univ.filter (fun c : Fin M => c = j), Real.exp lam) +
          (∑ c ∈ Finset.univ.filter (fun c : Fin M => ¬ c = j), (1 : ℝ)) := by
        rw [Finset.sum_ite]
      rw [hsplit]
      have h1 : (Finset.univ.filter (fun c : Fin M => c = j)).card = 1 := by
        rw [Finset.filter_eq', if_pos (Finset.mem_univ j), Finset.card_singleton]
      have h2 : (Finset.univ.filter (fun c : Fin M => ¬ c = j)).card = M - 1 := by
        have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin M))) (p := fun c => c = j)
        rw [h1, Finset.card_univ, Fintype.card_fin] at htot
        omega
      rw [Finset.sum_const, h1, nsmul_eq_mul, Nat.cast_one, one_mul, Finset.sum_const, h2, nsmul_eq_mul, mul_one,
        Nat.cast_sub hM, Nat.cast_one]
      ring
    · simp only [hx, false_and, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
  simp_rw [hinner]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hcardX : (Finset.univ.filter (fun x : Q => x.1 ∈ X)).card = X.card := by
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x1 _ x2 _ h; exact Subtype.ext h
    · intro a ha; exact ⟨⟨a, hXQ ha⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
  have hcardNX : (Finset.univ.filter (fun x : Q => ¬ x.1 ∈ X)).card = Q.card - X.card := by
    have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Q)) (p := fun x => x.1 ∈ X)
    rw [hcardX, Finset.card_univ, Fintype.card_coe] at htot
    omega
  rw [hcardX, hcardNX, mul_comm]

private lemma chernoff_bucket_lower {Q : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (X : Finset ℕ) (hXQ : X ⊆ Q)
    (j : Fin M) :
    ((Finset.univ.filter (fun f : Q → Fin M =>
      (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ) ≤
        (5 / 6 : ℝ) * ((X.card : ℝ) / (M : ℝ)))).card : ℝ) ≤
      ((M : ℝ) ^ Q.card) * Real.exp (-(1 / 252 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
  set Bad := Finset.univ.filter (fun f : Q → Fin M =>
    (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ) ≤
      (5 / 6 : ℝ) * ((X.card : ℝ) / (M : ℝ)))
  set lam : ℝ := -(1 / 6 : ℝ)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hmarkov : (Bad.card : ℝ) * Real.exp (-(5 / 36 : ℝ) * ((X.card : ℝ) / (M : ℝ))) ≤
      ∑ f : (Q → Fin M), Real.exp (lam * (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ)) := by
    calc (Bad.card : ℝ) * Real.exp (-(5 / 36 : ℝ) * ((X.card : ℝ) / (M : ℝ)))
        = ∑ _f ∈ Bad, Real.exp (-(5 / 36 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ f ∈ Bad, Real.exp (lam * (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun f hf => Real.exp_le_exp.mpr ?_
          have hle := (Finset.mem_filter.mp hf).2
          dsimp only [lam] at hle ⊢; linarith
      _ ≤ ∑ f : (Q → Fin M), Real.exp (lam * (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ)) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le
  rw [mgf_bucket_sum hM X hXQ j lam] at hmarkov
  have hexp_le : Real.exp lam ≤ 6 / 7 := by
    dsimp [lam]; rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have h := Real.add_one_le_exp (1 / 6 : ℝ)
    linarith [show (6 / 7 : ℝ)⁻¹ = 7 / 6 by norm_num]
  have hbase_le : (M : ℝ) - 1 + Real.exp lam ≤ (M : ℝ) * Real.exp (-(1 / 7 : ℝ) / (M : ℝ)) := by
    have h1 : (M : ℝ) - 1 + Real.exp lam ≤ (M : ℝ) * (1 - (1 / 7 : ℝ) / (M : ℝ)) := by
      have hrew : (M : ℝ) * (1 - (1 / 7 : ℝ) / (M : ℝ)) = (M : ℝ) - 1 / 7 := by
        field_simp [hMpos.ne']
      linarith
    have h2 : 1 - (1 / 7 : ℝ) / (M : ℝ) ≤ Real.exp (-(1 / 7 : ℝ) / (M : ℝ)) := by
      simpa [sub_eq_add_neg, add_comm, neg_div] using Real.add_one_le_exp (-(1 / 7 : ℝ) / (M : ℝ))
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hMpos.le)
  have hbase_nn : 0 ≤ (M : ℝ) - 1 + Real.exp lam := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith [Real.exp_pos lam]
  have hpow_le : ((M : ℝ) - 1 + Real.exp lam) ^ X.card ≤
      ((M : ℝ) ^ X.card) * Real.exp (-(1 / 7 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
    calc ((M : ℝ) - 1 + Real.exp lam) ^ X.card
        ≤ ((M : ℝ) * Real.exp (-(1 / 7 : ℝ) / (M : ℝ))) ^ X.card := pow_le_pow_left₀ hbase_nn hbase_le _
      _ = ((M : ℝ) ^ X.card) * (Real.exp (-(1 / 7 : ℝ) / (M : ℝ))) ^ X.card := mul_pow _ _ _
      _ = ((M : ℝ) ^ X.card) * Real.exp (-(1 / 7 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
          rw [← Real.exp_nat_mul]; congr 2; ring
  have hMpow : (M : ℝ) ^ (Q.card - X.card) * (M : ℝ) ^ X.card = (M : ℝ) ^ Q.card := by
    rw [← pow_add, Nat.sub_add_cancel (Finset.card_le_card hXQ)]
  have hcomb : (Bad.card : ℝ) * Real.exp (-(5 / 36 : ℝ) * ((X.card : ℝ) / (M : ℝ))) ≤
      ((M : ℝ) ^ Q.card) * Real.exp (-(1 / 7 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
    calc _ ≤ ((M : ℝ) ^ (Q.card - X.card)) * (((M : ℝ) ^ X.card) * Real.exp (-(1 / 7 : ℝ) * ((X.card : ℝ) / (M : ℝ)))) :=
          hmarkov.trans (mul_le_mul_of_nonneg_left hpow_le (by positivity))
      _ = ((M : ℝ) ^ (Q.card - X.card) * (M : ℝ) ^ X.card) * Real.exp (-(1 / 7 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by ring
      _ = _ := by rw [hMpow]
  have hpos := Real.exp_pos (-(5 / 36 : ℝ) * ((X.card : ℝ) / (M : ℝ)))
  have hdiv := (le_div_iff₀ hpos).mpr hcomb
  calc (Bad.card : ℝ)
      ≤ ((M : ℝ) ^ Q.card) * Real.exp (-(1 / 7 : ℝ) * ((X.card : ℝ) / (M : ℝ))) /
          Real.exp (-(5 / 36 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := hdiv
    _ = ((M : ℝ) ^ Q.card) * Real.exp (-(1 / 252 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
        rw [mul_div_assoc, ← Real.exp_sub]; congr 2; ring

private lemma chernoff_bucket_upper {Q : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (X : Finset ℕ) (hXQ : X ⊆ Q)
    (j : Fin M) :
    ((Finset.univ.filter (fun f : Q → Fin M =>
      (5 / 4 : ℝ) * ((X.card : ℝ) / (M : ℝ)) ≤
        (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ))).card : ℝ) ≤
      ((M : ℝ) ^ Q.card) * Real.exp (-(1 / 120 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
  set Bad := Finset.univ.filter (fun f : Q → Fin M =>
    (5 / 4 : ℝ) * ((X.card : ℝ) / (M : ℝ)) ≤
      (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ))
  set lam : ℝ := (1 / 6 : ℝ)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hmarkov : (Bad.card : ℝ) * Real.exp ((5 / 24 : ℝ) * ((X.card : ℝ) / (M : ℝ))) ≤
      ∑ f : (Q → Fin M), Real.exp (lam * (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ)) := by
    calc (Bad.card : ℝ) * Real.exp ((5 / 24 : ℝ) * ((X.card : ℝ) / (M : ℝ)))
        = ∑ _f ∈ Bad, Real.exp ((5 / 24 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ f ∈ Bad, Real.exp (lam * (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun f hf => Real.exp_le_exp.mpr ?_
          have hle := (Finset.mem_filter.mp hf).2
          dsimp only [lam] at hle ⊢; linarith
      _ ≤ ∑ f : (Q → Fin M), Real.exp (lam * (((Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card : ℕ) : ℝ)) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le
  rw [mgf_bucket_sum hM X hXQ j lam] at hmarkov
  have hexp_le : Real.exp lam ≤ 6 / 5 := by
    have hneg : (5 / 6 : ℝ) ≤ Real.exp (-lam) := by
      dsimp [lam]; linarith [Real.add_one_le_exp (-(1 / 6 : ℝ))]
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 5 / 6) hneg
    rw [← Real.exp_neg, neg_neg] at hinv
    linarith [show (5 / 6 : ℝ)⁻¹ = 6 / 5 by norm_num]
  have hbase_le : (M : ℝ) - 1 + Real.exp lam ≤ (M : ℝ) * Real.exp ((1 / 5 : ℝ) / (M : ℝ)) := by
    have h1 : (M : ℝ) - 1 + Real.exp lam ≤ (M : ℝ) * (1 + (1 / 5 : ℝ) / (M : ℝ)) := by
      have hrew : (M : ℝ) * (1 + (1 / 5 : ℝ) / (M : ℝ)) = (M : ℝ) + 1 / 5 := by
        field_simp [hMpos.ne']
      linarith
    have h2 : 1 + (1 / 5 : ℝ) / (M : ℝ) ≤ Real.exp ((1 / 5 : ℝ) / (M : ℝ)) := by
      simpa [add_comm] using Real.add_one_le_exp ((1 / 5 : ℝ) / (M : ℝ))
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hMpos.le)
  have hbase_nn : 0 ≤ (M : ℝ) - 1 + Real.exp lam := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith [Real.exp_pos lam]
  have hpow_le : ((M : ℝ) - 1 + Real.exp lam) ^ X.card ≤
      ((M : ℝ) ^ X.card) * Real.exp ((1 / 5 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
    calc ((M : ℝ) - 1 + Real.exp lam) ^ X.card
        ≤ ((M : ℝ) * Real.exp ((1 / 5 : ℝ) / (M : ℝ))) ^ X.card := pow_le_pow_left₀ hbase_nn hbase_le _
      _ = ((M : ℝ) ^ X.card) * (Real.exp ((1 / 5 : ℝ) / (M : ℝ))) ^ X.card := mul_pow _ _ _
      _ = ((M : ℝ) ^ X.card) * Real.exp ((1 / 5 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
          rw [← Real.exp_nat_mul]; congr 2; ring
  have hMpow : (M : ℝ) ^ (Q.card - X.card) * (M : ℝ) ^ X.card = (M : ℝ) ^ Q.card := by
    rw [← pow_add, Nat.sub_add_cancel (Finset.card_le_card hXQ)]
  have hcomb : (Bad.card : ℝ) * Real.exp ((5 / 24 : ℝ) * ((X.card : ℝ) / (M : ℝ))) ≤
      ((M : ℝ) ^ Q.card) * Real.exp ((1 / 5 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
    calc _ ≤ ((M : ℝ) ^ (Q.card - X.card)) * (((M : ℝ) ^ X.card) * Real.exp ((1 / 5 : ℝ) * ((X.card : ℝ) / (M : ℝ)))) :=
          hmarkov.trans (mul_le_mul_of_nonneg_left hpow_le (by positivity))
      _ = ((M : ℝ) ^ (Q.card - X.card) * (M : ℝ) ^ X.card) * Real.exp ((1 / 5 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by ring
      _ = _ := by rw [hMpow]
  have hpos := Real.exp_pos ((5 / 24 : ℝ) * ((X.card : ℝ) / (M : ℝ)))
  have hdiv := (le_div_iff₀ hpos).mpr hcomb
  calc (Bad.card : ℝ)
      ≤ ((M : ℝ) ^ Q.card) * Real.exp ((1 / 5 : ℝ) * ((X.card : ℝ) / (M : ℝ))) /
          Real.exp ((5 / 24 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := hdiv
    _ = ((M : ℝ) ^ Q.card) * Real.exp (-(1 / 120 : ℝ) * ((X.card : ℝ) / (M : ℝ))) := by
        rw [mul_div_assoc, ← Real.exp_sub]; congr 2; ring

lemma exists_diverse_partition (ℓ : ℕ) (hℓ : 8 ≤ ℓ) :
    ∃ Y0 : ℕ, ∀ (y : ℕ) (Q : Finset ℕ), Y0 ≤ y →
      (∀ x ∈ Q, 1 ≤ x ∧ x < 2 * y) →
      (y : ℝ) ^ (1 / 3 : ℝ) ≤ (Q.card : ℝ) →
      (∀ d : ℕ, 2 ≤ d → (y : ℝ) ^ (1 / 4 : ℝ) ≤ ((Q.filter (fun x => ¬ d ∣ x)).card : ℝ)) →
      ∃ (A₁ A₂ : Fin ℓ → Finset ℕ),
        (∀ i, A₁ i ⊆ Q ∧ A₂ i ⊆ Q) ∧
        (∀ i, Disjoint (A₁ i) (A₂ i)) ∧
        (∀ i j, i ≠ j → Disjoint (A₁ i ∪ A₂ i) (A₁ j ∪ A₂ j)) ∧
        (∀ i, (Q.card : ℝ) / (24 * (ℓ : ℝ)) ≤ ((A₁ i).card : ℝ) ∧
              ((A₁ i).card : ℝ) ≤ (Q.card : ℝ) / (16 * (ℓ : ℝ))) ∧
        (∀ i, (Q.card : ℝ) / (24 * (ℓ : ℝ)) ≤ ((A₂ i).card : ℝ) ∧
              ((A₂ i).card : ℝ) ≤ (Q.card : ℝ) / (16 * (ℓ : ℝ))) ∧
        (∀ i, ∀ d : ℕ, 2 ≤ d →
          (y : ℝ) ^ (1 / 4 : ℝ) / (24 * (ℓ : ℝ)) ≤ (((A₁ i).filter (fun x => ¬ d ∣ x)).card : ℝ)) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hev : ∀ᶠ y : ℕ in atTop,
      100 ≤ y ∧
      (y : ℝ) ^ (1 / 4 : ℝ) ≤ (y : ℝ) ^ (1 / 3 : ℝ) ∧
      ((8 * ℓ * y : ℕ) : ℝ) * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ))) < 1 := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 4 : ℝ)) atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).tendsto_div_nhds_zero
    have h2 : Tendsto (fun x : ℝ => Real.log (8 * (ℓ : ℝ)) / x ^ (1 / 4 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num))
    filter_upwards [(h1.comp tendsto_natCast_atTop_atTop).eventually
        (gt_mem_nhds (show (0 : ℝ) < 1 / (20000 * (ℓ : ℝ)) by positivity)),
      (h2.comp tendsto_natCast_atTop_atTop).eventually
        (gt_mem_nhds (show (0 : ℝ) < 1 / (20000 * (ℓ : ℝ)) by positivity)),
      Filter.eventually_ge_atTop 100] with y hy1 hy2 hy100
    dsimp only [Function.comp_apply] at hy1 hy2
    have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
    have hrp_pos : 0 < (y : ℝ) ^ (1 / 4 : ℝ) := by positivity
    refine ⟨hy100, Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ y)) (by norm_num), ?_⟩
    have hlt1 := (div_lt_iff₀ hrp_pos).mp hy1
    have hlt2 := (div_lt_iff₀ hrp_pos).mp hy2
    have hlog_lt : Real.log (((8 * ℓ * y : ℕ) : ℝ)) < (y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)) := by
      push_cast
      rw [show (8 : ℝ) * (ℓ : ℝ) * (y : ℝ) = (8 * (ℓ : ℝ)) * (y : ℝ) by ring,
        Real.log_mul (by positivity) hypos.ne']
      have hsum : (1 / (20000 * (ℓ : ℝ)) + 1 / (20000 * (ℓ : ℝ))) * (y : ℝ) ^ (1 / 4 : ℝ) <
          (y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)) := by
        rw [show (1 / (20000 * (ℓ : ℝ)) + 1 / (20000 * (ℓ : ℝ))) * (y : ℝ) ^ (1 / 4 : ℝ) =
            (y : ℝ) ^ (1 / 4 : ℝ) / (10000 * (ℓ : ℝ)) by ring]
        exact div_lt_div_of_pos_left hrp_pos (by positivity) (by linarith)
      linarith
    have h1' : (((8 * ℓ * y : ℕ) : ℝ)) < Real.exp ((y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ))) := by
      rwa [← Real.log_lt_iff_lt_exp (by positivity)]
    have hneg : Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ))) =
        (Real.exp ((y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ))))⁻¹ := by
      rw [← Real.exp_neg, neg_div]
    rw [hneg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    exact h1'
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨Y0, fun y Q hyY0 hQ_rng hQ_card hQ_div => ?_⟩
  obtain ⟨hy100, hy_rpow, hprob_lt⟩ := hY0 y hyY0
  set M : ℕ := 20 * ℓ
  have hM1 : 1 ≤ M := by dsimp [M]; omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  -- Define bad event set on Ω = (Q → Fin M)
  let bucket (f : Q → Fin M) (j : Fin M) : Finset ℕ :=
    Q.filter (fun x => ∃ hx : x ∈ Q, f ⟨x, hx⟩ = j)
  have hbucket_card : ∀ (f : Q → Fin M) (X : Finset ℕ) (hXQ : X ⊆ Q) (j : Fin M),
      ((bucket f j).filter (fun x => x ∈ X)).card =
        (Finset.univ.filter (fun x : Q => x.1 ∈ X ∧ f x = j)).card := by
    intro f X hXQ j
    refine Finset.card_bij (fun x hx => ⟨x, (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1⟩) ?_ ?_ ?_
    · intro x hx
      simp only [bucket, Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, hx.2, hx.1.2.choose_spec⟩
    · intro x1 _ x2 _ h; exact congrArg Subtype.val h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      refine ⟨x.1, ?_, by ext; rfl⟩
      simp only [bucket, Finset.mem_filter]
      exact ⟨⟨x.2, x.2, hx.2⟩, hx.1⟩
  let BadLow (j : Fin (2 * ℓ)) : Finset (Q → Fin M) :=
    Finset.univ.filter (fun f =>
      (((Finset.univ.filter (fun x : Q => x.1 ∈ Q ∧ f x = ⟨j.1, by dsimp [M]; omega⟩)).card : ℕ) : ℝ) ≤
        (5 / 6 : ℝ) * ((Q.card : ℝ) / (M : ℝ)))
  let BadHigh (j : Fin (2 * ℓ)) : Finset (Q → Fin M) :=
    Finset.univ.filter (fun f =>
      (5 / 4 : ℝ) * ((Q.card : ℝ) / (M : ℝ)) ≤
        (((Finset.univ.filter (fun x : Q => x.1 ∈ Q ∧ f x = ⟨j.1, by dsimp [M]; omega⟩)).card : ℕ) : ℝ))
  let BadDiv (j : Fin (2 * ℓ)) (d : ℕ) : Finset (Q → Fin M) :=
    Finset.univ.filter (fun f =>
      (((Finset.univ.filter (fun x : Q => x.1 ∈ Q.filter (fun a => ¬ d ∣ a) ∧
          f x = ⟨j.1, by dsimp [M]; omega⟩)).card : ℕ) : ℝ) ≤
        (5 / 6 : ℝ) * (((Q.filter (fun a => ¬ d ∣ a)).card : ℝ) / (M : ℝ)))
  let AllBad : Finset (Q → Fin M) :=
    (Finset.univ.biUnion BadLow) ∪ (Finset.univ.biUnion BadHigh) ∪
      (Finset.univ.biUnion fun j : Fin (2 * ℓ) => (Finset.Icc 2 (2 * y)).biUnion (BadDiv j))
  have hQ_ge_y14 : (y : ℝ) ^ (1 / 4 : ℝ) ≤ (Q.card : ℝ) := hy_rpow.trans hQ_card
  have hAllBad_lt : (AllBad.card : ℝ) < (M : ℝ) ^ Q.card := by
    have hlow_b : ∀ j : Fin (2 * ℓ), (BadLow j).card ≤
        ((BadLow j).card) := fun _ => le_rfl
    have hsum1 : ∑ j : Fin (2 * ℓ), ((BadLow j).card : ℝ) ≤
        (2 * ℓ : ℝ) * ((M : ℝ) ^ Q.card * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)))) := by
      calc ∑ j : Fin (2 * ℓ), ((BadLow j).card : ℝ)
          ≤ ∑ _j : Fin (2 * ℓ), ((M : ℝ) ^ Q.card * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)))) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have hc := chernoff_bucket_lower hM1 Q subset_rfl ⟨j.1, by dsimp [M]; omega⟩
            refine hc.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
            have hrew : -(1 / 252 : ℝ) * ((Q.card : ℝ) / (M : ℝ)) = -(Q.card : ℝ) / (5040 * (ℓ : ℝ)) := by
              dsimp [M]; push_cast; ring
            rw [hrew, neg_div, neg_div, neg_le_neg_iff]
            exact div_le_div_of_nonneg_right hQ_ge_y14 (by positivity)
        _ = (2 * ℓ : ℝ) * _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
    have hsum2 : ∑ j : Fin (2 * ℓ), ((BadHigh j).card : ℝ) ≤
        (2 * ℓ : ℝ) * ((M : ℝ) ^ Q.card * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)))) := by
      calc ∑ j : Fin (2 * ℓ), ((BadHigh j).card : ℝ)
          ≤ ∑ _j : Fin (2 * ℓ), ((M : ℝ) ^ Q.card * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)))) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have hc := chernoff_bucket_upper hM1 Q subset_rfl ⟨j.1, by dsimp [M]; omega⟩
            refine hc.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
            have hrew : -(1 / 120 : ℝ) * ((Q.card : ℝ) / (M : ℝ)) = -(Q.card : ℝ) / (2400 * (ℓ : ℝ)) := by
              dsimp [M]; push_cast; ring
            rw [hrew, neg_div, neg_div, neg_le_neg_iff]
            have h1 : (y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)) ≤ (Q.card : ℝ) / (5040 * (ℓ : ℝ)) :=
              div_le_div_of_nonneg_right hQ_ge_y14 (by positivity)
            have h2 : (Q.card : ℝ) / (5040 * (ℓ : ℝ)) ≤ (Q.card : ℝ) / (2400 * (ℓ : ℝ)) :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
            exact h1.trans h2
        _ = (2 * ℓ : ℝ) * _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
    have hsum3 : ∑ j : Fin (2 * ℓ), ∑ d ∈ Finset.Icc 2 (2 * y), ((BadDiv j d).card : ℝ) ≤
        (2 * ℓ : ℝ) * (2 * (y : ℝ)) * ((M : ℝ) ^ Q.card * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)))) := by
      calc ∑ j : Fin (2 * ℓ), ∑ d ∈ Finset.Icc 2 (2 * y), ((BadDiv j d).card : ℝ)
          ≤ ∑ _j : Fin (2 * ℓ), ∑ _d ∈ Finset.Icc 2 (2 * y),
              ((M : ℝ) ^ Q.card * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)))) := by
            refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun d hd => ?_
            have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
            have hc := chernoff_bucket_lower hM1 (Q.filter (fun a => ¬ d ∣ a)) (Finset.filter_subset _ _)
              ⟨j.1, by dsimp [M]; omega⟩
            refine hc.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
            have hrew : -(1 / 252 : ℝ) * (((Q.filter (fun a => ¬ d ∣ a)).card : ℝ) / (M : ℝ)) =
                -(((Q.filter (fun a => ¬ d ∣ a)).card : ℝ)) / (5040 * (ℓ : ℝ)) := by
              dsimp [M]; push_cast; ring
            rw [hrew, neg_div, neg_div, neg_le_neg_iff]
            exact div_le_div_of_nonneg_right (hQ_div d hd2) (by positivity)
        _ = (2 * ℓ : ℝ) * (((Finset.Icc 2 (2 * y)).card : ℕ) : ℝ) *
              ((M : ℝ) ^ Q.card * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
        _ ≤ _ := by
            have hIcc : ((Finset.Icc 2 (2 * y)).card : ℝ) ≤ 2 * (y : ℝ) := by
              have : (Finset.Icc 2 (2 * y)).card ≤ 2 * y := by simp
              exact_mod_cast this
            gcongr
    have hcard_union : (AllBad.card : ℝ) ≤
        (∑ j : Fin (2 * ℓ), ((BadLow j).card : ℝ)) +
        (∑ j : Fin (2 * ℓ), ((BadHigh j).card : ℝ)) +
        (∑ j : Fin (2 * ℓ), ∑ d ∈ Finset.Icc 2 (2 * y), ((BadDiv j d).card : ℝ)) := by
      have h1 : AllBad.card ≤ (Finset.univ.biUnion BadLow).card + (Finset.univ.biUnion BadHigh).card +
          (Finset.univ.biUnion fun j : Fin (2 * ℓ) => (Finset.Icc 2 (2 * y)).biUnion (BadDiv j)).card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      have h2 : (Finset.univ.biUnion BadLow).card ≤ ∑ j : Fin (2 * ℓ), (BadLow j).card := Finset.card_biUnion_le
      have h3 : (Finset.univ.biUnion BadHigh).card ≤ ∑ j : Fin (2 * ℓ), (BadHigh j).card := Finset.card_biUnion_le
      have h4 : (Finset.univ.biUnion fun j : Fin (2 * ℓ) => (Finset.Icc 2 (2 * y)).biUnion (BadDiv j)).card ≤
          ∑ j : Fin (2 * ℓ), ∑ d ∈ Finset.Icc 2 (2 * y), (BadDiv j d).card :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
      have htot : AllBad.card ≤ (∑ j : Fin (2 * ℓ), (BadLow j).card) + (∑ j : Fin (2 * ℓ), (BadHigh j).card) +
          (∑ j : Fin (2 * ℓ), ∑ d ∈ Finset.Icc 2 (2 * y), (BadDiv j d).card) := by omega
      have htot_r : (AllBad.card : ℝ) ≤
          (((∑ j : Fin (2 * ℓ), (BadLow j).card) + (∑ j : Fin (2 * ℓ), (BadHigh j).card) +
            (∑ j : Fin (2 * ℓ), ∑ d ∈ Finset.Icc 2 (2 * y), (BadDiv j d).card) : ℕ) : ℝ) := by
        exact_mod_cast htot
      simpa only [Nat.cast_add, Nat.cast_sum] using htot_r
    have hcoef : (2 * (ℓ : ℝ)) + (2 * (ℓ : ℝ)) + (2 * (ℓ : ℝ)) * (2 * (y : ℝ)) ≤ ((8 * ℓ * y : ℕ) : ℝ) := by
      push_cast
      have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (by omega : 1 ≤ y)
      nlinarith
    have hnn_exp : 0 ≤ (M : ℝ) ^ Q.card * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ))) := by positivity
    calc (AllBad.card : ℝ)
        ≤ ((2 * (ℓ : ℝ)) + (2 * (ℓ : ℝ)) + (2 * (ℓ : ℝ)) * (2 * (y : ℝ))) *
            ((M : ℝ) ^ Q.card * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)))) := by linarith
      _ ≤ ((8 * ℓ * y : ℕ) : ℝ) * ((M : ℝ) ^ Q.card * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)))) :=
          mul_le_mul_of_nonneg_right hcoef hnn_exp
      _ = (M : ℝ) ^ Q.card * (((8 * ℓ * y : ℕ) : ℝ) * Real.exp (-(y : ℝ) ^ (1 / 4 : ℝ) / (5040 * (ℓ : ℝ)))) := by ring
      _ < (M : ℝ) ^ Q.card * 1 := mul_lt_mul_of_pos_left hprob_lt (by positivity)
      _ = (M : ℝ) ^ Q.card := mul_one _
  have hcard_univ : ((Finset.univ : Finset (Q → Fin M)).card : ℝ) = (M : ℝ) ^ Q.card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]; push_cast; rfl
  have hex : ∃ f : Q → Fin M, f ∉ AllBad := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Q → Fin M)) ⊆ AllBad := fun f _ => hall f
    have hle : ((Finset.univ : Finset (Q → Fin M)).card : ℝ) ≤ (AllBad.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    linarith
  obtain ⟨f, hf⟩ := hex
  let A₁ (i : Fin ℓ) : Finset ℕ := bucket f ⟨2 * i.1, by dsimp [M]; omega⟩
  let A₂ (i : Fin ℓ) : Finset ℕ := bucket f ⟨2 * i.1 + 1, by dsimp [M]; omega⟩
  have hbucket_good : ∀ j : Fin (2 * ℓ),
      (Q.card : ℝ) / (24 * (ℓ : ℝ)) ≤ ((bucket f ⟨j.1, by dsimp [M]; omega⟩).card : ℝ) ∧
      ((bucket f ⟨j.1, by dsimp [M]; omega⟩).card : ℝ) ≤ (Q.card : ℝ) / (16 * (ℓ : ℝ)) ∧
      ∀ d : ℕ, 2 ≤ d → (y : ℝ) ^ (1 / 4 : ℝ) / (24 * (ℓ : ℝ)) ≤
        (((bucket f ⟨j.1, by dsimp [M]; omega⟩).filter (fun x => ¬ d ∣ x)).card : ℝ) := by
    intro j
    have hnot_low : f ∉ BadLow j := fun h => hf (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩)))
    have hnot_high : f ∉ BadHigh j := fun h => hf (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩)))
    have hcard_eq : (bucket f ⟨j.1, by dsimp [M]; omega⟩).card =
        (Finset.univ.filter (fun x : Q => x.1 ∈ Q ∧ f x = ⟨j.1, by dsimp [M]; omega⟩)).card := by
      have h := hbucket_card f Q subset_rfl ⟨j.1, by dsimp [M]; omega⟩
      have hfilt : (bucket f ⟨j.1, by dsimp [M]; omega⟩).filter (fun x => x ∈ Q) =
          bucket f ⟨j.1, by dsimp [M]; omega⟩ := Finset.filter_true_of_mem fun x hx => (Finset.mem_filter.mp hx).1
      rwa [hfilt] at h
    have hlo : (Q.card : ℝ) / (24 * (ℓ : ℝ)) ≤ ((bucket f ⟨j.1, by dsimp [M]; omega⟩).card : ℝ) := by
      simp only [BadLow, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot_low
      rw [hcard_eq]
      have hrew : (5 / 6 : ℝ) * ((Q.card : ℝ) / (M : ℝ)) = (Q.card : ℝ) / (24 * (ℓ : ℝ)) := by
        dsimp [M]; push_cast; ring
      linarith
    have hhi : ((bucket f ⟨j.1, by dsimp [M]; omega⟩).card : ℝ) ≤ (Q.card : ℝ) / (16 * (ℓ : ℝ)) := by
      simp only [BadHigh, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot_high
      rw [hcard_eq]
      have hrew : (5 / 4 : ℝ) * ((Q.card : ℝ) / (M : ℝ)) = (Q.card : ℝ) / (16 * (ℓ : ℝ)) := by
        dsimp [M]; push_cast; ring
      linarith
    refine ⟨hlo, hhi, fun d hd2 => ?_⟩
    by_cases hdy : d ≤ 2 * y
    · have hnot_div : f ∉ BadDiv j d := fun h => hf (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨d, Finset.mem_Icc.mpr ⟨hd2, hdy⟩, h⟩⟩))
      have hnot_div' : (5 / 6 : ℝ) * (((Q.filter (fun a => ¬ d ∣ a)).card : ℝ) / (M : ℝ)) <
          (((Finset.univ.filter (fun x : Q => x.1 ∈ Q.filter (fun a => ¬ d ∣ a) ∧
            f x = ⟨j.1, by dsimp [M]; omega⟩)).card : ℕ) : ℝ) := by
        rw [← not_le]
        intro hle
        exact hnot_div (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
      have heq_f : (bucket f ⟨j.1, by dsimp [M]; omega⟩).filter (fun x => ¬ d ∣ x) =
          (bucket f ⟨j.1, by dsimp [M]; omega⟩).filter (fun x => x ∈ Q.filter (fun a => ¬ d ∣ a)) := by
        ext x; simp only [bucket, Finset.mem_filter]; tauto
      rw [heq_f, hbucket_card f (Q.filter (fun a => ¬ d ∣ a)) (Finset.filter_subset _ _) ⟨j.1, by dsimp [M]; omega⟩]
      have hrew : (5 / 6 : ℝ) * (((Q.filter (fun a => ¬ d ∣ a)).card : ℝ) / (M : ℝ)) =
          ((Q.filter (fun a => ¬ d ∣ a)).card : ℝ) / (24 * (ℓ : ℝ)) := by
        dsimp [M]; push_cast; ring
      have hdiv_ge := div_le_div_of_nonneg_right (hQ_div d hd2) (show 0 ≤ 24 * (ℓ : ℝ) by positivity)
      linarith
    · have hall_ndvd : (bucket f ⟨j.1, by dsimp [M]; omega⟩).filter (fun x => ¬ d ∣ x) =
          bucket f ⟨j.1, by dsimp [M]; omega⟩ := by
        refine Finset.filter_true_of_mem fun x hx => ?_
        have hxQ : x ∈ Q := (Finset.mem_filter.mp hx).1
        have hxr := hQ_rng x hxQ
        intro hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      rw [hall_ndvd]
      exact (div_le_div_of_nonneg_right hQ_ge_y14 (by positivity)).trans hlo
  refine ⟨A₁, A₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact ⟨Finset.filter_subset _ _, Finset.filter_subset _ _⟩
  · intro i
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [A₁, A₂, bucket, Finset.mem_filter] at h1 h2
    have heq := h1.2.choose_spec.symm.trans h2.2.choose_spec
    have hval := congrArg Fin.val heq
    dsimp at hval; omega
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [A₁, A₂, bucket, Finset.mem_union, Finset.mem_filter] at h1 h2
    have hij_val : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
    rcases h1 with ⟨hx1, _, hf1⟩ | ⟨hx1, _, hf1⟩ <;> rcases h2 with ⟨hx2, _, hf2⟩ | ⟨hx2, _, hf2⟩ <;>
    · have hval := congrArg Fin.val (hf1.symm.trans hf2); dsimp at hval; omega
  · intro i
    have hg := hbucket_good ⟨2 * i.1, by omega⟩
    exact ⟨hg.1, hg.2.1⟩
  · intro i
    have hg := hbucket_good ⟨2 * i.1 + 1, by omega⟩
    exact ⟨hg.1, hg.2.1⟩
  · intro i d hd2
    exact (hbucket_good ⟨2 * i.1, by omega⟩).2.2 d hd2

end Part1

section Part2
open Finset Nat
open scoped BigOperators Pointwise Classical

/- ### Section 1: Iterated Sumsets `nfoldSum` -/

private noncomputable def nfoldSum {G : Type*} [AddCommMonoid G] [DecidableEq G] :
    ℕ → Finset G → Finset G
  | 0, _ => {0}
  | k + 1, A => nfoldSum k A + A

lemma nfoldSum_zero {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    nfoldSum 0 A = {0} := rfl

lemma nfoldSum_succ {G : Type*} [AddCommMonoid G] [DecidableEq G] (k : ℕ) (A : Finset G) :
    nfoldSum (k + 1) A = nfoldSum k A + A := rfl

lemma nfoldSum_one {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    nfoldSum 1 A = A := by
  ext x; simp [nfoldSum, Finset.mem_add]

lemma nfoldSum_two {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    nfoldSum 2 A = A + A := by
  rw [nfoldSum_succ, nfoldSum_one]

lemma nfoldSum_add {G : Type*} [AddCommMonoid G] [DecidableEq G] (a b : ℕ) (A : Finset G) :
    nfoldSum (a + b) A = nfoldSum a A + nfoldSum b A := by
  induction b with
  | zero => ext x; simp [nfoldSum, Finset.mem_add]
  | succ b ih =>
    rw [← Nat.add_assoc, nfoldSum_succ, ih, nfoldSum_succ, add_assoc]

lemma nfoldSum_mul {G : Type*} [AddCommMonoid G] [DecidableEq G] (a b : ℕ) (A : Finset G) :
    nfoldSum (a * b) A = nfoldSum a (nfoldSum b A) := by
  induction a with
  | zero => simp [nfoldSum]
  | succ a ih =>
    rw [Nat.succ_mul, nfoldSum_add, ih, nfoldSum_succ]

lemma nfoldSum_mono {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A B : Finset G} (h : A ⊆ B) (k : ℕ) :
    nfoldSum k A ⊆ nfoldSum k B := by
  induction k with
  | zero => exact subset_rfl
  | succ k ih => exact Finset.add_subset_add ih h

lemma zero_mem_nfoldSum {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A : Finset G} (h0 : (0 : G) ∈ A) (k : ℕ) :
    (0 : G) ∈ nfoldSum k A := by
  induction k with
  | zero => simp [nfoldSum]
  | succ k ih =>
    rw [nfoldSum_succ]
    exact Finset.mem_add.mpr ⟨0, ih, 0, h0, add_zero 0⟩

lemma nfoldSum_le_mono {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A : Finset G} (h0 : (0 : G) ∈ A) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    nfoldSum k₁ A ⊆ nfoldSum k₂ A := by
  have heq : k₂ = k₁ + (k₂ - k₁) := (Nat.add_sub_cancel' hk).symm
  rw [heq, nfoldSum_add]
  intro x hx
  exact Finset.mem_add.mpr ⟨x, hx, 0, zero_mem_nfoldSum h0 (k₂ - k₁), add_zero x⟩

lemma subset_nfoldSum_of_zero_mem {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A : Finset G} (h0 : (0 : G) ∈ A) {k : ℕ} (hk : 1 ≤ k) :
    A ⊆ nfoldSum k A := by
  simpa [nfoldSum_one] using nfoldSum_le_mono h0 hk

/- ### Section 2: Subset Sums in `ℕ` and `ZMod t`, and CFP21 Lemma 2.5 (`lem:modp`) -/

private noncomputable def subsetSumsFin (A : Finset ℕ) : Finset ℕ :=
  A.powerset.image (fun B => ∑ x ∈ B, x)

private noncomputable def subsetSumsMod (t : ℕ) (A : Finset ℕ) : Finset (ZMod t) :=
  A.powerset.image (fun B => ((∑ x ∈ B, x : ℕ) : ZMod t))

lemma zero_mem_subsetSumsFin (A : Finset ℕ) : 0 ∈ subsetSumsFin A :=
  Finset.mem_image.mpr ⟨∅, Finset.empty_mem_powerset A, by simp⟩

lemma zero_mem_subsetSumsMod (t : ℕ) (A : Finset ℕ) : (0 : ZMod t) ∈ subsetSumsMod t A :=
  Finset.mem_image.mpr ⟨∅, Finset.empty_mem_powerset A, by simp⟩

lemma subsetSumsFin_mono {A B : Finset ℕ} (h : A ⊆ B) : subsetSumsFin A ⊆ subsetSumsFin B :=
  Finset.image_subset_image (Finset.powerset_mono.mpr h)

lemma subsetSumsMod_mono (t : ℕ) {A B : Finset ℕ} (h : A ⊆ B) :
    subsetSumsMod t A ⊆ subsetSumsMod t B :=
  Finset.image_subset_image (Finset.powerset_mono.mpr h)

lemma subsetSumsFin_insert {A : Finset ℕ} {a : ℕ} (ha : a ∉ A) :
    subsetSumsFin (insert a A) = subsetSumsFin A ∪ (subsetSumsFin A).image (· + a) := by
  ext s
  simp only [subsetSumsFin, Finset.mem_union, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨B, hB, rfl⟩
    by_cases haB : a ∈ B
    · right
      refine ⟨∑ x ∈ B.erase a, x, ⟨B.erase a, ?_, rfl⟩, ?_⟩
      · intro x hx
        have hxB := Finset.mem_erase.mp hx
        rcases Finset.mem_insert.mp (hB hxB.2) with rfl | hA
        · exact absurd rfl hxB.1
        · exact hA
      · rw [add_comm, Finset.add_sum_erase B (fun x => x) haB]
    · left
      refine ⟨B, fun x hx => ?_, rfl⟩
      rcases Finset.mem_insert.mp (hB hx) with rfl | hA
      · exact absurd hx haB
      · exact hA
  · rintro (⟨B, hB, rfl⟩ | ⟨t, ⟨B, hB, rfl⟩, rfl⟩)
    · exact ⟨B, hB.trans (Finset.subset_insert a A), rfl⟩
    · refine ⟨insert a B, Finset.insert_subset_insert a hB, ?_⟩
      rw [Finset.sum_insert (fun h => ha (hB h)), add_comm]

lemma subsetSumsMod_insert (t : ℕ) {A : Finset ℕ} {a : ℕ} (ha : a ∉ A) :
    subsetSumsMod t (insert a A) =
      subsetSumsMod t A ∪ (subsetSumsMod t A).image (· + (a : ZMod t)) := by
  have heq : subsetSumsMod t (insert a A) = (subsetSumsFin (insert a A)).image (fun s : ℕ => (s : ZMod t)) := by
    unfold subsetSumsMod subsetSumsFin; rw [Finset.image_image]; rfl
  have heqA : subsetSumsMod t A = (subsetSumsFin A).image (fun s : ℕ => (s : ZMod t)) := by
    unfold subsetSumsMod subsetSumsFin; rw [Finset.image_image]; rfl
  rw [heq, subsetSumsFin_insert ha, Finset.image_union, heqA, Finset.image_image, Finset.image_image]
  congr 1
  refine Finset.image_congr fun s _ => ?_
  simp only [Function.comp_apply, Nat.cast_add]

lemma card_subsetSumsFin_insert_ge {A : Finset ℕ} {m : ℕ} (hm : m ∉ A) (hm1 : 1 ≤ m) :
    (subsetSumsFin A).card + (subsetSumsMod m A).card ≤ (subsetSumsFin (insert m A)).card := by
  rw [subsetSumsFin_insert hm]
  have hsub_disj : Disjoint (subsetSumsFin A) ((subsetSumsFin A).image (· + m) \ subsetSumsFin A) :=
    Finset.disjoint_sdiff
  have hunion : subsetSumsFin A ∪ (subsetSumsFin A).image (· + m) =
      subsetSumsFin A ∪ ((subsetSumsFin A).image (· + m) \ subsetSumsFin A) :=
    (Finset.union_sdiff_self_eq_union).symm
  rw [hunion, Finset.card_union_of_disjoint hsub_disj]
  apply Nat.add_le_add_left
  -- For each r ∈ subsetSumsMod m A, take max element s_r of subsetSumsFin A with (s_r : ZMod m) = r
  -- Then s_r + m ∈ (subsetSumsFin A).image (· + m) \ subsetSumsFin A, and r ↦ s_r + m is injective
  have hne : ∀ r ∈ subsetSumsMod m A,
      ((subsetSumsFin A).filter (fun s : ℕ => (s : ZMod m) = r)).Nonempty := by
    intro r hr
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨∑ x ∈ B, x, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨B, hB, rfl⟩, rfl⟩⟩
  let f (r : ZMod m) : ℕ :=
    if h : r ∈ subsetSumsMod m A then
      ((subsetSumsFin A).filter (fun s : ℕ => (s : ZMod m) = r)).max' (hne r h) + m
    else 0
  have hf_mem : ∀ r ∈ subsetSumsMod m A,
      f r ∈ (subsetSumsFin A).image (· + m) \ subsetSumsFin A := by
    intro r hr
    dsimp [f]; rw [dif_pos hr]
    set F := (subsetSumsFin A).filter (fun s : ℕ => (s : ZMod m) = r)
    set s0 := F.max' (hne r hr)
    have hs0_mem : s0 ∈ F := Finset.max'_mem F (hne r hr)
    have hs0_A : s0 ∈ subsetSumsFin A := (Finset.mem_filter.mp hs0_mem).1
    have hs0_mod : (s0 : ZMod m) = r := (Finset.mem_filter.mp hs0_mem).2
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨s0, hs0_A, rfl⟩, fun hmem => ?_⟩
    have hs1_F : s0 + m ∈ F := by
      refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
      rw [Nat.cast_add, hs0_mod, ZMod.natCast_self, add_zero]
    have hle := Finset.le_max' F (s0 + m) hs1_F
    omega
  have hf_inj : Set.InjOn f (subsetSumsMod m A : Set (ZMod m)) := by
    intro r1 hr1 r2 hr2 heq
    have hr1' : r1 ∈ subsetSumsMod m A := Finset.mem_coe.mp hr1
    have hr2' : r2 ∈ subsetSumsMod m A := Finset.mem_coe.mp hr2
    dsimp [f] at heq
    rw [dif_pos hr1', dif_pos hr2'] at heq
    have h1 := (Finset.mem_filter.mp (Finset.max'_mem _ (hne r1 hr1'))).2
    have h2 := (Finset.mem_filter.mp (Finset.max'_mem _ (hne r2 hr2'))).2
    have hmod := congrArg (fun x : ℕ => (x : ZMod m)) heq
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero] at hmod
    rw [← h1, ← h2, hmod]
  calc (subsetSumsMod m A).card
      = ((subsetSumsMod m A).image f).card := (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ ((subsetSumsFin A).image (· + m) \ subsetSumsFin A).card :=
        Finset.card_le_card (Finset.image_subset_iff.mpr hf_mem)

lemma card_subsetSumsFin_union_ge {A B : Finset ℕ} (hdisj : Disjoint A B) {h : ℝ}
    (hB : ∀ t ∈ B, 1 ≤ t ∧ h ≤ ((subsetSumsMod t A).card : ℝ)) :
    (B.card : ℝ) * h ≤ ((subsetSumsFin (A ∪ B)).card : ℝ) := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert t B' ht ih =>
    have hdisj' : Disjoint A B' := Disjoint.mono_right (Finset.subset_insert t B') hdisj
    have htA : t ∉ A := Finset.disjoint_right.mp hdisj (Finset.mem_insert_self t B')
    have htAB : t ∉ A ∪ B' := by simp [htA, ht]
    have hB' : ∀ x ∈ B', 1 ≤ x ∧ h ≤ ((subsetSumsMod x A).card : ℝ) :=
      fun x hx => hB x (Finset.mem_insert_of_mem hx)
    have hih := ih hdisj' hB'
    have ht_prop := hB t (Finset.mem_insert_self t B')
    have hstep := card_subsetSumsFin_insert_ge (A := A ∪ B') htAB ht_prop.1
    have hmod_le : (subsetSumsMod t A).card ≤ (subsetSumsMod t (A ∪ B')).card :=
      Finset.card_le_card (subsetSumsMod_mono t Finset.subset_union_left)
    have hstep_r : ((subsetSumsFin (A ∪ B')).card : ℝ) + ((subsetSumsMod t A).card : ℝ) ≤
        ((subsetSumsFin (insert t (A ∪ B'))).card : ℝ) := by
      have : (subsetSumsFin (A ∪ B')).card + (subsetSumsMod t A).card ≤
          (subsetSumsFin (insert t (A ∪ B'))).card :=
        (Nat.add_le_add_left hmod_le _).trans hstep
      exact_mod_cast this
    have hunion_eq : A ∪ insert t B' = insert t (A ∪ B') := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [hunion_eq, Finset.card_insert_of_notMem ht]
    push_cast
    linarith

/- ### Section 3: Double Counting (`lem:double-count`) and Stable Period (`lem:stable-period`) -/

private noncomputable def Gset {m : ℕ} [NeZero m] (A : Finset (ZMod m)) (d : ℕ) : Finset (ZMod m) :=
  Finset.univ.filter (fun x => ((A.image (· + x)) \ A).card ≤ d)

lemma mem_Gset_iff {m : ℕ} [NeZero m] {A : Finset (ZMod m)} {d : ℕ} {x : ZMod m} :
    x ∈ Gset A d ↔ ((A.image (· + x)) \ A).card ≤ d := by
  simp [Gset]

lemma mem_Gset_iff_union {m : ℕ} [NeZero m] {A : Finset (ZMod m)} {d : ℕ} {x : ZMod m} :
    x ∈ Gset A d ↔ (A ∪ A.image (· + x)).card ≤ A.card + d := by
  rw [mem_Gset_iff]
  have hu : A ∪ A.image (· + x) = A ∪ (A.image (· + x) \ A) :=
    Finset.union_sdiff_self_eq_union.symm
  rw [hu, Finset.card_union_of_disjoint Finset.disjoint_sdiff]
  omega

lemma zero_mem_Gset {m : ℕ} [NeZero m] (A : Finset (ZMod m)) (d : ℕ) :
    (0 : ZMod m) ∈ Gset A d := by
  rw [mem_Gset_iff]
  have : A.image (· + (0 : ZMod m)) = A := by simp
  rw [this, Finset.sdiff_self, Finset.card_empty]
  exact Nat.zero_le d

lemma Gset_mono {m : ℕ} [NeZero m] (A : Finset (ZMod m)) {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    Gset A d₁ ⊆ Gset A d₂ := by
  intro x hx
  rw [mem_Gset_iff] at hx ⊢
  omega

lemma card_shift_sdiff_add_le {m : ℕ} [NeZero m] (A : Finset (ZMod m)) (x y : ZMod m) :
    ((A.image (· + (x + y))) \ A).card ≤
      ((A.image (· + x)) \ A).card + ((A.image (· + y)) \ A).card := by
  have hsub : (A.image (· + (x + y))) \ A ⊆
      ((A.image (· + (x + y))) \ (A.image (· + y))) ∪ ((A.image (· + y)) \ A) := by
    intro z hz
    simp only [Finset.mem_sdiff, Finset.mem_union] at hz ⊢
    by_cases hy : z ∈ A.image (· + y)
    · exact Or.inr ⟨hy, hz.2⟩
    · exact Or.inl ⟨hz.1, hy⟩
  have hshift_eq : ((A.image (· + (x + y))) \ (A.image (· + y))).card =
      ((A.image (· + x)) \ A).card := by
    have heq : (A.image (· + (x + y))) \ (A.image (· + y)) =
        ((A.image (· + x)) \ A).image (· + y) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hnot⟩
        refine ⟨a + x, ⟨⟨a, ha, rfl⟩, fun hA => hnot ⟨a + x, hA, add_assoc a x y⟩⟩, add_assoc a x y⟩
      · rintro ⟨w, ⟨⟨a, ha, rfl⟩, hnot⟩, rfl⟩
        refine ⟨⟨a, ha, (add_assoc a x y).symm⟩, ?_⟩
        rintro ⟨b, hb, heqb⟩
        have : a + x = b := add_right_cancel heqb.symm
        exact hnot (this ▸ hb)
    rw [heq, Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
  calc ((A.image (· + (x + y))) \ A).card
      ≤ (((A.image (· + (x + y))) \ (A.image (· + y))) ∪ ((A.image (· + y)) \ A)).card :=
        Finset.card_le_card hsub
    _ ≤ ((A.image (· + (x + y))) \ (A.image (· + y))).card + ((A.image (· + y)) \ A).card :=
        Finset.card_union_le _ _
    _ = ((A.image (· + x)) \ A).card + ((A.image (· + y)) \ A).card := by rw [hshift_eq]

lemma nfoldSum_Gset_subset {m : ℕ} [NeZero m] (A : Finset (ZMod m)) (d k : ℕ) :
    nfoldSum k (Gset A d) ⊆ Gset A (k * d) := by
  induction k with
  | zero =>
    intro x hx
    simp only [nfoldSum_zero, Finset.mem_singleton] at hx
    subst hx
    simpa using zero_mem_Gset A 0
  | succ k ih =>
    intro z hz
    rw [nfoldSum_succ] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    have hx' := mem_Gset_iff.mp (ih hx)
    have hy' := mem_Gset_iff.mp hy
    rw [mem_Gset_iff]
    have htri := card_shift_sdiff_add_le A x y
    have hmul : (k + 1) * d = k * d + d := by ring
    omega

lemma card_Gset_le {m : ℕ} [NeZero m] (A : Finset (ZMod m)) (d : ℕ)
    (hd : d < A.card) :
    ((Gset A d).card : ℝ) ≤ (A.card : ℝ) ^ 2 / ((A.card : ℝ) - (d : ℝ)) := by
  have hsum_eq : ∑ x : ZMod m, ((A.image (· + x)) \ A).card = A.card * (m - A.card) := by
    have h1 : ∀ x : ZMod m, ((A.image (· + x)) \ A).card =
        (A.filter (fun a => a + x ∉ A)).card := by
      intro x
      refine Finset.card_bij (fun z _ => z - x) ?_ ?_ ?_
      · intro z hz
        obtain ⟨hz1, hnot⟩ := Finset.mem_sdiff.mp hz
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz1
        simp only [Finset.mem_filter, add_sub_cancel_right]
        exact ⟨ha, hnot⟩
      · intro z1 _ z2 _ heq; exact sub_left_inj.mp heq
      · intro a ha
        obtain ⟨haA, hnot⟩ := Finset.mem_filter.mp ha
        exact ⟨a + x, Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨a, haA, rfl⟩, hnot⟩, add_sub_cancel_right a x⟩
    simp_rw [h1, Finset.card_filter]
    rw [Finset.sum_comm]
    have h2 : ∀ a ∈ A, ∑ x : ZMod m, (if a + x ∉ A then 1 else 0) = m - A.card := by
      intro a _
      rw [← Finset.card_filter]
      have hbij : (Finset.univ.filter (fun x : ZMod m => a + x ∉ A)).card =
          ((Finset.univ : Finset (ZMod m)) \ A).card := by
        refine Finset.card_bij (fun x _ => a + x) ?_ ?_ ?_
        · intro x hx; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        · intro x1 _ x2 _ heq; exact add_left_cancel heq
        · intro y hy
          exact ⟨y - a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [add_sub_cancel] using (Finset.mem_sdiff.mp hy).2⟩,
            add_sub_cancel a y⟩
      rw [hbij, Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, ZMod.card m]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]
  have hsum_le : ∑ x : ZMod m, ((A.image (· + x)) \ A).card ≤
      (Gset A d).card * d + (m - (Gset A d).card) * A.card := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (ZMod m)))
      (p := fun x => ((A.image (· + x)) \ A).card ≤ d) (f := fun x => ((A.image (· + x)) \ A).card)
    rw [← hsplit]
    have hpart1 : ∑ x ∈ Finset.univ.filter (fun x : ZMod m => ((A.image (· + x)) \ A).card ≤ d),
        ((A.image (· + x)) \ A).card ≤ (Gset A d).card * d := by
      calc ∑ x ∈ Gset A d, ((A.image (· + x)) \ A).card
          ≤ ∑ _x ∈ Gset A d, d := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
        _ = (Gset A d).card * d := by rw [Finset.sum_const, smul_eq_mul]
    have hpart2 : ∑ x ∈ Finset.univ.filter (fun x : ZMod m => ¬ ((A.image (· + x)) \ A).card ≤ d),
        ((A.image (· + x)) \ A).card ≤ (m - (Gset A d).card) * A.card := by
      have hcard_not : (Finset.univ.filter (fun x : ZMod m => ¬ ((A.image (· + x)) \ A).card ≤ d)).card =
          m - (Gset A d).card := by
        have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod m)))
          (p := fun x => ((A.image (· + x)) \ A).card ≤ d)
        rw [Finset.card_univ, ZMod.card m] at htot
        dsimp [Gset]; omega
      calc _ ≤ ∑ _x ∈ Finset.univ.filter (fun x : ZMod m => ¬ ((A.image (· + x)) \ A).card ≤ d), A.card :=
            Finset.sum_le_sum fun x _ => (Finset.card_le_card Finset.sdiff_subset).trans Finset.card_image_le
        _ = (m - (Gset A d).card) * A.card := by rw [Finset.sum_const, hcard_not, smul_eq_mul]
    exact Nat.add_le_add hpart1 hpart2
  have hAm : A.card ≤ m := by simpa [ZMod.card] using Finset.card_le_univ A
  have hGm : (Gset A d).card ≤ m := by simpa [ZMod.card] using Finset.card_le_univ (Gset A d)
  have hineq : (A.card : ℝ) * ((m : ℝ) - (A.card : ℝ)) ≤
      ((Gset A d).card : ℝ) * (d : ℝ) + ((m : ℝ) - ((Gset A d).card : ℝ)) * (A.card : ℝ) := by
    have hnat : A.card * (m - A.card) ≤ (Gset A d).card * d + (m - (Gset A d).card) * A.card :=
      hsum_eq ▸ hsum_le
    have hcast : ((A.card * (m - A.card) : ℕ) : ℝ) ≤
        (((Gset A d).card * d + (m - (Gset A d).card) * A.card : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast [Nat.cast_sub hAm, Nat.cast_sub hGm] at hcast
    exact hcast
  have hpos : 0 < (A.card : ℝ) - (d : ℝ) := by
    have : (d : ℝ) < (A.card : ℝ) := by exact_mod_cast hd
    linarith
  rw [le_div_iff₀ hpos]
  nlinarith

/- ### Section 4: Full Mod-`d` Subset Sums from Diversity (`lem:full-mod-d`) and Coset Fiber (`lem:Su`) -/

private lemma natCast_sum_zmod (m : ℕ) (S : Finset ℕ) :
    ((∑ x ∈ S, x : ℕ) : ZMod m) = ∑ x ∈ S, (x : ZMod m) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.cast_add, ih]

private lemma add_closure_zmultiples {d : ℕ} [NeZero d] {S : Finset (ZMod d)}
    (T : Finset ℕ) (hT : ∀ a ∈ T, ∀ s ∈ S, s + (a : ZMod d) ∈ S) :
    ∀ s ∈ S, s + ((Nat.gcd d (T.gcd id) : ℕ) : ZMod d) ∈ S := by
  -- Closed under +a for all a ∈ T implies closed under +k*a for all k : ℕ, hence under +z*a for all z : ℤ
  have hmul_nat : ∀ x : ZMod d, (∀ s ∈ S, s + x ∈ S) → ∀ k : ℕ, ∀ s ∈ S, s + (k : ZMod d) * x ∈ S := by
    intro x hx k
    induction k with
    | zero => intro s hs; simpa using hs
    | succ k ih =>
      intro s hs
      have h1 := ih s hs
      have h2 := hx _ h1
      have heq : s + (k : ZMod d) * x + x = s + ((k + 1 : ℕ) : ZMod d) * x := by push_cast; ring
      rwa [heq] at h2
  have hmul_int : ∀ x : ZMod d, (∀ s ∈ S, s + x ∈ S) → ∀ z : ℤ, ∀ s ∈ S, s + (z : ZMod d) * x ∈ S := by
    intro x hx z s hs
    have hd_pos : 0 < d := NeZero.pos d
    have hmod : (z : ZMod d) = (((z % (d : ℤ)).toNat : ℕ) : ZMod d) := by
      have hnn : 0 ≤ z % (d : ℤ) := Int.emod_nonneg z (by exact_mod_cast hd_pos.ne')
      have h1 : (((z % (d : ℤ)).toNat : ℕ) : ℤ) = z % (d : ℤ) := Int.toNat_of_nonneg hnn
      calc (z : ZMod d)
          = ((z % (d : ℤ) : ℤ) : ZMod d) := (ZMod.intCast_mod z d).symm
        _ = ((((z % (d : ℤ)).toNat : ℕ) : ℤ) : ZMod d) := by rw [h1]
        _ = (((z % (d : ℤ)).toNat : ℕ) : ZMod d) := Int.cast_natCast _
    rw [hmod]
    exact hmul_nat x hx (z % (d : ℤ)).toNat s hs
  -- Show any finset T has gcd(T) as an integer linear combination of elements of T
  have hgcd_closed : ∀ U : Finset ℕ, (∀ a ∈ U, ∀ s ∈ S, s + (a : ZMod d) ∈ S) →
      ∀ s ∈ S, s + ((U.gcd id : ℕ) : ZMod d) ∈ S := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro _ s hs; simpa using hs
    | insert a U ha ih =>
      intro hU
      have ha_cl : ∀ s ∈ S, s + (a : ZMod d) ∈ S := hU a (Finset.mem_insert_self a U)
      have hU_cl : ∀ s ∈ S, s + ((U.gcd id : ℕ) : ZMod d) ∈ S :=
        ih fun b hb => hU b (Finset.mem_insert_of_mem hb)
      rw [Finset.gcd_insert]
      intro s hs
      have hbez := Nat.gcd_eq_gcd_ab a (U.gcd id)
      have hcast : (((Nat.gcd a (U.gcd id) : ℕ) : ZMod d)) =
          (Nat.gcdA a (U.gcd id) : ZMod d) * (a : ZMod d) +
          (Nat.gcdB a (U.gcd id) : ZMod d) * ((U.gcd id : ℕ) : ZMod d) := by
        have h := congrArg (fun z : ℤ => (z : ZMod d)) hbez
        push_cast at h
        simpa [mul_comm] using h
      have h1 := hmul_int (a : ZMod d) ha_cl (Nat.gcdA a (U.gcd id)) s hs
      have h2 := hmul_int ((U.gcd id : ℕ) : ZMod d) hU_cl (Nat.gcdB a (U.gcd id)) _ h1
      have heq : s + ((Nat.gcd a (U.gcd id) : ℕ) : ZMod d) =
          s + (Nat.gcdA a (U.gcd id) : ZMod d) * (a : ZMod d) +
          (Nat.gcdB a (U.gcd id) : ZMod d) * ((U.gcd id : ℕ) : ZMod d) := by
        rw [hcast, add_assoc]
      change s + ((Nat.gcd a (U.gcd id) : ℕ) : ZMod d) ∈ S
      rw [heq]; exact h2
  have hTgcd := hgcd_closed T hT
  have hd_cl : ∀ s ∈ S, s + (d : ZMod d) ∈ S := fun s hs => by simpa using hs
  intro s hs
  have hbez := Nat.gcd_eq_gcd_ab d (T.gcd id)
  have hcast : (((Nat.gcd d (T.gcd id) : ℕ) : ZMod d)) =
      (Nat.gcdB d (T.gcd id) : ZMod d) * ((T.gcd id : ℕ) : ZMod d) := by
    have h := congrArg (fun z : ℤ => (z : ZMod d)) hbez
    push_cast at h
    simpa [ZMod.natCast_self, mul_comm] using h
  rw [hcast]
  exact hmul_int ((T.gcd id : ℕ) : ZMod d) hTgcd (Nat.gcdB d (T.gcd id)) s hs

lemma subsetSumsMod_eq_univ_of_diverse :
    ∀ (d : ℕ) [NeZero d] (A : Finset ℕ),
      (∀ d' : ℕ, d' ∣ d → 2 ≤ d' → d' - 1 ≤ (A.filter (fun a => ¬ d' ∣ a)).card) →
      subsetSumsMod d A = Finset.univ := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro _ A hdiv
    by_cases hd1 : d = 1
    · subst hd1
      apply Finset.eq_univ_of_card
      have h1 : 1 ≤ (subsetSumsMod 1 A).card :=
        Finset.card_pos.mpr ⟨0, zero_mem_subsetSumsMod 1 A⟩
      have h2 : (subsetSumsMod 1 A).card ≤ 1 := by
        simpa [ZMod.card] using Finset.card_le_univ (subsetSumsMod 1 A)
      rw [ZMod.card]; omega
    · have hd2 : 2 ≤ d := by have := NeZero.pos d; omega
      -- Greedily build B ⊆ A with |subsetSumsMod d B| ≥ |B| + 1 until either |subsetSumsMod d B| = d
      -- or no remaining element of A₀ = A.filter (¬ d ∣ ·) increases |subsetSumsMod d B|.
      set A₀ := A.filter (fun a => ¬ d ∣ a)
      have hA₀_card : d - 1 ≤ A₀.card := hdiv d dvd_rfl hd2
      have hloop : ∀ k ≤ d - 1, ∃ B ⊆ A₀,
          (B.card ≤ k ∧ subsetSumsMod d B = Finset.univ) ∨
          (B.card = k ∧ k + 1 ≤ (subsetSumsMod d B).card) ∨
          (B.card < k ∧ ∀ a ∈ A₀ \ B, ∀ s ∈ subsetSumsMod d B, s + (a : ZMod d) ∈ subsetSumsMod d B) := by
        intro k
        induction k with
        | zero =>
          intro _
          refine ⟨∅, Finset.empty_subset _, Or.inr (Or.inl ⟨by simp, ?_⟩)⟩
          exact Finset.card_pos.mpr ⟨0, zero_mem_subsetSumsMod d ∅⟩
        | succ k ihk =>
          intro hk
          obtain ⟨B, hBA₀, hcase⟩ := ihk (by omega)
          rcases hcase with ⟨hBcard, huniv⟩ | ⟨hBcard, hScard⟩ | ⟨hBcard, hclosed⟩
          · exact ⟨B, hBA₀, Or.inl ⟨by omega, huniv⟩⟩
          · by_cases hcan : ∃ a ∈ A₀ \ B, ∃ s ∈ subsetSumsMod d B, s + (a : ZMod d) ∉ subsetSumsMod d B
            · obtain ⟨a, ha, s, hs, hnot⟩ := hcan
              have haA₀ : a ∈ A₀ := (Finset.mem_sdiff.mp ha).1
              have haB : a ∉ B := (Finset.mem_sdiff.mp ha).2
              refine ⟨insert a B, Finset.insert_subset haA₀ hBA₀, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
              · rw [Finset.card_insert_of_notMem haB, hBcard]
              · have hsub_s : subsetSumsMod d B ⊂ subsetSumsMod d (insert a B) := by
                  rw [subsetSumsMod_insert d haB]
                  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, fun heq => ?_⟩
                  have hmem : s + (a : ZMod d) ∈ subsetSumsMod d B ∪ (subsetSumsMod d B).image (· + (a : ZMod d)) :=
                    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
                  exact hnot (heq ▸ hmem)
                have hlt := Finset.card_lt_card hsub_s
                omega
            · push Not at hcan
              exact ⟨B, hBA₀, Or.inr (Or.inr ⟨by omega, hcan⟩)⟩
          · exact ⟨B, hBA₀, Or.inr (Or.inr ⟨by omega, hclosed⟩)⟩
      obtain ⟨B, hBA₀, hres⟩ := hloop (d - 1) le_rfl
      have hBA : B ⊆ A := hBA₀.trans (Finset.filter_subset _ _)
      rcases hres with ⟨_, huniv⟩ | ⟨_, hScard⟩ | ⟨hBlt, hclosed⟩
      · exact Finset.eq_univ_iff_forall.mpr fun x => subsetSumsMod_mono d hBA (huniv ▸ Finset.mem_univ x)
      · have hcard : (subsetSumsMod d B).card = Fintype.card (ZMod d) := by
          have hle : (subsetSumsMod d B).card ≤ d := by simpa [ZMod.card] using Finset.card_le_univ (subsetSumsMod d B)
          rw [ZMod.card]; omega
        have huniv := Finset.eq_univ_of_card _ hcard
        exact Finset.eq_univ_iff_forall.mpr fun x => subsetSumsMod_mono d hBA (huniv ▸ Finset.mem_univ x)
      · -- B.card < d - 1 ≤ A₀.card, so R = A₀ \ B is nonempty!
        set R := A₀ \ B
        have hR_ne : R.Nonempty := by
          have hcard : B.card < A₀.card := by omega
          exact Finset.sdiff_nonempty.mpr fun hsub => by have := Finset.card_le_card hsub; omega
        set g := Nat.gcd d (R.gcd id)
        have hgd : g ∣ d := Nat.gcd_dvd_left _ _
        have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hgd (NeZero.pos d)
        have : NeZero g := ⟨hg_pos.ne'⟩
        have hg_lt : g < d := by
          obtain ⟨r, hr⟩ := hR_ne
          have hr_ndvd : ¬ d ∣ r := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1).2
          have hg_dvd_r : g ∣ r := (Nat.gcd_dvd_right d (R.gcd id)).trans (Finset.gcd_dvd hr)
          have hle : g ≤ d := Nat.le_of_dvd (NeZero.pos d) hgd
          by_contra hge
          have heq : g = d := by omega
          exact hr_ndvd (heq ▸ hg_dvd_r)
        have hcl_g : ∀ s ∈ subsetSumsMod d B, s + (g : ZMod d) ∈ subsetSumsMod d B :=
          add_closure_zmultiples R hclosed
        -- Closed under +k*g for all k : ℕ
        have hcl_kg : ∀ k : ℕ, ∀ s ∈ subsetSumsMod d B, s + ((k * g : ℕ) : ZMod d) ∈ subsetSumsMod d B := by
          intro k
          induction k with
          | zero => intro s hs; simpa using hs
          | succ k ihk =>
            intro s hs
            have h1 := hcl_g _ (ihk s hs)
            have heq : s + ((k * g : ℕ) : ZMod d) + (g : ZMod d) = s + (((k + 1) * g : ℕ) : ZMod d) := by
              push_cast; ring
            rwa [heq] at h1
        -- Every a ∈ A \ B is divisible by g!
        have hall_g : ∀ a ∈ A, a ∉ B → g ∣ a := by
          intro a haA haB
          by_cases hda : d ∣ a
          · exact hgd.trans hda
          · have haR : a ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨haA, hda⟩, haB⟩
            exact (Nat.gcd_dvd_right d (R.gcd id)).trans (Finset.gcd_dvd haR)
        -- By IH on g < d, subsetSumsMod g A = Finset.univ
        have hg_univ : subsetSumsMod g A = Finset.univ :=
          ih g hg_lt A (fun d' hd'g hd'2 => hdiv d' (hd'g.trans hgd) hd'2)
        -- Hence subsetSumsMod g B = Finset.univ (elements of A \ B are 0 mod g)
        have hg_B_univ : subsetSumsMod g B = Finset.univ := by
          rw [Finset.eq_univ_iff_forall]
          intro u
          have hu : u ∈ subsetSumsMod g A := hg_univ ▸ Finset.mem_univ u
          obtain ⟨C, hCA, rfl⟩ := Finset.mem_image.mp hu
          refine Finset.mem_image.mpr ⟨C ∩ B, Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
          have hC_split : C = (C ∩ B) ∪ (C \ B) := by
            ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
          have hdisj : Disjoint (C ∩ B) (C \ B) :=
            Disjoint.mono_left Finset.inter_subset_right Finset.disjoint_sdiff
          conv_rhs => rw [hC_split]
          rw [Finset.sum_union hdisj, Nat.cast_add]
          have hzero : ((∑ x ∈ C \ B, x : ℕ) : ZMod g) = 0 := by
            rw [natCast_sum_zmod]
            refine Finset.sum_eq_zero fun x hx => ?_
            have hxC := (Finset.mem_sdiff.mp hx).1
            have hxB := (Finset.mem_sdiff.mp hx).2
            exact (ZMod.natCast_eq_zero_iff x g).mpr (hall_g x (Finset.mem_powerset.mp hCA hxC) hxB)
          rw [hzero, add_zero]
        -- Now prove every z : ZMod d is in subsetSumsMod d B ⊆ subsetSumsMod d A!
        rw [Finset.eq_univ_iff_forall]
        intro z
        apply subsetSumsMod_mono d hBA
        have hz_g : ZMod.castHom hgd (ZMod g) z ∈ subsetSumsMod g B := hg_B_univ ▸ Finset.mem_univ _
        obtain ⟨C, hCB, hCeq⟩ := Finset.mem_image.mp hz_g
        set s : ZMod d := ((∑ x ∈ C, x : ℕ) : ZMod d)
        have hs_mem : s ∈ subsetSumsMod d B := Finset.mem_image.mpr ⟨C, hCB, rfl⟩
        have hdiff_zero : ZMod.castHom hgd (ZMod g) (z - s) = 0 := by
          rw [map_sub, ← hCeq]
          have hs_cast : ZMod.castHom hgd (ZMod g) s = ((∑ x ∈ C, x : ℕ) : ZMod g) := by
            dsimp [s]; exact map_natCast (ZMod.castHom hgd (ZMod g)) _
          rw [hs_cast, sub_self]
        -- Since castHom hgd (z - s) = 0, g ∣ (z - s).val!
        have hdvd_val : g ∣ (z - s).val := by
          rw [← ZMod.natCast_eq_zero_iff]
          have h1 : ((z - s).val : ZMod d) = z - s := ZMod.natCast_zmod_val (z - s)
          have h2 : ZMod.castHom hgd (ZMod g) (((z - s).val : ℕ) : ZMod d) = ((z - s).val : ZMod g) := by simp
          rw [← h2, h1, hdiff_zero]
        obtain ⟨k, hk⟩ := hdvd_val
        have hz_eq : z = s + ((k * g : ℕ) : ZMod d) := by
          have h1 : ((z - s).val : ZMod d) = z - s := ZMod.natCast_zmod_val (z - s)
          rw [hk, mul_comm] at h1
          rw [h1, add_sub_cancel]
        rw [hz_eq]
        exact hcl_kg k s hs_mem

lemma card_coset_fiber_ge {t g : ℕ} [NeZero t] [NeZero g] (hgt : g ∣ t)
    (A : Finset ℕ) (u : ZMod g)
    (hne : ((subsetSumsMod t A).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).Nonempty) :
    (subsetSumsMod t (A.filter (fun a => g ∣ a))).card ≤
      ((subsetSumsMod t A).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).card := by
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨hs0_sum, hs0_u⟩ := Finset.mem_filter.mp hs0
  obtain ⟨B, hBA, rfl⟩ := Finset.mem_image.mp hs0_sum
  set Ag := A.filter (fun a => g ∣ a)
  set B' := B \ Ag
  have hB'_sub : B' ⊆ A := Finset.sdiff_subset.trans (Finset.mem_powerset.mp hBA)
  have hB'_disj : Disjoint B' Ag := Finset.sdiff_disjoint
  set x0 : ZMod t := ((∑ a ∈ B', a : ℕ) : ZMod t)
  have hx0_u : ZMod.castHom hgt (ZMod g) x0 = u := by
    have hB_split : B = B' ∪ (B ∩ Ag) := by
      ext a; simp only [B', Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
    have hdisj : Disjoint B' (B ∩ Ag) := Disjoint.mono_right Finset.inter_subset_right Finset.sdiff_disjoint
    have hsum_eq : ∑ a ∈ B, a = ∑ a ∈ B', a + ∑ a ∈ B ∩ Ag, a := by
      conv_lhs => rw [hB_split]
      exact Finset.sum_union hdisj
    rw [hsum_eq, Nat.cast_add, map_add] at hs0_u
    have hzero : ZMod.castHom hgt (ZMod g) ((∑ a ∈ B ∩ Ag, a : ℕ) : ZMod t) = 0 := by
      rw [map_natCast, natCast_sum_zmod]
      refine Finset.sum_eq_zero fun a ha => ?_
      exact (ZMod.natCast_eq_zero_iff a g).mpr (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2
    rw [hzero, add_zero] at hs0_u
    exact hs0_u
  have hmaps : ∀ y ∈ subsetSumsMod t Ag,
      x0 + y ∈ (subsetSumsMod t A).filter (fun s => ZMod.castHom hgt (ZMod g) s = u) := by
    intro y hy
    obtain ⟨C, hCAg, rfl⟩ := Finset.mem_image.mp hy
    have hCAg' : C ⊆ Ag := Finset.mem_powerset.mp hCAg
    have hdisjC : Disjoint B' C := Disjoint.mono_right hCAg' hB'_disj
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨B' ∪ C,
      Finset.mem_powerset.mpr (Finset.union_subset hB'_sub (hCAg'.trans (Finset.filter_subset _ _))), ?_⟩, ?_⟩
    · rw [Finset.sum_union hdisjC, Nat.cast_add]
    · rw [map_add, hx0_u]
      have hzero : ZMod.castHom hgt (ZMod g) ((∑ a ∈ C, a : ℕ) : ZMod t) = 0 := by
        rw [map_natCast, natCast_sum_zmod]
        refine Finset.sum_eq_zero fun a ha => ?_
        exact (ZMod.natCast_eq_zero_iff a g).mpr (Finset.mem_filter.mp (hCAg' ha)).2
      rw [hzero, add_zero]
  have hinj : Set.InjOn (fun y : ZMod t => x0 + y) (subsetSumsMod t Ag : Set (ZMod t)) :=
    fun y1 _ y2 _ h => add_left_cancel h
  calc (subsetSumsMod t Ag).card
      = ((subsetSumsMod t Ag).image (fun y => x0 + y)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((subsetSumsMod t A).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).card :=
        Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)

end Part2

section Part3
open Finset Nat Real
open scoped BigOperators Pointwise Classical

/- ### Section 1: Minimal Interfaces Matching `H1`, `H2`, and `Part 2` -/

private lemma nfoldSum3_zero {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    nfoldSum 0 A = {0} := rfl

private lemma nfoldSum3_one {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    nfoldSum 1 A = A := by ext x; simp [nfoldSum, Finset.mem_add]

private lemma nfoldSum3_two {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    nfoldSum 2 A = A + A := by rw [nfoldSum, nfoldSum3_one]

private lemma nfoldSum3_add {G : Type*} [AddCommMonoid G] [DecidableEq G] (a b : ℕ) (A : Finset G) :
    nfoldSum (a + b) A = nfoldSum a A + nfoldSum b A := by
  induction b with
  | zero => ext x; simp [nfoldSum, Finset.mem_add]
  | succ b ih => rw [← Nat.add_assoc, nfoldSum, ih, nfoldSum, add_assoc]

private lemma nfoldSum3_mul {G : Type*} [AddCommMonoid G] [DecidableEq G] (a b : ℕ) (A : Finset G) :
    nfoldSum (a * b) A = nfoldSum a (nfoldSum b A) := by
  induction a with
  | zero => simp [nfoldSum]
  | succ a ih => rw [Nat.succ_mul, nfoldSum3_add, ih, nfoldSum]

private lemma zero_mem_nfoldSum3 {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A : Finset G} (h0 : (0 : G) ∈ A) (k : ℕ) : (0 : G) ∈ nfoldSum k A := by
  induction k with
  | zero => simp [nfoldSum]
  | succ k ih => exact Finset.mem_add.mpr ⟨0, ih, 0, h0, add_zero 0⟩

private lemma nfoldSum3_le_mono {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A : Finset G} (h0 : (0 : G) ∈ A) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    nfoldSum k₁ A ⊆ nfoldSum k₂ A := by
  have heq : k₂ = k₁ + (k₂ - k₁) := (Nat.add_sub_cancel' hk).symm
  rw [heq, nfoldSum3_add]
  intro x hx
  exact Finset.mem_add.mpr ⟨x, hx, 0, zero_mem_nfoldSum3 h0 (k₂ - k₁), add_zero x⟩

private lemma zero_mem_Gset3 {m : ℕ} [NeZero m] (A : Finset (ZMod m)) (d : ℕ) :
    (0 : ZMod m) ∈ Gset A d := by
  rw [Gset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have : A.image (· + (0 : ZMod m)) = A := by simp
  rw [this, Finset.sdiff_self, Finset.card_empty]
  exact Nat.zero_le d

/- ### Section 2: Subgroups of `ZMod m` via `ZMod.castHom` -/

lemma subgroup_zmod_eq_ker {m : ℕ} [NeZero m] (H : AddSubgroup (ZMod m)) :
    ∃ (q : ℕ) (hq : q ∣ m), 1 ≤ q ∧ Nat.card H = m / q ∧
      ∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0 := by
  have hm_pos : 0 < m := NeZero.pos m
  have hcard_dvd : Nat.card H ∣ m :=
    ⟨H.index, by have h := AddSubgroup.card_mul_index H; rw [Nat.card_zmod] at h; exact h.symm⟩
  have hH_pos : 0 < Nat.card H := Nat.pos_of_dvd_of_pos hcard_dvd hm_pos
  set q : ℕ := m / Nat.card H
  have hqm : q * Nat.card H = m := Nat.div_mul_cancel hcard_dvd
  have hq_dvd : q ∣ m := ⟨Nat.card H, by linarith⟩
  have hq_pos : 1 ≤ q := Nat.div_pos (Nat.le_of_dvd hm_pos hcard_dvd) hH_pos
  have : NeZero q := ⟨by omega⟩
  have hH_eq_div : Nat.card H = m / q :=
    (Nat.div_eq_of_eq_mul_right (by omega : 0 < q) (by linarith)).symm
  let proj : ZMod m →+* ZMod q := ZMod.castHom hq_dvd (ZMod q)
  have hH_le_ker : H ≤ proj.toAddMonoidHom.ker := by
    intro h hh
    rw [AddMonoidHom.mem_ker]
    have hord : (Nat.card H) • (⟨h, hh⟩ : H) = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (by
      have := addOrderOf_dvd_natCard (⟨h, hh⟩ : H)
      exact this)
    have hval0 : (Nat.card H) • h = 0 := by
      have hsub := congrArg Subtype.val hord
      simpa only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] using hsub
    have hm_dvd : m ∣ Nat.card H * h.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, ← nsmul_eq_mul]
      exact hval0
    have hq_dvd_val : q ∣ h.val := by
      obtain ⟨k, hk⟩ := hm_dvd
      refine ⟨k, ?_⟩
      have h1 : Nat.card H * h.val = Nat.card H * (q * k) := by
        calc Nat.card H * h.val = m * k := hk
          _ = (q * Nat.card H) * k := by rw [hqm]
          _ = Nat.card H * (q * k) := by ring
      exact Nat.eq_of_mul_eq_mul_left hH_pos h1
    have hcast : proj.toAddMonoidHom h = ((h.val : ℕ) : ZMod q) := by
      change proj h = ((h.val : ℕ) : ZMod q)
      have h1 := ZMod.natCast_zmod_val h
      conv_lhs => rw [← h1]
      exact map_natCast proj h.val
    rw [hcast, ZMod.natCast_eq_zero_iff]
    exact hq_dvd_val
  have hproj_surj : Function.Surjective proj.toAddMonoidHom := by
    intro y
    refine ⟨(y.val : ZMod m), ?_⟩
    change proj (y.val : ZMod m) = y
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hker_card : Nat.card proj.toAddMonoidHom.ker = Nat.card H := by
    have hmul := AddSubgroup.card_mul_index proj.toAddMonoidHom.ker
    rw [Nat.card_zmod] at hmul
    have hidx : proj.toAddMonoidHom.ker.index = q := by
      have hq_equiv := QuotientAddGroup.quotientKerEquivOfSurjective proj.toAddMonoidHom hproj_surj
      have h1 : Nat.card (ZMod m ⧸ proj.toAddMonoidHom.ker) = Nat.card (ZMod q) := Nat.card_congr hq_equiv.toEquiv
      rw [Nat.card_zmod] at h1
      exact h1
    rw [hidx] at hmul
    have h2 : Nat.card proj.toAddMonoidHom.ker * q = Nat.card H * q := by linarith
    exact Nat.eq_of_mul_eq_mul_right (by omega) h2
  have hH_eq_ker : H = proj.toAddMonoidHom.ker := by
    have hsub : (H : Set (ZMod m)) ⊆ (proj.toAddMonoidHom.ker : Set (ZMod m)) := hH_le_ker
    have hcard_fin : ((H : Set (ZMod m)).toFinset).card = ((proj.toAddMonoidHom.ker : Set (ZMod m)).toFinset).card := by
      have h1 : ((H : Set (ZMod m)).toFinset).card = Nat.card H := by
        rw [Nat.card_eq_fintype_card]; exact Set.toFinset_card (H : Set (ZMod m))
      have h2 : ((proj.toAddMonoidHom.ker : Set (ZMod m)).toFinset).card = Nat.card proj.toAddMonoidHom.ker := by
        rw [Nat.card_eq_fintype_card]
        exact (Set.toFinset_card (proj.toAddMonoidHom.ker : Set (ZMod m))).trans (Fintype.card_congr (Equiv.refl _))
      omega
    have hsub_fin : (H : Set (ZMod m)).toFinset ⊆ (proj.toAddMonoidHom.ker : Set (ZMod m)).toFinset := by
      intro x hx; rw [Set.mem_toFinset] at hx ⊢; exact hsub hx
    have heq_fin := Finset.eq_of_subset_of_card_le hsub_fin hcard_fin.ge
    ext x
    have hx1 : x ∈ H ↔ x ∈ (H : Set (ZMod m)).toFinset := by rw [Set.mem_toFinset]; rfl
    have hx2 : x ∈ proj.toAddMonoidHom.ker ↔ x ∈ (proj.toAddMonoidHom.ker : Set (ZMod m)).toFinset := by
      rw [Set.mem_toFinset]; rfl
    rw [hx1, hx2, heq_fin]
  refine ⟨q, hq_dvd, hq_pos, hH_eq_div, fun x => ?_⟩
  rw [hH_eq_ker, AddMonoidHom.mem_ker]
  rfl

lemma proper_subgroup_iff_two_le_q {m q : ℕ} [NeZero m] (hq : q ∣ m) (hq1 : 1 ≤ q)
    (H : AddSubgroup (ZMod m)) (hH : ∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0) :
    H ≠ ⊤ ↔ 2 ≤ q := by
  have : NeZero q := ⟨by omega⟩
  constructor
  · intro hne
    by_contra hlt
    have hq_eq1 : q = 1 := by omega
    subst hq_eq1
    apply hne
    ext x
    simp only [AddSubgroup.mem_top, iff_true, hH]
    exact Subsingleton.elim _ _
  · intro hq2 htop
    have h1 : (1 : ZMod m) ∈ H := htop ▸ AddSubgroup.mem_top (1 : ZMod m)
    have h0 := (hH 1).mp h1
    simp only [map_one] at h0
    have hne0 : (1 : ZMod q) ≠ 0 := by
      have : Fact (1 < q) := ⟨by omega⟩
      exact one_ne_zero
    exact hne0 h0

/- ### Section 3: Interval Shrinking in `ZMod q` -/

private def inZModInterval (q a b : ℕ) (z : ZMod q) : Prop :=
  ∃ k : ℤ, -(a : ℤ) ≤ k ∧ k ≤ (b : ℤ) ∧ (k : ZMod q) = z

private lemma shrink_interval_step {q a b : ℕ} (hq : 2 * (a + b) < q) {z : ZMod q}
    (hz : inZModInterval q a b z) (h2z : inZModInterval q a b (2 * z)) :
    inZModInterval q (a / 2) (b / 2) z := by
  obtain ⟨k, hka, hkb, rfl⟩ := hz
  obtain ⟨k', hk'a, hk'b, hk'eq⟩ := h2z
  have hzero : ((2 * k - k' : ℤ) : ZMod q) = 0 := by
    push_cast
    rw [hk'eq, sub_self]
  have hdvd : (q : ℤ) ∣ (2 * k - k') := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * k - k') q).mp hzero
  have hdiff_eq : 2 * k - k' = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    have hbound1 : 2 * k - k' < (q : ℤ) := by omega
    have hbound2 : -(q : ℤ) < 2 * k - k' := by omega
    by_contra hne
    have hc0 : c ≠ 0 := fun h0 => hne (by rw [hc, h0, mul_zero])
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · have : (q : ℤ) * c ≤ -(q : ℤ) := by nlinarith
      linarith
    · have : (q : ℤ) ≤ (q : ℤ) * c := by nlinarith
      linarith
  have h2k_eq : 2 * k = k' := by omega
  refine ⟨k, ?_, ?_, rfl⟩ <;> omega

private lemma shrink_interval_pow {q a b : ℕ} (hq : 2 * (a + b) < q) :
    ∀ h : ℕ, ∀ z : ZMod q,
      (∀ t ≤ h, inZModInterval q a b ((2 ^ t : ℕ) * z)) →
      inZModInterval q (a / 2 ^ h) (b / 2 ^ h) z := by
  intro h
  induction h with
  | zero =>
    intro z hz
    simpa using hz 0 le_rfl
  | succ h ih =>
    intro z hz
    have h1 : inZModInterval q (a / 2 ^ h) (b / 2 ^ h) z :=
      ih z (fun t ht => hz t (by omega))
    have h2 : inZModInterval q (a / 2 ^ h) (b / 2 ^ h) (2 * z) := by
      refine ih (2 * z) fun t ht => ?_
      have heq : ((2 ^ t : ℕ) : ZMod q) * (2 * z) = ((2 ^ (t + 1) : ℕ) : ZMod q) * z := by
        rw [pow_succ]; push_cast; ring
      rw [heq]
      exact hz (t + 1) (by omega)
    have hq' : 2 * (a / 2 ^ h + b / 2 ^ h) < q := by
      have ha : a / 2 ^ h ≤ a := Nat.div_le_self a _
      have hb : b / 2 ^ h ≤ b := Nat.div_le_self b _
      omega
    have hstep := shrink_interval_step hq' h1 h2
    rwa [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ] at hstep

/- ### Section 4: Structure Lemma (CFP21 Lemma 5.6 / `lem:structure`) -/

private lemma two_rpow_102_le_204 : (2 : ℝ) ^ (1.02 : ℝ) ≤ 2.04 := by
  have h50 : ((2 : ℝ) ^ (1.02 : ℝ)) ^ (50 : ℕ) ≤ (2.04 : ℝ) ^ (50 : ℕ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (1.02 : ℝ)) 50, ← Real.rpow_mul (by norm_num)]
    norm_num
  exact le_of_pow_le_pow_left₀ (by decide : 50 ≠ 0) (by norm_num) h50

private lemma two_rpow_306_le_ten : (2 : ℝ) ^ (3.06 : ℝ) ≤ 10 := by
  have h50 : ((2 : ℝ) ^ (3.06 : ℝ)) ^ (50 : ℕ) ≤ (10 : ℝ) ^ (50 : ℕ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (3.06 : ℝ)) 50, ← Real.rpow_mul (by norm_num)]
    norm_num
  exact le_of_pow_le_pow_left₀ (by decide : 50 ≠ 0) (by norm_num) h50

private lemma three_coset_subgroup {q : ℕ} [NeZero q] {S : Finset (ZMod q)}
    (h0 : (0 : ZMod q) ∈ S) (h2 : 2 ≤ S.card) (h4 : (nfoldSum 4 S).card ≤ 3) :
    ∃ K : AddSubgroup (ZMod q), Nat.card K ≤ 3 ∧ ∀ s ∈ S, s ∈ K := by
  -- Pick a nonzero element s₁ ∈ S
  have hex : ∃ s₁ ∈ S, s₁ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsub : S ⊆ {0} := fun x hx => Finset.mem_singleton.mpr (hall x hx)
    have := Finset.card_le_card hsub
    simp at this; omega
  obtain ⟨s₁, hs₁, hs₁_ne⟩ := hex
  have hS_sub_2S : S ⊆ nfoldSum 2 S := by simpa [nfoldSum3_one] using nfoldSum3_le_mono h0 (by decide : 1 ≤ 2)
  have h2S_sub_4S : nfoldSum 2 S ⊆ nfoldSum 4 S := nfoldSum3_le_mono h0 (by decide)
  -- Show every element of S lies in {0, s₁, -s₁} and 3 * s₁ = 0 or 2 * s₁ = 0
  have h2s₁ : s₁ + s₁ ∈ nfoldSum 4 S :=
    h2S_sub_4S (by rw [nfoldSum3_two]; exact Finset.mem_add.mpr ⟨s₁, hs₁, s₁, hs₁, rfl⟩)
  have h3s₁ : s₁ + s₁ + s₁ ∈ nfoldSum 4 S := by
    have h1 : s₁ + s₁ + s₁ ∈ nfoldSum 3 S := by
      rw [nfoldSum, nfoldSum3_two]
      exact Finset.mem_add.mpr ⟨s₁ + s₁, Finset.mem_add.mpr ⟨s₁, hs₁, s₁, hs₁, rfl⟩, s₁, hs₁, rfl⟩
    exact nfoldSum3_le_mono h0 (by decide : 3 ≤ 4) h1
  have hord_le3 : s₁ + s₁ = 0 ∨ s₁ + s₁ + s₁ = 0 := by
    by_contra hneither
    push Not at hneither
    have hsub : ({0, s₁, s₁ + s₁, s₁ + s₁ + s₁} : Finset (ZMod q)) ⊆ nfoldSum 4 S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact zero_mem_nfoldSum3 h0 4
      · exact h2S_sub_4S (hS_sub_2S hs₁)
      · exact h2s₁
      · exact h3s₁
    have hne1 : (0 : ZMod q) ≠ s₁ := hs₁_ne.symm
    have hne2 : (0 : ZMod q) ≠ s₁ + s₁ := Ne.symm hneither.1
    have hne3 : (0 : ZMod q) ≠ s₁ + s₁ + s₁ := Ne.symm hneither.2
    have hne4 : s₁ ≠ s₁ + s₁ := fun h => hs₁_ne (by linear_combination -h)
    have hne5 : s₁ ≠ s₁ + s₁ + s₁ := fun h => hneither.1 (by linear_combination -h)
    have hne6 : s₁ + s₁ ≠ s₁ + s₁ + s₁ := fun h => hs₁_ne (by linear_combination -h)
    have hcard4 : ({0, s₁, s₁ + s₁, s₁ + s₁ + s₁} : Finset (ZMod q)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hne1, hne2, hne3]),
        Finset.card_insert_of_notMem (by simp [hne4, hne5]),
        Finset.card_insert_of_notMem (by simp [hne6]), Finset.card_singleton]
    have := Finset.card_le_card hsub
    omega
  -- Now show every s ∈ S is in AddSubgroup.zmultiples s₁!
  have hall_in : ∀ s ∈ S, s ∈ AddSubgroup.zmultiples s₁ := by
    intro s hs
    by_cases hs0 : s = 0
    · subst hs0; exact zero_mem _
    · by_cases hss1 : s = s₁
      · rw [hss1]; exact AddSubgroup.mem_zmultiples s₁
      · -- {0, s₁, s, s₁ + s} ⊆ 2S ⊆ 4S has card ≤ 3!
        have hsub : ({0, s₁, s, s₁ + s} : Finset (ZMod q)) ⊆ nfoldSum 4 S := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact zero_mem_nfoldSum3 h0 4
          · exact h2S_sub_4S (hS_sub_2S hs₁)
          · exact h2S_sub_4S (hS_sub_2S hs)
          · exact h2S_sub_4S (by rw [nfoldSum3_two]; exact Finset.mem_add.mpr ⟨s₁, hs₁, s, hs, rfl⟩)
        have hsum0 : s₁ + s = 0 := by
          by_contra hne0
          have hne1 : s₁ + s ≠ s₁ := fun h => hs0 (by linear_combination h)
          have hne2 : s₁ + s ≠ s := fun h => hs₁_ne (by linear_combination h)
          have hcard4 : ({0, s₁, s, s₁ + s} : Finset (ZMod q)).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [hs₁_ne.symm, Ne.symm hs0, Ne.symm hne0]),
              Finset.card_insert_of_notMem (by simp [Ne.symm hss1, Ne.symm hne1]),
              Finset.card_insert_of_notMem (by simp [Ne.symm hne2]), Finset.card_singleton]
          have := Finset.card_le_card hsub
          omega
        have hs_eq : s = -s₁ := by linear_combination hsum0
        rw [hs_eq]
        exact neg_mem (AddSubgroup.mem_zmultiples s₁)
  refine ⟨AddSubgroup.zmultiples s₁, ?_, hall_in⟩
  -- Card of zmultiples s₁ ≤ 3 because 2*s₁ = 0 or 3*s₁ = 0!
  have hsub_fin : ((AddSubgroup.zmultiples s₁ : Set (ZMod q)).toFinset) ⊆ {0, s₁, s₁ + s₁} := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hord_le3 with h2_0 | h3_0
    · have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
      have hdiv : k = 2 * (k / 2) + k % 2 := by omega
      rw [hdiv, add_zsmul, mul_zsmul]
      have h2z : (2 : ℤ) • s₁ = 0 := by rw [two_zsmul]; exact h2_0
      rw [zsmul_comm, h2z, zsmul_zero, zero_add]
      rcases hmod with h0' | h1'
      · left; simp [h0']
      · right; left; simp [h1']
    · have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      have hdiv : k = 3 * (k / 3) + k % 3 := by omega
      rw [hdiv, add_zsmul, mul_zsmul]
      have h3z : (3 : ℤ) • s₁ = 0 := by
        rw [show (3 : ℤ) = 1 + 1 + 1 by norm_num, add_zsmul, add_zsmul, one_zsmul]; exact h3_0
      rw [zsmul_comm, h3z, zsmul_zero, zero_add]
      rcases hmod with h0' | h1' | h2'
      · left; simp [h0']
      · right; left; simp [h1']
      · right; right; rw [h2', two_zsmul]
  have hcard_le : ((AddSubgroup.zmultiples s₁ : Set (ZMod q)).toFinset).card ≤ 3 :=
    (Finset.card_le_card hsub_fin).trans (by
      calc ({0, s₁, s₁ + s₁} : Finset (ZMod q)).card ≤ 1 + ({s₁, s₁ + s₁} : Finset (ZMod q)).card := by
            have := Finset.card_insert_le (0 : ZMod q) {s₁, s₁ + s₁}; omega
        _ ≤ 1 + (1 + ({s₁ + s₁} : Finset (ZMod q)).card) := by
            have := Finset.card_insert_le s₁ {s₁ + s₁}; omega
        _ = 3 := by simp)
  have hcard_eq : Nat.card (AddSubgroup.zmultiples s₁) =
      ((AddSubgroup.zmultiples s₁ : Set (ZMod q)).toFinset).card := by
    rw [Nat.card_eq_fintype_card]
    exact (Set.toFinset_card (AddSubgroup.zmultiples s₁ : Set (ZMod q))).symm
  omega

set_option maxHeartbeats 1200000 in
lemma structure_lemma
    {ξ : ℝ} (_hξ_pos : 0 < ξ) (hξ_lt : ξ < 1 / 100)
    (hDF : ∀ (m : ℕ) [NeZero m] (X : Finset (ZMod m)),
      X.Nonempty →
      (X.card : ℝ) ≤ ξ * (m : ℝ) →
      ((X + X).card : ℝ) ≤ 2.04 * (X.card : ℝ) →
      ∃ H : AddSubgroup (ZMod m), H ≠ ⊤ ∧
        ((∃ (x d : ZMod m) (L : ℕ), 2 ≤ L ∧
            (∀ a ∈ X, ∃ k < L, a - (x + (k : ZMod m) * d) ∈ H) ∧
            ((L - 1 : ℕ) : ℝ) * (Nat.card H : ℝ) ≤ ((X + X).card : ℝ) - (X.card : ℝ)) ∨
         (∃ (c₁ c₂ c₃ : ZMod m),
            (∀ a ∈ X, a - c₁ ∈ H ∨ a - c₂ ∈ H ∨ a - c₃ ∈ H) ∧
            (Nat.card H : ℝ) ≤ ((X + X).card : ℝ) - (X.card : ℝ)) ∨
         (∃ x : ZMod m, ∀ a ∈ X, a - x ∈ H)))
    (hCOS : ∀ (m : ℕ) [NeZero m] (X : Finset (ZMod m)) (k : ℕ),
      1 ≤ k →
      (∀ H : AddSubgroup (ZMod m), H ≠ ⊤ → ¬ ∃ x : ZMod m, ∀ a ∈ X, a - x ∈ H) →
      min (m : ℝ) (((k + 1 : ℕ) : ℝ) * (X.card : ℝ) / 2) ≤ ((nfoldSum k X).card : ℝ))
    (h_stable : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d k : ℕ),
      nfoldSum k (Gset A d) ⊆ Gset A (k * d))
    (h_dcount : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d : ℕ),
      d < A.card → ((Gset A d).card : ℝ) ≤ (A.card : ℝ) ^ 2 / ((A.card : ℝ) - (d : ℝ)))
    {m : ℕ} [NeZero m] (A : Finset (ZMod m)) {d : ℕ}
    (hd1 : 1 ≤ d) (h8d : 8 * d < A.card) (hA_small : (A.card : ℝ) < (ξ / 2) * (m : ℝ))
    (hnot_sub : ∀ H : AddSubgroup (ZMod m), H ≠ ⊤ → ¬ ∀ x ∈ Gset A d, x ∈ H) :
    ((Gset A d).card : ℝ) ≤ 20 * (A.card : ℝ) / ((A.card : ℝ) / (2 * (d : ℝ))) ^ (1.02 : ℝ) ∨
    ∃ (q : ℕ) (hq : q ∣ m) (u : (ZMod q)ˣ) (a₀ L : ℕ),
      2 ≤ q ∧ 2 ≤ L ∧ L ≤ q ∧ L * (m / q) ≤ 128 * d ∧
      ∀ x ∈ Gset A d, ∃ k < L, u.1 * ZMod.castHom hq (ZMod q) x = ((a₀ + k : ℕ) : ZMod q) := by
  set Gd := Gset A d
  have h0_Gd : (0 : ZMod m) ∈ Gd := zero_mem_Gset3 A d
  set i : ℕ := Nat.log 2 (A.card / (2 * d))
  have hdiv_ge4 : 4 ≤ A.card / (2 * d) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hi2 : 2 ≤ i := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by norm_num; omega)
  set k : ℕ := 2 ^ i
  have hk_le : k ≤ A.card / (2 * d) := Nat.pow_log_le_self 2 (by omega)
  have hkd_le : k * d ≤ A.card / 2 := by
    have h1 : k * (2 * d) ≤ A.card := (Nat.le_div_iff_mul_le (by omega)).mp hk_le
    have h2 : 2 * (k * d) = k * (2 * d) := by ring
    omega
  have h2i1_gt : A.card / (2 * d) < 2 ^ (i + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have h2i1_gt_r : (A.card : ℝ) / (2 * (d : ℝ)) < ((2 ^ (i + 1) : ℕ) : ℝ) := by
    have h1 : A.card < 2 ^ (i + 1) * (2 * d) := by
      have h2 := Nat.div_add_mod A.card (2 * d)
      have h3 := Nat.mod_lt A.card (by omega : 0 < 2 * d)
      nlinarith
    rw [div_lt_iff₀ (by positivity)]
    exact_mod_cast h1
  -- Bound |2^i Gd| ≤ 2 |A|
  have hXi_le : ((nfoldSum k Gd).card : ℝ) ≤ 2 * (A.card : ℝ) := by
    have hsub := h_stable m A d k
    have hcard_le : ((nfoldSum k Gd).card : ℝ) ≤ ((Gset A (k * d)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hkd_lt : k * d < A.card := by omega
    have hdc := h_dcount m A (k * d) hkd_lt
    have hden_ge : (A.card : ℝ) / 2 ≤ (A.card : ℝ) - ((k * d : ℕ) : ℝ) := by
      have : ((k * d : ℕ) : ℝ) ≤ (A.card : ℝ) / 2 := by
        have h2 : 2 * (k * d) ≤ A.card := by omega
        have h2r : 2 * ((k * d : ℕ) : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast h2
        linarith
      linarith
    have hA_pos : (0 : ℝ) < A.card := by exact_mod_cast (by omega : 0 < A.card)
    have hfrac : (A.card : ℝ) ^ 2 / ((A.card : ℝ) - ((k * d : ℕ) : ℝ)) ≤ 2 * (A.card : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    exact (hcard_le.trans hdc).trans hfrac
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have h2A_lt_ξm : 2 * (A.card : ℝ) < ξ * (m : ℝ) := by linarith
  -- For every j < i, X_j = 2^j Gd is not in any proper coset and satisfies |X_j| ≤ 2^(1+j-i) |X_i| < ξ m
  have hXj_not_coset : ∀ j : ℕ, ∀ H : AddSubgroup (ZMod m), H ≠ ⊤ →
      ¬ ∃ x : ZMod m, ∀ a ∈ nfoldSum (2 ^ j) Gd, a - x ∈ H := by
    intro j H hH ⟨x, hx⟩
    apply hnot_sub H hH
    intro a ha
    have h0_mem : (0 : ZMod m) ∈ nfoldSum (2 ^ j) Gd := zero_mem_nfoldSum3 h0_Gd _
    have ha_mem : a ∈ nfoldSum (2 ^ j) Gd :=
      nfoldSum3_le_mono h0_Gd (show 1 ≤ 2 ^ j from Nat.one_le_two_pow) (by rwa [nfoldSum3_one])
    have h0x : 0 - x ∈ H := hx 0 h0_mem
    have hax : a - x ∈ H := hx a ha_mem
    have heq : a = (a - x) - (0 - x) := by abel
    rw [heq]; exact sub_mem hax h0x
  have hXj_le : ∀ j < i,
      ((nfoldSum (2 ^ j) Gd).card : ℝ) * ((2 ^ (i - j - 1) : ℕ) : ℝ) ≤ ((nfoldSum k Gd).card : ℝ) := by
    intro j hj
    have hpow_mul : 2 ^ (i - j) * 2 ^ j = k := by
      dsimp [k]; rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have hmul_eq : nfoldSum (2 ^ (i - j)) (nfoldSum (2 ^ j) Gd) = nfoldSum k Gd := by
      rw [← nfoldSum3_mul, hpow_mul]
    have hcos := hCOS m (nfoldSum (2 ^ j) Gd) (2 ^ (i - j)) (Nat.one_le_two_pow) (hXj_not_coset j)
    rw [hmul_eq] at hcos
    have hlt_m : ((nfoldSum k Gd).card : ℝ) < (m : ℝ) := by
      calc ((nfoldSum k Gd).card : ℝ) ≤ 2 * (A.card : ℝ) := hXi_le
        _ < ξ * (m : ℝ) := h2A_lt_ξm
        _ < (m : ℝ) := by nlinarith
    have hnot_m : ¬ (m : ℝ) ≤ ((nfoldSum k Gd).card : ℝ) := not_le.mpr hlt_m
    have hle_half : (((2 ^ (i - j) + 1 : ℕ) : ℝ) * ((nfoldSum (2 ^ j) Gd).card : ℝ) / 2) ≤
        ((nfoldSum k Gd).card : ℝ) := by
      rcases le_total (m : ℝ) (((2 ^ (i - j) + 1 : ℕ) : ℝ) * ((nfoldSum (2 ^ j) Gd).card : ℝ) / 2) with h | h
      · rw [min_eq_left h] at hcos; exact absurd hcos hnot_m
      · rwa [min_eq_right h] at hcos
    have h2pow : 2 * 2 ^ (i - j - 1) = 2 ^ (i - j) := by
      conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ i - j by omega), pow_succ]
      ring
    have h2pow_r : (2 : ℝ) * ((2 ^ (i - j - 1) : ℕ) : ℝ) ≤ ((2 ^ (i - j) + 1 : ℕ) : ℝ) := by
      have : 2 * 2 ^ (i - j - 1) ≤ 2 ^ (i - j) + 1 := by omega
      exact_mod_cast this
    have hcard_nn : (0 : ℝ) ≤ ((nfoldSum (2 ^ j) Gd).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- Split on whether ∃ j ∈ [2, i) with |X_j + X_j| ≤ 2.04 |X_j|
  by_cases hexj : ∃ j, 2 ≤ j ∧ j < i ∧
      (((nfoldSum (2 ^ j) Gd + nfoldSum (2 ^ j) Gd).card : ℕ) : ℝ) ≤
        2.04 * ((nfoldSum (2 ^ j) Gd).card : ℝ)
  · right
    obtain ⟨j, hj2, hji, hdoub⟩ := hexj
    set Xj := nfoldSum (2 ^ j) Gd
    have hXj_ne : Xj.Nonempty := ⟨0, zero_mem_nfoldSum3 h0_Gd _⟩
    have hXj_small : (Xj.card : ℝ) ≤ ξ * (m : ℝ) := by
      have h1 := hXj_le j hji
      have hpow1 : (1 : ℝ) ≤ ((2 ^ (i - j - 1) : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
      have hcard_nn : (0 : ℝ) ≤ (Xj.card : ℝ) := Nat.cast_nonneg _
      have hle_Xi : (Xj.card : ℝ) ≤ ((nfoldSum k Gd).card : ℝ) := by nlinarith
      linarith
    obtain ⟨H, hH_ne, hDF_case⟩ := hDF m Xj hXj_ne hXj_small hdoub
    obtain ⟨q, hq_dvd, hq1, hH_card, hH_ker⟩ := subgroup_zmod_eq_ker H
    have hq2 : 2 ≤ q := (proper_subgroup_iff_two_le_q hq_dvd hq1 H hH_ker).mp hH_ne
    have : NeZero q := ⟨by omega⟩
    let proj : ZMod m →+* ZMod q := ZMod.castHom hq_dvd (ZMod q)
    rcases hDF_case with ⟨x, d0, L, hL2, hAP, hLH⟩ | ⟨c₁, c₂, c₃, h3c, hHle⟩ | ⟨x, hx⟩
    · -- Case 1: Xj is covered by an AP of H-cosets of length L with (L - 1) |H| ≤ |Xj + Xj| - |Xj| ≤ 1.04 |Xj|
      -- Step 1a: proj d0 must be a unit in ZMod q!
      have hd0_cop : Nat.Coprime (proj d0).val q := by
        by_contra hncop
        set g := Nat.gcd (proj d0).val q
        have hg_dvd_q : g ∣ q := Nat.gcd_dvd_right _ _
        have hg_dvd_d0 : g ∣ (proj d0).val := Nat.gcd_dvd_left _ _
        have hg2 : 2 ≤ g := by
          have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
          have hg_ne1 : g ≠ 1 := hncop
          omega
        have hg_dvd_m : g ∣ m := hg_dvd_q.trans hq_dvd
        have : NeZero g := ⟨by omega⟩
        let K : AddSubgroup (ZMod m) := (ZMod.castHom hg_dvd_m (ZMod g)).toAddMonoidHom.ker
        have hK_ne : K ≠ ⊤ :=
          (proper_subgroup_iff_two_le_q hg_dvd_m (by omega) K (fun _ => Iff.rfl)).mpr hg2
        apply hXj_not_coset j K hK_ne
        refine ⟨x, fun a ha => ?_⟩
        obtain ⟨r, _, har⟩ := hAP a ha
        have hproj_eq : proj (a - x) = (r : ZMod q) * proj d0 := by
          have h0 : proj (a - (x + (r : ZMod m) * d0)) = 0 := (hH_ker _).mp har
          have hsub : proj (a - (x + (r : ZMod m) * d0)) = proj (a - x) - (r : ZMod q) * proj d0 := by
            simp only [map_sub, map_add, map_mul, map_natCast]; ring
          rw [hsub, sub_eq_zero] at h0
          exact h0
        have hcast_eq : ZMod.castHom hg_dvd_m (ZMod g) (a - x) =
            ZMod.castHom hg_dvd_q (ZMod g) (proj (a - x)) := by
          dsimp [proj]
          exact RingHom.congr_fun (ZMod.castHom_comp hg_dvd_q hq_dvd).symm (a - x)
        change ZMod.castHom hg_dvd_m (ZMod g) (a - x) = 0
        rw [hcast_eq, hproj_eq, map_mul]
        have hd0_zero : ZMod.castHom hg_dvd_q (ZMod g) (proj d0) = 0 := by
          have h1 : ((proj d0).val : ZMod q) = proj d0 := ZMod.natCast_zmod_val (proj d0)
          conv_lhs => rw [← h1]
          simp only [map_natCast, ZMod.natCast_eq_zero_iff]
          exact hg_dvd_d0
        rw [hd0_zero, mul_zero]
      -- Define unit u = (proj d0)⁻¹ in (ZMod q)ˣ
      set u0 : (ZMod q)ˣ := ZMod.unitOfCoprime (proj d0).val hd0_cop
      have hu0_val : (u0 : ZMod q) = proj d0 :=
        (ZMod.coe_unitOfCoprime (proj d0).val hd0_cop).trans (ZMod.natCast_zmod_val (proj d0))
      set u : (ZMod q)ˣ := u0⁻¹
      have hu_mul : u.1 * proj d0 = 1 := by
        dsimp [u]; rw [← hu0_val]; exact Units.inv_mul u0
      -- Since 0 ∈ Xj, pick r₀ < L with u * proj(-x) = r₀, so u * proj(a) ∈ [-r₀, L - 1 - r₀] mod q!
      have h0_Xj : (0 : ZMod m) ∈ Xj := zero_mem_nfoldSum3 h0_Gd _
      obtain ⟨r₀, hr₀L, hr₀_mem⟩ := hAP 0 h0_Xj
      have hux : u.1 * proj x = -((r₀ : ℕ) : ZMod q) := by
        have h0 : proj (0 - (x + (r₀ : ZMod m) * d0)) = 0 := (hH_ker _).mp hr₀_mem
        have h1 : proj (0 - (x + (r₀ : ZMod m) * d0)) = -(proj x + (r₀ : ZMod q) * proj d0) := by
          rw [zero_sub, map_neg, map_add, map_mul, map_natCast]
        rw [h1, neg_eq_zero] at h0
        have h2 := congrArg (u.1 * ·) h0
        rw [mul_zero, mul_add, ← mul_assoc, mul_comm u.1 (r₀ : ZMod q), mul_assoc, hu_mul, mul_one] at h2
        linear_combination h2
      have hXj_int : ∀ a ∈ Xj, inZModInterval q r₀ (L - 1 - r₀) (u.1 * proj a) := by
        intro a ha
        obtain ⟨r, hrL, har⟩ := hAP a ha
        have h0 : proj (a - (x + (r : ZMod m) * d0)) = 0 := (hH_ker _).mp har
        have h1 : proj a = proj x + (r : ZMod q) * proj d0 := by
          have hsub : proj (a - (x + (r : ZMod m) * d0)) = proj a - (proj x + (r : ZMod q) * proj d0) := by
            simp only [map_sub, map_add, map_mul, map_natCast]
          rw [hsub, sub_eq_zero] at h0; exact h0
        refine ⟨(r : ℤ) - (r₀ : ℤ), by omega, by omega, ?_⟩
        rw [h1, mul_add, hux, ← mul_assoc, mul_comm u.1 (r : ZMod q), mul_assoc, hu_mul, mul_one]
        push_cast; ring
      -- Check 2 * (r₀ + (L - 1 - r₀)) = 2 * (L - 1) < q!
      have hLH_le : ((L - 1 : ℕ) : ℝ) * (Nat.card H : ℝ) ≤ 1.04 * (Xj.card : ℝ) := by linarith
      have h2L_lt_q : 2 * (r₀ + (L - 1 - r₀)) < q := by
        have hsum_eq : r₀ + (L - 1 - r₀) = L - 1 := by omega
        rw [hsum_eq]
        have hH_pos : (0 : ℝ) < (Nat.card H : ℝ) := by
          rw [hH_card]
          have : 0 < m / q := Nat.div_pos (Nat.le_of_dvd (NeZero.pos m) hq_dvd) (by omega)
          exact_mod_cast this
        have hmq : (q : ℝ) * (Nat.card H : ℝ) = (m : ℝ) := by
          rw [hH_card, ← Nat.cast_mul, Nat.mul_div_cancel' hq_dvd]
        have h1 : 2 * ((L - 1 : ℕ) : ℝ) * (Nat.card H : ℝ) ≤ 2.08 * (Xj.card : ℝ) := by linarith
        have h2 : 2.08 * (Xj.card : ℝ) < (m : ℝ) := by
          have : 2.08 * (Xj.card : ℝ) ≤ 2.08 * (ξ * (m : ℝ)) := by linarith
          nlinarith
        have h3 : (2 * ((L - 1 : ℕ) : ℝ)) * (Nat.card H : ℝ) < (q : ℝ) * (Nat.card H : ℝ) := by linarith
        have h4 : (2 * ((L - 1 : ℕ) : ℝ)) < (q : ℝ) := lt_of_mul_lt_mul_right h3 hH_pos.le
        exact_mod_cast h4
      -- Apply shrink_interval_pow to every z ∈ Gd!
      have hGd_shrink : ∀ x ∈ Gd, inZModInterval q (r₀ / 2 ^ j) ((L - 1 - r₀) / 2 ^ j) (u.1 * proj x) := by
        intro x hx
        refine shrink_interval_pow h2L_lt_q j (u.1 * proj x) fun t ht => ?_
        have hmem_t : ((2 ^ t : ℕ) : ZMod m) * x ∈ nfoldSum (2 ^ t) Gd := by
          have hgen : ∀ n : ℕ, (n : ZMod m) * x ∈ nfoldSum n Gd := by
            intro n
            induction n with
            | zero => simp [nfoldSum]
            | succ n ihn =>
              rw [nfoldSum, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
              exact Finset.mem_add.mpr ⟨(n : ZMod m) * x, ihn, x, hx, rfl⟩
          exact hgen (2 ^ t)
        have hmem_j : ((2 ^ t : ℕ) : ZMod m) * x ∈ Xj :=
          nfoldSum3_le_mono h0_Gd (Nat.pow_le_pow_right (by decide) ht) hmem_t
        have heq : ((2 ^ t : ℕ) : ZMod q) * (u.1 * proj x) = u.1 * proj (((2 ^ t : ℕ) : ZMod m) * x) := by
          rw [map_mul, map_natCast]; ring
        rw [heq]
        exact hXj_int _ hmem_j
      -- Set L₀ = r₀ / 2^j + (L - 1 - r₀) / 2^j + 1
      set aS := r₀ / 2 ^ j
      set bS := (L - 1 - r₀) / 2 ^ j
      set L₀ := aS + bS + 1
      have hL₀_ge2 : 2 ≤ L₀ := by
        by_contra hlt
        dsimp [L₀] at hlt
        have haS0 : aS = 0 := by have := Nat.zero_le aS; have := Nat.zero_le bS; omega
        have hbS0 : bS = 0 := by have := Nat.zero_le aS; have := Nat.zero_le bS; omega
        apply hnot_sub H hH_ne
        intro x hx
        obtain ⟨k', hk1, hk2, hkeq⟩ := hGd_shrink x hx
        have hk0 : k' = 0 := by omega
        rw [hk0, Int.cast_zero] at hkeq
        have hproj0 : proj x = 0 := by
          have := congrArg (u0.1 * ·) hkeq.symm
          rw [mul_zero, ← mul_assoc] at this
          have hu1 : u0.1 * u.1 = 1 := Units.mul_inv u0
          rw [hu1, one_mul] at this
          exact this
        exact (hH_ker x).mpr hproj0
      have hL₀_le_q : L₀ ≤ q := by
        have h1 : aS ≤ r₀ := Nat.div_le_self _ _
        have h2 : bS ≤ L - 1 - r₀ := Nat.div_le_self _ _
        omega
      -- Bound L₀ * (m / q) ≤ 128 * d!
      have hL₀_mul_le : L₀ * (m / q) ≤ 128 * d := by
        have hsum_div : aS + bS ≤ (L - 1) / 2 ^ j := by
          have h1 : aS * 2 ^ j + bS * 2 ^ j ≤ L - 1 := by
            have h1a : aS * 2 ^ j ≤ r₀ := Nat.div_mul_le_self r₀ (2 ^ j)
            have h1b : bS * 2 ^ j ≤ L - 1 - r₀ := Nat.div_mul_le_self (L - 1 - r₀) (2 ^ j)
            omega
          exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by linarith)
        have hL₀_le_2 : L₀ ≤ 2 * ((L - 1) / 2 ^ j) := by omega
        have hL₀_pow : L₀ * 2 ^ j ≤ 2 * (L - 1) := by
          have := Nat.div_mul_le_self (L - 1) (2 ^ j)
          nlinarith
        have hL₀_pow_r : (L₀ : ℝ) * ((2 ^ j : ℕ) : ℝ) * (Nat.card H : ℝ) ≤ 2.08 * (Xj.card : ℝ) := by
          have h1 : (L₀ : ℝ) * ((2 ^ j : ℕ) : ℝ) ≤ 2 * ((L - 1 : ℕ) : ℝ) := by exact_mod_cast hL₀_pow
          calc _ ≤ (2 * ((L - 1 : ℕ) : ℝ)) * (Nat.card H : ℝ) :=
                mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
            _ = 2 * (((L - 1 : ℕ) : ℝ) * (Nat.card H : ℝ)) := by ring
            _ ≤ 2 * (1.04 * (Xj.card : ℝ)) := by linarith
            _ = 2.08 * (Xj.card : ℝ) := by ring
        have h2i_eq : ((2 ^ j : ℕ) : ℝ) * ((2 ^ (i - j - 1) : ℕ) : ℝ) = ((2 ^ (i - 1) : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, ← pow_add, show j + (i - j - 1) = i - 1 by omega]
        have hprod_le : (L₀ : ℝ) * ((2 ^ (i - 1) : ℕ) : ℝ) * (Nat.card H : ℝ) ≤ 4.16 * (A.card : ℝ) := by
          have h1 := mul_le_mul_of_nonneg_right hL₀_pow_r (Nat.cast_nonneg (2 ^ (i - j - 1)))
          have h2 := hXj_le j hji
          have hrew : (L₀ : ℝ) * ((2 ^ j : ℕ) : ℝ) * (Nat.card H : ℝ) * ((2 ^ (i - j - 1) : ℕ) : ℝ) =
              (L₀ : ℝ) * (((2 ^ j : ℕ) : ℝ) * ((2 ^ (i - j - 1) : ℕ) : ℝ)) * (Nat.card H : ℝ) := by ring
          rw [hrew, h2i_eq] at h1
          linarith
        have h2i1_eq : (4 : ℝ) * ((2 ^ (i - 1) : ℕ) : ℝ) = ((2 ^ (i + 1) : ℕ) : ℝ) := by
          have : 4 * 2 ^ (i - 1) = 2 ^ (i + 1) := by
            have h1 : i + 1 = (i - 1) + 2 := by omega
            rw [h1, pow_add]; ring
          exact_mod_cast this
        have hA_lt_2i : (A.card : ℝ) < (8 : ℝ) * (d : ℝ) * ((2 ^ (i - 1) : ℕ) : ℝ) := by
          have h1 := (div_lt_iff₀ (show (0 : ℝ) < 2 * (d : ℝ) by positivity)).mp h2i1_gt_r
          rw [← h2i1_eq] at h1
          linarith
        have h2im_pos : (0 : ℝ) < ((2 ^ (i - 1) : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
        have hbound_r : (L₀ : ℝ) * (Nat.card H : ℝ) ≤ 128 * (d : ℝ) := by
          have h1 : (L₀ : ℝ) * (Nat.card H : ℝ) * ((2 ^ (i - 1) : ℕ) : ℝ) <
              4.16 * (8 * (d : ℝ) * ((2 ^ (i - 1) : ℕ) : ℝ)) := by nlinarith
          have h2 : (L₀ : ℝ) * (Nat.card H : ℝ) < 4.16 * (8 * (d : ℝ)) :=
            lt_of_mul_lt_mul_right (by linarith) h2im_pos.le
          linarith
        rw [hH_card] at hbound_r
        exact_mod_cast hbound_r
      -- Express [-aS, bS] as {a₀ + k : k < L₀} mod q using a₀ = (q - aS % q) % q!
      set a₀ : ℕ := q - aS % q
      refine ⟨q, hq_dvd, u, a₀, L₀, hq2, hL₀_ge2, hL₀_le_q, hL₀_mul_le, fun x hx => ?_⟩
      obtain ⟨k', hk1, hk2, hkeq⟩ := hGd_shrink x hx
      refine ⟨(k' + (aS : ℤ)).toNat, ?_, ?_⟩
      · have hnn : 0 ≤ k' + (aS : ℤ) := by omega
        have hlt : k' + (aS : ℤ) < (L₀ : ℤ) := by dsimp [L₀]; omega
        omega
      · have hnn : 0 ≤ k' + (aS : ℤ) := by omega
        have htoNat : (((k' + (aS : ℤ)).toNat : ℕ) : ℤ) = k' + (aS : ℤ) := Int.toNat_of_nonneg hnn
        change u.1 * proj x = _
        rw [← hkeq]
        have ha₀_cast : ((a₀ : ℕ) : ZMod q) = -((aS : ℕ) : ZMod q) := by
          have hmod_le : aS % q ≤ q := (Nat.mod_lt aS (by omega)).le
          dsimp [a₀]
          rw [Nat.cast_sub hmod_le, ZMod.natCast_self, zero_sub, ZMod.natCast_mod]
        rw [Nat.cast_add, ha₀_cast]
        have hcast_k : (((k' + (aS : ℤ)).toNat : ℕ) : ZMod q) = (k' : ZMod q) + ((aS : ℕ) : ZMod q) := by
          have := congrArg (fun z : ℤ => (z : ZMod q)) htoNat
          push_cast at this
          exact this
        rw [hcast_k]; ring
    · -- Case 2: Xj meets at most 3 cosets of H and |H| ≤ |Xj + Xj| - |Xj| ≤ 1.04 |Xj|
      exfalso
      have h4Gd_sub : nfoldSum 4 Gd ⊆ Xj :=
        nfoldSum3_le_mono h0_Gd (show 4 ≤ 2 ^ j from (by decide : 4 = 2 ^ 2) ▸ Nat.pow_le_pow_right (by decide) hj2)
      set S : Finset (ZMod q) := Gd.image proj
      have h0_S : (0 : ZMod q) ∈ S := Finset.mem_image.mpr ⟨0, h0_Gd, map_zero proj⟩
      have hS_ge2 : 2 ≤ S.card := by
        by_contra hlt
        have hS1 : S = {0} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨h0_S, fun y hy => ?_⟩
          by_contra hy0
          have hsub : ({0, y} : Finset (ZMod q)) ⊆ S := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          have h2 : ({0, y} : Finset (ZMod q)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [Ne.symm hy0]), Finset.card_singleton]
          have := Finset.card_le_card hsub; omega
        apply hnot_sub H hH_ne
        intro x hx
        have hmem : proj x ∈ S := Finset.mem_image.mpr ⟨x, hx, rfl⟩
        rw [hS1, Finset.mem_singleton] at hmem
        exact (hH_ker x).mpr hmem
      have h4S_le3 : (nfoldSum 4 S).card ≤ 3 := by
        have himg : nfoldSum 4 S = (nfoldSum 4 Gd).image proj := by
          have hgen : ∀ n : ℕ, nfoldSum n (Gd.image proj) = (nfoldSum n Gd).image proj := by
            intro n
            induction n with
            | zero => simp [nfoldSum]
            | succ n ihn =>
              rw [nfoldSum, nfoldSum, ihn]
              ext z; simp only [Finset.mem_add, Finset.mem_image]
              constructor
              · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
                exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, map_add proj a b⟩
              · rintro ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩
                exact ⟨proj a, ⟨a, ha, rfl⟩, proj b, ⟨b, hb, rfl⟩, (map_add proj a b).symm⟩
          exact hgen 4
        rw [himg]
        have hsub3 : (nfoldSum 4 Gd).image proj ⊆ {proj c₁, proj c₂, proj c₃} := by
          intro y hy
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases h3c a (h4Gd_sub ha) with h1 | h2 | h3
          · left; exact sub_eq_zero.mp ((map_sub proj a c₁) ▸ (hH_ker _).mp h1)
          · right; left; exact sub_eq_zero.mp ((map_sub proj a c₂) ▸ (hH_ker _).mp h2)
          · right; right; exact sub_eq_zero.mp ((map_sub proj a c₃) ▸ (hH_ker _).mp h3)
        exact (Finset.card_le_card hsub3).trans (by
          calc ({proj c₁, proj c₂, proj c₃} : Finset (ZMod q)).card ≤ 1 + ({proj c₂, proj c₃} : Finset (ZMod q)).card := by
                have := Finset.card_insert_le (proj c₁) {proj c₂, proj c₃}; omega
            _ ≤ 1 + (1 + ({proj c₃} : Finset (ZMod q)).card) := by
                have := Finset.card_insert_le (proj c₂) {proj c₃}; omega
            _ = 3 := by simp)
      obtain ⟨K, hK_card, hS_in_K⟩ := three_coset_subgroup h0_S hS_ge2 h4S_le3
      -- Pull back K along proj to get a proper subgroup of ZMod m containing Gd!
      set H' : AddSubgroup (ZMod m) := K.comap proj.toAddMonoidHom
      have hGd_H' : ∀ x ∈ Gd, x ∈ H' := fun x hx => hS_in_K (proj x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      have hH'_card : Nat.card H' ≤ 3 * Nat.card H := by
        -- H' = ⋃_{k ∈ K} proj⁻¹(k), each fiber has size |H| = m / q
        have hcard_le : ((H' : Set (ZMod m)).toFinset).card ≤
            ((K : Set (ZMod q)).toFinset).card * (m / q) := by
          have hfib : ∀ y ∈ (K : Set (ZMod q)).toFinset,
              ((H' : Set (ZMod m)).toFinset.filter (fun x => proj x = y)).card ≤ m / q := by
            intro y _
            have hsub : (H' : Set (ZMod m)).toFinset.filter (fun x => proj x = y) ⊆
                Finset.univ.filter (fun x : ZMod m => proj x = y) :=
              Finset.filter_subset_filter _ (Finset.subset_univ _)
            refine (Finset.card_le_card hsub).trans ?_
            -- Size of fiber of proj at y is at most |ker proj| = |H| = m / q
            set x0 : ZMod m := (y.val : ZMod m)
            have hx0 : proj x0 = y := by dsimp [x0]; rw [map_natCast, ZMod.natCast_zmod_val]
            have hbij : (Finset.univ.filter (fun x : ZMod m => proj x = y)).card =
                ((H : Set (ZMod m)).toFinset).card := by
              refine Finset.card_bij (fun x _ => x - x0) ?_ ?_ ?_
              · intro x hx
                rw [Set.mem_toFinset]
                exact (hH_ker _).mpr (by
                  change proj (x - x0) = 0
                  rw [map_sub, (Finset.mem_filter.mp hx).2, hx0, sub_self])
              · intro x1 _ x2 _ h; exact sub_left_inj.mp h
              · intro h hh
                rw [Set.mem_toFinset] at hh
                refine ⟨h + x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, add_sub_cancel_right h x0⟩
                have hh0 : proj h = 0 := (hH_ker h).mp hh
                rw [map_add, hh0, hx0, zero_add]
            rw [hbij]
            have hEq : ((H : Set (ZMod m)).toFinset).card = Nat.card H := by
              rw [Nat.card_eq_fintype_card]; exact Set.toFinset_card (H : Set (ZMod m))
            rw [hEq, hH_card]
          have hmaps : ∀ x ∈ (H' : Set (ZMod m)).toFinset, proj x ∈ (K : Set (ZMod q)).toFinset := by
            intro x hx; rw [Set.mem_toFinset] at hx ⊢; exact hx
          calc ((H' : Set (ZMod m)).toFinset).card
              = ∑ y ∈ (K : Set (ZMod q)).toFinset,
                  ((H' : Set (ZMod m)).toFinset.filter (fun x => proj x = y)).card :=
                Finset.card_eq_sum_card_fiberwise hmaps
            _ ≤ ∑ _y ∈ (K : Set (ZMod q)).toFinset, (m / q) := Finset.sum_le_sum hfib
            _ = ((K : Set (ZMod q)).toFinset).card * (m / q) := by rw [Finset.sum_const, smul_eq_mul]
        have h1 : ((H' : Set (ZMod m)).toFinset).card = Nat.card H' := by
          rw [Nat.card_eq_fintype_card]; exact Set.toFinset_card (H' : Set (ZMod m))
        have h2 : ((K : Set (ZMod q)).toFinset).card = Nat.card K := by
          rw [Nat.card_eq_fintype_card]; exact Set.toFinset_card (K : Set (ZMod q))
        rw [h1, h2, ← hH_card] at hcard_le
        exact hcard_le.trans (Nat.mul_le_mul_right _ hK_card)
      have hH'_ne : H' ≠ ⊤ := by
        intro htop
        have hcard_m : Nat.card H' = m := by
          rw [htop, Nat.card_eq_fintype_card]
          simp [ZMod.card]
        have hH_le_r : (Nat.card H : ℝ) ≤ 1.04 * (Xj.card : ℝ) := by linarith
        have hm_le : (m : ℝ) ≤ 3 * (Nat.card H : ℝ) := by exact_mod_cast (hcard_m ▸ hH'_card)
        have hlt : 3 * (1.04 * (Xj.card : ℝ)) < (m : ℝ) := by
          have : 3.12 * (Xj.card : ℝ) ≤ 3.12 * (ξ * (m : ℝ)) := by linarith
          nlinarith
        linarith
      exact hnot_sub H' hH'_ne hGd_H'
    · -- Case 3: Xj contained in a single coset of H ≠ ⊤
      exact absurd ⟨x, hx⟩ (hXj_not_coset j H hH_ne)
  · -- Exponential growth branch: for all j ∈ [2, i), |2^(j+1) Gd| > 2.04 |2^j Gd|
    left
    push Not at hexj
    have hexp_ind : ∀ t : ℕ, t ≤ i - 2 →
        (2.04 : ℝ) ^ t * (Gd.card : ℝ) ≤ ((nfoldSum (2 ^ (2 + t)) Gd).card : ℝ) := by
      intro t
      induction t with
      | zero =>
        intro _
        simp only [pow_zero, one_mul, add_zero]
        exact_mod_cast Finset.card_le_card (nfoldSum3_le_mono h0_Gd (by decide : 1 ≤ 2 ^ 2) |>.trans'
          (by rw [nfoldSum3_one]))
      | succ t iht =>
        intro ht
        have hstep := hexj (2 + t) (by omega) (by omega)
        have hsum_eq : nfoldSum (2 ^ (2 + (t + 1))) Gd =
            nfoldSum (2 ^ (2 + t)) Gd + nfoldSum (2 ^ (2 + t)) Gd := by
          rw [show 2 + (t + 1) = (2 + t) + 1 by omega, pow_succ, mul_two, nfoldSum3_add]
        rw [hsum_eq]
        have hprev := iht (by omega)
        have h204_nn : (0 : ℝ) ≤ 2.04 := by norm_num
        calc (2.04 : ℝ) ^ (t + 1) * (Gd.card : ℝ)
            = 2.04 * ((2.04 : ℝ) ^ t * (Gd.card : ℝ)) := by rw [pow_succ]; ring
          _ ≤ 2.04 * ((nfoldSum (2 ^ (2 + t)) Gd).card : ℝ) :=
              mul_le_mul_of_nonneg_left hprev h204_nn
          _ ≤ ((nfoldSum (2 ^ (2 + t)) Gd + nfoldSum (2 ^ (2 + t)) Gd).card : ℝ) := hstep.le
    have hfin := hexp_ind (i - 2) le_rfl
    rw [show 2 + (i - 2) = i by omega] at hfin
    have hpow_ge : ((A.card : ℝ) / (2 * (d : ℝ))) ^ (1.02 : ℝ) / 10 ≤ (2.04 : ℝ) ^ (i - 2) := by
      have h1 : ((A.card : ℝ) / (2 * (d : ℝ))) ^ (1.02 : ℝ) ≤
          (((2 ^ (i + 1) : ℕ) : ℝ)) ^ (1.02 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h2i1_gt_r.le (by norm_num)
      have h2 : (((2 ^ (i + 1) : ℕ) : ℝ)) ^ (1.02 : ℝ) =
          (2 : ℝ) ^ (3.06 : ℝ) * ((2 : ℝ) ^ (1.02 : ℝ)) ^ (i - 2) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) (i + 1),
          ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (1.02 : ℝ)) (i - 2),
          ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        have hi2_r : ((i - 2 : ℕ) : ℝ) = (i : ℝ) - 2 := by rw [Nat.cast_sub hi2]; push_cast; rfl
        rw [hi2_r]; push_cast; ring
      have h3 : ((2 : ℝ) ^ (1.02 : ℝ)) ^ (i - 2) ≤ (2.04 : ℝ) ^ (i - 2) :=
        pow_le_pow_left₀ (by positivity) two_rpow_102_le_204 (i - 2)
      have h4 : (2 : ℝ) ^ (3.06 : ℝ) * ((2 : ℝ) ^ (1.02 : ℝ)) ^ (i - 2) ≤
          10 * (2.04 : ℝ) ^ (i - 2) :=
        mul_le_mul two_rpow_306_le_ten h3 (by positivity) (by norm_num)
      linarith
    have hpos_den : 0 < ((A.card : ℝ) / (2 * (d : ℝ))) ^ (1.02 : ℝ) := by
      have : (0 : ℝ) < (A.card : ℝ) / (2 * (d : ℝ)) := by
        have : (0 : ℝ) < A.card := by exact_mod_cast (by omega : 0 < A.card)
        positivity
      exact Real.rpow_pos_of_pos this _
    rw [le_div_iff₀ hpos_den]
    have h1 : (((A.card : ℝ) / (2 * (d : ℝ))) ^ (1.02 : ℝ) / 10) * (Gd.card : ℝ) ≤
        (2.04 : ℝ) ^ (i - 2) * (Gd.card : ℝ) :=
      mul_le_mul_of_nonneg_right hpow_ge (Nat.cast_nonneg _)
    linarith

/- ### Section 5: Covering a Coset-AP in `[x₀, x₀ + t)` by Integer APs (`lem:ap-mod-t`) -/

private lemma list_sum_flatMap {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.sum_append, ih]

private lemma dirichlet_pigeonhole_zmod {q L : ℕ} (hq : 2 ≤ q) (hL2 : 2 ≤ L) (hLq : L ≤ q)
    (w : (ZMod q)ˣ) :
    ∃ (s : ℕ) (v : ℤ),
      1 ≤ s ∧ s ≤ Nat.floor (Real.sqrt (L : ℝ)) ∧
      v ≠ 0 ∧ v.natAbs * Nat.ceil (Real.sqrt (L : ℝ)) ≤ q ∧
      (v : ZMod q) = (s : ZMod q) * w.1 := by
  have : NeZero q := ⟨by omega⟩
  set S := Nat.floor (Real.sqrt (L : ℝ))
  set Q := Nat.ceil (Real.sqrt (L : ℝ))
  have hS1 : 1 ≤ S := Nat.le_floor (by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; norm_num; exact_mod_cast (by omega : 1 ≤ L))
  have hQ_ge_S : S ≤ Q := by
    have h1 : (S : ℝ) ≤ Real.sqrt (L : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (L : ℝ) ≤ (Q : ℝ) := Nat.le_ceil _
    exact_mod_cast h1.trans h2
  have hQ_le_S1 : Q ≤ S + 1 := by
    have h1 : Real.sqrt (L : ℝ) < (S : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : Q ≤ S + 1 := Nat.ceil_le.mpr (by push_cast; exact h1.le)
    exact h2
  have hS_lt_q : S < q := by
    have h1 : (S : ℝ) ≤ Real.sqrt (L : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (L : ℝ) < (L : ℝ) := by
      rw [Real.sqrt_lt' (by exact_mod_cast (by omega : 0 < L))]
      have hL2r : (2 : ℝ) ≤ L := by exact_mod_cast hL2
      nlinarith
    have hSL : S < L := by exact_mod_cast h1.trans_lt h2
    omega
  have hsw_ne0 : ∀ s : ℕ, 1 ≤ s → s ≤ S → ((s : ZMod q) * w.1) ≠ 0 := by
    intro s hs1 hsS heq
    have hs0 : (s : ZMod q) = 0 := by
      have := congrArg (· * (w⁻¹).1) heq
      rw [zero_mul, mul_assoc, Units.mul_inv, mul_one] at this
      exact this
    have hdvd : q ∣ s := (ZMod.natCast_eq_zero_iff s q).mp hs0
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  -- Bucket function b : ZMod q → Fin Q given by r ↦ r.val * Q / q
  let buck (r : ZMod q) : ℕ := r.val * Q / q
  have hQ_pos : 0 < Q := Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hS1) hQ_ge_S
  have hbuck_lt : ∀ r : ZMod q, buck r < Q := by
    intro r
    exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [mul_comm Q q]; exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt r) hQ_pos)
  -- Case A: some s ∈ [1, S] lands in bucket 0 or bucket Q - 1
  by_cases h0 : ∃ s ∈ Finset.Icc 1 S, buck ((s : ZMod q) * w.1) = 0
  · obtain ⟨s, hs, hb0⟩ := h0
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hsS : s ≤ S := (Finset.mem_Icc.mp hs).2
    set r := ((s : ZMod q) * w.1).val
    have hr_ne0 : r ≠ 0 := by
      intro h; apply hsw_ne0 s hs1 hsS
      rw [← ZMod.natCast_zmod_val ((s : ZMod q) * w.1)]
      change ((r : ℕ) : ZMod q) = 0
      rw [h, Nat.cast_zero]
    have hrQ_lt : r * Q < q := (Nat.div_eq_zero_iff_lt (by omega)).mp hb0
    refine ⟨s, (r : ℤ), hs1, hsS, by omega, by simpa using hrQ_lt.le, ?_⟩
    simp [r]
  · by_cases htop : ∃ s ∈ Finset.Icc 1 S, buck ((s : ZMod q) * w.1) = Q - 1
    · obtain ⟨s, hs, hbt⟩ := htop
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      have hsS : s ≤ S := (Finset.mem_Icc.mp hs).2
      set r := ((s : ZMod q) * w.1).val
      have hr_lt : r < q := ZMod.val_lt _
      have hr_ge : (Q - 1) * q ≤ r * Q := (Nat.le_div_iff_mul_le (by omega)).mp hbt.ge
      have hqrQ_le : (q - r) * Q ≤ q := by
        have h1 : (q - r) * Q + r * Q = q * Q := by rw [← add_mul, Nat.sub_add_cancel hr_lt.le]
        have h2 : (Q - 1) * q + q = q * Q := by
          have hQ1 : 1 ≤ Q := by omega
          calc (Q - 1) * q + q = (Q - 1 + 1) * q := by ring
            _ = Q * q := by rw [Nat.sub_add_cancel hQ1]
            _ = q * Q := mul_comm _ _
        omega
      refine ⟨s, -((q - r : ℕ) : ℤ), hs1, hsS, by omega, by simpa using hqrQ_le, ?_⟩
      rw [Int.cast_neg, Int.cast_natCast, Nat.cast_sub hr_lt.le, ZMod.natCast_self, zero_sub, neg_neg]
      simp [r]
    · -- Case B: all s ∈ Icc 1 S land in Ico 1 (Q - 1), which has size Q - 2 < S!
      push Not at h0 htop
      have hmaps : ∀ s ∈ Finset.Icc 1 S, buck ((s : ZMod q) * w.1) ∈ Finset.Ico 1 (Q - 1) := by
        intro s hs
        have hlt := hbuck_lt ((s : ZMod q) * w.1)
        have hne0 := h0 s hs
        have hnet := htop s hs
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have hcard_lt : (Finset.Ico 1 (Q - 1)).card < (Finset.Icc 1 S).card := by
        simp only [Nat.card_Ico, Nat.card_Icc]; omega
      obtain ⟨s₁, hs₁, s₂, hs₂, hne, hbeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt hmaps
      -- WLOG s₁ < s₂
      have hpair : ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ b ≤ S ∧
          buck ((a : ZMod q) * w.1) = buck ((b : ZMod q) * w.1) := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ⟨s₁, s₂, (Finset.mem_Icc.mp hs₁).1, hlt, (Finset.mem_Icc.mp hs₂).2, hbeq⟩
        · exact ⟨s₂, s₁, (Finset.mem_Icc.mp hs₂).1, hgt, (Finset.mem_Icc.mp hs₁).2, hbeq.symm⟩
      obtain ⟨a, b, ha1, hab, hbS, heqb⟩ := hpair
      set r₁ := ((a : ZMod q) * w.1).val
      set r₂ := ((b : ZMod q) * w.1).val
      set s := b - a
      have hs1 : 1 ≤ s := by omega
      have hsS : s ≤ S := by omega
      have hv_cast : ((((r₂ : ℤ) - (r₁ : ℤ)) : ℤ) : ZMod q) = (s : ZMod q) * w.1 := by
        rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
          ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Nat.cast_sub hab.le]
        ring
      have hv_ne0 : (r₂ : ℤ) - (r₁ : ℤ) ≠ 0 := by
        intro hzero
        have : ((s : ZMod q) * w.1) = 0 := by rw [← hv_cast, hzero, Int.cast_zero]
        exact hsw_ne0 s hs1 hsS this
      have hdiff_le : ((r₂ : ℤ) - (r₁ : ℤ)).natAbs * Q ≤ q := by
        set m0 := r₁ * Q / q
        have hmq : (m0 + 1) * q = m0 * q + q := by ring
        have h1 : m0 * q ≤ r₁ * Q := Nat.div_mul_le_self _ _
        have h2 : r₁ * Q < (m0 + 1) * q := by
          have hlt := Nat.lt_div_mul_add (a := r₁ * Q) (b := q) (by omega)
          change r₁ * Q < m0 * q + q at hlt
          omega
        have h3 : m0 * q ≤ r₂ * Q := by
          have : m0 = r₂ * Q / q := heqb
          rw [this]; exact Nat.div_mul_le_self _ _
        have h4 : r₂ * Q < (m0 + 1) * q := by
          have : m0 = r₂ * Q / q := heqb
          have hlt := Nat.lt_div_mul_add (a := r₂ * Q) (b := q) (by omega)
          rw [← this] at hlt
          omega
        have hmul_abs : ((r₂ : ℤ) - (r₁ : ℤ)).natAbs * Q < q := by
          rcases le_total r₁ r₂ with hle | hge
          · have habs : ((r₂ : ℤ) - (r₁ : ℤ)).natAbs = r₂ - r₁ := by omega
            rw [habs, Nat.sub_mul]
            omega
          · have habs : ((r₂ : ℤ) - (r₁ : ℤ)).natAbs = r₁ - r₂ := by omega
            rw [habs, Nat.sub_mul]
            omega
        exact hmul_abs.le
      exact ⟨s, (r₂ : ℤ) - (r₁ : ℤ), hs1, hsS, hv_ne0, hdiff_le, hv_cast⟩

/-- Partition a modular progression `m ↦ (r0 + m * v) % q` (shifted by `x0`) of length `len`
into integer APs of step `|v|` and length ≥ `Q`, with total length ≤ `len + 2 * (Q - 1)`. -/
private lemma partition_mod_prog_pos {q x0 r0 step Q : ℕ} (hq : 1 ≤ q) (hstep : 1 ≤ step)
    (hQ : 1 ≤ Q) (hstepQ : step * Q ≤ q) (hr0 : r0 < q) (len : ℕ) :
    ∃ APs : List (ℕ × ℕ),
      (∀ m < len, ∃ p ∈ APs, ∃ k < p.2, x0 + (r0 + m * step) % q = p.1 + step * k) ∧
      (∀ p ∈ APs, Q ≤ p.2) ∧
      (APs.map Prod.snd).sum ≤ len + 2 * (Q - 1) := by
  by_cases hlen0 : len = 0
  · subst hlen0; exact ⟨[], by simp, by simp, by simp⟩
  -- Strong induction on len!
  -- Actually, track the greedy wraparound runs:
  -- For any starting index `start < len`, the maximal non-wrapping run starting at `start`
  -- has length `rlen = min (len - start) ((q - 1 - cur) / step + 1)` where `cur = (r0 + start * step) % q`.
  -- Notice if `cur < step`, then `(q - 1 - cur) / step + 1 ≥ Q` (since `cur + (Q - 1) * step < step * Q ≤ q`)!
  -- And after ANY wraparound, the new `cur` satisfies `cur < step`!
  have hgen : ∀ (n : ℕ) (cur : ℕ), cur < q →
      ∃ APs : List (ℕ × ℕ),
        (∀ m < n, ∃ p ∈ APs, ∃ k < p.2, x0 + (cur + m * step) % q = p.1 + step * k) ∧
        (∀ p ∈ APs, Q ≤ p.2) ∧
        (APs.map Prod.snd).sum ≤ n + (if cur < step then Q - 1 else 2 * (Q - 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro cur hcur
      by_cases hn0 : n = 0
      · subst hn0; exact ⟨[], by simp, by simp, by simp⟩
      set runLen : ℕ := min n ((q - 1 - cur) / step + 1)
      have hrun_pos : 1 ≤ runLen := le_min (by omega) (Nat.succ_pos _)
      have hrun_le_n : runLen ≤ n := min_le_left _ _
      have hrun_nowrap : ∀ m < runLen, cur + m * step < q := by
        intro m hm
        have hm2 : m ≤ (q - 1 - cur) / step := by dsimp [runLen] at hm; omega
        have hmul : m * step ≤ q - 1 - cur := (Nat.le_div_iff_mul_le hstep).mp hm2
        omega
      by_cases hfull : runLen = n
      · -- Single run covers all of `0 .. n - 1`; pad to max n Q!
        refine ⟨[(x0 + cur, max n Q)], ?_, ?_, ?_⟩
        · intro m hm
          refine ⟨(x0 + cur, max n Q), by simp, m, by omega, ?_⟩
          have hlt := hrun_nowrap m (by omega)
          rw [Nat.mod_eq_of_lt hlt]; ring
        · intro p hp; simp at hp; subst hp; exact le_max_right _ _
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          split_ifs <;> omega
      · -- Wraparound occurs! So runLen = (q - 1 - cur) / step + 1 < n!
        have hrun_eq : runLen = (q - 1 - cur) / step + 1 := by
          dsimp [runLen] at hfull ⊢; omega
        have hwrap_ge : q ≤ cur + runLen * step := by
          have h1 := Nat.lt_div_mul_add (a := q - 1 - cur) (b := step) hstep
          have h2 : runLen * step = ((q - 1 - cur) / step) * step + step := by rw [hrun_eq]; ring
          omega
        have hwrap_lt : cur + runLen * step < q + step := by
          have hprev := hrun_nowrap (runLen - 1) (by omega)
          have h2 : runLen * step = (runLen - 1) * step + step := by
            conv_lhs => rw [← Nat.sub_add_cancel hrun_pos]
            ring
          omega
        set cur' : ℕ := (cur + runLen * step) % q
        have hcur'_eq : cur' = cur + runLen * step - q := by
          dsimp [cur']
          have hstep_le_q : step ≤ q := by nlinarith
          have h1 : cur + runLen * step = q + (cur + runLen * step - q) := by omega
          conv_lhs => rw [h1]
          rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        have hcur'_lt_step : cur' < step := by omega
        have hcur'_lt_q : cur' < q := Nat.mod_lt _ (by omega)
        obtain ⟨APs', hcov', hlen', hsum'⟩ := ih (n - runLen) (by omega) cur' hcur'_lt_q
        rw [if_pos hcur'_lt_step] at hsum'
        -- If cur < step, then runLen ≥ Q ALREADY (zero padding!)
        have hgeQ_of_lt : cur < step → Q ≤ runLen := by
          intro hcs
          have h1 : (Q - 1) * step ≤ q - 1 - cur := by
            have : (Q - 1) * step + step = step * Q := by
              calc (Q - 1) * step + step = (Q - 1 + 1) * step := by ring
                _ = Q * step := by rw [Nat.sub_add_cancel hQ]
                _ = step * Q := mul_comm _ _
            omega
          have h2 : Q - 1 ≤ (q - 1 - cur) / step := (Nat.le_div_iff_mul_le hstep).mpr h1
          omega
        refine ⟨(x0 + cur, max runLen Q) :: APs', ?_, ?_, ?_⟩
        · intro m hm
          by_cases hmr : m < runLen
          · refine ⟨(x0 + cur, max runLen Q), List.mem_cons_self, m, by omega, ?_⟩
            rw [Nat.mod_eq_of_lt (hrun_nowrap m hmr)]; ring
          · obtain ⟨p, hp, k, hk, heq⟩ := hcov' (m - runLen) (by omega)
            refine ⟨p, List.mem_cons_of_mem _ hp, k, hk, ?_⟩
            have hmod_eq : (cur + m * step) % q = (cur' + (m - runLen) * step) % q := by
              have hsplit : cur + m * step = (cur + runLen * step) + (m - runLen) * step := by
                have hm_eq : m = runLen + (m - runLen) := by omega
                conv_lhs => rw [hm_eq, add_mul]
                ring
              rw [hsplit, Nat.add_mod, Nat.add_mod cur']
              simp [cur']
            rw [hmod_eq]; exact heq
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact le_max_right _ _
          · exact hlen' p hp'
        · simp only [List.map_cons, List.sum_cons]
          by_cases hcs : cur < step
          · rw [if_pos hcs]
            have hQle := hgeQ_of_lt hcs
            rw [max_eq_left hQle]
            omega
          · rw [if_neg hcs]
            omega
  obtain ⟨APs, hcov, hlen, hsum⟩ := hgen len r0 hr0
  refine ⟨APs, hcov, hlen, hsum.trans ?_⟩
  split_ifs <;> omega

lemma ap_mod_t_cover {t x0 q a0 L : ℕ} (ht : 1 ≤ t) (hq2 : 2 ≤ q) (hq_dvd : q ∣ t)
    (hL1 : 1 ≤ L) (hLq : L ≤ q) (u : (ZMod q)ˣ) :
    let H_sz := t / q
    let R := (Finset.Ico x0 (x0 + t)).filter
      (fun z : ℕ => ∃ k < L, u.1 * (z : ZMod q) = ((a0 + k : ℕ) : ZMod q))
    ∃ APs : List (ℕ × ℕ × ℕ),
      (∀ z ∈ R, ∃ p ∈ APs, ∃ k < p.2.2, z = p.1 + p.2.1 * k) ∧
      (∀ p ∈ APs, 1 ≤ p.2.1 ∧ p.2.1 ≤ t ∧ ((L * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ (p.2.2 : ℝ)) ∧
      (APs.map (fun p => p.2.2)).sum ≤ 3 * (L * H_sz) := by
  have : NeZero q := ⟨by omega⟩
  set H_sz : ℕ := t / q
  have hq_le_t : q ≤ t := Nat.le_of_dvd ht hq_dvd
  have hH_pos : 1 ≤ H_sz := Nat.div_pos hq_le_t (by omega)
  have ht_eq : q * H_sz = t := Nat.mul_div_cancel' hq_dvd
  -- Helper: unique representative in [x0, x0 + q) for any y : ZMod q
  let rep (y : ZMod q) : ℕ := x0 + (y - (x0 : ZMod q)).val
  have hrep_cast : ∀ y : ZMod q, ((rep y : ℕ) : ZMod q) = y := by
    intro y; dsimp [rep]; rw [Nat.cast_add, ZMod.natCast_zmod_val]; abel
  have hrep_rng : ∀ y : ZMod q, x0 ≤ rep y ∧ rep y < x0 + q := by
    intro y; dsimp [rep]; have := ZMod.val_lt (y - (x0 : ZMod q)); omega
  have hdecomp : ∀ z ∈ Finset.Ico x0 (x0 + t),
      ∃ h < H_sz, z = rep (z : ZMod q) + h * q := by
    intro z hz
    have hz1 := (Finset.mem_Ico.mp hz).1
    have hz2 := (Finset.mem_Ico.mp hz).2
    have hmod : (z - x0) % q = ((z : ZMod q) - (x0 : ZMod q)).val := by
      have h1 : (((z - x0 : ℕ) : ZMod q)) = (z : ZMod q) - (x0 : ZMod q) := Nat.cast_sub hz1
      rw [← h1, ZMod.val_natCast]
    refine ⟨(z - x0) / q, ?_, ?_⟩
    · have : H_sz * q = t := by rw [mul_comm, ht_eq]
      exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    · dsimp [rep]
      have hdiv := Nat.div_add_mod (z - x0) q
      have hmulc : q * ((z - x0) / q) = (z - x0) / q * q := mul_comm _ _
      rw [← hmod]; omega
  by_cases hH_big : ((L * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ (H_sz : ℝ)
  · -- Case 1: each H-coset is already an AP of length H_sz ≥ (L * H_sz)^(1/3)!
    refine ⟨(List.range L).map (fun k => (rep ((u⁻¹).1 * ((a0 + k : ℕ) : ZMod q)), q, H_sz)), ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨hz_Ico, k, hkL, hzk⟩ := Finset.mem_filter.mp hz
      obtain ⟨h, hhH, hzeq⟩ := hdecomp z hz_Ico
      have hz_mod : (z : ZMod q) = (u⁻¹).1 * ((a0 + k : ℕ) : ZMod q) := by
        have := congrArg ((u⁻¹).1 * ·) hzk
        rw [← mul_assoc, Units.inv_mul, one_mul] at this
        exact this
      refine ⟨(rep ((u⁻¹).1 * ((a0 + k : ℕ) : ZMod q)), q, H_sz),
        List.mem_map.mpr ⟨k, List.mem_range.mpr hkL, rfl⟩, h, hhH, ?_⟩
      rw [← hz_mod, mul_comm]; exact hzeq
    · intro p hp
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
      exact ⟨le_trans (by decide : 1 ≤ 2) hq2, hq_le_t, hH_big⟩
    · rw [List.map_map]
      have hsum : ((List.range L).map ((fun p : ℕ × ℕ × ℕ => p.2.2) ∘
          fun k => (rep ((u⁻¹).1 * ((a0 + k : ℕ) : ZMod q)), q, H_sz))).sum = L * H_sz := by
        simp [Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul]
      rw [hsum]; omega
  · -- Case 2: H_sz < (L * H_sz)^(1/3), hence L ≥ 2 and (L * H_sz)^(1/3) ≤ √L ≤ ⌈√L⌉₊!
    push Not at hH_big
    have hL2 : 2 ≤ L := by
      by_contra hlt
      have hL1' : L = 1 := by omega
      subst hL1'
      have h1 : (1 : ℝ) ≤ (H_sz : ℝ) := by exact_mod_cast hH_pos
      have hle : ((1 * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ (H_sz : ℝ) := by
        rw [one_mul]
        calc (H_sz : ℝ) ^ (1 / 3 : ℝ) ≤ (H_sz : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
          _ = (H_sz : ℝ) := Real.rpow_one _
      linarith
    have hQ_ge_rpow : ((L * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ (Nat.ceil (Real.sqrt (L : ℝ)) : ℝ) := by
      have hH3_lt : (H_sz : ℝ) ^ (3 : ℕ) < (L : ℝ) * (H_sz : ℝ) := by
        have h := pow_lt_pow_left₀ hH_big (by positivity) (by decide : 3 ≠ 0)
        rw [← Real.rpow_natCast (((L * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ)) 3,
          ← Real.rpow_mul (by positivity)] at h
        norm_num at h
        exact h
      have hH_pos_r : (0 : ℝ) < H_sz := by exact_mod_cast hH_pos
      have hH2_lt_L : (H_sz : ℝ) ^ (2 : ℕ) < (L : ℝ) := by nlinarith
      have hLH2_lt_L3 : ((L * H_sz : ℕ) : ℝ) ^ (2 : ℕ) < (L : ℝ) ^ (3 : ℕ) := by
        push_cast
        have hL_pos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
        have hsq : ((L : ℝ) * (H_sz : ℝ)) ^ 2 = (L : ℝ) ^ 2 * (H_sz : ℝ) ^ 2 := by ring
        rw [hsq]
        have hL2_pos : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
        nlinarith
      have hLH_le_sq : ((L * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ Real.sqrt (L : ℝ) := by
        have h6 : (((L * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ)) ^ (6 : ℕ) ≤ (Real.sqrt (L : ℝ)) ^ (6 : ℕ) := by
          rw [← Real.rpow_natCast (((L * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ)) 6,
            ← Real.rpow_mul (by positivity), show (1 / 3 : ℝ) * ((6 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
          have hsq6 : (Real.sqrt (L : ℝ)) ^ (6 : ℕ) = (L : ℝ) ^ (3 : ℕ) := by
            rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (Nat.cast_nonneg L)]
          rw [hsq6]; exact hLH2_lt_L3.le
        exact le_of_pow_le_pow_left₀ (by decide : 6 ≠ 0) (Real.sqrt_nonneg _) h6
      exact hLH_le_sq.trans (Nat.le_ceil _)
    set Q := Nat.ceil (Real.sqrt (L : ℝ))
    have hQ1 : 1 ≤ Q := by
      have : (1 : ℝ) ≤ Real.sqrt (L : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]; norm_num; exact_mod_cast (by omega : 1 ≤ L)
      exact_mod_cast this.trans (Nat.le_ceil _)
    obtain ⟨s, v, hs1, hsS, hv_ne0, hvQ_le, hv_eq⟩ := dirichlet_pigeonhole_zmod hq2 hL2 hLq u⁻¹
    set step := v.natAbs
    have hstep1 : 1 ≤ step := Int.natAbs_pos.mpr hv_ne0
    have hstep_le_q : step ≤ q := by
      calc step = step * 1 := (mul_one _).symm
        _ ≤ step * Q := Nat.mul_le_mul_left step hQ1
        _ ≤ q := hvQ_le
    -- For each residue class j < s, build APs covering {rep (u⁻¹ * (a0 + j + s * m)) | j + s * m < L}
    have hclass : ∀ j : ℕ, j < s →
        ∃ APj : List (ℕ × ℕ),
          (∀ m < (L - 1 - j) / s + 1, j + s * m < L →
            ∃ p ∈ APj, ∃ r < p.2,
              rep ((u⁻¹).1 * ((a0 + (j + s * m) : ℕ) : ZMod q)) = p.1 + step * r) ∧
          (∀ p ∈ APj, Q ≤ p.2) ∧
          (APj.map Prod.snd).sum ≤ (if j < L then (L - 1 - j) / s + 1 else 0) + 2 * (Q - 1) := by
      intro j hj
      by_cases hjL : j < L
      · set len := (L - 1 - j) / s + 1
        have hlen_pos : 1 ≤ len := Nat.succ_pos _
        by_cases hv_pos : 0 < v
        · -- Positive step: v = step
          have hv_eq_step : v = (step : ℤ) := (Int.natAbs_of_nonneg hv_pos.le).symm
          set r0 := ((u⁻¹).1 * ((a0 + j : ℕ) : ZMod q) - (x0 : ZMod q)).val
          have hr0_lt : r0 < q := ZMod.val_lt _
          obtain ⟨APj, hcov, hlenQ, hsum⟩ :=
            partition_mod_prog_pos (x0 := x0) (by omega : 1 ≤ q) hstep1 hQ1 hvQ_le hr0_lt len
          refine ⟨APj, ?_, hlenQ, by rw [if_pos hjL]; exact hsum⟩
          intro m hm _
          obtain ⟨p, hp, r, hr, heq⟩ := hcov m hm
          refine ⟨p, hp, r, hr, ?_⟩
          have hrep_eq : rep ((u⁻¹).1 * ((a0 + (j + s * m) : ℕ) : ZMod q)) =
              x0 + (r0 + m * step) % q := by
            dsimp [rep]
            congr 1
            have hcast : ((u⁻¹).1 * ((a0 + (j + s * m) : ℕ) : ZMod q) - (x0 : ZMod q)) =
                (((r0 + m * step : ℕ) : ZMod q)) := by
              conv_rhs => rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
              have hv_cast : ((step : ℕ) : ZMod q) = (s : ZMod q) * (u⁻¹).1 := by
                have := hv_eq; rw [hv_eq_step, Int.cast_natCast] at this; exact this
              rw [hv_cast]
              push_cast; ring
            rw [hcast, ZMod.val_natCast]
          rw [hrep_eq]; exact heq
        · -- Negative step: v = -step; reverse the index m ↦ (len - 1 - m)!
          have hv_neg : v < 0 := lt_of_le_of_ne (not_lt.mp hv_pos) hv_ne0
          have hv_eq_neg : v = -(step : ℤ) := by
            have := Int.ofNat_natAbs_of_nonpos hv_neg.le
            dsimp [step]; omega
          set r0 := ((u⁻¹).1 * ((a0 + (j + s * (len - 1)) : ℕ) : ZMod q) - (x0 : ZMod q)).val
          have hr0_lt : r0 < q := ZMod.val_lt _
          obtain ⟨APj, hcov, hlenQ, hsum⟩ :=
            partition_mod_prog_pos (x0 := x0) (by omega : 1 ≤ q) hstep1 hQ1 hvQ_le hr0_lt len
          refine ⟨APj, ?_, hlenQ, by rw [if_pos hjL]; exact hsum⟩
          intro m hm _
          obtain ⟨p, hp, r, hr, heq⟩ := hcov (len - 1 - m) (by omega)
          refine ⟨p, hp, r, hr, ?_⟩
          have hrep_eq : rep ((u⁻¹).1 * ((a0 + (j + s * m) : ℕ) : ZMod q)) =
              x0 + (r0 + (len - 1 - m) * step) % q := by
            dsimp [rep]
            congr 1
            have hcast : ((u⁻¹).1 * ((a0 + (j + s * m) : ℕ) : ZMod q) - (x0 : ZMod q)) =
                (((r0 + (len - 1 - m) * step : ℕ) : ZMod q)) := by
              conv_rhs => rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
              have hv_cast : ((step : ℕ) : ZMod q) = -((s : ZMod q) * (u⁻¹).1) := by
                have := hv_eq; rw [hv_eq_neg, Int.cast_neg, Int.cast_natCast] at this
                linear_combination -this
              rw [hv_cast, Nat.cast_sub (show m ≤ len - 1 by omega)]
              push_cast; ring
            rw [hcast, ZMod.val_natCast]
          rw [hrep_eq]; exact heq
      · refine ⟨[], ?_, by simp, by simp [if_neg hjL]⟩
        intro m _ hlt; omega
    choose APj hcovj hlenj hsumj using hclass
    -- Collect all (a, step, len) across j < s, then replicate across h < H_sz!
    let baseAPs : List (ℕ × ℕ) := (List.finRange s).flatMap (fun j => APj j.1 j.2)
    let allAPs : List (ℕ × ℕ × ℕ) :=
      (List.range H_sz).flatMap (fun h => baseAPs.map (fun p => (p.1 + h * q, step, p.2)))
    -- Sum of lengths of baseAPs ≤ 3 * L
    have hbase_sum : (baseAPs.map Prod.snd).sum ≤ 3 * L := by
      have h1 : (baseAPs.map Prod.snd).sum =
          ∑ j : Fin s, ((APj j.1 j.2).map Prod.snd).sum := by
        dsimp [baseAPs]
        rw [List.map_flatMap, list_sum_flatMap]
        rw [← Fin.sum_univ_def]
      rw [h1]
      have hsum_counts : ∑ j : Fin s, (if j.1 < L then (L - 1 - j.1) / s + 1 else 0) = L := by
        -- Count of {k ∈ range L | k % s = j} is (L - 1 - j) / s + 1 if j < L else 0
        have hbij : ∀ j : Fin s,
            ((Finset.range L).filter (fun k => k % s = j.1)).card =
              if j.1 < L then (L - 1 - j.1) / s + 1 else 0 := by
          intro j
          by_cases hjL : j.1 < L
          · rw [if_pos hjL]
            have heq : (Finset.range L).filter (fun k => k % s = j.1) =
                (Finset.range ((L - 1 - j.1) / s + 1)).image (fun m => j.1 + s * m) := by
              ext k
              simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
              constructor
              · rintro ⟨hkL, hkmod⟩
                refine ⟨k / s, ?_, ?_⟩
                · have hdiv := Nat.div_add_mod k s
                  have hmulc : s * (k / s) = (k / s) * s := mul_comm _ _
                  have hle : k / s ≤ (L - 1 - j.1) / s :=
                    (Nat.le_div_iff_mul_le hs1).mpr (by omega)
                  omega
                · have hdiv := Nat.div_add_mod k s; omega
              · rintro ⟨m, hm, rfl⟩
                have hle : m ≤ (L - 1 - j.1) / s := by omega
                have hmul : m * s ≤ L - 1 - j.1 := (Nat.le_div_iff_mul_le hs1).mp hle
                have hmulc : s * m = m * s := mul_comm _ _
                refine ⟨by omega, ?_⟩
                rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.2]
            rw [heq, Finset.card_image_of_injective _ (fun a b h => by
              have : s * a = s * b := by omega
              exact Nat.eq_of_mul_eq_mul_left hs1 this), Finset.card_range]
          · rw [if_neg hjL, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro k hk hmod
            have hkL := Finset.mem_range.mp hk
            have := Nat.mod_le k s
            omega
        simp_rw [← hbij]
        have hpart := Finset.card_eq_sum_card_fiberwise (s := Finset.range L) (t := (Finset.univ : Finset (Fin s)))
          (f := fun k => (⟨k % s, Nat.mod_lt k hs1⟩ : Fin s)) (fun _ _ => Finset.mem_univ _)
        rw [Finset.card_range] at hpart
        conv_rhs => rw [hpart]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1; ext k; simp [Fin.ext_iff]
      have h2sQ : 2 * s * (Q - 1) ≤ 2 * L := by
        have hs_r : (s : ℝ) ≤ Real.sqrt (L : ℝ) :=
          (Nat.cast_le.mpr hsS).trans (Nat.floor_le (Real.sqrt_nonneg _))
        have hQ_r : ((Q - 1 : ℕ) : ℝ) < Real.sqrt (L : ℝ) := by
          have h := Nat.ceil_lt_add_one (Real.sqrt_nonneg (L : ℝ))
          rw [Nat.cast_sub hQ1]; push_cast; linarith
        have hmul_r : (s : ℝ) * ((Q - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by
          calc (s : ℝ) * ((Q - 1 : ℕ) : ℝ)
              ≤ Real.sqrt (L : ℝ) * Real.sqrt (L : ℝ) :=
                mul_le_mul hs_r hQ_r.le (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
            _ = (L : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg L)
        have hmul_n : s * (Q - 1) ≤ L := by exact_mod_cast hmul_r
        have hassoc : 2 * s * (Q - 1) = 2 * (s * (Q - 1)) := by ring
        omega
      calc ∑ j : Fin s, ((APj j.1 j.2).map Prod.snd).sum
          ≤ ∑ j : Fin s, ((if j.1 < L then (L - 1 - j.1) / s + 1 else 0) + 2 * (Q - 1)) :=
            Finset.sum_le_sum fun j _ => hsumj j.1 j.2
        _ = (∑ j : Fin s, (if j.1 < L then (L - 1 - j.1) / s + 1 else 0)) +
            ∑ _j : Fin s, (2 * (Q - 1)) := Finset.sum_add_distrib
        _ = L + s * (2 * (Q - 1)) := by rw [hsum_counts, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ 3 * L := by
            have hcomm : s * (2 * (Q - 1)) = 2 * s * (Q - 1) := by ring
            omega
    refine ⟨allAPs, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨hz_Ico, k, hkL, hzk⟩ := Finset.mem_filter.mp hz
      obtain ⟨h, hhH, hzeq⟩ := hdecomp z hz_Ico
      have hz_mod : (z : ZMod q) = (u⁻¹).1 * ((a0 + k : ℕ) : ZMod q) := by
        have := congrArg ((u⁻¹).1 * ·) hzk
        rw [← mul_assoc, Units.inv_mul, one_mul] at this
        exact this
      set j : ℕ := k % s
      set m : ℕ := k / s
      have hj_lt : j < s := Nat.mod_lt k hs1
      have hk_eq : j + s * m = k := by
        have hdiv := Nat.div_add_mod k s
        change k % s + s * (k / s) = k
        omega
      have hm_lt : m < (L - 1 - j) / s + 1 := by
        have hms : m * s = s * m := mul_comm _ _
        have : m ≤ (L - 1 - j) / s := (Nat.le_div_iff_mul_le hs1).mpr (by omega)
        omega
      obtain ⟨p, hp, r, hr, hpeq⟩ := hcovj j hj_lt m hm_lt (hk_eq ▸ hkL)
      have hp_base : p ∈ baseAPs :=
        List.mem_flatMap.mpr ⟨⟨j, hj_lt⟩, List.mem_finRange _, hp⟩
      refine ⟨(p.1 + h * q, step, p.2),
        List.mem_flatMap.mpr ⟨h, List.mem_range.mpr hhH, List.mem_map.mpr ⟨p, hp_base, rfl⟩⟩,
        r, hr, ?_⟩
      rw [hzeq, hz_mod, ← hk_eq, hpeq]
      ring
    · intro p hp
      obtain ⟨h, _, hmem⟩ := List.mem_flatMap.mp hp
      obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨j, _, hpj⟩ := List.mem_flatMap.mp hp0
      have hQle := hlenj j.1 j.2 p0 hpj
      refine ⟨hstep1, hstep_le_q.trans hq_le_t, hQ_ge_rpow.trans (by exact_mod_cast hQle)⟩
    · dsimp [allAPs]
      rw [List.map_flatMap, list_sum_flatMap]
      have hinner : ∀ h : ℕ, ((baseAPs.map (fun p => (p.1 + h * q, step, p.2))).map (fun p => p.2.2)).sum =
          (baseAPs.map Prod.snd).sum := by
        intro h; rw [List.map_map]; rfl
      simp_rw [hinner]
      rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
      calc H_sz * (baseAPs.map Prod.snd).sum ≤ H_sz * (3 * L) := Nat.mul_le_mul_left H_sz hbase_sum
        _ = 3 * (L * H_sz) := by ring

end Part3

section Part4
open Finset Nat Filter
open scoped BigOperators Pointwise Classical
private lemma nfoldSum4_eq_piFinset {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (k : ℕ) (A : Finset G) :
    nfoldSum k A = (Fintype.piFinset (fun _ : Fin k => A)).image (fun f => ∑ i : Fin k, f i) := by
  induction k with
  | zero =>
    ext x
    simp only [nfoldSum, Finset.mem_singleton, Finset.mem_image, Fintype.mem_piFinset]
    constructor
    · rintro rfl; exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
    · rintro ⟨f, _, rfl⟩; simp
  | succ k ih =>
    rw [nfoldSum, ih]
    ext x
    simp only [Finset.mem_add, Finset.mem_image, Fintype.mem_piFinset]
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, a, ha, rfl⟩
      refine ⟨Fin.snoc g a, fun i => ?_, ?_⟩
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using ha
        · simpa using hg j
      · rw [Fin.sum_univ_castSucc]
        simp [Fin.snoc]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨∑ i : Fin k, f i.castSucc,
        ⟨fun i => f i.castSucc, fun i => hf i.castSucc, rfl⟩,
        f (Fin.last k), hf (Fin.last k), (Fin.sum_univ_castSucc f).symm⟩

private lemma subsetSumsMod4_insert (t : ℕ) {A : Finset ℕ} {a : ℕ} (ha : a ∉ A) :
    subsetSumsMod t (insert a A) =
      subsetSumsMod t A ∪ (subsetSumsMod t A).image (· + (a : ZMod t)) := by
  ext z
  simp only [subsetSumsMod, Finset.mem_union, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨B, hB, rfl⟩
    by_cases haB : a ∈ B
    · right
      refine ⟨((∑ x ∈ B.erase a, x : ℕ) : ZMod t), ⟨B.erase a, ?_, rfl⟩, ?_⟩
      · intro x hx
        have hxB := Finset.mem_erase.mp hx
        rcases Finset.mem_insert.mp (hB hxB.2) with rfl | hA
        · exact absurd rfl hxB.1
        · exact hA
      · rw [← Nat.cast_add, add_comm, Finset.add_sum_erase B (fun x => x) haB]
    · left
      refine ⟨B, fun x hx => ?_, rfl⟩
      rcases Finset.mem_insert.mp (hB hx) with rfl | hA
      · exact absurd hx haB
      · exact hA
  · rintro (⟨B, hB, rfl⟩ | ⟨s, ⟨B, hB, rfl⟩, rfl⟩)
    · exact ⟨B, hB.trans (Finset.subset_insert a A), rfl⟩
    · refine ⟨insert a B, Finset.insert_subset_insert a hB, ?_⟩
      rw [Finset.sum_insert (fun h => ha (hB h)), Nat.cast_add, add_comm]

private lemma card_subsetSumsMod4_insert (t : ℕ) {A : Finset ℕ} {a : ℕ} (ha : a ∉ A) :
    (subsetSumsMod t (insert a A)).card =
      (subsetSumsMod t A).card +
        (((subsetSumsMod t A).image (· + (a : ZMod t))) \ subsetSumsMod t A).card := by
  rw [subsetSumsMod4_insert t ha]
  have hu : subsetSumsMod t A ∪ (subsetSumsMod t A).image (· + (a : ZMod t)) =
      subsetSumsMod t A ∪ (((subsetSumsMod t A).image (· + (a : ZMod t))) \ subsetSumsMod t A) :=
    Finset.union_sdiff_self_eq_union.symm
  rw [hu, Finset.card_union_of_disjoint Finset.disjoint_sdiff]

private lemma subsetSumsMod4_mono (t : ℕ) {A B : Finset ℕ} (h : A ⊆ B) :
    subsetSumsMod t A ⊆ subsetSumsMod t B :=
  Finset.image_subset_image (Finset.powerset_mono.mpr h)

private lemma zero_mem_subsetSumsMod4 (t : ℕ) (A : Finset ℕ) : (0 : ZMod t) ∈ subsetSumsMod t A :=
  Finset.mem_image.mpr ⟨∅, Finset.empty_mem_powerset A, by simp⟩

private lemma natCast_sum_zmod4 (m : ℕ) (S : Finset ℕ) :
    ((∑ x ∈ S, x : ℕ) : ZMod m) = ∑ x ∈ S, (x : ZMod m) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.cast_add, ih]

/- ### Section 2: Explicit Isomorphism Between `ker(castHom hgt)` and `ZMod (t / g)` -/

private lemma zmod_castHom_eq_zero_iff_dvd_val {t g : ℕ} [NeZero t] [NeZero g] (hgt : g ∣ t)
    (w : ZMod t) : ZMod.castHom hgt (ZMod g) w = 0 ↔ g ∣ w.val := by
  rw [← ZMod.natCast_eq_zero_iff]
  have h1 : ((w.val : ℕ) : ZMod t) = w := ZMod.natCast_zmod_val w
  have h2 : ZMod.castHom hgt (ZMod g) ((w.val : ℕ) : ZMod t) = ((w.val : ℕ) : ZMod g) :=
    map_natCast (ZMod.castHom hgt (ZMod g)) w.val
  rw [← h2, h1]

private lemma mulG_add {t g : ℕ} [NeZero t] [NeZero g] (hgt : g ∣ t)
    (z₁ z₂ : ZMod (t / g)) :
    ((g * (z₁ + z₂).val : ℕ) : ZMod t) =
      ((g * z₁.val : ℕ) : ZMod t) + ((g * z₂.val : ℕ) : ZMod t) := by
  have hm_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd (NeZero.pos t) hgt) (NeZero.pos g)
  have : NeZero (t / g) := ⟨hm_pos.ne'⟩
  have htm : g * (t / g) = t := Nat.mul_div_cancel' hgt
  have hval : (z₁ + z₂).val = (z₁.val + z₂.val) % (t / g) := ZMod.val_add z₁ z₂
  rw [hval, ← Nat.cast_add, ← mul_add]
  have hdiv := Nat.div_add_mod (z₁.val + z₂.val) (t / g)
  have heq : g * (z₁.val + z₂.val) =
      g * ((z₁.val + z₂.val) % (t / g)) + t * ((z₁.val + z₂.val) / (t / g)) := by
    calc g * (z₁.val + z₂.val)
        = g * ((t / g) * ((z₁.val + z₂.val) / (t / g)) + (z₁.val + z₂.val) % (t / g)) := by rw [hdiv]
      _ = g * ((z₁.val + z₂.val) % (t / g)) + (g * (t / g)) * ((z₁.val + z₂.val) / (t / g)) := by ring
      _ = g * ((z₁.val + z₂.val) % (t / g)) + t * ((z₁.val + z₂.val) / (t / g)) := by rw [htm]
  rw [heq]; push_cast; rw [ZMod.natCast_self, zero_mul, add_zero]

private lemma divG_mulG {t g : ℕ} [NeZero t] [NeZero g] (hgt : g ∣ t)
    (z : ZMod (t / g)) :
    ((((((g * z.val : ℕ) : ZMod t)).val / g : ℕ) : ZMod (t / g))) = z := by
  have hm_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd (NeZero.pos t) hgt) (NeZero.pos g)
  have : NeZero (t / g) := ⟨hm_pos.ne'⟩
  have htm : g * (t / g) = t := Nat.mul_div_cancel' hgt
  have hlt : g * z.val < t := by
    calc g * z.val < g * (t / g) := Nat.mul_lt_mul_of_pos_left (ZMod.val_lt z) (NeZero.pos g)
      _ = t := htm
  rw [ZMod.val_natCast_of_lt hlt, Nat.mul_div_cancel_left _ (NeZero.pos g), ZMod.natCast_zmod_val]

private lemma mulG_divG {t g : ℕ} [NeZero t] [NeZero g] (hgt : g ∣ t)
    {w : ZMod t} (hw : ZMod.castHom hgt (ZMod g) w = 0) :
    ((g * (((w.val / g : ℕ) : ZMod (t / g))).val : ℕ) : ZMod t) = w := by
  have hm_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd (NeZero.pos t) hgt) (NeZero.pos g)
  have : NeZero (t / g) := ⟨hm_pos.ne'⟩
  have htm : g * (t / g) = t := Nat.mul_div_cancel' hgt
  have hdvd : g ∣ w.val := (zmod_castHom_eq_zero_iff_dvd_val hgt w).mp hw
  have hlt : w.val / g < t / g := by
    refine (Nat.div_lt_iff_lt_mul (NeZero.pos g)).mpr ?_
    rw [mul_comm, htm]
    exact ZMod.val_lt w
  rw [ZMod.val_natCast_of_lt hlt, Nat.mul_div_cancel' hdvd, ZMod.natCast_zmod_val]

private lemma mulG_div_nat {t g : ℕ} [NeZero t] [NeZero g] (hgt : g ∣ t)
    {a : ℕ} (ha : g ∣ a) :
    ((g * (((a / g : ℕ) : ZMod (t / g))).val : ℕ) : ZMod t) = (a : ZMod t) := by
  have hm_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd (NeZero.pos t) hgt) (NeZero.pos g)
  have : NeZero (t / g) := ⟨hm_pos.ne'⟩
  have htm : g * (t / g) = t := Nat.mul_div_cancel' hgt
  rw [ZMod.val_natCast]
  have hdiv := Nat.div_add_mod (a / g) (t / g)
  have heq : a = g * ((a / g) % (t / g)) + t * ((a / g) / (t / g)) := by
    calc a = g * (a / g) := (Nat.mul_div_cancel' ha).symm
      _ = g * ((t / g) * ((a / g) / (t / g)) + (a / g) % (t / g)) := by rw [hdiv]
      _ = g * ((a / g) % (t / g)) + (g * (t / g)) * ((a / g) / (t / g)) := by ring
      _ = g * ((a / g) % (t / g)) + t * ((a / g) / (t / g)) := by rw [htm]
  conv_rhs => rw [heq]
  push_cast; rw [ZMod.natCast_self, zero_mul, add_zero]

private lemma divG_add_of_ker {t g : ℕ} [NeZero t] [NeZero g] (hgt : g ∣ t)
    {w₁ w₂ : ZMod t} (hw₁ : ZMod.castHom hgt (ZMod g) w₁ = 0)
    (hw₂ : ZMod.castHom hgt (ZMod g) w₂ = 0) :
    ((((w₁ + w₂).val / g : ℕ) : ZMod (t / g))) =
      ((w₁.val / g : ℕ) : ZMod (t / g)) + ((w₂.val / g : ℕ) : ZMod (t / g)) := by
  set z₁ : ZMod (t / g) := ((w₁.val / g : ℕ) : ZMod (t / g))
  set z₂ : ZMod (t / g) := ((w₂.val / g : ℕ) : ZMod (t / g))
  have h1 : ((g * z₁.val : ℕ) : ZMod t) = w₁ := mulG_divG hgt hw₁
  have h2 : ((g * z₂.val : ℕ) : ZMod t) = w₂ := mulG_divG hgt hw₂
  have hsum : w₁ + w₂ = ((g * (z₁ + z₂).val : ℕ) : ZMod t) := by
    rw [mulG_add hgt z₁ z₂, h1, h2]
  rw [hsum]
  exact divG_mulG hgt (z₁ + z₂)

private lemma divG_nat_of_dvd {t g : ℕ} [NeZero t] [NeZero g] (hgt : g ∣ t)
    {a : ℕ} (ha : g ∣ a) :
    (((((a : ZMod t)).val / g : ℕ) : ZMod (t / g))) = ((a / g : ℕ) : ZMod (t / g)) := by
  have h := mulG_div_nat hgt ha
  rw [← h]
  exact divG_mulG hgt ((a / g : ℕ) : ZMod (t / g))

/-- Transfer a subset `S` of a coset `u + gℤ_t` (with `s₀ ∈ S`) into `ZMod (t / g)` via
`s ↦ divG (s - s₀)`. Preserves cardinality and every shift difference `|(S + a) \ S|` for `g ∣ a`. -/
private lemma coset_transfer_divG {t g : ℕ} [NeZero t] [NeZero g] (hgt : g ∣ t)
    {u : ZMod g} {S : Finset (ZMod t)} (hS : ∀ s ∈ S, ZMod.castHom hgt (ZMod g) s = u)
    {s₀ : ZMod t} (hs₀ : ZMod.castHom hgt (ZMod g) s₀ = u) :
    let S' : Finset (ZMod (t / g)) := S.image (fun s => (((s - s₀).val / g : ℕ) : ZMod (t / g)))
    S'.card = S.card ∧
    ∀ a : ℕ, g ∣ a →
      ((S.image (· + (a : ZMod t))) \ S).card =
        ((S'.image (· + ((a / g : ℕ) : ZMod (t / g)))) \ S').card := by
  intro S'
  let f : ZMod t → ZMod (t / g) := fun s => (((s - s₀).val / g : ℕ) : ZMod (t / g))
  have hf_ker : ∀ s ∈ S, ZMod.castHom hgt (ZMod g) (s - s₀) = 0 := fun s hs => by
    rw [map_sub, hS s hs, hs₀, sub_self]
  have hf_inv : ∀ s : ZMod t, ZMod.castHom hgt (ZMod g) s = u →
      s₀ + ((g * (f s).val : ℕ) : ZMod t) = s := by
    intro s hs
    have hker : ZMod.castHom hgt (ZMod g) (s - s₀) = 0 := by rw [map_sub, hs, hs₀, sub_self]
    rw [mulG_divG hgt hker, add_sub_cancel]
  have hf_inj : Set.InjOn f (S : Set (ZMod t)) := by
    intro s₁ hs₁ s₂ hs₂ heq
    rw [← hf_inv s₁ (hS s₁ hs₁), ← hf_inv s₂ (hS s₂ hs₂), heq]
  refine ⟨Finset.card_image_of_injOn hf_inj, fun a ha => ?_⟩
  have ha_ker : ZMod.castHom hgt (ZMod g) (a : ZMod t) = 0 := by
    rw [map_natCast, ZMod.natCast_eq_zero_iff]; exact ha
  have hf_add : ∀ s : ZMod t, ZMod.castHom hgt (ZMod g) s = u →
      f (s + (a : ZMod t)) = f s + ((a / g : ℕ) : ZMod (t / g)) := by
    intro s hs
    dsimp [f]
    have hrew : s + (a : ZMod t) - s₀ = (s - s₀) + (a : ZMod t) := by abel
    rw [hrew, divG_add_of_ker hgt (by rw [map_sub, hs, hs₀, sub_self]) ha_ker,
      divG_nat_of_dvd hgt ha]
  refine Finset.card_bij (fun x _ => f x) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.mp hx1
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨f s, Finset.mem_image.mpr ⟨s, hsS, rfl⟩,
      (hf_add s (hS s hsS)).symm⟩, fun hmem => ?_⟩
    obtain ⟨s', hs'S, hs'eq⟩ := Finset.mem_image.mp hmem
    have hker_sa : ZMod.castHom hgt (ZMod g) (s + (a : ZMod t)) = u := by
      rw [map_add, hS s hsS, ha_ker, add_zero]
    have hs'eq' : f s' = f (s + (a : ZMod t)) := hs'eq
    have heq_el : s + (a : ZMod t) = s' := by
      rw [← hf_inv (s + (a : ZMod t)) hker_sa, ← hf_inv s' (hS s' hs'S), hs'eq']
    exact hx2 (heq_el ▸ hs'S)
  · intro x₁ hx₁ x₂ hx₂ heq
    obtain ⟨s₁, hs₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hx₁).1
    obtain ⟨s₂, hs₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hx₂).1
    have h1 : ZMod.castHom hgt (ZMod g) (s₁ + (a : ZMod t)) = u := by
      rw [map_add, hS s₁ hs₁, ha_ker, add_zero]
    have h2 : ZMod.castHom hgt (ZMod g) (s₂ + (a : ZMod t)) = u := by
      rw [map_add, hS s₂ hs₂, ha_ker, add_zero]
    rw [← hf_inv _ h1, ← hf_inv _ h2, heq]
  · intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨s + (a : ZMod t), Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨s, hsS, rfl⟩, fun hmem => ?_⟩,
      hf_add s (hS s hsS)⟩
    apply hz2
    rw [← hf_add s (hS s hsS)]
    exact Finset.mem_image.mpr ⟨s + (a : ZMod t), hmem, rfl⟩

/-- Injectivity of `a ↦ ((a / g : ℕ) : ZMod (t / g))` on `T ⊆ Q` when `g ∣ a` for all `a ∈ T`,
`g ∣ t`, and all elements of `T ∪ {t}` lie in `[y / v, 2 y / v)`. -/
private lemma divG_injOn_Q {y v t g : ℕ} (hv : 1 ≤ v) (ht_lo : y ≤ v * t) (hgt : g ∣ t) (hg : 1 ≤ g)
    {T : Finset ℕ} (hT_rng : ∀ a ∈ T, y ≤ v * a ∧ v * a < 2 * y)
    (hT_dvd : ∀ a ∈ T, g ∣ a) :
    Set.InjOn (fun a : ℕ => ((a / g : ℕ) : ZMod (t / g))) (T : Set ℕ) := by
  intro a₁ ha₁ a₂ ha₂ heq
  have ha₁' : a₁ ∈ T := Finset.mem_coe.mp ha₁
  have ha₂' : a₂ ∈ T := Finset.mem_coe.mp ha₂
  have h1 := hT_rng a₁ ha₁'
  have h2 := hT_rng a₂ ha₂'
  have hd1 := hT_dvd a₁ ha₁'
  have hd2 := hT_dvd a₂ ha₂'
  have hm_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd (by nlinarith) hgt) (by omega)
  have htm : g * (t / g) = t := Nat.mul_div_cancel' hgt
  wlog hle : a₁ ≤ a₂ generalizing a₁ a₂
  · exact (this ha₂ ha₁ heq.symm ha₂' ha₁' h2 h1 hd2 hd1 (by omega)).symm
  have hdiff_lt_t : a₂ - a₁ < t := by
    have hmul : v * (a₂ - a₁) < v * t := by
      have : v * (a₂ - a₁) + v * a₁ = v * a₂ := by rw [← mul_add, Nat.sub_add_cancel hle]
      omega
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hdiff_div : a₂ / g - a₁ / g < t / g := by
    have hmul : g * (a₂ / g - a₁ / g) < g * (t / g) := by
      have hsub_eq : g * (a₂ / g - a₁ / g) = a₂ - a₁ := by
        have h1' : g * (a₁ / g) = a₁ := Nat.mul_div_cancel' hd1
        have h2' : g * (a₂ / g) = a₂ := Nat.mul_div_cancel' hd2
        have hle' : a₁ / g ≤ a₂ / g := Nat.div_le_div_right hle
        rw [Nat.mul_sub_left_distrib, h2', h1']
      rw [hsub_eq, htm]
      exact hdiff_lt_t
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hzero : (((a₂ / g - a₁ / g : ℕ) : ZMod (t / g))) = 0 := by
    dsimp at heq
    rw [Nat.cast_sub (Nat.div_le_div_right hle), heq, sub_self]
  have hdvd : (t / g) ∣ (a₂ / g - a₁ / g) := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hsub0 : a₂ / g - a₁ / g = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hdiff_div
  have hdiv_eq : a₁ / g = a₂ / g := by have := Nat.div_le_div_right (c := g) hle; omega
  calc a₁ = g * (a₁ / g) := (Nat.mul_div_cancel' hd1).symm
    _ = g * (a₂ / g) := by rw [hdiv_eq]
    _ = a₂ := Nat.mul_div_cancel' hd2

/-- If `g = Nat.gcd (T.gcd id) t`, then `T.image (fun a => (a / g : ZMod (t / g)))` is not
contained in any proper subgroup of `ZMod (t / g)`. -/
private lemma divG_image_not_subgroup
    (h_sub_ker : ∀ (m : ℕ) [NeZero m] (H : AddSubgroup (ZMod m)),
      ∃ (q : ℕ) (hq : q ∣ m), 1 ≤ q ∧ Nat.card H = m / q ∧
        ∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0)
    (h_proper_iff : ∀ (m q : ℕ) [NeZero m] (hq : q ∣ m) (hq1 : 1 ≤ q)
      (H : AddSubgroup (ZMod m)), (∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0) →
      (H ≠ ⊤ ↔ 2 ≤ q))
    {t : ℕ} [NeZero t] (T : Finset ℕ) :
    let g := Nat.gcd (T.gcd id) t
    let hgt : g ∣ t := Nat.gcd_dvd_right _ _
    have : NeZero (t / g) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos t) hgt)
      (Nat.pos_of_dvd_of_pos hgt (NeZero.pos t))).ne'⟩
    ∀ H : AddSubgroup (ZMod (t / g)), H ≠ ⊤ →
      ¬ ∀ x ∈ T.image (fun a => ((a / g : ℕ) : ZMod (t / g))), x ∈ H := by
  intro g hgt _ H hH hall
  obtain ⟨q, hq_dvd, hq1, _, hH_ker⟩ := h_sub_ker (t / g) H
  have hq2 : 2 ≤ q := (h_proper_iff (t / g) q hq_dvd hq1 H hH_ker).mp hH
  have : NeZero q := ⟨by omega⟩
  have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hgt (NeZero.pos t)
  have hgq_dvd_t : g * q ∣ t := by
    obtain ⟨k, hk⟩ := hq_dvd
    refine ⟨k, ?_⟩
    calc t = g * (t / g) := (Nat.mul_div_cancel' hgt).symm
      _ = g * (q * k) := by rw [hk]
      _ = g * q * k := by ring
  have hgq_dvd_T : g * q ∣ T.gcd id := by
    refine Finset.dvd_gcd fun a ha => ?_
    have hmem : ((a / g : ℕ) : ZMod (t / g)) ∈ H := hall _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    have h0 := (hH_ker _).mp hmem
    rw [map_natCast, ZMod.natCast_eq_zero_iff] at h0
    have hga : g ∣ a := (Nat.gcd_dvd_left (T.gcd id) t).trans (Finset.gcd_dvd ha)
    obtain ⟨k, hk⟩ := h0
    refine ⟨k, ?_⟩
    calc id a = a := rfl
      _ = g * (a / g) := (Nat.mul_div_cancel' hga).symm
      _ = g * (q * k) := by rw [hk]
      _ = g * q * k := by ring
  have hgq_dvd_g : g * q ∣ g := Nat.dvd_gcd hgq_dvd_T hgq_dvd_t
  have hle : g * q ≤ g := Nat.le_of_dvd hg_pos hgq_dvd_g
  nlinarith

private lemma zero_mem_not_coset_of_not_subgroup {m : ℕ} [NeZero m] {X : Finset (ZMod m)}
    (h0 : (0 : ZMod m) ∈ X)
    (hnot : ∀ H : AddSubgroup (ZMod m), H ≠ ⊤ → ¬ ∀ a ∈ X, a ∈ H) :
    ∀ H : AddSubgroup (ZMod m), H ≠ ⊤ → ¬ ∃ x : ZMod m, ∀ a ∈ X, a - x ∈ H := by
  intro H hH ⟨x, hx⟩
  apply hnot H hH
  intro a ha
  have h0x : 0 - x ∈ H := hx 0 h0
  have hax : a - x ∈ H := hx a ha
  have heq : a = (a - x) - (0 - x) := by abel
  rw [heq]
  exact sub_mem hax h0x

/- ### Section 3: Elementary Counting & Asymptotic Helpers -/

private lemma weighted_geom_mean {z Y N A B α β : ℝ}
    (hz : 0 < z) (hY : 0 < Y) (hN : 0 < N) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h1 : A * Y ≤ z) (h2 : B * N / Y ≤ z) :
    A ^ α * B ^ β * N ^ β * Y ^ (α - β) ≤ z ^ (α + β) := by
  have hp1 : (A * Y) ^ α ≤ z ^ α := Real.rpow_le_rpow (by positivity) h1 hα
  have hp2 : (B * N / Y) ^ β ≤ z ^ β := Real.rpow_le_rpow (by positivity) h2 hβ
  have hmul : (A * Y) ^ α * (B * N / Y) ^ β ≤ z ^ α * z ^ β :=
    mul_le_mul hp1 hp2 (by positivity) (by positivity)
  rw [← Real.rpow_add hz] at hmul
  have hlhs : (A * Y) ^ α * (B * N / Y) ^ β = A ^ α * B ^ β * N ^ β * Y ^ (α - β) := by
    rw [Real.mul_rpow hA hY.le, Real.div_rpow (by positivity) hY.le, Real.mul_rpow hB hN.le]
    have hYdiv : Y ^ α / Y ^ β = Y ^ (α - β) := (Real.rpow_sub hY α β).symm
    calc A ^ α * Y ^ α * (B ^ β * N ^ β / Y ^ β)
        = A ^ α * B ^ β * N ^ β * (Y ^ α / Y ^ β) := by ring
      _ = A ^ α * B ^ β * N ^ β * Y ^ (α - β) := by rw [hYdiv]
  rwa [← hlhs]

private lemma card_image_div_chain_le {M B : ℕ} (g : ℕ → ℕ)
    (hpos : ∀ k ≤ M, 1 ≤ g k) (hdvd : ∀ k < M, g k ∣ g (k + 1)) (hB : g M ≤ B) :
    ((Finset.range M).image g).card ≤ Nat.log 2 B + 1 := by
  have hg0 : 1 ≤ g 0 := hpos 0 (Nat.zero_le M)
  have hmono : ∀ k₁ k₂, k₁ ≤ k₂ → k₂ ≤ M → g k₁ ≤ g k₂ := by
    intro k₁ k₂ h12 h2M
    induction k₂ with
    | zero =>
      have hk0 : k₁ = 0 := by omega
      rw [hk0]
    | succ k₂ ih =>
      rcases eq_or_lt_of_le h12 with rfl | hlt
      · exact le_rfl
      · exact (ih (by omega) (by omega)).trans (Nat.le_of_dvd (hpos (k₂ + 1) h2M) (hdvd k₂ (by omega)))
  have hjumps : ∀ m ≤ M, 2 ^ ((Finset.range m).filter (fun k => g k ≠ g (k + 1))).card * g 0 ≤ g m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hmM
      have hih := ih (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hne : g m ≠ g (m + 1)
      · rw [if_pos hne, Finset.card_insert_of_notMem (by simp), pow_succ]
        have hstep : 2 * g m ≤ g (m + 1) := by
          obtain ⟨q, hq⟩ := hdvd m (by omega)
          have hq2 : 2 ≤ q := by
            have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; have := hpos (m + 1) hmM; omega
            have hq1 : q ≠ 1 := by intro h1; rw [h1, mul_one] at hq; exact hne hq.symm
            omega
          have : g m * 2 ≤ g m * q := Nat.mul_le_mul_left (g m) hq2
          linarith
        nlinarith
      · rw [if_neg hne]
        exact hih.trans (Nat.le_of_dvd (hpos (m + 1) hmM) (hdvd m (by omega)))
  set J := (Finset.range M).filter (fun k => g k ≠ g (k + 1))
  have hpow_le : 2 ^ J.card ≤ B := by
    have h1 := hjumps M le_rfl
    have h2 : 2 ^ J.card ≤ 2 ^ J.card * g 0 := Nat.le_mul_of_pos_right _ hg0
    exact (h2.trans h1).trans hB
  have hB_pos : 1 ≤ B := (hmono 0 M (Nat.zero_le M) le_rfl).trans hB |> le_trans hg0
  have hJ_le : J.card ≤ Nat.log 2 B :=
    (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hpow_le
  by_cases hM0 : M = 0
  · subst hM0; simp
  -- Every value v ∈ ((range M).image g).erase (g (M - 1)) has a max k < M with g k = v;
  -- since v ≠ g (M - 1), k < M - 1 and g k ≠ g (k + 1), giving an injection into J!
  have hcard_img : ((Finset.range M).image g).card ≤ J.card + 1 := by
    set S := (Finset.range M).image g
    have hlast_mem : g (M - 1) ∈ S := Finset.mem_image.mpr ⟨M - 1, Finset.mem_range.mpr (by omega), rfl⟩
    have hcard_er : (S.erase (g (M - 1))).card + 1 = S.card := by
      have := Finset.card_erase_add_one hlast_mem; exact this
    suffices hle : (S.erase (g (M - 1))).card ≤ J.card by omega
    have hne_fib : ∀ v ∈ S.erase (g (M - 1)), ((Finset.range M).filter (fun k => g k = v)).Nonempty := by
      intro v hv
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hv)
      exact ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
    let fmax (v : ℕ) : ℕ :=
      if h : v ∈ S.erase (g (M - 1)) then
        ((Finset.range M).filter (fun k => g k = v)).max' (hne_fib v h)
      else 0
    have hmaps : ∀ v ∈ S.erase (g (M - 1)), fmax v ∈ J := by
      intro v hv
      dsimp [fmax]; rw [dif_pos hv]
      set F := (Finset.range M).filter (fun k => g k = v)
      set k0 := F.max' (hne_fib v hv)
      have hk0_mem : k0 ∈ F := Finset.max'_mem F (hne_fib v hv)
      have hk0_lt : k0 < M := Finset.mem_range.mp (Finset.mem_filter.mp hk0_mem).1
      have hgk0 : g k0 = v := (Finset.mem_filter.mp hk0_mem).2
      have hne_last : v ≠ g (M - 1) := (Finset.mem_erase.mp hv).1
      have hk0_lt' : k0 + 1 < M := by
        by_contra hge
        have : k0 = M - 1 := by omega
        exact hne_last (hgk0 ▸ congrArg g this)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk0_lt, fun heq => ?_⟩
      have hk1_mem : k0 + 1 ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk0_lt', heq.symm.trans hgk0⟩
      have := Finset.le_max' F (k0 + 1) hk1_mem
      omega
    have hinj : Set.InjOn fmax (S.erase (g (M - 1)) : Set ℕ) := by
      intro v₁ hv₁ v₂ hv₂ heq
      have hv₁' := Finset.mem_coe.mp hv₁
      have hv₂' := Finset.mem_coe.mp hv₂
      dsimp [fmax] at heq
      rw [dif_pos hv₁', dif_pos hv₂'] at heq
      have h1 := (Finset.mem_filter.mp (Finset.max'_mem _ (hne_fib v₁ hv₁'))).2
      have h2 := (Finset.mem_filter.mp (Finset.max'_mem _ (hne_fib v₂ hv₂'))).2
      rw [← h1, ← h2, heq]
    calc (S.erase (g (M - 1))).card
        = ((S.erase (g (M - 1))).image fmax).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ J.card := Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)
  omega

private lemma monotone_exp_steps_le {M : ℕ} {B : ℝ} (f : ℕ → ℕ)
    (hf0 : 1 ≤ f 0) (hmono : ∀ k < M, f k ≤ f (k + 1)) (hB : (f M : ℝ) ≤ B)
    (K : Finset ℕ) (hKM : K ⊆ Finset.range M)
    (hstep : ∀ k ∈ K, (3 / 2 : ℝ) * (f k : ℝ) ≤ (f (k + 1) : ℝ)) :
    (K.card : ℝ) ≤ Real.log B / Real.log (3 / 2 : ℝ) := by
  have hpow : ∀ m ≤ M, (3 / 2 : ℝ) ^ (K.filter (fun k => k < m)).card * (f 0 : ℝ) ≤ (f m : ℝ) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hmM
      have hih := ih (by omega)
      have hsplit : K.filter (fun k => k < m + 1) =
          if m ∈ K then insert m (K.filter (fun k => k < m)) else K.filter (fun k => k < m) := by
        ext k; split_ifs with hmK <;> simp only [Finset.mem_filter, Finset.mem_insert]
        · constructor
          · rintro ⟨hkK, hlt⟩
            rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with rfl | hlt'
            · exact Or.inl rfl
            · exact Or.inr ⟨hkK, hlt'⟩
          · rintro (rfl | ⟨hkK, hlt⟩)
            · exact ⟨hmK, Nat.lt_succ_self k⟩
            · exact ⟨hkK, Nat.lt_succ_of_lt hlt⟩
        · constructor
          · rintro ⟨hkK, hlt⟩
            refine ⟨hkK, ?_⟩
            rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with rfl | hlt'
            · exact absurd hkK hmK
            · exact hlt'
          · rintro ⟨hkK, hlt⟩; exact ⟨hkK, Nat.lt_succ_of_lt hlt⟩
      rw [hsplit]
      by_cases hmK : m ∈ K
      · rw [if_pos hmK, Finset.card_insert_of_notMem (by simp), pow_succ]
        have hs := hstep m hmK
        calc (3 / 2 : ℝ) ^ (K.filter (fun k => k < m)).card * (3 / 2 : ℝ) * (f 0 : ℝ)
            = (3 / 2 : ℝ) * ((3 / 2 : ℝ) ^ (K.filter (fun k => k < m)).card * (f 0 : ℝ)) := by ring
          _ ≤ (3 / 2 : ℝ) * (f m : ℝ) := mul_le_mul_of_nonneg_left hih (by norm_num)
          _ ≤ (f (m + 1) : ℝ) := hs
      · rw [if_neg hmK]
        have hle : (f m : ℝ) ≤ (f (m + 1) : ℝ) := by exact_mod_cast hmono m (by omega)
        exact hih.trans hle
  have hfilt : K.filter (fun k => k < M) = K :=
    Finset.filter_true_of_mem fun k hk => Finset.mem_range.mp (hKM hk)
  have h1 := hpow M le_rfl
  rw [hfilt] at h1
  have hf0_r : (1 : ℝ) ≤ (f 0 : ℝ) := by exact_mod_cast hf0
  have h2 : (3 / 2 : ℝ) ^ K.card ≤ B := by
    calc (3 / 2 : ℝ) ^ K.card = (3 / 2 : ℝ) ^ K.card * 1 := (mul_one _).symm
      _ ≤ (3 / 2 : ℝ) ^ K.card * (f 0 : ℝ) := mul_le_mul_of_nonneg_left hf0_r (by positivity)
      _ ≤ (f M : ℝ) := h1
      _ ≤ B := hB
  have hlog_pos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog_pos]
  have hB_pos : 0 < B := lt_of_lt_of_le (by positivity) h2
  have hlog := Real.log_le_log (by positivity) h2
  rwa [Real.log_pow] at hlog

private lemma monotone_lin_steps_le {M : ℕ} {B δ : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (f : ℕ → ℕ)
    (hmono : ∀ k < M, f k ≤ f (k + 1))
    (K : Finset ℕ) (hKM : K ⊆ Finset.range M)
    (hstep : ∀ k ∈ K, (f k : ℝ) ≤ B ∧ (f k : ℝ) + δ ≤ (f (k + 1) : ℝ)) :
    (K.card : ℝ) ≤ B / δ + 1 := by
  by_cases hKne : K.Nonempty
  · set kmax := K.max' hKne
    have hkmax_mem : kmax ∈ K := Finset.max'_mem K hKne
    have hkmax_lt : kmax < M := Finset.mem_range.mp (hKM hkmax_mem)
    have htele : ∀ m ≤ M, ((K.filter (fun k => k < m)).card : ℝ) * δ ≤ (f m : ℝ) := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hmM
        have hih := ih (by omega)
        have hsplit : K.filter (fun k => k < m + 1) =
            if m ∈ K then insert m (K.filter (fun k => k < m)) else K.filter (fun k => k < m) := by
          ext k; split_ifs with hmK <;> simp only [Finset.mem_filter, Finset.mem_insert]
          · constructor
            · rintro ⟨hkK, hlt⟩
              rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with rfl | hlt'
              · exact Or.inl rfl
              · exact Or.inr ⟨hkK, hlt'⟩
            · rintro (rfl | ⟨hkK, hlt⟩)
              · exact ⟨hmK, Nat.lt_succ_self k⟩
              · exact ⟨hkK, Nat.lt_succ_of_lt hlt⟩
          · constructor
            · rintro ⟨hkK, hlt⟩
              refine ⟨hkK, ?_⟩
              rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with rfl | hlt'
              · exact absurd hkK hmK
              · exact hlt'
            · rintro ⟨hkK, hlt⟩; exact ⟨hkK, Nat.lt_succ_of_lt hlt⟩
        rw [hsplit]
        by_cases hmK : m ∈ K
        · rw [if_pos hmK, Finset.card_insert_of_notMem (by simp), Nat.cast_add, Nat.cast_one]
          have hs := (hstep m hmK).2
          linarith
        · rw [if_neg hmK]
          have hle : (f m : ℝ) ≤ (f (m + 1) : ℝ) := by exact_mod_cast hmono m (by omega)
          linarith
    have h1 := htele kmax hkmax_lt.le
    have h2 : K.filter (fun k => k < kmax) = K.erase kmax := by
      ext k; simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hkK, hlt⟩; exact ⟨hlt.ne, hkK⟩
      · rintro ⟨hne, hkK⟩
        have hle := Finset.le_max' K k hkK
        exact ⟨hkK, lt_of_le_of_ne hle hne⟩
    rw [h2] at h1
    have hcard_er : (K.erase kmax).card + 1 = K.card := Finset.card_erase_add_one hkmax_mem
    have hcard_r : ((K.erase kmax).card : ℝ) = (K.card : ℝ) - 1 := by
      have : ((K.erase kmax).card : ℝ) + 1 = (K.card : ℝ) := by exact_mod_cast hcard_er
      linarith
    rw [hcard_r] at h1
    have hfk : (f kmax : ℝ) ≤ B := (hstep kmax hkmax_mem).1
    have h3 : ((K.card : ℝ) - 1) * δ ≤ B := h1.trans hfk
    have h4 : (K.card : ℝ) - 1 ≤ B / δ := (le_div_iff₀ hδ).mpr h3
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hKne
    subst hKne; simp; positivity

private lemma list_cover_card_le {Q A : Finset ℕ} (hAQ : A ⊆ Q) (g : ℕ) :
    ∀ l : List (ℕ × ℕ × ℕ),
      (∀ a ∈ A, ∃ p ∈ l, ∃ k < p.2.2, a = g * p.1 + (g * p.2.1) * k) →
      A.card ≤ (l.map (fun p =>
        ((Finset.range p.2.2).filter (fun k => g * p.1 + (g * p.2.1) * k ∈ Q)).card)).sum := by
  intro l
  induction l generalizing A with
  | nil =>
    intro hcov
    have hA0 : A = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun a ha => by
      obtain ⟨p, hp, _⟩ := hcov a ha; simp at hp
    subst hA0; simp
  | cons p rest ih =>
    intro hcov
    set A1 := A.filter (fun a => ∃ k < p.2.2, a = g * p.1 + (g * p.2.1) * k)
    set A2 := A.filter (fun a => ¬ ∃ k < p.2.2, a = g * p.1 + (g * p.2.1) * k)
    have hsplit : A1.card + A2.card = A.card := Finset.card_filter_add_card_filter_not _
    have hA1_le : A1.card ≤ ((Finset.range p.2.2).filter (fun k => g * p.1 + (g * p.2.1) * k ∈ Q)).card := by
      have hsub : A1 ⊆ ((Finset.range p.2.2).filter (fun k => g * p.1 + (g * p.2.1) * k ∈ Q)).image
          (fun k => g * p.1 + (g * p.2.1) * k) := by
        intro a ha
        obtain ⟨haA, k, hk, rfl⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hAQ haA⟩, rfl⟩
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    have hA2_cov : ∀ a ∈ A2, ∃ q ∈ rest, ∃ k < q.2.2, a = g * q.1 + (g * q.2.1) * k := by
      intro a ha
      obtain ⟨haA, hnot⟩ := Finset.mem_filter.mp ha
      obtain ⟨q, hq, k, hk, hqa⟩ := hcov a haA
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact absurd ⟨k, hk, hqa⟩ hnot
      · exact ⟨q, hq', k, hk, hqa⟩
    have hA2_le : A2.card ≤ (rest.map (fun p =>
        ((Finset.range p.2.2).filter (fun k => g * p.1 + (g * p.2.1) * k ∈ Q)).card)).sum :=
      ih ((Finset.filter_subset _ _).trans hAQ) hA2_cov
    simp only [List.map_cons, List.sum_cons]
    omega

/- ### Section 4: Claims 1 & 2 (Growth Phase and Unsaturated Phase Gains) -/

/-- Claim 1 (small branch): if `|Σ(g, B)| < |A_rem| / 2`, some `a ∈ A_rem` expands `Σ(g, B)` by ≥ 3/2×. -/
private lemma growth_gain_small
    (h_dcount : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d : ℕ),
      d < A.card → ((Gset A d).card : ℝ) ≤ (A.card : ℝ) ^ 2 / ((A.card : ℝ) - (d : ℝ)))
    {y v t g : ℕ} [NeZero t] [NeZero g] (hv : 1 ≤ v) (ht_lo : y ≤ v * t) (hgt : g ∣ t)
    {B A_rem : Finset ℕ} (hdisj : Disjoint B A_rem)
    (hA_rng : ∀ a ∈ A_rem, y ≤ v * a ∧ v * a < 2 * y)
    (hA_dvd : ∀ a ∈ A_rem, g ∣ a)
    (hsmall : (subsetSumsMod t (B.filter (fun x => g ∣ x))).card < A_rem.card / 2) :
    ∃ a ∈ A_rem,
      (3 / 2 : ℝ) * ((subsetSumsMod t (B.filter (fun x => g ∣ x))).card : ℝ) ≤
        ((subsetSumsMod t ((insert a B).filter (fun x => g ∣ x))).card : ℝ) := by
  set Bg := B.filter (fun x => g ∣ x)
  set S := subsetSumsMod t Bg
  have hm_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd (NeZero.pos t) hgt) (NeZero.pos g)
  have : NeZero (t / g) := ⟨hm_pos.ne'⟩
  have hS_ker : ∀ s ∈ S, ZMod.castHom hgt (ZMod g) s = 0 := by
    intro s hs
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hs
    rw [map_natCast, natCast_sum_zmod4]
    refine Finset.sum_eq_zero fun x hx => ?_
    exact (ZMod.natCast_eq_zero_iff x g).mpr (Finset.mem_filter.mp (Finset.mem_powerset.mp hC hx)).2
  obtain ⟨hS'_card, hS'_sdiff⟩ := coset_transfer_divG hgt hS_ker (map_zero _)
  set S' : Finset (ZMod (t / g)) := S.image (fun s => (((s - 0).val / g : ℕ) : ZMod (t / g)))
  have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, zero_mem_subsetSumsMod4 t Bg⟩
  set d := S.card / 2
  have hd_lt : d < S'.card := by rw [hS'_card]; dsimp [d]; omega
  have hdc := h_dcount (t / g) S' d hd_lt
  rw [hS'_card] at hdc
  have hG_le : ((Gset S' d).card : ℝ) ≤ 2 * (S.card : ℝ) := by
    have hden : (S.card : ℝ) / 2 ≤ (S.card : ℝ) - (d : ℝ) := by
      have : 2 * d ≤ S.card := by dsimp [d]; omega
      have : (2 : ℝ) * (d : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast this
      linarith
    have hS_pos_r : (0 : ℝ) < S.card := by exact_mod_cast hS_pos
    have hfrac : (S.card : ℝ) ^ 2 / ((S.card : ℝ) - (d : ℝ)) ≤ 2 * (S.card : ℝ) := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    exact hdc.trans hfrac
  set C := A_rem.image (fun a => ((a / g : ℕ) : ZMod (t / g)))
  have hC_card : C.card = A_rem.card :=
    Finset.card_image_of_injOn (divG_injOn_Q hv ht_lo hgt (NeZero.pos g) hA_rng hA_dvd)
  have hG_lt_C : (Gset S' d).card < C.card := by
    rw [hC_card]
    have h2S_lt : 2 * S.card < A_rem.card := by omega
    have h2S_r : (2 : ℝ) * (S.card : ℝ) < (A_rem.card : ℝ) := by exact_mod_cast h2S_lt
    have hG_lt_r : ((Gset S' d).card : ℝ) < (A_rem.card : ℝ) := hG_le.trans_lt h2S_r
    exact_mod_cast hG_lt_r
  have hex : ∃ z ∈ C, z ∉ Gset S' d := by
    by_contra hall; push Not at hall
    have := Finset.card_le_card (show C ⊆ Gset S' d from hall)
    omega
  obtain ⟨z, hzC, hz_not⟩ := hex
  obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hzC
  have ha_notB : a ∉ B := Finset.disjoint_right.mp hdisj haA
  have ha_notBg : a ∉ Bg := fun h => ha_notB (Finset.mem_filter.mp h).1
  have hfilt_ins : (insert a B).filter (fun x => g ∣ x) = insert a Bg := by
    rw [Finset.filter_insert, if_pos (hA_dvd a haA)]
  refine ⟨a, haA, ?_⟩
  rw [hfilt_ins, card_subsetSumsMod4_insert t ha_notBg]
  have hsdiff_gt : d < ((S'.image (· + ((a / g : ℕ) : ZMod (t / g)))) \ S').card := by
    simp only [Gset, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hz_not
    exact hz_not
  rw [← hS'_sdiff a (hA_dvd a haA)] at hsdiff_gt
  have hgain : S.card / 2 + 1 ≤ ((S.image (· + (a : ZMod t))) \ S).card := by omega
  have hgain_r : (S.card : ℝ) / 2 ≤ (((S.image (· + (a : ZMod t))) \ S).card : ℝ) := by
    have : S.card ≤ 2 * (S.card / 2 + 1) := by omega
    have h1 : (S.card : ℝ) ≤ 2 * (((S.card / 2 + 1 : ℕ) : ℝ)) := by exact_mod_cast this
    have h2 : ((S.card / 2 + 1 : ℕ) : ℝ) ≤ (((S.image (· + (a : ZMod t))) \ S).card : ℝ) := by
      exact_mod_cast hgain
    linarith
  push_cast
  linarith

/-- Claim 1 (large branch): if `|A_rem| / 2 ≤ |Σ(g, B)|` and `2 * |Σ(g, B)| < t / g`,
then by `H2` (COS) some `a ∈ A_rem` expands `Σ(g, B)` by at least `|A_rem| / 8`. -/
private lemma growth_gain_large
    (hH2 : H2)
    (h_sub_ker : ∀ (m : ℕ) [NeZero m] (H : AddSubgroup (ZMod m)),
      ∃ (q : ℕ) (hq : q ∣ m), 1 ≤ q ∧ Nat.card H = m / q ∧
        ∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0)
    (h_proper_iff : ∀ (m q : ℕ) [NeZero m] (hq : q ∣ m) (hq1 : 1 ≤ q)
      (H : AddSubgroup (ZMod m)), (∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0) →
      (H ≠ ⊤ ↔ 2 ≤ q))
    (h_stable : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d k : ℕ),
      nfoldSum k (Gset A d) ⊆ Gset A (k * d))
    (h_dcount : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d : ℕ),
      d < A.card → ((Gset A d).card : ℝ) ≤ (A.card : ℝ) ^ 2 / ((A.card : ℝ) - (d : ℝ)))
    {y v t : ℕ} [NeZero t] (hv : 1 ≤ v) (ht_lo : y ≤ v * t)
    {B A_rem : Finset ℕ} (hdisj : Disjoint B A_rem) (hA_ne : 1 ≤ A_rem.card)
    (hA_rng : ∀ a ∈ A_rem, y ≤ v * a ∧ v * a < 2 * y)
    (hge : A_rem.card / 2 ≤ (subsetSumsMod t (B.filter (fun x => Nat.gcd (A_rem.gcd id) t ∣ x))).card)
    (hlt_m : 2 * (subsetSumsMod t (B.filter (fun x => Nat.gcd (A_rem.gcd id) t ∣ x))).card <
      t / Nat.gcd (A_rem.gcd id) t) :
    let g := Nat.gcd (A_rem.gcd id) t
    ∃ a ∈ A_rem,
      ((subsetSumsMod t (B.filter (fun x => g ∣ x))).card : ℝ) + (A_rem.card : ℝ) / 8 ≤
        ((subsetSumsMod t ((insert a B).filter (fun x => g ∣ x))).card : ℝ) := by
  set g := Nat.gcd (A_rem.gcd id) t
  have hgt : g ∣ t := Nat.gcd_dvd_right _ _
  have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hgt (NeZero.pos t)
  have : NeZero g := ⟨hg_pos.ne'⟩
  have hm_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd (NeZero.pos t) hgt) hg_pos
  have : NeZero (t / g) := ⟨hm_pos.ne'⟩
  have hA_dvd : ∀ a ∈ A_rem, g ∣ a := fun a ha =>
    (Nat.gcd_dvd_left (A_rem.gcd id) t).trans (Finset.gcd_dvd ha)
  set Bg := B.filter (fun x => g ∣ x)
  set S := subsetSumsMod t Bg
  have hS_ker : ∀ s ∈ S, ZMod.castHom hgt (ZMod g) s = 0 := by
    intro s hs
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hs
    rw [map_natCast, natCast_sum_zmod4]
    refine Finset.sum_eq_zero fun x hx => ?_
    exact (ZMod.natCast_eq_zero_iff x g).mpr (Finset.mem_filter.mp (Finset.mem_powerset.mp hC hx)).2
  obtain ⟨hS'_card, hS'_sdiff⟩ := coset_transfer_divG hgt hS_ker (map_zero _)
  set S' : Finset (ZMod (t / g)) := S.image (fun s => (((s - 0).val / g : ℕ) : ZMod (t / g)))
  set d₀ : ℕ := (A_rem.card - 1) / 8
  have hd₀_lt : (d₀ : ℝ) < (A_rem.card : ℝ) / 8 := by
    have h1 : 8 * d₀ ≤ A_rem.card - 1 := by dsimp [d₀]; omega
    have h2 : 8 * d₀ < A_rem.card := by omega
    have h2r : (8 : ℝ) * (d₀ : ℝ) < (A_rem.card : ℝ) := by exact_mod_cast h2
    linarith
  dsimp only
  by_contra hno
  push Not at hno
  -- Every a ∈ A_rem has gain < A_rem.card / 8, hence gain ≤ d₀, hence (a / g) ∈ Gset S' d₀!
  set C := A_rem.image (fun a => ((a / g : ℕ) : ZMod (t / g)))
  have hC_card : C.card = A_rem.card :=
    Finset.card_image_of_injOn (divG_injOn_Q hv ht_lo hgt hg_pos hA_rng hA_dvd)
  have hC_sub : C ⊆ Gset S' d₀ := by
    intro z hz
    obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hz
    have ha_notB : a ∉ B := Finset.disjoint_right.mp hdisj haA
    have ha_notBg : a ∉ Bg := fun h => ha_notB (Finset.mem_filter.mp h).1
    have hfilt_ins : (insert a B).filter (fun x => g ∣ x) = insert a Bg := by
      rw [Finset.filter_insert, if_pos (hA_dvd a haA)]
    have hlt := hno a haA
    rw [hfilt_ins, card_subsetSumsMod4_insert t ha_notBg] at hlt
    push_cast at hlt
    have hgain_lt : (((S.image (· + (a : ZMod t))) \ S).card : ℝ) < (A_rem.card : ℝ) / 8 := by linarith
    have hgain_le : ((S.image (· + (a : ZMod t))) \ S).card ≤ d₀ := by
      have h8 : 8 * ((S.image (· + (a : ZMod t))) \ S).card < A_rem.card := by
        have : (8 : ℝ) * (((S.image (· + (a : ZMod t))) \ S).card : ℝ) < (A_rem.card : ℝ) := by linarith
        exact_mod_cast this
      dsimp [d₀]; omega
    rw [hS'_sdiff a (hA_dvd a haA)] at hgain_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgain_le⟩
  have h0_mem : (0 : ZMod (t / g)) ∈ Gset S' d₀ := by
    rw [Gset, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : S'.image (· + (0 : ZMod (t / g))) = S' := by simp
    rw [this, Finset.sdiff_self, Finset.card_empty]
    exact Nat.zero_le _
  set C0 := insert (0 : ZMod (t / g)) C
  have hC0_sub : C0 ⊆ Gset S' d₀ := Finset.insert_subset h0_mem hC_sub
  have hC0_not_coset : ∀ H : AddSubgroup (ZMod (t / g)), H ≠ ⊤ →
      ¬ ∃ x : ZMod (t / g), ∀ a ∈ C0, a - x ∈ H := by
    refine zero_mem_not_coset_of_not_subgroup (Finset.mem_insert_self 0 C) fun H hH hall => ?_
    exact divG_image_not_subgroup h_sub_ker h_proper_iff A_rem H hH fun x hx =>
      hall x (Finset.mem_insert_of_mem hx)
  set r_k : ℕ := 4 * S.card / A_rem.card
  have hrk1 : 1 ≤ r_k := by
    dsimp [r_k]
    refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
    have : A_rem.card ≤ 2 * (A_rem.card / 2) + 1 := by omega
    have hS1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, zero_mem_subsetSumsMod4 t Bg⟩
    omega
  have hrk_d0_lt : ((r_k * d₀ : ℕ) : ℝ) < (S.card : ℝ) / 2 := by
    have hrk_le : (r_k : ℝ) ≤ 4 * (S.card : ℝ) / (A_rem.card : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < A_rem.card))]
      have : r_k * A_rem.card ≤ 4 * S.card := Nat.div_mul_le_self _ _
      exact_mod_cast this
    have hrk_pos : (0 : ℝ) < r_k := by exact_mod_cast hrk1
    push_cast
    calc (r_k : ℝ) * (d₀ : ℝ) < (r_k : ℝ) * ((A_rem.card : ℝ) / 8) := mul_lt_mul_of_pos_left hd₀_lt hrk_pos
      _ ≤ (4 * (S.card : ℝ) / (A_rem.card : ℝ)) * ((A_rem.card : ℝ) / 8) :=
          mul_le_mul_of_nonneg_right hrk_le (by positivity)
      _ = (S.card : ℝ) / 2 := by field_simp; ring
  have hS_pos_r : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_subsetSumsMod4 t Bg⟩
  have hrk_d0_lt_S : r_k * d₀ < S'.card := by
    rw [hS'_card]
    have : ((r_k * d₀ : ℕ) : ℝ) < (S.card : ℝ) := by linarith
    exact_mod_cast this
  have hmono_nf : nfoldSum r_k C0 ⊆ nfoldSum r_k (Gset S' d₀) := by
    clear hrk1 hrk_d0_lt hrk_d0_lt_S
    induction r_k with
    | zero => exact subset_rfl
    | succ k ih => exact Finset.add_subset_add ih hC0_sub
  have hnf_le_2S : ((nfoldSum r_k C0).card : ℝ) ≤ 2 * (S.card : ℝ) := by
    have h1 : (nfoldSum r_k C0).card ≤ (Gset S' (r_k * d₀)).card :=
      Finset.card_le_card (hmono_nf.trans (h_stable (t / g) S' d₀ r_k))
    have h1r : ((nfoldSum r_k C0).card : ℝ) ≤ ((Gset S' (r_k * d₀)).card : ℝ) := by exact_mod_cast h1
    have hdc := h_dcount (t / g) S' (r_k * d₀) hrk_d0_lt_S
    rw [hS'_card] at hdc
    have hden : (S.card : ℝ) / 2 < (S.card : ℝ) - ((r_k * d₀ : ℕ) : ℝ) := by linarith
    have hfrac : (S.card : ℝ) ^ 2 / ((S.card : ℝ) - ((r_k * d₀ : ℕ) : ℝ)) ≤ 2 * (S.card : ℝ) := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    exact (h1r.trans hdc).trans hfrac
  have hcos := hH2 (t / g) C0 r_k hrk1 hC0_not_coset
  rw [← nfoldSum4_eq_piFinset] at hcos
  have hlt_mr : ((nfoldSum r_k C0).card : ℝ) < ((t / g : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) * (S.card : ℝ) < ((t / g : ℕ) : ℝ) := by exact_mod_cast hlt_m
    linarith
  have hmin_eq : min ((t / g : ℕ) : ℝ) (((r_k + 1 : ℕ) : ℝ) * (C0.card : ℝ) / 2) =
      (((r_k + 1 : ℕ) : ℝ) * (C0.card : ℝ) / 2) := by
    rcases le_total ((t / g : ℕ) : ℝ) (((r_k + 1 : ℕ) : ℝ) * (C0.card : ℝ) / 2) with h | h
    · rw [min_eq_left h] at hcos; linarith
    · exact min_eq_right h
  rw [hmin_eq] at hcos
  have hC0_ge : (A_rem.card : ℝ) ≤ (C0.card : ℝ) := by
    have : C.card ≤ C0.card := Finset.card_le_card (Finset.subset_insert 0 C)
    rw [hC_card] at this
    exact_mod_cast this
  have hbound : (((r_k + 1 : ℕ) : ℝ) * (A_rem.card : ℝ)) ≤ 4 * (S.card : ℝ) := by
    have h1 : (((r_k + 1 : ℕ) : ℝ) * (A_rem.card : ℝ) / 2) ≤ ((nfoldSum r_k C0).card : ℝ) := by
      have : (((r_k + 1 : ℕ) : ℝ) * (A_rem.card : ℝ) / 2) ≤ (((r_k + 1 : ℕ) : ℝ) * (C0.card : ℝ) / 2) := by
        gcongr
      exact this.trans hcos
    linarith
  have hnat : (r_k + 1) * A_rem.card ≤ 4 * S.card := by exact_mod_cast hbound
  have hlt_div := Nat.lt_div_mul_add (a := 4 * S.card) (b := A_rem.card) (by omega)
  have heq_mul : (r_k + 1) * A_rem.card = 4 * S.card / A_rem.card * A_rem.card + A_rem.card := by
    dsimp [r_k]; ring
  omega

/- Claim 2: In an unsaturated phase, some `a ∈ A_rem` expands `Σ_t(B)` by strictly more than `d_step`. -/
set_option maxHeartbeats 800000 in
private lemma unsaturated_step_gain
    {ξ : ℝ}
    (h_sub_ker : ∀ (m : ℕ) [NeZero m] (H : AddSubgroup (ZMod m)),
      ∃ (q : ℕ) (hq : q ∣ m), 1 ≤ q ∧ Nat.card H = m / q ∧
        ∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0)
    (h_proper_iff : ∀ (m q : ℕ) [NeZero m] (hq : q ∣ m) (hq1 : 1 ≤ q)
      (H : AddSubgroup (ZMod m)), (∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0) →
      (H ≠ ⊤ ↔ 2 ≤ q))
    (h_struct : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d : ℕ),
      1 ≤ d → 8 * d < A.card → (A.card : ℝ) < (ξ / 2) * (m : ℝ) →
      (∀ H : AddSubgroup (ZMod m), H ≠ ⊤ → ¬ ∀ x ∈ Gset A d, x ∈ H) →
      ((Gset A d).card : ℝ) ≤ 20 * (A.card : ℝ) / ((A.card : ℝ) / (2 * (d : ℝ))) ^ (1.02 : ℝ) ∨
      ∃ (q : ℕ) (hq : q ∣ m) (u : (ZMod q)ˣ) (a₀ L : ℕ),
        2 ≤ q ∧ 2 ≤ L ∧ L ≤ q ∧ L * (m / q) ≤ 128 * d ∧
        ∀ x ∈ Gset A d, ∃ k < L, u.1 * ZMod.castHom hq (ZMod q) x = ((a₀ + k : ℕ) : ZMod q))
    (h_ap_cover : ∀ (m x0 q a0 L : ℕ), 1 ≤ m → 2 ≤ q → q ∣ m → 1 ≤ L → L ≤ q → ∀ u : (ZMod q)ˣ,
      let H_sz := m / q
      let R := (Finset.Ico x0 (x0 + m)).filter
        (fun z : ℕ => ∃ k < L, u.1 * (z : ZMod q) = ((a0 + k : ℕ) : ZMod q))
      ∃ APs : List (ℕ × ℕ × ℕ),
        (∀ z ∈ R, ∃ p ∈ APs, ∃ k < p.2.2, z = p.1 + p.2.1 * k) ∧
        (∀ p ∈ APs, 1 ≤ p.2.1 ∧ p.2.1 ≤ m ∧ ((L * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ (p.2.2 : ℝ)) ∧
        (APs.map (fun p => p.2.2)).sum ≤ 3 * (L * H_sz))
    {n y r v t d_step : ℕ} [NeZero t]
    (hv : 1 ≤ v) (ht_lo : y ≤ v * t) (ht_lt_n : t ≤ n)
    (hd1 : 1 ≤ d_step)
    {Q B A_rem : Finset ℕ} (hAQ : A_rem ⊆ Q) (hdisj : Disjoint B A_rem)
    (hA_ne : A_rem.Nonempty)
    (hA_rng : ∀ a ∈ A_rem, y ≤ v * a ∧ v * a < 2 * y)
    (hAP_Q : ∀ a b L : ℕ, 1 ≤ b → b ≤ n → (r : ℝ) ^ (1 / 16 : ℝ) ≤ (L : ℝ) →
      (((Finset.range L).filter (fun k => a + b * k ∈ Q)).card : ℝ) ≤
        256 * (L : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ))
    (hlog_nn : 0 ≤ Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ))
    {u : ZMod (Nat.gcd (A_rem.gcd id) t)}
    (hSu_gt_y : (y : ℝ) ^ (3 / 4 : ℝ) <
      (((subsetSumsMod t B).filter
        (fun s => ZMod.castHom (Nat.gcd_dvd_right (A_rem.gcd id) t) _ s = u)).card : ℝ))
    (hSu_lt : (((subsetSumsMod t B).filter
        (fun s => ZMod.castHom (Nat.gcd_dvd_right (A_rem.gcd id) t) _ s = u)).card : ℝ) <
      (ξ / 2) * ((t / Nat.gcd (A_rem.gcd id) t : ℕ) : ℝ))
    (h8d_lt : (8 * d_step : ℝ) ≤ (y : ℝ) ^ (3 / 4 : ℝ))
    (hsmall_contra : 20 * (2 * (d_step : ℝ)) ^ (1.02 : ℝ) / ((y : ℝ) ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ) <
      (A_rem.card : ℝ))
    (hlen_ge : (r : ℝ) ^ (1 / 16 : ℝ) ≤ ((A_rem.card : ℝ) / 3) ^ (1 / 3 : ℝ))
    (hap_contra : 256 * (3 * (128 * (d_step : ℝ))) * (Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ)) <
      (A_rem.card : ℝ)) :
    ∃ a ∈ A_rem,
      (subsetSumsMod t B).card + d_step < (subsetSumsMod t (insert a B)).card := by
  let g := Nat.gcd (A_rem.gcd id) t
  have hgt : g ∣ t := Nat.gcd_dvd_right _ _
  have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hgt (NeZero.pos t)
  have : NeZero g := ⟨hg_pos.ne'⟩
  have hm_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd (NeZero.pos t) hgt) hg_pos
  have : NeZero (t / g) := ⟨hm_pos.ne'⟩
  have hA_dvd : ∀ a ∈ A_rem, g ∣ a := fun a ha =>
    (Nat.gcd_dvd_left (A_rem.gcd id) t).trans (Finset.gcd_dvd ha)
  let Su := (subsetSumsMod t B).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)
  have hSu_gt_y' : (y : ℝ) ^ (3 / 4 : ℝ) < (Su.card : ℝ) := hSu_gt_y
  have hSu_lt' : (Su.card : ℝ) < (ξ / 2) * ((t / g : ℕ) : ℝ) := hSu_lt
  have hSu_ne : Su.Nonempty := by
    apply Finset.card_pos.mp
    have h0 : (0 : ℝ) ≤ (y : ℝ) ^ (3 / 4 : ℝ) := by positivity
    have hpos : (0 : ℝ) < (Su.card : ℝ) := h0.trans_lt hSu_gt_y'
    exact_mod_cast hpos
  obtain ⟨s₀, hs₀⟩ := hSu_ne
  have hs₀_u : ZMod.castHom hgt (ZMod g) s₀ = u := (Finset.mem_filter.mp hs₀).2
  have hSu_u : ∀ s ∈ Su, ZMod.castHom hgt (ZMod g) s = u := fun s hs => (Finset.mem_filter.mp hs).2
  obtain ⟨hSu'_card, hSu'_sdiff⟩ := coset_transfer_divG hgt hSu_u hs₀_u
  set Su' : Finset (ZMod (t / g)) := Su.image (fun s => (((s - s₀).val / g : ℕ) : ZMod (t / g)))
  by_contra hno
  push Not at hno
  -- Show C = A_rem.image (· / g mod (t/g)) ⊆ Gset Su' d_step
  set C := A_rem.image (fun a => ((a / g : ℕ) : ZMod (t / g)))
  have hC_card : C.card = A_rem.card :=
    Finset.card_image_of_injOn (divG_injOn_Q hv ht_lo hgt hg_pos hA_rng hA_dvd)
  have hC_sub : C ⊆ Gset Su' d_step := by
    intro z hz
    obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hz
    have ha_notB : a ∉ B := Finset.disjoint_right.mp hdisj haA
    have hle := hno a haA
    rw [card_subsetSumsMod4_insert t ha_notB] at hle
    have htot_le : (((subsetSumsMod t B).image (· + (a : ZMod t))) \ subsetSumsMod t B).card ≤ d_step := by
      omega
    have hsub_Su : (Su.image (· + (a : ZMod t))) \ Su ⊆
        ((subsetSumsMod t B).image (· + (a : ZMod t))) \ subsetSumsMod t B := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨s, hsSu, rfl⟩ := Finset.mem_image.mp hx1
      have hsB : s ∈ subsetSumsMod t B := (Finset.mem_filter.mp hsSu).1
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨s, hsB, rfl⟩, fun hmem => ?_⟩
      apply hx2
      refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
      rw [map_add, hSu_u s hsSu, map_natCast, (ZMod.natCast_eq_zero_iff a g).mpr (hA_dvd a haA), add_zero]
    have hSu_le : ((Su.image (· + (a : ZMod t))) \ Su).card ≤ d_step :=
      (Finset.card_le_card hsub_Su).trans htot_le
    rw [hSu'_sdiff a (hA_dvd a haA)] at hSu_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSu_le⟩
  have hnot_sub : ∀ H : AddSubgroup (ZMod (t / g)), H ≠ ⊤ → ¬ ∀ x ∈ Gset Su' d_step, x ∈ H :=
    fun H hH hall => divG_image_not_subgroup h_sub_ker h_proper_iff A_rem H hH
      fun x hx => hall x (hC_sub hx)
  have h8d_Su' : 8 * d_step < Su'.card := by
    rw [hSu'_card]
    have : ((8 * d_step : ℕ) : ℝ) < (Su.card : ℝ) := by push_cast; linarith [hSu_gt_y']
    exact_mod_cast this
  have hSu'_lt : (Su'.card : ℝ) < (ξ / 2) * ((t / g : ℕ) : ℝ) := by rw [hSu'_card]; exact hSu_lt'
  rcases h_struct (t / g) Su' d_step hd1 h8d_Su' hSu'_lt hnot_sub with hsmall_G | hAP_G
  · -- Contradict hsmall_contra!
    have hC_le_G : (A_rem.card : ℝ) ≤ ((Gset Su' d_step).card : ℝ) := by
      rw [← hC_card]; exact_mod_cast Finset.card_le_card hC_sub
    have hSu_pos : (0 : ℝ) < (Su.card : ℝ) := by
      have : (0 : ℝ) ≤ (y : ℝ) ^ (3 / 4 : ℝ) := by positivity
      linarith [hSu_gt_y']
    have hrew : 20 * (Su'.card : ℝ) / ((Su'.card : ℝ) / (2 * (d_step : ℝ))) ^ (1.02 : ℝ) =
        20 * (2 * (d_step : ℝ)) ^ (1.02 : ℝ) / (Su.card : ℝ) ^ (0.02 : ℝ) := by
      rw [hSu'_card, Real.div_rpow hSu_pos.le (by positivity)]
      have hpow : (Su.card : ℝ) ^ (1.02 : ℝ) = (Su.card : ℝ) * (Su.card : ℝ) ^ (0.02 : ℝ) := by
        conv_lhs => rw [show (1.02 : ℝ) = 1 + 0.02 by norm_num, Real.rpow_add hSu_pos, Real.rpow_one]
      rw [hpow]
      have h1 : (Su.card : ℝ) ≠ 0 := hSu_pos.ne'
      have h2 : (Su.card : ℝ) ^ (0.02 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hSu_pos _).ne'
      field_simp
    have hden_le : ((y : ℝ) ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ) ≤ (Su.card : ℝ) ^ (0.02 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hSu_gt_y'.le (by norm_num)
    have hy34_pos : (0 : ℝ) < ((y : ℝ) ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ) := by
      have hy_pos : (0 : ℝ) < y := by
        have h1 : 8 * (d_step : ℝ) ≤ (y : ℝ) ^ (3 / 4 : ℝ) := by exact_mod_cast h8d_lt
        have h2 : (0 : ℝ) < (y : ℝ) ^ (3 / 4 : ℝ) := by
          have : (1 : ℝ) ≤ d_step := by exact_mod_cast hd1
          linarith
        by_contra hle; push Not at hle
        have hy0 : y = 0 := by exact_mod_cast le_antisymm hle (Nat.cast_nonneg y)
        subst hy0; simp at h2
      positivity
    have hfrac_le : 20 * (2 * (d_step : ℝ)) ^ (1.02 : ℝ) / (Su.card : ℝ) ^ (0.02 : ℝ) ≤
        20 * (2 * (d_step : ℝ)) ^ (1.02 : ℝ) / ((y : ℝ) ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hy34_pos hden_le
    rw [hrew] at hsmall_G
    linarith
  · -- Structured AP of H-cosets in ZMod (t / g): lift via ap_mod_t_cover and contradict hAP_Q!
    obtain ⟨q, hq_dvd, u_q, a₀, L, hq2, hL2, hLq, hLH_le, hcov_G⟩ := hAP_G
    have : NeZero q := ⟨by omega⟩
    set a_min := A_rem.min' hA_ne
    have ha_min_mem : a_min ∈ A_rem := Finset.min'_mem A_rem hA_ne
    set x0 := a_min / g
    obtain ⟨APs, hAP_cov, hAP_prop, hAP_sum⟩ :=
      h_ap_cover (t / g) x0 q a₀ L hm_pos hq2 hq_dvd (by omega) hLq u_q
    -- Every a ∈ A_rem has a / g ∈ R!
    have hA_in_R : ∀ a ∈ A_rem, a / g ∈ (Finset.Ico x0 (x0 + t / g)).filter
        (fun z : ℕ => ∃ k < L, u_q.1 * (z : ZMod q) = ((a₀ + k : ℕ) : ZMod q)) := by
      intro a haA
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Nat.div_le_div_right (Finset.min'_le A_rem a haA)
      · have hle : a_min ≤ a := Finset.min'_le A_rem a haA
        have h1 := hA_rng a_min ha_min_mem
        have h2 := hA_rng a haA
        have hdiff_lt : a - a_min < t := by
          have hmul : v * (a - a_min) < v * t := by
            have : v * (a - a_min) + v * a_min = v * a := by rw [← mul_add, Nat.sub_add_cancel hle]
            omega
          exact Nat.lt_of_mul_lt_mul_left hmul
        have htm : g * (t / g) = t := Nat.mul_div_cancel' hgt
        have hmul_div : g * (a / g - x0) < g * (t / g) := by
          have hsub_eq : g * (a / g - x0) = a - a_min := by
            rw [Nat.mul_sub_left_distrib, Nat.mul_div_cancel' (hA_dvd a haA),
              Nat.mul_div_cancel' (hA_dvd a_min ha_min_mem)]
          rw [hsub_eq, htm]; exact hdiff_lt
        have hlt_sub : a / g - x0 < t / g := Nat.lt_of_mul_lt_mul_left hmul_div
        have hx0_le : x0 ≤ a / g := Nat.div_le_div_right hle
        omega
      · obtain ⟨k, hkL, hkeq⟩ := hcov_G ((a / g : ℕ) : ZMod (t / g))
          (hC_sub (Finset.mem_image.mpr ⟨a, haA, rfl⟩))
        rw [map_natCast] at hkeq
        exact ⟨k, hkL, hkeq⟩
    have hA_cov_APs : ∀ a ∈ A_rem, ∃ p ∈ APs, ∃ k < p.2.2, a = g * p.1 + (g * p.2.1) * k := by
      intro a haA
      obtain ⟨p, hp, k, hk, hzeq⟩ := hAP_cov (a / g) (hA_in_R a haA)
      refine ⟨p, hp, k, hk, ?_⟩
      calc a = g * (a / g) := (Nat.mul_div_cancel' (hA_dvd a haA)).symm
        _ = g * (p.1 + p.2.1 * k) := by rw [hzeq]
        _ = g * p.1 + (g * p.2.1) * k := by ring
    -- First deduce A_rem.card / 3 ≤ L * (t / g / q), so each AP has length ≥ r^(1/16)!
    have hLH_ge : (A_rem.card : ℝ) / 3 ≤ ((L * (t / g / q) : ℕ) : ℝ) := by
      have hcard_le : A_rem.card ≤ (APs.map (fun p => p.2.2)).sum := by
        have h1 := list_cover_card_le hAQ g APs hA_cov_APs
        have h2 : (APs.map (fun p =>
            ((Finset.range p.2.2).filter (fun k => g * p.1 + (g * p.2.1) * k ∈ Q)).card)).sum ≤
            (APs.map (fun p => p.2.2)).sum := by
          clear h1 hAP_cov hAP_prop hAP_sum hA_cov_APs
          induction APs with
          | nil => simp
          | cons p rest ih =>
            simp only [List.map_cons, List.sum_cons]
            have hp : ((Finset.range p.2.2).filter (fun k => g * p.1 + (g * p.2.1) * k ∈ Q)).card ≤ p.2.2 :=
              (Finset.card_filter_le _ _).trans (by simp)
            omega
        exact h1.trans h2
      have h3 : A_rem.card ≤ 3 * (L * (t / g / q)) := hcard_le.trans hAP_sum
      have h3r : (A_rem.card : ℝ) ≤ 3 * ((L * (t / g / q) : ℕ) : ℝ) := by exact_mod_cast h3
      linarith
    -- Now apply hAP_Q to every p ∈ APs and sum!
    have hsum_Q : ∀ l : List (ℕ × ℕ × ℕ),
        (∀ p ∈ l, 1 ≤ p.2.1 ∧ p.2.1 ≤ t / g ∧ ((L * (t / g / q) : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ (p.2.2 : ℝ)) →
        ((l.map (fun p =>
          ((Finset.range p.2.2).filter (fun k => g * p.1 + (g * p.2.1) * k ∈ Q)).card)).sum : ℝ) ≤
          256 * ((l.map (fun p => p.2.2)).sum : ℝ) * (Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ)) := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons p rest ih =>
        intro hl
        have hp := hl p List.mem_cons_self
        have hrest := ih fun p' hp' => hl p' (List.mem_cons_of_mem _ hp')
        have hb1 : 1 ≤ g * p.2.1 := Nat.mul_pos hg_pos hp.1
        have hbn : g * p.2.1 ≤ n := by
          have h1 : g * p.2.1 ≤ g * (t / g) := Nat.mul_le_mul_left g hp.2.1
          rw [Nat.mul_div_cancel' hgt] at h1
          exact h1.trans ht_lt_n
        have hLp : (r : ℝ) ^ (1 / 16 : ℝ) ≤ (p.2.2 : ℝ) :=
          hlen_ge.trans ((Real.rpow_le_rpow (by positivity) hLH_ge (by norm_num)).trans hp.2.2)
        have hbound_p := hAP_Q (g * p.1) (g * p.2.1) p.2.2 hb1 hbn hLp
        simp only [List.map_cons, List.sum_cons, Nat.cast_add]
        have hrew : 256 * (p.2.2 : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ) =
            256 * (p.2.2 : ℝ) * (Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ)) := by ring
        rw [hrew] at hbound_p
        linarith
    have hA_le_sum : (A_rem.card : ℝ) ≤
        ((APs.map (fun p =>
          ((Finset.range p.2.2).filter (fun k => g * p.1 + (g * p.2.1) * k ∈ Q)).card)).sum : ℝ) := by
      exact_mod_cast list_cover_card_le hAQ g APs hA_cov_APs
    have hS_bound := hsum_Q APs hAP_prop
    have hsum_le : ((APs.map (fun p => p.2.2)).sum : ℝ) ≤ 3 * (128 * (d_step : ℝ)) := by
      have h1 : (APs.map (fun p => p.2.2)).sum ≤ 3 * (128 * d_step) :=
        hAP_sum.trans (Nat.mul_le_mul_left 3 hLH_le)
      have h2 : (((APs.map (fun p => p.2.2)).sum : ℕ) : ℝ) ≤ ((3 * (128 * d_step) : ℕ) : ℝ) :=
        Nat.cast_le.mpr h1
      have hcast : ∀ l : List (ℕ × ℕ × ℕ),
          (l.map (fun p => (p.2.2 : ℝ))).sum = (((l.map (fun p => p.2.2)).sum : ℕ) : ℝ) := by
        intro l
        induction l with
        | nil => simp
        | cons p rest ih => simp [ih]
      rw [hcast APs]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h2
    have hfinal : (A_rem.card : ℝ) ≤
        256 * (3 * (128 * (d_step : ℝ))) * (Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ)) := by
      calc (A_rem.card : ℝ)
          ≤ 256 * ((APs.map (fun p => p.2.2)).sum : ℝ) * (Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ)) :=
            hA_le_sum.trans hS_bound
        _ ≤ 256 * (3 * (128 * (d_step : ℝ))) * (Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ)) := by
            gcongr
    linarith

/- ### Section 5: Greedy Process (`growth_mod_t`, CFP21 Lemma 5.5) and Final Assembly of `H4` -/

set_option maxHeartbeats 1200000 in
private lemma growth_mod_t
    {ξ : ℝ} (hξ_pos : 0 < ξ)
    (hH2 : H2)
    (h_sub_ker : ∀ (m : ℕ) [NeZero m] (H : AddSubgroup (ZMod m)),
      ∃ (q : ℕ) (hq : q ∣ m), 1 ≤ q ∧ Nat.card H = m / q ∧
        ∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0)
    (h_proper_iff : ∀ (m q : ℕ) [NeZero m] (hq : q ∣ m) (hq1 : 1 ≤ q)
      (H : AddSubgroup (ZMod m)), (∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0) →
      (H ≠ ⊤ ↔ 2 ≤ q))
    (h_stable : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d k : ℕ),
      nfoldSum k (Gset A d) ⊆ Gset A (k * d))
    (h_dcount : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d : ℕ),
      d < A.card → ((Gset A d).card : ℝ) ≤ (A.card : ℝ) ^ 2 / ((A.card : ℝ) - (d : ℝ)))
    (h_full : ∀ (d : ℕ) [NeZero d] (A : Finset ℕ),
      (∀ d' : ℕ, d' ∣ d → 2 ≤ d' → d' - 1 ≤ (A.filter (fun a => ¬ d' ∣ a)).card) →
      subsetSumsMod d A = Finset.univ)
    (h_fiber : ∀ (t g : ℕ) [NeZero t] [NeZero g] (hgt : g ∣ t) (A : Finset ℕ) (u : ZMod g),
      ((subsetSumsMod t A).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).Nonempty →
      (subsetSumsMod t (A.filter (fun a => g ∣ a))).card ≤
        ((subsetSumsMod t A).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).card)
    (h_struct : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d : ℕ),
      1 ≤ d → 8 * d < A.card → (A.card : ℝ) < (ξ / 2) * (m : ℝ) →
      (∀ H : AddSubgroup (ZMod m), H ≠ ⊤ → ¬ ∀ x ∈ Gset A d, x ∈ H) →
      ((Gset A d).card : ℝ) ≤ 20 * (A.card : ℝ) / ((A.card : ℝ) / (2 * (d : ℝ))) ^ (1.02 : ℝ) ∨
      ∃ (q : ℕ) (hq : q ∣ m) (u : (ZMod q)ˣ) (a₀ L : ℕ),
        2 ≤ q ∧ 2 ≤ L ∧ L ≤ q ∧ L * (m / q) ≤ 128 * d ∧
        ∀ x ∈ Gset A d, ∃ k < L, u.1 * ZMod.castHom hq (ZMod q) x = ((a₀ + k : ℕ) : ZMod q))
    (h_ap_cover : ∀ (m x0 q a0 L : ℕ), 1 ≤ m → 2 ≤ q → q ∣ m → 1 ≤ L → L ≤ q → ∀ u : (ZMod q)ˣ,
      let H_sz := m / q
      let R := (Finset.Ico x0 (x0 + m)).filter
        (fun z : ℕ => ∃ k < L, u.1 * (z : ZMod q) = ((a0 + k : ℕ) : ZMod q))
      ∃ APs : List (ℕ × ℕ × ℕ),
        (∀ z ∈ R, ∃ p ∈ APs, ∃ k < p.2.2, z = p.1 + p.2.1 * k) ∧
        (∀ p ∈ APs, 1 ≤ p.2.1 ∧ p.2.1 ≤ m ∧ ((L * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ (p.2.2 : ℝ)) ∧
        (APs.map (fun p => p.2.2)).sum ≤ 3 * (L * H_sz))
    {n y r v t ℓ : ℕ} [NeZero t]
    (hℓ : 8 ≤ ℓ) (hℓ_ξ : 80 / (ℓ : ℝ) ≤ ξ / 2)
    (hv : 1 ≤ v) (ht_lo : y ≤ v * t) (ht_hi : v * t < 2 * y) (ht_lt_n : t ≤ n)
    {Q A₁ : Finset ℕ} (hA₁Q : A₁ ⊆ Q)
    (hQ_rng : ∀ x ∈ Q, y ≤ v * x ∧ v * x < 2 * y)
    (hA₁_lo : (Q.card : ℝ) / (24 * (ℓ : ℝ)) ≤ (A₁.card : ℝ))
    (hA₁_div : ∀ d : ℕ, 2 ≤ d → (y : ℝ) ^ (1 / 4 : ℝ) / (24 * (ℓ : ℝ)) ≤ ((A₁.filter (fun x => ¬ d ∣ x)).card : ℝ))
    (hGCD : ∀ T : Finset ℕ, T ⊆ A₁ → A₁.card / 2 ≤ T.card →
      ((T.gcd id : ℕ) : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ))
    (hAP_Q : ∀ a b L : ℕ, 1 ≤ b → b ≤ n → (r : ℝ) ^ (1 / 16 : ℝ) ≤ (L : ℝ) →
      (((Finset.range L).filter (fun k => a + b * k ∈ Q)).card : ℝ) ≤
        256 * (L : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ))
    (hlog_nn : 0 ≤ Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ))
    (hM_ge : (Q.card : ℝ) / (50 * (ℓ : ℝ)) ≤ ((A₁.card / 2 : ℕ) : ℝ))
    (hQ_pos : 1 ≤ Q.card)
    (hy16_lt_div : (y : ℝ) ^ (1 / 16 : ℝ) ≤ (y : ℝ) ^ (1 / 4 : ℝ) / (24 * (ℓ : ℝ)))
    (hy34_lt_tg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) →
      2 * (y : ℝ) ^ (3 / 4 : ℝ) < ((t / g : ℕ) : ℝ))
    (hd_step_bounds :
      let d_step := Nat.floor (2 ^ 14 * (y : ℝ) / (Q.card : ℝ)) + 1
      (8 * (d_step : ℝ)) ≤ (y : ℝ) ^ (3 / 4 : ℝ) ∧
      20 * (2 * (d_step : ℝ)) ^ (1.02 : ℝ) / ((y : ℝ) ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ) <
        (Q.card : ℝ) / (50 * (ℓ : ℝ)) ∧
      (r : ℝ) ^ (1 / 16 : ℝ) ≤ ((Q.card : ℝ) / (150 * (ℓ : ℝ))) ^ (1 / 3 : ℝ) ∧
      256 * (3 * (128 * (d_step : ℝ))) * (Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ)) <
        (Q.card : ℝ) / (50 * (ℓ : ℝ)))
    (hgrowth_budget :
      ((Nat.log 2 (Nat.floor ((y : ℝ) ^ (1 / 16 : ℝ))) + 1 : ℕ) : ℝ) *
        (Real.log (2 * (y : ℝ)) / Real.log (3 / 2 : ℝ) +
          (y : ℝ) ^ (3 / 4 : ℝ) / ((Q.card : ℝ) / (400 * (ℓ : ℝ))) + 1) ≤
        (Q.card : ℝ) / (100 * (ℓ : ℝ))) :
    (80 / (ℓ : ℝ)) * (t : ℝ) ≤ ((subsetSumsMod t A₁).card : ℝ) := by
  set M := A₁.card / 2
  set d_step := Nat.floor (2 ^ 14 * (y : ℝ) / (Q.card : ℝ)) + 1
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hM_pos : 1 ≤ M := by
    have h1 : (0 : ℝ) < (Q.card : ℝ) / (50 * (ℓ : ℝ)) := by
      have : (0 : ℝ) < Q.card := by exact_mod_cast hQ_pos
      positivity
    have h2 : (0 : ℝ) < (M : ℝ) := h1.trans_le hM_ge
    exact_mod_cast h2
  have hd_step_1 : 1 ≤ d_step := Nat.succ_pos _
  have hd_step_gt : 2 ^ 14 * (y : ℝ) / (Q.card : ℝ) < (d_step : ℝ) := by
    dsimp [d_step]; push_cast; exact Nat.lt_floor_add_one _
  -- Define growth / unsaturated / saturated predicate on a pair (B, A_rem)
  let isGrowth (B A_rem : Finset ℕ) : Prop :=
    let g := Nat.gcd (A_rem.gcd id) t
    let hgt : g ∣ t := Nat.gcd_dvd_right _ _
    ∃ u : ZMod g,
      ((subsetSumsMod t B).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).Nonempty ∧
      (((subsetSumsMod t B).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).card : ℝ) ≤
        (y : ℝ) ^ (3 / 4 : ℝ)
  let isUnsat (B A_rem : Finset ℕ) : Prop :=
    ¬ isGrowth B A_rem ∧
    let g := Nat.gcd (A_rem.gcd id) t
    let hgt : g ∣ t := Nat.gcd_dvd_right _ _
    ∃ u : ZMod g,
      (((subsetSumsMod t B).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).card : ℝ) <
        (ξ / 2) * ((t / g : ℕ) : ℝ)
  -- Step function: given (B, A_rem) with B ⊆ A₁, Disjoint B A_rem, B ∪ A_rem = A₁, |B| < M, pick a ∈ A_rem!
  have hstep_ex : ∀ (B A_rem : Finset ℕ),
      B ∪ A_rem = A₁ → Disjoint B A_rem → B.card < M →
      ∃ a ∈ A_rem,
        (isGrowth B A_rem →
          let g := Nat.gcd (A_rem.gcd id) t
          ((subsetSumsMod t (B.filter (fun x => g ∣ x))).card < A_rem.card / 2 →
            (3 / 2 : ℝ) * ((subsetSumsMod t (B.filter (fun x => g ∣ x))).card : ℝ) ≤
              ((subsetSumsMod t ((insert a B).filter (fun x => g ∣ x))).card : ℝ)) ∧
          (A_rem.card / 2 ≤ (subsetSumsMod t (B.filter (fun x => g ∣ x))).card →
            ((subsetSumsMod t (B.filter (fun x => g ∣ x))).card : ℝ) + (Q.card : ℝ) / (400 * (ℓ : ℝ)) ≤
              ((subsetSumsMod t ((insert a B).filter (fun x => g ∣ x))).card : ℝ))) ∧
        (isUnsat B A_rem →
          (subsetSumsMod t B).card + d_step < (subsetSumsMod t (insert a B)).card) := by
    intro B A_rem hunion hdisj hBM
    have hA_sub : A_rem ⊆ A₁ := hunion ▸ Finset.subset_union_right
    have hA_card_ge : M ≤ A_rem.card := by
      have htot := Finset.card_union_of_disjoint hdisj
      rw [hunion] at htot
      omega
    have hA_card_r : (Q.card : ℝ) / (50 * (ℓ : ℝ)) ≤ (A_rem.card : ℝ) :=
      hM_ge.trans (by exact_mod_cast hA_card_ge)
    have hA_ne : A_rem.Nonempty := Finset.card_pos.mp (by omega)
    have hA_rng : ∀ a ∈ A_rem, y ≤ v * a ∧ v * a < 2 * y := fun a ha => hQ_rng a (hA₁Q (hA_sub ha))
    set g := Nat.gcd (A_rem.gcd id) t
    have hgt : g ∣ t := Nat.gcd_dvd_right _ _
    have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hgt (NeZero.pos t)
    have : NeZero g := ⟨hg_pos.ne'⟩
    have hg_le_y16 : (g : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) := by
      have h1 : g ≤ A_rem.gcd id := by
        have hAg_pos : 0 < A_rem.gcd id := by
          obtain ⟨a0, ha0⟩ := hA_ne
          have hlt := hA_rng a0 ha0
          have hy_pos : 0 < y := by
            have := NeZero.pos t; nlinarith
          have ha0_pos : 0 < a0 := by nlinarith
          have : A_rem.gcd id ∣ a0 := Finset.gcd_dvd ha0
          exact Nat.pos_of_dvd_of_pos this ha0_pos
        exact Nat.le_of_dvd hAg_pos (Nat.gcd_dvd_left _ _)
      exact (Nat.cast_le.mpr h1).trans (hGCD A_rem hA_sub hA_card_ge)
    by_cases hG : isGrowth B A_rem
    · obtain ⟨u, hu_ne, hu_le⟩ := hG
      have hfib := h_fiber t g hgt B u hu_ne
      have hBg_le_y34 : ((subsetSumsMod t (B.filter (fun x => g ∣ x))).card : ℝ) ≤ (y : ℝ) ^ (3 / 4 : ℝ) :=
        (Nat.cast_le.mpr hfib).trans hu_le
      by_cases hsm : (subsetSumsMod t (B.filter (fun x => g ∣ x))).card < A_rem.card / 2
      · obtain ⟨a, haA, hgain⟩ := growth_gain_small h_dcount hv ht_lo hgt hdisj hA_rng
          (fun a ha => (Nat.gcd_dvd_left (A_rem.gcd id) t).trans (Finset.gcd_dvd ha)) hsm
        exact ⟨a, haA, ⟨fun _ => ⟨fun _ => hgain, fun hge => absurd hsm (not_lt.mpr hge)⟩,
          fun hu => absurd ⟨u, hu_ne, hu_le⟩ hu.1⟩⟩
      · push Not at hsm
        have hlt_m : 2 * (subsetSumsMod t (B.filter (fun x => g ∣ x))).card < t / g := by
          have h1 := hy34_lt_tg g hg_pos hg_le_y16
          have h2 : (2 : ℝ) * ((subsetSumsMod t (B.filter (fun x => g ∣ x))).card : ℝ) < ((t / g : ℕ) : ℝ) := by
            linarith
          exact_mod_cast h2
        obtain ⟨a, haA, hgain⟩ := growth_gain_large hH2 h_sub_ker h_proper_iff h_stable h_dcount
          hv ht_lo hdisj (by omega) hA_rng hsm hlt_m
        refine ⟨a, haA, ⟨fun _ => ⟨fun hlt => absurd hlt (not_lt.mpr hsm), fun _ => ?_⟩,
          fun hu => absurd ⟨u, hu_ne, hu_le⟩ hu.1⟩⟩
        have hdiv : (Q.card : ℝ) / (400 * (ℓ : ℝ)) ≤ (A_rem.card : ℝ) / 8 := by
          calc (Q.card : ℝ) / (400 * (ℓ : ℝ)) = ((Q.card : ℝ) / (50 * (ℓ : ℝ))) / 8 := by ring
            _ ≤ (A_rem.card : ℝ) / 8 := by gcongr
        linarith
    · by_cases hU : isUnsat B A_rem
      · obtain ⟨_, u, hu_lt⟩ := hU
        have hSu_gt_y : (y : ℝ) ^ (3 / 4 : ℝ) <
            (((subsetSumsMod t B).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).card : ℝ) := by
          -- First show S_u is nonempty using diversity of A₁!
          have hSu_ne : ((subsetSumsMod t B).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).Nonempty := by
            have hg_univ : subsetSumsMod g A₁ = Finset.univ := by
              refine h_full g A₁ fun d' hd'g hd'2 => ?_
              have hd'_le : (d' : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) :=
                (Nat.cast_le.mpr (Nat.le_of_dvd hg_pos hd'g)).trans hg_le_y16
              have hdiv_d' := hA₁_div d' hd'2
              have hle_r : ((d' - 1 : ℕ) : ℝ) ≤ ((A₁.filter (fun x => ¬ d' ∣ x)).card : ℝ) := by
                have : ((d' - 1 : ℕ) : ℝ) ≤ (d' : ℝ) := by exact_mod_cast Nat.sub_le d' 1
                linarith
              exact_mod_cast hle_r
            have hu_mem : u ∈ subsetSumsMod g A₁ := hg_univ ▸ Finset.mem_univ u
            obtain ⟨C, hCA₁, rfl⟩ := Finset.mem_image.mp hu_mem
            have hCB_sub : C ∩ B ⊆ B := Finset.inter_subset_right
            refine ⟨((∑ x ∈ C ∩ B, x : ℕ) : ZMod t),
              Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨C ∩ B, Finset.mem_powerset.mpr hCB_sub, rfl⟩, ?_⟩⟩
            rw [map_natCast]
            have hC_split : C = (C ∩ B) ∪ (C \ B) := by
              ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
            have hdisjC : Disjoint (C ∩ B) (C \ B) :=
              Disjoint.mono_left Finset.inter_subset_right Finset.disjoint_sdiff
            conv_rhs => rw [hC_split]
            rw [Finset.sum_union hdisjC, Nat.cast_add]
            have hzero : ((∑ x ∈ C \ B, x : ℕ) : ZMod g) = 0 := by
              rw [natCast_sum_zmod4]
              refine Finset.sum_eq_zero fun x hx => ?_
              have hxA₁ : x ∈ A₁ := Finset.mem_powerset.mp hCA₁ (Finset.mem_sdiff.mp hx).1
              have hxnotB : x ∉ B := (Finset.mem_sdiff.mp hx).2
              have hxA : x ∈ A_rem := by
                rw [← hunion] at hxA₁
                rcases Finset.mem_union.mp hxA₁ with h | h
                · exact absurd h hxnotB
                · exact h
              exact (ZMod.natCast_eq_zero_iff x g).mpr ((Nat.gcd_dvd_left (A_rem.gcd id) t).trans (Finset.gcd_dvd hxA))
            rw [hzero, add_zero]
          by_contra hle; push Not at hle
          exact hG ⟨u, hSu_ne, hle⟩
        obtain ⟨a, haA, hgain⟩ := unsaturated_step_gain h_sub_ker h_proper_iff h_struct h_ap_cover
          hv ht_lo ht_lt_n hd_step_1 (hA_sub.trans hA₁Q) hdisj hA_ne hA_rng hAP_Q hlog_nn
          hSu_gt_y hu_lt hd_step_bounds.1
          (hd_step_bounds.2.1.trans_le hA_card_r)
          (hd_step_bounds.2.2.1.trans (Real.rpow_le_rpow (by positivity)
            (by calc (Q.card : ℝ) / (150 * (ℓ : ℝ)) = ((Q.card : ℝ) / (50 * (ℓ : ℝ))) / 3 := by ring
                  _ ≤ (A_rem.card : ℝ) / 3 := by gcongr) (by norm_num)))
          (hd_step_bounds.2.2.2.trans_le hA_card_r)
        exact ⟨a, haA, ⟨fun h => absurd h hG, fun _ => hgain⟩⟩
      · -- Saturated: pick any element of A_rem!
        obtain ⟨a, haA⟩ := hA_ne
        exact ⟨a, haA, ⟨fun h => absurd h hG, fun h => absurd h hU⟩⟩
  -- Build the greedy sequence (B k, A k) for k = 0..M by recursion!
  let nextStep (p : Finset ℕ × Finset ℕ) : Finset ℕ × Finset ℕ :=
    if h : p.1 ∪ p.2 = A₁ ∧ Disjoint p.1 p.2 ∧ p.1.card < M then
      let a := (hstep_ex p.1 p.2 h.1 h.2.1 h.2.2).choose
      (insert a p.1, p.2.erase a)
    else p
  let seq : ℕ → Finset ℕ × Finset ℕ := fun k => Nat.rec (∅, A₁) (fun _ p => nextStep p) k
  have hinv : ∀ k ≤ M, (seq k).1 ∪ (seq k).2 = A₁ ∧ Disjoint (seq k).1 (seq k).2 ∧ (seq k).1.card = k := by
    intro k
    induction k with
    | zero => intro _; simp [seq]
    | succ k ih =>
      intro hkM
      obtain ⟨hu, hd, hc⟩ := ih (by omega)
      change (nextStep (seq k)).1 ∪ (nextStep (seq k)).2 = A₁ ∧
        Disjoint (nextStep (seq k)).1 (nextStep (seq k)).2 ∧ (nextStep (seq k)).1.card = k + 1
      dsimp only [nextStep]
      have hcond : (seq k).1 ∪ (seq k).2 = A₁ ∧ Disjoint (seq k).1 (seq k).2 ∧ (seq k).1.card < M :=
        ⟨hu, hd, by omega⟩
      rw [dif_pos hcond]
      set a := (hstep_ex (seq k).1 (seq k).2 hcond.1 hcond.2.1 hcond.2.2).choose
      have ha_mem : a ∈ (seq k).2 :=
        (hstep_ex (seq k).1 (seq k).2 hcond.1 hcond.2.1 hcond.2.2).choose_spec.1
      have ha_notB : a ∉ (seq k).1 := Finset.disjoint_right.mp hd ha_mem
      refine ⟨?_, ?_, ?_⟩
      · ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        rw [← hu, Finset.mem_union]
        by_cases hxa : x = a
        · subst hxa; simp [ha_mem]
        · simp [hxa]
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        rcases Finset.mem_insert.mp hx1 with rfl | hxB
        · exact (Finset.mem_erase.mp hx2).1 rfl
        · exact Finset.disjoint_left.mp hd hxB (Finset.mem_erase.mp hx2).2
      · rw [Finset.card_insert_of_notMem ha_notB, hc]
  have hstep_prop : ∀ k < M,
      ∃ a ∈ (seq k).2,
        (seq (k + 1)).1 = insert a (seq k).1 ∧
        (seq (k + 1)).2 = (seq k).2.erase a ∧
        (isGrowth (seq k).1 (seq k).2 →
          let g := Nat.gcd ((seq k).2.gcd id) t
          ((subsetSumsMod t ((seq k).1.filter (fun x => g ∣ x))).card < (seq k).2.card / 2 →
            (3 / 2 : ℝ) * ((subsetSumsMod t ((seq k).1.filter (fun x => g ∣ x))).card : ℝ) ≤
              ((subsetSumsMod t ((seq (k + 1)).1.filter (fun x => g ∣ x))).card : ℝ)) ∧
          ((seq k).2.card / 2 ≤ (subsetSumsMod t ((seq k).1.filter (fun x => g ∣ x))).card →
            ((subsetSumsMod t ((seq k).1.filter (fun x => g ∣ x))).card : ℝ) + (Q.card : ℝ) / (400 * (ℓ : ℝ)) ≤
              ((subsetSumsMod t ((seq (k + 1)).1.filter (fun x => g ∣ x))).card : ℝ))) ∧
        (isUnsat (seq k).1 (seq k).2 →
          (subsetSumsMod t (seq k).1).card + d_step < (subsetSumsMod t (seq (k + 1)).1).card) := by
    intro k hkM
    obtain ⟨hu, hd, hc⟩ := hinv k hkM.le
    have hcond : (seq k).1 ∪ (seq k).2 = A₁ ∧ Disjoint (seq k).1 (seq k).2 ∧ (seq k).1.card < M :=
      ⟨hu, hd, by omega⟩
    have hspec := (hstep_ex (seq k).1 (seq k).2 hcond.1 hcond.2.1 hcond.2.2).choose_spec
    set a := (hstep_ex (seq k).1 (seq k).2 hcond.1 hcond.2.1 hcond.2.2).choose
    have hnext : seq (k + 1) = (insert a (seq k).1, (seq k).2.erase a) := by
      change nextStep (seq k) = _
      dsimp only [nextStep]
      rw [dif_pos hcond]
    refine ⟨a, hspec.1, by rw [hnext], by rw [hnext], ?_, ?_⟩
    · rw [hnext]; exact hspec.2.1
    · rw [hnext]; exact hspec.2.2
  -- Case 1: Some step k < M is saturated (neither growth nor unsaturated)!
  by_cases hsat : ∃ k < M, ¬ isGrowth (seq k).1 (seq k).2 ∧ ¬ isUnsat (seq k).1 (seq k).2
  · obtain ⟨k, hkM, hnotG, hnotU⟩ := hsat
    obtain ⟨hu, hd, hc⟩ := hinv k hkM.le
    set g := Nat.gcd ((seq k).2.gcd id) t
    have hgt : g ∣ t := Nat.gcd_dvd_right _ _
    have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hgt (NeZero.pos t)
    have : NeZero g := ⟨hg_pos.ne'⟩
    have hA_sub : (seq k).2 ⊆ A₁ := hu ▸ Finset.subset_union_right
    have hA_card_ge : M ≤ (seq k).2.card := by
      have := Finset.card_union_of_disjoint hd; rw [hu] at this; omega
    have hg_le_y16 : (g : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) := by
      have hA_ne : (seq k).2.Nonempty := Finset.card_pos.mp (by omega)
      have hAg_pos : 0 < (seq k).2.gcd id := by
        obtain ⟨a0, ha0⟩ := hA_ne
        have hlt := hQ_rng a0 (hA₁Q (hA_sub ha0))
        have hy_pos : 0 < y := by have := NeZero.pos t; nlinarith
        have ha0_pos : 0 < a0 := by nlinarith
        exact Nat.pos_of_dvd_of_pos (Finset.gcd_dvd ha0) ha0_pos
      exact (Nat.cast_le.mpr (Nat.le_of_dvd hAg_pos (Nat.gcd_dvd_left _ _))).trans
        (hGCD (seq k).2 hA_sub hA_card_ge)
    -- Every coset u : ZMod g has |S_u| ≥ (ξ / 2) * (t / g)!
    have hfib_ge : ∀ u : ZMod g,
        (ξ / 2) * ((t / g : ℕ) : ℝ) ≤
          (((subsetSumsMod t (seq k).1).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).card : ℝ) := by
      intro u
      by_contra hlt; push Not at hlt
      exact hnotU ⟨hnotG, u, hlt⟩
    have hsum_eq : (subsetSumsMod t (seq k).1).card =
        ∑ u : ZMod g, ((subsetSumsMod t (seq k).1).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    have hBk_ge : (ξ / 2) * (t : ℝ) ≤ ((subsetSumsMod t (seq k).1).card : ℝ) := by
      rw [hsum_eq, Nat.cast_sum]
      calc (ξ / 2) * (t : ℝ)
          = (g : ℝ) * ((ξ / 2) * ((t / g : ℕ) : ℝ)) := by
              have htm : (g : ℝ) * ((t / g : ℕ) : ℝ) = (t : ℝ) := by
                exact_mod_cast Nat.mul_div_cancel' hgt
              rw [← htm]; ring
        _ = ∑ _u : ZMod g, ((ξ / 2) * ((t / g : ℕ) : ℝ)) := by
              rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun u _ => hfib_ge u
    have hsub_A₁ : (seq k).1 ⊆ A₁ := hu ▸ Finset.subset_union_left
    have hle_A₁ : ((subsetSumsMod t (seq k).1).card : ℝ) ≤ ((subsetSumsMod t A₁).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (subsetSumsMod4_mono t hsub_A₁)
    calc (80 / (ℓ : ℝ)) * (t : ℝ) ≤ (ξ / 2) * (t : ℝ) := mul_le_mul_of_nonneg_right hℓ_ξ (Nat.cast_nonneg t)
      _ ≤ ((subsetSumsMod t (seq k).1).card : ℝ) := hBk_ge
      _ ≤ ((subsetSumsMod t A₁).card : ℝ) := hle_A₁
  · -- Case 2: No step k < M is saturated! Every step k < M is either growth or unsaturated!
    push Not at hsat
    let g_seq (k : ℕ) : ℕ := Nat.gcd ((seq k).2.gcd id) t
    have hg_dvd_next : ∀ k < M, g_seq k ∣ g_seq (k + 1) := by
      intro k hkM
      obtain ⟨a, _, _, hA_eq, _, _⟩ := hstep_prop k hkM
      have hsub : (seq (k + 1)).2 ⊆ (seq k).2 := by rw [hA_eq]; exact Finset.erase_subset a _
      have hdvd_gcd : (seq k).2.gcd id ∣ (seq (k + 1)).2.gcd id :=
        Finset.dvd_gcd fun x hx => Finset.gcd_dvd (hsub hx)
      exact Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans hdvd_gcd) (Nat.gcd_dvd_right _ _)
    have hg_pos_all : ∀ k ≤ M, 1 ≤ g_seq k := fun k _ =>
      Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right _ _) (NeZero.pos t)
    have hgM_le : g_seq M ≤ Nat.floor ((y : ℝ) ^ (1 / 16 : ℝ)) := by
      obtain ⟨hu, hd, hc⟩ := hinv M le_rfl
      have hA_sub : (seq M).2 ⊆ A₁ := hu ▸ Finset.subset_union_right
      have hA_card : M ≤ (seq M).2.card := by
        have := Finset.card_union_of_disjoint hd; rw [hu] at this; omega
      have hA_ne : (seq M).2.Nonempty := Finset.card_pos.mp (by omega)
      have hAg_pos : 0 < (seq M).2.gcd id := by
        obtain ⟨a0, ha0⟩ := hA_ne
        have hlt := hQ_rng a0 (hA₁Q (hA_sub ha0))
        have hy_pos : 0 < y := by have := NeZero.pos t; nlinarith
        have ha0_pos : 0 < a0 := by nlinarith
        exact Nat.pos_of_dvd_of_pos (Finset.gcd_dvd ha0) ha0_pos
      have hle_r : (g_seq M : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) :=
        (Nat.cast_le.mpr (Nat.le_of_dvd hAg_pos (Nat.gcd_dvd_left _ _))).trans
          (hGCD (seq M).2 hA_sub hA_card)
      exact Nat.le_floor hle_r
    have hGvals_le : ((Finset.range M).image g_seq).card ≤
        Nat.log 2 (Nat.floor ((y : ℝ) ^ (1 / 16 : ℝ))) + 1 :=
      card_image_div_chain_le g_seq hg_pos_all hg_dvd_next hgM_le
    -- Count growth steps grouped by g ∈ (range M).image g_seq!
    set Growth := (Finset.range M).filter (fun k => isGrowth (seq k).1 (seq k).2)
    have hGrowth_le : (Growth.card : ℝ) ≤ (Q.card : ℝ) / (100 * (ℓ : ℝ)) := by
      have hfib_sum : Growth.card = ∑ g ∈ (Finset.range M).image g_seq,
          (Growth.filter (fun k => g_seq k = g)).card :=
        Finset.card_eq_sum_card_fiberwise fun k hk =>
          Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
      have hper_g : ∀ g ∈ (Finset.range M).image g_seq,
          ((Growth.filter (fun k => g_seq k = g)).card : ℝ) ≤
            Real.log (2 * (y : ℝ)) / Real.log (3 / 2 : ℝ) +
              (y : ℝ) ^ (3 / 4 : ℝ) / ((Q.card : ℝ) / (400 * (ℓ : ℝ))) + 1 := by
        intro g hg_img
        let f (k : ℕ) : ℕ := (subsetSumsMod t ((seq k).1.filter (fun x => g ∣ x))).card
        have hf0 : 1 ≤ f 0 := Finset.card_pos.mpr ⟨0, zero_mem_subsetSumsMod4 t _⟩
        have hf_mono : ∀ k < M, f k ≤ f (k + 1) := by
          intro k hkM
          obtain ⟨a, _, hB_eq, _, _, _⟩ := hstep_prop k hkM
          refine Finset.card_le_card (subsetSumsMod4_mono t ?_)
          rw [hB_eq]
          exact Finset.filter_subset_filter _ (Finset.subset_insert a _)
        have hfM_le : (f M : ℝ) ≤ 2 * (y : ℝ) := by
          have h1 : f M ≤ t := by
            simpa [ZMod.card] using Finset.card_le_univ (subsetSumsMod t ((seq M).1.filter (fun x => g ∣ x)))
          have h2 : t ≤ 2 * y := by nlinarith
          exact_mod_cast h1.trans h2
        set Kg := Growth.filter (fun k => g_seq k = g)
        set KA := Kg.filter (fun k => f k < (seq k).2.card / 2)
        set KB := Kg.filter (fun k => ¬ f k < (seq k).2.card / 2)
        have hsplit : KA.card + KB.card = Kg.card := Finset.card_filter_add_card_filter_not _
        have hKA_le : (KA.card : ℝ) ≤ Real.log (2 * (y : ℝ)) / Real.log (3 / 2 : ℝ) := by
          refine monotone_exp_steps_le f hf0 hf_mono hfM_le KA
            ((Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)))
            fun k hk => ?_
          have hkKg := (Finset.mem_filter.mp hk).1
          have hklt := (Finset.mem_filter.mp hk).2
          have hkG := (Finset.mem_filter.mp hkKg).1
          have hkg := (Finset.mem_filter.mp hkKg).2
          have hkM : k < M := Finset.mem_range.mp (Finset.mem_filter.mp hkG).1
          have hisG : isGrowth (seq k).1 (seq k).2 := (Finset.mem_filter.mp hkG).2
          obtain ⟨_, _, _, _, hGstep, _⟩ := hstep_prop k hkM
          have h1 := (hGstep hisG).1
          dsimp [g_seq] at hkg
          rw [hkg] at h1
          exact h1 hklt
        have hKB_le : (KB.card : ℝ) ≤ (y : ℝ) ^ (3 / 4 : ℝ) / ((Q.card : ℝ) / (400 * (ℓ : ℝ))) + 1 := by
          have hδ : (0 : ℝ) < (Q.card : ℝ) / (400 * (ℓ : ℝ)) := by
            have : (0 : ℝ) < Q.card := by exact_mod_cast hQ_pos
            positivity
          refine monotone_lin_steps_le hδ (by positivity) f hf_mono KB
            ((Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)))
            fun k hk => ?_
          have hkKg := (Finset.mem_filter.mp hk).1
          have hkge : (seq k).2.card / 2 ≤ f k := not_lt.mp (Finset.mem_filter.mp hk).2
          have hkG := (Finset.mem_filter.mp hkKg).1
          have hkg := (Finset.mem_filter.mp hkKg).2
          have hkM : k < M := Finset.mem_range.mp (Finset.mem_filter.mp hkG).1
          have hisG : isGrowth (seq k).1 (seq k).2 := (Finset.mem_filter.mp hkG).2
          obtain ⟨u, hu_ne, hu_le⟩ := hisG
          have hgt : g ∣ t := hkg ▸ Nat.gcd_dvd_right _ _
          have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hgt (NeZero.pos t)
          have : NeZero g := ⟨hg_pos.ne'⟩
          have hfk_le : (f k : ℝ) ≤ (y : ℝ) ^ (3 / 4 : ℝ) := by
            have : NeZero (g_seq k) := ⟨(Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right _ _) (NeZero.pos t)).ne'⟩
            have hfib := h_fiber t (g_seq k) (Nat.gcd_dvd_right _ _) (seq k).1 u hu_ne
            have hfib' : f k ≤ ((subsetSumsMod t (seq k).1).filter
                (fun s => ZMod.castHom (Nat.gcd_dvd_right _ _) (ZMod (g_seq k)) s = u)).card := by
              dsimp [f]; rwa [← hkg]
            exact (Nat.cast_le.mpr hfib').trans hu_le
          obtain ⟨_, _, _, _, hGstep, _⟩ := hstep_prop k hkM
          have h2 := (hGstep ⟨u, hu_ne, hu_le⟩).2
          dsimp [g_seq] at hkg
          rw [hkg] at h2
          exact ⟨hfk_le, h2 hkge⟩
        have hsplit_r : (Kg.card : ℝ) = (KA.card : ℝ) + (KB.card : ℝ) := by
          exact_mod_cast hsplit.symm
        linarith
      rw [hfib_sum, Nat.cast_sum]
      calc ∑ g ∈ (Finset.range M).image g_seq, ((Growth.filter (fun k => g_seq k = g)).card : ℝ)
          ≤ ∑ _g ∈ (Finset.range M).image g_seq,
              (Real.log (2 * (y : ℝ)) / Real.log (3 / 2 : ℝ) +
                (y : ℝ) ^ (3 / 4 : ℝ) / ((Q.card : ℝ) / (400 * (ℓ : ℝ))) + 1) :=
            Finset.sum_le_sum hper_g
        _ = (((Finset.range M).image g_seq).card : ℝ) *
              (Real.log (2 * (y : ℝ)) / Real.log (3 / 2 : ℝ) +
                (y : ℝ) ^ (3 / 4 : ℝ) / ((Q.card : ℝ) / (400 * (ℓ : ℝ))) + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((Nat.log 2 (Nat.floor ((y : ℝ) ^ (1 / 16 : ℝ))) + 1 : ℕ) : ℝ) *
              (Real.log (2 * (y : ℝ)) / Real.log (3 / 2 : ℝ) +
                (y : ℝ) ^ (3 / 4 : ℝ) / ((Q.card : ℝ) / (400 * (ℓ : ℝ))) + 1) := by
            have hnn : 0 ≤ Real.log (2 * (y : ℝ)) / Real.log (3 / 2 : ℝ) +
                (y : ℝ) ^ (3 / 4 : ℝ) / ((Q.card : ℝ) / (400 * (ℓ : ℝ))) + 1 := by
              have h1 : (1 : ℝ) ≤ 2 * (y : ℝ) := by
                have hy1 : 1 ≤ y := by have := NeZero.pos t; nlinarith
                have : (1 : ℝ) ≤ y := by exact_mod_cast hy1
                linarith
              have hlog1 : 0 ≤ Real.log (2 * (y : ℝ)) := Real.log_nonneg h1
              have hlog2 : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
              positivity
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hGvals_le) hnn
        _ ≤ (Q.card : ℝ) / (100 * (ℓ : ℝ)) := hgrowth_budget
    -- Count unsaturated steps: Unsat = (range M).filter (¬ isGrowth) has card ≥ M - Growth.card ≥ |Q|/(100 ℓ)!
    set Unsat := (Finset.range M).filter (fun k => ¬ isGrowth (seq k).1 (seq k).2)
    have hUnsat_ge : (Q.card : ℝ) / (100 * (ℓ : ℝ)) ≤ (Unsat.card : ℝ) := by
      have htot := Finset.card_filter_add_card_filter_not (s := Finset.range M)
        (p := fun k => isGrowth (seq k).1 (seq k).2)
      rw [Finset.card_range] at htot
      have htot_r : (Growth.card : ℝ) + (Unsat.card : ℝ) = (M : ℝ) := by exact_mod_cast htot
      have hrew : (Q.card : ℝ) / (50 * (ℓ : ℝ)) =
          (Q.card : ℝ) / (100 * (ℓ : ℝ)) + (Q.card : ℝ) / (100 * (ℓ : ℝ)) := by ring
      linarith
    -- Telescope |subsetSumsMod t (seq M).1| ≥ Unsat.card * d_step!
    have htele : ∀ m ≤ M,
        ((Unsat.filter (fun k => k < m)).card : ℕ) * d_step ≤ (subsetSumsMod t (seq m).1).card := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hmM
        have hih := ih (by omega)
        have hsplit : Unsat.filter (fun k => k < m + 1) =
            if m ∈ Unsat then insert m (Unsat.filter (fun k => k < m)) else Unsat.filter (fun k => k < m) := by
          ext k; split_ifs with hmU <;> simp only [Finset.mem_filter, Finset.mem_insert]
          · constructor
            · rintro ⟨hkU, hlt⟩
              rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with rfl | hlt'
              · exact Or.inl rfl
              · exact Or.inr ⟨hkU, hlt'⟩
            · rintro (rfl | ⟨hkU, hlt⟩)
              · exact ⟨hmU, Nat.lt_succ_self k⟩
              · exact ⟨hkU, Nat.lt_succ_of_lt hlt⟩
          · constructor
            · rintro ⟨hkU, hlt⟩
              refine ⟨hkU, ?_⟩
              rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt) with rfl | hlt'
              · exact absurd hkU hmU
              · exact hlt'
            · rintro ⟨hkU, hlt⟩; exact ⟨hkU, Nat.lt_succ_of_lt hlt⟩
        rw [hsplit]
        obtain ⟨a, _, hB_eq, _, _, hUstep⟩ := hstep_prop m (by omega)
        by_cases hmU : m ∈ Unsat
        · rw [if_pos hmU, Finset.card_insert_of_notMem (by simp), add_mul, one_mul]
          have hnotG : ¬ isGrowth (seq m).1 (seq m).2 := (Finset.mem_filter.mp hmU).2
          have hisU : isUnsat (seq m).1 (seq m).2 := hsat m (by omega) hnotG
          have hgain := hUstep hisU
          omega
        · rw [if_neg hmU]
          have hmono : (subsetSumsMod t (seq m).1).card ≤ (subsetSumsMod t (seq (m + 1)).1).card := by
            rw [hB_eq]
            exact Finset.card_le_card (subsetSumsMod4_mono t (Finset.subset_insert a _))
          omega
    have h1 := htele M le_rfl
    have hfilt : Unsat.filter (fun k => k < M) = Unsat :=
      Finset.filter_true_of_mem fun k hk => Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    rw [hfilt] at h1
    have hsub_A₁ : (seq M).1 ⊆ A₁ := (hinv M le_rfl).1 ▸ Finset.subset_union_left
    have h2 : (Unsat.card : ℝ) * (d_step : ℝ) ≤ ((subsetSumsMod t A₁).card : ℝ) := by
      have hle : Unsat.card * d_step ≤ (subsetSumsMod t A₁).card :=
        h1.trans (Finset.card_le_card (subsetSumsMod4_mono t hsub_A₁))
      exact_mod_cast hle
    have ht_le_2y : (t : ℝ) ≤ 2 * (y : ℝ) := by
      have : t ≤ 2 * y := by nlinarith
      exact_mod_cast this
    have hQ_pos_r : (0 : ℝ) < Q.card := by exact_mod_cast hQ_pos
    have hprod_ge : (80 / (ℓ : ℝ)) * (t : ℝ) ≤ (Unsat.card : ℝ) * (d_step : ℝ) := by
      calc (80 / (ℓ : ℝ)) * (t : ℝ)
          ≤ (80 / (ℓ : ℝ)) * (2 * (y : ℝ)) := by gcongr
        _ = (160 / (ℓ : ℝ)) * (y : ℝ) := by ring
        _ ≤ (16384 / 100) / (ℓ : ℝ) * (y : ℝ) := by gcongr; norm_num
        _ = ((Q.card : ℝ) / (100 * (ℓ : ℝ))) * (2 ^ 14 * (y : ℝ) / (Q.card : ℝ)) := by
            field_simp; ring
        _ ≤ (Unsat.card : ℝ) * (d_step : ℝ) :=
            mul_le_mul hUnsat_ge hd_step_gt.le (by positivity) (Nat.cast_nonneg _)
    exact hprod_ge.trans h2

set_option maxHeartbeats 1600000 in
/- Helper 1: Basic lower bounds on `z`, plus `(S1)`, `(S2)`, `(S3)`, `(S6)`, `(S7)` from abstract reals. -/
set_option maxHeartbeats 800000 in
private lemma H4_asymp_core {ℓ : ℕ} (hℓ8 : 8 ≤ ℓ)
    {N Y R P tau z : ℝ} {d_step : ℕ}
    (hN10000 : (10000 : ℝ) ≤ N) (hlln1 : (1 : ℝ) ≤ Real.log (Real.log N))
    (hnlogℓ : 128000 * (ℓ : ℝ) < Real.log N)
    (hnℓ : 25600 * (ℓ : ℝ) ≤ N ^ (1 / 100 : ℝ))
    (hnlog : Real.log N ≤ N ^ (1 / 1000 : ℝ))
    (hP1 : 1 ≤ P) (hY_lo : N ^ (3 / 5 : ℝ) ≤ Y) (hY_hi : 2 * Y < N)
    (hR_lo : N ^ (1 / 4 : ℝ) ≤ R) (hR_le_N : R ≤ N)
    (hR_le_cpsi : R ≤ (1 / (10 ^ 15 * (ℓ : ℝ))) *
      (N ^ (1 / 3 : ℝ) * P / (Real.log N ^ (1 / 3 : ℝ) * Real.log (Real.log N) ^ (2 / 3 : ℝ))))
    (htau_ge : 1 / (4 * Real.log R) ≤ tau)
    (hL : N ≤ Y ^ 2 * P * tau / (15 * R))
    (hQ_lo : (1 / 10 : ℝ) * P * tau * Y / R ≤ z) (hz_le_2Y : z ≤ 2 * Y)
    (hd_step : d_step = Nat.floor (2 ^ 14 * Y / z) + 1) :
    Y ^ (1 / 3 : ℝ) ≤ z ∧
    N ^ (3 / 10 : ℝ) ≤ z ∧
    (8 * (d_step : ℝ)) ≤ Y ^ (3 / 4 : ℝ) ∧
    20 * (2 * (d_step : ℝ)) ^ (1.02 : ℝ) / (Y ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ) < z / (50 * (ℓ : ℝ)) ∧
    R ^ (1 / 16 : ℝ) ≤ (z / (150 * (ℓ : ℝ))) ^ (1 / 3 : ℝ) ∧
    Y ^ (1 / 16 : ℝ) ≤ Y ^ (1 / 4 : ℝ) / (24 * (ℓ : ℝ)) ∧
    64 * P * tau * Y / (R * Real.log R) < z / (50 * (ℓ : ℝ)) ∧
    (1 / (40 * (1 / (10 ^ 15 * (ℓ : ℝ))))) / (N ^ (1 / 3 : ℝ) * Real.log N) * Y ≤ z ∧
    (3 / 2 : ℝ) * N / Y ≤ z := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
  have hN_pos : 0 < N := by linarith
  have hN_ge1 : (1 : ℝ) ≤ N := by linarith
  have hY_ge1 : 1 ≤ Y := (Real.one_le_rpow hN_ge1 (by norm_num)).trans hY_lo
  have hY_pos : 0 < Y := by linarith
  have hY_lt_N : Y < N := by linarith
  have hlogN_ge1 : (1 : ℝ) ≤ Real.log N := by
    have : (8 : ℝ) ≤ ℓ := by exact_mod_cast hℓ8
    linarith
  have hlogN_pos : 0 < Real.log N := by linarith
  have hR_ge2 : (2 : ℝ) ≤ R := by
    have h1 : (2 : ℝ) ≤ N ^ (1 / 4 : ℝ) := by
      have h16 : (2 : ℝ) ^ (4 : ℕ) ≤ N := by norm_num; linarith
      have : (2 : ℝ) = ((2 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [this]; exact Real.rpow_le_rpow (by positivity) h16 (by norm_num)
    exact h1.trans hR_lo
  have hR_pos : 0 < R := by linarith
  have hlogR_pos : 0 < Real.log R := Real.log_pos (by linarith)
  have hlogR_le_logN : Real.log R ≤ Real.log N := Real.log_le_log hR_pos hR_le_N
  have hlogR_ge_quarter : Real.log N / 4 ≤ Real.log R := by
    have h1 := Real.log_le_log (by positivity) hR_lo
    rw [Real.log_rpow hN_pos] at h1
    linarith
  have htau_ge_N : 1 / (4 * Real.log N) ≤ tau :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)).trans htau_ge
  set c : ℝ := 1 / (10 ^ 15 * (ℓ : ℝ))
  have hc_pos : 0 < c := by positivity
  set C1 : ℝ := 1 / (40 * c)
  have hC1_eq : C1 = 10 ^ 15 * (ℓ : ℝ) / 40 := by dsimp [C1, c]; field_simp
  have hC1_ge1 : 1 ≤ C1 := by rw [hC1_eq]; linarith
  have hC1_pos : 0 < C1 := by linarith
  have hdenom_ge1 : 1 ≤ Real.log N ^ (1 / 3 : ℝ) * Real.log (Real.log N) ^ (2 / 3 : ℝ) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hlogN_ge1 (by norm_num))
      (Real.one_le_rpow hlln1 (by norm_num))
  have hPR_ge : 1 / (c * N ^ (1 / 3 : ℝ)) ≤ P / R := by
    have hR_le : R ≤ c * N ^ (1 / 3 : ℝ) * P := by
      calc R ≤ c * (N ^ (1 / 3 : ℝ) * P / (Real.log N ^ (1 / 3 : ℝ) * Real.log (Real.log N) ^ (2 / 3 : ℝ))) := hR_le_cpsi
        _ ≤ c * (N ^ (1 / 3 : ℝ) * P / 1) := by gcongr
        _ = c * N ^ (1 / 3 : ℝ) * P := by ring
    rw [div_le_div_iff₀ (by positivity) hR_pos]
    linarith
  have hB1 : C1 / (N ^ (1 / 3 : ℝ) * Real.log N) * Y ≤ z := by
    have h1 : (1 / 10 : ℝ) * (P / R) * tau * Y ≤ z := by
      have : (1 / 10 : ℝ) * P * tau * Y / R = (1 / 10 : ℝ) * (P / R) * tau * Y := by ring
      linarith
    have h2 : C1 / (N ^ (1 / 3 : ℝ) * Real.log N) ≤ (1 / 10 : ℝ) * (P / R) * tau := by
      calc C1 / (N ^ (1 / 3 : ℝ) * Real.log N)
          = (1 / 10 : ℝ) * (1 / (c * N ^ (1 / 3 : ℝ))) * (1 / (4 * Real.log N)) := by
              dsimp [C1]; field_simp; ring
        _ ≤ (1 / 10 : ℝ) * (P / R) * tau := by gcongr
    exact (mul_le_mul_of_nonneg_right h2 hY_pos.le).trans h1
  have hB2 : (3 / 2 : ℝ) * N / Y ≤ z := by
    have h1 : 15 * N ≤ Y ^ 2 * P * tau / R := by
      have := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 15 by norm_num)
      have hrew : 15 * (Y ^ 2 * P * tau / (15 * R)) = Y ^ 2 * P * tau / R := by field_simp
      linarith
    have h2 : (3 / 2 : ℝ) * N / Y ≤ (1 / 10 : ℝ) * P * tau * Y / R := by
      rw [div_le_iff₀ hY_pos]
      have hrew : (1 / 10 : ℝ) * P * tau * Y / R * Y = (1 / 10 : ℝ) * (Y ^ 2 * P * tau / R) := by ring
      rw [hrew]; linarith
    exact h2.trans hQ_lo
  have hz_pos : 0 < z := lt_of_lt_of_le (by positivity) hB2
  -- (1) Y^(1/3) ≤ z
  have hz_ge_Y13 : Y ^ (1 / 3 : ℝ) ≤ z := by
    have hgm := weighted_geom_mean hz_pos hY_pos hN_pos (by positivity) (by norm_num)
      (show (0 : ℝ) ≤ 2 / 3 by norm_num) (show (0 : ℝ) ≤ 1 / 3 by norm_num) hB1 hB2
    rw [show (2 / 3 + 1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one,
      show (2 / 3 - 1 / 3 : ℝ) = 1 / 3 by norm_num] at hgm
    suffices hcoef : (1 : ℝ) ≤ (C1 / (N ^ (1 / 3 : ℝ) * Real.log N)) ^ (2 / 3 : ℝ) *
        (3 / 2 : ℝ) ^ (1 / 3 : ℝ) * N ^ (1 / 3 : ℝ) by
      calc Y ^ (1 / 3 : ℝ) = 1 * Y ^ (1 / 3 : ℝ) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ ≤ z := hgm
    rw [Real.div_rpow hC1_pos.le (by positivity), Real.mul_rpow (by positivity) hlogN_pos.le,
      ← Real.rpow_mul hN_pos.le]
    have hC1_pow : 1 ≤ C1 ^ (2 / 3 : ℝ) := Real.one_le_rpow hC1_ge1 (by norm_num)
    have h32 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
    have hlog_bd : Real.log N ^ (2 / 3 : ℝ) ≤ N ^ (1 / 1000 : ℝ) := by
      calc Real.log N ^ (2 / 3 : ℝ) ≤ Real.log N ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlogN_ge1 (by norm_num)
        _ = Real.log N := Real.rpow_one _
        _ ≤ N ^ (1 / 1000 : ℝ) := hnlog
    have hden_le : N ^ (1 / 3 * (2 / 3) : ℝ) * Real.log N ^ (2 / 3 : ℝ) ≤ N ^ (1 / 3 : ℝ) := by
      calc N ^ (1 / 3 * (2 / 3) : ℝ) * Real.log N ^ (2 / 3 : ℝ)
          ≤ N ^ (1 / 3 * (2 / 3) : ℝ) * N ^ (1 / 1000 : ℝ) := by gcongr
        _ = N ^ (1 / 3 * (2 / 3) + 1 / 1000 : ℝ) := (Real.rpow_add hN_pos _ _).symm
        _ ≤ N ^ (1 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ C1 ^ (2 / 3 : ℝ) * (3 / 2 : ℝ) ^ (1 / 3 : ℝ) *
            (N ^ (1 / 3 : ℝ) / (N ^ (1 / 3 * (2 / 3) : ℝ) * Real.log N ^ (2 / 3 : ℝ))) := by
          gcongr; rw [one_le_div (by positivity)]; exact hden_le
      _ = C1 ^ (2 / 3 : ℝ) / (N ^ (1 / 3 * (2 / 3) : ℝ) * Real.log N ^ (2 / 3 : ℝ)) *
            (3 / 2 : ℝ) ^ (1 / 3 : ℝ) * N ^ (1 / 3 : ℝ) := by ring
  -- (2) N^(3/10) ≤ z
  have hz_ge_N310 : N ^ (3 / 10 : ℝ) ≤ z := by
    have hgm := weighted_geom_mean hz_pos hY_pos hN_pos (by positivity) (by norm_num)
      (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num) hB1 hB2
    rw [show (1 + 1 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (1 - 1 : ℝ) = 0 by norm_num, Real.rpow_zero, mul_one,
      Real.rpow_one, Real.rpow_one, Real.rpow_one] at hgm
    have hsq : (N ^ (3 / 10 : ℝ)) ^ (2 : ℕ) ≤ z ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast (N ^ (3 / 10 : ℝ)) 2, ← Real.rpow_mul hN_pos.le]
      norm_num
      refine le_trans ?_ hgm
      have hpow_le : N ^ (3 / 5 : ℝ) * (N ^ (1 / 3 : ℝ) * Real.log N) ≤ N := by
        calc N ^ (3 / 5 : ℝ) * (N ^ (1 / 3 : ℝ) * Real.log N)
            ≤ N ^ (3 / 5 : ℝ) * (N ^ (1 / 3 : ℝ) * N ^ (1 / 1000 : ℝ)) := by gcongr
          _ = N ^ (3 / 5 + 1 / 3 + 1 / 1000 : ℝ) := by
              rw [← mul_assoc, ← Real.rpow_add hN_pos, ← Real.rpow_add hN_pos]
          _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
          _ = N := Real.rpow_one N
      calc N ^ (3 / 5 : ℝ) ≤ 1 / (N ^ (1 / 3 : ℝ) * Real.log N) * 1 * N := by
            rw [mul_one, one_div_mul_eq_div, le_div_iff₀ (by positivity)]; exact hpow_le
        _ ≤ C1 / (N ^ (1 / 3 : ℝ) * Real.log N) * (3 / 2 : ℝ) * N := by gcongr; norm_num
    exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) hz_pos.le hsq
  -- d_step ≤ 2^15 * Y / z
  have hd_step_le : (d_step : ℝ) ≤ 2 ^ 15 * Y / z := by
    have h1 : (1 : ℝ) ≤ 2 ^ 14 * Y / z := by rw [one_le_div hz_pos]; linarith
    have h2 : (Nat.floor (2 ^ 14 * Y / z) : ℝ) ≤ 2 ^ 14 * Y / z := Nat.floor_le (by positivity)
    have hdbl : 2 ^ 14 * Y / z + 2 ^ 14 * Y / z = 2 ^ 15 * Y / z := by ring
    rw [hd_step]; push_cast; linarith
  -- (3) 8 * d_step ≤ Y^(3/4)
  have hS1 : 8 * (d_step : ℝ) ≤ Y ^ (3 / 4 : ℝ) := by
    have h1 : 8 * (2 ^ 15 * Y / z) ≤ Y ^ (3 / 4 : ℝ) := by
      rw [show 8 * (2 ^ 15 * Y / z) = 2 ^ 18 * Y / z by ring, div_le_iff₀ hz_pos]
      have hY14 : Y ^ (1 / 4 : ℝ) ≤ N ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hY_pos.le hY_lt_N.le (by norm_num)
      have h218 : (2 ^ 18 : ℝ) ≤ N ^ (1 / 20 : ℝ) := by
        have ha : (2 ^ 18 : ℝ) ≤ (25600 * (ℓ : ℝ)) ^ (2 : ℕ) := by
          have : (8 : ℝ) ≤ ℓ := by exact_mod_cast hℓ8
          nlinarith
        have hb : (25600 * (ℓ : ℝ)) ^ (2 : ℕ) ≤ (N ^ (1 / 100 : ℝ)) ^ (2 : ℕ) := by gcongr
        have hc : (N ^ (1 / 100 : ℝ)) ^ (2 : ℕ) = N ^ (1 / 50 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
        exact (ha.trans hb).trans (hc ▸ Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num))
      have hmul : 2 ^ 18 * Y ^ (1 / 4 : ℝ) ≤ N ^ (3 / 10 : ℝ) := by
        calc 2 ^ 18 * Y ^ (1 / 4 : ℝ) ≤ N ^ (1 / 20 : ℝ) * N ^ (1 / 4 : ℝ) := by gcongr
          _ = N ^ (3 / 10 : ℝ) := by rw [← Real.rpow_add hN_pos]; norm_num
      have hsplit : Y = Y ^ (3 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hY_pos]; norm_num
      calc 2 ^ 18 * Y = Y ^ (3 / 4 : ℝ) * (2 ^ 18 * Y ^ (1 / 4 : ℝ)) := by
            conv_lhs => rw [hsplit]
            ring
        _ ≤ Y ^ (3 / 4 : ℝ) * z := mul_le_mul_of_nonneg_left (hmul.trans hz_ge_N310) (by positivity)
    linarith
  -- (4) 20 * (2 * d_step)^1.02 / (Y^(3/4))^0.02 < z / (50 * ℓ)
  have hS2 : 20 * (2 * (d_step : ℝ)) ^ (1.02 : ℝ) / (Y ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ) < z / (50 * (ℓ : ℝ)) := by
    have hgm := weighted_geom_mean hz_pos hY_pos hN_pos (by positivity) (by norm_num)
      (show (0 : ℝ) ≤ 1.5125 by norm_num) (show (0 : ℝ) ≤ 0.5075 by norm_num) hB1 hB2
    rw [show (1.5125 + 0.5075 : ℝ) = 2.02 by norm_num,
      show (1.5125 - 0.5075 : ℝ) = 1.005 by norm_num] at hgm
    have h216 : (2 * (2 ^ 15 : ℝ)) ^ (1.02 : ℝ) ≤ 2 ^ 17 := by
      rw [show (2 * (2 ^ 15 : ℝ)) = (2 : ℝ) ^ (16 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      have : (2 : ℝ) ^ (16 * 1.02 : ℝ) ≤ (2 : ℝ) ^ (17 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      simpa using this
    have hlhs_le : 20 * (2 * (d_step : ℝ)) ^ (1.02 : ℝ) / (Y ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ) ≤
        (20 * 2 ^ 17) * Y ^ (1.005 : ℝ) / z ^ (1.02 : ℝ) := by
      have hd2 : 2 * (d_step : ℝ) ≤ (2 * 2 ^ 15) * (Y / z) := by
        calc 2 * (d_step : ℝ) ≤ 2 * (2 ^ 15 * Y / z) := by linarith
          _ = (2 * 2 ^ 15) * (Y / z) := by ring
      have hpow : (2 * (d_step : ℝ)) ^ (1.02 : ℝ) ≤ 2 ^ 17 * (Y ^ (1.02 : ℝ) / z ^ (1.02 : ℝ)) := by
        calc (2 * (d_step : ℝ)) ^ (1.02 : ℝ)
            ≤ ((2 * 2 ^ 15) * (Y / z)) ^ (1.02 : ℝ) := Real.rpow_le_rpow (by positivity) hd2 (by norm_num)
          _ = (2 * 2 ^ 15 : ℝ) ^ (1.02 : ℝ) * (Y / z) ^ (1.02 : ℝ) := Real.mul_rpow (by positivity) (by positivity)
          _ ≤ 2 ^ 17 * (Y / z) ^ (1.02 : ℝ) := mul_le_mul_of_nonneg_right h216 (by positivity)
          _ = 2 ^ 17 * (Y ^ (1.02 : ℝ) / z ^ (1.02 : ℝ)) := by rw [Real.div_rpow hY_pos.le hz_pos.le]
      have hYpow : Y ^ (1.02 : ℝ) / (Y ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ) = Y ^ (1.005 : ℝ) := by
        rw [← Real.rpow_mul hY_pos.le, ← Real.rpow_sub hY_pos]; norm_num
      calc 20 * (2 * (d_step : ℝ)) ^ (1.02 : ℝ) / (Y ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ)
          ≤ 20 * (2 ^ 17 * (Y ^ (1.02 : ℝ) / z ^ (1.02 : ℝ))) / (Y ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ) := by gcongr
        _ = (20 * 2 ^ 17) * (Y ^ (1.02 : ℝ) / (Y ^ (3 / 4 : ℝ)) ^ (0.02 : ℝ)) / z ^ (1.02 : ℝ) := by ring
        _ = (20 * 2 ^ 17) * Y ^ (1.005 : ℝ) / z ^ (1.02 : ℝ) := by rw [hYpow]
    suffices hstrict : (50 * (ℓ : ℝ)) * (20 * 2 ^ 17) * Y ^ (1.005 : ℝ) < z ^ (2.02 : ℝ) by
      refine lt_of_le_of_lt hlhs_le ?_
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have hz2 : z * z ^ (1.02 : ℝ) = z ^ (2.02 : ℝ) := by
        calc z * z ^ (1.02 : ℝ) = z ^ (1 : ℝ) * z ^ (1.02 : ℝ) := by rw [Real.rpow_one]
          _ = z ^ (1 + 1.02 : ℝ) := (Real.rpow_add hz_pos _ _).symm
          _ = z ^ (2.02 : ℝ) := by norm_num
      linarith [show (20 * 2 ^ 17) * Y ^ (1.005 : ℝ) * (50 * (ℓ : ℝ)) =
        (50 * (ℓ : ℝ)) * (20 * 2 ^ 17) * Y ^ (1.005 : ℝ) by ring]
    refine lt_of_lt_of_le ?_ hgm
    have hcoeff : (50 * (ℓ : ℝ)) * (20 * 2 ^ 17) <
        (C1 / (N ^ (1 / 3 : ℝ) * Real.log N)) ^ (1.5125 : ℝ) * (3 / 2 : ℝ) ^ (0.5075 : ℝ) * N ^ (0.5075 : ℝ) := by
      rw [Real.div_rpow hC1_pos.le (by positivity), Real.mul_rpow (by positivity) hlogN_pos.le,
        ← Real.rpow_mul hN_pos.le]
      have hC1_lt : (50 * (ℓ : ℝ)) * (20 * 2 ^ 17) < C1 ^ (1.5125 : ℝ) := by
        have h1 : (50 * (ℓ : ℝ)) * (20 * 2 ^ 17) < C1 := by rw [hC1_eq]; nlinarith
        have h2 : C1 ≤ C1 ^ (1.5125 : ℝ) := by
          conv_lhs => rw [← Real.rpow_one C1]
          exact Real.rpow_le_rpow_of_exponent_le hC1_ge1 (by norm_num)
        linarith
      have h32 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ (0.5075 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
      have hlog_pow : Real.log N ^ (1.5125 : ℝ) ≤ N ^ (1.5125 / 1000 : ℝ) := by
        calc Real.log N ^ (1.5125 : ℝ) ≤ (N ^ (1 / 1000 : ℝ)) ^ (1.5125 : ℝ) :=
              Real.rpow_le_rpow hlogN_pos.le hnlog (by norm_num)
          _ = N ^ (1.5125 / 1000 : ℝ) := by rw [← Real.rpow_mul hN_pos.le]; norm_num
      have hden_le_N : N ^ (1 / 3 * 1.5125 : ℝ) * Real.log N ^ (1.5125 : ℝ) ≤ N ^ (0.5075 : ℝ) := by
        calc N ^ (1 / 3 * 1.5125 : ℝ) * Real.log N ^ (1.5125 : ℝ)
            ≤ N ^ (1 / 3 * 1.5125 : ℝ) * N ^ (1.5125 / 1000 : ℝ) := by gcongr
          _ = N ^ (1 / 3 * 1.5125 + 1.5125 / 1000 : ℝ) := (Real.rpow_add hN_pos _ _).symm
          _ ≤ N ^ (0.5075 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
      have hfrac_ge1 : 1 ≤ (3 / 2 : ℝ) ^ (0.5075 : ℝ) * (N ^ (0.5075 : ℝ) /
          (N ^ (1 / 3 * 1.5125 : ℝ) * Real.log N ^ (1.5125 : ℝ))) :=
        one_le_mul_of_one_le_of_one_le h32 ((one_le_div (by positivity)).mpr hden_le_N)
      have hrew : C1 ^ (1.5125 : ℝ) / (N ^ (1 / 3 * 1.5125 : ℝ) * Real.log N ^ (1.5125 : ℝ)) *
          (3 / 2 : ℝ) ^ (0.5075 : ℝ) * N ^ (0.5075 : ℝ) =
          C1 ^ (1.5125 : ℝ) * ((3 / 2 : ℝ) ^ (0.5075 : ℝ) * (N ^ (0.5075 : ℝ) /
            (N ^ (1 / 3 * 1.5125 : ℝ) * Real.log N ^ (1.5125 : ℝ)))) := by ring
      rw [hrew]
      calc (50 * (ℓ : ℝ)) * (20 * 2 ^ 17) < C1 ^ (1.5125 : ℝ) := hC1_lt
        _ = C1 ^ (1.5125 : ℝ) * 1 := (mul_one _).symm
        _ ≤ C1 ^ (1.5125 : ℝ) * _ := mul_le_mul_of_nonneg_left hfrac_ge1 (by positivity)
    exact mul_lt_mul_of_pos_right hcoeff (by positivity)
  -- (5) R^(1/16) ≤ (z / (150 * ℓ))^(1/3)
  have hS3 : R ^ (1 / 16 : ℝ) ≤ (z / (150 * (ℓ : ℝ))) ^ (1 / 3 : ℝ) := by
    have h1 : R ^ (1 / 16 : ℝ) ≤ N ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow hR_pos.le hR_le_N (by norm_num)
    have h2 : N ^ (3 / 16 : ℝ) ≤ z / (150 * (ℓ : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      have hℓ_bd : 150 * (ℓ : ℝ) ≤ N ^ (1 / 100 : ℝ) := by linarith
      calc N ^ (3 / 16 : ℝ) * (150 * (ℓ : ℝ))
          ≤ N ^ (3 / 16 : ℝ) * N ^ (1 / 100 : ℝ) := by gcongr
        _ = N ^ (3 / 16 + 1 / 100 : ℝ) := (Real.rpow_add hN_pos _ _).symm
        _ ≤ N ^ (3 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
        _ ≤ z := hz_ge_N310
    calc R ^ (1 / 16 : ℝ) ≤ N ^ (1 / 16 : ℝ) := h1
      _ = (N ^ (3 / 16 : ℝ)) ^ (1 / 3 : ℝ) := by rw [← Real.rpow_mul hN_pos.le]; norm_num
      _ ≤ (z / (150 * (ℓ : ℝ))) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  -- (6) Y^(1/16) ≤ Y^(1/4) / (24 * ℓ)
  have hy16_lt_div : Y ^ (1 / 16 : ℝ) ≤ Y ^ (1 / 4 : ℝ) / (24 * (ℓ : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : 24 * (ℓ : ℝ) ≤ Y ^ (3 / 16 : ℝ) := by
      have ha : 24 * (ℓ : ℝ) ≤ N ^ (1 / 100 : ℝ) := by linarith
      have hb : N ^ (1 / 100 : ℝ) ≤ (N ^ (3 / 5 : ℝ)) ^ (3 / 16 : ℝ) := by
        rw [← Real.rpow_mul hN_pos.le]
        exact Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
      exact (ha.trans hb).trans (Real.rpow_le_rpow (by positivity) hY_lo (by norm_num))
    calc Y ^ (1 / 16 : ℝ) * (24 * (ℓ : ℝ)) ≤ Y ^ (1 / 16 : ℝ) * Y ^ (3 / 16 : ℝ) := by gcongr
      _ = Y ^ (1 / 16 + 3 / 16 : ℝ) := (Real.rpow_add hY_pos _ _).symm
      _ = Y ^ (1 / 4 : ℝ) := by norm_num
  -- (7) 64 * P * tau * Y / (R * log R) < z / (50 * ℓ)
  have hGCD_thresh : 64 * P * tau * Y / (R * Real.log R) < z / (50 * (ℓ : ℝ)) := by
    have hlogR_gt : 32000 * (ℓ : ℝ) < Real.log R := by linarith
    have h1 : P * tau * Y / R ≤ 10 * z := by
      have hrew : (1 / 10 : ℝ) * P * tau * Y / R = (1 / 10 : ℝ) * (P * tau * Y / R) := by ring
      linarith
    have h2 : 64 * P * tau * Y / (R * Real.log R) ≤ 640 * z / Real.log R := by
      rw [show 64 * P * tau * Y / (R * Real.log R) = 64 * (P * tau * Y / R) / Real.log R by ring,
        show 640 * z / Real.log R = 64 * (10 * z) / Real.log R by ring]
      gcongr
    have h3 : 640 * z / Real.log R < z / (50 * (ℓ : ℝ)) := by
      rw [div_lt_div_iff₀ hlogR_pos (by positivity)]
      nlinarith
    exact h2.trans_lt h3
  exact ⟨hz_ge_Y13, hz_ge_N310, hS1, hS2, hS3, hy16_lt_div, hGCD_thresh, hB1, hB2⟩

/- Helper 2: Claim 2 AP contradiction (`hS4`) from abstract reals. -/
private lemma H4_asymp_S4 {ℓ : ℕ} (hℓ8 : 8 ≤ ℓ)
    {N Y R P tau z : ℝ} {d_step : ℕ}
    (hN10000 : (10000 : ℝ) ≤ N) (hlln1 : (1 : ℝ) ≤ Real.log (Real.log N))
    (hlogN1 : (1 : ℝ) ≤ Real.log N)
    (hP1 : 1 ≤ P) (hY_pos : 0 < Y)
    (hR_ge2 : (2 : ℝ) ≤ R) (hR_le_N : R ≤ N)
    (hR_le_cpsi : R ≤ (1 / (10 ^ 15 * (ℓ : ℝ))) *
      (N ^ (1 / 3 : ℝ) * P / (Real.log N ^ (1 / 3 : ℝ) * Real.log (Real.log N) ^ (2 / 3 : ℝ))))
    (htau_ge : 1 / (4 * Real.log R) ≤ tau)
    (hL : N ≤ Y ^ 2 * P * tau / (15 * R))
    (hQ_lo : (1 / 10 : ℝ) * P * tau * Y / R ≤ z) (hz_le_2Y : z ≤ 2 * Y)
    (hd_step : d_step = Nat.floor (2 ^ 14 * Y / z) + 1) :
    256 * (3 * (128 * (d_step : ℝ))) * (Real.log (Real.log N) / Real.log R) < z / (50 * (ℓ : ℝ)) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
  have hN_pos : 0 < N := by linarith
  have hlogN_pos : 0 < Real.log N := by linarith
  have hlln_pos : 0 < Real.log (Real.log N) := by linarith
  have hR_pos : 0 < R := by linarith
  have hlogR_pos : 0 < Real.log R := Real.log_pos (by linarith)
  have hlogR_le_logN : Real.log R ≤ Real.log N := Real.log_le_log hR_pos hR_le_N
  have htau_pos : 0 < tau := lt_of_lt_of_le (by positivity) htau_ge
  have hz_pos : 0 < z := lt_of_lt_of_le (by positivity) hQ_lo
  set c : ℝ := 1 / (10 ^ 15 * (ℓ : ℝ))
  have hc_pos : 0 < c := by positivity
  have hc_le1 : c ≤ 1 := by dsimp [c]; rw [div_le_one (by positivity)]; linarith
  set psi : ℝ := N ^ (1 / 3 : ℝ) * P / (Real.log N ^ (1 / 3 : ℝ) * Real.log (Real.log N) ^ (2 / 3 : ℝ))
  have hd_step_le : (d_step : ℝ) ≤ 2 ^ 15 * Y / z := by
    have h1 : (1 : ℝ) ≤ 2 ^ 14 * Y / z := by rw [one_le_div hz_pos]; linarith
    have h2 : (Nat.floor (2 ^ 14 * Y / z) : ℝ) ≤ 2 ^ 14 * Y / z := Nat.floor_le (by positivity)
    have hdbl : 2 ^ 14 * Y / z + 2 ^ 14 * Y / z = 2 ^ 15 * Y / z := by ring
    rw [hd_step]; push_cast; linarith
  have h1 : Y / z ^ 2 ≤ 100 * Real.sqrt (R ^ 3 / (15 * N * P ^ 3 * tau ^ 3)) := by
    have hz2 : (1 / 100 : ℝ) * P ^ 2 * tau ^ 2 * Y ^ 2 / R ^ 2 ≤ z ^ 2 := by
      have h := mul_le_mul hQ_lo hQ_lo (by positivity) hz_pos.le
      have hrew : (1 / 10 : ℝ) * P * tau * Y / R * ((1 / 10 : ℝ) * P * tau * Y / R) =
          (1 / 100 : ℝ) * P ^ 2 * tau ^ 2 * Y ^ 2 / R ^ 2 := by ring
      linarith
    have hYz : Y / z ^ 2 ≤ 100 * R ^ 2 / (P ^ 2 * tau ^ 2 * Y) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hmul := mul_le_mul_of_nonneg_left hz2 (show (0 : ℝ) ≤ 100 * R ^ 2 by positivity)
      have hrew : 100 * R ^ 2 * ((1 / 100 : ℝ) * P ^ 2 * tau ^ 2 * Y ^ 2 / R ^ 2) =
          Y * (P ^ 2 * tau ^ 2 * Y) := by field_simp
      linarith
    have hinvY : 1 / Y ≤ Real.sqrt (P * tau / (15 * N * R)) := by
      rw [Real.le_sqrt (by positivity) (by positivity), div_pow, one_pow,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have hmul := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 15 * R by positivity)
      have hrew : 15 * R * (Y ^ 2 * P * tau / (15 * R)) = P * tau * Y ^ 2 := by field_simp
      linarith
    calc Y / z ^ 2
        ≤ 100 * R ^ 2 / (P ^ 2 * tau ^ 2 * Y) := hYz
      _ = (100 * R ^ 2 / (P ^ 2 * tau ^ 2)) * (1 / Y) := by ring
      _ ≤ (100 * R ^ 2 / (P ^ 2 * tau ^ 2)) * Real.sqrt (P * tau / (15 * N * R)) := by gcongr
      _ = 100 * (Real.sqrt ((R ^ 2 / (P ^ 2 * tau ^ 2)) ^ 2) * Real.sqrt (P * tau / (15 * N * R))) := by
          rw [Real.sqrt_sq (by positivity)]; ring
      _ = 100 * Real.sqrt ((R ^ 2 / (P ^ 2 * tau ^ 2)) ^ 2 * (P * tau / (15 * N * R))) := by
          rw [← Real.sqrt_mul (by positivity)]
      _ = 100 * Real.sqrt (R ^ 3 / (15 * N * P ^ 3 * tau ^ 3)) := by
          congr 2; field_simp
  have h2 : (Y / z ^ 2) * (Real.log (Real.log N) / Real.log R) ≤ 300 * c := by
    have htau3 : (1 / (64 * Real.log R ^ 3)) ≤ tau ^ 3 := by
      calc (1 / (64 * Real.log R ^ 3)) = (1 / (4 * Real.log R)) ^ 3 := by ring
        _ ≤ tau ^ 3 := pow_le_pow_left₀ (by positivity) htau_ge 3
    have hR3 : R ^ 3 * Real.log R * Real.log (Real.log N) ^ 2 / (N * P ^ 3) ≤ c ^ 3 := by
      have hpsi3 : psi ^ 3 = N * P ^ 3 / (Real.log N * Real.log (Real.log N) ^ 2) := by
        dsimp [psi]
        rw [div_pow, mul_pow, mul_pow]
        have ha : (N ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = N := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
        have hb : (Real.log N ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = Real.log N := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hlogN_pos.le]; norm_num
        have hc : (Real.log (Real.log N) ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = Real.log (Real.log N) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hlln_pos.le]; norm_num
        rw [ha, hb, hc]
      have hR3_le : R ^ 3 ≤ c ^ 3 * psi ^ 3 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hR_pos.le hR_le_cpsi 3
      calc R ^ 3 * Real.log R * Real.log (Real.log N) ^ 2 / (N * P ^ 3)
          ≤ (c ^ 3 * psi ^ 3) * Real.log N * Real.log (Real.log N) ^ 2 / (N * P ^ 3) := by gcongr
        _ = c ^ 3 := by rw [hpsi3]; field_simp
    have hrad : R ^ 3 / (15 * N * P ^ 3 * tau ^ 3) * (Real.log (Real.log N) / Real.log R) ^ 2 ≤ 9 * c ^ 2 := by
      have h64 : R ^ 3 / (15 * N * P ^ 3 * tau ^ 3) * (Real.log (Real.log N) / Real.log R) ^ 2 ≤
          (64 / 15 : ℝ) * (R ^ 3 * Real.log R * Real.log (Real.log N) ^ 2 / (N * P ^ 3)) := by
        have hinv_tau : 1 / tau ^ 3 ≤ 64 * Real.log R ^ 3 := by
          rw [div_le_iff₀ (by positivity)]
          have := mul_le_mul_of_nonneg_left htau3 (show (0 : ℝ) ≤ 64 * Real.log R ^ 3 by positivity)
          rwa [mul_div_cancel₀ _ (by positivity)] at this
        calc R ^ 3 / (15 * N * P ^ 3 * tau ^ 3) * (Real.log (Real.log N) / Real.log R) ^ 2
            = (1 / tau ^ 3) * (R ^ 3 * Real.log (Real.log N) ^ 2 / (15 * N * P ^ 3 * Real.log R ^ 2)) := by
                field_simp
          _ ≤ (64 * Real.log R ^ 3) * (R ^ 3 * Real.log (Real.log N) ^ 2 / (15 * N * P ^ 3 * Real.log R ^ 2)) := by
                gcongr
          _ = (64 / 15 : ℝ) * (R ^ 3 * Real.log R * Real.log (Real.log N) ^ 2 / (N * P ^ 3)) := by
                field_simp
      have hc3 : c ^ 3 ≤ c ^ 2 := by nlinarith [sq_nonneg c]
      calc _ ≤ (64 / 15 : ℝ) * c ^ 3 := h64.trans (mul_le_mul_of_nonneg_left hR3 (by norm_num))
        _ ≤ 9 * c ^ 2 := by nlinarith [sq_nonneg c]
    calc (Y / z ^ 2) * (Real.log (Real.log N) / Real.log R)
        ≤ 100 * Real.sqrt (R ^ 3 / (15 * N * P ^ 3 * tau ^ 3)) * (Real.log (Real.log N) / Real.log R) := by gcongr
      _ = 100 * (Real.sqrt (R ^ 3 / (15 * N * P ^ 3 * tau ^ 3)) *
            Real.sqrt ((Real.log (Real.log N) / Real.log R) ^ 2)) := by
          rw [Real.sqrt_sq (by positivity)]; ring
      _ = 100 * Real.sqrt (R ^ 3 / (15 * N * P ^ 3 * tau ^ 3) * (Real.log (Real.log N) / Real.log R) ^ 2) := by
          rw [← Real.sqrt_mul (by positivity)]
      _ ≤ 100 * Real.sqrt (9 * c ^ 2) := by gcongr
      _ = 300 * c := by
          rw [show 9 * c ^ 2 = (3 * c) ^ 2 by ring, Real.sqrt_sq (by positivity)]; ring
  have hcoeff_lt : (50 * (ℓ : ℝ)) * (256 * (3 * (128 * 2 ^ 15))) * (300 * c) < 1 := by
    dsimp [c]
    rw [show (50 * (ℓ : ℝ)) * (256 * (3 * (128 * 2 ^ 15))) * (300 * (1 / (10 ^ 15 * (ℓ : ℝ)))) =
      50 * 256 * 3 * 128 * 2 ^ 15 * 300 / 10 ^ 15 by field_simp]
    norm_num
  rw [lt_div_iff₀ (by positivity)]
  have hmul : 256 * (3 * (128 * (d_step : ℝ))) * (Real.log (Real.log N) / Real.log R) * (50 * (ℓ : ℝ)) ≤
      (50 * (ℓ : ℝ)) * (256 * (3 * (128 * 2 ^ 15))) * (Y / z ^ 2 * (Real.log (Real.log N) / Real.log R)) * z := by
    calc 256 * (3 * (128 * (d_step : ℝ))) * (Real.log (Real.log N) / Real.log R) * (50 * (ℓ : ℝ))
        ≤ 256 * (3 * (128 * (2 ^ 15 * Y / z))) * (Real.log (Real.log N) / Real.log R) * (50 * (ℓ : ℝ)) := by gcongr
      _ = (50 * (ℓ : ℝ)) * (256 * (3 * (128 * 2 ^ 15))) * (Y / z ^ 2 * (Real.log (Real.log N) / Real.log R)) * z := by
          field_simp
  calc _ ≤ (50 * (ℓ : ℝ)) * (256 * (3 * (128 * 2 ^ 15))) * (300 * c) * z := hmul.trans (by gcongr)
    _ < 1 * z := mul_lt_mul_of_pos_right hcoeff_lt hz_pos
    _ = z := one_mul z

/- Helper 3: Claim 1 growth budget (`hS5`) from abstract reals. -/
private lemma H4_asymp_S5 {ℓ : ℕ} (hℓ8 : 8 ≤ ℓ)
    {N Y z : ℝ}
    (hN10000 : (10000 : ℝ) ≤ N) (hlogN1 : (1 : ℝ) ≤ Real.log N)
    (hnℓ : 25600 * (ℓ : ℝ) ≤ N ^ (1 / 100 : ℝ))
    (hnlog : Real.log N ≤ N ^ (1 / 1000 : ℝ))
    (hY_ge1 : (1 : ℝ) ≤ Y) (hY_hi : 2 * Y < N)
    (hz_ge_N310 : N ^ (3 / 10 : ℝ) ≤ z)
    (hB1 : (1 / (40 * (1 / (10 ^ 15 * (ℓ : ℝ))))) / (N ^ (1 / 3 : ℝ) * Real.log N) * Y ≤ z)
    (hB2 : (3 / 2 : ℝ) * N / Y ≤ z) :
    ((Nat.log 2 (Nat.floor (Y ^ (1 / 16 : ℝ))) + 1 : ℕ) : ℝ) *
      (Real.log (2 * Y) / Real.log (3 / 2 : ℝ) + Y ^ (3 / 4 : ℝ) / (z / (400 * (ℓ : ℝ))) + 1) ≤
      z / (100 * (ℓ : ℝ)) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
  have hN_pos : 0 < N := by linarith
  have hN_ge1 : (1 : ℝ) ≤ N := by linarith
  have hY_pos : 0 < Y := by linarith
  have hY_lt_N : Y < N := by linarith
  have hlogN_pos : 0 < Real.log N := by linarith
  have hz_pos : 0 < z := lt_of_lt_of_le (by positivity) hB2
  set C1 : ℝ := 1 / (40 * (1 / (10 ^ 15 * (ℓ : ℝ))))
  have hC1_eq : C1 = 10 ^ 15 * (ℓ : ℝ) / 40 := by dsimp [C1]; field_simp
  have hC1_ge1 : 1 ≤ C1 := by rw [hC1_eq]; linarith
  have hC1_pos : 0 < C1 := by linarith
  have hlog2_le : ((Nat.log 2 (Nat.floor (Y ^ (1 / 16 : ℝ))) + 1 : ℕ) : ℝ) ≤ 2 * Real.log N := by
    have h1 : (2 : ℝ) ^ (Nat.log 2 (Nat.floor (Y ^ (1 / 16 : ℝ)))) ≤ Y ^ (1 / 16 : ℝ) := by
      by_cases hf0 : Nat.floor (Y ^ (1 / 16 : ℝ)) = 0
      · rw [hf0, Nat.log_zero_right, pow_zero]; exact Real.one_le_rpow hY_ge1 (by norm_num)
      · have hle : (2 : ℝ) ^ (Nat.log 2 (Nat.floor (Y ^ (1 / 16 : ℝ)))) ≤
            (Nat.floor (Y ^ (1 / 16 : ℝ)) : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hf0
        exact hle.trans (Nat.floor_le (by positivity))
    have h2 : (Nat.log 2 (Nat.floor (Y ^ (1 / 16 : ℝ))) : ℝ) * Real.log 2 ≤ Real.log (Y ^ (1 / 16 : ℝ)) := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h1
    rw [Real.log_rpow hY_pos] at h2
    have hlog2_pos : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogY_le : Real.log Y ≤ Real.log N := Real.log_le_log hY_pos hY_lt_N.le
    have hnat_le : (Nat.log 2 (Nat.floor (Y ^ (1 / 16 : ℝ))) : ℝ) ≤ Real.log N := by nlinarith
    push_cast; linarith
  have hlog32_ge : (1 / 3 : ℝ) ≤ Real.log (3 / 2 : ℝ) := by
    have h1 : Real.exp (1 / 3 : ℝ) ≤ 3 / 2 := by
      have h3 : (Real.exp (1 / 3 : ℝ)) ^ (3 : ℕ) ≤ (3 / 2 : ℝ) ^ (3 : ℕ) := by
        rw [← Real.exp_nat_mul]; norm_num; linarith [Real.exp_one_lt_d9]
      exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by norm_num) h3
    rw [← Real.log_exp (1 / 3 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) h1
  have hterm1 : Real.log (2 * Y) / Real.log (3 / 2 : ℝ) + 1 ≤ 4 * Real.log N := by
    have h2Y_le : Real.log (2 * Y) ≤ Real.log N := Real.log_le_log (by positivity) hY_hi.le
    have hdiv : Real.log (2 * Y) / Real.log (3 / 2 : ℝ) ≤ 3 * Real.log N := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hpiece1 : 800 * (ℓ : ℝ) * Real.log N ^ 2 ≤ z / 2 := by
    calc 800 * (ℓ : ℝ) * Real.log N ^ 2
        ≤ N ^ (1 / 100 : ℝ) * (N ^ (1 / 1000 : ℝ)) ^ 2 := by
            have h1 : 800 * (ℓ : ℝ) ≤ N ^ (1 / 100 : ℝ) := by linarith
            gcongr
      _ = N ^ (1 / 100 + 2 / 1000 : ℝ) := by
            rw [← Real.rpow_natCast (N ^ (1 / 1000 : ℝ)) 2, ← Real.rpow_mul hN_pos.le,
              ← Real.rpow_add hN_pos]; norm_num
      _ ≤ N ^ (3 / 10 : ℝ) / 2 := by
            rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
            have h2_le : (2 : ℝ) ≤ N ^ (1 / 10 : ℝ) := by
              have h10 : (2 : ℝ) ^ (10 : ℕ) ≤ N := by norm_num; linarith
              have : (2 : ℝ) = ((2 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
              rw [this]; exact Real.rpow_le_rpow (by positivity) h10 (by norm_num)
            calc N ^ (1 / 100 + 2 / 1000 : ℝ) * 2
                ≤ N ^ (1 / 100 + 2 / 1000 : ℝ) * N ^ (1 / 10 : ℝ) := by gcongr
              _ = N ^ (1 / 100 + 2 / 1000 + 1 / 10 : ℝ) := (Real.rpow_add hN_pos _ _).symm
              _ ≤ N ^ (3 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
      _ ≤ z / 2 := by linarith
  have hpiece2 : 160000 * (ℓ : ℝ) ^ 2 * Real.log N * Y ^ (3 / 4 : ℝ) ≤ z ^ 2 := by
    have hgm := weighted_geom_mean hz_pos hY_pos hN_pos (by positivity) (by norm_num)
      (show (0 : ℝ) ≤ 11 / 8 by norm_num) (show (0 : ℝ) ≤ 5 / 8 by norm_num) hB1 hB2
    rw [show (11 / 8 + 5 / 8 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (11 / 8 - 5 / 8 : ℝ) = 3 / 4 by norm_num] at hgm
    refine le_trans ?_ hgm
    suffices hcoef : 160000 * (ℓ : ℝ) ^ 2 * Real.log N ≤
        (C1 / (N ^ (1 / 3 : ℝ) * Real.log N)) ^ (11 / 8 : ℝ) * (3 / 2 : ℝ) ^ (5 / 8 : ℝ) * N ^ (5 / 8 : ℝ) by
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    rw [Real.div_rpow hC1_pos.le (by positivity), Real.mul_rpow (by positivity) hlogN_pos.le,
      ← Real.rpow_mul hN_pos.le]
    have hC1_pow : 1 ≤ C1 ^ (11 / 8 : ℝ) := Real.one_le_rpow hC1_ge1 (by norm_num)
    have h32 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ (5 / 8 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
    have hlog_pow : Real.log N ^ (11 / 8 : ℝ) ≤ N ^ (11 / 8000 : ℝ) := by
      calc Real.log N ^ (11 / 8 : ℝ) ≤ (N ^ (1 / 1000 : ℝ)) ^ (11 / 8 : ℝ) :=
            Real.rpow_le_rpow hlogN_pos.le hnlog (by norm_num)
        _ = N ^ (11 / 8000 : ℝ) := by rw [← Real.rpow_mul hN_pos.le]; norm_num
    have hlhs : 160000 * (ℓ : ℝ) ^ 2 * Real.log N ≤ N ^ (1 / 50 : ℝ) * N ^ (1 / 1000 : ℝ) := by
      have h1 : 160000 * (ℓ : ℝ) ^ 2 ≤ (25600 * (ℓ : ℝ)) ^ (2 : ℕ) := by nlinarith
      have h2 : (25600 * (ℓ : ℝ)) ^ (2 : ℕ) ≤ (N ^ (1 / 100 : ℝ)) ^ (2 : ℕ) := by gcongr
      have h3 : (N ^ (1 / 100 : ℝ)) ^ (2 : ℕ) = N ^ (1 / 50 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
      exact mul_le_mul ((h1.trans h2).trans h3.le) hnlog hlogN_pos.le (by positivity)
    have hpow_le : (N ^ (1 / 50 : ℝ) * N ^ (1 / 1000 : ℝ)) * (N ^ (1 / 3 * (11 / 8) : ℝ) * N ^ (11 / 8000 : ℝ)) ≤
        N ^ (5 / 8 : ℝ) := by
      rw [← Real.rpow_add hN_pos, ← Real.rpow_add hN_pos, ← Real.rpow_add hN_pos]
      exact Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
    calc 160000 * (ℓ : ℝ) ^ 2 * Real.log N
        ≤ N ^ (1 / 50 : ℝ) * N ^ (1 / 1000 : ℝ) := hlhs
      _ ≤ 1 / (N ^ (1 / 3 * (11 / 8) : ℝ) * N ^ (11 / 8000 : ℝ)) * 1 * N ^ (5 / 8 : ℝ) := by
          rw [mul_one, one_div_mul_eq_div, le_div_iff₀ (by positivity)]; exact hpow_le
      _ ≤ C1 ^ (11 / 8 : ℝ) / (N ^ (1 / 3 * (11 / 8) : ℝ) * Real.log N ^ (11 / 8 : ℝ)) *
            (3 / 2 : ℝ) ^ (5 / 8 : ℝ) * N ^ (5 / 8 : ℝ) := by gcongr
  have hcomb : (2 * Real.log N) * (4 * Real.log N + Y ^ (3 / 4 : ℝ) / (z / (400 * (ℓ : ℝ)))) ≤
      z / (100 * (ℓ : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have hrew : (2 * Real.log N) * (4 * Real.log N + Y ^ (3 / 4 : ℝ) / (z / (400 * (ℓ : ℝ)))) * (100 * (ℓ : ℝ)) =
        (800 * (ℓ : ℝ) * Real.log N ^ 2) + (80000 * (ℓ : ℝ) ^ 2 * Real.log N * Y ^ (3 / 4 : ℝ)) / z := by
      field_simp; ring
    rw [hrew]
    have h2 : 80000 * (ℓ : ℝ) ^ 2 * Real.log N * Y ^ (3 / 4 : ℝ) / z ≤ z / 2 := by
      rw [div_le_iff₀ hz_pos]; nlinarith
    linarith
  have hstep1 : Real.log (2 * Y) / Real.log (3 / 2 : ℝ) + Y ^ (3 / 4 : ℝ) / (z / (400 * (ℓ : ℝ))) + 1 ≤
      4 * Real.log N + Y ^ (3 / 4 : ℝ) / (z / (400 * (ℓ : ℝ))) := by linarith
  have hnn1 : 0 ≤ Real.log (2 * Y) / Real.log (3 / 2 : ℝ) + Y ^ (3 / 4 : ℝ) / (z / (400 * (ℓ : ℝ))) + 1 := by
    have : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
    have : 0 < Real.log (3 / 2 : ℝ) := by linarith
    positivity
  calc _ ≤ (2 * Real.log N) * (4 * Real.log N + Y ^ (3 / 4 : ℝ) / (z / (400 * (ℓ : ℝ)))) :=
        mul_le_mul hlog2_le hstep1 hnn1 (by positivity)
    _ ≤ z / (100 * (ℓ : ℝ)) := hcomb

set_option maxHeartbeats 1200000 in
lemma main_H4_from_parts
    (h_tau : ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, (n : ℝ) ^ (1 / 4 : ℝ) ≤ (r : ℝ) → r ≤ n →
      1 / (4 * Real.log (r : ℝ)) ≤
        ∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
          (1 - (1 : ℝ) / (p : ℝ)))
    (h_part : ∀ (ℓ : ℕ), 8 ≤ ℓ →
      ∃ Y0 : ℕ, ∀ (y : ℕ) (Q : Finset ℕ), Y0 ≤ y →
        (∀ x ∈ Q, 1 ≤ x ∧ x < 2 * y) →
        (y : ℝ) ^ (1 / 3 : ℝ) ≤ (Q.card : ℝ) →
        (∀ d : ℕ, 2 ≤ d → (y : ℝ) ^ (1 / 4 : ℝ) ≤ ((Q.filter (fun x => ¬ d ∣ x)).card : ℝ)) →
        ∃ (A₁ A₂ : Fin ℓ → Finset ℕ),
          (∀ i, A₁ i ⊆ Q ∧ A₂ i ⊆ Q) ∧
          (∀ i, Disjoint (A₁ i) (A₂ i)) ∧
          (∀ i j, i ≠ j → Disjoint (A₁ i ∪ A₂ i) (A₁ j ∪ A₂ j)) ∧
          (∀ i, (Q.card : ℝ) / (24 * (ℓ : ℝ)) ≤ ((A₁ i).card : ℝ) ∧
                ((A₁ i).card : ℝ) ≤ (Q.card : ℝ) / (16 * (ℓ : ℝ))) ∧
          (∀ i, (Q.card : ℝ) / (24 * (ℓ : ℝ)) ≤ ((A₂ i).card : ℝ) ∧
                ((A₂ i).card : ℝ) ≤ (Q.card : ℝ) / (16 * (ℓ : ℝ))) ∧
          (∀ i, ∀ d : ℕ, 2 ≤ d →
            (y : ℝ) ^ (1 / 4 : ℝ) / (24 * (ℓ : ℝ)) ≤ (((A₁ i).filter (fun x => ¬ d ∣ x)).card : ℝ)))
    (h_union : ∀ (A B : Finset ℕ) (h : ℝ), Disjoint A B →
      (∀ t ∈ B, 1 ≤ t ∧ h ≤ ((subsetSumsMod t A).card : ℝ)) →
      (B.card : ℝ) * h ≤ ((subsetSumsFin (A ∪ B)).card : ℝ))
    (h_stable : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d k : ℕ),
      nfoldSum k (Gset A d) ⊆ Gset A (k * d))
    (h_dcount : ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d : ℕ),
      d < A.card → ((Gset A d).card : ℝ) ≤ (A.card : ℝ) ^ 2 / ((A.card : ℝ) - (d : ℝ)))
    (h_full : ∀ (d : ℕ) [NeZero d] (A : Finset ℕ),
      (∀ d' : ℕ, d' ∣ d → 2 ≤ d' → d' - 1 ≤ (A.filter (fun a => ¬ d' ∣ a)).card) →
      subsetSumsMod d A = Finset.univ)
    (h_fiber : ∀ (t g : ℕ) [NeZero t] [NeZero g] (hgt : g ∣ t) (A : Finset ℕ) (u : ZMod g),
      ((subsetSumsMod t A).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).Nonempty →
      (subsetSumsMod t (A.filter (fun a => g ∣ a))).card ≤
        ((subsetSumsMod t A).filter (fun s => ZMod.castHom hgt (ZMod g) s = u)).card)
    (h_sub_ker : ∀ (m : ℕ) [NeZero m] (H : AddSubgroup (ZMod m)),
      ∃ (q : ℕ) (hq : q ∣ m), 1 ≤ q ∧ Nat.card H = m / q ∧
        ∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0)
    (h_proper_iff : ∀ (m q : ℕ) [NeZero m] (hq : q ∣ m) (hq1 : 1 ≤ q)
      (H : AddSubgroup (ZMod m)), (∀ x : ZMod m, x ∈ H ↔ ZMod.castHom hq (ZMod q) x = 0) →
      (H ≠ ⊤ ↔ 2 ≤ q))
    (h_struct_raw : ∀ (ξ : ℝ), 0 < ξ → ξ < 1 / 100 →
      (∀ (m : ℕ) [NeZero m] (X : Finset (ZMod m)),
        X.Nonempty → (X.card : ℝ) ≤ ξ * (m : ℝ) → ((X + X).card : ℝ) ≤ 2.04 * (X.card : ℝ) →
        ∃ H : AddSubgroup (ZMod m), H ≠ ⊤ ∧
          ((∃ (x d : ZMod m) (L : ℕ), 2 ≤ L ∧
              (∀ a ∈ X, ∃ k < L, a - (x + (k : ZMod m) * d) ∈ H) ∧
              ((L - 1 : ℕ) : ℝ) * (Nat.card H : ℝ) ≤ ((X + X).card : ℝ) - (X.card : ℝ)) ∨
           (∃ (c₁ c₂ c₃ : ZMod m),
              (∀ a ∈ X, a - c₁ ∈ H ∨ a - c₂ ∈ H ∨ a - c₃ ∈ H) ∧
              (Nat.card H : ℝ) ≤ ((X + X).card : ℝ) - (X.card : ℝ)) ∨
           (∃ x : ZMod m, ∀ a ∈ X, a - x ∈ H))) →
      (∀ (m : ℕ) [NeZero m] (X : Finset (ZMod m)) (k : ℕ), 1 ≤ k →
        (∀ H : AddSubgroup (ZMod m), H ≠ ⊤ → ¬ ∃ x : ZMod m, ∀ a ∈ X, a - x ∈ H) →
        min (m : ℝ) (((k + 1 : ℕ) : ℝ) * (X.card : ℝ) / 2) ≤ ((nfoldSum k X).card : ℝ)) →
      ∀ (m : ℕ) [NeZero m] (A : Finset (ZMod m)) (d : ℕ),
        1 ≤ d → 8 * d < A.card → (A.card : ℝ) < (ξ / 2) * (m : ℝ) →
        (∀ H : AddSubgroup (ZMod m), H ≠ ⊤ → ¬ ∀ x ∈ Gset A d, x ∈ H) →
        ((Gset A d).card : ℝ) ≤ 20 * (A.card : ℝ) / ((A.card : ℝ) / (2 * (d : ℝ))) ^ (1.02 : ℝ) ∨
        ∃ (q : ℕ) (hq : q ∣ m) (u : (ZMod q)ˣ) (a₀ L : ℕ),
          2 ≤ q ∧ 2 ≤ L ∧ L ≤ q ∧ L * (m / q) ≤ 128 * d ∧
          ∀ x ∈ Gset A d, ∃ k < L, u.1 * ZMod.castHom hq (ZMod q) x = ((a₀ + k : ℕ) : ZMod q))
    (h_ap_cover : ∀ (m x0 q a0 L : ℕ), 1 ≤ m → 2 ≤ q → q ∣ m → 1 ≤ L → L ≤ q → ∀ u : (ZMod q)ˣ,
      let H_sz := m / q
      let R := (Finset.Ico x0 (x0 + m)).filter
        (fun z : ℕ => ∃ k < L, u.1 * (z : ZMod q) = ((a0 + k : ℕ) : ZMod q))
      ∃ APs : List (ℕ × ℕ × ℕ),
        (∀ z ∈ R, ∃ p ∈ APs, ∃ k < p.2.2, z = p.1 + p.2.1 * k) ∧
        (∀ p ∈ APs, 1 ≤ p.2.1 ∧ p.2.1 ≤ m ∧ ((L * H_sz : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ (p.2.2 : ℝ)) ∧
        (APs.map (fun p => p.2.2)).sum ≤ 3 * (L * H_sz))
    (hH1 : H1) (hH2 : H2) :
    OMA.R_Erdos360_erdos_360_R1_H4_R1.H4 := by
  obtain ⟨ξ, hξ_pos, hξ_lt, hDF⟩ := hH1
  have hCOS : ∀ (m : ℕ) [NeZero m] (X : Finset (ZMod m)) (k : ℕ), 1 ≤ k →
      (∀ H : AddSubgroup (ZMod m), H ≠ ⊤ → ¬ ∃ x : ZMod m, ∀ a ∈ X, a - x ∈ H) →
      min (m : ℝ) (((k + 1 : ℕ) : ℝ) * (X.card : ℝ) / 2) ≤ ((nfoldSum k X).card : ℝ) := by
    intro m _ X k hk hnot
    rw [nfoldSum4_eq_piFinset]
    exact hH2 m X k hk hnot
  have h_struct := h_struct_raw ξ hξ_pos hξ_lt hDF hCOS
  set ℓ : ℕ := max 8 (Nat.ceil (160 / ξ) + 1)
  have hℓ8 : 8 ≤ ℓ := le_max_left _ _
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ_ξ : 80 / (ℓ : ℝ) ≤ ξ / 2 := by
    have h1 : 160 / ξ ≤ (ℓ : ℝ) := by
      have ha : 160 / ξ ≤ (Nat.ceil (160 / ξ) : ℝ) := Nat.le_ceil _
      have hb : Nat.ceil (160 / ξ) ≤ ℓ := (Nat.le_succ _).trans (le_max_right _ _)
      exact ha.trans (Nat.cast_le.mpr hb)
    have h2 : 160 ≤ (ℓ : ℝ) * ξ := (div_le_iff₀ hξ_pos).mp h1
    rw [div_le_div_iff₀ hℓpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  set c : ℝ := 1 / (10 ^ 15 * (ℓ : ℝ))
  have hc_pos : 0 < c := by positivity
  obtain ⟨Y0, hY0⟩ := h_part ℓ hℓ8
  refine ⟨c, hc_pos, ℓ, hℓ8, ?_⟩
  have ht_log_rpow : ∀ α : ℝ, 0 < α → ∀ K : ℝ, ∀ᶠ n : ℕ in atTop,
      K * Real.log (n : ℝ) ≤ (n : ℝ) ^ α := by
    intro α hα K
    have hlim := (isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (max K 1) by positivity)),
      Filter.eventually_ge_atTop 10] with n hn hn10
    have hpos : (0 : ℝ) < (n : ℝ) ^ α := by positivity
    dsimp only [Function.comp_apply] at hn
    have h1 := (div_lt_iff₀ hpos).mp hn
    have h2 : (max K 1) * Real.log (n : ℝ) < (n : ℝ) ^ α := by
      have hm : (0 : ℝ) < max K 1 := by positivity
      have := mul_lt_mul_of_pos_left h1 hm
      rwa [← mul_assoc, mul_div_cancel₀ _ hm.ne', one_mul] at this
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have : K * Real.log (n : ℝ) ≤ max K 1 * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left K 1) hlog_nn
    linarith
  have ht_pow : ∀ α : ℝ, 0 < α → ∀ B : ℝ, ∀ᶠ n : ℕ in atTop, B ≤ (n : ℝ) ^ α := by
    intro α hα B
    exact ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop B)
  have hE2 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 4 : ℝ) + 1 ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) / Real.log (n : ℝ) := by
    filter_upwards [ht_log_rpow (1 / 12 : ℝ) (by norm_num) (2 / c),
      Filter.eventually_ge_atTop 100] with n hn hn100
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have h1 : 2 * Real.log (n : ℝ) ≤ c * (n : ℝ) ^ (1 / 12 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hn hc_pos.le
      rwa [← mul_assoc, mul_div_cancel₀ _ hc_pos.ne'] at this
    have h2 : 2 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log (n : ℝ) ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) by positivity)
      have hpow : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_add hn_pos]; norm_num
      linarith [show (n : ℝ) ^ (1 / 4 : ℝ) * (c * (n : ℝ) ^ (1 / 12 : ℝ)) = c * (n : ℝ) ^ (1 / 3 : ℝ) by
        rw [← mul_assoc, mul_comm ((n : ℝ) ^ (1 / 4 : ℝ)) c, mul_assoc, hpow]]
    have h3 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    rw [le_div_iff₀ hlog_pos]
    nlinarith
  have hE_log : ∀ᶠ n : ℕ in atTop,
      10000 ≤ n ∧
      (1 : ℝ) ≤ Real.log (Real.log (n : ℝ)) ∧
      128000 * (ℓ : ℝ) < Real.log (n : ℝ) ∧
      (Y0 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) ∧
      (25600 * (ℓ : ℝ)) ≤ (n : ℝ) ^ (1 / 100 : ℝ) ∧
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 1000 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 10000,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_gt_atTop (128000 * (ℓ : ℝ))),
      ht_pow (3 / 5 : ℝ) (by norm_num) (Y0 : ℝ),
      ht_pow (1 / 100 : ℝ) (by norm_num) (25600 * (ℓ : ℝ)),
      ht_log_rpow (1 / 1000 : ℝ) (by norm_num) 1] with
      n hn10000 hnlogℓ hnY0 hnℓ hnlog
    refine ⟨hn10000, ?_, hnlogℓ, hnY0, hnℓ, by simpa using hnlog⟩
    have h1 : Real.exp (Real.exp 1) ≤ (n : ℝ) := by
      have he1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
      have he3 : Real.exp 3 ≤ 27 := by
        calc Real.exp 3 = Real.exp (1 + 1 + 1) := by norm_num
          _ = Real.exp 1 * Real.exp 1 * Real.exp 1 := by rw [Real.exp_add, Real.exp_add]
          _ ≤ 3 * 3 * 3 := by gcongr
          _ = 27 := by norm_num
      have h2 : Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.mpr he1
      have hn_r : (10000 : ℝ) ≤ n := by exact_mod_cast hn10000
      linarith
    have h2 : Real.exp 1 ≤ Real.log (n : ℝ) := by
      rw [← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) h1
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) h2
  filter_upwards [h_tau, hE2, hE_log] with n htau_n hE2_n hE_n
  obtain ⟨hn10000, hlln1, hnlogℓ, hnY0, hnℓ, hnlog⟩ := hE_n
  intro y r v Q
  dsimp only
  intro hr_def h2yn hr2y hy_lo _hU hL hv1 hv_hi hQ_rng hQ_lo _hQ_hi hQ_div hQ_gcd hQ_ap
  have hN10000 : (10000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10000
  have hN_ge1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hN_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogN1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have : (8 : ℝ) ≤ ℓ := by exact_mod_cast hℓ8
    linarith
  have hlogN_pos : 0 < Real.log (n : ℝ) := by linarith
  have hP1 : 1 ≤ (n : ℝ) / (n.totient : ℝ) := by
    have hphi_pos : 0 < n.totient := Nat.totient_pos.mpr (by omega)
    rw [one_le_div (by exact_mod_cast hphi_pos)]
    exact_mod_cast Nat.totient_le n
  have hY_ge1 : (1 : ℝ) ≤ (y : ℝ) := (Real.one_le_rpow hN_ge1 (by norm_num)).trans hy_lo
  have hY_pos : (0 : ℝ) < (y : ℝ) := by linarith
  have hY_hi : 2 * (y : ℝ) < (n : ℝ) := by exact_mod_cast h2yn
  have hy_ge_Y0 : Y0 ≤ y := by exact_mod_cast hnY0.trans hy_lo
  have hR_lo : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (r : ℝ) := by
    have hdenom_le : Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) ≤ Real.log (n : ℝ) := by
      have hll_le : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) :=
        (Real.log_le_sub_one_of_pos hlogN_pos).trans (by linarith)
      calc Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ)
          ≤ Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (n : ℝ) ^ (2 / 3 : ℝ) := by gcongr
        _ = Real.log (n : ℝ) ^ (1 / 3 + 2 / 3 : ℝ) := (Real.rpow_add hlogN_pos _ _).symm
        _ = Real.log (n : ℝ) := by norm_num
    have hpsi_ge : (n : ℝ) ^ (1 / 4 : ℝ) + 1 ≤ c * ((n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
        (Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ))) := by
      calc (n : ℝ) ^ (1 / 4 : ℝ) + 1 ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) / Real.log (n : ℝ) := hE2_n
        _ ≤ c * ((n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) / Real.log (n : ℝ)) := by
            rw [mul_div_assoc]; gcongr; exact le_mul_of_one_le_right (by positivity) hP1
        _ ≤ _ := by gcongr
    have hr_gt : c * ((n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
        (Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ))) - 1 < (r : ℝ) := by
      have := Nat.lt_floor_add_one (c * ((n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
        (Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ))))
      rw [← hr_def] at this; linarith
    linarith
  have hR_le_n : r ≤ n := by
    have : r ≤ r ^ 2 := by nlinarith
    omega
  have hR_le_N : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hR_le_n
  have hR_ge2 : (2 : ℝ) ≤ (r : ℝ) := by
    have h1 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
      have h16 : (2 : ℝ) ^ (4 : ℕ) ≤ (n : ℝ) := by norm_num; linarith
      have : (2 : ℝ) = ((2 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [this]; exact Real.rpow_le_rpow (by positivity) h16 (by norm_num)
    exact h1.trans hR_lo
  have hR_le_cpsi : (r : ℝ) ≤ c * ((n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
      (Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ))) := by
    rw [hr_def]; exact Nat.floor_le (by positivity)
  have htau_ge : 1 / (4 * Real.log (r : ℝ)) ≤
      ∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime), (1 - (1 : ℝ) / (p : ℝ)) :=
    htau_n r hR_lo hR_le_n
  have hQ_rng_1 : ∀ x ∈ Q, 1 ≤ x ∧ x < 2 * y := fun x hx => by
    have h := hQ_rng x hx
    have hy1 : 1 ≤ y := by exact_mod_cast hY_ge1
    exact ⟨by nlinarith, by nlinarith⟩
  have hz_le_2Y : (Q.card : ℝ) ≤ 2 * (y : ℝ) := by
    have hsub : Q ⊆ Finset.Ico 0 (2 * y) := fun x hx =>
      Finset.mem_Ico.mpr ⟨Nat.zero_le _, (hQ_rng_1 x hx).2⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Ico, Nat.sub_zero] at hcard
    exact_mod_cast hcard
  have hcore := H4_asymp_core hℓ8 hN10000 hlln1 hnlogℓ hnℓ hnlog hP1 hy_lo hY_hi hR_lo hR_le_N
    hR_le_cpsi htau_ge hL hQ_lo hz_le_2Y rfl
  obtain ⟨hz_ge_Y13, hz_ge_N310, hS1, hS2, hS3, hy16_lt_div, hGCD_thresh, hB1, hB2⟩ := hcore
  have hS4 := H4_asymp_S4 hℓ8 hN10000 hlln1 hlogN1 hP1 hY_pos hR_ge2 hR_le_N
    hR_le_cpsi htau_ge hL hQ_lo hz_le_2Y rfl
  have hS5 := H4_asymp_S5 hℓ8 hN10000 hlogN1 hnℓ hnlog hY_ge1 hY_hi hz_ge_N310 hB1 hB2
  have hQ_pos : 1 ≤ Q.card := by
    have h1 : (1 : ℝ) ≤ (Q.card : ℝ) := (Real.one_le_rpow hN_ge1 (by norm_num)).trans hz_ge_N310
    exact_mod_cast h1
  obtain ⟨A₁, A₂, hA_sub, hA_disj, hV_disj, hA₁_card, hA₂_card, hA₁_div⟩ :=
    hY0 y Q hy_ge_Y0 hQ_rng_1 hz_ge_Y13 hQ_div
  refine ⟨fun i => A₁ i ∪ A₂ i, ?_, ?_, ?_, ?_⟩
  · intro i; exact Finset.union_subset (hA_sub i).1 (hA_sub i).2
  · exact hV_disj
  · intro i
    have h1 : ((A₁ i ∪ A₂ i).card : ℝ) ≤ ((A₁ i).card : ℝ) + ((A₂ i).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (A₁ i) (A₂ i)
    have hrew : (Q.card : ℝ) / (16 * (ℓ : ℝ)) + (Q.card : ℝ) / (16 * (ℓ : ℝ)) =
        (Q.card : ℝ) / (8 * (ℓ : ℝ)) := by ring
    linarith [(hA₁_card i).2, (hA₂_card i).2]
  · intro i
    have hM_ge : (Q.card : ℝ) / (50 * (ℓ : ℝ)) ≤ (((A₁ i).card / 2 : ℕ) : ℝ) := by
      have h1 : (Q.card : ℝ) / (24 * (ℓ : ℝ)) ≤ ((A₁ i).card : ℝ) := (hA₁_card i).1
      have h2 : ((A₁ i).card : ℝ) / 2 - 1 / 2 ≤ (((A₁ i).card / 2 : ℕ) : ℝ) := by
        have hnat : (A₁ i).card ≤ 2 * ((A₁ i).card / 2) + 1 := by omega
        have hnat_r : ((A₁ i).card : ℝ) ≤ 2 * (((A₁ i).card / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
        linarith
      have hgap : (1 / 2 : ℝ) ≤ (Q.card : ℝ) / (1200 * (ℓ : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have ha : 600 * (ℓ : ℝ) ≤ (n : ℝ) ^ (1 / 100 : ℝ) := by linarith
        have hb : (n : ℝ) ^ (1 / 100 : ℝ) ≤ (n : ℝ) ^ (3 / 10 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
        linarith
      have hrew : (Q.card : ℝ) / (24 * (ℓ : ℝ)) / 2 - (Q.card : ℝ) / (1200 * (ℓ : ℝ)) =
          (Q.card : ℝ) / (50 * (ℓ : ℝ)) := by ring
      linarith
    have hGCD_i : ∀ T : Finset ℕ, T ⊆ A₁ i → (A₁ i).card / 2 ≤ T.card →
        ((T.gcd id : ℕ) : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) := by
      intro T hTA₁ hTcard
      have hT_gt : 64 * ((n : ℝ) / (n.totient : ℝ)) *
          (∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime), (1 - (1 : ℝ) / (p : ℝ))) *
          (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) < (T.card : ℝ) :=
        hGCD_thresh.trans_le (hM_ge.trans (by exact_mod_cast hTcard))
      have hvg := hQ_gcd T (hTA₁.trans (hA_sub i).1) hT_gt
      have hV1 : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv1
      have h1 : ((T.gcd id : ℕ) : ℝ) ≤ (v : ℝ) * ((T.gcd (fun x => x) : ℕ) : ℝ) :=
        le_mul_of_one_le_left (Nat.cast_nonneg _) hV1
      exact h1.trans hvg
    have hmod_A₂ : ∀ t ∈ A₂ i, 1 ≤ t ∧ (80 / (ℓ : ℝ)) * ((y : ℝ) / (v : ℝ)) ≤
        ((subsetSumsMod t (A₁ i)).card : ℝ) := by
      intro t htA₂
      have htQ : t ∈ Q := (hA_sub i).2 htA₂
      have ht_rng := hQ_rng t htQ
      have ht1 : 1 ≤ t := (hQ_rng_1 t htQ).1
      have : NeZero t := ⟨by omega⟩
      have ht_le_n : t ≤ n := by nlinarith
      have hy34_lt_tg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) →
          2 * (y : ℝ) ^ (3 / 4 : ℝ) < ((t / g : ℕ) : ℝ) := by
        intro g hg1 hg_le
        have htg_ge : (t : ℝ) / (g : ℝ) - 1 < ((t / g : ℕ) : ℝ) := by
          have hg_pos : (0 : ℝ) < g := by exact_mod_cast hg1
          have hdiv := Nat.lt_div_mul_add (a := t) (b := g) hg1
          have hdiv_r : (t : ℝ) < ((t / g : ℕ) : ℝ) * (g : ℝ) + (g : ℝ) := by exact_mod_cast hdiv
          rw [sub_lt_iff_lt_add, div_lt_iff₀ hg_pos]
          linarith
        have hY78 : (y : ℝ) ^ (7 / 8 : ℝ) ≤ (t : ℝ) / (g : ℝ) := by
          have hVg : (v : ℝ) * (g : ℝ) ≤ (y : ℝ) ^ (1 / 8 : ℝ) := by
            calc (v : ℝ) * (g : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) * (y : ℝ) ^ (1 / 16 : ℝ) := by gcongr
              _ = (y : ℝ) ^ (1 / 16 + 1 / 16 : ℝ) := (Real.rpow_add hY_pos _ _).symm
              _ = (y : ℝ) ^ (1 / 8 : ℝ) := by norm_num
          have h1 : (y : ℝ) / (y : ℝ) ^ (1 / 8 : ℝ) ≤ (t : ℝ) / (g : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hg1)]
            have htV : (y : ℝ) ≤ (t : ℝ) * (v : ℝ) := by
              have : (y : ℝ) ≤ (v : ℝ) * (t : ℝ) := by exact_mod_cast ht_rng.1
              linarith
            calc (y : ℝ) * (g : ℝ) ≤ ((t : ℝ) * (v : ℝ)) * (g : ℝ) :=
                  mul_le_mul_of_nonneg_right htV (Nat.cast_nonneg g)
              _ = (t : ℝ) * ((v : ℝ) * (g : ℝ)) := by ring
              _ ≤ (t : ℝ) * (y : ℝ) ^ (1 / 8 : ℝ) := mul_le_mul_of_nonneg_left hVg (Nat.cast_nonneg t)
          have hYeq : (y : ℝ) / (y : ℝ) ^ (1 / 8 : ℝ) = (y : ℝ) ^ (7 / 8 : ℝ) := by
            calc (y : ℝ) / (y : ℝ) ^ (1 / 8 : ℝ) = (y : ℝ) ^ (1 : ℝ) / (y : ℝ) ^ (1 / 8 : ℝ) := by
                  rw [Real.rpow_one]
              _ = (y : ℝ) ^ (1 - 1 / 8 : ℝ) := (Real.rpow_sub hY_pos _ _).symm
              _ = (y : ℝ) ^ (7 / 8 : ℝ) := by norm_num
          rwa [hYeq] at h1
        have h3_le : (3 : ℝ) ≤ (y : ℝ) ^ (1 / 8 : ℝ) := by
          have h3ℓ : (3 : ℝ) ≤ 25600 * (ℓ : ℝ) := by
            have : (8 : ℝ) ≤ ℓ := by exact_mod_cast hℓ8
            linarith
          have hN340 : (n : ℝ) ^ (1 / 100 : ℝ) ≤ ((n : ℝ) ^ (3 / 5 : ℝ)) ^ (1 / 8 : ℝ) := by
            rw [← Real.rpow_mul hN_pos.le]
            exact Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
          exact ((h3ℓ.trans hnℓ).trans hN340).trans (Real.rpow_le_rpow (by positivity) hy_lo (by norm_num))
        have hY34_ge1 : 1 ≤ (y : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hY_ge1 (by norm_num)
        have hY78_eq : (y : ℝ) ^ (7 / 8 : ℝ) = (y : ℝ) ^ (3 / 4 : ℝ) * (y : ℝ) ^ (1 / 8 : ℝ) := by
          rw [← Real.rpow_add hY_pos]; norm_num
        nlinarith
      have hlog_nn : 0 ≤ Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ) :=
        div_nonneg (by linarith) (Real.log_pos (by linarith)).le
      have hgt_res := growth_mod_t hξ_pos hH2 h_sub_ker h_proper_iff h_stable h_dcount h_full h_fiber
        h_struct h_ap_cover hℓ8 hℓ_ξ hv1 ht_rng.1 ht_rng.2 ht_le_n (hA_sub i).1 hQ_rng (hA₁_card i).1
        (hA₁_div i) hGCD_i hQ_ap hlog_nn hM_ge hQ_pos hy16_lt_div hy34_lt_tg
        ⟨hS1, hS2, hS3, hS4⟩ hS5
      refine ⟨ht1, ?_⟩
      have ht_ge : (y : ℝ) / (v : ℝ) ≤ (t : ℝ) := by
        rw [div_le_iff₀ (by exact_mod_cast hv1)]
        have : (y : ℝ) ≤ (v : ℝ) * (t : ℝ) := by exact_mod_cast ht_rng.1
        linarith
      exact (mul_le_mul_of_nonneg_left ht_ge (by positivity)).trans hgt_res
    constructor
    · have hU := h_union (A₁ i) (A₂ i) ((80 / (ℓ : ℝ)) * ((y : ℝ) / (v : ℝ))) (hA_disj i) hmod_A₂
      have hA₂_lo := (hA₂_card i).1
      have hV_pos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv1
      have hprod : (y : ℝ) * (Q.card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)) ≤
          ((A₂ i).card : ℝ) * ((80 / (ℓ : ℝ)) * ((y : ℝ) / (v : ℝ))) := by
        calc (y : ℝ) * (Q.card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ))
            ≤ (80 / 24 : ℝ) * ((y : ℝ) * (Q.card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ))) := by
              have : (0 : ℝ) ≤ (y : ℝ) * (Q.card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)) := by positivity
              linarith
          _ = ((Q.card : ℝ) / (24 * (ℓ : ℝ))) * ((80 / (ℓ : ℝ)) * ((y : ℝ) / (v : ℝ))) := by field_simp
          _ ≤ ((A₂ i).card : ℝ) * ((80 / (ℓ : ℝ)) * ((y : ℝ) / (v : ℝ))) :=
              mul_le_mul_of_nonneg_right hA₂_lo (by positivity)
      exact hprod.trans hU
    · intro d hd1 hall_mod
      have hd2 : 2 ≤ d := hd1
      have hdiv := hA₁_div i d hd2
      have hpos_card : 0 < ((A₁ i).filter (fun x => ¬ d ∣ x)).card := by
        have hge1 : (1 : ℝ) ≤ (y : ℝ) ^ (1 / 4 : ℝ) / (24 * (ℓ : ℝ)) := by
          have : (1 : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) := Real.one_le_rpow hY_ge1 (by norm_num)
          linarith
        have hpos_r : (0 : ℝ) < (((A₁ i).filter (fun x => ¬ d ∣ x)).card : ℝ) := by linarith
        exact_mod_cast hpos_r
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos_card
      have hxV : x ∈ A₁ i ∪ A₂ i := Finset.mem_union_left _ (Finset.mem_filter.mp hx).1
      have hx_ndvd : ¬ d ∣ x := (Finset.mem_filter.mp hx).2
      have h0_mem : 0 ∈ (A₁ i ∪ A₂ i).powerset.image (fun B => ∑ a ∈ B, a) :=
        Finset.mem_image.mpr ⟨∅, Finset.empty_mem_powerset _, by simp⟩
      have hx_mem : x ∈ (A₁ i ∪ A₂ i).powerset.image (fun B => ∑ a ∈ B, a) :=
        Finset.mem_image.mpr ⟨{x}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hxV), by simp⟩
      have hmod := hall_mod x hx_mem 0 h0_mem
      rw [Nat.zero_mod] at hmod
      exact hx_ndvd (Nat.dvd_of_mod_eq_zero hmod)

end Part4

theorem main : H1 → H2 → OMA.R_Erdos360_erdos_360_R1_H4_R1.H4 :=
  main_H4_from_parts tau_ge_inv_four_log_r exists_diverse_partition
    (fun _ _ _ hdisj hB => card_subsetSumsFin_union_ge hdisj hB)
    (fun _ _ A d k => nfoldSum_Gset_subset A d k)
    (fun _ _ A d hd => card_Gset_le A d hd)
    subsetSumsMod_eq_univ_of_diverse
    (fun _ _ _ _ hgt A u hne => card_coset_fiber_ge hgt A u hne)
    (fun _ _ H => subgroup_zmod_eq_ker H)
    (fun _ _ _ hq hq1 H hH => proper_subgroup_iff_two_le_q hq hq1 H hH)
    (fun _ hξ1 hξ2 hDF hCOS _ _ A _ hd1 h8d hAsmall hnot =>
      structure_lemma hξ1 hξ2 hDF hCOS (fun _ _ A d k => nfoldSum_Gset_subset A d k)
        (fun _ _ A d hd => card_Gset_le A d hd) A hd1 h8d hAsmall hnot)
    (fun _ _ _ _ _ hm hq2 hqd hL1 hLq u => ap_mod_t_cover hm hq2 hqd hL1 hLq u)

end OMA.R_Erdos360_erdos_360_R1_H4_R1_H4_R1
