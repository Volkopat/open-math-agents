import OMAReductions.R_Green97_green_97_variants_simkin_R2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Proof of `Green97.green_97.variants.simkin.R2.H3` via an explicit 8-fold symmetric
12 x 12 rational step density matrix achieving value > -1.94483 > -1.9449.
-/

section Green97SimkinH3

open Finset Real

private noncomputable def poly8 (q : ℝ) : ℝ :=
  1 + q + q ^ 2 / 2 + q ^ 3 / 6 + q ^ 4 / 24 + q ^ 5 / 120 +
    q ^ 6 / 720 + q ^ 7 / 5040 + q ^ 8 / 40320

private lemma poly8_le_exp {q : ℝ} (hq : 0 ≤ q) : poly8 q ≤ Real.exp q := by
  have h := Real.sum_le_exp_of_nonneg hq 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
    Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, pow_zero, pow_one, div_one, zero_add] at h
  unfold poly8
  linarith

private lemma exp_le_poly8_add {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.exp q ≤ poly8 q + q ^ 9 / 300000 := by
  have habs : |q| ≤ 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have h := Real.exp_bound habs (show 0 < 9 by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
    Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, pow_zero, pow_one, div_one, zero_add,
    abs_of_nonneg hq0] at h
  have hle := (abs_le.mp h).2
  have hcoef : q ^ 9 * (((9 : ℝ) + 1) / ((362880 : ℝ) * 9)) ≤ q ^ 9 / 300000 := by
    have hq9 : 0 ≤ q ^ 9 := pow_nonneg hq0 9
    have hc : ((9 : ℝ) + 1) / ((362880 : ℝ) * 9) ≤ 1 / 300000 := by norm_num
    calc q ^ 9 * (((9 : ℝ) + 1) / ((362880 : ℝ) * 9))
        ≤ q ^ 9 * (1 / 300000) := mul_le_mul_of_nonneg_left hc hq9
      _ = q ^ 9 / 300000 := by ring
  unfold poly8
  linarith

private lemma log_le_of_scale {x y q : ℝ} {s : ℕ} (hx : 0 < x) (hq : 0 ≤ q)
    (hmul : x * (2 : ℝ) ^ s = y) (hpoly : y ≤ poly8 q) :
    Real.log x ≤ q - (s : ℝ) * (6931471803 / 10000000000 : ℝ) := by
  have hy_pos : 0 < y := by rw [← hmul]; positivity
  have hly : Real.log y ≤ q := by
    have := Real.log_le_log hy_pos (hpoly.trans (poly8_le_exp hq))
    rwa [Real.log_exp] at this
  have hlog := congrArg Real.log hmul
  rw [Real.log_mul hx.ne' (by positivity), Real.log_pow] at hlog
  have hl2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hs_mul : (s : ℝ) * (6931471803 / 10000000000 : ℝ) ≤ (s : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg s)
  linarith

private lemma le_log_of_scale {x y q : ℝ} {s : ℕ} (hx : 0 < x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmul : x * (2 : ℝ) ^ s = y) (hpoly : poly8 q + q ^ 9 / 300000 ≤ y) :
    q - (s : ℝ) * (6931471808 / 10000000000 : ℝ) ≤ Real.log x := by
  have hly : q ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos q) ((exp_le_poly8_add hq0 hq1).trans hpoly)
    rwa [Real.log_exp] at this
  have hlog := congrArg Real.log hmul
  rw [Real.log_mul hx.ne' (by positivity), Real.log_pow] at hlog
  have hl2 : Real.log 2 ≤ (6931471808 / 10000000000 : ℝ) := by
    have := Real.log_two_lt_d9; linarith
  have hs_mul : (s : ℝ) * Real.log 2 ≤ (s : ℝ) * (6931471808 / 10000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg s)
  linarith

private lemma integral_mul_log_linear {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ∫ t in (0 : ℝ)..1, ((1 - t) * a + t * b) * Real.log ((1 - t) * a + t * b) =
      ((b ^ 2 * Real.log b - a ^ 2 * Real.log a) / 2 - (b ^ 2 - a ^ 2) / 4) / (b - a) := by
  let L : ℝ → ℝ := fun t => (1 - t) * a + t * b
  let F : ℝ → ℝ := fun t => ((L t) ^ 2 * Real.log (L t) / 2 - (L t) ^ 2 / 4) / (b - a)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hL_pos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < L t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    dsimp only [L]
    by_cases h0 : t = 0
    · subst h0; linarith
    · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
      have h1 : 0 ≤ (1 - t) * a := mul_nonneg (sub_nonneg.mpr ht.2) ha.le
      have h2 : 0 < t * b := mul_pos ht0 hb
      linarith
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (L t * Real.log (L t)) t := by
    intro t ht
    have hLp : 0 < L t := hL_pos t ht
    have hL' : HasDerivAt L (b - a) t := by
      have : L = fun s => a + (b - a) * s := by funext s; dsimp only [L]; ring
      rw [this]
      simpa using ((hasDerivAt_id t).const_mul (b - a)).const_add a
    have hsq : HasDerivAt (fun s => (L s) ^ 2) (2 * L t * (b - a)) t := by
      have h1 : HasDerivAt (fun s => L s * L s) ((b - a) * L t + L t * (b - a)) t := hL'.mul hL'
      have h2 : (fun s => (L s) ^ 2) = (fun s => L s * L s) := by funext s; ring
      have h3 : 2 * L t * (b - a) = (b - a) * L t + L t * (b - a) := by ring
      rw [h2, h3]
      exact h1
    have hlog : HasDerivAt (fun s => Real.log (L s)) ((b - a) / L t) t := by
      simpa [div_eq_mul_inv, mul_comm] using hL'.log hLp.ne'
    have hprod : HasDerivAt (fun s => (L s) ^ 2 * Real.log (L s))
        ((2 * L t * (b - a)) * Real.log (L t) + (L t) ^ 2 * ((b - a) / L t)) t :=
      hsq.mul hlog
    have hF : HasDerivAt F
        ((((2 * L t * (b - a)) * Real.log (L t) + (L t) ^ 2 * ((b - a) / L t)) / 2 -
          (2 * L t * (b - a)) / 4) / (b - a)) t :=
      ((hprod.div_const 2).sub (hsq.div_const 4)).div_const (b - a)
    convert hF using 1
    field_simp [hba, hLp.ne']
    ring
  have hcont : ContinuousOn (fun t => L t * Real.log (L t)) (Set.uIcc 0 1) := by
    have hLc : Continuous L := by fun_prop
    refine hLc.continuousOn.mul ?_
    intro t ht
    exact (Real.continuousAt_log (hL_pos t ht).ne').comp hLc.continuousAt |>.continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hint]
  dsimp only [F, L]
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add]
  ring

private def M6 : Fin 6 → Fin 6 → ℕ :=
  ![![582, 765, 955, 1127, 1252, 1319],
    ![765, 861, 993, 1083, 1137, 1161],
    ![955, 993, 987, 1018, 1024, 1023],
    ![1127, 1083, 1018, 939, 922, 911],
    ![1252, 1137, 1024, 922, 839, 826],
    ![1319, 1161, 1023, 911, 826, 760]]

private def idx6 (i : Fin 12) : Fin 6 :=
  if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩

private def A_nat (i j : Fin 12) : ℕ := M6 (idx6 i) (idx6 j)

private def d_nat (b : Bool) (k : ℕ) : ℕ :=
  12000 - ∑ i : Fin 12, ∑ j : Fin 12,
    if i.val + j.val + 1 = k then A_nat i (if b then j.rev else j) else 0

private lemma row_sum_nat : ∀ i : Fin 12, ∑ j : Fin 12, A_nat i j = 12000 := by decide
private lemma col_sum_nat : ∀ j : Fin 12, ∑ i : Fin 12, A_nat i j = 12000 := by decide
private lemma diag_le_nat : ∀ (b : Bool) (k : Fin 25),
    (∑ i : Fin 12, ∑ j : Fin 12,
      if i.val + j.val + 1 = k.val then A_nat i (if b then j.rev else j) else 0) ≤ 12000 := by decide

private def d_table : Fin 25 → ℕ :=
  ![12000, 11418, 10470, 9229, 7760, 6343, 5052, 4053, 3284, 2765, 2402, 2192, 2064,
    2192, 2402, 2765, 3284, 4053, 5052, 6343, 7760, 9229, 10470, 11418, 12000]

private lemma d_nat_eq_table : ∀ (b : Bool) (k : Fin 25), d_nat b k.val = d_table k := by decide

private lemma log_A_582 : Real.log (((291 : ℝ) / 500)) ≤ ((-5412831803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((291 : ℝ) / 500)) (y := ((291 : ℝ) / 250)) (q := ((18983 : ℝ) / 125000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_760 : Real.log (((19 : ℝ) / 25)) ≤ ((-2744351803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((19 : ℝ) / 25)) (y := ((38 : ℝ) / 25)) (q := ((52339 : ℝ) / 125000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_765 : Real.log (((153 : ℝ) / 200)) ≤ ((-2678781803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((153 : ℝ) / 200)) (y := ((153 : ℝ) / 100)) (q := ((425269 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_826 : Real.log (((413 : ℝ) / 500)) ≤ ((-1911591803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((413 : ℝ) / 500)) (y := ((413 : ℝ) / 250)) (q := ((125497 : ℝ) / 250000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_839 : Real.log (((839 : ℝ) / 1000)) ≤ ((-1755431803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((839 : ℝ) / 1000)) (y := ((839 : ℝ) / 500)) (q := ((129401 : ℝ) / 250000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_861 : Real.log (((861 : ℝ) / 1000)) ≤ ((-1496591803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((861 : ℝ) / 1000)) (y := ((861 : ℝ) / 500)) (q := ((8492 : ℝ) / 15625)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_911 : Real.log (((911 : ℝ) / 1000)) ≤ ((-932111803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((911 : ℝ) / 1000)) (y := ((911 : ℝ) / 500)) (q := ((9374 : ℝ) / 15625)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_922 : Real.log (((461 : ℝ) / 500)) ≤ ((-812081803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((461 : ℝ) / 500)) (y := ((461 : ℝ) / 250)) (q := ((611939 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_939 : Real.log (((939 : ℝ) / 1000)) ≤ ((-629381803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((939 : ℝ) / 1000)) (y := ((939 : ℝ) / 500)) (q := ((630209 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_955 : Real.log (((191 : ℝ) / 200)) ≤ ((-460421803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((191 : ℝ) / 200)) (y := ((191 : ℝ) / 100)) (q := ((129421 : ℝ) / 200000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_987 : Real.log (((987 : ℝ) / 1000)) ≤ ((-130841803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((987 : ℝ) / 1000)) (y := ((987 : ℝ) / 500)) (q := ((680063 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_993 : Real.log (((993 : ℝ) / 1000)) ≤ ((-70231803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((993 : ℝ) / 1000)) (y := ((993 : ℝ) / 500)) (q := ((171531 : ℝ) / 250000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_1018 : Real.log (((509 : ℝ) / 500)) ≤ ((17841 : ℝ) / 1000000) := by
  have h := log_le_of_scale (x := ((509 : ℝ) / 500)) (y := ((509 : ℝ) / 500)) (q := ((17841 : ℝ) / 1000000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_1023 : Real.log (((1023 : ℝ) / 1000)) ≤ ((22741 : ℝ) / 1000000) := by
  have h := log_le_of_scale (x := ((1023 : ℝ) / 1000)) (y := ((1023 : ℝ) / 1000)) (q := ((22741 : ℝ) / 1000000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_1024 : Real.log (((128 : ℝ) / 125)) ≤ ((11859 : ℝ) / 500000) := by
  have h := log_le_of_scale (x := ((128 : ℝ) / 125)) (y := ((128 : ℝ) / 125)) (q := ((11859 : ℝ) / 500000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_1083 : Real.log (((1083 : ℝ) / 1000)) ≤ ((9967 : ℝ) / 125000) := by
  have h := log_le_of_scale (x := ((1083 : ℝ) / 1000)) (y := ((1083 : ℝ) / 1000)) (q := ((9967 : ℝ) / 125000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_1127 : Real.log (((1127 : ℝ) / 1000)) ≤ ((119561 : ℝ) / 1000000) := by
  have h := log_le_of_scale (x := ((1127 : ℝ) / 1000)) (y := ((1127 : ℝ) / 1000)) (q := ((119561 : ℝ) / 1000000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_1137 : Real.log (((1137 : ℝ) / 1000)) ≤ ((25679 : ℝ) / 200000) := by
  have h := log_le_of_scale (x := ((1137 : ℝ) / 1000)) (y := ((1137 : ℝ) / 1000)) (q := ((25679 : ℝ) / 200000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_1161 : Real.log (((1161 : ℝ) / 1000)) ≤ ((149283 : ℝ) / 1000000) := by
  have h := log_le_of_scale (x := ((1161 : ℝ) / 1000)) (y := ((1161 : ℝ) / 1000)) (q := ((149283 : ℝ) / 1000000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_1252 : Real.log (((313 : ℝ) / 250)) ≤ ((28093 : ℝ) / 125000) := by
  have h := log_le_of_scale (x := ((313 : ℝ) / 250)) (y := ((313 : ℝ) / 250)) (q := ((28093 : ℝ) / 125000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_A_1319 : Real.log (((1319 : ℝ) / 1000)) ≤ ((443 : ℝ) / 1600) := by
  have h := log_le_of_scale (x := ((1319 : ℝ) / 1000)) (y := ((1319 : ℝ) / 1000)) (q := ((443 : ℝ) / 1600)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_0 : Real.log ((1 : ℝ)) ≤ ((1 : ℝ) / 1000000) := by
  have h := log_le_of_scale (x := (1 : ℝ)) (y := (1 : ℝ)) (q := ((1 : ℝ) / 1000000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_1 : Real.log (((1903 : ℝ) / 2000)) ≤ ((-497141803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((1903 : ℝ) / 2000)) (y := ((1903 : ℝ) / 1000)) (q := ((643433 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_1 : ((-15536619 : ℝ) / 312500000) ≤ Real.log (((1903 : ℝ) / 2000)) := by
  have h := le_log_of_scale (x := ((1903 : ℝ) / 2000)) (y := ((1903 : ℝ) / 1000)) (q := ((64343 : ℝ) / 100000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_2 : Real.log (((349 : ℝ) / 400)) ≤ ((-1363911803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((349 : ℝ) / 400)) (y := ((349 : ℝ) / 200)) (q := ((139189 : ℝ) / 250000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_2 : ((-85246363 : ℝ) / 625000000) ≤ Real.log (((349 : ℝ) / 400)) := by
  have h := le_log_of_scale (x := ((349 : ℝ) / 400)) (y := ((349 : ℝ) / 200)) (q := ((556753 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_3 : Real.log (((9229 : ℝ) / 12000)) ≤ ((-2625541803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((9229 : ℝ) / 12000)) (y := ((9229 : ℝ) / 6000)) (q := ((430593 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_3 : ((-82049119 : ℝ) / 312500000) ≤ Real.log (((9229 : ℝ) / 12000)) := by
  have h := le_log_of_scale (x := ((9229 : ℝ) / 12000)) (y := ((9229 : ℝ) / 6000)) (q := ((43059 : ℝ) / 100000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_4 : Real.log (((97 : ℝ) / 150)) ≤ ((-4359231803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((97 : ℝ) / 150)) (y := ((97 : ℝ) / 75)) (q := ((32153 : ℝ) / 125000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_4 : ((-272453863 : ℝ) / 625000000) ≤ Real.log (((97 : ℝ) / 150)) := by
  have h := le_log_of_scale (x := ((97 : ℝ) / 150)) (y := ((97 : ℝ) / 75)) (q := ((257221 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_5 : Real.log (((6343 : ℝ) / 12000)) ≤ ((-6375531803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((6343 : ℝ) / 12000)) (y := ((6343 : ℝ) / 6000)) (q := ((27797 : ℝ) / 500000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_5 : ((-398472613 : ℝ) / 625000000) ≤ Real.log (((6343 : ℝ) / 12000)) := by
  have h := le_log_of_scale (x := ((6343 : ℝ) / 12000)) (y := ((6343 : ℝ) / 6000)) (q := ((55591 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_6 : Real.log (((421 : ℝ) / 1000)) ≤ ((-4325606803 : ℝ) / 5000000000) := by
  have h := log_le_of_scale (x := ((421 : ℝ) / 1000)) (y := ((421 : ℝ) / 250)) (q := ((521173 : ℝ) / 1000000)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_6 : ((-270351363 : ℝ) / 312500000) ≤ Real.log (((421 : ℝ) / 1000)) := by
  have h := le_log_of_scale (x := ((421 : ℝ) / 1000)) (y := ((421 : ℝ) / 250)) (q := ((52117 : ℝ) / 100000)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_7 : Real.log (((1351 : ℝ) / 4000)) ≤ ((-5427236803 : ℝ) / 5000000000) := by
  have h := log_le_of_scale (x := ((1351 : ℝ) / 4000)) (y := ((1351 : ℝ) / 1000)) (q := ((300847 : ℝ) / 1000000)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_7 : ((-169601619 : ℝ) / 156250000) ≤ Real.log (((1351 : ℝ) / 4000)) := by
  have h := le_log_of_scale (x := ((1351 : ℝ) / 4000)) (y := ((1351 : ℝ) / 1000)) (q := ((75211 : ℝ) / 250000)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_8 : Real.log (((821 : ℝ) / 3000)) ≤ ((-6479216803 : ℝ) / 5000000000) := by
  have h := log_le_of_scale (x := ((821 : ℝ) / 3000)) (y := ((821 : ℝ) / 750)) (q := ((90451 : ℝ) / 1000000)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_8 : ((-101237997 : ℝ) / 78125000) ≤ Real.log (((821 : ℝ) / 3000)) := by
  have h := le_log_of_scale (x := ((821 : ℝ) / 3000)) (y := ((821 : ℝ) / 750)) (q := ((5653 : ℝ) / 62500)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_9 : Real.log (((553 : ℝ) / 2400)) ≤ ((-14678645409 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((553 : ℝ) / 2400)) (y := ((553 : ℝ) / 300)) (q := ((611577 : ℝ) / 1000000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_9 : ((-458708607 : ℝ) / 312500000) ≤ Real.log (((553 : ℝ) / 2400)) := by
  have h := le_log_of_scale (x := ((553 : ℝ) / 2400)) (y := ((553 : ℝ) / 300)) (q := ((305787 : ℝ) / 500000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_10 : Real.log (((1201 : ℝ) / 6000)) ≤ ((-16086035409 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((1201 : ℝ) / 6000)) (y := ((1201 : ℝ) / 750)) (q := ((235419 : ℝ) / 500000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_10 : ((-1005379089 : ℝ) / 625000000) ≤ Real.log (((1201 : ℝ) / 6000)) := by
  have h := le_log_of_scale (x := ((1201 : ℝ) / 6000)) (y := ((1201 : ℝ) / 750)) (q := ((94167 : ℝ) / 200000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_11 : Real.log (((137 : ℝ) / 750)) ≤ ((-17000905409 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((137 : ℝ) / 750)) (y := ((548 : ℝ) / 375)) (q := ((379351 : ℝ) / 1000000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_11 : ((-16602476 : ℝ) / 9765625) ≤ Real.log (((137 : ℝ) / 750)) := by
  have h := le_log_of_scale (x := ((137 : ℝ) / 750)) (y := ((548 : ℝ) / 375)) (q := ((94837 : ℝ) / 250000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_ub_12 : Real.log (((43 : ℝ) / 250)) ≤ ((-17602595409 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((43 : ℝ) / 250)) (y := ((172 : ℝ) / 125)) (q := ((159591 : ℝ) / 500000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith
private lemma log_d_lb_12 : ((-1100164089 : ℝ) / 625000000) ≤ Real.log (((43 : ℝ) / 250)) := by
  have h := le_log_of_scale (x := ((43 : ℝ) / 250)) (y := ((172 : ℝ) / 125)) (q := ((319179 : ℝ) / 1000000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold poly8; norm_num)
  linarith

private def log_A_ub_int : ℕ → ℤ
  | 582 => -5412831803
  | 760 => -2744351803
  | 765 => -2678781803
  | 826 => -1911591803
  | 839 => -1755431803
  | 861 => -1496591803
  | 911 => -932111803
  | 922 => -812081803
  | 939 => -629381803
  | 955 => -460421803
  | 987 => -130841803
  | 993 => -70231803
  | 1018 => 178410000
  | 1023 => 227410000
  | 1024 => 237180000
  | 1083 => 797360000
  | 1127 => 1195610000
  | 1137 => 1283950000
  | 1161 => 1492830000
  | 1252 => 2247440000
  | 1319 => 2768750000
  | _ => 0

private lemma A_nat_mem : ∀ i j : Fin 12, A_nat i j ∈ ({582, 760, 765, 826, 839, 861, 911, 922, 939, 955, 987, 993, 1018, 1023, 1024, 1083, 1127, 1137, 1161, 1252, 1319} : Finset ℕ) := by decide

private lemma log_A_ub_int_spec (n : ℕ) (hn : n ∈ ({582, 760, 765, 826, 839, 861, 911, 922, 939, 955, 987, 993, 1018, 1023, 1024, 1083, 1127, 1137, 1161, 1252, 1319} : Finset ℕ)) :
    Real.log ((n : ℝ) / 1000) ≤ ((log_A_ub_int n : ℤ) : ℝ) / 10000000000 := by
  fin_cases hn
  · simpa [log_A_ub_int] using (by have h := log_A_582; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((582 : ℝ) / 1000) ≤ ((log_A_ub_int 582 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_760; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((760 : ℝ) / 1000) ≤ ((log_A_ub_int 760 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_765; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((765 : ℝ) / 1000) ≤ ((log_A_ub_int 765 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_826; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((826 : ℝ) / 1000) ≤ ((log_A_ub_int 826 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_839; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((839 : ℝ) / 1000) ≤ ((log_A_ub_int 839 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_861; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((861 : ℝ) / 1000) ≤ ((log_A_ub_int 861 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_911; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((911 : ℝ) / 1000) ≤ ((log_A_ub_int 911 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_922; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((922 : ℝ) / 1000) ≤ ((log_A_ub_int 922 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_939; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((939 : ℝ) / 1000) ≤ ((log_A_ub_int 939 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_955; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((955 : ℝ) / 1000) ≤ ((log_A_ub_int 955 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_987; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((987 : ℝ) / 1000) ≤ ((log_A_ub_int 987 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_993; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((993 : ℝ) / 1000) ≤ ((log_A_ub_int 993 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_1018; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((1018 : ℝ) / 1000) ≤ ((log_A_ub_int 1018 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_1023; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((1023 : ℝ) / 1000) ≤ ((log_A_ub_int 1023 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_1024; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((1024 : ℝ) / 1000) ≤ ((log_A_ub_int 1024 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_1083; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((1083 : ℝ) / 1000) ≤ ((log_A_ub_int 1083 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_1127; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((1127 : ℝ) / 1000) ≤ ((log_A_ub_int 1127 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_1137; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((1137 : ℝ) / 1000) ≤ ((log_A_ub_int 1137 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_1161; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((1161 : ℝ) / 1000) ≤ ((log_A_ub_int 1161 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_1252; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((1252 : ℝ) / 1000) ≤ ((log_A_ub_int 1252 : ℤ) : ℝ) / 10000000000)
  · simpa [log_A_ub_int] using (by have h := log_A_1319; norm_num [log_A_ub_int] at h ⊢; linarith : Real.log ((1319 : ℝ) / 1000) ≤ ((log_A_ub_int 1319 : ℤ) : ℝ) / 10000000000)

private lemma sum_A_int_le :
    (∑ i : Fin 12, ∑ j : Fin 12, (A_nat i j : ℤ) * log_A_ub_int (A_nat i j)) ≤ 19460894925056 := by
  decide

private lemma sum_A_bound :
    ∑ i : Fin 12, ∑ j : Fin 12, ((A_nat i j : ℝ) / 1000) * Real.log ((A_nat i j : ℝ) / 1000) ≤ ((76019120801 : ℝ) / 39062500000) := by
  have hcell : ∀ i j : Fin 12, ((A_nat i j : ℝ) / 1000) * Real.log ((A_nat i j : ℝ) / 1000) ≤
      ((A_nat i j : ℝ) / 1000) * (((log_A_ub_int (A_nat i j) : ℤ) : ℝ) / 10000000000) := fun i j =>
    mul_le_mul_of_nonneg_left (log_A_ub_int_spec (A_nat i j) (A_nat_mem i j)) (by positivity)
  have hsum_eq : (∑ i : Fin 12, ∑ j : Fin 12,
      ((A_nat i j : ℝ) / 1000) * (((log_A_ub_int (A_nat i j) : ℤ) : ℝ) / 10000000000)) =
      ((∑ i : Fin 12, ∑ j : Fin 12, (A_nat i j : ℤ) * log_A_ub_int (A_nat i j) : ℤ) : ℝ) / 10000000000000 := by
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro j _
    push_cast
    ring
  calc ∑ i : Fin 12, ∑ j : Fin 12, ((A_nat i j : ℝ) / 1000) * Real.log ((A_nat i j : ℝ) / 1000)
      ≤ ∑ i : Fin 12, ∑ j : Fin 12,
          ((A_nat i j : ℝ) / 1000) * (((log_A_ub_int (A_nat i j) : ℤ) : ℝ) / 10000000000) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hcell i j
    _ = ((∑ i : Fin 12, ∑ j : Fin 12, (A_nat i j : ℤ) * log_A_ub_int (A_nat i j) : ℤ) : ℝ) / 10000000000000 := hsum_eq
    _ ≤ (19460894925056 : ℝ) / 10000000000000 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact_mod_cast sum_A_int_le
    _ = ((76019120801 : ℝ) / 39062500000) := by norm_num

private lemma int_d_0 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * ((1 : ℝ)) + t * (((1903 : ℝ) / 2000))) * Real.log ((1 - t) * ((1 : ℝ)) + t * (((1903 : ℝ) / 2000))) ≤ ((-2889141873829 : ℝ) / 121250000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_0
  have hb := log_d_lb_1
  ring_nf
  linarith

private lemma int_d_rev_0 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1903 : ℝ) / 2000)) + t * ((1 : ℝ))) * Real.log ((1 - t) * (((1903 : ℝ) / 2000)) + t * ((1 : ℝ))) ≤ ((-2889141873829 : ℝ) / 121250000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_0
  have hb := log_d_lb_1
  ring_nf
  linarith

private lemma int_d_1 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1903 : ℝ) / 2000)) + t * (((349 : ℝ) / 400))) * Real.log ((1 - t) * (((1903 : ℝ) / 2000)) + t * (((349 : ℝ) / 400))) ≤ ((-529036895755227 : ℝ) / 6320000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_1
  have hb := log_d_lb_2
  ring_nf
  linarith

private lemma int_d_rev_1 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((349 : ℝ) / 400)) + t * (((1903 : ℝ) / 2000))) * Real.log ((1 - t) * (((349 : ℝ) / 400)) + t * (((1903 : ℝ) / 2000))) ≤ ((-529036895755227 : ℝ) / 6320000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_1
  have hb := log_d_lb_2
  ring_nf
  linarith

private lemma int_d_2 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((349 : ℝ) / 400)) + t * (((9229 : ℝ) / 12000))) * Real.log ((1 - t) * (((349 : ℝ) / 400)) + t * (((9229 : ℝ) / 12000))) ≤ ((-12028480828430843 : ℝ) / 74460000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_2
  have hb := log_d_lb_3
  ring_nf
  linarith

private lemma int_d_rev_2 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((9229 : ℝ) / 12000)) + t * (((349 : ℝ) / 400))) * Real.log ((1 - t) * (((9229 : ℝ) / 12000)) + t * (((349 : ℝ) / 400))) ≤ ((-12028480828430843 : ℝ) / 74460000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_2
  have hb := log_d_lb_3
  ring_nf
  linarith

private lemma int_d_3 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((9229 : ℝ) / 12000)) + t * (((97 : ℝ) / 150))) * Real.log ((1 - t) * (((9229 : ℝ) / 12000)) + t * (((97 : ℝ) / 150))) ≤ ((-85908976543236323 : ℝ) / 352560000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_3
  have hb := log_d_lb_4
  ring_nf
  linarith

private lemma int_d_rev_3 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((97 : ℝ) / 150)) + t * (((9229 : ℝ) / 12000))) * Real.log ((1 - t) * (((97 : ℝ) / 150)) + t * (((9229 : ℝ) / 12000))) ≤ ((-85908976543236323 : ℝ) / 352560000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_3
  have hb := log_d_lb_4
  ring_nf
  linarith

private lemma int_d_4 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((97 : ℝ) / 150)) + t * (((6343 : ℝ) / 12000))) * Real.log ((1 - t) * (((97 : ℝ) / 150)) + t * (((6343 : ℝ) / 12000))) ≤ ((-6619382253715963 : ℝ) / 21255000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_4
  have hb := log_d_lb_5
  ring_nf
  linarith

private lemma int_d_rev_4 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((6343 : ℝ) / 12000)) + t * (((97 : ℝ) / 150))) * Real.log ((1 - t) * (((6343 : ℝ) / 12000)) + t * (((97 : ℝ) / 150))) ≤ ((-6619382253715963 : ℝ) / 21255000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_4
  have hb := log_d_lb_5
  ring_nf
  linarith

private lemma int_d_5 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((6343 : ℝ) / 12000)) + t * (((421 : ℝ) / 1000))) * Real.log ((1 - t) * (((6343 : ℝ) / 12000)) + t * (((421 : ℝ) / 1000))) ≤ ((-109262503707181483 : ℝ) / 309840000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_5
  have hb := log_d_lb_6
  ring_nf
  linarith

private lemma int_d_rev_5 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((421 : ℝ) / 1000)) + t * (((6343 : ℝ) / 12000))) * Real.log ((1 - t) * (((421 : ℝ) / 1000)) + t * (((6343 : ℝ) / 12000))) ≤ ((-109262503707181483 : ℝ) / 309840000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_5
  have hb := log_d_lb_6
  ring_nf
  linarith

private lemma int_d_6 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((421 : ℝ) / 1000)) + t * (((1351 : ℝ) / 4000))) * Real.log ((1 - t) * (((421 : ℝ) / 1000)) + t * (((1351 : ℝ) / 4000))) ≤ ((-61095125983937 : ℝ) / 166500000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_6
  have hb := log_d_lb_7
  ring_nf
  linarith

private lemma int_d_rev_6 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1351 : ℝ) / 4000)) + t * (((421 : ℝ) / 1000))) * Real.log ((1 - t) * (((1351 : ℝ) / 4000)) + t * (((421 : ℝ) / 1000))) ≤ ((-61095125983937 : ℝ) / 166500000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_6
  have hb := log_d_lb_7
  ring_nf
  linarith

private lemma int_d_7 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1351 : ℝ) / 4000)) + t * (((821 : ℝ) / 3000))) * Real.log ((1 - t) * (((1351 : ℝ) / 4000)) + t * (((821 : ℝ) / 3000))) ≤ ((-33381278667113579 : ℝ) / 92280000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_7
  have hb := log_d_lb_8
  ring_nf
  linarith

private lemma int_d_rev_7 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((821 : ℝ) / 3000)) + t * (((1351 : ℝ) / 4000))) * Real.log ((1 - t) * (((821 : ℝ) / 3000)) + t * (((1351 : ℝ) / 4000))) ≤ ((-33381278667113579 : ℝ) / 92280000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_7
  have hb := log_d_lb_8
  ring_nf
  linarith

private lemma int_d_8 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((821 : ℝ) / 3000)) + t * (((553 : ℝ) / 2400))) * Real.log ((1 - t) * (((821 : ℝ) / 3000)) + t * (((553 : ℝ) / 2400))) ≤ ((-337715839227337 : ℝ) / 973125000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_8
  have hb := log_d_lb_9
  ring_nf
  linarith

private lemma int_d_rev_8 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((553 : ℝ) / 2400)) + t * (((821 : ℝ) / 3000))) * Real.log ((1 - t) * (((553 : ℝ) / 2400)) + t * (((821 : ℝ) / 3000))) ≤ ((-337715839227337 : ℝ) / 973125000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_8
  have hb := log_d_lb_9
  ring_nf
  linarith

private lemma int_d_9 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((553 : ℝ) / 2400)) + t * (((1201 : ℝ) / 6000))) * Real.log ((1 - t) * (((553 : ℝ) / 2400)) + t * (((1201 : ℝ) / 6000))) ≤ ((-3198824936938881 : ℝ) / 9680000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_9
  have hb := log_d_lb_10
  ring_nf
  linarith

private lemma int_d_rev_9 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1201 : ℝ) / 6000)) + t * (((553 : ℝ) / 2400))) * Real.log ((1 - t) * (((1201 : ℝ) / 6000)) + t * (((553 : ℝ) / 2400))) ≤ ((-3198824936938881 : ℝ) / 9680000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_9
  have hb := log_d_lb_10
  ring_nf
  linarith

private lemma int_d_10 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1201 : ℝ) / 6000)) + t * (((137 : ℝ) / 750))) * Real.log ((1 - t) * (((1201 : ℝ) / 6000)) + t * (((137 : ℝ) / 750))) ≤ ((-159465716548057 : ℝ) / 504000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_10
  have hb := log_d_lb_11
  ring_nf
  linarith

private lemma int_d_rev_10 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((137 : ℝ) / 750)) + t * (((1201 : ℝ) / 6000))) * Real.log ((1 - t) * (((137 : ℝ) / 750)) + t * (((1201 : ℝ) / 6000))) ≤ ((-159465716548057 : ℝ) / 504000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_10
  have hb := log_d_lb_11
  ring_nf
  linarith

private lemma int_d_11 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((137 : ℝ) / 750)) + t * (((43 : ℝ) / 250))) * Real.log ((1 - t) * (((137 : ℝ) / 750)) + t * (((43 : ℝ) / 250))) ≤ ((-36804703940737 : ℝ) / 120000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_11
  have hb := log_d_lb_12
  ring_nf
  linarith

private lemma int_d_rev_11 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((43 : ℝ) / 250)) + t * (((137 : ℝ) / 750))) * Real.log ((1 - t) * (((43 : ℝ) / 250)) + t * (((137 : ℝ) / 750))) ≤ ((-36804703940737 : ℝ) / 120000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_11
  have hb := log_d_lb_12
  ring_nf
  linarith

set_option maxHeartbeats 1200000 in
theorem OMA.solution :
    OMA.R_Green97_green_97_variants_simkin_R2.H3 := by
  let A : Fin 12 → Fin 12 → ℝ := fun i j => (A_nat i j : ℝ) / 1000
  let f : ℝ → ℝ := fun x => x * Real.log x
  let d : Bool → ℕ → ℝ := fun b k =>
    1 - (∑ i : Fin 12, ∑ j : Fin 12,
      if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / 12
  let r : ℝ := -3 - (∑ i : Fin 12, ∑ j : Fin 12, f (A i j)) / (12 : ℝ) ^ 2 -
    (∑ b : Bool, ∑ k : Fin 24, ∫ t in (0 : ℝ)..1,
      f ((1 - t) * d b k.val + t * d b (k.val + 1))) / 12
  have hd_eq : ∀ (b : Bool) (k : Fin 25), d b k.val = (d_table k : ℝ) / 12000 := by
    intro b k
    dsimp only [d, A]
    have hle := diag_le_nat b k
    have hsum : (∑ i : Fin 12, ∑ j : Fin 12,
        if i.val + j.val + 1 = k.val then ((A_nat i (if b then j.rev else j) : ℝ) / 1000) else 0) =
        ((∑ i : Fin 12, ∑ j : Fin 12,
          if i.val + j.val + 1 = k.val then A_nat i (if b then j.rev else j) else 0 : ℕ) : ℝ) / 1000 := by
      rw [Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro i _
      rw [Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> simp
    rw [hsum, div_div, show (1000 : ℝ) * 12 = 12000 by norm_num]
    have hsub : (d_table k : ℝ) = (12000 : ℝ) -
        ((∑ i : Fin 12, ∑ j : Fin 12,
          if i.val + j.val + 1 = k.val then A_nat i (if b then j.rev else j) else 0 : ℕ) : ℝ) := by
      have hnat := d_nat_eq_table b k
      dsimp only [d_nat] at hnat
      rw [← hnat, Nat.cast_sub hle]
      simp only [Nat.cast_ofNat]
    rw [hsub, sub_div, div_self (by norm_num : (12000 : ℝ) ≠ 0)]
  refine ⟨r, ⟨12, by norm_num, A, ?_, ?_, ?_, ?_, rfl⟩, ?_⟩
  · intro i j; dsimp only [A]; positivity
  · intro i
    dsimp only [A]
    rw [← Finset.sum_div]
    have h : (∑ j : Fin 12, (A_nat i j : ℝ)) = 12000 := by exact_mod_cast row_sum_nat i
    rw [h]; norm_num
  · intro j
    dsimp only [A]
    rw [← Finset.sum_div]
    have h : (∑ i : Fin 12, (A_nat i j : ℝ)) = 12000 := by exact_mod_cast col_sum_nat j
    rw [h]; norm_num
  · intro b k
    change 0 ≤ d b k.val
    rw [hd_eq b k]; positivity
  ·
    have hsum_int : ∀ b : Bool,
        ∑ k : Fin 24, ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1)) ≤ ((-147809600682664895195852314115805512593 : ℝ) / 23051290904263358923414665937500000000) := by
      intro b
      have hterm : ∀ k : Fin 24,
          ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1)) ≤
            match k.val with

              | 0 => ((-2889141873829 : ℝ) / 121250000000000)
              | 1 => ((-529036895755227 : ℝ) / 6320000000000000)
              | 2 => ((-12028480828430843 : ℝ) / 74460000000000000)
              | 3 => ((-85908976543236323 : ℝ) / 352560000000000000)
              | 4 => ((-6619382253715963 : ℝ) / 21255000000000000)
              | 5 => ((-109262503707181483 : ℝ) / 309840000000000000)
              | 6 => ((-61095125983937 : ℝ) / 166500000000000)
              | 7 => ((-33381278667113579 : ℝ) / 92280000000000000)
              | 8 => ((-337715839227337 : ℝ) / 973125000000000)
              | 9 => ((-3198824936938881 : ℝ) / 9680000000000000)
              | 10 => ((-159465716548057 : ℝ) / 504000000000000)
              | 11 => ((-36804703940737 : ℝ) / 120000000000000)
              | 23 => ((-2889141873829 : ℝ) / 121250000000000)
              | 22 => ((-529036895755227 : ℝ) / 6320000000000000)
              | 21 => ((-12028480828430843 : ℝ) / 74460000000000000)
              | 20 => ((-85908976543236323 : ℝ) / 352560000000000000)
              | 19 => ((-6619382253715963 : ℝ) / 21255000000000000)
              | 18 => ((-109262503707181483 : ℝ) / 309840000000000000)
              | 17 => ((-61095125983937 : ℝ) / 166500000000000)
              | 16 => ((-33381278667113579 : ℝ) / 92280000000000000)
              | 15 => ((-337715839227337 : ℝ) / 973125000000000)
              | 14 => ((-3198824936938881 : ℝ) / 9680000000000000)
              | 13 => ((-159465716548057 : ℝ) / 504000000000000)
              | 12 => ((-36804703940737 : ℝ) / 120000000000000)
              | _ => 0 := by
        intro k
        have h1 : d b k.val = (d_table ⟨k.val, by omega⟩ : ℝ) / 12000 := hd_eq b ⟨k.val, by omega⟩
        have h2 : d b (k.val + 1) = (d_table ⟨k.val + 1, by omega⟩ : ℝ) / 12000 := hd_eq b ⟨k.val + 1, by omega⟩
        rw [h1, h2]
        dsimp only [f]
        fin_cases k <;> simp only [d_table]

        · simpa [show (12000 : ℝ) / 12000 = (1 : ℝ) by norm_num, show (11418 : ℝ) / 12000 = ((1903 : ℝ) / 2000) by norm_num] using int_d_0
        · simpa [show (11418 : ℝ) / 12000 = ((1903 : ℝ) / 2000) by norm_num, show (10470 : ℝ) / 12000 = ((349 : ℝ) / 400) by norm_num] using int_d_1
        · simpa [show (10470 : ℝ) / 12000 = ((349 : ℝ) / 400) by norm_num, show (9229 : ℝ) / 12000 = ((9229 : ℝ) / 12000) by norm_num] using int_d_2
        · simpa [show (9229 : ℝ) / 12000 = ((9229 : ℝ) / 12000) by norm_num, show (7760 : ℝ) / 12000 = ((97 : ℝ) / 150) by norm_num] using int_d_3
        · simpa [show (7760 : ℝ) / 12000 = ((97 : ℝ) / 150) by norm_num, show (6343 : ℝ) / 12000 = ((6343 : ℝ) / 12000) by norm_num] using int_d_4
        · simpa [show (6343 : ℝ) / 12000 = ((6343 : ℝ) / 12000) by norm_num, show (5052 : ℝ) / 12000 = ((421 : ℝ) / 1000) by norm_num] using int_d_5
        · simpa [show (5052 : ℝ) / 12000 = ((421 : ℝ) / 1000) by norm_num, show (4053 : ℝ) / 12000 = ((1351 : ℝ) / 4000) by norm_num] using int_d_6
        · simpa [show (4053 : ℝ) / 12000 = ((1351 : ℝ) / 4000) by norm_num, show (3284 : ℝ) / 12000 = ((821 : ℝ) / 3000) by norm_num] using int_d_7
        · simpa [show (3284 : ℝ) / 12000 = ((821 : ℝ) / 3000) by norm_num, show (2765 : ℝ) / 12000 = ((553 : ℝ) / 2400) by norm_num] using int_d_8
        · simpa [show (2765 : ℝ) / 12000 = ((553 : ℝ) / 2400) by norm_num, show (2402 : ℝ) / 12000 = ((1201 : ℝ) / 6000) by norm_num] using int_d_9
        · simpa [show (2402 : ℝ) / 12000 = ((1201 : ℝ) / 6000) by norm_num, show (2192 : ℝ) / 12000 = ((137 : ℝ) / 750) by norm_num] using int_d_10
        · simpa [show (2192 : ℝ) / 12000 = ((137 : ℝ) / 750) by norm_num, show (2064 : ℝ) / 12000 = ((43 : ℝ) / 250) by norm_num] using int_d_11
        · simpa [show (2064 : ℝ) / 12000 = ((43 : ℝ) / 250) by norm_num, show (2192 : ℝ) / 12000 = ((137 : ℝ) / 750) by norm_num] using int_d_rev_11
        · simpa [show (2192 : ℝ) / 12000 = ((137 : ℝ) / 750) by norm_num, show (2402 : ℝ) / 12000 = ((1201 : ℝ) / 6000) by norm_num] using int_d_rev_10
        · simpa [show (2402 : ℝ) / 12000 = ((1201 : ℝ) / 6000) by norm_num, show (2765 : ℝ) / 12000 = ((553 : ℝ) / 2400) by norm_num] using int_d_rev_9
        · simpa [show (2765 : ℝ) / 12000 = ((553 : ℝ) / 2400) by norm_num, show (3284 : ℝ) / 12000 = ((821 : ℝ) / 3000) by norm_num] using int_d_rev_8
        · simpa [show (3284 : ℝ) / 12000 = ((821 : ℝ) / 3000) by norm_num, show (4053 : ℝ) / 12000 = ((1351 : ℝ) / 4000) by norm_num] using int_d_rev_7
        · simpa [show (4053 : ℝ) / 12000 = ((1351 : ℝ) / 4000) by norm_num, show (5052 : ℝ) / 12000 = ((421 : ℝ) / 1000) by norm_num] using int_d_rev_6
        · simpa [show (5052 : ℝ) / 12000 = ((421 : ℝ) / 1000) by norm_num, show (6343 : ℝ) / 12000 = ((6343 : ℝ) / 12000) by norm_num] using int_d_rev_5
        · simpa [show (6343 : ℝ) / 12000 = ((6343 : ℝ) / 12000) by norm_num, show (7760 : ℝ) / 12000 = ((97 : ℝ) / 150) by norm_num] using int_d_rev_4
        · simpa [show (7760 : ℝ) / 12000 = ((97 : ℝ) / 150) by norm_num, show (9229 : ℝ) / 12000 = ((9229 : ℝ) / 12000) by norm_num] using int_d_rev_3
        · simpa [show (9229 : ℝ) / 12000 = ((9229 : ℝ) / 12000) by norm_num, show (10470 : ℝ) / 12000 = ((349 : ℝ) / 400) by norm_num] using int_d_rev_2
        · simpa [show (10470 : ℝ) / 12000 = ((349 : ℝ) / 400) by norm_num, show (11418 : ℝ) / 12000 = ((1903 : ℝ) / 2000) by norm_num] using int_d_rev_1
        · simpa [show (11418 : ℝ) / 12000 = ((1903 : ℝ) / 2000) by norm_num, show (12000 : ℝ) / 12000 = (1 : ℝ) by norm_num] using int_d_rev_0
      calc ∑ k : Fin 24, ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1))
          ≤ ∑ k : Fin 24, match k.val with

              | 0 => ((-2889141873829 : ℝ) / 121250000000000)
              | 1 => ((-529036895755227 : ℝ) / 6320000000000000)
              | 2 => ((-12028480828430843 : ℝ) / 74460000000000000)
              | 3 => ((-85908976543236323 : ℝ) / 352560000000000000)
              | 4 => ((-6619382253715963 : ℝ) / 21255000000000000)
              | 5 => ((-109262503707181483 : ℝ) / 309840000000000000)
              | 6 => ((-61095125983937 : ℝ) / 166500000000000)
              | 7 => ((-33381278667113579 : ℝ) / 92280000000000000)
              | 8 => ((-337715839227337 : ℝ) / 973125000000000)
              | 9 => ((-3198824936938881 : ℝ) / 9680000000000000)
              | 10 => ((-159465716548057 : ℝ) / 504000000000000)
              | 11 => ((-36804703940737 : ℝ) / 120000000000000)
              | 23 => ((-2889141873829 : ℝ) / 121250000000000)
              | 22 => ((-529036895755227 : ℝ) / 6320000000000000)
              | 21 => ((-12028480828430843 : ℝ) / 74460000000000000)
              | 20 => ((-85908976543236323 : ℝ) / 352560000000000000)
              | 19 => ((-6619382253715963 : ℝ) / 21255000000000000)
              | 18 => ((-109262503707181483 : ℝ) / 309840000000000000)
              | 17 => ((-61095125983937 : ℝ) / 166500000000000)
              | 16 => ((-33381278667113579 : ℝ) / 92280000000000000)
              | 15 => ((-337715839227337 : ℝ) / 973125000000000)
              | 14 => ((-3198824936938881 : ℝ) / 9680000000000000)
              | 13 => ((-159465716548057 : ℝ) / 504000000000000)
              | 12 => ((-36804703940737 : ℝ) / 120000000000000)
              | _ => 0 := sum_le_sum fun k _ => hterm k
        _ = ((-147809600682664895195852314115805512593 : ℝ) / 23051290904263358923414665937500000000) := by norm_num [Fin.sum_univ_succ]
    have hA_ub : ∑ i : Fin 12, ∑ j : Fin 12, f (A i j) ≤ ((76019120801 : ℝ) / 39062500000) := sum_A_bound
    have hbool : ∑ b : Bool, ∑ k : Fin 24,
        ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1)) ≤ 2 * (((-147809600682664895195852314115805512593 : ℝ) / 23051290904263358923414665937500000000)) := by
      rw [Fintype.sum_bool]
      linarith [hsum_int true, hsum_int false]
    dsimp only [r]
    linarith

end Green97SimkinH3
