import OMAStatements.S_oeis_a380678
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a380678

open OMA.S_oeis_a380678

private lemma zmod2_ps_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

private lemma zmod2_ps_add_self (f : PowerSeries (ZMod 2)) : f + f = 0 := by
  rw [← two_mul, zmod2_ps_two, zero_mul]

private lemma zmod2_ps_sub (f g : PowerSeries (ZMod 2)) : f - g = f + g := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (zmod2_ps_add_self g)]

private lemma zmod2_ps_add_sq (f g : PowerSeries (ZMod 2)) : (f + g) ^ 2 = f ^ 2 + g ^ 2 := by
  calc (f + g) ^ 2 = f ^ 2 + 2 * (f * g) + g ^ 2 := by ring
    _ = f ^ 2 + 0 * (f * g) + g ^ 2 := by rw [zmod2_ps_two]
    _ = f ^ 2 + g ^ 2 := by ring

private lemma coeff_sq_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 2) = if Even n then PowerSeries.coeff (n / 2) f else 0 := by
  rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j f)]
  let t : ℕ → ZMod 2 := fun i => PowerSeries.coeff i f * PowerSeries.coeff (n - i) f
  have hsym : ∀ i ≤ n, t (n - i) = t i := by
    intro i hi; dsimp only [t]; rw [Nat.sub_sub_self hi, mul_comm]
  let L := (Finset.range (n + 1)).filter (fun i => i < n - i)
  let R := (Finset.range (n + 1)).filter (fun i => n - i < i)
  let M := (Finset.range (n + 1)).filter (fun i => i = n - i)
  have hpart : Finset.range (n + 1) = L ∪ (R ∪ M) := by
    ext i; simp only [L, R, M, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hi
      rcases lt_trichotomy i (n - i) with h | h | h
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr (Or.inr ⟨hi, h⟩)
      · exact Or.inr (Or.inl ⟨hi, h⟩)
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  have hd1 : Disjoint L (R ∪ M) := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [L, R, M, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
  have hd2 : Disjoint R M := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [R, M, Finset.mem_filter] at h1 h2; omega
  have hLR : ∑ i ∈ L, t i = ∑ i ∈ R, t i := by
    refine Finset.sum_bij (fun i _ => n - i) ?_ ?_ ?_ ?_
    · intro i hi; simp only [L, R, Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
    · intro i1 h1 i2 h2 heq; simp only [L, Finset.mem_filter, Finset.mem_range] at h1 h2; omega
    · intro j hj; simp only [L, R, Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨n - j, ⟨by omega, by omega⟩, by omega⟩
    · intro i hi; simp only [L, Finset.mem_filter, Finset.mem_range] at hi
      exact (hsym i (by omega)).symm
  change ∑ i ∈ Finset.range (n + 1), t i = _
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2, hLR, ← add_assoc]
  have hadd2 : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [hadd2, zero_add]
  by_cases hev : Even n
  · rw [if_pos hev]
    have hM : M = {n / 2} := by
      ext i; simp only [M, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      rcases hev with ⟨m, rfl⟩; omega
    rw [hM, Finset.sum_singleton]
    dsimp only [t]
    have hsub : n - n / 2 = n / 2 := by rcases hev with ⟨m, rfl⟩; omega
    rw [hsub]
    have hsq : ∀ x : ZMod 2, x * x = x := by decide
    exact hsq _
  · rw [if_neg hev]
    have hM : M = ∅ := by
      ext i; simp only [M, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      rintro ⟨_, heq⟩; exact hev ⟨i, by omega⟩
    rw [hM, Finset.sum_empty]

private def isA027383 (n : ℕ) : Prop :=
  ∃ m : ℕ, n = 3 * 2 ^ m - 2 ∨ n = 4 * 2 ^ m - 2

private noncomputable def F0 : PowerSeries (ZMod 2) :=
  letI := Classical.decPred isA027383
  PowerSeries.mk fun n => if isA027383 n then 1 else 0

private lemma coeff_F0 (n : ℕ) :
    letI := Classical.decPred isA027383
    PowerSeries.coeff n F0 = if isA027383 n then 1 else 0 := by
  classical
  simp [F0]

private lemma F0_const : PowerSeries.constantCoeff F0 = 0 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_F0]
  rw [if_neg]
  rintro ⟨m, h | h⟩
  · have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num); omega
  · have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num); omega

private lemma F0_coeff_one : PowerSeries.coeff 1 F0 = 1 := by
  classical
  rw [coeff_F0, if_pos ⟨0, Or.inl (by norm_num)⟩]

private lemma F0_quad :
    (PowerSeries.X : PowerSeries (ZMod 2)) ^ 2 * F0 ^ 2 + F0 =
      PowerSeries.X + PowerSeries.X ^ 2 := by
  classical
  ext n
  rw [map_add, map_add, PowerSeries.coeff_X_pow_mul', coeff_sq_zmod2, coeff_F0,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  by_cases hn0 : n = 0
  · subst hn0
    simp [F0_const]
  · by_cases hn1 : n = 1
    · subst hn1
      simp [F0_coeff_one]
    · by_cases hn2 : n = 2
      · subst hn2
        have h2 : isA027383 2 := ⟨0, Or.inr (by norm_num)⟩
        have h0 : ¬ isA027383 0 := by
          rintro ⟨m, h | h⟩ <;> have := Nat.one_le_pow m 2 (by norm_num) <;> omega
        rw [if_pos (by norm_num), if_pos (by decide : Even 0), coeff_F0, if_neg h0, if_pos h2]
        decide
      · have hn3 : 3 ≤ n := by omega
        rw [if_pos (by omega), if_neg (by omega : ¬ n = 1), if_neg (by omega : ¬ n = 2), zero_add]
        by_cases hev : Even (n - 2)
        · rw [if_pos hev, coeff_F0]
          have hiff : isA027383 ((n - 2) / 2) ↔ isA027383 n := by
            rcases hev with ⟨k, hk⟩
            have hn_eq : n = 2 * k + 2 := by omega
            have hdiv : (n - 2) / 2 = k := by omega
            rw [hdiv]
            constructor
            · rintro ⟨m, hm | hm⟩
              · refine ⟨m + 1, Or.inl ?_⟩
                have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
                rw [pow_succ']; omega
              · refine ⟨m + 1, Or.inr ?_⟩
                have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
                rw [pow_succ']; omega
            · rintro ⟨m, hm | hm⟩
              · cases m with
                | zero => simp at hm; omega
                | succ m =>
                  refine ⟨m, Or.inl ?_⟩
                  have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
                  rw [pow_succ'] at hm; omega
              · cases m with
                | zero => simp at hm; omega
                | succ m =>
                  refine ⟨m, Or.inr ?_⟩
                  have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
                  rw [pow_succ'] at hm; omega
          by_cases h : isA027383 n
          · rw [if_pos (hiff.mpr h), if_pos h]; decide
          · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]; decide
        · rw [if_neg hev, zero_add]
          have hnot : ¬ isA027383 n := by
            rintro ⟨m, hm | hm⟩
            · cases m with
              | zero => simp at hm; omega
              | succ m =>
                apply hev; refine ⟨3 * 2 ^ m - 2, ?_⟩
                have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
                rw [pow_succ'] at hm; omega
            · cases m with
              | zero => simp at hm; omega
              | succ m =>
                apply hev; refine ⟨4 * 2 ^ m - 2, ?_⟩
                have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
                rw [pow_succ'] at hm; omega
          rw [coeff_F0, if_neg hnot]

private lemma coeff_pow_eq_zero_of_lt {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) {d n : ℕ} (h : n < d) :
    PowerSeries.coeff n (g ^ d) = 0 := by
  have hgX : g = PowerSeries.X * PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) g) := by
    have := PowerSeries.sub_const_eq_X_mul_shift g
    rwa [hg0, map_zero, sub_zero] at this
  rw [hgX, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

private lemma coeff_pow_diag {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) (d : ℕ) :
    PowerSeries.coeff d (g ^ d) = (PowerSeries.coeff 1 g) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (g ^ d) * PowerSeries.coeff j g)]
    rw [Finset.sum_eq_single d]
    · rw [ih, Nat.add_sub_cancel_left, pow_succ]
    · intro k hk hne
      have hklt : k ≤ d + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [coeff_pow_eq_zero_of_lt hg0 hlt, zero_mul]
      · have hk_eq : k = d + 1 := by omega
        rw [hk_eq, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, hg0, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma coeff_pow_congr {R : Type*} [CommRing R] {u v : PowerSeries R} {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff k u = PowerSeries.coeff k v) (d : ℕ) :
    ∀ k ≤ n, PowerSeries.coeff k (u ^ d) = PowerSeries.coeff k (v ^ d) := by
  induction d with
  | zero => intro k _; simp
  | succ d ih =>
    intro k hk
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij
    rw [ih i (by omega), h j (by omega)]

private lemma coeff_subst_eq_sum {R : Type*} [CommRing R] {f g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst g f) =
      ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) := by
  have hSub : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero hg0
  rw [PowerSeries.coeff_subst' hSub]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support, ne_eq] at hd
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hge
  exact hd (by rw [coeff_pow_eq_zero_of_lt hg0 (by omega), mul_zero])

private lemma subst_quad_unique {v Y1 Y2 : PowerSeries (ZMod 2)}
    (hv0 : PowerSeries.constantCoeff v = 0)
    (h1 : v ^ 2 * Y1 ^ 2 + Y1 = v + v ^ 2)
    (h2 : v ^ 2 * Y2 ^ 2 + Y2 = v + v ^ 2) : Y1 = Y2 := by
  have hdiff : Y1 + Y2 = v ^ 2 * (Y1 + Y2) ^ 2 := by
    have hadd : (v ^ 2 * Y1 ^ 2 + Y1) + (v ^ 2 * Y2 ^ 2 + Y2) = (v + v ^ 2) + (v + v ^ 2) := by
      rw [h1, h2]
    rw [zmod2_ps_add_self] at hadd
    have hlhs : (v ^ 2 * Y1 ^ 2 + Y1) + (v ^ 2 * Y2 ^ 2 + Y2) =
        (Y1 + Y2) + v ^ 2 * (Y1 + Y2) ^ 2 := by
      rw [zmod2_ps_add_sq]; ring
    rw [hlhs] at hadd
    have := congrArg (· + v ^ 2 * (Y1 + Y2) ^ 2) hadd
    rw [add_assoc, zmod2_ps_add_self, add_zero, zero_add] at this
    exact this
  have hzero : ∀ n, PowerSeries.coeff n (Y1 + Y2) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hc := congrArg (PowerSeries.coeff n) hdiff
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (v ^ 2) * PowerSeries.coeff j ((Y1 + Y2) ^ 2))] at hc
      rw [hc]
      apply Finset.sum_eq_zero
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hi2 : i < 2
      · rw [coeff_pow_eq_zero_of_lt hv0 hi2, zero_mul]
      · conv_lhs => arg 2; rw [coeff_sq_zmod2]
        split_ifs with hev
        · have hlt : (n - i) / 2 < n := by omega
          rw [ih ((n - i) / 2) hlt, mul_zero]
        · rw [mul_zero]
  ext n
  have h0 := hzero n
  rw [map_add] at h0
  have heq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact heq _ _ h0

private lemma F0_subst_v :
    ∃ v : PowerSeries (ZMod 2),
      PowerSeries.constantCoeff v = 0 ∧
      (1 + F0 ^ 2) * v = (1 + F0 ^ 2) * PowerSeries.X + F0 ^ 2 ∧
      PowerSeries.subst v F0 = PowerSeries.X := by
  have hu : IsUnit (1 + F0 ^ 2) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp [map_add, map_pow, F0_const]
  let v : PowerSeries (ZMod 2) := PowerSeries.X + F0 ^ 2 * Ring.inverse (1 + F0 ^ 2)
  have hv_eq : (1 + F0 ^ 2) * v = (1 + F0 ^ 2) * PowerSeries.X + F0 ^ 2 := by
    dsimp only [v]
    rw [mul_add, ← mul_assoc, mul_comm (1 + F0 ^ 2) (F0 ^ 2), mul_assoc,
      Ring.mul_inverse_cancel _ hu, mul_one]
  have hv0 : PowerSeries.constantCoeff v = 0 := by
    dsimp only [v]
    simp [map_add, map_mul, map_pow, F0_const]
  have hSub : PowerSeries.HasSubst v := PowerSeries.HasSubst.of_constantCoeff_zero hv0
  have hX_sol : v ^ 2 * (PowerSeries.X : PowerSeries (ZMod 2)) ^ 2 + PowerSeries.X = v + v ^ 2 := by
    set X2 : PowerSeries (ZMod 2) := PowerSeries.X
    have hmul_zero : (1 + F0 ^ 2) ^ 2 * (v ^ 2 * (1 + X2 ^ 2) + v + X2) = 0 := by
      have h1 : (1 + F0 ^ 2) ^ 2 * (v ^ 2 * (1 + X2 ^ 2) + v + X2) =
          ((1 + F0 ^ 2) * v) ^ 2 * (1 + X2 ^ 2) + (1 + F0 ^ 2) * ((1 + F0 ^ 2) * v) +
            (1 + F0 ^ 2) ^ 2 * X2 := by ring
      rw [h1, hv_eq]
      have hsq1 : ((1 + F0 ^ 2) * X2 + F0 ^ 2) ^ 2 = (1 + F0 ^ 4) * X2 ^ 2 + F0 ^ 4 := by
        rw [zmod2_ps_add_sq, mul_pow, zmod2_ps_add_sq, one_pow]; ring
      have hsq2 : (1 + F0 ^ 2) ^ 2 = 1 + F0 ^ 4 := by
        rw [zmod2_ps_add_sq, one_pow]; ring
      rw [hsq1, hsq2]
      have hexp : ((1 + F0 ^ 4) * X2 ^ 2 + F0 ^ 4) * (1 + X2 ^ 2) +
          (1 + F0 ^ 2) * ((1 + F0 ^ 2) * X2 + F0 ^ 2) + (1 + F0 ^ 4) * X2 =
          (X2 ^ 2 * F0 ^ 2 + F0 + X2 + X2 ^ 2) ^ 2 := by
        have hsq_rhs : (X2 ^ 2 * F0 ^ 2 + F0 + X2 + X2 ^ 2) ^ 2 =
            X2 ^ 4 * F0 ^ 4 + F0 ^ 2 + X2 ^ 2 + X2 ^ 4 := by
          rw [zmod2_ps_add_sq, zmod2_ps_add_sq, zmod2_ps_add_sq]; ring
        rw [hsq_rhs]
        have hz1 : X2 ^ 2 * F0 ^ 4 + X2 ^ 2 * F0 ^ 4 = 0 := zmod2_ps_add_self _
        have hz2 : F0 ^ 4 + F0 ^ 4 = 0 := zmod2_ps_add_self _
        have hz3 : X2 + X2 = 0 := zmod2_ps_add_self _
        have hz4 : F0 ^ 4 * X2 + F0 ^ 4 * X2 = 0 := zmod2_ps_add_self _
        have hz5 : F0 ^ 2 * X2 + F0 ^ 2 * X2 = 0 := zmod2_ps_add_self _
        calc ((1 + F0 ^ 4) * X2 ^ 2 + F0 ^ 4) * (1 + X2 ^ 2) +
              (1 + F0 ^ 2) * ((1 + F0 ^ 2) * X2 + F0 ^ 2) + (1 + F0 ^ 4) * X2
            = X2 ^ 4 * F0 ^ 4 + F0 ^ 2 + X2 ^ 2 + X2 ^ 4 +
              (X2 ^ 2 * F0 ^ 4 + X2 ^ 2 * F0 ^ 4) + (F0 ^ 4 + F0 ^ 4) +
              (X2 + X2) + (F0 ^ 4 * X2 + F0 ^ 4 * X2) + (F0 ^ 2 * X2 + F0 ^ 2 * X2) := by ring
          _ = X2 ^ 4 * F0 ^ 4 + F0 ^ 2 + X2 ^ 2 + X2 ^ 4 := by
              rw [hz1, hz2, hz3, hz4, hz5]; ring
      rw [hexp, F0_quad]
      have : (X2 + X2 ^ 2) + X2 + X2 ^ 2 = (X2 + X2) + (X2 ^ 2 + X2 ^ 2) := by ring
      rw [this, zmod2_ps_add_self, zmod2_ps_add_self, add_zero, zero_pow (by norm_num)]
    have hu2 : IsUnit ((1 + F0 ^ 2) ^ 2) := hu.pow 2
    have hzero : v ^ 2 * (1 + X2 ^ 2) + v + X2 = 0 := (IsUnit.mul_right_eq_zero hu2).mp hmul_zero
    have hsplit : v ^ 2 * (1 + X2 ^ 2) + v + X2 = (v ^ 2 * X2 ^ 2 + X2) + (v + v ^ 2) := by ring
    rw [hsplit] at hzero
    have := congrArg (· + (v + v ^ 2)) hzero
    rw [add_assoc, zmod2_ps_add_self, add_zero, zero_add] at this
    exact this
  have hF_sol : v ^ 2 * (PowerSeries.subst v F0) ^ 2 + PowerSeries.subst v F0 = v + v ^ 2 := by
    have hs := congrArg (PowerSeries.subst v) F0_quad
    simp only [PowerSeries.subst_add hSub, PowerSeries.subst_mul hSub, PowerSeries.subst_pow hSub,
      PowerSeries.subst_X hSub] at hs
    exact hs
  exact ⟨v, hv0, hv_eq, subst_quad_unique hv0 hF_sol hX_sol⟩

private lemma mod2_unique (a2 u2 : PowerSeries (ZMod 2))
    (ha0 : PowerSeries.constantCoeff a2 = 0)
    (ha1 : PowerSeries.coeff 1 a2 = 1)
    (hu0 : PowerSeries.constantCoeff u2 = 0)
    (hu_eq : (1 + a2 ^ 2) * u2 = (1 + a2 ^ 2) * PowerSeries.X + a2 ^ 2)
    (hsubst : PowerSeries.subst u2 a2 = PowerSeries.X) : a2 = F0 := by
  obtain ⟨v, hv0, hv_eq, hv_subst⟩ := F0_subst_v
  have hu1 : PowerSeries.coeff 1 u2 = 1 := by
    have hc := congrArg (PowerSeries.coeff 1) hu_eq
    rw [map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul] at hc
    simp only [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      map_add, PowerSeries.coeff_one, PowerSeries.coeff_X, coeff_sq_zmod2] at hc
    have h0a : PowerSeries.coeff 0 a2 = 0 := by rwa [PowerSeries.coeff_zero_eq_constantCoeff]
    have h0u : PowerSeries.coeff 0 u2 = 0 := by rwa [PowerSeries.coeff_zero_eq_constantCoeff]
    simpa [h0a, h0u] using hc
  have hv1 : PowerSeries.coeff 1 v = 1 := by
    have hc := congrArg (PowerSeries.coeff 1) hv_eq
    rw [map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul] at hc
    simp only [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      map_add, PowerSeries.coeff_one, PowerSeries.coeff_X, coeff_sq_zmod2] at hc
    have h0f : PowerSeries.coeff 0 F0 = 0 := by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact F0_const
    have h0v : PowerSeries.coeff 0 v = 0 := by rwa [PowerSeries.coeff_zero_eq_constantCoeff]
    simpa [h0f, h0v] using hc
  have hcoeff : ∀ n, PowerSeries.coeff n a2 = PowerSeries.coeff n F0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | n'
      · rw [PowerSeries.coeff_zero_eq_constantCoeff, ha0, F0_const]
      · rw [ha1, F0_coeff_one]
      · set m := n' + 2
        -- First show a2^2 and F0^2 agree on all k ≤ m (since k / 2 < m for k ≤ m when m ≥ 2!)
        have hsq_eq : ∀ k ≤ m, PowerSeries.coeff k (a2 ^ 2) = PowerSeries.coeff k (F0 ^ 2) := by
          intro k hk
          rw [coeff_sq_zmod2, coeff_sq_zmod2]
          split_ifs
          · exact ih (k / 2) (by omega)
          · rfl
        -- Next show u2 and v agree on all k ≤ m!
        have huv : ∀ k ≤ m, PowerSeries.coeff k u2 = PowerSeries.coeff k v := by
          intro k
          induction k using Nat.strong_induction_on with
          | h k ihk =>
            intro hk
            have hc1 := congrArg (PowerSeries.coeff k) hu_eq
            have hc2 := congrArg (PowerSeries.coeff k) hv_eq
            -- Compare RHSs:
            have hrhs : PowerSeries.coeff k ((1 + a2 ^ 2) * PowerSeries.X + a2 ^ 2) =
                PowerSeries.coeff k ((1 + F0 ^ 2) * PowerSeries.X + F0 ^ 2) := by
              rw [map_add, map_add, hsq_eq k hk]
              congr 1
              rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
              apply Finset.sum_congr rfl
              intro ⟨i, j⟩ hij
              rw [Finset.mem_antidiagonal] at hij
              rw [map_add, map_add, hsq_eq i (by omega)]
            rw [hrhs, ← hc2] at hc1
            rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul] at hc1
            conv_lhs at hc1 => rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i (1 + a2 ^ 2) * PowerSeries.coeff j u2), Finset.sum_range_succ']
            conv_rhs at hc1 => rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i (1 + F0 ^ 2) * PowerSeries.coeff j v), Finset.sum_range_succ']
            have htail : ∑ i ∈ Finset.range k,
                PowerSeries.coeff (i + 1) (1 + a2 ^ 2) * PowerSeries.coeff (k - (i + 1)) u2 =
                ∑ i ∈ Finset.range k,
                PowerSeries.coeff (i + 1) (1 + F0 ^ 2) * PowerSeries.coeff (k - (i + 1)) v := by
              apply Finset.sum_congr rfl
              intro i hi
              have hik : i < k := Finset.mem_range.mp hi
              rw [map_add, map_add, hsq_eq (i + 1) (by omega), ihk (k - (i + 1)) (by omega) (by omega)]
            rw [htail] at hc1
            have h0c1 : PowerSeries.coeff 0 (1 + a2 ^ 2) = 1 := by
              rw [PowerSeries.coeff_zero_eq_constantCoeff]; simp [map_add, map_pow, ha0]
            have h0c2 : PowerSeries.coeff 0 (1 + F0 ^ 2) = 1 := by
              rw [PowerSeries.coeff_zero_eq_constantCoeff]; simp [map_add, map_pow, F0_const]
            simp only [Nat.sub_zero, h0c1, h0c2, one_mul] at hc1
            exact add_left_cancel hc1
        -- Now compare coeff m (a2.subst u2) = coeff m X = coeff m (F0.subst v)!
        have hs1 := congrArg (PowerSeries.coeff m) hsubst
        have hs2 := congrArg (PowerSeries.coeff m) hv_subst
        rw [← hs2, coeff_subst_eq_sum hu0, coeff_subst_eq_sum hv0] at hs1
        conv_lhs at hs1 => rw [Finset.sum_range_succ]
        conv_rhs at hs1 => rw [Finset.sum_range_succ]
        have hlow : ∑ d ∈ Finset.range m, PowerSeries.coeff d a2 * PowerSeries.coeff m (u2 ^ d) =
            ∑ d ∈ Finset.range m, PowerSeries.coeff d F0 * PowerSeries.coeff m (v ^ d) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdm : d < m := Finset.mem_range.mp hd
          rw [ih d hdm, coeff_pow_congr huv d m le_rfl]
        rw [hlow, coeff_pow_diag hu0 m, coeff_pow_diag hv0 m, hu1, hv1, one_pow, mul_one, mul_one] at hs1
        exact add_left_cancel hs1
  ext n
  exact hcoeff n

private lemma map_subst_mod2 {f g : PowerSeries ℤ} (hg0 : PowerSeries.constantCoeff g = 0) :
    let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
    PowerSeries.subst (φ g) (φ f) = φ (PowerSeries.subst g f) := by
  intro φ
  have hφg0 : PowerSeries.constantCoeff (φ g) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hg0, map_zero]
  ext n
  rw [coeff_subst_eq_sum hφg0, PowerSeries.coeff_map, coeff_subst_eq_sum hg0, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_mul, PowerSeries.coeff_map, ← map_pow φ, PowerSeries.coeff_map]

private lemma odd_iff_zmod2_eq_one (z : ℤ) : Odd z ↔ (z : ZMod 2) = 1 := by
  constructor
  · rintro ⟨k, rfl⟩; push_cast; have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add]
  · intro h
    rcases Int.even_or_odd z with ⟨k, rfl⟩ | hodd
    · push_cast at h
      have h2 : (k : ZMod 2) + (k : ZMod 2) = 0 := by
        generalize (k : ZMod 2) = x; revert x; decide
      rw [h2] at h; exact absurd h (by decide)
    · exact hodd

private theorem prove_main : type_of% @OMA.S_oeis_a380678.main := by
  classical
  intro A hA0 hA1 hEq
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  let u := PowerSeries.X - A ^ 2 * Ring.inverse ((1 - A ^ 2))
  have hu_unit : IsUnit ((1 - A ^ 2)) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp [map_pow, map_sub, hA0]
  have hu_rel : (1 - A ^ 2) * u = (1 - A ^ 2) * PowerSeries.X - A ^ 2 := by
    dsimp only [u]
    rw [mul_sub, ← mul_assoc, mul_comm ((1 - A ^ 2)) (A ^ 2), mul_assoc,
      Ring.mul_inverse_cancel _ hu_unit, mul_one]
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    dsimp only [u]
    simp [map_sub, map_mul, map_pow, hA0]
  have hφA0 : PowerSeries.constantCoeff (φ A) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_zero]
  have hφA1 : PowerSeries.coeff 1 (φ A) = 1 := by
    rw [PowerSeries.coeff_map, hA1, map_one]
  have hφu0 : PowerSeries.constantCoeff (φ u) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hu0, map_zero]
  have hφu_rel : (1 + (φ A) ^ 2) * φ u = (1 + (φ A) ^ 2) * PowerSeries.X + (φ A) ^ 2 := by
    have hm := congrArg φ hu_rel
    conv_lhs at hm => rw [map_mul, map_sub, map_one, map_pow, zmod2_ps_sub]
    conv_rhs at hm => rw [map_sub, map_mul, map_sub, map_one, map_pow, PowerSeries.map_X, zmod2_ps_sub, zmod2_ps_sub]
    exact hm
  have hφsubst : PowerSeries.subst (φ u) (φ A) = PowerSeries.X := by
    rw [map_subst_mod2 hu0, hEq, PowerSeries.map_X]
  have ha2_eq : φ A = F0 := mod2_unique (φ A) (φ u) hφA0 hφA1 hφu0 hφu_rel hφsubst
  intro n _
  rw [odd_iff_zmod2_eq_one]
  have hc : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = PowerSeries.coeff n F0 := by
    rw [← ha2_eq, PowerSeries.coeff_map]; rfl
  rw [hc, coeff_F0]
  unfold isA027383
  by_cases h : ∃ m : ℕ, n = 3 * 2 ^ m - 2 ∨ n = 4 * 2 ^ m - 2
  · simp [h]
  · simp [h]

end OMA.P_oeis_a380678

theorem OMA.solution : type_of% @OMA.S_oeis_a380678.main :=
  OMA.P_oeis_a380678.prove_main
