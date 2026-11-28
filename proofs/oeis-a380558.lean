import OMAStatements.S_oeis_a380558
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a380558

open OMA.S_oeis_a380558

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

private lemma isNoLeading10_zero : ¬ isNoLeading10 0 := by
  rintro (h | ⟨k, h1, _⟩)
  · omega
  · have := Nat.one_le_pow k 2 (by norm_num); omega

private lemma isNoLeading10_one : isNoLeading10 1 := Or.inl rfl

private lemma isNoLeading10_two : ¬ isNoLeading10 2 := by
  rintro (h | ⟨k, h1, _⟩)
  · omega
  · have := Nat.one_le_pow k 2 (by norm_num); omega

private lemma isNoLeading10_iff_div2 {m : ℕ} (hm : 3 ≤ m) :
    isNoLeading10 m ↔ isNoLeading10 (m / 2) := by
  by_cases hm3 : m = 3
  · subst hm3
    constructor
    · intro _; exact Or.inl rfl
    · intro _; exact Or.inr ⟨0, by norm_num, by norm_num⟩
  · have hm4 : 4 ≤ m := by omega
    have hne1 : m ≠ 1 := by omega
    have hdiv_ne1 : m / 2 ≠ 1 := by omega
    constructor
    · rintro (h | ⟨k, h1, h2⟩)
      · exact absurd h hne1
      · cases k with
        | zero => simp at h2; omega
        | succ k =>
          refine Or.inr ⟨k, ?_, ?_⟩
          · rw [pow_succ'] at h1; omega
          · rw [pow_succ'] at h2; omega
    · rintro (h | ⟨k, h1, h2⟩)
      · exact absurd h hdiv_ne1
      · refine Or.inr ⟨k + 1, ?_, ?_⟩
        · rw [pow_succ']; omega
        · rw [pow_succ']; omega

private noncomputable def B0 : PowerSeries (ZMod 2) :=
  letI := Classical.decPred isNoLeading10
  PowerSeries.mk fun m => if isNoLeading10 m then 1 else 0

private lemma coeff_B0 (m : ℕ) :
    letI := Classical.decPred isNoLeading10
    PowerSeries.coeff m B0 = if isNoLeading10 m then 1 else 0 := by
  classical
  simp [B0]

private lemma B0_const : PowerSeries.constantCoeff B0 = 0 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_B0, if_neg isNoLeading10_zero]

private lemma B0_quad :
    (1 + (PowerSeries.X : PowerSeries (ZMod 2))) * B0 ^ 2 + B0 =
      PowerSeries.X + PowerSeries.X ^ 2 := by
  classical
  ext n
  rw [add_mul, one_mul, map_add, map_add, map_add]
  have hXmul : PowerSeries.coeff n ((PowerSeries.X : PowerSeries (ZMod 2)) * B0 ^ 2) = if 1 ≤ n then PowerSeries.coeff (n - 1) (B0 ^ 2) else 0 := by
    rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul']
  rw [hXmul,
    coeff_sq_zmod2, coeff_sq_zmod2, coeff_B0, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  by_cases hn0 : n = 0
  · subst hn0
    simp only [coeff_B0, isNoLeading10_zero, show Even 0 by decide, ↓reduceIte, Nat.zero_div,
      show ¬ (1 ≤ 0) by omega, show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ 2 by omega]
    decide
  · by_cases hn1 : n = 1
    · subst hn1
      simp only [coeff_B0, isNoLeading10_zero, isNoLeading10_one, show ¬ Even 1 by decide,
        show Even 0 by decide, ↓reduceIte, Nat.sub_self, Nat.zero_div,
        show (1 : ℕ) ≤ 1 by omega, show (1 : ℕ) ≠ 2 by omega]
      decide
    · by_cases hn2 : n = 2
      · subst hn2
        simp only [coeff_B0, isNoLeading10_one, isNoLeading10_two, show Even 2 by decide,
          show ¬ Even 1 by decide, ↓reduceIte, show (2 : ℕ) / 2 = 1 by decide,
          show (2 : ℕ) - 1 = 1 by decide, show (1 : ℕ) ≤ 2 by omega, show (2 : ℕ) ≠ 1 by omega]
        decide
      · have hn3 : 3 ≤ n := by omega
        have hn_ge1 : 1 ≤ n := by omega
        have hne1 : n ≠ 1 := by omega
        have hne2 : n ≠ 2 := by omega
        simp only [hn_ge1, hne1, hne2, ↓reduceIte, zero_add]
        by_cases hev : Even n
        · have hodd : ¬ Even (n - 1) := by rcases hev with ⟨k, rfl⟩; intro ⟨j, hj⟩; omega
          simp only [hev, hodd, ↓reduceIte, add_zero, coeff_B0]
          by_cases h : isNoLeading10 n
          · rw [if_pos ((isNoLeading10_iff_div2 hn3).mp h), if_pos h]; decide
          · rw [if_neg (fun h' => h ((isNoLeading10_iff_div2 hn3).mpr h')), if_neg h]; decide
        · have hev1 : Even (n - 1) := by
            rcases Nat.even_or_odd n with h | ⟨k, rfl⟩
            · exact absurd h hev
            · exact ⟨k, by omega⟩
          have hdiv : (n - 1) / 2 = n / 2 := by
            rcases Nat.even_or_odd n with h | ⟨k, rfl⟩
            · exact absurd h hev
            · omega
          simp only [hev, hev1, ↓reduceIte, zero_add, coeff_B0, hdiv]
          by_cases h : isNoLeading10 n
          · rw [if_pos ((isNoLeading10_iff_div2 hn3).mp h), if_pos h]; decide
          · rw [if_neg (fun h' => h ((isNoLeading10_iff_div2 hn3).mpr h')), if_neg h]; decide

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

private lemma quad_sol_unique {u Y1 Y2 : PowerSeries (ZMod 2)}
    (hY0 : PowerSeries.constantCoeff (Y1 + Y2) = 0)
    (h1 : (1 + u) * Y1 ^ 2 + Y1 = u + u ^ 2)
    (h2 : (1 + u) * Y2 ^ 2 + Y2 = u + u ^ 2) : Y1 = Y2 := by
  have hdiff : Y1 + Y2 = (1 + u) * (Y1 + Y2) ^ 2 := by
    have hadd : ((1 + u) * Y1 ^ 2 + Y1) + ((1 + u) * Y2 ^ 2 + Y2) = (u + u ^ 2) + (u + u ^ 2) := by
      rw [h1, h2]
    rw [zmod2_ps_add_self] at hadd
    have hlhs : ((1 + u) * Y1 ^ 2 + Y1) + ((1 + u) * Y2 ^ 2 + Y2) =
        (Y1 + Y2) + (1 + u) * (Y1 + Y2) ^ 2 := by
      rw [zmod2_ps_add_sq]; ring
    rw [hlhs] at hadd
    have := congrArg (· + (1 + u) * (Y1 + Y2) ^ 2) hadd
    rw [add_assoc, zmod2_ps_add_self, add_zero, zero_add] at this
    exact this
  have hzero : ∀ n, PowerSeries.coeff n (Y1 + Y2) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => rwa [PowerSeries.coeff_zero_eq_constantCoeff]
      | succ m =>
        have hc := congrArg (PowerSeries.coeff (m + 1)) hdiff
        rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (1 + u) * PowerSeries.coeff j ((Y1 + Y2) ^ 2))] at hc
        rw [hc]
        apply Finset.sum_eq_zero
        intro i hi
        have him : i ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [coeff_sq_zmod2]
        split_ifs with hev
        · have hlt : (m + 1 - i) / 2 < m + 1 := by omega
          rw [ih ((m + 1 - i) / 2) hlt, mul_zero]
        · rw [mul_zero]
  ext n
  have h0 := hzero n
  rw [map_add] at h0
  have heq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact heq _ _ h0

private lemma B0_subst_eq :
    let u : PowerSeries (ZMod 2) := PowerSeries.X + B0 ^ 2
    (1 + PowerSeries.X) * PowerSeries.subst u B0 = PowerSeries.X := by
  intro u
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    dsimp only [u]; simp [map_add, map_pow, B0_const]
  have hSub : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu0
  have h1X_unit : IsUnit (1 + (PowerSeries.X : PowerSeries (ZMod 2))) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp
  let Y2 : PowerSeries (ZMod 2) := PowerSeries.X * Ring.inverse (1 + PowerSeries.X)
  have hY2_mul : (1 + PowerSeries.X) * Y2 = PowerSeries.X := by
    dsimp only [Y2]
    rw [← mul_assoc, mul_comm (1 + PowerSeries.X) PowerSeries.X, mul_assoc,
      Ring.mul_inverse_cancel _ h1X_unit, mul_one]
  have hY2_0 : PowerSeries.constantCoeff Y2 = 0 := by
    dsimp only [Y2]; simp [map_mul]
  have hB_sol : (1 + u) * (PowerSeries.subst u B0) ^ 2 + PowerSeries.subst u B0 = u + u ^ 2 := by
    have hs := congrArg (PowerSeries.subst u) B0_quad
    have h1s : PowerSeries.subst u (1 : PowerSeries (ZMod 2)) = 1 := by
      change PowerSeries.subst u (PowerSeries.C 1) = 1; rw [PowerSeries.subst_C]; rfl
    simp only [PowerSeries.subst_add hSub, PowerSeries.subst_mul hSub, PowerSeries.subst_pow hSub,
      PowerSeries.subst_X hSub, h1s] at hs
    exact hs
  have hY2_sol : (1 + u) * Y2 ^ 2 + Y2 = u + u ^ 2 := by
    set X2 : PowerSeries (ZMod 2) := PowerSeries.X
    have hmul : (1 + X2) ^ 2 * ((1 + u) * Y2 ^ 2 + Y2) = (1 + X2) ^ 2 * (u + u ^ 2) := by
      have hsqX : (1 + X2) ^ 2 = 1 + X2 ^ 2 := by rw [zmod2_ps_add_sq, one_pow]
      have hlhs : (1 + X2) ^ 2 * ((1 + u) * Y2 ^ 2 + Y2) =
          (1 + u) * ((1 + X2) * Y2) ^ 2 + (1 + X2) * ((1 + X2) * Y2) := by ring
      rw [hlhs, hY2_mul]
      have hlhs2 : (1 + u) * X2 ^ 2 + (1 + X2) * X2 = X2 + X2 ^ 3 + X2 ^ 2 * B0 ^ 2 := by
        dsimp only [u]
        have hx2 : X2 ^ 2 + X2 ^ 2 = 0 := zmod2_ps_add_self _
        calc (1 + (X2 + B0 ^ 2)) * X2 ^ 2 + (1 + X2) * X2
            = X2 + (X2 ^ 2 + X2 ^ 2) + X2 ^ 3 + X2 ^ 2 * B0 ^ 2 := by ring
          _ = X2 + 0 + X2 ^ 3 + X2 ^ 2 * B0 ^ 2 := by rw [hx2]
          _ = X2 + X2 ^ 3 + X2 ^ 2 * B0 ^ 2 := by ring
      rw [hlhs2, hsqX]
      have hu_sq : u ^ 2 = X2 ^ 2 + B0 ^ 4 := by dsimp only [u]; rw [zmod2_ps_add_sq]; ring
      have hB4 : (1 + X2 ^ 2) * B0 ^ 4 = B0 ^ 2 + X2 ^ 2 + X2 ^ 4 := by
        have hq := congrArg (· ^ 2) B0_quad
        rw [zmod2_ps_add_sq, mul_pow, zmod2_ps_add_sq, one_pow, zmod2_ps_add_sq] at hq
        have := congrArg (· + B0 ^ 2) hq
        rw [add_assoc, zmod2_ps_add_self, add_zero] at this
        calc (1 + X2 ^ 2) * B0 ^ 4 = (1 + X2 ^ 2) * (B0 ^ 2) ^ 2 := by ring
          _ = X2 ^ 2 + (X2 ^ 2) ^ 2 + B0 ^ 2 := this
          _ = B0 ^ 2 + X2 ^ 2 + X2 ^ 4 := by ring
      rw [hu_sq]
      dsimp only [u]
      have hb2_z : B0 ^ 2 + B0 ^ 2 = 0 := zmod2_ps_add_self _
      have hx2_z : X2 ^ 2 + X2 ^ 2 = 0 := zmod2_ps_add_self _
      have hx4_z : X2 ^ 4 + X2 ^ 4 = 0 := zmod2_ps_add_self _
      calc X2 + X2 ^ 3 + X2 ^ 2 * B0 ^ 2
          = X2 + X2 ^ 3 + X2 ^ 2 * B0 ^ 2 + (B0 ^ 2 + B0 ^ 2) + (X2 ^ 2 + X2 ^ 2) + (X2 ^ 4 + X2 ^ 4) := by
            rw [hb2_z, hx2_z, hx4_z]; ring
        _ = (1 + X2 ^ 2) * (X2 + B0 ^ 2 + X2 ^ 2) + (B0 ^ 2 + X2 ^ 2 + X2 ^ 4) := by ring
        _ = (1 + X2 ^ 2) * (X2 + B0 ^ 2 + X2 ^ 2) + (1 + X2 ^ 2) * B0 ^ 4 := by rw [← hB4]
        _ = (1 + X2 ^ 2) * (X2 + B0 ^ 2 + (X2 ^ 2 + B0 ^ 4)) := by ring
    exact (h1X_unit.pow 2).mul_left_cancel hmul
  have hY0 : PowerSeries.constantCoeff (PowerSeries.subst u B0 + Y2) = 0 := by
    rw [map_add, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_subst_eq_sum hu0]
    simp [PowerSeries.coeff_zero_eq_constantCoeff, B0_const, hY2_0]
  have heq : PowerSeries.subst u B0 = Y2 := quad_sol_unique hY0 hB_sol hY2_sol
  rw [heq, hY2_mul]

private lemma subst_comp_X_sq (f g : PowerSeries (ZMod 2))
    (hg0 : PowerSeries.constantCoeff g = 0) :
    PowerSeries.subst g (PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) f) =
      PowerSeries.subst (g ^ 2) f := by
  have hX2_0 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (by decide)]
  ext n
  rw [coeff_subst_eq_sum hg0, coeff_subst_eq_sum (by rw [map_pow, hg0, zero_pow (by decide)])]
  have hX2_coeff : ∀ d, PowerSeries.coeff d (PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) f) =
      if Even d then PowerSeries.coeff (d / 2) f else 0 := by
    intro d; rw [coeff_subst_eq_sum hX2_0]
    by_cases hev : Even d
    · rw [if_pos hev]; rcases hev with ⟨m, rfl⟩
      rw [Finset.sum_eq_single m]
      · rw [show m + m = 2 * m by omega, show 2 * m / 2 = m by omega, ← pow_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
      · intro k _ hk; rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · rw [if_neg hev]; refine Finset.sum_eq_zero fun k _ => ?_
      rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg (fun h => hev ⟨k, by omega⟩), mul_zero]
  simp_rw [hX2_coeff]
  refine Finset.sum_bij_ne_zero (fun d _ _ => d / 2) ?_ ?_ ?_ ?_
  · intro d hd _; rw [Finset.mem_range] at hd ⊢; omega
  · intro d1 _ h1 d2 _ h2 heq
    have he1 : Even d1 := by by_contra hc; simp [hc] at h1
    have he2 : Even d2 := by by_contra hc; simp [hc] at h2
    rcases he1 with ⟨a, rfl⟩; rcases he2 with ⟨b, rfl⟩; omega
  · intro m hm hne
    rw [Finset.mem_range] at hm
    have h2m : 2 * m ≤ n := by
      by_contra hgt
      have h0 : PowerSeries.coeff n ((g ^ 2) ^ m) = 0 := by
        rw [← pow_mul]; exact coeff_pow_eq_zero_of_lt hg0 (by omega)
      exact hne (by rw [h0, mul_zero])
    refine ⟨2 * m, Finset.mem_range.mpr (by omega), ?_, by omega⟩
    rw [if_pos ⟨m, by omega⟩, show 2 * m / 2 = m by omega, pow_mul]; exact hne
  · intro d _ hne
    have he : Even d := by by_contra hc; simp [hc] at hne
    rw [if_pos he, ← pow_mul]; rcases he with ⟨m, rfl⟩; rw [show m + m = 2 * m by omega, show 2 * m / 2 = m by omega]

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

private theorem prove_main : type_of% @OMA.S_oeis_a380558.main := by
  classical
  intro A hA0 hA1 hEq
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  set a2 : PowerSeries (ZMod 2) := φ A
  have ha2_0 : PowerSeries.constantCoeff a2 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_zero]
  have ha2_1 : PowerSeries.coeff 1 a2 = 0 := by
    rw [PowerSeries.coeff_map, hA1, map_zero]
  have hXA0 : PowerSeries.constantCoeff (PowerSeries.X - A) = 0 := by
    simp [map_sub, hA0]
  have ha2_eq : (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) *
      PowerSeries.subst (PowerSeries.X + a2) a2 = PowerSeries.X ^ 2 := by
    have hm := congrArg φ hEq
    rw [map_mul, map_sub, map_one, map_pow, PowerSeries.map_X, zmod2_ps_sub,
      ← map_subst_mod2 hXA0] at hm
    have harg : φ (PowerSeries.X - A) = PowerSeries.X + a2 := by
      rw [map_sub, PowerSeries.map_X, zmod2_ps_sub]
    rwa [harg] at hm
  -- Define F0 = B0(X^2) and prove F0 satisfies the same equation!
  set F0 : PowerSeries (ZMod 2) := PowerSeries.subst (PowerSeries.X ^ 2) B0
  have hX2_0 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) = 0 := by simp
  have hF0_coeff : ∀ n, PowerSeries.coeff n F0 =
      if Even n then PowerSeries.coeff (n / 2) B0 else 0 := by
    intro n
    rw [coeff_subst_eq_sum hX2_0]
    by_cases hev : Even n
    · rw [if_pos hev]
      rcases hev with ⟨m, rfl⟩
      rw [Finset.sum_eq_single m]
      · rw [show m + m = 2 * m by omega, show 2 * m / 2 = m by omega, ← pow_mul,
          PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
      · intro d _ hne
        rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · rw [if_neg hev]
      apply Finset.sum_eq_zero
      intro d _
      rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg (fun h => hev ⟨d, by omega⟩), mul_zero]
  have hF0_0 : PowerSeries.constantCoeff F0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hF0_coeff, if_pos (by decide : Even 0)]
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using B0_const
  have hF0_1 : PowerSeries.coeff 1 F0 = 0 := by
    rw [hF0_coeff, if_neg (by decide : ¬ Even 1)]
  have hF0_eq : (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) *
      PowerSeries.subst (PowerSeries.X + F0) F0 = PowerSeries.X ^ 2 := by
    have hXF0 : PowerSeries.constantCoeff (PowerSeries.X + F0) = 0 := by
      simp [map_add, hF0_0]
    rw [subst_comp_X_sq B0 (PowerSeries.X + F0) hXF0, zmod2_ps_add_sq]
    have hX2_sub : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hX2_0
    have hsub := congrArg (PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) ^ 2)) B0_subst_eq
    have h1x : PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) (1 : PowerSeries (ZMod 2)) = 1 := by
      change PowerSeries.subst (PowerSeries.X ^ 2) (PowerSeries.C 1) = 1; rw [PowerSeries.subst_C]; rfl
    rw [PowerSeries.subst_mul hX2_sub, PowerSeries.subst_add hX2_sub, h1x,
      PowerSeries.subst_X hX2_sub] at hsub
    have hu0 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries (ZMod 2)) + B0 ^ 2) = 0 := by
      rw [map_add, map_pow, PowerSeries.constantCoeff_X, B0_const]; norm_num
    have hu_sub : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries (ZMod 2)) + B0 ^ 2) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hu0
    have hcomp : PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) (PowerSeries.subst (PowerSeries.X + B0 ^ 2) B0) =
        PowerSeries.subst (PowerSeries.X ^ 2 + F0 ^ 2) B0 := by
      have h1 := PowerSeries.subst_comp_subst (R := ZMod 2) hu_sub hX2_sub
      have h2 := congrFun h1 B0
      dsimp only [Function.comp_apply] at h2
      rw [h2, PowerSeries.subst_add hX2_sub, PowerSeries.subst_X hX2_sub, PowerSeries.subst_pow hX2_sub]
    rw [hcomp] at hsub
    exact hsub
  -- Cancel unit (1 + X^2) to get subst (X + a2) a2 = subst (X + F0) F0!
  have h1X2_unit : IsUnit (1 + (PowerSeries.X : PowerSeries (ZMod 2)) ^ 2) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr; simp
  have hsubst_eq : PowerSeries.subst (PowerSeries.X + a2) a2 =
      PowerSeries.subst (PowerSeries.X + F0) F0 :=
    h1X2_unit.mul_left_cancel (ha2_eq.trans hF0_eq.symm)
  -- Prove a2 = F0 by strong induction on coefficients!
  have ha2_eq_F0 : a2 = F0 := by
    have hcoeff : ∀ n, PowerSeries.coeff n a2 = PowerSeries.coeff n F0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        rcases n with _ | _ | n'
        · rw [PowerSeries.coeff_zero_eq_constantCoeff, ha2_0, hF0_0]
        · rw [ha2_1, hF0_1]
        · set m := n' + 2
          have hXa_0 : PowerSeries.constantCoeff (PowerSeries.X + a2) = 0 := by simp [map_add, ha2_0]
          have hXF_0 : PowerSeries.constantCoeff (PowerSeries.X + F0) = 0 := by simp [map_add, hF0_0]
          have hXa_1 : PowerSeries.coeff 1 (PowerSeries.X + a2) = 1 := by
            rw [map_add, PowerSeries.coeff_X, if_pos rfl, ha2_1, add_zero]
          have hXF_1 : PowerSeries.coeff 1 (PowerSeries.X + F0) = 1 := by
            rw [map_add, PowerSeries.coeff_X, if_pos rfl, hF0_1, add_zero]
          have hs := congrArg (PowerSeries.coeff m) hsubst_eq
          rw [coeff_subst_eq_sum hXa_0, coeff_subst_eq_sum hXF_0] at hs
          conv_lhs at hs => rw [Finset.sum_range_succ]
          conv_rhs at hs => rw [Finset.sum_range_succ]
          -- For d < m, show coeff d a2 * coeff m ((X + a2)^d) = coeff d F0 * coeff m ((X + F0)^d)!
          -- Wait: since coeff 0 a2 = coeff 1 a2 = 0, d = 0 and d = 1 give 0; for d ≥ 2, coeff m ((X + a2)^d)
          -- only uses coeff k (X + a2) for k ≤ m - (d - 1) ≤ m - 1 < m!
          have hlow : ∑ d ∈ Finset.range m, PowerSeries.coeff d a2 * PowerSeries.coeff m ((PowerSeries.X + a2) ^ d) =
              ∑ d ∈ Finset.range m, PowerSeries.coeff d F0 * PowerSeries.coeff m ((PowerSeries.X + F0) ^ d) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdm : d < m := Finset.mem_range.mp hd
            rcases d with _ | _ | d'
            · rw [PowerSeries.coeff_zero_eq_constantCoeff, ha2_0, hF0_0, zero_mul, zero_mul]
            · rw [ha2_1, hF0_1, zero_mul, zero_mul]
            · rw [ih (d' + 2) hdm]
              congr 1
              have hagree : ∀ k ≤ m - 1, PowerSeries.coeff k (PowerSeries.X + a2) =
                  PowerSeries.coeff k (PowerSeries.X + F0) := by
                intro k hk
                rw [map_add, map_add, ih k (by omega)]
              conv_lhs => rw [pow_succ, PowerSeries.coeff_mul]
              conv_rhs => rw [pow_succ, PowerSeries.coeff_mul]
              apply Finset.sum_congr rfl
              intro ⟨i, j⟩ hij
              rw [Finset.mem_antidiagonal] at hij
              by_cases hj0 : j = 0
              · subst hj0
                rw [PowerSeries.coeff_zero_eq_constantCoeff, hXa_0, hXF_0, mul_zero, mul_zero]
              · by_cases hi0 : i = 0
                · subst hi0
                  rw [coeff_pow_eq_zero_of_lt hXa_0 (by omega), coeff_pow_eq_zero_of_lt hXF_0 (by omega),
                    zero_mul, zero_mul]
                · rw [coeff_pow_congr hagree (d' + 1) i (by omega), hagree j (by omega)]
          rw [hlow, coeff_pow_diag hXa_0 m, coeff_pow_diag hXF_0 m, hXa_1, hXF_1, one_pow,
            mul_one, mul_one] at hs
          exact add_left_cancel hs
    ext n; exact hcoeff n
  intro n _
  rw [odd_iff_zmod2_eq_one]
  have hc : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = PowerSeries.coeff n F0 := by
    rw [← ha2_eq_F0, PowerSeries.coeff_map]; rfl
  rw [hc, hF0_coeff]
  by_cases hev : Even n
  · rw [if_pos hev, coeff_B0]
    rcases hev with ⟨m, rfl⟩
    have hdiv : (m + m) / 2 = m := by omega
    rw [hdiv]
    constructor
    · intro h
      by_cases hm : isNoLeading10 m
      · exact ⟨m, by omega, hm⟩
      · rw [if_neg hm] at h; exact absurd h (by decide)
    · rintro ⟨m', hm', hno⟩
      have : m' = m := by omega
      subst this
      rw [if_pos hno]
  · rw [if_neg hev]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨m, rfl, _⟩; exact absurd ⟨m, by omega⟩ hev

end OMA.P_oeis_a380558

theorem OMA.solution : type_of% @OMA.S_oeis_a380558.main :=
  OMA.P_oeis_a380558.prove_main
