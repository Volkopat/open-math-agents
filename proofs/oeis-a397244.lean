import OMAStatements.S_oeis_a397244
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic

namespace OMA.P_oeis_a397244

open OMA.S_oeis_a397244

private lemma zmod2_ps_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

private lemma zmod2_ps_add_self (f : PowerSeries (ZMod 2)) : f + f = 0 := by
  rw [← two_mul, zmod2_ps_two, zero_mul]

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

private lemma isFibbinary_two_mul (r : ℕ) : isFibbinary (2 * r) ↔ isFibbinary r := by
  constructor
  · intro h i
    have hi := h (i + 1)
    rw [pow_succ', Nat.mul_div_mul_left _ _ (by decide : 0 < 2)] at hi
    exact hi
  · intro h i
    cases i with
    | zero => simp; omega
    | succ i' =>
      rw [pow_succ', Nat.mul_div_mul_left _ _ (by decide : 0 < 2)]
      exact h i'

private lemma isFibbinary_four_mul_add_one (r : ℕ) : isFibbinary (4 * r + 1) ↔ isFibbinary r := by
  constructor
  · intro h i
    have hi := h (i + 2)
    have hdiv : (4 * r + 1) / 2 ^ (i + 2) = r / 2 ^ i := by
      rw [pow_succ', pow_succ', ← mul_assoc, ← Nat.div_div_eq_div_mul, show (4 * r + 1) / (2 * 2) = r by omega]
    rwa [hdiv] at hi
  · intro h i
    rcases i with _ | _ | i'
    · simp
    · rw [pow_one, show (4 * r + 1) / 2 = 2 * r by omega]; omega
    · have hdiv : (4 * r + 1) / 2 ^ (i' + 2) = r / 2 ^ i' := by
        rw [pow_succ', pow_succ', ← mul_assoc, ← Nat.div_div_eq_div_mul, show (4 * r + 1) / (2 * 2) = r by omega]
      rw [hdiv]
      exact h i'

private lemma not_isFibbinary_four_mul_add_three (r : ℕ) : ¬ isFibbinary (4 * r + 3) := by
  intro h; have h0 := h 0; simp at h0

private noncomputable def Ffib : PowerSeries (ZMod 2) :=
  letI := Classical.decPred isFibbinary
  PowerSeries.mk fun m => if isFibbinary m then 1 else 0

private lemma coeff_Ffib (m : ℕ) :
    letI := Classical.decPred isFibbinary
    PowerSeries.coeff m Ffib = if isFibbinary m then 1 else 0 := by
  classical
  simp [Ffib]

private lemma Ffib_const : PowerSeries.constantCoeff Ffib = 1 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Ffib, if_pos]
  intro i; simp

private lemma Ffib_eq : Ffib = Ffib ^ 2 + (PowerSeries.X : PowerSeries (ZMod 2)) * Ffib ^ 4 := by
  classical
  ext n
  rw [map_add, coeff_Ffib, coeff_sq_zmod2, ← pow_one (PowerSeries.X : PowerSeries (ZMod 2)),
    PowerSeries.coeff_X_pow_mul']
  have h4 : Ffib ^ 4 = (Ffib ^ 2) ^ 2 := by ring
  rw [h4]
  by_cases hmod : n % 2 = 0
  · have hev : Even n := ⟨n / 2, by omega⟩
    rw [if_pos hev, coeff_Ffib]
    have hX : (if 1 ≤ n then PowerSeries.coeff (n - 1) ((Ffib ^ 2) ^ 2) else 0) = 0 := by
      split_ifs with h1
      · rw [coeff_sq_zmod2, if_neg (by rintro ⟨k, hk⟩; omega)]
      · rfl
    rw [hX, add_zero]
    have hiff : isFibbinary n ↔ isFibbinary (n / 2) := by
      have : n = 2 * (n / 2) := by omega
      conv_lhs => rw [this]
      exact isFibbinary_two_mul (n / 2)
    by_cases h : isFibbinary n
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  · have hodd : ¬ Even n := by rintro ⟨k, hk⟩; omega
    rw [if_neg hodd, zero_add, if_pos (by omega : 1 ≤ n), coeff_sq_zmod2]
    have hev1 : Even (n - 1) := ⟨(n - 1) / 2, by omega⟩
    rw [if_pos hev1, coeff_sq_zmod2]
    by_cases h4m : n % 4 = 1
    · have hev2 : Even ((n - 1) / 2) := ⟨n / 4, by omega⟩
      rw [if_pos hev2, coeff_Ffib]
      have hdiv : (n - 1) / 2 / 2 = n / 4 := by omega
      rw [hdiv]
      have hiff : isFibbinary n ↔ isFibbinary (n / 4) := by
        have : n = 4 * (n / 4) + 1 := by omega
        conv_lhs => rw [this]
        exact isFibbinary_four_mul_add_one (n / 4)
      by_cases h : isFibbinary n
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
    · have h4m3 : n % 4 = 3 := by omega
      have hodd2 : ¬ Even ((n - 1) / 2) := by rintro ⟨k, hk⟩; omega
      rw [if_neg hodd2]
      have hnot : ¬ isFibbinary n := by
        have : n = 4 * (n / 4) + 3 := by omega
        rw [this]
        exact not_isFibbinary_four_mul_add_three (n / 4)
      rw [if_neg hnot]

private lemma Ffib_cubic : Ffib + (PowerSeries.X : PowerSeries (ZMod 2)) * Ffib ^ 3 = 1 := by
  have hu : IsUnit Ffib := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [Ffib_const]; exact isUnit_one)
  apply hu.mul_left_cancel
  calc Ffib * (Ffib + PowerSeries.X * Ffib ^ 3) = Ffib ^ 2 + PowerSeries.X * Ffib ^ 4 := by ring
    _ = Ffib := Ffib_eq.symm
    _ = Ffib * 1 := (mul_one Ffib).symm

private noncomputable def u0 : PowerSeries (ZMod 2) :=
  (PowerSeries.X : PowerSeries (ZMod 2)) * Ffib ^ 2

private lemma coeff_u0 (n : ℕ) :
    letI := Classical.decPred (fun n : ℕ => ∃ m : ℕ, isFibbinary m ∧ n = 2 * m + 1)
    PowerSeries.coeff n u0 = if ∃ m : ℕ, isFibbinary m ∧ n = 2 * m + 1 then 1 else 0 := by
  classical
  rw [u0, ← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul']
  cases n with
  | zero => rw [if_neg (by omega), if_neg (by rintro ⟨m, _, hm⟩; omega)]
  | succ k =>
    rw [if_pos (by omega), Nat.add_sub_cancel, coeff_sq_zmod2]
    by_cases hev : Even k
    · rw [if_pos hev, coeff_Ffib]
      have hiff : isFibbinary (k / 2) ↔ ∃ m : ℕ, isFibbinary m ∧ k + 1 = 2 * m + 1 := by
        rcases hev with ⟨m, rfl⟩
        constructor
        · intro h; exact ⟨m, by rwa [show (m + m) / 2 = m by omega] at h, by omega⟩
        · rintro ⟨m', hm', heq⟩
          have hmeq : m' = m := by omega
          rw [show (m + m) / 2 = m by omega, ← hmeq]
          exact hm'
      by_cases h : isFibbinary (k / 2)
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
    · rw [if_neg hev, if_neg]
      rintro ⟨m, _, hm⟩; exact hev ⟨m, by omega⟩

private lemma u0_const : PowerSeries.constantCoeff u0 = 0 := by simp [u0, map_mul]

private lemma u0_cubic : u0 + u0 ^ 3 = (PowerSeries.X : PowerSeries (ZMod 2)) := by
  have hsq : Ffib ^ 2 + PowerSeries.X ^ 2 * Ffib ^ 6 = 1 := by
    have h := congrArg (· ^ 2) Ffib_cubic
    rw [zmod2_ps_add_sq, mul_pow, one_pow] at h
    calc Ffib ^ 2 + PowerSeries.X ^ 2 * Ffib ^ 6 = Ffib ^ 2 + PowerSeries.X ^ 2 * (Ffib ^ 3) ^ 2 := by ring
      _ = 1 := h
  calc u0 + u0 ^ 3 = PowerSeries.X * (Ffib ^ 2 + PowerSeries.X ^ 2 * Ffib ^ 6) := by dsimp only [u0]; ring
    _ = PowerSeries.X * 1 := by rw [hsq]
    _ = PowerSeries.X := mul_one _

private noncomputable def B0 : PowerSeries (ZMod 2) := 1 + u0

private lemma B0_const : PowerSeries.constantCoeff B0 = 1 := by simp [B0, map_add, u0_const]

private lemma coeff_B0 (n : ℕ) (hn : 0 < n) :
    letI := Classical.decPred (fun n : ℕ => ∃ m : ℕ, isFibbinary m ∧ n = 2 * m + 1)
    PowerSeries.coeff n B0 = if ∃ m : ℕ, isFibbinary m ∧ n = 2 * m + 1 then 1 else 0 := by
  classical
  rw [B0, map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add, coeff_u0]

private lemma coeff_pow_eq_zero_of_lt {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) {d n : ℕ} (h : n < d) :
    PowerSeries.coeff n (g ^ d) = 0 := by
  have hgX : g = PowerSeries.X * PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) g) := by
    ext k
    rw [← pow_one PowerSeries.X, PowerSeries.coeff_X_pow_mul']
    cases k with
    | zero => rw [if_neg (by omega), PowerSeries.coeff_zero_eq_constantCoeff, hg0]
    | succ p => rw [if_pos (by omega), Nat.add_sub_cancel, PowerSeries.coeff_mk]
  rw [hgX, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

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

private lemma subst_XX3_u0 :
    PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 3) u0 =
      PowerSeries.X := by
  set S : PowerSeries (ZMod 2) := PowerSeries.X + PowerSeries.X ^ 3
  have hS0 : PowerSeries.constantCoeff S = 0 := by
    rw [map_add, map_pow, PowerSeries.constantCoeff_X]; norm_num
  have hSub : PowerSeries.HasSubst S := PowerSeries.HasSubst.of_constantCoeff_zero hS0
  set Y : PowerSeries (ZMod 2) := PowerSeries.subst S u0
  have hY0 : PowerSeries.constantCoeff Y = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst_eq_sum hS0]
    simp [PowerSeries.coeff_zero_eq_constantCoeff, u0_const]
  have hYc : Y + Y ^ 3 = S := by
    have hs := congrArg (PowerSeries.subst S) u0_cubic
    rw [PowerSeries.subst_add hSub, PowerSeries.subst_pow hSub, PowerSeries.subst_X hSub] at hs
    exact hs
  have hdiff : Y + PowerSeries.X = Y ^ 3 + PowerSeries.X ^ 3 := by
    have hadd : (Y + Y ^ 3) + (PowerSeries.X + PowerSeries.X ^ 3) = S + S := by rw [hYc]
    rw [zmod2_ps_add_self] at hadd
    have := congrArg (· + (Y ^ 3 + PowerSeries.X ^ 3)) hadd
    calc Y + PowerSeries.X = (Y + PowerSeries.X) + 0 := (add_zero _).symm
      _ = (Y + PowerSeries.X) + ((Y ^ 3 + PowerSeries.X ^ 3) + (Y ^ 3 + PowerSeries.X ^ 3)) := by rw [zmod2_ps_add_self]
      _ = ((Y + Y ^ 3) + (PowerSeries.X + PowerSeries.X ^ 3)) + (Y ^ 3 + PowerSeries.X ^ 3) := by ring
      _ = 0 + (Y ^ 3 + PowerSeries.X ^ 3) := this
      _ = Y ^ 3 + PowerSeries.X ^ 3 := zero_add _
  have hfac : Y + PowerSeries.X = (Y + PowerSeries.X) * (Y ^ 2 + Y * PowerSeries.X + PowerSeries.X ^ 2) := by
    conv_lhs => rw [hdiff]
    have h2 : ∀ f : PowerSeries (ZMod 2), f + f = 0 := zmod2_ps_add_self
    calc Y ^ 3 + PowerSeries.X ^ 3
        = Y ^ 3 + PowerSeries.X ^ 3 + (Y ^ 2 * PowerSeries.X + Y ^ 2 * PowerSeries.X) +
            (Y * PowerSeries.X ^ 2 + Y * PowerSeries.X ^ 2) := by rw [h2, h2]; ring
      _ = (Y + PowerSeries.X) * (Y ^ 2 + Y * PowerSeries.X + PowerSeries.X ^ 2) := by ring
  have hconst : PowerSeries.constantCoeff (Y ^ 2 + Y * PowerSeries.X + PowerSeries.X ^ 2) = 0 := by
    rw [map_add, map_add, map_pow, map_mul, map_pow, hY0, PowerSeries.constantCoeff_X]; simp
  have hzero : ∀ n, PowerSeries.coeff n (Y + PowerSeries.X) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff, map_add, hY0, PowerSeries.constantCoeff_X, add_zero]
      | succ m =>
        have hc := congrArg (PowerSeries.coeff (m + 1)) hfac
        rw [hc, PowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun ⟨i, j⟩ hij => ?_
        rw [Finset.mem_antidiagonal] at hij
        by_cases hj0 : j = 0
        · subst hj0
          rw [PowerSeries.coeff_zero_eq_constantCoeff, hconst, mul_zero]
        · rw [ih i (by omega), zero_mul]
  ext n
  have h0 := hzero n
  rw [map_add] at h0
  have heq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact heq _ _ h0

private lemma subst_XX3_B0_pow (m : ℕ) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 3) (B0 ^ m) =
      (1 + PowerSeries.X) ^ m := by
  have hS0 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 3) = 0 := by
    rw [map_add, map_pow, PowerSeries.constantCoeff_X]; norm_num
  have hSub : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 3) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hS0
  have h1s : PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 3) (1 : PowerSeries (ZMod 2)) = 1 := by
    change PowerSeries.subst _ (PowerSeries.C 1) = 1; rw [PowerSeries.subst_C]; rfl
  rw [PowerSeries.subst_pow hSub, B0, PowerSeries.subst_add hSub, h1s, subst_XX3_u0]

private def inv1X : PowerSeries (ZMod 2) := PowerSeries.mk fun _ => 1

private lemma one_add_X_mul_inv1X :
    (1 + (PowerSeries.X : PowerSeries (ZMod 2))) * inv1X = 1 := by
  ext n
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_one]
  have hX : PowerSeries.coeff n ((PowerSeries.X : PowerSeries (ZMod 2)) * inv1X) =
      if 1 ≤ n then PowerSeries.coeff (n - 1) inv1X else 0 := by
    rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul']
  rw [hX]
  simp only [inv1X, PowerSeries.coeff_mk]
  cases n with
  | zero => decide
  | succ m => simp [show 1 ≤ m + 1 by omega]; decide

private lemma coeff_inv1X_pow (k n : ℕ) :
    PowerSeries.coeff n (inv1X ^ (k + 1)) = (Nat.choose (n + k) n : ZMod 2) := by
  induction k generalizing n with
  | zero => simp [inv1X]
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (inv1X ^ (k + 1)) * PowerSeries.coeff j inv1X)]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        PowerSeries.coeff i (inv1X ^ (k + 1)) * PowerSeries.coeff (n - i) inv1X =
          (Nat.choose (i + k) i : ZMod 2) := by
      intro i _
      rw [ih i, show PowerSeries.coeff (n - i) inv1X = 1 by simp [inv1X], mul_one]
    rw [Finset.sum_congr rfl hterm]
    clear hterm ih
    induction n with
    | zero => simp
    | succ m ihm =>
      rw [Finset.sum_range_succ, ihm, ← Nat.cast_add]
      congr 1
      conv_rhs => rw [show m + 1 + (k + 1) = (m + k + 1) + 1 by omega, Nat.choose_succ_succ]
      rw [show m + 1 + k = m + k + 1 by omega, show m + (k + 1) = m + k + 1 by omega, add_comm]

private lemma choose_even_of_bit {v M K : ℕ}
    (hK : (K / 2 ^ v) % 2 = 1) (hM : (M / 2 ^ v) % 2 = 0) :
    (Nat.choose M K : ZMod 2) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  induction v generalizing M K with
  | zero =>
    simp only [pow_zero, Nat.div_one] at hK hM
    have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := M) (k := K)
    have hz : Nat.choose (M % 2) (K % 2) = 0 := by rw [hM, hK]; decide
    have h0 : Nat.choose M K % 2 = 0 := by
      change Nat.choose M K % 2 = (Nat.choose (M % 2) (K % 2) * Nat.choose (M / 2) (K / 2)) % 2 at hluc
      rw [hz, zero_mul] at hluc
      exact hluc
    rw [← ZMod.natCast_mod, h0]; rfl
  | succ v ih =>
    have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := M) (k := K)
    have hK' : ((K / 2) / 2 ^ v) % 2 = 1 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']; exact hK
    have hM' : ((M / 2) / 2 ^ v) % 2 = 0 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']; exact hM
    have hdiv0 := ih hK' hM'
    have hmod0 : Nat.choose (M / 2) (K / 2) % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ 2).mp hdiv0)
    have h0 : Nat.choose M K % 2 = 0 := by
      change Nat.choose M K % 2 = (Nat.choose (M % 2) (K % 2) * Nat.choose (M / 2) (K / 2)) % 2 at hluc
      rw [Nat.mul_mod, hmod0, mul_zero] at hluc
      exact hluc
    rw [← ZMod.natCast_mod, h0]; rfl

private lemma choose_three_mul_sub_one_zmod2 (r : ℕ) (hr : 1 ≤ r) :
    (Nat.choose (3 * r - 1) r : ZMod 2) = 0 := by
  have hex : ∃ v u : ℕ, r = 2 ^ v * u ∧ u % 2 = 1 := by
    induction r using Nat.strongRecOn with
    | ind m ihm =>
      by_cases h2 : m % 2 = 0
      · obtain ⟨v, u, heq, hu⟩ := ihm (m / 2) (by omega) (by omega)
        exact ⟨v + 1, u, by rw [pow_succ', mul_assoc, ← heq]; omega, hu⟩
      · exact ⟨0, m, by simp, by omega⟩
  obtain ⟨v, u, hreq, huodd⟩ := hex
  have h2v_pos : 0 < 2 ^ v := pow_pos (by decide) v
  have hKbit : (r / 2 ^ v) % 2 = 1 := by
    rw [hreq, Nat.mul_div_cancel_left u h2v_pos]; exact huodd
  refine choose_even_of_bit (v := v) hKbit ?_
  have hu1 : 1 ≤ u := by omega
  have hsplit : 3 * r - 1 = 2 ^ v * (3 * u - 1) + (2 ^ v - 1) := by
    rw [hreq]
    have h3u : 3 * (2 ^ v * u) = 2 ^ v * (3 * u - 1) + 2 ^ v := by
      have : 3 * u = (3 * u - 1) + 1 := by omega
      calc 3 * (2 ^ v * u) = 2 ^ v * (3 * u) := by ring
        _ = 2 ^ v * ((3 * u - 1) + 1) := congrArg (2 ^ v * ·) this
        _ = 2 ^ v * (3 * u - 1) + 2 ^ v := by ring
    omega
  rw [hsplit, Nat.mul_add_div h2v_pos, Nat.div_eq_of_lt (by omega : 2 ^ v - 1 < 2 ^ v), add_zero]
  omega

private lemma lagrange_cubic_zmod2 (F : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst (PowerSeries.X + PowerSeries.X ^ 3) F * inv1X ^ (2 * n)) =
      PowerSeries.coeff n F := by
  set S : PowerSeries (ZMod 2) := PowerSeries.X + PowerSeries.X ^ 3
  have hS0 : PowerSeries.constantCoeff S = 0 := by
    rw [map_add, map_pow, PowerSeries.constantCoeff_X]; norm_num
  have hS_fac : S = PowerSeries.X * (1 + PowerSeries.X) ^ 2 := by
    dsimp only [S]; rw [zmod2_ps_add_sq, one_pow]; ring
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.subst S F) * PowerSeries.coeff j (inv1X ^ (2 * n)))]
  have hsubst_split : ∀ i ∈ Finset.range (n + 1),
      PowerSeries.coeff i (PowerSeries.subst S F) =
        ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F * PowerSeries.coeff i (S ^ d) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [coeff_subst_eq_sum hS0]
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun d _ hd => ?_
    rw [Finset.mem_range] at hd
    rw [coeff_pow_eq_zero_of_lt hS0 (by omega), mul_zero]
  have hswap :
      ∑ i ∈ Finset.range (n + 1),
        PowerSeries.coeff i (PowerSeries.subst S F) * PowerSeries.coeff (n - i) (inv1X ^ (2 * n)) =
      ∑ d ∈ Finset.range (n + 1),
        PowerSeries.coeff d F * PowerSeries.coeff n (S ^ d * inv1X ^ (2 * n)) := by
    calc ∑ i ∈ Finset.range (n + 1),
            PowerSeries.coeff i (PowerSeries.subst S F) * PowerSeries.coeff (n - i) (inv1X ^ (2 * n))
        = ∑ i ∈ Finset.range (n + 1),
            (∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F * PowerSeries.coeff i (S ^ d)) *
              PowerSeries.coeff (n - i) (inv1X ^ (2 * n)) :=
          Finset.sum_congr rfl fun i hi => by rw [hsubst_split i hi]
      _ = ∑ i ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1),
            PowerSeries.coeff d F * (PowerSeries.coeff i (S ^ d) * PowerSeries.coeff (n - i) (inv1X ^ (2 * n))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => by ring
      _ = ∑ d ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
            PowerSeries.coeff d F * (PowerSeries.coeff i (S ^ d) * PowerSeries.coeff (n - i) (inv1X ^ (2 * n))) :=
          Finset.sum_comm
      _ = ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F *
            ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i (S ^ d) * PowerSeries.coeff (n - i) (inv1X ^ (2 * n)) := by
          refine Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ d ∈ Finset.range (n + 1),
            PowerSeries.coeff d F * PowerSeries.coeff n (S ^ d * inv1X ^ (2 * n)) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (S ^ d) * PowerSeries.coeff j (inv1X ^ (2 * n)))]
  rw [hswap, Finset.sum_eq_single n]
  · have hcancel : S ^ n * inv1X ^ (2 * n) = PowerSeries.X ^ n := by
      rw [hS_fac, mul_pow, ← pow_mul, mul_assoc, ← mul_pow, one_add_X_mul_inv1X, one_pow, mul_one]
    rw [hcancel, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
  · intro d hd hne
    rw [Finset.mem_range] at hd
    have hdn : d < n := by omega
    have hcancel : S ^ d * inv1X ^ (2 * n) = PowerSeries.X ^ d * inv1X ^ (2 * (n - d)) := by
      rw [hS_fac, mul_pow, ← pow_mul, show 2 * n = 2 * d + 2 * (n - d) by omega, pow_add,
        mul_assoc, ← mul_assoc ((1 + PowerSeries.X) ^ (2 * d)), ← mul_pow,
        one_add_X_mul_inv1X, one_pow, one_mul]
    rw [hcancel, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
      show 2 * (n - d) = (2 * (n - d) - 1) + 1 by omega, coeff_inv1X_pow,
      show n - d + (2 * (n - d) - 1) = 3 * (n - d) - 1 by omega,
      choose_three_mul_sub_one_zmod2 (n - d) (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma coeff_B0_pow_two_mul_add_one (n : ℕ) (hn : 1 < n) :
    PowerSeries.coeff n (B0 ^ (2 * n + 1)) = 0 := by
  rw [← lagrange_cubic_zmod2 (B0 ^ (2 * n + 1)) n, subst_XX3_B0_pow]
  have hmul : (1 + (PowerSeries.X : PowerSeries (ZMod 2))) ^ (2 * n + 1) * inv1X ^ (2 * n) =
      1 + PowerSeries.X := by
    rw [pow_succ', mul_assoc, ← mul_pow, one_add_X_mul_inv1X, one_pow, mul_one]
  rw [hmul, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
    if_neg (by omega), if_neg (by omega), add_zero]

private lemma coeff_pow_diff_of_agree {f g : PowerSeries (ZMod 2)} {n : ℕ}
    (hf0 : PowerSeries.constantCoeff f = 1) (hg0 : PowerSeries.constantCoeff g = 1)
    (hagree : ∀ j < n, PowerSeries.coeff j f = PowerSeries.coeff j g) (k : ℕ) :
    PowerSeries.coeff n (f ^ k) + PowerSeries.coeff n (g ^ k) =
      (k : ZMod 2) * (PowerSeries.coeff n f + PowerSeries.coeff n g) := by
  have hpow_agree : ∀ r : ℕ, ∀ j < n, PowerSeries.coeff j (f ^ r) = PowerSeries.coeff j (g ^ r) := by
    intro r
    induction r with
    | zero => intro j _; rfl
    | succ r ihr =>
      intro j hj
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun ⟨a, b⟩ hab => ?_
      rw [Finset.mem_antidiagonal] at hab
      rw [ihr a (by omega), hagree b (by omega)]
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
    exact h2 _
  | succ k ih =>
    cases n with
    | zero =>
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hf0, hg0, one_pow]
      have h2 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [h2, mul_zero]
    | succ m =>
      have hsplit : ∀ h : PowerSeries (ZMod 2), PowerSeries.constantCoeff h = 1 →
          PowerSeries.coeff (m + 1) (h ^ (k + 1)) =
            (∑ i ∈ Finset.range m, PowerSeries.coeff (i + 1) (h ^ k) * PowerSeries.coeff (m + 1 - (i + 1)) h) +
              PowerSeries.coeff (m + 1) h + PowerSeries.coeff (m + 1) (h ^ k) := by
        intro h hh0
        rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (h ^ k) * PowerSeries.coeff j h),
          Finset.sum_range_succ, Finset.sum_range_succ']
        simp only [Nat.sub_zero, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff,
          map_pow, hh0, one_pow, one_mul, mul_one]
      have hmid :
          ∑ i ∈ Finset.range m, PowerSeries.coeff (i + 1) (f ^ k) * PowerSeries.coeff (m + 1 - (i + 1)) f =
          ∑ i ∈ Finset.range m, PowerSeries.coeff (i + 1) (g ^ k) * PowerSeries.coeff (m + 1 - (i + 1)) g := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [hpow_agree k (i + 1) (by omega), hagree (m + 1 - (i + 1)) (by omega)]
      rw [hsplit f hf0, hsplit g hg0, hmid, Nat.cast_add, Nat.cast_one]
      have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
      set S := ∑ i ∈ Finset.range m, PowerSeries.coeff (i + 1) (g ^ k) * PowerSeries.coeff (m + 1 - (i + 1)) g
      calc (S + PowerSeries.coeff (m + 1) f + PowerSeries.coeff (m + 1) (f ^ k)) +
            (S + PowerSeries.coeff (m + 1) g + PowerSeries.coeff (m + 1) (g ^ k))
          = (S + S) + (PowerSeries.coeff (m + 1) f + PowerSeries.coeff (m + 1) g) +
              (PowerSeries.coeff (m + 1) (f ^ k) + PowerSeries.coeff (m + 1) (g ^ k)) := by ring
        _ = 0 + (PowerSeries.coeff (m + 1) f + PowerSeries.coeff (m + 1) g) +
              (k : ZMod 2) * (PowerSeries.coeff (m + 1) f + PowerSeries.coeff (m + 1) g) := by rw [h2 S, ih]
        _ = ((k : ZMod 2) + 1) * (PowerSeries.coeff (m + 1) f + PowerSeries.coeff (m + 1) g) := by ring

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

private theorem prove_main : type_of% @OMA.S_oeis_a397244.main := by
  classical
  intro A hA0 hA1 hEq
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  set a2 : PowerSeries (ZMod 2) := φ A
  have ha2_0 : PowerSeries.constantCoeff a2 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
  have ha2_1 : PowerSeries.coeff 1 a2 = 1 := by rw [PowerSeries.coeff_map, hA1, map_one]
  have hB0_1 : PowerSeries.coeff 1 B0 = 1 := by
    rw [coeff_B0 1 (by omega), if_pos ⟨0, fun i => by simp, by omega⟩]
  have ha2_eq : ∀ n : ℕ, 1 < n → PowerSeries.coeff n (a2 ^ (2 * n + 1)) = 0 := by
    intro n hn
    have h := congrArg (Int.castRingHom (ZMod 2)) (hEq n hn)
    simp only [map_mul, map_natCast, ← PowerSeries.coeff_map, map_pow] at h
    have h2n : ((2 * n : ℕ) : ZMod 2) = 0 := by
      rw [Nat.cast_mul]
      have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]
    have h2nm1 : ((2 * n - 1 : ℕ) : ZMod 2) = 1 := by
      have : (2 * n - 1) % 2 = 1 := by omega
      rw [← ZMod.natCast_mod, this]; rfl
    rw [h2n, zero_mul, h2nm1, one_mul] at h
    exact h.symm
  have hcoeff : ∀ n : ℕ, PowerSeries.coeff n a2 = PowerSeries.coeff n B0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | n'
      · rw [PowerSeries.coeff_zero_eq_constantCoeff, ha2_0, B0_const]
      · rw [ha2_1, hB0_1]
      · set m := n' + 2
        have h1 := coeff_pow_diff_of_agree ha2_0 B0_const ih (2 * m + 1)
        rw [ha2_eq m (by omega), coeff_B0_pow_two_mul_add_one m (by omega), add_zero] at h1
        have h2m1 : ((2 * m + 1 : ℕ) : ZMod 2) = 1 := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
          have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
          rw [h2, zero_mul, zero_add]
        rw [h2m1, one_mul] at h1
        have heq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
        exact heq _ _ h1.symm
  intro n hn
  rw [odd_iff_zmod2_eq_one]
  have hc : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = PowerSeries.coeff n B0 := by
    rw [← hcoeff n, PowerSeries.coeff_map]; rfl
  rw [hc, coeff_B0 n hn]
  by_cases h : ∃ m : ℕ, isFibbinary m ∧ n = 2 * m + 1
  · simp [h]
  · simp [h]

end OMA.P_oeis_a397244

theorem OMA.solution : type_of% @OMA.S_oeis_a397244.main :=
  OMA.P_oeis_a397244.prove_main
