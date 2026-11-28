import OMAStatements.S_oeis_a396808
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a396808

open OMA.S_oeis_a396808

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

private noncomputable def u0 : PowerSeries (ZMod 2) :=
  letI := Classical.decPred (fun n : ℕ => ∃ k : ℕ, n = 2 ^ k)
  PowerSeries.mk fun n => if ∃ k : ℕ, n = 2 ^ k then 1 else 0

private lemma coeff_u0 (n : ℕ) :
    letI := Classical.decPred (fun n : ℕ => ∃ k : ℕ, n = 2 ^ k)
    PowerSeries.coeff n u0 = if ∃ k : ℕ, n = 2 ^ k then 1 else 0 := by
  classical
  simp [u0]

private lemma u0_const : PowerSeries.constantCoeff u0 = 0 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_u0]
  rw [if_neg]
  rintro ⟨k, hk⟩
  have := Nat.one_le_pow k 2 (by decide)
  omega

private lemma u0_quad : u0 + u0 ^ 2 = (PowerSeries.X : PowerSeries (ZMod 2)) := by
  classical
  ext n
  rw [map_add, coeff_u0, coeff_sq_zmod2, PowerSeries.coeff_X]
  by_cases hn0 : n = 0
  · subst hn0
    have hne : ¬ ∃ k : ℕ, (0 : ℕ) = 2 ^ k := by
      rintro ⟨k, hk⟩; have := Nat.one_le_pow k 2 (by decide); omega
    simp only [hne, show Even 0 by decide, Nat.zero_div, coeff_u0, ↓reduceIte,
      show (0 : ℕ) ≠ 1 by omega]
    decide
  · by_cases hn1 : n = 1
    · subst hn1
      have h1 : ∃ k : ℕ, (1 : ℕ) = 2 ^ k := ⟨0, by norm_num⟩
      simp only [h1, show ¬ Even 1 by decide, ↓reduceIte]
      decide
    · have hne1 : n ≠ 1 := hn1
      rw [if_neg hne1]
      by_cases hev : Even n
      · rw [if_pos hev, coeff_u0]
        have hiff : (∃ k : ℕ, n = 2 ^ k) ↔ (∃ k : ℕ, n / 2 = 2 ^ k) := by
          constructor
          · rintro ⟨k, hk⟩
            cases k with
            | zero => simp at hk; omega
            | succ k' => exact ⟨k', by rw [hk, pow_succ']; omega⟩
          · rintro ⟨k, hk⟩
            rcases hev with ⟨m, rfl⟩
            exact ⟨k + 1, by rw [pow_succ']; omega⟩
        by_cases h : ∃ k : ℕ, n = 2 ^ k
        · rw [if_pos h, if_pos (hiff.mp h)]; decide
        · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; decide
      · rw [if_neg hev, add_zero]
        have hnot : ¬ ∃ k : ℕ, n = 2 ^ k := by
          rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk; omega
          | succ k' => exact hev ⟨2 ^ k', by rw [hk, pow_succ']; omega⟩
        rw [if_neg hnot]

private noncomputable def B0 : PowerSeries (ZMod 2) := 1 + u0

private lemma B0_const : PowerSeries.constantCoeff B0 = 1 := by
  simp [B0, map_add, u0_const]

private lemma coeff_B0 (n : ℕ) (hn : 0 < n) :
    letI := Classical.decPred (fun n : ℕ => ∃ k : ℕ, n = 2 ^ k)
    PowerSeries.coeff n B0 = if ∃ k : ℕ, n = 2 ^ k then 1 else 0 := by
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

private lemma subst_XX2_u0 :
    PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 2) u0 =
      PowerSeries.X := by
  set S : PowerSeries (ZMod 2) := PowerSeries.X + PowerSeries.X ^ 2
  have hS0 : PowerSeries.constantCoeff S = 0 := by
    rw [map_add, map_pow, PowerSeries.constantCoeff_X]; norm_num
  have hSub : PowerSeries.HasSubst S := PowerSeries.HasSubst.of_constantCoeff_zero hS0
  set Y : PowerSeries (ZMod 2) := PowerSeries.subst S u0
  have hY0 : PowerSeries.constantCoeff Y = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst_eq_sum hS0]
    simp [PowerSeries.coeff_zero_eq_constantCoeff, u0_const]
  have hYq : Y + Y ^ 2 = S := by
    have hs := congrArg (PowerSeries.subst S) u0_quad
    rw [PowerSeries.subst_add hSub, PowerSeries.subst_pow hSub, PowerSeries.subst_X hSub] at hs
    exact hs
  have hdiff : Y + PowerSeries.X = (Y + PowerSeries.X) ^ 2 := by
    have hadd : (Y + Y ^ 2) + (PowerSeries.X + PowerSeries.X ^ 2) = S + S := by rw [hYq]
    rw [zmod2_ps_add_self] at hadd
    have hlhs : (Y + Y ^ 2) + (PowerSeries.X + PowerSeries.X ^ 2) =
        (Y + PowerSeries.X) + (Y + PowerSeries.X) ^ 2 := by
      rw [zmod2_ps_add_sq]; ring
    rw [hlhs] at hadd
    have := congrArg (· + (Y + PowerSeries.X) ^ 2) hadd
    rw [add_assoc, zmod2_ps_add_self, add_zero, zero_add] at this
    exact this
  have hzero : ∀ n, PowerSeries.coeff n (Y + PowerSeries.X) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero =>
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_add, hY0, PowerSeries.constantCoeff_X, add_zero]
      | succ m =>
        have hc := congrArg (PowerSeries.coeff (m + 1)) hdiff
        rw [coeff_sq_zmod2] at hc
        rw [hc]
        split_ifs with hev
        · exact ih ((m + 1) / 2) (by omega)
        · rfl
  ext n
  have h0 := hzero n
  rw [map_add] at h0
  have heq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact heq _ _ h0

private lemma subst_XX2_B0_pow (m : ℕ) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 2) (B0 ^ m) =
      (1 + PowerSeries.X) ^ m := by
  have hS0 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 2) = 0 := by
    rw [map_add, map_pow, PowerSeries.constantCoeff_X]; norm_num
  have hSub : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 2) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hS0
  have h1s : PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 2) (1 : PowerSeries (ZMod 2)) = 1 := by
    change PowerSeries.subst _ (PowerSeries.C 1) = 1; rw [PowerSeries.subst_C]; rfl
  rw [PowerSeries.subst_pow hSub, B0, PowerSeries.subst_add hSub, h1s, subst_XX2_u0]

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

private lemma choose_two_mul_zmod2 (r : ℕ) (hr : 1 ≤ r) :
    (Nat.choose (2 * r) r : ZMod 2) = 0 := by
  have h : Nat.choose (2 * r) r = 2 * Nat.choose (2 * r - 1) (r - 1) := by
    set m := r - 1
    have hr_eq : r = m + 1 := by omega
    rw [hr_eq, show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
    have h1 := Nat.choose_succ_succ (2 * m + 1) m
    simp only [Nat.succ_eq_add_one] at h1
    have h2 : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m :=
      Nat.choose_symm_of_eq_add (by omega)
    omega
  rw [h, Nat.cast_mul]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h2, zero_mul]

private lemma lagrange_zmod2 (F : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst (PowerSeries.X + PowerSeries.X ^ 2) F * inv1X ^ (n + 1)) =
      PowerSeries.coeff n F := by
  set S : PowerSeries (ZMod 2) := PowerSeries.X + PowerSeries.X ^ 2
  have hS0 : PowerSeries.constantCoeff S = 0 := by
    rw [map_add, map_pow, PowerSeries.constantCoeff_X]; norm_num
  have hS_fac : S = PowerSeries.X * (1 + PowerSeries.X) := by dsimp only [S]; ring
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.subst S F) * PowerSeries.coeff j (inv1X ^ (n + 1)))]
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
        PowerSeries.coeff i (PowerSeries.subst S F) * PowerSeries.coeff (n - i) (inv1X ^ (n + 1)) =
      ∑ d ∈ Finset.range (n + 1),
        PowerSeries.coeff d F * PowerSeries.coeff n (S ^ d * inv1X ^ (n + 1)) := by
    calc ∑ i ∈ Finset.range (n + 1),
            PowerSeries.coeff i (PowerSeries.subst S F) * PowerSeries.coeff (n - i) (inv1X ^ (n + 1))
        = ∑ i ∈ Finset.range (n + 1),
            (∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F * PowerSeries.coeff i (S ^ d)) *
              PowerSeries.coeff (n - i) (inv1X ^ (n + 1)) :=
          Finset.sum_congr rfl fun i hi => by rw [hsubst_split i hi]
      _ = ∑ i ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1),
            PowerSeries.coeff d F * (PowerSeries.coeff i (S ^ d) * PowerSeries.coeff (n - i) (inv1X ^ (n + 1))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => by ring
      _ = ∑ d ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
            PowerSeries.coeff d F * (PowerSeries.coeff i (S ^ d) * PowerSeries.coeff (n - i) (inv1X ^ (n + 1))) :=
          Finset.sum_comm
      _ = ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F *
            ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i (S ^ d) * PowerSeries.coeff (n - i) (inv1X ^ (n + 1)) := by
          refine Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ d ∈ Finset.range (n + 1),
            PowerSeries.coeff d F * PowerSeries.coeff n (S ^ d * inv1X ^ (n + 1)) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (S ^ d) * PowerSeries.coeff j (inv1X ^ (n + 1)))]
  rw [hswap, Finset.sum_eq_single n]
  · have hcancel : S ^ n * inv1X ^ (n + 1) = PowerSeries.X ^ n * inv1X := by
      rw [hS_fac, mul_pow, pow_succ, mul_assoc, ← mul_assoc ((1 + PowerSeries.X) ^ n),
        ← mul_pow, one_add_X_mul_inv1X, one_pow, one_mul]
    rw [hcancel, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    simp [inv1X]
  · intro d hd hne
    rw [Finset.mem_range] at hd
    have hdn : d < n := by omega
    have hcancel : S ^ d * inv1X ^ (n + 1) = PowerSeries.X ^ d * inv1X ^ (n - d + 1) := by
      rw [hS_fac, mul_pow, show n + 1 = d + (n - d + 1) by omega, pow_add,
        mul_assoc, ← mul_assoc ((1 + PowerSeries.X) ^ d), ← mul_pow,
        one_add_X_mul_inv1X, one_pow, one_mul]
    rw [hcancel, PowerSeries.coeff_X_pow_mul', if_pos (by omega), coeff_inv1X_pow,
      show n - d + (n - d) = 2 * (n - d) by omega, choose_two_mul_zmod2 (n - d) (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma coeff_B0_pow (m n : ℕ) (h : n + 1 ≤ m) :
    PowerSeries.coeff n (B0 ^ m) = (Nat.choose (m - n - 1) n : ZMod 2) := by
  rw [← lagrange_zmod2 (B0 ^ m) n, subst_XX2_B0_pow]
  have hmul : (1 + (PowerSeries.X : PowerSeries (ZMod 2))) ^ m * inv1X ^ (n + 1) =
      (1 + PowerSeries.X) ^ (m - n - 1) := by
    conv_lhs => rw [show m = (m - n - 1) + (n + 1) by omega]
    rw [pow_add, mul_assoc, ← mul_pow, one_add_X_mul_inv1X, one_pow, mul_one]
  rw [hmul, add_comm (1 : PowerSeries (ZMod 2)) PowerSeries.X, add_pow, map_sum]
  have hterm : ∀ k ∈ Finset.range (m - n - 1 + 1),
      PowerSeries.coeff n (PowerSeries.X ^ k * (1 : PowerSeries (ZMod 2)) ^ (m - n - 1 - k) *
        ((m - n - 1).choose k : PowerSeries (ZMod 2))) =
      if k = n then ((m - n - 1).choose k : ZMod 2) else 0 := by
    intro k _
    rw [one_pow, mul_one, show ((m - n - 1).choose k : PowerSeries (ZMod 2)) =
      PowerSeries.C ((m - n - 1).choose k : ZMod 2) by simp,
      PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
    split_ifs with h1 h2
    · simp
    · omega
    · omega
    · simp
  rw [Finset.sum_congr rfl hterm]
  by_cases hle : n ≤ m - n - 1
  · rw [Finset.sum_eq_single n]
    · rw [if_pos rfl]
    · intro k _ hk; rw [if_neg hk]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [if_neg (by omega)]

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

private theorem prove_main : type_of% @OMA.S_oeis_a396808.main := by
  classical
  intro A hA0 hA1 hEq
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  set a2 : PowerSeries (ZMod 2) := φ A
  have ha2_0 : PowerSeries.constantCoeff a2 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
  have ha2_1 : PowerSeries.coeff 1 a2 = 1 := by
    rw [PowerSeries.coeff_map, hA1, map_one]
  have hB0_1 : PowerSeries.coeff 1 B0 = 1 := by
    rw [coeff_B0 1 (by omega), if_pos ⟨0, by norm_num⟩]
  have ha2_eq : ∀ n : ℕ, 1 < n →
      ((n + 1 : ℕ) : ZMod 2) * PowerSeries.coeff n (a2 ^ (n + 1)) =
        (n : ZMod 2) * PowerSeries.coeff n (a2 ^ (n + 2)) := by
    intro n hn
    have h := congrArg (Int.castRingHom (ZMod 2)) (hEq n hn)
    simp only [map_mul, map_natCast, ← PowerSeries.coeff_map, map_pow] at h
    exact h
  have hB0_eq : ∀ n : ℕ, 1 < n →
      ((n + 1 : ℕ) : ZMod 2) * PowerSeries.coeff n (B0 ^ (n + 1)) =
        (n : ZMod 2) * PowerSeries.coeff n (B0 ^ (n + 2)) := by
    intro n hn
    rw [coeff_B0_pow (n + 1) n le_rfl, coeff_B0_pow (n + 2) n (by omega)]
    rw [show n + 1 - n - 1 = 0 by omega, show n + 2 - n - 1 = 1 by omega,
      Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hcoeff : ∀ n : ℕ, PowerSeries.coeff n a2 = PowerSeries.coeff n B0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | n'
      · rw [PowerSeries.coeff_zero_eq_constantCoeff, ha2_0, B0_const]
      · rw [ha2_1, hB0_1]
      · set m := n' + 2
        have h1 := coeff_pow_diff_of_agree ha2_0 B0_const ih (m + 1)
        have h2 := coeff_pow_diff_of_agree ha2_0 B0_const ih (m + 2)
        have hrelA := ha2_eq m (by omega)
        have hrelB := hB0_eq m (by omega)
        have hdiff : ((m + 1 : ℕ) : ZMod 2) * (PowerSeries.coeff m (a2 ^ (m + 1)) + PowerSeries.coeff m (B0 ^ (m + 1))) +
            (m : ZMod 2) * (PowerSeries.coeff m (a2 ^ (m + 2)) + PowerSeries.coeff m (B0 ^ (m + 2))) = 0 := by
          have hadd : ((m + 1 : ℕ) : ZMod 2) * PowerSeries.coeff m (a2 ^ (m + 1)) +
              (m : ZMod 2) * PowerSeries.coeff m (a2 ^ (m + 2)) = 0 := by
            rw [hrelA]; generalize ((m : ZMod 2) * PowerSeries.coeff m (a2 ^ (m + 2))) = x; revert x; decide
          have haddB : ((m + 1 : ℕ) : ZMod 2) * PowerSeries.coeff m (B0 ^ (m + 1)) +
              (m : ZMod 2) * PowerSeries.coeff m (B0 ^ (m + 2)) = 0 := by
            rw [hrelB]; generalize ((m : ZMod 2) * PowerSeries.coeff m (B0 ^ (m + 2))) = x; revert x; decide
          calc _ = (((m + 1 : ℕ) : ZMod 2) * PowerSeries.coeff m (a2 ^ (m + 1)) +
                (m : ZMod 2) * PowerSeries.coeff m (a2 ^ (m + 2))) +
                (((m + 1 : ℕ) : ZMod 2) * PowerSeries.coeff m (B0 ^ (m + 1)) +
                (m : ZMod 2) * PowerSeries.coeff m (B0 ^ (m + 2))) := by ring
            _ = 0 + 0 := by rw [hadd, haddB]
            _ = 0 := by ring
        rw [h1, h2] at hdiff
        have hcoef1 : ((m + 1 : ℕ) : ZMod 2) * ((m + 1 : ℕ) : ZMod 2) + (m : ZMod 2) * ((m + 2 : ℕ) : ZMod 2) = 1 := by
          push_cast
          generalize (m : ZMod 2) = x; revert x; decide
        have hc0 : PowerSeries.coeff m a2 + PowerSeries.coeff m B0 = 0 := by
          calc PowerSeries.coeff m a2 + PowerSeries.coeff m B0
              = 1 * (PowerSeries.coeff m a2 + PowerSeries.coeff m B0) := by ring
            _ = (((m + 1 : ℕ) : ZMod 2) * ((m + 1 : ℕ) : ZMod 2) + (m : ZMod 2) * ((m + 2 : ℕ) : ZMod 2)) *
                (PowerSeries.coeff m a2 + PowerSeries.coeff m B0) := by rw [hcoef1]
            _ = ((m + 1 : ℕ) : ZMod 2) * (((m + 1 : ℕ) : ZMod 2) * (PowerSeries.coeff m a2 + PowerSeries.coeff m B0)) +
                (m : ZMod 2) * (((m + 2 : ℕ) : ZMod 2) * (PowerSeries.coeff m a2 + PowerSeries.coeff m B0)) := by ring
            _ = 0 := hdiff
        have heq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
        exact heq _ _ hc0
  intro n hn
  rw [odd_iff_zmod2_eq_one]
  have hc : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = PowerSeries.coeff n B0 := by
    rw [← hcoeff n, PowerSeries.coeff_map]; rfl
  rw [hc, coeff_B0 n hn]
  by_cases h : ∃ k : ℕ, n = 2 ^ k
  · simp [h]
  · simp [h]

end OMA.P_oeis_a396808

theorem OMA.solution : type_of% @OMA.S_oeis_a396808.main :=
  OMA.P_oeis_a396808.prove_main
