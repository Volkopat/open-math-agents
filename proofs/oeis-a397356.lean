import OMAStatements.S_oeis_a397356
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic

namespace OMA.P_oeis_a397356

open OMA.S_oeis_a397356

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
    · rw [if_neg hn1]
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

private noncomputable def C0 : PowerSeries (ZMod 2) :=
  letI := Classical.decPred (fun n : ℕ => ∃ k : ℕ, n + 1 = 2 ^ k)
  PowerSeries.mk fun n => if ∃ k : ℕ, n + 1 = 2 ^ k then 1 else 0

private lemma coeff_C0 (n : ℕ) :
    letI := Classical.decPred (fun n : ℕ => ∃ k : ℕ, n + 1 = 2 ^ k)
    PowerSeries.coeff n C0 = if ∃ k : ℕ, n + 1 = 2 ^ k then 1 else 0 := by
  classical
  simp [C0]

private lemma X_mul_C0_eq_u0 : (PowerSeries.X : PowerSeries (ZMod 2)) * C0 = u0 := by
  classical
  ext n
  rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul', coeff_u0]
  cases n with
  | zero =>
    rw [if_neg (by omega)]
    have hne : ¬ ∃ k : ℕ, (0 : ℕ) = 2 ^ k := by
      rintro ⟨k, hk⟩; have := Nat.one_le_pow k 2 (by decide); omega
    rw [if_neg hne]
  | succ m =>
    rw [if_pos (by omega), Nat.add_sub_cancel, coeff_C0]

private lemma C0_quad : C0 = 1 + (PowerSeries.X : PowerSeries (ZMod 2)) * C0 ^ 2 := by
  classical
  ext n
  rw [coeff_C0, map_add, PowerSeries.coeff_one]
  rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul']
  cases n with
  | zero =>
    rw [if_pos ⟨0, by norm_num⟩, if_pos rfl, if_neg (by omega), add_zero]
  | succ m =>
    rw [if_neg (by omega : m + 1 ≠ 0), zero_add, if_pos (by omega : 1 ≤ m + 1), Nat.add_sub_cancel, coeff_sq_zmod2]
    by_cases hev : Even m
    · rw [if_pos hev, coeff_C0]
      have hiff : (∃ k : ℕ, m + 1 + 1 = 2 ^ k) ↔ (∃ k : ℕ, m / 2 + 1 = 2 ^ k) := by
        rcases hev with ⟨j, rfl⟩
        have hdiv : (j + j) / 2 = j := by omega
        rw [hdiv]
        constructor
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k' => exact ⟨k', by rw [pow_succ'] at hk; omega⟩
        · rintro ⟨k, hk⟩
          exact ⟨k + 1, by rw [pow_succ']; omega⟩
      by_cases h : ∃ k : ℕ, m + 1 + 1 = 2 ^ k
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
    · rw [if_neg hev]
      have hnot : ¬ ∃ k : ℕ, m + 1 + 1 = 2 ^ k := by
        rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk
        | succ k' => exact hev ⟨2 ^ k' - 1, by rw [pow_succ'] at hk; have := Nat.one_le_pow k' 2 (by decide); omega⟩
      rw [if_neg hnot]

private lemma C0_mul_B0 : C0 * B0 = 1 := by
  have h1 : B0 = 1 + PowerSeries.X * C0 := by rw [B0, X_mul_C0_eq_u0]
  rw [h1, mul_add, mul_one]
  calc C0 + C0 * (PowerSeries.X * C0) = C0 + PowerSeries.X * C0 ^ 2 := by ring
    _ = (1 + PowerSeries.X * C0 ^ 2) + PowerSeries.X * C0 ^ 2 := congrArg (· + PowerSeries.X * C0 ^ 2) C0_quad
    _ = 1 + (PowerSeries.X * C0 ^ 2 + PowerSeries.X * C0 ^ 2) := by ring
    _ = 1 + 0 := by rw [zmod2_ps_add_self]
    _ = 1 := by ring

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

private lemma choose_nsq_even (n : ℕ) (hn : 2 ≤ n) :
    (Nat.choose (n ^ 2 - n - 2) (n - 1) : ZMod 2) = 0 := by
  set k := n - 1
  have hk : 1 ≤ k := by omega
  have hM_eq : n ^ 2 - n - 2 = k * k + k - 2 := by
    have hnk : n = k + 1 := by omega
    rw [hnk]
    have hsq : (k + 1) ^ 2 = k * k + 2 * k + 1 := by ring
    rw [hsq]; omega
  rw [hM_eq]
  by_cases hodd : k % 2 = 1
  · refine choose_even_of_bit (v := 0) (by simpa using hodd) ?_
    simp only [pow_zero, Nat.div_one]
    have hkk : (k * k + k) % 2 = 0 := by
      rw [Nat.add_mod, Nat.mul_mod, hodd]
    have hge2 : 2 ≤ k * k + k := by nlinarith
    omega
  · have hev : k % 2 = 0 := by omega
    -- Write k = 2^v * u with v ≥ 1 and u odd
    have hex : ∃ v u : ℕ, 1 ≤ v ∧ k = 2 ^ v * u ∧ u % 2 = 1 := by
      have haux : ∀ m : ℕ, 1 ≤ m → ∃ v u : ℕ, m = 2 ^ v * u ∧ u % 2 = 1 := by
        intro m
        induction m using Nat.strongRecOn with
        | ind m ihm =>
          intro hm
          by_cases h2 : m % 2 = 0
          · obtain ⟨v, u, heq, hu⟩ := ihm (m / 2) (by omega) (by omega)
            refine ⟨v + 1, u, ?_, hu⟩
            rw [pow_succ', mul_assoc, ← heq]; omega
          · exact ⟨0, m, by simp, by omega⟩
      obtain ⟨v, u, heq, hu⟩ := haux k hk
      have hv1 : 1 ≤ v := by
        rcases Nat.eq_zero_or_pos v with rfl | hpos
        · simp at heq; omega
        · exact hpos
      exact ⟨v, u, hv1, heq, hu⟩
    obtain ⟨v, u, hv1, hkeq, huodd⟩ := hex
    have hKbit : (k / 2 ^ v) % 2 = 1 := by
      rw [hkeq, Nat.mul_div_cancel_left u (pow_pos (by decide) v)]
      exact huodd
    by_cases hv_eq1 : v = 1
    · -- v = 1: k = 2*u with u odd, so k^2 + k - 2 = 4*u^2 + 2*u - 2 ≡ 4 (mod 8),
      --Wait: k^2 + k - 2 = 4*(u^2) + 2*(u - 1) = 4*(u^2 + (u-1)/2) is divisible by 4!
      -- So (k^2 + k - 2) / 2 is EVEN, i.e., bit v=1 is 0!
      subst hv_eq1
      refine choose_even_of_bit (v := 1) hKbit ?_
      rw [pow_one, hkeq, pow_one]
      have hu1 : 1 ≤ u := by omega
      have hcalc : (2 * u * (2 * u) + 2 * u - 2) / 2 = 2 * (u * u) + (u - 1) := by
        have hmul : 2 * u * (2 * u) + 2 * u - 2 = 2 * (2 * (u * u) + (u - 1)) := by
          have : 2 * u * (2 * u) = 4 * (u * u) := by ring
          omega
        rw [hmul, Nat.mul_div_cancel_left _ (by decide)]
      rw [hcalc]
      omega
    · have hv2 : 2 ≤ v := by omega
      refine choose_even_of_bit (v := v) hKbit ?_
      have h2v_pos : 0 < 2 ^ v := pow_pos (by decide) v
      have h2v_ge4 : 4 ≤ 2 ^ v := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hv2
      have hk2_dvd : 2 ^ (v + 1) ∣ k * k := by
        rw [hkeq]
        have h1 : 2 ^ (v + 1) ∣ 2 ^ v * 2 ^ v := by
          rw [← pow_add]; exact Nat.pow_dvd_pow 2 (by omega)
        have h2 : 2 ^ v * u * (2 ^ v * u) = (2 ^ v * 2 ^ v) * (u * u) := by ring
        rw [h2]
        exact dvd_mul_of_dvd_left h1 _
      obtain ⟨q, hq⟩ := hk2_dvd
      have hu1 : 1 ≤ u := by omega
      have hsplit : k * k + k - 2 = 2 ^ v * (2 * q + (u - 1)) + (2 ^ v - 2) := by
        have hq2 : 2 ^ (v + 1) * q = 2 ^ v * (2 * q) := by rw [pow_succ]; ring
        have hku : k = 2 ^ v * (u - 1) + 2 ^ v := by
          have hu_eq : u = (u - 1) + 1 := by omega
          calc k = 2 ^ v * u := hkeq
            _ = 2 ^ v * ((u - 1) + 1) := congrArg (2 ^ v * ·) hu_eq
            _ = 2 ^ v * (u - 1) + 2 ^ v := by ring
        have hsum : k * k + k = 2 ^ v * (2 * q + (u - 1)) + 2 ^ v := by
          rw [hq, hq2, hku]; ring
        omega
      rw [hsplit, Nat.mul_add_div h2v_pos, Nat.div_eq_of_lt (by omega : 2 ^ v - 2 < 2 ^ v), add_zero]
      omega

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

private theorem prove_main : type_of% @OMA.S_oeis_a397356.main := by
  classical
  intro A hA0 hA1 hEq
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  set B : PowerSeries ℤ := Ring.inverse A
  have hA_unit : IsUnit A := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hA0]; exact isUnit_one)
  have hAB : A * B = 1 := Ring.mul_inverse_cancel A hA_unit
  set a2 : PowerSeries (ZMod 2) := φ A
  set b2 : PowerSeries (ZMod 2) := φ B
  have ha2b2 : a2 * b2 = 1 := by
    have := congrArg φ hAB
    rwa [map_mul, map_one] at this
  have hb2_0 : PowerSeries.constantCoeff b2 = 1 := by
    have h0 := congrArg PowerSeries.constantCoeff ha2b2
    rw [map_mul, map_one] at h0
    have ha2_0 : PowerSeries.constantCoeff a2 = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
    rwa [ha2_0, one_mul] at h0
  have hb2_1 : PowerSeries.coeff 1 b2 = 1 := by
    have h1 := congrArg (PowerSeries.coeff 1) ha2b2
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i a2 * PowerSeries.coeff j b2),
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h1
    simp only [Nat.sub_zero, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_one, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte] at h1
    have ha2_0 : PowerSeries.constantCoeff a2 = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
    have ha2_1 : PowerSeries.coeff 1 a2 = 1 := by rw [PowerSeries.coeff_map, hA1, map_one]
    rw [ha2_0, ha2_1, hb2_0, one_mul, mul_one] at h1
    generalize PowerSeries.coeff 1 b2 = x at h1 ⊢
    revert x h1; decide
  have hB0_1 : PowerSeries.coeff 1 B0 = 1 := by
    rw [coeff_B0 1 (by omega), if_pos ⟨0, by norm_num⟩]
  have hb2_eq : ∀ n : ℕ, 1 < n →
      PowerSeries.coeff n (b2 ^ (n ^ 2)) = PowerSeries.coeff n (b2 ^ (n ^ 2 - 1)) := by
    intro n hn
    have h := congrArg (Int.castRingHom (ZMod 2)) (hEq n hn)
    simp only [← PowerSeries.coeff_map, map_pow] at h
    exact h
  have hB0_eq : ∀ n : ℕ, 1 < n →
      PowerSeries.coeff n (B0 ^ (n ^ 2)) = PowerSeries.coeff n (B0 ^ (n ^ 2 - 1)) := by
    intro n hn
    have hsq : n + 2 ≤ n ^ 2 := by nlinarith
    have hle1 : n + 1 ≤ n ^ 2 - 1 := by omega
    rw [coeff_B0_pow (n ^ 2) n (by omega), coeff_B0_pow (n ^ 2 - 1) n hle1]
    have hpas : Nat.choose (n ^ 2 - n - 1) n =
        Nat.choose (n ^ 2 - 1 - n - 1) (n - 1) + Nat.choose (n ^ 2 - 1 - n - 1) n := by
      have h1 := Nat.choose_succ_succ (n ^ 2 - 1 - n - 1) (n - 1)
      simp only [Nat.succ_eq_add_one] at h1
      rw [show (n ^ 2 - 1 - n - 1) + 1 = n ^ 2 - n - 1 by omega,
          show (n - 1) + 1 = n by omega] at h1
      exact h1
    rw [hpas, Nat.cast_add]
    have h0 : (Nat.choose (n ^ 2 - 1 - n - 1) (n - 1) : ZMod 2) = 0 := by
      rw [show n ^ 2 - 1 - n - 1 = n ^ 2 - n - 2 by omega]
      exact choose_nsq_even n (by omega)
    rw [h0, zero_add]
  have hb2_eq_B0 : b2 = B0 := by
    ext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | n'
      · rw [PowerSeries.coeff_zero_eq_constantCoeff, hb2_0, B0_const]
      · rw [hb2_1, hB0_1]
      · set m := n' + 2
        have h1 := coeff_pow_diff_of_agree hb2_0 B0_const ih (m ^ 2)
        have h2 := coeff_pow_diff_of_agree hb2_0 B0_const ih (m ^ 2 - 1)
        have hrelB := hb2_eq m (by omega)
        have hrelB0 := hB0_eq m (by omega)
        have hsum0 : (PowerSeries.coeff m (b2 ^ (m ^ 2)) + PowerSeries.coeff m (B0 ^ (m ^ 2))) +
            (PowerSeries.coeff m (b2 ^ (m ^ 2 - 1)) + PowerSeries.coeff m (B0 ^ (m ^ 2 - 1))) = 0 := by
          rw [hrelB, hrelB0]
          generalize PowerSeries.coeff m (b2 ^ (m ^ 2 - 1)) + PowerSeries.coeff m (B0 ^ (m ^ 2 - 1)) = x
          revert x; decide
        rw [h1, h2] at hsum0
        have hcoef1 : ((m ^ 2 : ℕ) : ZMod 2) + ((m ^ 2 - 1 : ℕ) : ZMod 2) = 1 := by
          have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m (by omega)
          have : m ^ 2 = (m ^ 2 - 1) + 1 := by omega
          conv_lhs => rw [this]
          push_cast
          generalize ((m ^ 2 - 1 : ℕ) : ZMod 2) = x; revert x; decide
        have hc0 : PowerSeries.coeff m b2 + PowerSeries.coeff m B0 = 0 := by
          calc PowerSeries.coeff m b2 + PowerSeries.coeff m B0
              = 1 * (PowerSeries.coeff m b2 + PowerSeries.coeff m B0) := by ring
            _ = (((m ^ 2 : ℕ) : ZMod 2) + ((m ^ 2 - 1 : ℕ) : ZMod 2)) *
                (PowerSeries.coeff m b2 + PowerSeries.coeff m B0) := by rw [hcoef1]
            _ = ((m ^ 2 : ℕ) : ZMod 2) * (PowerSeries.coeff m b2 + PowerSeries.coeff m B0) +
                ((m ^ 2 - 1 : ℕ) : ZMod 2) * (PowerSeries.coeff m b2 + PowerSeries.coeff m B0) := by ring
            _ = 0 := hsum0
        have heq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
        exact heq _ _ hc0
  have ha2_eq_C0 : a2 = C0 := by
    calc a2 = a2 * 1 := (mul_one a2).symm
      _ = a2 * (B0 * C0) := by rw [mul_comm B0 C0, C0_mul_B0]
      _ = (a2 * b2) * C0 := by rw [← hb2_eq_B0, mul_assoc]
      _ = 1 * C0 := by rw [ha2b2]
      _ = C0 := one_mul C0
  intro n
  rw [odd_iff_zmod2_eq_one]
  have hc : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = PowerSeries.coeff n C0 := by
    rw [← ha2_eq_C0, PowerSeries.coeff_map]; rfl
  rw [hc, coeff_C0 n]
  by_cases h : ∃ k : ℕ, n + 1 = 2 ^ k
  · simp [h]
  · simp [h]

end OMA.P_oeis_a397356

theorem OMA.solution : type_of% @OMA.S_oeis_a397356.main :=
  OMA.P_oeis_a397356.prove_main
