import OMAStatements.S_oeis_a294359
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic

namespace OMA.P_oeis_a294359

open OMA.S_oeis_a294359

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

private lemma coeff_pow4_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 4) = if 4 ∣ n then PowerSeries.coeff (n / 4) f else 0 := by
  have h4 : f ^ 4 = (f ^ 2) ^ 2 := by ring
  rw [h4, coeff_sq_zmod2]
  by_cases h2 : Even n
  · rw [if_pos h2, coeff_sq_zmod2]
    by_cases h4d : 4 ∣ n
    · rw [if_pos h4d]
      have hev2 : Even (n / 2) := by rcases h4d with ⟨q, rfl⟩; exact ⟨q, by omega⟩
      rw [if_pos hev2, show n / 2 / 2 = n / 4 by omega]
    · rw [if_neg h4d]
      have hnev2 : ¬ Even (n / 2) := by
        rintro ⟨q, hq⟩; exact h4d ⟨q, by rcases h2 with ⟨m, rfl⟩; omega⟩
      rw [if_neg hnev2]
  · rw [if_neg h2]
    have h4nd : ¬ 4 ∣ n := by rintro ⟨q, rfl⟩; exact h2 ⟨2 * q, by omega⟩
    rw [if_neg h4nd]

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

private lemma coeff_subst_eq_sum {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) (F : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst g F) =
      ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F * PowerSeries.coeff n (g ^ d) := by
  have hg : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero hg0
  rw [PowerSeries.coeff_subst' hg]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support, ne_eq] at hd
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hge
  exact hd (by rw [coeff_pow_eq_zero_of_lt hg0 (by omega), mul_zero])

private lemma coeff_subst_X_pow {R : Type*} [CommRing R] (k : ℕ) (hk : 1 ≤ k)
    (F : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst (PowerSeries.X ^ k) F) =
      if k ∣ n then PowerSeries.coeff (n / k) F else 0 := by
  have hX0 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries R) ^ k) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]
  rw [coeff_subst_eq_sum hX0]
  by_cases hdiv : k ∣ n
  · rw [if_pos hdiv]
    rcases hdiv with ⟨q, rfl⟩
    rw [Nat.mul_div_cancel_left q (by omega)]
    rw [Finset.sum_eq_single q]
    · rw [← pow_mul, mul_comm k q, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
    · intro d _ hne
      rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg (by intro h; apply hne; nlinarith), mul_zero]
    · intro h
      have hle : q ≤ k * q := Nat.le_mul_of_pos_left q (by omega)
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hdiv]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg (by intro h; exact hdiv ⟨d, h⟩), mul_zero]

private lemma subst_XX3_of_cubic {u : PowerSeries (ZMod 2)}
    (hu0 : PowerSeries.constantCoeff u = 0)
    (huc : u + u ^ 3 = (PowerSeries.X : PowerSeries (ZMod 2))) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries (ZMod 2)) + PowerSeries.X ^ 3) u =
      PowerSeries.X := by
  set S : PowerSeries (ZMod 2) := PowerSeries.X + PowerSeries.X ^ 3
  have hS0 : PowerSeries.constantCoeff S = 0 := by
    rw [map_add, map_pow, PowerSeries.constantCoeff_X]; norm_num
  have hSub : PowerSeries.HasSubst S := PowerSeries.HasSubst.of_constantCoeff_zero hS0
  set Y : PowerSeries (ZMod 2) := PowerSeries.subst S u
  have hY0 : PowerSeries.constantCoeff Y = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst_eq_sum hS0]
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hu0]
  have hYc : Y + Y ^ 3 = S := by
    have hs := congrArg (PowerSeries.subst S) huc
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

private lemma coeff_one_add_X_pow (m k : ℕ) :
    PowerSeries.coeff k (((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ m) =
      (Nat.choose m k : ZMod 2) := by
  induction m generalizing k with
  | zero =>
    simp only [pow_zero, PowerSeries.coeff_one]
    cases k with
    | zero => simp
    | succ k' => simp
  | succ m ih =>
    rw [pow_succ, mul_add, mul_one, map_add, ih]
    have hXmul : ((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ m * PowerSeries.X =
        PowerSeries.X ^ 1 * ((1 : PowerSeries (ZMod 2)) + PowerSeries.X) ^ m := by ring
    rw [hXmul, PowerSeries.coeff_X_pow_mul']
    cases k with
    | zero => simp
    | succ k' =>
      rw [if_pos (by omega), Nat.add_sub_cancel, ih, Nat.choose_succ_succ, Nat.cast_add, add_comm]

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

private lemma choose_sq_add_one_even (n : ℕ) (hn : 1 ≤ n) :
    (Nat.choose (n ^ 2 + 1) n : ZMod 2) = 0 := by
  by_cases hodd : n % 2 = 1
  · refine choose_even_of_bit (v := 0) (by simpa using hodd) ?_
    simp only [pow_zero, Nat.div_one]
    rw [sq, Nat.add_mod, Nat.mul_mod, hodd]
  · have hex : ∃ v u : ℕ, 1 ≤ v ∧ n = 2 ^ v * u ∧ u % 2 = 1 := by
      have haux : ∀ m : ℕ, 1 ≤ m → ∃ v u : ℕ, m = 2 ^ v * u ∧ u % 2 = 1 := by
        intro m
        induction m using Nat.strongRecOn with
        | ind m ihm =>
          intro hm
          by_cases h2 : m % 2 = 0
          · obtain ⟨v, u, heq, hu⟩ := ihm (m / 2) (by omega) (by omega)
            exact ⟨v + 1, u, by rw [pow_succ', mul_assoc, ← heq]; omega, hu⟩
          · exact ⟨0, m, by simp, by omega⟩
      obtain ⟨v, u, heq, hu⟩ := haux n hn
      have hv1 : 1 ≤ v := by
        rcases Nat.eq_zero_or_pos v with rfl | hpos
        · simp at heq; omega
        · exact hpos
      exact ⟨v, u, hv1, heq, hu⟩
    obtain ⟨v, u, hv1, hneq, huodd⟩ := hex
    have h2v_pos : 0 < 2 ^ v := pow_pos (by decide) v
    have h2v_ge2 : 2 ≤ 2 ^ v := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hv1
    refine choose_even_of_bit (v := v) ?_ ?_
    · rw [hneq, Nat.mul_div_cancel_left u h2v_pos]; exact huodd
    · have h2v_even : 2 ∣ 2 ^ v := dvd_pow_self 2 (by omega)
      rcases h2v_even with ⟨q, hq⟩
      have hsq : n ^ 2 + 1 = 2 ^ v * (2 * q * u ^ 2) + 1 := by
        rw [hneq, hq]; ring
      rw [hsq, Nat.mul_add_div h2v_pos, Nat.div_eq_of_lt (by omega : 1 < 2 ^ v), add_zero,
          mul_assoc 2 q (u ^ 2)]
      exact Nat.mul_mod_right 2 (q * u ^ 2)

private lemma even_of_zmod2_eq_zero (z : ℤ) (h : (z : ZMod 2) = 0) : Even z := by
  rcases Int.even_or_odd z with hev | ⟨k, rfl⟩
  · exact hev
  · push_cast at h
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add] at h
    exact absurd h (by decide)

theorem solution : type_of% @OMA.S_oeis_a294359.main := by
  intro F hF0 hFeq
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let B : PowerSeries ℤ := Ring.inverse F
  have hF_unit : IsUnit F := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hF0]; exact isUnit_one)
  have hFB : F * B = 1 := Ring.mul_inverse_cancel F hF_unit
  let f2 : PowerSeries (ZMod 2) := φ F
  let b2 : PowerSeries (ZMod 2) := φ B
  have hf2b2 : f2 * b2 = 1 := by
    dsimp only [f2, b2]; rw [← map_mul, hFB, map_one]
  have hf2_0 : PowerSeries.constantCoeff f2 = 1 := by
    dsimp only [f2, φ]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, hF0, map_one]
  have hb2_0 : PowerSeries.constantCoeff b2 = 1 := by
    have h := congrArg PowerSeries.constantCoeff hf2b2
    rw [map_mul, hf2_0, one_mul, map_one] at h; exact h
  have hsub2 : φ (PowerSeries.subst (PowerSeries.X ^ 2) F) = f2 ^ 2 := by
    ext n
    dsimp only [f2, φ]
    rw [PowerSeries.coeff_map, coeff_subst_X_pow 2 (by decide), coeff_sq_zmod2]
    have hev_iff : (2 ∣ n) ↔ Even n := even_iff_two_dvd.symm
    by_cases h2 : 2 ∣ n
    · rw [if_pos h2, if_pos (hev_iff.mp h2), PowerSeries.coeff_map]
    · rw [if_neg h2, if_neg (fun h => h2 (hev_iff.mpr h)), map_zero]
  have hsub4 : φ (PowerSeries.subst (PowerSeries.X ^ 4) F) = f2 ^ 4 := by
    ext n
    dsimp only [f2, φ]
    rw [PowerSeries.coeff_map, coeff_subst_X_pow 4 (by decide), coeff_pow4_zmod2]
    by_cases h4 : 4 ∣ n
    · rw [if_pos h4, if_pos h4, PowerSeries.coeff_map]
    · rw [if_neg h4, if_neg h4, map_zero]
  have hf2_eq : f2 = f2 ^ 2 + PowerSeries.X * f2 ^ 4 := by
    have h := congrArg φ hFeq
    rw [map_add, map_mul, PowerSeries.map_X, hsub2, hsub4] at h
    exact h
  have hb2_eq : b2 ^ 3 + b2 ^ 2 = PowerSeries.X := by
    have h1 : f2 * b2 ^ 4 = f2 ^ 2 * b2 ^ 4 + PowerSeries.X * (f2 * b2) ^ 4 := by
      conv_lhs => rw [hf2_eq]
      ring
    rw [hf2b2, one_pow, mul_one] at h1
    have h2 : b2 ^ 3 = b2 ^ 2 + PowerSeries.X := by
      calc b2 ^ 3 = (f2 * b2) * b2 ^ 3 := by rw [hf2b2, one_mul]
        _ = f2 * b2 ^ 4 := by ring
        _ = f2 ^ 2 * b2 ^ 4 + PowerSeries.X := h1
        _ = (f2 * b2) ^ 2 * b2 ^ 2 + PowerSeries.X := by ring
        _ = b2 ^ 2 + PowerSeries.X := by rw [hf2b2, one_pow, one_mul]
    calc b2 ^ 3 + b2 ^ 2 = (b2 ^ 2 + PowerSeries.X) + b2 ^ 2 := by rw [h2]
      _ = (b2 ^ 2 + b2 ^ 2) + PowerSeries.X := by ring
      _ = 0 + PowerSeries.X := by rw [zmod2_ps_add_self]
      _ = PowerSeries.X := zero_add _
  let u : PowerSeries (ZMod 2) := 1 + b2
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    dsimp only [u]; rw [map_add, map_one, hb2_0]; decide
  have huc : u + u ^ 3 = PowerSeries.X := by
    dsimp only [u]
    have h2 := zmod2_ps_two
    calc (1 + b2) + (1 + b2) ^ 3
        = (b2 ^ 3 + b2 ^ 2) + 2 * (1 + 2 * b2 + b2 ^ 2) := by ring
      _ = b2 ^ 3 + b2 ^ 2 := by rw [h2, zero_mul, add_zero]
      _ = PowerSeries.X := hb2_eq
  have hb2_1u : b2 = 1 + u := by
    dsimp only [u]; rw [← add_assoc, zmod2_ps_add_self, zero_add]
  intro n hn
  apply even_of_zmod2_eq_zero
  have hc : ((PowerSeries.coeff n (B ^ ((n + 1) ^ 2)) : ℤ) : ZMod 2) =
      PowerSeries.coeff n (b2 ^ ((n + 1) ^ 2)) := by
    change Int.castRingHom (ZMod 2) (PowerSeries.coeff n (B ^ ((n + 1) ^ 2))) = _
    dsimp only [b2, φ]; rw [← PowerSeries.coeff_map, map_pow]
  rw [hc, ← lagrange_cubic_zmod2 (b2 ^ ((n + 1) ^ 2)) n]
  set S : PowerSeries (ZMod 2) := PowerSeries.X + PowerSeries.X ^ 3
  have hS0 : PowerSeries.constantCoeff S = 0 := by
    dsimp only [S]; rw [map_add, map_pow, PowerSeries.constantCoeff_X]; norm_num
  have hSub : PowerSeries.HasSubst S := PowerSeries.HasSubst.of_constantCoeff_zero hS0
  have h1s : PowerSeries.subst S (1 : PowerSeries (ZMod 2)) = 1 := by
    change PowerSeries.subst _ (PowerSeries.C 1) = 1; rw [PowerSeries.subst_C]; rfl
  have hsub_b : PowerSeries.subst S (b2 ^ ((n + 1) ^ 2)) = (1 + PowerSeries.X) ^ ((n + 1) ^ 2) := by
    rw [PowerSeries.subst_pow hSub, hb2_1u, PowerSeries.subst_add hSub, h1s,
        subst_XX3_of_cubic hu0 huc]
  rw [hsub_b]
  have hcancel : (1 + PowerSeries.X) ^ ((n + 1) ^ 2) * inv1X ^ (2 * n) =
      (1 + PowerSeries.X) ^ (n ^ 2 + 1) := by
    have hexp : (n + 1) ^ 2 = (n ^ 2 + 1) + 2 * n := by ring
    rw [hexp, pow_add, mul_assoc, ← mul_pow, one_add_X_mul_inv1X, one_pow, mul_one]
  rw [hcancel, coeff_one_add_X_pow]
  exact choose_sq_add_one_even n hn

end OMA.P_oeis_a294359

theorem OMA.solution : type_of% @OMA.S_oeis_a294359.main := OMA.P_oeis_a294359.solution
