import OMAStatements.S_oeis_a338635
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a338635

open OMA.S_oeis_a338635

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
  intro h
  have h0 := h 0
  simp at h0

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
  | zero =>
    rw [if_neg (by omega), if_neg (by rintro ⟨m, _, hm⟩; omega)]
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
      rintro ⟨m, _, hm⟩
      exact hev ⟨m, by omega⟩

private lemma u0_const : PowerSeries.constantCoeff u0 = 0 := by
  simp [u0, map_mul]

private lemma u0_cubic : u0 + u0 ^ 3 = (PowerSeries.X : PowerSeries (ZMod 2)) := by
  have hsq : Ffib ^ 2 + PowerSeries.X ^ 2 * Ffib ^ 6 = 1 := by
    have h := congrArg (· ^ 2) Ffib_cubic
    rw [zmod2_ps_add_sq, mul_pow, one_pow] at h
    calc Ffib ^ 2 + PowerSeries.X ^ 2 * Ffib ^ 6 = Ffib ^ 2 + PowerSeries.X ^ 2 * (Ffib ^ 3) ^ 2 := by ring
      _ = 1 := h
  calc u0 + u0 ^ 3 = PowerSeries.X * (Ffib ^ 2 + PowerSeries.X ^ 2 * Ffib ^ 6) := by dsimp only [u0]; ring
    _ = PowerSeries.X * 1 := by rw [hsq]
    _ = PowerSeries.X := mul_one _

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

private theorem prove_main : type_of% @OMA.S_oeis_a338635.main := by
  classical
  intro A hA0 hCF
  obtain ⟨R, hR0, hRk⟩ := hCF
  let φ := PowerSeries.map (Int.castRingHom (ZMod 2))
  set a2 : PowerSeries (ZMod 2) := φ A
  have ha2_0 : PowerSeries.constantCoeff a2 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
  -- Reduce k = 1: R 1 * (A - 6 * X * R 2) = 1 => φ (R 1) * a2 = 1
  have hR1_mul : φ (R 1) * a2 = 1 := by
    have h1 := congrArg φ (hRk 1)
    have h6 : φ ((((1 + 2) * (1 + 3) / 2 : ℕ) : PowerSeries ℤ)) = 0 := by
      have h6c : ((((1 + 2) * (1 + 3) / 2 : ℕ) : PowerSeries ℤ)) = PowerSeries.C (6 : ℤ) := by norm_num
      rw [h6c, PowerSeries.map_C]
      have h6z : (Int.castRingHom (ZMod 2)) 6 = 0 := by decide
      rw [h6z, map_zero]
    rw [map_mul, map_sub, map_mul, map_mul, h6, zero_mul, zero_mul, sub_zero, map_one] at h1
    exact h1
  -- Reduce k = 0: R 0 * (A - 3 * X * R 1) = 1 => φ (R 0) * (a2 + X * φ (R 1)) = 1
  have hR0_mul : φ (R 0) * (a2 + PowerSeries.X * φ (R 1)) = 1 := by
    have h0 := congrArg φ (hRk 0)
    have h3 : φ ((((0 + 2) * (0 + 3) / 2 : ℕ) : PowerSeries ℤ)) = 1 := by
      have h3c : ((((0 + 2) * (0 + 3) / 2 : ℕ) : PowerSeries ℤ)) = PowerSeries.C (3 : ℤ) := by norm_num
      rw [h3c, PowerSeries.map_C]
      have h3z : (Int.castRingHom (ZMod 2)) 3 = 1 := by decide
      rw [h3z, map_one]
    have hX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
    rw [map_mul, map_sub, map_mul, map_mul, h3, one_mul, zmod2_ps_sub, map_one, hX] at h0
    exact h0
  -- Reduce A - 1 = X * R 0 => a2 + 1 = X * φ (R 0)
  have ha2_sub : a2 + 1 = PowerSeries.X * φ (R 0) := by
    have h := congrArg φ hR0
    have hX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
    rw [map_sub, map_one, map_mul, zmod2_ps_sub, hX] at h
    exact h
  -- Eliminate R 0 and R 1: (a2 + 1) * a2^2 = X, i.e., u + u^3 = X where u = a2 + 1!
  set u : PowerSeries (ZMod 2) := a2 + 1
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    dsimp only [u]; rw [map_add, ha2_0, map_one]; decide
  have hu_cubic : u + u ^ 3 = PowerSeries.X := by
    have h1 : (a2 + 1) * (a2 ^ 2 + PowerSeries.X) = PowerSeries.X * a2 := by
      calc (a2 + 1) * (a2 ^ 2 + PowerSeries.X)
          = (a2 + 1) * (a2 * a2 + PowerSeries.X * (φ (R 1) * a2)) := by rw [hR1_mul, mul_one]; ring
        _ = ((a2 + 1) * (a2 + PowerSeries.X * φ (R 1))) * a2 := by ring
        _ = (u * (a2 + PowerSeries.X * φ (R 1))) * a2 := rfl
        _ = ((PowerSeries.X * φ (R 0)) * (a2 + PowerSeries.X * φ (R 1))) * a2 := by rw [ha2_sub]
        _ = (PowerSeries.X * (φ (R 0) * (a2 + PowerSeries.X * φ (R 1)))) * a2 := by ring
        _ = (PowerSeries.X * 1) * a2 := by rw [hR0_mul]
        _ = PowerSeries.X * a2 := by ring
    have h2 : (a2 + 1) * a2 ^ 2 = PowerSeries.X := by
      have hexp : (a2 + 1) * (a2 ^ 2 + PowerSeries.X) = (a2 + 1) * a2 ^ 2 + PowerSeries.X * a2 + PowerSeries.X := by ring
      rw [hexp] at h1
      have := congrArg (· + (PowerSeries.X * a2 + PowerSeries.X)) h1
      calc (a2 + 1) * a2 ^ 2
          = ((a2 + 1) * a2 ^ 2 + PowerSeries.X * a2 + PowerSeries.X) + (PowerSeries.X * a2 + PowerSeries.X) := by
            have hza := zmod2_ps_add_self (PowerSeries.X * a2 + PowerSeries.X)
            calc (a2 + 1) * a2 ^ 2 = (a2 + 1) * a2 ^ 2 + 0 := (add_zero _).symm
              _ = (a2 + 1) * a2 ^ 2 + ((PowerSeries.X * a2 + PowerSeries.X) + (PowerSeries.X * a2 + PowerSeries.X)) := by rw [hza]
              _ = _ := by ring
        _ = PowerSeries.X * a2 + (PowerSeries.X * a2 + PowerSeries.X) := this
        _ = (PowerSeries.X * a2 + PowerSeries.X * a2) + PowerSeries.X := by ring
        _ = 0 + PowerSeries.X := by rw [zmod2_ps_add_self]
        _ = PowerSeries.X := zero_add _
    have ha2_eq : a2 = u + 1 := by dsimp only [u]; rw [add_assoc, zmod2_ps_add_self, add_zero]
    rw [← h2, ha2_eq, zmod2_ps_add_sq, one_pow]
    calc u + u ^ 3 = u * (u ^ 2 + 1) := by ring
      _ = (u + 1 + 1) * (u ^ 2 + 1) := by rw [add_assoc, zmod2_ps_add_self, add_zero]
  -- Uniqueness: (u + u0) = (u + u0) * (u^2 + u*u0 + u0^2) with constantCoeff 0 => u = u0!
  have hu_eq : u = u0 := by
    have hdiff : u + u0 = u ^ 3 + u0 ^ 3 := by
      have hadd : (u + u ^ 3) + (u0 + u0 ^ 3) = PowerSeries.X + PowerSeries.X := by rw [hu_cubic, u0_cubic]
      rw [zmod2_ps_add_self] at hadd
      have := congrArg (· + (u ^ 3 + u0 ^ 3)) hadd
      calc u + u0 = (u + u0) + 0 := (add_zero _).symm
        _ = (u + u0) + ((u ^ 3 + u0 ^ 3) + (u ^ 3 + u0 ^ 3)) := by rw [zmod2_ps_add_self]
        _ = ((u + u ^ 3) + (u0 + u0 ^ 3)) + (u ^ 3 + u0 ^ 3) := by ring
        _ = 0 + (u ^ 3 + u0 ^ 3) := this
        _ = u ^ 3 + u0 ^ 3 := zero_add _
    have hfac : u + u0 = (u + u0) * (u ^ 2 + u * u0 + u0 ^ 2) := by
      conv_lhs => rw [hdiff]
      have h2 : ∀ f : PowerSeries (ZMod 2), f + f = 0 := zmod2_ps_add_self
      calc u ^ 3 + u0 ^ 3
          = u ^ 3 + u0 ^ 3 + (u ^ 2 * u0 + u ^ 2 * u0) + (u * u0 ^ 2 + u * u0 ^ 2) := by rw [h2, h2]; ring
        _ = (u + u0) * (u ^ 2 + u * u0 + u0 ^ 2) := by ring
    have hconst : PowerSeries.constantCoeff (u ^ 2 + u * u0 + u0 ^ 2) = 0 := by
      rw [map_add, map_add, map_pow, map_mul, map_pow, hu0, u0_const]; simp
    have hzero : ∀ n, PowerSeries.coeff n (u + u0) = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        cases n with
        | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff, map_add, hu0, u0_const, add_zero]
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
  intro n hn
  rw [odd_iff_zmod2_eq_one]
  have hc : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = PowerSeries.coeff n u0 := by
    rw [← hu_eq]
    dsimp only [u]
    rw [map_add, PowerSeries.coeff_one, if_neg (by omega), add_zero, PowerSeries.coeff_map]
    rfl
  rw [hc, coeff_u0]
  by_cases h : ∃ m : ℕ, isFibbinary m ∧ n = 2 * m + 1
  · simp [h]
  · simp [h]

end OMA.P_oeis_a338635

theorem OMA.solution : type_of% @OMA.S_oeis_a338635.main :=
  OMA.P_oeis_a338635.prove_main
