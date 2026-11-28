import OMAStatements.S_oeis_a369083
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic

namespace OMA.P_oeis_a369083

open OMA.S_oeis_a369083

private lemma zmod2_ps_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

private lemma zmod2_ps_add_self (f : PowerSeries (ZMod 2)) : f + f = 0 := by
  rw [← two_mul, zmod2_ps_two, zero_mul]

private lemma coeff_sq_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 2) = if n % 2 = 0 then PowerSeries.coeff (n / 2) f else 0 := by
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
  change ∑ i ∈ Finset.range (n + 1), t i = _
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2]
  have hLR : ∑ i ∈ L, t i = ∑ i ∈ R, t i := by
    refine Finset.sum_bij (fun i _ => n - i) ?_ ?_ ?_ ?_
    · intro i hi; simp only [L, R, Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
    · intro i hi j hj hij; simp only [L, Finset.mem_filter, Finset.mem_range] at hi hj; omega
    · intro j hj; simp only [L, R, Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨n - j, ⟨by omega, by omega⟩, by omega⟩
    · intro i hi; simp only [L, Finset.mem_filter, Finset.mem_range] at hi
      exact (hsym i (by omega)).symm
  rw [← add_assoc, hLR, show ∀ x : ZMod 2, x + x = 0 from fun x => by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul], zero_add]
  by_cases hev : n % 2 = 0
  · rw [if_pos hev]
    have hM : M = {n / 2} := by
      ext i; simp only [M, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
    rw [hM, Finset.sum_singleton]
    dsimp only [t]
    rw [show n - n / 2 = n / 2 by omega]
    have hsq : ∀ x : ZMod 2, x * x = x := by decide
    exact hsq _
  · rw [if_neg hev]
    have hM : M = ∅ := by
      ext i; simp only [M, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      omega
    rw [hM, Finset.sum_empty]

private lemma coeff_pow4_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 4) = if n % 4 = 0 then PowerSeries.coeff (n / 4) f else 0 := by
  rw [show f ^ 4 = (f ^ 2) ^ 2 by ring, coeff_sq_zmod2]
  by_cases h2 : n % 2 = 0
  · rw [if_pos h2, coeff_sq_zmod2]
    by_cases h4 : n % 4 = 0
    · rw [if_pos h4, if_pos (by omega), show n / 2 / 2 = n / 4 by omega]
    · rw [if_neg h4, if_neg (by omega)]
  · rw [if_neg h2, if_neg (by omega)]

private lemma coeff_pow8_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 8) = if n % 8 = 0 then PowerSeries.coeff (n / 8) f else 0 := by
  rw [show f ^ 8 = (f ^ 4) ^ 2 by ring, coeff_sq_zmod2]
  by_cases h2 : n % 2 = 0
  · rw [if_pos h2, coeff_pow4_zmod2]
    by_cases h8 : n % 8 = 0
    · rw [if_pos h8, if_pos (by omega), show n / 2 / 4 = n / 8 by omega]
    · rw [if_neg h8, if_neg (by omega)]
  · rw [if_neg h2, if_neg (by omega)]

private lemma three_dvd_four_pow_sub_one (k : ℕ) : 3 ∣ 4 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases ih with ⟨q, hq⟩
    have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
    refine ⟨4 * q + 1, ?_⟩
    rw [pow_succ']; omega

private lemma div3_four_pow_succ (k : ℕ) :
    (4 ^ (k + 1) - 1) / 3 = 4 * ((4 ^ k - 1) / 3) + 1 := by
  rcases three_dvd_four_pow_sub_one k with ⟨q, hq⟩
  have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
  have h2 : 4 ^ (k + 1) - 1 = 3 * (4 * q + 1) := by rw [pow_succ']; omega
  rw [h2, hq, Nat.mul_div_cancel_left _ (by decide), Nat.mul_div_cancel_left _ (by decide)]

private noncomputable def C0 : PowerSeries (ZMod 2) :=
  letI := Classical.decPred (fun n : ℕ => ∃ k : ℕ, n = (4 ^ k - 1) / 3)
  PowerSeries.mk fun n => if ∃ k : ℕ, n = (4 ^ k - 1) / 3 then 1 else 0

private lemma coeff_C0 (n : ℕ) :
    letI := Classical.decPred (fun n : ℕ => ∃ k : ℕ, n = (4 ^ k - 1) / 3)
    PowerSeries.coeff n C0 = if ∃ k : ℕ, n = (4 ^ k - 1) / 3 then 1 else 0 := by
  classical
  simp [C0]

private lemma C0_quartic : C0 = 1 + (PowerSeries.X : PowerSeries (ZMod 2)) * C0 ^ 4 := by
  classical
  ext n
  rw [coeff_C0, map_add, PowerSeries.coeff_one]
  rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul']
  cases n with
  | zero =>
    rw [if_pos ⟨0, by norm_num⟩, if_pos rfl, if_neg (by omega), add_zero]
  | succ m =>
    rw [if_neg (by omega : m + 1 ≠ 0), zero_add, if_pos (by omega : 1 ≤ m + 1),
      Nat.add_sub_cancel, coeff_pow4_zmod2]
    by_cases h4 : m % 4 = 0
    · rw [if_pos h4, coeff_C0]
      have hiff : (∃ k : ℕ, m + 1 = (4 ^ k - 1) / 3) ↔ (∃ k : ℕ, m / 4 = (4 ^ k - 1) / 3) := by
        constructor
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k' =>
            rw [div3_four_pow_succ] at hk
            exact ⟨k', by omega⟩
        · rintro ⟨k, hk⟩
          exact ⟨k + 1, by rw [div3_four_pow_succ]; omega⟩
      by_cases h : ∃ k : ℕ, m + 1 = (4 ^ k - 1) / 3
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
    · rw [if_neg h4]
      have hnot : ¬ ∃ k : ℕ, m + 1 = (4 ^ k - 1) / 3 := by
        rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk
        | succ k' =>
          rw [div3_four_pow_succ] at hk
          omega
      rw [if_neg hnot]

private lemma lucas_mod2 (a b : ℕ) :
    (Nat.choose a b : ZMod 2) = (Nat.choose (a % 2) (b % 2) : ZMod 2) * (Nat.choose (a / 2) (b / 2) : ZMod 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := a) (k := b)
  rw [← Nat.cast_mul]
  exact (ZMod.natCast_eq_natCast_iff _ _ 2).mpr h

private lemma choose_4n_n_zmod2 (n : ℕ) :
    (Nat.choose (4 * n) n : ZMod 2) = if n = 0 then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ m =>
      rw [if_neg (by omega)]
      rcases Nat.even_or_odd (m + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hk_eq : m + 1 = 2 * k := by omega
        rw [hk_eq, lucas_mod2 (4 * (2 * k)) (2 * k)]
        rw [show (4 * (2 * k)) % 2 = 0 by omega, show (2 * k) % 2 = 0 by omega,
            show (4 * (2 * k)) / 2 = 4 * k by omega, show (2 * k) / 2 = k by omega]
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
        rw [ih k (by omega), if_neg (by omega)]
      · have hk_eq : m + 1 = 2 * k + 1 := by omega
        rw [hk_eq, lucas_mod2 (4 * (2 * k + 1)) (2 * k + 1)]
        rw [show (4 * (2 * k + 1)) % 2 = 0 by omega, show (2 * k + 1) % 2 = 1 by omega]
        simp

private lemma choose_4n1_n_zmod2 (n : ℕ) :
    (Nat.choose (4 * n + 1) n : ZMod 2) = PowerSeries.coeff n C0 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_C0]
    cases n with
    | zero => simp; exact ⟨0, by norm_num⟩
    | succ m =>
      rcases Nat.even_or_odd (m + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hk_eq : m + 1 = 2 * k := by omega
        rw [hk_eq, lucas_mod2 (4 * (2 * k) + 1) (2 * k)]
        rw [show (4 * (2 * k) + 1) % 2 = 1 by omega, show (2 * k) % 2 = 0 by omega,
            show (4 * (2 * k) + 1) / 2 = 4 * k by omega, show (2 * k) / 2 = k by omega]
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
        rw [choose_4n_n_zmod2 k, if_neg (by omega)]
        symm; rw [if_neg]
        rintro ⟨t, ht⟩
        cases t with
        | zero => simp at ht; omega
        | succ t' => rw [div3_four_pow_succ] at ht; omega
      · have hk_eq : m + 1 = 2 * k + 1 := by omega
        rw [hk_eq, lucas_mod2 (4 * (2 * k + 1) + 1) (2 * k + 1)]
        rw [show (4 * (2 * k + 1) + 1) % 2 = 1 by omega, show (2 * k + 1) % 2 = 1 by omega,
            show (4 * (2 * k + 1) + 1) / 2 = 4 * k + 2 by omega, show (2 * k + 1) / 2 = k by omega]
        simp only [Nat.choose_self, Nat.cast_one, one_mul]
        rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · have hj_eq : k = 2 * j := by omega
          rw [hj_eq, lucas_mod2 (4 * (2 * j) + 2) (2 * j)]
          rw [show (4 * (2 * j) + 2) % 2 = 0 by omega, show (2 * j) % 2 = 0 by omega,
              show (4 * (2 * j) + 2) / 2 = 4 * j + 1 by omega, show (2 * j) / 2 = j by omega]
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
          rw [ih j (by omega), coeff_C0]
          have hiff : (∃ t : ℕ, j = (4 ^ t - 1) / 3) ↔ (∃ t : ℕ, 2 * (2 * j) + 1 = (4 ^ t - 1) / 3) := by
            constructor
            · rintro ⟨t, ht⟩; exact ⟨t + 1, by rw [div3_four_pow_succ, ← ht]; omega⟩
            · rintro ⟨t, ht⟩
              cases t with
              | zero => simp at ht
              | succ t' => rw [div3_four_pow_succ] at ht; exact ⟨t', by omega⟩
          by_cases h : ∃ t : ℕ, j = (4 ^ t - 1) / 3
          · rw [if_pos h, if_pos (hiff.mp h)]
          · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
        · have hj_eq : k = 2 * j + 1 := by omega
          rw [hj_eq, lucas_mod2 (4 * (2 * j + 1) + 2) (2 * j + 1)]
          rw [show (4 * (2 * j + 1) + 2) % 2 = 0 by omega, show (2 * j + 1) % 2 = 1 by omega]
          simp only [Nat.choose_zero_succ, Nat.cast_zero, zero_mul]
          symm; rw [if_neg]
          rintro ⟨t, ht⟩
          cases t with
          | zero => simp at ht
          | succ t' => rw [div3_four_pow_succ] at ht; omega

private lemma choose_4n3_n_eq_C0_cube (n : ℕ) :
    (Nat.choose (4 * n + 3) n : ZMod 2) = PowerSeries.coeff n (C0 ^ 3) := by
  have hC0_cube : C0 ^ 3 = 1 + PowerSeries.X * C0 ^ 4 + PowerSeries.X ^ 2 * C0 ^ 8 +
      PowerSeries.X ^ 3 * (C0 ^ 3) ^ 4 := by
    have h2 : (1 + PowerSeries.X * C0 ^ 4) ^ 3 =
        1 + PowerSeries.X * C0 ^ 4 + PowerSeries.X ^ 2 * C0 ^ 8 + PowerSeries.X ^ 3 * (C0 ^ 3) ^ 4 +
        2 * (PowerSeries.X * C0 ^ 4 + PowerSeries.X ^ 2 * C0 ^ 8) := by ring
    calc C0 ^ 3 = (1 + PowerSeries.X * C0 ^ 4) ^ 3 := by conv_lhs => rw [C0_quartic]
      _ = 1 + PowerSeries.X * C0 ^ 4 + PowerSeries.X ^ 2 * C0 ^ 8 + PowerSeries.X ^ 3 * (C0 ^ 3) ^ 4 +
          2 * (PowerSeries.X * C0 ^ 4 + PowerSeries.X ^ 2 * C0 ^ 8) := h2
      _ = 1 + PowerSeries.X * C0 ^ 4 + PowerSeries.X ^ 2 * C0 ^ 8 + PowerSeries.X ^ 3 * (C0 ^ 3) ^ 4 := by
          rw [zmod2_ps_two, zero_mul, add_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hcube_n := congrArg (PowerSeries.coeff n) hC0_cube
    rw [map_add, map_add, map_add, PowerSeries.coeff_one,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
        ← pow_one (PowerSeries.X : PowerSeries (ZMod 2)),
        PowerSeries.coeff_X_pow_mul'] at hcube_n
    rw [hcube_n]
    have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hmod with h0 | h1 | h2 | h3
    · set j := n / 4
      have hn : n = 4 * j := by omega
      rw [hn, lucas_mod2 (4 * (4 * j) + 3) (4 * j)]
      rw [show (4 * (4 * j) + 3) % 2 = 1 by omega, show (4 * j) % 2 = 0 by omega,
          show (4 * (4 * j) + 3) / 2 = 8 * j + 1 by omega, show (4 * j) / 2 = 2 * j by omega,
          Nat.choose_zero_right, Nat.cast_one, one_mul, lucas_mod2 (8 * j + 1) (2 * j),
          show (8 * j + 1) % 2 = 1 by omega, show (2 * j) % 2 = 0 by omega,
          show (8 * j + 1) / 2 = 4 * j by omega, show (2 * j) / 2 = j by omega,
          Nat.choose_zero_right, Nat.cast_one, one_mul, choose_4n_n_zmod2 j]
      have hc1 : (if 1 ≤ 4 * j then PowerSeries.coeff (4 * j - 1) (C0 ^ 4) else 0) = 0 := by
        split_ifs with hle
        · rw [coeff_pow4_zmod2, if_neg (by omega)]
        · rfl
      have hc2 : (if 2 ≤ 4 * j then PowerSeries.coeff (4 * j - 2) (C0 ^ 8) else 0) = 0 := by
        split_ifs with hle
        · rw [coeff_pow8_zmod2, if_neg (by omega)]
        · rfl
      have hc3 : (if 3 ≤ 4 * j then PowerSeries.coeff (4 * j - 3) ((C0 ^ 3) ^ 4) else 0) = 0 := by
        split_ifs with hle
        · rw [coeff_pow4_zmod2, if_neg (by omega)]
        · rfl
      rw [hc1, hc2, hc3, add_zero, add_zero, add_zero]
      by_cases hj : j = 0 <;> simp [hj]
    · set j := n / 4
      have hn : n = 4 * j + 1 := by omega
      rw [hn, lucas_mod2 (4 * (4 * j + 1) + 3) (4 * j + 1)]
      rw [show (4 * (4 * j + 1) + 3) % 2 = 1 by omega, show (4 * j + 1) % 2 = 1 by omega,
          show (4 * (4 * j + 1) + 3) / 2 = 8 * j + 3 by omega, show (4 * j + 1) / 2 = 2 * j by omega,
          Nat.choose_self, Nat.cast_one, one_mul, lucas_mod2 (8 * j + 3) (2 * j),
          show (8 * j + 3) % 2 = 1 by omega, show (2 * j) % 2 = 0 by omega,
          show (8 * j + 3) / 2 = 4 * j + 1 by omega, show (2 * j) / 2 = j by omega,
          Nat.choose_zero_right, Nat.cast_one, one_mul, choose_4n1_n_zmod2 j]
      rw [if_neg (by omega), zero_add, if_pos (by omega), Nat.add_sub_cancel, coeff_pow4_zmod2,
          if_pos (by omega), Nat.mul_div_cancel_left j (by omega)]
      have hc2 : (if 2 ≤ 4 * j + 1 then PowerSeries.coeff (4 * j + 1 - 2) (C0 ^ 8) else 0) = 0 := by
        split_ifs with hle
        · rw [coeff_pow8_zmod2, if_neg (by omega)]
        · rfl
      have hc3 : (if 3 ≤ 4 * j + 1 then PowerSeries.coeff (4 * j + 1 - 3) ((C0 ^ 3) ^ 4) else 0) = 0 := by
        split_ifs with hle
        · rw [coeff_pow4_zmod2, if_neg (by omega)]
        · rfl
      rw [hc2, hc3, add_zero, add_zero]
    · set j := n / 4
      have hn : n = 4 * j + 2 := by omega
      rw [hn, lucas_mod2 (4 * (4 * j + 2) + 3) (4 * j + 2)]
      rw [show (4 * (4 * j + 2) + 3) % 2 = 1 by omega, show (4 * j + 2) % 2 = 0 by omega,
          show (4 * (4 * j + 2) + 3) / 2 = 8 * j + 5 by omega, show (4 * j + 2) / 2 = 2 * j + 1 by omega,
          Nat.choose_zero_right, Nat.cast_one, one_mul, lucas_mod2 (8 * j + 5) (2 * j + 1),
          show (8 * j + 5) % 2 = 1 by omega, show (2 * j + 1) % 2 = 1 by omega,
          show (8 * j + 5) / 2 = 4 * j + 2 by omega, show (2 * j + 1) / 2 = j by omega,
          Nat.choose_self, Nat.cast_one, one_mul]
      rw [if_neg (by omega), zero_add, if_pos (by omega), if_pos (by omega),
          show 4 * j + 2 - 1 = 4 * j + 1 by omega, coeff_pow4_zmod2, if_neg (by omega), zero_add,
          show 4 * j + 2 - 2 = 4 * j by omega, coeff_pow8_zmod2]
      have hc3 : (if 3 ≤ 4 * j + 2 then PowerSeries.coeff (4 * j + 2 - 3) ((C0 ^ 3) ^ 4) else 0) = 0 := by
        split_ifs with hle
        · rw [coeff_pow4_zmod2, if_neg (by omega)]
        · rfl
      rw [hc3, add_zero]
      rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hj : j = 2 * m := by omega
        rw [hj, lucas_mod2 (4 * (2 * m) + 2) (2 * m),
            show (4 * (2 * m) + 2) % 2 = 0 by omega, show (2 * m) % 2 = 0 by omega,
            show (4 * (2 * m) + 2) / 2 = 4 * m + 1 by omega, show (2 * m) / 2 = m by omega,
            Nat.choose_zero_right, Nat.cast_one, one_mul, choose_4n1_n_zmod2 m,
            if_pos (by omega), show 4 * (2 * m) / 8 = m by omega]
      · have hj : j = 2 * m + 1 := by omega
        rw [hj, lucas_mod2 (4 * (2 * m + 1) + 2) (2 * m + 1),
            show (4 * (2 * m + 1) + 2) % 2 = 0 by omega, show (2 * m + 1) % 2 = 1 by omega,
            Nat.choose_zero_succ, Nat.cast_zero, zero_mul, if_neg (by omega)]
    · set j := n / 4
      have hn : n = 4 * j + 3 := by omega
      rw [hn, lucas_mod2 (4 * (4 * j + 3) + 3) (4 * j + 3)]
      rw [show (4 * (4 * j + 3) + 3) % 2 = 1 by omega, show (4 * j + 3) % 2 = 1 by omega,
          show (4 * (4 * j + 3) + 3) / 2 = 8 * j + 7 by omega, show (4 * j + 3) / 2 = 2 * j + 1 by omega,
          Nat.choose_self, Nat.cast_one, one_mul, lucas_mod2 (8 * j + 7) (2 * j + 1),
          show (8 * j + 7) % 2 = 1 by omega, show (2 * j + 1) % 2 = 1 by omega,
          show (8 * j + 7) / 2 = 4 * j + 3 by omega, show (2 * j + 1) / 2 = j by omega,
          Nat.choose_self, Nat.cast_one, one_mul]
      rw [ih j (by omega), if_neg (by omega), zero_add, if_pos (by omega), if_pos (by omega),
          if_pos (by omega), show 4 * j + 3 - 1 = 4 * j + 2 by omega, coeff_pow4_zmod2,
          if_neg (by omega), zero_add, show 4 * j + 3 - 2 = 4 * j + 1 by omega, coeff_pow8_zmod2,
          if_neg (by omega), zero_add, show 4 * j + 3 - 3 = 4 * j by omega, coeff_pow4_zmod2,
          if_pos (by omega), Nat.mul_div_cancel_left j (by omega)]

private lemma eq_of_alg_eq (f g : PowerSeries (ZMod 2))
    (hf : f = 1 + PowerSeries.X * f + PowerSeries.X ^ 4 * f ^ 5)
    (hg : g = 1 + PowerSeries.X * g + PowerSeries.X ^ 4 * g ^ 5) :
    ∀ n : ℕ, PowerSeries.coeff n f = PowerSeries.coeff n g := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have h1 := congrArg (PowerSeries.coeff n) hf
    have h2 := congrArg (PowerSeries.coeff n) hg
    rw [map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow_mul'] at h1 h2
    rw [h1, h2]
    cases n with
    | zero =>
      simp [PowerSeries.coeff_zero_X_mul]
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, ih m (by omega)]
      congr 1
      split_ifs with hle
      · have hpow : ∀ k : ℕ, ∀ t ≤ m + 1 - 4,
            PowerSeries.coeff t (f ^ k) = PowerSeries.coeff t (g ^ k) := by
          intro k
          induction k with
          | zero => intro t _; rfl
          | succ j ihj =>
            intro t ht
            rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
            refine Finset.sum_congr rfl fun p hp => ?_
            have hp1 : p.1 ≤ m + 1 - 4 := by have := Finset.mem_antidiagonal.mp hp; omega
            have hp2 : p.2 ≤ m + 1 - 4 := by have := Finset.mem_antidiagonal.mp hp; omega
            rw [ihj p.1 hp1, ih p.2 (by omega)]
        exact hpow 5 (m + 1 - 4) le_rfl
      · rfl

theorem solution : type_of% @OMA.S_oeis_a369083.main := by
  intro A hEq
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let a : PowerSeries (ZMod 2) := φ A
  let Aneg : PowerSeries ℤ := PowerSeries.mk fun n => (-1 : ℤ) ^ n * PowerSeries.coeff n A
  have hA0 : PowerSeries.coeff 0 A = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) hEq
    rw [show (4 : PowerSeries ℤ) * (A - 1) = PowerSeries.C 4 * (A - 1) by simp,
        PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_one, if_pos rfl,
        ← pow_one (PowerSeries.X : PowerSeries ℤ), PowerSeries.coeff_X_pow_mul',
        if_neg (by omega)] at h0
    omega
  have hAneg_sq : ∀ n : ℕ, PowerSeries.coeff n (Aneg ^ 2) = (-1 : ℤ) ^ n * PowerSeries.coeff n (A ^ 2) := by
    intro n
    rw [sq, sq, PowerSeries.coeff_mul, PowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    simp only [Aneg, PowerSeries.coeff_mk]
    rw [show (-1 : ℤ) ^ p.1 * PowerSeries.coeff p.1 A * ((-1 : ℤ) ^ p.2 * PowerSeries.coeff p.2 A) =
        ((-1 : ℤ) ^ p.1 * (-1 : ℤ) ^ p.2) * (PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 A) by ring,
        ← pow_add, hsum]
  -- Extract even/odd coefficient recurrences in ZMod 2
  have ha_odd : ∀ k : ℕ, PowerSeries.coeff (2 * k + 1) a = PowerSeries.coeff k a := by
    intro k
    have h := congrArg (PowerSeries.coeff (2 * k + 1)) hEq
    rw [show (4 : PowerSeries ℤ) * (A - 1) = PowerSeries.C 4 * (A - 1) by simp,
        PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_one, if_neg (by omega), sub_zero,
        ← pow_one (PowerSeries.X : PowerSeries ℤ), PowerSeries.coeff_X_pow_mul',
        if_pos (by omega), Nat.add_sub_cancel, map_sub,
        show (5 : PowerSeries ℤ) * A ^ 2 = PowerSeries.C 5 * A ^ 2 by simp,
        PowerSeries.coeff_C_mul, hAneg_sq (2 * k),
        show (-1 : ℤ) ^ (2 * k) = 1 by rw [pow_mul]; simp] at h
    have heq_int : PowerSeries.coeff (2 * k + 1) A = PowerSeries.coeff (2 * k) (A ^ 2) := by linarith
    have hcast := congrArg (Int.castRingHom (ZMod 2)) heq_int
    change PowerSeries.coeff (2 * k + 1) a = (Int.castRingHom (ZMod 2)) (PowerSeries.coeff (2 * k) (A ^ 2)) at hcast
    rw [← PowerSeries.coeff_map, map_pow, coeff_sq_zmod2, if_pos (by omega),
        Nat.mul_div_cancel_left k (by omega)] at hcast
    exact hcast
  have ha_even : ∀ k : ℕ, PowerSeries.coeff (2 * k + 2) a =
      ∑ p ∈ Finset.antidiagonal k, PowerSeries.coeff (2 * p.1) a * PowerSeries.coeff (2 * p.2 + 1) a := by
    intro k
    have h := congrArg (PowerSeries.coeff (2 * k + 2)) hEq
    rw [show (4 : PowerSeries ℤ) * (A - 1) = PowerSeries.C 4 * (A - 1) by simp,
        PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_one, if_neg (by omega), sub_zero,
        ← pow_one (PowerSeries.X : PowerSeries ℤ), PowerSeries.coeff_X_pow_mul',
        if_pos (by omega), show 2 * k + 2 - 1 = 2 * k + 1 by omega, map_sub,
        show (5 : PowerSeries ℤ) * A ^ 2 = PowerSeries.C 5 * A ^ 2 by simp,
        PowerSeries.coeff_C_mul, hAneg_sq (2 * k + 1),
        show (-1 : ℤ) ^ (2 * k + 1) = -1 by rw [pow_succ, pow_mul]; simp] at h
    -- coeff (2k+1) (A^2) = 2 * ∑_{p.1+p.2=k} coeff (2*p.1) A * coeff (2*p.2+1) A
    have hsq_odd : PowerSeries.coeff (2 * k + 1) (A ^ 2) =
        2 * ∑ p ∈ Finset.antidiagonal k,
          PowerSeries.coeff (2 * p.1) A * PowerSeries.coeff (2 * p.2 + 1) A := by
      rw [sq, PowerSeries.coeff_mul]
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal (2 * k + 1)) (fun p => p.1 % 2 = 0)]
      have h1 : ∑ p ∈ (Finset.antidiagonal (2 * k + 1)).filter (fun p => p.1 % 2 = 0),
          PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 A =
          ∑ p ∈ Finset.antidiagonal k, PowerSeries.coeff (2 * p.1) A * PowerSeries.coeff (2 * p.2 + 1) A := by
        refine Finset.sum_bij (fun p _ => (p.1 / 2, p.2 / 2)) ?_ ?_ ?_ ?_
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢; omega
        · intro p1 hp1 p2 hp2 heq
          simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp1 hp2
          have h1' := congrArg Prod.fst heq; have h2' := congrArg Prod.snd heq
          exact Prod.ext (by omega) (by omega)
        · intro q hq; simp only [Finset.mem_antidiagonal] at hq
          refine ⟨(2 * q.1, 2 * q.2 + 1), ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_antidiagonal]; omega
          · exact Prod.ext (by omega) (by omega)
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
          rw [show 2 * (p.1 / 2) = p.1 by omega, show 2 * (p.2 / 2) + 1 = p.2 by omega]
      have h2 : ∑ p ∈ (Finset.antidiagonal (2 * k + 1)).filter (fun p => ¬ p.1 % 2 = 0),
          PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 A =
          ∑ p ∈ Finset.antidiagonal k, PowerSeries.coeff (2 * p.1) A * PowerSeries.coeff (2 * p.2 + 1) A := by
        refine Finset.sum_bij (fun p _ => (p.2 / 2, p.1 / 2)) ?_ ?_ ?_ ?_
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢; omega
        · intro p1 hp1 p2 hp2 heq
          simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp1 hp2
          have h1' := congrArg Prod.fst heq; have h2' := congrArg Prod.snd heq
          exact Prod.ext (by omega) (by omega)
        · intro q hq; simp only [Finset.mem_antidiagonal] at hq
          refine ⟨(2 * q.2 + 1, 2 * q.1), ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_antidiagonal]; omega
          · exact Prod.ext (by omega) (by omega)
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
          rw [show 2 * (p.2 / 2) = p.2 by omega, show 2 * (p.1 / 2) + 1 = p.1 by omega, mul_comm]
      rw [h1, h2]; ring
    rw [hsq_odd] at h
    have heq_int : PowerSeries.coeff (2 * k + 2) A =
        3 * ∑ p ∈ Finset.antidiagonal k,
          PowerSeries.coeff (2 * p.1) A * PowerSeries.coeff (2 * p.2 + 1) A := by linarith
    have hcast := congrArg (Int.castRingHom (ZMod 2)) heq_int
    rw [map_mul, map_ofNat, show (3 : ZMod 2) = 1 by decide, one_mul, map_sum] at hcast
    simpa [a, φ] using hcast
  -- Express E(X^2) and O(X^2) in ZMod 2[[X]]
  let E : PowerSeries (ZMod 2) := PowerSeries.mk fun k => PowerSeries.coeff (2 * k) a
  have ha_decomp : a = E ^ 2 + PowerSeries.X * a ^ 2 := by
    ext n
    rw [map_add, coeff_sq_zmod2, ← pow_one (PowerSeries.X : PowerSeries (ZMod 2)),
        PowerSeries.coeff_X_pow_mul']
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hn : n = 2 * k := by omega
      rw [hn, if_pos (by omega), Nat.mul_div_cancel_left k (by omega)]
      simp only [E, PowerSeries.coeff_mk]
      split_ifs with hle
      · rw [coeff_sq_zmod2, if_neg (by omega), add_zero]
      · rw [add_zero]
    · have hn : n = 2 * k + 1 := by omega
      rw [hn, if_neg (by omega), zero_add, if_pos (by omega), Nat.add_sub_cancel,
          coeff_sq_zmod2, if_pos (by omega), Nat.mul_div_cancel_left k (by omega)]
      exact ha_odd k
  have hE_eq : E = 1 + PowerSeries.X * E * a := by
    ext k
    rw [map_add, PowerSeries.coeff_one,
        show PowerSeries.X * E * a = PowerSeries.X * (E * a) by ring,
        ← pow_one (PowerSeries.X : PowerSeries (ZMod 2)), PowerSeries.coeff_X_pow_mul']
    cases k with
    | zero =>
      rw [if_pos rfl, if_neg (by omega), add_zero]
      simp only [E, PowerSeries.coeff_mk, Nat.mul_zero]
      change (Int.castRingHom (ZMod 2)) (PowerSeries.coeff 0 A) = 1
      rw [hA0, map_one]
    | succ m =>
      rw [if_neg (by omega), zero_add, if_pos (by omega), Nat.add_sub_cancel, PowerSeries.coeff_mul]
      simp only [E, PowerSeries.coeff_mk]
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, ha_even m]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [ha_odd p.2]
  -- Square hE_eq: E^2 = 1 + X^2 * E^2 * a^2
  have hE2 : E ^ 2 = 1 + PowerSeries.X ^ 2 * E ^ 2 * a ^ 2 := by
    have h1 := congrArg (· ^ 2) hE_eq
    have h2 : (1 + PowerSeries.X * E * a) ^ 2 =
        1 + PowerSeries.X ^ 2 * E ^ 2 * a ^ 2 + 2 * (PowerSeries.X * E * a) := by ring
    rw [h2, zmod2_ps_two, zero_mul, add_zero] at h1
    exact h1
  -- Substitute E^2 = a + X * a^2 into hE2 to get a = 1 + X * a + X^4 * a^5!
  have hE2_val : E ^ 2 = a + PowerSeries.X * a ^ 2 := by
    calc E ^ 2 = (E ^ 2 + PowerSeries.X * a ^ 2) + PowerSeries.X * a ^ 2 := by
          rw [add_assoc, zmod2_ps_add_self, add_zero]
      _ = a + PowerSeries.X * a ^ 2 := by rw [← ha_decomp]
  have ha_alg : a = 1 + PowerSeries.X * a + PowerSeries.X ^ 4 * a ^ 5 := by
    have h1 : a + PowerSeries.X * a ^ 2 = 1 + PowerSeries.X ^ 2 * (a + PowerSeries.X * a ^ 2) * a ^ 2 := by
      rw [← hE2_val]; exact hE2
    have h2 := congrArg ((1 + PowerSeries.X * a) * ·) h1
    have hlhs : (1 + PowerSeries.X * a) * (a + PowerSeries.X * a ^ 2) =
        a + PowerSeries.X ^ 2 * a ^ 3 + 2 * (PowerSeries.X * a ^ 2) := by ring
    have hrhs : (1 + PowerSeries.X * a) * (1 + PowerSeries.X ^ 2 * (a + PowerSeries.X * a ^ 2) * a ^ 2) =
        1 + PowerSeries.X * a + PowerSeries.X ^ 2 * a ^ 3 + PowerSeries.X ^ 4 * a ^ 5 +
        2 * (PowerSeries.X ^ 3 * a ^ 4) := by ring
    rw [hlhs, hrhs, zmod2_ps_two, zero_mul, zero_mul, add_zero, add_zero] at h2
    calc a = (a + PowerSeries.X ^ 2 * a ^ 3) + PowerSeries.X ^ 2 * a ^ 3 := by
          rw [add_assoc, zmod2_ps_add_self, add_zero]
      _ = (1 + PowerSeries.X * a + PowerSeries.X ^ 2 * a ^ 3 + PowerSeries.X ^ 4 * a ^ 5) +
          PowerSeries.X ^ 2 * a ^ 3 := by rw [h2]
      _ = 1 + PowerSeries.X * a + PowerSeries.X ^ 4 * a ^ 5 +
          (PowerSeries.X ^ 2 * a ^ 3 + PowerSeries.X ^ 2 * a ^ 3) := by ring
      _ = 1 + PowerSeries.X * a + PowerSeries.X ^ 4 * a ^ 5 := by rw [zmod2_ps_add_self, add_zero]
  -- Check that C0^3 satisfies the exact same equation C0^3 = 1 + X * C0^3 + X^4 * (C0^3)^5!
  have hC03_alg : C0 ^ 3 = 1 + PowerSeries.X * C0 ^ 3 + PowerSeries.X ^ 4 * (C0 ^ 3) ^ 5 := by
    have hXC4 : PowerSeries.X * C0 ^ 4 = 1 + C0 := by
      calc PowerSeries.X * C0 ^ 4 = (1 + PowerSeries.X * C0 ^ 4) + 1 := by
            rw [add_comm 1 (PowerSeries.X * C0 ^ 4), add_assoc, zmod2_ps_add_self, add_zero]
        _ = C0 + 1 := by rw [← C0_quartic]
        _ = 1 + C0 := by ring
    have h1 : PowerSeries.X ^ 4 * (C0 ^ 3) ^ 5 = (PowerSeries.X * C0 ^ 4) ^ 3 * (PowerSeries.X * C0 ^ 3) := by
      ring
    rw [h1, hXC4]
    have h2 : 1 + PowerSeries.X * C0 ^ 3 + (1 + C0) ^ 3 * (PowerSeries.X * C0 ^ 3) =
        1 + (PowerSeries.X * C0 ^ 4) * (1 + C0 + C0 ^ 2) +
        2 * (PowerSeries.X * C0 ^ 3 + PowerSeries.X * C0 ^ 4 + PowerSeries.X * C0 ^ 5) := by ring
    rw [h2, zmod2_ps_two, zero_mul, add_zero, hXC4]
    have h3 : 1 + (1 + C0) * (1 + C0 + C0 ^ 2) = C0 ^ 3 + 2 * (1 + C0 + C0 ^ 2) := by ring
    rw [h3, zmod2_ps_two, zero_mul, add_zero]
  -- By strong induction, coeff n a = coeff n (C0^3) for all n!
  have ha_eq_C03 : ∀ n : ℕ, PowerSeries.coeff n a = PowerSeries.coeff n (C0 ^ 3) :=
    eq_of_alg_eq a (C0 ^ 3) ha_alg hC03_alg
  -- Translate to ℤ mod 2
  intro n
  have hcast : ((PowerSeries.coeff n A : ℤ) : ZMod 2) = ((Nat.choose (4 * n + 3) n : ℤ) : ZMod 2) := by
    change PowerSeries.coeff n a = ((Nat.choose (4 * n + 3) n : ℕ) : ZMod 2)
    rw [ha_eq_C03 n, choose_4n3_n_eq_C0_cube n]
  have hdvd : (2 : ℤ) ∣ (PowerSeries.coeff n A - (Nat.choose (4 * n + 3) n : ℤ)) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    rw [Int.cast_sub, hcast, sub_self]
  rcases hdvd with ⟨q, hq⟩
  omega

end OMA.P_oeis_a369083

theorem OMA.solution : type_of% @OMA.S_oeis_a369083.main := OMA.P_oeis_a369083.solution
