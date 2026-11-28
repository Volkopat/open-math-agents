import OMAStatements.S_oeis_a298689
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic

namespace OMA.P_oeis_a298689

open OMA.S_oeis_a298689

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

private lemma zmod2_sq (a : ZMod 2) : a ^ 2 = a := by
  fin_cases a <;> rfl

private lemma coeff_sq_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 2) =
      if n % 2 = 0 then PowerSeries.coeff (n / 2) f else 0 := by
  rw [sq, PowerSeries.coeff_mul]
  let S := Finset.antidiagonal n
  let Slt := S.filter (fun p => p.1 < p.2)
  let Sgt := S.filter (fun p => p.2 < p.1)
  let Seq := S.filter (fun p => p.1 = p.2)
  have hd1 : Disjoint Slt Sgt := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Slt, Sgt, Finset.mem_filter] at h1 h2; omega
  have hd2 : Disjoint (Slt ∪ Sgt) Seq := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Finset.mem_union, Slt, Sgt, Seq, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1 <;> omega
  have hun : S = (Slt ∪ Sgt) ∪ Seq := by
    ext p
    simp only [Finset.mem_union, S, Slt, Sgt, Seq, Finset.mem_filter]
    constructor
    · intro hp
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl (Or.inl ⟨hp, h⟩)
      · exact Or.inr ⟨hp, h⟩
      · exact Or.inl (Or.inr ⟨hp, h⟩)
    · rintro ((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
  have hswap : ∑ p ∈ Sgt, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f =
      ∑ p ∈ Slt, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Sgt, Slt, S, Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢; omega
    · intro p1 _ p2 _ h
      rcases p1 with ⟨a1, b1⟩; rcases p2 with ⟨a2, b2⟩
      simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · intro q hq
      refine ⟨(q.2, q.1), ?_, Prod.ext rfl rfl⟩
      simp only [Sgt, Slt, S, Finset.mem_filter, Finset.mem_antidiagonal] at hq ⊢; omega
    · intro p _; exact mul_comm _ _
  have hdiag : ∑ p ∈ Seq, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f =
      if n % 2 = 0 then PowerSeries.coeff (n / 2) f else 0 := by
    split_ifs with hev
    · have hseq : Seq = {(n / 2, n / 2)} := by
        ext ⟨a, b⟩
        simp only [Seq, S, Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton,
          Prod.mk.injEq]
        omega
      rw [hseq, Finset.sum_singleton, ← sq, zmod2_sq]
    · have hseq : Seq = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        rintro ⟨a, b⟩ hp
        simp only [Seq, S, Finset.mem_filter, Finset.mem_antidiagonal] at hp
        omega
      rw [hseq, Finset.sum_empty]
  change ∑ p ∈ S, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f = _
  rw [hun, Finset.sum_union hd2, Finset.sum_union hd1, hswap, zmod2_add_self, zero_add, hdiag]

private lemma choose_mod2_zero_of_bit {a b : ℕ} (k : ℕ)
    (ha : (a / 2 ^ k) % 2 = 0) (hb : (b / 2 ^ k) % 2 = 1) :
    Nat.choose a b % 2 = 0 := by
  induction k generalizing a b with
  | zero =>
    simp only [pow_zero, Nat.div_one] at ha hb
    have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := a) (k := b)
    rw [Nat.ModEq] at hluc
    rw [hluc, ha, hb]
    simp
  | succ r ih =>
    have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := a) (k := b)
    rw [Nat.ModEq] at hluc
    rw [hluc, Nat.mul_mod]
    have ha' : (a / 2 / 2 ^ r) % 2 = 0 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']; exact ha
    have hb' : (b / 2 / 2 ^ r) % 2 = 1 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']; exact hb
    rw [ih ha' hb', mul_zero, Nat.zero_mod]

private lemma choose_sq_even (n : ℕ) (hn : 2 ≤ n) : Nat.choose (n ^ 2) n % 2 = 0 := by
  by_cases hev : n % 2 = 0
  · -- Write n = 2^k * u with k ≥ 1 and u odd; bit k of n is 1, bit k of n^2 is 0
    have hne : n ≠ 0 := by omega
    let k := padicValNat 2 n
    have hk_pos : 1 ≤ k := by
      have h2dvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hev
      exact one_le_padicValNat_of_dvd hne h2dvd
    have hdvd : 2 ^ k ∣ n := pow_padicValNat_dvd
    obtain ⟨u, hu⟩ := hdvd
    have hu_odd : u % 2 = 1 := by
      by_contra h
      have h2u : 2 ∣ u := Nat.dvd_of_mod_eq_zero (by omega)
      obtain ⟨v, rfl⟩ := h2u
      have hdvd' : 2 ^ (k + 1) ∣ n := ⟨v, by rw [hu, pow_succ]; ring⟩
      have hle : k + 1 ≤ k := (padicValNat_dvd_iff_le hne).mp hdvd'
      omega
    have hbn : (n / 2 ^ k) % 2 = 1 := by
      rw [hu, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) k)]
      exact hu_odd
    have hba : (n ^ 2 / 2 ^ k) % 2 = 0 := by
      have hsq : n ^ 2 = 2 ^ k * (2 * (2 ^ (k - 1) * u ^ 2)) := by
        rw [hu, mul_pow, ← pow_mul]
        have hpow : 2 ^ (k * 2) = 2 ^ k * (2 * 2 ^ (k - 1)) := by
          rw [← pow_succ', ← pow_add]
          congr 1; omega
        rw [hpow]; ring
      rw [hsq, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) k)]
      omega
    exact choose_mod2_zero_of_bit k hba hbn
  · -- n ≥ 3 is odd; write n - 1 = 2^k * v with k ≥ 1 and v odd; bit k of n is 1, bit k of n^2 is 0
    have hm_ne : n - 1 ≠ 0 := by omega
    have hm_ev : (n - 1) % 2 = 0 := by omega
    let k := padicValNat 2 (n - 1)
    have hk_pos : 1 ≤ k := one_le_padicValNat_of_dvd hm_ne (Nat.dvd_of_mod_eq_zero hm_ev)
    obtain ⟨v, hv⟩ := (pow_padicValNat_dvd : 2 ^ k ∣ n - 1)
    have hv_odd : v % 2 = 1 := by
      by_contra h
      have h2v : 2 ∣ v := Nat.dvd_of_mod_eq_zero (by omega)
      obtain ⟨w, rfl⟩ := h2v
      have hdvd' : 2 ^ (k + 1) ∣ n - 1 := ⟨w, by rw [hv, pow_succ]; ring⟩
      have hle : k + 1 ≤ k := (padicValNat_dvd_iff_le hm_ne).mp hdvd'
      omega
    have hn_eq : n = 2 ^ k * v + 1 := by rw [← hv]; omega
    have h2k_gt1 : 1 < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
    have hbn : (n / 2 ^ k) % 2 = 1 := by
      rw [hn_eq, add_comm, Nat.add_mul_div_left _ _ (pow_pos (by norm_num) k),
        Nat.div_eq_of_lt h2k_gt1, zero_add]
      exact hv_odd
    have hba : (n ^ 2 / 2 ^ k) % 2 = 0 := by
      have hsq : n ^ 2 = 1 + 2 ^ k * (2 * (2 ^ (k - 1) * v ^ 2 + v)) := by
        rw [hn_eq]
        have hpow : 2 ^ k * 2 ^ k = 2 ^ k * (2 * 2 ^ (k - 1)) := by
          congr 1; rw [← pow_succ']; congr 1; omega
        calc (2 ^ k * v + 1) ^ 2
            = 1 + 2 * (2 ^ k * v) + (2 ^ k * 2 ^ k) * v ^ 2 := by ring
          _ = 1 + 2 * (2 ^ k * v) + (2 ^ k * (2 * 2 ^ (k - 1))) * v ^ 2 := by rw [hpow]
          _ = 1 + 2 ^ k * (2 * (2 ^ (k - 1) * v ^ 2 + v)) := by ring
      rw [hsq, Nat.add_mul_div_left _ _ (pow_pos (by norm_num) k),
        Nat.div_eq_of_lt h2k_gt1, zero_add]
      omega
    exact choose_mod2_zero_of_bit k hba hbn

private lemma coeff_X_mul_eq (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.X : PowerSeries (ZMod 2)) * f) =
      if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with h1
  · rw [Finset.sum_eq_single (1, n - 1)]
    · rw [PowerSeries.coeff_X, if_pos rfl, one_mul]
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have ha1 : p.1 ≠ 1 := fun h => hne (Prod.ext h (by omega))
      rw [PowerSeries.coeff_X, if_neg ha1, zero_mul]
    · intro hnot
      exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega
  · apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    have ha1 : p.1 ≠ 1 := by omega
    rw [PowerSeries.coeff_X, if_neg ha1, zero_mul]

private lemma mul_cancel_unit_zmod2 {f g : PowerSeries (ZMod 2)}
    (hg0 : PowerSeries.constantCoeff g = 1) (h : f * g = 0) : f = 0 := by
  ext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hc := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_mul, map_zero] at hc
    rw [Finset.sum_eq_single (n, 0)] at hc
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, hg0, mul_one] at hc
      exact hc
    · rintro ⟨a, b⟩ hab hne
      rw [Finset.mem_antidiagonal] at hab
      have hlt : a < n := by
        have hb : b ≠ 0 := fun hb0 => hne (Prod.ext (by omega) hb0)
        omega
      rw [ih a hlt, map_zero, zero_mul]
    · intro hnot
      exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega

open Classical in
private noncomputable def Bseries : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if n = 0 ∨ ∃ k : ℕ, n = 2 ^ k then 1 else 0

open Classical in
private lemma Bseries_sq : Bseries ^ 2 = Bseries + PowerSeries.X := by
  ext n
  rw [coeff_sq_zmod2, map_add, PowerSeries.coeff_X]
  simp only [Bseries, PowerSeries.coeff_mk]
  match n with
  | 0 => simp
  | 1 =>
    have h1 : ∃ k : ℕ, (1 : ℕ) = 2 ^ k := ⟨0, rfl⟩
    simp [h1]
    decide
  | m + 2 =>
    rw [if_neg (by omega : m + 2 ≠ 1), add_zero]
    by_cases hev : (m + 2) % 2 = 0
    · rw [if_pos hev]
      have hiff : ((m + 2) / 2 = 0 ∨ ∃ k : ℕ, (m + 2) / 2 = 2 ^ k) ↔
          (m + 2 = 0 ∨ ∃ k : ℕ, m + 2 = 2 ^ k) := by
        constructor
        · rintro (h0 | ⟨k, hk⟩)
          · omega
          · right; refine ⟨k + 1, ?_⟩; rw [pow_succ']; omega
        · rintro (h0 | ⟨k, hk⟩)
          · omega
          · cases k with
            | zero => omega
            | succ r =>
              right; refine ⟨r, ?_⟩; rw [pow_succ'] at hk; omega
      by_cases h : m + 2 = 0 ∨ ∃ k : ℕ, m + 2 = 2 ^ k
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    · rw [if_neg hev]
      have hnot : ¬ (m + 2 = 0 ∨ ∃ k : ℕ, m + 2 = 2 ^ k) := by
        rintro (h0 | ⟨k, hk⟩)
        · omega
        · cases k with
          | zero => omega
          | succ r => rw [pow_succ'] at hk; omega
      rw [if_neg hnot]

private lemma odd_int_iff_zmod2 (z : ℤ) : Odd z ↔ ((z : ZMod 2) = 1) := by
  rw [Int.odd_iff, show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) from rfl,
    ZMod.intCast_eq_intCast_iff, Int.ModEq]
  omega

open Classical in
private theorem prove_main :
    ∀ A R : PowerSeries ℤ,
      SatisfiesA298689 A R →
      ∀ m : ℕ, 1 ≤ m →
        (Odd (PowerSeries.coeff m A) ↔ ∃ k : ℕ, m = 2 ^ k) := by
  intro A R ⟨hAR, hcoeff⟩ m hm
  set Am : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) A
  set Rm : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) R
  have hAmRm : Am * Rm = 1 := by
    rw [← map_mul, hAR, map_one]
  have hAm_eq_one_add : Am = 1 + PowerSeries.X * Rm := by
    ext n
    rw [PowerSeries.coeff_map, hcoeff n, map_sum, map_add, PowerSeries.coeff_one, coeff_X_mul_eq]
    have hzero : ∀ k ∈ Finset.range (n + 1), 2 ≤ k →
        (Int.castRingHom (ZMod 2)) ((Nat.choose (k ^ 2) k : ℤ) *
          PowerSeries.coeff (n - k) (R ^ (k ^ 2))) = 0 := by
      intro k _ hk
      rw [map_mul, map_natCast]
      have hev := choose_sq_even k hk
      have hc0 : ((Nat.choose (k ^ 2) k : ℕ) : ZMod 2) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact Nat.dvd_of_mod_eq_zero hev
      rw [hc0, zero_mul]
    cases n with
    | zero =>
      simp
    | succ r =>
      have hsplit : ∑ k ∈ Finset.range (r + 2),
          (Int.castRingHom (ZMod 2)) ((Nat.choose (k ^ 2) k : ℤ) *
            PowerSeries.coeff (r + 1 - k) (R ^ (k ^ 2))) =
          ∑ k ∈ Finset.range 2,
            (Int.castRingHom (ZMod 2)) ((Nat.choose (k ^ 2) k : ℤ) *
              PowerSeries.coeff (r + 1 - k) (R ^ (k ^ 2))) := by
        symm
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun k hk hnot => ?_
        rw [Finset.mem_range] at hk hnot
        exact hzero k (Finset.mem_range.mpr hk) (by omega)
      rw [hsplit, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Nat.sub_zero, Nat.succ_ne_zero, ↓reduceIte, zero_add, show 1 ≤ r + 1 by omega,
        Nat.add_sub_cancel, zero_pow (by norm_num : 2 ≠ 0), pow_zero, Nat.choose_self,
        Nat.cast_one, one_mul, PowerSeries.coeff_one, one_pow, pow_one, map_zero,
        Rm, PowerSeries.coeff_map]
  have hAm_sq : Am ^ 2 = Am + PowerSeries.X := by
    calc Am ^ 2 = Am * (1 + PowerSeries.X * Rm) := by rw [sq]; nth_rw 2 [hAm_eq_one_add]
      _ = Am + PowerSeries.X * (Am * Rm) := by ring
      _ = Am + PowerSeries.X * 1 := by rw [hAmRm]
      _ = Am + PowerSeries.X := by ring
  have hAm0 : PowerSeries.constantCoeff Am = 1 := by
    rw [hAm_eq_one_add]; simp
  have hB0 : PowerSeries.constantCoeff Bseries = 1 := by
    simp [Bseries]
  have hdiff_sq : (Am - Bseries) ^ 2 = Am - Bseries := by
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
      ext k; rw [show (2 : PowerSeries (ZMod 2)) = PowerSeries.C (2 : ZMod 2) from rfl,
        map_zero, PowerSeries.coeff_C]; split_ifs <;> decide
    calc (Am - Bseries) ^ 2
        = Am ^ 2 - 2 * Am * Bseries + Bseries ^ 2 := by ring
      _ = Am ^ 2 - 0 * Am * Bseries + Bseries ^ 2 := by rw [h2]
      _ = (Am + PowerSeries.X) + (Bseries + PowerSeries.X) := by rw [hAm_sq, Bseries_sq]; ring
      _ = (Am - Bseries) + 2 * (Bseries + PowerSeries.X) := by ring
      _ = (Am - Bseries) + 0 * (Bseries + PowerSeries.X) := by rw [h2]
      _ = Am - Bseries := by ring
  have hfac : (Am - Bseries) * (Am - Bseries - 1) = 0 := by
    calc (Am - Bseries) * (Am - Bseries - 1) = (Am - Bseries) ^ 2 - (Am - Bseries) := by ring
      _ = 0 := sub_eq_zero.mpr hdiff_sq
  have hu : PowerSeries.constantCoeff (Am - Bseries - 1) = 1 := by
    simp only [map_sub, map_one, hAm0, hB0]
    decide
  have hEq : Am = Bseries := sub_eq_zero.mp (mul_cancel_unit_zmod2 hu hfac)
  have hc := congrArg (PowerSeries.coeff m) hEq
  rw [PowerSeries.coeff_map] at hc
  simp only [Bseries, PowerSeries.coeff_mk, show m ≠ 0 by omega, false_or] at hc
  rw [odd_int_iff_zmod2]
  rw [show ((PowerSeries.coeff m A : ℤ) : ZMod 2) =
      (Int.castRingHom (ZMod 2)) (PowerSeries.coeff m A) from rfl, hc]
  by_cases h : ∃ k : ℕ, m = 2 ^ k
  · simp [h]
  · simp [h]

end OMA.P_oeis_a298689

theorem OMA.solution : type_of% @OMA.S_oeis_a298689.main :=
  OMA.P_oeis_a298689.prove_main
