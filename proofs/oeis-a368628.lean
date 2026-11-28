import OMAStatements.S_oeis_a368628
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA368628Proof

open Classical
open OMA.S_oeis_a368628

private noncomputable def evenPart (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n % 2 = 0 then PowerSeries.coeff n A else 0

private noncomputable def oddPart (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n % 2 = 1 then PowerSeries.coeff n A else 0

private lemma A_eq_even_add_odd (A : PowerSeries ℤ) :
    A = evenPart A + oddPart A := by
  ext n
  simp only [map_add, evenPart, oddPart, PowerSeries.coeff_mk]
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg h, if_pos (by omega), zero_add]

private lemma negArg_eq_even_sub_odd (A : PowerSeries ℤ) :
    negArg A = evenPart A - oddPart A := by
  ext n
  simp only [map_sub, negArg, evenPart, oddPart, PowerSeries.coeff_mk]
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_neg (by omega), sub_zero, (Nat.even_iff.mpr h).neg_one_pow, one_mul]
  · rw [if_neg h, if_pos (by omega), zero_sub, (Nat.odd_iff.mpr (by omega)).neg_one_pow]; ring

private lemma cancel_two_ps (F G : PowerSeries ℤ) (h : 2 * F = 2 * G) : F = G := by
  ext k
  have hk := congrArg (PowerSeries.coeff k) h
  rw [show (2 : PowerSeries ℤ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul] at hk
  omega

private lemma coeff_X_mul_ps {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X * f) = if n = 0 then 0 else PowerSeries.coeff (n - 1) f := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.X : PowerSeries R) * PowerSeries.coeff j f)]
  cases n with
  | zero => simp [PowerSeries.coeff_X]
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [Finset.sum_eq_single 1]
    · simp [PowerSeries.coeff_X]
    · intro i _ hne; simp [PowerSeries.coeff_X, hne]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma coeff_sq_mod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 2) =
      if n % 2 = 0 then PowerSeries.coeff (n / 2) f else 0 := by
  rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j f)]
  set S := Finset.range (n + 1)
  set Slt := S.filter (fun i => i < n - i)
  set Sgt := S.filter (fun i => n - i < i)
  set Seq := S.filter (fun i => i = n - i)
  have hdisj1 : Disjoint Slt Sgt := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Slt, Sgt, Finset.mem_filter] at h1 h2; omega
  have hdisj2 : Disjoint (Slt ∪ Sgt) Seq := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
  have hunion : S = (Slt ∪ Sgt) ∪ Seq := by
    ext i; simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hi; rcases lt_trichotomy i (n - i) with h | h | h
      · exact Or.inl (Or.inl ⟨hi, h⟩)
      · exact Or.inr ⟨hi, h⟩
      · exact Or.inl (Or.inr ⟨hi, h⟩)
    · rintro ((⟨hi, _⟩ | ⟨hi, _⟩) | ⟨hi, _⟩) <;> exact hi
  have hsym :
      ∑ i ∈ Sgt, PowerSeries.coeff i f * PowerSeries.coeff (n - i) f =
      ∑ i ∈ Slt, PowerSeries.coeff i f * PowerSeries.coeff (n - i) f := by
    apply Finset.sum_bij (fun i _ => n - i)
    · intro i hi; simp only [Slt, Sgt, S, Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
    · intro a ha b hb h; simp only [Sgt, S, Finset.mem_filter, Finset.mem_range] at ha hb; omega
    · intro i hi; simp only [Slt, Sgt, S, Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact ⟨n - i, ⟨by omega, by omega⟩, by omega⟩
    · intro i hi
      simp only [Sgt, S, Finset.mem_filter, Finset.mem_range] at hi
      rw [show n - (n - i) = i by omega, mul_comm]
  change ∑ i ∈ S, PowerSeries.coeff i f * PowerSeries.coeff (n - i) f = _
  rw [hunion, Finset.sum_union hdisj2, Finset.sum_union hdisj1, hsym]
  have h2z : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [h2z, zero_add]
  by_cases hpar : n % 2 = 0
  · rw [if_pos hpar]
    have hSeq : Seq = {n / 2} := by
      ext i; simp only [Seq, S, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
    rw [hSeq, Finset.sum_singleton, show n - n / 2 = n / 2 by omega]
    have hsq : ∀ x : ZMod 2, x * x = x := by decide
    exact hsq _
  · rw [if_neg hpar]
    have hSeq : Seq = ∅ := by
      ext i; simp only [Seq, S, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty,
        iff_false]; omega
    rw [hSeq, Finset.sum_empty]

private lemma coeff_pow4_mod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 4) =
      if n % 4 = 0 then PowerSeries.coeff (n / 4) f else 0 := by
  rw [show f ^ 4 = (f ^ 2) ^ 2 by ring, coeff_sq_mod2]
  by_cases h4 : n % 4 = 0
  · rw [if_pos h4, if_pos (by omega : n % 2 = 0), coeff_sq_mod2, if_pos (by omega : (n / 2) % 2 = 0),
      show n / 2 / 2 = n / 4 by omega]
  · rw [if_neg h4]
    by_cases h2 : n % 2 = 0
    · rw [if_pos h2, coeff_sq_mod2, if_neg (by omega : ¬((n / 2) % 2 = 0))]
    · rw [if_neg h2]

private lemma A_eq_pow4_mod2 {A : PowerSeries ℤ} (hA : IsA368628 A) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) A =
      1 + PowerSeries.X * (PowerSeries.map (Int.castRingHom (ZMod 2)) A) ^ 4 := by
  have hZ : A = 1 + PowerSeries.X *
      (2 * evenPart A * oddPart A + evenPart A ^ 4 + 6 * evenPart A ^ 2 * oddPart A ^ 2 + oddPart A ^ 4) := by
    apply cancel_two_ps
    have h := hA
    unfold IsA368628 at h
    have hsplit : (A ^ 2 - negArg A ^ 2) + (A ^ 4 + negArg A ^ 4) =
        2 * (2 * evenPart A * oddPart A + evenPart A ^ 4 + 6 * evenPart A ^ 2 * oddPart A ^ 2 + oddPart A ^ 4) := by
      have hN := negArg_eq_even_sub_odd A
      have hA' := A_eq_even_add_odd A
      generalize evenPart A = E at hN hA' ⊢
      generalize oddPart A = O at hN hA' ⊢
      rw [hN, hA']
      ring
    calc 2 * A = 2 + PowerSeries.X * (A ^ 2 - negArg A ^ 2) + PowerSeries.X * (A ^ 4 + negArg A ^ 4) := h
      _ = 2 + PowerSeries.X * ((A ^ 2 - negArg A ^ 2) + (A ^ 4 + negArg A ^ 4)) := by ring
      _ = 2 + PowerSeries.X * (2 * (2 * evenPart A * oddPart A + evenPart A ^ 4 +
            6 * evenPart A ^ 2 * oddPart A ^ 2 + oddPart A ^ 4)) := by rw [hsplit]
      _ = 2 * (1 + PowerSeries.X * (2 * evenPart A * oddPart A + evenPart A ^ 4 +
            6 * evenPart A ^ 2 * oddPart A ^ 2 + oddPart A ^ 4)) := by ring
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have h2z : (2 : PowerSeries (ZMod 2)) = 0 := by
    ext k; rw [show (2 : PowerSeries (ZMod 2)) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C]
    split_ifs <;> simp [show (2 : ZMod 2) = 0 by decide]
  have hphi2 : phi 2 = 0 := by rw [map_ofNat, h2z]
  have hphi6 : phi 6 = 0 := by
    rw [map_ofNat, show (6 : PowerSeries (ZMod 2)) = 2 * 3 by norm_num, h2z, zero_mul]
  have h := congrArg phi hZ
  simp only [map_add, map_mul, map_pow, map_one, hphi2, hphi6, zero_mul,
    zero_add, add_zero] at h
  have hEO4 : phi (evenPart A) ^ 4 + phi (oddPart A) ^ 4 = phi A ^ 4 := by
    have hsum : phi A = phi (evenPart A) + phi (oddPart A) := by
      conv_lhs => rw [A_eq_even_add_odd A]
      rw [map_add]
    rw [hsum]
    calc phi (evenPart A) ^ 4 + phi (oddPart A) ^ 4
        = (phi (evenPart A) + phi (oddPart A)) ^ 4 -
            2 * (2 * phi (evenPart A) ^ 3 * phi (oddPart A) +
                 3 * phi (evenPart A) ^ 2 * phi (oddPart A) ^ 2 +
                 2 * phi (evenPart A) * phi (oddPart A) ^ 3) := by ring
      _ = (phi (evenPart A) + phi (oddPart A)) ^ 4 := by rw [h2z, zero_mul, sub_zero]
  rw [hEO4] at h
  dsimp only [phi] at h
  rw [PowerSeries.map_X] at h
  exact h

private lemma three_dvd_four_pow_sub_one (k : ℕ) : 3 ∣ 4 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases ih with ⟨q, hq⟩
    have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
    refine ⟨4 * q + 1, ?_⟩
    rw [pow_succ']
    omega

private lemma coeff_A_mod2 {A : PowerSeries ℤ} (hA : IsA368628 A) :
    ∀ n : ℕ, PowerSeries.coeff n (PowerSeries.map (Int.castRingHom (ZMod 2)) A) =
      if ∃ k : ℕ, n = (4 ^ k - 1) / 3 then 1 else 0 := by
  let A2 := PowerSeries.map (Int.castRingHom (ZMod 2)) A
  have hA2 : A2 = 1 + PowerSeries.X * A2 ^ 4 := A_eq_pow4_mod2 hA
  intro n
  change PowerSeries.coeff n A2 = _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [hA2, map_add, coeff_X_mul_ps, PowerSeries.coeff_one]
    cases n with
    | zero =>
      simp only [↓reduceIte, add_zero]
      rw [if_pos ⟨0, rfl⟩]
    | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, Nat.add_sub_cancel]
      rw [coeff_pow4_mod2]
      by_cases h4 : n % 4 = 0
      · rw [if_pos h4, ih (n / 4) (by omega)]
        have hiff : (∃ k : ℕ, n / 4 = (4 ^ k - 1) / 3) ↔ (∃ k : ℕ, n + 1 = (4 ^ k - 1) / 3) := by
          constructor
          · rintro ⟨k, hk⟩
            have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
            have hd := three_dvd_four_pow_sub_one k
            have h3 : 3 * ((4 ^ k - 1) / 3) = 4 ^ k - 1 := Nat.mul_div_cancel' hd
            have hd1 := three_dvd_four_pow_sub_one (k + 1)
            have h31 : 3 * ((4 ^ (k + 1) - 1) / 3) = 4 ^ (k + 1) - 1 := Nat.mul_div_cancel' hd1
            rw [pow_succ'] at h31
            exact ⟨k + 1, by omega⟩
          · rintro ⟨k, hk⟩
            cases k with
            | zero => omega
            | succ k' =>
              have h1 : 1 ≤ 4 ^ k' := Nat.one_le_pow k' 4 (by decide)
              have hd := three_dvd_four_pow_sub_one k'
              have h3 : 3 * ((4 ^ k' - 1) / 3) = 4 ^ k' - 1 := Nat.mul_div_cancel' hd
              have hd1 := three_dvd_four_pow_sub_one (k' + 1)
              have h31 : 3 * ((4 ^ (k' + 1) - 1) / 3) = 4 ^ (k' + 1) - 1 := Nat.mul_div_cancel' hd1
              rw [pow_succ'] at h31
              exact ⟨k', by omega⟩
        by_cases hex : ∃ k : ℕ, n / 4 = (4 ^ k - 1) / 3
        · rw [if_pos hex, if_pos (hiff.mp hex)]
        · rw [if_neg hex, if_neg (mt hiff.mpr hex)]
      · rw [if_neg h4]
        have hnot : ¬ ∃ k : ℕ, n + 1 = (4 ^ k - 1) / 3 := by
          rintro ⟨k, hk⟩
          cases k with
          | zero => omega
          | succ k' =>
            have h1 : 1 ≤ 4 ^ k' := Nat.one_le_pow k' 4 (by decide)
            have hd := three_dvd_four_pow_sub_one k'
            have h3 : 3 * ((4 ^ k' - 1) / 3) = 4 ^ k' - 1 := Nat.mul_div_cancel' hd
            have hd1 := three_dvd_four_pow_sub_one (k' + 1)
            have h31 : 3 * ((4 ^ (k' + 1) - 1) / 3) = 4 ^ (k' + 1) - 1 := Nat.mul_div_cancel' hd1
            rw [pow_succ'] at h31
            omega
        rw [if_neg hnot]

end OeisA368628Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a368628.main := by
  intro A hA n
  have hmod : PowerSeries.coeff n A % 2 = 1 ↔ ((PowerSeries.coeff n A : ℤ) : ZMod 2) = 1 := by
    constructor
    · intro h
      have h' : PowerSeries.coeff n A ≡ 1 [ZMOD ((2 : ℕ) : ℤ)] := by rw [Int.ModEq]; omega
      simpa using (ZMod.intCast_eq_intCast_iff _ _ 2).mpr h'
    · intro h
      have h' : PowerSeries.coeff n A ≡ 1 [ZMOD ((2 : ℕ) : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff _ _ 2).mp (by simpa using h)
      rw [Int.ModEq] at h'; omega
  rw [hmod]
  have h := OeisA368628Proof.coeff_A_mod2 hA n
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom] at h
  rw [h]
  split_ifs with hex
  · simp [hex]
  · simp [hex]
