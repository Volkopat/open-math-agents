import OMAStatements.S_oeis_a373312
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA373312Proof

open Classical
open OMA.S_oeis_a373312

private noncomputable def psComp2 (F G : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

private noncomputable def seriesB : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k - 1 then 1 else 0

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

private lemma psComp2_X_sq (f : PowerSeries (ZMod 2)) :
    psComp2 f (PowerSeries.X ^ 2) = f ^ 2 := by
  ext n
  unfold psComp2
  rw [PowerSeries.coeff_mk, coeff_sq_mod2]
  have hX2 : ∀ k : ℕ, PowerSeries.coeff n ((PowerSeries.X ^ 2 : PowerSeries (ZMod 2)) ^ k) =
      if n = 2 * k then 1 else 0 := by
    intro k
    rw [← pow_mul, PowerSeries.coeff_X_pow]
  simp_rw [hX2]
  by_cases hpar : n % 2 = 0
  · rw [if_pos hpar]
    rw [Finset.sum_eq_single (n / 2)]
    · rw [if_pos (show n = 2 * (n / 2) by omega), mul_one]
    · intro k _ hne; rw [if_neg (show n ≠ 2 * k by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hpar]
    apply Finset.sum_eq_zero
    intro k _; rw [if_neg (show n ≠ 2 * k by omega), mul_zero]

private lemma map_psComp (F G : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (psComp F G) =
      psComp2 (PowerSeries.map (Int.castRingHom (ZMod 2)) F)
              (PowerSeries.map (Int.castRingHom (ZMod 2)) G) := by
  ext n
  simp only [PowerSeries.coeff_map, psComp, psComp2, PowerSeries.coeff_mk, map_sum, map_mul,
    ← map_pow]

private lemma two_eq_zero_ps2 : (2 : PowerSeries (ZMod 2)) = 0 := by
  ext k; rw [show (2 : PowerSeries (ZMod 2)) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C]
  split_ifs <;> simp [show (2 : ZMod 2) = 0 by decide]

private lemma seriesB_eq : seriesB = PowerSeries.X + PowerSeries.X * seriesB ^ 2 := by
  ext n
  rw [map_add, PowerSeries.coeff_X, coeff_X_mul_ps]
  unfold seriesB
  rw [PowerSeries.coeff_mk]
  match n with
  | 0 =>
    simp only [show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, add_zero]
    rw [if_neg]
    rintro ⟨k, hk, h⟩
    have h2 : 2 ≤ 2 ^ k := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hk)
    omega
  | 1 =>
    simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, Nat.sub_self]
    rw [coeff_sq_mod2]
    simp only [Nat.zero_mod, ↓reduceIte, Nat.zero_div, PowerSeries.coeff_mk]
    have hnot0 : ¬ ∃ k : ℕ, 1 ≤ k ∧ 0 = 2 ^ k - 1 := by
      rintro ⟨k, hk, h⟩
      have h2 : 2 ≤ 2 ^ k := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hk)
      omega
    rw [if_neg hnot0, add_zero, if_pos ⟨1, le_refl 1, rfl⟩]
  | m + 2 =>
    simp only [show m + 2 ≠ 1 by omega, ↓reduceIte, zero_add,
      show m + 2 ≠ 0 by omega, show m + 2 - 1 = m + 1 by omega]
    rw [coeff_sq_mod2]
    by_cases hpar : (m + 1) % 2 = 0
    · rw [if_pos hpar, PowerSeries.coeff_mk]
      have hiff : (∃ k : ℕ, 1 ≤ k ∧ (m + 1) / 2 = 2 ^ k - 1) ↔
          (∃ k : ℕ, 1 ≤ k ∧ m + 2 = 2 ^ k - 1) := by
        constructor
        · rintro ⟨k, hk, h⟩
          have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
          exact ⟨k + 1, by omega, by rw [pow_succ]; omega⟩
        · rintro ⟨k, hk, h⟩
          have hk2 : 2 ≤ k := by
            by_contra hlt
            have : k = 1 := by omega
            subst this; norm_num at h; omega
          have h1 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow (k - 1) 2 (by decide)
          have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
          exact ⟨k - 1, by omega, by omega⟩
      by_cases hex : ∃ k : ℕ, 1 ≤ k ∧ (m + 1) / 2 = 2 ^ k - 1
      · rw [if_pos hex, if_pos (hiff.mp hex)]
      · rw [if_neg hex, if_neg (mt hiff.mpr hex)]
    · rw [if_neg hpar]
      have hnot : ¬ ∃ k : ℕ, 1 ≤ k ∧ m + 2 = 2 ^ k - 1 := by
        rintro ⟨k, hk, h⟩
        have hk2 : 2 ≤ k := by
          by_contra hlt
          have : k = 1 := by omega
          subst this; norm_num at h; omega
        have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
        have h1 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow (k - 1) 2 (by decide)
        omega
      rw [if_neg hnot]

private lemma seriesB_G_eq :
    PowerSeries.X ^ 2 * (1 - seriesB) ^ 2 = PowerSeries.X * seriesB := by
  have hsq : (1 - seriesB : PowerSeries (ZMod 2)) ^ 2 = 1 + seriesB ^ 2 := by
    calc (1 - seriesB : PowerSeries (ZMod 2)) ^ 2
        = 1 + seriesB ^ 2 - 2 * seriesB := by ring
      _ = 1 + seriesB ^ 2 := by rw [two_eq_zero_ps2, zero_mul, sub_zero]
  rw [hsq]
  calc PowerSeries.X ^ 2 * (1 + seriesB ^ 2)
      = PowerSeries.X * (PowerSeries.X + PowerSeries.X * seriesB ^ 2) := by ring
    _ = PowerSeries.X * seriesB := by rw [← seriesB_eq]

private lemma coeff_pow_zero_of_lt2 {G : PowerSeries (ZMod 2)}
    (hG0 : PowerSeries.coeff 0 G = 0) (hG1 : PowerSeries.coeff 1 G = 0) :
    ∀ k m : ℕ, m < 2 * k → PowerSeries.coeff m (G ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro m hm; omega
  | succ k ih =>
    intro m hm
    rw [pow_succ, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (G ^ k) * PowerSeries.coeff j G)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hlt : i < 2 * k
    · rw [ih i hlt, zero_mul]
    · have hmj : m - i = 0 ∨ m - i = 1 := by omega
      rcases hmj with h | h
      · rw [h, hG0, mul_zero]
      · rw [h, hG1, mul_zero]

private lemma coeff_pow_congr {G1 G2 : PowerSeries (ZMod 2)}
    (hG10 : PowerSeries.coeff 0 G1 = 0) (hG11 : PowerSeries.coeff 1 G1 = 0)
    (hG20 : PowerSeries.coeff 0 G2 = 0) (hG21 : PowerSeries.coeff 1 G2 = 0)
    {M : ℕ} (hagree : ∀ j ≤ M, PowerSeries.coeff j G1 = PowerSeries.coeff j G2) :
    ∀ k : ℕ, 2 ≤ k → ∀ m ≤ M + 2, PowerSeries.coeff m (G1 ^ k) = PowerSeries.coeff m (G2 ^ k) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    intro m hm
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (G1 ^ k) * PowerSeries.coeff j G1),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (G2 ^ k) * PowerSeries.coeff j G2)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases h1 : i < 2 * k
    · rw [coeff_pow_zero_of_lt2 hG10 hG11 k i h1, coeff_pow_zero_of_lt2 hG20 hG21 k i h1,
        zero_mul, zero_mul]
    · by_cases h2 : m - i < 2
      · have hcases : m - i = 0 ∨ m - i = 1 := by omega
        rcases hcases with h | h
        · rw [h, hG10, hG20, mul_zero, mul_zero]
        · rw [h, hG11, hG21, mul_zero, mul_zero]
      · have hmi_le : m - i ≤ M := by omega
        rw [hagree (m - i) hmi_le]
        congr 1
        by_cases hk1 : k = 1
        · subst hk1
          simp only [pow_one]
          exact hagree i (by omega)
        · exact ih (by omega) i (by omega)

private lemma unique_A2_eq_B (A2 G2 : PowerSeries (ZMod 2))
    (hA20 : PowerSeries.coeff 0 A2 = 0) (hA21 : PowerSeries.coeff 1 A2 = 1)
    (hGeq : G2 * (1 - A2) ^ 2 = PowerSeries.X * A2)
    (hA2eq : A2 ^ 2 = psComp2 A2 G2) : A2 = seriesB := by
  have hB0 : PowerSeries.coeff 0 seriesB = 0 := by
    simp only [seriesB, PowerSeries.coeff_mk]
    rw [if_neg]
    rintro ⟨k, hk, h⟩
    have h2 : 2 ≤ 2 ^ k := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hk)
    omega
  have hB1 : PowerSeries.coeff 1 seriesB = 1 := by
    simp only [seriesB, PowerSeries.coeff_mk]
    rw [if_pos ⟨1, le_refl 1, rfl⟩]
  have hsq_id : ∀ f : PowerSeries (ZMod 2), (1 - f) ^ 2 = 1 + f ^ 2 := by
    intro f
    calc (1 - f) ^ 2 = 1 + f ^ 2 - 2 * f := by ring
      _ = 1 + f ^ 2 := by rw [two_eq_zero_ps2, zero_mul, sub_zero]
  have hG2_eq' : G2 * (1 + A2 ^ 2) = PowerSeries.X * A2 := by
    rw [← hsq_id A2]; exact hGeq
  have hGB_eq' : PowerSeries.X ^ 2 * (1 + seriesB ^ 2) = PowerSeries.X * seriesB := by
    rw [← hsq_id seriesB]; exact seriesB_G_eq
  have h1A0 : PowerSeries.coeff 0 (1 + A2 ^ 2) = 1 := by
    rw [map_add, PowerSeries.coeff_one, coeff_sq_mod2]; simp [hA20]
  have h1A1 : PowerSeries.coeff 1 (1 + A2 ^ 2) = 0 := by
    rw [map_add, PowerSeries.coeff_one, coeff_sq_mod2]; simp
  have h1B0 : PowerSeries.coeff 0 (1 + seriesB ^ 2) = 1 := by
    rw [map_add, PowerSeries.coeff_one, coeff_sq_mod2]; simp [hB0]
  have hG20 : PowerSeries.coeff 0 G2 = 0 := by
    have h := congrArg (PowerSeries.coeff 0) hG2_eq'
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, h1A0, mul_one,
      coeff_X_mul_ps] at h
    simpa using h
  have hG21 : PowerSeries.coeff 1 G2 = 0 := by
    have h := congrArg (PowerSeries.coeff 1) hG2_eq'
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i G2 * PowerSeries.coeff j (1 + A2 ^ 2)),
      coeff_X_mul_ps] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add, Nat.sub_self, hG20, zero_mul, zero_add, h1A0, mul_one,
      if_neg (by decide : (1 : ℕ) ≠ 0), hA20] at h
    exact h
  have hX20 : PowerSeries.coeff 0 (PowerSeries.X ^ 2 : PowerSeries (ZMod 2)) = 0 := by
    rw [PowerSeries.coeff_X_pow]; simp
  have hX21 : PowerSeries.coeff 1 (PowerSeries.X ^ 2 : PowerSeries (ZMod 2)) = 0 := by
    rw [PowerSeries.coeff_X_pow]; simp
  have hBeq : seriesB ^ 2 = psComp2 seriesB (PowerSeries.X ^ 2) := (psComp2_X_sq seriesB).symm
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rw [hA20, hB0]
    | 1 => rw [hA21, hB1]
    | m + 2 =>
      -- Step 1: G2 agrees with X^2 up to index m + 2 (uses A2 = B up to m + 1)
      have hG_agree : ∀ j ≤ m + 2, PowerSeries.coeff j G2 = PowerSeries.coeff j (PowerSeries.X ^ 2) := by
        intro j
        induction j using Nat.strong_induction_on with
        | h j ihG =>
          intro hj
          have hcoeff := congrArg (PowerSeries.coeff j) hG2_eq'
          have hcoeffB := congrArg (PowerSeries.coeff j) hGB_eq'
          have hRHS : PowerSeries.coeff j (PowerSeries.X * A2) = PowerSeries.coeff j (PowerSeries.X * seriesB) := by
            rw [coeff_X_mul_ps, coeff_X_mul_ps]
            split_ifs
            · rfl
            · exact ih (j - 1) (by omega)
          have heq_mul : PowerSeries.coeff j (G2 * (1 + A2 ^ 2)) =
              PowerSeries.coeff j (PowerSeries.X ^ 2 * (1 + seriesB ^ 2)) := by
            rw [hcoeff, hcoeffB, hRHS]
          rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i l => PowerSeries.coeff i G2 * PowerSeries.coeff l (1 + A2 ^ 2)),
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i l => PowerSeries.coeff i (PowerSeries.X ^ 2) * PowerSeries.coeff l (1 + seriesB ^ 2))] at heq_mul
          conv at heq_mul => lhs; rw [Finset.sum_range_succ]
          conv at heq_mul => rhs; rw [Finset.sum_range_succ]
          simp only [Nat.sub_self, h1A0, h1B0, mul_one] at heq_mul
          have hpre :
              ∑ i ∈ Finset.range j, PowerSeries.coeff i G2 * PowerSeries.coeff (j - i) (1 + A2 ^ 2) =
              ∑ i ∈ Finset.range j, PowerSeries.coeff i (PowerSeries.X ^ 2) * PowerSeries.coeff (j - i) (1 + seriesB ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mem_range] at hi
            rw [ihG i hi (by omega)]
            congr 1
            rw [map_add, map_add, coeff_sq_mod2, coeff_sq_mod2]
            congr 1
            split_ifs
            · exact ih ((j - i) / 2) (by omega)
            · rfl
          rw [hpre] at heq_mul
          exact add_left_cancel heq_mul
      -- Step 2: [x^(m+3)] (A2^2) = [x^(m+3)] (B^2) gives coeff (m+3) G2 = coeff (m+3) (X^2)!
      have hLHS : PowerSeries.coeff (m + 3) (A2 ^ 2) = PowerSeries.coeff (m + 3) (seriesB ^ 2) := by
        rw [coeff_sq_mod2, coeff_sq_mod2]
        split_ifs
        · exact ih ((m + 3) / 2) (by omega)
        · rfl
      have hRHS_eq : PowerSeries.coeff (m + 3) (psComp2 A2 G2) =
          PowerSeries.coeff (m + 3) (psComp2 seriesB (PowerSeries.X ^ 2)) := by
        rw [← hA2eq, ← hBeq, hLHS]
      simp only [psComp2, PowerSeries.coeff_mk] at hRHS_eq
      conv at hRHS_eq => lhs; rw [Finset.sum_range_succ', Finset.sum_range_succ']
      conv at hRHS_eq => rhs; rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [hA20, hB0, zero_mul, add_zero, hA21, hB1, one_mul, Nat.zero_add, pow_one] at hRHS_eq
      have htail :
          ∑ k ∈ Finset.range (m + 2),
            PowerSeries.coeff (k + 1 + 1) A2 * PowerSeries.coeff (m + 3) (G2 ^ (k + 1 + 1)) =
          ∑ k ∈ Finset.range (m + 2),
            PowerSeries.coeff (k + 1 + 1) seriesB * PowerSeries.coeff (m + 3) ((PowerSeries.X ^ 2) ^ (k + 1 + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        by_cases hlt : m + 3 < 2 * (k + 1 + 1)
        · rw [coeff_pow_zero_of_lt2 hG20 hG21 (k + 1 + 1) (m + 3) hlt,
            coeff_pow_zero_of_lt2 hX20 hX21 (k + 1 + 1) (m + 3) hlt, mul_zero, mul_zero]
        · have hklt : k + 1 + 1 < m + 2 := by omega
          rw [ih (k + 1 + 1) hklt]
          congr 1
          exact coeff_pow_congr hG20 hG21 hX20 hX21 (fun j hj => hG_agree j (by omega)) (k + 1 + 1) (by omega) (m + 3) (by omega)
      have hGm3 : PowerSeries.coeff (m + 3) G2 = PowerSeries.coeff (m + 3) (PowerSeries.X ^ 2) := by
        rw [htail] at hRHS_eq
        exact add_left_cancel hRHS_eq
      -- Step 3: [x^(m+3)] (G2 * (1 + A2^2)) = [x^(m+3)] (X * A2) yields coeff (m+2) A2 = coeff (m+2) B!
      have hmul_eq : PowerSeries.coeff (m + 3) (G2 * (1 + A2 ^ 2)) =
          PowerSeries.coeff (m + 3) (PowerSeries.X ^ 2 * (1 + seriesB ^ 2)) := by
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i l => PowerSeries.coeff i G2 * PowerSeries.coeff l (1 + A2 ^ 2)),
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i l => PowerSeries.coeff i (PowerSeries.X ^ 2) * PowerSeries.coeff l (1 + seriesB ^ 2))]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hGi : PowerSeries.coeff i G2 = PowerSeries.coeff i (PowerSeries.X ^ 2) := by
          by_cases him : i = m + 3
          · subst him; exact hGm3
          · exact hG_agree i (by omega)
        rw [hGi]
        congr 1
        rw [map_add, map_add, coeff_sq_mod2, coeff_sq_mod2]
        congr 1
        split_ifs
        · exact ih ((m + 3 - i) / 2) (by omega)
        · rfl
      rw [hG2_eq', hGB_eq', coeff_X_mul_ps, coeff_X_mul_ps] at hmul_eq
      simpa using hmul_eq

private lemma map_A_eq_seriesB {A : PowerSeries ℤ} (hA : IsA373312 A) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) A = seriesB := by
  rcases hA with ⟨hA0, hA1, G, hGeq, hAeq⟩
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hA20 : PowerSeries.coeff 0 (phi A) = 0 := by simp [phi, hA0]
  have hA21 : PowerSeries.coeff 1 (phi A) = 1 := by simp [phi, hA1]
  have hG2eq : phi G * (1 - phi A) ^ 2 = PowerSeries.X * phi A := by
    have h := congrArg phi hGeq
    simp only [map_mul, map_pow, map_sub, map_one] at h
    dsimp only [phi] at h
    rw [PowerSeries.map_X] at h
    exact h
  have hA2eq : (phi A) ^ 2 = psComp2 (phi A) (phi G) := by
    have h := congrArg phi hAeq
    rw [map_pow, map_psComp] at h
    exact h
  exact unique_A2_eq_B (phi A) (phi G) hA20 hA21 hG2eq hA2eq

end OeisA373312Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a373312.main := by
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
  have h := congrArg (PowerSeries.coeff n) (OeisA373312Proof.map_A_eq_seriesB hA)
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom, OeisA373312Proof.seriesB,
    PowerSeries.coeff_mk] at h
  rw [h]
  split_ifs with hex
  · simp [hex]
  · simp [hex]
