import OMAStatements.S_oeis_a374570
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA374570Proof

open Classical
open OMA.S_oeis_a374570

private noncomputable def psComp2 (F G : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

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
      · -- Both i ≥ 2k ≥ 2 and m - i ≥ 2, so i ≤ M and m - i ≤ M!
        have hmi_le : m - i ≤ M := by omega
        rw [hagree (m - i) hmi_le]
        congr 1
        by_cases hk1 : k = 1
        · subst hk1
          simp only [pow_one]
          exact hagree i (by omega)
        · exact ih (by omega) i (by omega)

private lemma unique_A2_eq_B2 (A2 B2 C2 : PowerSeries (ZMod 2))
    (hC20 : PowerSeries.coeff 0 C2 = 0) (hC21 : PowerSeries.coeff 1 C2 = 1)
    (hA20 : PowerSeries.coeff 0 A2 = 0) (hA21 : PowerSeries.coeff 1 A2 = 1)
    (hB20 : PowerSeries.coeff 0 B2 = 0) (hB21 : PowerSeries.coeff 1 B2 = 1)
    (hA2eq : A2 ^ 2 = psComp2 A2 (A2 * C2))
    (hB2eq : B2 ^ 2 = psComp2 B2 (B2 * C2))
    (hAC0 : PowerSeries.coeff 0 (A2 * C2) = 0) (hAC1 : PowerSeries.coeff 1 (A2 * C2) = 0)
    (hBC0 : PowerSeries.coeff 0 (B2 * C2) = 0) (hBC1 : PowerSeries.coeff 1 (B2 * C2) = 0) :
    A2 = B2 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rw [hA20, hB20]
    | 1 => rw [hA21, hB21]
    | m + 2 =>
      have hAC_agree : ∀ j ≤ m + 2, PowerSeries.coeff j (A2 * C2) = PowerSeries.coeff j (B2 * C2) := by
        intro j hj
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i l => PowerSeries.coeff i A2 * PowerSeries.coeff l C2),
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i l => PowerSeries.coeff i B2 * PowerSeries.coeff l C2)]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        by_cases hij : i = j
        · subst hij; rw [Nat.sub_self, hC20, mul_zero, mul_zero]
        · rw [ih i (by omega)]
      have hLHS : PowerSeries.coeff (m + 3) (A2 ^ 2) = PowerSeries.coeff (m + 3) (B2 ^ 2) := by
        rw [coeff_sq_mod2, coeff_sq_mod2]
        split_ifs
        · exact ih ((m + 3) / 2) (by omega)
        · rfl
      have hRHS_eq : PowerSeries.coeff (m + 3) (psComp2 A2 (A2 * C2)) =
          PowerSeries.coeff (m + 3) (psComp2 B2 (B2 * C2)) := by
        rw [← hA2eq, ← hB2eq, hLHS]
      simp only [psComp2, PowerSeries.coeff_mk] at hRHS_eq
      conv at hRHS_eq =>
        lhs
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
      conv at hRHS_eq =>
        rhs
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [hA20, hB20, zero_mul, add_zero, hA21, hB21, one_mul, Nat.zero_add, pow_one] at hRHS_eq
      have htail :
          ∑ k ∈ Finset.range (m + 2),
            PowerSeries.coeff (k + 1 + 1) A2 * PowerSeries.coeff (m + 3) ((A2 * C2) ^ (k + 1 + 1)) =
          ∑ k ∈ Finset.range (m + 2),
            PowerSeries.coeff (k + 1 + 1) B2 * PowerSeries.coeff (m + 3) ((B2 * C2) ^ (k + 1 + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        by_cases hlt : m + 3 < 2 * (k + 1 + 1)
        · rw [coeff_pow_zero_of_lt2 hAC0 hAC1 (k + 1 + 1) (m + 3) hlt,
            coeff_pow_zero_of_lt2 hBC0 hBC1 (k + 1 + 1) (m + 3) hlt, mul_zero, mul_zero]
        · have hklt : k + 1 + 1 < m + 2 := by omega
          rw [ih (k + 1 + 1) hklt]
          congr 1
          exact coeff_pow_congr hAC0 hAC1 hBC0 hBC1 hAC_agree (k + 1 + 1) (by omega) (m + 3) (by omega)
      have hmul_eq : PowerSeries.coeff (m + 3) (A2 * C2) = PowerSeries.coeff (m + 3) (B2 * C2) := by
        rw [htail] at hRHS_eq
        exact add_left_cancel hRHS_eq
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i l => PowerSeries.coeff i A2 * PowerSeries.coeff l C2),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i l => PowerSeries.coeff i B2 * PowerSeries.coeff l C2)] at hmul_eq
      conv at hmul_eq =>
        lhs
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
      conv at hmul_eq =>
        rhs
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Nat.sub_self, hC20, mul_zero, add_zero,
        show m + 3 - (m + 2) = 1 by omega, hC21, mul_one] at hmul_eq
      have hpre :
          ∑ x ∈ Finset.range (m + 2), PowerSeries.coeff x A2 * PowerSeries.coeff (m + 3 - x) C2 =
          ∑ x ∈ Finset.range (m + 2), PowerSeries.coeff x B2 * PowerSeries.coeff (m + 3 - x) C2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_range] at hx
        rw [ih x hx]
      rw [hpre] at hmul_eq
      exact add_left_cancel hmul_eq

private lemma coeff_A_eq_X_add_X_mul_C_mod2 {A C : PowerSeries ℤ}
    (hA0 : PowerSeries.coeff 0 A = 0) (hA1 : PowerSeries.coeff 1 A = 1)
    (hC : IsCatalanX C) (heq : A ^ 2 = psComp A (A * C)) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) A =
      PowerSeries.X + PowerSeries.X * PowerSeries.map (Int.castRingHom (ZMod 2)) C := by
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let A2 := phi A
  let C2 := phi C
  let B2 : PowerSeries (ZMod 2) := PowerSeries.X + PowerSeries.X * C2
  have hC20 : PowerSeries.coeff 0 C2 = 0 := by simp [C2, phi, hC.1]
  have hC2eq : C2 = PowerSeries.X + C2 ^ 2 := by
    have h := congrArg phi hC.2; simpa [phi, C2] using h
  have hC21 : PowerSeries.coeff 1 C2 = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hC2eq
    rw [map_add, PowerSeries.coeff_X, if_pos rfl, coeff_sq_mod2] at h
    simpa using h
  have hA20 : PowerSeries.coeff 0 A2 = 0 := by simp [A2, phi, hA0]
  have hA21 : PowerSeries.coeff 1 A2 = 1 := by simp [A2, phi, hA1]
  have hB20 : PowerSeries.coeff 0 B2 = 0 := by simp [B2]
  have hB21 : PowerSeries.coeff 1 B2 = 1 := by simp [B2, PowerSeries.coeff_X, hC20]
  have hA2eq : A2 ^ 2 = psComp2 A2 (A2 * C2) := by
    have h := congrArg phi heq
    rw [map_pow, map_psComp, map_mul] at h
    exact h
  have hB2mulC2 : B2 * C2 = PowerSeries.X ^ 2 := by
    have h2z : (2 : PowerSeries (ZMod 2)) = 0 := by
      ext k; rw [show (2 : PowerSeries (ZMod 2)) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C]
      split_ifs <;> simp [show (2 : ZMod 2) = 0 by decide]
    have hCadd : C2 + C2 ^ 2 = PowerSeries.X := by
      have h1 : C2 + C2 ^ 2 = PowerSeries.X + (C2 ^ 2 + C2 ^ 2) := by
        conv_lhs => arg 1; rw [hC2eq]
        ring
      rw [h1, ← two_mul, h2z, zero_mul, add_zero]
    calc B2 * C2 = PowerSeries.X * (C2 + C2 ^ 2) := by dsimp only [B2]; ring
      _ = PowerSeries.X * PowerSeries.X := by rw [hCadd]
      _ = PowerSeries.X ^ 2 := by ring
  have hB2eq : B2 ^ 2 = psComp2 B2 (B2 * C2) := by
    rw [hB2mulC2, psComp2_X_sq]
  have hAC0 : PowerSeries.coeff 0 (A2 * C2) = 0 := by
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hA20, zero_mul]
  have hAC1 : PowerSeries.coeff 1 (A2 * C2) = 0 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i A2 * PowerSeries.coeff j C2)]
    simp [Finset.sum_range_succ, hA20, hC20]
  have hBC0 : PowerSeries.coeff 0 (B2 * C2) = 0 := by
    rw [hB2mulC2, PowerSeries.coeff_X_pow]; simp
  have hBC1 : PowerSeries.coeff 1 (B2 * C2) = 0 := by
    rw [hB2mulC2, PowerSeries.coeff_X_pow]; simp
  exact unique_A2_eq_B2 A2 B2 C2 hC20 hC21 hA20 hA21 hB20 hB21 hA2eq hB2eq hAC0 hAC1 hBC0 hBC1

private lemma catalanX_mod2 {C : PowerSeries ℤ} (hC : IsCatalanX C) :
    ∀ n : ℕ, PowerSeries.coeff n (PowerSeries.map (Int.castRingHom (ZMod 2)) C) =
      if ∃ k : ℕ, n = 2 ^ k then 1 else 0 := by
  let C2 := PowerSeries.map (Int.castRingHom (ZMod 2)) C
  have hC20 : PowerSeries.coeff 0 C2 = 0 := by simp [C2, hC.1]
  have hC2 : C2 = PowerSeries.X + C2 ^ 2 := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) hC.2
    simpa [C2] using h
  intro n
  change PowerSeries.coeff n C2 = _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      rw [hC20, if_neg (by rintro ⟨k, hk⟩; have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide); omega)]
    | 1 =>
      have h := congrArg (PowerSeries.coeff 1) hC2
      rw [map_add, PowerSeries.coeff_X, if_pos rfl, coeff_sq_mod2] at h
      simpa [if_pos (⟨0, rfl⟩ : ∃ k : ℕ, 1 = 2 ^ k)] using h
    | m + 2 =>
      rw [hC2, map_add, PowerSeries.coeff_X, if_neg (by omega), zero_add, coeff_sq_mod2]
      by_cases hpar : (m + 2) % 2 = 0
      · rw [if_pos hpar, ih ((m + 2) / 2) (by omega)]
        have hiff : (∃ k : ℕ, (m + 2) / 2 = 2 ^ k) ↔ (∃ k : ℕ, m + 2 = 2 ^ k) := by
          constructor
          · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [pow_succ]; omega⟩
          · rintro ⟨k, hk⟩
            cases k with
            | zero => omega
            | succ k' => exact ⟨k', by rw [pow_succ] at hk; omega⟩
        by_cases hex : ∃ k : ℕ, (m + 2) / 2 = 2 ^ k
        · rw [if_pos hex, if_pos (hiff.mp hex)]
        · rw [if_neg hex, if_neg (mt hiff.mpr hex)]
      · rw [if_neg hpar]
        have hnot : ¬ ∃ k : ℕ, m + 2 = 2 ^ k := by
          rintro ⟨k, hk⟩
          cases k with
          | zero => omega
          | succ k' => rw [pow_succ] at hk; omega
        rw [if_neg hnot]

end OeisA374570Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a374570.main := by
  intro A ⟨hA0, hA1, C, hC, heq⟩ n hn
  have hA2 := OeisA374570Proof.coeff_A_eq_X_add_X_mul_C_mod2 hA0 hA1 hC heq
  have hc := congrArg (PowerSeries.coeff n) hA2
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom, map_add, PowerSeries.coeff_X,
    OeisA374570Proof.coeff_X_mul_ps] at hc
  rw [if_neg (by omega : n ≠ 1), zero_add, if_neg (by omega : n ≠ 0)] at hc
  have hmod : PowerSeries.coeff n A % 2 = 1 ↔ ((PowerSeries.coeff n A : ℤ) : ZMod 2) = 1 := by
    constructor
    · intro h
      have h' : PowerSeries.coeff n A ≡ 1 [ZMOD ((2 : ℕ) : ℤ)] := by rw [Int.ModEq]; omega
      simpa using (ZMod.intCast_eq_intCast_iff _ _ 2).mpr h'
    · intro h
      have h' : PowerSeries.coeff n A ≡ 1 [ZMOD ((2 : ℕ) : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff _ _ 2).mp (by simpa using h)
      rw [Int.ModEq] at h'; omega
  have hcC := OeisA374570Proof.catalanX_mod2 hC (n - 1)
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom] at hcC
  rw [hmod, hc, hcC]
  have hiff : (∃ k : ℕ, n - 1 = 2 ^ k) ↔ (∃ k : ℕ, n = 2 ^ k + 1) := by
    constructor <;> (rintro ⟨k, hk⟩; exact ⟨k, by omega⟩)
  split_ifs with h
  · simp [hiff.mp h]
  · simp [mt hiff.mpr h]
