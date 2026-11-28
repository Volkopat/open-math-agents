import OMAStatements.S_oeis_a361552

/-!
Proof of the OEIS A361552 conjectures (Paul D. Hanna).

1. Existence of `A` satisfying `SatisfiesA361552` and `B` satisfying `SatisfiesA359914` via
   structural list recursion (`buildListA`, `buildListB`).
2. By strong induction on `k ≥ 1`, `2 ∣ A.coeff k` and `2 ∣ B.coeff k`.
3. Writing `A = 1 + 2 * D` and `B = 1 + 2 * E` (`D.coeff 0 = E.coeff 0 = 0`), modulo `4`
   every paired summand in A361552 collapses to
   `2 * (X^(m*(3*m-1)/2) + X^(m*(3*m+1)/2)) * D (mod 4)`, giving
   `pentagonalSeries (ZMod 2) * (D mod 2) = X`.
4. Similarly, every paired summand in A359914 collapses to
   `2 * (X^(m*(3*m-1)/2) + X^(m*(3*m+1)/2)) * (1 + E) (mod 4)`, giving
   `pentagonalSeries (ZMod 2) * (1 + E mod 2) = 1`.
5. Combining Euler's pentagonal number theorem (`PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq`)
   and Mathlib's partition generating function (`Nat.Partition.hasProd_genFun`), we prove
   `pentagonalSeries (ZMod 2) * P = 1`, where `P.coeff n = (A000041 n : ZMod 2)`.
6. Therefore `D ≡ X * P (mod 2)` and `1 + E ≡ P (mod 2)`, yielding:
   - for all `n ≥ 1`: `2 ∣ A.coeff n` and `(A.coeff n / 2) % 2 = (A000041 (n - 1) : ℤ) % 2`;
   - for all `n > 1`: `A.coeff n ≡ B.coeff (n - 1) [ZMOD 4]`.
-/

namespace A361552Proof

open Finset OMA.S_oeis_a361552

private lemma coeff_mul_eq_of_prefix {R : Type*} [CommRing R] {F₁ F₂ G₁ G₂ : PowerSeries R} {n : ℕ}
    (hF : ∀ j ≤ n, F₁.coeff j = F₂.coeff j) (hG : ∀ j ≤ n, G₁.coeff j = G₂.coeff j) :
    ∀ k ≤ n, (F₁ * G₁).coeff k = (F₂ * G₂).coeff k := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [hF p.1 (by omega), hG p.2 (by omega)]

private lemma coeff_pow_eq_of_prefix {F₁ F₂ : PowerSeries ℤ} {n : ℕ}
    (hF : ∀ j ≤ n, F₁.coeff j = F₂.coeff j) :
    ∀ e k : ℕ, k ≤ n → (F₁ ^ e).coeff k = (F₂ ^ e).coeff k := by
  intro e
  induction e with
  | zero => intro k _; rfl
  | succ e ih =>
    intro k hk
    rw [pow_succ, pow_succ]
    exact coeff_mul_eq_of_prefix (fun j hj => ih j hj) hF k hk

private lemma coeff_pow_eq_zero_of_lt {F : PowerSeries ℤ} (hF : F.coeff 0 = 0) :
    ∀ e k : ℕ, k < e → (F ^ e).coeff k = 0 := by
  intro e
  induction e with
  | zero => intro k hk; omega
  | succ e ih =>
    intro k hk
    rw [pow_succ, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases hp2 : p.2 = 0
    · rw [hp2, hF, mul_zero]
    · rw [ih p.1 (by omega), zero_mul]

private lemma coeff_invOfUnit_zero (A : PowerSeries ℤ) : (invOfUnit A).coeff 0 = 1 := by
  unfold invOfUnit
  rw [PowerSeries.coeff_mk]
  simp

private lemma coeff_invOfUnit_eq_of_prefix {A B : PowerSeries ℤ} {n : ℕ}
    (h : ∀ j ≤ n, A.coeff j = B.coeff j) :
    ∀ k ≤ n, (invOfUnit A).coeff k = (invOfUnit B).coeff k := by
  intro k hk
  unfold invOfUnit
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : ∀ i ≤ n, (1 - A).coeff i = (1 - B).coeff i := by
    intro i hi
    rw [map_sub, map_sub, h i hi]
  exact coeff_pow_eq_of_prefix h1 j k hk

private lemma mul_invOfUnit {A : PowerSeries ℤ} (hA0 : A.coeff 0 = 1) :
    A * invOfUnit A = 1 := by
  set F : PowerSeries ℤ := 1 - A
  have hF0 : F.coeff 0 = 0 := by
    show (1 - A).coeff 0 = 0
    rw [map_sub, PowerSeries.coeff_one, if_pos rfl, hA0, sub_self]
  have hAeq : A = 1 - F := by simp [F]
  ext k
  have hlhs : (A * invOfUnit A).coeff k = (invOfUnit A).coeff k - (F * invOfUnit A).coeff k := by
    have hmulA : A * invOfUnit A = (1 - F) * invOfUnit A := congrArg (· * invOfUnit A) hAeq
    rw [hmulA, sub_mul, one_mul, map_sub]
  rw [hlhs]
  have hmul : (F * invOfUnit A).coeff k = ∑ j ∈ Finset.range (k + 1), (F ^ (j + 1)).coeff k := by
    rw [PowerSeries.coeff_mul]
    have hstep : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        F.coeff p.1 * (invOfUnit A).coeff p.2 =
        ∑ j ∈ Finset.range (k + 1), F.coeff p.1 * (F ^ j).coeff p.2 := by
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      unfold invOfUnit
      rw [PowerSeries.coeff_mk, Finset.mul_sum]
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hnot
      rw [Finset.mem_range] at hj hnot
      rw [coeff_pow_eq_zero_of_lt hF0 j p.2 (by omega), mul_zero]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ', PowerSeries.coeff_mul]
  have hinv : (invOfUnit A).coeff k = ∑ j ∈ Finset.range (k + 1), (F ^ j).coeff k := by
    unfold invOfUnit
    rw [PowerSeries.coeff_mk]
  rw [hinv, hmul]
  have htele :
      (∑ j ∈ Finset.range (k + 1), (F ^ j).coeff k) -
      (∑ j ∈ Finset.range (k + 1), (F ^ (j + 1)).coeff k) =
      (F ^ 0).coeff k - (F ^ (k + 1)).coeff k := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    ring
  rw [htele, pow_zero, coeff_pow_eq_zero_of_lt hF0 (k + 1) k (by omega), sub_zero]

private lemma pent1_ge {m : ℕ} (hm : 1 ≤ m) : m ≤ m * (3 * m - 1) / 2 := by
  have h1 : 2 * m ≤ m * (3 * m - 1) := by
    have : 2 ≤ 3 * m - 1 := by omega
    nlinarith
  omega

private lemma pent2_ge {m : ℕ} (hm : 1 ≤ m) : m ≤ m * (3 * m + 1) / 2 := by
  have h1 : 2 * m ≤ m * (3 * m + 1) := by nlinarith
  omega

private lemma coeff_term359914_eq_of_strict_prefix {A B : PowerSeries ℤ} {k m : ℕ}
    (hm : 1 ≤ m) (h : ∀ j < k, A.coeff j = B.coeff j) :
    (term359914 A m).coeff k = (term359914 B m).coeff k := by
  unfold term359914
  have hneg : ((-1 : PowerSeries ℤ) ^ m) = PowerSeries.C ((-1 : ℤ) ^ m) := by simp
  rw [hneg, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  congr 1
  rw [map_add, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  have hp1 : 1 ≤ m * (3 * m - 1) / 2 := le_trans hm (pent1_ge hm)
  have hp2 : 1 ≤ m * (3 * m + 1) / 2 := le_trans hm (pent2_ge hm)
  congr 1
  · split_ifs with hle
    · cases k with
      | zero => omega
      | succ k' =>
        have hpre : ∀ j ≤ k', A.coeff j = B.coeff j := fun j hj => h j (by omega)
        rw [map_add, map_add,
          coeff_pow_eq_of_prefix hpre (3 * m) _ (by omega),
          coeff_pow_eq_of_prefix (coeff_invOfUnit_eq_of_prefix hpre) (3 * m - 1) _ (by omega)]
    · rfl
  · split_ifs with hle
    · cases k with
      | zero => omega
      | succ k' =>
        have hpre : ∀ j ≤ k', A.coeff j = B.coeff j := fun j hj => h j (by omega)
        rw [map_add, map_add,
          coeff_pow_eq_of_prefix hpre (3 * m + 1) _ (by omega),
          coeff_pow_eq_of_prefix (coeff_invOfUnit_eq_of_prefix hpre) (3 * m) _ (by omega)]
    · rfl

private lemma coeff_term361552_eq_of_strict_prefix {A B : PowerSeries ℤ} {k m : ℕ}
    (hm : 1 ≤ m) (h : ∀ j < k, A.coeff j = B.coeff j) :
    (term361552 A m).coeff k = (term361552 B m).coeff k := by
  unfold term361552
  rw [map_add, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  have hp1 : 1 ≤ m * (3 * m - 1) / 2 := le_trans hm (pent1_ge hm)
  have hp2 : 1 ≤ m * (3 * m + 1) / 2 := le_trans hm (pent2_ge hm)
  congr 1
  · split_ifs with hle
    · cases k with
      | zero => omega
      | succ k' =>
        have hpre : ∀ j ≤ k', A.coeff j = B.coeff j := fun j hj => h j (by omega)
        rw [map_sub, map_sub,
          coeff_pow_eq_of_prefix hpre (3 * m) _ (by omega),
          coeff_pow_eq_of_prefix (coeff_invOfUnit_eq_of_prefix hpre) (3 * m + 1) _ (by omega)]
    · rfl
  · split_ifs with hle
    · cases k with
      | zero => omega
      | succ k' =>
        have hpre : ∀ j ≤ k', A.coeff j = B.coeff j := fun j hj => h j (by omega)
        rw [map_sub, map_sub,
          coeff_pow_eq_of_prefix (coeff_invOfUnit_eq_of_prefix hpre) (3 * m) _ (by omega),
          coeff_pow_eq_of_prefix hpre (3 * m - 1) _ (by omega)]
    · rfl

private noncomputable def buildListB : ℕ → List ℤ
  | 0 => []
  | k + 1 =>
    let L := buildListB k
    let val : ℤ :=
      if k = 0 then 1
      else
        let Bprev : PowerSeries ℤ := PowerSeries.mk fun j => L.getD j 0
        (-(∑ m ∈ Finset.Icc 1 k, (term359914 Bprev m).coeff k))
    L ++ [val]

private lemma buildListB_length (n : ℕ) : (buildListB n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildListB, ih]

private lemma buildListB_getD_of_lt : ∀ (n j : ℕ), j < n →
    (buildListB n).getD j 0 = (buildListB (j + 1)).getD j 0 := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with rfl | hlt
    · rfl
    · simp only [buildListB, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [buildListB_length]; exact hlt)]
      exact ih j hlt

private noncomputable def buildSeqB (k : ℕ) : ℤ :=
  (buildListB (k + 1)).getD k 0

private lemma exists_A359914 : ∃ B : PowerSeries ℤ, SatisfiesA359914 B := by
  let B : PowerSeries ℤ := PowerSeries.mk buildSeqB
  refine ⟨B, ?_, ?_⟩
  · rw [PowerSeries.coeff_mk]
    unfold buildSeqB
    simp [buildListB]
  · intro k hk
    rw [PowerSeries.coeff_mk]
    unfold buildSeqB
    have hlen : (buildListB k).length = k := buildListB_length k
    have hlast : (buildListB (k + 1)).getD k 0 =
        let Bprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildListB k).getD j 0
        (-(∑ m ∈ Finset.Icc 1 k, (term359914 Bprev m).coeff k)) := by
      conv_lhs => unfold buildListB
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]), hlen,
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, show k ≠ 0 by omega, ↓reduceIte]
    rw [hlast]
    let Bprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildListB k).getD j 0
    have hpre : ∀ j < k, Bprev.coeff j = B.coeff j := by
      intro j hj
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      exact buildListB_getD_of_lt k j hj
    have hsum : ∑ m ∈ Finset.Icc 1 k, (term359914 Bprev m).coeff k =
        ∑ m ∈ Finset.Icc 1 k, (term359914 B m).coeff k :=
      Finset.sum_congr rfl fun m hm =>
        coeff_term359914_eq_of_strict_prefix (Finset.mem_Icc.mp hm).1 hpre
    change -(∑ m ∈ Finset.Icc 1 k, (term359914 Bprev m).coeff k) + _ = 0
    rw [hsum, neg_add_cancel]

private noncomputable def restInv (A : PowerSeries ℤ) (k : ℕ) : ℤ :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0),
    A.coeff p.1 * (invOfUnit A).coeff p.2

private lemma neg_invOfUnit_coeff {A : PowerSeries ℤ} (hA0 : A.coeff 0 = 1) {k : ℕ} (hk : 1 ≤ k) :
    -(invOfUnit A).coeff k = A.coeff k + restInv A k := by
  have h0 : (A * invOfUnit A).coeff k = 0 := by
    rw [mul_invOfUnit hA0, PowerSeries.coeff_one, if_neg (by omega)]
  rw [PowerSeries.coeff_mul] at h0
  have hmem1 : (k, 0) ∈ Finset.HasAntidiagonal.antidiagonal k :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)
  have hmem2 : (0, k) ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (k, 0) := by
    rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨by intro h; have := (Prod.mk.inj h).1; omega, by omega⟩
  have hfilt : ((Finset.HasAntidiagonal.antidiagonal k).erase (k, 0)).erase (0, k) =
      (Finset.HasAntidiagonal.antidiagonal k).filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0) := by
    ext p
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
    constructor
    · rintro ⟨h2, h1, hsum⟩
      refine ⟨hsum, ?_, ?_⟩
      · intro hp1; exact h2 (Prod.ext hp1 (by omega))
      · intro hp2; exact h1 (Prod.ext (by omega) hp2)
    · rintro ⟨hsum, hp1, hp2⟩
      exact ⟨fun h => hp1 (Prod.mk.inj h).1, fun h => hp2 (Prod.mk.inj h).2, hsum⟩
  rw [← Finset.add_sum_erase _ _ hmem1, ← Finset.add_sum_erase _ _ hmem2, hfilt] at h0
  rw [coeff_invOfUnit_zero, hA0, mul_one, one_mul] at h0
  unfold restInv
  linarith

private lemma restInv_eq_of_strict_prefix {A₁ A₂ : PowerSeries ℤ} {k : ℕ}
    (h : ∀ j < k, A₁.coeff j = A₂.coeff j) : restInv A₁ k = restInv A₂ k := by
  unfold restInv
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
  cases k with
  | zero => omega
  | succ k' =>
    have hpre : ∀ j ≤ k', A₁.coeff j = A₂.coeff j := fun j hj => h j (by omega)
    rw [hpre p.1 (by omega), coeff_invOfUnit_eq_of_prefix hpre p.2 (by omega)]

private noncomputable def buildListA : ℕ → List ℤ
  | 0 => []
  | k + 1 =>
    let L := buildListA k
    let val : ℤ :=
      if k = 0 then 1
      else
        let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => L.getD j 0
        (if k = 1 then (2 : ℤ) else 0) - restInv Aprev k -
          ∑ m ∈ Finset.Icc 1 k, (term361552 Aprev m).coeff k
    L ++ [val]

private lemma buildListA_length (n : ℕ) : (buildListA n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildListA, ih]

private lemma buildListA_getD_of_lt : ∀ (n j : ℕ), j < n →
    (buildListA n).getD j 0 = (buildListA (j + 1)).getD j 0 := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with rfl | hlt
    · rfl
    · simp only [buildListA, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [buildListA_length]; exact hlt)]
      exact ih j hlt

private noncomputable def buildSeqA (k : ℕ) : ℤ :=
  (buildListA (k + 1)).getD k 0

private lemma exists_A361552 : ∃ A : PowerSeries ℤ, SatisfiesA361552 A := by
  let A : PowerSeries ℤ := PowerSeries.mk buildSeqA
  have hA0 : A.coeff 0 = 1 := by
    rw [PowerSeries.coeff_mk]
    unfold buildSeqA
    simp [buildListA]
  refine ⟨A, hA0, fun k hk => ?_⟩
  rw [neg_invOfUnit_coeff hA0 hk]
  have hAk : A.coeff k = (if k = 1 then (2 : ℤ) else 0) - restInv A k -
      ∑ m ∈ Finset.Icc 1 k, (term361552 A m).coeff k := by
    rw [PowerSeries.coeff_mk]
    unfold buildSeqA
    have hlen : (buildListA k).length = k := buildListA_length k
    have hlast : (buildListA (k + 1)).getD k 0 =
        let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildListA k).getD j 0
        (if k = 1 then (2 : ℤ) else 0) - restInv Aprev k -
          ∑ m ∈ Finset.Icc 1 k, (term361552 Aprev m).coeff k := by
      conv_lhs => unfold buildListA
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]), hlen,
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, show k ≠ 0 by omega, ↓reduceIte]
    rw [hlast]
    let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildListA k).getD j 0
    have hpre : ∀ j < k, Aprev.coeff j = A.coeff j := by
      intro j hj
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      exact buildListA_getD_of_lt k j hj
    have hrest : restInv Aprev k = restInv A k := restInv_eq_of_strict_prefix hpre
    have hsum : ∑ m ∈ Finset.Icc 1 k, (term361552 Aprev m).coeff k =
        ∑ m ∈ Finset.Icc 1 k, (term361552 A m).coeff k :=
      Finset.sum_congr rfl fun m hm =>
        coeff_term361552_eq_of_strict_prefix (Finset.mem_Icc.mp hm).1 hpre
    change (if k = 1 then (2 : ℤ) else 0) - restInv Aprev k - _ = _
    rw [hrest, hsum]
  linarith

private lemma mod2_pow_of_unit_prefix {F : PowerSeries ℤ} {n : ℕ}
    (h0 : F.coeff 0 = 1) (h2 : ∀ j, 1 ≤ j → j ≤ n → (2 : ℤ) ∣ F.coeff j) :
    ∀ e j : ℕ, j ≤ n → ((F ^ e).coeff j : ZMod 2) = if j = 0 then 1 else 0 := by
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hF : ∀ j ≤ n, (φ F).coeff j = (1 : PowerSeries (ZMod 2)).coeff j := by
    intro j hj
    rw [PowerSeries.coeff_map, PowerSeries.coeff_one]
    by_cases hj0 : j = 0
    · subst hj0; rw [if_pos rfl, h0]; simp
    · rw [if_neg hj0]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (h2 j (by omega) hj)
  have hpow : ∀ e j : ℕ, j ≤ n → ((φ F) ^ e).coeff j = ((1 : PowerSeries (ZMod 2)) ^ e).coeff j := by
    intro e
    induction e with
    | zero => intro j _; rfl
    | succ e ih =>
      intro j hj
      rw [pow_succ, pow_succ]
      exact coeff_mul_eq_of_prefix (fun i hi => ih i hi) hF j hj
  intro e j hj
  have h1 := hpow e j hj
  rw [← map_pow, PowerSeries.coeff_map, one_pow, PowerSeries.coeff_one] at h1
  exact h1

private lemma mod2_invOfUnit_of_unit_prefix {F : PowerSeries ℤ} {n : ℕ}
    (h0 : F.coeff 0 = 1) (h2 : ∀ j, 1 ≤ j → j ≤ n → (2 : ℤ) ∣ F.coeff j) :
    ∀ j, 1 ≤ j → j ≤ n → (2 : ℤ) ∣ (invOfUnit F).coeff j := by
  intro j hj1 hjn
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hneg := neg_invOfUnit_coeff h0 hj1
    have hrest : (2 : ℤ) ∣ restInv F j := by
      unfold restInv
      apply Finset.dvd_sum
      intro p hp
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
      exact dvd_mul_of_dvd_left (h2 p.1 (by omega) (by omega)) _
    have hFj : (2 : ℤ) ∣ F.coeff j := h2 j hj1 hjn
    have hsum : (2 : ℤ) ∣ (-(invOfUnit F).coeff j) := by rw [hneg]; exact dvd_add hFj hrest
    exact dvd_neg.mp hsum

private lemma two_dvd_A359914 {B : PowerSeries ℤ} (hB : SatisfiesA359914 B) :
    ∀ k : ℕ, 1 ≤ k → (2 : ℤ) ∣ B.coeff k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hsum2 : (2 : ℤ) ∣ ∑ m ∈ Finset.Icc 1 k, (term359914 B m).coeff k := by
      apply Finset.dvd_sum
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hB_pre : ∀ j, 1 ≤ j → j ≤ k - 1 → (2 : ℤ) ∣ B.coeff j :=
        fun j hj1 hjk => ih j (by omega) hj1
      have hI_pre : ∀ j, 1 ≤ j → j ≤ k - 1 → (2 : ℤ) ∣ (invOfUnit B).coeff j :=
        mod2_invOfUnit_of_unit_prefix hB.1 hB_pre
      have hpair : ∀ (e₁ e₂ j : ℕ), j ≤ k - 1 →
          (2 : ℤ) ∣ (B ^ e₁ + (invOfUnit B) ^ e₂).coeff j := by
        intro e₁ e₂ j hj
        rw [map_add]
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
        rw [Int.cast_add, mod2_pow_of_unit_prefix hB.1 hB_pre e₁ j hj,
          mod2_pow_of_unit_prefix (coeff_invOfUnit_zero B) hI_pre e₂ j hj]
        split_ifs <;> decide
      unfold term359914
      have hneg : ((-1 : PowerSeries ℤ) ^ m) = PowerSeries.C ((-1 : ℤ) ^ m) := by simp
      rw [hneg, PowerSeries.coeff_C_mul, map_add, PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_X_pow_mul']
      have hp1 : 1 ≤ m * (3 * m - 1) / 2 := le_trans hm.1 (pent1_ge hm.1)
      have hp2 : 1 ≤ m * (3 * m + 1) / 2 := le_trans hm.1 (pent2_ge hm.1)
      apply dvd_mul_of_dvd_right
      apply dvd_add
      · split_ifs with hle
        · exact hpair (3 * m) (3 * m - 1) (k - m * (3 * m - 1) / 2) (by omega)
        · exact dvd_zero 2
      · split_ifs with hle
        · exact hpair (3 * m + 1) (3 * m) (k - m * (3 * m + 1) / 2) (by omega)
        · exact dvd_zero 2
    have heq := hB.2 k hk
    have hBk : B.coeff k = -(∑ m ∈ Finset.Icc 1 k, (term359914 B m).coeff k) := by linarith
    rw [hBk]
    exact hsum2.neg_right

private lemma two_dvd_A361552 {A : PowerSeries ℤ} (hA : SatisfiesA361552 A) :
    ∀ k : ℕ, 1 ≤ k → (2 : ℤ) ∣ A.coeff k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hA_pre : ∀ j, 1 ≤ j → j ≤ k - 1 → (2 : ℤ) ∣ A.coeff j :=
      fun j hj1 hjk => ih j (by omega) hj1
    have hI_pre : ∀ j, 1 ≤ j → j ≤ k - 1 → (2 : ℤ) ∣ (invOfUnit A).coeff j :=
      mod2_invOfUnit_of_unit_prefix hA.1 hA_pre
    have hsum2 : (2 : ℤ) ∣ ∑ m ∈ Finset.Icc 1 k, (term361552 A m).coeff k := by
      apply Finset.dvd_sum
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hdiff : ∀ (F G : PowerSeries ℤ),
          F.coeff 0 = 1 → (∀ j, 1 ≤ j → j ≤ k - 1 → (2 : ℤ) ∣ F.coeff j) →
          G.coeff 0 = 1 → (∀ j, 1 ≤ j → j ≤ k - 1 → (2 : ℤ) ∣ G.coeff j) →
          ∀ (e₁ e₂ j : ℕ), j ≤ k - 1 → (2 : ℤ) ∣ (F ^ e₁ - G ^ e₂).coeff j := by
        intro F G hF0 hF2 hG0 hG2 e₁ e₂ j hj
        rw [map_sub]
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
        rw [Int.cast_sub, mod2_pow_of_unit_prefix hF0 hF2 e₁ j hj,
          mod2_pow_of_unit_prefix hG0 hG2 e₂ j hj, sub_self]
      unfold term361552
      rw [map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
      have hp1 : 1 ≤ m * (3 * m - 1) / 2 := le_trans hm.1 (pent1_ge hm.1)
      have hp2 : 1 ≤ m * (3 * m + 1) / 2 := le_trans hm.1 (pent2_ge hm.1)
      apply dvd_add
      · split_ifs with hle
        · exact hdiff A (invOfUnit A) hA.1 hA_pre (coeff_invOfUnit_zero A) hI_pre
            (3 * m) (3 * m + 1) _ (by omega)
        · exact dvd_zero 2
      · split_ifs with hle
        · exact hdiff (invOfUnit A) A (coeff_invOfUnit_zero A) hI_pre hA.1 hA_pre
            (3 * m) (3 * m - 1) _ (by omega)
        · exact dvd_zero 2
    have hrest : (2 : ℤ) ∣ restInv A k := by
      unfold restInv
      apply Finset.dvd_sum
      intro p hp
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
      exact dvd_mul_of_dvd_left (hA_pre p.1 (by omega) (by omega)) _
    have hneg := neg_invOfUnit_coeff hA.1 hk
    have heq := hA.2 k hk
    have hrhs : (2 : ℤ) ∣ (if k = 1 then (2 : ℤ) else 0) := by split_ifs <;> decide
    have hAk : A.coeff k = (if k = 1 then (2 : ℤ) else 0) - restInv A k -
        ∑ m ∈ Finset.Icc 1 k, (term361552 A m).coeff k := by linarith
    rw [hAk]
    exact dvd_sub (dvd_sub hrhs hrest) hsum2

private lemma four_eq_zero_ps4 : (4 : PowerSeries (ZMod 4)) = 0 := by
  ext k
  rw [show (4 : PowerSeries (ZMod 4)) = PowerSeries.C (4 : ZMod 4) from rfl,
    PowerSeries.coeff_C, map_zero]
  split_ifs <;> decide

private lemma neg_two_eq_two_ps4 : (-2 : PowerSeries (ZMod 4)) = 2 := by
  linear_combination -four_eq_zero_ps4

private lemma one_add_two_mul_pow (F : PowerSeries (ZMod 4)) :
    ∀ r : ℕ, (1 + 2 * F) ^ r = 1 + 2 * (r : PowerSeries (ZMod 4)) * F := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ih]
    have h4 := four_eq_zero_ps4
    push_cast
    linear_combination (r : PowerSeries (ZMod 4)) * F ^ 2 * h4

private lemma inv_one_add_two_mul_ps4 {A D : PowerSeries ℤ}
    (hA0 : A.coeff 0 = 1) (hAD : A = 1 + 2 * D) :
    PowerSeries.map (Int.castRingHom (ZMod 4)) (invOfUnit A) =
    1 + 2 * PowerSeries.map (Int.castRingHom (ZMod 4)) D := by
  let ψ : PowerSeries ℤ →+* PowerSeries (ZMod 4) := PowerSeries.map (Int.castRingHom (ZMod 4))
  have hψA : ψ A = 1 + 2 * ψ D := by
    rw [hAD, map_add, map_one, map_mul, map_ofNat]
  have hsq : (1 + 2 * ψ D) * ψ A = 1 := by
    rw [hψA]
    have h4 := four_eq_zero_ps4
    linear_combination (ψ D + (ψ D) ^ 2) * h4
  have hmul : ψ A * ψ (invOfUnit A) = 1 := by
    rw [← map_mul, mul_invOfUnit hA0, map_one]
  calc
    ψ (invOfUnit A) = 1 * ψ (invOfUnit A) := (one_mul _).symm
    _ = ((1 + 2 * ψ D) * ψ A) * ψ (invOfUnit A) := by rw [hsq]
    _ = (1 + 2 * ψ D) * (ψ A * ψ (invOfUnit A)) := mul_assoc _ _ _
    _ = 1 + 2 * ψ D := by rw [hmul, mul_one]

private lemma coeff_pentagonalSeries_zmod2 (k : ℕ) :
    (PowerSeries.pentagonalSeries (ZMod 2)).coeff k =
      ((1 : PowerSeries (ZMod 2)) +
        ∑ m ∈ Finset.Icc 1 k,
          (PowerSeries.X ^ (m * (3 * m - 1) / 2) + PowerSeries.X ^ (m * (3 * m + 1) / 2))).coeff k := by
  have hp_pos : ∀ m : ℕ, 1 ≤ m → pentagonal (m : ℤ) = m * (3 * m - 1) / 2 := by
    intro m hm
    have h := two_mul_natCast_pentagonal (m : ℤ)
    have hz : (m : ℤ) * (3 * (m : ℤ) - 1) = ((m * (3 * m - 1) : ℕ) : ℤ) := by
      have : 1 ≤ 3 * m := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hz] at h
    have h2 : 2 * pentagonal (m : ℤ) = m * (3 * m - 1) := by omega
    omega
  have hp_neg : ∀ m : ℕ, 1 ≤ m → pentagonal (-(m : ℤ)) = m * (3 * m + 1) / 2 := by
    intro m hm
    have h := two_mul_natCast_pentagonal_neg (m : ℤ)
    have hz : (m : ℤ) * (3 * (m : ℤ) + 1) = ((m * (3 * m + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [hz] at h
    have h2 : 2 * pentagonal (-(m : ℤ)) = m * (3 * m + 1) := by omega
    omega
  have hneg1 : ∀ z : ℤ, (Int.negOnePow z : ZMod 2) = 1 := by
    intro z
    rcases Int.units_eq_one_or (Int.negOnePow z) with h | h <;> rw [h] <;> decide
  rw [map_add, PowerSeries.coeff_one, map_sum]
  simp only [map_add, PowerSeries.coeff_X_pow]
  by_cases hk0 : k = 0
  · subst hk0
    have h0 : pentagonal 0 = 0 := by decide
    have hI : Finset.Icc 1 0 = ∅ := by decide
    rw [hI, Finset.sum_empty, if_pos rfl, add_zero, ← h0,
      PowerSeries.coeff_pentagonalSeries_pentagonal, hneg1]
  · rw [if_neg hk0, zero_add]
    by_cases hmem : k ∈ Set.range pentagonal
    · obtain ⟨z, hz⟩ := hmem
      conv_lhs => rw [← hz]
      rw [PowerSeries.coeff_pentagonalSeries_pentagonal, hneg1]
      have hz0 : z ≠ 0 := by
        intro h0; subst h0
        have : pentagonal 0 = 0 := by decide
        omega
      rcases lt_or_gt_of_ne hz0 with hlt | hgt
      · set m := (-z).toNat
        have hm1 : 1 ≤ m := by omega
        have hzm : z = -(m : ℤ) := by omega
        have hkm : m * (3 * m + 1) / 2 = k := by rw [← hp_neg m hm1, ← hzm, hz]
        have hmk : m ≤ k := le_trans (pent2_ge hm1) (by omega)
        rw [Finset.sum_eq_single m]
        · have hne : k ≠ m * (3 * m - 1) / 2 := by
            rw [← hp_pos m hm1, ← hz]
            intro heq; have := pentagonal_injective heq; omega
          rw [if_neg hne, if_pos hkm.symm, zero_add]
        · intro b hb hbm
          rw [Finset.mem_Icc] at hb
          have hne1 : k ≠ b * (3 * b - 1) / 2 := by
            rw [← hp_pos b hb.1, ← hz]
            intro heq; have := pentagonal_injective heq; omega
          have hne2 : k ≠ b * (3 * b + 1) / 2 := by
            rw [← hp_neg b hb.1, ← hz]
            intro heq; have := pentagonal_injective heq; omega
          rw [if_neg hne1, if_neg hne2, add_zero]
        · intro hnot; exact (hnot (Finset.mem_Icc.mpr ⟨hm1, hmk⟩)).elim
      · set m := z.toNat
        have hm1 : 1 ≤ m := by omega
        have hzm : z = (m : ℤ) := by omega
        have hkm : m * (3 * m - 1) / 2 = k := by rw [← hp_pos m hm1, ← hzm, hz]
        have hmk : m ≤ k := le_trans (pent1_ge hm1) (by omega)
        rw [Finset.sum_eq_single m]
        · have hne : k ≠ m * (3 * m + 1) / 2 := by
            rw [← hp_neg m hm1, ← hz]
            intro heq; have := pentagonal_injective heq; omega
          rw [if_pos hkm.symm, if_neg hne, add_zero]
        · intro b hb hbm
          rw [Finset.mem_Icc] at hb
          have hne1 : k ≠ b * (3 * b - 1) / 2 := by
            rw [← hp_pos b hb.1, ← hz]
            intro heq; have := pentagonal_injective heq; omega
          have hne2 : k ≠ b * (3 * b + 1) / 2 := by
            rw [← hp_neg b hb.1, ← hz]
            intro heq; have := pentagonal_injective heq; omega
          rw [if_neg hne1, if_neg hne2, add_zero]
        · intro hnot; exact (hnot (Finset.mem_Icc.mpr ⟨hm1, hmk⟩)).elim
    · rw [PowerSeries.coeff_pentagonalSeries_eq_zero _ hmem]
      symm
      apply Finset.sum_eq_zero
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hne1 : k ≠ m * (3 * m - 1) / 2 := by
        intro heq; exact hmem ⟨(m : ℤ), by rw [hp_pos m hm.1, heq]⟩
      have hne2 : k ≠ m * (3 * m + 1) / 2 := by
        intro heq; exact hmem ⟨-(m : ℤ), by rw [hp_neg m hm.1, heq]⟩
      rw [if_neg hne1, if_neg hne2, add_zero]

private lemma coeff_pentagonal_mul_zmod2 (G : PowerSeries (ZMod 2)) (k : ℕ) :
    (PowerSeries.pentagonalSeries (ZMod 2) * G).coeff k =
      G.coeff k + ∑ m ∈ Finset.Icc 1 k,
        ((PowerSeries.X ^ (m * (3 * m - 1) / 2) * G).coeff k +
         (PowerSeries.X ^ (m * (3 * m + 1) / 2) * G).coeff k) := by
  let Pk : PowerSeries (ZMod 2) :=
    1 + ∑ m ∈ Finset.Icc 1 k,
      (PowerSeries.X ^ (m * (3 * m - 1) / 2) + PowerSeries.X ^ (m * (3 * m + 1) / 2))
  have hpre : ∀ j ≤ k, (PowerSeries.pentagonalSeries (ZMod 2)).coeff j = Pk.coeff j := by
    intro j hj
    rw [coeff_pentagonalSeries_zmod2 j]
    simp only [Pk, map_add, map_sum, PowerSeries.coeff_X_pow]
    congr 1
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right hj)
    intro m hm hnot
    rw [Finset.mem_Icc] at hm hnot
    have hgt : j < m := by omega
    have h1 : j < m * (3 * m - 1) / 2 := lt_of_lt_of_le hgt (pent1_ge hm.1)
    have h2 : j < m * (3 * m + 1) / 2 := lt_of_lt_of_le hgt (pent2_ge hm.1)
    rw [if_neg (by omega), if_neg (by omega), add_zero]
  rw [coeff_mul_eq_of_prefix hpre (fun _ _ => rfl) k le_rfl]
  simp only [Pk, add_mul, one_mul, Finset.sum_mul, map_add, map_sum]

open scoped PowerSeries.WithPiTopology in
private lemma pentagonal_mul_partitionGenFun :
    PowerSeries.pentagonalSeries (ZMod 2) *
      Nat.Partition.genFun (fun _ _ => (1 : ZMod 2)) = 1 := by
  let : TopologicalSpace (ZMod 2) := ⊥
  have : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  let g : ℕ → PowerSeries (ZMod 2) :=
    fun i => 1 + ∑' j : ℕ, (1 : ZMod 2) • (PowerSeries.X : PowerSeries (ZMod 2)) ^ ((i + 1) * (j + 1))
  have hfactor : ∀ i : ℕ, (1 - PowerSeries.X ^ (i + 1) : PowerSeries (ZMod 2)) * g i = 1 := by
    intro i
    have hg_coeff : ∀ d : ℕ, (g i).coeff d = if (i + 1) ∣ d then (1 : ZMod 2) else 0 := by
      intro d
      simp only [g, map_add, PowerSeries.coeff_one]
      have htsum := (Nat.Partition.summable_genFun_term (fun _ _ => (1 : ZMod 2)) i).map_tsum _
        (PowerSeries.WithPiTopology.continuous_coeff (ZMod 2) d)
      rw [htsum]
      simp only [one_smul, PowerSeries.coeff_X_pow]
      by_cases hd0 : d = 0
      · subst hd0
        rw [if_pos rfl, if_pos (dvd_zero _)]
        have h0 : (∑' j : ℕ, if (0 : ℕ) = (i + 1) * (j + 1) then (1 : ZMod 2) else 0) = 0 := by
          have hf : (fun j : ℕ => if (0 : ℕ) = (i + 1) * (j + 1) then (1 : ZMod 2) else 0) = fun _ => 0 := by
            funext j
            rw [if_neg]
            have : 1 ≤ (i + 1) * (j + 1) := by nlinarith
            omega
          rw [hf, tsum_zero]
        rw [h0, add_zero]
      · rw [if_neg hd0, zero_add]
        by_cases hdvd : (i + 1) ∣ d
        · rw [if_pos hdvd]
          obtain ⟨q, hq⟩ := hdvd
          have hq1 : 1 ≤ q := by
            rcases Nat.eq_zero_or_pos q with rfl | hpos
            · simp at hq; exact (hd0 hq).elim
            · omega
          rw [tsum_eq_single (q - 1)]
          · rw [if_pos (by rw [hq, Nat.sub_add_cancel hq1])]
          · intro b hb
            rw [if_neg]
            intro heq
            have hmul : (i + 1) * q = (i + 1) * (b + 1) := by rw [← hq, heq]
            have hqb := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos i) hmul
            exact hb (by omega)
        · rw [if_neg hdvd]
          have hf : (fun j : ℕ => if d = (i + 1) * (j + 1) then (1 : ZMod 2) else 0) = fun _ => 0 := by
            funext j
            rw [if_neg]
            intro heq
            exact hdvd ⟨j + 1, heq⟩
          rw [hf, tsum_zero]
    ext d
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', hg_coeff d, PowerSeries.coeff_one]
    by_cases hd0 : d = 0
    · subst hd0
      rw [if_pos (dvd_zero _), if_neg (by omega), if_pos rfl, sub_zero]
    · rw [if_neg hd0]
      by_cases hle : i + 1 ≤ d
      · rw [if_pos hle, hg_coeff (d - (i + 1))]
        have hiff : (i + 1) ∣ d ↔ (i + 1) ∣ (d - (i + 1)) := by
          constructor
          · intro ⟨q, hq⟩
            exact ⟨q - 1, by
              have hq1 : 1 ≤ q := by
                rcases Nat.eq_zero_or_pos q with rfl | hpos
                · simp at hq; omega
                · omega
              rw [Nat.mul_sub_left_distrib, mul_one, ← hq]⟩
          · intro ⟨q, hq⟩
            exact ⟨q + 1, by rw [Nat.mul_add, mul_one, ← hq]; omega⟩
        by_cases hdvd : (i + 1) ∣ d
        · rw [if_pos hdvd, if_pos (hiff.mp hdvd), sub_self]
        · rw [if_neg hdvd, if_neg (fun h => hdvd (hiff.mpr h)), sub_self]
      · rw [if_neg hle, sub_zero]
        have hndvd : ¬ (i + 1) ∣ d := by
          intro h
          have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h
          omega
        rw [if_neg hndvd]
  have hp1 : ∀ j : ℕ, ∀ᶠ s : Finset ℕ in Filter.atTop,
      (∏ i ∈ s, (1 - PowerSeries.X ^ (i + 1) : PowerSeries (ZMod 2))).coeff j =
      (PowerSeries.pentagonalSeries (ZMod 2)).coeff j :=
    fun j => PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq (ZMod 2) j
  have hp2 : ∀ j : ℕ, ∀ᶠ s : Finset ℕ in Filter.atTop,
      (∏ i ∈ s, g i).coeff j = (Nat.Partition.genFun (fun _ _ => (1 : ZMod 2))).coeff j := by
    intro j
    have h := Nat.Partition.hasProd_genFun (fun _ _ => (1 : ZMod 2))
    rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at h
    have hj := h j
    simpa [g] using hj
  ext k
  have hall1 : ∀ᶠ s : Finset ℕ in Filter.atTop, ∀ j ∈ Finset.range (k + 1),
      (∏ i ∈ s, (1 - PowerSeries.X ^ (i + 1) : PowerSeries (ZMod 2))).coeff j =
      (PowerSeries.pentagonalSeries (ZMod 2)).coeff j :=
    (Finset.eventually_all (Finset.range (k + 1))).mpr fun j _ => hp1 j
  have hall2 : ∀ᶠ s : Finset ℕ in Filter.atTop, ∀ j ∈ Finset.range (k + 1),
      (∏ i ∈ s, g i).coeff j = (Nat.Partition.genFun (fun _ _ => (1 : ZMod 2))).coeff j :=
    (Finset.eventually_all (Finset.range (k + 1))).mpr fun j _ => hp2 j
  obtain ⟨s, hs1, hs2⟩ := (hall1.and hall2).exists
  have hmul_eq : (PowerSeries.pentagonalSeries (ZMod 2) *
      Nat.Partition.genFun (fun _ _ => (1 : ZMod 2))).coeff k =
      ((∏ i ∈ s, (1 - PowerSeries.X ^ (i + 1) : PowerSeries (ZMod 2))) * (∏ i ∈ s, g i)).coeff k :=
    coeff_mul_eq_of_prefix
      (fun j hj => (hs1 j (Finset.mem_range.mpr (by omega))).symm)
      (fun j hj => (hs2 j (Finset.mem_range.mpr (by omega))).symm) k le_rfl
  rw [hmul_eq, ← Finset.prod_mul_distrib]
  have hprod1 : (∏ i ∈ s, ((1 - PowerSeries.X ^ (i + 1) : PowerSeries (ZMod 2)) * g i)) = 1 :=
    Finset.prod_eq_one fun i _ => hfactor i
  rw [hprod1]

private lemma coeff_partitionGenFun (n : ℕ) :
    (Nat.Partition.genFun (fun _ _ => (1 : ZMod 2))).coeff n = (A000041 n : ZMod 2) := by
  rw [Nat.Partition.coeff_genFun]
  unfold A000041
  simp

private lemma two_mul_eq_zero_zmod4_iff (z : ℤ) :
    (2 : ZMod 4) * (z : ZMod 4) = 0 ↔ (z : ZMod 2) = 0 := by
  constructor
  · intro h
    have h0 : ((2 * z : ℤ) : ZMod 4) = 0 := by push_cast; exact h
    have hd4 : (4 : ℤ) ∣ 2 * z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h0
    have hd2 : (2 : ℤ) ∣ z := by obtain ⟨q, hq⟩ := hd4; exact ⟨q, by omega⟩
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mpr hd2
  · intro h
    have hd2 : (2 : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp h
    have hd4 : (4 : ℤ) ∣ 2 * z := by obtain ⟨q, hq⟩ := hd2; exact ⟨q, by omega⟩
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * z) 4).mpr hd4
    simpa using h0

private lemma A359914_half_mod2 {B : PowerSeries ℤ} (hB : SatisfiesA359914 B) :
    ∀ n : ℕ, 1 ≤ n → ((B.coeff n / 2 : ℤ) : ZMod 2) = (A000041 n : ZMod 2) := by
  have h2 := two_dvd_A359914 hB
  let E : PowerSeries ℤ := PowerSeries.mk fun k => if k = 0 then 0 else B.coeff k / 2
  have hE0 : E.coeff 0 = 0 := by simp [E]
  have hBE : B = 1 + 2 * E := by
    ext k
    rw [map_add, PowerSeries.coeff_one, show (2 : PowerSeries ℤ) = PowerSeries.C 2 from rfl,
      PowerSeries.coeff_C_mul]
    simp only [E, PowerSeries.coeff_mk]
    by_cases hk0 : k = 0
    · subst hk0; simp [hB.1]
    · rw [if_neg hk0, if_neg hk0, zero_add, Int.mul_ediv_cancel' (h2 k (by omega))]
  let ψ : PowerSeries ℤ →+* PowerSeries (ZMod 4) := PowerSeries.map (Int.castRingHom (ZMod 4))
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hψB : ψ B = 1 + 2 * ψ E := by rw [hBE, map_add, map_one, map_mul, map_ofNat]
  have hψI : ψ (invOfUnit B) = 1 + 2 * ψ E := inv_one_add_two_mul_ps4 hB.1 hBE
  have hψX : ψ PowerSeries.X = PowerSeries.X := PowerSeries.map_X (Int.castRingHom (ZMod 4))
  have hpair4 : ∀ s : ℕ,
      (1 + 2 * ψ E) ^ (s + 1) + (1 + 2 * ψ E) ^ s = 2 * (1 + ψ E) := by
    intro s
    rw [one_add_two_mul_pow, one_add_two_mul_pow]
    have h4 := four_eq_zero_ps4
    push_cast
    linear_combination (s : PowerSeries (ZMod 4)) * ψ E * h4
  have hterm4 : ∀ m : ℕ, 1 ≤ m →
      ψ (term359914 B m) =
        2 * (PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + ψ E) +
             PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + ψ E)) := by
    intro m hm
    unfold term359914
    simp only [map_mul, map_add, map_pow, map_neg, map_one, hψX, hψB, hψI]
    have hpair_sub : (1 + 2 * ψ E) ^ (3 * m) + (1 + 2 * ψ E) ^ (3 * m - 1) = 2 * (1 + ψ E) := by
      have h3m : 3 * m = (3 * m - 1) + 1 := by omega
      conv_lhs => arg 1; rw [h3m]
      exact hpair4 (3 * m - 1)
    rw [hpair_sub, hpair4 (3 * m)]
    have hneg2 : (-1 : PowerSeries (ZMod 4)) ^ m * 2 = 2 := by
      rcases Nat.even_or_odd m with hev | hodd
      · rw [hev.neg_one_pow, one_mul]
      · rw [hodd.neg_one_pow, neg_one_mul, neg_two_eq_two_ps4]
    calc
      (-1 : PowerSeries (ZMod 4)) ^ m *
        (PowerSeries.X ^ (m * (3 * m - 1) / 2) * (2 * (1 + ψ E)) +
         PowerSeries.X ^ (m * (3 * m + 1) / 2) * (2 * (1 + ψ E)))
          = ((-1 : PowerSeries (ZMod 4)) ^ m * 2) *
            (PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + ψ E) +
             PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + ψ E)) := by ring
      _ = 2 * (PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + ψ E) +
               PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + ψ E)) := by rw [hneg2]
  have hG_eq : PowerSeries.pentagonalSeries (ZMod 2) * (1 + φ E) = 1 := by
    ext k
    rw [PowerSeries.coeff_one]
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff]
      have hp0 : (PowerSeries.pentagonalSeries (ZMod 2)).coeff 0 = 1 := by
        have h0 : pentagonal 0 = 0 := by decide
        rw [← h0, PowerSeries.coeff_pentagonalSeries_pentagonal]; decide
      rw [hp0, map_add, PowerSeries.coeff_one, if_pos rfl, PowerSeries.coeff_map, hE0]
      simp
    · rw [if_neg hk0, coeff_pentagonal_mul_zmod2]
      have h4eq := congrArg (fun z : ℤ => (z : ZMod 4)) (hB.2 k (by omega))
      simp only [Int.cast_add, Int.cast_sum, Int.cast_zero] at h4eq
      have hBk4 : (B.coeff k : ZMod 4) = 2 * ((1 + E).coeff k : ZMod 4) := by
        have h1 : (B.coeff k : ZMod 4) = (ψ B).coeff k :=
          (PowerSeries.coeff_map (Int.castRingHom (ZMod 4)) k B).symm
        rw [h1, hψB, map_add, PowerSeries.coeff_one, if_neg hk0, zero_add,
          show (2 : PowerSeries (ZMod 4)) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_map, map_add, PowerSeries.coeff_one, if_neg hk0, zero_add]
        rfl
      have hsum4 : ∑ m ∈ Finset.Icc 1 k, ((term359914 B m).coeff k : ZMod 4) =
          2 * ∑ m ∈ Finset.Icc 1 k,
            (((PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + E)).coeff k +
              (PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + E)).coeff k : ℤ) : ZMod 4) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_Icc] at hm
        have h1 : ((term359914 B m).coeff k : ZMod 4) = (ψ (term359914 B m)).coeff k :=
          (PowerSeries.coeff_map (Int.castRingHom (ZMod 4)) k _).symm
        rw [h1, hterm4 m hm.1, show (2 : PowerSeries (ZMod 4)) = PowerSeries.C 2 from rfl,
          PowerSeries.coeff_C_mul]
        have hmap1 : PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + ψ E) =
            ψ (PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + E)) := by
          simp [map_mul, map_pow, map_add, map_one, hψX]
        have hmap2 : PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + ψ E) =
            ψ (PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + E)) := by
          simp [map_mul, map_pow, map_add, map_one, hψX]
        rw [map_add, hmap1, hmap2, PowerSeries.coeff_map, PowerSeries.coeff_map]
        simp
      rw [hBk4, hsum4, ← mul_add] at h4eq
      set S : ℤ := (1 + E).coeff k + ∑ m ∈ Finset.Icc 1 k,
        ((PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + E)).coeff k +
         (PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + E)).coeff k)
      have hS4 : (2 : ZMod 4) * (S : ZMod 4) = 0 := by
        have : (S : ZMod 4) = ((1 + E).coeff k : ZMod 4) +
            ∑ m ∈ Finset.Icc 1 k,
              (((PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + E)).coeff k +
                (PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + E)).coeff k : ℤ) : ZMod 4) := by
          simp [S]
        rw [this]; exact h4eq
      have hS2 : (S : ZMod 2) = 0 := (two_mul_eq_zero_zmod4_iff S).mp hS4
      have hφX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X (Int.castRingHom (ZMod 2))
      have hS2_eq : (S : ZMod 2) = (1 + φ E).coeff k + ∑ m ∈ Finset.Icc 1 k,
          ((PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + φ E)).coeff k +
           (PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + φ E)).coeff k) := by
        simp only [S, Int.cast_add, Int.cast_sum]
        congr 1
        · have : ((1 + E).coeff k : ZMod 2) = (φ (1 + E)).coeff k :=
            (PowerSeries.coeff_map (Int.castRingHom (ZMod 2)) k _).symm
          rw [this, map_add, map_one]
        · apply Finset.sum_congr rfl
          intro m _
          have h1 : ((PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + E)).coeff k : ZMod 2) =
              (φ (PowerSeries.X ^ (m * (3 * m - 1) / 2) * (1 + E))).coeff k :=
            (PowerSeries.coeff_map (Int.castRingHom (ZMod 2)) k _).symm
          have h2 : ((PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + E)).coeff k : ZMod 2) =
              (φ (PowerSeries.X ^ (m * (3 * m + 1) / 2) * (1 + E))).coeff k :=
            (PowerSeries.coeff_map (Int.castRingHom (ZMod 2)) k _).symm
          rw [h1, h2]
          simp [map_mul, map_pow, map_add, map_one, hφX]
      rw [← hS2_eq]
      exact hS2
  have h1E_eq : 1 + φ E = Nat.Partition.genFun (fun _ _ => (1 : ZMod 2)) := by
    calc
      1 + φ E = (1 + φ E) * 1 := (mul_one _).symm
      _ = (1 + φ E) * (PowerSeries.pentagonalSeries (ZMod 2) *
            Nat.Partition.genFun (fun _ _ => (1 : ZMod 2))) := by
          rw [pentagonal_mul_partitionGenFun]
      _ = (PowerSeries.pentagonalSeries (ZMod 2) * (1 + φ E)) *
            Nat.Partition.genFun (fun _ _ => (1 : ZMod 2)) := by ring
      _ = Nat.Partition.genFun (fun _ _ => (1 : ZMod 2)) := by rw [hG_eq, one_mul]
  intro n hn
  have hc := congrArg (PowerSeries.coeff n) h1E_eq
  rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add, PowerSeries.coeff_map,
    coeff_partitionGenFun] at hc
  simp only [E, PowerSeries.coeff_mk, show n ≠ 0 by omega, ↓reduceIte] at hc
  exact hc

private lemma A361552_half_mod2 {A : PowerSeries ℤ} (hA : SatisfiesA361552 A) :
    ∀ n : ℕ, 1 ≤ n → ((A.coeff n / 2 : ℤ) : ZMod 2) = (A000041 (n - 1) : ZMod 2) := by
  have h2 := two_dvd_A361552 hA
  let D : PowerSeries ℤ := PowerSeries.mk fun k => if k = 0 then 0 else A.coeff k / 2
  have hD0 : D.coeff 0 = 0 := by simp [D]
  have hAD : A = 1 + 2 * D := by
    ext k
    rw [map_add, PowerSeries.coeff_one, show (2 : PowerSeries ℤ) = PowerSeries.C 2 from rfl,
      PowerSeries.coeff_C_mul]
    simp only [D, PowerSeries.coeff_mk]
    by_cases hk0 : k = 0
    · subst hk0; simp [hA.1]
    · rw [if_neg hk0, if_neg hk0, zero_add, Int.mul_ediv_cancel' (h2 k (by omega))]
  let ψ : PowerSeries ℤ →+* PowerSeries (ZMod 4) := PowerSeries.map (Int.castRingHom (ZMod 4))
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hψA : ψ A = 1 + 2 * ψ D := by rw [hAD, map_add, map_one, map_mul, map_ofNat]
  have hψI : ψ (invOfUnit A) = 1 + 2 * ψ D := inv_one_add_two_mul_ps4 hA.1 hAD
  have hψX : ψ PowerSeries.X = PowerSeries.X := PowerSeries.map_X (Int.castRingHom (ZMod 4))
  have hdiff1 : ∀ s : ℕ,
      (1 + 2 * ψ D) ^ s - (1 + 2 * ψ D) ^ (s + 1) = 2 * ψ D := by
    intro s
    rw [one_add_two_mul_pow, one_add_two_mul_pow]
    have hneg2 := neg_two_eq_two_ps4
    push_cast
    linear_combination ψ D * hneg2
  have hdiff2 : ∀ s : ℕ,
      (1 + 2 * ψ D) ^ (s + 1) - (1 + 2 * ψ D) ^ s = 2 * ψ D := by
    intro s
    rw [one_add_two_mul_pow, one_add_two_mul_pow]
    push_cast
    ring
  have hterm4 : ∀ m : ℕ, 1 ≤ m →
      ψ (term361552 A m) =
        2 * (PowerSeries.X ^ (m * (3 * m - 1) / 2) * ψ D +
             PowerSeries.X ^ (m * (3 * m + 1) / 2) * ψ D) := by
    intro m hm
    unfold term361552
    simp only [map_add, map_mul, map_sub, map_pow, hψX, hψA, hψI]
    have hdiff_sub : (1 + 2 * ψ D) ^ (3 * m) - (1 + 2 * ψ D) ^ (3 * m - 1) = 2 * ψ D := by
      have h3m : 3 * m = (3 * m - 1) + 1 := by omega
      conv_lhs => arg 1; rw [h3m]
      exact hdiff2 (3 * m - 1)
    rw [hdiff1 (3 * m), hdiff_sub]
    ring
  have hH_eq : PowerSeries.pentagonalSeries (ZMod 2) * φ D = PowerSeries.X := by
    ext k
    rw [PowerSeries.coeff_X]
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_neg (by decide : (0 : ℕ) ≠ 1), PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_map, hD0]
      simp
    · rw [coeff_pentagonal_mul_zmod2]
      have h4eq := congrArg (fun z : ℤ => (z : ZMod 4)) (hA.2 k (by omega))
      simp only [Int.cast_add, Int.cast_neg, Int.cast_sum, Int.cast_ite, Int.cast_ofNat,
        Int.cast_zero] at h4eq
      have hnegI4 : -((invOfUnit A).coeff k : ZMod 4) = 2 * (D.coeff k : ZMod 4) := by
        have h1 : ((invOfUnit A).coeff k : ZMod 4) = (ψ (invOfUnit A)).coeff k :=
          (PowerSeries.coeff_map (Int.castRingHom (ZMod 4)) k _).symm
        rw [h1, hψI, map_add, PowerSeries.coeff_one, if_neg hk0, zero_add,
          show (2 : PowerSeries (ZMod 4)) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_map]
        simp only [Int.coe_castRingHom]
        have hneg2z : (-2 : ZMod 4) = 2 := by decide
        have : -((2 : ZMod 4) * (D.coeff k : ZMod 4)) = (-2 : ZMod 4) * (D.coeff k : ZMod 4) := by ring
        rw [this, hneg2z]
      have hsum4 : ∑ m ∈ Finset.Icc 1 k, ((term361552 A m).coeff k : ZMod 4) =
          2 * ∑ m ∈ Finset.Icc 1 k,
            (((PowerSeries.X ^ (m * (3 * m - 1) / 2) * D).coeff k +
              (PowerSeries.X ^ (m * (3 * m + 1) / 2) * D).coeff k : ℤ) : ZMod 4) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_Icc] at hm
        have h1 : ((term361552 A m).coeff k : ZMod 4) = (ψ (term361552 A m)).coeff k :=
          (PowerSeries.coeff_map (Int.castRingHom (ZMod 4)) k _).symm
        rw [h1, hterm4 m hm.1, show (2 : PowerSeries (ZMod 4)) = PowerSeries.C 2 from rfl,
          PowerSeries.coeff_C_mul]
        have hmap1 : PowerSeries.X ^ (m * (3 * m - 1) / 2) * ψ D =
            ψ (PowerSeries.X ^ (m * (3 * m - 1) / 2) * D) := by
          simp [map_mul, map_pow, hψX]
        have hmap2 : PowerSeries.X ^ (m * (3 * m + 1) / 2) * ψ D =
            ψ (PowerSeries.X ^ (m * (3 * m + 1) / 2) * D) := by
          simp [map_mul, map_pow, hψX]
        rw [map_add, hmap1, hmap2, PowerSeries.coeff_map, PowerSeries.coeff_map]
        simp
      rw [hnegI4, hsum4, ← mul_add] at h4eq
      set S : ℤ := D.coeff k + ∑ m ∈ Finset.Icc 1 k,
        ((PowerSeries.X ^ (m * (3 * m - 1) / 2) * D).coeff k +
         (PowerSeries.X ^ (m * (3 * m + 1) / 2) * D).coeff k)
      set rhsZ : ℤ := if k = 1 then 1 else 0
      have hS4 : (2 : ZMod 4) * ((S - rhsZ : ℤ) : ZMod 4) = 0 := by
        have hSeq : (S : ZMod 4) = (D.coeff k : ZMod 4) +
            ∑ m ∈ Finset.Icc 1 k,
              (((PowerSeries.X ^ (m * (3 * m - 1) / 2) * D).coeff k +
                (PowerSeries.X ^ (m * (3 * m + 1) / 2) * D).coeff k : ℤ) : ZMod 4) := by
          simp [S]
        have hrhs : (2 : ZMod 4) * (rhsZ : ZMod 4) = if k = 1 then (2 : ZMod 4) else 0 := by
          simp only [rhsZ]; split_ifs <;> simp
        rw [Int.cast_sub, mul_sub, hSeq, h4eq, hrhs, sub_self]
      have hS2 : ((S - rhsZ : ℤ) : ZMod 2) = 0 := (two_mul_eq_zero_zmod4_iff (S - rhsZ)).mp hS4
      have hS2' : (S : ZMod 2) = (rhsZ : ZMod 2) := sub_eq_zero.mp (by simpa using hS2)
      have hφX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X (Int.castRingHom (ZMod 2))
      have hS2_eq : (S : ZMod 2) = (φ D).coeff k + ∑ m ∈ Finset.Icc 1 k,
          ((PowerSeries.X ^ (m * (3 * m - 1) / 2) * φ D).coeff k +
           (PowerSeries.X ^ (m * (3 * m + 1) / 2) * φ D).coeff k) := by
        simp only [S, Int.cast_add, Int.cast_sum]
        refine congrArg₂ (· + ·) (PowerSeries.coeff_map (Int.castRingHom (ZMod 2)) k D).symm ?_
        apply Finset.sum_congr rfl
        intro m _
        have h1 : ((PowerSeries.X ^ (m * (3 * m - 1) / 2) * D).coeff k : ZMod 2) =
            (φ (PowerSeries.X ^ (m * (3 * m - 1) / 2) * D)).coeff k :=
          (PowerSeries.coeff_map (Int.castRingHom (ZMod 2)) k _).symm
        have h2 : ((PowerSeries.X ^ (m * (3 * m + 1) / 2) * D).coeff k : ZMod 2) =
            (φ (PowerSeries.X ^ (m * (3 * m + 1) / 2) * D)).coeff k :=
          (PowerSeries.coeff_map (Int.castRingHom (ZMod 2)) k _).symm
        rw [h1, h2]
        simp [map_mul, map_pow, hφX]
      rw [← hS2_eq, hS2']
      simp only [rhsZ]
      split_ifs <;> simp
  have hD_eq : φ D = PowerSeries.X * Nat.Partition.genFun (fun _ _ => (1 : ZMod 2)) := by
    calc
      φ D = φ D * 1 := (mul_one _).symm
      _ = φ D * (PowerSeries.pentagonalSeries (ZMod 2) *
            Nat.Partition.genFun (fun _ _ => (1 : ZMod 2))) := by
          rw [pentagonal_mul_partitionGenFun]
      _ = (PowerSeries.pentagonalSeries (ZMod 2) * φ D) *
            Nat.Partition.genFun (fun _ _ => (1 : ZMod 2)) := by ring
      _ = PowerSeries.X * Nat.Partition.genFun (fun _ _ => (1 : ZMod 2)) := by rw [hH_eq]
  intro n hn
  cases n with
  | zero => omega
  | succ n' =>
    have hc := congrArg (PowerSeries.coeff (n' + 1)) hD_eq
    rw [PowerSeries.coeff_map, PowerSeries.coeff_succ_X_mul, coeff_partitionGenFun] at hc
    simp only [D, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hc ⊢
    exact hc

private lemma zmod2_eq_iff_mod2 (a b : ℤ) : (a : ZMod 2) = (b : ZMod 2) ↔ a % 2 = b % 2 := by
  constructor
  · intro h
    have h0 : ((a - b : ℤ) : ZMod 2) = 0 := by push_cast; rw [h, sub_self]
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) 2).mp h0
    omega
  · intro h
    have hd : (2 : ℤ) ∣ (a - b) := by omega
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) 2).mpr hd
    push_cast at h0
    exact sub_eq_zero.mp h0

theorem solve : type_of% @OMA.S_oeis_a361552.main := by
  refine ⟨exists_A361552, exists_A359914, fun A B hA hB => ⟨?_, ?_⟩⟩
  · intro n hn
    have h2A : (2 : ℤ) ∣ A.coeff n := two_dvd_A361552 hA n hn
    have hAmod := A361552_half_mod2 hA n hn
    have hmod2 : (A.coeff n / 2) % 2 = ((A000041 (n - 1) : ℤ) % 2) := by
      rw [← zmod2_eq_iff_mod2]
      simpa using hAmod
    exact ⟨h2A, hmod2⟩
  · intro n hn
    have h2A : (2 : ℤ) ∣ A.coeff n := two_dvd_A361552 hA n (by omega)
    have h2B : (2 : ℤ) ∣ B.coeff (n - 1) := two_dvd_A359914 hB (n - 1) (by omega)
    have hAmod := A361552_half_mod2 hA n (by omega)
    have hBmod := A359914_half_mod2 hB (n - 1) (by omega)
    have heq2 : ((A.coeff n / 2 : ℤ) : ZMod 2) = ((B.coeff (n - 1) / 2 : ℤ) : ZMod 2) :=
      hAmod.trans hBmod.symm
    have hm := (zmod2_eq_iff_mod2 _ _).mp heq2
    rw [Int.modEq_iff_dvd]
    obtain ⟨q1, hq1⟩ := h2A
    obtain ⟨q2, hq2⟩ := h2B
    have hq1' : A.coeff n / 2 = q1 := by omega
    have hq2' : B.coeff (n - 1) / 2 = q2 := by omega
    rw [hq1', hq2'] at hm
    exact ⟨(q2 - q1) / 2, by omega⟩

end A361552Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a361552.main :=
  A361552Proof.solve
