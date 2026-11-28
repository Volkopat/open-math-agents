import OMAStatements.S_oeis_a379764

/-!
Proof of both conjectures on OEIS A379764.

1. For every `n ≥ 1`, `posTerm A n = 16 * (4^(n-1) * (4^(n-1)*A^n - A)^(n+1))`, so `16 ∣ (posTerm A n).coeff k`.
2. For every `m ≥ 2`, `m*(m-1) ≥ 2`, so `16 ∣ (negTerm A m).coeff k`.
3. From the functional equation, for all `k ≥ 1`,
   `4 * A.coeff k = -twoTheta4Coeff k + (multiple of 16)`,
   so `A.coeff k ≡ -twoTheta4Coeff k / 4 (mod 4)`.
   When `k` is a square, `-twoTheta4Coeff k / 4 = -(-1)^k = (-1)^(k - 1)` (which is odd,
   `±1 mod 4`); when `k` is nonsquare, `twoTheta4Coeff k = 0`, so `4 ∣ A.coeff k`.
4. Existence follows by strong recursion on `k`, since when `A.coeff 0 = 0`, every `posTerm A n`
   (`n ≥ 1`) and `negTerm A m` (`m ≥ 2`) at coefficient `k` depends only on `A.coeff j` for `j < k`
   and is divisible by `16` (hence by `4`).
-/

namespace A379764Proof

open Finset PowerSeries OMA.S_oeis_a379764

private lemma coeff_C_mul_int (c : ℤ) (F : PowerSeries ℤ) (k : ℕ) :
    ((c : PowerSeries ℤ) * F).coeff k = c * F.coeff k := by
  have : (c : PowerSeries ℤ) = PowerSeries.C c := by simp
  rw [this, PowerSeries.coeff_C_mul]

private lemma sixteen_dvd_posTerm (A : PowerSeries ℤ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (16 : ℤ) ∣ (posTerm A n).coeff k := by
  unfold posTerm
  have hfac : (4 : PowerSeries ℤ) ^ n * A ^ n - 4 * A =
      (4 : PowerSeries ℤ) * ((4 : PowerSeries ℤ) ^ (n - 1) * A ^ n - A) := by
    have hpow : (4 : PowerSeries ℤ) ^ n = 4 * (4 : PowerSeries ℤ) ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    rw [hpow]; ring
  rw [hfac, mul_pow]
  have h16 : (4 : PowerSeries ℤ) ^ (n + 1) = (16 : PowerSeries ℤ) * (4 : PowerSeries ℤ) ^ (n - 1) := by
    rw [show n + 1 = 2 + (n - 1) by omega, pow_add]
    norm_num
  rw [h16, mul_assoc]
  have hcast : (16 : PowerSeries ℤ) = ((16 : ℤ) : PowerSeries ℤ) := by norm_num
  rw [hcast, coeff_C_mul_int]
  exact dvd_mul_right 16 _

private lemma sixteen_dvd_negTerm (A : PowerSeries ℤ) {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    (16 : ℤ) ∣ (negTerm A m).coeff k := by
  unfold negTerm
  have hge2 : 2 ≤ m * (m - 1) := by
    have h1 : 1 ≤ m - 1 := by omega
    nlinarith
  have h16 : (4 : PowerSeries ℤ) ^ (m * (m - 1)) =
      (16 : PowerSeries ℤ) * (4 : PowerSeries ℤ) ^ (m * (m - 1) - 2) := by
    rw [show m * (m - 1) = 2 + (m * (m - 1) - 2) by omega, pow_add]
    norm_num
  rw [h16, mul_assoc, mul_assoc]
  have hcast : (16 : PowerSeries ℤ) = ((16 : ℤ) : PowerSeries ℤ) := by norm_num
  rw [hcast, coeff_C_mul_int]
  exact dvd_mul_right 16 _

private lemma coeff_mul_eq_of_prefix {A₁ A₂ B₁ B₂ : PowerSeries ℤ} {n : ℕ}
    (h1 : ∀ j ≤ n, A₁.coeff j = B₁.coeff j) (h2 : ∀ j ≤ n, A₂.coeff j = B₂.coeff j) :
    ∀ k ≤ n, (A₁ * A₂).coeff k = (B₁ * B₂).coeff k := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [h1 p.1 (by omega), h2 p.2 (by omega)]

private lemma coeff_pow_eq_of_prefix {A B : PowerSeries ℤ} {n : ℕ}
    (h : ∀ j ≤ n, A.coeff j = B.coeff j) :
    ∀ e k : ℕ, k ≤ n → (A ^ e).coeff k = (B ^ e).coeff k := by
  intro e
  induction e with
  | zero => intro k _; simp
  | succ e ih =>
    intro k hk
    rw [pow_succ, pow_succ]
    exact coeff_mul_eq_of_prefix ih h k hk

private lemma coeff_invOneSub_eq_of_prefix {F G : PowerSeries ℤ} {n : ℕ}
    (h : ∀ j ≤ n, F.coeff j = G.coeff j) :
    ∀ k ≤ n, (invOneSub F).coeff k = (invOneSub G).coeff k := by
  intro k hk
  unfold invOneSub
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro j _
  exact coeff_pow_eq_of_prefix h j k hk

private lemma coeff_pow_eq_of_strict_prefix {F G : PowerSeries ℤ} (hF0 : F.coeff 0 = 0)
    (hG0 : G.coeff 0 = 0) {k : ℕ} (h : ∀ j < k, F.coeff j = G.coeff j) :
    ∀ e : ℕ, 2 ≤ e → (F ^ e).coeff k = (G ^ e).coeff k := by
  intro e he
  have hmul : ∀ {U V U' V' : PowerSeries ℤ}, U.coeff 0 = 0 → V.coeff 0 = 0 →
      U'.coeff 0 = 0 → V'.coeff 0 = 0 →
      (∀ j < k, U.coeff j = U'.coeff j) → (∀ j < k, V.coeff j = V'.coeff j) →
      (U * V).coeff k = (U' * V').coeff k := by
    intro U V U' V' hU0 hV0 hU'0 hV'0 hU hV
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases hp1 : p.1 = 0
    · rw [hp1, hU0, hU'0, zero_mul, zero_mul]
    · by_cases hp2 : p.2 = 0
      · rw [hp2, hV0, hV'0, mul_zero, mul_zero]
      · rw [hU p.1 (by omega), hV p.2 (by omega)]
  have hpow0 : ∀ (H : PowerSeries ℤ) (r : ℕ), H.coeff 0 = 0 → 1 ≤ r → (H ^ r).coeff 0 = 0 := by
    intro H r hH0 hr
    rw [show r = (r - 1) + 1 by omega, pow_succ, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff, hH0, mul_zero]
  rw [show e = (e - 1) + 1 by omega, pow_succ, pow_succ]
  apply hmul (hpow0 F (e - 1) hF0 (by omega)) hF0 (hpow0 G (e - 1) hG0 (by omega)) hG0 _ h
  intro j hj
  cases k with
  | zero => omega
  | succ k' =>
    exact coeff_pow_eq_of_prefix (n := k') (fun i hi => h i (by omega)) (e - 1) j (by omega)

private lemma coeff_posTerm_eq_of_strict_prefix {A B : PowerSeries ℤ} (hA0 : A.coeff 0 = 0)
    (hB0 : B.coeff 0 = 0) {k n : ℕ} (hn : 1 ≤ n) (h : ∀ j < k, A.coeff j = B.coeff j) :
    (posTerm A n).coeff k = (posTerm B n).coeff k := by
  unfold posTerm
  have hpow0 : ∀ (H : PowerSeries ℤ), H.coeff 0 = 0 →
      ((4 : PowerSeries ℤ) ^ n * H ^ n - 4 * H).coeff 0 = 0 := by
    intro H hH0
    rw [map_sub, PowerSeries.coeff_zero_eq_constantCoeff,
      map_mul, map_mul, map_pow, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, hH0,
      zero_pow (by omega), mul_zero, mul_zero, sub_zero]
  apply coeff_pow_eq_of_strict_prefix (hpow0 A hA0) (hpow0 B hB0) _ (n + 1) (by omega)
  intro j hj
  cases k with
  | zero => omega
  | succ k' =>
    have hpre : ∀ i ≤ k', A.coeff i = B.coeff i := fun i hi => h i (by omega)
    rw [map_sub, map_sub]
    have h1 : ((4 : PowerSeries ℤ) ^ n * A ^ n).coeff j = ((4 : PowerSeries ℤ) ^ n * B ^ n).coeff j :=
      coeff_mul_eq_of_prefix (fun _ _ => rfl) (coeff_pow_eq_of_prefix hpre n) j (by omega)
    have h2 : ((4 : PowerSeries ℤ) * A).coeff j = ((4 : PowerSeries ℤ) * B).coeff j :=
      coeff_mul_eq_of_prefix (fun _ _ => rfl) hpre j (by omega)
    rw [h1, h2]

private lemma coeff_negTerm_eq_of_strict_prefix {A B : PowerSeries ℤ} (hA0 : A.coeff 0 = 0)
    (hB0 : B.coeff 0 = 0) {k m : ℕ} (hm : 2 ≤ m) (h : ∀ j < k, A.coeff j = B.coeff j) :
    (negTerm A m).coeff k = (negTerm B m).coeff k := by
  unfold negTerm
  have hge2 : 2 ≤ m * (m - 1) := by
    have : 1 ≤ m - 1 := by omega
    nlinarith
  have hA_pow0 : (A ^ (m * (m - 1))).coeff 0 = 0 := by
    rw [show m * (m - 1) = (m * (m - 1) - 1) + 1 by omega, pow_succ,
      PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff, hA0, mul_zero]
  have hB_pow0 : (B ^ (m * (m - 1))).coeff 0 = 0 := by
    rw [show m * (m - 1) = (m * (m - 1) - 1) + 1 by omega, pow_succ,
      PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff, hB0, mul_zero]
  have hpow_le : ∀ j ≤ k, (A ^ (m * (m - 1))).coeff j = (B ^ (m * (m - 1))).coeff j := by
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | rfl
    · cases k with
      | zero => omega
      | succ k' =>
        exact coeff_pow_eq_of_prefix (n := k') (fun i hi => h i (by omega)) (m * (m - 1)) j (by omega)
    · exact coeff_pow_eq_of_strict_prefix hA0 hB0 h (m * (m - 1)) hge2
  have h4A : ∀ j ≤ k,
      ((4 : PowerSeries ℤ) ^ (m * (m - 1)) * A ^ (m * (m - 1))).coeff j =
      ((4 : PowerSeries ℤ) ^ (m * (m - 1)) * B ^ (m * (m - 1))).coeff j :=
    coeff_mul_eq_of_prefix (fun _ _ => rfl) hpow_le
  have h4A0 : ((4 : PowerSeries ℤ) ^ (m * (m - 1)) * A ^ (m * (m - 1))).coeff 0 = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff, hA_pow0, mul_zero]
  have h4B0 : ((4 : PowerSeries ℤ) ^ (m * (m - 1)) * B ^ (m * (m - 1))).coeff 0 = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff, hB_pow0, mul_zero]
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases hp1 : p.1 = 0
  · rw [hp1, h4A0, h4B0, zero_mul, zero_mul]
  · rw [h4A p.1 (by omega)]
    congr 1
    cases k with
    | zero => omega
    | succ k' =>
      have hpre : ∀ i ≤ k', A.coeff i = B.coeff i := fun i hi => h i (by omega)
      have hsub : ∀ i ≤ k', ((4 : PowerSeries ℤ) ^ (m + 1) * A ^ (m + 1)).coeff i =
          ((4 : PowerSeries ℤ) ^ (m + 1) * B ^ (m + 1)).coeff i :=
        coeff_mul_eq_of_prefix (fun _ _ => rfl) (coeff_pow_eq_of_prefix hpre (m + 1))
      exact coeff_pow_eq_of_prefix (coeff_invOneSub_eq_of_prefix hsub) (m - 1) p.2 (by omega)

private noncomputable def buildList : ℕ → List ℤ
  | 0 => []
  | k + 1 =>
    let L := buildList k
    let val : ℤ :=
      if k = 0 then 0
      else
        let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => L.getD j 0
        ((∑ n ∈ Finset.Icc 1 k, (posTerm Aprev n).coeff k) +
         (∑ m ∈ Finset.Icc 2 k, (negTerm Aprev m).coeff k) -
         twoTheta4Coeff k) / 4
    L ++ [val]

private lemma buildList_length (n : ℕ) : (buildList n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [buildList, ih]

private lemma buildList_getD_of_lt : ∀ (n j : ℕ), j < n →
    (buildList n).getD j 0 = (buildList (j + 1)).getD j 0 := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with rfl | hlt
    · rfl
    · simp only [buildList, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [buildList_length]; exact hlt)]
      exact ih j hlt

private noncomputable def buildSeq (k : ℕ) : ℤ :=
  (buildList (k + 1)).getD k 0

private lemma buildSeq_zero : buildSeq 0 = 0 := by
  unfold buildSeq; simp [buildList]

private lemma exists_solution : ∃ A : PowerSeries ℤ, SatisfiesA379764 A := by
  let A : PowerSeries ℤ := PowerSeries.mk buildSeq
  have hA0 : A.coeff 0 = 0 := by rw [PowerSeries.coeff_mk]; exact buildSeq_zero
  refine ⟨A, hA0, fun k => ?_⟩
  cases k with
  | zero =>
    have h1 : Finset.Icc 1 0 = ∅ := by decide
    have h2 : Finset.Icc 2 0 = ∅ := by decide
    rw [if_pos rfl, hA0, h1, h2]
    unfold twoTheta4Coeff
    simp
  | succ k' =>
    set k := k' + 1
    have hk0 : k ≠ 0 := Nat.succ_ne_zero k'
    have hbuild : A.coeff k =
        ((∑ n ∈ Finset.Icc 1 k, (posTerm A n).coeff k) +
         (∑ m ∈ Finset.Icc 2 k, (negTerm A m).coeff k) -
         twoTheta4Coeff k) / 4 := by
      rw [PowerSeries.coeff_mk]
      unfold buildSeq
      have hlen : (buildList k).length = k := buildList_length k
      have hlast : (buildList (k + 1)).getD k 0 =
          let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildList k).getD j 0
          ((∑ n ∈ Finset.Icc 1 k, (posTerm Aprev n).coeff k) +
           (∑ m ∈ Finset.Icc 2 k, (negTerm Aprev m).coeff k) -
           twoTheta4Coeff k) / 4 := by
        simp [buildList, List.getD_eq_getElem?_getD, hlen, hk0]
      rw [hlast]
      let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildList k).getD j 0
      have hAprev0 : Aprev.coeff 0 = 0 := by
        rw [PowerSeries.coeff_mk, buildList_getD_of_lt k 0 (by omega)]
        exact buildSeq_zero
      have hpre : ∀ j < k, Aprev.coeff j = A.coeff j := by
        intro j hj
        rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
        exact buildList_getD_of_lt k j hj
      have hpos : ∑ n ∈ Finset.Icc 1 k, (posTerm Aprev n).coeff k =
          ∑ n ∈ Finset.Icc 1 k, (posTerm A n).coeff k := by
        apply Finset.sum_congr rfl
        intro n hn; rw [Finset.mem_Icc] at hn
        exact coeff_posTerm_eq_of_strict_prefix hAprev0 hA0 hn.1 hpre
      have hneg : ∑ m ∈ Finset.Icc 2 k, (negTerm Aprev m).coeff k =
          ∑ m ∈ Finset.Icc 2 k, (negTerm A m).coeff k := by
        apply Finset.sum_congr rfl
        intro m hm; rw [Finset.mem_Icc] at hm
        exact coeff_negTerm_eq_of_strict_prefix hAprev0 hA0 hm.1 hpre
      change ((∑ n ∈ Finset.Icc 1 k, (posTerm Aprev n).coeff k) +
          (∑ m ∈ Finset.Icc 2 k, (negTerm Aprev m).coeff k) - twoTheta4Coeff k) / 4 = _
      rw [hpos, hneg]
    have hdvd_pos : (4 : ℤ) ∣ ∑ n ∈ Finset.Icc 1 k, (posTerm A n).coeff k := by
      apply Finset.dvd_sum
      intro n hn; rw [Finset.mem_Icc] at hn
      exact dvd_trans (by decide : (4 : ℤ) ∣ 16) (sixteen_dvd_posTerm A hn.1 k)
    have hdvd_neg : (4 : ℤ) ∣ ∑ m ∈ Finset.Icc 2 k, (negTerm A m).coeff k := by
      apply Finset.dvd_sum
      intro m hm; rw [Finset.mem_Icc] at hm
      exact dvd_trans (by decide : (4 : ℤ) ∣ 16) (sixteen_dvd_negTerm A hm.1 k)
    have hdvd_th : (4 : ℤ) ∣ twoTheta4Coeff k := by
      unfold twoTheta4Coeff
      rw [if_neg hk0]
      split_ifs
      · exact dvd_mul_right 4 _
      · exact dvd_zero 4
    have hdvd_num : (4 : ℤ) ∣
        (∑ n ∈ Finset.Icc 1 k, (posTerm A n).coeff k) +
        (∑ m ∈ Finset.Icc 2 k, (negTerm A m).coeff k) - twoTheta4Coeff k :=
      dvd_sub (dvd_add hdvd_pos hdvd_neg) hdvd_th
    rw [if_neg hk0, hbuild, Int.mul_ediv_cancel' hdvd_num]
    ring

private lemma coeff_congruences {A : PowerSeries ℤ} (hA : SatisfiesA379764 A)
    (n : ℕ) (hn : 1 ≤ n) :
    (Odd (A.coeff n) ↔ IsSquare n) ∧
    (A.coeff n ≡ (-1 : ℤ) ^ (n - 1) [ZMOD 4] ↔ IsSquare n) ∧
    (¬ IsSquare n → (4 : ℤ) ∣ A.coeff n) := by
  have heq := hA.2 n
  rw [if_neg (by omega), zero_sub] at heq
  have hdvd_pos : (16 : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, (posTerm A i).coeff n := by
    apply Finset.dvd_sum
    intro i hi; rw [Finset.mem_Icc] at hi
    exact sixteen_dvd_posTerm A hi.1 n
  have hdvd_neg : (16 : ℤ) ∣ ∑ m ∈ Finset.Icc 2 n, (negTerm A m).coeff n := by
    apply Finset.dvd_sum
    intro m hm; rw [Finset.mem_Icc] at hm
    exact sixteen_dvd_negTerm A hm.1 n
  obtain ⟨q, hq⟩ := dvd_add hdvd_pos hdvd_neg
  have heq2 : -4 * A.coeff n + 16 * q = twoTheta4Coeff n := by linarith
  by_cases hsq : IsSquare n
  · have hth : twoTheta4Coeff n = 4 * (-1 : ℤ) ^ n := by
      unfold twoTheta4Coeff; rw [if_neg (by omega), if_pos hsq]
    rw [hth] at heq2
    have hsign : -(-1 : ℤ) ^ n = (-1 : ℤ) ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      ring
    have hAn : A.coeff n = (-1 : ℤ) ^ (n - 1) + 4 * q := by linarith
    have hpow_odd : (-1 : ℤ) ^ (n - 1) = 1 ∨ (-1 : ℤ) ^ (n - 1) = -1 := by
      rcases Nat.even_or_odd (n - 1) with hev | hodd
      · left; exact hev.neg_one_pow
      · right; exact hodd.neg_one_pow
    refine ⟨⟨fun _ => hsq, fun _ => ?_⟩, ⟨fun _ => hsq, fun _ => ?_⟩, fun h => (h hsq).elim⟩
    · rcases hpow_odd with h1 | hm1
      · exact ⟨2 * q, by omega⟩
      · exact ⟨2 * q - 1, by omega⟩
    · rw [Int.modEq_iff_dvd]
      exact ⟨-q, by linarith⟩
  · have hth : twoTheta4Coeff n = 0 := by
      unfold twoTheta4Coeff; rw [if_neg (by omega), if_neg hsq]
    rw [hth] at heq2
    have hAn : A.coeff n = 4 * q := by linarith
    have hpow_odd : (-1 : ℤ) ^ (n - 1) = 1 ∨ (-1 : ℤ) ^ (n - 1) = -1 := by
      rcases Nat.even_or_odd (n - 1) with hev | hodd
      · left; exact hev.neg_one_pow
      · right; exact hodd.neg_one_pow
    refine ⟨⟨fun ⟨r, hr⟩ => by omega, fun h => (hsq h).elim⟩,
      ⟨fun hmod => ?_, fun h => (hsq h).elim⟩,
      fun _ => ⟨q, hAn⟩⟩
    rw [Int.modEq_iff_dvd] at hmod
    obtain ⟨t, ht⟩ := hmod
    rcases hpow_odd with h1 | hm1 <;> omega

theorem solve : type_of% @OMA.S_oeis_a379764.main :=
  ⟨exists_solution, fun _ hA n hn => coeff_congruences hA n hn⟩

end A379764Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a379764.main :=
  A379764Proof.solve
