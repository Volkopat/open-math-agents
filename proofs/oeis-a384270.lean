import OMAStatements.S_oeis_a384270

section Helpers

open PowerSeries

private noncomputable def argV {R : Type*} [CommRing R] (A : PowerSeries R) : PowerSeries R :=
  (X : PowerSeries R) ^ 3 + 3 * X * A ^ 3

private noncomputable def argW {R : Type*} [CommRing R] (A : PowerSeries R) : PowerSeries R :=
  (X : PowerSeries R) ^ 4 + 4 * X * A ^ 4

private noncomputable def lhsEq {R : Type*} [CommRing R] (A : PowerSeries R) : PowerSeries R :=
  A * A.subst (argV A)

private noncomputable def rhsEq {R : Type*} [CommRing R] (A : PowerSeries R) : PowerSeries R :=
  A.subst (argW A)

private lemma X_dvd_of_constantCoeff_zero {R : Type*} [CommRing R] {A : PowerSeries R}
    (hA : A.constantCoeff = 0) : (X : PowerSeries R) ∣ A := by
  rw [← pow_one (X : PowerSeries R), X_pow_dvd_iff]
  intro m hm
  rw [Nat.lt_one_iff.mp hm, coeff_zero_eq_constantCoeff, hA]

private lemma X_pow_mul_dvd {R : Type*} [CommRing R] {P : PowerSeries R} {k : ℕ}
    (hP : (X : PowerSeries R) ^ k ∣ P) (d : ℕ) : (X : PowerSeries R) ^ (k * d) ∣ P ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, pow_add, pow_succ]
    exact mul_dvd_mul ih hP

private lemma X_pow_three_dvd_argV {R : Type*} [CommRing R] {A : PowerSeries R}
    (hA : A.constantCoeff = 0) : (X : PowerSeries R) ^ 3 ∣ argV A := by
  have hA3 : (X : PowerSeries R) ^ 3 ∣ A ^ 3 :=
    pow_dvd_pow_of_dvd (X_dvd_of_constantCoeff_zero hA) 3
  dsimp [argV]
  exact dvd_add dvd_rfl (dvd_mul_of_dvd_right hA3 _)

private lemma X_pow_four_dvd_argW {R : Type*} [CommRing R] {A : PowerSeries R}
    (hA : A.constantCoeff = 0) : (X : PowerSeries R) ^ 4 ∣ argW A := by
  have hA4 : (X : PowerSeries R) ^ 4 ∣ A ^ 4 :=
    pow_dvd_pow_of_dvd (X_dvd_of_constantCoeff_zero hA) 4
  dsimp [argW]
  exact dvd_add dvd_rfl (dvd_mul_of_dvd_right hA4 _)

private lemma hasSubst_of_X_pow_dvd {R : Type*} [CommRing R] {U : PowerSeries R} {k : ℕ}
    (hk : 0 < k) (hU : (X : PowerSeries R) ^ k ∣ U) : HasSubst U := by
  apply HasSubst.of_constantCoeff_zero'
  rw [← coeff_zero_eq_constantCoeff]
  exact X_pow_dvd_iff.mp hU 0 hk

private lemma argV_sub_dvd {R : Type*} [CommRing R] {A B : PowerSeries R} {n : ℕ}
    (hA : A.constantCoeff = 0) (hB : B.constantCoeff = 0)
    (hAB : (X : PowerSeries R) ^ n ∣ A - B) :
    (X : PowerSeries R) ^ (n + 3) ∣ argV A - argV B := by
  have hXA := X_dvd_of_constantCoeff_zero hA
  have hXB := X_dvd_of_constantCoeff_zero hB
  have h1 : (X : PowerSeries R) ^ 1 ∣ 3 * X := by
    rw [pow_one]
    exact dvd_mul_left X 3
  have h2 : (X : PowerSeries R) ^ 2 ∣ A ^ 2 + A * B + B ^ 2 := by
    refine dvd_add (dvd_add ?_ ?_) ?_
    · simpa using pow_dvd_pow_of_dvd hXA 2
    · rw [sq]
      exact mul_dvd_mul hXA hXB
    · simpa using pow_dvd_pow_of_dvd hXB 2
  have hAlg : argV A - argV B = 3 * X * (A - B) * (A ^ 2 + A * B + B ^ 2) := by
    dsimp [argV]
    ring
  rw [hAlg, show n + 3 = 1 + n + 2 by omega, pow_add, pow_add]
  exact mul_dvd_mul (mul_dvd_mul h1 hAB) h2

private lemma argW_sub_dvd {R : Type*} [CommRing R] {A B : PowerSeries R} {n : ℕ}
    (hA : A.constantCoeff = 0) (hB : B.constantCoeff = 0)
    (hAB : (X : PowerSeries R) ^ n ∣ A - B) :
    (X : PowerSeries R) ^ (n + 4) ∣ argW A - argW B := by
  have hXA := X_dvd_of_constantCoeff_zero hA
  have hXB := X_dvd_of_constantCoeff_zero hB
  have h1 : (X : PowerSeries R) ^ 1 ∣ 4 * X := by
    rw [pow_one]
    exact dvd_mul_left X 4
  have h3 : (X : PowerSeries R) ^ 3 ∣ A ^ 3 + A ^ 2 * B + A * B ^ 2 + B ^ 3 := by
    refine dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_
    · simpa using pow_dvd_pow_of_dvd hXA 3
    · rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one]
      exact mul_dvd_mul (pow_dvd_pow_of_dvd hXA 2) hXB
    · rw [show (3 : ℕ) = 1 + 2 by rfl, pow_add, pow_one]
      exact mul_dvd_mul hXA (pow_dvd_pow_of_dvd hXB 2)
    · simpa using pow_dvd_pow_of_dvd hXB 3
  have hAlg : argW A - argW B = 4 * X * (A - B) * (A ^ 3 + A ^ 2 * B + A * B ^ 2 + B ^ 3) := by
    dsimp [argW]
    ring
  rw [hAlg, show n + 4 = 1 + n + 3 by omega, pow_add, pow_add]
  exact mul_dvd_mul (mul_dvd_mul h1 hAB) h3

private lemma subst_mod {R : Type*} [CommRing R] {A B U V : PowerSeries R} {k N : ℕ}
    (hkpos : 0 < k) (hA0 : A.constantCoeff = 0) (hB0 : B.constantCoeff = 0)
    (hkU : (X : PowerSeries R) ^ k ∣ U) (hkV : (X : PowerSeries R) ^ k ∣ V)
    (hUV : (X : PowerSeries R) ^ N ∣ U - V)
    (hAB : ∀ d : ℕ, 1 ≤ d → k * d < N → coeff d A = coeff d B) :
    (X : PowerSeries R) ^ N ∣ A.subst U - B.subst V := by
  have hUs := hasSubst_of_X_pow_dvd hkpos hkU
  have hVs := hasSubst_of_X_pow_dvd hkpos hkV
  rw [X_pow_dvd_iff]
  intro e he
  rw [map_sub, sub_eq_zero, coeff_subst' hUs, coeff_subst' hVs]
  refine finsum_congr fun d => ?_
  by_cases hd0 : d = 0
  · subst hd0
    simp only [coeff_zero_eq_constantCoeff, hA0, hB0, zero_smul]
  · by_cases hkd : k * d < N
    · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
      rw [hAB d hd1 hkd]
      have hdvd : (X : PowerSeries R) ^ N ∣ U ^ d - V ^ d := hUV.trans (sub_dvd_pow_sub_pow U V d)
      have hce : coeff e (U ^ d) = coeff e (V ^ d) := by
        have hsub := X_pow_dvd_iff.mp hdvd e he
        rwa [map_sub, sub_eq_zero] at hsub
      rw [hce]
    · have he_lt : e < k * d := lt_of_lt_of_le he (not_lt.mp hkd)
      have hcU : coeff e (U ^ d) = 0 := X_pow_dvd_iff.mp (X_pow_mul_dvd hkU d) e he_lt
      have hcV : coeff e (V ^ d) = 0 := X_pow_dvd_iff.mp (X_pow_mul_dvd hkV d) e he_lt
      rw [hcU, hcV, smul_zero, smul_zero]

private lemma subst_argV_sub_X_pow {R : Type*} [CommRing R] {A : PowerSeries R}
    (hA0 : A.constantCoeff = 0) (hA1 : coeff 1 A = 1) :
    (X : PowerSeries R) ^ 4 ∣ A.subst (argV A) - X ^ 3 := by
  have hB0 : (X : PowerSeries R).constantCoeff = 0 := constantCoeff_X
  have hXV : (X : PowerSeries R) ^ 4 ∣ argV A - X ^ 3 := by
    dsimp [argV]
    rw [add_sub_cancel_left, show (4 : ℕ) = 1 + 3 by rfl, pow_add]
    exact mul_dvd_mul (by rw [pow_one]; exact dvd_mul_left X 3)
      (pow_dvd_pow_of_dvd (X_dvd_of_constantCoeff_zero hA0) 3)
  have hX3 : (X : PowerSeries R) ^ 3 ∣ X ^ 3 := dvd_rfl
  have hsub := subst_mod (k := 3) (N := 4) (by omega) hA0 hB0
    (X_pow_three_dvd_argV hA0) hX3 hXV (fun d hd1 hkd => by
      have hd : d = 1 := by omega
      subst hd
      rw [hA1, coeff_X]
      simp)
  have hXsub : (X : PowerSeries R).subst (X ^ 3) = X ^ 3 :=
    subst_X (hasSubst_of_X_pow_dvd (k := 3) (by omega) hX3)
  rwa [hXsub] at hsub

private lemma rhsEq_sub_X_pow {R : Type*} [CommRing R] {A : PowerSeries R}
    (hA0 : A.constantCoeff = 0) (hA1 : coeff 1 A = 1) :
    (X : PowerSeries R) ^ 5 ∣ rhsEq A - X ^ 4 := by
  have hB0 : (X : PowerSeries R).constantCoeff = 0 := constantCoeff_X
  have hXW : (X : PowerSeries R) ^ 5 ∣ argW A - X ^ 4 := by
    dsimp [argW]
    rw [add_sub_cancel_left, show (5 : ℕ) = 1 + 4 by rfl, pow_add]
    exact mul_dvd_mul (by rw [pow_one]; exact dvd_mul_left X 4)
      (pow_dvd_pow_of_dvd (X_dvd_of_constantCoeff_zero hA0) 4)
  have hX4 : (X : PowerSeries R) ^ 4 ∣ X ^ 4 := dvd_rfl
  have hsub := subst_mod (k := 4) (N := 5) (by omega) hA0 hB0
    (X_pow_four_dvd_argW hA0) hX4 hXW (fun d hd1 hkd => by
      have hd : d = 1 := by omega
      subst hd
      rw [hA1, coeff_X]
      simp)
  have hXsub : (X : PowerSeries R).subst (X ^ 4) = X ^ 4 :=
    subst_X (hasSubst_of_X_pow_dvd (k := 4) (by omega) hX4)
  dsimp [rhsEq]
  rwa [hXsub] at hsub

private lemma lhsEq_sub_X_pow {R : Type*} [CommRing R] {A : PowerSeries R}
    (hA0 : A.constantCoeff = 0) (hA1 : coeff 1 A = 1) :
    (X : PowerSeries R) ^ 5 ∣ lhsEq A - X ^ 4 := by
  have hAX2 : (X : PowerSeries R) ^ 2 ∣ A - X := by
    rw [X_pow_dvd_iff]
    intro m hm
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · simp only [map_sub, coeff_zero_eq_constantCoeff, hA0, constantCoeff_X, sub_self]
    · rw [map_sub, hA1, coeff_X]
      simp
  have hF := subst_argV_sub_X_pow hA0 hA1
  have hAlg : lhsEq A - X ^ 4 =
      (A - X) * (A.subst (argV A) - X ^ 3) + (A - X) * X ^ 3 + X * (A.subst (argV A) - X ^ 3) := by
    dsimp [lhsEq]
    ring
  rw [hAlg]
  refine dvd_add (dvd_add ?_ ?_) ?_
  · rw [show (5 : ℕ) = 2 + 3 by rfl, pow_add]
    exact mul_dvd_mul hAX2 (dvd_trans (by rw [show (4 : ℕ) = 3 + 1 by rfl, pow_add]; exact dvd_mul_right _ _) hF)
  · rw [show (5 : ℕ) = 2 + 3 by rfl, pow_add]
    exact mul_dvd_mul hAX2 dvd_rfl
  · rw [show (5 : ℕ) = 1 + 4 by rfl, pow_add, pow_one]
    exact mul_dvd_mul dvd_rfl hF

private lemma rhsEq_sub_dvd {R : Type*} [CommRing R] {A B : PowerSeries R} {n : ℕ}
    (hn : 2 ≤ n) (hA0 : A.constantCoeff = 0) (hB0 : B.constantCoeff = 0)
    (hAB : (X : PowerSeries R) ^ n ∣ A - B) :
    (X : PowerSeries R) ^ (n + 4) ∣ rhsEq A - rhsEq B := by
  dsimp [rhsEq]
  refine subst_mod (k := 4) (N := n + 4) (by omega) hA0 hB0
    (X_pow_four_dvd_argW hA0) (X_pow_four_dvd_argW hB0) (argW_sub_dvd hA0 hB0 hAB) ?_
  intro d hd1 hkd
  have hdn : d < n := by omega
  have hsub := X_pow_dvd_iff.mp hAB d hdn
  rwa [map_sub, sub_eq_zero] at hsub

private lemma lhsEq_sub_dvd {R : Type*} [CommRing R] {A B : PowerSeries R} {n : ℕ}
    (hn : 2 ≤ n) (hA0 : A.constantCoeff = 0) (hB0 : B.constantCoeff = 0)
    (hA1 : coeff 1 A = 1) (hAB : (X : PowerSeries R) ^ n ∣ A - B) :
    (X : PowerSeries R) ^ (n + 4) ∣ (lhsEq A - lhsEq B) - (A - B) * X ^ 3 := by
  have hSubV : (X : PowerSeries R) ^ (n + 3) ∣ A.subst (argV A) - B.subst (argV B) := by
    refine subst_mod (k := 3) (N := n + 3) (by omega) hA0 hB0
      (X_pow_three_dvd_argV hA0) (X_pow_three_dvd_argV hB0) (argV_sub_dvd hA0 hB0 hAB) ?_
    intro d hd1 hkd
    have hdn : d < n := by omega
    have hsub := X_pow_dvd_iff.mp hAB d hdn
    rwa [map_sub, sub_eq_zero] at hsub
  have hFA := subst_argV_sub_X_pow hA0 hA1
  have hXB := X_dvd_of_constantCoeff_zero hB0
  have hAlg : (lhsEq A - lhsEq B) - (A - B) * X ^ 3 =
      (A - B) * (A.subst (argV A) - X ^ 3) + B * (A.subst (argV A) - B.subst (argV B)) := by
    dsimp [lhsEq]
    ring
  rw [hAlg]
  refine dvd_add ?_ ?_
  · rw [pow_add]
    exact mul_dvd_mul hAB hFA
  · rw [show n + 4 = 1 + (n + 3) by omega, pow_add, pow_one]
    exact mul_dvd_mul hXB hSubV

private lemma coeff_lhsEq_sub_step {R : Type*} [CommRing R] {A B : PowerSeries R} {n : ℕ}
    (hn : 2 ≤ n) (hA0 : A.constantCoeff = 0) (hB0 : B.constantCoeff = 0)
    (hA1 : coeff 1 A = 1) (hAB : (X : PowerSeries R) ^ n ∣ A - B) :
    coeff (n + 3) (lhsEq A) - coeff (n + 3) (lhsEq B) = coeff n A - coeff n B := by
  have h0 := X_pow_dvd_iff.mp (lhsEq_sub_dvd hn hA0 hB0 hA1 hAB) (n + 3) (by omega)
  rw [map_sub, map_sub, sub_eq_zero, mul_comm, coeff_X_pow_mul'] at h0
  simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, map_sub] at h0
  exact h0

private lemma coeff_rhsEq_step {R : Type*} [CommRing R] {A B : PowerSeries R} {n : ℕ}
    (hn : 2 ≤ n) (hA0 : A.constantCoeff = 0) (hB0 : B.constantCoeff = 0)
    (hAB : (X : PowerSeries R) ^ n ∣ A - B) :
    coeff (n + 3) (rhsEq A) = coeff (n + 3) (rhsEq B) := by
  have h0 := X_pow_dvd_iff.mp (rhsEq_sub_dvd hn hA0 hB0 hAB) (n + 3) (by omega)
  rwa [map_sub, sub_eq_zero] at h0

private lemma unique_of_eq {R : Type*} [CommRing R] {A B : PowerSeries R}
    (hA0 : A.constantCoeff = 0) (hA1 : coeff 1 A = 1) (hAe : lhsEq A = rhsEq A)
    (hB0 : B.constantCoeff = 0) (hB1 : coeff 1 B = 1) (hBe : lhsEq B = rhsEq B) :
    A = B := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp only [coeff_zero_eq_constantCoeff, hA0, hB0]
    · rw [hA1, hB1]
    · have hAB : (X : PowerSeries R) ^ (n + 2) ∣ A - B := by
        rw [X_pow_dvd_iff]
        intro m hm
        rw [map_sub, sub_eq_zero, ih m hm]
      have hL := coeff_lhsEq_sub_step (by omega) hA0 hB0 hA1 hAB
      have hR := coeff_rhsEq_step (by omega) hA0 hB0 hAB
      rw [hAe, hBe, hR, sub_self, eq_comm, sub_eq_zero] at hL
      exact hL

private noncomputable def seq : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let P : PowerSeries ℤ := ∑ i : Fin (n + 2), C (seq i.1) * X ^ i.1
    coeff (n + 5) (rhsEq P) - coeff (n + 5) (lhsEq P)

private noncomputable def seriesA : PowerSeries ℤ := PowerSeries.mk seq

private lemma coeff_finSum_seq (m n : ℕ) :
    coeff m (∑ i : Fin n, C (seq i.1) * (X : PowerSeries ℤ) ^ i.1) = if m < n then seq m else 0 := by
  rw [map_sum]
  split_ifs with hm
  · rw [Finset.sum_eq_single ⟨m, hm⟩]
    · rw [coeff_C_mul, coeff_X_pow]
      simp
    · intro b _ hb
      have hne : m ≠ b.1 := fun h => hb (Fin.ext h.symm)
      rw [coeff_C_mul, coeff_X_pow]
      simp [hne]
    · intro hmem
      exact absurd (Finset.mem_univ (⟨m, hm⟩ : Fin n)) hmem
  · refine Finset.sum_eq_zero fun b _ => ?_
    have hne : m ≠ b.1 := fun h => hm (h ▸ b.isLt)
    rw [coeff_C_mul, coeff_X_pow]
    simp [hne]

private lemma defines_seriesA : OMA.S_oeis_a384270.Defines seriesA := by
  have hA0 : seriesA.constantCoeff = 0 := by
    rw [← coeff_zero_eq_constantCoeff, seriesA, coeff_mk, seq]
  have hA1 : coeff 1 seriesA = 1 := by
    rw [seriesA, coeff_mk, seq]
  refine ⟨hA0, hA1, ?_⟩
  change lhsEq seriesA = rhsEq seriesA
  ext m
  by_cases hm : m < 5
  · have hL := X_pow_dvd_iff.mp (lhsEq_sub_X_pow hA0 hA1) m hm
    have hR := X_pow_dvd_iff.mp (rhsEq_sub_X_pow hA0 hA1) m hm
    rw [map_sub, sub_eq_zero] at hL hR
    rw [hL, hR]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 5 := ⟨m - 5, by omega⟩
    let P : PowerSeries ℤ := ∑ i : Fin (k + 2), C (seq i.1) * X ^ i.1
    have hP0 : P.constantCoeff = 0 := by
      rw [← coeff_zero_eq_constantCoeff, coeff_finSum_seq]
      simp [seq]
    have hP1 : coeff 1 P = 1 := by
      rw [coeff_finSum_seq]
      simp [seq]
    have hAP : (X : PowerSeries ℤ) ^ (k + 2) ∣ seriesA - P := by
      rw [X_pow_dvd_iff]
      intro d hd
      rw [map_sub, sub_eq_zero, seriesA, coeff_mk, coeff_finSum_seq]
      simp [hd]
    have hL := coeff_lhsEq_sub_step (by omega) hA0 hP0 hA1 hAP
    have hR := coeff_rhsEq_step (by omega) hA0 hP0 hAP
    have hPk2 : coeff (k + 2) P = 0 := by
      rw [coeff_finSum_seq]
      simp
    have hAk2 : coeff (k + 2) seriesA = coeff (k + 5) (rhsEq P) - coeff (k + 5) (lhsEq P) := by
      rw [seriesA, coeff_mk, seq]
    rw [hPk2, sub_zero, hAk2] at hL
    have hLk5 : coeff (k + 5) (lhsEq seriesA) = coeff (k + 5) (rhsEq P) := by linarith
    rw [hLk5, hR]

private noncomputable def seriesB : PowerSeries (ZMod 2) :=
  letI := Classical.propDecidable
  PowerSeries.mk (fun n => if ∃ k : ℕ, n = 2 ^ k then 1 else 0)

private lemma coeff_seriesB_eq_one (n : ℕ) :
    coeff n seriesB = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  unfold seriesB
  simp only [coeff_mk]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

private lemma coeff_seriesB_eq_zero (n : ℕ) :
    coeff n seriesB = 0 ↔ ¬ ∃ k : ℕ, n = 2 ^ k := by
  unfold seriesB
  simp only [coeff_mk]
  split_ifs with h
  · exact iff_of_false (by decide) (not_not.mpr h)
  · exact iff_of_true rfl h

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

private lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

private lemma zmod2_series_add_self (F : PowerSeries (ZMod 2)) : F + F = 0 := by
  ext n
  rw [map_add, map_zero]
  exact zmod2_add_self _

private lemma zmod2_series_add_sq (F G : PowerSeries (ZMod 2)) : (F + G) ^ 2 = F ^ 2 + G ^ 2 := by
  have h2 : (2 : PowerSeries (ZMod 2)) * (F * G) = 0 := by
    rw [show (2 : PowerSeries (ZMod 2)) * (F * G) = F * G + F * G by ring]
    exact zmod2_series_add_self _
  calc (F + G) ^ 2 = F ^ 2 + 2 * (F * G) + G ^ 2 := by ring
    _ = F ^ 2 + 0 + G ^ 2 := by rw [h2]
    _ = F ^ 2 + G ^ 2 := by rw [add_zero]

private lemma zmod2_series_add_two_pow (F G : PowerSeries (ZMod 2)) (k : ℕ) :
    (F + G) ^ (2 ^ k) = F ^ (2 ^ k) + G ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih, zmod2_series_add_sq]

private lemma seriesB_sq_add_seriesB : seriesB ^ 2 + seriesB = X := by
  ext n
  rw [map_add, sq, coeff_mul]
  have hsq : ∑ p ∈ Finset.antidiagonal n, coeff p.1 seriesB * coeff p.2 seriesB =
      if 2 ∣ n then coeff (n / 2) seriesB else 0 := by
    split_ifs with h2
    · obtain ⟨m, rfl⟩ := h2
      have hm_mem : (m, m) ∈ Finset.antidiagonal (2 * m) :=
        Finset.mem_antidiagonal.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hm_mem]
      have hrest : ∑ p ∈ (Finset.antidiagonal (2 * m)).erase (m, m),
          coeff p.1 seriesB * coeff p.2 seriesB = 0 := by
        refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
        · intro p _
          rw [mul_comm (coeff p.2 seriesB)]
          exact zmod2_add_self _
        · intro p hp _ hpeq
          have hp' := Finset.mem_erase.mp hp
          have hadd := Finset.mem_antidiagonal.mp hp'.2
          have h12 : p.1 = p.2 := congrArg Prod.fst hpeq.symm
          exact hp'.1 (Prod.ext (by omega) (by omega))
        · intro p hp
          have hp' := Finset.mem_erase.mp hp
          have hadd := Finset.mem_antidiagonal.mp hp'.2
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_antidiagonal.mpr (by omega)⟩
          intro hpeq
          exact hp'.1 (Prod.ext (congrArg Prod.snd hpeq) (congrArg Prod.fst hpeq))
        · intro p _
          rfl
      rw [hrest, add_zero, Nat.mul_div_cancel_left m (by omega), zmod2_mul_self]
    · refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p _
        rw [mul_comm (coeff p.2 seriesB)]
        exact zmod2_add_self _
      · intro p hp _ hpeq
        have hadd := Finset.mem_antidiagonal.mp hp
        have h12 : p.1 = p.2 := congrArg Prod.fst hpeq.symm
        exact h2 ⟨p.1, by omega⟩
      · intro p hp
        have hadd := Finset.mem_antidiagonal.mp hp
        exact Finset.mem_antidiagonal.mpr (by omega)
      · intro p _
        rfl
  rw [hsq]
  rcases eq_or_ne n 1 with rfl | hn1
  · have hnd2 : ¬ 2 ∣ (1 : ℕ) := by decide
    have hB1 : coeff 1 seriesB = 1 := (coeff_seriesB_eq_one 1).mpr ⟨0, by decide⟩
    simp [hnd2, hB1, coeff_X]
  · rw [coeff_X]
    simp only [hn1, ↓reduceIte]
    split_ifs with h2
    · obtain ⟨m, rfl⟩ := h2
      rw [Nat.mul_div_cancel_left m (by omega)]
      by_cases hm : ∃ k : ℕ, m = 2 ^ k
      · have hm2 : ∃ k : ℕ, 2 * m = 2 ^ k := by
          obtain ⟨k, rfl⟩ := hm
          exact ⟨k + 1, by rw [pow_succ']⟩
        rw [(coeff_seriesB_eq_one m).mpr hm, (coeff_seriesB_eq_one (2 * m)).mpr hm2]
        rfl
      · have hm2 : ¬ ∃ k : ℕ, 2 * m = 2 ^ k := by
          rintro ⟨k, hk⟩
          rcases k with _ | k
          · omega
          · rw [pow_succ'] at hk
            exact hm ⟨k, by omega⟩
        rw [(coeff_seriesB_eq_zero m).mpr hm, (coeff_seriesB_eq_zero (2 * m)).mpr hm2, add_zero]
    · by_cases hpow : ∃ k : ℕ, n = 2 ^ k
      · obtain ⟨k, rfl⟩ := hpow
        rcases k with _ | k
        · exact absurd rfl hn1
        · exact absurd ⟨2 ^ k, by rw [pow_succ']⟩ h2
      · rw [(coeff_seriesB_eq_zero n).mpr hpow, add_zero]

private lemma coeff_seriesB_subst' {U : PowerSeries (ZMod 2)} (hU : U.constantCoeff = 0) (n : ℕ) :
    coeff n (seriesB.subst U) = ∑ k ∈ Finset.range (n + 1), coeff n (U ^ (2 ^ k)) := by
  have hUs := HasSubst.of_constantCoeff_zero' hU
  rw [coeff_subst' hUs]
  have hX : (X : PowerSeries (ZMod 2)) ∣ U := X_dvd_of_constantCoeff_zero hU
  have hsupp : Function.support (fun d => coeff d seriesB • coeff n (U ^ d)) ⊆
      (Finset.image (fun k : ℕ => 2 ^ k) (Finset.range (n + 1)) : Finset ℕ) := by
    intro d hd
    rw [Function.mem_support] at hd
    have hd_le : d ≤ n := by
      by_contra hlt
      have hlt' : n < d := Nat.lt_of_not_ge hlt
      have hc0 : coeff n (U ^ d) = 0 :=
        X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX d) n hlt'
      rw [hc0, smul_zero] at hd
      exact hd rfl
    have hBne : coeff d seriesB ≠ 0 := fun h0 => hd (by rw [h0, zero_smul])
    have hex : ∃ k : ℕ, d = 2 ^ k := by
      by_contra hnex
      exact hBne ((coeff_seriesB_eq_zero d).mpr hnex)
    obtain ⟨k, rfl⟩ := hex
    rw [Finset.mem_coe, Finset.mem_image]
    have hk_lt : k < n + 1 := Nat.lt_trans Nat.lt_two_pow_self (Nat.lt_succ_iff.mpr hd_le)
    exact ⟨k, Finset.mem_range.mpr hk_lt, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [(coeff_seriesB_eq_one (2 ^ k)).mpr ⟨k, rfl⟩, one_smul]
  · intro a _ b _ hab
    exact Nat.pow_right_injective (by decide : 1 < 2) hab

private lemma seriesB_subst_add {U V : PowerSeries (ZMod 2)}
    (hU : U.constantCoeff = 0) (hV : V.constantCoeff = 0) :
    seriesB.subst (U + V) = seriesB.subst U + seriesB.subst V := by
  have hUV : (U + V).constantCoeff = 0 := by rw [map_add, hU, hV, add_zero]
  ext n
  rw [map_add, coeff_seriesB_subst' hUV n, coeff_seriesB_subst' hU n, coeff_seriesB_subst' hV n,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zmod2_series_add_two_pow, map_add]

private lemma seriesB_subst_sq_add {U : PowerSeries (ZMod 2)} (hU : U.constantCoeff = 0) :
    seriesB.subst (U ^ 2) + seriesB.subst U = U := by
  have hU2 : (U ^ 2).constantCoeff = 0 := by rw [map_pow, hU, zero_pow (by decide)]
  have hX : (X : PowerSeries (ZMod 2)) ∣ U := X_dvd_of_constantCoeff_zero hU
  ext n
  rw [map_add, coeff_seriesB_subst' hU2 n, coeff_seriesB_subst' hU n]
  have h0 : ∑ k ∈ Finset.range (n + 1), coeff n ((U ^ 2) ^ (2 ^ k)) =
      ∑ k ∈ Finset.range n, coeff n (U ^ (2 ^ (k + 1))) := by
    rw [Finset.sum_range_succ]
    have hpow : ∀ k : ℕ, (U ^ 2) ^ (2 ^ k) = U ^ (2 ^ (k + 1)) := fun k => by
      rw [← pow_mul, pow_succ']
    simp_rw [hpow]
    have hlast : coeff n (U ^ (2 ^ (n + 1))) = 0 := by
      have hlt : n < 2 ^ (n + 1) := lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self n))
      exact X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX (2 ^ (n + 1))) n hlt
    rw [hlast, add_zero]
  have h1 : ∑ k ∈ Finset.range (n + 1), coeff n (U ^ (2 ^ k)) =
      coeff n U + ∑ k ∈ Finset.range n, coeff n (U ^ (2 ^ (k + 1))) := by
    rw [Finset.sum_range_succ', pow_zero, pow_one, add_comm]
  rw [h0, h1, add_left_comm, zmod2_add_self, add_zero]

private lemma seriesB_eq : lhsEq seriesB = rhsEq seriesB := by
  have hB0 : seriesB.constantCoeff = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_seriesB_eq_zero]
    rintro ⟨k, hk⟩
    have := Nat.two_pow_pos k
    omega
  have hB3_0 : (seriesB ^ 3).constantCoeff = 0 := by rw [map_pow, hB0, zero_pow (by decide)]
  have hB4_0 : (seriesB ^ 4).constantCoeff = 0 := by rw [map_pow, hB0, zero_pow (by decide)]
  have hB6_0 : ((seriesB ^ 3) ^ 2).constantCoeff = 0 := by rw [map_pow, hB3_0, zero_pow (by decide)]
  have hB8_0 : ((seriesB ^ 4) ^ 2).constantCoeff = 0 := by rw [map_pow, hB4_0, zero_pow (by decide)]
  have h11 : (1 : PowerSeries (ZMod 2)) + 1 = 0 := by
    rw [← map_one C, ← map_add, show (1 + 1 : ZMod 2) = 0 from rfl, map_zero]
  have h3p : (3 : PowerSeries (ZMod 2)) = 1 := by
    rw [show (3 : PowerSeries (ZMod 2)) = (1 + 1) + 1 by norm_num, h11, zero_add]
  have h4p : (4 : PowerSeries (ZMod 2)) = 0 := by
    rw [show (4 : PowerSeries (ZMod 2)) = (1 + 1) + (1 + 1) by norm_num, h11, zero_add]
  have hX : (X : PowerSeries (ZMod 2)) = seriesB ^ 2 + seriesB := seriesB_sq_add_seriesB.symm
  have hV_eq : argV seriesB = (seriesB ^ 3) ^ 2 + seriesB ^ 3 := by
    dsimp [argV]
    rw [h3p, one_mul, hX]
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
      rw [show (2 : PowerSeries (ZMod 2)) = 1 + 1 by norm_num, h11]
    calc (seriesB ^ 2 + seriesB) ^ 3 + (seriesB ^ 2 + seriesB) * seriesB ^ 3
        = seriesB ^ 6 + 3 * seriesB ^ 5 + 3 * seriesB ^ 4 + seriesB ^ 3 + seriesB ^ 5 + seriesB ^ 4 := by ring
      _ = seriesB ^ 6 + 4 * seriesB ^ 5 + 4 * seriesB ^ 4 + seriesB ^ 3 := by ring
      _ = seriesB ^ 6 + 0 * seriesB ^ 5 + 0 * seriesB ^ 4 + seriesB ^ 3 := by rw [h4p]
      _ = (seriesB ^ 3) ^ 2 + seriesB ^ 3 := by ring
  have hW_eq : argW seriesB = (seriesB ^ 4) ^ 2 + seriesB ^ 4 := by
    dsimp [argW]
    rw [h4p, zero_mul, zero_mul, add_zero, hX]
    rw [show (seriesB ^ 2 + seriesB) ^ 4 = ((seriesB ^ 2 + seriesB) ^ 2) ^ 2 by ring]
    rw [zmod2_series_add_sq, zmod2_series_add_sq]
    ring
  have hL : lhsEq seriesB = seriesB ^ 4 := by
    dsimp [lhsEq]
    rw [hV_eq, seriesB_subst_add hB6_0 hB3_0, seriesB_subst_sq_add hB3_0]
    ring
  have hR : rhsEq seriesB = seriesB ^ 4 := by
    dsimp [rhsEq]
    rw [hW_eq, seriesB_subst_add hB8_0 hB4_0, seriesB_subst_sq_add hB4_0]
  rw [hL, hR]

private lemma odd_iff_zmod2_eq_one (k : ℤ) : Odd k ↔ (k : ZMod 2) = 1 := by
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · constructor
    · intro hodd
      exfalso
      rcases hodd with ⟨t, ht⟩
      omega
    · intro h1
      exfalso
      have h0 : ((m + m : ℤ) : ZMod 2) = 0 := by
        push_cast
        exact zmod2_add_self _
      rw [h0] at h1
      exact absurd h1 (by decide)
  · constructor
    · intro _
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
    · intro _
      exact ⟨m, rfl⟩

end Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a384270.main := by
  refine ⟨⟨seriesA, defines_seriesA⟩, ?_⟩
  intro A hA n _
  rcases hA with ⟨hA0, hA1, hAeq⟩
  let f : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  let A2 : PowerSeries (ZMod 2) := A.map f
  have hA2_0 : A2.constantCoeff = 0 := by
    dsimp [A2]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_zero]
  have hA2_1 : PowerSeries.coeff 1 A2 = 1 := by
    dsimp [A2]
    rw [hA1, map_one]
  have hV_sub : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries ℤ) ^ 3 + 3 * PowerSeries.X * A ^ 3) :=
    hasSubst_of_X_pow_dvd (k := 3) (by omega) (X_pow_three_dvd_argV hA0)
  have hW_sub : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries ℤ) ^ 4 + 4 * PowerSeries.X * A ^ 4) :=
    hasSubst_of_X_pow_dvd (k := 4) (by omega) (X_pow_four_dvd_argW hA0)
  have hmap_eq : lhsEq A2 = rhsEq A2 := by
    have hmap := congrArg (PowerSeries.map f) hAeq
    rw [map_mul] at hmap
    change PowerSeries.map f A * MvPowerSeries.map f (PowerSeries.subst _ A) =
      MvPowerSeries.map f (PowerSeries.subst _ A) at hmap
    rw [PowerSeries.map_subst hV_sub, PowerSeries.map_subst hW_sub] at hmap
    have hmV : MvPowerSeries.map f ((PowerSeries.X : PowerSeries ℤ) ^ 3 + 3 * PowerSeries.X * A ^ 3) = argV A2 := by
      change PowerSeries.map f ((PowerSeries.X : PowerSeries ℤ) ^ 3 + 3 * PowerSeries.X * A ^ 3) = argV A2
      dsimp [argV, A2]
      simp [map_ofNat]
    have hmW : MvPowerSeries.map f ((PowerSeries.X : PowerSeries ℤ) ^ 4 + 4 * PowerSeries.X * A ^ 4) = argW A2 := by
      change PowerSeries.map f ((PowerSeries.X : PowerSeries ℤ) ^ 4 + 4 * PowerSeries.X * A ^ 4) = argW A2
      dsimp [argW, A2]
      simp [map_ofNat]
    rw [hmV, hmW] at hmap
    exact hmap
  have hB0 : seriesB.constantCoeff = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_seriesB_eq_zero]
    rintro ⟨k, hk⟩
    have := Nat.two_pow_pos k
    omega
  have hB1 : PowerSeries.coeff 1 seriesB = 1 := (coeff_seriesB_eq_one 1).mpr ⟨0, by decide⟩
  have hA2_eq_B : A2 = seriesB :=
    unique_of_eq hA2_0 hA2_1 hmap_eq hB0 hB1 seriesB_eq
  rw [odd_iff_zmod2_eq_one]
  change (f (PowerSeries.coeff n A)) = 1 ↔ ∃ k : ℕ, n = 2 ^ k
  rw [← PowerSeries.coeff_map f, show A.map f = A2 from rfl, hA2_eq_B, coeff_seriesB_eq_one]
