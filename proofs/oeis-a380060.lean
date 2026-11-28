import OMAStatements.S_oeis_a380060

/-!
Proof of the OEIS A380060 conjecture.
-/

namespace A380060Proof

open Finset PowerSeries OMA.S_oeis_a380060

private lemma coeff_pow_eq_zero_of_lt {F : PowerSeries ℤ} (hF : F.coeff 0 = 0) :
    ∀ j k : ℕ, k < j → (F ^ j).coeff k = 0 := by
  intro j
  induction j with
  | zero => intro k hk; omega
  | succ j ih =>
    intro k hk
    rw [pow_succ, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases hp2 : p.2 = 0
    · rw [hp2, hF, mul_zero]
    · rw [ih p.1 (by omega), zero_mul]

private lemma mul_invOneSub_eq_one {F : PowerSeries ℤ} (hF : F.coeff 0 = 0) :
    (1 - F) * invOneSub F = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_one]
  unfold invOneSub
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  have hFmul : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      F.coeff p.1 * (PowerSeries.mk fun k => ∑ j ∈ Finset.range (k + 1), (F ^ j).coeff k).coeff p.2 =
      ∑ j ∈ Finset.range k, (F ^ (j + 1)).coeff k := by
    have h1 : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        F.coeff p.1 * (PowerSeries.mk fun k => ∑ j ∈ Finset.range (k + 1), (F ^ j).coeff k).coeff p.2 =
        F.coeff p.1 * ∑ j ∈ Finset.range (k + 1), (F ^ j).coeff p.2 := by
      intro p hp
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [PowerSeries.coeff_mk]
      congr 1
      have hsub : Finset.range (p.2 + 1) ⊆ Finset.range (k + 1) := Finset.range_mono (by omega)
      rw [Finset.sum_subset hsub]
      intro j hj hnot
      rw [Finset.mem_range] at hj hnot
      exact coeff_pow_eq_zero_of_lt hF j p.2 (by omega)
    rw [Finset.sum_congr rfl h1]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ j ∈ Finset.range (k + 1),
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, F.coeff p.1 * (F ^ j).coeff p.2 = (F ^ (j + 1)).coeff k := by
      intro j _
      rw [pow_succ', PowerSeries.coeff_mul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_succ,
      coeff_pow_eq_zero_of_lt hF (k + 1) k (by omega), add_zero]
  rw [hFmul, Finset.sum_range_succ']
  simp [pow_zero, PowerSeries.coeff_one]

private lemma coeff_mul_eq_of_prefix {A₁ A₂ B₁ B₂ : PowerSeries ℤ} {n : ℕ}
    (h1 : ∀ j ≤ n, A₁.coeff j = B₁.coeff j) (h2 : ∀ j ≤ n, A₂.coeff j = B₂.coeff j) :
    ∀ k ≤ n, (A₁ * A₂).coeff k = (B₁ * B₂).coeff k := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
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

private lemma coeff_summand_eq_of_prefix {A B : PowerSeries ℤ} {k m : ℕ} (hm : 1 ≤ m)
    (h : ∀ j < k, A.coeff j = B.coeff j) :
    (summand A m).coeff k = (summand B m).coeff k := by
  unfold summand
  rw [mul_assoc, mul_assoc, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  split_ifs with hle
  · have hlt : k - m ^ 2 < k := by
      have hm1 : 1 ≤ m ^ 2 := by nlinarith
      omega
    have hpre : ∀ j ≤ k - m ^ 2, A.coeff j = B.coeff j := fun j hj => h j (by omega)
    have hsub : ∀ j ≤ k - m ^ 2, (A - PowerSeries.X ^ m).coeff j = (B - PowerSeries.X ^ m).coeff j := by
      intro j hj; simp [map_sub, hpre j hj]
    have hmul : ∀ j ≤ k - m ^ 2, (PowerSeries.X ^ m * A).coeff j = (PowerSeries.X ^ m * B).coeff j := by
      intro j hj
      rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
      split_ifs with hj'
      · exact hpre (j - m) (by omega)
      · rfl
    exact coeff_mul_eq_of_prefix
      (coeff_pow_eq_of_prefix hsub m)
      (coeff_pow_eq_of_prefix (coeff_invOneSub_eq_of_prefix hmul) m)
      (k - m ^ 2) le_rfl
  · rfl

private noncomputable def buildList : ℕ → List ℤ
  | 0 => []
  | n + 1 =>
    let L := buildList n
    let val : ℤ :=
      if n = 0 then 1
      else
        let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => L.getD j 0
        2 * ∑ m ∈ Finset.Icc 1 n, (summand Aprev m).coeff n
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

private lemma buildSeq_eq (k : ℕ) :
    buildSeq k =
      if k = 0 then 1
      else 2 * ∑ m ∈ Finset.Icc 1 k, (summand (PowerSeries.mk buildSeq) m).coeff k := by
  unfold buildSeq
  have hlen : (buildList k).length = k := buildList_length k
  have hlast : (buildList (k + 1)).getD k 0 =
      if k = 0 then 1
      else
        let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildList k).getD j 0
        2 * ∑ m ∈ Finset.Icc 1 k, (summand Aprev m).coeff k := by
    simp [buildList, List.getD_eq_getElem?_getD, hlen]
  rw [hlast]
  split_ifs with hk0
  · rfl
  · dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    apply coeff_summand_eq_of_prefix hm.1
    intro j hj
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    exact buildList_getD_of_lt k j hj

private lemma exists_solution : ∃ A : PowerSeries ℤ, SatisfiesA380060 A := by
  refine ⟨PowerSeries.mk buildSeq, ?_⟩
  unfold SatisfiesA380060
  ext k
  rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_mk]
  have h2 : (2 * PowerSeries.mk (fun k => ∑ m ∈ Finset.Icc 1 k, (summand (PowerSeries.mk buildSeq) m).coeff k)).coeff k =
      2 * ∑ m ∈ Finset.Icc 1 k, (summand (PowerSeries.mk buildSeq) m).coeff k := by
    have : (2 : PowerSeries ℤ) = PowerSeries.C 2 := rfl
    rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  rw [h2, buildSeq_eq k]
  cases k with
  | zero => simp
  | succ k' => simp

private lemma coeff_mod_four {A : PowerSeries ℤ} (hA : SatisfiesA380060 A) (n : ℕ) (hn : 1 ≤ n) :
    (A.coeff n % 4 = 2 ↔ IsSquare n) ∧ (¬ IsSquare n → (4 : ℤ) ∣ A.coeff n) := by
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hφ_coeff : ∀ (F : PowerSeries ℤ) (k : ℕ), (φ F).coeff k = ((F.coeff k : ℤ) : ZMod 2) := by
    intro F k; exact PowerSeries.coeff_map (Int.castRingHom (ZMod 2)) k F
  have hφX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X (Int.castRingHom (ZMod 2))
  have hφA : φ A = 1 := by
    rw [hA, map_add, map_one, map_mul, map_ofNat]
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
      ext k
      rw [show (2 : PowerSeries (ZMod 2)) = PowerSeries.C (2 : ZMod 2) from rfl,
        PowerSeries.coeff_C, map_zero]
      split_ifs <;> decide
    rw [h2, zero_mul, add_zero]
  have hφ_summand : ∀ m : ℕ, 1 ≤ m → φ (summand A m) = PowerSeries.X ^ (m ^ 2) := by
    intro m hm
    unfold summand
    have hF0 : (PowerSeries.X ^ m * A).coeff 0 = 0 := by
      rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
    have hinv := mul_invOneSub_eq_one hF0
    have hφ_inv : (1 - PowerSeries.X ^ m : PowerSeries (ZMod 2)) * φ (invOneSub (PowerSeries.X ^ m * A)) = 1 := by
      have h := congrArg φ hinv
      simp only [map_mul, map_sub, map_one, map_pow, hφX, hφA, mul_one] at h
      exact h
    simp only [map_mul, map_sub, map_pow, hφX, hφA]
    rw [mul_assoc, ← mul_pow, hφ_inv, one_pow, mul_one]
  set S : ℤ := ∑ m ∈ Finset.Icc 1 n, (summand A m).coeff n
  have hAn : A.coeff n = 2 * S := by
    have h := congrArg (PowerSeries.coeff n) hA
    rw [map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add] at h
    have h2 : (2 * PowerSeries.mk (fun k => ∑ m ∈ Finset.Icc 1 k, (summand A m).coeff k)).coeff n = 2 * S := by
      have : (2 : PowerSeries ℤ) = PowerSeries.C 2 := rfl
      rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    rw [h2] at h
    exact h
  have hS_mod2 : (S : ZMod 2) = if IsSquare n then 1 else 0 := by
    dsimp [S]
    rw [Int.cast_sum]
    have hterm : ∀ m ∈ Finset.Icc 1 n, ((summand A m).coeff n : ZMod 2) = if n = m ^ 2 then 1 else 0 := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [← hφ_coeff, hφ_summand m hm.1, PowerSeries.coeff_X_pow]
    rw [Finset.sum_congr rfl hterm]
    by_cases hsq : IsSquare n
    · rw [if_pos hsq]
      obtain ⟨r, hr⟩ := hsq
      have hr1 : 1 ≤ r := by nlinarith
      have hrn : r ≤ n := by nlinarith
      rw [Finset.sum_eq_single r]
      · rw [if_pos (by rw [hr, sq])]
      · intro m _ hmr
        rw [if_neg]
        intro heq
        have hsq_eq : m * m = r * r := by rw [← sq, ← heq, hr]
        rcases lt_trichotomy m r with hlt | heq' | hgt
        · nlinarith
        · exact hmr heq'
        · nlinarith
      · intro hnot
        exact (hnot (Finset.mem_Icc.mpr ⟨hr1, hrn⟩)).elim
    · rw [if_neg hsq]
      apply Finset.sum_eq_zero
      intro m _
      rw [if_neg]
      intro heq
      exact hsq ⟨m, by rw [heq, sq]⟩
  have hS_int : (S % 2 = 1 ↔ IsSquare n) ∧ (¬ IsSquare n → S % 2 = 0) := by
    have hZ : ∀ z : ℤ, (z : ZMod 2) = 0 ↔ z % 2 = 0 := by
      intro z
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      omega
    have hZ1 : ∀ z : ℤ, (z : ZMod 2) = 1 ↔ z % 2 = 1 := by
      intro z
      constructor
      · intro h1
        have h0 : ((z - 1 : ℤ) : ZMod 2) = 0 := by push_cast; rw [h1, sub_self]
        have := (hZ (z - 1)).mp h0
        omega
      · intro h1
        have h0 : ((z - 1 : ℤ) : ZMod 2) = 0 := (hZ (z - 1)).mpr (by omega)
        push_cast at h0
        exact sub_eq_zero.mp h0
    by_cases hsq : IsSquare n
    · rw [if_pos hsq] at hS_mod2
      exact ⟨⟨fun _ => hsq, fun _ => (hZ1 S).mp hS_mod2⟩, fun h => (h hsq).elim⟩
    · rw [if_neg hsq] at hS_mod2
      have h0 := (hZ S).mp hS_mod2
      exact ⟨⟨fun h1 => by omega, fun h => (hsq h).elim⟩, fun _ => h0⟩
  rw [hAn]
  constructor
  · constructor
    · intro hmod; exact hS_int.1.mp (by omega)
    · intro hsq; have := hS_int.1.mpr hsq; omega
  · intro hnsq
    have := hS_int.2 hnsq
    omega

theorem solve : type_of% @OMA.S_oeis_a380060.main :=
  ⟨exists_solution, fun _ hA n hn => coeff_mod_four hA n hn⟩

end A380060Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a380060.main :=
  A380060Proof.solve
