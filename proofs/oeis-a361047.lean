import OMAStatements.S_oeis_a361047

/-!
Proof of the OEIS A361047 conjecture (Paul D. Hanna).

1. Existence of `A` satisfying `SatisfiesA361047` via structural list recursion:
   Let `G(A) = X - X^3 * (derivPS A)^2`. Since `G(A) = X + O(X^3)`, for `n ≥ 2`:
   - `(G(A) ^ m).coeff n` for `m < n` only depends on `G(A).coeff j` for `j ≤ n - 1`,
     hence on `(derivPS A).coeff j` for `j ≤ n - 4`, hence on `A.coeff j` for `j ≤ n - 3 < n`;
   - `(G(A) ^ n).coeff n = (G(A).coeff 1)^n = 1`.
   Thus `[x^n] compPS A (G A) = A.coeff n + ∑_{m=0}^{n-1} A.coeff m * (G(A)^m).coeff n = 0`
   uniquely and explicitly determines `A.coeff n` over `ℤ` from `A.coeff j` (`j < n`).
2. Modulo 3 characterization (Frobenius telescoping!):
   Define `F : PowerSeries (ZMod 3)` by `F.coeff r = if ∃ k : ℕ, r = 3 ^ k then 1 else 0`.
   - `F.coeff 0 = 0`, `F.coeff 1 = 1`.
   - In `(ZMod 3)⟦X⟧`, `derivPS3 F = 1` (since for every `k ≥ 1`, `3 ∣ 3^k`!).
   - Hence `G3(F) = X - X^3`.
   - By the Frobenius identity `(X - X^3)^(3^k) = X^(3^k) - X^(3^(k+1))` in `(ZMod 3)⟦X⟧`,
     the sum `∑_{m=0}^n F.coeff m * ((X - X^3)^m).coeff n` telescopes to `(X : (ZMod 3)⟦X⟧).coeff n`!
   - By uniqueness of the solution to `compPS3 H (G3 H) = X` with `H.coeff 0 = 0, H.coeff 1 = 1`
     (proved by strong induction on `n`), `PowerSeries.map (Int.castRingHom (ZMod 3)) A = F`!
3. Specializing to `r = 2 * n + 1`: `2 * n + 1 = 3 ^ k ↔ n = (3 ^ k - 1) / 2` (since `3^k` is odd),
   giving the exact mod-3 characterization of `A.coeff (2 * n + 1)`.
-/

namespace A361047Proof

open Finset OMA.S_oeis_a361047

private lemma coeff_mul_eq_of_prefix {R : Type*} [CommRing R] {F₁ F₂ G₁ G₂ : PowerSeries R} {n : ℕ}
    (hF : ∀ j ≤ n, F₁.coeff j = F₂.coeff j) (hG : ∀ j ≤ n, G₁.coeff j = G₂.coeff j) :
    ∀ k ≤ n, (F₁ * G₁).coeff k = (F₂ * G₂).coeff k := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [hF p.1 (by omega), hG p.2 (by omega)]

private lemma coeff_pow_eq_of_prefix {R : Type*} [CommRing R] {F₁ F₂ : PowerSeries R} {n : ℕ}
    (hF : ∀ j ≤ n, F₁.coeff j = F₂.coeff j) :
    ∀ e k : ℕ, k ≤ n → (F₁ ^ e).coeff k = (F₂ ^ e).coeff k := by
  intro e
  induction e with
  | zero => intro k _; rfl
  | succ e ih =>
    intro k hk
    rw [pow_succ, pow_succ]
    exact coeff_mul_eq_of_prefix (fun j hj => ih j hj) hF k hk

private lemma coeff_pow_eq_zero_of_lt {R : Type*} [CommRing R] {G : PowerSeries R}
    (hG0 : G.coeff 0 = 0) :
    ∀ e k : ℕ, k < e → (G ^ e).coeff k = 0 := by
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
    · rw [hp2, hG0, mul_zero]
    · rw [ih p.1 (by omega), zero_mul]

private lemma coeff_pow_self {R : Type*} [CommRing R] {G : PowerSeries R}
    (hG0 : G.coeff 0 = 0) :
    ∀ e : ℕ, (G ^ e).coeff e = (G.coeff 1) ^ e := by
  intro e
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul]
    rw [Finset.sum_eq_single (e, 1)]
    · rw [ih]
    · intro p hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases hp2 : p.2 = 0
      · rw [hp2, hG0, mul_zero]
      · have hp1 : p.1 < e := by
          by_contra hge
          have h1 : p.1 = e := by omega
          have h2 : p.2 = 1 := by omega
          exact hne (Prod.ext h1 h2)
        rw [coeff_pow_eq_zero_of_lt hG0 e p.1 hp1, zero_mul]
    · intro hnot
      exact (hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega))).elim

private noncomputable def gOf (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.X - PowerSeries.X ^ 3 * (derivPS A) ^ 2

private lemma gOf_coeff_zero (A : PowerSeries ℤ) : (gOf A).coeff 0 = 0 := by
  unfold gOf
  rw [map_sub, PowerSeries.coeff_X, if_neg (by decide), PowerSeries.coeff_X_pow_mul',
    if_neg (by decide), sub_self]

private lemma gOf_coeff_one (A : PowerSeries ℤ) : (gOf A).coeff 1 = 1 := by
  unfold gOf
  rw [map_sub, PowerSeries.coeff_X, if_pos rfl, PowerSeries.coeff_X_pow_mul',
    if_neg (by decide), sub_zero]

private lemma gOf_coeff_eq_of_strict_prefix {A B : PowerSeries ℤ} {n : ℕ}
    (h : ∀ j < n, A.coeff j = B.coeff j) :
    ∀ j ≤ n, (gOf A).coeff j = (gOf B).coeff j := by
  intro j hj
  unfold gOf
  rw [map_sub, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  congr 1
  split_ifs with hle
  · have hd : ∀ i ≤ j - 3, (derivPS A).coeff i = (derivPS B).coeff i := by
      intro i hi
      unfold derivPS
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, h (i + 1) (by omega)]
    exact coeff_pow_eq_of_prefix hd 2 (j - 3) le_rfl
  · rfl

private noncomputable def buildList : ℕ → List ℤ
  | 0 => []
  | n + 1 =>
    let L := buildList n
    let val : ℤ :=
      if n = 0 then 0
      else if n = 1 then 1
      else
        let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => L.getD j 0
        (-(∑ m ∈ Finset.range n, Aprev.coeff m * ((gOf Aprev) ^ m).coeff n))
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

private noncomputable def buildSeq (n : ℕ) : ℤ :=
  (buildList (n + 1)).getD n 0

private lemma exists_solution : ∃ A : PowerSeries ℤ, SatisfiesA361047 A := by
  let A : PowerSeries ℤ := PowerSeries.mk buildSeq
  have hA0 : A.coeff 0 = 0 := by
    rw [PowerSeries.coeff_mk]; unfold buildSeq; simp [buildList]
  have hA1 : A.coeff 1 = 1 := by
    rw [PowerSeries.coeff_mk]; unfold buildSeq; simp [buildList]
  refine ⟨A, hA0, hA1, ?_⟩
  ext n
  unfold compPS
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_X]
  change ∑ m ∈ Finset.range (n + 1), A.coeff m * ((gOf A) ^ m).coeff n = if n = 1 then 1 else 0
  cases n with
  | zero => simp [hA0]
  | succ n' =>
    cases n' with
    | zero =>
      rw [if_pos rfl, Finset.sum_range_succ, Finset.sum_range_one, hA0, zero_mul, zero_add,
        hA1, one_mul, pow_one, gOf_coeff_one]
    | succ n'' =>
      set n := n'' + 2
      rw [if_neg (by omega), Finset.sum_range_succ, coeff_pow_self (gOf_coeff_zero A),
        gOf_coeff_one, one_pow, mul_one]
      have hAn : A.coeff n = -(∑ m ∈ Finset.range n, A.coeff m * ((gOf A) ^ m).coeff n) := by
        rw [PowerSeries.coeff_mk]
        unfold buildSeq
        have hlen : (buildList n).length = n := buildList_length n
        have hlast : (buildList (n + 1)).getD n 0 =
            let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildList n).getD j 0
            (-(∑ m ∈ Finset.range n, Aprev.coeff m * ((gOf Aprev) ^ m).coeff n)) := by
          conv_lhs => unfold buildList
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]), hlen,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
            show n ≠ 0 by omega, show n ≠ 1 by omega, ↓reduceIte]
        rw [hlast]
        let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildList n).getD j 0
        have hpre : ∀ j < n, Aprev.coeff j = A.coeff j := by
          intro j hj
          rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
          exact buildList_getD_of_lt n j hj
        have hg : ∀ j ≤ n, (gOf Aprev).coeff j = (gOf A).coeff j :=
          gOf_coeff_eq_of_strict_prefix hpre
        change -(∑ m ∈ Finset.range n, Aprev.coeff m * ((gOf Aprev) ^ m).coeff n) = _
        congr 1
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_range] at hm
        rw [hpre m hm, coeff_pow_eq_of_prefix hg m n le_rfl]
      rw [hAn, add_neg_cancel]

/-! ### Modulo 3 reduction and Frobenius telescoping -/

private noncomputable def derivPS3 (H : PowerSeries (ZMod 3)) : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun m => ((m + 1 : ℕ) : ZMod 3) * H.coeff (m + 1)

private noncomputable def gOf3 (H : PowerSeries (ZMod 3)) : PowerSeries (ZMod 3) :=
  PowerSeries.X - PowerSeries.X ^ 3 * (derivPS3 H) ^ 2

private noncomputable def compPS3 (H G : PowerSeries (ZMod 3)) : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1), H.coeff m * (G ^ m).coeff n

private lemma gOf3_coeff_zero (H : PowerSeries (ZMod 3)) : (gOf3 H).coeff 0 = 0 := by
  unfold gOf3
  rw [map_sub, PowerSeries.coeff_X, if_neg (by decide), PowerSeries.coeff_X_pow_mul',
    if_neg (by decide), sub_self]

private lemma gOf3_coeff_one (H : PowerSeries (ZMod 3)) : (gOf3 H).coeff 1 = 1 := by
  unfold gOf3
  rw [map_sub, PowerSeries.coeff_X, if_pos rfl, PowerSeries.coeff_X_pow_mul',
    if_neg (by decide), sub_zero]

private lemma gOf3_coeff_eq_of_strict_prefix {H₁ H₂ : PowerSeries (ZMod 3)} {n : ℕ}
    (h : ∀ j < n, H₁.coeff j = H₂.coeff j) :
    ∀ j ≤ n, (gOf3 H₁).coeff j = (gOf3 H₂).coeff j := by
  intro j hj
  unfold gOf3
  rw [map_sub, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  congr 1
  split_ifs with hle
  · have hd : ∀ i ≤ j - 3, (derivPS3 H₁).coeff i = (derivPS3 H₂).coeff i := by
      intro i hi
      unfold derivPS3
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, h (i + 1) (by omega)]
    exact coeff_pow_eq_of_prefix hd 2 (j - 3) le_rfl
  · rfl

private lemma map3_satisfies {A : PowerSeries ℤ} (hA : SatisfiesA361047 A) :
    let H := PowerSeries.map (Int.castRingHom (ZMod 3)) A
    H.coeff 0 = 0 ∧ H.coeff 1 = 1 ∧ compPS3 H (gOf3 H) = PowerSeries.X := by
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 3) := PowerSeries.map (Int.castRingHom (ZMod 3))
  have hφX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X (Int.castRingHom (ZMod 3))
  have hderiv : φ (derivPS A) = derivPS3 (φ A) := by
    ext m
    rw [PowerSeries.coeff_map, derivPS, derivPS3, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      PowerSeries.coeff_map]
    simp
  have hg : φ (gOf A) = gOf3 (φ A) := by
    unfold gOf gOf3
    simp only [map_sub, map_mul, map_pow, hφX, hderiv]
  refine ⟨?_, ?_, ?_⟩
  · rw [PowerSeries.coeff_map, hA.1]; simp
  · rw [PowerSeries.coeff_map, hA.2.1]; simp
  · ext n
    have hcomp := congrArg (PowerSeries.coeff n) (congrArg φ hA.2.2)
    rw [hφX, PowerSeries.coeff_map] at hcomp
    unfold compPS at hcomp
    rw [PowerSeries.coeff_mk] at hcomp
    unfold compPS3
    rw [PowerSeries.coeff_mk]
    rw [← hcomp]
    simp only [Int.coe_castRingHom, Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [PowerSeries.coeff_map, ← hg, ← map_pow, PowerSeries.coeff_map]
    rfl

private lemma unique_mod3 {H₁ H₂ : PowerSeries (ZMod 3)}
    (h10 : H₁.coeff 0 = 0) (h11 : H₁.coeff 1 = 1) (h1 : compPS3 H₁ (gOf3 H₁) = PowerSeries.X)
    (h20 : H₂.coeff 0 = 0) (h21 : H₂.coeff 1 = 1) (h2 : compPS3 H₂ (gOf3 H₂) = PowerSeries.X) :
    H₁ = H₂ := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [h10, h20]
    | succ n' =>
      cases n' with
      | zero => rw [h11, h21]
      | succ n'' =>
        set n := n'' + 2
        have hc1 := congrArg (PowerSeries.coeff n) h1
        have hc2 := congrArg (PowerSeries.coeff n) h2
        unfold compPS3 at hc1 hc2
        rw [PowerSeries.coeff_mk, PowerSeries.coeff_X, if_neg (by omega),
          Finset.sum_range_succ, coeff_pow_self (gOf3_coeff_zero H₁), gOf3_coeff_one, one_pow, mul_one] at hc1
        rw [PowerSeries.coeff_mk, PowerSeries.coeff_X, if_neg (by omega),
          Finset.sum_range_succ, coeff_pow_self (gOf3_coeff_zero H₂), gOf3_coeff_one, one_pow, mul_one] at hc2
        have hg : ∀ j ≤ n, (gOf3 H₁).coeff j = (gOf3 H₂).coeff j :=
          gOf3_coeff_eq_of_strict_prefix ih
        have hsum : ∑ m ∈ Finset.range n, H₁.coeff m * ((gOf3 H₁) ^ m).coeff n =
            ∑ m ∈ Finset.range n, H₂.coeff m * ((gOf3 H₂) ^ m).coeff n := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mem_range] at hm
          rw [ih m hm, coeff_pow_eq_of_prefix hg m n le_rfl]
        rw [hsum] at hc1
        exact add_left_cancel (hc1.trans hc2.symm)

private lemma frobenius_sub_pow_three (F G : PowerSeries (ZMod 3)) :
    (F - G) ^ 3 = F ^ 3 - G ^ 3 := by
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    ext k
    rw [show (3 : PowerSeries (ZMod 3)) = PowerSeries.C (3 : ZMod 3) from rfl,
      PowerSeries.coeff_C, map_zero]
    split_ifs <;> decide
  linear_combination (-(F ^ 2 * G) + F * G ^ 2) * h3

private lemma frobenius_X_sub_X3_pow (k : ℕ) :
    ((PowerSeries.X - PowerSeries.X ^ 3 : PowerSeries (ZMod 3)) ^ (3 ^ k)) =
    PowerSeries.X ^ (3 ^ k) - PowerSeries.X ^ (3 ^ (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ 3 k, pow_mul, ih, frobenius_sub_pow_three, ← pow_mul, ← pow_mul,
      ← pow_succ, ← pow_succ]

open Classical in
private lemma target_mod3_satisfies :
    let F : PowerSeries (ZMod 3) := PowerSeries.mk fun r => if ∃ k : ℕ, r = 3 ^ k then 1 else 0
    F.coeff 0 = 0 ∧ F.coeff 1 = 1 ∧ compPS3 F (gOf3 F) = PowerSeries.X := by
  let F : PowerSeries (ZMod 3) := PowerSeries.mk fun r => if ∃ k : ℕ, r = 3 ^ k then 1 else 0
  have hF0 : F.coeff 0 = 0 := by
    simp only [F, PowerSeries.coeff_mk]
    rw [if_neg]
    rintro ⟨k, hk⟩
    have : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
    omega
  have hF1 : F.coeff 1 = 1 := by
    simp only [F, PowerSeries.coeff_mk]
    rw [if_pos ⟨0, by norm_num⟩]
  have hderivF : derivPS3 F = 1 := by
    ext m
    unfold derivPS3
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    cases m with
    | zero => rw [if_pos rfl, hF1]; simp
    | succ m' =>
      rw [if_neg (Nat.succ_ne_zero m')]
      simp only [F, PowerSeries.coeff_mk]
      split_ifs with hex
      · obtain ⟨k, hk⟩ := hex
        have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with rfl | hpos
          · norm_num at hk
          · omega
        have h3dvd : 3 ∣ (m' + 1 + 1) := by
          rw [hk, show k = (k - 1) + 1 by omega, pow_succ]
          exact dvd_mul_left 3 _
        have h0 : ((m' + 1 + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).mpr h3dvd
        rw [h0, zero_mul]
      · rw [mul_zero]
  have hgF : gOf3 F = PowerSeries.X - PowerSeries.X ^ 3 := by
    unfold gOf3
    rw [hderivF, one_pow, mul_one]
  refine ⟨hF0, hF1, ?_⟩
  rw [hgF]
  ext n
  unfold compPS3
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_X]
  -- Evaluate the sum over m ∈ range (n + 1): only m = 3^k contributes, and
  -- ((X - X^3)^(3^k)).coeff n = [n = 3^k] - [n = 3^(k+1)], which telescopes!
  have hpow_le : ∀ k : ℕ, n < 3 ^ (n + 1) := fun _ =>
    lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 3)))
  have hsum_eq : ∑ m ∈ Finset.range (n + 1),
      F.coeff m * ((PowerSeries.X - PowerSeries.X ^ 3 : PowerSeries (ZMod 3)) ^ m).coeff n =
      ∑ k ∈ Finset.range (n + 1),
        ((PowerSeries.X ^ (3 ^ k) : PowerSeries (ZMod 3)).coeff n -
         (PowerSeries.X ^ (3 ^ (k + 1)) : PowerSeries (ZMod 3)).coeff n) := by
    have hsplit : ∑ m ∈ Finset.range (n + 1),
        F.coeff m * ((PowerSeries.X - PowerSeries.X ^ 3 : PowerSeries (ZMod 3)) ^ m).coeff n =
        ∑ m ∈ (Finset.range (n + 1)).filter (fun m => ∃ k : ℕ, m = 3 ^ k),
          ((PowerSeries.X - PowerSeries.X ^ 3 : PowerSeries (ZMod 3)) ^ m).coeff n := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) (fun m => ∃ k : ℕ, m = 3 ^ k)]
      have h2 : ∑ m ∈ (Finset.range (n + 1)).filter (fun m => ¬ ∃ k : ℕ, m = 3 ^ k),
          F.coeff m * ((PowerSeries.X - PowerSeries.X ^ 3 : PowerSeries (ZMod 3)) ^ m).coeff n = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rw [Finset.mem_filter] at hm
        simp only [F, PowerSeries.coeff_mk, if_neg hm.2, zero_mul]
      rw [h2, add_zero]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_filter] at hm
      simp only [F, PowerSeries.coeff_mk, if_pos hm.2, one_mul]
    rw [hsplit]
    have hfilt_eq : ∑ k ∈ Finset.range (n + 1),
        ((PowerSeries.X ^ (3 ^ k) : PowerSeries (ZMod 3)).coeff n -
         (PowerSeries.X ^ (3 ^ (k + 1)) : PowerSeries (ZMod 3)).coeff n) =
        ∑ k ∈ (Finset.range (n + 1)).filter (fun k => 3 ^ k ≤ n),
          ((PowerSeries.X ^ (3 ^ k) : PowerSeries (ZMod 3)).coeff n -
           (PowerSeries.X ^ (3 ^ (k + 1)) : PowerSeries (ZMod 3)).coeff n) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hnot
      rw [Finset.mem_filter] at hnot
      have hgt : n < 3 ^ k := lt_of_not_ge (fun hle => hnot ⟨hk, hle⟩)
      have hgt2 : n < 3 ^ (k + 1) := by
        have : 3 ^ k ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      rw [PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow, if_neg (by omega), if_neg (by omega), sub_self]
    rw [hfilt_eq]
    symm
    apply Finset.sum_bij (fun k _ => 3 ^ k)
    · intro k hk
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨Finset.mem_range.mpr (by omega), ⟨k, rfl⟩⟩
    · intro a _ b _ heq
      exact Nat.pow_right_injective (by decide : 1 < 3) heq
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_range] at hm
      obtain ⟨k, rfl⟩ := hm.2
      have hkn : k < n + 1 := by
        have : k < 3 ^ k := Nat.lt_pow_self (by decide : 1 < 3)
        omega
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkn, by omega⟩, rfl⟩
    · intro k _
      rw [frobenius_X_sub_X3_pow k, map_sub]
  rw [hsum_eq]
  have htele : ∑ k ∈ Finset.range (n + 1),
      ((PowerSeries.X ^ (3 ^ k) : PowerSeries (ZMod 3)).coeff n -
       (PowerSeries.X ^ (3 ^ (k + 1)) : PowerSeries (ZMod 3)).coeff n) =
      (PowerSeries.X ^ (3 ^ 0) : PowerSeries (ZMod 3)).coeff n -
      (PowerSeries.X ^ (3 ^ (n + 1)) : PowerSeries (ZMod 3)).coeff n := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.sum_range_succ]
    ring
  have hne : n ≠ 3 ^ (n + 1) := by have := hpow_le 0; omega
  rw [htele, pow_zero, pow_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
    if_neg hne, sub_zero]

private lemma three_pow_mod_two (k : ℕ) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih => rw [pow_succ, Nat.mul_mod, ih]

private lemma zmod3_eq_iff_mod3 (z : ℤ) (c : ℤ) (hc0 : 0 ≤ c) (hc3 : c < 3) :
    (z : ZMod 3) = (c : ZMod 3) ↔ z % 3 = c := by
  constructor
  · intro h
    have h0 : ((z - c : ℤ) : ZMod 3) = 0 := by push_cast; rw [h, sub_self]
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (z - c) 3).mp h0
    omega
  · intro h
    have hd : (3 : ℤ) ∣ (z - c) := by omega
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (z - c) 3).mpr hd
    push_cast at h0
    exact sub_eq_zero.mp h0

open Classical in
theorem solve : type_of% @OMA.S_oeis_a361047.main := by
  refine ⟨exists_solution, fun A hA n => ?_⟩
  obtain ⟨hH0, hH1, hH⟩ := map3_satisfies hA
  obtain ⟨hF0, hF1, hF⟩ := target_mod3_satisfies
  have hEq : PowerSeries.map (Int.castRingHom (ZMod 3)) A =
      PowerSeries.mk fun r => if ∃ k : ℕ, r = 3 ^ k then (1 : ZMod 3) else 0 :=
    unique_mod3 hH0 hH1 hH hF0 hF1 hF
  have hcoeff := congrArg (PowerSeries.coeff (2 * n + 1)) hEq
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk] at hcoeff
  have hiff : (∃ k : ℕ, 2 * n + 1 = 3 ^ k) ↔ (∃ k : ℕ, n = (3 ^ k - 1) / 2) := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by omega⟩
    · rintro ⟨k, hk⟩
      have hodd : 3 ^ k % 2 = 1 := three_pow_mod_two k
      have hpos : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
      exact ⟨k, by omega⟩
  by_cases hex : ∃ k : ℕ, n = (3 ^ k - 1) / 2
  · rw [if_pos (hiff.mpr hex)] at hcoeff
    have hm1 : A.coeff (2 * n + 1) % 3 = 1 :=
      (zmod3_eq_iff_mod3 (A.coeff (2 * n + 1)) 1 (by omega) (by omega)).mp (by simpa using hcoeff)
    exact ⟨⟨fun _ => hex, fun _ => hm1⟩, fun hnot => (hnot hex).elim⟩
  · rw [if_neg (fun h => hex (hiff.mp h))] at hcoeff
    have hm0 : A.coeff (2 * n + 1) % 3 = 0 :=
      (zmod3_eq_iff_mod3 (A.coeff (2 * n + 1)) 0 (by omega) (by omega)).mp (by simpa using hcoeff)
    exact ⟨⟨fun hm1 => by omega, fun h => (hex h).elim⟩, fun _ => hm0⟩

end A361047Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a361047.main :=
  A361047Proof.solve
