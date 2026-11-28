import OMAStatements.S_oeis_a379204

/-!
Proof of both conjectures on OEIS A379204.

1. Existence: since `A.coeff (r + 1)` depends only on `A.coeff j` for `j ≤ r`, strong
   recursion defines `A` satisfying `SatisfiesA379204 A`.
2. Mod-4 reduction via `ψ : PowerSeries ℤ →+* PowerSeries (ZMod 4)`:
   - For `n ≥ 1`, `ψ (posTerm A n) = (ψ A) ^ ((n + 1) ^ 2)`.
   - For `m ≥ 2`, `ψ (invOneAdd (4 * A^m)) = 1`, so `ψ (negTerm A m) = (ψ A) ^ ((m - 1) ^ 2)`.
   - Pairing `n = k - 1` (`k ≥ 2`) with `m = k + 1` (`k ≥ 2`), plus `5 * A` with `negTerm A 2`
     (`m = 2`, `k = 1`), gives for every `r : ℕ`:
     `(A.coeff (r + 1) : ZMod 4) = (if r = 0 then 1 else 0) + 2 * ∑_{k=1}^{r} ((ψ A) ^ (k^2)).coeff r`.
   - Reducing mod 2 immediately gives `A.coeff 1 ≡ 1 (mod 2)` and `A.coeff (r + 1) ≡ 0 (mod 2)`
     for `r ≥ 1`, i.e., `A ≡ X (mod 2)`.
   - Hence `2 * ((ψ A) ^ (k^2)).coeff r = 2 * (X ^ (k^2)).coeff r` in `ZMod 4`, so for all `r ≥ 1`,
     `(A.coeff (r + 1) : ZMod 4) = 2` iff `r = k^2` for some `k ≥ 1`, else `0`.
-/

namespace A379204Proof

open Finset PowerSeries OMA.S_oeis_a379204

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

private lemma coeff_invOneAdd_eq_of_prefix {F G : PowerSeries ℤ} {n : ℕ}
    (h : ∀ j ≤ n, F.coeff j = G.coeff j) :
    ∀ k ≤ n, (invOneAdd F).coeff k = (invOneAdd G).coeff k := by
  intro k hk
  unfold invOneAdd
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro j _
  exact coeff_pow_eq_of_prefix (fun i hi => by simp [map_neg, h i hi]) j k hk

private lemma coeff_posTerm_eq_of_prefix {A B : PowerSeries ℤ} {r n : ℕ}
    (h : ∀ j ≤ r, A.coeff j = B.coeff j) :
    (posTerm A n).coeff r = (posTerm B n).coeff r := by
  unfold posTerm
  have h1 := coeff_pow_eq_of_prefix h (n + 1)
  have h2 : ∀ j ≤ r, (A ^ n + 4).coeff j = (B ^ n + 4).coeff j := by
    intro j hj; simp [map_add, coeff_pow_eq_of_prefix h n j hj]
  exact coeff_mul_eq_of_prefix h1 (coeff_pow_eq_of_prefix h2 (n + 1)) r le_rfl

private lemma coeff_negTerm_eq_of_prefix {A B : PowerSeries ℤ} {r m : ℕ}
    (h : ∀ j ≤ r, A.coeff j = B.coeff j) :
    (negTerm A m).coeff r = (negTerm B m).coeff r := by
  unfold negTerm
  have h1 := coeff_pow_eq_of_prefix h ((m - 1) ^ 2)
  have h4 : ∀ j ≤ r, ((4 : PowerSeries ℤ) * A ^ m).coeff j = ((4 : PowerSeries ℤ) * B ^ m).coeff j :=
    coeff_mul_eq_of_prefix (fun _ _ => rfl) (coeff_pow_eq_of_prefix h m)
  exact coeff_mul_eq_of_prefix h1 (coeff_pow_eq_of_prefix (coeff_invOneAdd_eq_of_prefix h4) (m - 1)) r le_rfl

private noncomputable def buildList : ℕ → List ℤ
  | 0 => []
  | k + 1 =>
    let L := buildList k
    let val : ℤ :=
      match k with
      | 0 => 0
      | r + 1 =>
        let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => L.getD j 0
        (if r = 0 then (1 : ℤ) else 0) + 5 * Aprev.coeff r +
          (∑ n ∈ Finset.Icc 1 r, (posTerm Aprev n).coeff r) +
          (∑ m ∈ Finset.Icc 2 (r + 1), (negTerm Aprev m).coeff r)
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

private lemma exists_solution : ∃ A : PowerSeries ℤ, SatisfiesA379204 A := by
  let A : PowerSeries ℤ := PowerSeries.mk buildSeq
  refine ⟨A, by rw [PowerSeries.coeff_mk]; exact buildSeq_zero, fun r => ?_⟩
  rw [PowerSeries.coeff_mk]
  unfold buildSeq
  have hlen : (buildList (r + 1)).length = r + 1 := buildList_length (r + 1)
  have hlast : (buildList (r + 2)).getD (r + 1) 0 =
      let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildList (r + 1)).getD j 0
      (if r = 0 then (1 : ℤ) else 0) + 5 * Aprev.coeff r +
        (∑ n ∈ Finset.Icc 1 r, (posTerm Aprev n).coeff r) +
        (∑ m ∈ Finset.Icc 2 (r + 1), (negTerm Aprev m).coeff r) := by
    conv_lhs => unfold buildList
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]), hlen,
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hlast]
  let Aprev : PowerSeries ℤ := PowerSeries.mk fun j => (buildList (r + 1)).getD j 0
  have hpre : ∀ j ≤ r, Aprev.coeff j = A.coeff j := by
    intro j hj
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    exact buildList_getD_of_lt (r + 1) j (by omega)
  change (if r = 0 then (1 : ℤ) else 0) + 5 * Aprev.coeff r +
      (∑ n ∈ Finset.Icc 1 r, (posTerm Aprev n).coeff r) +
      (∑ m ∈ Finset.Icc 2 (r + 1), (negTerm Aprev m).coeff r) = _
  rw [hpre r le_rfl]
  have hpos : ∑ n ∈ Finset.Icc 1 r, (posTerm Aprev n).coeff r =
      ∑ n ∈ Finset.Icc 1 r, (posTerm A n).coeff r :=
    Finset.sum_congr rfl fun n _ => coeff_posTerm_eq_of_prefix hpre
  have hneg : ∑ m ∈ Finset.Icc 2 (r + 1), (negTerm Aprev m).coeff r =
      ∑ m ∈ Finset.Icc 2 (r + 1), (negTerm A m).coeff r :=
    Finset.sum_congr rfl fun m _ => coeff_negTerm_eq_of_prefix hpre
  rw [hpos, hneg]

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

private lemma map4_posTerm (A : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod 4)) (posTerm A n) =
    (PowerSeries.map (Int.castRingHom (ZMod 4)) A) ^ ((n + 1) ^ 2) := by
  unfold posTerm
  simp only [map_mul, map_pow, map_add, map_ofNat]
  have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by ext k; rw [show (4 : PowerSeries (ZMod 4)) = PowerSeries.C (4 : ZMod 4) from rfl, PowerSeries.coeff_C, map_zero]; split_ifs <;> decide
  rw [h4, add_zero, ← pow_mul, ← pow_add]
  congr 1; ring

private lemma map4_invOneAdd_four_mul (F : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod 4)) (invOneAdd (4 * F)) = 1 := by
  ext k
  rw [PowerSeries.coeff_map, PowerSeries.coeff_one]
  unfold invOneAdd
  rw [PowerSeries.coeff_mk]
  simp only [Int.coe_castRingHom, Int.cast_sum]
  rw [Finset.sum_range_succ']
  have htail : ∑ j ∈ Finset.range k, ((((-(4 * F)) ^ (j + 1)).coeff k : ℤ) : ZMod 4) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hdvd : (4 : ℤ) ∣ ((-(4 * F)) ^ (j + 1)).coeff k := by
      have hfac : (-(4 * F)) ^ (j + 1) = PowerSeries.C (4 : ℤ) * ((-1 : PowerSeries ℤ) ^ (j + 1) * (4 : PowerSeries ℤ) ^ j * F ^ (j + 1)) := by
        have h4 : (4 : PowerSeries ℤ) = PowerSeries.C 4 := rfl
        rw [← h4, neg_eq_neg_one_mul, mul_pow, mul_pow, pow_succ']
        ring
      rw [hfac, PowerSeries.coeff_C_mul]
      exact dvd_mul_right 4 _
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hdvd
  rw [htail, zero_add, pow_zero, PowerSeries.coeff_one]
  split_ifs <;> simp

private lemma map4_negTerm (A : PowerSeries ℤ) (m : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod 4)) (negTerm A m) =
    (PowerSeries.map (Int.castRingHom (ZMod 4)) A) ^ ((m - 1) ^ 2) := by
  unfold negTerm
  simp only [map_mul, map_pow, map4_invOneAdd_four_mul, one_pow, mul_one]

private lemma coeff_mod4_formula {A : PowerSeries ℤ} (hA : SatisfiesA379204 A) (r : ℕ) :
    ((A.coeff (r + 1) : ℤ) : ZMod 4) =
      (if r = 0 then (1 : ZMod 4) else 0) +
      2 * ∑ k ∈ Finset.Icc 1 r,
        ((PowerSeries.map (Int.castRingHom (ZMod 4)) A) ^ (k ^ 2)).coeff r := by
  let ψ : PowerSeries ℤ →+* PowerSeries (ZMod 4) := PowerSeries.map (Int.castRingHom (ZMod 4))
  have hψ_coeff : ∀ (F : PowerSeries ℤ) (j : ℕ), ((F.coeff j : ℤ) : ZMod 4) = (ψ F).coeff j := by
    intro F j; exact (PowerSeries.coeff_map (Int.castRingHom (ZMod 4)) j F).symm
  have h := congrArg (fun z : ℤ => (z : ZMod 4)) (hA.2 r)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Int.cast_ofNat] at h
  rw [h]
  have hpos : ∑ n ∈ Finset.Icc 1 r, ((posTerm A n).coeff r : ZMod 4) =
      ∑ k ∈ Finset.Icc 2 (r + 1), ((ψ A) ^ (k ^ 2)).coeff r := by
    apply Finset.sum_bij (fun n _ => n + 1)
    · intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
    · intro a _ b _ heq; omega
    · intro k hk; rw [Finset.mem_Icc] at hk
      exact ⟨k - 1, Finset.mem_Icc.mpr (by omega), by omega⟩
    · intro n _
      rw [hψ_coeff, map4_posTerm]
  have hneg : ∑ m ∈ Finset.Icc 2 (r + 1), ((negTerm A m).coeff r : ZMod 4) =
      ∑ k ∈ Finset.Icc 1 r, ((ψ A) ^ (k ^ 2)).coeff r := by
    apply Finset.sum_bij (fun m _ => m - 1)
    · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
    · intro a ha b hb heq; rw [Finset.mem_Icc] at ha hb; omega
    · intro k hk; rw [Finset.mem_Icc] at hk
      exact ⟨k + 1, Finset.mem_Icc.mpr (by omega), by omega⟩
    · intro m _
      rw [hψ_coeff, map4_negTerm]
  rw [hpos, hneg]
  cases r with
  | zero =>
    have h0 : (ψ A).coeff 0 = 0 := by rw [← hψ_coeff, hA.1]; simp
    have h1 : Finset.Icc 1 0 = ∅ := by decide
    have h2 : Finset.Icc 2 1 = ∅ := by decide
    rw [h1, h2, Finset.sum_empty, hψ_coeff, h0]
    simp
  | succ r' =>
    set r := r' + 1
    have htop : ((ψ A) ^ ((r + 1) ^ 2)).coeff r = 0 := by
      have hlt : r < (r + 1) ^ 2 := by nlinarith
      rw [← map_pow, ← hψ_coeff, coeff_pow_eq_zero_of_lt hA.1 ((r + 1) ^ 2) r hlt]
      simp
    have hsplit_pos : Finset.Icc 2 (r + 1) = insert (r + 1) (Finset.Icc 2 r) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot_top : r + 1 ∉ Finset.Icc 2 r := by simp only [Finset.mem_Icc]; omega
    rw [hsplit_pos, Finset.sum_insert hnot_top, htop, zero_add]
    have hsplit_neg : Finset.Icc 1 r = insert 1 (Finset.Icc 2 r) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot_one : 1 ∉ Finset.Icc 2 r := by simp only [Finset.mem_Icc]; omega
    rw [hsplit_neg, Finset.sum_insert hnot_one, one_pow, pow_one, hψ_coeff]
    have h5 : (5 : ZMod 4) = 1 := by decide
    rw [h5, one_mul]
    ring

private lemma coeff_even {A : PowerSeries ℤ} (hA : SatisfiesA379204 A) :
    ∀ n : ℕ, 1 < n → Even (A.coeff n) := by
  intro n hn
  have h := coeff_mod4_formula hA (n - 1)
  rw [show n - 1 + 1 = n by omega, if_neg (by omega), zero_add] at h
  have h2dvd : (2 : ℤ) ∣ A.coeff n := by
    have hmod2 : ((A.coeff n : ℤ) : ZMod 2) = 0 := by
      have hcast := congrArg (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) h
      simp only [map_intCast, map_mul, map_ofNat] at hcast
      have h20 : (2 : ZMod 2) = 0 := by decide
      rw [h20, zero_mul] at hcast
      exact hcast
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hmod2
  obtain ⟨q, hq⟩ := h2dvd
  exact ⟨q, by omega⟩

private lemma coeff_mod4_char {A : PowerSeries ℤ} (hA : SatisfiesA379204 A) :
    ∀ n : ℕ, 1 ≤ n → (A.coeff n % 4 = 2 ↔ ∃ k : ℕ, 1 < k ∧ n = (k - 1) ^ 2 + 1) := by
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have hA1_odd : ((A.coeff 1 : ℤ) : ZMod 2) = 1 := by
    have h := coeff_mod4_formula hA 0
    have h1 : Finset.Icc 1 0 = ∅ := by decide
    rw [h1, Finset.sum_empty, mul_zero, add_zero, if_pos rfl] at h
    have hc := congrArg (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) h
    simpa using hc
  have hφA : φ A = PowerSeries.X := by
    ext j
    rw [PowerSeries.coeff_map, PowerSeries.coeff_X]
    cases j with
    | zero => rw [if_neg (by decide), hA.1]; simp
    | succ j' =>
      cases j' with
      | zero => rw [if_pos rfl]; exact hA1_odd
      | succ j'' =>
        rw [if_neg (by omega)]
        obtain ⟨q, hq⟩ := coeff_even hA (j'' + 2) (by omega)
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr ⟨q, by rw [show j'' + 1 + 1 = j'' + 2 by omega, hq]; ring⟩
  have h2mul : ∀ (k r : ℕ),
      (2 : ZMod 4) * ((PowerSeries.map (Int.castRingHom (ZMod 4)) A) ^ (k ^ 2)).coeff r =
      (2 : ZMod 4) * (if r = k ^ 2 then 1 else 0) := by
    intro k r
    have hcoeff_mod2 : (((A ^ (k ^ 2)).coeff r : ℤ) : ZMod 2) = if r = k ^ 2 then 1 else 0 := by
      have h1 : (φ (A ^ (k ^ 2))).coeff r = ((PowerSeries.X : PowerSeries (ZMod 2)) ^ (k ^ 2)).coeff r := by
        rw [map_pow, hφA]
      rw [PowerSeries.coeff_map, PowerSeries.coeff_X_pow] at h1
      exact h1
    have hcast4 : ((PowerSeries.map (Int.castRingHom (ZMod 4)) A) ^ (k ^ 2)).coeff r =
        (((A ^ (k ^ 2)).coeff r : ℤ) : ZMod 4) := by
      rw [← map_pow, PowerSeries.coeff_map]; rfl
    rw [hcast4]
    set z := (A ^ (k ^ 2)).coeff r
    by_cases heq : r = k ^ 2
    · rw [if_pos heq] at hcoeff_mod2 ⊢
      have hodd : z % 2 = 1 := by
        have h0 : ((z - 1 : ℤ) : ZMod 2) = 0 := by push_cast; rw [hcoeff_mod2, sub_self]
        have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (z - 1) 2).mp h0
        omega
      have hd4 : (4 : ℤ) ∣ (2 * z - 2) := by omega
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * z - 2) 4).mpr hd4
      push_cast at h0
      rw [mul_one]
      exact sub_eq_zero.mp h0
    · rw [if_neg heq] at hcoeff_mod2 ⊢
      have hev : (2 : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp hcoeff_mod2
      have hd4 : (4 : ℤ) ∣ 2 * z := by obtain ⟨q, hq⟩ := hev; exact ⟨q, by omega⟩
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * z) 4).mpr hd4
      push_cast at h0
      rw [mul_zero]; exact h0
  intro n hn
  cases n with
  | zero => omega
  | succ r =>
    have h4 := coeff_mod4_formula hA r
    rw [Finset.mul_sum] at h4
    have hsum : ∑ k ∈ Finset.Icc 1 r,
        (2 : ZMod 4) * ((PowerSeries.map (Int.castRingHom (ZMod 4)) A) ^ (k ^ 2)).coeff r =
        if 1 ≤ r ∧ IsSquare r then (2 : ZMod 4) else 0 := by
      rw [Finset.sum_congr rfl (fun k _ => h2mul k r)]
      by_cases hcond : 1 ≤ r ∧ IsSquare r
      · rw [if_pos hcond]
        obtain ⟨hr1, ⟨s, hs⟩⟩ := hcond
        have hs1 : 1 ≤ s := by nlinarith
        have hsr : s ≤ r := by nlinarith
        rw [Finset.sum_eq_single s]
        · rw [if_pos (by rw [hs, sq]), mul_one]
        · intro k _ hks
          rw [if_neg, mul_zero]
          intro heq
          have : k * k = s * s := by rw [← sq, ← heq, hs]
          rcases lt_trichotomy k s with hlt | heq' | hgt
          · nlinarith
          · exact hks heq'
          · nlinarith
        · intro hnot; exact (hnot (Finset.mem_Icc.mpr ⟨hs1, hsr⟩)).elim
      · rw [if_neg hcond]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_Icc] at hk
        rw [if_neg, mul_zero]
        intro heq
        exact hcond ⟨by omega, ⟨k, by rw [heq, sq]⟩⟩
    rw [hsum] at h4
    have hZ4 : ∀ (z : ℤ) (c : ℤ), 0 ≤ c → c < 4 → ((z : ZMod 4) = (c : ZMod 4) ↔ z % 4 = c) := by
      intro z c hc0 hc4
      constructor
      · intro heq
        have h0 : ((z - c : ℤ) : ZMod 4) = 0 := by push_cast; rw [heq, sub_self]
        have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (z - c) 4).mp h0
        omega
      · intro hmod
        have hd : (4 : ℤ) ∣ (z - c) := by omega
        have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (z - c) 4).mpr hd
        push_cast at h0
        exact sub_eq_zero.mp h0
    cases r with
    | zero =>
      have h0not : ¬ (1 ≤ (0 : ℕ) ∧ IsSquare (0 : ℕ)) := fun h => absurd h.1 (by decide)
      simp only [↓reduceIte, h0not, add_zero] at h4
      have hm1 : A.coeff 1 % 4 = 1 := (hZ4 (A.coeff 1) 1 (by omega) (by omega)).mp (by simpa using h4)
      constructor
      · intro hm2; simp only [zero_add] at hm2; exfalso; omega
      · rintro ⟨k, hk1, hk2⟩
        have hkm1 : 1 ≤ k - 1 := by omega
        have hsq1 : 1 ≤ (k - 1) ^ 2 := by nlinarith
        omega
    | succ r' =>
      set r := r' + 1
      rw [if_neg (Nat.succ_ne_zero r'), zero_add] at h4
      by_cases hsq : IsSquare r
      · rw [if_pos ⟨by omega, hsq⟩] at h4
        have hm2 : A.coeff (r + 1) % 4 = 2 :=
          (hZ4 (A.coeff (r + 1)) 2 (by omega) (by omega)).mp (by simpa using h4)
        obtain ⟨s, hs⟩ := hsq
        have hr1 : 1 ≤ r := by omega
        have hs1 : 1 ≤ s := by nlinarith
        exact ⟨fun _ => ⟨s + 1, by omega, by simp [hs, sq]⟩, fun _ => hm2⟩
      · rw [if_neg (fun h => hsq h.2)] at h4
        have hm0 : A.coeff (r + 1) % 4 = 0 :=
          (hZ4 (A.coeff (r + 1)) 0 (by omega) (by omega)).mp (by simpa using h4)
        constructor
        · intro hm2; omega
        · rintro ⟨k, hk1, hk2⟩
          exact (hsq ⟨k - 1, by rw [← sq]; omega⟩).elim

theorem solve : type_of% @OMA.S_oeis_a379204.main :=
  ⟨exists_solution, fun _ hA => ⟨coeff_even hA, coeff_mod4_char hA⟩⟩

end A379204Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a379204.main :=
  A379204Proof.solve
