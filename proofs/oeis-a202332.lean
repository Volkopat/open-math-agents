import OMAStatements.S_oeis_a202332

namespace OMA.P_oeis_a202332

open OMA.S_oeis_a202332

private instance (b0 b1 b2 : Fin 2) : Decidable (win2Ok b0 b1 b2) := by
  unfold win2Ok; infer_instance

private def rowCode (i : Fin 8) : ℕ :=
  match i.1 with
  | 0 => 0
  | 1 => 16
  | 2 => 32
  | 3 => 48
  | 4 => 56
  | 5 => 60
  | 6 => 62
  | 7 => 63
  | _ => 0

private def bitsOf (m : ℕ) (c : Fin 6) : Fin 2 :=
  ⟨(m / 2 ^ c.1) % 2, Nat.mod_lt _ (by omega)⟩

private def rowBit (i : Fin 8) (c : Fin 6) : Fin 2 :=
  bitsOf (rowCode i) c

private def encodeRow (r : Fin 6 → Fin 2) : ℕ :=
  (r 0).1 + 2 * (r 1).1 + 4 * (r 2).1 + 8 * (r 3).1 + 16 * (r 4).1 + 32 * (r 5).1

private def codeToIdx (m : ℕ) : Fin 8 :=
  match m with
  | 0 => 0
  | 16 => 1
  | 32 => 2
  | 48 => 3
  | 56 => 4
  | 60 => 5
  | 62 => 6
  | 63 => 7
  | _ => 0

private def rowValid (r : Fin 6 → Fin 2) : Prop :=
  ∀ c : Fin 4, win2Ok (r ⟨c.1, by omega⟩) (r ⟨c.1 + 1, by omega⟩) (r ⟨c.1 + 2, by omega⟩)

private instance (r : Fin 6 → Fin 2) : Decidable (rowValid r) := by
  unfold rowValid win2Ok; infer_instance

private lemma rowBit_valid (i : Fin 8) : rowValid (rowBit i) := by
  revert i; decide

private lemma codeToIdx_encodeRow (i : Fin 8) : codeToIdx (encodeRow (rowBit i)) = i := by
  revert i; decide

private lemma encodeRow_lt (r : Fin 6 → Fin 2) : encodeRow r < 64 := by
  unfold encodeRow
  have : ∀ c : Fin 6, (r c).1 < 2 := fun c => (r c).2
  have h0 := this 0 ; have h1 := this 1 ; have h2 := this 2 ; have h3 := this 3 ; have h4 := this 4 ; have h5 := this 5
  omega

private lemma bitsOf_encodeRow (r : Fin 6 → Fin 2) : bitsOf (encodeRow r) = r := by
  funext c; apply Fin.ext; unfold bitsOf encodeRow
  have : ∀ j : Fin 6, (r j).1 < 2 := fun j => (r j).2
  have h0 := this 0 ; have h1 := this 1 ; have h2 := this 2 ; have h3 := this 3 ; have h4 := this 4 ; have h5 := this 5
  fin_cases c <;> dsimp <;> omega

private lemma rowBit_codeToIdx (r : Fin 6 → Fin 2) (hr : rowValid r) :
    rowBit (codeToIdx (encodeRow r)) = r := by
  have hall : ∀ (a : Fin 16) (b : Fin 4),
      rowValid (bitsOf (a.1 + 16 * b.1)) →
      rowBit (codeToIdx (a.1 + 16 * b.1)) = bitsOf (a.1 + 16 * b.1) := by
    decide
  have hlt := encodeRow_lt r
  let a : Fin 16 := ⟨encodeRow r % 16, Nat.mod_lt _ (by omega)⟩
  let b : Fin 4 := ⟨encodeRow r / 16, by omega⟩
  have hab : a.1 + 16 * b.1 = encodeRow r := by dsimp [a, b]; omega
  have h1 := hall a b (by rw [hab, bitsOf_encodeRow]; exact hr)
  rw [hab, bitsOf_encodeRow] at h1
  exact h1

private def rowEquiv : {r : Fin 6 → Fin 2 // rowValid r} ≃ Fin 8 where
  toFun r := codeToIdx (encodeRow r.1)
  invFun i := ⟨rowBit i, rowBit_valid i⟩
  left_inv r := Subtype.ext (rowBit_codeToIdx r.1 r.2)
  right_inv i := codeToIdx_encodeRow i

private def colOk (i j k : Fin 8) : Bool :=
  (rowCode i &&& ((rowCode j ^^^ 63) ||| (rowCode k ^^^ 63))) == 0

private lemma colOk_iff (i j k : Fin 8) :
    colOk i j k = true ↔ ∀ c : Fin 6, win2Ok (rowBit i c) (rowBit j c) (rowBit k c) := by
  revert j k; fin_cases i <;> decide

private def dp : ℕ → Fin 8 → Fin 8 → ℕ
  | 0, _, _ => 1
  | n + 1, j, k => ∑ i : Fin 8, if colOk i j k = true then dp n i j else 0

private lemma dp_succ_eq (n : ℕ) (j k : Fin 8) :
    dp (n + 1) j k = ∑ i : Fin 8, if colOk i j k = true then dp n i j else 0 := rfl

private def tbl_0 (j k : Fin 8) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 2 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 3 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 4 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 5 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 6 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 7 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | _ => 0

private def tbl_1 (j k : Fin 8) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 2, 1, 2, 2, 2, 2, 2].getD k.1 0
  | 2 => #[1, 1, 2, 2, 2, 2, 2, 2].getD k.1 0
  | 3 => #[1, 2, 2, 4, 4, 4, 4, 4].getD k.1 0
  | 4 => #[1, 2, 2, 4, 5, 5, 5, 5].getD k.1 0
  | 5 => #[1, 2, 2, 4, 5, 6, 6, 6].getD k.1 0
  | 6 => #[1, 2, 2, 4, 5, 6, 7, 7].getD k.1 0
  | 7 => #[1, 2, 2, 4, 5, 6, 7, 8].getD k.1 0
  | _ => 0

private def tbl_2 (j k : Fin 8) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 3, 1, 3, 3, 3, 3, 3].getD k.1 0
  | 2 => #[1, 1, 3, 3, 3, 3, 3, 3].getD k.1 0
  | 3 => #[1, 3, 3, 9, 9, 9, 9, 9].getD k.1 0
  | 4 => #[1, 3, 3, 9, 14, 14, 14, 14].getD k.1 0
  | 5 => #[1, 3, 3, 9, 14, 20, 20, 20].getD k.1 0
  | 6 => #[1, 3, 3, 9, 14, 20, 27, 27].getD k.1 0
  | 7 => #[1, 3, 3, 9, 14, 20, 27, 35].getD k.1 0
  | _ => 0

private def tbl_3 (j k : Fin 8) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 4, 1, 4, 4, 4, 4, 4].getD k.1 0
  | 2 => #[1, 1, 4, 4, 4, 4, 4, 4].getD k.1 0
  | 3 => #[1, 4, 4, 16, 16, 16, 16, 16].getD k.1 0
  | 4 => #[1, 4, 4, 16, 30, 30, 30, 30].getD k.1 0
  | 5 => #[1, 4, 4, 16, 30, 50, 50, 50].getD k.1 0
  | 6 => #[1, 4, 4, 16, 30, 50, 77, 77].getD k.1 0
  | 7 => #[1, 4, 4, 16, 30, 50, 77, 112].getD k.1 0
  | _ => 0

private def tbl_4 (j k : Fin 8) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 5, 1, 5, 5, 5, 5, 5].getD k.1 0
  | 2 => #[1, 1, 5, 5, 5, 5, 5, 5].getD k.1 0
  | 3 => #[1, 5, 5, 25, 25, 25, 25, 25].getD k.1 0
  | 4 => #[1, 5, 5, 25, 55, 55, 55, 55].getD k.1 0
  | 5 => #[1, 5, 5, 25, 55, 105, 105, 105].getD k.1 0
  | 6 => #[1, 5, 5, 25, 55, 105, 182, 182].getD k.1 0
  | 7 => #[1, 5, 5, 25, 55, 105, 182, 294].getD k.1 0
  | _ => 0

private def tbl_5 (j k : Fin 8) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 6, 1, 6, 6, 6, 6, 6].getD k.1 0
  | 2 => #[1, 1, 6, 6, 6, 6, 6, 6].getD k.1 0
  | 3 => #[1, 6, 6, 36, 36, 36, 36, 36].getD k.1 0
  | 4 => #[1, 6, 6, 36, 91, 91, 91, 91].getD k.1 0
  | 5 => #[1, 6, 6, 36, 91, 196, 196, 196].getD k.1 0
  | 6 => #[1, 6, 6, 36, 91, 196, 378, 378].getD k.1 0
  | 7 => #[1, 6, 6, 36, 91, 196, 378, 672].getD k.1 0
  | _ => 0

private def tbl_6 (j k : Fin 8) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 7, 1, 7, 7, 7, 7, 7].getD k.1 0
  | 2 => #[1, 1, 7, 7, 7, 7, 7, 7].getD k.1 0
  | 3 => #[1, 7, 7, 49, 49, 49, 49, 49].getD k.1 0
  | 4 => #[1, 7, 7, 49, 140, 140, 140, 140].getD k.1 0
  | 5 => #[1, 7, 7, 49, 140, 336, 336, 336].getD k.1 0
  | 6 => #[1, 7, 7, 49, 140, 336, 714, 714].getD k.1 0
  | 7 => #[1, 7, 7, 49, 140, 336, 714, 1386].getD k.1 0
  | _ => 0

private def tbl_7 (j k : Fin 8) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 8, 1, 8, 8, 8, 8, 8].getD k.1 0
  | 2 => #[1, 1, 8, 8, 8, 8, 8, 8].getD k.1 0
  | 3 => #[1, 8, 8, 64, 64, 64, 64, 64].getD k.1 0
  | 4 => #[1, 8, 8, 64, 204, 204, 204, 204].getD k.1 0
  | 5 => #[1, 8, 8, 64, 204, 540, 540, 540].getD k.1 0
  | 6 => #[1, 8, 8, 64, 204, 540, 1254, 1254].getD k.1 0
  | 7 => #[1, 8, 8, 64, 204, 540, 1254, 2640].getD k.1 0
  | _ => 0

private lemma dp_eq_tbl_0 (j k : Fin 8) : dp 0 j k = tbl_0 j k := by
  revert j k; decide

private lemma dp_eq_tbl_1 (j k : Fin 8) : dp 1 j k = tbl_1 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 8, if colOk i j k = true then dp 0 i j else 0) =
      ∑ i : Fin 8, if colOk i j k = true then tbl_0 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_0]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_2 (j k : Fin 8) : dp 2 j k = tbl_2 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 8, if colOk i j k = true then dp 1 i j else 0) =
      ∑ i : Fin 8, if colOk i j k = true then tbl_1 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_1]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_3 (j k : Fin 8) : dp 3 j k = tbl_3 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 8, if colOk i j k = true then dp 2 i j else 0) =
      ∑ i : Fin 8, if colOk i j k = true then tbl_2 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_2]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_4 (j k : Fin 8) : dp 4 j k = tbl_4 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 8, if colOk i j k = true then dp 3 i j else 0) =
      ∑ i : Fin 8, if colOk i j k = true then tbl_3 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_3]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_5 (j k : Fin 8) : dp 5 j k = tbl_5 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 8, if colOk i j k = true then dp 4 i j else 0) =
      ∑ i : Fin 8, if colOk i j k = true then tbl_4 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_4]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_6 (j k : Fin 8) : dp 6 j k = tbl_6 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 8, if colOk i j k = true then dp 5 i j else 0) =
      ∑ i : Fin 8, if colOk i j k = true then tbl_5 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_5]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_7 (j k : Fin 8) : dp 7 j k = tbl_7 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 8, if colOk i j k = true then dp 6 i j else 0) =
      ∑ i : Fin 8, if colOk i j k = true then tbl_6 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_6]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_rec_base :
    ∀ j k : Fin 8, dp 7 j k + 21 * dp 5 j k + 35 * dp 3 j k + 7 * dp 1 j k = 7 * dp 6 j k + 35 * dp 4 j k + 21 * dp 2 j k + dp 0 j k := by
  intro j k
  rw [dp_eq_tbl_0, dp_eq_tbl_1, dp_eq_tbl_2, dp_eq_tbl_3, dp_eq_tbl_4, dp_eq_tbl_5, dp_eq_tbl_6, dp_eq_tbl_7]
  revert j k; decide

private lemma sum_lin (f7 f6 f5 f4 f3 f2 f1 f0 : Fin 8 → ℕ) (g : Fin 8 → Bool)
    (h : ∀ i : Fin 8, f7 i + 21 * f5 i + 35 * f3 i + 7 * f1 i = 7 * f6 i + 35 * f4 i + 21 * f2 i + f0 i) :
    (∑ i : Fin 8, if g i = true then f7 i else 0) + 21 * (∑ i : Fin 8, if g i = true then f5 i else 0) + 35 * (∑ i : Fin 8, if g i = true then f3 i else 0) + 7 * (∑ i : Fin 8, if g i = true then f1 i else 0) = 7 * (∑ i : Fin 8, if g i = true then f6 i else 0) + 35 * (∑ i : Fin 8, if g i = true then f4 i else 0) + 21 * (∑ i : Fin 8, if g i = true then f2 i else 0) + (∑ i : Fin 8, if g i = true then f0 i else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  cases g i
  · simp
  · simp only [↓reduceIte]; exact h i

private lemma dp_rec (m : ℕ) :
    ∀ j k : Fin 8, dp (m + 7) j k + 21 * dp (m + 5) j k + 35 * dp (m + 3) j k + 7 * dp (m + 1) j k = 7 * dp (m + 6) j k + 35 * dp (m + 4) j k + 21 * dp (m + 2) j k + dp m j k := by
  induction m with
  | zero => exact dp_rec_base
  | succ m ih =>
    intro j k
    rw [dp_succ_eq (m + 7), dp_succ_eq (m + 6), dp_succ_eq (m + 5), dp_succ_eq (m + 4), dp_succ_eq (m + 3), dp_succ_eq (m + 2), dp_succ_eq (m + 1), dp_succ_eq m]
    exact sum_lin (fun i => dp (m + 7) i j) (fun i => dp (m + 6) i j) (fun i => dp (m + 5) i j) (fun i => dp (m + 4) i j) (fun i => dp (m + 3) i j) (fun i => dp (m + 2) i j) (fun i => dp (m + 1) i j) (fun i => dp m i j) (fun i => colOk i j k) (fun i => ih i j)

private abbrev ValidSeq (n : ℕ) (j k : Fin 8) :=
  {s : Fin (n + 2) → Fin 8 //
    (∀ r : Fin n, colOk (s ⟨r.1, by omega⟩) (s ⟨r.1 + 1, by omega⟩) (s ⟨r.1 + 2, by omega⟩) = true) ∧
    s ⟨n, by omega⟩ = j ∧ s ⟨n + 1, by omega⟩ = k}

private lemma card_ValidSeq (n : ℕ) :
    ∀ j k : Fin 8, Fintype.card (ValidSeq n j k) = dp n j k := by
  induction n with
  | zero =>
    intro j k
    simp only [dp]
    refine Fintype.card_eq_one_iff.mpr ⟨⟨fun r => if r.1 = 0 then j else k, fun r => r.elim0, rfl, rfl⟩, ?_⟩
    rintro ⟨s, _, hj, hk⟩
    apply Subtype.ext; funext r; fin_cases r
    · exact hj
    · exact hk
  | succ n ih =>
    intro j k
    rw [dp_succ_eq]
    let φ : (Σ i : Fin 8, {t : ValidSeq n i j // colOk i j k = true}) → ValidSeq (n + 1) j k :=
      fun ⟨i, ⟨⟨t, ht, hti, htj⟩, hok⟩⟩ =>
        let s : Fin (n + 3) → Fin 8 := Fin.snoc t k
        ⟨s, by
          intro r
          by_cases hr : r.1 < n
          · have h := ht ⟨r.1, hr⟩
            have e0 : s ⟨r.1, by omega⟩ = t ⟨r.1, by omega⟩ := by
              have : (⟨r.1, by omega⟩ : Fin (n + 3)) = (⟨r.1, by omega⟩ : Fin (n + 2)).castSucc := rfl
              rw [this]; simp only [s, Fin.snoc_castSucc]
            have e1 : s ⟨r.1 + 1, by omega⟩ = t ⟨r.1 + 1, by omega⟩ := by
              have : (⟨r.1 + 1, by omega⟩ : Fin (n + 3)) = (⟨r.1 + 1, by omega⟩ : Fin (n + 2)).castSucc := rfl
              rw [this]; simp only [s, Fin.snoc_castSucc]
            have e2 : s ⟨r.1 + 2, by omega⟩ = t ⟨r.1 + 2, by omega⟩ := by
              have : (⟨r.1 + 2, by omega⟩ : Fin (n + 3)) = (⟨r.1 + 2, by omega⟩ : Fin (n + 2)).castSucc := rfl
              rw [this]; simp only [s, Fin.snoc_castSucc]
            rw [e0, e1, e2]; exact h
          · have hreq : r.1 = n := by omega
            have e0 : s ⟨r.1, by omega⟩ = i := by
              have : (⟨r.1, by omega⟩ : Fin (n + 3)) = (⟨n, by omega⟩ : Fin (n + 2)).castSucc := by ext; simp [hreq]
              rw [this]; simp only [s, Fin.snoc_castSucc, hti]
            have e1 : s ⟨r.1 + 1, by omega⟩ = j := by
              have : (⟨r.1 + 1, by omega⟩ : Fin (n + 3)) = (⟨n + 1, by omega⟩ : Fin (n + 2)).castSucc := by ext; simp [hreq]
              rw [this]; simp only [s, Fin.snoc_castSucc, htj]
            have e2 : s ⟨r.1 + 2, by omega⟩ = k := by
              have : (⟨r.1 + 2, by omega⟩ : Fin (n + 3)) = Fin.last (n + 2) := by ext; simp [Fin.last, hreq]
              rw [this]; simp only [s, Fin.snoc_last]
            rw [e0, e1, e2]; exact hok,
          by
            have : (⟨n + 1, by omega⟩ : Fin (n + 3)) = (⟨n + 1, by omega⟩ : Fin (n + 2)).castSucc := rfl
            rw [this]; simp only [s, Fin.snoc_castSucc, htj],
          by
            have : (⟨n + 2, by omega⟩ : Fin (n + 3)) = Fin.last (n + 2) := rfl
            rw [this]; simp only [s, Fin.snoc_last]⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro ⟨i1, ⟨⟨t1, ht1, hi1, hj1⟩, hok1⟩⟩ ⟨i2, ⟨⟨t2, ht2, hi2, hj2⟩, hok2⟩⟩ heq
        have hfun : (Fin.snoc t1 k : Fin (n + 3) → Fin 8) = Fin.snoc t2 k := congrArg Subtype.val heq
        have ht_eq : t1 = t2 := by funext r; simpa using congrFun hfun r.castSucc
        subst ht_eq
        have hi_eq : i1 = i2 := hi1.symm.trans hi2
        subst hi_eq; rfl
      · rintro ⟨s, hs, hj, hk⟩
        let i := s ⟨n, by omega⟩
        let t : ValidSeq n i j := ⟨fun r => s r.castSucc, fun r => hs ⟨r.1, by omega⟩, rfl, hj⟩
        have hok : colOk i j k = true := by
          have h := hs (Fin.last n)
          have e0 : s ⟨(Fin.last n).1, by omega⟩ = i := rfl
          have e1 : s ⟨(Fin.last n).1 + 1, by omega⟩ = j := by simpa [Fin.last] using hj
          have e2 : s ⟨(Fin.last n).1 + 2, by omega⟩ = k := by simpa [Fin.last] using hk
          rw [e0, e1, e2] at h; exact h
        refine ⟨⟨i, ⟨t, hok⟩⟩, ?_⟩
        apply Subtype.ext; funext r; refine Fin.lastCases ?_ ?_ r
        · dsimp [φ, t]; rw [Fin.snoc_last]; exact hk.symm
        · intro r'; dsimp [φ, t]; rw [Fin.snoc_castSucc]
    rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
    apply Finset.sum_congr rfl; intro i _
    by_cases hok : colOk i j k = true
    · rw [if_pos hok, ← ih i j]
      refine Fintype.card_congr ⟨fun ⟨t, _⟩ => t, fun t => ⟨t, hok⟩, fun ⟨_, _⟩ => rfl, fun _ => rfl⟩
    · rw [if_neg hok, Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨_, h⟩ => hok h⟩

private lemma a_eq_sum_dp (m : ℕ) :
    a (m + 1) = ∑ j : Fin 8, ∑ k : Fin 8, dp m j k := by
  unfold a; rw [if_neg (by omega)]
  let φ : (Σ j : Fin 8, Σ k : Fin 8, ValidSeq m j k) → {A : Fin (m + 2) → Fin 6 → Fin 2 // isValid (m + 1) A} :=
    fun ⟨_, _, ⟨s, hs, _, _⟩⟩ =>
      ⟨fun r => rowBit (s r), fun r => rowBit_valid (s r), fun c r => (colOk_iff _ _ _).mp (hs r) c⟩
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨j1, k1, ⟨s1, hs1, hj1, hk1⟩⟩ ⟨j2, k2, ⟨s2, hs2, hj2, hk2⟩⟩ heq
      have hfun : (fun r => rowBit (s1 r)) = fun r => rowBit (s2 r) := congrArg Subtype.val heq
      have hs_eq : s1 = s2 := by
        funext r
        have := congrArg (fun x => codeToIdx (encodeRow x)) (congrFun hfun r)
        simpa [codeToIdx_encodeRow] using this
      subst hs_eq
      have hj_eq : j1 = j2 := hj1.symm.trans hj2
      have hk_eq : k1 = k2 := hk1.symm.trans hk2
      subst hj_eq; subst hk_eq; rfl
    · rintro ⟨A, hA1, hA2⟩
      let s : Fin (m + 2) → Fin 8 := fun r => rowEquiv ⟨A r, hA1 r⟩
      have hs : ∀ r : Fin m, colOk (s ⟨r.1, by omega⟩) (s ⟨r.1 + 1, by omega⟩) (s ⟨r.1 + 2, by omega⟩) = true := by
        intro r; rw [colOk_iff]; intro c
        have h0 : rowBit (s ⟨r.1, by omega⟩) = A ⟨r.1, by omega⟩ := congrArg Subtype.val (rowEquiv.left_inv ⟨A ⟨r.1, by omega⟩, hA1 _⟩)
        have h1 : rowBit (s ⟨r.1 + 1, by omega⟩) = A ⟨r.1 + 1, by omega⟩ := congrArg Subtype.val (rowEquiv.left_inv ⟨A ⟨r.1 + 1, by omega⟩, hA1 _⟩)
        have h2 : rowBit (s ⟨r.1 + 2, by omega⟩) = A ⟨r.1 + 2, by omega⟩ := congrArg Subtype.val (rowEquiv.left_inv ⟨A ⟨r.1 + 2, by omega⟩, hA1 _⟩)
        rw [h0, h1, h2]; exact hA2 c r
      refine ⟨⟨s ⟨m, by omega⟩, s ⟨m + 1, by omega⟩, ⟨s, hs, rfl, rfl⟩⟩, ?_⟩
      apply Subtype.ext; funext r
      exact congrArg Subtype.val (rowEquiv.left_inv ⟨A r, hA1 r⟩)
  rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro j _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro k _
  exact card_ValidSeq m j k

private lemma a_rec_d (m : ℕ) :
    a (m + 8) + 21 * a (m + 6) + 35 * a (m + 4) + 7 * a (m + 2) = 7 * a (m + 7) + 35 * a (m + 5) + 21 * a (m + 3) + a (m + 1) := by
  rw [a_eq_sum_dp (m + 7), a_eq_sum_dp (m + 6), a_eq_sum_dp (m + 5), a_eq_sum_dp (m + 4), a_eq_sum_dp (m + 3), a_eq_sum_dp (m + 2), a_eq_sum_dp (m + 1), a_eq_sum_dp m]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  exact dp_rec m j k

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_val_1 : a 1 = 64 := by
  rw [a_eq_sum_dp 0]
  have h : (∑ j : Fin 8, ∑ k : Fin 8, dp 0 j k) = ∑ j : Fin 8, ∑ k : Fin 8, tbl_0 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_0 j k
  rw [h]; decide
private lemma a_val_2 : a 2 = 191 := by
  rw [a_eq_sum_dp 1]
  have h : (∑ j : Fin 8, ∑ k : Fin 8, dp 1 j k) = ∑ j : Fin 8, ∑ k : Fin 8, tbl_1 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_1 j k
  rw [h]; decide
private lemma a_val_3 : a 3 = 478 := by
  rw [a_eq_sum_dp 2]
  have h : (∑ j : Fin 8, ∑ k : Fin 8, dp 2 j k) = ∑ j : Fin 8, ∑ k : Fin 8, tbl_2 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_2 j k
  rw [h]; decide
private lemma a_val_4 : a 4 = 1052 := by
  rw [a_eq_sum_dp 3]
  have h : (∑ j : Fin 8, ∑ k : Fin 8, dp 3 j k) = ∑ j : Fin 8, ∑ k : Fin 8, tbl_3 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_3 j k
  rw [h]; decide
private lemma a_val_5 : a 5 = 2102 := by
  rw [a_eq_sum_dp 4]
  have h : (∑ j : Fin 8, ∑ k : Fin 8, dp 4 j k) = ∑ j : Fin 8, ∑ k : Fin 8, tbl_4 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_4 j k
  rw [h]; decide
private lemma a_val_6 : a 6 = 3896 := by
  rw [a_eq_sum_dp 5]
  have h : (∑ j : Fin 8, ∑ k : Fin 8, dp 5 j k) = ∑ j : Fin 8, ∑ k : Fin 8, tbl_5 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_5 j k
  rw [h]; decide
private lemma a_val_7 : a 7 = 6800 := by
  rw [a_eq_sum_dp 6]
  have h : (∑ j : Fin 8, ∑ k : Fin 8, dp 6 j k) = ∑ j : Fin 8, ∑ k : Fin 8, tbl_6 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_6 j k
  rw [h]; decide

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ j * f) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, ih m]
      split_ifs with h1 h2
      · simp [Nat.succ_sub_succ]
      · omega
      · omega
      · rfl

private lemma coeff_mul_X_pow_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X ^ j) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  rw [mul_comm]; exact coeff_X_pow_mul_eq f j n

theorem solution : type_of% @OMA.S_oeis_a202332.main := by
  have hrec_d : ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ) := by
    intro n hn
    have h := a_rec_d (n - 8)
    simp only [show n - 8 + 8 = n by omega, show n - 8 + 7 = n - 1 by omega, show n - 8 + 6 = n - 2 by omega, show n - 8 + 5 = n - 3 by omega, show n - 8 + 4 = n - 4 by omega, show n - 8 + 3 = n - 5 by omega, show n - 8 + 2 = n - 6 by omega, show n - 8 + 1 = n - 7 by omega] at h
    omega
  refine ⟨?_, hrec_d⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 7 = 1 - PowerSeries.C 7 * PowerSeries.X ^ 1 + PowerSeries.C 21 * PowerSeries.X ^ 2 - PowerSeries.C 35 * PowerSeries.X ^ 3 + PowerSeries.C 35 * PowerSeries.X ^ 4 - PowerSeries.C 21 * PowerSeries.X ^ 5 + PowerSeries.C 7 * PowerSeries.X ^ 6 - PowerSeries.X ^ 7 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X : PowerSeries ℚ) * (64 - 257 * PowerSeries.X + 485 * PowerSeries.X ^ 2 - 523 * PowerSeries.X ^ 3 + 331 * PowerSeries.X ^ 4 - 115 * PowerSeries.X ^ 5 + 17 * PowerSeries.X ^ 6) = PowerSeries.C 64 * PowerSeries.X ^ 1 - PowerSeries.C 257 * PowerSeries.X ^ 2 + PowerSeries.C 485 * PowerSeries.X ^ 3 - PowerSeries.C 523 * PowerSeries.X ^ 4 + PowerSeries.C 331 * PowerSeries.X ^ 5 - PowerSeries.C 115 * PowerSeries.X ^ 6 + PowerSeries.C 17 * PowerSeries.X ^ 7 := by
    simp only [map_ofNat]; ring
  rw [hR]
  have hc : ∀ (c : ℚ) (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ j)) =
      c * if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro c j
    rw [mul_comm (PowerSeries.C c), ← mul_assoc, mul_comm _ (PowerSeries.C c),
        PowerSeries.coeff_C_mul, coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  have hX : ∀ (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * PowerSeries.X ^ j) =
      if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro j; rw [coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk, hc, hX,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]; try norm_num
  · simp [a_zero, a_val_1, a_val_2]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7]; try norm_num
  · have hgt : 7 < m + 8 := by omega
    have hr := hrec_d (m + 8) hgt
    have hrq : (a (m + 8) : ℚ) = 7 * (a (m + 7) : ℚ) - 21 * (a (m + 6) : ℚ) + 35 * (a (m + 5) : ℚ) - 35 * (a (m + 4) : ℚ) + 21 * (a (m + 3) : ℚ) - 7 * (a (m + 2) : ℚ) + (a (m + 1) : ℚ) := by
      exact_mod_cast hr
    simp only [show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega, show 3 ≤ m + 8 by omega, show 4 ≤ m + 8 by omega, show 5 ≤ m + 8 by omega, show 6 ≤ m + 8 by omega, show 7 ≤ m + 8 by omega, ↓reduceIte,
      show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega,
      show ¬(m + 8 = 1) by omega, show ¬(m + 8 = 2) by omega, show ¬(m + 8 = 3) by omega, show ¬(m + 8 = 4) by omega, show ¬(m + 8 = 5) by omega, show ¬(m + 8 = 6) by omega, show ¬(m + 8 = 7) by omega]
    linarith

end OMA.P_oeis_a202332

theorem OMA.solution : type_of% @OMA.S_oeis_a202332.main :=
  OMA.P_oeis_a202332.solution
