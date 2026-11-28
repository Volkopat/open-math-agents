import OMAStatements.S_oeis_a202334

namespace OMA.P_oeis_a202334

open OMA.S_oeis_a202334

private instance (b0 b1 b2 : Fin 2) : Decidable (win2Ok b0 b1 b2) := by
  unfold win2Ok; infer_instance

private def rowCode (i : Fin 10) : ℕ :=
  match i.1 with
  | 0 => 0
  | 1 => 64
  | 2 => 128
  | 3 => 192
  | 4 => 224
  | 5 => 240
  | 6 => 248
  | 7 => 252
  | 8 => 254
  | 9 => 255
  | _ => 0

private def bitsOf (m : ℕ) (c : Fin 8) : Fin 2 :=
  ⟨(m / 2 ^ c.1) % 2, Nat.mod_lt _ (by omega)⟩

private def rowBit (i : Fin 10) (c : Fin 8) : Fin 2 :=
  bitsOf (rowCode i) c

private def encodeRow (r : Fin 8 → Fin 2) : ℕ :=
  (r 0).1 + 2 * (r 1).1 + 4 * (r 2).1 + 8 * (r 3).1 + 16 * (r 4).1 + 32 * (r 5).1 + 64 * (r 6).1 + 128 * (r 7).1

private def codeToIdx (m : ℕ) : Fin 10 :=
  match m with
  | 0 => 0
  | 64 => 1
  | 128 => 2
  | 192 => 3
  | 224 => 4
  | 240 => 5
  | 248 => 6
  | 252 => 7
  | 254 => 8
  | 255 => 9
  | _ => 0

private def rowValid (r : Fin 8 → Fin 2) : Prop :=
  ∀ c : Fin 6, win2Ok (r ⟨c.1, by omega⟩) (r ⟨c.1 + 1, by omega⟩) (r ⟨c.1 + 2, by omega⟩)

private instance (r : Fin 8 → Fin 2) : Decidable (rowValid r) := by
  unfold rowValid win2Ok; infer_instance

private lemma rowBit_valid (i : Fin 10) : rowValid (rowBit i) := by
  revert i; decide

private lemma codeToIdx_encodeRow (i : Fin 10) : codeToIdx (encodeRow (rowBit i)) = i := by
  revert i; decide

private lemma encodeRow_lt (r : Fin 8 → Fin 2) : encodeRow r < 256 := by
  unfold encodeRow
  have : ∀ c : Fin 8, (r c).1 < 2 := fun c => (r c).2
  have h0 := this 0 ; have h1 := this 1 ; have h2 := this 2 ; have h3 := this 3 ; have h4 := this 4 ; have h5 := this 5 ; have h6 := this 6 ; have h7 := this 7
  omega

private lemma bitsOf_encodeRow (r : Fin 8 → Fin 2) : bitsOf (encodeRow r) = r := by
  funext c; apply Fin.ext; unfold bitsOf encodeRow
  have : ∀ j : Fin 8, (r j).1 < 2 := fun j => (r j).2
  have h0 := this 0 ; have h1 := this 1 ; have h2 := this 2 ; have h3 := this 3 ; have h4 := this 4 ; have h5 := this 5 ; have h6 := this 6 ; have h7 := this 7
  fin_cases c <;> dsimp <;> omega

private lemma rowBit_codeToIdx (r : Fin 8 → Fin 2) (hr : rowValid r) :
    rowBit (codeToIdx (encodeRow r)) = r := by
  have hall : ∀ (a : Fin 16) (b : Fin 16),
      rowValid (bitsOf (a.1 + 16 * b.1)) →
      rowBit (codeToIdx (a.1 + 16 * b.1)) = bitsOf (a.1 + 16 * b.1) := by
    decide
  have hlt := encodeRow_lt r
  let a : Fin 16 := ⟨encodeRow r % 16, Nat.mod_lt _ (by omega)⟩
  let b : Fin 16 := ⟨encodeRow r / 16, by omega⟩
  have hab : a.1 + 16 * b.1 = encodeRow r := by dsimp [a, b]; omega
  have h1 := hall a b (by rw [hab, bitsOf_encodeRow]; exact hr)
  rw [hab, bitsOf_encodeRow] at h1
  exact h1

private def rowEquiv : {r : Fin 8 → Fin 2 // rowValid r} ≃ Fin 10 where
  toFun r := codeToIdx (encodeRow r.1)
  invFun i := ⟨rowBit i, rowBit_valid i⟩
  left_inv r := Subtype.ext (rowBit_codeToIdx r.1 r.2)
  right_inv i := codeToIdx_encodeRow i

private def colOk (i j k : Fin 10) : Bool :=
  (rowCode i &&& ((rowCode j ^^^ 255) ||| (rowCode k ^^^ 255))) == 0

private lemma colOk_iff (i j k : Fin 10) :
    colOk i j k = true ↔ ∀ c : Fin 8, win2Ok (rowBit i c) (rowBit j c) (rowBit k c) := by
  revert j k; fin_cases i <;> decide

private def dp : ℕ → Fin 10 → Fin 10 → ℕ
  | 0, _, _ => 1
  | n + 1, j, k => ∑ i : Fin 10, if colOk i j k = true then dp n i j else 0

private lemma dp_succ_eq (n : ℕ) (j k : Fin 10) :
    dp (n + 1) j k = ∑ i : Fin 10, if colOk i j k = true then dp n i j else 0 := rfl

private def tbl_0 (j k : Fin 10) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 2 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 3 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 4 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 5 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 6 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 7 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 8 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 9 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | _ => 0

private def tbl_1 (j k : Fin 10) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 2, 1, 2, 2, 2, 2, 2, 2, 2].getD k.1 0
  | 2 => #[1, 1, 2, 2, 2, 2, 2, 2, 2, 2].getD k.1 0
  | 3 => #[1, 2, 2, 4, 4, 4, 4, 4, 4, 4].getD k.1 0
  | 4 => #[1, 2, 2, 4, 5, 5, 5, 5, 5, 5].getD k.1 0
  | 5 => #[1, 2, 2, 4, 5, 6, 6, 6, 6, 6].getD k.1 0
  | 6 => #[1, 2, 2, 4, 5, 6, 7, 7, 7, 7].getD k.1 0
  | 7 => #[1, 2, 2, 4, 5, 6, 7, 8, 8, 8].getD k.1 0
  | 8 => #[1, 2, 2, 4, 5, 6, 7, 8, 9, 9].getD k.1 0
  | 9 => #[1, 2, 2, 4, 5, 6, 7, 8, 9, 10].getD k.1 0
  | _ => 0

private def tbl_2 (j k : Fin 10) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 3, 1, 3, 3, 3, 3, 3, 3, 3].getD k.1 0
  | 2 => #[1, 1, 3, 3, 3, 3, 3, 3, 3, 3].getD k.1 0
  | 3 => #[1, 3, 3, 9, 9, 9, 9, 9, 9, 9].getD k.1 0
  | 4 => #[1, 3, 3, 9, 14, 14, 14, 14, 14, 14].getD k.1 0
  | 5 => #[1, 3, 3, 9, 14, 20, 20, 20, 20, 20].getD k.1 0
  | 6 => #[1, 3, 3, 9, 14, 20, 27, 27, 27, 27].getD k.1 0
  | 7 => #[1, 3, 3, 9, 14, 20, 27, 35, 35, 35].getD k.1 0
  | 8 => #[1, 3, 3, 9, 14, 20, 27, 35, 44, 44].getD k.1 0
  | 9 => #[1, 3, 3, 9, 14, 20, 27, 35, 44, 54].getD k.1 0
  | _ => 0

private def tbl_3 (j k : Fin 10) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 4, 1, 4, 4, 4, 4, 4, 4, 4].getD k.1 0
  | 2 => #[1, 1, 4, 4, 4, 4, 4, 4, 4, 4].getD k.1 0
  | 3 => #[1, 4, 4, 16, 16, 16, 16, 16, 16, 16].getD k.1 0
  | 4 => #[1, 4, 4, 16, 30, 30, 30, 30, 30, 30].getD k.1 0
  | 5 => #[1, 4, 4, 16, 30, 50, 50, 50, 50, 50].getD k.1 0
  | 6 => #[1, 4, 4, 16, 30, 50, 77, 77, 77, 77].getD k.1 0
  | 7 => #[1, 4, 4, 16, 30, 50, 77, 112, 112, 112].getD k.1 0
  | 8 => #[1, 4, 4, 16, 30, 50, 77, 112, 156, 156].getD k.1 0
  | 9 => #[1, 4, 4, 16, 30, 50, 77, 112, 156, 210].getD k.1 0
  | _ => 0

private def tbl_4 (j k : Fin 10) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 5, 1, 5, 5, 5, 5, 5, 5, 5].getD k.1 0
  | 2 => #[1, 1, 5, 5, 5, 5, 5, 5, 5, 5].getD k.1 0
  | 3 => #[1, 5, 5, 25, 25, 25, 25, 25, 25, 25].getD k.1 0
  | 4 => #[1, 5, 5, 25, 55, 55, 55, 55, 55, 55].getD k.1 0
  | 5 => #[1, 5, 5, 25, 55, 105, 105, 105, 105, 105].getD k.1 0
  | 6 => #[1, 5, 5, 25, 55, 105, 182, 182, 182, 182].getD k.1 0
  | 7 => #[1, 5, 5, 25, 55, 105, 182, 294, 294, 294].getD k.1 0
  | 8 => #[1, 5, 5, 25, 55, 105, 182, 294, 450, 450].getD k.1 0
  | 9 => #[1, 5, 5, 25, 55, 105, 182, 294, 450, 660].getD k.1 0
  | _ => 0

private def tbl_5 (j k : Fin 10) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 6, 1, 6, 6, 6, 6, 6, 6, 6].getD k.1 0
  | 2 => #[1, 1, 6, 6, 6, 6, 6, 6, 6, 6].getD k.1 0
  | 3 => #[1, 6, 6, 36, 36, 36, 36, 36, 36, 36].getD k.1 0
  | 4 => #[1, 6, 6, 36, 91, 91, 91, 91, 91, 91].getD k.1 0
  | 5 => #[1, 6, 6, 36, 91, 196, 196, 196, 196, 196].getD k.1 0
  | 6 => #[1, 6, 6, 36, 91, 196, 378, 378, 378, 378].getD k.1 0
  | 7 => #[1, 6, 6, 36, 91, 196, 378, 672, 672, 672].getD k.1 0
  | 8 => #[1, 6, 6, 36, 91, 196, 378, 672, 1122, 1122].getD k.1 0
  | 9 => #[1, 6, 6, 36, 91, 196, 378, 672, 1122, 1782].getD k.1 0
  | _ => 0

private def tbl_6 (j k : Fin 10) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 7, 1, 7, 7, 7, 7, 7, 7, 7].getD k.1 0
  | 2 => #[1, 1, 7, 7, 7, 7, 7, 7, 7, 7].getD k.1 0
  | 3 => #[1, 7, 7, 49, 49, 49, 49, 49, 49, 49].getD k.1 0
  | 4 => #[1, 7, 7, 49, 140, 140, 140, 140, 140, 140].getD k.1 0
  | 5 => #[1, 7, 7, 49, 140, 336, 336, 336, 336, 336].getD k.1 0
  | 6 => #[1, 7, 7, 49, 140, 336, 714, 714, 714, 714].getD k.1 0
  | 7 => #[1, 7, 7, 49, 140, 336, 714, 1386, 1386, 1386].getD k.1 0
  | 8 => #[1, 7, 7, 49, 140, 336, 714, 1386, 2508, 2508].getD k.1 0
  | 9 => #[1, 7, 7, 49, 140, 336, 714, 1386, 2508, 4290].getD k.1 0
  | _ => 0

private def tbl_7 (j k : Fin 10) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 8, 1, 8, 8, 8, 8, 8, 8, 8].getD k.1 0
  | 2 => #[1, 1, 8, 8, 8, 8, 8, 8, 8, 8].getD k.1 0
  | 3 => #[1, 8, 8, 64, 64, 64, 64, 64, 64, 64].getD k.1 0
  | 4 => #[1, 8, 8, 64, 204, 204, 204, 204, 204, 204].getD k.1 0
  | 5 => #[1, 8, 8, 64, 204, 540, 540, 540, 540, 540].getD k.1 0
  | 6 => #[1, 8, 8, 64, 204, 540, 1254, 1254, 1254, 1254].getD k.1 0
  | 7 => #[1, 8, 8, 64, 204, 540, 1254, 2640, 2640, 2640].getD k.1 0
  | 8 => #[1, 8, 8, 64, 204, 540, 1254, 2640, 5148, 5148].getD k.1 0
  | 9 => #[1, 8, 8, 64, 204, 540, 1254, 2640, 5148, 9438].getD k.1 0
  | _ => 0

private def tbl_8 (j k : Fin 10) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 9, 1, 9, 9, 9, 9, 9, 9, 9].getD k.1 0
  | 2 => #[1, 1, 9, 9, 9, 9, 9, 9, 9, 9].getD k.1 0
  | 3 => #[1, 9, 9, 81, 81, 81, 81, 81, 81, 81].getD k.1 0
  | 4 => #[1, 9, 9, 81, 285, 285, 285, 285, 285, 285].getD k.1 0
  | 5 => #[1, 9, 9, 81, 285, 825, 825, 825, 825, 825].getD k.1 0
  | 6 => #[1, 9, 9, 81, 285, 825, 2079, 2079, 2079, 2079].getD k.1 0
  | 7 => #[1, 9, 9, 81, 285, 825, 2079, 4719, 4719, 4719].getD k.1 0
  | 8 => #[1, 9, 9, 81, 285, 825, 2079, 4719, 9867, 9867].getD k.1 0
  | 9 => #[1, 9, 9, 81, 285, 825, 2079, 4719, 9867, 19305].getD k.1 0
  | _ => 0

private def tbl_9 (j k : Fin 10) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 10, 1, 10, 10, 10, 10, 10, 10, 10].getD k.1 0
  | 2 => #[1, 1, 10, 10, 10, 10, 10, 10, 10, 10].getD k.1 0
  | 3 => #[1, 10, 10, 100, 100, 100, 100, 100, 100, 100].getD k.1 0
  | 4 => #[1, 10, 10, 100, 385, 385, 385, 385, 385, 385].getD k.1 0
  | 5 => #[1, 10, 10, 100, 385, 1210, 1210, 1210, 1210, 1210].getD k.1 0
  | 6 => #[1, 10, 10, 100, 385, 1210, 3289, 3289, 3289, 3289].getD k.1 0
  | 7 => #[1, 10, 10, 100, 385, 1210, 3289, 8008, 8008, 8008].getD k.1 0
  | 8 => #[1, 10, 10, 100, 385, 1210, 3289, 8008, 17875, 17875].getD k.1 0
  | 9 => #[1, 10, 10, 100, 385, 1210, 3289, 8008, 17875, 37180].getD k.1 0
  | _ => 0

private lemma dp_eq_tbl_0 (j k : Fin 10) : dp 0 j k = tbl_0 j k := by
  revert j k; decide

private lemma dp_eq_tbl_1 (j k : Fin 10) : dp 1 j k = tbl_1 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 10, if colOk i j k = true then dp 0 i j else 0) =
      ∑ i : Fin 10, if colOk i j k = true then tbl_0 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_0]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_2 (j k : Fin 10) : dp 2 j k = tbl_2 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 10, if colOk i j k = true then dp 1 i j else 0) =
      ∑ i : Fin 10, if colOk i j k = true then tbl_1 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_1]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_3 (j k : Fin 10) : dp 3 j k = tbl_3 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 10, if colOk i j k = true then dp 2 i j else 0) =
      ∑ i : Fin 10, if colOk i j k = true then tbl_2 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_2]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_4 (j k : Fin 10) : dp 4 j k = tbl_4 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 10, if colOk i j k = true then dp 3 i j else 0) =
      ∑ i : Fin 10, if colOk i j k = true then tbl_3 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_3]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_5 (j k : Fin 10) : dp 5 j k = tbl_5 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 10, if colOk i j k = true then dp 4 i j else 0) =
      ∑ i : Fin 10, if colOk i j k = true then tbl_4 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_4]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_6 (j k : Fin 10) : dp 6 j k = tbl_6 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 10, if colOk i j k = true then dp 5 i j else 0) =
      ∑ i : Fin 10, if colOk i j k = true then tbl_5 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_5]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_7 (j k : Fin 10) : dp 7 j k = tbl_7 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 10, if colOk i j k = true then dp 6 i j else 0) =
      ∑ i : Fin 10, if colOk i j k = true then tbl_6 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_6]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_8 (j k : Fin 10) : dp 8 j k = tbl_8 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 10, if colOk i j k = true then dp 7 i j else 0) =
      ∑ i : Fin 10, if colOk i j k = true then tbl_7 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_7]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_9 (j k : Fin 10) : dp 9 j k = tbl_9 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 10, if colOk i j k = true then dp 8 i j else 0) =
      ∑ i : Fin 10, if colOk i j k = true then tbl_8 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_8]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_rec_base :
    ∀ j k : Fin 10, dp 9 j k + 36 * dp 7 j k + 126 * dp 5 j k + 84 * dp 3 j k + 9 * dp 1 j k = 9 * dp 8 j k + 84 * dp 6 j k + 126 * dp 4 j k + 36 * dp 2 j k + dp 0 j k := by
  intro j k
  rw [dp_eq_tbl_0, dp_eq_tbl_1, dp_eq_tbl_2, dp_eq_tbl_3, dp_eq_tbl_4, dp_eq_tbl_5, dp_eq_tbl_6, dp_eq_tbl_7, dp_eq_tbl_8, dp_eq_tbl_9]
  revert j k; decide

private lemma sum_lin (f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 : Fin 10 → ℕ) (g : Fin 10 → Bool)
    (h : ∀ i : Fin 10, f9 i + 36 * f7 i + 126 * f5 i + 84 * f3 i + 9 * f1 i = 9 * f8 i + 84 * f6 i + 126 * f4 i + 36 * f2 i + f0 i) :
    (∑ i : Fin 10, if g i = true then f9 i else 0) + 36 * (∑ i : Fin 10, if g i = true then f7 i else 0) + 126 * (∑ i : Fin 10, if g i = true then f5 i else 0) + 84 * (∑ i : Fin 10, if g i = true then f3 i else 0) + 9 * (∑ i : Fin 10, if g i = true then f1 i else 0) = 9 * (∑ i : Fin 10, if g i = true then f8 i else 0) + 84 * (∑ i : Fin 10, if g i = true then f6 i else 0) + 126 * (∑ i : Fin 10, if g i = true then f4 i else 0) + 36 * (∑ i : Fin 10, if g i = true then f2 i else 0) + (∑ i : Fin 10, if g i = true then f0 i else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  cases g i
  · simp
  · simp only [↓reduceIte]; exact h i

private lemma dp_rec (m : ℕ) :
    ∀ j k : Fin 10, dp (m + 9) j k + 36 * dp (m + 7) j k + 126 * dp (m + 5) j k + 84 * dp (m + 3) j k + 9 * dp (m + 1) j k = 9 * dp (m + 8) j k + 84 * dp (m + 6) j k + 126 * dp (m + 4) j k + 36 * dp (m + 2) j k + dp m j k := by
  induction m with
  | zero => exact dp_rec_base
  | succ m ih =>
    intro j k
    rw [dp_succ_eq (m + 9), dp_succ_eq (m + 8), dp_succ_eq (m + 7), dp_succ_eq (m + 6), dp_succ_eq (m + 5), dp_succ_eq (m + 4), dp_succ_eq (m + 3), dp_succ_eq (m + 2), dp_succ_eq (m + 1), dp_succ_eq m]
    exact sum_lin (fun i => dp (m + 9) i j) (fun i => dp (m + 8) i j) (fun i => dp (m + 7) i j) (fun i => dp (m + 6) i j) (fun i => dp (m + 5) i j) (fun i => dp (m + 4) i j) (fun i => dp (m + 3) i j) (fun i => dp (m + 2) i j) (fun i => dp (m + 1) i j) (fun i => dp m i j) (fun i => colOk i j k) (fun i => ih i j)

private abbrev ValidSeq (n : ℕ) (j k : Fin 10) :=
  {s : Fin (n + 2) → Fin 10 //
    (∀ r : Fin n, colOk (s ⟨r.1, by omega⟩) (s ⟨r.1 + 1, by omega⟩) (s ⟨r.1 + 2, by omega⟩) = true) ∧
    s ⟨n, by omega⟩ = j ∧ s ⟨n + 1, by omega⟩ = k}

private lemma card_ValidSeq (n : ℕ) :
    ∀ j k : Fin 10, Fintype.card (ValidSeq n j k) = dp n j k := by
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
    let φ : (Σ i : Fin 10, {t : ValidSeq n i j // colOk i j k = true}) → ValidSeq (n + 1) j k :=
      fun ⟨i, ⟨⟨t, ht, hti, htj⟩, hok⟩⟩ =>
        let s : Fin (n + 3) → Fin 10 := Fin.snoc t k
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
        have hfun : (Fin.snoc t1 k : Fin (n + 3) → Fin 10) = Fin.snoc t2 k := congrArg Subtype.val heq
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
    a (m + 1) = ∑ j : Fin 10, ∑ k : Fin 10, dp m j k := by
  unfold a; rw [if_neg (by omega)]
  let φ : (Σ j : Fin 10, Σ k : Fin 10, ValidSeq m j k) → {A : Fin (m + 2) → Fin 8 → Fin 2 // isValid (m + 1) A} :=
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
      let s : Fin (m + 2) → Fin 10 := fun r => rowEquiv ⟨A r, hA1 r⟩
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
    a (m + 10) + 36 * a (m + 8) + 126 * a (m + 6) + 84 * a (m + 4) + 9 * a (m + 2) = 9 * a (m + 9) + 84 * a (m + 7) + 126 * a (m + 5) + 36 * a (m + 3) + a (m + 1) := by
  rw [a_eq_sum_dp (m + 9), a_eq_sum_dp (m + 8), a_eq_sum_dp (m + 7), a_eq_sum_dp (m + 6), a_eq_sum_dp (m + 5), a_eq_sum_dp (m + 4), a_eq_sum_dp (m + 3), a_eq_sum_dp (m + 2), a_eq_sum_dp (m + 1), a_eq_sum_dp m]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  exact dp_rec m j k

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_val_1 : a 1 = 100 := by
  rw [a_eq_sum_dp 0]
  have h : (∑ j : Fin 10, ∑ k : Fin 10, dp 0 j k) = ∑ j : Fin 10, ∑ k : Fin 10, tbl_0 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_0 j k
  rw [h]; decide
private lemma a_val_2 : a 2 = 368 := by
  rw [a_eq_sum_dp 1]
  have h : (∑ j : Fin 10, ∑ k : Fin 10, dp 1 j k) = ∑ j : Fin 10, ∑ k : Fin 10, tbl_1 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_1 j k
  rw [h]; decide
private lemma a_val_3 : a 3 = 1112 := by
  rw [a_eq_sum_dp 2]
  have h : (∑ j : Fin 10, ∑ k : Fin 10, dp 2 j k) = ∑ j : Fin 10, ∑ k : Fin 10, tbl_2 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_2 j k
  rw [h]; decide
private lemma a_val_4 : a 4 = 2906 := by
  rw [a_eq_sum_dp 3]
  have h : (∑ j : Fin 10, ∑ k : Fin 10, dp 3 j k) = ∑ j : Fin 10, ∑ k : Fin 10, tbl_3 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_3 j k
  rw [h]; decide
private lemma a_val_5 : a 5 = 6800 := by
  rw [a_eq_sum_dp 4]
  have h : (∑ j : Fin 10, ∑ k : Fin 10, dp 4 j k) = ∑ j : Fin 10, ∑ k : Fin 10, tbl_4 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_4 j k
  rw [h]; decide
private lemma a_val_6 : a 6 = 14588 := by
  rw [a_eq_sum_dp 5]
  have h : (∑ j : Fin 10, ∑ k : Fin 10, dp 5 j k) = ∑ j : Fin 10, ∑ k : Fin 10, tbl_5 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_5 j k
  rw [h]; decide
private lemma a_val_7 : a 7 = 29174 := by
  rw [a_eq_sum_dp 6]
  have h : (∑ j : Fin 10, ∑ k : Fin 10, dp 6 j k) = ∑ j : Fin 10, ∑ k : Fin 10, tbl_6 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_6 j k
  rw [h]; decide
private lemma a_val_8 : a 8 = 55057 := by
  rw [a_eq_sum_dp 7]
  have h : (∑ j : Fin 10, ∑ k : Fin 10, dp 7 j k) = ∑ j : Fin 10, ∑ k : Fin 10, tbl_7 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_7 j k
  rw [h]; decide
private lemma a_val_9 : a 9 = 98958 := by
  rw [a_eq_sum_dp 8]
  have h : (∑ j : Fin 10, ∑ k : Fin 10, dp 8 j k) = ∑ j : Fin 10, ∑ k : Fin 10, tbl_8 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_8 j k
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

theorem solution : type_of% @OMA.S_oeis_a202334.main := by
  have hrec_d : ∀ n : ℕ, 9 < n →
      (a n : ℤ) = 9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ) - 126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ) + 36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + (a (n - 9) : ℤ) := by
    intro n hn
    have h := a_rec_d (n - 10)
    simp only [show n - 10 + 10 = n by omega, show n - 10 + 9 = n - 1 by omega, show n - 10 + 8 = n - 2 by omega, show n - 10 + 7 = n - 3 by omega, show n - 10 + 6 = n - 4 by omega, show n - 10 + 5 = n - 5 by omega, show n - 10 + 4 = n - 6 by omega, show n - 10 + 3 = n - 7 by omega, show n - 10 + 2 = n - 8 by omega, show n - 10 + 1 = n - 9 by omega] at h
    omega
  refine ⟨?_, hrec_d⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 9 = 1 - PowerSeries.C 9 * PowerSeries.X ^ 1 + PowerSeries.C 36 * PowerSeries.X ^ 2 - PowerSeries.C 84 * PowerSeries.X ^ 3 + PowerSeries.C 126 * PowerSeries.X ^ 4 - PowerSeries.C 126 * PowerSeries.X ^ 5 + PowerSeries.C 84 * PowerSeries.X ^ 6 - PowerSeries.C 36 * PowerSeries.X ^ 7 + PowerSeries.C 9 * PowerSeries.X ^ 8 - PowerSeries.X ^ 9 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X : PowerSeries ℚ) * (100 - 532 * PowerSeries.X + 1400 * PowerSeries.X ^ 2 - 2254 * PowerSeries.X ^ 3 + 2366 * PowerSeries.X ^ 4 - 1636 * PowerSeries.X ^ 5 + 722 * PowerSeries.X ^ 6 - 185 * PowerSeries.X ^ 7 + 21 * PowerSeries.X ^ 8) = PowerSeries.C 100 * PowerSeries.X ^ 1 - PowerSeries.C 532 * PowerSeries.X ^ 2 + PowerSeries.C 1400 * PowerSeries.X ^ 3 - PowerSeries.C 2254 * PowerSeries.X ^ 4 + PowerSeries.C 2366 * PowerSeries.X ^ 5 - PowerSeries.C 1636 * PowerSeries.X ^ 6 + PowerSeries.C 722 * PowerSeries.X ^ 7 - PowerSeries.C 185 * PowerSeries.X ^ 8 + PowerSeries.C 21 * PowerSeries.X ^ 9 := by
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
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]; try norm_num
  · simp [a_zero, a_val_1, a_val_2]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8]; try norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9]; try norm_num
  · have hgt : 9 < m + 10 := by omega
    have hr := hrec_d (m + 10) hgt
    have hrq : (a (m + 10) : ℚ) = 9 * (a (m + 9) : ℚ) - 36 * (a (m + 8) : ℚ) + 84 * (a (m + 7) : ℚ) - 126 * (a (m + 6) : ℚ) + 126 * (a (m + 5) : ℚ) - 84 * (a (m + 4) : ℚ) + 36 * (a (m + 3) : ℚ) - 9 * (a (m + 2) : ℚ) + (a (m + 1) : ℚ) := by
      exact_mod_cast hr
    simp only [show 1 ≤ m + 10 by omega, show 2 ≤ m + 10 by omega, show 3 ≤ m + 10 by omega, show 4 ≤ m + 10 by omega, show 5 ≤ m + 10 by omega, show 6 ≤ m + 10 by omega, show 7 ≤ m + 10 by omega, show 8 ≤ m + 10 by omega, show 9 ≤ m + 10 by omega, ↓reduceIte,
      show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega, show m + 10 - 9 = m + 1 by omega,
      show ¬(m + 10 = 1) by omega, show ¬(m + 10 = 2) by omega, show ¬(m + 10 = 3) by omega, show ¬(m + 10 = 4) by omega, show ¬(m + 10 = 5) by omega, show ¬(m + 10 = 6) by omega, show ¬(m + 10 = 7) by omega, show ¬(m + 10 = 8) by omega, show ¬(m + 10 = 9) by omega]
    linarith

end OMA.P_oeis_a202334

theorem OMA.solution : type_of% @OMA.S_oeis_a202334.main :=
  OMA.P_oeis_a202334.solution
