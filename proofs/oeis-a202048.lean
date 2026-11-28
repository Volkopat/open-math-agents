import OMAStatements.S_oeis_a202048

namespace OMA.P_oeis_a202048

open OMA.S_oeis_a202048

private instance (b0 b1 b2 : Fin 2) : Decidable (avoids3 b0 b1 b2) := by
  unfold avoids3; infer_instance

private def rowCode (i : Fin 12) : ℕ :=
  match i.1 with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 10
  | 5 => 21
  | 6 => 42
  | 7 => 53
  | 8 => 58
  | 9 => 61
  | 10 => 62
  | 11 => 63
  | _ => 0

private def bitsOf (m : ℕ) (c : Fin 6) : Fin 2 :=
  ⟨(m / 2 ^ c.1) % 2, Nat.mod_lt _ (by omega)⟩

private def rowBit (i : Fin 12) (c : Fin 6) : Fin 2 :=
  bitsOf (rowCode i) c

private def encodeRow (r : Fin 6 → Fin 2) : ℕ :=
  (r 0).1 + 2 * (r 1).1 + 4 * (r 2).1 + 8 * (r 3).1 + 16 * (r 4).1 + 32 * (r 5).1

private def codeToIdx (m : ℕ) : Fin 12 :=
  match m with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 5 => 3
  | 10 => 4
  | 21 => 5
  | 42 => 6
  | 53 => 7
  | 58 => 8
  | 61 => 9
  | 62 => 10
  | 63 => 11
  | _ => 0

private def rowValid (r : Fin 6 → Fin 2) : Prop :=
  ∀ c : Fin 4, avoids3 (r ⟨c.1, by omega⟩) (r ⟨c.1 + 1, by omega⟩) (r ⟨c.1 + 2, by omega⟩)

private instance (r : Fin 6 → Fin 2) : Decidable (rowValid r) := by
  unfold rowValid avoids3; infer_instance

private lemma rowBit_valid (i : Fin 12) : rowValid (rowBit i) := by
  revert i; decide

private lemma codeToIdx_encodeRow (i : Fin 12) : codeToIdx (encodeRow (rowBit i)) = i := by
  revert i; decide

private lemma encodeRow_lt (r : Fin 6 → Fin 2) : encodeRow r < 64 := by
  unfold encodeRow
  have : ∀ c : Fin 6, (r c).1 < 2 := fun c => (r c).2
  have h0 := this 0 ; have h1 := this 1 ; have h2 := this 2 ; have h3 := this 3 ; have h4 := this 4 ; have h5 := this 5
  omega

private lemma bitsOf_encodeRow (r : Fin 6 → Fin 2) : bitsOf (encodeRow r) = r := by
  funext c
  apply Fin.ext
  unfold bitsOf encodeRow
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

private def rowEquiv : {r : Fin 6 → Fin 2 // rowValid r} ≃ Fin 12 where
  toFun r := codeToIdx (encodeRow r.1)
  invFun i := ⟨rowBit i, rowBit_valid i⟩
  left_inv r := Subtype.ext (rowBit_codeToIdx r.1 r.2)
  right_inv i := codeToIdx_encodeRow i

private def colOk (i j k : Fin 12) : Bool :=
  ((rowCode i ^^^ rowCode j ^^^ 63) &&& (rowCode j ^^^ rowCode k)) == 0

private lemma colOk_iff (i j k : Fin 12) :
    colOk i j k = true ↔ ∀ c : Fin 6, avoids3 (rowBit i c) (rowBit j c) (rowBit k c) := by
  revert j k; fin_cases i <;> decide

private def dp : ℕ → Fin 12 → Fin 12 → ℕ
  | 0, _, _ => 1
  | n + 1, j, k => ∑ i : Fin 12, if colOk i j k = true then dp n i j else 0

private lemma dp_succ_eq (n : ℕ) (j k : Fin 12) :
    dp (n + 1) j k = ∑ i : Fin 12, if colOk i j k = true then dp n i j else 0 := rfl

private def tbl_0 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 2 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 3 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 4 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 5 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 6 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 7 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 8 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 9 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 10 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 11 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | _ => 0

private def tbl_1 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[12, 6, 6, 5, 5, 4, 4, 3, 3, 2, 2, 1].getD k.1 0
  | 1 => #[6, 12, 5, 6, 4, 5, 3, 4, 2, 3, 1, 2].getD k.1 0
  | 2 => #[6, 5, 12, 4, 6, 3, 5, 2, 4, 1, 3, 2].getD k.1 0
  | 3 => #[5, 6, 4, 12, 3, 6, 2, 5, 1, 4, 2, 3].getD k.1 0
  | 4 => #[5, 4, 6, 3, 12, 2, 6, 1, 5, 2, 4, 3].getD k.1 0
  | 5 => #[4, 5, 3, 6, 2, 12, 1, 6, 2, 5, 3, 4].getD k.1 0
  | 6 => #[4, 3, 5, 2, 6, 1, 12, 2, 6, 3, 5, 4].getD k.1 0
  | 7 => #[3, 4, 2, 5, 1, 6, 2, 12, 3, 6, 4, 5].getD k.1 0
  | 8 => #[3, 2, 4, 1, 5, 2, 6, 3, 12, 4, 6, 5].getD k.1 0
  | 9 => #[2, 3, 1, 4, 2, 5, 3, 6, 4, 12, 5, 6].getD k.1 0
  | 10 => #[2, 1, 3, 2, 4, 3, 5, 4, 6, 5, 12, 6].getD k.1 0
  | 11 => #[1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 12].getD k.1 0
  | _ => 0

private def tbl_2 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[53, 21, 21, 15, 15, 10, 10, 6, 6, 3, 3, 1].getD k.1 0
  | 1 => #[21, 53, 15, 21, 10, 15, 6, 10, 3, 6, 1, 3].getD k.1 0
  | 2 => #[21, 15, 53, 10, 21, 6, 15, 3, 10, 1, 6, 3].getD k.1 0
  | 3 => #[15, 21, 10, 53, 6, 21, 3, 15, 1, 10, 3, 6].getD k.1 0
  | 4 => #[15, 10, 21, 6, 53, 3, 21, 1, 15, 3, 10, 6].getD k.1 0
  | 5 => #[10, 15, 6, 21, 3, 53, 1, 21, 3, 15, 6, 10].getD k.1 0
  | 6 => #[10, 6, 15, 3, 21, 1, 53, 3, 21, 6, 15, 10].getD k.1 0
  | 7 => #[6, 10, 3, 15, 1, 21, 3, 53, 6, 21, 10, 15].getD k.1 0
  | 8 => #[6, 3, 10, 1, 15, 3, 21, 6, 53, 10, 21, 15].getD k.1 0
  | 9 => #[3, 6, 1, 10, 3, 15, 6, 21, 10, 53, 15, 21].getD k.1 0
  | 10 => #[3, 1, 6, 3, 10, 6, 15, 10, 21, 15, 53, 21].getD k.1 0
  | 11 => #[1, 3, 3, 6, 6, 10, 10, 15, 15, 21, 21, 53].getD k.1 0
  | _ => 0

private def tbl_3 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[164, 56, 56, 35, 35, 20, 20, 10, 10, 4, 4, 1].getD k.1 0
  | 1 => #[56, 164, 35, 56, 20, 35, 10, 20, 4, 10, 1, 4].getD k.1 0
  | 2 => #[56, 35, 164, 20, 56, 10, 35, 4, 20, 1, 10, 4].getD k.1 0
  | 3 => #[35, 56, 20, 164, 10, 56, 4, 35, 1, 20, 4, 10].getD k.1 0
  | 4 => #[35, 20, 56, 10, 164, 4, 56, 1, 35, 4, 20, 10].getD k.1 0
  | 5 => #[20, 35, 10, 56, 4, 164, 1, 56, 4, 35, 10, 20].getD k.1 0
  | 6 => #[20, 10, 35, 4, 56, 1, 164, 4, 56, 10, 35, 20].getD k.1 0
  | 7 => #[10, 20, 4, 35, 1, 56, 4, 164, 10, 56, 20, 35].getD k.1 0
  | 8 => #[10, 4, 20, 1, 35, 4, 56, 10, 164, 20, 56, 35].getD k.1 0
  | 9 => #[4, 10, 1, 20, 4, 35, 10, 56, 20, 164, 35, 56].getD k.1 0
  | 10 => #[4, 1, 10, 4, 20, 10, 35, 20, 56, 35, 164, 56].getD k.1 0
  | 11 => #[1, 4, 4, 10, 10, 20, 20, 35, 35, 56, 56, 164].getD k.1 0
  | _ => 0

private def tbl_4 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[415, 126, 126, 70, 70, 35, 35, 15, 15, 5, 5, 1].getD k.1 0
  | 1 => #[126, 415, 70, 126, 35, 70, 15, 35, 5, 15, 1, 5].getD k.1 0
  | 2 => #[126, 70, 415, 35, 126, 15, 70, 5, 35, 1, 15, 5].getD k.1 0
  | 3 => #[70, 126, 35, 415, 15, 126, 5, 70, 1, 35, 5, 15].getD k.1 0
  | 4 => #[70, 35, 126, 15, 415, 5, 126, 1, 70, 5, 35, 15].getD k.1 0
  | 5 => #[35, 70, 15, 126, 5, 415, 1, 126, 5, 70, 15, 35].getD k.1 0
  | 6 => #[35, 15, 70, 5, 126, 1, 415, 5, 126, 15, 70, 35].getD k.1 0
  | 7 => #[15, 35, 5, 70, 1, 126, 5, 415, 15, 126, 35, 70].getD k.1 0
  | 8 => #[15, 5, 35, 1, 70, 5, 126, 15, 415, 35, 126, 70].getD k.1 0
  | 9 => #[5, 15, 1, 35, 5, 70, 15, 126, 35, 415, 70, 126].getD k.1 0
  | 10 => #[5, 1, 15, 5, 35, 15, 70, 35, 126, 70, 415, 126].getD k.1 0
  | 11 => #[1, 5, 5, 15, 15, 35, 35, 70, 70, 126, 126, 415].getD k.1 0
  | _ => 0

private def tbl_5 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[918, 252, 252, 126, 126, 56, 56, 21, 21, 6, 6, 1].getD k.1 0
  | 1 => #[252, 918, 126, 252, 56, 126, 21, 56, 6, 21, 1, 6].getD k.1 0
  | 2 => #[252, 126, 918, 56, 252, 21, 126, 6, 56, 1, 21, 6].getD k.1 0
  | 3 => #[126, 252, 56, 918, 21, 252, 6, 126, 1, 56, 6, 21].getD k.1 0
  | 4 => #[126, 56, 252, 21, 918, 6, 252, 1, 126, 6, 56, 21].getD k.1 0
  | 5 => #[56, 126, 21, 252, 6, 918, 1, 252, 6, 126, 21, 56].getD k.1 0
  | 6 => #[56, 21, 126, 6, 252, 1, 918, 6, 252, 21, 126, 56].getD k.1 0
  | 7 => #[21, 56, 6, 126, 1, 252, 6, 918, 21, 252, 56, 126].getD k.1 0
  | 8 => #[21, 6, 56, 1, 126, 6, 252, 21, 918, 56, 252, 126].getD k.1 0
  | 9 => #[6, 21, 1, 56, 6, 126, 21, 252, 56, 918, 126, 252].getD k.1 0
  | 10 => #[6, 1, 21, 6, 56, 21, 126, 56, 252, 126, 918, 252].getD k.1 0
  | 11 => #[1, 6, 6, 21, 21, 56, 56, 126, 126, 252, 252, 918].getD k.1 0
  | _ => 0

private def tbl_6 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[1841, 462, 462, 210, 210, 84, 84, 28, 28, 7, 7, 1].getD k.1 0
  | 1 => #[462, 1841, 210, 462, 84, 210, 28, 84, 7, 28, 1, 7].getD k.1 0
  | 2 => #[462, 210, 1841, 84, 462, 28, 210, 7, 84, 1, 28, 7].getD k.1 0
  | 3 => #[210, 462, 84, 1841, 28, 462, 7, 210, 1, 84, 7, 28].getD k.1 0
  | 4 => #[210, 84, 462, 28, 1841, 7, 462, 1, 210, 7, 84, 28].getD k.1 0
  | 5 => #[84, 210, 28, 462, 7, 1841, 1, 462, 7, 210, 28, 84].getD k.1 0
  | 6 => #[84, 28, 210, 7, 462, 1, 1841, 7, 462, 28, 210, 84].getD k.1 0
  | 7 => #[28, 84, 7, 210, 1, 462, 7, 1841, 28, 462, 84, 210].getD k.1 0
  | 8 => #[28, 7, 84, 1, 210, 7, 462, 28, 1841, 84, 462, 210].getD k.1 0
  | 9 => #[7, 28, 1, 84, 7, 210, 28, 462, 84, 1841, 210, 462].getD k.1 0
  | 10 => #[7, 1, 28, 7, 84, 28, 210, 84, 462, 210, 1841, 462].getD k.1 0
  | 11 => #[1, 7, 7, 28, 28, 84, 84, 210, 210, 462, 462, 1841].getD k.1 0
  | _ => 0

private def tbl_7 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[3424, 792, 792, 330, 330, 120, 120, 36, 36, 8, 8, 1].getD k.1 0
  | 1 => #[792, 3424, 330, 792, 120, 330, 36, 120, 8, 36, 1, 8].getD k.1 0
  | 2 => #[792, 330, 3424, 120, 792, 36, 330, 8, 120, 1, 36, 8].getD k.1 0
  | 3 => #[330, 792, 120, 3424, 36, 792, 8, 330, 1, 120, 8, 36].getD k.1 0
  | 4 => #[330, 120, 792, 36, 3424, 8, 792, 1, 330, 8, 120, 36].getD k.1 0
  | 5 => #[120, 330, 36, 792, 8, 3424, 1, 792, 8, 330, 36, 120].getD k.1 0
  | 6 => #[120, 36, 330, 8, 792, 1, 3424, 8, 792, 36, 330, 120].getD k.1 0
  | 7 => #[36, 120, 8, 330, 1, 792, 8, 3424, 36, 792, 120, 330].getD k.1 0
  | 8 => #[36, 8, 120, 1, 330, 8, 792, 36, 3424, 120, 792, 330].getD k.1 0
  | 9 => #[8, 36, 1, 120, 8, 330, 36, 792, 120, 3424, 330, 792].getD k.1 0
  | 10 => #[8, 1, 36, 8, 120, 36, 330, 120, 792, 330, 3424, 792].getD k.1 0
  | 11 => #[1, 8, 8, 36, 36, 120, 120, 330, 330, 792, 792, 3424].getD k.1 0
  | _ => 0

private lemma dp_eq_tbl_0 (j k : Fin 12) : dp 0 j k = tbl_0 j k := by
  revert j k; decide

private lemma dp_eq_tbl_1 (j k : Fin 12) : dp 1 j k = tbl_1 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 0 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_0 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_0]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_2 (j k : Fin 12) : dp 2 j k = tbl_2 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 1 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_1 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_1]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_3 (j k : Fin 12) : dp 3 j k = tbl_3 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 2 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_2 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_2]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_4 (j k : Fin 12) : dp 4 j k = tbl_4 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 3 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_3 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_3]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_5 (j k : Fin 12) : dp 5 j k = tbl_5 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 4 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_4 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_4]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_6 (j k : Fin 12) : dp 6 j k = tbl_6 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 5 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_5 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_5]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_7 (j k : Fin 12) : dp 7 j k = tbl_7 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 6 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_6 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_6]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_rec_base :
    ∀ j k : Fin 12, dp 7 j k + 21 * dp 5 j k + 35 * dp 3 j k + 7 * dp 1 j k = 7 * dp 6 j k + 35 * dp 4 j k + 21 * dp 2 j k + dp 0 j k := by
  intro j k
  rw [dp_eq_tbl_0, dp_eq_tbl_1, dp_eq_tbl_2, dp_eq_tbl_3, dp_eq_tbl_4, dp_eq_tbl_5, dp_eq_tbl_6, dp_eq_tbl_7]
  revert j k; decide

private lemma sum_lin (f7 f6 f5 f4 f3 f2 f1 f0 : Fin 12 → ℕ) (g : Fin 12 → Bool)
    (h : ∀ i : Fin 12, f7 i + 21 * f5 i + 35 * f3 i + 7 * f1 i = 7 * f6 i + 35 * f4 i + 21 * f2 i + f0 i) :
    (∑ i : Fin 12, if g i = true then f7 i else 0) + 21 * (∑ i : Fin 12, if g i = true then f5 i else 0) + 35 * (∑ i : Fin 12, if g i = true then f3 i else 0) + 7 * (∑ i : Fin 12, if g i = true then f1 i else 0) = 7 * (∑ i : Fin 12, if g i = true then f6 i else 0) + 35 * (∑ i : Fin 12, if g i = true then f4 i else 0) + 21 * (∑ i : Fin 12, if g i = true then f2 i else 0) + (∑ i : Fin 12, if g i = true then f0 i else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  cases g i
  · simp
  · simp only [↓reduceIte]; exact h i

private lemma dp_rec (m : ℕ) :
    ∀ j k : Fin 12, dp (m + 7) j k + 21 * dp (m + 5) j k + 35 * dp (m + 3) j k + 7 * dp (m + 1) j k = 7 * dp (m + 6) j k + 35 * dp (m + 4) j k + 21 * dp (m + 2) j k + dp m j k := by
  induction m with
  | zero => exact dp_rec_base
  | succ m ih =>
    intro j k
    rw [dp_succ_eq (m + 7), dp_succ_eq (m + 6), dp_succ_eq (m + 5), dp_succ_eq (m + 4), dp_succ_eq (m + 3), dp_succ_eq (m + 2), dp_succ_eq (m + 1), dp_succ_eq m]
    exact sum_lin (fun i => dp (m + 7) i j) (fun i => dp (m + 6) i j) (fun i => dp (m + 5) i j) (fun i => dp (m + 4) i j) (fun i => dp (m + 3) i j) (fun i => dp (m + 2) i j) (fun i => dp (m + 1) i j) (fun i => dp m i j) (fun i => colOk i j k) (fun i => ih i j)

private abbrev ValidSeq (n : ℕ) (j k : Fin 12) :=
  {s : Fin (n + 2) → Fin 12 //
    (∀ r : Fin n, colOk (s ⟨r.1, by omega⟩) (s ⟨r.1 + 1, by omega⟩) (s ⟨r.1 + 2, by omega⟩) = true) ∧
    s ⟨n, by omega⟩ = j ∧ s ⟨n + 1, by omega⟩ = k}

private lemma card_ValidSeq (n : ℕ) :
    ∀ j k : Fin 12, Fintype.card (ValidSeq n j k) = dp n j k := by
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
    let φ : (Σ i : Fin 12, {t : ValidSeq n i j // colOk i j k = true}) → ValidSeq (n + 1) j k :=
      fun ⟨i, ⟨⟨t, ht, hti, htj⟩, hok⟩⟩ =>
        let s : Fin (n + 3) → Fin 12 := Fin.snoc t k
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
        have hfun : (Fin.snoc t1 k : Fin (n + 3) → Fin 12) = Fin.snoc t2 k := congrArg Subtype.val heq
        have ht_eq : t1 = t2 := by
          funext r
          have h := congrFun hfun r.castSucc
          simpa using h
        subst ht_eq
        have hi_eq : i1 = i2 := hi1.symm.trans hi2
        subst hi_eq
        rfl
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

private lemma a_eq_sum_dp (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ j : Fin 12, ∑ k : Fin 12, dp n j k := by
  unfold a; rw [if_neg (by omega)]
  let φ : (Σ j : Fin 12, Σ k : Fin 12, ValidSeq n j k) → {A : Fin (n + 2) → Fin 6 → Fin 2 // isValid n A} :=
    fun ⟨_, _, ⟨s, hs, _, _⟩⟩ =>
      ⟨fun r => rowBit (s r), fun r => rowBit_valid (s r), fun c r => (colOk_iff _ _ _).mp (hs r) c⟩
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨j1, k1, ⟨s1, hs1, hj1, hk1⟩⟩ ⟨j2, k2, ⟨s2, hs2, hj2, hk2⟩⟩ heq
      have hfun : (fun r => rowBit (s1 r)) = fun r => rowBit (s2 r) := congrArg Subtype.val heq
      have hs_eq : s1 = s2 := by
        funext r
        have h := congrFun hfun r
        have := congrArg (fun x => codeToIdx (encodeRow x)) h
        simpa [codeToIdx_encodeRow] using this
      subst hs_eq
      have hj_eq : j1 = j2 := hj1.symm.trans hj2
      have hk_eq : k1 = k2 := hk1.symm.trans hk2
      subst hj_eq; subst hk_eq; rfl
    · rintro ⟨A, hA1, hA2⟩
      let s : Fin (n + 2) → Fin 12 := fun r => rowEquiv ⟨A r, hA1 r⟩
      have hs : ∀ r : Fin n, colOk (s ⟨r.1, by omega⟩) (s ⟨r.1 + 1, by omega⟩) (s ⟨r.1 + 2, by omega⟩) = true := by
        intro r; rw [colOk_iff]
        intro c
        have h0 : rowBit (s ⟨r.1, by omega⟩) = A ⟨r.1, by omega⟩ := congrArg Subtype.val (rowEquiv.left_inv ⟨A ⟨r.1, by omega⟩, hA1 _⟩)
        have h1 : rowBit (s ⟨r.1 + 1, by omega⟩) = A ⟨r.1 + 1, by omega⟩ := congrArg Subtype.val (rowEquiv.left_inv ⟨A ⟨r.1 + 1, by omega⟩, hA1 _⟩)
        have h2 : rowBit (s ⟨r.1 + 2, by omega⟩) = A ⟨r.1 + 2, by omega⟩ := congrArg Subtype.val (rowEquiv.left_inv ⟨A ⟨r.1 + 2, by omega⟩, hA1 _⟩)
        rw [h0, h1, h2]; exact hA2 c r
      refine ⟨⟨s ⟨n, by omega⟩, s ⟨n + 1, by omega⟩, ⟨s, hs, rfl, rfl⟩⟩, ?_⟩
      apply Subtype.ext; funext r
      exact congrArg Subtype.val (rowEquiv.left_inv ⟨A r, hA1 r⟩)
  rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro j _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro k _
  exact card_ValidSeq n j k

private lemma a_rec_d (m : ℕ) (hm : 1 ≤ m) :
    a (m + 7) + 21 * a (m + 5) + 35 * a (m + 3) + 7 * a (m + 1) = 7 * a (m + 6) + 35 * a (m + 4) + 21 * a (m + 2) + a m := by
  rw [a_eq_sum_dp (m + 7) (by omega), a_eq_sum_dp (m + 6) (by omega), a_eq_sum_dp (m + 5) (by omega), a_eq_sum_dp (m + 4) (by omega), a_eq_sum_dp (m + 3) (by omega), a_eq_sum_dp (m + 2) (by omega), a_eq_sum_dp (m + 1) (by omega), a_eq_sum_dp m hm]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  exact dp_rec m j k

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_val_1 : a 1 = 636 := by
  rw [a_eq_sum_dp 1 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 1 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_1 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_1 j k
  rw [h]; decide
private lemma a_val_2 : a 2 = 1968 := by
  rw [a_eq_sum_dp 2 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 2 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_2 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_2 j k
  rw [h]; decide
private lemma a_val_3 : a 3 = 4980 := by
  rw [a_eq_sum_dp 3 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 3 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_3 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_3 j k
  rw [h]; decide
private lemma a_val_4 : a 4 = 11016 := by
  rw [a_eq_sum_dp 4 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 4 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_4 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_4 j k
  rw [h]; decide
private lemma a_val_5 : a 5 = 22092 := by
  rw [a_eq_sum_dp 5 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 5 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_5 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_5 j k
  rw [h]; decide
private lemma a_val_6 : a 6 = 41088 := by
  rw [a_eq_sum_dp 6 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 6 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_6 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_6 j k
  rw [h]; decide
private lemma a_val_7 : a 7 = 71964 := by
  rw [a_eq_sum_dp 7 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 7 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_7 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_7 j k
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

theorem solution : type_of% @OMA.S_oeis_a202048.main := by
  have hrec_d : ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ) := by
    intro n hn
    have h := a_rec_d (n - 7) (by omega)
    simp only [show n - 7 + 7 = n by omega, show n - 7 + 6 = n - 1 by omega, show n - 7 + 5 = n - 2 by omega, show n - 7 + 4 = n - 3 by omega, show n - 7 + 3 = n - 4 by omega, show n - 7 + 2 = n - 5 by omega, show n - 7 + 1 = n - 6 by omega] at h
    omega
  have hrec_stmt : ∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ) := by
    intro n hn
    have h1 := hrec_d n (by omega)
    have h2 := hrec_d (n - 1) (by omega)
    simp only [show n - 1 - 1 = n - 2 by omega, show n - 1 - 2 = n - 3 by omega, show n - 1 - 3 = n - 4 by omega, show n - 1 - 4 = n - 5 by omega, show n - 1 - 5 = n - 6 by omega, show n - 1 - 6 = n - 7 by omega, show n - 1 - 7 = n - 8 by omega] at h2
    linarith
  refine ⟨?_, hrec_stmt⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 7 = 1 - PowerSeries.C 7 * PowerSeries.X ^ 1 + PowerSeries.C 21 * PowerSeries.X ^ 2 - PowerSeries.C 35 * PowerSeries.X ^ 3 + PowerSeries.C 35 * PowerSeries.X ^ 4 - PowerSeries.C 21 * PowerSeries.X ^ 5 + PowerSeries.C 7 * PowerSeries.X ^ 6 - PowerSeries.X ^ 7 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : 12 * (PowerSeries.X : PowerSeries ℚ) * (53 - 207 * PowerSeries.X + 380 * PowerSeries.X ^ 2 - 398 * PowerSeries.X ^ 3 + 245 * PowerSeries.X ^ 4 - 83 * PowerSeries.X ^ 5 + 12 * PowerSeries.X ^ 6) = PowerSeries.C 636 * PowerSeries.X ^ 1 - PowerSeries.C 2484 * PowerSeries.X ^ 2 + PowerSeries.C 4560 * PowerSeries.X ^ 3 - PowerSeries.C 4776 * PowerSeries.X ^ 4 + PowerSeries.C 2940 * PowerSeries.X ^ 5 - PowerSeries.C 996 * PowerSeries.X ^ 6 + PowerSeries.C 144 * PowerSeries.X ^ 7 := by
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

end OMA.P_oeis_a202048

theorem OMA.solution : type_of% @OMA.S_oeis_a202048.main :=
  OMA.P_oeis_a202048.solution
