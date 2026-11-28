import OMAStatements.S_oeis_a202443

namespace OMA.P_oeis_a202443

open OMA.S_oeis_a202443

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
  funext c; apply Fin.ext; unfold bitsOf encodeRow
  have : ∀ j : Fin 6, (r j).1 < 2 := fun j => (r j).2
  have h0 := this 0 ; have h1 := this 1 ; have h2 := this 2 ; have h3 := this 3 ; have h4 := this 4 ; have h5 := this 5
  fin_cases c <;> dsimp <;> omega

private lemma rowBit_codeToIdx (r : Fin 6 → Fin 2) (hr : rowValid r) :
    rowBit (codeToIdx (encodeRow r)) = r := by
  have hall : ∀ m : Fin 64, rowValid (bitsOf m.1) → rowBit (codeToIdx m.1) = bitsOf m.1 := by
    decide
  have h1 := hall ⟨encodeRow r, encodeRow_lt r⟩ (by rw [bitsOf_encodeRow]; exact hr)
  rw [bitsOf_encodeRow] at h1
  exact h1

private def rowEquiv : {r : Fin 6 → Fin 2 // rowValid r} ≃ Fin 12 where
  toFun r := codeToIdx (encodeRow r.1)
  invFun i := ⟨rowBit i, rowBit_valid i⟩
  left_inv r := Subtype.ext (rowBit_codeToIdx r.1 r.2)
  right_inv i := codeToIdx_encodeRow i

private def colOk (i j k : Fin 12) : Bool :=
  (((rowCode i ^^^ rowCode j ^^^ 63) &&& (rowCode j ^^^ rowCode k)) == 0) &&
  ((((rowCode i &&& 15) ^^^ ((rowCode j >>> 1) &&& 15) ^^^ 15) &&&
    (((rowCode j >>> 1) &&& 15) ^^^ ((rowCode k >>> 2) &&& 15))) == 0)

private lemma colOk_iff (i j k : Fin 12) :
    colOk i j k = true ↔
      (∀ c : Fin 6, avoids3 (rowBit i c) (rowBit j c) (rowBit k c)) ∧
      (∀ c : Fin 4, avoids3 (rowBit i ⟨c.1, by omega⟩) (rowBit j ⟨c.1 + 1, by omega⟩) (rowBit k ⟨c.1 + 2, by omega⟩)) := by
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
  | 0 => #[12, 6, 6, 5, 5, 4, 4, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[6, 12, 5, 5, 4, 4, 3, 2, 1, 1, 0, 1].getD k.1 0
  | 2 => #[1, 0, 6, 4, 4, 3, 3, 1, 1, 0, 2, 1].getD k.1 0
  | 3 => #[1, 2, 0, 5, 3, 3, 2, 1, 0, 2, 0, 1].getD k.1 0
  | 4 => #[1, 0, 2, 0, 4, 2, 2, 0, 2, 0, 2, 1].getD k.1 0
  | 5 => #[1, 2, 0, 2, 0, 3, 1, 2, 0, 2, 0, 1].getD k.1 0
  | 6 => #[1, 0, 2, 0, 2, 1, 3, 0, 2, 0, 2, 1].getD k.1 0
  | 7 => #[1, 2, 0, 2, 0, 2, 2, 4, 0, 2, 0, 1].getD k.1 0
  | 8 => #[1, 0, 2, 0, 1, 2, 3, 3, 5, 0, 2, 1].getD k.1 0
  | 9 => #[1, 2, 0, 1, 1, 3, 3, 4, 4, 6, 0, 1].getD k.1 0
  | 10 => #[1, 0, 1, 1, 2, 3, 4, 4, 5, 5, 12, 6].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 4, 4, 5, 5, 6, 6, 12].getD k.1 0
  | _ => 0

private def tbl_2 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[28, 11, 6, 5, 5, 4, 4, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[6, 27, 0, 9, 0, 7, 0, 3, 0, 1, 0, 1].getD k.1 0
  | 2 => #[6, 0, 19, 0, 7, 0, 5, 0, 1, 0, 2, 1].getD k.1 0
  | 3 => #[5, 10, 0, 15, 0, 5, 0, 1, 0, 3, 0, 2].getD k.1 0
  | 4 => #[5, 0, 9, 0, 11, 0, 3, 0, 3, 0, 4, 2].getD k.1 0
  | 5 => #[4, 8, 0, 7, 0, 8, 1, 5, 0, 7, 0, 4].getD k.1 0
  | 6 => #[4, 0, 7, 0, 5, 1, 8, 0, 7, 0, 8, 4].getD k.1 0
  | 7 => #[2, 4, 0, 3, 0, 3, 0, 11, 0, 9, 0, 5].getD k.1 0
  | 8 => #[2, 0, 3, 0, 1, 0, 5, 0, 15, 0, 10, 5].getD k.1 0
  | 9 => #[1, 2, 0, 1, 0, 5, 0, 7, 0, 19, 0, 6].getD k.1 0
  | 10 => #[1, 0, 1, 0, 3, 0, 7, 0, 9, 0, 27, 6].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 4, 4, 5, 5, 6, 11, 28].getD k.1 0
  | _ => 0

private def tbl_3 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[65, 19, 19, 13, 13, 8, 8, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[11, 63, 0, 25, 0, 15, 0, 3, 0, 1, 0, 1].getD k.1 0
  | 2 => #[6, 0, 45, 0, 20, 0, 11, 0, 1, 0, 2, 1].getD k.1 0
  | 3 => #[5, 14, 0, 35, 0, 11, 0, 1, 0, 3, 0, 2].getD k.1 0
  | 4 => #[5, 0, 12, 0, 24, 0, 6, 0, 4, 0, 5, 2].getD k.1 0
  | 5 => #[4, 11, 0, 12, 0, 16, 1, 8, 0, 9, 0, 4].getD k.1 0
  | 6 => #[4, 0, 9, 0, 8, 1, 16, 0, 12, 0, 11, 4].getD k.1 0
  | 7 => #[2, 5, 0, 4, 0, 6, 0, 24, 0, 12, 0, 5].getD k.1 0
  | 8 => #[2, 0, 3, 0, 1, 0, 11, 0, 35, 0, 14, 5].getD k.1 0
  | 9 => #[1, 2, 0, 1, 0, 11, 0, 20, 0, 45, 0, 6].getD k.1 0
  | 10 => #[1, 0, 1, 0, 3, 0, 15, 0, 25, 0, 63, 11].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 8, 8, 13, 13, 19, 19, 65].getD k.1 0
  | _ => 0

private def tbl_4 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[107, 24, 19, 13, 13, 8, 8, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[19, 115, 0, 33, 0, 19, 0, 3, 0, 1, 0, 1].getD k.1 0
  | 2 => #[19, 0, 89, 0, 25, 0, 13, 0, 1, 0, 2, 1].getD k.1 0
  | 3 => #[13, 38, 0, 77, 0, 17, 0, 1, 0, 3, 0, 2].getD k.1 0
  | 4 => #[13, 0, 33, 0, 53, 0, 9, 0, 4, 0, 5, 2].getD k.1 0
  | 5 => #[8, 23, 0, 26, 0, 33, 1, 17, 0, 19, 0, 8].getD k.1 0
  | 6 => #[8, 0, 19, 0, 17, 1, 33, 0, 26, 0, 23, 8].getD k.1 0
  | 7 => #[2, 5, 0, 4, 0, 9, 0, 53, 0, 33, 0, 13].getD k.1 0
  | 8 => #[2, 0, 3, 0, 1, 0, 17, 0, 77, 0, 38, 13].getD k.1 0
  | 9 => #[1, 2, 0, 1, 0, 13, 0, 25, 0, 89, 0, 19].getD k.1 0
  | 10 => #[1, 0, 1, 0, 3, 0, 19, 0, 33, 0, 115, 19].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 8, 8, 13, 13, 19, 24, 107].getD k.1 0
  | _ => 0

private def tbl_5 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[194, 44, 44, 25, 25, 12, 12, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[24, 208, 0, 69, 0, 31, 0, 3, 0, 1, 0, 1].getD k.1 0
  | 2 => #[19, 0, 164, 0, 56, 0, 23, 0, 1, 0, 2, 1].getD k.1 0
  | 3 => #[13, 46, 0, 141, 0, 31, 0, 1, 0, 3, 0, 2].getD k.1 0
  | 4 => #[13, 0, 38, 0, 96, 0, 18, 0, 4, 0, 5, 2].getD k.1 0
  | 5 => #[8, 27, 0, 36, 0, 59, 1, 22, 0, 21, 0, 8].getD k.1 0
  | 6 => #[8, 0, 21, 0, 22, 1, 59, 0, 36, 0, 27, 8].getD k.1 0
  | 7 => #[2, 5, 0, 4, 0, 18, 0, 96, 0, 38, 0, 13].getD k.1 0
  | 8 => #[2, 0, 3, 0, 1, 0, 31, 0, 141, 0, 46, 13].getD k.1 0
  | 9 => #[1, 2, 0, 1, 0, 23, 0, 56, 0, 164, 0, 19].getD k.1 0
  | 10 => #[1, 0, 1, 0, 3, 0, 31, 0, 69, 0, 208, 24].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 12, 12, 25, 25, 44, 44, 194].getD k.1 0
  | _ => 0

private def tbl_6 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[286, 49, 44, 25, 25, 12, 12, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[44, 333, 0, 81, 0, 35, 0, 3, 0, 1, 0, 1].getD k.1 0
  | 2 => #[44, 0, 271, 0, 63, 0, 25, 0, 1, 0, 2, 1].getD k.1 0
  | 3 => #[25, 94, 0, 251, 0, 41, 0, 1, 0, 3, 0, 2].getD k.1 0
  | 4 => #[25, 0, 81, 0, 175, 0, 23, 0, 4, 0, 5, 2].getD k.1 0
  | 5 => #[12, 43, 0, 62, 0, 108, 1, 41, 0, 35, 0, 12].getD k.1 0
  | 6 => #[12, 0, 35, 0, 41, 1, 108, 0, 62, 0, 43, 12].getD k.1 0
  | 7 => #[2, 5, 0, 4, 0, 23, 0, 175, 0, 81, 0, 25].getD k.1 0
  | 8 => #[2, 0, 3, 0, 1, 0, 41, 0, 251, 0, 94, 25].getD k.1 0
  | 9 => #[1, 2, 0, 1, 0, 25, 0, 63, 0, 271, 0, 44].getD k.1 0
  | 10 => #[1, 0, 1, 0, 3, 0, 35, 0, 81, 0, 333, 44].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 12, 12, 25, 25, 44, 49, 286].getD k.1 0
  | _ => 0

private def tbl_7 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[455, 85, 85, 41, 41, 16, 16, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[49, 527, 0, 145, 0, 51, 0, 3, 0, 1, 0, 1].getD k.1 0
  | 2 => #[44, 0, 435, 0, 120, 0, 39, 0, 1, 0, 2, 1].getD k.1 0
  | 3 => #[25, 106, 0, 399, 0, 67, 0, 1, 0, 3, 0, 2].getD k.1 0
  | 4 => #[25, 0, 88, 0, 280, 0, 42, 0, 4, 0, 5, 2].getD k.1 0
  | 5 => #[12, 47, 0, 76, 0, 172, 1, 48, 0, 37, 0, 12].getD k.1 0
  | 6 => #[12, 0, 37, 0, 48, 1, 172, 0, 76, 0, 47, 12].getD k.1 0
  | 7 => #[2, 5, 0, 4, 0, 42, 0, 280, 0, 88, 0, 25].getD k.1 0
  | 8 => #[2, 0, 3, 0, 1, 0, 67, 0, 399, 0, 106, 25].getD k.1 0
  | 9 => #[1, 2, 0, 1, 0, 39, 0, 120, 0, 435, 0, 44].getD k.1 0
  | 10 => #[1, 0, 1, 0, 3, 0, 51, 0, 145, 0, 527, 49].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 16, 16, 41, 41, 85, 85, 455].getD k.1 0
  | _ => 0

private def tbl_8 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[629, 90, 85, 41, 41, 16, 16, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[85, 773, 0, 161, 0, 55, 0, 3, 0, 1, 0, 1].getD k.1 0
  | 2 => #[85, 0, 649, 0, 129, 0, 41, 0, 1, 0, 2, 1].getD k.1 0
  | 3 => #[41, 186, 0, 625, 0, 81, 0, 1, 0, 3, 0, 2].getD k.1 0
  | 4 => #[41, 0, 161, 0, 449, 0, 49, 0, 4, 0, 5, 2].getD k.1 0
  | 5 => #[16, 67, 0, 118, 0, 281, 1, 81, 0, 55, 0, 16].getD k.1 0
  | 6 => #[16, 0, 55, 0, 81, 1, 281, 0, 118, 0, 67, 16].getD k.1 0
  | 7 => #[2, 5, 0, 4, 0, 49, 0, 449, 0, 161, 0, 41].getD k.1 0
  | 8 => #[2, 0, 3, 0, 1, 0, 81, 0, 625, 0, 186, 41].getD k.1 0
  | 9 => #[1, 2, 0, 1, 0, 41, 0, 129, 0, 649, 0, 85].getD k.1 0
  | 10 => #[1, 0, 1, 0, 3, 0, 55, 0, 161, 0, 773, 85].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 16, 16, 41, 41, 85, 90, 629].getD k.1 0
  | _ => 0

private def tbl_9 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[920, 146, 146, 61, 61, 20, 20, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[90, 1124, 0, 261, 0, 75, 0, 3, 0, 1, 0, 1].getD k.1 0
  | 2 => #[85, 0, 954, 0, 220, 0, 59, 0, 1, 0, 2, 1].getD k.1 0
  | 3 => #[41, 202, 0, 909, 0, 123, 0, 1, 0, 3, 0, 2].getD k.1 0
  | 4 => #[41, 0, 170, 0, 660, 0, 82, 0, 4, 0, 5, 2].getD k.1 0
  | 5 => #[16, 71, 0, 136, 0, 411, 1, 90, 0, 57, 0, 16].getD k.1 0
  | 6 => #[16, 0, 57, 0, 90, 1, 411, 0, 136, 0, 71, 16].getD k.1 0
  | 7 => #[2, 5, 0, 4, 0, 82, 0, 660, 0, 170, 0, 41].getD k.1 0
  | 8 => #[2, 0, 3, 0, 1, 0, 123, 0, 909, 0, 202, 41].getD k.1 0
  | 9 => #[1, 2, 0, 1, 0, 59, 0, 220, 0, 954, 0, 85].getD k.1 0
  | 10 => #[1, 0, 1, 0, 3, 0, 75, 0, 261, 0, 1124, 90].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 20, 20, 61, 61, 146, 146, 920].getD k.1 0
  | _ => 0

private def tbl_10 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[1216, 151, 146, 61, 61, 20, 20, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[146, 1551, 0, 281, 0, 79, 0, 3, 0, 1, 0, 1].getD k.1 0
  | 2 => #[146, 0, 1331, 0, 231, 0, 61, 0, 1, 0, 2, 1].getD k.1 0
  | 3 => #[61, 322, 0, 1311, 0, 141, 0, 1, 0, 3, 0, 2].getD k.1 0
  | 4 => #[61, 0, 281, 0, 971, 0, 91, 0, 4, 0, 5, 2].getD k.1 0
  | 5 => #[20, 95, 0, 198, 0, 616, 1, 141, 0, 79, 0, 20].getD k.1 0
  | 6 => #[20, 0, 79, 0, 141, 1, 616, 0, 198, 0, 95, 20].getD k.1 0
  | 7 => #[2, 5, 0, 4, 0, 91, 0, 971, 0, 281, 0, 61].getD k.1 0
  | 8 => #[2, 0, 3, 0, 1, 0, 141, 0, 1311, 0, 322, 61].getD k.1 0
  | 9 => #[1, 2, 0, 1, 0, 61, 0, 231, 0, 1331, 0, 146].getD k.1 0
  | 10 => #[1, 0, 1, 0, 3, 0, 79, 0, 281, 0, 1551, 146].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 20, 20, 61, 61, 146, 151, 1216].getD k.1 0
  | _ => 0

private def tbl_11 (j k : Fin 12) : ℕ :=
  match j.1 with
  | 0 => #[1677, 231, 231, 85, 85, 24, 24, 2, 2, 1, 1, 1].getD k.1 0
  | 1 => #[151, 2127, 0, 425, 0, 103, 0, 3, 0, 1, 0, 1].getD k.1 0
  | 2 => #[146, 0, 1841, 0, 364, 0, 83, 0, 1, 0, 2, 1].getD k.1 0
  | 3 => #[61, 342, 0, 1795, 0, 203, 0, 1, 0, 3, 0, 2].getD k.1 0
  | 4 => #[61, 0, 292, 0, 1344, 0, 142, 0, 4, 0, 5, 2].getD k.1 0
  | 5 => #[20, 99, 0, 220, 0, 848, 1, 152, 0, 81, 0, 20].getD k.1 0
  | 6 => #[20, 0, 81, 0, 152, 1, 848, 0, 220, 0, 99, 20].getD k.1 0
  | 7 => #[2, 5, 0, 4, 0, 142, 0, 1344, 0, 292, 0, 61].getD k.1 0
  | 8 => #[2, 0, 3, 0, 1, 0, 203, 0, 1795, 0, 342, 61].getD k.1 0
  | 9 => #[1, 2, 0, 1, 0, 83, 0, 364, 0, 1841, 0, 146].getD k.1 0
  | 10 => #[1, 0, 1, 0, 3, 0, 103, 0, 425, 0, 2127, 151].getD k.1 0
  | 11 => #[1, 1, 1, 2, 2, 24, 24, 85, 85, 231, 231, 1677].getD k.1 0
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

private lemma dp_eq_tbl_8 (j k : Fin 12) : dp 8 j k = tbl_8 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 7 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_7 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_7]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_9 (j k : Fin 12) : dp 9 j k = tbl_9 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 8 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_8 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_8]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_10 (j k : Fin 12) : dp 10 j k = tbl_10 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 9 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_9 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_9]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_11 (j k : Fin 12) : dp 11 j k = tbl_11 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 12, if colOk i j k = true then dp 10 i j else 0) =
      ∑ i : Fin 12, if colOk i j k = true then tbl_10 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_10]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_rec_base :
    ∀ j k : Fin 12,
      dp 11 j k + 6 * dp 8 j k + 2 * dp 5 j k + 2 * dp 4 j k =
      2 * dp 10 j k + 2 * dp 9 j k + 6 * dp 6 j k + dp 3 j k := by
  intro j k
  rw [dp_eq_tbl_11, dp_eq_tbl_10, dp_eq_tbl_9, dp_eq_tbl_8, dp_eq_tbl_6, dp_eq_tbl_5, dp_eq_tbl_4, dp_eq_tbl_3]
  revert j k; decide

private lemma sum_lin (f8 f7 f6 f5 f3 f2 f1 f0 : Fin 12 → ℕ) (g : Fin 12 → Bool)
    (h : ∀ i : Fin 12,
      f8 i + 6 * f5 i + 2 * f2 i + 2 * f1 i = 2 * f7 i + 2 * f6 i + 6 * f3 i + f0 i) :
    (∑ i : Fin 12, if g i = true then f8 i else 0) +
    6 * (∑ i : Fin 12, if g i = true then f5 i else 0) +
    2 * (∑ i : Fin 12, if g i = true then f2 i else 0) +
    2 * (∑ i : Fin 12, if g i = true then f1 i else 0) =
    2 * (∑ i : Fin 12, if g i = true then f7 i else 0) +
    2 * (∑ i : Fin 12, if g i = true then f6 i else 0) +
    6 * (∑ i : Fin 12, if g i = true then f3 i else 0) +
    (∑ i : Fin 12, if g i = true then f0 i else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  cases g i
  · simp
  · simp only [↓reduceIte]; exact h i

private lemma dp_rec (m : ℕ) :
    ∀ j k : Fin 12,
      dp (m + 11) j k + 6 * dp (m + 8) j k + 2 * dp (m + 5) j k + 2 * dp (m + 4) j k =
      2 * dp (m + 10) j k + 2 * dp (m + 9) j k + 6 * dp (m + 6) j k + dp (m + 3) j k := by
  induction m with
  | zero => exact dp_rec_base
  | succ m ih =>
    intro j k
    rw [dp_succ_eq (m + 11), dp_succ_eq (m + 10), dp_succ_eq (m + 9),
        dp_succ_eq (m + 8), dp_succ_eq (m + 6), dp_succ_eq (m + 5),
        dp_succ_eq (m + 4), dp_succ_eq (m + 3)]
    exact sum_lin (fun i => dp (m + 11) i j) (fun i => dp (m + 10) i j)
      (fun i => dp (m + 9) i j) (fun i => dp (m + 8) i j)
      (fun i => dp (m + 6) i j) (fun i => dp (m + 5) i j)
      (fun i => dp (m + 4) i j) (fun i => dp (m + 3) i j)
      (fun i => colOk i j k) (fun i => ih i j)

private abbrev ValidSeq (n : ℕ) (j k : Fin 12) :=
  {s : Fin (n + 2) → Fin 12 //
    (∀ r : Fin n, colOk (s ⟨r.1, by omega⟩) (s ⟨r.1 + 1, by omega⟩) (s ⟨r.1 + 2, by omega⟩) = true) ∧
    s ⟨n, by omega⟩ = j ∧ s ⟨n + 1, by omega⟩ = k}

private lemma card_ValidSeq (n : ℕ) :
    ∀ j k : Fin 12, Fintype.card (ValidSeq n j k) = dp n j k := by
  induction n with
  | zero =>
    intro j k; simp only [dp]
    refine Fintype.card_eq_one_iff.mpr ⟨⟨fun r => if r.1 = 0 then j else k, fun r => r.elim0, rfl, rfl⟩, ?_⟩
    rintro ⟨s, _, hj, hk⟩; apply Subtype.ext; funext r; fin_cases r <;> assumption
  | succ n ih =>
    intro j k; rw [dp_succ_eq]
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
      · rintro ⟨i1, ⟨⟨t1, _, hi1, _⟩, _⟩⟩ ⟨i2, ⟨⟨t2, _, hi2, _⟩, _⟩⟩ heq
        have hfun : (Fin.snoc t1 k : Fin (n + 3) → Fin 12) = Fin.snoc t2 k := congrArg Subtype.val heq
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

private lemma a_eq_sum_dp (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ j : Fin 12, ∑ k : Fin 12, dp n j k := by
  unfold a; rw [if_neg (by omega)]
  let φ : (Σ j : Fin 12, Σ k : Fin 12, ValidSeq n j k) → {A : Fin (n + 2) → Fin 6 → Fin 2 // isValid n A} :=
    fun ⟨_, _, ⟨s, hs, _, _⟩⟩ =>
      ⟨fun r => rowBit (s r), fun r => rowBit_valid (s r),
        fun c r => ((colOk_iff _ _ _).mp (hs r)).1 c,
        fun r c => ((colOk_iff _ _ _).mp (hs r)).2 c⟩
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨j1, k1, ⟨s1, _, hj1, hk1⟩⟩ ⟨j2, k2, ⟨s2, _, hj2, hk2⟩⟩ heq
      have hfun : (fun r => rowBit (s1 r)) = fun r => rowBit (s2 r) := congrArg Subtype.val heq
      have hs_eq : s1 = s2 := by
        funext r
        have := congrArg (fun x => codeToIdx (encodeRow x)) (congrFun hfun r)
        simpa [codeToIdx_encodeRow] using this
      subst hs_eq
      have hj_eq : j1 = j2 := hj1.symm.trans hj2
      have hk_eq : k1 = k2 := hk1.symm.trans hk2
      subst hj_eq; subst hk_eq; rfl
    · rintro ⟨A, hA1, hA2, hA3⟩
      let s : Fin (n + 2) → Fin 12 := fun r => rowEquiv ⟨A r, hA1 r⟩
      have hs : ∀ r : Fin n, colOk (s ⟨r.1, by omega⟩) (s ⟨r.1 + 1, by omega⟩) (s ⟨r.1 + 2, by omega⟩) = true := by
        intro r; rw [colOk_iff]
        have h0 : rowBit (s ⟨r.1, by omega⟩) = A ⟨r.1, by omega⟩ := congrArg Subtype.val (rowEquiv.left_inv ⟨A ⟨r.1, by omega⟩, hA1 _⟩)
        have h1 : rowBit (s ⟨r.1 + 1, by omega⟩) = A ⟨r.1 + 1, by omega⟩ := congrArg Subtype.val (rowEquiv.left_inv ⟨A ⟨r.1 + 1, by omega⟩, hA1 _⟩)
        have h2 : rowBit (s ⟨r.1 + 2, by omega⟩) = A ⟨r.1 + 2, by omega⟩ := congrArg Subtype.val (rowEquiv.left_inv ⟨A ⟨r.1 + 2, by omega⟩, hA1 _⟩)
        rw [h0, h1, h2]; exact ⟨fun c => hA2 c r, fun c => hA3 r c⟩
      refine ⟨⟨s ⟨n, by omega⟩, s ⟨n + 1, by omega⟩, ⟨s, hs, rfl, rfl⟩⟩, ?_⟩
      apply Subtype.ext; funext r
      exact congrArg Subtype.val (rowEquiv.left_inv ⟨A r, hA1 r⟩)
  rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro j _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro k _
  exact card_ValidSeq n j k

private lemma a_rec_m (m : ℕ) :
    a (m + 11) + 6 * a (m + 8) + 2 * a (m + 5) + 2 * a (m + 4) =
    2 * a (m + 10) + 2 * a (m + 9) + 6 * a (m + 6) + a (m + 3) := by
  rw [a_eq_sum_dp (m + 11) (by omega), a_eq_sum_dp (m + 10) (by omega),
      a_eq_sum_dp (m + 9) (by omega), a_eq_sum_dp (m + 8) (by omega),
      a_eq_sum_dp (m + 6) (by omega), a_eq_sum_dp (m + 5) (by omega),
      a_eq_sum_dp (m + 4) (by omega), a_eq_sum_dp (m + 3) (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  exact dp_rec m j k

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_val_1 : a 1 = 338 := by
  rw [a_eq_sum_dp 1 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 1 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_1 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_1 j k
  rw [h]; decide
private lemma a_val_2 : a 2 = 574 := by
  rw [a_eq_sum_dp 2 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 2 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_2 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_2 j k
  rw [h]; decide
private lemma a_val_3 : a 3 = 1102 := by
  rw [a_eq_sum_dp 3 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 3 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_3 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_3 j k
  rw [h]; decide
private lemma a_val_4 : a 4 = 1890 := by
  rw [a_eq_sum_dp 4 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 4 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_4 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_4 j k
  rw [h]; decide
private lemma a_val_5 : a 5 = 3122 := by
  rw [a_eq_sum_dp 5 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 5 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_5 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_5 j k
  rw [h]; decide
private lemma a_val_6 : a 6 = 4822 := by
  rw [a_eq_sum_dp 6 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 6 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_6 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_6 j k
  rw [h]; decide
private lemma a_val_7 : a 7 = 7238 := by
  rw [a_eq_sum_dp 7 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 7 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_7 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_7 j k
  rw [h]; decide
private lemma a_val_8 : a 8 = 10394 := by
  rw [a_eq_sum_dp 8 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 8 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_8 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_8 j k
  rw [h]; decide
private lemma a_val_9 : a 9 = 14602 := by
  rw [a_eq_sum_dp 9 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 9 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_9 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_9 j k
  rw [h]; decide
private lemma a_val_10 : a 10 = 19886 := by
  rw [a_eq_sum_dp 10 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 10 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_10 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_10 j k
  rw [h]; decide
private lemma a_val_11 : a 11 = 26622 := by
  rw [a_eq_sum_dp 11 (by omega)]
  have h : (∑ j : Fin 12, ∑ k : Fin 12, dp 11 j k) = ∑ j : Fin 12, ∑ k : Fin 12, tbl_11 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_11 j k
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

theorem solution : type_of% @OMA.S_oeis_a202443.main := by
  let Pe : ℚ → ℚ := fun x => (2 / 3 : ℚ) * (x ^ 4 + 12 * x ^ 3 + 59 * x ^ 2 + 177 * x + 159)
  let Po : ℚ → ℚ := fun x => (2 / 3 : ℚ) * (x ^ 4 + 12 * x ^ 3 + 59 * x ^ 2 + 183 * x + 168)
  have hclosed : ∀ n : ℕ, 2 ≤ n → (a n : ℚ) = if Even n then Pe n else Po n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
      · omega
      · omega
      · simp [a_val_2]; norm_num
      · have hne : ¬Even 3 := by decide
        simp [hne, a_val_3]; norm_num
      · simp [a_val_4]; norm_num
      · have hne : ¬Even 5 := by decide
        simp [hne, a_val_5]; norm_num
      · simp [a_val_6]; norm_num
      · have hne : ¬Even 7 := by decide
        simp [hne, a_val_7]; norm_num
      · simp [a_val_8]; norm_num
      · have hne : ¬Even 9 := by decide
        simp [hne, a_val_9]; norm_num
      · simp [a_val_10]; norm_num
      · have hr := a_rec_m m
        have hrq : (a (m + 11) : ℚ) + 6 * (a (m + 8) : ℚ) + 2 * (a (m + 5) : ℚ) + 2 * (a (m + 4) : ℚ) =
            2 * (a (m + 10) : ℚ) + 2 * (a (m + 9) : ℚ) + 6 * (a (m + 6) : ℚ) + (a (m + 3) : ℚ) := by
          exact_mod_cast hr
        have h7 := ih (m + 10) (by omega) (by omega)
        have h6 := ih (m + 9) (by omega) (by omega)
        have h5 := ih (m + 8) (by omega) (by omega)
        have h3 := ih (m + 6) (by omega) (by omega)
        have h2 := ih (m + 5) (by omega) (by omega)
        have h1 := ih (m + 4) (by omega) (by omega)
        have h0 := ih (m + 3) (by omega) (by omega)
        rcases Nat.even_or_odd (m + 3) with ⟨r, hr0⟩ | ⟨r, hr0⟩
        · have he0 : Even (m + 3) := ⟨r, hr0⟩
          have ho1 : ¬Even (m + 4) := by intro ⟨t, ht⟩; omega
          have he2 : Even (m + 5) := ⟨r + 1, by omega⟩
          have ho3 : ¬Even (m + 6) := by intro ⟨t, ht⟩; omega
          have ho5 : ¬Even (m + 8) := by intro ⟨t, ht⟩; omega
          have he6 : Even (m + 9) := ⟨r + 3, by omega⟩
          have ho7 : ¬Even (m + 10) := by intro ⟨t, ht⟩; omega
          have he8 : Even (m + 11) := ⟨r + 4, by omega⟩
          simp only [he0, ho1, he2, ho3, ho5, he6, ho7, he8, ↓reduceIte] at h0 h1 h2 h3 h5 h6 h7 ⊢
          rw [h0, h1, h2, h3, h5, h6, h7] at hrq
          dsimp [Pe, Po] at hrq ⊢; push_cast at hrq ⊢; linarith
        · have ho0 : ¬Even (m + 3) := by intro ⟨t, ht⟩; omega
          have he1 : Even (m + 4) := ⟨r + 1, by omega⟩
          have ho2 : ¬Even (m + 5) := by intro ⟨t, ht⟩; omega
          have he3 : Even (m + 6) := ⟨r + 2, by omega⟩
          have he5 : Even (m + 8) := ⟨r + 3, by omega⟩
          have ho6 : ¬Even (m + 9) := by intro ⟨t, ht⟩; omega
          have he7 : Even (m + 10) := ⟨r + 4, by omega⟩
          have ho8 : ¬Even (m + 11) := by intro ⟨t, ht⟩; omega
          simp only [ho0, he1, ho2, he3, he5, ho6, he7, ho8, ↓reduceIte] at h0 h1 h2 h3 h5 h6 h7 ⊢
          rw [h0, h1, h2, h3, h5, h6, h7] at hrq
          dsimp [Pe, Po] at hrq ⊢; push_cast at hrq ⊢; linarith
  have heven : ∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = (2 / 3 : ℚ) * ((n : ℚ) ^ 4 + 12 * (n : ℚ) ^ 3 + 59 * (n : ℚ) ^ 2 + 177 * (n : ℚ) + 159) := by
    intro n hn he
    have hn2 : 2 ≤ n := by rcases he with ⟨r, rfl⟩; omega
    have h := hclosed n hn2
    simpa [he, Pe] using h
  have hodd : ∀ n : ℕ, 1 < n → Odd n → (a n : ℚ) = (2 / 3 : ℚ) * ((n : ℚ) ^ 4 + 12 * (n : ℚ) ^ 3 + 59 * (n : ℚ) ^ 2 + 183 * (n : ℚ) + 168) := by
    intro n hn ho
    have hne : ¬Even n := Nat.not_even_iff_odd.mpr ho
    have h := hclosed n (by omega)
    simpa [hne, Po] using h
  refine ⟨?_, heven, hodd⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 5 * (1 + PowerSeries.X) ^ 2 =
      1 - PowerSeries.C 3 * PowerSeries.X ^ 1 + PowerSeries.X ^ 2 + PowerSeries.C 5 * PowerSeries.X ^ 3 -
      PowerSeries.C 5 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5 + PowerSeries.C 3 * PowerSeries.X ^ 6 - PowerSeries.X ^ 7 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : 2 * (PowerSeries.X : PowerSeries ℚ) * (169 - 220 * PowerSeries.X - 141 * PowerSeries.X ^ 2 + 424 * PowerSeries.X ^ 3 - 133 * PowerSeries.X ^ 4 - 176 * PowerSeries.X ^ 5 + 137 * PowerSeries.X ^ 6 - 28 * PowerSeries.X ^ 7) = PowerSeries.C 338 * PowerSeries.X ^ 1 - PowerSeries.C 440 * PowerSeries.X ^ 2 - PowerSeries.C 282 * PowerSeries.X ^ 3 + PowerSeries.C 848 * PowerSeries.X ^ 4 - PowerSeries.C 266 * PowerSeries.X ^ 5 - PowerSeries.C 352 * PowerSeries.X ^ 6 + PowerSeries.C 274 * PowerSeries.X ^ 7 - PowerSeries.C 56 * PowerSeries.X ^ 8 := by
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
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]
  · simp [a_zero, a_val_1, a_val_2]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7]; norm_num
  · simp [a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8]; norm_num
  · simp only [show 1 ≤ m + 9 by omega, show 2 ≤ m + 9 by omega, show 3 ≤ m + 9 by omega,
      show 4 ≤ m + 9 by omega, show 5 ≤ m + 9 by omega, show 6 ≤ m + 9 by omega, show 7 ≤ m + 9 by omega, ↓reduceIte,
      show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega,
      show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega,
      show m + 9 - 7 = m + 2 by omega,
      show ¬(m + 9 = 1) by omega, show ¬(m + 9 = 2) by omega, show ¬(m + 9 = 3) by omega,
      show ¬(m + 9 = 4) by omega, show ¬(m + 9 = 5) by omega, show ¬(m + 9 = 6) by omega,
      show ¬(m + 9 = 7) by omega, show ¬(m + 9 = 8) by omega]
    have h2 := hclosed (m + 2) (by omega)
    have h3 := hclosed (m + 3) (by omega)
    have h4 := hclosed (m + 4) (by omega)
    have h5 := hclosed (m + 5) (by omega)
    have h6 := hclosed (m + 6) (by omega)
    have h7 := hclosed (m + 7) (by omega)
    have h8 := hclosed (m + 8) (by omega)
    have h9 := hclosed (m + 9) (by omega)
    rcases Nat.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · have he2 : Even (r + r + 2) := ⟨r + 1, by omega⟩
      have ho3 : ¬Even (r + r + 3) := by intro ⟨t, ht⟩; omega
      have he4 : Even (r + r + 4) := ⟨r + 2, by omega⟩
      have ho5 : ¬Even (r + r + 5) := by intro ⟨t, ht⟩; omega
      have he6 : Even (r + r + 6) := ⟨r + 3, by omega⟩
      have ho7 : ¬Even (r + r + 7) := by intro ⟨t, ht⟩; omega
      have he8 : Even (r + r + 8) := ⟨r + 4, by omega⟩
      have ho9 : ¬Even (r + r + 9) := by intro ⟨t, ht⟩; omega
      simp only [he2, ho3, he4, ho5, he6, ho7, he8, ho9, ↓reduceIte] at h2 h3 h4 h5 h6 h7 h8 h9
      rw [h2, h3, h4, h5, h6, h7, h8, h9]; dsimp [Pe, Po]; push_cast; ring
    · have ho2 : ¬Even (2 * r + 1 + 2) := by intro ⟨t, ht⟩; omega
      have he3 : Even (2 * r + 1 + 3) := ⟨r + 2, by omega⟩
      have ho4 : ¬Even (2 * r + 1 + 4) := by intro ⟨t, ht⟩; omega
      have he5 : Even (2 * r + 1 + 5) := ⟨r + 3, by omega⟩
      have ho6 : ¬Even (2 * r + 1 + 6) := by intro ⟨t, ht⟩; omega
      have he7 : Even (2 * r + 1 + 7) := ⟨r + 4, by omega⟩
      have ho8 : ¬Even (2 * r + 1 + 8) := by intro ⟨t, ht⟩; omega
      have he9 : Even (2 * r + 1 + 9) := ⟨r + 5, by omega⟩
      simp only [ho2, he3, ho4, he5, ho6, he7, ho8, he9, ↓reduceIte] at h2 h3 h4 h5 h6 h7 h8 h9
      rw [h2, h3, h4, h5, h6, h7, h8, h9]; dsimp [Pe, Po]; push_cast; ring

end OMA.P_oeis_a202443

theorem OMA.solution : type_of% @OMA.S_oeis_a202443.main :=
  OMA.P_oeis_a202443.solution
