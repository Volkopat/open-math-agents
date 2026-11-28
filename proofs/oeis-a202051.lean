import OMAStatements.S_oeis_a202051

namespace OMA.P_oeis_a202051

open OMA.S_oeis_a202051

private instance (b0 b1 b2 : Fin 2) : Decidable (avoids3 b0 b1 b2) := by
  unfold avoids3; infer_instance

private def rowCode (i : Fin 18) : ℕ :=
  match i.1 with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 10
  | 5 => 21
  | 6 => 42
  | 7 => 85
  | 8 => 170
  | 9 => 341
  | 10 => 426
  | 11 => 469
  | 12 => 490
  | 13 => 501
  | 14 => 506
  | 15 => 509
  | 16 => 510
  | 17 => 511
  | _ => 0

private def bitsOf (m : ℕ) (c : Fin 9) : Fin 2 :=
  ⟨(m / 2 ^ c.1) % 2, Nat.mod_lt _ (by omega)⟩

private def rowBit (i : Fin 18) (c : Fin 9) : Fin 2 :=
  bitsOf (rowCode i) c

private def encodeRow (r : Fin 9 → Fin 2) : ℕ :=
  (r 0).1 + 2 * (r 1).1 + 4 * (r 2).1 + 8 * (r 3).1 + 16 * (r 4).1 + 32 * (r 5).1 + 64 * (r 6).1 + 128 * (r 7).1 + 256 * (r 8).1

private def codeToIdx (m : ℕ) : Fin 18 :=
  match m with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 5 => 3
  | 10 => 4
  | 21 => 5
  | 42 => 6
  | 85 => 7
  | 170 => 8
  | 341 => 9
  | 426 => 10
  | 469 => 11
  | 490 => 12
  | 501 => 13
  | 506 => 14
  | 509 => 15
  | 510 => 16
  | 511 => 17
  | _ => 0

private def rowValid (r : Fin 9 → Fin 2) : Prop :=
  ∀ c : Fin 7, avoids3 (r ⟨c.1, by omega⟩) (r ⟨c.1 + 1, by omega⟩) (r ⟨c.1 + 2, by omega⟩)

private instance (r : Fin 9 → Fin 2) : Decidable (rowValid r) := by
  unfold rowValid avoids3; infer_instance

private lemma rowBit_valid (i : Fin 18) : rowValid (rowBit i) := by
  revert i; decide

private lemma codeToIdx_encodeRow (i : Fin 18) : codeToIdx (encodeRow (rowBit i)) = i := by
  revert i; decide

private lemma encodeRow_lt (r : Fin 9 → Fin 2) : encodeRow r < 512 := by
  unfold encodeRow
  have : ∀ c : Fin 9, (r c).1 < 2 := fun c => (r c).2
  have h0 := this 0 ; have h1 := this 1 ; have h2 := this 2 ; have h3 := this 3 ; have h4 := this 4 ; have h5 := this 5 ; have h6 := this 6 ; have h7 := this 7 ; have h8 := this 8
  omega

private lemma bitsOf_encodeRow (r : Fin 9 → Fin 2) : bitsOf (encodeRow r) = r := by
  funext c
  apply Fin.ext
  unfold bitsOf encodeRow
  have : ∀ j : Fin 9, (r j).1 < 2 := fun j => (r j).2
  have h0 := this 0 ; have h1 := this 1 ; have h2 := this 2 ; have h3 := this 3 ; have h4 := this 4 ; have h5 := this 5 ; have h6 := this 6 ; have h7 := this 7 ; have h8 := this 8
  fin_cases c <;> dsimp <;> omega

private lemma rowBit_codeToIdx (r : Fin 9 → Fin 2) (hr : rowValid r) :
    rowBit (codeToIdx (encodeRow r)) = r := by
  have hall : ∀ (a : Fin 16) (b : Fin 32),
      rowValid (bitsOf (a.1 + 16 * b.1)) →
      rowBit (codeToIdx (a.1 + 16 * b.1)) = bitsOf (a.1 + 16 * b.1) := by
    decide
  have hlt := encodeRow_lt r
  let a : Fin 16 := ⟨encodeRow r % 16, Nat.mod_lt _ (by omega)⟩
  let b : Fin 32 := ⟨encodeRow r / 16, by omega⟩
  have hab : a.1 + 16 * b.1 = encodeRow r := by dsimp [a, b]; omega
  have h1 := hall a b (by rw [hab, bitsOf_encodeRow]; exact hr)
  rw [hab, bitsOf_encodeRow] at h1
  exact h1

private def rowEquiv : {r : Fin 9 → Fin 2 // rowValid r} ≃ Fin 18 where
  toFun r := codeToIdx (encodeRow r.1)
  invFun i := ⟨rowBit i, rowBit_valid i⟩
  left_inv r := Subtype.ext (rowBit_codeToIdx r.1 r.2)
  right_inv i := codeToIdx_encodeRow i

private def colOk (i j k : Fin 18) : Bool :=
  ((rowCode i ^^^ rowCode j ^^^ 511) &&& (rowCode j ^^^ rowCode k)) == 0

private lemma colOk_iff (i j k : Fin 18) :
    colOk i j k = true ↔ ∀ c : Fin 9, avoids3 (rowBit i c) (rowBit j c) (rowBit k c) := by
  revert j k; fin_cases i <;> decide

private def dp : ℕ → Fin 18 → Fin 18 → ℕ
  | 0, _, _ => 1
  | n + 1, j, k => ∑ i : Fin 18, if colOk i j k = true then dp n i j else 0

private lemma dp_succ_eq (n : ℕ) (j k : Fin 18) :
    dp (n + 1) j k = ∑ i : Fin 18, if colOk i j k = true then dp n i j else 0 := rfl

private def tbl_0 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 1 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 2 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 3 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 4 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 5 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 6 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 7 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 8 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 9 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 10 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 11 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 12 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 13 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 14 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 15 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 16 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | 17 => #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k.1 0
  | _ => 0

private def tbl_1 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[18, 9, 9, 8, 8, 7, 7, 6, 6, 5, 5, 4, 4, 3, 3, 2, 2, 1].getD k.1 0
  | 1 => #[9, 18, 8, 9, 7, 8, 6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 1, 2].getD k.1 0
  | 2 => #[9, 8, 18, 7, 9, 6, 8, 5, 7, 4, 6, 3, 5, 2, 4, 1, 3, 2].getD k.1 0
  | 3 => #[8, 9, 7, 18, 6, 9, 5, 8, 4, 7, 3, 6, 2, 5, 1, 4, 2, 3].getD k.1 0
  | 4 => #[8, 7, 9, 6, 18, 5, 9, 4, 8, 3, 7, 2, 6, 1, 5, 2, 4, 3].getD k.1 0
  | 5 => #[7, 8, 6, 9, 5, 18, 4, 9, 3, 8, 2, 7, 1, 6, 2, 5, 3, 4].getD k.1 0
  | 6 => #[7, 6, 8, 5, 9, 4, 18, 3, 9, 2, 8, 1, 7, 2, 6, 3, 5, 4].getD k.1 0
  | 7 => #[6, 7, 5, 8, 4, 9, 3, 18, 2, 9, 1, 8, 2, 7, 3, 6, 4, 5].getD k.1 0
  | 8 => #[6, 5, 7, 4, 8, 3, 9, 2, 18, 1, 9, 2, 8, 3, 7, 4, 6, 5].getD k.1 0
  | 9 => #[5, 6, 4, 7, 3, 8, 2, 9, 1, 18, 2, 9, 3, 8, 4, 7, 5, 6].getD k.1 0
  | 10 => #[5, 4, 6, 3, 7, 2, 8, 1, 9, 2, 18, 3, 9, 4, 8, 5, 7, 6].getD k.1 0
  | 11 => #[4, 5, 3, 6, 2, 7, 1, 8, 2, 9, 3, 18, 4, 9, 5, 8, 6, 7].getD k.1 0
  | 12 => #[4, 3, 5, 2, 6, 1, 7, 2, 8, 3, 9, 4, 18, 5, 9, 6, 8, 7].getD k.1 0
  | 13 => #[3, 4, 2, 5, 1, 6, 2, 7, 3, 8, 4, 9, 5, 18, 6, 9, 7, 8].getD k.1 0
  | 14 => #[3, 2, 4, 1, 5, 2, 6, 3, 7, 4, 8, 5, 9, 6, 18, 7, 9, 8].getD k.1 0
  | 15 => #[2, 3, 1, 4, 2, 5, 3, 6, 4, 7, 5, 8, 6, 9, 7, 18, 8, 9].getD k.1 0
  | 16 => #[2, 1, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6, 8, 7, 9, 8, 18, 9].getD k.1 0
  | 17 => #[1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 18].getD k.1 0
  | _ => 0

private def tbl_2 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[107, 45, 45, 36, 36, 28, 28, 21, 21, 15, 15, 10, 10, 6, 6, 3, 3, 1].getD k.1 0
  | 1 => #[45, 107, 36, 45, 28, 36, 21, 28, 15, 21, 10, 15, 6, 10, 3, 6, 1, 3].getD k.1 0
  | 2 => #[45, 36, 107, 28, 45, 21, 36, 15, 28, 10, 21, 6, 15, 3, 10, 1, 6, 3].getD k.1 0
  | 3 => #[36, 45, 28, 107, 21, 45, 15, 36, 10, 28, 6, 21, 3, 15, 1, 10, 3, 6].getD k.1 0
  | 4 => #[36, 28, 45, 21, 107, 15, 45, 10, 36, 6, 28, 3, 21, 1, 15, 3, 10, 6].getD k.1 0
  | 5 => #[28, 36, 21, 45, 15, 107, 10, 45, 6, 36, 3, 28, 1, 21, 3, 15, 6, 10].getD k.1 0
  | 6 => #[28, 21, 36, 15, 45, 10, 107, 6, 45, 3, 36, 1, 28, 3, 21, 6, 15, 10].getD k.1 0
  | 7 => #[21, 28, 15, 36, 10, 45, 6, 107, 3, 45, 1, 36, 3, 28, 6, 21, 10, 15].getD k.1 0
  | 8 => #[21, 15, 28, 10, 36, 6, 45, 3, 107, 1, 45, 3, 36, 6, 28, 10, 21, 15].getD k.1 0
  | 9 => #[15, 21, 10, 28, 6, 36, 3, 45, 1, 107, 3, 45, 6, 36, 10, 28, 15, 21].getD k.1 0
  | 10 => #[15, 10, 21, 6, 28, 3, 36, 1, 45, 3, 107, 6, 45, 10, 36, 15, 28, 21].getD k.1 0
  | 11 => #[10, 15, 6, 21, 3, 28, 1, 36, 3, 45, 6, 107, 10, 45, 15, 36, 21, 28].getD k.1 0
  | 12 => #[10, 6, 15, 3, 21, 1, 28, 3, 36, 6, 45, 10, 107, 15, 45, 21, 36, 28].getD k.1 0
  | 13 => #[6, 10, 3, 15, 1, 21, 3, 28, 6, 36, 10, 45, 15, 107, 21, 45, 28, 36].getD k.1 0
  | 14 => #[6, 3, 10, 1, 15, 3, 21, 6, 28, 10, 36, 15, 45, 21, 107, 28, 45, 36].getD k.1 0
  | 15 => #[3, 6, 1, 10, 3, 15, 6, 21, 10, 28, 15, 36, 21, 45, 28, 107, 36, 45].getD k.1 0
  | 16 => #[3, 1, 6, 3, 10, 6, 15, 10, 21, 15, 28, 21, 36, 28, 45, 36, 107, 45].getD k.1 0
  | 17 => #[1, 3, 3, 6, 6, 10, 10, 15, 15, 21, 21, 28, 28, 36, 36, 45, 45, 107].getD k.1 0
  | _ => 0

private def tbl_3 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[436, 165, 165, 120, 120, 84, 84, 56, 56, 35, 35, 20, 20, 10, 10, 4, 4, 1].getD k.1 0
  | 1 => #[165, 436, 120, 165, 84, 120, 56, 84, 35, 56, 20, 35, 10, 20, 4, 10, 1, 4].getD k.1 0
  | 2 => #[165, 120, 436, 84, 165, 56, 120, 35, 84, 20, 56, 10, 35, 4, 20, 1, 10, 4].getD k.1 0
  | 3 => #[120, 165, 84, 436, 56, 165, 35, 120, 20, 84, 10, 56, 4, 35, 1, 20, 4, 10].getD k.1 0
  | 4 => #[120, 84, 165, 56, 436, 35, 165, 20, 120, 10, 84, 4, 56, 1, 35, 4, 20, 10].getD k.1 0
  | 5 => #[84, 120, 56, 165, 35, 436, 20, 165, 10, 120, 4, 84, 1, 56, 4, 35, 10, 20].getD k.1 0
  | 6 => #[84, 56, 120, 35, 165, 20, 436, 10, 165, 4, 120, 1, 84, 4, 56, 10, 35, 20].getD k.1 0
  | 7 => #[56, 84, 35, 120, 20, 165, 10, 436, 4, 165, 1, 120, 4, 84, 10, 56, 20, 35].getD k.1 0
  | 8 => #[56, 35, 84, 20, 120, 10, 165, 4, 436, 1, 165, 4, 120, 10, 84, 20, 56, 35].getD k.1 0
  | 9 => #[35, 56, 20, 84, 10, 120, 4, 165, 1, 436, 4, 165, 10, 120, 20, 84, 35, 56].getD k.1 0
  | 10 => #[35, 20, 56, 10, 84, 4, 120, 1, 165, 4, 436, 10, 165, 20, 120, 35, 84, 56].getD k.1 0
  | 11 => #[20, 35, 10, 56, 4, 84, 1, 120, 4, 165, 10, 436, 20, 165, 35, 120, 56, 84].getD k.1 0
  | 12 => #[20, 10, 35, 4, 56, 1, 84, 4, 120, 10, 165, 20, 436, 35, 165, 56, 120, 84].getD k.1 0
  | 13 => #[10, 20, 4, 35, 1, 56, 4, 84, 10, 120, 20, 165, 35, 436, 56, 165, 84, 120].getD k.1 0
  | 14 => #[10, 4, 20, 1, 35, 4, 56, 10, 84, 20, 120, 35, 165, 56, 436, 84, 165, 120].getD k.1 0
  | 15 => #[4, 10, 1, 20, 4, 35, 10, 56, 20, 84, 35, 120, 56, 165, 84, 436, 120, 165].getD k.1 0
  | 16 => #[4, 1, 10, 4, 20, 10, 35, 20, 56, 35, 84, 56, 120, 84, 165, 120, 436, 165].getD k.1 0
  | 17 => #[1, 4, 4, 10, 10, 20, 20, 35, 35, 56, 56, 84, 84, 120, 120, 165, 165, 436].getD k.1 0
  | _ => 0

private def tbl_4 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[1425, 495, 495, 330, 330, 210, 210, 126, 126, 70, 70, 35, 35, 15, 15, 5, 5, 1].getD k.1 0
  | 1 => #[495, 1425, 330, 495, 210, 330, 126, 210, 70, 126, 35, 70, 15, 35, 5, 15, 1, 5].getD k.1 0
  | 2 => #[495, 330, 1425, 210, 495, 126, 330, 70, 210, 35, 126, 15, 70, 5, 35, 1, 15, 5].getD k.1 0
  | 3 => #[330, 495, 210, 1425, 126, 495, 70, 330, 35, 210, 15, 126, 5, 70, 1, 35, 5, 15].getD k.1 0
  | 4 => #[330, 210, 495, 126, 1425, 70, 495, 35, 330, 15, 210, 5, 126, 1, 70, 5, 35, 15].getD k.1 0
  | 5 => #[210, 330, 126, 495, 70, 1425, 35, 495, 15, 330, 5, 210, 1, 126, 5, 70, 15, 35].getD k.1 0
  | 6 => #[210, 126, 330, 70, 495, 35, 1425, 15, 495, 5, 330, 1, 210, 5, 126, 15, 70, 35].getD k.1 0
  | 7 => #[126, 210, 70, 330, 35, 495, 15, 1425, 5, 495, 1, 330, 5, 210, 15, 126, 35, 70].getD k.1 0
  | 8 => #[126, 70, 210, 35, 330, 15, 495, 5, 1425, 1, 495, 5, 330, 15, 210, 35, 126, 70].getD k.1 0
  | 9 => #[70, 126, 35, 210, 15, 330, 5, 495, 1, 1425, 5, 495, 15, 330, 35, 210, 70, 126].getD k.1 0
  | 10 => #[70, 35, 126, 15, 210, 5, 330, 1, 495, 5, 1425, 15, 495, 35, 330, 70, 210, 126].getD k.1 0
  | 11 => #[35, 70, 15, 126, 5, 210, 1, 330, 5, 495, 15, 1425, 35, 495, 70, 330, 126, 210].getD k.1 0
  | 12 => #[35, 15, 70, 5, 126, 1, 210, 5, 330, 15, 495, 35, 1425, 70, 495, 126, 330, 210].getD k.1 0
  | 13 => #[15, 35, 5, 70, 1, 126, 5, 210, 15, 330, 35, 495, 70, 1425, 126, 495, 210, 330].getD k.1 0
  | 14 => #[15, 5, 35, 1, 70, 5, 126, 15, 210, 35, 330, 70, 495, 126, 1425, 210, 495, 330].getD k.1 0
  | 15 => #[5, 15, 1, 35, 5, 70, 15, 126, 35, 210, 70, 330, 126, 495, 210, 1425, 330, 495].getD k.1 0
  | 16 => #[5, 1, 15, 5, 35, 15, 70, 35, 126, 70, 210, 126, 330, 210, 495, 330, 1425, 495].getD k.1 0
  | 17 => #[1, 5, 5, 15, 15, 35, 35, 70, 70, 126, 126, 210, 210, 330, 330, 495, 495, 1425].getD k.1 0
  | _ => 0

private def tbl_5 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[3998, 1287, 1287, 792, 792, 462, 462, 252, 252, 126, 126, 56, 56, 21, 21, 6, 6, 1].getD k.1 0
  | 1 => #[1287, 3998, 792, 1287, 462, 792, 252, 462, 126, 252, 56, 126, 21, 56, 6, 21, 1, 6].getD k.1 0
  | 2 => #[1287, 792, 3998, 462, 1287, 252, 792, 126, 462, 56, 252, 21, 126, 6, 56, 1, 21, 6].getD k.1 0
  | 3 => #[792, 1287, 462, 3998, 252, 1287, 126, 792, 56, 462, 21, 252, 6, 126, 1, 56, 6, 21].getD k.1 0
  | 4 => #[792, 462, 1287, 252, 3998, 126, 1287, 56, 792, 21, 462, 6, 252, 1, 126, 6, 56, 21].getD k.1 0
  | 5 => #[462, 792, 252, 1287, 126, 3998, 56, 1287, 21, 792, 6, 462, 1, 252, 6, 126, 21, 56].getD k.1 0
  | 6 => #[462, 252, 792, 126, 1287, 56, 3998, 21, 1287, 6, 792, 1, 462, 6, 252, 21, 126, 56].getD k.1 0
  | 7 => #[252, 462, 126, 792, 56, 1287, 21, 3998, 6, 1287, 1, 792, 6, 462, 21, 252, 56, 126].getD k.1 0
  | 8 => #[252, 126, 462, 56, 792, 21, 1287, 6, 3998, 1, 1287, 6, 792, 21, 462, 56, 252, 126].getD k.1 0
  | 9 => #[126, 252, 56, 462, 21, 792, 6, 1287, 1, 3998, 6, 1287, 21, 792, 56, 462, 126, 252].getD k.1 0
  | 10 => #[126, 56, 252, 21, 462, 6, 792, 1, 1287, 6, 3998, 21, 1287, 56, 792, 126, 462, 252].getD k.1 0
  | 11 => #[56, 126, 21, 252, 6, 462, 1, 792, 6, 1287, 21, 3998, 56, 1287, 126, 792, 252, 462].getD k.1 0
  | 12 => #[56, 21, 126, 6, 252, 1, 462, 6, 792, 21, 1287, 56, 3998, 126, 1287, 252, 792, 462].getD k.1 0
  | 13 => #[21, 56, 6, 126, 1, 252, 6, 462, 21, 792, 56, 1287, 126, 3998, 252, 1287, 462, 792].getD k.1 0
  | 14 => #[21, 6, 56, 1, 126, 6, 252, 21, 462, 56, 792, 126, 1287, 252, 3998, 462, 1287, 792].getD k.1 0
  | 15 => #[6, 21, 1, 56, 6, 126, 21, 252, 56, 462, 126, 792, 252, 1287, 462, 3998, 792, 1287].getD k.1 0
  | 16 => #[6, 1, 21, 6, 56, 21, 126, 56, 252, 126, 462, 252, 792, 462, 1287, 792, 3998, 1287].getD k.1 0
  | 17 => #[1, 6, 6, 21, 21, 56, 56, 126, 126, 252, 252, 462, 462, 792, 792, 1287, 1287, 3998].getD k.1 0
  | _ => 0

private def tbl_6 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[10003, 3003, 3003, 1716, 1716, 924, 924, 462, 462, 210, 210, 84, 84, 28, 28, 7, 7, 1].getD k.1 0
  | 1 => #[3003, 10003, 1716, 3003, 924, 1716, 462, 924, 210, 462, 84, 210, 28, 84, 7, 28, 1, 7].getD k.1 0
  | 2 => #[3003, 1716, 10003, 924, 3003, 462, 1716, 210, 924, 84, 462, 28, 210, 7, 84, 1, 28, 7].getD k.1 0
  | 3 => #[1716, 3003, 924, 10003, 462, 3003, 210, 1716, 84, 924, 28, 462, 7, 210, 1, 84, 7, 28].getD k.1 0
  | 4 => #[1716, 924, 3003, 462, 10003, 210, 3003, 84, 1716, 28, 924, 7, 462, 1, 210, 7, 84, 28].getD k.1 0
  | 5 => #[924, 1716, 462, 3003, 210, 10003, 84, 3003, 28, 1716, 7, 924, 1, 462, 7, 210, 28, 84].getD k.1 0
  | 6 => #[924, 462, 1716, 210, 3003, 84, 10003, 28, 3003, 7, 1716, 1, 924, 7, 462, 28, 210, 84].getD k.1 0
  | 7 => #[462, 924, 210, 1716, 84, 3003, 28, 10003, 7, 3003, 1, 1716, 7, 924, 28, 462, 84, 210].getD k.1 0
  | 8 => #[462, 210, 924, 84, 1716, 28, 3003, 7, 10003, 1, 3003, 7, 1716, 28, 924, 84, 462, 210].getD k.1 0
  | 9 => #[210, 462, 84, 924, 28, 1716, 7, 3003, 1, 10003, 7, 3003, 28, 1716, 84, 924, 210, 462].getD k.1 0
  | 10 => #[210, 84, 462, 28, 924, 7, 1716, 1, 3003, 7, 10003, 28, 3003, 84, 1716, 210, 924, 462].getD k.1 0
  | 11 => #[84, 210, 28, 462, 7, 924, 1, 1716, 7, 3003, 28, 10003, 84, 3003, 210, 1716, 462, 924].getD k.1 0
  | 12 => #[84, 28, 210, 7, 462, 1, 924, 7, 1716, 28, 3003, 84, 10003, 210, 3003, 462, 1716, 924].getD k.1 0
  | 13 => #[28, 84, 7, 210, 1, 462, 7, 924, 28, 1716, 84, 3003, 210, 10003, 462, 3003, 924, 1716].getD k.1 0
  | 14 => #[28, 7, 84, 1, 210, 7, 462, 28, 924, 84, 1716, 210, 3003, 462, 10003, 924, 3003, 1716].getD k.1 0
  | 15 => #[7, 28, 1, 84, 7, 210, 28, 462, 84, 924, 210, 1716, 462, 3003, 924, 10003, 1716, 3003].getD k.1 0
  | 16 => #[7, 1, 28, 7, 84, 28, 210, 84, 462, 210, 924, 462, 1716, 924, 3003, 1716, 10003, 3003].getD k.1 0
  | 17 => #[1, 7, 7, 28, 28, 84, 84, 210, 210, 462, 462, 924, 924, 1716, 1716, 3003, 3003, 10003].getD k.1 0
  | _ => 0

private def tbl_7 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[22872, 6435, 6435, 3432, 3432, 1716, 1716, 792, 792, 330, 330, 120, 120, 36, 36, 8, 8, 1].getD k.1 0
  | 1 => #[6435, 22872, 3432, 6435, 1716, 3432, 792, 1716, 330, 792, 120, 330, 36, 120, 8, 36, 1, 8].getD k.1 0
  | 2 => #[6435, 3432, 22872, 1716, 6435, 792, 3432, 330, 1716, 120, 792, 36, 330, 8, 120, 1, 36, 8].getD k.1 0
  | 3 => #[3432, 6435, 1716, 22872, 792, 6435, 330, 3432, 120, 1716, 36, 792, 8, 330, 1, 120, 8, 36].getD k.1 0
  | 4 => #[3432, 1716, 6435, 792, 22872, 330, 6435, 120, 3432, 36, 1716, 8, 792, 1, 330, 8, 120, 36].getD k.1 0
  | 5 => #[1716, 3432, 792, 6435, 330, 22872, 120, 6435, 36, 3432, 8, 1716, 1, 792, 8, 330, 36, 120].getD k.1 0
  | 6 => #[1716, 792, 3432, 330, 6435, 120, 22872, 36, 6435, 8, 3432, 1, 1716, 8, 792, 36, 330, 120].getD k.1 0
  | 7 => #[792, 1716, 330, 3432, 120, 6435, 36, 22872, 8, 6435, 1, 3432, 8, 1716, 36, 792, 120, 330].getD k.1 0
  | 8 => #[792, 330, 1716, 120, 3432, 36, 6435, 8, 22872, 1, 6435, 8, 3432, 36, 1716, 120, 792, 330].getD k.1 0
  | 9 => #[330, 792, 120, 1716, 36, 3432, 8, 6435, 1, 22872, 8, 6435, 36, 3432, 120, 1716, 330, 792].getD k.1 0
  | 10 => #[330, 120, 792, 36, 1716, 8, 3432, 1, 6435, 8, 22872, 36, 6435, 120, 3432, 330, 1716, 792].getD k.1 0
  | 11 => #[120, 330, 36, 792, 8, 1716, 1, 3432, 8, 6435, 36, 22872, 120, 6435, 330, 3432, 792, 1716].getD k.1 0
  | 12 => #[120, 36, 330, 8, 792, 1, 1716, 8, 3432, 36, 6435, 120, 22872, 330, 6435, 792, 3432, 1716].getD k.1 0
  | 13 => #[36, 120, 8, 330, 1, 792, 8, 1716, 36, 3432, 120, 6435, 330, 22872, 792, 6435, 1716, 3432].getD k.1 0
  | 14 => #[36, 8, 120, 1, 330, 8, 792, 36, 1716, 120, 3432, 330, 6435, 792, 22872, 1716, 6435, 3432].getD k.1 0
  | 15 => #[8, 36, 1, 120, 8, 330, 36, 792, 120, 1716, 330, 3432, 792, 6435, 1716, 22872, 3432, 6435].getD k.1 0
  | 16 => #[8, 1, 36, 8, 120, 36, 330, 120, 792, 330, 1716, 792, 3432, 1716, 6435, 3432, 22872, 6435].getD k.1 0
  | 17 => #[1, 8, 8, 36, 36, 120, 120, 330, 330, 792, 792, 1716, 1716, 3432, 3432, 6435, 6435, 22872].getD k.1 0
  | _ => 0

private def tbl_8 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[48611, 12870, 12870, 6435, 6435, 3003, 3003, 1287, 1287, 495, 495, 165, 165, 45, 45, 9, 9, 1].getD k.1 0
  | 1 => #[12870, 48611, 6435, 12870, 3003, 6435, 1287, 3003, 495, 1287, 165, 495, 45, 165, 9, 45, 1, 9].getD k.1 0
  | 2 => #[12870, 6435, 48611, 3003, 12870, 1287, 6435, 495, 3003, 165, 1287, 45, 495, 9, 165, 1, 45, 9].getD k.1 0
  | 3 => #[6435, 12870, 3003, 48611, 1287, 12870, 495, 6435, 165, 3003, 45, 1287, 9, 495, 1, 165, 9, 45].getD k.1 0
  | 4 => #[6435, 3003, 12870, 1287, 48611, 495, 12870, 165, 6435, 45, 3003, 9, 1287, 1, 495, 9, 165, 45].getD k.1 0
  | 5 => #[3003, 6435, 1287, 12870, 495, 48611, 165, 12870, 45, 6435, 9, 3003, 1, 1287, 9, 495, 45, 165].getD k.1 0
  | 6 => #[3003, 1287, 6435, 495, 12870, 165, 48611, 45, 12870, 9, 6435, 1, 3003, 9, 1287, 45, 495, 165].getD k.1 0
  | 7 => #[1287, 3003, 495, 6435, 165, 12870, 45, 48611, 9, 12870, 1, 6435, 9, 3003, 45, 1287, 165, 495].getD k.1 0
  | 8 => #[1287, 495, 3003, 165, 6435, 45, 12870, 9, 48611, 1, 12870, 9, 6435, 45, 3003, 165, 1287, 495].getD k.1 0
  | 9 => #[495, 1287, 165, 3003, 45, 6435, 9, 12870, 1, 48611, 9, 12870, 45, 6435, 165, 3003, 495, 1287].getD k.1 0
  | 10 => #[495, 165, 1287, 45, 3003, 9, 6435, 1, 12870, 9, 48611, 45, 12870, 165, 6435, 495, 3003, 1287].getD k.1 0
  | 11 => #[165, 495, 45, 1287, 9, 3003, 1, 6435, 9, 12870, 45, 48611, 165, 12870, 495, 6435, 1287, 3003].getD k.1 0
  | 12 => #[165, 45, 495, 9, 1287, 1, 3003, 9, 6435, 45, 12870, 165, 48611, 495, 12870, 1287, 6435, 3003].getD k.1 0
  | 13 => #[45, 165, 9, 495, 1, 1287, 9, 3003, 45, 6435, 165, 12870, 495, 48611, 1287, 12870, 3003, 6435].getD k.1 0
  | 14 => #[45, 9, 165, 1, 495, 9, 1287, 45, 3003, 165, 6435, 495, 12870, 1287, 48611, 3003, 12870, 6435].getD k.1 0
  | 15 => #[9, 45, 1, 165, 9, 495, 45, 1287, 165, 3003, 495, 6435, 1287, 12870, 3003, 48611, 6435, 12870].getD k.1 0
  | 16 => #[9, 1, 45, 9, 165, 45, 495, 165, 1287, 495, 3003, 1287, 6435, 3003, 12870, 6435, 48611, 12870].getD k.1 0
  | 17 => #[1, 9, 9, 45, 45, 165, 165, 495, 495, 1287, 1287, 3003, 3003, 6435, 6435, 12870, 12870, 48611].getD k.1 0
  | _ => 0

private def tbl_9 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[97230, 24310, 24310, 11440, 11440, 5005, 5005, 2002, 2002, 715, 715, 220, 220, 55, 55, 10, 10, 1].getD k.1 0
  | 1 => #[24310, 97230, 11440, 24310, 5005, 11440, 2002, 5005, 715, 2002, 220, 715, 55, 220, 10, 55, 1, 10].getD k.1 0
  | 2 => #[24310, 11440, 97230, 5005, 24310, 2002, 11440, 715, 5005, 220, 2002, 55, 715, 10, 220, 1, 55, 10].getD k.1 0
  | 3 => #[11440, 24310, 5005, 97230, 2002, 24310, 715, 11440, 220, 5005, 55, 2002, 10, 715, 1, 220, 10, 55].getD k.1 0
  | 4 => #[11440, 5005, 24310, 2002, 97230, 715, 24310, 220, 11440, 55, 5005, 10, 2002, 1, 715, 10, 220, 55].getD k.1 0
  | 5 => #[5005, 11440, 2002, 24310, 715, 97230, 220, 24310, 55, 11440, 10, 5005, 1, 2002, 10, 715, 55, 220].getD k.1 0
  | 6 => #[5005, 2002, 11440, 715, 24310, 220, 97230, 55, 24310, 10, 11440, 1, 5005, 10, 2002, 55, 715, 220].getD k.1 0
  | 7 => #[2002, 5005, 715, 11440, 220, 24310, 55, 97230, 10, 24310, 1, 11440, 10, 5005, 55, 2002, 220, 715].getD k.1 0
  | 8 => #[2002, 715, 5005, 220, 11440, 55, 24310, 10, 97230, 1, 24310, 10, 11440, 55, 5005, 220, 2002, 715].getD k.1 0
  | 9 => #[715, 2002, 220, 5005, 55, 11440, 10, 24310, 1, 97230, 10, 24310, 55, 11440, 220, 5005, 715, 2002].getD k.1 0
  | 10 => #[715, 220, 2002, 55, 5005, 10, 11440, 1, 24310, 10, 97230, 55, 24310, 220, 11440, 715, 5005, 2002].getD k.1 0
  | 11 => #[220, 715, 55, 2002, 10, 5005, 1, 11440, 10, 24310, 55, 97230, 220, 24310, 715, 11440, 2002, 5005].getD k.1 0
  | 12 => #[220, 55, 715, 10, 2002, 1, 5005, 10, 11440, 55, 24310, 220, 97230, 715, 24310, 2002, 11440, 5005].getD k.1 0
  | 13 => #[55, 220, 10, 715, 1, 2002, 10, 5005, 55, 11440, 220, 24310, 715, 97230, 2002, 24310, 5005, 11440].getD k.1 0
  | 14 => #[55, 10, 220, 1, 715, 10, 2002, 55, 5005, 220, 11440, 715, 24310, 2002, 97230, 5005, 24310, 11440].getD k.1 0
  | 15 => #[10, 55, 1, 220, 10, 715, 55, 2002, 220, 5005, 715, 11440, 2002, 24310, 5005, 97230, 11440, 24310].getD k.1 0
  | 16 => #[10, 1, 55, 10, 220, 55, 715, 220, 2002, 715, 5005, 2002, 11440, 5005, 24310, 11440, 97230, 24310].getD k.1 0
  | 17 => #[1, 10, 10, 55, 55, 220, 220, 715, 715, 2002, 2002, 5005, 5005, 11440, 11440, 24310, 24310, 97230].getD k.1 0
  | _ => 0

private def tbl_10 (j k : Fin 18) : ℕ :=
  match j.1 with
  | 0 => #[184745, 43758, 43758, 19448, 19448, 8008, 8008, 3003, 3003, 1001, 1001, 286, 286, 66, 66, 11, 11, 1].getD k.1 0
  | 1 => #[43758, 184745, 19448, 43758, 8008, 19448, 3003, 8008, 1001, 3003, 286, 1001, 66, 286, 11, 66, 1, 11].getD k.1 0
  | 2 => #[43758, 19448, 184745, 8008, 43758, 3003, 19448, 1001, 8008, 286, 3003, 66, 1001, 11, 286, 1, 66, 11].getD k.1 0
  | 3 => #[19448, 43758, 8008, 184745, 3003, 43758, 1001, 19448, 286, 8008, 66, 3003, 11, 1001, 1, 286, 11, 66].getD k.1 0
  | 4 => #[19448, 8008, 43758, 3003, 184745, 1001, 43758, 286, 19448, 66, 8008, 11, 3003, 1, 1001, 11, 286, 66].getD k.1 0
  | 5 => #[8008, 19448, 3003, 43758, 1001, 184745, 286, 43758, 66, 19448, 11, 8008, 1, 3003, 11, 1001, 66, 286].getD k.1 0
  | 6 => #[8008, 3003, 19448, 1001, 43758, 286, 184745, 66, 43758, 11, 19448, 1, 8008, 11, 3003, 66, 1001, 286].getD k.1 0
  | 7 => #[3003, 8008, 1001, 19448, 286, 43758, 66, 184745, 11, 43758, 1, 19448, 11, 8008, 66, 3003, 286, 1001].getD k.1 0
  | 8 => #[3003, 1001, 8008, 286, 19448, 66, 43758, 11, 184745, 1, 43758, 11, 19448, 66, 8008, 286, 3003, 1001].getD k.1 0
  | 9 => #[1001, 3003, 286, 8008, 66, 19448, 11, 43758, 1, 184745, 11, 43758, 66, 19448, 286, 8008, 1001, 3003].getD k.1 0
  | 10 => #[1001, 286, 3003, 66, 8008, 11, 19448, 1, 43758, 11, 184745, 66, 43758, 286, 19448, 1001, 8008, 3003].getD k.1 0
  | 11 => #[286, 1001, 66, 3003, 11, 8008, 1, 19448, 11, 43758, 66, 184745, 286, 43758, 1001, 19448, 3003, 8008].getD k.1 0
  | 12 => #[286, 66, 1001, 11, 3003, 1, 8008, 11, 19448, 66, 43758, 286, 184745, 1001, 43758, 3003, 19448, 8008].getD k.1 0
  | 13 => #[66, 286, 11, 1001, 1, 3003, 11, 8008, 66, 19448, 286, 43758, 1001, 184745, 3003, 43758, 8008, 19448].getD k.1 0
  | 14 => #[66, 11, 286, 1, 1001, 11, 3003, 66, 8008, 286, 19448, 1001, 43758, 3003, 184745, 8008, 43758, 19448].getD k.1 0
  | 15 => #[11, 66, 1, 286, 11, 1001, 66, 3003, 286, 8008, 1001, 19448, 3003, 43758, 8008, 184745, 19448, 43758].getD k.1 0
  | 16 => #[11, 1, 66, 11, 286, 66, 1001, 286, 3003, 1001, 8008, 3003, 19448, 8008, 43758, 19448, 184745, 43758].getD k.1 0
  | 17 => #[1, 11, 11, 66, 66, 286, 286, 1001, 1001, 3003, 3003, 8008, 8008, 19448, 19448, 43758, 43758, 184745].getD k.1 0
  | _ => 0

private lemma dp_eq_tbl_0 (j k : Fin 18) : dp 0 j k = tbl_0 j k := by
  revert j k; decide

private lemma dp_eq_tbl_1 (j k : Fin 18) : dp 1 j k = tbl_1 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 18, if colOk i j k = true then dp 0 i j else 0) =
      ∑ i : Fin 18, if colOk i j k = true then tbl_0 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_0]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_2 (j k : Fin 18) : dp 2 j k = tbl_2 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 18, if colOk i j k = true then dp 1 i j else 0) =
      ∑ i : Fin 18, if colOk i j k = true then tbl_1 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_1]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_3 (j k : Fin 18) : dp 3 j k = tbl_3 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 18, if colOk i j k = true then dp 2 i j else 0) =
      ∑ i : Fin 18, if colOk i j k = true then tbl_2 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_2]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_4 (j k : Fin 18) : dp 4 j k = tbl_4 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 18, if colOk i j k = true then dp 3 i j else 0) =
      ∑ i : Fin 18, if colOk i j k = true then tbl_3 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_3]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_5 (j k : Fin 18) : dp 5 j k = tbl_5 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 18, if colOk i j k = true then dp 4 i j else 0) =
      ∑ i : Fin 18, if colOk i j k = true then tbl_4 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_4]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_6 (j k : Fin 18) : dp 6 j k = tbl_6 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 18, if colOk i j k = true then dp 5 i j else 0) =
      ∑ i : Fin 18, if colOk i j k = true then tbl_5 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_5]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_7 (j k : Fin 18) : dp 7 j k = tbl_7 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 18, if colOk i j k = true then dp 6 i j else 0) =
      ∑ i : Fin 18, if colOk i j k = true then tbl_6 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_6]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_8 (j k : Fin 18) : dp 8 j k = tbl_8 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 18, if colOk i j k = true then dp 7 i j else 0) =
      ∑ i : Fin 18, if colOk i j k = true then tbl_7 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_7]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_9 (j k : Fin 18) : dp 9 j k = tbl_9 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 18, if colOk i j k = true then dp 8 i j else 0) =
      ∑ i : Fin 18, if colOk i j k = true then tbl_8 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_8]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_eq_tbl_10 (j k : Fin 18) : dp 10 j k = tbl_10 j k := by
  rw [dp_succ_eq]
  have h1 : (∑ i : Fin 18, if colOk i j k = true then dp 9 i j else 0) =
      ∑ i : Fin 18, if colOk i j k = true then tbl_9 i j else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [dp_eq_tbl_9]
  rw [h1]
  fin_cases j <;> fin_cases k <;> rfl

private lemma dp_rec_base :
    ∀ j k : Fin 18, dp 10 j k + 45 * dp 8 j k + 210 * dp 6 j k + 210 * dp 4 j k + 45 * dp 2 j k + dp 0 j k = 10 * dp 9 j k + 120 * dp 7 j k + 252 * dp 5 j k + 120 * dp 3 j k + 10 * dp 1 j k := by
  intro j k
  rw [dp_eq_tbl_0, dp_eq_tbl_1, dp_eq_tbl_2, dp_eq_tbl_3, dp_eq_tbl_4, dp_eq_tbl_5, dp_eq_tbl_6, dp_eq_tbl_7, dp_eq_tbl_8, dp_eq_tbl_9, dp_eq_tbl_10]
  revert j k; decide

private lemma sum_lin (f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 : Fin 18 → ℕ) (g : Fin 18 → Bool)
    (h : ∀ i : Fin 18, f10 i + 45 * f8 i + 210 * f6 i + 210 * f4 i + 45 * f2 i + f0 i = 10 * f9 i + 120 * f7 i + 252 * f5 i + 120 * f3 i + 10 * f1 i) :
    (∑ i : Fin 18, if g i = true then f10 i else 0) + 45 * (∑ i : Fin 18, if g i = true then f8 i else 0) + 210 * (∑ i : Fin 18, if g i = true then f6 i else 0) + 210 * (∑ i : Fin 18, if g i = true then f4 i else 0) + 45 * (∑ i : Fin 18, if g i = true then f2 i else 0) + (∑ i : Fin 18, if g i = true then f0 i else 0) = 10 * (∑ i : Fin 18, if g i = true then f9 i else 0) + 120 * (∑ i : Fin 18, if g i = true then f7 i else 0) + 252 * (∑ i : Fin 18, if g i = true then f5 i else 0) + 120 * (∑ i : Fin 18, if g i = true then f3 i else 0) + 10 * (∑ i : Fin 18, if g i = true then f1 i else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  cases g i
  · simp
  · simp only [↓reduceIte]; exact h i

private lemma dp_rec (m : ℕ) :
    ∀ j k : Fin 18, dp (m + 10) j k + 45 * dp (m + 8) j k + 210 * dp (m + 6) j k + 210 * dp (m + 4) j k + 45 * dp (m + 2) j k + dp m j k = 10 * dp (m + 9) j k + 120 * dp (m + 7) j k + 252 * dp (m + 5) j k + 120 * dp (m + 3) j k + 10 * dp (m + 1) j k := by
  induction m with
  | zero => exact dp_rec_base
  | succ m ih =>
    intro j k
    rw [dp_succ_eq (m + 10), dp_succ_eq (m + 9), dp_succ_eq (m + 8), dp_succ_eq (m + 7), dp_succ_eq (m + 6), dp_succ_eq (m + 5), dp_succ_eq (m + 4), dp_succ_eq (m + 3), dp_succ_eq (m + 2), dp_succ_eq (m + 1), dp_succ_eq m]
    exact sum_lin (fun i => dp (m + 10) i j) (fun i => dp (m + 9) i j) (fun i => dp (m + 8) i j) (fun i => dp (m + 7) i j) (fun i => dp (m + 6) i j) (fun i => dp (m + 5) i j) (fun i => dp (m + 4) i j) (fun i => dp (m + 3) i j) (fun i => dp (m + 2) i j) (fun i => dp (m + 1) i j) (fun i => dp m i j) (fun i => colOk i j k) (fun i => ih i j)

private abbrev ValidSeq (n : ℕ) (j k : Fin 18) :=
  {s : Fin (n + 2) → Fin 18 //
    (∀ r : Fin n, colOk (s ⟨r.1, by omega⟩) (s ⟨r.1 + 1, by omega⟩) (s ⟨r.1 + 2, by omega⟩) = true) ∧
    s ⟨n, by omega⟩ = j ∧ s ⟨n + 1, by omega⟩ = k}

private lemma card_ValidSeq (n : ℕ) :
    ∀ j k : Fin 18, Fintype.card (ValidSeq n j k) = dp n j k := by
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
    let φ : (Σ i : Fin 18, {t : ValidSeq n i j // colOk i j k = true}) → ValidSeq (n + 1) j k :=
      fun ⟨i, ⟨⟨t, ht, hti, htj⟩, hok⟩⟩ =>
        let s : Fin (n + 3) → Fin 18 := Fin.snoc t k
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
        have hfun : (Fin.snoc t1 k : Fin (n + 3) → Fin 18) = Fin.snoc t2 k := congrArg Subtype.val heq
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
    a n = ∑ j : Fin 18, ∑ k : Fin 18, dp n j k := by
  unfold a; rw [if_neg (by omega)]
  let φ : (Σ j : Fin 18, Σ k : Fin 18, ValidSeq n j k) → {A : Fin (n + 2) → Fin 9 → Fin 2 // isValid n A} :=
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
      let s : Fin (n + 2) → Fin 18 := fun r => rowEquiv ⟨A r, hA1 r⟩
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
    a (m + 10) + 45 * a (m + 8) + 210 * a (m + 6) + 210 * a (m + 4) + 45 * a (m + 2) + a m = 10 * a (m + 9) + 120 * a (m + 7) + 252 * a (m + 5) + 120 * a (m + 3) + 10 * a (m + 1) := by
  rw [a_eq_sum_dp (m + 10) (by omega), a_eq_sum_dp (m + 9) (by omega), a_eq_sum_dp (m + 8) (by omega), a_eq_sum_dp (m + 7) (by omega), a_eq_sum_dp (m + 6) (by omega), a_eq_sum_dp (m + 5) (by omega), a_eq_sum_dp (m + 4) (by omega), a_eq_sum_dp (m + 3) (by omega), a_eq_sum_dp (m + 2) (by omega), a_eq_sum_dp (m + 1) (by omega), a_eq_sum_dp m hm]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  exact dp_rec m j k

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_val_1 : a 1 = 1926 := by
  rw [a_eq_sum_dp 1 (by omega)]
  have h : (∑ j : Fin 18, ∑ k : Fin 18, dp 1 j k) = ∑ j : Fin 18, ∑ k : Fin 18, tbl_1 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_1 j k
  rw [h]; decide
private lemma a_val_2 : a 2 = 7848 := by
  rw [a_eq_sum_dp 2 (by omega)]
  have h : (∑ j : Fin 18, ∑ k : Fin 18, dp 2 j k) = ∑ j : Fin 18, ∑ k : Fin 18, tbl_2 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_2 j k
  rw [h]; decide
private lemma a_val_3 : a 3 = 25650 := by
  rw [a_eq_sum_dp 3 (by omega)]
  have h : (∑ j : Fin 18, ∑ k : Fin 18, dp 3 j k) = ∑ j : Fin 18, ∑ k : Fin 18, tbl_3 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_3 j k
  rw [h]; decide
private lemma a_val_4 : a 4 = 71964 := by
  rw [a_eq_sum_dp 4 (by omega)]
  have h : (∑ j : Fin 18, ∑ k : Fin 18, dp 4 j k) = ∑ j : Fin 18, ∑ k : Fin 18, tbl_4 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_4 j k
  rw [h]; decide
private lemma a_val_5 : a 5 = 180054 := by
  rw [a_eq_sum_dp 5 (by omega)]
  have h : (∑ j : Fin 18, ∑ k : Fin 18, dp 5 j k) = ∑ j : Fin 18, ∑ k : Fin 18, tbl_5 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_5 j k
  rw [h]; decide
private lemma a_val_6 : a 6 = 411696 := by
  rw [a_eq_sum_dp 6 (by omega)]
  have h : (∑ j : Fin 18, ∑ k : Fin 18, dp 6 j k) = ∑ j : Fin 18, ∑ k : Fin 18, tbl_6 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_6 j k
  rw [h]; decide
private lemma a_val_7 : a 7 = 874998 := by
  rw [a_eq_sum_dp 7 (by omega)]
  have h : (∑ j : Fin 18, ∑ k : Fin 18, dp 7 j k) = ∑ j : Fin 18, ∑ k : Fin 18, tbl_7 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_7 j k
  rw [h]; decide
private lemma a_val_8 : a 8 = 1750140 := by
  rw [a_eq_sum_dp 8 (by omega)]
  have h : (∑ j : Fin 18, ∑ k : Fin 18, dp 8 j k) = ∑ j : Fin 18, ∑ k : Fin 18, tbl_8 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_8 j k
  rw [h]; decide
private lemma a_val_9 : a 9 = 3325410 := by
  rw [a_eq_sum_dp 9 (by omega)]
  have h : (∑ j : Fin 18, ∑ k : Fin 18, dp 9 j k) = ∑ j : Fin 18, ∑ k : Fin 18, tbl_9 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_9 j k
  rw [h]; decide
private lemma a_val_10 : a 10 = 6046344 := by
  rw [a_eq_sum_dp 10 (by omega)]
  have h : (∑ j : Fin 18, ∑ k : Fin 18, dp 10 j k) = ∑ j : Fin 18, ∑ k : Fin 18, tbl_10 j k := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    exact dp_eq_tbl_10 j k
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

theorem solution : type_of% @OMA.S_oeis_a202051.main := by
  have hrec_d : ∀ n : ℕ, 10 < n →
      (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 45 * (a (n - 2) : ℤ) + 120 * (a (n - 3) : ℤ) - 210 * (a (n - 4) : ℤ) + 252 * (a (n - 5) : ℤ) - 210 * (a (n - 6) : ℤ) + 120 * (a (n - 7) : ℤ) - 45 * (a (n - 8) : ℤ) + 10 * (a (n - 9) : ℤ) - (a (n - 10) : ℤ) := by
    intro n hn
    have h := a_rec_d (n - 10) (by omega)
    simp only [show n - 10 + 10 = n by omega, show n - 10 + 9 = n - 1 by omega, show n - 10 + 8 = n - 2 by omega, show n - 10 + 7 = n - 3 by omega, show n - 10 + 6 = n - 4 by omega, show n - 10 + 5 = n - 5 by omega, show n - 10 + 4 = n - 6 by omega, show n - 10 + 3 = n - 7 by omega, show n - 10 + 2 = n - 8 by omega, show n - 10 + 1 = n - 9 by omega] at h
    omega
  refine ⟨?_, hrec_d⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 10 = 1 - PowerSeries.C 10 * PowerSeries.X ^ 1 + PowerSeries.C 45 * PowerSeries.X ^ 2 - PowerSeries.C 120 * PowerSeries.X ^ 3 + PowerSeries.C 210 * PowerSeries.X ^ 4 - PowerSeries.C 252 * PowerSeries.X ^ 5 + PowerSeries.C 210 * PowerSeries.X ^ 6 - PowerSeries.C 120 * PowerSeries.X ^ 7 + PowerSeries.C 45 * PowerSeries.X ^ 8 - PowerSeries.C 10 * PowerSeries.X ^ 9 + PowerSeries.X ^ 10 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : 18 * (PowerSeries.X : PowerSeries ℚ) * (107 - 634 * PowerSeries.X + 1880 * PowerSeries.X ^ 2 - 3472 * PowerSeries.X ^ 3 + 4298 * PowerSeries.X ^ 4 - 3652 * PowerSeries.X ^ 5 + 2114 * PowerSeries.X ^ 6 - 800 * PowerSeries.X ^ 7 + 179 * PowerSeries.X ^ 8 - 18 * PowerSeries.X ^ 9) = PowerSeries.C 1926 * PowerSeries.X ^ 1 - PowerSeries.C 11412 * PowerSeries.X ^ 2 + PowerSeries.C 33840 * PowerSeries.X ^ 3 - PowerSeries.C 62496 * PowerSeries.X ^ 4 + PowerSeries.C 77364 * PowerSeries.X ^ 5 - PowerSeries.C 65736 * PowerSeries.X ^ 6 + PowerSeries.C 38052 * PowerSeries.X ^ 7 - PowerSeries.C 14400 * PowerSeries.X ^ 8 + PowerSeries.C 3222 * PowerSeries.X ^ 9 - PowerSeries.C 324 * PowerSeries.X ^ 10 := by
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
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
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
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10]; try norm_num
  · have hgt : 10 < m + 11 := by omega
    have hr := hrec_d (m + 11) hgt
    have hrq : (a (m + 11) : ℚ) = 10 * (a (m + 10) : ℚ) - 45 * (a (m + 9) : ℚ) + 120 * (a (m + 8) : ℚ) - 210 * (a (m + 7) : ℚ) + 252 * (a (m + 6) : ℚ) - 210 * (a (m + 5) : ℚ) + 120 * (a (m + 4) : ℚ) - 45 * (a (m + 3) : ℚ) + 10 * (a (m + 2) : ℚ) - (a (m + 1) : ℚ) := by
      exact_mod_cast hr
    simp only [show 1 ≤ m + 11 by omega, show 2 ≤ m + 11 by omega, show 3 ≤ m + 11 by omega, show 4 ≤ m + 11 by omega, show 5 ≤ m + 11 by omega, show 6 ≤ m + 11 by omega, show 7 ≤ m + 11 by omega, show 8 ≤ m + 11 by omega, show 9 ≤ m + 11 by omega, show 10 ≤ m + 11 by omega, ↓reduceIte,
      show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega, show m + 11 - 9 = m + 2 by omega, show m + 11 - 10 = m + 1 by omega,
      show ¬(m + 11 = 1) by omega, show ¬(m + 11 = 2) by omega, show ¬(m + 11 = 3) by omega, show ¬(m + 11 = 4) by omega, show ¬(m + 11 = 5) by omega, show ¬(m + 11 = 6) by omega, show ¬(m + 11 = 7) by omega, show ¬(m + 11 = 8) by omega, show ¬(m + 11 = 9) by omega, show ¬(m + 11 = 10) by omega]
    linarith

end OMA.P_oeis_a202051

theorem OMA.solution : type_of% @OMA.S_oeis_a202051.main :=
  OMA.P_oeis_a202051.solution
