import OMAStatements.S_oeis_a283849

namespace OMA.S_oeis_a283849.Proof

open OMA.S_oeis_a283849

private def fastRule (c : Bool) (s : ℕ) : Bool :=
  match c, s with
  | false, 1 | false, 2 | false, 3 => true
  | false, _ => false
  | true, 2 => false
  | true, _ => true

private lemma bool_toNat_le_one (b : Bool) : b.toNat ≤ 1 := by
  cases b <;> decide

private lemma rule734_eq_fastRule (c : Bool) (s : ℕ) (hs : s ≤ 4) :
    (734 : ℕ).testBit (c.toNat + 2 * s) = fastRule c s := by
  cases c <;> interval_cases s <;> rfl

private lemma cell_succ_fast (t : ℕ) (i j : ℤ) :
    cell 734 (t + 1) i j =
      fastRule (cell 734 t i j)
        ((cell 734 t (i + 1) j).toNat + (cell 734 t (i - 1) j).toNat +
         (cell 734 t i (j + 1)).toNat + (cell 734 t i (j - 1)).toNat) := by
  change (734 : ℕ).testBit _ = _
  apply rule734_eq_fastRule
  have b1 := bool_toNat_le_one (cell 734 t (i + 1) j)
  have b2 := bool_toNat_le_one (cell 734 t (i - 1) j)
  have b3 := bool_toNat_le_one (cell 734 t i (j + 1))
  have b4 := bool_toNat_le_one (cell 734 t i (j - 1))
  omega

private lemma fastRule_true_ge3 (s : ℕ) (h : 3 ≤ s) :
    fastRule true s = true := by
  rcases s with _ | _ | _ | s'
  · omega
  · omega
  · omega
  · rfl

private lemma cell_neg_x (t : ℕ) : ∀ i j : ℤ, cell 734 t (-i) j = cell 734 t i j := by
  induction t with
  | zero =>
    intro i j
    simp [cell]
  | succ t ih =>
    intro i j
    simp only [cell_succ_fast]
    have h1 : -i + 1 = -(i - 1) := by ring
    have h2 : -i - 1 = -(i + 1) := by ring
    rw [ih i j, h1, ih (i - 1) j, h2, ih (i + 1) j, ih i (j + 1), ih i (j - 1)]
    congr 1
    omega

private lemma cell_neg_y (t : ℕ) : ∀ i j : ℤ, cell 734 t i (-j) = cell 734 t i j := by
  induction t with
  | zero =>
    intro i j
    simp [cell]
  | succ t ih =>
    intro i j
    simp only [cell_succ_fast]
    have h1 : -j + 1 = -(j - 1) := by ring
    have h2 : -j - 1 = -(j + 1) := by ring
    rw [ih i j, ih (i + 1) j, ih (i - 1) j, h1, ih i (j - 1), h2, ih i (j + 1)]
    congr 1
    omega

private lemma cell_swap (t : ℕ) : ∀ i j : ℤ, cell 734 t j i = cell 734 t i j := by
  induction t with
  | zero =>
    intro i j
    simp [cell, and_comm]
  | succ t ih =>
    intro i j
    simp only [cell_succ_fast]
    rw [ih i j, ih i (j + 1), ih i (j - 1), ih (i + 1) j, ih (i - 1) j]
    congr 1
    omega

private lemma cell_out (t : ℕ) :
    ∀ i j : ℤ, t < i.natAbs + j.natAbs → cell 734 t i j = false := by
  induction t with
  | zero =>
    intro i j h
    have hne : ¬ (i = 0 ∧ j = 0) := by omega
    simp [cell, hne]
  | succ t ih =>
    intro i j h
    rw [cell_succ_fast,
      ih i j (by omega),
      ih (i + 1) j (by omega),
      ih (i - 1) j (by omega),
      ih i (j + 1) (by omega),
      ih i (j - 1) (by omega)]
    rfl

-- Symmetric lookup table for t = 0..21 (stored for 0 <= y <= x, x + y <= t)
private def tblN : ℕ → ℕ → ℕ → Bool
  | 0, 0, x => x == 0
  | 1, 0, x => x == 0 || x == 1
  | 2, 0, x => x == 0 || x == 1 || x == 2
  | 2, 1, x => x == 1
  | 3, 0, x => x == 0 || x == 1 || x == 2 || x == 3
  | 3, 1, x => x == 2
  | 4, 0, x => x == 0 || x == 2 || x == 3 || x == 4
  | 4, 1, x => x == 2 || x == 3
  | 4, 2, x => x == 2
  | 5, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5
  | 5, 1, x => x == 1 || x == 2 || x == 4
  | 5, 2, x => x == 3
  | 6, 0, x => x == 0 || x == 1 || x == 2 || x == 4 || x == 5 || x == 6
  | 6, 1, x => x == 1 || x == 4 || x == 5
  | 6, 2, x => x == 3 || x == 4
  | 6, 3, x => x == 3
  | 7, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7
  | 7, 1, x => x == 2 || x == 3 || x == 4 || x == 6
  | 7, 2, x => x == 2 || x == 5
  | 7, 3, x => x == 4
  | 8, 0, x => x == 0 || x == 2 || x == 3 || x == 4 || x == 6 || x == 7 || x == 8
  | 8, 1, x => x == 2 || x == 3 || x == 6 || x == 7
  | 8, 2, x => x == 3 || x == 4 || x == 5 || x == 6
  | 8, 3, x => x == 3 || x == 4 || x == 5
  | 8, 4, x => x == 4
  | 9, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9
  | 9, 1, x => x == 1 || x == 3 || x == 4 || x == 5 || x == 6 || x == 8
  | 9, 2, x => x == 3 || x == 4 || x == 5 || x == 7
  | 9, 3, x => x == 3 || x == 4 || x == 6
  | 9, 4, x => x == 5
  | 10, 0, x => x == 0 || x == 1 || x == 3 || x == 4 || x == 5 || x == 6 || x == 8 || x == 9 || x == 10
  | 10, 1, x => x == 2 || x == 3 || x == 4 || x == 5 || x == 8 || x == 9
  | 10, 2, x => x == 2 || x == 3 || x == 4 || x == 7 || x == 8
  | 10, 3, x => x == 3 || x == 6 || x == 7
  | 10, 4, x => x == 5 || x == 6
  | 10, 5, x => x == 5
  | 11, 0, x => x == 0 || x == 1 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11
  | 11, 1, x => x == 3 || x == 4 || x == 6 || x == 7 || x == 8 || x == 10
  | 11, 2, x => x == 2 || x == 3 || x == 5 || x == 6 || x == 9
  | 11, 3, x => x == 4 || x == 5 || x == 8
  | 11, 4, x => x == 4 || x == 7
  | 11, 5, x => x == 6
  | 12, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 6 || x == 7 || x == 8 || x == 10 || x == 11 || x == 12
  | 12, 1, x => x == 1 || x == 2 || x == 3 || x == 6 || x == 7 || x == 10 || x == 11
  | 12, 2, x => x == 7 || x == 8 || x == 9 || x == 10
  | 12, 3, x => x == 6 || x == 7 || x == 8 || x == 9
  | 12, 4, x => x == 5 || x == 6 || x == 7 || x == 8
  | 12, 5, x => x == 5 || x == 6 || x == 7
  | 12, 6, x => x == 6
  | 13, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 13
  | 13, 1, x => x == 1 || x == 2 || x == 4 || x == 5 || x == 7 || x == 8 || x == 9 || x == 10 || x == 12
  | 13, 2, x => x == 2 || x == 3 || x == 6 || x == 7 || x == 8 || x == 9 || x == 11
  | 13, 3, x => x == 5 || x == 7 || x == 8 || x == 10
  | 13, 4, x => x == 4 || x == 6 || x == 7 || x == 9
  | 13, 5, x => x == 5 || x == 6 || x == 8
  | 13, 6, x => x == 7
  | 14, 0, x => x == 0 || x == 1 || x == 2 || x == 4 || x == 5 || x == 7 || x == 8 || x == 9 || x == 10 || x == 12 || x == 13 || x == 14
  | 14, 1, x => x == 1 || x == 2 || x == 7 || x == 8 || x == 9 || x == 12 || x == 13
  | 14, 2, x => x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 11 || x == 12
  | 14, 3, x => x == 3 || x == 4 || x == 5 || x == 7 || x == 10 || x == 11
  | 14, 4, x => x == 4 || x == 9 || x == 10
  | 14, 5, x => x == 8 || x == 9
  | 14, 6, x => x == 7 || x == 8
  | 14, 7, x => x == 7
  | 15, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 13 || x == 14 || x == 15
  | 15, 1, x => x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 10 || x == 11 || x == 12 || x == 14
  | 15, 2, x => x == 2 || x == 3 || x == 4 || x == 5 || x == 7 || x == 9 || x == 10 || x == 13
  | 15, 3, x => x == 3 || x == 4 || x == 6 || x == 7 || x == 8 || x == 9 || x == 12
  | 15, 4, x => x == 5 || x == 7 || x == 8 || x == 11
  | 15, 5, x => x == 7 || x == 10
  | 15, 6, x => x == 6 || x == 9
  | 15, 7, x => x == 8
  | 16, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 10 || x == 11 || x == 12 || x == 14 || x == 15 || x == 16
  | 16, 1, x => x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 10 || x == 11 || x == 14 || x == 15
  | 16, 2, x => x == 2 || x == 3 || x == 4 || x == 11 || x == 12 || x == 13 || x == 14
  | 16, 3, x => x == 3 || x == 6 || x == 7 || x == 8 || x == 10 || x == 11 || x == 12 || x == 13
  | 16, 4, x => x == 5 || x == 6 || x == 7 || x == 9 || x == 10 || x == 11 || x == 12
  | 16, 5, x => x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11
  | 16, 6, x => x == 6 || x == 7 || x == 8 || x == 9 || x == 10
  | 16, 7, x => x == 7 || x == 8 || x == 9
  | 16, 8, x => x == 8
  | 17, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 13 || x == 14 || x == 15 || x == 16 || x == 17
  | 17, 1, x => x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 8 || x == 9 || x == 11 || x == 12 || x == 13 || x == 14 || x == 16
  | 17, 2, x => x == 2 || x == 3 || x == 5 || x == 6 || x == 7 || x == 8 || x == 10 || x == 11 || x == 12 || x == 13 || x == 15
  | 17, 3, x => x == 4 || x == 5 || x == 7 || x == 8 || x == 9 || x == 11 || x == 12 || x == 14
  | 17, 4, x => x == 4 || x == 6 || x == 7 || x == 10 || x == 11 || x == 13
  | 17, 5, x => x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 12
  | 17, 6, x => x == 6 || x == 7 || x == 8 || x == 9 || x == 11
  | 17, 7, x => x == 7 || x == 8 || x == 10
  | 17, 8, x => x == 9
  | 18, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 8 || x == 9 || x == 11 || x == 12 || x == 13 || x == 14 || x == 16 || x == 17 || x == 18
  | 18, 1, x => x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 8 || x == 11 || x == 12 || x == 13 || x == 16 || x == 17
  | 18, 2, x => x == 2 || x == 5 || x == 6 || x == 7 || x == 8 || x == 10 || x == 11 || x == 12 || x == 15 || x == 16
  | 18, 3, x => x == 7 || x == 8 || x == 9 || x == 11 || x == 14 || x == 15
  | 18, 4, x => x == 7 || x == 8 || x == 9 || x == 13 || x == 14
  | 18, 5, x => x == 6 || x == 7 || x == 8 || x == 9 || x == 12 || x == 13
  | 18, 6, x => x == 6 || x == 7 || x == 8 || x == 11 || x == 12
  | 18, 7, x => x == 7 || x == 10 || x == 11
  | 18, 8, x => x == 9 || x == 10
  | 18, 9, x => x == 9
  | 19, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 13 || x == 14 || x == 15 || x == 16 || x == 17 || x == 18 || x == 19
  | 19, 1, x => x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 9 || x == 10 || x == 11 || x == 12 || x == 14 || x == 15 || x == 16 || x == 18
  | 19, 2, x => x == 3 || x == 4 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 13 || x == 14 || x == 17
  | 19, 3, x => x == 5 || x == 6 || x == 7 || x == 8 || x == 10 || x == 11 || x == 12 || x == 13 || x == 16
  | 19, 4, x => x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 15
  | 19, 5, x => x == 5 || x == 7 || x == 8 || x == 10 || x == 11 || x == 14
  | 19, 6, x => x == 6 || x == 7 || x == 9 || x == 10 || x == 13
  | 19, 7, x => x == 8 || x == 9 || x == 12
  | 19, 8, x => x == 8 || x == 11
  | 19, 9, x => x == 10
  | 20, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 9 || x == 10 || x == 11 || x == 12 || x == 14 || x == 15 || x == 16 || x == 18 || x == 19 || x == 20
  | 20, 1, x => x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 9 || x == 10 || x == 11 || x == 14 || x == 15 || x == 18 || x == 19
  | 20, 2, x => x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 15 || x == 16 || x == 17 || x == 18
  | 20, 3, x => x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 10 || x == 11 || x == 12 || x == 14 || x == 15 || x == 16 || x == 17
  | 20, 4, x => x == 5 || x == 7 || x == 8 || x == 10 || x == 11 || x == 13 || x == 14 || x == 15 || x == 16
  | 20, 5, x => x == 5 || x == 7 || x == 10 || x == 12 || x == 13 || x == 14 || x == 15
  | 20, 6, x => x == 11 || x == 12 || x == 13 || x == 14
  | 20, 7, x => x == 10 || x == 11 || x == 12 || x == 13
  | 20, 8, x => x == 9 || x == 10 || x == 11 || x == 12
  | 20, 9, x => x == 9 || x == 10 || x == 11
  | 20, 10, x => x == 10
  | 21, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 13 || x == 14 || x == 15 || x == 16 || x == 17 || x == 18 || x == 19 || x == 20 || x == 21
  | 21, 1, x => x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 13 || x == 15 || x == 16 || x == 17 || x == 18 || x == 20
  | 21, 2, x => x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 14 || x == 15 || x == 16 || x == 17 || x == 19
  | 21, 3, x => x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 13 || x == 15 || x == 16 || x == 18
  | 21, 4, x => x == 6 || x == 7 || x == 9 || x == 10 || x == 14 || x == 15 || x == 17
  | 21, 5, x => x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 13 || x == 14 || x == 16
  | 21, 6, x => x == 7 || x == 10 || x == 12 || x == 13 || x == 15
  | 21, 7, x => x == 9 || x == 11 || x == 12 || x == 14
  | 21, 8, x => x == 8 || x == 10 || x == 11 || x == 13
  | 21, 9, x => x == 9 || x == 10 || x == 12
  | 21, 10, x => x == 11
  | _, _, _ => false

private def tblSym (t x y : ℕ) : Bool :=
  if t < x + y then false
  else if y ≤ x then tblN t y x
  else tblN t x y

private def tbl (t : ℕ) (i j : ℤ) : Bool :=
  tblSym t i.natAbs j.natAbs

private def predAbs (n : ℕ) : ℕ :=
  if n = 0 then 1 else n - 1

private lemma natAbs_sub_one (n : ℕ) : ((n : ℤ) - 1).natAbs = predAbs n := by
  cases n <;> simp [predAbs]

private lemma tbl_out (t : ℕ) (i j : ℤ) (h : t < i.natAbs + j.natAbs) :
    tbl t i j = false := by
  simp [tbl, tblSym, h]

private lemma tbl_neg_x (t : ℕ) (i j : ℤ) : tbl t (-i) j = tbl t i j := by
  simp [tbl]

private lemma tbl_neg_y (t : ℕ) (i j : ℤ) : tbl t i (-j) = tbl t i j := by
  simp [tbl]

private lemma tbl_swap (t : ℕ) (i j : ℤ) : tbl t j i = tbl t i j := by
  unfold tbl tblSym
  have hadd : j.natAbs + i.natAbs = i.natAbs + j.natAbs := Nat.add_comm _ _
  rw [hadd]
  by_cases hout : t < i.natAbs + j.natAbs
  · simp [hout]
  · simp only [hout, ↓reduceIte]
    by_cases h1 : i.natAbs ≤ j.natAbs
    · by_cases h2 : j.natAbs ≤ i.natAbs
      · have heq : i.natAbs = j.natAbs := by omega
        simp [heq]
      · simp [h1, h2]
    · have h2 : j.natAbs ≤ i.natAbs := by omega
      simp [h1, h2]

private def stepCheck (t x y : ℕ) : Bool :=
  fastRule (tblSym t x y)
    ((tblSym t (x + 1) y).toNat + (tblSym t (predAbs x) y).toNat +
     (tblSym t x (y + 1)).toNat + (tblSym t x (predAbs y)).toNat) ==
  tblSym (t + 1) x y

private lemma tbl_step_0 : ∀ x : Fin 2, ∀ y : Fin 2, y.1 ≤ x.1 → x.1 + y.1 ≤ 1 → stepCheck 0 x.1 y.1 = true := by decide
private lemma tbl_step_1 : ∀ x : Fin 3, ∀ y : Fin 3, y.1 ≤ x.1 → x.1 + y.1 ≤ 2 → stepCheck 1 x.1 y.1 = true := by decide
private lemma tbl_step_2 : ∀ x : Fin 4, ∀ y : Fin 4, y.1 ≤ x.1 → x.1 + y.1 ≤ 3 → stepCheck 2 x.1 y.1 = true := by decide
private lemma tbl_step_3 : ∀ x : Fin 5, ∀ y : Fin 5, y.1 ≤ x.1 → x.1 + y.1 ≤ 4 → stepCheck 3 x.1 y.1 = true := by decide
private lemma tbl_step_4 : ∀ x : Fin 6, ∀ y : Fin 6, y.1 ≤ x.1 → x.1 + y.1 ≤ 5 → stepCheck 4 x.1 y.1 = true := by decide
private lemma tbl_step_5 : ∀ x : Fin 7, ∀ y : Fin 7, y.1 ≤ x.1 → x.1 + y.1 ≤ 6 → stepCheck 5 x.1 y.1 = true := by decide
private lemma tbl_step_6 : ∀ x : Fin 8, ∀ y : Fin 8, y.1 ≤ x.1 → x.1 + y.1 ≤ 7 → stepCheck 6 x.1 y.1 = true := by decide
private lemma tbl_step_7 : ∀ x : Fin 9, ∀ y : Fin 9, y.1 ≤ x.1 → x.1 + y.1 ≤ 8 → stepCheck 7 x.1 y.1 = true := by decide
private lemma tbl_step_8 : ∀ x : Fin 10, ∀ y : Fin 10, y.1 ≤ x.1 → x.1 + y.1 ≤ 9 → stepCheck 8 x.1 y.1 = true := by decide
private lemma tbl_step_9 : ∀ x : Fin 11, ∀ y : Fin 11, y.1 ≤ x.1 → x.1 + y.1 ≤ 10 → stepCheck 9 x.1 y.1 = true := by decide
private lemma tbl_step_10 : ∀ x : Fin 12, ∀ y : Fin 12, y.1 ≤ x.1 → x.1 + y.1 ≤ 11 → stepCheck 10 x.1 y.1 = true := by decide
private lemma tbl_step_11 : ∀ x : Fin 13, ∀ y : Fin 13, y.1 ≤ x.1 → x.1 + y.1 ≤ 12 → stepCheck 11 x.1 y.1 = true := by decide
private lemma tbl_step_12 : ∀ x : Fin 14, ∀ y : Fin 14, y.1 ≤ x.1 → x.1 + y.1 ≤ 13 → stepCheck 12 x.1 y.1 = true := by decide
private lemma tbl_step_13 : ∀ x : Fin 15, ∀ y : Fin 15, y.1 ≤ x.1 → x.1 + y.1 ≤ 14 → stepCheck 13 x.1 y.1 = true := by decide
private lemma tbl_step_14 : ∀ x : Fin 16, ∀ y : Fin 16, y.1 ≤ x.1 → x.1 + y.1 ≤ 15 → stepCheck 14 x.1 y.1 = true := by decide
private lemma tbl_step_15 : ∀ x : Fin 17, ∀ y : Fin 17, y.1 ≤ x.1 → x.1 + y.1 ≤ 16 → stepCheck 15 x.1 y.1 = true := by decide
private lemma tbl_step_16 : ∀ x : Fin 18, ∀ y : Fin 18, y.1 ≤ x.1 → x.1 + y.1 ≤ 17 → stepCheck 16 x.1 y.1 = true := by decide
private lemma tbl_step_17 : ∀ x : Fin 19, ∀ y : Fin 19, y.1 ≤ x.1 → x.1 + y.1 ≤ 18 → stepCheck 17 x.1 y.1 = true := by decide
private lemma tbl_step_18 : ∀ x : Fin 20, ∀ y : Fin 20, y.1 ≤ x.1 → x.1 + y.1 ≤ 19 → stepCheck 18 x.1 y.1 = true := by decide
private lemma tbl_step_19 : ∀ x : Fin 21, ∀ y : Fin 21, y.1 ≤ x.1 → x.1 + y.1 ≤ 20 → stepCheck 19 x.1 y.1 = true := by decide
private lemma tbl_step_20 : ∀ x : Fin 22, ∀ y : Fin 22, y.1 ≤ x.1 → x.1 + y.1 ≤ 21 → stepCheck 20 x.1 y.1 = true := by decide

private lemma tbl_step_nat (t x y : ℕ) (ht : t < 21) (hyx : y ≤ x) (hxy : x + y ≤ t + 1) :
    fastRule (tblSym t x y)
      ((tblSym t (x + 1) y).toNat + (tblSym t (predAbs x) y).toNat +
       (tblSym t x (y + 1)).toNat + (tblSym t x (predAbs y)).toNat) =
    tblSym (t + 1) x y := by
  have hchk : stepCheck t x y = true := by
    interval_cases t
    · exact tbl_step_0 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_1 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_2 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_3 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_4 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_5 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_6 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_7 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_8 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_9 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_10 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_11 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_12 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_13 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_14 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_15 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_16 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_17 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_18 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_19 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
    · exact tbl_step_20 ⟨x, by omega⟩ ⟨y, by omega⟩ hyx hxy
  simpa [stepCheck] using hchk

private lemma cell_eq_tbl (t : ℕ) (ht : t ≤ 21) :
    ∀ i j : ℤ, cell 734 t i j = tbl t i j := by
  induction t with
  | zero =>
    intro i j
    by_cases h0 : i = 0 ∧ j = 0
    · rcases h0 with ⟨rfl, rfl⟩; rfl
    · have hout : 0 < i.natAbs + j.natAbs := by omega
      rw [cell_out 0 i j hout, tbl_out 0 i j hout]
  | succ t ih =>
    intro i j
    have ih' := ih (by omega)
    by_cases hout : t + 1 < i.natAbs + j.natAbs
    · rw [cell_out (t + 1) i j hout, tbl_out (t + 1) i j hout]
    · have hle : i.natAbs + j.natAbs ≤ t + 1 := by omega
      have hsub : ∀ i' j' : ℤ, 0 ≤ i' → 0 ≤ j' → j'.natAbs ≤ i'.natAbs →
          i'.natAbs + j'.natAbs ≤ t + 1 →
          cell 734 (t + 1) i' j' = tbl (t + 1) i' j' := by
        intro i' j' hi hj hyx hle'
        have hi_eq : (i'.natAbs : ℤ) = i' := Int.natAbs_of_nonneg hi
        have hj_eq : (j'.natAbs : ℤ) = j' := Int.natAbs_of_nonneg hj
        rw [← hi_eq, ← hj_eq, cell_succ_fast, ih', ih', ih', ih', ih']
        unfold tbl
        simp only [Int.natAbs_natCast, natAbs_sub_one,
          show ((i'.natAbs : ℤ) + 1).natAbs = i'.natAbs + 1 by omega,
          show ((j'.natAbs : ℤ) + 1).natAbs = j'.natAbs + 1 by omega]
        exact tbl_step_nat t i'.natAbs j'.natAbs (by omega) hyx hle'
      have hq : ∀ i' j' : ℤ, 0 ≤ i' → 0 ≤ j' → i'.natAbs + j'.natAbs ≤ t + 1 →
          cell 734 (t + 1) i' j' = tbl (t + 1) i' j' := by
        intro i' j' hi hj hle'
        by_cases hyx : j'.natAbs ≤ i'.natAbs
        · exact hsub i' j' hi hj hyx hle'
        · rw [← cell_swap, ← tbl_swap]
          exact hsub j' i' hj hi (by omega) (by omega)
      by_cases hi : 0 ≤ i
      · by_cases hj : 0 ≤ j
        · exact hq i j hi hj hle
        · rw [← cell_neg_y, ← tbl_neg_y]
          exact hq i (-j) hi (by omega) (by simpa using hle)
      · by_cases hj : 0 ≤ j
        · rw [← cell_neg_x, ← tbl_neg_x]
          exact hq (-i) j (by omega) hj (by simpa using hle)
        · rw [← cell_neg_x, ← cell_neg_y, ← tbl_neg_x, ← tbl_neg_y]
          exact hq (-i) (-j) (by omega) (by omega) (by simpa using hle)

-- Period-4 traveling wave patterns indexed by d = t - x
private def patY0 (r d : ℕ) : Bool :=
  match r % 4 with
  | 0 => !(d == 3 || d == 7)
  | 1 => true
  | 2 => !(d == 3 || d == 8)
  | _ => true

private def patY1 (r d : ℕ) : Bool :=
  match r % 4 with
  | 0 => !(d == 0 || d == 3 || d == 4 || d == 7 || d == 8)
  | 1 => !(d == 0 || d == 2 || d == 7)
  | 2 => !(d == 0 || d == 3 || d == 4 || d == 8 || d == 9)
  | _ => !(d == 0 || d == 2 || d == 6)

private def patY2 (r d : ℕ) : Bool :=
  match r % 4 with
  | 0 => !(d == 0 || d == 1 || d == 6 || d == 7 || d == 8)
  | 1 => !(d == 0 || d == 1 || d == 3 || d == 8)
  | 2 => !(d == 0 || d == 1 || d == 4 || d == 5 || d == 9)
  | _ => !(d == 0 || d == 1 || d == 3 || d == 4 || d == 7)

private def dmax3 (r : ℕ) : ℕ := if r % 4 = 3 then 11 else 10
private def dmax4 (r : ℕ) : ℕ := if r % 4 = 2 then 10 else 9

private lemma dmax3_bounds (r : ℕ) : 10 ≤ dmax3 r ∧ dmax3 r ≤ 11 := by
  unfold dmax3; split_ifs <;> omega

private lemma dmax4_bounds (r : ℕ) : 9 ≤ dmax4 r ∧ dmax4 r ≤ 10 := by
  unfold dmax4; split_ifs <;> omega

private def patY3 (r d : ℕ) : Bool :=
  match r % 4 with
  | 0 => d == 3 || d == 4 || d == 5 || d == 6 || d == 8 || d == 9 || d == 10
  | 1 => d == 3 || d == 5 || d == 6 || d == 8 || d == 9 || d == 10
  | 2 => d == 3 || d == 4 || d == 7 || d == 9 || d == 10
  | _ => d == 3 || d == 6 || d == 7 || d == 8 || d == 9 || d == 11

private def patY4 (r d : ℕ) : Bool :=
  match r % 4 with
  | 0 => d == 4 || d == 5 || d == 6 || d == 7 || d == 9
  | 1 => d == 4 || d == 6 || d == 7
  | 2 => d == 4 || d == 5 || d == 9 || d == 10
  | _ => d == 4 || d == 7 || d == 8 || d == 9

private def patDiag (r k : ℕ) : Bool :=
  match r % 4 with
  | 0 => decide (k ≤ 3)
  | 1 => k == 0 || k == 2 || k == 3
  | 2 => k == 0 || k == 1
  | _ => k == 0 || k == 3

private lemma patY0_ge10 (r d : ℕ) (hd : 10 ≤ d) : patY0 r d = true := by
  have hm : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases hm with h | h | h | h <;> unfold patY0 <;> rw [h] <;> simp <;> omega

private lemma patY1_ge10 (r d : ℕ) (hd : 10 ≤ d) : patY1 r d = true := by
  have hm : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases hm with h | h | h | h <;> unfold patY1 <;> rw [h] <;> simp <;> omega

private lemma patY2_ge10 (r d : ℕ) (hd : 10 ≤ d) : patY2 r d = true := by
  have hm : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases hm with h | h | h | h <;> unfold patY2 <;> rw [h] <;> simp <;> omega

private lemma patY2_eq_diag : ∀ r : Fin 4, ∀ k : Fin 4,
    patY2 r.1 (k.1 + 2) = patDiag r.1 k.1 := by decide

private lemma patY0_step : ∀ r : Fin 4, ∀ dn : Fin 12,
    fastRule (if dn.1 = 0 then false else patY0 r.1 (dn.1 - 1))
      ((if dn.1 < 2 then false else patY0 r.1 (dn.1 - 2)).toNat +
       (patY0 r.1 dn.1).toNat +
       (if dn.1 = 0 then false else patY1 r.1 (dn.1 - 1)).toNat +
       (if dn.1 = 0 then false else patY1 r.1 (dn.1 - 1)).toNat) =
    patY0 ((r.1 + 1) % 4) dn.1 := by decide

private lemma patY1_step : ∀ r : Fin 4, ∀ dn : Fin 12,
    fastRule (if dn.1 = 0 then false else patY1 r.1 (dn.1 - 1))
      ((if dn.1 < 2 then false else patY1 r.1 (dn.1 - 2)).toNat +
       (patY1 r.1 dn.1).toNat +
       (if dn.1 = 0 then false else patY2 r.1 (dn.1 - 1)).toNat +
       (if dn.1 = 0 then false else patY0 r.1 (dn.1 - 1)).toNat) =
    patY1 ((r.1 + 1) % 4) dn.1 := by decide

private lemma patY2_step : ∀ r : Fin 4, ∀ dn : Fin 12,
    fastRule (if dn.1 = 0 then false else patY2 r.1 (dn.1 - 1))
      ((if dn.1 < 2 then false else patY2 r.1 (dn.1 - 2)).toNat +
       (patY2 r.1 dn.1).toNat +
       (if dn.1 < 4 then false else patY3 r.1 (dn.1 - 1)).toNat +
       (if dn.1 = 0 then false else patY1 r.1 (dn.1 - 1)).toNat) =
    patY2 ((r.1 + 1) % 4) dn.1 := by decide

private lemma patY3_step : ∀ r : Fin 4, ∀ dn : Fin 12, ∀ u1 u2 : Bool,
    3 ≤ dn.1 → dn.1 ≤ dmax3 ((r.1 + 1) % 4) →
    fastRule (if dn.1 < 4 then false else patY3 r.1 (dn.1 - 1))
      ((if dn.1 < 5 then false else patY3 r.1 (dn.1 - 2)).toNat +
       (if dn.1 ≤ dmax3 r.1 then patY3 r.1 dn.1 else u1).toNat +
       (if dn.1 < 5 then false else if dn.1 - 1 ≤ dmax4 r.1 then patY4 r.1 (dn.1 - 1) else u2).toNat +
       (if dn.1 = 0 then false else patY2 r.1 (dn.1 - 1)).toNat) =
    patY3 ((r.1 + 1) % 4) dn.1 := by decide

private lemma patY4_step : ∀ r : Fin 4, ∀ dn : Fin 11, ∀ u1 u2 : Bool,
    4 ≤ dn.1 → dn.1 ≤ dmax4 ((r.1 + 1) % 4) →
    fastRule (if dn.1 < 5 then false else patY4 r.1 (dn.1 - 1))
      ((if dn.1 < 6 then false else patY4 r.1 (dn.1 - 2)).toNat +
       (if dn.1 ≤ dmax4 r.1 then patY4 r.1 dn.1 else u1).toNat +
       (if dn.1 < 6 then false else if dn.1 - 1 ≤ 8 then patDiag r.1 (dn.1 - 6) else u2).toNat +
       (if dn.1 < 4 then false else patY3 r.1 (dn.1 - 1)).toNat) =
    patY4 ((r.1 + 1) % 4) dn.1 := by decide

private lemma patDiag_step : ∀ r : Fin 4, ∀ k : Fin 4,
    fastRule (if k.1 = 0 then false else patDiag r.1 (k.1 - 1))
      ((if k.1 < 2 then false else patDiag r.1 (k.1 - 2)).toNat +
       (patDiag r.1 k.1).toNat +
       (if k.1 < 2 then false else patDiag r.1 (k.1 - 2)).toNat +
       (patDiag r.1 k.1).toNat) =
    patDiag ((r.1 + 1) % 4) k.1 := by decide

private structure Inv (t : ℕ) : Prop where
  y0 : ∀ x : ℕ, x ≤ t → cell 734 t (x : ℤ) 0 = patY0 (t % 4) (t - x)
  y1 : ∀ x : ℕ, x ≤ t → cell 734 t (x : ℤ) 1 = patY1 (t % 4) (t - x)
  y2 : ∀ x : ℕ, x ≤ t → cell 734 t (x : ℤ) 2 = patY2 (t % 4) (t - x)
  y3 : ∀ d : ℕ, 3 ≤ d → d ≤ dmax3 (t % 4) → cell 734 t ((t - d : ℕ) : ℤ) 3 = patY3 (t % 4) d
  y4 : ∀ d : ℕ, 4 ≤ d → d ≤ dmax4 (t % 4) → cell 734 t ((t - d : ℕ) : ℤ) 4 = patY4 (t % 4) d
  diag : ∀ x y : ℕ, 2 ≤ x → 2 ≤ y → x + y ≤ t → t - (x + y) ≤ 3 →
    cell 734 t (x : ℤ) (y : ℤ) = patDiag (t % 4) (t - (x + y))

-- Base case t = 21 checked via tblSym
private lemma base_y0 : ∀ x : Fin 22, tblSym 21 x.1 0 = patY0 (21 % 4) (21 - x.1) := by decide
private lemma base_y1 : ∀ x : Fin 22, tblSym 21 x.1 1 = patY1 (21 % 4) (21 - x.1) := by decide
private lemma base_y2 : ∀ x : Fin 22, tblSym 21 x.1 2 = patY2 (21 % 4) (21 - x.1) := by decide
private lemma base_y3 : ∀ d : Fin 11, 3 ≤ d.1 → tblSym 21 (21 - d.1) 3 = patY3 (21 % 4) d.1 := by decide
private lemma base_y4 : ∀ d : Fin 10, 4 ≤ d.1 → tblSym 21 (21 - d.1) 4 = patY4 (21 % 4) d.1 := by decide
private lemma base_diag : ∀ x : Fin 22, ∀ y : Fin 22, 2 ≤ x.1 → 2 ≤ y.1 → x.1 + y.1 ≤ 21 → 21 - (x.1 + y.1) ≤ 3 →
    tblSym 21 x.1 y.1 = patDiag (21 % 4) (21 - (x.1 + y.1)) := by decide

private lemma inv_base : Inv 21 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [cell_eq_tbl 21 (by omega)]
    exact base_y0 ⟨x, by omega⟩
  · intro x hx
    rw [cell_eq_tbl 21 (by omega)]
    exact base_y1 ⟨x, by omega⟩
  · intro x hx
    rw [cell_eq_tbl 21 (by omega)]
    exact base_y2 ⟨x, by omega⟩
  · intro d hd1 hd2
    have hd2' : d < 11 := by have : dmax3 (21 % 4) = 10 := rfl; omega
    rw [cell_eq_tbl 21 (by omega)]
    exact base_y3 ⟨d, hd2'⟩ hd1
  · intro d hd1 hd2
    have hd2' : d < 10 := by have : dmax4 (21 % 4) = 9 := rfl; omega
    rw [cell_eq_tbl 21 (by omega)]
    exact base_y4 ⟨d, hd2'⟩ hd1
  · intro x y hx hy hxy hk
    rw [cell_eq_tbl 21 (by omega)]
    exact base_diag ⟨x, by omega⟩ ⟨y, by omega⟩ hx hy hxy hk

private lemma cast_add_one (n : ℕ) : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by omega
private lemma cast_sub_one (n : ℕ) (h : 1 ≤ n) : ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) := by omega

private lemma inv_step (t : ℕ) (ht : 21 ≤ t) (h : Inv t) : Inv (t + 1) := by
  have hmod4 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
  have hdm3 := dmax3_bounds (t % 4)
  have hdm3n := dmax3_bounds ((t + 1) % 4)
  have hdm4 := dmax4_bounds (t % 4)
  have hdm4n := dmax4_bounds ((t + 1) % 4)
  have hy0_next : ∀ x : ℕ, x ≤ t + 1 → cell 734 (t + 1) (x : ℤ) 0 = patY0 ((t + 1) % 4) (t + 1 - x) := by
    intro x hx
    by_cases hbig : 12 ≤ t + 1 - x
    · rw [cell_succ_fast, h.y0 x (by omega), patY0_ge10 _ _ (by omega)]
      have hr : cell 734 t ((x : ℤ) + 1) 0 = true := by
        rw [cast_add_one, h.y0 (x + 1) (by omega), patY0_ge10 _ _ (by omega)]
      have hl : cell 734 t ((x : ℤ) - 1) 0 = true := by
        cases x with
        | zero =>
          have : ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
          rw [this, cell_neg_x, h.y0 1 (by omega), patY0_ge10 _ _ (by omega)]
        | succ x' =>
          have hsub : ((x' + 1 : ℕ) : ℤ) - 1 = (x' : ℤ) := by omega
          rw [hsub, h.y0 x' (by omega), patY0_ge10 _ _ (by omega)]
      have hu : cell 734 t (x : ℤ) ((0 : ℤ) + 1) = true := by
        have : (0 : ℤ) + 1 = 1 := by norm_num
        rw [this, h.y1 x (by omega), patY1_ge10 _ _ (by omega)]
      have hd : cell 734 t (x : ℤ) ((0 : ℤ) - 1) = true := by
        have : (0 : ℤ) - 1 = -(1 : ℤ) := by norm_num
        rw [this, cell_neg_y, h.y1 x (by omega), patY1_ge10 _ _ (by omega)]
      rw [hr, hl, hu, hd, patY0_ge10 _ _ (by omega)]
      rfl
    · set dn := t + 1 - x with hdn_def
      have hdn_lt : dn < 12 := by omega
      have hx1 : 1 ≤ x := by omega
      rw [cell_succ_fast, cast_add_one, cast_sub_one x hx1]
      have h0p : (0 : ℤ) + 1 = 1 := by norm_num
      have h0m : (0 : ℤ) - 1 = -(1 : ℤ) := by norm_num
      rw [h0p, h0m, cell_neg_y]
      have hc : cell 734 t (x : ℤ) 0 = if dn = 0 then false else patY0 (t % 4) (dn - 1) := by
        by_cases h0 : dn = 0
        · simp only [h0, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h0, ↓reduceIte]; rw [h.y0 x (by omega)]; congr 1; omega
      have hr : cell 734 t ((x + 1 : ℕ) : ℤ) 0 = if dn < 2 then false else patY0 (t % 4) (dn - 2) := by
        by_cases h2 : dn < 2
        · simp only [h2, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h2, ↓reduceIte]; rw [h.y0 (x + 1) (by omega)]; congr 1; omega
      have hl : cell 734 t ((x - 1 : ℕ) : ℤ) 0 = patY0 (t % 4) dn := by
        rw [h.y0 (x - 1) (by omega)]; congr 1; omega
      have hv : cell 734 t (x : ℤ) 1 = if dn = 0 then false else patY1 (t % 4) (dn - 1) := by
        by_cases h0 : dn = 0
        · simp only [h0, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h0, ↓reduceIte]; rw [h.y1 x (by omega)]; congr 1; omega
      rw [hc, hr, hl, hv, hmod4]
      exact patY0_step ⟨t % 4, Nat.mod_lt _ (by omega)⟩ ⟨dn, hdn_lt⟩
  have hy1_next : ∀ x : ℕ, x ≤ t + 1 → cell 734 (t + 1) (x : ℤ) 1 = patY1 ((t + 1) % 4) (t + 1 - x) := by
    intro x hx
    by_cases hbig : 12 ≤ t + 1 - x
    · rw [cell_succ_fast, h.y1 x (by omega), patY1_ge10 _ _ (by omega)]
      have hr : cell 734 t ((x : ℤ) + 1) 1 = true := by
        rw [cast_add_one, h.y1 (x + 1) (by omega), patY1_ge10 _ _ (by omega)]
      have hl : cell 734 t ((x : ℤ) - 1) 1 = true := by
        cases x with
        | zero =>
          have : ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
          rw [this, cell_neg_x, h.y1 1 (by omega), patY1_ge10 _ _ (by omega)]
        | succ x' =>
          have hsub : ((x' + 1 : ℕ) : ℤ) - 1 = (x' : ℤ) := by omega
          rw [hsub, h.y1 x' (by omega), patY1_ge10 _ _ (by omega)]
      have hu : cell 734 t (x : ℤ) ((1 : ℤ) + 1) = true := by
        have : (1 : ℤ) + 1 = 2 := by norm_num
        rw [this, h.y2 x (by omega), patY2_ge10 _ _ (by omega)]
      have hd : cell 734 t (x : ℤ) ((1 : ℤ) - 1) = true := by
        have : (1 : ℤ) - 1 = 0 := by norm_num
        rw [this, h.y0 x (by omega), patY0_ge10 _ _ (by omega)]
      rw [hr, hl, hu, hd, patY1_ge10 _ _ (by omega)]
      rfl
    · set dn := t + 1 - x with hdn_def
      have hdn_lt : dn < 12 := by omega
      have hx1 : 1 ≤ x := by omega
      rw [cell_succ_fast, cast_add_one, cast_sub_one x hx1]
      have h1p : (1 : ℤ) + 1 = 2 := by norm_num
      have h1m : (1 : ℤ) - 1 = 0 := by norm_num
      rw [h1p, h1m]
      have hc : cell 734 t (x : ℤ) 1 = if dn = 0 then false else patY1 (t % 4) (dn - 1) := by
        by_cases h0 : dn = 0
        · simp only [h0, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h0, ↓reduceIte]; rw [h.y1 x (by omega)]; congr 1; omega
      have hr : cell 734 t ((x + 1 : ℕ) : ℤ) 1 = if dn < 2 then false else patY1 (t % 4) (dn - 2) := by
        by_cases h2 : dn < 2
        · simp only [h2, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h2, ↓reduceIte]; rw [h.y1 (x + 1) (by omega)]; congr 1; omega
      have hl : cell 734 t ((x - 1 : ℕ) : ℤ) 1 = patY1 (t % 4) dn := by
        rw [h.y1 (x - 1) (by omega)]; congr 1; omega
      have hu : cell 734 t (x : ℤ) 2 = if dn = 0 then false else patY2 (t % 4) (dn - 1) := by
        by_cases h0 : dn = 0
        · simp only [h0, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h0, ↓reduceIte]; rw [h.y2 x (by omega)]; congr 1; omega
      have hd : cell 734 t (x : ℤ) 0 = if dn = 0 then false else patY0 (t % 4) (dn - 1) := by
        by_cases h0 : dn = 0
        · simp only [h0, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h0, ↓reduceIte]; rw [h.y0 x (by omega)]; congr 1; omega
      rw [hc, hr, hl, hu, hd, hmod4]
      exact patY1_step ⟨t % 4, Nat.mod_lt _ (by omega)⟩ ⟨dn, hdn_lt⟩
  have hy2_next : ∀ x : ℕ, x ≤ t + 1 → cell 734 (t + 1) (x : ℤ) 2 = patY2 ((t + 1) % 4) (t + 1 - x) := by
    intro x hx
    by_cases hbig : 12 ≤ t + 1 - x
    · rw [cell_succ_fast, h.y2 x (by omega), patY2_ge10 _ _ (by omega)]
      have hr : cell 734 t ((x : ℤ) + 1) 2 = true := by
        rw [cast_add_one, h.y2 (x + 1) (by omega), patY2_ge10 _ _ (by omega)]
      have hl : cell 734 t ((x : ℤ) - 1) 2 = true := by
        cases x with
        | zero =>
          have : ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
          rw [this, cell_neg_x, h.y2 1 (by omega), patY2_ge10 _ _ (by omega)]
        | succ x' =>
          have hsub : ((x' + 1 : ℕ) : ℤ) - 1 = (x' : ℤ) := by omega
          rw [hsub, h.y2 x' (by omega), patY2_ge10 _ _ (by omega)]
      have hd : cell 734 t (x : ℤ) ((2 : ℤ) - 1) = true := by
        have : (2 : ℤ) - 1 = 1 := by norm_num
        rw [this, h.y1 x (by omega), patY1_ge10 _ _ (by omega)]
      rw [hr, hl, hd, fastRule_true_ge3 _ (by simp), patY2_ge10 _ _ (by omega)]
    · set dn := t + 1 - x with hdn_def
      have hdn_lt : dn < 12 := by omega
      have hx1 : 1 ≤ x := by omega
      rw [cell_succ_fast, cast_add_one, cast_sub_one x hx1]
      have h2p : (2 : ℤ) + 1 = 3 := by norm_num
      have h2m : (2 : ℤ) - 1 = 1 := by norm_num
      rw [h2p, h2m]
      have hc : cell 734 t (x : ℤ) 2 = if dn = 0 then false else patY2 (t % 4) (dn - 1) := by
        by_cases h0 : dn = 0
        · simp only [h0, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h0, ↓reduceIte]; rw [h.y2 x (by omega)]; congr 1; omega
      have hr : cell 734 t ((x + 1 : ℕ) : ℤ) 2 = if dn < 2 then false else patY2 (t % 4) (dn - 2) := by
        by_cases h2 : dn < 2
        · simp only [h2, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h2, ↓reduceIte]; rw [h.y2 (x + 1) (by omega)]; congr 1; omega
      have hl : cell 734 t ((x - 1 : ℕ) : ℤ) 2 = patY2 (t % 4) dn := by
        rw [h.y2 (x - 1) (by omega)]; congr 1; omega
      have hu : cell 734 t (x : ℤ) 3 = if dn < 4 then false else patY3 (t % 4) (dn - 1) := by
        by_cases h4 : dn < 4
        · simp only [h4, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h4, ↓reduceIte]
          have hx_eq : x = t - (dn - 1) := by omega
          have hdm : dn - 1 ≤ dmax3 (t % 4) := by omega
          rw [hx_eq]; exact h.y3 (dn - 1) (by omega) hdm
      have hd : cell 734 t (x : ℤ) 1 = if dn = 0 then false else patY1 (t % 4) (dn - 1) := by
        by_cases h0 : dn = 0
        · simp only [h0, ↓reduceIte]; exact cell_out t _ _ (by omega)
        · simp only [h0, ↓reduceIte]; rw [h.y1 x (by omega)]; congr 1; omega
      rw [hc, hr, hl, hu, hd, hmod4]
      exact patY2_step ⟨t % 4, Nat.mod_lt _ (by omega)⟩ ⟨dn, hdn_lt⟩
  refine ⟨hy0_next, hy1_next, hy2_next, ?_, ?_, ?_⟩
  · -- y3 at t + 1
    intro dn hdn3 hdn_le
    have hdn_lt : dn < 12 := by omega
    set x := t + 1 - dn with hx_def
    have hx1 : 1 ≤ x := by omega
    rw [cell_succ_fast, cast_add_one, cast_sub_one x hx1]
    have h3p : (3 : ℤ) + 1 = 4 := by norm_num
    have h3m : (3 : ℤ) - 1 = 2 := by norm_num
    rw [h3p, h3m]
    have hc : cell 734 t (x : ℤ) 3 = if dn < 4 then false else patY3 (t % 4) (dn - 1) := by
      by_cases h4 : dn < 4
      · simp only [h4, ↓reduceIte]; exact cell_out t _ _ (by omega)
      · simp only [h4, ↓reduceIte]
        have hx_eq : x = t - (dn - 1) := by omega
        have hdm : dn - 1 ≤ dmax3 (t % 4) := by omega
        rw [hx_eq]; exact h.y3 (dn - 1) (by omega) hdm
    have hr : cell 734 t ((x + 1 : ℕ) : ℤ) 3 = if dn < 5 then false else patY3 (t % 4) (dn - 2) := by
      by_cases h5 : dn < 5
      · simp only [h5, ↓reduceIte]; exact cell_out t _ _ (by omega)
      · simp only [h5, ↓reduceIte]
        have hx_eq : x + 1 = t - (dn - 2) := by omega
        have hdm : dn - 2 ≤ dmax3 (t % 4) := by omega
        rw [hx_eq]; exact h.y3 (dn - 2) (by omega) hdm
    have hl : cell 734 t ((x - 1 : ℕ) : ℤ) 3 =
        if dn ≤ dmax3 (t % 4) then patY3 (t % 4) dn else cell 734 t ((x - 1 : ℕ) : ℤ) 3 := by
      by_cases hdm : dn ≤ dmax3 (t % 4)
      · simp only [hdm, ↓reduceIte]
        have hx_eq : x - 1 = t - dn := by omega
        rw [hx_eq]; exact h.y3 dn hdn3 hdm
      · simp only [hdm, ↓reduceIte]
    have hu : cell 734 t (x : ℤ) 4 =
        if dn < 5 then false else if dn - 1 ≤ dmax4 (t % 4) then patY4 (t % 4) (dn - 1) else cell 734 t (x : ℤ) 4 := by
      by_cases h5 : dn < 5
      · simp only [h5, ↓reduceIte]; exact cell_out t _ _ (by omega)
      · simp only [h5, ↓reduceIte]
        by_cases hdm : dn - 1 ≤ dmax4 (t % 4)
        · simp only [hdm, ↓reduceIte]
          have hx_eq : x = t - (dn - 1) := by omega
          rw [hx_eq]; exact h.y4 (dn - 1) (by omega) hdm
        · simp only [hdm, ↓reduceIte]
    have hd : cell 734 t (x : ℤ) 2 = if dn = 0 then false else patY2 (t % 4) (dn - 1) := by
      have h0 : dn ≠ 0 := by omega
      simp only [h0, ↓reduceIte]; rw [h.y2 x (by omega)]; congr 1; omega
    rw [hc, hr, hl, hu, hd, hmod4]
    exact patY3_step ⟨t % 4, Nat.mod_lt _ (by omega)⟩ ⟨dn, hdn_lt⟩ _ _ hdn3 (by rwa [← hmod4])
  · -- y4 at t + 1
    intro dn hdn4 hdn_le
    have hdn_lt : dn < 11 := by omega
    set x := t + 1 - dn with hx_def
    have hx1 : 1 ≤ x := by omega
    rw [cell_succ_fast, cast_add_one, cast_sub_one x hx1]
    have h4p : (4 : ℤ) + 1 = 5 := by norm_num
    have h4m : (4 : ℤ) - 1 = 3 := by norm_num
    rw [h4p, h4m]
    have hc : cell 734 t (x : ℤ) 4 = if dn < 5 then false else patY4 (t % 4) (dn - 1) := by
      by_cases h5 : dn < 5
      · simp only [h5, ↓reduceIte]; exact cell_out t _ _ (by omega)
      · simp only [h5, ↓reduceIte]
        have hx_eq : x = t - (dn - 1) := by omega
        have hdm : dn - 1 ≤ dmax4 (t % 4) := by omega
        rw [hx_eq]; exact h.y4 (dn - 1) (by omega) hdm
    have hr : cell 734 t ((x + 1 : ℕ) : ℤ) 4 = if dn < 6 then false else patY4 (t % 4) (dn - 2) := by
      by_cases h6 : dn < 6
      · simp only [h6, ↓reduceIte]; exact cell_out t _ _ (by omega)
      · simp only [h6, ↓reduceIte]
        have hx_eq : x + 1 = t - (dn - 2) := by omega
        have hdm : dn - 2 ≤ dmax4 (t % 4) := by omega
        rw [hx_eq]; exact h.y4 (dn - 2) (by omega) hdm
    have hl : cell 734 t ((x - 1 : ℕ) : ℤ) 4 =
        if dn ≤ dmax4 (t % 4) then patY4 (t % 4) dn else cell 734 t ((x - 1 : ℕ) : ℤ) 4 := by
      by_cases hdm : dn ≤ dmax4 (t % 4)
      · simp only [hdm, ↓reduceIte]
        have hx_eq : x - 1 = t - dn := by omega
        rw [hx_eq]; exact h.y4 dn hdn4 hdm
      · simp only [hdm, ↓reduceIte]
    have hu : cell 734 t (x : ℤ) 5 =
        if dn < 6 then false else if dn - 1 ≤ 8 then patDiag (t % 4) (dn - 6) else cell 734 t (x : ℤ) 5 := by
      by_cases h6 : dn < 6
      · simp only [h6, ↓reduceIte]; exact cell_out t _ _ (by omega)
      · simp only [h6, ↓reduceIte]
        by_cases h8 : dn - 1 ≤ 8
        · simp only [h8, ↓reduceIte]
          have h5 : (5 : ℤ) = ((5 : ℕ) : ℤ) := rfl
          rw [h5, h.diag x 5 (by omega) (by omega) (by omega) (by omega)]
          congr 1; omega
        · simp only [h8, ↓reduceIte]
    have hd : cell 734 t (x : ℤ) 3 = if dn < 4 then false else patY3 (t % 4) (dn - 1) := by
      have h4 : ¬ dn < 4 := by omega
      simp only [h4, ↓reduceIte]
      have hx_eq : x = t - (dn - 1) := by omega
      have hdm : dn - 1 ≤ dmax3 (t % 4) := by omega
      rw [hx_eq]; exact h.y3 (dn - 1) (by omega) hdm
    rw [hc, hr, hl, hu, hd, hmod4]
    exact patY4_step ⟨t % 4, Nat.mod_lt _ (by omega)⟩ ⟨dn, hdn_lt⟩ _ _ hdn4 (by rwa [← hmod4])
  · -- diag at t + 1
    intro x y hx hy hxy hk
    by_cases hy2 : y = 2
    · subst hy2
      have h2 : ((2 : ℕ) : ℤ) = 2 := rfl
      rw [h2, hy2_next x (by omega)]
      set k := t + 1 - (x + 2)
      have heq : t + 1 - x = k + 2 := by omega
      rw [heq]
      exact patY2_eq_diag ⟨(t + 1) % 4, Nat.mod_lt _ (by omega)⟩ ⟨k, by omega⟩
    · by_cases hx2 : x = 2
      · subst hx2
        rw [← cell_swap]
        have h2 : ((2 : ℕ) : ℤ) = 2 := rfl
        rw [h2, hy2_next y (by omega)]
        set k := t + 1 - (2 + y)
        have heq : t + 1 - y = k + 2 := by omega
        rw [heq]
        exact patY2_eq_diag ⟨(t + 1) % 4, Nat.mod_lt _ (by omega)⟩ ⟨k, by omega⟩
      · set k := t + 1 - (x + y) with hk_def
        rw [cell_succ_fast, cast_add_one, cast_sub_one x (by omega), cast_add_one, cast_sub_one y (by omega)]
        have hc : cell 734 t (x : ℤ) (y : ℤ) = if k = 0 then false else patDiag (t % 4) (k - 1) := by
          by_cases h0 : k = 0
          · simp only [h0, ↓reduceIte]; exact cell_out t _ _ (by omega)
          · simp only [h0, ↓reduceIte]; rw [h.diag x y (by omega) (by omega) (by omega) (by omega)]; congr 1; omega
        have hr : cell 734 t ((x + 1 : ℕ) : ℤ) (y : ℤ) = if k < 2 then false else patDiag (t % 4) (k - 2) := by
          by_cases h2 : k < 2
          · simp only [h2, ↓reduceIte]; exact cell_out t _ _ (by omega)
          · simp only [h2, ↓reduceIte]; rw [h.diag (x + 1) y (by omega) (by omega) (by omega) (by omega)]; congr 1; omega
        have hu : cell 734 t (x : ℤ) ((y + 1 : ℕ) : ℤ) = if k < 2 then false else patDiag (t % 4) (k - 2) := by
          by_cases h2 : k < 2
          · simp only [h2, ↓reduceIte]; exact cell_out t _ _ (by omega)
          · simp only [h2, ↓reduceIte]; rw [h.diag x (y + 1) (by omega) (by omega) (by omega) (by omega)]; congr 1; omega
        have hl : cell 734 t ((x - 1 : ℕ) : ℤ) (y : ℤ) = patDiag (t % 4) k := by
          rw [h.diag (x - 1) y (by omega) (by omega) (by omega) (by omega)]; congr 1; omega
        have hd : cell 734 t (x : ℤ) ((y - 1 : ℕ) : ℤ) = patDiag (t % 4) k := by
          rw [h.diag x (y - 1) (by omega) (by omega) (by omega) (by omega)]; congr 1; omega
        rw [hc, hr, hl, hu, hd, hmod4]
        exact patDiag_step ⟨t % 4, Nat.mod_lt _ (by omega)⟩ ⟨k, by omega⟩

private lemma inv_ge21 (t : ℕ) (ht : 21 ≤ t) : Inv t := by
  induction t, ht using Nat.le_induction with
  | base => exact inv_base
  | succ k hk ih => exact inv_step k hk ih

-- Closed form for a(n) for n >= 21
private def S (m : ℕ) : ℤ := ∑ k ∈ Finset.range m, (10 : ℤ) ^ k

private def K (r : ℕ) : ℤ :=
  match r % 4 with
  | 0 => 100010
  | 1 => 0
  | 2 => 100001
  | _ => 0

private lemma sum_reflect_ten (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (10 : ℤ) ^ (n - k) = S (n + 1) := by
  have h := Finset.sum_range_reflect (fun k => (10 : ℤ) ^ k) (n + 1)
  simpa [S, Nat.add_sub_cancel] using h

private lemma a_eq_S_sub_K (n : ℕ) (hn : 21 ≤ n) :
    a n = S (n + 1) - (10 : ℤ) ^ (n - 8) * K n := by
  have hinv := (inv_ge21 n hn).y0
  unfold a
  have hsplit :
      (∑ k ∈ Finset.range (n + 1), if cell 734 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0) +
      (∑ k ∈ Finset.range (n + 1), if cell 734 n ((k : ℤ) - n) 0 then 0 else (10 : ℤ) ^ (n - k)) =
      S (n + 1) := by
    rw [← Finset.sum_add_distrib, ← sum_reflect_ten n]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  have hoff :
      (∑ k ∈ Finset.range (n + 1), if cell 734 n ((k : ℤ) - n) 0 then 0 else (10 : ℤ) ^ (n - k)) =
      (10 : ℤ) ^ (n - 8) * K n := by
    have hcongr :
        (∑ k ∈ Finset.range (n + 1), if cell 734 n ((k : ℤ) - n) 0 then 0 else (10 : ℤ) ^ (n - k)) =
        (∑ k ∈ Finset.range (n + 1), if patY0 (n % 4) k then 0 else (10 : ℤ) ^ (n - k)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      have hneg : (k : ℤ) - n = -((n - k : ℕ) : ℤ) := by omega
      rw [hneg, cell_neg_x, hinv (n - k) (by omega), show n - (n - k) = k by omega]
    rw [hcongr]
    have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hmod with hm | hm | hm | hm
    · have hsub : ({3, 7} : Finset ℕ) ⊆ Finset.range (n + 1) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [Finset.mem_range]; omega
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_pair (by omega)]
        have hs1 : patY0 (n % 4) 3 = false := by unfold patY0; rw [hm]; rfl
        have hs2 : patY0 (n % 4) 7 = false := by unfold patY0; rw [hm]; rfl
        rw [hs1, hs2]; unfold K; rw [hm]
        have hp1 : n - 3 = (n - 8) + 5 := by omega
        have hp2 : n - 7 = (n - 8) + 1 := by omega
        rw [hp1, hp2, pow_add, pow_add]
        simp only [Bool.false_eq_true, ↓reduceIte]; ring
      · intro k hk hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        have hs : patY0 (n % 4) k = true := by unfold patY0; rw [hm]; simp; omega
        rw [hs]; rfl
    · unfold K; rw [hm]; simp only [mul_zero]
      apply Finset.sum_eq_zero
      intro k _
      change (if true = true then (0 : ℤ) else (10 : ℤ) ^ (n - k)) = 0
      rfl
    · have hsub : ({3, 8} : Finset ℕ) ⊆ Finset.range (n + 1) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [Finset.mem_range]; omega
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_pair (by omega)]
        have hs1 : patY0 (n % 4) 3 = false := by unfold patY0; rw [hm]; rfl
        have hs2 : patY0 (n % 4) 8 = false := by unfold patY0; rw [hm]; rfl
        rw [hs1, hs2]; unfold K; rw [hm]
        have hp1 : n - 3 = (n - 8) + 5 := by omega
        rw [hp1, pow_add]
        simp only [Bool.false_eq_true, ↓reduceIte]; ring
      · intro k hk hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        have hs : patY0 (n % 4) k = true := by unfold patY0; rw [hm]; simp; omega
        rw [hs]; rfl
    · unfold K; rw [hm]; simp only [mul_zero]
      apply Finset.sum_eq_zero
      intro k _
      change (if true = true then (0 : ℤ) else (10 : ℤ) ^ (n - k)) = 0
      rfl
  linarith

private lemma a_rec_int (n : ℕ) (hn : 26 ≤ n) :
    a n = a (n - 1) + 10000 * a (n - 4) - 10000 * a (n - 5) := by
  rw [a_eq_S_sub_K n (by omega),
      a_eq_S_sub_K (n - 1) (by omega),
      a_eq_S_sub_K (n - 4) (by omega),
      a_eq_S_sub_K (n - 5) (by omega)]
  have hS1 : S (n + 1) - S (n - 1 + 1) = (10 : ℤ) ^ n := by
    have h1 : n - 1 + 1 = n := by omega
    rw [h1]; unfold S; rw [Finset.sum_range_succ]; ring
  have hS2 : S (n - 4 + 1) - S (n - 5 + 1) = (10 : ℤ) ^ (n - 4) := by
    have h1 : n - 5 + 1 = n - 4 := by omega
    have h2 : n - 4 + 1 = (n - 4) + 1 := rfl
    rw [h1, h2]; unfold S; rw [Finset.sum_range_succ]; ring
  have hK1 : K n = K (n - 4) := by
    unfold K
    have hm : n % 4 = (n - 4) % 4 := by omega
    rw [hm]
  have hK2 : K (n - 1) = K (n - 5) := by
    unfold K
    have hm : (n - 1) % 4 = (n - 5) % 4 := by omega
    rw [hm]
  have hp0 : (10 : ℤ) ^ n = 10000 * (10 : ℤ) ^ (n - 4) := by
    have he : n = (n - 4) + 4 := by omega
    conv_lhs => rw [he]
    rw [pow_add]; ring
  have hp1 : (10 : ℤ) ^ (n - 8) = 10000 * (10 : ℤ) ^ (n - 4 - 8) := by
    have he : n - 8 = (n - 4 - 8) + 4 := by omega
    conv_lhs => rw [he]
    rw [pow_add]; ring
  have hp2 : (10 : ℤ) ^ (n - 1 - 8) = 10000 * (10 : ℤ) ^ (n - 5 - 8) := by
    have he : n - 1 - 8 = (n - 5 - 8) + 4 := by omega
    conv_lhs => rw [he]
    rw [pow_add]; ring
  rw [hK1, hK2, hp1, hp2]
  linarith

private lemma a_rec_rat (n : ℕ) (hn : 26 ≤ n) :
    (a n : ℚ) = a (n - 1) + 10000 * a (n - 4) - 10000 * a (n - 5) := by
  exact_mod_cast a_rec_int n hn

-- Concrete values a(0)..a(25)
private lemma a_eq_tbl_sum (n : ℕ) (hn : n ≤ 21) :
    a n = ∑ k ∈ Finset.range (n + 1), if tblN n 0 (n - k) then (10 : ℤ) ^ (n - k) else 0 := by
  unfold a
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hneg : (k : ℤ) - n = -((n - k : ℕ) : ℤ) := by omega
  rw [hneg, cell_neg_x, cell_eq_tbl n hn]
  have hsym : tbl n ((n - k : ℕ) : ℤ) 0 = tblN n 0 (n - k) := by
    unfold tbl tblSym
    simp only [Int.natAbs_natCast, Int.natAbs_zero, Nat.add_zero, Nat.zero_le, ↓reduceIte]
    have hle : ¬ n < n - k := by omega
    simp [hle]
  rw [hsym]

private def sumRowNat (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => sumRowNat n m + if tblN n 0 (n - m) then 10 ^ (n - m) else 0

private lemma sum_eq_sumRowNat (n m : ℕ) :
    (∑ k ∈ Finset.range m, if tblN n 0 (n - k) then (10 : ℤ) ^ (n - k) else 0) =
    (sumRowNat n m : ℤ) := by
  induction m with
  | zero => simp [sumRowNat]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [sumRowNat]
    split_ifs <;> push_cast <;> ring

private lemma a_eq_sumRowNat (n : ℕ) (hn : n ≤ 21) :
    a n = (sumRowNat n (n + 1) : ℤ) := by
  rw [a_eq_tbl_sum n hn, sum_eq_sumRowNat]

private lemma a_0 : a 0 = 1 := by
  have h : sumRowNat 0 (0 + 1) = 1 := rfl
  rw [a_eq_sumRowNat 0 (by omega), h]; rfl

private lemma a_1 : a 1 = 11 := by
  have h : sumRowNat 1 (1 + 1) = 11 := rfl
  rw [a_eq_sumRowNat 1 (by omega), h]; rfl

private lemma a_2 : a 2 = 111 := by
  have h : sumRowNat 2 (2 + 1) = 111 := rfl
  rw [a_eq_sumRowNat 2 (by omega), h]; rfl

private lemma a_3 : a 3 = 1111 := by
  have h : sumRowNat 3 (3 + 1) = 1111 := rfl
  rw [a_eq_sumRowNat 3 (by omega), h]; rfl

private lemma a_4 : a 4 = 11101 := by
  have h : sumRowNat 4 (4 + 1) = 11101 := rfl
  rw [a_eq_sumRowNat 4 (by omega), h]; rfl

private lemma a_5 : a 5 = 111111 := by
  have h : sumRowNat 5 (5 + 1) = 111111 := rfl
  rw [a_eq_sumRowNat 5 (by omega), h]; rfl

private lemma a_6 : a 6 = 1110111 := by
  have h : sumRowNat 6 (6 + 1) = 1110111 := rfl
  rw [a_eq_sumRowNat 6 (by omega), h]; rfl

private lemma a_7 : a 7 = 11111111 := by
  have h : sumRowNat 7 (7 + 1) = 11111111 := rfl
  rw [a_eq_sumRowNat 7 (by omega), h]; rfl

private lemma a_8 : a 8 = 111011101 := by
  have h : sumRowNat 8 (8 + 1) = 111011101 := rfl
  rw [a_eq_sumRowNat 8 (by omega), h]; rfl

private lemma a_9 : a 9 = 1111111111 := by
  have h : sumRowNat 9 (9 + 1) = 1111111111 := rfl
  rw [a_eq_sumRowNat 9 (by omega), h]; rfl

private lemma a_10 : a 10 = 11101111011 := by
  have h : sumRowNat 10 (10 + 1) = 11101111011 := rfl
  rw [a_eq_sumRowNat 10 (by omega), h]; rfl

private lemma a_11 : a 11 = 111111111011 := by
  have h : sumRowNat 11 (11 + 1) = 111111111011 := rfl
  rw [a_eq_sumRowNat 11 (by omega), h]; rfl

private lemma a_12 : a 12 = 1110111011111 := by
  have h : sumRowNat 12 (12 + 1) = 1110111011111 := rfl
  rw [a_eq_sumRowNat 12 (by omega), h]; rfl

private lemma a_13 : a 13 = 11111111111111 := by
  have h : sumRowNat 13 (13 + 1) = 11111111111111 := rfl
  rw [a_eq_sumRowNat 13 (by omega), h]; rfl

private lemma a_14 : a 14 = 111011110110111 := by
  have h : sumRowNat 14 (14 + 1) = 111011110110111 := rfl
  rw [a_eq_sumRowNat 14 (by omega), h]; rfl

private lemma a_15 : a 15 = 1111111111111111 := by
  have h : sumRowNat 15 (15 + 1) = 1111111111111111 := rfl
  rw [a_eq_sumRowNat 15 (by omega), h]; rfl

private lemma a_16 : a 16 = 11101110111111111 := by
  have h : sumRowNat 16 (16 + 1) = 11101110111111111 := rfl
  rw [a_eq_sumRowNat 16 (by omega), h]; rfl

private lemma a_17 : a 17 = 111111111111111111 := by
  have h : sumRowNat 17 (17 + 1) = 111111111111111111 := rfl
  rw [a_eq_sumRowNat 17 (by omega), h]; rfl

private lemma a_18 : a 18 = 1110111101101111111 := by
  have h : sumRowNat 18 (18 + 1) = 1110111101101111111 := rfl
  rw [a_eq_sumRowNat 18 (by omega), h]; rfl

private lemma a_19 : a 19 = 11111111111111111111 := by
  have h : sumRowNat 19 (19 + 1) = 11111111111111111111 := rfl
  rw [a_eq_sumRowNat 19 (by omega), h]; rfl

private lemma a_20 : a 20 = 111011101111011111111 := by
  have h : sumRowNat 20 (20 + 1) = 111011101111011111111 := rfl
  rw [a_eq_sumRowNat 20 (by omega), h]; rfl

private lemma a_21 : a 21 = 1111111111111111111111 := by
  have h : sumRowNat 21 (21 + 1) = 1111111111111111111111 := rfl
  rw [a_eq_sumRowNat 21 (by omega), h]; rfl

private lemma S_22 : S 22 = 1111111111111111111111 := by
  have h := a_eq_S_sub_K 21 (by omega)
  rw [a_21] at h; unfold K at h; norm_num at h; linarith

private lemma S_succ_add (m : ℕ) : S (m + 1) = S m + (10 : ℤ) ^ m := by
  unfold S; rw [Finset.sum_range_succ]

private lemma a_22 : a 22 = 11101111011111111111111 := by
  rw [a_eq_S_sub_K 22 (by omega), S_succ_add 22, S_22]; unfold K; norm_num

private lemma a_23 : a 23 = 111111111111111111111111 := by
  rw [a_eq_S_sub_K 23 (by omega), S_succ_add 23, S_succ_add 22, S_22]; unfold K; norm_num

private lemma a_24 : a 24 = 1110111011111111111111111 := by
  rw [a_eq_S_sub_K 24 (by omega), S_succ_add 24, S_succ_add 23, S_succ_add 22, S_22]; unfold K; norm_num

private lemma a_25 : a 25 = 11111111111111111111111111 := by
  rw [a_eq_S_sub_K 25 (by omega), S_succ_add 25, S_succ_add 24, S_succ_add 23, S_succ_add 22, S_22]; unfold K; norm_num

-- PowerSeries generating function proof
private lemma coeff_mul_X' (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X) =
      if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
  have h := PowerSeries.coeff_mul_X_pow' f 1 n
  simpa [pow_one] using h

open PowerSeries in
private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) * (10000 * X ^ 5 - 10000 * X ^ 4 - X + 1 : PowerSeries ℚ) =
      -1000000000000 * X ^ 25 + 1000000000000 * X ^ 24 - 100000000000 * X ^ 23 + 100000000000 * X ^ 22 + 100000000 * X ^ 21 - 100000000 * X ^ 20 - 1000000 * X ^ 16 + 1001000 * X ^ 15 - 1000 * X ^ 14 + 100 * X ^ 12 - 100 * X ^ 10 + 10 * X ^ 9 - 10 * X ^ 8 + 1000 * X ^ 7 - 1000 * X ^ 6 + 10 * X ^ 5 - 10 * X ^ 4 + 1000 * X ^ 3 + 100 * X ^ 2 + 10 * X + 1 := by
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hmul :
      F * (10000 * X ^ 5 - 10000 * X ^ 4 - X + 1) =
        PowerSeries.C 10000 * (F * X ^ 5) - PowerSeries.C 10000 * (F * X ^ 4) - F * X + F := by
    have h10000 : (PowerSeries.C (10000 : ℚ) : PowerSeries ℚ) = 10000 := map_ofNat (PowerSeries.C (R := ℚ)) 10000
    rw [h10000]; ring
  rw [hmul]
  have hc_1000000000000 : (1000000000000 : PowerSeries ℚ) = PowerSeries.C 1000000000000 := (map_ofNat (PowerSeries.C (R := ℚ)) 1000000000000).symm
  have hc_100000000000 : (100000000000 : PowerSeries ℚ) = PowerSeries.C 100000000000 := (map_ofNat (PowerSeries.C (R := ℚ)) 100000000000).symm
  have hc_100000000 : (100000000 : PowerSeries ℚ) = PowerSeries.C 100000000 := (map_ofNat (PowerSeries.C (R := ℚ)) 100000000).symm
  have hc_1000000 : (1000000 : PowerSeries ℚ) = PowerSeries.C 1000000 := (map_ofNat (PowerSeries.C (R := ℚ)) 1000000).symm
  have hc_1001000 : (1001000 : PowerSeries ℚ) = PowerSeries.C 1001000 := (map_ofNat (PowerSeries.C (R := ℚ)) 1001000).symm
  have hc_1000 : (1000 : PowerSeries ℚ) = PowerSeries.C 1000 := (map_ofNat (PowerSeries.C (R := ℚ)) 1000).symm
  have hc_100 : (100 : PowerSeries ℚ) = PowerSeries.C 100 := (map_ofNat (PowerSeries.C (R := ℚ)) 100).symm
  have hc_10 : (10 : PowerSeries ℚ) = PowerSeries.C 10 := (map_ofNat (PowerSeries.C (R := ℚ)) 10).symm
  rw [hc_1000000000000, hc_100000000000, hc_100000000, hc_1000000, hc_1001000, hc_1000, hc_100, hc_10]
  have hneg1 : -(PowerSeries.C (1000000000000 : ℚ)) * X ^ 25 = -(PowerSeries.C (1000000000000 : ℚ) * X ^ 25) := by ring
  rw [hneg1]
  ext n
  have hcoeff_F : ∀ m, PowerSeries.coeff m F = (a m : ℚ) := fun m => PowerSeries.coeff_mk m _
  simp only [map_add, map_sub, map_neg, coeff_C_mul]
  simp only [coeff_one, coeff_X, coeff_X_pow, coeff_mul_X', PowerSeries.coeff_mul_X_pow', hcoeff_F]
  by_cases hn : 26 ≤ n
  · have h1 : 1 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn5 : n ≠ 5 := by omega
    have hn6 : n ≠ 6 := by omega
    have hn7 : n ≠ 7 := by omega
    have hn8 : n ≠ 8 := by omega
    have hn9 : n ≠ 9 := by omega
    have hn10 : n ≠ 10 := by omega
    have hn12 : n ≠ 12 := by omega
    have hn14 : n ≠ 14 := by omega
    have hn15 : n ≠ 15 := by omega
    have hn16 : n ≠ 16 := by omega
    have hn20 : n ≠ 20 := by omega
    have hn21 : n ≠ 21 := by omega
    have hn22 : n ≠ 22 := by omega
    have hn23 : n ≠ 23 := by omega
    have hn24 : n ≠ 24 := by omega
    have hn25 : n ≠ 25 := by omega
    simp only [if_pos h1, if_pos h4, if_pos h5, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_neg hn7, if_neg hn8, if_neg hn9, if_neg hn10, if_neg hn12, if_neg hn14, if_neg hn15, if_neg hn16, if_neg hn20, if_neg hn21, if_neg hn22, if_neg hn23, if_neg hn24, if_neg hn25]
    have hrec := a_rec_rat n hn
    linarith
  · interval_cases n <;>
      norm_num [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12, a_13, a_14, a_15, a_16, a_17, a_18, a_19, a_20, a_21, a_22, a_23, a_24, a_25]

end OMA.S_oeis_a283849.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a283849.main := by
  exact ⟨OMA.S_oeis_a283849.Proof.a_rec_rat, OMA.S_oeis_a283849.Proof.gf_eq⟩
