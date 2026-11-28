import OMAStatements.S_oeis_a284541

namespace OMA.S_oeis_a284541.Proof

open OMA.S_oeis_a284541

private def fastRule (c : Bool) (s : ℕ) : Bool :=
  match s with
  | 0 => c
  | 1 => true
  | 2 => false
  | _ => true

private lemma bool_toNat_le_one (b : Bool) : b.toNat ≤ 1 := by
  cases b <;> decide

private lemma rule974_eq_fastRule (c : Bool) (s : ℕ) (hs : s ≤ 4) :
    (974 : ℕ).testBit (c.toNat + 2 * s) = fastRule c s := by
  cases c <;> interval_cases s <;> rfl

private lemma cell_succ_fast (t : ℕ) (i j : ℤ) :
    cell 974 (t + 1) i j =
      fastRule (cell 974 t i j)
        ((cell 974 t (i + 1) j).toNat + (cell 974 t (i - 1) j).toNat +
         (cell 974 t i (j + 1)).toNat + (cell 974 t i (j - 1)).toNat) := by
  change (974 : ℕ).testBit _ = _
  apply rule974_eq_fastRule
  have b1 := bool_toNat_le_one (cell 974 t (i + 1) j)
  have b2 := bool_toNat_le_one (cell 974 t (i - 1) j)
  have b3 := bool_toNat_le_one (cell 974 t i (j + 1))
  have b4 := bool_toNat_le_one (cell 974 t i (j - 1))
  omega

private lemma fastRule_idemp (c : Bool) (s : ℕ) :
    fastRule (fastRule c s) s = fastRule c s := by
  cases s with
  | zero => rfl
  | succ s => cases s with
    | zero => rfl
    | succ s => cases s <;> rfl

private lemma fastRule_ge3 (c : Bool) (s : ℕ) (h : 3 ≤ s) :
    fastRule c s = true := by
  rcases s with _ | _ | _ | s'
  · omega
  · omega
  · omega
  · rfl

private lemma cell_neg_x (t : ℕ) : ∀ i j : ℤ, cell 974 t (-i) j = cell 974 t i j := by
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

private lemma cell_neg_y (t : ℕ) : ∀ i j : ℤ, cell 974 t i (-j) = cell 974 t i j := by
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

private lemma cell_out (t : ℕ) :
    ∀ i j : ℤ, t < i.natAbs + j.natAbs → cell 974 t i j = false := by
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

private lemma cell_freeze (t : ℕ) :
    ∀ i j : ℤ, (i + j - (t : ℤ)) % 2 = 0 → cell 974 (t + 1) i j = cell 974 t i j := by
  induction t with
  | zero =>
    intro i j h
    have h1 : cell 974 0 (i + 1) j = false := by simp [cell]; omega
    have h2 : cell 974 0 (i - 1) j = false := by simp [cell]; omega
    have h3 : cell 974 0 i (j + 1) = false := by simp [cell]; omega
    have h4 : cell 974 0 i (j - 1) = false := by simp [cell]; omega
    rw [cell_succ_fast, h1, h2, h3, h4]
    rfl
  | succ t ih =>
    intro i j h
    have h1 : cell 974 (t + 1) (i + 1) j = cell 974 t (i + 1) j := ih (i + 1) j (by omega)
    have h2 : cell 974 (t + 1) (i - 1) j = cell 974 t (i - 1) j := ih (i - 1) j (by omega)
    have h3 : cell 974 (t + 1) i (j + 1) = cell 974 t i (j + 1) := ih i (j + 1) (by omega)
    have h4 : cell 974 (t + 1) i (j - 1) = cell 974 t i (j - 1) := ih i (j - 1) (by omega)
    rw [cell_succ_fast (t + 1), h1, h2, h3, h4, cell_succ_fast t]
    exact fastRule_idemp _ _

private lemma cell_diag0 (t : ℕ) :
    ∀ x y : ℕ, x + y = t → cell 974 t (x : ℤ) (y : ℤ) = decide (Nat.choose t y % 2 = 1) := by
  induction t with
  | zero =>
    intro x y h
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst hx; subst hy; rfl
  | succ t ih =>
    intro x y h
    rw [cell_succ_fast]
    have hc : cell 974 t (x : ℤ) (y : ℤ) = false := cell_out t _ _ (by omega)
    have hr : cell 974 t ((x : ℤ) + 1) (y : ℤ) = false := cell_out t _ _ (by omega)
    have hu : cell 974 t (x : ℤ) ((y : ℤ) + 1) = false := cell_out t _ _ (by omega)
    rw [hc, hr, hu]
    cases x with
    | zero =>
      have hy : y = t + 1 := by omega
      subst y
      simp only [Nat.cast_zero]
      have hl : cell 974 t ((0 : ℤ) - 1) ((t + 1 : ℕ) : ℤ) = false := cell_out t _ _ (by omega)
      have hd : cell 974 t (0 : ℤ) (((t + 1 : ℕ) : ℤ) - 1) = true := by
        have hsub : ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) := by omega
        rw [hsub]
        have h0 := ih 0 t (by omega)
        simpa [Nat.choose_self] using h0
      rw [hl, hd]
      simp [fastRule, Nat.choose_self]
    | succ x' =>
      cases y with
      | zero =>
        have hx : x' = t := by omega
        subst x'
        simp only [Nat.cast_zero]
        have hd : cell 974 t ((t + 1 : ℕ) : ℤ) ((0 : ℤ) - 1) = false := cell_out t _ _ (by omega)
        have hl : cell 974 t (((t + 1 : ℕ) : ℤ) - 1) (0 : ℤ) = true := by
          have hsub : ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) := by omega
          rw [hsub]
          have h0 := ih t 0 (by omega)
          simpa [Nat.choose_zero_right] using h0
        rw [hl, hd]
        simp [fastRule, Nat.choose_zero_right]
      | succ y' =>
        have hl : cell 974 t (((x' + 1 : ℕ) : ℤ) - 1) ((y' + 1 : ℕ) : ℤ) =
            decide (Nat.choose t (y' + 1) % 2 = 1) := by
          have hsub : ((x' + 1 : ℕ) : ℤ) - 1 = (x' : ℤ) := by omega
          rw [hsub]; exact ih x' (y' + 1) (by omega)
        have hd : cell 974 t ((x' + 1 : ℕ) : ℤ) (((y' + 1 : ℕ) : ℤ) - 1) =
            decide (Nat.choose t y' % 2 = 1) := by
          have hsub : ((y' + 1 : ℕ) : ℤ) - 1 = (y' : ℤ) := by omega
          rw [hsub]; exact ih (x' + 1) y' (by omega)
        rw [hl, hd, Nat.choose_succ_succ]
        have ha : Nat.choose t y' % 2 = 0 ∨ Nat.choose t y' % 2 = 1 := by omega
        have hb : Nat.choose t (y' + 1) % 2 = 0 ∨ Nat.choose t (y' + 1) % 2 = 1 := by omega
        rcases ha with ha | ha <;> rcases hb with hb | hb <;>
          simp [ha, hb, Nat.add_mod, fastRule]

private lemma cell_diag1 (t x y : ℕ) (h : x + y + 1 = t) :
    cell 974 t (x : ℤ) (y : ℤ) = decide (Nat.choose (t - 1) y % 2 = 1) := by
  cases t with
  | zero => omega
  | succ t' =>
    rw [cell_freeze t' (x : ℤ) (y : ℤ) (by omega)]
    exact cell_diag0 t' x y (by omega)

private lemma choose_2_mod2 (n : ℕ) :
    Nat.choose n 2 % 2 = if n % 4 = 2 ∨ n % 4 = 3 then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.add_mod, ih, Nat.choose_one_right]
    split_ifs <;> omega

private lemma choose_3_mod2 (n : ℕ) :
    Nat.choose n 3 % 2 = if n % 4 = 3 then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.add_mod, ih, choose_2_mod2]
    split_ifs <;> omega

private lemma choose_4_mod2 (n : ℕ) :
    Nat.choose n 4 % 2 = if 4 ≤ n % 8 then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.add_mod, ih, choose_3_mod2]
    split_ifs <;> omega

private lemma cell_diag0_y3 (t : ℕ) (ht : 3 ≤ t) :
    cell 974 t ((t - 3 : ℕ) : ℤ) 3 = decide (t % 4 = 3) := by
  have h := cell_diag0 t (t - 3) 3 (by omega)
  simp only [Nat.cast_ofNat] at h
  rw [h, choose_3_mod2]
  by_cases hr : t % 4 = 3 <;> simp [hr]

private lemma cell_diag1_y3 (t : ℕ) (ht : 4 ≤ t) :
    cell 974 t ((t - 4 : ℕ) : ℤ) 3 = decide (t % 4 = 0) := by
  have h := cell_diag1 t (t - 4) 3 (by omega)
  simp only [Nat.cast_ofNat] at h
  rw [h, choose_3_mod2]
  have hmod : (t - 1) % 4 = 3 ↔ t % 4 = 0 := by omega
  by_cases hr : t % 4 = 0
  · have h1 : (t - 1) % 4 = 3 := hmod.mpr hr
    simp [hr, h1]
  · have h1 : (t - 1) % 4 ≠ 3 := fun hc => hr (hmod.mp hc)
    simp [hr, h1]

private lemma cell_diag0_y4 (t : ℕ) (ht : 4 ≤ t) :
    cell 974 t ((t - 4 : ℕ) : ℤ) 4 = decide (4 ≤ t % 8) := by
  have h := cell_diag0 t (t - 4) 4 (by omega)
  simp only [Nat.cast_ofNat] at h
  rw [h, choose_4_mod2]
  by_cases hr : 4 ≤ t % 8 <;> simp [hr]

-- Pure Nat/Bool lookup table for t = 0..8 (zero testBit, zero Int inside decide)
private def tblN : ℕ → ℕ → ℕ → Bool
  | 0, 0, x => x == 0
  | 1, 0, x => x == 0 || x == 1
  | 1, 1, x => x == 0
  | 2, 0, x => x == 0 || x == 1 || x == 2
  | 2, 1, x => x == 0
  | 2, 2, x => x == 0
  | 3, 0, x => x == 0 || x == 2 || x == 3
  | 3, 1, x => x == 2
  | 3, 2, x => x == 0 || x == 1
  | 3, 3, x => x == 0
  | 4, 0, x => x == 0 || x == 2 || x == 3 || x == 4
  | 4, 1, x => x == 2
  | 4, 2, x => x == 0 || x == 1
  | 4, 3, x => x == 0
  | 4, 4, x => x == 0
  | 5, 0, x => x == 0 || x == 2 || x == 4 || x == 5
  | 5, 1, x => x == 2 || x == 4
  | 5, 2, x => x == 0 || x == 1
  | 5, 4, x => x == 0 || x == 1
  | 5, 5, x => x == 0
  | 6, 0, x => x == 0 || x == 4 || x == 5 || x == 6
  | 6, 1, x => x == 2 || x == 4
  | 6, 2, x => x == 1 || x == 4
  | 6, 4, x => x == 0 || x == 1 || x == 2
  | 6, 5, x => x == 0
  | 6, 6, x => x == 0
  | 7, 0, x => x == 0 || x == 1 || x == 3 || x == 4 || x == 6 || x == 7
  | 7, 1, x => x == 0 || x == 2 || x == 6
  | 7, 2, x => x == 1 || x == 3 || x == 4 || x == 5
  | 7, 3, x => x == 0 || x == 2 || x == 4
  | 7, 4, x => x == 0 || x == 2 || x == 3
  | 7, 5, x => x == 2
  | 7, 6, x => x == 0 || x == 1
  | 7, 7, x => x == 0
  | 8, 0, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 6 || x == 7 || x == 8
  | 8, 1, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 6
  | 8, 2, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5
  | 8, 3, x => x == 0 || x == 1 || x == 2 || x == 3 || x == 4
  | 8, 4, x => x == 0 || x == 2 || x == 3
  | 8, 5, x => x == 2
  | 8, 6, x => x == 0 || x == 1
  | 8, 7, x => x == 0
  | 8, 8, x => x == 0
  | _, _, _ => false

private def tbl (t : ℕ) (i j : ℤ) : Bool :=
  tblN t j.natAbs i.natAbs

private def predAbs (n : ℕ) : ℕ :=
  if n = 0 then 1 else n - 1

private lemma natAbs_sub_one (n : ℕ) : ((n : ℤ) - 1).natAbs = predAbs n := by
  cases n <;> simp [predAbs]

private lemma tblN_out (t y x : ℕ) (ht : t ≤ 8) (h : t < x + y) : tblN t y x = false := by
  by_cases hy : y ≤ 8
  · interval_cases t <;> interval_cases y <;> simp [tblN] <;> omega
  · rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | y'
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · interval_cases t <;> rfl

private lemma tbl_out (t : ℕ) (ht : t ≤ 8) (i j : ℤ) (h : t < i.natAbs + j.natAbs) :
    tbl t i j = false :=
  tblN_out t j.natAbs i.natAbs ht h

private def stepCheck (t x y : ℕ) : Bool :=
  fastRule (tblN t y x)
    ((tblN t y (x + 1)).toNat + (tblN t y (predAbs x)).toNat +
     (tblN t (y + 1) x).toNat + (tblN t (predAbs y) x).toNat) ==
  tblN (t + 1) y x

private lemma tbl_step_0 : ∀ x : Fin 2, ∀ y : Fin 2, stepCheck 0 x.1 y.1 = true := by decide
private lemma tbl_step_1 : ∀ x : Fin 3, ∀ y : Fin 3, stepCheck 1 x.1 y.1 = true := by decide
private lemma tbl_step_2 : ∀ x : Fin 4, ∀ y : Fin 4, stepCheck 2 x.1 y.1 = true := by decide
private lemma tbl_step_3 : ∀ x : Fin 5, ∀ y : Fin 5, stepCheck 3 x.1 y.1 = true := by decide
private lemma tbl_step_4 : ∀ x : Fin 6, ∀ y : Fin 6, stepCheck 4 x.1 y.1 = true := by decide
private lemma tbl_step_5 : ∀ x : Fin 7, ∀ y : Fin 7, stepCheck 5 x.1 y.1 = true := by decide
private lemma tbl_step_6 : ∀ x : Fin 8, ∀ y : Fin 8, stepCheck 6 x.1 y.1 = true := by decide
private lemma tbl_step_7 : ∀ x : Fin 9, ∀ y : Fin 9, stepCheck 7 x.1 y.1 = true := by decide

private lemma tbl_step_nat (t x y : ℕ) (ht : t < 8) (hx : x ≤ t + 1) (hy : y ≤ t + 1) :
    fastRule (tblN t y x)
      ((tblN t y (x + 1)).toNat + (tblN t y (predAbs x)).toNat +
       (tblN t (y + 1) x).toNat + (tblN t (predAbs y) x).toNat) =
    tblN (t + 1) y x := by
  have hchk : stepCheck t x y = true := by
    interval_cases t
    · exact tbl_step_0 ⟨x, by omega⟩ ⟨y, by omega⟩
    · exact tbl_step_1 ⟨x, by omega⟩ ⟨y, by omega⟩
    · exact tbl_step_2 ⟨x, by omega⟩ ⟨y, by omega⟩
    · exact tbl_step_3 ⟨x, by omega⟩ ⟨y, by omega⟩
    · exact tbl_step_4 ⟨x, by omega⟩ ⟨y, by omega⟩
    · exact tbl_step_5 ⟨x, by omega⟩ ⟨y, by omega⟩
    · exact tbl_step_6 ⟨x, by omega⟩ ⟨y, by omega⟩
    · exact tbl_step_7 ⟨x, by omega⟩ ⟨y, by omega⟩
  simpa [stepCheck] using hchk

private lemma tbl_neg_x (t : ℕ) (i j : ℤ) : tbl t (-i) j = tbl t i j := by
  simp [tbl]

private lemma tbl_neg_y (t : ℕ) (i j : ℤ) : tbl t i (-j) = tbl t i j := by
  simp [tbl]

private lemma cell_eq_tbl (t : ℕ) (ht : t ≤ 8) :
    ∀ i j : ℤ, cell 974 t i j = tbl t i j := by
  induction t with
  | zero =>
    intro i j
    by_cases h0 : i = 0 ∧ j = 0
    · rcases h0 with ⟨rfl, rfl⟩; rfl
    · have hout : 0 < i.natAbs + j.natAbs := by omega
      rw [cell_out 0 i j hout, tbl_out 0 (by omega) i j hout]
  | succ t ih =>
    intro i j
    have ih' := ih (by omega)
    by_cases hout : t + 1 < i.natAbs + j.natAbs
    · rw [cell_out (t + 1) i j hout, tbl_out (t + 1) ht i j hout]
    · have hle : i.natAbs + j.natAbs ≤ t + 1 := by omega
      have hsub : ∀ i' j' : ℤ, 0 ≤ i' → 0 ≤ j' → i'.natAbs + j'.natAbs ≤ t + 1 →
          cell 974 (t + 1) i' j' = tbl (t + 1) i' j' := by
        intro i' j' hi hj hle'
        have hi_eq : (i'.natAbs : ℤ) = i' := Int.natAbs_of_nonneg hi
        have hj_eq : (j'.natAbs : ℤ) = j' := Int.natAbs_of_nonneg hj
        rw [← hi_eq, ← hj_eq, cell_succ_fast, ih', ih', ih', ih', ih']
        unfold tbl
        simp only [Int.natAbs_natCast, natAbs_sub_one,
          show ((i'.natAbs : ℤ) + 1).natAbs = i'.natAbs + 1 by omega,
          show ((j'.natAbs : ℤ) + 1).natAbs = j'.natAbs + 1 by omega]
        exact tbl_step_nat t i'.natAbs j'.natAbs (by omega) (by omega) (by omega)
      by_cases hi : 0 ≤ i
      · by_cases hj : 0 ≤ j
        · exact hsub i j hi hj hle
        · rw [← cell_neg_y, ← tbl_neg_y]
          exact hsub i (-j) hi (by omega) (by simpa using hle)
      · by_cases hj : 0 ≤ j
        · rw [← cell_neg_x, ← tbl_neg_x]
          exact hsub (-i) j (by omega) hj (by simpa using hle)
        · rw [← cell_neg_x, ← cell_neg_y, ← tbl_neg_x, ← tbl_neg_y]
          exact hsub (-i) (-j) (by omega) (by omega) (by simpa using hle)

-- Relative patterns for d = x - (t - 7)
private def patY0 (r d : ℕ) : Bool :=
  match r % 4 with
  | 0 => decide (d ≤ 3 ∨ d = 5 ∨ d = 6 ∨ d = 7)
  | 1 => decide (d ≤ 2 ∨ d = 4 ∨ d = 6 ∨ d = 7)
  | 2 => decide (d ≤ 1 ∨ d = 5 ∨ d = 6 ∨ d = 7)
  | _ => decide (d ≤ 1 ∨ d = 3 ∨ d = 4 ∨ d = 6 ∨ d = 7)

private def patY1 (r d : ℕ) : Bool :=
  match r % 4 with
  | 0 => decide (d ≤ 2 ∨ d = 5)
  | 1 => decide (d ≤ 2 ∨ d = 4 ∨ d = 6)
  | 2 => decide (d ≤ 3 ∨ d = 5)
  | _ => decide (d ≤ 2 ∨ d = 6)

private def patY2 (r d : ℕ) : Bool :=
  match r % 4 with
  | 0 => decide (d ≤ 4)
  | 1 => decide (d ≤ 3)
  | 2 => decide (d ≤ 2 ∨ d = 5)
  | _ => decide (d ≤ 1 ∨ d = 3 ∨ d = 4 ∨ d = 5)

private def patY3_may (r d : ℕ) (u : Bool) : Bool :=
  if 5 ≤ d then false
  else if d = 4 then decide (r % 4 = 3)
  else if d = 3 then decide (r % 4 = 0)
  else if d = 2 ∧ r % 4 = 2 then true
  else if d = 1 ∧ r % 4 = 3 then true
  else u

private def specY0 (t x : ℕ) : Bool := patY0 (t % 4) (x - (t - 7))
private def specY1 (t x : ℕ) : Bool := patY1 (t % 4) (x - (t - 7))
private def specY2 (t x : ℕ) : Bool := patY2 (t % 4) (x - (t - 7))

private lemma patY0_step : ∀ r : Fin 4, ∀ d : Fin 8,
    fastRule (patY0 r.1 (d.1 + 1))
      ((patY0 r.1 (d.1 + 2)).toNat + (patY0 r.1 d.1).toNat +
       (patY1 r.1 (d.1 + 1)).toNat + (patY1 r.1 (d.1 + 1)).toNat) =
    patY0 ((r.1 + 1) % 4) d.1 := by decide

private lemma patY1_step : ∀ r : Fin 4, ∀ d : Fin 8,
    fastRule (patY1 r.1 (d.1 + 1))
      ((patY1 r.1 (d.1 + 2)).toNat + (patY1 r.1 d.1).toNat +
       (patY2 r.1 (d.1 + 1)).toNat + (patY0 r.1 (d.1 + 1)).toNat) =
    patY1 ((r.1 + 1) % 4) d.1 := by decide

private lemma patY2_step : ∀ r : Fin 4, ∀ d : Fin 8, ∀ u : Bool,
    fastRule (patY2 r.1 (d.1 + 1))
      ((patY2 r.1 (d.1 + 2)).toNat + (patY2 r.1 d.1).toNat +
       (patY3_may r.1 (d.1 + 1) u).toNat + (patY1 r.1 (d.1 + 1)).toNat) =
    patY2 ((r.1 + 1) % 4) d.1 := by decide

private lemma patY3a_step : ∀ r : Fin 8, ∀ u : Bool, r.1 ≠ 6 →
    fastRule (decide (r.1 % 4 = 0))
      ((decide (r.1 % 4 = 3)).toNat +
       (if r.1 = 7 then u else decide (r.1 ≠ 1)).toNat +
       (decide (4 ≤ r.1)).toNat +
       (patY2 (r.1 % 4) 3).toNat) =
    decide ((r.1 + 1) % 8 ≠ 1) := by decide

private lemma patY0_le1 (r d : ℕ) (hd : d ≤ 1) : patY0 r d = true := by
  have hm : r % 4 < 4 := Nat.mod_lt _ (by omega)
  have h' : ∀ a : Fin 4, ∀ b : Fin 2, patY0 a.1 b.1 = true := by decide
  have hres := h' ⟨r % 4, hm⟩ ⟨d, by omega⟩
  simpa [patY0] using hres

private lemma patY1_le1 (r d : ℕ) (hd : d ≤ 1) : patY1 r d = true := by
  have hm : r % 4 < 4 := Nat.mod_lt _ (by omega)
  have h' : ∀ a : Fin 4, ∀ b : Fin 2, patY1 a.1 b.1 = true := by decide
  have hres := h' ⟨r % 4, hm⟩ ⟨d, by omega⟩
  simpa [patY1] using hres

private lemma patY2_le1 (r d : ℕ) (hd : d ≤ 1) : patY2 r d = true := by
  have hm : r % 4 < 4 := Nat.mod_lt _ (by omega)
  have h' : ∀ a : Fin 4, ∀ b : Fin 2, patY2 a.1 b.1 = true := by decide
  have hres := h' ⟨r % 4, hm⟩ ⟨d, by omega⟩
  simpa [patY2] using hres

private lemma patY0_ge8 (r d : ℕ) (hd : 8 ≤ d) : patY0 r d = false := by
  unfold patY0
  have hm : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases hm with h | h | h | h <;> rw [h] <;> simp <;> omega

private lemma patY1_ge8 (r d : ℕ) (hd : 8 ≤ d) : patY1 r d = false := by
  unfold patY1
  have hm : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases hm with h | h | h | h <;> rw [h] <;> simp <;> omega

private lemma patY2_ge8 (r d : ℕ) (hd : 8 ≤ d) : patY2 r d = false := by
  unfold patY2
  have hm : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases hm with h | h | h | h <;> rw [h] <;> simp <;> omega

private structure Inv (t : ℕ) : Prop where
  y0 : ∀ x : ℕ, cell 974 t (x : ℤ) 0 = specY0 t x
  y1 : ∀ x : ℕ, cell 974 t (x : ℤ) 1 = specY1 t x
  y2 : ∀ x : ℕ, cell 974 t (x : ℤ) 2 = specY2 t x
  y3a : t % 8 ≠ 7 → cell 974 t ((t - 5 : ℕ) : ℤ) 3 = decide (t % 8 ≠ 1)
  y3b : (t % 8 = 3 ∨ t % 8 = 7) → cell 974 t ((t - 6 : ℕ) : ℤ) 3 = true

private lemma inv_base : Inv 8 where
  y0 x := by
    rw [cell_eq_tbl 8 (by omega)]
    by_cases hx : x < 9
    · interval_cases x <;> rfl
    · rw [tbl_out 8 (by omega) _ _ (by omega)]
      exact (patY0_ge8 _ _ (by omega)).symm
  y1 x := by
    rw [cell_eq_tbl 8 (by omega)]
    by_cases hx : x < 9
    · interval_cases x <;> rfl
    · rw [tbl_out 8 (by omega) _ _ (by omega)]
      exact (patY1_ge8 _ _ (by omega)).symm
  y2 x := by
    rw [cell_eq_tbl 8 (by omega)]
    by_cases hx : x < 9
    · interval_cases x <;> rfl
    · rw [tbl_out 8 (by omega) _ _ (by omega)]
      exact (patY2_ge8 _ _ (by omega)).symm
  y3a _ := by
    rw [cell_eq_tbl 8 (by omega)]
    rfl
  y3b h := by omega

private lemma cast_add_one (x : ℕ) : (x : ℤ) + 1 = ((x + 1 : ℕ) : ℤ) := by omega
private lemma cast_sub_one (x : ℕ) (hx : 1 ≤ x) : (x : ℤ) - 1 = ((x - 1 : ℕ) : ℤ) := by omega

private lemma cell_y_m1 (t x : ℕ) :
    cell 974 t (x : ℤ) ((0 : ℤ) - 1) = cell 974 t (x : ℤ) 1 := by
  have : (0 : ℤ) - 1 = -(1 : ℤ) := by norm_num
  rw [this, cell_neg_y]

private lemma inv_step (t : ℕ) (ht : 8 ≤ t) (h : Inv t) : Inv (t + 1) := by
  have hmod4 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
  have hmod8 : (t + 1) % 8 = (t % 8 + 1) % 8 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- y = 0
    intro x
    by_cases hgt : t + 1 < x
    · rw [cell_out (t + 1) _ _ (by omega)]
      exact (patY0_ge8 _ _ (by omega)).symm
    · by_cases hle : x ≤ t - 7
      · rw [cell_succ_fast, cast_add_one, cell_y_m1]
        have h01 : (0 : ℤ) + 1 = 1 := by norm_num
        rw [h01, h.y0 (x + 1), h.y1 x]
        have h1 : specY0 t (x + 1) = true := patY0_le1 _ _ (by omega)
        have h3 : specY1 t x = true := patY1_le1 _ _ (by omega)
        have h2 : cell 974 t ((x : ℤ) - 1) 0 = true := by
          cases x with
          | zero =>
            have : ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
            rw [this, cell_neg_x, h.y0 1]
            exact patY0_le1 _ _ (by omega)
          | succ x' =>
            rw [cast_sub_one (x' + 1) (by omega), h.y0]
            exact patY0_le1 _ _ (by omega)
        rw [h1, h2, h3, fastRule_ge3 _ _ (by simp)]
        exact (patY0_le1 _ _ (by omega)).symm
      · have hx1 : 1 ≤ x := by omega
        set d := x - (t - 6) with hd_def
        have hd_lt : d < 8 := by omega
        have hd1 : x - (t - 7) = d + 1 := by omega
        have hd2 : x + 1 - (t - 7) = d + 2 := by omega
        have hd0 : x - 1 - (t - 7) = d := by omega
        have hd_nxt : x - (t + 1 - 7) = d := by omega
        rw [cell_succ_fast, cast_add_one, cast_sub_one x hx1, cell_y_m1]
        have h01 : (0 : ℤ) + 1 = 1 := by norm_num
        rw [h01, h.y0 x, h.y0 (x + 1), h.y0 (x - 1), h.y1 x]
        simp only [specY0, specY1, hd1, hd2, hd0, hd_nxt, hmod4]
        exact patY0_step ⟨t % 4, Nat.mod_lt _ (by omega)⟩ ⟨d, hd_lt⟩
  · -- y = 1
    intro x
    by_cases hgt : t + 1 < x
    · rw [cell_out (t + 1) _ _ (by omega)]
      exact (patY1_ge8 _ _ (by omega)).symm
    · by_cases hle : x ≤ t - 7
      · rw [cell_succ_fast, cast_add_one]
        have h12 : (1 : ℤ) + 1 = 2 := by norm_num
        have h10 : (1 : ℤ) - 1 = 0 := by norm_num
        rw [h12, h10, h.y1 (x + 1), h.y2 x, h.y0 x]
        have h1 : specY1 t (x + 1) = true := patY1_le1 _ _ (by omega)
        have h3 : specY2 t x = true := patY2_le1 _ _ (by omega)
        have h4 : specY0 t x = true := patY0_le1 _ _ (by omega)
        have h2 : cell 974 t ((x : ℤ) - 1) 1 = true := by
          cases x with
          | zero =>
            have : ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
            rw [this, cell_neg_x, h.y1 1]
            exact patY1_le1 _ _ (by omega)
          | succ x' =>
            rw [cast_sub_one (x' + 1) (by omega), h.y1]
            exact patY1_le1 _ _ (by omega)
        rw [h1, h2, h3, h4, fastRule_ge3 _ _ (by simp)]
        exact (patY1_le1 _ _ (by omega)).symm
      · have hx1 : 1 ≤ x := by omega
        set d := x - (t - 6) with hd_def
        have hd_lt : d < 8 := by omega
        have hd1 : x - (t - 7) = d + 1 := by omega
        have hd2 : x + 1 - (t - 7) = d + 2 := by omega
        have hd0 : x - 1 - (t - 7) = d := by omega
        have hd_nxt : x - (t + 1 - 7) = d := by omega
        rw [cell_succ_fast, cast_add_one, cast_sub_one x hx1]
        have h12 : (1 : ℤ) + 1 = 2 := by norm_num
        have h10 : (1 : ℤ) - 1 = 0 := by norm_num
        rw [h12, h10, h.y1 x, h.y1 (x + 1), h.y1 (x - 1), h.y2 x, h.y0 x]
        simp only [specY0, specY1, specY2, hd1, hd2, hd0, hd_nxt, hmod4]
        exact patY1_step ⟨t % 4, Nat.mod_lt _ (by omega)⟩ ⟨d, hd_lt⟩
  · -- y = 2
    intro x
    by_cases hgt : t + 1 < x
    · rw [cell_out (t + 1) _ _ (by omega)]
      exact (patY2_ge8 _ _ (by omega)).symm
    · by_cases hle : x ≤ t - 7
      · rw [cell_succ_fast, cast_add_one]
        have h23 : (2 : ℤ) + 1 = 3 := by norm_num
        have h21 : (2 : ℤ) - 1 = 1 := by norm_num
        rw [h23, h21, h.y2 (x + 1), h.y1 x]
        have h1 : specY2 t (x + 1) = true := patY2_le1 _ _ (by omega)
        have h4 : specY1 t x = true := patY1_le1 _ _ (by omega)
        have h2 : cell 974 t ((x : ℤ) - 1) 2 = true := by
          cases x with
          | zero =>
            have : ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
            rw [this, cell_neg_x, h.y2 1]
            exact patY2_le1 _ _ (by omega)
          | succ x' =>
            rw [cast_sub_one (x' + 1) (by omega), h.y2]
            exact patY2_le1 _ _ (by omega)
        rw [h1, h2, h4, fastRule_ge3 _ _ (by simp)]
        exact (patY2_le1 _ _ (by omega)).symm
      · have hx1 : 1 ≤ x := by omega
        set d := x - (t - 6) with hd_def
        have hd_lt : d < 8 := by omega
        have hd1 : x - (t - 7) = d + 1 := by omega
        have hd2 : x + 1 - (t - 7) = d + 2 := by omega
        have hd0 : x - 1 - (t - 7) = d := by omega
        have hd_nxt : x - (t + 1 - 7) = d := by omega
        rw [cell_succ_fast, cast_add_one, cast_sub_one x hx1]
        have h23 : (2 : ℤ) + 1 = 3 := by norm_num
        have h21 : (2 : ℤ) - 1 = 1 := by norm_num
        rw [h23, h21, h.y2 x, h.y2 (x + 1), h.y2 (x - 1), h.y1 x]
        have hy3 : cell 974 t (x : ℤ) 3 = patY3_may (t % 4) (d + 1) (cell 974 t (x : ℤ) 3) := by
          unfold patY3_may
          have h44 : (t % 4) % 4 = t % 4 := by omega
          rw [h44]
          split_ifs with c1 c2 c3 c4 c5
          · exact cell_out t _ _ (by omega)
          · have hx_eq : x = t - 3 := by omega
            rw [hx_eq]
            exact cell_diag0_y3 t (by omega)
          · have hx_eq : x = t - 4 := by omega
            rw [hx_eq]
            exact cell_diag1_y3 t (by omega)
          · have hx_eq : x = t - 5 := by omega
            rw [hx_eq, h.y3a (by omega)]
            simp [show t % 8 ≠ 1 by omega]
          · have hx_eq : x = t - 6 := by omega
            rw [hx_eq]
            exact h.y3b (by omega)
          · rfl
        rw [hy3]
        simp only [specY1, specY2, hd1, hd2, hd0, hd_nxt, hmod4]
        exact patY2_step ⟨t % 4, Nat.mod_lt _ (by omega)⟩ ⟨d, hd_lt⟩ (cell 974 t (x : ℤ) 3)
  · -- y3a at t + 1: cell (t + 1) (t - 4) 3
    intro hne7
    have hr6 : t % 8 ≠ 6 := by omega
    have hx_eq : ((t + 1 - 5 : ℕ) : ℤ) = ((t - 4 : ℕ) : ℤ) := by omega
    rw [hx_eq, cell_succ_fast]
    have hx_r : ((t - 4 : ℕ) : ℤ) + 1 = ((t - 3 : ℕ) : ℤ) := by omega
    have hx_l : ((t - 4 : ℕ) : ℤ) - 1 = ((t - 5 : ℕ) : ℤ) := by omega
    have hy_u : (3 : ℤ) + 1 = 4 := by norm_num
    have hy_d : (3 : ℤ) - 1 = 2 := by norm_num
    rw [hx_r, hx_l, hy_u, hy_d,
        cell_diag1_y3 t (by omega),
        cell_diag0_y3 t (by omega),
        cell_diag0_y4 t (by omega),
        h.y2 (t - 4)]
    have hspec : specY2 t (t - 4) = patY2 ((t % 8) % 4) 3 := by
      unfold specY2
      have h1 : t - 4 - (t - 7) = 3 := by omega
      have h2 : (t % 8) % 4 = t % 4 := by omega
      rw [h1, h2]
    rw [hspec]
    have hleft : cell 974 t ((t - 5 : ℕ) : ℤ) 3 =
        if t % 8 = 7 then cell 974 t ((t - 5 : ℕ) : ℤ) 3 else decide (t % 8 ≠ 1) := by
      by_cases h7 : t % 8 = 7
      · simp [h7]
      · simp [h7, h.y3a h7]
    rw [hleft]
    have hm4 : t % 4 = (t % 8) % 4 := by omega
    rw [hm4, hmod8]
    exact patY3a_step ⟨t % 8, Nat.mod_lt _ (by omega)⟩ (cell 974 t ((t - 5 : ℕ) : ℤ) 3) hr6
  · -- y3b at t + 1: cell (t + 1) (t - 5) 3 by parity freeze
    intro h37
    have hx_eq : ((t + 1 - 6 : ℕ) : ℤ) = ((t - 5 : ℕ) : ℤ) := by omega
    rw [hx_eq, cell_freeze t _ _ (by omega), h.y3a (by omega)]
    simp [show t % 8 ≠ 1 by omega]

private lemma inv_ge8 (t : ℕ) (ht : 8 ≤ t) : Inv t := by
  induction t, ht using Nat.le_induction with
  | base => exact inv_base
  | succ k hk ih => exact inv_step k hk ih

-- Closed-form repunit S m = sum_{k < m} 10^k
private def S (m : ℕ) : ℤ := ∑ k ∈ Finset.range m, (10 : ℤ) ^ k

private lemma S_succ (m : ℕ) : S (m + 1) = 10 * S m + 1 := by
  induction m with
  | zero => simp [S]
  | succ m ih =>
    calc S (m + 2) = S (m + 1) + (10 : ℤ) ^ (m + 1) := by
          unfold S; rw [Finset.sum_range_succ]
      _ = (10 * S m + 1) + 10 * (10 : ℤ) ^ m := by rw [ih]; ring
      _ = 10 * (S m + (10 : ℤ) ^ m) + 1 := by ring
      _ = 10 * S (m + 1) + 1 := by unfold S; rw [Finset.sum_range_succ]

private def C (r : ℕ) : ℤ :=
  match r % 4 with
  | 0 => 1000
  | 1 => 10100
  | 2 => 111000
  | _ => 100100

private lemma sum_reflect_ten (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (10 : ℤ) ^ (n - k) = S (n + 1) := by
  have h := Finset.sum_range_reflect (fun k => (10 : ℤ) ^ k) (n + 1)
  simpa [S, Nat.add_sub_cancel] using h

private lemma a_eq_S_sub_C (n : ℕ) (hn : 8 ≤ n) : a n = S (n + 1) - C n := by
  have hinv := (inv_ge8 n hn).y0
  unfold a
  have hsplit :
      (∑ k ∈ Finset.range (n + 1), if cell 974 n (k : ℤ) 0 then (10 : ℤ) ^ (n - k) else 0) +
      (∑ k ∈ Finset.range (n + 1), if cell 974 n (k : ℤ) 0 then 0 else (10 : ℤ) ^ (n - k)) =
      S (n + 1) := by
    rw [← Finset.sum_add_distrib, ← sum_reflect_ten n]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  have hoff :
      (∑ k ∈ Finset.range (n + 1), if cell 974 n (k : ℤ) 0 then 0 else (10 : ℤ) ^ (n - k)) = C n := by
    have hcongr :
        (∑ k ∈ Finset.range (n + 1), if cell 974 n (k : ℤ) 0 then 0 else (10 : ℤ) ^ (n - k)) =
        (∑ k ∈ Finset.range (n + 1), if specY0 n k then 0 else (10 : ℤ) ^ (n - k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hinv k]
    rw [hcongr]
    have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hmod with hm | hm | hm | hm
    · rw [Finset.sum_eq_single (n - 3)]
      · have hs : specY0 n (n - 3) = false := by
          unfold specY0 patY0; rw [hm]; simp; omega
        have he : n - (n - 3) = 3 := by omega
        rw [hs, he]; unfold C; rw [hm]; norm_num
      · intro k hk hne
        rw [Finset.mem_range] at hk
        have hs : specY0 n k = true := by
          unfold specY0 patY0; rw [hm]; simp; omega
        rw [hs]; rfl
      · intro hnot
        exfalso; apply hnot; rw [Finset.mem_range]; omega
    · have hsub : ({n - 4, n - 2} : Finset ℕ) ⊆ Finset.range (n + 1) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [Finset.mem_range]; omega
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_pair (by omega)]
        have hs1 : specY0 n (n - 4) = false := by
          unfold specY0 patY0; rw [hm]; simp; omega
        have hs2 : specY0 n (n - 2) = false := by
          unfold specY0 patY0; rw [hm]; simp; omega
        have he1 : n - (n - 4) = 4 := by omega
        have he2 : n - (n - 2) = 2 := by omega
        rw [hs1, hs2, he1, he2]; unfold C; rw [hm]; norm_num
      · intro k hk hnot
        rw [Finset.mem_range] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        have hs : specY0 n k = true := by
          unfold specY0 patY0; rw [hm]; simp; omega
        rw [hs]; rfl
    · have hsub : ({n - 5, n - 4, n - 3} : Finset ℕ) ⊆ Finset.range (n + 1) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [Finset.mem_range]; omega
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega)]
        have hs1 : specY0 n (n - 5) = false := by
          unfold specY0 patY0; rw [hm]; simp; omega
        have hs2 : specY0 n (n - 4) = false := by
          unfold specY0 patY0; rw [hm]; simp; omega
        have hs3 : specY0 n (n - 3) = false := by
          unfold specY0 patY0; rw [hm]; simp; omega
        have he1 : n - (n - 5) = 5 := by omega
        have he2 : n - (n - 4) = 4 := by omega
        have he3 : n - (n - 3) = 3 := by omega
        rw [hs1, hs2, hs3, he1, he2, he3]; unfold C; rw [hm]; norm_num
      · intro k hk hnot
        rw [Finset.mem_range] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        have hs : specY0 n k = true := by
          unfold specY0 patY0; rw [hm]; simp; omega
        rw [hs]; rfl
    · have hsub : ({n - 5, n - 2} : Finset ℕ) ⊆ Finset.range (n + 1) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [Finset.mem_range]; omega
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_pair (by omega)]
        have hs1 : specY0 n (n - 5) = false := by
          unfold specY0 patY0; rw [hm]; simp; omega
        have hs2 : specY0 n (n - 2) = false := by
          unfold specY0 patY0; rw [hm]; simp; omega
        have he1 : n - (n - 5) = 5 := by omega
        have he2 : n - (n - 2) = 2 := by omega
        rw [hs1, hs2, he1, he2]; unfold C; rw [hm]; norm_num
      · intro k hk hnot
        rw [Finset.mem_range] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        have hs : specY0 n k = true := by
          unfold specY0 patY0; rw [hm]; simp; omega
        rw [hs]; rfl
  linarith

-- Concrete values a(0)..a(8) via tblN
private lemma a_eq_tbl_sum (n : ℕ) (hn : n ≤ 8) :
    a n = ∑ k ∈ Finset.range (n + 1), if tblN n 0 k then (10 : ℤ) ^ (n - k) else 0 := by
  unfold a
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cell_eq_tbl n hn (k : ℤ) 0]
  simp only [tbl, Int.natAbs_zero, Int.natAbs_natCast]
  rfl

private lemma a_0 : a 0 = 1 := by
  rw [a_eq_tbl_sum 0 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]
  norm_num

private lemma a_1 : a 1 = 11 := by
  rw [a_eq_tbl_sum 1 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]
  norm_num

private lemma a_2 : a 2 = 111 := by
  rw [a_eq_tbl_sum 2 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]
  norm_num

private lemma a_3 : a 3 = 1011 := by
  rw [a_eq_tbl_sum 3 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]
  norm_num

private lemma a_4 : a 4 = 10111 := by
  rw [a_eq_tbl_sum 4 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]
  norm_num

private lemma a_5 : a 5 = 101011 := by
  rw [a_eq_tbl_sum 5 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]
  norm_num

private lemma a_6 : a 6 = 1000111 := by
  rw [a_eq_tbl_sum 6 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]
  norm_num

private lemma a_7 : a 7 = 11011011 := by
  rw [a_eq_tbl_sum 7 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]
  norm_num

private lemma a_8 : a 8 = 111110111 := by
  rw [a_eq_tbl_sum 8 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]
  norm_num

private lemma S_9 : S 9 = 111111111 := by
  simp only [S, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num

private lemma a_9 : a 9 = 1111101011 := by
  rw [a_eq_S_sub_C 9 (by omega), S_succ 9, S_9]; unfold C; norm_num

private lemma a_10 : a 10 = 11111000111 := by
  rw [a_eq_S_sub_C 10 (by omega), S_succ 10, S_succ 9, S_9]; unfold C; norm_num

private lemma a_11 : a 11 = 111111011011 := by
  rw [a_eq_S_sub_C 11 (by omega), S_succ 11, S_succ 10, S_succ 9, S_9]; unfold C; norm_num

private lemma a_12 : a 12 = 1111111110111 := by
  rw [a_eq_S_sub_C 12 (by omega), S_succ 12, S_succ 11, S_succ 10, S_succ 9, S_9]; unfold C; norm_num

private lemma a_rec_int (n : ℕ) (hn : 9 ≤ n) :
    a n = 10 * a (n - 1) + a (n - 4) - 10 * a (n - 5) := by
  by_cases h13 : 13 ≤ n
  · rw [a_eq_S_sub_C n (by omega),
        a_eq_S_sub_C (n - 1) (by omega),
        a_eq_S_sub_C (n - 4) (by omega),
        a_eq_S_sub_C (n - 5) (by omega)]
    have hS1 : S (n + 1) = 10 * S (n - 1 + 1) + 1 := by
      have : n + 1 = (n - 1 + 1) + 1 := by omega
      rw [this, S_succ]
    have hS2 : S (n - 4 + 1) = 10 * S (n - 5 + 1) + 1 := by
      have : n - 4 + 1 = (n - 5 + 1) + 1 := by omega
      rw [this, S_succ]
    have hC1 : C n = C (n - 4) := by
      unfold C
      have : n % 4 = (n - 4) % 4 := by omega
      rw [this]
    have hC2 : C (n - 1) = C (n - 5) := by
      unfold C
      have : (n - 1) % 4 = (n - 5) % 4 := by omega
      rw [this]
    rw [hS1, hS2, hC1, hC2]
    ring
  · interval_cases n
    · norm_num [a_9, a_8, a_5, a_4]
    · norm_num [a_10, a_9, a_6, a_5]
    · norm_num [a_11, a_10, a_7, a_6]
    · norm_num [a_12, a_11, a_8, a_7]

private lemma a_rec_rat (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = 10 * a (n - 1) + a (n - 4) - 10 * a (n - 5) := by
  exact_mod_cast a_rec_int n hn

-- PowerSeries helper and proof
private lemma coeff_mul_X' (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X) =
      if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
  have h := PowerSeries.coeff_mul_X_pow' f 1 n
  simpa [pow_one] using h

open PowerSeries in
private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + X ^ 2) : PowerSeries ℚ) =
      1 + X + X ^ 2 - 99 * X ^ 3 - 100 * X ^ 5 - 10000 * X ^ 6 + 1010000 * X ^ 7 + 1000000 * X ^ 8 := by
  have hpoly :
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + X ^ 2) : PowerSeries ℚ) =
        1 - PowerSeries.C 10 * X - X ^ 4 + PowerSeries.C 10 * X ^ 5 := by
    have h10 : (PowerSeries.C (10 : ℚ) : PowerSeries ℚ) = 10 := map_ofNat (PowerSeries.C (R := ℚ)) 10
    rw [h10]
    ring
  rw [hpoly]
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hmul :
      F * (1 - PowerSeries.C 10 * X - X ^ 4 + PowerSeries.C 10 * X ^ 5) =
        F - PowerSeries.C 10 * (F * X) - F * X ^ 4 + PowerSeries.C 10 * (F * X ^ 5) := by
    ring
  rw [hmul]
  have h99 : (99 : PowerSeries ℚ) = PowerSeries.C 99 := (map_ofNat (PowerSeries.C (R := ℚ)) 99).symm
  have h100 : (100 : PowerSeries ℚ) = PowerSeries.C 100 := (map_ofNat (PowerSeries.C (R := ℚ)) 100).symm
  have h10000 : (10000 : PowerSeries ℚ) = PowerSeries.C 10000 := (map_ofNat (PowerSeries.C (R := ℚ)) 10000).symm
  have h1010000 : (1010000 : PowerSeries ℚ) = PowerSeries.C 1010000 := (map_ofNat (PowerSeries.C (R := ℚ)) 1010000).symm
  have h1000000 : (1000000 : PowerSeries ℚ) = PowerSeries.C 1000000 := (map_ofNat (PowerSeries.C (R := ℚ)) 1000000).symm
  rw [h99, h100, h10000, h1010000, h1000000]
  ext n
  have hcoeff_F : ∀ m, PowerSeries.coeff m F = (a m : ℚ) := fun m => PowerSeries.coeff_mk m _
  simp only [map_add, map_sub, coeff_C_mul]
  simp only [coeff_one, coeff_X, coeff_X_pow,
    coeff_mul_X', PowerSeries.coeff_mul_X_pow', hcoeff_F]
  by_cases hn : 9 ≤ n
  · have h1 : 1 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    have h0' : n ≠ 0 := by omega
    have h1' : n ≠ 1 := by omega
    have h2' : n ≠ 2 := by omega
    have h3' : n ≠ 3 := by omega
    have h5' : n ≠ 5 := by omega
    have h6' : n ≠ 6 := by omega
    have h7' : n ≠ 7 := by omega
    have h8' : n ≠ 8 := by omega
    simp only [if_pos h1, if_pos h4, if_pos h5,
      if_neg h0', if_neg h1', if_neg h2', if_neg h3', if_neg h5', if_neg h6', if_neg h7', if_neg h8']
    have hrec := a_rec_rat n hn
    linarith
  · interval_cases n <;>
      norm_num [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8]

end OMA.S_oeis_a284541.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a284541.main := by
  exact ⟨OMA.S_oeis_a284541.Proof.gf_eq, OMA.S_oeis_a284541.Proof.a_rec_rat⟩
