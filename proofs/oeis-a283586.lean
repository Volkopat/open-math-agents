import OMAStatements.S_oeis_a283586

namespace OMA.S_oeis_a283586.Proof

open OMA.S_oeis_a283586

-- Fast rule for Wolfram code 654 (binary 1010001110):
-- s = 0 -> c, s = 1 -> true, s = 2 -> false, s = 3 -> c, s = 4 -> c.
private def fastRule (c : Bool) (s : ℕ) : Bool :=
  match s with
  | 1 => true
  | 2 => false
  | _ => c

private lemma bool_toNat_le_one (b : Bool) : b.toNat ≤ 1 := by
  cases b <;> decide

private lemma rule654_eq_fastRule (c : Bool) (s : ℕ) (hs : s ≤ 4) :
    (654 : ℕ).testBit (c.toNat + 2 * s) = fastRule c s := by
  cases c <;> interval_cases s <;> rfl

private lemma cell_succ_fast (t : ℕ) (i j : ℤ) :
    cell 654 (t + 1) i j =
      fastRule (cell 654 t i j)
        ((cell 654 t (i + 1) j).toNat + (cell 654 t (i - 1) j).toNat +
         (cell 654 t i (j + 1)).toNat + (cell 654 t i (j - 1)).toNat) := by
  change (654 : ℕ).testBit _ = _
  apply rule654_eq_fastRule
  have b1 := bool_toNat_le_one (cell 654 t (i + 1) j)
  have b2 := bool_toNat_le_one (cell 654 t (i - 1) j)
  have b3 := bool_toNat_le_one (cell 654 t i (j + 1))
  have b4 := bool_toNat_le_one (cell 654 t i (j - 1))
  omega

private lemma fastRule_idemp (c : Bool) (s : ℕ) :
    fastRule (fastRule c s) s = fastRule c s := by
  rcases s with _ | _ | _ | s' <;> rfl

private lemma fastRule_false_of_ne_one (s : ℕ) (hs : s ≠ 1) :
    fastRule false s = false := by
  rcases s with _ | _ | _ | s'
  · rfl
  · omega
  · rfl
  · rfl

private lemma fastRule_true_of_ne_two (s : ℕ) (hs : s ≠ 2) :
    fastRule true s = true := by
  rcases s with _ | _ | _ | s'
  · rfl
  · rfl
  · omega
  · rfl

private lemma cell_neg_x (t : ℕ) : ∀ i j : ℤ, cell 654 t (-i) j = cell 654 t i j := by
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

private lemma cell_neg_y (t : ℕ) : ∀ i j : ℤ, cell 654 t i (-j) = cell 654 t i j := by
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
    ∀ i j : ℤ, t < i.natAbs + j.natAbs → cell 654 t i j = false := by
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
    ∀ i j : ℤ, (i + j - (t : ℤ)) % 2 = 0 → cell 654 (t + 1) i j = cell 654 t i j := by
  induction t with
  | zero =>
    intro i j h
    have h1 : cell 654 0 (i + 1) j = false := by simp [cell]; omega
    have h2 : cell 654 0 (i - 1) j = false := by simp [cell]; omega
    have h3 : cell 654 0 i (j + 1) = false := by simp [cell]; omega
    have h4 : cell 654 0 i (j - 1) = false := by simp [cell]; omega
    rw [cell_succ_fast, h1, h2, h3, h4]
    rfl
  | succ t ih =>
    intro i j h
    have h1 : cell 654 (t + 1) (i + 1) j = cell 654 t (i + 1) j := ih (i + 1) j (by omega)
    have h2 : cell 654 (t + 1) (i - 1) j = cell 654 t (i - 1) j := ih (i - 1) j (by omega)
    have h3 : cell 654 (t + 1) i (j + 1) = cell 654 t i (j + 1) := ih i (j + 1) (by omega)
    have h4 : cell 654 (t + 1) i (j - 1) = cell 654 t i (j - 1) := ih i (j - 1) (by omega)
    rw [cell_succ_fast (t + 1), h1, h2, h3, h4, cell_succ_fast t]
    exact fastRule_idemp _ _

-- Global theorem: every (odd, odd) cell is always false, and its neighbor sum is never 1.
private lemma odd_step_bool : ∀ e1 e2 e3 e4 a b c d : Bool,
    e1.toNat + e2.toNat + e3.toNat + e4.toNat ≠ 1 →
    (fastRule e1 (a.toNat + b.toNat)).toNat +
    (fastRule e2 (b.toNat + c.toNat)).toNat +
    (fastRule e3 (c.toNat + d.toNat)).toNat +
    (fastRule e4 (d.toNat + a.toNat)).toNat ≠ 1 := by decide

private lemma cell_odd_odd (t : ℕ) :
    ∀ i j : ℤ, i % 2 = 1 → j % 2 = 1 →
      cell 654 t i j = false ∧
      (cell 654 t (i + 1) j).toNat + (cell 654 t (i - 1) j).toNat +
      (cell 654 t i (j + 1)).toNat + (cell 654 t i (j - 1)).toNat ≠ 1 := by
  induction t with
  | zero =>
    intro i j hi hj
    have h0 : cell 654 0 i j = false := by simp [cell]; omega
    have h1 : cell 654 0 (i + 1) j = false := by simp [cell]; omega
    have h2 : cell 654 0 (i - 1) j = false := by simp [cell]; omega
    have h3 : cell 654 0 i (j + 1) = false := by simp [cell]; omega
    have h4 : cell 654 0 i (j - 1) = false := by simp [cell]; omega
    rw [h0, h1, h2, h3, h4]
    exact ⟨rfl, by decide⟩
  | succ t ih =>
    intro i j hi hj
    obtain ⟨hc, hs⟩ := ih i j hi hj
    by_cases ht : t % 2 = 0
    · refine ⟨?_, ?_⟩
      · rw [cell_freeze t i j (by omega), hc]
      · -- Rewrite the four neighbors at t + 1 using cell_succ_fast and odd-odd = false at t
        have h_i2j : cell 654 t (i + 1 + 1) j = false := (ih (i + 1 + 1) j (by omega) hj).1
        have h_im2j : cell 654 t (i - 1 - 1) j = false := (ih (i - 1 - 1) j (by omega) hj).1
        have h_ij2 : cell 654 t i (j + 1 + 1) = false := (ih i (j + 1 + 1) hi (by omega)).1
        have h_ijm2 : cell 654 t i (j - 1 - 1) = false := (ih i (j - 1 - 1) hi (by omega)).1
        have h_p1m1 : i + 1 - 1 = i := by ring
        have h_m1p1 : i - 1 + 1 = i := by ring
        have h_jp1m1 : j + 1 - 1 = j := by ring
        have h_jm1p1 : j - 1 + 1 = j := by ring
        have hn1 : cell 654 (t + 1) (i + 1) j =
            fastRule (cell 654 t (i + 1) j)
              ((cell 654 t (i + 1) (j - 1)).toNat + (cell 654 t (i + 1) (j + 1)).toNat) := by
          rw [cell_succ_fast, h_i2j, h_p1m1, hc]
          congr 1; simp; omega
        have hn2 : cell 654 (t + 1) i (j + 1) =
            fastRule (cell 654 t i (j + 1))
              ((cell 654 t (i + 1) (j + 1)).toNat + (cell 654 t (i - 1) (j + 1)).toNat) := by
          rw [cell_succ_fast, h_ij2, h_jp1m1, hc]
          congr 1
        have hn3 : cell 654 (t + 1) (i - 1) j =
            fastRule (cell 654 t (i - 1) j)
              ((cell 654 t (i - 1) (j + 1)).toNat + (cell 654 t (i - 1) (j - 1)).toNat) := by
          rw [cell_succ_fast, h_m1p1, h_im2j, hc]
          congr 1; simp
        have hn4 : cell 654 (t + 1) i (j - 1) =
            fastRule (cell 654 t i (j - 1))
              ((cell 654 t (i - 1) (j - 1)).toNat + (cell 654 t (i + 1) (j - 1)).toNat) := by
          rw [cell_succ_fast, h_jm1p1, h_ijm2, hc]
          congr 1; simp; omega
        rw [hn1, hn2, hn3, hn4]
        have hs' :
            (cell 654 t (i + 1) j).toNat + (cell 654 t i (j + 1)).toNat +
            (cell 654 t (i - 1) j).toNat + (cell 654 t i (j - 1)).toNat ≠ 1 := by omega
        have hstep := odd_step_bool
          (cell 654 t (i + 1) j) (cell 654 t i (j + 1))
          (cell 654 t (i - 1) j) (cell 654 t i (j - 1))
          (cell 654 t (i + 1) (j - 1)) (cell 654 t (i + 1) (j + 1))
          (cell 654 t (i - 1) (j + 1)) (cell 654 t (i - 1) (j - 1)) hs'
        omega
    · refine ⟨?_, ?_⟩
      · rw [cell_succ_fast, hc]
        exact fastRule_false_of_ne_one _ hs
      · rw [cell_freeze t (i + 1) j (by omega),
            cell_freeze t (i - 1) j (by omega),
            cell_freeze t i (j + 1) (by omega),
            cell_freeze t i (j - 1) (by omega)]
        exact hs

private lemma cell_odd_odd_false (t : ℕ) (i j : ℤ) (hi : i % 2 = 1) (hj : j % 2 = 1) :
    cell 654 t i j = false :=
  (cell_odd_odd t i j hi hj).1

-- Outer two diagonals (Pascal mod 2)
private lemma cell_diag0 (t : ℕ) :
    ∀ x y : ℕ, x + y = t → cell 654 t (x : ℤ) (y : ℤ) = decide (Nat.choose t y % 2 = 1) := by
  induction t with
  | zero =>
    intro x y h
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst hx; subst hy; rfl
  | succ t ih =>
    intro x y h
    rw [cell_succ_fast]
    have hc : cell 654 t (x : ℤ) (y : ℤ) = false := cell_out t _ _ (by omega)
    have hr : cell 654 t ((x : ℤ) + 1) (y : ℤ) = false := cell_out t _ _ (by omega)
    have hu : cell 654 t (x : ℤ) ((y : ℤ) + 1) = false := cell_out t _ _ (by omega)
    rw [hc, hr, hu]
    cases x with
    | zero =>
      have hy : y = t + 1 := by omega
      subst y
      simp only [Nat.cast_zero]
      have hl : cell 654 t ((0 : ℤ) - 1) ((t + 1 : ℕ) : ℤ) = false := cell_out t _ _ (by omega)
      have hd : cell 654 t (0 : ℤ) (((t + 1 : ℕ) : ℤ) - 1) = true := by
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
        have hd : cell 654 t ((t + 1 : ℕ) : ℤ) ((0 : ℤ) - 1) = false := cell_out t _ _ (by omega)
        have hl : cell 654 t (((t + 1 : ℕ) : ℤ) - 1) (0 : ℤ) = true := by
          have hsub : ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) := by omega
          rw [hsub]
          have h0 := ih t 0 (by omega)
          simpa [Nat.choose_zero_right] using h0
        rw [hl, hd]
        simp [fastRule, Nat.choose_zero_right]
      | succ y' =>
        have hl : cell 654 t (((x' + 1 : ℕ) : ℤ) - 1) ((y' + 1 : ℕ) : ℤ) =
            decide (Nat.choose t (y' + 1) % 2 = 1) := by
          have hsub : ((x' + 1 : ℕ) : ℤ) - 1 = (x' : ℤ) := by omega
          rw [hsub]; exact ih x' (y' + 1) (by omega)
        have hd : cell 654 t ((x' + 1 : ℕ) : ℤ) (((y' + 1 : ℕ) : ℤ) - 1) =
            decide (Nat.choose t y' % 2 = 1) := by
          have hsub : ((y' + 1 : ℕ) : ℤ) - 1 = (y' : ℤ) := by omega
          rw [hsub]; exact ih (x' + 1) y' (by omega)
        rw [hl, hd, Nat.choose_succ_succ]
        have ha : Nat.choose t y' % 2 = 0 ∨ Nat.choose t y' % 2 = 1 := by omega
        have hb : Nat.choose t (y' + 1) % 2 = 0 ∨ Nat.choose t (y' + 1) % 2 = 1 := by omega
        rcases ha with ha | ha <;> rcases hb with hb | hb <;>
          simp [ha, hb, Nat.add_mod, fastRule]

private lemma cell_diag1 (t x y : ℕ) (h : x + y + 1 = t) :
    cell 654 t (x : ℤ) (y : ℤ) = decide (Nat.choose (t - 1) y % 2 = 1) := by
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

private lemma choose_5_mod2 (n : ℕ) :
    Nat.choose n 5 % 2 = if n % 8 = 5 ∨ n % 8 = 7 then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.add_mod, ih, choose_4_mod2]
    split_ifs <;> omega

private lemma choose_6_mod2 (n : ℕ) :
    Nat.choose n 6 % 2 = if n % 8 = 6 ∨ n % 8 = 7 then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.add_mod, ih, choose_5_mod2]
    split_ifs <;> omega

private lemma cell_diag0_y4 (t x : ℕ) (h : x + 4 = t) :
    cell 654 t (x : ℤ) 4 = decide (4 ≤ t % 8) := by
  have hc := cell_diag0 t x 4 h
  simp only [Nat.cast_ofNat] at hc
  rw [hc, choose_4_mod2]
  by_cases hr : 4 ≤ t % 8 <;> simp [hr]

private lemma cell_diag0_y5 (t x : ℕ) (h : x + 5 = t) :
    cell 654 t (x : ℤ) 5 = decide (t % 8 = 5 ∨ t % 8 = 7) := by
  have hc := cell_diag0 t x 5 h
  simp only [Nat.cast_ofNat] at hc
  rw [hc, choose_5_mod2]
  by_cases hr : t % 8 = 5 ∨ t % 8 = 7 <;> simp [hr]

private lemma cell_diag1_y5 (t x : ℕ) (h : x + 6 = t) :
    cell 654 t (x : ℤ) 5 = decide (t % 8 = 6 ∨ t % 8 = 0) := by
  have hc := cell_diag1 t x 5 (by omega)
  simp only [Nat.cast_ofNat] at hc
  rw [hc, choose_5_mod2]
  have hiff : ((t - 1) % 8 = 5 ∨ (t - 1) % 8 = 7) ↔ (t % 8 = 6 ∨ t % 8 = 0) := by omega
  by_cases hr : t % 8 = 6 ∨ t % 8 = 0
  · have h1 := hiff.mpr hr; simp [hr, h1]
  · have h1 : ¬ ((t - 1) % 8 = 5 ∨ (t - 1) % 8 = 7) := fun c => hr (hiff.mp c)
    simp [hr, h1]

private lemma cell_diag0_y6 (t x : ℕ) (h : x + 6 = t) :
    cell 654 t (x : ℤ) 6 = decide (t % 8 = 6 ∨ t % 8 = 7) := by
  have hc := cell_diag0 t x 6 h
  simp only [Nat.cast_ofNat] at hc
  rw [hc, choose_6_mod2]
  by_cases hr : t % 8 = 6 ∨ t % 8 = 7 <;> simp [hr]

-- Pure Nat/Bool lookup table for t = 0..8
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
  | 8, 0, x => x == 0 || x == 1 || x == 3 || x == 4 || x == 6 || x == 7 || x == 8
  | 8, 1, x => x == 0 || x == 2 || x == 6
  | 8, 2, x => x == 1 || x == 3 || x == 4 || x == 5
  | 8, 3, x => x == 0 || x == 2 || x == 4
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
    ∀ i j : ℤ, cell 654 t i j = tbl t i j := by
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
          cell 654 (t + 1) i' j' = tbl (t + 1) i' j' := by
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

-- Periodic interior and frontier patterns for y = 0..3 and y = 4
private def interiorY (j x : ℕ) : Bool :=
  match j with
  | 0 => decide (x % 2 = 1 ∨ x % 8 = 0)
  | 1 => decide (x % 2 = 0)
  | 2 => decide (x % 2 = 1 ∨ x % 8 = 4)
  | _ => decide (x % 2 = 0)

private lemma interiorY_mod8 (j x : ℕ) : interiorY j x = interiorY j (x % 8) := by
  unfold interiorY
  have h2 : x % 2 = (x % 8) % 2 := by omega
  have h8 : (x % 8) % 8 = x % 8 := by omega
  cases j with
  | zero => simp only [h2, h8]
  | succ j => cases j with
    | zero => simp only [h2]
    | succ j => cases j with
      | zero => simp only [h2, h8]
      | succ j => simp only [h2]

private def patY : ℕ → ℕ → ℕ → Bool
  | 0, 0, rx => rx == 0 || rx == 1 || rx == 3 || rx == 4 || rx == 6 || rx == 7 || rx == 8
  | 0, 1, rx => rx == 0 || rx == 1 || rx == 3 || rx == 4 || rx == 6 || rx == 8 || rx == 9
  | 0, 2, rx => rx == 0 || rx == 1 || rx == 3 || rx == 4 || rx == 8 || rx == 9 || rx == 10
  | 0, 3, rx => rx == 0 || rx == 1 || rx == 3 || rx == 4 || rx == 5 || rx == 7 || rx == 8 || rx == 10 || rx == 11
  | 0, 4, rx => rx == 0 || rx == 1 || rx == 3 || rx == 5 || rx == 7 || rx == 8 || rx == 10 || rx == 11 || rx == 12
  | 0, 5, rx => rx == 0 || rx == 1 || rx == 3 || rx == 5 || rx == 7 || rx == 8 || rx == 10 || rx == 12 || rx == 13
  | 0, 6, rx => rx == 0 || rx == 1 || rx == 3 || rx == 5 || rx == 7 || rx == 8 || rx == 12 || rx == 13 || rx == 14
  | 0, 7, rx => rx == 0 || rx == 1 || rx == 3 || rx == 5 || rx == 7 || rx == 8 || rx == 9 || rx == 11 || rx == 12 || rx == 14 || rx == 15
  | 1, 0, rx => rx == 0 || rx == 2 || rx == 6
  | 1, 1, rx => rx == 0 || rx == 2 || rx == 6 || rx == 8
  | 1, 2, rx => rx == 0 || rx == 2 || rx == 6 || rx == 8
  | 1, 3, rx => rx == 0 || rx == 2 || rx == 6 || rx == 10
  | 1, 4, rx => rx == 0 || rx == 2 || rx == 6 || rx == 10
  | 1, 5, rx => rx == 0 || rx == 2 || rx == 4 || rx == 6 || rx == 10 || rx == 12
  | 1, 6, rx => rx == 0 || rx == 2 || rx == 4 || rx == 6 || rx == 10 || rx == 12
  | 1, 7, rx => rx == 0 || rx == 2 || rx == 4 || rx == 6 || rx == 8 || rx == 10 || rx == 14
  | 2, 0, rx => rx == 1 || rx == 3 || rx == 4 || rx == 5
  | 2, 1, rx => rx == 1 || rx == 3 || rx == 4 || rx == 5
  | 2, 2, rx => rx == 1 || rx == 3 || rx == 4 || rx == 5 || rx == 8
  | 2, 3, rx => rx == 1 || rx == 3 || rx == 4 || rx == 5 || rx == 7 || rx == 8 || rx == 9
  | 2, 4, rx => rx == 1 || rx == 3 || rx == 4 || rx == 5 || rx == 7 || rx == 8 || rx == 9
  | 2, 5, rx => rx == 1 || rx == 3 || rx == 4 || rx == 5 || rx == 7 || rx == 8 || rx == 9
  | 2, 6, rx => rx == 1 || rx == 3 || rx == 4 || rx == 5 || rx == 7 || rx == 9 || rx == 12
  | 2, 7, rx => rx == 1 || rx == 3 || rx == 4 || rx == 5 || rx == 7 || rx == 9 || rx == 11 || rx == 12 || rx == 13
  | 3, 0, rx => rx == 0 || rx == 2 || rx == 4
  | 3, 1, rx => rx == 0 || rx == 2 || rx == 4
  | 3, 2, rx => rx == 0 || rx == 2 || rx == 4
  | 3, 3, rx => rx == 0 || rx == 2 || rx == 4 || rx == 8
  | 3, 4, rx => rx == 0 || rx == 2 || rx == 4 || rx == 8
  | 3, 5, rx => rx == 0 || rx == 2 || rx == 4
  | 3, 6, rx => rx == 0 || rx == 2 || rx == 4
  | 3, 7, rx => rx == 0 || rx == 2 || rx == 4 || rx == 6 || rx == 8 || rx == 10 || rx == 12
  | _, _, _ => false

private def pat4 (r rx : ℕ) : Bool :=
  match r with
  | 4 => rx == 8
  | 5 => rx == 7 || rx == 8 || rx == 9
  | 6 => rx == 6 || rx == 7 || rx == 8 || rx == 9 || rx == 10
  | 7 => rx == 8 || rx == 10 || rx == 11
  | _ => false

private def pat4May (r rx : ℕ) (u : Bool) : Bool :=
  if rx = 2 ∨ rx = 3 then true
  else if rx = 4 then false
  else if r ≤ 6 ∧ 4 ≤ rx then pat4 r rx
  else if r = 7 ∧ 8 ≤ rx then pat4 7 rx
  else u

private def y5May (r rx : ℕ) (u : Bool) : Bool :=
  if rx % 2 = 1 then false
  else if 8 + r < rx + 5 then false
  else if rx + 5 = 8 + r then decide (r = 5 ∨ r = 7)
  else if rx + 5 = 7 + r then decide (r = 0 ∨ r = 6)
  else if r = 5 ∧ rx = 6 then false
  else u

private def baseT (t : ℕ) : ℕ := 8 * (t / 8 - 1)

private def specY (j t x : ℕ) : Bool :=
  if x < baseT t then interiorY j x else patY j (t % 8) (x - baseT t)

private def patYExt (j r rx : ℕ) : Bool :=
  match rx with
  | 0 => interiorY j 7
  | rx' + 1 => patY j r rx'

private def nextSpec (j r rx : ℕ) : Bool :=
  if r < 7 then patY j (r + 1) rx
  else if rx < 8 then interiorY j rx
  else patY j 0 (rx - 8)

private lemma patY_zero_eq : ∀ j : Fin 4, ∀ r : Fin 8, patY j.1 r.1 0 = interiorY j.1 0 := by decide
private lemma patY_one_eq : ∀ j : Fin 4, ∀ r : Fin 8, patY j.1 r.1 1 = interiorY j.1 7 := by decide
private lemma interiorY_one_eq_seven : ∀ j : Fin 4, interiorY j.1 1 = interiorY j.1 7 := by decide

private lemma patY_out (j r rx : ℕ) (hj : j < 4) (hr : r < 8) (h : r + 8 < rx) :
    patY j r rx = false := by
  by_cases h16 : rx < 16
  · have h' : ∀ a : Fin 4, ∀ b : Fin 8, ∀ c : Fin 16, b.1 + 8 < c.1 → patY a.1 b.1 c.1 = false := by decide
    exact h' ⟨j, hj⟩ ⟨r, hr⟩ ⟨rx, h16⟩ h
  · interval_cases j <;> interval_cases r <;> simp [patY] <;> omega

private lemma pat4_out (r rx : ℕ) (hr : r < 8) (h : r + 4 < rx) :
    pat4 r rx = false := by
  interval_cases r <;> simp [pat4] <;> omega

-- Finite transition checks proved by decide
private lemma interior_step : ∀ j : Fin 4, ∀ m : Fin 8, ∀ u : Bool,
    fastRule (interiorY j.1 m.1)
      ((interiorY j.1 ((m.1 + 1) % 8)).toNat +
       (interiorY j.1 ((m.1 + 7) % 8)).toNat +
       (if j.1 < 3 then interiorY (j.1 + 1) m.1 else if m.1 = 4 then false else u).toNat +
       (if j.1 = 0 then interiorY 1 m.1 else interiorY (j.1 - 1) m.1).toNat) =
    interiorY j.1 m.1 := by decide

private lemma frontier_step : ∀ j : Fin 4, ∀ r : Fin 8, ∀ rx : Fin 17, ∀ u : Bool,
    fastRule (patYExt j.1 r.1 (rx.1 + 1))
      ((patYExt j.1 r.1 (rx.1 + 2)).toNat +
       (patYExt j.1 r.1 rx.1).toNat +
       (if j.1 < 3 then patYExt (j.1 + 1) r.1 (rx.1 + 1) else pat4May r.1 rx.1 u).toNat +
       (if j.1 = 0 then patYExt 1 r.1 (rx.1 + 1) else patYExt (j.1 - 1) r.1 (rx.1 + 1)).toNat) =
    nextSpec j.1 r.1 rx.1 := by decide

private lemma f4_step_dec : ∀ r : Fin 7, ∀ rx : Fin 13, ∀ u : Bool,
    (r.1 ≤ 5 → 4 ≤ rx.1) →
    (r.1 = 6 → 8 ≤ rx.1) →
    rx.1 ≤ r.1 + 5 →
    fastRule (pat4 r.1 rx.1)
      ((pat4 r.1 (rx.1 + 1)).toNat +
       (if rx.1 = 4 then true else pat4 r.1 (rx.1 - 1)).toNat +
       (y5May r.1 rx.1 u).toNat +
       (patY 3 r.1 rx.1).toNat) =
    pat4 (r.1 + 1) rx.1 := by decide

private lemma patY3_b42_dec : ∀ r : Fin 8, ∀ rx : Fin 16,
    rx.1 % 8 = 2 → rx.1 + 5 ≤ 8 + r.1 → patY 3 r.1 rx.1 = true := by decide

private lemma patY3_b44_dec : ∀ r : Fin 8, ∀ rx : Fin 16,
    rx.1 % 8 = 4 → rx.1 + 4 ≤ 8 + r.1 → patY 3 r.1 rx.1 = true := by decide

private structure Inv (t : ℕ) : Prop where
  y0 : ∀ x : ℕ, cell 654 t (x : ℤ) 0 = specY 0 t x
  y1 : ∀ x : ℕ, cell 654 t (x : ℤ) 1 = specY 1 t x
  y2 : ∀ x : ℕ, cell 654 t (x : ℤ) 2 = specY 2 t x
  y3 : ∀ x : ℕ, cell 654 t (x : ℤ) 3 = specY 3 t x
  b61 : ∀ x : ℕ, x % 8 = 1 → x + 6 ≤ t → cell 654 t (x : ℤ) 6 = true
  b62 : ∀ x : ℕ, x % 8 = 2 → cell 654 t (x : ℤ) 6 = false
  b52 : ∀ x : ℕ, x % 8 = 2 → x + 5 ≤ t → cell 654 t (x : ℤ) 5 = true
  b42 : ∀ x : ℕ, x % 8 = 2 → x + 4 ≤ t → cell 654 t (x : ℤ) 4 = true
  b43 : ∀ x : ℕ, x % 8 = 3 → x + 4 ≤ t → cell 654 t (x : ℤ) 4 = true
  b44 : ∀ x : ℕ, x % 8 = 4 → cell 654 t (x : ℤ) 4 = false
  f4 : ∀ rx : ℕ, (t % 8 ≤ 6 → 4 ≤ rx) → (t % 8 = 7 → 8 ≤ rx) →
        cell 654 t ((baseT t + rx : ℕ) : ℤ) 4 = pat4 (t % 8) rx
  f5 : t % 8 = 5 → cell 654 t ((baseT t + 6 : ℕ) : ℤ) 5 = false

private lemma inv_base : Inv 8 where
  y0 x := by
    rw [cell_eq_tbl 8 (by omega)]
    by_cases hx : x < 9
    · interval_cases x <;> rfl
    · rw [tbl_out 8 (by omega) _ _ (by omega)]
      simp only [specY, baseT]
      exact (patY_out 0 0 x (by omega) (by omega) (by omega)).symm
  y1 x := by
    rw [cell_eq_tbl 8 (by omega)]
    by_cases hx : x < 9
    · interval_cases x <;> rfl
    · rw [tbl_out 8 (by omega) _ _ (by omega)]
      simp only [specY, baseT]
      exact (patY_out 1 0 x (by omega) (by omega) (by omega)).symm
  y2 x := by
    rw [cell_eq_tbl 8 (by omega)]
    by_cases hx : x < 9
    · interval_cases x <;> rfl
    · rw [tbl_out 8 (by omega) _ _ (by omega)]
      simp only [specY, baseT]
      exact (patY_out 2 0 x (by omega) (by omega) (by omega)).symm
  y3 x := by
    rw [cell_eq_tbl 8 (by omega)]
    by_cases hx : x < 9
    · interval_cases x <;> rfl
    · rw [tbl_out 8 (by omega) _ _ (by omega)]
      simp only [specY, baseT]
      exact (patY_out 3 0 x (by omega) (by omega) (by omega)).symm
  b61 x hm hle := by
    have hx : x = 1 := by omega
    subst hx; rw [cell_eq_tbl 8 (by omega)]; rfl
  b62 x hm := by
    rw [cell_eq_tbl 8 (by omega)]
    by_cases hx : x ≤ 2
    · have hx2 : x = 2 := by omega
      subst hx2; rfl
    · exact tbl_out 8 (by omega) _ _ (by omega)
  b52 x hm hle := by
    have hx : x = 2 := by omega
    subst hx; rw [cell_eq_tbl 8 (by omega)]; rfl
  b42 x hm hle := by
    have hx : x = 2 := by omega
    subst hx; rw [cell_eq_tbl 8 (by omega)]; rfl
  b43 x hm hle := by
    have hx : x = 3 := by omega
    subst hx; rw [cell_eq_tbl 8 (by omega)]; rfl
  b44 x hm := by
    rw [cell_eq_tbl 8 (by omega)]
    by_cases hx : x ≤ 4
    · have hx4 : x = 4 := by omega
      subst hx4; rfl
    · exact tbl_out 8 (by omega) _ _ (by omega)
  f4 rx h1 _ := by
    have h4 : 4 ≤ rx := h1 (by omega)
    have hbase : baseT 8 = 0 := rfl
    rw [hbase, Nat.zero_add, cell_eq_tbl 8 (by omega)]
    by_cases hrx : rx = 4
    · subst hrx; rfl
    · rw [tbl_out 8 (by omega) _ _ (by omega)]; rfl
  f5 h := by omega

private lemma cast_add_one (x : ℕ) : (x : ℤ) + 1 = ((x + 1 : ℕ) : ℤ) := by omega
private lemma cast_sub_one (x : ℕ) (hx : 1 ≤ x) : (x : ℤ) - 1 = ((x - 1 : ℕ) : ℤ) := by omega

private lemma cell_y_m1 (t x : ℕ) :
    cell 654 t (x : ℤ) ((0 : ℤ) - 1) = cell 654 t (x : ℤ) 1 := by
  have : (0 : ℤ) - 1 = -(1 : ℤ) := by norm_num
  rw [this, cell_neg_y]

private lemma inv_y (t : ℕ) (h : Inv t) (j : ℕ) (hj : j < 4) (x : ℕ) :
    cell 654 t (x : ℤ) (j : ℤ) = specY j t x := by
  interval_cases j
  · exact h.y0 x
  · exact h.y1 x
  · exact h.y2 x
  · exact h.y3 x

private lemma specY_interior_right (j t x : ℕ) (hj : j < 4) (hx : x < baseT t) :
    specY j t (x + 1) = interiorY j ((x % 8 + 1) % 8) := by
  unfold specY
  by_cases h1 : x + 1 < baseT t
  · rw [if_pos h1, interiorY_mod8]
    have hm : (x + 1) % 8 = (x % 8 + 1) % 8 := by omega
    rw [hm]
  · rw [if_neg h1]
    have heq : x + 1 = baseT t := by omega
    have hsub : x + 1 - baseT t = 0 := by omega
    have hm : (x % 8 + 1) % 8 = 0 := by
      unfold baseT at heq; omega
    rw [hsub, hm]
    exact patY_zero_eq ⟨j, hj⟩ ⟨t % 8, Nat.mod_lt _ (by omega)⟩

private lemma cell_interior_left (t : ℕ) (h : Inv t) (j x : ℕ) (hj : j < 4) (hx : x < baseT t) :
    cell 654 t ((x : ℤ) - 1) (j : ℤ) = interiorY j ((x % 8 + 7) % 8) := by
  cases x with
  | zero =>
    have hneg : ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
    rw [hneg, cell_neg_x, inv_y t h j hj 1]
    unfold specY
    have h1 : 1 < baseT t := by unfold baseT at *; omega
    rw [if_pos h1]
    exact interiorY_one_eq_seven ⟨j, hj⟩
  | succ x' =>
    have hsub : ((x' + 1 : ℕ) : ℤ) - 1 = (x' : ℤ) := by omega
    rw [hsub, inv_y t h j hj x']
    unfold specY
    rw [if_pos (by omega), interiorY_mod8]
    have hm : x' % 8 = ((x' + 1) % 8 + 7) % 8 := by omega
    rw [hm]

private lemma cell_frontier_left (t : ℕ) (h : Inv t) (j rx : ℕ) (hj : j < 4) :
    cell 654 t (((baseT t + rx : ℕ) : ℤ) - 1) (j : ℤ) = patYExt j (t % 8) rx := by
  cases rx with
  | zero =>
    rw [Nat.add_zero]
    by_cases hb : baseT t = 0
    · rw [hb]
      have hneg : ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) := by norm_num
      rw [hneg, cell_neg_x, inv_y t h j hj 1]
      unfold specY
      rw [if_neg (by omega), hb, Nat.sub_zero]
      exact patY_one_eq ⟨j, hj⟩ ⟨t % 8, Nat.mod_lt _ (by omega)⟩
    · rw [cast_sub_one (baseT t) (by omega), inv_y t h j hj (baseT t - 1)]
      unfold specY
      rw [if_pos (by omega), interiorY_mod8]
      have hm : (baseT t - 1) % 8 = 7 := by unfold baseT at *; omega
      rw [hm]; rfl
  | succ rx' =>
    rw [cast_sub_one (baseT t + (rx' + 1)) (by omega)]
    have hsub : baseT t + (rx' + 1) - 1 = baseT t + rx' := by omega
    rw [hsub, inv_y t h j hj (baseT t + rx')]
    unfold specY
    rw [if_neg (by omega), Nat.add_sub_cancel_left]
    rfl

private lemma specY_next_eq (j t rx : ℕ) (ht : 8 ≤ t) :
    specY j (t + 1) (baseT t + rx) = nextSpec j (t % 8) rx := by
  unfold specY nextSpec baseT
  by_cases h7 : t % 8 < 7
  · have hdiv : (t + 1) / 8 = t / 8 := by omega
    have hmod : (t + 1) % 8 = t % 8 + 1 := by omega
    rw [if_pos h7, hdiv, hmod, if_neg (by omega), Nat.add_sub_cancel_left]
  · have hr7 : t % 8 = 7 := by omega
    have hdiv : (t + 1) / 8 = t / 8 + 1 := by omega
    have hmod : (t + 1) % 8 = 0 := by omega
    have hb : 8 * ((t + 1) / 8 - 1) = 8 * (t / 8 - 1) + 8 := by omega
    rw [if_neg h7, hb, hmod]
    by_cases hrx : rx < 8
    · rw [if_pos hrx, if_pos (by omega), interiorY_mod8, interiorY_mod8 j rx]
      have hm : (8 * (t / 8 - 1) + rx) % 8 = rx % 8 := by omega
      rw [hm]
    · rw [if_neg hrx, if_neg (by omega)]
      have hsub : 8 * (t / 8 - 1) + rx - (8 * (t / 8 - 1) + 8) = rx - 8 := by omega
      rw [hsub]

private lemma inv_step_y (t : ℕ) (ht : 8 ≤ t) (h : Inv t) (j : ℕ) (hj : j < 4) (x : ℕ) :
    cell 654 (t + 1) (x : ℤ) (j : ℤ) = specY j (t + 1) x := by
  by_cases hgt : t + 1 < x
  · rw [cell_out (t + 1) _ _ (by omega)]
    unfold specY
    have hge : baseT (t + 1) ≤ x := by unfold baseT; omega
    rw [if_neg (by omega)]
    have hrx : (t + 1) % 8 + 8 < x - baseT (t + 1) := by unfold baseT; omega
    exact (patY_out j ((t + 1) % 8) (x - baseT (t + 1)) hj (Nat.mod_lt _ (by omega)) hrx).symm
  · by_cases hx : x < baseT t
    · have hx' : x < baseT (t + 1) := by unfold baseT at *; omega
      rw [cell_succ_fast, cast_add_one]
      have hc : cell 654 t (x : ℤ) (j : ℤ) = interiorY j (x % 8) := by
        rw [inv_y t h j hj x]; unfold specY; rw [if_pos hx, interiorY_mod8]
      have hr : cell 654 t ((x + 1 : ℕ) : ℤ) (j : ℤ) = interiorY j ((x % 8 + 1) % 8) := by
        rw [inv_y t h j hj (x + 1)]; exact specY_interior_right j t x hj hx
      have hl : cell 654 t ((x : ℤ) - 1) (j : ℤ) = interiorY j ((x % 8 + 7) % 8) :=
        cell_interior_left t h j x hj hx
      have hd : cell 654 t (x : ℤ) ((j : ℤ) - 1) =
          if j = 0 then interiorY 1 (x % 8) else interiorY (j - 1) (x % 8) := by
        cases j with
        | zero =>
          simp only [Nat.cast_zero, ↓reduceIte]
          rw [cell_y_m1, h.y1 x]; unfold specY; rw [if_pos hx, interiorY_mod8]
        | succ j' =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          have hsub : ((j' + 1 : ℕ) : ℤ) - 1 = (j' : ℤ) := by omega
          rw [hsub, inv_y t h j' (by omega) x]; unfold specY; rw [if_pos hx, interiorY_mod8]
      have hu : cell 654 t (x : ℤ) ((j : ℤ) + 1) =
          if j < 3 then interiorY (j + 1) (x % 8)
          else if x % 8 = 4 then false else cell 654 t (x : ℤ) 4 := by
        by_cases hj3 : j < 3
        · simp only [hj3, ↓reduceIte]
          have hadd : (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) := by omega
          rw [hadd, inv_y t h (j + 1) (by omega) x]; unfold specY; rw [if_pos hx, interiorY_mod8]
        · have hj_eq : j = 3 := by omega
          subst hj_eq
          simp only [show ¬ (3 < 3) by omega, ↓reduceIte]
          have h34 : ((3 : ℕ) : ℤ) + 1 = 4 := by norm_num
          rw [h34]
          by_cases hm4 : x % 8 = 4
          · simp only [hm4, ↓reduceIte]; exact h.b44 x hm4
          · simp only [hm4, ↓reduceIte]
      rw [hc, hr, hl, hd, hu]
      have hres := interior_step ⟨j, hj⟩ ⟨x % 8, Nat.mod_lt _ (by omega)⟩ (cell 654 t (x : ℤ) 4)
      have hspec : specY j (t + 1) x = interiorY j (x % 8) := by
        unfold specY; rw [if_pos hx', interiorY_mod8]
      rw [hspec]
      exact hres
    · set rx := x - baseT t with hrx_def
      have hx_eq : x = baseT t + rx := by omega
      have hrx_lt : rx < 17 := by unfold baseT at *; omega
      rw [hx_eq, cell_succ_fast, cast_add_one, specY_next_eq j t rx ht]
      have hc : cell 654 t ((baseT t + rx : ℕ) : ℤ) (j : ℤ) = patYExt j (t % 8) (rx + 1) := by
        rw [inv_y t h j hj (baseT t + rx)]; unfold specY
        rw [if_neg (by omega), Nat.add_sub_cancel_left]; rfl
      have hr : cell 654 t ((baseT t + rx + 1 : ℕ) : ℤ) (j : ℤ) = patYExt j (t % 8) (rx + 2) := by
        have hadd : baseT t + rx + 1 = baseT t + (rx + 1) := by omega
        rw [hadd, inv_y t h j hj (baseT t + (rx + 1))]; unfold specY
        rw [if_neg (by omega), Nat.add_sub_cancel_left]; rfl
      have hl : cell 654 t (((baseT t + rx : ℕ) : ℤ) - 1) (j : ℤ) = patYExt j (t % 8) rx :=
        cell_frontier_left t h j rx hj
      have hd : cell 654 t ((baseT t + rx : ℕ) : ℤ) ((j : ℤ) - 1) =
          if j = 0 then patYExt 1 (t % 8) (rx + 1) else patYExt (j - 1) (t % 8) (rx + 1) := by
        cases j with
        | zero =>
          simp only [Nat.cast_zero, ↓reduceIte]
          rw [cell_y_m1, h.y1 (baseT t + rx)]; unfold specY
          rw [if_neg (by omega), Nat.add_sub_cancel_left]; rfl
        | succ j' =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          have hsub : ((j' + 1 : ℕ) : ℤ) - 1 = (j' : ℤ) := by omega
          rw [hsub, inv_y t h j' (by omega) (baseT t + rx)]; unfold specY
          rw [if_neg (by omega), Nat.add_sub_cancel_left]; rfl
      have hu : cell 654 t ((baseT t + rx : ℕ) : ℤ) ((j : ℤ) + 1) =
          if j < 3 then patYExt (j + 1) (t % 8) (rx + 1)
          else pat4May (t % 8) rx (cell 654 t ((baseT t + rx : ℕ) : ℤ) 4) := by
        by_cases hj3 : j < 3
        · simp only [hj3, ↓reduceIte]
          have hadd : (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) := by omega
          rw [hadd, inv_y t h (j + 1) (by omega) (baseT t + rx)]; unfold specY
          rw [if_neg (by omega), Nat.add_sub_cancel_left]; rfl
        · have hj_eq : j = 3 := by omega
          subst hj_eq
          simp only [show ¬ (3 < 3) by omega, ↓reduceIte]
          have h34 : ((3 : ℕ) : ℤ) + 1 = 4 := by norm_num
          rw [h34]
          unfold pat4May
          split_ifs with c1 c2 c3 c4
          · rcases c1 with hrx2 | hrx3
            · rw [hrx2]
              exact h.b42 (baseT t + 2) (by unfold baseT; omega) (by unfold baseT; omega)
            · rw [hrx3]
              exact h.b43 (baseT t + 3) (by unfold baseT; omega) (by unfold baseT; omega)
          · rw [c2]
            exact h.b44 (baseT t + 4) (by unfold baseT; omega)
          · exact h.f4 rx (fun _ => c3.2) (fun h7 => by omega)
          · rw [← c4.1]
            exact h.f4 rx (fun h6 => by omega) (fun _ => c4.2)
          · rfl
      rw [hc, hr, hl, hd, hu]
      exact frontier_step ⟨j, hj⟩ ⟨t % 8, Nat.mod_lt _ (by omega)⟩ ⟨rx, hrx_lt⟩
        (cell 654 t ((baseT t + rx : ℕ) : ℤ) 4)

private lemma specY3_b42 (t x : ℕ) (ht : 8 ≤ t) (hm : x % 8 = 2) (hle : x + 5 ≤ t) :
    specY 3 t x = true := by
  unfold specY
  by_cases hx : x < baseT t
  · rw [if_pos hx]; unfold interiorY; simp; omega
  · rw [if_neg hx]
    have hrx_lt : x - baseT t < 16 := by unfold baseT at *; omega
    have h1 : (x - baseT t) % 8 = 2 := by unfold baseT at *; omega
    have h2 : (x - baseT t) + 5 ≤ 8 + t % 8 := by unfold baseT at *; omega
    exact patY3_b42_dec ⟨t % 8, Nat.mod_lt _ (by omega)⟩ ⟨x - baseT t, hrx_lt⟩ h1 h2

private lemma specY3_b44 (t x : ℕ) (ht : 8 ≤ t) (hm : x % 8 = 4) (hle : x + 4 ≤ t) :
    specY 3 t x = true := by
  unfold specY
  by_cases hx : x < baseT t
  · rw [if_pos hx]; unfold interiorY; simp; omega
  · rw [if_neg hx]
    have hrx_lt : x - baseT t < 16 := by unfold baseT at *; omega
    have h1 : (x - baseT t) % 8 = 4 := by unfold baseT at *; omega
    have h2 : (x - baseT t) + 4 ≤ 8 + t % 8 := by unfold baseT at *; omega
    exact patY3_b44_dec ⟨t % 8, Nat.mod_lt _ (by omega)⟩ ⟨x - baseT t, hrx_lt⟩ h1 h2

private lemma inv_step (t : ℕ) (ht : 8 ≤ t) (h : Inv t) : Inv (t + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_step_y t ht h 0 (by omega)
  · exact inv_step_y t ht h 1 (by omega)
  · exact inv_step_y t ht h 2 (by omega)
  · exact inv_step_y t ht h 3 (by omega)
  · -- b61
    intro x hm hle
    by_cases heq : x + 6 = t + 1
    · rw [cell_diag0_y6 (t + 1) x heq]
      have hmod : (t + 1) % 8 = 7 := by omega
      simp [hmod]
    · rw [cell_succ_fast, cast_add_one]
      have h67 : (6 : ℤ) + 1 = 7 := by norm_num
      have h65 : (6 : ℤ) - 1 = 5 := by norm_num
      rw [h67, h65,
          h.b61 x hm (by omega),
          h.b62 (x + 1) (by omega),
          cell_odd_odd_false t (x : ℤ) 7 (by omega) (by omega),
          cell_odd_odd_false t (x : ℤ) 5 (by omega) (by omega)]
      apply fastRule_true_of_ne_two
      have b := bool_toNat_le_one (cell 654 t ((x : ℤ) - 1) 6)
      simp; omega
  · -- b62
    intro x hm
    by_cases hout : t + 1 < x + 6
    · exact cell_out (t + 1) _ _ (by omega)
    · by_cases heq : x + 6 = t + 1
      · rw [cell_diag0_y6 (t + 1) x heq]
        have hmod : (t + 1) % 8 = 0 := by omega
        simp [hmod]
      · rw [cell_succ_fast, cast_sub_one x (by omega)]
        have h65 : (6 : ℤ) - 1 = 5 := by norm_num
        rw [h65, h.b62 x hm, h.b61 (x - 1) (by omega) (by omega), h.b52 x hm (by omega)]
        apply fastRule_false_of_ne_one
        simp
  · -- b52
    intro x hm hle
    by_cases heq : x + 5 = t + 1
    · rw [cell_diag0_y5 (t + 1) x heq]
      have hmod : (t + 1) % 8 = 7 := by omega
      simp [hmod]
    · rw [cell_succ_fast]
      have h56 : (5 : ℤ) + 1 = 6 := by norm_num
      have h54 : (5 : ℤ) - 1 = 4 := by norm_num
      rw [h56, h54,
          cell_odd_odd_false t ((x : ℤ) + 1) 5 (by omega) (by omega),
          cell_odd_odd_false t ((x : ℤ) - 1) 5 (by omega) (by omega),
          h.b62 x hm,
          h.b42 x hm (by omega)]
      rfl
  · -- b42
    intro x hm hle
    by_cases heq1 : x + 4 = t + 1
    · rw [cell_diag0_y4 (t + 1) x heq1]
      have hmod : (t + 1) % 8 = 6 := by omega
      simp [hmod]
    · by_cases heq2 : x + 4 = t
      · rw [cell_freeze t (x : ℤ) 4 (by omega), h.b42 x hm (by omega)]
      · rw [cell_succ_fast, cast_add_one]
        have h45 : (4 : ℤ) + 1 = 5 := by norm_num
        have h43 : (4 : ℤ) - 1 = 3 := by norm_num
        rw [h45, h43,
            h.b42 x hm (by omega),
            h.b43 (x + 1) (by omega) (by omega),
            h.b52 x hm (by omega),
            h.y3 x, specY3_b42 t x ht hm (by omega)]
        apply fastRule_true_of_ne_two
        simp
  · -- b43
    intro x hm hle
    by_cases heq : x + 4 = t + 1
    · rw [cell_diag0_y4 (t + 1) x heq]
      have hmod : (t + 1) % 8 = 7 := by omega
      simp [hmod]
    · rw [cell_succ_fast, cast_add_one, cast_sub_one x (by omega)]
      have h45 : (4 : ℤ) + 1 = 5 := by norm_num
      have h43 : (4 : ℤ) - 1 = 3 := by norm_num
      rw [h45, h43,
          h.b44 (x + 1) (by omega),
          h.b42 (x - 1) (by omega) (by omega),
          cell_odd_odd_false t (x : ℤ) 5 (by omega) (by omega),
          cell_odd_odd_false t (x : ℤ) 3 (by omega) (by omega)]
      rfl
  · -- b44
    intro x hm
    by_cases hout : t + 1 < x + 4
    · exact cell_out (t + 1) _ _ (by omega)
    · by_cases heq : x + 4 = t + 1
      · rw [cell_diag0_y4 (t + 1) x heq]
        have hmod : (t + 1) % 8 = 0 := by omega
        simp [hmod]
      · rw [cell_succ_fast, cast_sub_one x (by omega)]
        have h43 : (4 : ℤ) - 1 = 3 := by norm_num
        rw [h43, h.b44 x hm, h.b43 (x - 1) (by omega) (by omega),
            h.y3 x, specY3_b44 t x ht hm (by omega)]
        apply fastRule_false_of_ne_one
        simp
  · -- f4
    intro rx hle6 h7
    by_cases hr7 : t % 8 = 7
    · have hmod : (t + 1) % 8 = 0 := by omega
      have h4 : 4 ≤ rx := hle6 (by omega)
      rw [hmod]
      change cell 654 (t + 1) ((baseT (t + 1) + rx : ℕ) : ℤ) 4 = false
      by_cases hrx4 : rx = 4
      · rw [cell_diag0_y4 (t + 1) (baseT (t + 1) + rx) (by unfold baseT; omega)]
        simp [hmod]
      · exact cell_out (t + 1) _ _ (by unfold baseT; omega)
    · have hr_lt : t % 8 < 7 := by omega
      have hbase_eq : baseT (t + 1) = baseT t := by unfold baseT; omega
      have hmod : (t + 1) % 8 = t % 8 + 1 := by omega
      rw [hbase_eq, hmod]
      by_cases hout : t % 8 + 5 < rx
      · rw [cell_out (t + 1) _ _ (by unfold baseT; omega)]
        exact (pat4_out (t % 8 + 1) rx (by omega) (by omega)).symm
      · have hrx_le : rx ≤ t % 8 + 5 := by omega
        have hrx_lt : rx < 13 := by omega
        have hrx4 : 4 ≤ rx := by
          by_cases hr5 : t % 8 ≤ 5
          · exact hle6 (by omega)
          · have hr6 : t % 8 = 6 := by omega
            have h8 := h7 (by omega)
            omega
        rw [cell_succ_fast, cast_add_one, cast_sub_one (baseT t + rx) (by omega)]
        have h45 : (4 : ℤ) + 1 = 5 := by norm_num
        have h43 : (4 : ℤ) - 1 = 3 := by norm_num
        rw [h45, h43]
        have hc : cell 654 t ((baseT t + rx : ℕ) : ℤ) 4 = pat4 (t % 8) rx :=
          h.f4 rx (fun _ => hrx4) (fun hc7 => by omega)
        have hright : cell 654 t ((baseT t + rx + 1 : ℕ) : ℤ) 4 = pat4 (t % 8) (rx + 1) := by
          have ha : baseT t + rx + 1 = baseT t + (rx + 1) := by omega
          rw [ha]
          exact h.f4 (rx + 1) (fun _ => by omega) (fun hc7 => by omega)
        have hleft : cell 654 t ((baseT t + rx - 1 : ℕ) : ℤ) 4 =
            if rx = 4 then true else pat4 (t % 8) (rx - 1) := by
          by_cases hx4 : rx = 4
          · simp only [hx4, ↓reduceIte]
            exact h.b43 (baseT t + 4 - 1) (by unfold baseT; omega) (by unfold baseT; omega)
          · simp only [hx4, ↓reduceIte]
            have ha : baseT t + rx - 1 = baseT t + (rx - 1) := by omega
            rw [ha]
            exact h.f4 (rx - 1) (fun _ => by omega) (fun hc7 => by omega)
        have hdown : cell 654 t ((baseT t + rx : ℕ) : ℤ) 3 = patY 3 (t % 8) rx := by
          rw [h.y3 (baseT t + rx)]; unfold specY
          rw [if_neg (by omega), Nat.add_sub_cancel_left]
        have hup : cell 654 t ((baseT t + rx : ℕ) : ℤ) 5 =
            y5May (t % 8) rx (cell 654 t ((baseT t + rx : ℕ) : ℤ) 5) := by
          unfold y5May
          split_ifs with c1 c2 c3 c4 c5
          · exact cell_odd_odd_false t _ 5 (by unfold baseT; omega) (by omega)
          · exact cell_out t _ _ (by unfold baseT; omega)
          · exact cell_diag0_y5 t (baseT t + rx) (by unfold baseT; omega)
          · have hd1 := cell_diag1_y5 t (baseT t + rx) (by unfold baseT; omega)
            rw [hd1]
            have hiff : (t % 8 = 6 ∨ t % 8 = 0) ↔ (t % 8 = 0 ∨ t % 8 = 6) := by tauto
            exact decide_eq_decide.mpr hiff
          · rw [c5.2]
            exact h.f5 c5.1
          · rfl
        rw [hc, hright, hleft, hdown, hup]
        have h5' : t % 8 ≤ 5 → 4 ≤ rx := fun hr5 => hle6 (by omega)
        have h6' : t % 8 = 6 → 8 ≤ rx := fun hr6 => h7 (by omega)
        exact f4_step_dec ⟨t % 8, hr_lt⟩ ⟨rx, hrx_lt⟩
          (cell 654 t ((baseT t + rx : ℕ) : ℤ) 5) h5' h6' hrx_le
  · -- f5
    intro hmod5
    have hr4 : t % 8 = 4 := by omega
    have hbase_eq : baseT (t + 1) = baseT t := by unfold baseT; omega
    rw [hbase_eq, cell_succ_fast]
    have h56 : (5 : ℤ) + 1 = 6 := by norm_num
    have h54 : (5 : ℤ) - 1 = 4 := by norm_num
    rw [h56, h54]
    have hc : cell 654 t ((baseT t + 6 : ℕ) : ℤ) 5 = false := by
      rw [cell_diag1_y5 t (baseT t + 6) (by unfold baseT; omega)]
      simp [hr4]
    have hl : cell 654 t (((baseT t + 6 : ℕ) : ℤ) - 1) 5 = false :=
      cell_odd_odd_false t _ 5 (by unfold baseT; omega) (by omega)
    have hr : cell 654 t (((baseT t + 6 : ℕ) : ℤ) + 1) 5 = false :=
      cell_odd_odd_false t _ 5 (by unfold baseT; omega) (by omega)
    have hd : cell 654 t ((baseT t + 6 : ℕ) : ℤ) 4 = false := by
      rw [h.f4 6 (fun _ => by omega) (fun hc7 => by omega), hr4]; rfl
    have hu : cell 654 t ((baseT t + 6 : ℕ) : ℤ) 6 = false := by
      rw [cell_diag0_y6 t (baseT t + 6) (by unfold baseT; omega)]
      simp [hr4]
    rw [hc, hl, hr, hd, hu]
    rfl

private lemma inv_ge8 (t : ℕ) (ht : 8 ≤ t) : Inv t := by
  induction t, ht using Nat.le_induction with
  | base => exact inv_base
  | succ k hk ih => exact inv_step k hk ih

-- Period-8 first difference a(n) - 10 * a(n - 1) = diffD n for n >= 9
private def diffD (n : ℕ) : ℤ :=
  match n % 8 with
  | 0 => 1
  | 1 => -99
  | 2 => -9999
  | 3 => 1009901
  | 4 => -99999999
  | 5 => -99
  | 6 => -9999
  | _ => 1009901

private lemma patY0_edge_true : ∀ r : Fin 8, patY 0 r.1 (8 + r.1) = true := by decide

private def isDiffIdx (r rx : ℕ) : Bool :=
  match r with
  | 0 => rx == 7
  | 1 => rx == 6
  | 2 => rx == 5 || rx == 7 || rx == 9
  | 3 => rx == 4
  | 4 => rx == 11
  | 5 => rx == 10
  | 6 => rx == 9 || rx == 11 || rx == 13
  | _ => false

private lemma patY0_diff_eq : ∀ r : Fin 8, ∀ rx : Fin 16,
    rx.1 ≤ r.1 + 8 → isDiffIdx r.1 rx.1 = false →
    nextSpec 0 r.1 rx.1 = patY 0 r.1 rx.1 := by decide

private lemma specY0_self (n : ℕ) (hn : 8 ≤ n) : specY 0 n n = true := by
  unfold specY
  rw [if_neg (by unfold baseT; omega)]
  have hsub : n - baseT n = 8 + n % 8 := by unfold baseT; omega
  rw [hsub]
  exact patY0_edge_true ⟨n % 8, Nat.mod_lt _ (by omega)⟩

private lemma a_diff_front (m rx : ℕ) (hm : 8 ≤ m) :
    specY 0 (m + 1) (baseT m + rx) = nextSpec 0 (m % 8) rx ∧
    specY 0 m (baseT m + rx) = patY 0 (m % 8) rx := by
  refine ⟨specY_next_eq 0 m rx hm, ?_⟩
  unfold specY
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

private lemma a_diff_zero_term (m k : ℕ) (hm : 8 ≤ m) (hk : k < m + 1)
    (hnot : baseT m ≤ k → isDiffIdx (m % 8) (k - baseT m) = false) :
    ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
     (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) = 0 := by
  by_cases hlt : k < baseT m
  · have hk' : k < baseT (m + 1) := by unfold baseT at *; omega
    have heq : specY 0 (m + 1) k = specY 0 m k := by
      unfold specY; rw [if_pos hk', if_pos hlt]
    rw [heq]; ring
  · have hge : baseT m ≤ k := by omega
    have hrx_lt : k - baseT m < 16 := by unfold baseT at *; omega
    have hrx_le : k - baseT m ≤ m % 8 + 8 := by unfold baseT at *; omega
    have h1 : specY 0 (m + 1) k = nextSpec 0 (m % 8) (k - baseT m) := by
      have hk_eq : k = baseT m + (k - baseT m) := by omega
      conv_lhs => rw [hk_eq]
      exact specY_next_eq 0 m (k - baseT m) hm
    have h2 : specY 0 m k = patY 0 (m % 8) (k - baseT m) := by
      unfold specY; rw [if_neg hlt]
    rw [h1, h2, patY0_diff_eq ⟨m % 8, Nat.mod_lt _ (by omega)⟩ ⟨k - baseT m, hrx_lt⟩
      hrx_le (hnot hge)]
    ring

private lemma a_diff_succ (m : ℕ) (hm : 8 ≤ m) :
    a (m + 1) - 10 * a m = diffD (m + 1) := by
  have hm0 := (inv_ge8 m hm).y0
  have hm1 := (inv_ge8 (m + 1) (by omega)).y0
  have hterm :
      a (m + 1) - 10 * a m =
        (if specY 0 (m + 1) (m + 1) then (1 : ℤ) else 0) +
        ∑ k ∈ Finset.range (m + 1),
          ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
           (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) := by
    unfold a
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, Finset.mul_sum]
    have hmul :
        ∑ k ∈ Finset.range (m + 1),
          (10 : ℤ) * (if cell 654 m (k : ℤ) 0 then (10 : ℤ) ^ (m - k) else 0) =
        ∑ k ∈ Finset.range (m + 1),
          if specY 0 m k then (10 : ℤ) ^ (m + 1 - k) else 0 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [hm0 k]
      have hexp : m + 1 - k = (m - k) + 1 := by omega
      rw [hexp, pow_succ]
      split_ifs <;> ring
    have h1 :
        ∑ k ∈ Finset.range (m + 1),
          (if cell 654 (m + 1) (k : ℤ) 0 then (10 : ℤ) ^ (m + 1 - k) else 0) =
        ∑ k ∈ Finset.range (m + 1),
          if specY 0 (m + 1) k then (10 : ℤ) ^ (m + 1 - k) else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hm1 k]
    rw [hmul, h1, hm1 (m + 1)]
    have hsub :
        (∑ k ∈ Finset.range (m + 1), if specY 0 (m + 1) k then (10 : ℤ) ^ (m + 1 - k) else 0) -
        (∑ k ∈ Finset.range (m + 1), if specY 0 m k then (10 : ℤ) ^ (m + 1 - k) else 0) =
        ∑ k ∈ Finset.range (m + 1),
          ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
           (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
    linarith
  rw [hterm, specY0_self (m + 1) (by omega), if_pos rfl]
  have hmod : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨
              m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by omega
  rcases hmod with hr | hr | hr | hr | hr | hr | hr | hr
  · -- m % 8 = 0, (m + 1) % 8 = 1 -> -99
    have hsum :
        ∑ k ∈ Finset.range (m + 1),
          ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
           (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) = -100 := by
      rw [Finset.sum_eq_single (baseT m + 7)]
      · obtain ⟨h1, h2⟩ := a_diff_front m 7 hm
        rw [h1, h2, hr, show m + 1 - (baseT m + 7) = 2 by unfold baseT; omega]
        norm_num [nextSpec, patY]
      · intro k hk hne
        rw [Finset.mem_range] at hk
        refine a_diff_zero_term m k hm hk fun hge => ?_
        rw [hr]; simp only [isDiffIdx, beq_eq_false_iff_ne]; omega
      · intro hnot; exfalso; apply hnot; rw [Finset.mem_range]; unfold baseT; omega
    rw [hsum]; unfold diffD; rw [show (m + 1) % 8 = 1 by omega]; norm_num
  · -- m % 8 = 1, (m + 1) % 8 = 2 -> -9999
    have hsum :
        ∑ k ∈ Finset.range (m + 1),
          ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
           (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) = -10000 := by
      rw [Finset.sum_eq_single (baseT m + 6)]
      · obtain ⟨h1, h2⟩ := a_diff_front m 6 hm
        rw [h1, h2, hr, show m + 1 - (baseT m + 6) = 4 by unfold baseT; omega]
        norm_num [nextSpec, patY]
      · intro k hk hne
        rw [Finset.mem_range] at hk
        refine a_diff_zero_term m k hm hk fun hge => ?_
        rw [hr]; simp only [isDiffIdx, beq_eq_false_iff_ne]; omega
      · intro hnot; exfalso; apply hnot; rw [Finset.mem_range]; unfold baseT; omega
    rw [hsum]; unfold diffD; rw [show (m + 1) % 8 = 2 by omega]; norm_num
  · -- m % 8 = 2, (m + 1) % 8 = 3 -> 1009901
    have hsum :
        ∑ k ∈ Finset.range (m + 1),
          ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
           (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) = 1009900 := by
      have hsub : ({baseT m + 5, baseT m + 7, baseT m + 9} : Finset ℕ) ⊆ Finset.range (m + 1) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [Finset.mem_range]; unfold baseT at *; omega
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_insert (by simp), Finset.sum_pair (by omega)]
        obtain ⟨h1a, h2a⟩ := a_diff_front m 5 hm
        obtain ⟨h1b, h2b⟩ := a_diff_front m 7 hm
        obtain ⟨h1c, h2c⟩ := a_diff_front m 9 hm
        rw [h1a, h2a, h1b, h2b, h1c, h2c, hr,
            show m + 1 - (baseT m + 5) = 6 by unfold baseT; omega,
            show m + 1 - (baseT m + 7) = 4 by unfold baseT; omega,
            show m + 1 - (baseT m + 9) = 2 by unfold baseT; omega]
        norm_num [nextSpec, patY]
      · intro k hk hnot
        rw [Finset.mem_range] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        refine a_diff_zero_term m k hm hk fun hge => ?_
        rw [hr]; simp only [isDiffIdx, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [hsum]; unfold diffD; rw [show (m + 1) % 8 = 3 by omega]; norm_num
  · -- m % 8 = 3, (m + 1) % 8 = 4 -> -99999999
    have hsum :
        ∑ k ∈ Finset.range (m + 1),
          ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
           (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) = -100000000 := by
      rw [Finset.sum_eq_single (baseT m + 4)]
      · obtain ⟨h1, h2⟩ := a_diff_front m 4 hm
        rw [h1, h2, hr, show m + 1 - (baseT m + 4) = 8 by unfold baseT; omega]
        norm_num [nextSpec, patY]
      · intro k hk hne
        rw [Finset.mem_range] at hk
        refine a_diff_zero_term m k hm hk fun hge => ?_
        rw [hr]; simp only [isDiffIdx, beq_eq_false_iff_ne]; omega
      · intro hnot; exfalso; apply hnot; rw [Finset.mem_range]; unfold baseT; omega
    rw [hsum]; unfold diffD; rw [show (m + 1) % 8 = 4 by omega]; norm_num
  · -- m % 8 = 4, (m + 1) % 8 = 5 -> -99
    have hsum :
        ∑ k ∈ Finset.range (m + 1),
          ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
           (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) = -100 := by
      rw [Finset.sum_eq_single (baseT m + 11)]
      · obtain ⟨h1, h2⟩ := a_diff_front m 11 hm
        rw [h1, h2, hr, show m + 1 - (baseT m + 11) = 2 by unfold baseT; omega]
        norm_num [nextSpec, patY]
      · intro k hk hne
        rw [Finset.mem_range] at hk
        refine a_diff_zero_term m k hm hk fun hge => ?_
        rw [hr]; simp only [isDiffIdx, beq_eq_false_iff_ne]; omega
      · intro hnot; exfalso; apply hnot; rw [Finset.mem_range]; unfold baseT; omega
    rw [hsum]; unfold diffD; rw [show (m + 1) % 8 = 5 by omega]; norm_num
  · -- m % 8 = 5, (m + 1) % 8 = 6 -> -9999
    have hsum :
        ∑ k ∈ Finset.range (m + 1),
          ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
           (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) = -10000 := by
      rw [Finset.sum_eq_single (baseT m + 10)]
      · obtain ⟨h1, h2⟩ := a_diff_front m 10 hm
        rw [h1, h2, hr, show m + 1 - (baseT m + 10) = 4 by unfold baseT; omega]
        norm_num [nextSpec, patY]
      · intro k hk hne
        rw [Finset.mem_range] at hk
        refine a_diff_zero_term m k hm hk fun hge => ?_
        rw [hr]; simp only [isDiffIdx, beq_eq_false_iff_ne]; omega
      · intro hnot; exfalso; apply hnot; rw [Finset.mem_range]; unfold baseT; omega
    rw [hsum]; unfold diffD; rw [show (m + 1) % 8 = 6 by omega]; norm_num
  · -- m % 8 = 6, (m + 1) % 8 = 7 -> 1009901
    have hsum :
        ∑ k ∈ Finset.range (m + 1),
          ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
           (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) = 1009900 := by
      have hsub : ({baseT m + 9, baseT m + 11, baseT m + 13} : Finset ℕ) ⊆ Finset.range (m + 1) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [Finset.mem_range]; unfold baseT at *; omega
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_insert (by simp), Finset.sum_pair (by omega)]
        obtain ⟨h1a, h2a⟩ := a_diff_front m 9 hm
        obtain ⟨h1b, h2b⟩ := a_diff_front m 11 hm
        obtain ⟨h1c, h2c⟩ := a_diff_front m 13 hm
        rw [h1a, h2a, h1b, h2b, h1c, h2c, hr,
            show m + 1 - (baseT m + 9) = 6 by unfold baseT; omega,
            show m + 1 - (baseT m + 11) = 4 by unfold baseT; omega,
            show m + 1 - (baseT m + 13) = 2 by unfold baseT; omega]
        norm_num [nextSpec, patY]
      · intro k hk hnot
        rw [Finset.mem_range] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        refine a_diff_zero_term m k hm hk fun hge => ?_
        rw [hr]; simp only [isDiffIdx, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [hsum]; unfold diffD; rw [show (m + 1) % 8 = 7 by omega]; norm_num
  · -- m % 8 = 7, (m + 1) % 8 = 0 -> 1
    have hsum :
        ∑ k ∈ Finset.range (m + 1),
          ((if specY 0 (m + 1) k then (1 : ℤ) else 0) -
           (if specY 0 m k then (1 : ℤ) else 0)) * (10 : ℤ) ^ (m + 1 - k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      refine a_diff_zero_term m k hm hk fun _ => ?_
      rw [hr]; rfl
    rw [hsum]; unfold diffD; rw [show (m + 1) % 8 = 0 by omega]; norm_num

private lemma a_diff (n : ℕ) (hn : 9 ≤ n) : a n - 10 * a (n - 1) = diffD n := by
  have h := a_diff_succ (n - 1) (by omega)
  rwa [show n - 1 + 1 = n by omega] at h

-- Concrete values a(0)..a(12)
private lemma a_eq_tbl_sum (n : ℕ) (hn : n ≤ 8) :
    a n = ∑ k ∈ Finset.range (n + 1), if tblN n 0 k then (10 : ℤ) ^ (n - k) else 0 := by
  unfold a
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cell_eq_tbl n hn (k : ℤ) 0]
  simp only [tbl, Int.natAbs_zero, Int.natAbs_natCast]
  rfl

private lemma a_0 : a 0 = 1 := by
  rw [a_eq_tbl_sum 0 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]; norm_num

private lemma a_1 : a 1 = 11 := by
  rw [a_eq_tbl_sum 1 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]; norm_num

private lemma a_2 : a 2 = 111 := by
  rw [a_eq_tbl_sum 2 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]; norm_num

private lemma a_3 : a 3 = 1011 := by
  rw [a_eq_tbl_sum 3 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]; norm_num

private lemma a_4 : a 4 = 10111 := by
  rw [a_eq_tbl_sum 4 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]; norm_num

private lemma a_5 : a 5 = 101011 := by
  rw [a_eq_tbl_sum 5 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]; norm_num

private lemma a_6 : a 6 = 1000111 := by
  rw [a_eq_tbl_sum 6 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]; norm_num

private lemma a_7 : a 7 = 11011011 := by
  rw [a_eq_tbl_sum 7 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]; norm_num

private lemma a_8 : a 8 = 110110111 := by
  rw [a_eq_tbl_sum 8 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, tblN]; norm_num

private lemma a_9 : a 9 = 1101101011 := by
  have h := a_diff 9 (by omega); norm_num [diffD, a_8] at h; linarith

private lemma a_10 : a 10 = 11011000111 := by
  have h := a_diff 10 (by omega); norm_num [diffD, a_9] at h; linarith

private lemma a_11 : a 11 = 110111011011 := by
  have h := a_diff 11 (by omega); norm_num [diffD, a_10] at h; linarith

private lemma a_12 : a 12 = 1101010110111 := by
  have h := a_diff 12 (by omega); norm_num [diffD, a_11] at h; linarith

private lemma a_rec_int (n : ℕ) (hn : 13 ≤ n) :
    a n = 10 * a (n - 1) + a (n - 8) - 10 * a (n - 9) := by
  have h1 := a_diff n (by omega)
  by_cases h17 : 17 ≤ n
  · have h2 := a_diff (n - 8) (by omega)
    have hsub : n - 8 - 1 = n - 9 := by omega
    rw [hsub] at h2
    have hD : diffD n = diffD (n - 8) := by
      unfold diffD
      rw [show n % 8 = (n - 8) % 8 by omega]
    linarith
  · interval_cases n
    · norm_num [diffD] at h1; linarith [a_4, a_5]
    · norm_num [diffD] at h1; linarith [a_5, a_6]
    · norm_num [diffD] at h1; linarith [a_6, a_7]
    · norm_num [diffD] at h1; linarith [a_7, a_8]

private lemma a_rec_rat (n : ℕ) (hn : 13 ≤ n) :
    (a n : ℚ) = 10 * a (n - 1) + a (n - 8) - 10 * a (n - 9) := by
  exact_mod_cast a_rec_int n hn

-- PowerSeries generating function proof
private lemma coeff_mul_X' (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X) =
      if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
  have h := PowerSeries.coeff_mul_X_pow' f 1 n
  simpa [pow_one] using h

open PowerSeries in
private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + X ^ 2) * (1 + X ^ 4) : PowerSeries ℚ) =
    1 + X + X ^ 2 - 99 * X ^ 3 + X ^ 4 - 99 * X ^ 5 - 9999 * X ^ 6 + 1009901 * X ^ 7 -
      100 * X ^ 9 - 10000 * X ^ 10 + 1010000 * X ^ 11 - 100000000 * X ^ 12 := by
  have hpoly :
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + X ^ 2) * (1 + X ^ 4) : PowerSeries ℚ) =
        1 - PowerSeries.C 10 * X - X ^ 8 + PowerSeries.C 10 * X ^ 9 := by
    have h10 : (PowerSeries.C (10 : ℚ) : PowerSeries ℚ) = 10 :=
      map_ofNat (PowerSeries.C (R := ℚ)) 10
    rw [h10]
    ring
  rw [hpoly]
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hmul :
      F * (1 - PowerSeries.C 10 * X - X ^ 8 + PowerSeries.C 10 * X ^ 9) =
        F - PowerSeries.C 10 * (F * X) - F * X ^ 8 + PowerSeries.C 10 * (F * X ^ 9) := by
    ring
  rw [hmul]
  have h99 : (99 : PowerSeries ℚ) = PowerSeries.C 99 :=
    (map_ofNat (PowerSeries.C (R := ℚ)) 99).symm
  have h9999 : (9999 : PowerSeries ℚ) = PowerSeries.C 9999 :=
    (map_ofNat (PowerSeries.C (R := ℚ)) 9999).symm
  have h1009901 : (1009901 : PowerSeries ℚ) = PowerSeries.C 1009901 :=
    (map_ofNat (PowerSeries.C (R := ℚ)) 1009901).symm
  have h100 : (100 : PowerSeries ℚ) = PowerSeries.C 100 :=
    (map_ofNat (PowerSeries.C (R := ℚ)) 100).symm
  have h10000 : (10000 : PowerSeries ℚ) = PowerSeries.C 10000 :=
    (map_ofNat (PowerSeries.C (R := ℚ)) 10000).symm
  have h1010000 : (1010000 : PowerSeries ℚ) = PowerSeries.C 1010000 :=
    (map_ofNat (PowerSeries.C (R := ℚ)) 1010000).symm
  have h100000000 : (100000000 : PowerSeries ℚ) = PowerSeries.C 100000000 :=
    (map_ofNat (PowerSeries.C (R := ℚ)) 100000000).symm
  rw [h99, h9999, h1009901, h100, h10000, h1010000, h100000000]
  ext n
  have hcoeff_F : ∀ m, PowerSeries.coeff m F = (a m : ℚ) := fun m => PowerSeries.coeff_mk m _
  simp only [map_add, map_sub, coeff_C_mul]
  simp only [coeff_one, coeff_X, coeff_X_pow,
    coeff_mul_X', PowerSeries.coeff_mul_X_pow', hcoeff_F]
  by_cases hn : 13 ≤ n
  · have h1 : 1 ≤ n := by omega
    have h8 : 8 ≤ n := by omega
    have h9 : 9 ≤ n := by omega
    have h0' : n ≠ 0 := by omega
    have h1' : n ≠ 1 := by omega
    have h2' : n ≠ 2 := by omega
    have h3' : n ≠ 3 := by omega
    have h4' : n ≠ 4 := by omega
    have h5' : n ≠ 5 := by omega
    have h6' : n ≠ 6 := by omega
    have h7' : n ≠ 7 := by omega
    have h9' : n ≠ 9 := by omega
    have h10' : n ≠ 10 := by omega
    have h11' : n ≠ 11 := by omega
    have h12' : n ≠ 12 := by omega
    simp only [if_pos h1, if_pos h8, if_pos h9,
      if_neg h0', if_neg h1', if_neg h2', if_neg h3', if_neg h4', if_neg h5',
      if_neg h6', if_neg h7', if_neg h9', if_neg h10', if_neg h11', if_neg h12']
    have hrec := a_rec_rat n hn
    linarith
  · interval_cases n <;>
      norm_num [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12]

end OMA.S_oeis_a283586.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a283586.main := by
  exact ⟨OMA.S_oeis_a283586.Proof.gf_eq, OMA.S_oeis_a283586.Proof.a_rec_rat⟩
