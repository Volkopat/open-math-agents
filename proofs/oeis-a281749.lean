import OMAStatements.S_oeis_a281749
import Mathlib

-- Credit: @qu1r0ra

open OMA.S_oeis_a281749

private def rule395 (c e w n s : Bool) : Bool :=
  (395 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat))

private def rule395Fast (c e w n s : Bool) : Bool :=
  match c, e.toNat + w.toNat + n.toNat + s.toNat with
  | false, 0 | false, 4 => true
  | true, 0 | true, 1 | true, 3 => true
  | _, _ => false

private lemma rule395_eq (c e w n s : Bool) :
    rule395 c e w n s = rule395Fast c e w n s := by
  cases c <;> cases e <;> cases w <;> cases n <;> cases s <;> decide

private lemma cell_succ (t : ℕ) (i j : ℤ) :
    cell 395 (t + 1) i j =
      rule395 (cell 395 t i j) (cell 395 t (i + 1) j) (cell 395 t (i - 1) j)
        (cell 395 t i (j + 1)) (cell 395 t i (j - 1)) := rfl

private lemma cell_neg_i (t : ℕ) (i j : ℤ) : cell 395 t (-i) j = cell 395 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    have h1 : -i + 1 = -(i - 1) := by omega
    have h2 : -i - 1 = -(i + 1) := by omega
    rw [h1, h2, ih i j, ih (i - 1) j, ih (i + 1) j, ih i (j + 1), ih i (j - 1)]
    congr 1; omega

private lemma cell_neg_j (t : ℕ) (i j : ℤ) : cell 395 t i (-j) = cell 395 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    have h1 : -j + 1 = -(j - 1) := by omega
    have h2 : -j - 1 = -(j + 1) := by omega
    rw [h1, h2, ih i j, ih (i + 1) j, ih (i - 1) j, ih i (j - 1), ih i (j + 1)]
    congr 1; omega

private lemma cell_swap (t : ℕ) (i j : ℤ) : cell 395 t j i = cell 395 t i j := by
  induction t generalizing i j with
  | zero => simp [cell, and_comm]
  | succ t ih =>
    simp only [cell]
    rw [ih i j, ih i (j + 1), ih i (j - 1), ih (i + 1) j, ih (i - 1) j]
    congr 1; omega

private lemma cell_natAbs (t : ℕ) (i j : ℤ) :
    cell 395 t i j = cell 395 t (i.natAbs : ℤ) (j.natAbs : ℤ) := by
  rcases Int.natAbs_eq i with hi | hi <;> rcases Int.natAbs_eq j with hj | hj
  · conv_lhs => rw [hi, hj]
  · conv_lhs => rw [hi, hj]
    exact cell_neg_j t _ _
  · conv_lhs => rw [hi, hj]
    exact cell_neg_i t _ _
  · conv_lhs => rw [hi, hj]
    rw [cell_neg_i, cell_neg_j]

private lemma cell_outside (t : ℕ) (i j : ℤ) (h : t < i.natAbs + j.natAbs) :
    cell 395 t i j = decide (t % 2 = 1) := by
  induction t generalizing i j with
  | zero =>
    simp only [cell]
    have hne : ¬(i = 0 ∧ j = 0) := by omega
    simp [hne]
  | succ t ih =>
    rw [cell_succ, rule395_eq]
    rw [ih i j (by omega), ih (i + 1) j (by omega), ih (i - 1) j (by omega),
        ih i (j + 1) (by omega), ih i (j - 1) (by omega)]
    have hmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases hmod with hm | hm
    · have hm1 : (t + 1) % 2 = 1 := by omega
      simp [hm, hm1, rule395Fast]
    · have hm1 : (t + 1) % 2 ≠ 1 := by omega
      simp [hm, hm1, rule395Fast]

private def bitAt (m k : ℕ) : Bool := (m / 2 ^ k) % 2 == 1

private def gridRow : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 1, 0 => 1
  | 2, 0 => 7
  | 3, 0 => 4
  | 4, 0 => 29 | 4, 1 => 2
  | 5, 0 => 23 | 5, 1 => 2 | 5, 2 => 12
  | 6, 0 => 116 | 6, 2 => 24
  | 7, 0 => 85 | 7, 1 => 2 | 7, 2 => 24
  | 8, 0 => 471 | 8, 1 => 34 | 8, 2 => 24
  | 9, 0 => 372 | 9, 1 => 32 | 9, 2 => 216 | 9, 3 => 96 | 9, 4 => 48
  | 10, 0 => 1877 | 10, 1 => 34 | 10, 2 => 440
  | 11, 0 => 1399 | 11, 1 => 34 | 11, 2 => 392 | 11, 3 => 64 | 11, 4 => 240 | 11, 5 => 96
  | 12, 0 => 7508 | 12, 1 => 544 | 12, 2 => 392 | 12, 3 => 64 | 12, 4 => 416
  | 13, 0 => 6005 | 13, 1 => 546 | 13, 2 => 3464 | 13, 3 => 1616 | 13, 4 => 416 | 13, 5 => 64 | 13, 6 => 192
  | 14, 0 => 30039 | 14, 1 => 546 | 14, 2 => 7048 | 14, 3 => 600 | 14, 4 => 2032 | 14, 5 => 96 | 14, 6 => 384
  | 15, 0 => 22388 | 15, 1 => 544 | 15, 2 => 6792 | 15, 3 => 64 | 15, 4 => 1568 | 15, 6 => 448
  | 16, 0 => 120149 | 16, 1 => 8226 | 16, 2 => 6792 | 16, 3 => 336 | 16, 4 => 1696 | 16, 6 => 256
  | 17, 0 => 95607 | 17, 1 => 8226 | 17, 2 => 55944 | 17, 3 => 25048 | 17, 4 => 14000 | 17, 5 => 6208 | 17, 6 => 3392 | 17, 7 => 1664 | 17, 8 => 768
  | 18, 0 => 480596 | 18, 1 => 8224 | 18, 2 => 113288 | 18, 3 => 320 | 18, 4 => 1760 | 18, 5 => 96 | 18, 6 => 256 | 18, 7 => 384
  | 19, 0 => 357749 | 19, 1 => 8226 | 19, 2 => 101000 | 19, 3 => 16848 | 19, 4 => 63104 | 19, 5 => 30720 | 19, 6 => 15616 | 19, 7 => 7168 | 19, 8 => 3584 | 19, 9 => 1536
  | 20, 0 => 1922391 | 20, 1 => 139298 | 20, 2 => 101000 | 20, 3 => 16728 | 20, 4 => 108192 | 20, 5 => 96 | 20, 6 => 320 | 20, 7 => 1152
  | _, _ => 0

private def gridVal (t i j : ℕ) : Bool :=
  if t < i + j then decide (t % 2 = 1)
  else bitAt (gridRow t (min i j)) (max i j)

private lemma gridVal_symm (t i j : ℕ) : gridVal t j i = gridVal t i j := by
  simp only [gridVal, Nat.add_comm j i, min_comm j i, max_comm j i]

private def stepGridVal (t i j : ℕ) : Bool :=
  rule395Fast
    (gridVal t i j)
    (gridVal t (i + 1) j)
    (gridVal t (if i = 0 then 1 else i - 1) j)
    (gridVal t i (j + 1))
    (gridVal t i (if j = 0 then 1 else j - 1))

private lemma gridVal_step_ok :
    ∀ t : Fin 20, ∀ i : Fin 21, ∀ j : Fin 21,
      i.val + j.val ≤ t.val + 1 → j.val ≤ i.val →
      stepGridVal t.val i.val j.val = gridVal (t.val + 1) i.val j.val := by
  decide

private lemma natAbs_sub_one (k : ℕ) : ((k : ℤ) - 1).natAbs = if k = 0 then 1 else k - 1 := by
  cases k with
  | zero => rfl
  | succ k => simp

private lemma cell_eq_gridVal (t : ℕ) (ht : t ≤ 20) (i j : ℤ) :
    cell 395 t i j = gridVal t i.natAbs j.natAbs := by
  induction t generalizing i j with
  | zero =>
    rw [cell_natAbs]
    set a := i.natAbs
    set b := j.natAbs
    by_cases h : 0 < a + b
    · rw [cell_outside 0 (a : ℤ) (b : ℤ) (by simpa using h)]
      simp [gridVal, h]
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      rw [ha, hb]; decide
  | succ t ih =>
    rw [cell_natAbs]
    set a := i.natAbs
    set b := j.natAbs
    by_cases hout : t + 1 < a + b
    · rw [cell_outside (t + 1) (a : ℤ) (b : ℤ) (by simpa using hout)]
      simp [gridVal, hout]
    · have hle : a + b ≤ t + 1 := by omega
      suffices hmain : ∀ x y : ℕ, x + y ≤ t + 1 → y ≤ x →
          cell 395 (t + 1) (x : ℤ) (y : ℤ) = gridVal (t + 1) x y by
        rcases le_total b a with hba | hab
        · exact hmain a b hle hba
        · rw [← cell_swap, ← gridVal_symm]
          exact hmain b a (by omega) hab
      intro x y hxy hyx
      rw [cell_succ, rule395_eq]
      rw [ih (by omega) (x : ℤ) (y : ℤ),
          ih (by omega) ((x : ℤ) + 1) (y : ℤ),
          ih (by omega) ((x : ℤ) - 1) (y : ℤ),
          ih (by omega) (x : ℤ) ((y : ℤ) + 1),
          ih (by omega) (x : ℤ) ((y : ℤ) - 1)]
      have hx1 : ((x : ℤ) + 1).natAbs = x + 1 := by omega
      have hy1 : ((y : ℤ) + 1).natAbs = y + 1 := by omega
      simp only [Int.natAbs_natCast, hx1, hy1, natAbs_sub_one]
      exact gridVal_step_ok ⟨t, by omega⟩ ⟨x, by omega⟩ ⟨y, by omega⟩ hxy hyx

private lemma wedge_base_ok :
    ∀ j : Fin 6, ∀ i : Fin 13,
      j.val + 2 ≤ i.val → i.val + j.val ≤ 12 →
      gridVal 20 (i.val + 8) j.val = gridVal 12 i.val j.val := by
  decide

private lemma wedge_period (d : ℕ) (i j : ℤ) (h : (d : ℤ) + 2 ≤ i - (j.natAbs : ℤ)) :
    cell 395 (d + 20) (i + 8) j = cell 395 (d + 12) i j := by
  induction d generalizing i j with
  | zero =>
    have hi0 : 0 ≤ i := by omega
    rw [cell_natAbs (0 + 20), cell_natAbs (0 + 12)]
    set a := i.natAbs
    set b := j.natAbs
    have ha : (a : ℤ) = i := Int.natAbs_of_nonneg hi0
    have ha8 : (i + 8).natAbs = a + 8 := by omega
    rw [ha8]
    by_cases hout : 12 < a + b
    · rw [cell_outside 20 ((a + 8 : ℕ) : ℤ) (b : ℤ) (by simp; omega),
          cell_outside 12 (a : ℤ) (b : ℤ) (by simp; omega)]
    · rw [cell_eq_gridVal 20 (by omega), cell_eq_gridVal 12 (by omega)]
      simp only [Int.natAbs_natCast]
      have hb2a : b + 2 ≤ a := by omega
      have hab12 : a + b ≤ 12 := by omega
      exact wedge_base_ok ⟨b, by omega⟩ ⟨a, by omega⟩ hb2a hab12
  | succ d ih =>
    have hstep1 : d + 1 + 20 = (d + 20) + 1 := by omega
    have hstep2 : d + 1 + 12 = (d + 12) + 1 := by omega
    conv_lhs => rw [hstep1, cell_succ]
    conv_rhs => rw [hstep2, cell_succ]
    have e1 : i + 8 + 1 = (i + 1) + 8 := by omega
    have e2 : i + 8 - 1 = (i - 1) + 8 := by omega
    rw [e1, e2,
        ih i j (by omega),
        ih (i + 1) j (by omega),
        ih (i - 1) j (by omega),
        ih i (j + 1) (by omega),
        ih i (j - 1) (by omega)]

private lemma wedge_period_mul (q : ℕ) (t : ℕ) (ht : 12 ≤ t) (i j : ℤ)
    (h : (t : ℤ) - 10 ≤ i - (j.natAbs : ℤ)) :
    cell 395 (t + 8 * q) (i + 8 * (q : ℤ)) j = cell 395 t i j := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : t + 8 * (q + 1) = (t + 8 * q - 12) + 20 := by omega
    have h2 : t + 8 * q = (t + 8 * q - 12) + 12 := by omega
    have h3 : i + 8 * ((q + 1 : ℕ) : ℤ) = (i + 8 * (q : ℤ)) + 8 := by push_cast; ring
    rw [h1, h3, wedge_period (t + 8 * q - 12) (i + 8 * (q : ℤ)) j (by omega)]
    rw [← h2]
    exact ih

private def f0 (t x : ℕ) : Bool :=
  if x = 0 then decide (t % 3 ≠ 0)
  else if x = 1 then decide (t % 3 = 2)
  else decide (x % 2 = 0 ∨ (t % 2 = 1 ∧ x % 8 = 5))

private def f1 (t x : ℕ) : Bool :=
  if x = 0 then decide (t % 3 = 2)
  else if x = 1 then decide (t % 3 ≠ 0)
  else decide (x % 8 = 5)

private def f2 (_t x : ℕ) : Bool :=
  if x = 0 then true
  else if x = 1 then false
  else if x = 2 then false
  else decide (x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 7)

private lemma f0_mod_t (t x : ℕ) : f0 t x = f0 (t % 6) x := by
  unfold f0
  have h3 : (t % 6) % 3 = t % 3 := by omega
  have h2 : (t % 6) % 2 = t % 2 := by omega
  simp [h3, h2]

private lemma f1_mod_t (t x : ℕ) : f1 t x = f1 (t % 6) x := by
  unfold f1
  have h3 : (t % 6) % 3 = t % 3 := by omega
  simp [h3]

private lemma f0_congr {t₁ t₂ x₁ x₂ : ℕ} (ht : t₁ % 2 = t₂ % 2)
    (hx1 : 2 ≤ x₁) (hx2 : 2 ≤ x₂) (hx : x₁ % 8 = x₂ % 8) :
    f0 t₁ x₁ = f0 t₂ x₂ := by
  have h2x : x₁ % 2 = x₂ % 2 := by omega
  have hne : x₁ ≠ 0 ∧ x₁ ≠ 1 ∧ x₂ ≠ 0 ∧ x₂ ≠ 1 := by omega
  simp [f0, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2, ht, h2x, hx]

private lemma f1_congr {t₁ t₂ x₁ x₂ : ℕ}
    (hx1 : 2 ≤ x₁) (hx2 : 2 ≤ x₂) (hx : x₁ % 8 = x₂ % 8) :
    f1 t₁ x₁ = f1 t₂ x₂ := by
  have hne : x₁ ≠ 0 ∧ x₁ ≠ 1 ∧ x₂ ≠ 0 ∧ x₂ ≠ 1 := by omega
  simp [f1, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2, hx]

private lemma f2_congr {t₁ t₂ x₁ x₂ : ℕ}
    (hx1 : 2 ≤ x₁) (hx2 : 2 ≤ x₂) (hx : x₁ % 8 = x₂ % 8) :
    f2 t₁ x₁ = f2 t₂ x₂ := by
  have hne : x₁ ≠ 0 ∧ x₁ ≠ 1 ∧ x₂ ≠ 0 ∧ x₂ ≠ 1 := by omega
  unfold f2
  simp only [hne.1, hne.2.1, hne.2.2.1, hne.2.2.2, ↓reduceIte]
  by_cases h1 : x₁ = 2 <;> by_cases h2 : x₂ = 2
  · simp [h1, h2]
  · simp only [h1, h2, ↓reduceIte]
    have h2mod : x₂ % 8 = 2 := by omega
    simp [h2mod]
  · simp only [h1, h2, ↓reduceIte]
    have h1mod : x₁ % 8 = 2 := by omega
    simp [h1mod]
  · simp [h1, h2, hx]

private lemma step_f_small_ok :
    ∀ t : Fin 6, ∀ x : Fin 11,
      rule395Fast (f0 t.val x.val) (f0 t.val (x.val + 1))
        (f0 t.val (if x.val = 0 then 1 else x.val - 1)) (f1 t.val x.val) (f1 t.val x.val) =
        f0 (t.val + 1) x.val ∧
      rule395Fast (f1 t.val x.val) (f1 t.val (x.val + 1))
        (f1 t.val (if x.val = 0 then 1 else x.val - 1)) (f2 t.val x.val) (f0 t.val x.val) =
        f1 (t.val + 1) x.val := by
  decide

private lemma step_f2_ge3_small_ok :
    ∀ t : Fin 6, ∀ x : Fin 11, ∀ b : Bool,
      3 ≤ x.val →
      rule395Fast (f2 t.val x.val) (f2 t.val (x.val + 1)) (f2 t.val (x.val - 1))
        b (f1 t.val x.val) = f2 (t.val + 1) x.val := by
  decide

private lemma step_f2_2_ok :
    ∀ t : Fin 6,
      rule395Fast (f2 t.val 2) (f2 t.val 3) (f2 t.val 1) (f2 t.val 3) (f1 t.val 2) =
        f2 (t.val + 1) 2 := by
  decide

private lemma step_f0 (t x : ℕ) :
    rule395Fast (f0 t x) (f0 t (x + 1)) (f0 t (if x = 0 then 1 else x - 1))
      (f1 t x) (f1 t x) = f0 (t + 1) x := by
  set r := t % 6
  have hr : r < 6 := Nat.mod_lt t (by omega)
  have ht1 : (t + 1) % 6 = (r + 1) % 6 := by omega
  by_cases hx : x < 3
  · rw [f0_mod_t t x, f0_mod_t t (x + 1), f0_mod_t t (if x = 0 then 1 else x - 1),
        f1_mod_t t x, f0_mod_t (t + 1) x, ht1, ← f0_mod_t (r + 1) x]
    exact (step_f_small_ok ⟨r, hr⟩ ⟨x, by omega⟩).1
  · set x' := 3 + (x - 3) % 8
    have hx' : x' < 11 := by omega
    have hif1 : (if x = 0 then 1 else x - 1) = x - 1 := if_neg (by omega)
    have hif2 : (if x' = 0 then 1 else x' - 1) = x' - 1 := if_neg (by omega)
    have e0 : f0 t x = f0 r x' := f0_congr (by omega) (by omega) (by omega) (by omega)
    have e1 : f0 t (x + 1) = f0 r (x' + 1) := f0_congr (by omega) (by omega) (by omega) (by omega)
    have e2 : f0 t (x - 1) = f0 r (x' - 1) := f0_congr (by omega) (by omega) (by omega) (by omega)
    have e3 : f1 t x = f1 r x' := f1_congr (by omega) (by omega) (by omega)
    have e4 : f0 (t + 1) x = f0 (r + 1) x' := f0_congr (by omega) (by omega) (by omega) (by omega)
    rw [hif1, e0, e1, e2, e3, e4]
    have h := (step_f_small_ok ⟨r, hr⟩ ⟨x', hx'⟩).1
    dsimp only at h
    rw [hif2] at h
    exact h

private lemma step_f1 (t x : ℕ) :
    rule395Fast (f1 t x) (f1 t (x + 1)) (f1 t (if x = 0 then 1 else x - 1))
      (f2 t x) (f0 t x) = f1 (t + 1) x := by
  set r := t % 6
  have hr : r < 6 := Nat.mod_lt t (by omega)
  have ht1 : (t + 1) % 6 = (r + 1) % 6 := by omega
  by_cases hx : x < 3
  · rw [f1_mod_t t x, f1_mod_t t (x + 1), f1_mod_t t (if x = 0 then 1 else x - 1),
        f0_mod_t t x, f1_mod_t (t + 1) x, ht1, ← f1_mod_t (r + 1) x]
    exact (step_f_small_ok ⟨r, hr⟩ ⟨x, by omega⟩).2
  · set x' := 3 + (x - 3) % 8
    have hx' : x' < 11 := by omega
    have hif1 : (if x = 0 then 1 else x - 1) = x - 1 := if_neg (by omega)
    have hif2 : (if x' = 0 then 1 else x' - 1) = x' - 1 := if_neg (by omega)
    have e0 : f1 t x = f1 r x' := f1_congr (by omega) (by omega) (by omega)
    have e1 : f1 t (x + 1) = f1 r (x' + 1) := f1_congr (by omega) (by omega) (by omega)
    have e2 : f1 t (x - 1) = f1 r (x' - 1) := f1_congr (by omega) (by omega) (by omega)
    have e3 : f2 t x = f2 r x' := f2_congr (by omega) (by omega) (by omega)
    have e4 : f0 t x = f0 r x' := f0_congr (by omega) (by omega) (by omega) (by omega)
    have e5 : f1 (t + 1) x = f1 (r + 1) x' := f1_congr (by omega) (by omega) (by omega)
    rw [hif1, e0, e1, e2, e3, e4, e5]
    have h := (step_f_small_ok ⟨r, hr⟩ ⟨x', hx'⟩).2
    dsimp only at h
    rw [hif2] at h
    exact h

private lemma step_f2_ge3 (t x : ℕ) (hx : 3 ≤ x) (b : Bool) :
    rule395Fast (f2 t x) (f2 t (x + 1)) (f2 t (x - 1)) b (f1 t x) = f2 (t + 1) x := by
  set r := t % 6
  have hr : r < 6 := Nat.mod_lt t (by omega)
  set x' := 3 + (x - 3) % 8
  have hx' : x' < 11 := by omega
  have hx'3 : 3 ≤ x' := by omega
  have e0 : f2 t x = f2 r x' := f2_congr (by omega) (by omega) (by omega)
  have e1 : f2 t (x + 1) = f2 r (x' + 1) := f2_congr (by omega) (by omega) (by omega)
  have e2 : f2 t (x - 1) = f2 r (x' - 1) := f2_congr (by omega) (by omega) (by omega)
  have e3 : f1 t x = f1 r x' := f1_congr (by omega) (by omega) (by omega)
  have e4 : f2 (t + 1) x = f2 (r + 1) x' := f2_congr (by omega) (by omega) (by omega)
  rw [e0, e1, e2, e3, e4]
  exact step_f2_ge3_small_ok ⟨r, hr⟩ ⟨x', hx'⟩ b hx'3

private lemma strip_base_ok :
    ∀ x : Fin 6,
      gridVal 12 x.val 0 = f0 12 x.val ∧
      gridVal 12 x.val 1 = f1 12 x.val ∧
      gridVal 12 x.val 2 = f2 12 x.val := by
  decide

private lemma strip_boundary_ok :
    ∀ k : Fin 8, ∀ d : Fin 2,
      let t := k.val + 12
      let x := t - (d.val + 7)
      gridVal t x 0 = f0 t x ∧
      gridVal t x 1 = f1 t x ∧
      gridVal t x 2 = f2 t x := by
  decide

private lemma natAbs_two : (2 : ℤ).natAbs = 2 := rfl

private lemma strip_eq (d : ℕ) :
    ∀ x : ℕ, x + 7 ≤ d + 12 →
      cell 395 (d + 12) (x : ℤ) 0 = f0 (d + 12) x ∧
      cell 395 (d + 12) (x : ℤ) 1 = f1 (d + 12) x ∧
      cell 395 (d + 12) (x : ℤ) 2 = f2 (d + 12) x := by
  induction d with
  | zero =>
    intro x hx
    rw [cell_eq_gridVal 12 (by omega), cell_eq_gridVal 12 (by omega), cell_eq_gridVal 12 (by omega)]
    simp only [Int.natAbs_natCast, Int.natAbs_zero, Int.natAbs_one, natAbs_two]
    exact strip_base_ok ⟨x, by omega⟩
  | succ d ih =>
    set t := d + 12
    have ht1 : d + 1 + 12 = t + 1 := by omega
    rw [ht1]
    have h_inner_0 : ∀ x : ℕ, x + 8 ≤ t → cell 395 (t + 1) (x : ℤ) 0 = f0 (t + 1) x := by
      intro x hx
      rw [cell_succ, rule395_eq]
      have hneg1 : cell 395 t (x : ℤ) (0 - 1) = cell 395 t (x : ℤ) 1 := by
        simpa using cell_neg_j t (x : ℤ) 1
      have hxm : cell 395 t ((x : ℤ) - 1) 0 = cell 395 t ((if x = 0 then 1 else x - 1 : ℕ) : ℤ) 0 := by
        cases x with
        | zero => simpa using cell_neg_i t 1 0
        | succ k => simp
      have hxp : ((x : ℤ) + 1) = ((x + 1 : ℕ) : ℤ) := by push_cast; ring
      have hxm_lt : (if x = 0 then 1 else x - 1) + 7 ≤ t := by split_ifs <;> omega
      rw [hneg1, hxm, hxp, show (0 : ℤ) + 1 = 1 by omega]
      rw [(ih x (by omega)).1, (ih (x + 1) (by omega)).1,
          (ih (if x = 0 then 1 else x - 1) hxm_lt).1,
          (ih x (by omega)).2.1]
      exact step_f0 t x
    have h_inner_1 : ∀ x : ℕ, x + 8 ≤ t → cell 395 (t + 1) (x : ℤ) 1 = f1 (t + 1) x := by
      intro x hx
      rw [cell_succ, rule395_eq]
      have hxm : cell 395 t ((x : ℤ) - 1) 1 = cell 395 t ((if x = 0 then 1 else x - 1 : ℕ) : ℤ) 1 := by
        cases x with
        | zero => simpa using cell_neg_i t 1 1
        | succ k => simp
      have hxp : ((x : ℤ) + 1) = ((x + 1 : ℕ) : ℤ) := by push_cast; ring
      have hxm_lt : (if x = 0 then 1 else x - 1) + 7 ≤ t := by split_ifs <;> omega
      rw [hxm, hxp, show (1 : ℤ) + 1 = 2 by omega, show (1 : ℤ) - 1 = 0 by omega]
      rw [(ih x (by omega)).2.1, (ih (x + 1) (by omega)).2.1,
          (ih (if x = 0 then 1 else x - 1) hxm_lt).2.1,
          (ih x (by omega)).2.2, (ih x (by omega)).1]
      exact step_f1 t x
    intro x hx
    by_cases hcase : x + 8 ≤ t
    · refine ⟨h_inner_0 x hcase, h_inner_1 x hcase, ?_⟩
      by_cases hx0 : x = 0
      · subst hx0
        rw [cell_swap]
        have h := h_inner_0 2 (by omega)
        simpa [f0, f2] using h
      · by_cases hx1 : x = 1
        · subst hx1
          rw [cell_swap]
          have h := h_inner_1 2 (by omega)
          simpa [f1, f2] using h
        · by_cases hx2 : x = 2
          · subst hx2
            rw [cell_succ, rule395_eq]
            simp only [Nat.cast_ofNat]
            have h23 : cell 395 t 2 (2 + 1) = cell 395 t 3 2 := by
              rw [show (2 : ℤ) + 1 = 3 by omega, cell_swap]
            rw [h23, show (2 : ℤ) + 1 = 3 by omega, show (2 : ℤ) - 1 = 1 by omega]
            have i2 := ih 2 (by omega)
            have i3 := ih 3 (by omega)
            have i1 := ih 1 (by omega)
            simp only [Nat.cast_ofNat, Nat.cast_one] at i2 i3 i1
            rw [i2.2.2, i3.2.2, i1.2.2, i2.2.1]
            have hr := step_f2_2_ok ⟨t % 6, Nat.mod_lt t (by omega)⟩
            simpa [f1, f2] using hr
          · rw [cell_succ, rule395_eq]
            have hxp : ((x : ℤ) + 1) = ((x + 1 : ℕ) : ℤ) := by push_cast; ring
            have hxm : ((x : ℤ) - 1) = ((x - 1 : ℕ) : ℤ) := by omega
            rw [hxp, hxm, show (2 : ℤ) - 1 = 1 by omega]
            rw [(ih x (by omega)).2.2, (ih (x + 1) (by omega)).2.2,
                (ih (x - 1) (by omega)).2.2, (ih x (by omega)).2.1]
            exact step_f2_ge3 t x (by omega) _
    · set t1 := t + 1
      set q := (t1 - 12) / 8
      set k := (t1 - 12) % 8
      set t0 := k + 12
      set delta := t1 - x - 7
      set x0 := t0 - (delta + 7)
      have ht1_eq : t1 = t0 + 8 * q := by omega
      have hx_eq : (x : ℤ) = (x0 : ℤ) + 8 * (q : ℤ) := by omega
      have hx_nat : x = x0 + 8 * q := by omega
      have hbd := strip_boundary_ok ⟨k, by omega⟩ ⟨delta, by omega⟩
      dsimp only at hbd
      have htmod : t0 % 2 = (t0 + 8 * q) % 2 := by omega
      have hxmod : x0 % 8 = x % 8 := by omega
      have hc0 : cell 395 t1 (x : ℤ) 0 = f0 t1 x := by
        rw [ht1_eq, hx_eq, wedge_period_mul q t0 (by omega) (x0 : ℤ) 0 (by simp; omega)]
        rw [cell_eq_gridVal t0 (by omega)]
        simp only [Int.natAbs_natCast, Int.natAbs_zero]
        rw [hbd.1]
        exact f0_congr htmod (by omega) (by omega) hxmod
      have hc1 : cell 395 t1 (x : ℤ) 1 = f1 t1 x := by
        rw [ht1_eq, hx_eq, wedge_period_mul q t0 (by omega) (x0 : ℤ) 1 (by simp; omega)]
        rw [cell_eq_gridVal t0 (by omega)]
        simp only [Int.natAbs_natCast, Int.natAbs_one]
        rw [hbd.2.1]
        exact f1_congr (by omega) (by omega) hxmod
      have hc2 : cell 395 t1 (x : ℤ) 2 = f2 t1 x := by
        rw [ht1_eq, hx_eq, wedge_period_mul q t0 (by omega) (x0 : ℤ) 2 (by simp; omega)]
        rw [cell_eq_gridVal t0 (by omega)]
        simp only [Int.natAbs_natCast, natAbs_two]
        rw [hbd.2.2]
        exact f2_congr (by omega) (by omega) hxmod
      exact ⟨hc0, hc1, hc2⟩

private lemma cell_shift8_x0 (n k : ℕ) (hn : 20 ≤ n) (hk : 10 ≤ k) :
    cell 395 n (k : ℤ) 0 = cell 395 (n - 8) ((k - 8 : ℕ) : ℤ) 0 := by
  by_cases hw : n ≤ k + 10
  · have h1 : n = (n - 20) + 20 := by omega
    have h2 : n - 8 = (n - 20) + 12 := by omega
    have h3 : (k : ℤ) = ((k - 8 : ℕ) : ℤ) + 8 := by omega
    conv_lhs => rw [h1, h3]
    conv_rhs => rw [h2]
    exact wedge_period (n - 20) ((k - 8 : ℕ) : ℤ) 0 (by simp; omega)
  · have h1 : n = (n - 12) + 12 := by omega
    have h2 : n - 8 = (n - 20) + 12 := by omega
    have e1 := (strip_eq (n - 12) k (by omega)).1
    have e2 := (strip_eq (n - 20) (k - 8) (by omega)).1
    rw [← h1] at e1
    rw [← h2] at e2
    rw [e1, e2]
    exact f0_congr (by omega) (by omega) (by omega) (by omega)

private def Cval (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => 10101000
  | 1 => 1010110999
  | 2 => 1110101010
  | 3 => 10111000
  | 4 => 1010100999
  | _ => 1110111010

private lemma Cval_eq_sum (n : ℕ) (hn : 8 ≤ n) :
    (∑ k ∈ Finset.range 10, if f0 n k then (10 : ℤ) ^ (9 - k) else 0) -
      (∑ k ∈ Finset.range 2, if f0 (n - 8) k then (10 : ℤ) ^ (1 - k) else 0) = Cval n := by
  have h1 : ∀ k, f0 n k = f0 (n % 6) k := fun k => f0_mod_t n k
  have h2 : ∀ k, f0 (n - 8) k = f0 ((n % 6 + 4) % 6) k := by
    intro k
    rw [f0_mod_t (n - 8) k]
    have : (n - 8) % 6 = (n % 6 + 4) % 6 := by omega
    rw [this]
  simp only [h1, h2, Cval]
  have hr : n % 6 < 6 := Nat.mod_lt n (by omega)
  set r := n % 6
  interval_cases r <;> decide

private lemma diff8_ge20 (n : ℕ) (hn : 20 ≤ n) :
    a n - a (n - 8) = (10 : ℤ) ^ (n - 9) * Cval n := by
  unfold a
  have hsplit1 : n + 1 = 10 + (n - 9) := by omega
  have hsplit2 : n - 8 + 1 = 2 + (n - 9) := by omega
  rw [hsplit1, Finset.sum_range_add, hsplit2, Finset.sum_range_add]
  have htail :
      (∑ j ∈ Finset.range (n - 9), if cell 395 n ((10 + j : ℕ) : ℤ) 0 then (10 : ℤ) ^ (n - (10 + j)) else 0) =
      (∑ j ∈ Finset.range (n - 9), if cell 395 (n - 8) ((2 + j : ℕ) : ℤ) 0 then (10 : ℤ) ^ (n - 8 - (2 + j)) else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc := cell_shift8_x0 n (10 + j) hn (by omega)
    have hsub : 10 + j - 8 = 2 + j := by omega
    have hexp : n - (10 + j) = n - 8 - (2 + j) := by omega
    rw [hsub] at hc
    rw [hc, hexp]
  rw [htail]
  have hcancel : ∀ x y z : ℤ, (x + z) - (y + z) = x - y := fun x y z => by ring
  rw [hcancel]
  have hhead1 :
      (∑ k ∈ Finset.range 10, if cell 395 n (k : ℤ) 0 then (10 : ℤ) ^ (n - k) else 0) =
      (10 : ℤ) ^ (n - 9) * ∑ k ∈ Finset.range 10, if f0 n k then (10 : ℤ) ^ (9 - k) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hklt : k < 10 := Finset.mem_range.mp hk
    have h1 : n = (n - 12) + 12 := by omega
    have hc := (strip_eq (n - 12) k (by omega)).1
    rw [← h1] at hc
    rw [hc]
    split_ifs
    · rw [← pow_add, show n - 9 + (9 - k) = n - k by omega]
    · simp
  have hhead2 :
      (∑ k ∈ Finset.range 2, if cell 395 (n - 8) (k : ℤ) 0 then (10 : ℤ) ^ (n - 8 - k) else 0) =
      (10 : ℤ) ^ (n - 9) * ∑ k ∈ Finset.range 2, if f0 (n - 8) k then (10 : ℤ) ^ (1 - k) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hklt : k < 2 := Finset.mem_range.mp hk
    have h2 : n - 8 = (n - 20) + 12 := by omega
    have hc := (strip_eq (n - 20) k (by omega)).1
    rw [← h2] at hc
    rw [hc]
    split_ifs
    · rw [← pow_add, show n - 9 + (1 - k) = n - 8 - k by omega]
    · simp
  rw [hhead1, hhead2, ← mul_sub, Cval_eq_sum n (by omega)]

private def aGrid (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if gridVal n k 0 then (10 : ℤ) ^ (n - k) else 0

private lemma a_eq_aGrid (n : ℕ) (hn : n ≤ 20) : a n = aGrid n := by
  unfold a aGrid
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cell_eq_gridVal n hn (k : ℤ) 0]
  simp

private lemma a_val_0 : a 0 = 1 := by rw [a_eq_aGrid 0 (by omega)]; decide
private lemma a_val_1 : a 1 = 10 := by rw [a_eq_aGrid 1 (by omega)]; decide
private lemma a_val_2 : a 2 = 111 := by rw [a_eq_aGrid 2 (by omega)]; decide
private lemma a_val_3 : a 3 = 10 := by rw [a_eq_aGrid 3 (by omega)]; decide
private lemma a_val_4 : a 4 = 10111 := by rw [a_eq_aGrid 4 (by omega)]; decide
private lemma a_val_5 : a 5 = 111010 := by rw [a_eq_aGrid 5 (by omega)]; decide
private lemma a_val_6 : a 6 = 10111 := by rw [a_eq_aGrid 6 (by omega)]; decide
private lemma a_val_7 : a 7 = 10101010 := by rw [a_eq_aGrid 7 (by omega)]; decide
private lemma a_val_8 : a 8 = 111010111 := by rw [a_eq_aGrid 8 (by omega)]; decide
private lemma a_val_9 : a 9 = 10111010 := by rw [a_eq_aGrid 9 (by omega)]; decide
private lemma a_val_10 : a 10 = 10101010111 := by rw [a_eq_aGrid 10 (by omega)]; decide
private lemma a_val_11 : a 11 = 111011101010 := by rw [a_eq_aGrid 11 (by omega)]; decide
private lemma a_val_12 : a 12 = 10101010111 := by rw [a_eq_aGrid 12 (by omega)]; decide
private lemma a_val_13 : a 13 = 10101110111010 := by rw [a_eq_aGrid 13 (by omega)]; decide
private lemma a_val_14 : a 14 = 111010101010111 := by rw [a_eq_aGrid 14 (by omega)]; decide
private lemma a_val_15 : a 15 = 10111011101010 := by rw [a_eq_aGrid 15 (by omega)]; decide
private lemma a_val_16 : a 16 = 10101010101010111 := by rw [a_eq_aGrid 16 (by omega)]; decide
private lemma a_val_17 : a 17 = 111011101010111010 := by rw [a_eq_aGrid 17 (by omega)]; decide
private lemma a_val_18 : a 18 = 10101010101010111 := by rw [a_eq_aGrid 18 (by omega)]; decide
private lemma a_val_19 : a 19 = 10101110101011101010 := by rw [a_eq_aGrid 19 (by omega)]; decide

private lemma diff8 (n : ℕ) (hn : 16 ≤ n) :
    a n - a (n - 8) = (10 : ℤ) ^ (n - 9) * Cval n := by
  by_cases h20 : 20 ≤ n
  · exact diff8_ge20 n h20
  · interval_cases n
    · norm_num [a_val_16, a_val_8, Cval]
    · norm_num [a_val_17, a_val_9, Cval]
    · norm_num [a_val_18, a_val_10, Cval]
    · norm_num [a_val_19, a_val_11, Cval]

private lemma Cval_recur (n : ℕ) (hn : 4 ≤ n) :
    Cval n + Cval (n - 1) - Cval (n - 3) - Cval (n - 4) = 0 := by
  unfold Cval
  have h1 : (n - 1) % 6 = (n % 6 + 5) % 6 := by omega
  have h3 : (n - 3) % 6 = (n % 6 + 3) % 6 := by omega
  have h4 : (n - 4) % 6 = (n % 6 + 2) % 6 := by omega
  rw [h1, h3, h4]
  have hr : n % 6 < 6 := Nat.mod_lt n (by omega)
  set r := n % 6
  interval_cases r <;> norm_num

private lemma recur_int (n : ℕ) (hn : 20 ≤ n) :
    a n = -10 * a (n - 1) + 1000 * a (n - 3) + 10000 * a (n - 4) +
          a (n - 8) + 10 * a (n - 9) - 1000 * a (n - 11) - 10000 * a (n - 12) := by
  have h0 := diff8 n (by omega)
  have h1 := diff8 (n - 1) (by omega)
  have h3 := diff8 (n - 3) (by omega)
  have h4 := diff8 (n - 4) (by omega)
  rw [show n - 1 - 8 = n - 9 by omega, show n - 1 - 9 = n - 10 by omega] at h1
  rw [show n - 3 - 8 = n - 11 by omega, show n - 3 - 9 = n - 12 by omega] at h3
  rw [show n - 4 - 8 = n - 12 by omega, show n - 4 - 9 = n - 13 by omega] at h4
  have hp1 : (10 : ℤ) ^ (n - 9) = 10 * (10 : ℤ) ^ (n - 10) := by
    rw [show n - 9 = (n - 10) + 1 by omega, pow_succ]; ring
  have hp3 : (10 : ℤ) ^ (n - 9) = 1000 * (10 : ℤ) ^ (n - 12) := by
    rw [show n - 9 = (n - 12) + 3 by omega, pow_add]; norm_num; ring
  have hp4 : (10 : ℤ) ^ (n - 9) = 10000 * (10 : ℤ) ^ (n - 13) := by
    rw [show n - 9 = (n - 13) + 4 by omega, pow_add]; norm_num; ring
  have hc := Cval_recur n (by omega)
  linear_combination h0 + 10 * h1 - 1000 * h3 - 10000 * h4 -
    Cval (n - 1) * hp1 + Cval (n - 3) * hp3 + Cval (n - 4) * hp4 +
    (10 : ℤ) ^ (n - 9) * hc

private lemma recur_rat (n : ℕ) (hn : 20 ≤ n) :
    (a n : ℚ) = -10 * a (n - 1) + 1000 * a (n - 3) + 10000 * a (n - 4) +
      a (n - 8) + 10 * a (n - 9) - 1000 * a (n - 11) - 10000 * a (n - 12) := by
  exact_mod_cast recur_int n hn

open PowerSeries in
private lemma gf :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      (10000 * X ^ 12 + 1000 * X ^ 11 - 10 * X ^ 9 - X ^ 8 - 10000 * X ^ 4 - 1000 * X ^ 3 + 10 * X + 1 : PowerSeries ℚ) =
    -10000000000 * X ^ 19 - 1000000000 * X ^ 18 - 100000000 * X ^ 17 + 1000000 * X ^ 15 -
      90000 * X ^ 12 + 991000 * X ^ 11 + 1100 * X ^ 9 - 99790 * X ^ 8 - 8880 * X ^ 7 +
      211 * X ^ 6 + 1120 * X ^ 5 - 9789 * X ^ 4 + 120 * X ^ 3 + 211 * X ^ 2 + 20 * X + 1 := by
  set F : PowerSeries ℚ := mk (fun n => (a n : ℚ)) with hF
  have lhs_eq :
      F * (10000 * X ^ 12 + 1000 * X ^ 11 - 10 * X ^ 9 - X ^ 8 - 10000 * X ^ 4 - 1000 * X ^ 3 + 10 * X + 1 : PowerSeries ℚ) =
      F + (10 : ℤ) • (F * X ^ 1) + (-1000 : ℤ) • (F * X ^ 3) + (-10000 : ℤ) • (F * X ^ 4) +
      (-1 : ℤ) • (F * X ^ 8) + (-10 : ℤ) • (F * X ^ 9) + (1000 : ℤ) • (F * X ^ 11) +
      (10000 : ℤ) • (F * X ^ 12) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs_eq :
      (-10000000000 * X ^ 19 - 1000000000 * X ^ 18 - 100000000 * X ^ 17 + 1000000 * X ^ 15 -
        90000 * X ^ 12 + 991000 * X ^ 11 + 1100 * X ^ 9 - 99790 * X ^ 8 - 8880 * X ^ 7 +
        211 * X ^ 6 + 1120 * X ^ 5 - 9789 * X ^ 4 + 120 * X ^ 3 + 211 * X ^ 2 + 20 * X + 1 : PowerSeries ℚ) =
      (1 : ℤ) • X ^ 0 + (20 : ℤ) • X ^ 1 + (211 : ℤ) • X ^ 2 + (120 : ℤ) • X ^ 3 +
      (-9789 : ℤ) • X ^ 4 + (1120 : ℤ) • X ^ 5 + (211 : ℤ) • X ^ 6 + (-8880 : ℤ) • X ^ 7 +
      (-99790 : ℤ) • X ^ 8 + (1100 : ℤ) • X ^ 9 + (991000 : ℤ) • X ^ 11 + (-90000 : ℤ) • X ^ 12 +
      (1000000 : ℤ) • X ^ 15 + (-100000000 : ℤ) • X ^ 17 + (-1000000000 : ℤ) • X ^ 18 +
      (-10000000000 : ℤ) • X ^ 19 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [lhs_eq, rhs_eq]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow]
  simp only [zsmul_eq_mul]
  by_cases hn : 20 ≤ n
  · have hr := recur_rat n hn
    simp only [show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 8 ≤ n by omega, show 9 ≤ n by omega, show 11 ≤ n by omega, show 12 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega,
      show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega,
      show n ≠ 15 by omega, show n ≠ 17 by omega, show n ≠ 18 by omega, show n ≠ 19 by omega,
      ite_true, ite_false]
    push_cast
    linarith
  · interval_cases n <;>
      norm_num [a_val_0, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8,
        a_val_9, a_val_10, a_val_11, a_val_12, a_val_13, a_val_14, a_val_15, a_val_16, a_val_17,
        a_val_18, a_val_19]

theorem OMA.solution : type_of% @OMA.S_oeis_a281749.main := by
  exact ⟨recur_rat, gf⟩
