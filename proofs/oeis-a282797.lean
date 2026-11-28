import OMAStatements.S_oeis_a282797

-- Problem: A282797: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 505
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

open OMA.S_oeis_a282797 PowerSeries

namespace OMA.Proof_oeis_a282797

private abbrev c (t : ℕ) (x y : ℤ) : Bool := cell 505 t x y

private lemma cell_succ (t : ℕ) (x y : ℤ) :
    c (t + 1) x y =
      (505 : ℕ).testBit ((c t x y).toNat + 2 * ((c t (x + 1) y).toNat +
        (c t (x - 1) y).toNat + (c t x (y + 1)).toNat + (c t x (y - 1)).toNat)) :=
  rfl

private lemma abs_le_abs_add_one (z : ℤ) : |z| ≤ |z + 1| + 1 := by
  have h : |(z + 1) - 1| ≤ |z + 1| + |(1 : ℤ)| := abs_sub (z + 1) 1
  have h1 : (z + 1) - 1 = z := by ring
  have h2 : |(1 : ℤ)| = 1 := by norm_num
  rw [h1, h2] at h
  exact h

private lemma abs_le_abs_sub_one (z : ℤ) : |z| ≤ |z - 1| + 1 := by
  have h : |(z - 1) + 1| ≤ |z - 1| + |(1 : ℤ)| := abs_add_le (z - 1) 1
  have h1 : (z - 1) + 1 = z := by ring
  have h2 : |(1 : ℤ)| = 1 := by norm_num
  rw [h1, h2] at h
  exact h

private lemma cell_outside (t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| + |y|) :
    c t x y = decide (Odd t) := by
  induction t generalizing x y with
  | zero =>
    simp only [c, cell, Nat.not_odd_zero, decide_false, decide_eq_false_iff_not, not_and]
    intro hx hy; subst hx; subst hy; simp at h
  | succ t ih =>
    push_cast at h
    have h0 : (t : ℤ) < |x| + |y| := by omega
    have h1 : (t : ℤ) < |x + 1| + |y| := by linarith [abs_le_abs_add_one x]
    have h2 : (t : ℤ) < |x - 1| + |y| := by linarith [abs_le_abs_sub_one x]
    have h3 : (t : ℤ) < |x| + |y + 1| := by linarith [abs_le_abs_add_one y]
    have h4 : (t : ℤ) < |x| + |y - 1| := by linarith [abs_le_abs_sub_one y]
    rw [cell_succ, ih x y h0, ih (x + 1) y h1, ih (x - 1) y h2, ih x (y + 1) h3, ih x (y - 1) h4]
    rcases Nat.even_or_odd t with he | ho
    · have hne : ¬ Odd t := Nat.not_odd_iff_even.mpr he
      have ho1 : Odd (t + 1) := he.add_one
      simp only [hne, ho1, decide_false, decide_true]
      decide
    · have hne1 : ¬ Odd (t + 1) := Nat.not_odd_iff_even.mpr ho.add_one
      simp only [ho, hne1, decide_true, decide_false]
      decide

private lemma cell_neg_x (t : ℕ) (x y : ℤ) : c t (-x) y = c t x y := by
  induction t generalizing x y with
  | zero => simp [c, cell]
  | succ t ih =>
    rw [cell_succ, cell_succ]
    have h1 : -x + 1 = -(x - 1) := by ring
    have h2 : -x - 1 = -(x + 1) := by ring
    rw [h1, h2, ih x y, ih (x - 1) y, ih (x + 1) y, ih x (y + 1), ih x (y - 1)]
    congr 2; omega

private lemma cell_neg_y (t : ℕ) (x y : ℤ) : c t x (-y) = c t x y := by
  induction t generalizing x y with
  | zero => simp [c, cell]
  | succ t ih =>
    rw [cell_succ, cell_succ]
    have h1 : -y + 1 = -(y - 1) := by ring
    have h2 : -y - 1 = -(y + 1) := by ring
    rw [h1, h2, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y - 1), ih x (y + 1)]
    congr 2; omega

private lemma cell_swap (t : ℕ) (x y : ℤ) : c t y x = c t x y := by
  induction t generalizing x y with
  | zero => simp [c, cell, and_comm]
  | succ t ih =>
    rw [cell_succ, cell_succ]
    rw [ih x y, ih x (y + 1), ih x (y - 1), ih (x + 1) y, ih (x - 1) y]
    congr 2; omega

private lemma rule505_s4 (b : Bool) : (505 : ℕ).testBit (b.toNat + 2 * 4) = !b := by
  cases b <;> decide

private lemma rule505_true_step2 (e w n s : Bool) :
    (505 : ℕ).testBit
      (((505 : ℕ).testBit (1 + 2 * (e.toNat + w.toNat + n.toNat + s.toNat))).toNat +
        2 * ((!e).toNat + (!w).toNat + (!n).toNat + (!s).toNat)) = true := by
  cases e <;> cases w <;> cases n <;> cases s <;> decide

private lemma rule505_false_of_ge2 (k : ℕ) (h1 : 2 ≤ k) (h2 : k ≤ 4) :
    (505 : ℕ).testBit (0 + 2 * k) = true := by
  interval_cases k <;> decide

private lemma rule505_true_of_1_3 (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 3) :
    (505 : ℕ).testBit (1 + 2 * k) = true := by
  interval_cases k <;> decide

private def OddInv (t : ℕ) : Prop :=
  (∀ x y : ℤ, ¬ (x = 0 ∧ y = 0) → Even (x + y) → c t x y = true) ∧
  (∀ x y : ℤ, |y| = 1 → x ≠ 0 → c t x y = true) ∧
  (∀ x : ℤ, c t x 0 = decide (x ≠ 0 ∧ (Even x ∨ (t : ℤ) < |x|)))

private lemma oddInv_one : OddInv 1 := by
  have h1 : ∀ x y : ℤ, c 1 x y = decide (¬ (x = 0 ∧ y = 0) ∧ ¬ (|x| + |y| = 1)) := by
    intro x y
    by_cases h0 : x = 0 ∧ y = 0
    · rcases h0 with ⟨rfl, rfl⟩; decide
    · by_cases h1 : |x| + |y| = 1
      · have hcases : (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) := by
          rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
          · rw [abs_of_nonneg hx, abs_of_nonneg hy] at h1; omega
          · rw [abs_of_nonneg hx, abs_of_neg hy] at h1; omega
          · rw [abs_of_neg hx, abs_of_nonneg hy] at h1; omega
          · rw [abs_of_neg hx, abs_of_neg hy] at h1; omega
        rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      · have hgt : (1 : ℤ) < |x| + |y| := by
          have : 0 ≤ |x| := abs_nonneg x
          have : 0 ≤ |y| := abs_nonneg y
          have hne : |x| + |y| ≠ 0 := by
            intro hz
            have hx0 : |x| = 0 := by omega
            have hy0 : |y| = 0 := by omega
            exact h0 ⟨abs_eq_zero.mp hx0, abs_eq_zero.mp hy0⟩
          omega
        have hout := cell_outside 1 x y (by simpa using hgt)
        simp [hout, h0, h1]
  refine ⟨?_, ?_, ?_⟩
  · intro x y hne hev
    rw [h1]
    simp only [decide_eq_true_eq]
    refine ⟨hne, ?_⟩
    intro hsum
    have hcases : (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) := by
      rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
      · rw [abs_of_nonneg hx, abs_of_nonneg hy] at hsum; omega
      · rw [abs_of_nonneg hx, abs_of_neg hy] at hsum; omega
      · rw [abs_of_neg hx, abs_of_nonneg hy] at hsum; omega
      · rw [abs_of_neg hx, abs_of_neg hy] at hsum; omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · rcases hev with ⟨k, hk⟩; omega
  · intro x y hy hx
    rw [h1]
    simp only [decide_eq_true_eq]
    have hx1 : 1 ≤ |x| := by
      rcases lt_or_gt_of_ne hx with h | h
      · rw [abs_of_neg h]; omega
      · rw [abs_of_pos h]; omega
    refine ⟨by intro ⟨h, _⟩; exact hx h, by omega⟩
  · intro x
    rw [h1]
    by_cases hx0 : x = 0
    · subst hx0; decide
    · by_cases hx1 : |x| = 1
      · have hodd : ¬ Even x := by
          intro ⟨k, hk⟩
          rcases le_or_gt 0 x with h | h
          · rw [abs_of_nonneg h] at hx1; omega
          · rw [abs_of_neg h] at hx1; omega
        simp [hx0, hx1, hodd]
      · have hgt : (1 : ℤ) < |x| := by
          have : 1 ≤ |x| := by
            rcases lt_or_gt_of_ne hx0 with h | h
            · rw [abs_of_neg h]; omega
            · rw [abs_of_pos h]; omega
          omega
        simp [hx0, hx1, hgt]

private lemma oddInv_even_step {t : ℕ} (ht : Odd t) (hinv : OddInv t) :
    (∀ x y : ℤ, Odd (x + y) → c (t + 1) x y = !(c t x y)) ∧
    (∀ x : ℤ, c (t + 1) x 0 = decide (|x| ≤ (t + 1 : ℕ))) ∧
    (∀ x y : ℤ, |y| = 1 →
      c (t + 1) x y = decide (x = 0 ∨ (Odd x ∧ |x| ≤ (t : ℤ)))) := by
  obtain ⟨hP1, hP2, hP3⟩ := hinv
  have h1_false : c t 1 0 = false := by
    rw [hP3 1]
    simp only [decide_eq_false_iff_not, not_and, not_or]
    intro _; refine ⟨?_, ?_⟩
    · intro ⟨k, hk⟩; omega
    · rcases ht with ⟨m, rfl⟩; norm_num
  have hm1_false : c t (-1) 0 = false := by
    rw [cell_neg_x t 1 0]; exact h1_false
  have h01_false : c t 0 1 = false := by
    rw [cell_swap t 1 0]; exact h1_false
  have h0m1_false : c t 0 (-1) = false := by
    rw [cell_neg_y t 0 1]; exact h01_false
  have h00_false : c t 0 0 = false := by
    rw [hP3 0]; simp
  have hflip : ∀ x y : ℤ, Odd (x + y) → c (t + 1) x y = !(c t x y) := by
    intro x y hodd
    have he1 : Even ((x + 1) + y) := by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    have he2 : Even ((x - 1) + y) := by rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
    have he3 : Even (x + (y + 1)) := by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    have he4 : Even (x + (y - 1)) := by rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
    rw [cell_succ]
    by_cases h1 : x + 1 = 0 ∧ y = 0
    · rcases h1 with ⟨hx, rfl⟩
      have hx' : x = -1 := by omega
      subst hx'
      have hb : c t (-2) 0 = true := hP1 (-2) 0 (by omega) ⟨-1, by omega⟩
      have hc : c t (-1) 1 = true := hP1 (-1) 1 (by omega) ⟨0, by omega⟩
      have hd : c t (-1) (-1) = true := hP1 (-1) (-1) (by omega) ⟨-1, by omega⟩
      norm_num
      rw [hm1_false, h00_false, hb, hc, hd]; decide
    · by_cases h2 : x - 1 = 0 ∧ y = 0
      · rcases h2 with ⟨hx, rfl⟩
        have hx' : x = 1 := by omega
        subst hx'
        have ha : c t 2 0 = true := hP1 2 0 (by omega) ⟨1, by omega⟩
        have hc : c t 1 1 = true := hP1 1 1 (by omega) ⟨1, by omega⟩
        have hd : c t 1 (-1) = true := hP1 1 (-1) (by omega) ⟨0, by omega⟩
        norm_num
        rw [h1_false, ha, h00_false, hc, hd]; decide
      · by_cases h3 : x = 0 ∧ y + 1 = 0
        · rcases h3 with ⟨rfl, hy⟩
          have hy' : y = -1 := by omega
          subst hy'
          have ha : c t 1 (-1) = true := hP1 1 (-1) (by omega) ⟨0, by omega⟩
          have hb : c t (-1) (-1) = true := hP1 (-1) (-1) (by omega) ⟨-1, by omega⟩
          have hd : c t 0 (-2) = true := hP1 0 (-2) (by omega) ⟨-1, by omega⟩
          norm_num
          rw [h0m1_false, ha, hb, h00_false, hd]; decide
        · by_cases h4 : x = 0 ∧ y - 1 = 0
          · rcases h4 with ⟨rfl, hy⟩
            have hy' : y = 1 := by omega
            subst hy'
            have ha : c t 1 1 = true := hP1 1 1 (by omega) ⟨1, by omega⟩
            have hb : c t (-1) 1 = true := hP1 (-1) 1 (by omega) ⟨0, by omega⟩
            have hc : c t 0 2 = true := hP1 0 2 (by omega) ⟨1, by omega⟩
            norm_num
            rw [h01_false, ha, hb, hc, h00_false]; decide
          · have ha : c t (x + 1) y = true := hP1 (x + 1) y h1 he1
            have hb : c t (x - 1) y = true := hP1 (x - 1) y h2 he2
            have hc : c t x (y + 1) = true := hP1 x (y + 1) h3 he3
            have hd : c t x (y - 1) = true := hP1 x (y - 1) h4 he4
            rw [ha, hb, hc, hd]
            simpa using rule505_s4 (c t x y)
  have hE1 : ∀ x : ℤ, c (t + 1) x 0 = decide (|x| ≤ (t + 1 : ℕ)) := by
    intro x
    rcases Int.even_or_odd x with hev | hodd
    · by_cases hx0 : x = 0
      · subst hx0
        rw [cell_succ]
        norm_num
        rw [h00_false, h1_false, hm1_false, h01_false, h0m1_false]
        have hpos : (0 : ℤ) ≤ (t : ℤ) + 1 := by omega
        simp [hpos]
      · rw [cell_succ]
        simp only [zero_add, zero_sub]
        have hc0 : c t x 0 = true := hP1 x 0 (by intro ⟨h, _⟩; exact hx0 h) (by simpa using hev)
        have hn : c t x 1 = true := hP2 x 1 (by norm_num) hx0
        have hs : c t x (-1) = true := hP2 x (-1) (by norm_num) hx0
        have hodd_p : ¬ Even (x + 1) := by rcases hev with ⟨k, hk⟩; intro ⟨m, hm⟩; omega
        have hodd_m : ¬ Even (x - 1) := by rcases hev with ⟨k, hk⟩; intro ⟨m, hm⟩; omega
        have hxp : c t (x + 1) 0 = decide ((t : ℤ) < |x + 1|) := by
          rw [hP3 (x + 1)]
          have hne : x + 1 ≠ 0 := by rcases hev with ⟨k, hk⟩; omega
          simp [hne, hodd_p]
        have hxm : c t (x - 1) 0 = decide ((t : ℤ) < |x - 1|) := by
          rw [hP3 (x - 1)]
          have hne : x - 1 ≠ 0 := by rcases hev with ⟨k, hk⟩; omega
          simp [hne, hodd_m]
        rw [hc0, hn, hs, hxp, hxm]
        by_cases hle : |x| ≤ ((t + 1 : ℕ) : ℤ)
        · simp only [hle, decide_true]
          have hor : ¬ ((t : ℤ) < |x + 1|) ∨ ¬ ((t : ℤ) < |x - 1|) := by
            rcases le_or_gt 0 x with hx | hx
            · right; rw [abs_of_nonneg hx] at hle; rw [abs_of_nonneg (by omega)]; omega
            · left; rw [abs_of_neg hx] at hle; rw [abs_of_nonpos (by omega)]; omega
          rcases hor with hp | hm
          · rw [decide_eq_false hp]; cases (decide ((t : ℤ) < |x - 1|)) <;> decide
          · rw [decide_eq_false hm]; cases (decide ((t : ℤ) < |x + 1|)) <;> decide
        · simp only [hle, decide_false]
          have hp : (t : ℤ) < |x + 1| := by
            rcases ht with ⟨m, rfl⟩
            rcases hev with ⟨k, hk⟩
            rcases le_or_gt 0 x with hx | hx
            · rw [abs_of_nonneg hx] at hle; rw [abs_of_nonneg (by omega)]; omega
            · rw [abs_of_neg hx] at hle; rw [abs_of_neg (by omega)]; omega
          have hm : (t : ℤ) < |x - 1| := by
            rcases ht with ⟨m, rfl⟩
            rcases hev with ⟨k, hk⟩
            rcases le_or_gt 0 x with hx | hx
            · rw [abs_of_nonneg hx] at hle; rw [abs_of_nonneg (by omega)]; omega
            · rw [abs_of_neg hx] at hle; rw [abs_of_neg (by omega)]; omega
          rw [decide_eq_true hp, decide_eq_true hm]; decide
    · have hf := hflip x 0 (by simpa using hodd)
      rw [hf, hP3 x]
      have hx0 : x ≠ 0 := by rcases hodd with ⟨k, hk⟩; omega
      have hne : ¬ Even x := by rcases hodd with ⟨k, hk⟩; intro ⟨m, hm⟩; omega
      simp only [hx0, ne_eq, not_false_eq_true, hne, false_or, true_and]
      have hiff : |x| ≤ (t : ℤ) ↔ |x| ≤ ((t + 1 : ℕ) : ℤ) := by
        rcases ht with ⟨m, rfl⟩
        rcases hodd with ⟨k, hk⟩
        rcases le_or_gt 0 x with hx | hx
        · rw [abs_of_nonneg hx]; omega
        · rw [abs_of_neg hx]; omega
      by_cases h : |x| ≤ (t : ℤ)
      · have h1 : ¬ ((t : ℤ) < |x|) := by omega
        have h2 : |x| ≤ ((t + 1 : ℕ) : ℤ) := hiff.mp h
        rw [decide_eq_false h1, decide_eq_true h2]; rfl
      · have h1 : (t : ℤ) < |x| := by omega
        have h2 : ¬ (|x| ≤ ((t + 1 : ℕ) : ℤ)) := fun hc => h (hiff.mpr hc)
        rw [decide_eq_true h1, decide_eq_false h2]; rfl
  have hE2 : ∀ x y : ℤ, |y| = 1 →
      c (t + 1) x y = decide (x = 0 ∨ (Odd x ∧ |x| ≤ (t : ℤ))) := by
    intro x y hy
    rcases Int.even_or_odd x with hev | hodd
    · have hodd_sum : Odd (x + y) := by
        rcases hev with ⟨k, hk⟩
        have hycases : y = 1 ∨ y = -1 := by
          rcases le_or_gt 0 y with h | h
          · left; rw [abs_of_nonneg h] at hy; omega
          · right; rw [abs_of_neg h] at hy; omega
        rcases hycases with rfl | rfl
        · exact ⟨k, by omega⟩
        · exact ⟨k - 1, by omega⟩
      rw [hflip x y hodd_sum]
      by_cases hx0 : x = 0
      · subst hx0
        have hy1 : c t 0 y = false := by
          have hycases : y = 1 ∨ y = -1 := by
            rcases le_or_gt 0 y with h | h
            · left; rw [abs_of_nonneg h] at hy; omega
            · right; rw [abs_of_neg h] at hy; omega
          rcases hycases with rfl | rfl
          · exact h01_false
          · exact h0m1_false
        simp [hy1]
      · have hne : ¬ Odd x := by rcases hev with ⟨k, hk⟩; intro ⟨m, hm⟩; omega
        rw [hP2 x y hy hx0]
        simp [hx0, hne]
    · have hx0 : x ≠ 0 := by rcases hodd with ⟨k, hk⟩; omega
      by_cases hle : |x| ≤ (t : ℤ)
      · simp only [hx0, false_or, hodd, hle, and_self, decide_true]
        rw [cell_succ]
        have hc0 : c t x y = true := hP2 x y hy hx0
        have hbot : c t x 0 = false := by
          rw [hP3 x]
          have hne : ¬ Even x := by rcases hodd with ⟨k, hk⟩; intro ⟨m, hm⟩; omega
          simp [hx0, hne, show ¬ ((t : ℤ) < |x|) by omega]
        have hside : c t (x + 1) y = true ∨ c t (x - 1) y = true := by
          by_cases hp : x + 1 = 0
          · right; exact hP2 (x - 1) y hy (by omega)
          · left; exact hP2 (x + 1) y hy hp
        have hbot_eq : c t x (y - 1) = false ∨ c t x (y + 1) = false := by
          have hycases : y = 1 ∨ y = -1 := by
            rcases le_or_gt 0 y with h | h
            · left; rw [abs_of_nonneg h] at hy; omega
            · right; rw [abs_of_neg h] at hy; omega
          rcases hycases with rfl | rfl
          · left; simpa using hbot
          · right; simpa using hbot
        rw [hc0]
        set e := c t (x + 1) y
        set w := c t (x - 1) y
        set n := c t x (y + 1)
        set s := c t x (y - 1)
        have h1 : 1 ≤ e.toNat + w.toNat + n.toNat + s.toNat := by
          rcases hside with h | h <;> simp [h] <;> omega
        have h2 : e.toNat + w.toNat + n.toNat + s.toNat ≤ 3 := by
          rcases hbot_eq with h | h
          · simp only [h, Bool.toNat_false, add_zero]
            have := Bool.toNat_le e; have := Bool.toNat_le w; have := Bool.toNat_le n; omega
          · simp only [h, Bool.toNat_false, add_zero]
            have := Bool.toNat_le e; have := Bool.toNat_le w; have := Bool.toNat_le s; omega
        exact rule505_true_of_1_3 _ h1 h2
      · have hgt : ((t + 1 : ℕ) : ℤ) < |x| + |y| := by
          rcases ht with ⟨m, rfl⟩
          rcases hodd with ⟨k, hk⟩
          rcases le_or_gt 0 x with hx | hx
          · rw [abs_of_nonneg hx] at hle ⊢; omega
          · rw [abs_of_neg hx] at hle ⊢; omega
        have hout := cell_outside (t + 1) x y hgt
        have hev1 : ¬ Odd (t + 1) := Nat.not_odd_iff_even.mpr ht.add_one
        simp [hout, hev1, hx0, hle]
  exact ⟨hflip, hE1, hE2⟩

private lemma oddInv_step2 {t : ℕ} (ht : Odd t) (hinv : OddInv t) : OddInv (t + 2) := by
  obtain ⟨hflip, hE1, hE2⟩ := oddInv_even_step ht hinv
  obtain ⟨hP1, hP2, hP3⟩ := hinv
  have hP1' : ∀ x y : ℤ, ¬ (x = 0 ∧ y = 0) → Even (x + y) → c (t + 2) x y = true := by
    intro x y hne hev
    have ho1 : Odd ((x + 1) + y) := by rcases hev with ⟨k, hk⟩; exact ⟨k, by omega⟩
    have ho2 : Odd ((x - 1) + y) := by rcases hev with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    have ho3 : Odd (x + (y + 1)) := by rcases hev with ⟨k, hk⟩; exact ⟨k, by omega⟩
    have ho4 : Odd (x + (y - 1)) := by rcases hev with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    have hc : c t x y = true := hP1 x y hne hev
    have hf1 := hflip (x + 1) y ho1
    have hf2 := hflip (x - 1) y ho2
    have hf3 := hflip x (y + 1) ho3
    have hf4 := hflip x (y - 1) ho4
    change c ((t + 1) + 1) x y = true
    rw [cell_succ, hf1, hf2, hf3, hf4, cell_succ, hc, Bool.toNat_true]
    exact rule505_true_step2 (c t (x + 1) y) (c t (x - 1) y) (c t x (y + 1)) (c t x (y - 1))
  have hP2' : ∀ x y : ℤ, |y| = 1 → x ≠ 0 → c (t + 2) x y = true := by
    intro x y hy hx0
    rcases Int.even_or_odd x with hev | hodd
    · by_cases hle : |x| ≤ ((t + 1 : ℕ) : ℤ)
      · change c ((t + 1) + 1) x y = true
        rw [cell_succ]
        have hc0 : c (t + 1) x y = false := by
          have := hE2 x y hy
          have hno : ¬ Odd x := by rcases hev with ⟨k, hk⟩; intro ⟨m, hm⟩; omega
          simpa [hx0, hno] using this
        have hbot : c (t + 1) x 0 = true := by
          rw [hE1 x, decide_eq_true hle]
        have hbot_eq : c (t + 1) x (y - 1) = true ∨ c (t + 1) x (y + 1) = true := by
          have hycases : y = 1 ∨ y = -1 := by
            rcases le_or_gt 0 y with h | h
            · left; rw [abs_of_nonneg h] at hy; omega
            · right; rw [abs_of_neg h] at hy; omega
          rcases hycases with rfl | rfl
          · left; simpa using hbot
          · right; simpa using hbot
        have hside : c (t + 1) (x + 1) y = true ∨ c (t + 1) (x - 1) y = true := by
          rcases le_or_gt 0 x with hx | hx
          · right
            have h1 := hE2 (x - 1) y hy
            have ho : Odd (x - 1) := by rcases hev with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
            have hle' : |x - 1| ≤ (t : ℤ) := by
              rw [abs_of_nonneg hx] at hle
              rw [abs_of_nonneg (by omega)]
              omega
            simpa [ho, hle'] using h1
          · left
            have h1 := hE2 (x + 1) y hy
            have ho : Odd (x + 1) := by rcases hev with ⟨k, hk⟩; exact ⟨k, by omega⟩
            have hle' : |x + 1| ≤ (t : ℤ) := by
              rw [abs_of_neg hx] at hle
              rw [abs_of_nonpos (by omega)]
              omega
            simpa [ho, hle'] using h1
        rw [hc0, Bool.toNat_false]
        set e := c (t + 1) (x + 1) y
        set w := c (t + 1) (x - 1) y
        set n := c (t + 1) x (y + 1)
        set s := c (t + 1) x (y - 1)
        have hge2 : 2 ≤ e.toNat + w.toNat + n.toNat + s.toNat := by
          rcases hside with hs1 | hs1 <;> rcases hbot_eq with hb1 | hb1 <;> simp [hs1, hb1] <;> omega
        have hle4 : e.toNat + w.toNat + n.toNat + s.toNat ≤ 4 := by
          have := Bool.toNat_le e; have := Bool.toNat_le w; have := Bool.toNat_le n; have := Bool.toNat_le s; omega
        exact rule505_false_of_ge2 _ hge2 hle4
      · have hgt : ((t + 2 : ℕ) : ℤ) < |x| + |y| := by
          rcases ht with ⟨m, rfl⟩
          rcases hev with ⟨k, hk⟩
          rcases le_or_gt 0 x with hx | hx
          · rw [abs_of_nonneg hx] at hle ⊢; omega
          · rw [abs_of_neg hx] at hle ⊢; omega
        have hout := cell_outside (t + 2) x y hgt
        have ho2 : Odd (t + 2) := by rcases ht with ⟨m, rfl⟩; exact ⟨m + 1, by omega⟩
        simpa [ho2] using hout
    · apply hP1' x y (by intro ⟨h, _⟩; exact hx0 h)
      rcases hodd with ⟨k, hk⟩
      have hycases : y = 1 ∨ y = -1 := by
        rcases le_or_gt 0 y with h | h
        · left; rw [abs_of_nonneg h] at hy; omega
        · right; rw [abs_of_neg h] at hy; omega
      rcases hycases with rfl | rfl
      · exact ⟨k + 1, by omega⟩
      · exact ⟨k, by omega⟩
  have hP3' : ∀ x : ℤ, c (t + 2) x 0 = decide (x ≠ 0 ∧ (Even x ∨ ((t + 2 : ℕ) : ℤ) < |x|)) := by
    intro x
    rcases Int.even_or_odd x with hev | hodd
    · by_cases hx0 : x = 0
      · subst hx0
        change c ((t + 1) + 1) 0 0 = decide _
        rw [cell_succ]
        have h0 : c (t + 1) 0 0 = true := by
          rw [hE1 0, decide_eq_true (by simp; omega)]
        have h1 : c (t + 1) 1 0 = true := by
          rw [hE1 1, decide_eq_true (by norm_num)]
        have h2 : c (t + 1) (-1) 0 = true := by
          rw [hE1 (-1), decide_eq_true (by norm_num)]
        have h3 : c (t + 1) 0 1 = true := by
          have := hE2 0 1 (by norm_num); simpa using this
        have h4 : c (t + 1) 0 (-1) = true := by
          have := hE2 0 (-1) (by norm_num); simpa using this
        simp only [zero_add, zero_sub]
        rw [h0, h1, h2, h3, h4]
        simp; decide
      · have h1 := hP1' x 0 (by intro ⟨h, _⟩; exact hx0 h) (by simpa using hev)
        simp [h1, hx0, hev]
    · have hx0 : x ≠ 0 := by rcases hodd with ⟨k, hk⟩; omega
      have hne : ¬ Even x := by rcases hodd with ⟨k, hk⟩; intro ⟨m, hm⟩; omega
      change c ((t + 1) + 1) x 0 = _
      rw [cell_succ]
      simp only [zero_add, zero_sub]
      have h0 : c (t + 1) x 0 = decide (|x| ≤ ((t + 1 : ℕ) : ℤ)) := hE1 x
      have hp : c (t + 1) (x + 1) 0 = decide (|x + 1| ≤ ((t + 1 : ℕ) : ℤ)) := hE1 (x + 1)
      have hm : c (t + 1) (x - 1) 0 = decide (|x - 1| ≤ ((t + 1 : ℕ) : ℤ)) := hE1 (x - 1)
      have hn : c (t + 1) x 1 = decide (|x| ≤ (t : ℤ)) := by
        have := hE2 x 1 (by norm_num); simpa [hx0, hodd] using this
      have hs : c (t + 1) x (-1) = decide (|x| ≤ (t : ℤ)) := by
        have := hE2 x (-1) (by norm_num); simpa [hx0, hodd] using this
      rw [h0, hp, hm, hn, hs]
      simp only [hx0, ne_eq, not_false_eq_true, hne, false_or, true_and]
      by_cases hle : |x| ≤ (t : ℤ)
      · have hle1 : |x| ≤ ((t + 1 : ℕ) : ℤ) := by omega
        have hlep : |x + 1| ≤ ((t + 1 : ℕ) : ℤ) := by
          have := abs_add_le x 1; norm_num at this; omega
        have hlem : |x - 1| ≤ ((t + 1 : ℕ) : ℤ) := by
          have := abs_sub x 1; norm_num at this; omega
        have hnotgt : ¬ (((t + 2 : ℕ) : ℤ) < |x|) := by omega
        rw [decide_eq_true hle1, decide_eq_true hlep, decide_eq_true hlem, decide_eq_true hle,
            decide_eq_false hnotgt]
        decide
      · by_cases heq : |x| = ((t + 2 : ℕ) : ℤ)
        · have hnot0 : ¬ (|x| ≤ ((t + 1 : ℕ) : ℤ)) := by omega
          have hnotgt : ¬ (((t + 2 : ℕ) : ℤ) < |x|) := by omega
          rw [decide_eq_false hnot0, decide_eq_false hle, decide_eq_false hnotgt]
          rcases le_or_gt 0 x with hx | hx
          · rw [abs_of_nonneg hx] at heq
            have h1 : ¬ (|x + 1| ≤ ((t + 1 : ℕ) : ℤ)) := by rw [abs_of_nonneg (by omega)]; omega
            have h2 : |x - 1| ≤ ((t + 1 : ℕ) : ℤ) := by rw [abs_of_nonneg (by omega)]; omega
            rw [decide_eq_false h1, decide_eq_true h2]; decide
          · rw [abs_of_neg hx] at heq
            have h1 : |x + 1| ≤ ((t + 1 : ℕ) : ℤ) := by rw [abs_of_nonpos (by omega)]; omega
            have h2 : ¬ (|x - 1| ≤ ((t + 1 : ℕ) : ℤ)) := by rw [abs_of_neg (by omega)]; omega
            rw [decide_eq_true h1, decide_eq_false h2]; decide
        · have hgt : ((t + 2 : ℕ) : ℤ) < |x| := by
            rcases ht with ⟨m, rfl⟩
            rcases hodd with ⟨k, hk⟩
            rcases le_or_gt 0 x with hx | hx
            · rw [abs_of_nonneg hx] at hle heq ⊢; omega
            · rw [abs_of_neg hx] at hle heq ⊢; omega
          have hnot0 : ¬ (|x| ≤ ((t + 1 : ℕ) : ℤ)) := by omega
          have hnotp : ¬ (|x + 1| ≤ ((t + 1 : ℕ) : ℤ)) := by
            push_cast at hgt ⊢; linarith [abs_le_abs_add_one x]
          have hnotm : ¬ (|x - 1| ≤ ((t + 1 : ℕ) : ℤ)) := by
            push_cast at hgt ⊢; linarith [abs_le_abs_sub_one x]
          rw [decide_eq_false hnot0, decide_eq_false hnotp, decide_eq_false hnotm,
              decide_eq_false hle, decide_eq_true hgt]
          decide
  exact ⟨hP1', hP2', hP3'⟩

private lemma oddInv_all (m : ℕ) : OddInv (2 * m + 1) := by
  induction m with
  | zero => exact oddInv_one
  | succ m ih =>
    have hstep : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    rw [hstep]
    exact oddInv_step2 ⟨m, rfl⟩ ih

private lemma axis_even (n : ℕ) (hn : Even n) (x : ℤ) :
    c n x 0 = decide (|x| ≤ (n : ℤ)) := by
  rcases hn with ⟨m, rfl⟩
  cases m with
  | zero =>
    simp only [Nat.cast_zero, add_zero, c, cell, and_true]
    by_cases hx : x = 0
    · subst hx; simp
    · have : ¬ (|x| ≤ 0) := by
        intro h
        exact hx (abs_eq_zero.mp (le_antisymm h (abs_nonneg x)))
      simp [hx, this]
  | succ m =>
    have heq : (m + 1) + (m + 1) = (2 * m + 1) + 1 := by omega
    rw [heq]
    have hE := (oddInv_even_step ⟨m, rfl⟩ (oddInv_all m)).2.1 x
    simpa [Nat.cast_add, Nat.cast_one] using hE

private lemma axis_odd (n : ℕ) (hn : Odd n) (x : ℤ) :
    c n x 0 = decide (x ≠ 0 ∧ (Even x ∨ (n : ℤ) < |x|)) := by
  rcases hn with ⟨m, rfl⟩
  exact (oddInv_all m).2.2 x

private lemma geom_ten_even (n : ℕ) :
    9 * (∑ k ∈ Finset.range (n + 1), (10 : ℚ) ^ (n - k)) = (10 : ℚ) ^ (n + 1) - 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hshift : (∑ k ∈ Finset.range (n + 1), (10 : ℚ) ^ (n + 1 - k)) =
        10 * ∑ k ∈ Finset.range (n + 1), (10 : ℚ) ^ (n - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k < n + 1 := Finset.mem_range.mp hk
      have heq : n + 1 - k = (n - k) + 1 := by omega
      rw [heq, pow_succ']
    rw [hshift]
    have hsub : n + 1 - (n + 1) = 0 := by omega
    rw [hsub, pow_zero, pow_succ]
    linarith

private lemma a_even_rat (n : ℕ) (hn : Even n) :
    (a n : ℚ) = ((10 : ℚ) ^ (n + 1) - 1) / 9 := by
  have ha : a n = ∑ k ∈ Finset.range (n + 1), (10 : ℤ) ^ (n - k) := by
    unfold a
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hst : cell 505 n (k : ℤ) 0 = true := by
      have := axis_even n hn (k : ℤ)
      simp only [c] at this
      rw [this, abs_of_nonneg (Nat.cast_nonneg k)]
      simp [hkn]
    simp [hst]
  rw [ha]
  push_cast
  have h := geom_ten_even n
  linarith

private lemma geom_hundred_odd (m : ℕ) :
    99 * (∑ j ∈ Finset.range m, (10 : ℚ) ^ (2 * (m - 1 - j) + 1)) = (10 : ℚ) ^ (2 * m + 1) - 10 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hshift : (∑ j ∈ Finset.range m, (10 : ℚ) ^ (2 * (m + 1 - 1 - j) + 1)) =
        100 * ∑ j ∈ Finset.range m, (10 : ℚ) ^ (2 * (m - 1 - j) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjm : j < m := Finset.mem_range.mp hj
      have heq : 2 * (m + 1 - 1 - j) + 1 = (2 * (m - 1 - j) + 1) + 2 := by omega
      rw [heq, pow_add]
      ring
    rw [hshift]
    have hsub : 2 * (m + 1 - 1 - m) + 1 = 1 := by omega
    rw [hsub, pow_one]
    have hpow : (10 : ℚ) ^ (2 * (m + 1) + 1) = 100 * (10 : ℚ) ^ (2 * m + 1) := by
      have : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
      rw [this, pow_add]; ring
    linarith

private lemma a_odd_rat (n : ℕ) (hn : Odd n) :
    (a n : ℚ) = ((10 : ℚ) ^ n - 10) / 99 := by
  rcases hn with ⟨m, rfl⟩
  have hsum : a (2 * m + 1) = ∑ j ∈ Finset.range m, (10 : ℤ) ^ (2 * (m - 1 - j) + 1) := by
    unfold a
    have hterm : ∀ k ∈ Finset.range (2 * m + 1 + 1),
        (if cell 505 (2 * m + 1) (k : ℤ) 0 then (10 : ℤ) ^ (2 * m + 1 - k) else 0) =
        if k ≠ 0 ∧ Even k then (10 : ℤ) ^ (2 * m + 1 - k) else 0 := by
      intro k hk
      have hkle : k ≤ 2 * m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hst : cell 505 (2 * m + 1) (k : ℤ) 0 = decide (k ≠ 0 ∧ Even k) := by
        have := axis_odd (2 * m + 1) ⟨m, rfl⟩ (k : ℤ)
        simp only [c] at this
        rw [this, abs_of_nonneg (Nat.cast_nonneg k)]
        have hnotgt : ¬ (2 * (m : ℤ) + 1 < (k : ℤ)) := by omega
        have hev : Even (k : ℤ) ↔ Even k := Int.even_coe_nat k
        simp [hnotgt, hev]
      simp [hst]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    refine Finset.sum_bij (fun k _ => k / 2 - 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      rcases hk.2.2 with ⟨r, hr⟩
      rw [Finset.mem_range]; omega
    · intro k1 hk1 k2 hk2 h
      simp only [Finset.mem_filter, Finset.mem_range] at hk1 hk2
      rcases hk1.2.2 with ⟨r1, hr1⟩
      rcases hk2.2.2 with ⟨r2, hr2⟩
      omega
    · intro j hj
      rw [Finset.mem_range] at hj
      refine ⟨2 * (j + 1), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by omega, ⟨j + 1, by omega⟩⟩
      · omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      rcases hk.2.2 with ⟨r, hr⟩
      congr 1; omega
  rw [hsum]
  push_cast
  have h := geom_hundred_odd m
  linarith

private lemma a_rec (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℚ) = 101 * (a (n - 2) : ℚ) - 100 * (a (n - 4) : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hm2 : m + 4 - 2 = m + 2 := by omega
  have hm4 : m + 4 - 4 = m := by omega
  rw [hm2, hm4]
  rcases Nat.even_or_odd m with hm | hm
  · have h2 : Even (m + 2) := hm.add (by decide)
    have h4 : Even (m + 4) := hm.add (by decide)
    rw [a_even_rat _ h4, a_even_rat _ h2, a_even_rat _ hm]
    ring
  · have h2 : Odd (m + 2) := hm.add_even (by decide)
    have h4 : Odd (m + 4) := hm.add_even (by decide)
    rw [a_odd_rat _ h4, a_odd_rat _ h2, a_odd_rat _ hm]
    ring

private lemma a_val_0 : (a 0 : ℚ) = 1 := by rw [a_even_rat 0 (by decide)]; norm_num
private lemma a_val_1 : (a 1 : ℚ) = 0 := by rw [a_odd_rat 1 (by decide)]; norm_num
private lemma a_val_2 : (a 2 : ℚ) = 111 := by rw [a_even_rat 2 (by decide)]; norm_num
private lemma a_val_3 : (a 3 : ℚ) = 10 := by rw [a_odd_rat 3 (by decide)]; norm_num

private lemma coeff_mul_X_pow (f : ℚ⟦X⟧) (k n : ℕ) :
    PowerSeries.coeff n (f * X ^ k) = if k ≤ n then PowerSeries.coeff (n - k) f else 0 :=
  PowerSeries.coeff_mul_X_pow' f k n

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      1 + 10 * X ^ 2 + 10 * X ^ 3 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  have hD : ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : ℚ⟦X⟧) =
      1 - C (101 : ℚ) * X ^ 2 + C (100 : ℚ) * X ^ 4 := by
    simp only [map_ofNat]; ring
  have hN : (1 + 10 * X ^ 2 + 10 * X ^ 3 : ℚ⟦X⟧) =
      C (1 : ℚ) + C (10 : ℚ) * X ^ 2 + C (10 : ℚ) * X ^ 3 := by
    simp only [map_one, map_ofNat]
  rw [hD, hN]
  ext n
  have hmul : A * (1 - C (101 : ℚ) * X ^ 2 + C (100 : ℚ) * X ^ 4) =
      A - C (101 : ℚ) * (A * X ^ 2) + C (100 : ℚ) * (A * X ^ 4) := by ring
  rw [hmul]
  simp only [map_add, map_sub, PowerSeries.coeff_C, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, coeff_mul_X_pow, A, PowerSeries.coeff_mk]
  match n with
  | 0 => simp [a_val_0]
  | 1 => simp [a_val_1]
  | 2 => simp [a_val_0, a_val_2]; norm_num
  | 3 => simp [a_val_1, a_val_3]
  | m + 4 =>
    have hrec := a_rec (m + 4) (by omega)
    have h0 : m + 4 ≠ 0 := by omega
    have h2 : m + 4 ≠ 2 := by omega
    have h3 : m + 4 ≠ 3 := by omega
    have hge2 : 2 ≤ m + 4 := by omega
    have hge4 : 4 ≤ m + 4 := by omega
    simp only [h0, h2, h3, hge2, hge4, ↓reduceIte, mul_zero, add_zero]
    linarith

end OMA.Proof_oeis_a282797

theorem OMA.solution : type_of% @OMA.S_oeis_a282797.main :=
  ⟨OMA.Proof_oeis_a282797.a_even_rat,
   OMA.Proof_oeis_a282797.a_odd_rat,
   OMA.Proof_oeis_a282797.a_rec,
   OMA.Proof_oeis_a282797.gf_eq⟩
