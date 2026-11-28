import OMAStatements.S_oeis_a281742
import Mathlib

namespace OMA.Helpers_a281742

open OMA.S_oeis_a281742

/-- the local rule of code 393: arguments are the cell, its left, right, up and down neighbours -/
def R (c l r u d : Bool) : Bool := Nat.testBit 393 (c.toNat + 2 * (r.toNat + l.toNat + u.toNat + d.toNat))

lemma cell_succ (t : ℕ) (i j : ℤ) : cell 393 (t + 1) i j =
    R (cell 393 t i j) (cell 393 t (i - 1) j) (cell 393 t (i + 1) j) (cell 393 t i (j + 1))
      (cell 393 t i (j - 1)) := rfl

def bg (t : ℕ) : Bool := t % 2 == 1

def newRow (M : ℕ) (b b' : Bool) (up c dn : ℕ) : ℕ :=
  let bm := if b then M else 0
  let cr := c ^^^ bm
  let l := ((c <<< 1) &&& M) ^^^ bm
  let r := (c >>> 1) ^^^ bm
  let u := up ^^^ bm
  let d := dn ^^^ bm
  let p := l ^^^ r ^^^ u ^^^ d
  let e := (M ^^^ (l ^^^ r)) &&& (M ^^^ (r ^^^ u)) &&& (M ^^^ (u ^^^ d))
  let nw := (cr &&& p) ||| ((M ^^^ cr) &&& e)
  nw ^^^ (if b' then M else 0)

lemma R_formula (c l r u d b b' : Bool) :
    ((((c ^^ b) && ((l ^^ b) ^^ (r ^^ b) ^^ (u ^^ b) ^^ (d ^^ b))) ||
      ((true ^^ (c ^^ b)) && ((true ^^ ((l ^^ b) ^^ (r ^^ b))) && (true ^^ ((r ^^ b) ^^ (u ^^ b))) &&
        (true ^^ ((u ^^ b) ^^ (d ^^ b)))))) ^^ b') =
      (R (c ^^ b) (l ^^ b) (r ^^ b) (u ^^ b) (d ^^ b) ^^ b') := by
  cases c <;> cases l <;> cases r <;> cases u <;> cases d <;> cases b <;> cases b' <;> decide

lemma newRow_bit (w : ℕ) (b b' : Bool) (up c dn k : ℕ) (hk : k < w) :
    (newRow (2 ^ w - 1) b b' up c dn).testBit k =
      (R (c.testBit k ^^ b) ((decide (1 ≤ k) && c.testBit (k - 1)) ^^ b) (c.testBit (k + 1) ^^ b)
        (up.testBit k ^^ b) (dn.testBit k ^^ b) ^^ b') := by
  have hM : (2 ^ w - 1).testBit k = true := by simp [hk]
  have hb : ∀ x : Bool, (if x then 2 ^ w - 1 else 0).testBit k = x := by
    intro x; cases x <;> simp [hk]
  simp only [newRow, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, hM, hb]
  rw [← R_formula]
  rw [show 1 + k = k + 1 by omega]
  cases (decide (1 ≤ k)) <;> cases (decide (k ≥ 1)) <;> simp

lemma R_bg (b : Bool) : R b b b b b = !b := by cases b <;> decide

lemma bg_succ (t : ℕ) : bg (t + 1) = !bg t := by
  unfold bg
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [Nat.add_mod, h]

/-- outside the light cone every cell shows the background -/
lemma cone : ∀ t : ℕ, ∀ i j : ℤ, (t : ℤ) < |i| + |j| → cell 393 t i j = bg t := by
  intro t
  induction t with
  | zero =>
    intro i j h
    show decide (i = 0 ∧ j = 0) = bg 0
    have : ¬(i = 0 ∧ j = 0) := by rintro ⟨rfl, rfl⟩; simp at h
    simp [this, bg]
  | succ t ih =>
    intro i j h
    push_cast at h
    rw [cell_succ, ih _ _ (by cases abs_cases i <;> cases abs_cases j <;> omega),
      ih _ _ (by cases abs_cases i <;> cases abs_cases j <;> cases abs_cases (i - 1) <;> omega),
      ih _ _ (by cases abs_cases i <;> cases abs_cases j <;> cases abs_cases (i + 1) <;> omega),
      ih _ _ (by cases abs_cases i <;> cases abs_cases j <;> cases abs_cases (j + 1) <;> omega),
      ih _ _ (by cases abs_cases i <;> cases abs_cases j <;> cases abs_cases (j - 1) <;> omega),
      R_bg, bg_succ]

/-- the whole window `[-W, W]²` packed in one natural number, bit `(j + W) * w + (i + W)` -/
def gstep (W : ℕ) (b b' : Bool) (g : ℕ) : ℕ :=
  newRow (2 ^ ((2 * W + 1) * (2 * W + 1)) - 1) b b' (g >>> (2 * W + 1)) g
    ((g <<< (2 * W + 1)) &&& (2 ^ ((2 * W + 1) * (2 * W + 1)) - 1))

def grid (W : ℕ) : ℕ → ℕ
  | 0 => 2 ^ (W * (2 * W + 1) + W)
  | t + 1 => gstep W (bg t) (bg (t + 1)) (grid W t)

lemma newRow_lt (n : ℕ) (b b' : Bool) (up c dn : ℕ) (hu : up < 2 ^ n) (hc : c < 2 ^ n)
    (hd : dn < 2 ^ n) : newRow (2 ^ n - 1) b b' up c dn < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  have h1 : ∀ x, x < 2 ^ n → x.testBit k = false := fun x hx =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk))
  have hM : (2 ^ n - 1).testBit k = false := by simp; omega
  have hb : ∀ x : Bool, (if x then 2 ^ n - 1 else 0).testBit k = false := by
    intro x; cases x <;> simp [hM]
  simp only [newRow, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, hM, hb, h1 up hu, h1 c hc, h1 dn hd]
  simp

lemma grid_lt (W t : ℕ) : grid W t < 2 ^ ((2 * W + 1) * (2 * W + 1)) := by
  induction t with
  | zero => exact Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  | succ t ih =>
    refine newRow_lt _ _ _ _ _ _ ?_ ih ?_
    · exact lt_of_le_of_lt (Nat.shiftRight_le _ _) ih
    · exact lt_of_le_of_lt Nat.and_le_right (by have := Nat.one_le_two_pow (n := (2 * W + 1) * (2 * W + 1)); omega)

lemma pos_inj {w a b a' b' : ℕ} (ha : a < w) (ha' : a' < w) (h : b * w + a = b' * w + a') :
    a = a' ∧ b = b' := by
  rcases lt_trichotomy b b' with h1 | h1 | h1
  · have : (b + 1) * w ≤ b' * w := Nat.mul_le_mul_right _ h1
    nlinarith
  · subst h1; omega
  · have : (b' + 1) * w ≤ b * w := Nat.mul_le_mul_right _ h1
    nlinarith

def S (W t : ℕ) (i j : ℤ) : Bool :=
  if -(W : ℤ) ≤ i ∧ i ≤ W ∧ -(W : ℤ) ≤ j ∧ j ≤ W then
    (grid W t).testBit ((j + W).toNat * (2 * W + 1) + (i + W).toNat) ^^ bg t
  else bg t

lemma cell_eq (W T : ℕ) (hW : T + 1 < W) : ∀ t ≤ T, ∀ i j : ℤ, cell 393 t i j = S W t i j := by
  intro t
  induction t with
  | zero =>
    intro _ i j
    show decide (i = 0 ∧ j = 0) = S W 0 i j
    unfold S
    split_ifs with hin
    · simp only [grid, bg, Nat.testBit_two_pow]
      by_cases h : i = 0 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := h; simp
      · have : W * (2 * W + 1) + W ≠ (j + W).toNat * (2 * W + 1) + (i + W).toNat := by
          intro he
          apply h
          have := pos_inj (w := 2 * W + 1) (a := W) (b := W) (by omega) (by omega : (i + W).toNat < 2 * W + 1) he
          constructor <;> omega
        simp [this, h]
    · have : ¬(i = 0 ∧ j = 0) := fun h => hin ⟨by omega, by omega, by omega, by omega⟩
      simp [this, bg]
  | succ t ih =>
    intro ht i j
    have IH := ih (by omega)
    set w := 2 * W + 1 with hw
    by_cases hin : -(W : ℤ) ≤ i ∧ i ≤ W ∧ -(W : ℤ) ≤ j ∧ j ≤ W
    · have hglt := grid_lt W t
      set g := grid W t with hg
      set p := (j + W).toNat * w + (i + W).toNat with hp
      have hpN : p < w * w := by
        have h1 : (j + W).toNat + 1 ≤ w := by omega
        have h2 : ((j + W).toNat + 1) * w ≤ w * w := Nat.mul_le_mul_right _ h1
        rw [hp]; rw [Nat.add_mul] at h2; omega
      have hS : S W (t + 1) i j = ((newRow (2 ^ (w * w) - 1) (bg t) (bg (t + 1)) (g >>> w) g
          ((g <<< w) &&& (2 ^ (w * w) - 1))).testBit p ^^ bg (t + 1)) := by
        unfold S; rw [if_pos hin]; rfl
      -- reading a neighbour bit
      have rd : ∀ i' j' : ℤ, -(W : ℤ) ≤ i' → i' ≤ W → -(W : ℤ) ≤ j' → j' ≤ W →
          (g.testBit ((j' + W).toNat * w + (i' + W).toNat) ^^ bg t) = cell 393 t i' j' := by
        intro i' j' h1 h2 h3 h4
        rw [IH]; unfold S; rw [if_pos ⟨h1, h2, h3, h4⟩]
      -- a bit of the window that is outside the light cone reads as zero
      have z : ∀ i' j' : ℤ, -(W : ℤ) ≤ i' → i' ≤ W → -(W : ℤ) ≤ j' → j' ≤ W → (t : ℤ) < |i'| + |j'| →
          g.testBit ((j' + W).toNat * w + (i' + W).toNat) = false := by
        intro i' j' h1 h2 h3 h4 h5
        have := rd i' j' h1 h2 h3 h4
        rw [cone t i' j' h5] at this
        revert this
        cases g.testBit ((j' + W).toNat * w + (i' + W).toNat) <;> cases bg t <;> simp
      have hz : ∀ k, w * w ≤ k → g.testBit k = false := fun k hk =>
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hglt (Nat.pow_le_pow_right (by norm_num) hk))
      rw [hS, newRow_bit _ _ _ _ _ _ _ hpN, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, cell_succ]
      congr 1
      · exact (rd i j hin.1 hin.2.1 hin.2.2.1 hin.2.2.2).symm
      · by_cases hi : i = -W
        · rw [cone t _ _ (by cases abs_cases j <;> cases abs_cases (i - 1) <;> omega)]
          by_cases hj : j = -W
          · rw [show p = 0 by rw [hp]; simp [hi, hj]]; simp
          · have e : p - 1 = (j - 1 + W).toNat * w + ((W : ℤ) + W).toNat := by
              rw [hp, show (j + W).toNat = (j - 1 + W).toNat + 1 by omega, hi]
              simp only [neg_add_cancel, Int.toNat_zero, add_zero]
              rw [show ((W : ℤ) + W).toNat = 2 * W by omega, Nat.add_mul, hw]; omega
            rw [e, z W (j - 1) (by omega) le_rfl (by omega) (by omega)
              (by cases abs_cases (j - 1) <;> rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ W)] <;> omega)]
            simp
        · rw [← rd (i - 1) j (by omega) (by omega) hin.2.2.1 hin.2.2.2]
          rw [show (i - 1 + W).toNat = (i + W).toNat - 1 by omega,
            show (j + W).toNat * w + ((i + W).toNat - 1) = p - 1 by rw [hp]; omega]
          rw [show decide (1 ≤ p) = true by simp; rw [hp]; omega]; simp
      · by_cases hi : i = W
        · rw [cone t _ _ (by cases abs_cases j <;> cases abs_cases (i + 1) <;> omega)]
          by_cases hj : j = W
          · rw [hz _ (by rw [hp, hi, hj, show ((W : ℤ) + W).toNat = 2 * W by omega, hw]; nlinarith)]
            simp
          · have e : p + 1 = (j + 1 + W).toNat * w + (-(W : ℤ) + W).toNat := by
              rw [hp, show (j + 1 + W).toNat = (j + W).toNat + 1 by omega, hi]
              simp only [neg_add_cancel, Int.toNat_zero, add_zero]
              rw [show ((W : ℤ) + W).toNat = 2 * W by omega, Nat.add_mul, hw]; omega
            rw [e, z (-W) (j + 1) le_rfl (by omega) (by omega) (by omega)
              (by cases abs_cases (j + 1) <;> rw [abs_neg, abs_of_nonneg (by omega : (0 : ℤ) ≤ W)] <;> omega)]
            simp
        · rw [← rd (i + 1) j (by omega) (by omega) hin.2.2.1 hin.2.2.2]
          rw [show (i + 1 + W).toNat = (i + W).toNat + 1 by omega]
          congr 2
      · rw [Nat.testBit_shiftRight]
        by_cases hj : j = W
        · rw [cone t _ _ (by cases abs_cases i <;> cases abs_cases (j + 1) <;> omega),
            hz _ (by rw [hp, hj, show ((W : ℤ) + W).toNat = 2 * W by omega, hw]; nlinarith)]
          simp
        · rw [← rd i (j + 1) hin.1 hin.2.1 (by omega) (by omega)]
          rw [show (j + 1 + W).toNat = (j + W).toNat + 1 by omega]
          congr 2; rw [hp, Nat.add_mul]; omega
      · simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
        by_cases hj : j = -W
        · rw [cone t _ _ (by cases abs_cases i <;> cases abs_cases (j - 1) <;> omega)]
          rw [show decide (p ≥ w) = false by
            simp only [decide_eq_false_iff_not, not_le]; rw [hp, hj]; simp; omega]
          simp
        · rw [← rd i (j - 1) hin.1 hin.2.1 (by omega) (by omega)]
          have e : p - w = (j - 1 + W).toNat * w + (i + W).toNat := by
            rw [hp, show (j + W).toNat = (j - 1 + W).toNat + 1 by omega, Nat.add_mul]; omega
          have e2 : w ≤ p := by
            rw [hp, show (j + W).toNat = (j - 1 + W).toNat + 1 by omega, Nat.add_mul]; omega
          rw [e, decide_eq_true e2, decide_eq_true hpN]
          simp
    · have hS : S W (t + 1) i j = bg (t + 1) := by unfold S; rw [if_neg hin]
      rw [hS, cone (t + 1) i j (by push_cast; cases abs_cases i <;> cases abs_cases j <;> omega)]

def AV (W n g : ℕ) (b : Bool) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if g.testBit (W * (2 * W + 1) + W + k) ^^ b then 2 ^ (n - k) else 0

lemma a_eq (W T n : ℕ) (hW : T + 1 < W) (hn : n ≤ T) :
    a n = (AV W n (grid W n) (bg n) : ℤ) := by
  unfold a AV
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hS : S W n (k : ℤ) 0 = ((grid W n).testBit (W * (2 * W + 1) + W + k) ^^ bg n) := by
    unfold S
    rw [if_pos (by omega), show ((0 : ℤ) + W).toNat = W by omega,
      show ((k : ℤ) + W).toNat = W + k by omega, Nat.add_assoc]
  rw [cell_eq W T hW n hn, hS]

lemma no_rec (W n : ℕ) (hn : 10 ≤ n) (hW : n + 1 < W)
    (hne : AV W n (grid W n) (bg n) + 4 * AV W (n - 10) (grid W (n - 10)) (bg (n - 10)) ≠
      4 * AV W (n - 2) (grid W (n - 2)) (bg (n - 2)) + AV W (n - 8) (grid W (n - 8)) (bg (n - 8))) :
    ¬ ((a n : ℚ) = 4 * a (n - 2) + a (n - 8) - 4 * a (n - 10)) := by
  intro h
  rw [a_eq W n n hW le_rfl, a_eq W n (n - 2) hW (by omega),
    a_eq W n (n - 8) hW (by omega), a_eq W n (n - 10) hW (by omega)] at h
  apply hne
  have : ((AV W n (grid W n) (bg n) + 4 * AV W (n - 10) (grid W (n - 10)) (bg (n - 10)) : ℕ) : ℚ) =
      ((4 * AV W (n - 2) (grid W (n - 2)) (bg (n - 2)) + AV W (n - 8) (grid W (n - 8)) (bg (n - 8)) : ℕ) : ℚ) := by
    push_cast; push_cast at h; linarith
  exact_mod_cast this

end OMA.Helpers_a281742

open OMA.Helpers_a281742 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a281742.main) := by
  rintro ⟨hrec, -⟩
  have hv : AV 368 366 (grid 368 366) (bg 366) +
      4 * AV 368 (366 - 10) (grid 368 (366 - 10)) (bg (366 - 10)) ≠
      4 * AV 368 (366 - 2) (grid 368 (366 - 2)) (bg (366 - 2)) +
        AV 368 (366 - 8) (grid 368 (366 - 8)) (bg (366 - 8)) := by
    decide +kernel
  exact no_rec 368 366 (by norm_num) (by norm_num) hv (hrec 366 (by norm_num))
