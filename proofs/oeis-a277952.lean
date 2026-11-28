import OMAStatements.S_oeis_a277952

open OMA.S_oeis_a277952 PowerSeries

namespace Rule14

def update (c r l u d : Bool) : Bool :=
  (14 : ℕ).testBit (c.toNat + 2 * (r.toNat + l.toNat + u.toNat + d.toNat))

lemma step (t : ℕ) (i j : ℤ) :
    cell 14 (t + 1) i j = update (cell 14 t i j) (cell 14 t (i + 1) j)
      (cell 14 t (i - 1) j) (cell 14 t i (j + 1)) (cell 14 t i (j - 1)) := rfl

lemma cell_neg_x (t : ℕ) : ∀ i j : ℤ, cell 14 t (-i) j = cell 14 t i j := by
  induction t with
  | zero => intro i j; simp [cell]
  | succ t ih =>
    intro i j
    rw [step, step]
    have h1 : -i + 1 = -(i - 1) := by omega
    have h2 : -i - 1 = -(i + 1) := by omega
    rw [h1, h2, ih i j, ih (i - 1) j, ih (i + 1) j, ih i (j + 1), ih i (j - 1)]
    unfold update
    congr 1; omega

lemma cell_neg_y (t : ℕ) : ∀ i j : ℤ, cell 14 t i (-j) = cell 14 t i j := by
  induction t with
  | zero => intro i j; simp [cell]
  | succ t ih =>
    intro i j
    rw [step, step]
    have h1 : -j + 1 = -(j - 1) := by omega
    have h2 : -j - 1 = -(j + 1) := by omega
    rw [h1, h2, ih i j, ih (i + 1) j, ih (i - 1) j, ih i (j - 1), ih i (j + 1)]
    unfold update
    congr 1; omega

lemma light_cone (t : ℕ) : ∀ i j : ℤ, t < i.natAbs + j.natAbs → cell 14 t i j = false := by
  induction t with
  | zero =>
    intro i j h
    simp only [cell, decide_eq_false_iff_not]
    rintro ⟨rfl, rfl⟩
    simp at h
  | succ t ih =>
    intro i j h
    rw [step, ih i j (by omega), ih (i + 1) j (by omega), ih (i - 1) j (by omega),
        ih i (j + 1) (by omega), ih i (j - 1) (by omega)]
    decide

def pOdd0 (m x : ℕ) : Bool := decide ((x < 2 * m ∧ x % 2 = 1) ∨ x = 2 * m ∨ x = 2 * m + 1)
def pEven0 (m x : ℕ) : Bool := decide ((x < 2 * m + 2 ∧ x % 2 = 1) ∨ x = 2 * m + 2)
def pRow1 (m x : ℕ) : Bool := decide (x ≤ 2 * m ∧ x % 2 = 0)

def InvOdd (m : ℕ) : Prop :=
  (∀ x : ℕ, cell 14 (2 * m + 1) (x : ℤ) 0 = pOdd0 m x) ∧
  (∀ x : ℕ, cell 14 (2 * m + 1) (x : ℤ) 1 = pRow1 m x)

def InvEven (m : ℕ) : Prop :=
  (∀ x : ℕ, cell 14 (2 * m + 2) (x : ℤ) 0 = pEven0 m x) ∧
  (∀ x : ℕ, cell 14 (2 * m + 2) (x : ℤ) 1 = pRow1 m x)

lemma at_add_one {t : ℕ} {y : ℤ} {f : ℕ → Bool} (h : ∀ x : ℕ, cell 14 t (x : ℤ) y = f x) (x : ℕ) :
    cell 14 t ((x : ℤ) + 1) y = f (x + 1) := by
  exact_mod_cast h (x + 1)

lemma at_sub_one_zero {t : ℕ} {y : ℤ} {f : ℕ → Bool} (h : ∀ x : ℕ, cell 14 t (x : ℤ) y = f x) :
    cell 14 t (((0 : ℕ) : ℤ) - 1) y = f 1 := by
  rw [show ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) by omega, cell_neg_x, h 1]

lemma at_sub_one_pos {t : ℕ} {y : ℤ} {f : ℕ → Bool} (h : ∀ x : ℕ, cell 14 t (x : ℤ) y = f x)
    (x : ℕ) (hx : 1 ≤ x) :
    cell 14 t ((x : ℤ) - 1) y = f (x - 1) := by
  rw [show (x : ℤ) - 1 = ((x - 1 : ℕ) : ℤ) by omega, h (x - 1)]

lemma pOdd0_T (m x : ℕ) (h : (x < 2 * m ∧ x % 2 = 1) ∨ x = 2 * m ∨ x = 2 * m + 1) : pOdd0 m x = true := decide_eq_true h
lemma pOdd0_F (m x : ℕ) (h : ¬((x < 2 * m ∧ x % 2 = 1) ∨ x = 2 * m ∨ x = 2 * m + 1)) : pOdd0 m x = false := decide_eq_false h
lemma pEven0_T (m x : ℕ) (h : (x < 2 * m + 2 ∧ x % 2 = 1) ∨ x = 2 * m + 2) : pEven0 m x = true := decide_eq_true h
lemma pEven0_F (m x : ℕ) (h : ¬((x < 2 * m + 2 ∧ x % 2 = 1) ∨ x = 2 * m + 2)) : pEven0 m x = false := decide_eq_false h
lemma pRow1_T (m x : ℕ) (h : x ≤ 2 * m ∧ x % 2 = 0) : pRow1 m x = true := decide_eq_true h
lemma pRow1_F (m x : ℕ) (h : ¬(x ≤ 2 * m ∧ x % 2 = 0)) : pRow1 m x = false := decide_eq_false h

lemma inv_odd_zero : InvOdd 0 := by
  constructor
  · intro x
    rcases (show x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with rfl | rfl | hx
    · decide
    · decide
    · rw [light_cone 1 (x : ℤ) 0 (by omega), pOdd0_F 0 x (by omega)]
  · intro x
    rcases (show x = 0 ∨ 1 ≤ x by omega) with rfl | hx
    · decide
    · rw [light_cone 1 (x : ℤ) 1 (by omega), pRow1_F 0 x (by omega)]

lemma step_odd_to_even {m : ℕ} (h : InvOdd m) : InvEven m := by
  obtain ⟨h0, h1⟩ := h
  constructor
  · intro x
    rcases (show (x = 0 ∧ 1 ≤ m) ∨ (1 ≤ x ∧ x < 2 * m ∧ x % 2 = 0) ∨ (x + 1 < 2 * m ∧ x % 2 = 1) ∨
        (1 ≤ m ∧ x = 2 * m - 1) ∨ (x = 0 ∧ m = 0) ∨ (1 ≤ m ∧ x = 2 * m) ∨
        x = 2 * m + 1 ∨ x = 2 * m + 2 ∨ 2 * m + 3 ≤ x by omega) with
      ⟨rfl, hm⟩ | hx | hx | ⟨hm, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hm, rfl⟩ | rfl | rfl | hx
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 0, at_add_one h0 0, at_sub_one_zero h0, h1 0,
          pOdd0_F m 0 (by omega), pOdd0_T m 1 (by omega), pRow1_T m 0 (by omega), pEven0_F m 0 (by omega)]
      decide
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 x, at_add_one h0 x, at_sub_one_pos h0 x (by omega), h1 x,
          pOdd0_F m x (by omega), pOdd0_T m (x + 1) (by omega), pOdd0_T m (x - 1) (by omega),
          pRow1_T m x (by omega), pEven0_F m x (by omega)]
      decide
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 x, at_add_one h0 x, at_sub_one_pos h0 x (by omega), h1 x,
          pOdd0_T m x (by omega), pOdd0_F m (x + 1) (by omega), pOdd0_F m (x - 1) (by omega),
          pRow1_F m x (by omega), pEven0_T m x (by omega)]
      decide
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 _, at_add_one h0 _, at_sub_one_pos h0 _ (by omega), h1 _,
          pOdd0_T m (2 * m - 1) (by omega), pOdd0_T m (2 * m - 1 + 1) (by omega), pOdd0_F m (2 * m - 1 - 1) (by omega),
          pRow1_F m (2 * m - 1) (by omega), pEven0_T m (2 * m - 1) (by omega)]
      decide
    · decide
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 _, at_add_one h0 _, at_sub_one_pos h0 _ (by omega), h1 _,
          pOdd0_T m (2 * m) (by omega), pOdd0_T m (2 * m + 1) (by omega), pOdd0_T m (2 * m - 1) (by omega),
          pRow1_T m (2 * m) (by omega), pEven0_F m (2 * m) (by omega)]
      decide
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 _, at_add_one h0 _, at_sub_one_pos h0 _ (by omega), h1 _,
          pOdd0_T m (2 * m + 1) (by omega), pOdd0_F m (2 * m + 1 + 1) (by omega), pOdd0_T m (2 * m + 1 - 1) (by omega),
          pRow1_F m (2 * m + 1) (by omega), pEven0_T m (2 * m + 1) (by omega)]
      decide
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 _, at_add_one h0 _, at_sub_one_pos h0 _ (by omega), h1 _,
          pOdd0_F m (2 * m + 2) (by omega), pOdd0_F m (2 * m + 2 + 1) (by omega), pOdd0_T m (2 * m + 2 - 1) (by omega),
          pRow1_F m (2 * m + 2) (by omega), pEven0_T m (2 * m + 2) (by omega)]
      decide
    · rw [light_cone (2 * m + 2) (x : ℤ) 0 (by omega), pEven0_F m x (by omega)]
  · intro x
    rcases (show (x = 0 ∧ 1 ≤ m) ∨ (1 ≤ x ∧ x < 2 * m ∧ x % 2 = 0) ∨ (x < 2 * m ∧ x % 2 = 1) ∨
        (x = 0 ∧ m = 0) ∨ (1 ≤ m ∧ x = 2 * m) ∨ x = 2 * m + 1 ∨ 2 * m + 2 ≤ x by omega) with
      ⟨rfl, hm⟩ | hx | hx | ⟨rfl, rfl⟩ | ⟨hm, rfl⟩ | rfl | hx
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (1 : ℤ) - 1 = 0 by omega,
          h1 0, at_add_one h1 0, at_sub_one_zero h1, h0 0,
          pRow1_T m 0 (by omega), pRow1_F m 1 (by omega), pOdd0_F m 0 (by omega)]
      cases cell 14 (2 * m + 1) (0 : ℤ) (1 + 1) <;> decide
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (1 : ℤ) - 1 = 0 by omega,
          h1 x, at_add_one h1 x, at_sub_one_pos h1 x (by omega), h0 x,
          pRow1_T m x (by omega), pRow1_F m (x + 1) (by omega), pRow1_F m (x - 1) (by omega),
          pOdd0_F m x (by omega)]
      cases cell 14 (2 * m + 1) (x : ℤ) (1 + 1) <;> decide
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (1 : ℤ) - 1 = 0 by omega,
          h1 x, at_add_one h1 x, at_sub_one_pos h1 x (by omega), h0 x,
          pRow1_F m x (by omega), pRow1_T m (x + 1) (by omega), pRow1_T m (x - 1) (by omega),
          pOdd0_T m x (by omega)]
      cases cell 14 (2 * m + 1) (x : ℤ) (1 + 1) <;> decide
    · decide
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (1 : ℤ) - 1 = 0 by omega,
          h1 _, at_add_one h1 _, at_sub_one_pos h1 _ (by omega), h0 _,
          light_cone (2 * m + 1) ((2 * m : ℕ) : ℤ) (1 + 1) (by omega),
          pRow1_T m (2 * m) (by omega), pRow1_F m (2 * m + 1) (by omega), pRow1_F m (2 * m - 1) (by omega),
          pOdd0_T m (2 * m) (by omega)]
      decide
    · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, step, show (1 : ℤ) - 1 = 0 by omega,
          h1 _, at_add_one h1 _, at_sub_one_pos h1 _ (by omega), h0 _,
          light_cone (2 * m + 1) ((2 * m + 1 : ℕ) : ℤ) (1 + 1) (by omega),
          pRow1_F m (2 * m + 1) (by omega), pRow1_F m (2 * m + 1 + 1) (by omega), pRow1_T m (2 * m + 1 - 1) (by omega),
          pOdd0_T m (2 * m + 1) (by omega)]
      decide
    · rw [light_cone (2 * m + 2) (x : ℤ) 1 (by omega), pRow1_F m x (by omega)]

lemma step_even_to_odd {m : ℕ} (h : InvEven m) : InvOdd (m + 1) := by
  obtain ⟨h0, h1⟩ := h
  constructor
  · intro x
    rcases (show x = 0 ∨ (1 ≤ x ∧ x ≤ 2 * m ∧ x % 2 = 0) ∨ (x < 2 * m + 1 ∧ x % 2 = 1) ∨
        x = 2 * m + 1 ∨ x = 2 * m + 2 ∨ x = 2 * m + 3 ∨ 2 * m + 4 ≤ x by omega) with
      rfl | hx | hx | rfl | rfl | rfl | hx
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 0, at_add_one h0 0, at_sub_one_zero h0, h1 0,
          pEven0_F m 0 (by omega), pEven0_T m 1 (by omega), pRow1_T m 0 (by omega), pOdd0_F (m + 1) 0 (by omega)]
      decide
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 x, at_add_one h0 x, at_sub_one_pos h0 x (by omega), h1 x,
          pEven0_F m x (by omega), pEven0_T m (x + 1) (by omega), pEven0_T m (x - 1) (by omega),
          pRow1_T m x (by omega), pOdd0_F (m + 1) x (by omega)]
      decide
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 x, at_add_one h0 x, at_sub_one_pos h0 x (by omega), h1 x,
          pEven0_T m x (by omega), pEven0_F m (x + 1) (by omega), pEven0_F m (x - 1) (by omega),
          pRow1_F m x (by omega), pOdd0_T (m + 1) x (by omega)]
      decide
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 _, at_add_one h0 _, at_sub_one_pos h0 _ (by omega), h1 _,
          pEven0_T m (2 * m + 1) (by omega), pEven0_T m (2 * m + 1 + 1) (by omega), pEven0_F m (2 * m + 1 - 1) (by omega),
          pRow1_F m (2 * m + 1) (by omega), pOdd0_T (m + 1) (2 * m + 1) (by omega)]
      decide
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 _, at_add_one h0 _, at_sub_one_pos h0 _ (by omega), h1 _,
          pEven0_T m (2 * m + 2) (by omega), pEven0_F m (2 * m + 2 + 1) (by omega), pEven0_T m (2 * m + 2 - 1) (by omega),
          pRow1_F m (2 * m + 2) (by omega), pOdd0_T (m + 1) (2 * m + 2) (by omega)]
      decide
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (0 : ℤ) - 1 = -1 by omega, cell_neg_y _ _ 1, zero_add,
          h0 _, at_add_one h0 _, at_sub_one_pos h0 _ (by omega), h1 _,
          pEven0_F m (2 * m + 3) (by omega), pEven0_F m (2 * m + 3 + 1) (by omega), pEven0_T m (2 * m + 3 - 1) (by omega),
          pRow1_F m (2 * m + 3) (by omega), pOdd0_T (m + 1) (2 * m + 3) (by omega)]
      decide
    · rw [light_cone (2 * (m + 1) + 1) (x : ℤ) 0 (by omega), pOdd0_F (m + 1) x (by omega)]
  · intro x
    rcases (show x = 0 ∨ (1 ≤ x ∧ x ≤ 2 * m ∧ x % 2 = 0) ∨ (x < 2 * m ∧ x % 2 = 1) ∨
        x = 2 * m + 1 ∨ x = 2 * m + 2 ∨ 2 * m + 3 ≤ x by omega) with
      rfl | hx | hx | rfl | rfl | hx
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (1 : ℤ) - 1 = 0 by omega,
          h1 0, at_add_one h1 0, at_sub_one_zero h1, h0 0,
          pRow1_T m 0 (by omega), pRow1_F m 1 (by omega), pEven0_F m 0 (by omega), pRow1_T (m + 1) 0 (by omega)]
      cases cell 14 (2 * m + 2) (0 : ℤ) (1 + 1) <;> decide
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (1 : ℤ) - 1 = 0 by omega,
          h1 x, at_add_one h1 x, at_sub_one_pos h1 x (by omega), h0 x,
          pRow1_T m x (by omega), pRow1_F m (x + 1) (by omega), pRow1_F m (x - 1) (by omega),
          pEven0_F m x (by omega), pRow1_T (m + 1) x (by omega)]
      cases cell 14 (2 * m + 2) (x : ℤ) (1 + 1) <;> decide
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (1 : ℤ) - 1 = 0 by omega,
          h1 x, at_add_one h1 x, at_sub_one_pos h1 x (by omega), h0 x,
          pRow1_F m x (by omega), pRow1_T m (x + 1) (by omega), pRow1_T m (x - 1) (by omega),
          pEven0_T m x (by omega), pRow1_F (m + 1) x (by omega)]
      cases cell 14 (2 * m + 2) (x : ℤ) (1 + 1) <;> decide
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (1 : ℤ) - 1 = 0 by omega,
          h1 _, at_add_one h1 _, at_sub_one_pos h1 _ (by omega), h0 _,
          light_cone (2 * m + 2) ((2 * m + 1 : ℕ) : ℤ) (1 + 1) (by omega),
          pRow1_F m (2 * m + 1) (by omega), pRow1_F m (2 * m + 1 + 1) (by omega), pRow1_T m (2 * m + 1 - 1) (by omega),
          pEven0_T m (2 * m + 1) (by omega), pRow1_F (m + 1) (2 * m + 1) (by omega)]
      decide
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega, step, show (1 : ℤ) - 1 = 0 by omega,
          h1 _, at_add_one h1 _, at_sub_one_pos h1 _ (by omega), h0 _,
          light_cone (2 * m + 2) ((2 * m + 2 : ℕ) : ℤ) (1 + 1) (by omega),
          pRow1_F m (2 * m + 2) (by omega), pRow1_F m (2 * m + 2 + 1) (by omega), pRow1_F m (2 * m + 2 - 1) (by omega),
          pEven0_T m (2 * m + 2) (by omega), pRow1_T (m + 1) (2 * m + 2) (by omega)]
      decide
    · rw [light_cone (2 * (m + 1) + 1) (x : ℤ) 1 (by omega), pRow1_F (m + 1) x (by omega)]

lemma inv_both (m : ℕ) : InvOdd m ∧ InvEven m := by
  induction m with
  | zero => exact ⟨inv_odd_zero, step_odd_to_even inv_odd_zero⟩
  | succ m ih =>
    have ho := step_even_to_odd ih.2
    exact ⟨ho, step_odd_to_even ho⟩

lemma a_eq_sum_pos (n : ℕ) :
    a n = ∑ x ∈ Finset.range (n + 1), if cell 14 n (x : ℤ) 0 then (10 : ℤ) ^ x else 0 := by
  unfold a
  rw [← Finset.sum_range_reflect (fun k => if cell 14 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0) (n + 1)]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x < n + 1 := Finset.mem_range.mp hx
  have hneg : (((n - x : ℕ) : ℤ) - n) = -(x : ℤ) := by omega
  have hsub : n - (n - x) = x := by omega
  rw [hneg, cell_neg_x, hsub]

lemma a_step_even (m : ℕ) :
    a (2 * m + 2) = a (2 * m + 1) - (10 : ℤ) ^ (2 * m) + (10 : ℤ) ^ (2 * m + 2) := by
  rw [a_eq_sum_pos (2 * m + 2), a_eq_sum_pos (2 * m + 1)]
  conv_lhs =>
    rw [Finset.sum_range_succ, show 2 * m + 2 = (2 * m + 1) + 1 by rfl, Finset.sum_range_succ, Finset.sum_range_succ]
  conv_rhs =>
    arg 1; arg 1
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have he := (inv_both m).2.1
  have ho := (inv_both m).1.1
  have htop : cell 14 (2 * m + 2) ((2 * m + 2 : ℕ) : ℤ) 0 = true := by
    rw [he, pEven0_T m (2 * m + 2) (by omega)]
  have hm1_e : cell 14 (2 * m + 2) ((2 * m + 1 : ℕ) : ℤ) 0 = true := by
    rw [he, pEven0_T m (2 * m + 1) (by omega)]
  have hm1_o : cell 14 (2 * m + 1) ((2 * m + 1 : ℕ) : ℤ) 0 = true := by
    rw [ho, pOdd0_T m (2 * m + 1) (by omega)]
  have hm0_e : cell 14 (2 * m + 2) ((2 * m : ℕ) : ℤ) 0 = false := by
    rw [he, pEven0_F m (2 * m) (by omega)]
  have hm0_o : cell 14 (2 * m + 1) ((2 * m : ℕ) : ℤ) 0 = true := by
    rw [ho, pOdd0_T m (2 * m) (by omega)]
  have hsum : (∑ x ∈ Finset.range (2 * m), if cell 14 (2 * m + 2) (x : ℤ) 0 then (10 : ℤ) ^ x else 0) =
      (∑ x ∈ Finset.range (2 * m), if cell 14 (2 * m + 1) (x : ℤ) 0 then (10 : ℤ) ^ x else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x < 2 * m := Finset.mem_range.mp hx
    have hpe : pEven0 m x = pOdd0 m x := by
      unfold pEven0 pOdd0; rw [decide_eq_decide]; omega
    rw [he x, ho x, hpe]
  change ((∑ x ∈ Finset.range (2 * m), if cell 14 (2 * m + 2) (x : ℤ) 0 then (10 : ℤ) ^ x else 0) +
      (if cell 14 (2 * m + 2) ((2 * m : ℕ) : ℤ) 0 then (10 : ℤ) ^ (2 * m) else 0) +
      (if cell 14 (2 * m + 2) ((2 * m + 1 : ℕ) : ℤ) 0 then (10 : ℤ) ^ (2 * m + 1) else 0) +
      (if cell 14 (2 * m + 2) ((2 * m + 2 : ℕ) : ℤ) 0 then (10 : ℤ) ^ (2 * m + 2) else 0)) = _
  rw [htop, hm1_e, hm1_o, hm0_e, hm0_o, hsum]
  simp only [↓reduceIte, Bool.false_eq_true]
  ring

lemma a_step_odd (m : ℕ) :
    a (2 * (m + 1) + 1) = a (2 * m + 2) + (10 : ℤ) ^ (2 * (m + 1) + 1) := by
  rw [a_eq_sum_pos (2 * (m + 1) + 1), a_eq_sum_pos (2 * m + 2)]
  have heq : 2 * (m + 1) + 1 = 2 * m + 2 + 1 := by omega
  conv_lhs => rw [show 2 * (m + 1) + 1 + 1 = (2 * m + 2 + 1) + 1 by omega, Finset.sum_range_succ]
  have he := (inv_both m).2.1
  have ho := (inv_both (m + 1)).1.1
  have htop : cell 14 (2 * (m + 1) + 1) ((2 * m + 2 + 1 : ℕ) : ℤ) 0 = true := by
    rw [ho, pOdd0_T (m + 1) (2 * m + 2 + 1) (by omega)]
  have hsum : (∑ x ∈ Finset.range (2 * m + 2 + 1), if cell 14 (2 * (m + 1) + 1) (x : ℤ) 0 then (10 : ℤ) ^ x else 0) =
      (∑ x ∈ Finset.range (2 * m + 2 + 1), if cell 14 (2 * m + 2) (x : ℤ) 0 then (10 : ℤ) ^ x else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x < 2 * m + 2 + 1 := Finset.mem_range.mp hx
    have hpe : pOdd0 (m + 1) x = pEven0 m x := by
      unfold pOdd0 pEven0; rw [decide_eq_decide]; omega
    rw [ho x, he x, hpe]
  rw [htop, hsum, ← heq]
  simp only [↓reduceIte]

lemma neg_ten_even (k : ℕ) : (-10 : ℚ) ^ (2 * k) = (10 : ℚ) ^ (2 * k) := by
  rw [pow_mul, pow_mul]; norm_num

lemma neg_ten_odd (k : ℕ) : (-10 : ℚ) ^ (2 * k + 1) = -10 * (10 : ℚ) ^ (2 * k) := by
  rw [pow_succ, neg_ten_even]; ring

lemma closed_pair (m : ℕ) :
    ((a (2 * m + 1) : ℚ) = (-200 - 9 * (-10 : ℚ) ^ (2 * m + 1) + 2189 * (10 : ℚ) ^ (2 * m + 1)) / 1980) ∧
    ((a (2 * m + 2) : ℚ) = (-200 - 9 * (-10 : ℚ) ^ (2 * m + 2) + 2189 * (10 : ℚ) ^ (2 * m + 2)) / 1980) := by
  induction m with
  | zero =>
    have ha1 : a 1 = 11 := by decide
    have ha2 : a 2 = 110 := by decide
    simp only [Nat.mul_zero, zero_add, ha1, ha2]
    norm_num
  | succ m ih =>
    have h1 : (a (2 * (m + 1) + 1) : ℚ) = (-200 - 9 * (-10 : ℚ) ^ (2 * (m + 1) + 1) + 2189 * (10 : ℚ) ^ (2 * (m + 1) + 1)) / 1980 := by
      have hs := a_step_odd m
      have hcast : (a (2 * (m + 1) + 1) : ℚ) = (a (2 * m + 2) : ℚ) + (10 : ℚ) ^ (2 * (m + 1) + 1) := by exact_mod_cast hs
      rw [hcast, ih.2, show 2 * m + 2 = 2 * (m + 1) by omega, neg_ten_even (m + 1), neg_ten_odd (m + 1)]
      ring
    refine ⟨h1, ?_⟩
    have hs2 := a_step_even (m + 1)
    have hcast2 : (a (2 * (m + 1) + 2) : ℚ) = (a (2 * (m + 1) + 1) : ℚ) - (10 : ℚ) ^ (2 * (m + 1)) + (10 : ℚ) ^ (2 * (m + 1) + 2) := by exact_mod_cast hs2
    rw [hcast2, h1, show 2 * (m + 1) + 2 = 2 * (m + 2) by omega,
        neg_ten_odd (m + 1), neg_ten_even (m + 2)]
    ring

lemma closed_form (n : ℕ) :
    (a n : ℚ) = (-200 - 9 * (-10 : ℚ) ^ n + 2189 * (10 : ℚ) ^ n) / 1980 := by
  rcases n with _ | n
  · have ha0 : a 0 = 1 := by decide
    simp [ha0]; norm_num
  · rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · exact (closed_pair m).1
    · rw [show 2 * m + 1 + 1 = 2 * m + 2 by omega]
      exact (closed_pair m).2

lemma recurrence (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℚ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
             show k + 3 - 3 = k by omega, closed_form]
  ring

end Rule14

open Rule14

theorem OMA.solution : type_of% @OMA.S_oeis_a277952.main := by
  refine ⟨?_, recurrence, closed_form⟩
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  have hd : s * ((1 - X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      C (1 : ℚ) * (s * X ^ 0)
      + C (-1 : ℚ) * (s * X ^ 1)
      + C (-100 : ℚ) * (s * X ^ 2)
      + C (100 : ℚ) * (s * X ^ 3) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  have hp : (1 + 10 * X - X ^ 2 : PowerSeries ℚ) =
      C (1 : ℚ) * (X ^ 0 : PowerSeries ℚ)
      + C (10 : ℚ) * (X ^ 1 : PowerSeries ℚ)
      + C (-1 : ℚ) * (X ^ 2 : PowerSeries ℚ) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hd, hp]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
  by_cases hn : n < 3
  · interval_cases n <;> norm_num [closed_form]
  · have hr := recurrence n (by omega)
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
          show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
    linarith
