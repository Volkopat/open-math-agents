import OMAStatements.S_oeis_a282954
import Mathlib

namespace OMA.Helpers_a282954
open OMA.S_oeis_a282954

def R (c r l u d : Bool) : Bool := Nat.testBit 533 (c.toNat + 2 * (r.toNat + l.toNat + u.toNat + d.toNat))

theorem cell_succ (t : ℕ) (i j : ℤ) : cell 533 (t + 1) i j = R (cell 533 t i j) (cell 533 t (i + 1) j)
    (cell 533 t (i - 1) j) (cell 533 t i (j + 1)) (cell 533 t i (j - 1)) := rfl

def bg (t : ℕ) : Bool := decide (0 < t)

theorem cone : ∀ t : ℕ, ∀ x y : ℤ, (t : ℤ) < |x| + |y| → cell 533 t x y = bg t := by
  intro t
  induction t with
  | zero =>
    intro x y h
    show decide (x = 0 ∧ y = 0) = decide (0 < 0)
    simp only [lt_irrefl, decide_false, decide_eq_false_iff_not, not_and]
    intro hx hy; subst hx hy; simp at h
  | succ t ih =>
    intro x y h
    push_cast at h
    rw [cell_succ, ih x y (by omega),
      ih (x + 1) y (by cases abs_cases x <;> cases abs_cases (x + 1) <;> cases abs_cases y <;> omega),
      ih (x - 1) y (by cases abs_cases x <;> cases abs_cases (x - 1) <;> cases abs_cases y <;> omega),
      ih x (y + 1) (by cases abs_cases x <;> cases abs_cases (y + 1) <;> cases abs_cases y <;> omega),
      ih x (y - 1) (by cases abs_cases x <;> cases abs_cases (y - 1) <;> cases abs_cases y <;> omega)]
    have : bg (t + 1) = true := by simp [bg]
    rw [this]
    cases bg t <;> decide

theorem symm : ∀ t : ℕ, ∀ x y : ℤ, cell 533 t (-x) y = cell 533 t x y := by
  intro t
  induction t with
  | zero => intro x y; show decide (-x = 0 ∧ y = 0) = decide (x = 0 ∧ y = 0); simp
  | succ t ih =>
    intro x y
    rw [cell_succ, cell_succ, ih, show -x + 1 = -(x - 1) by ring, ih, show -x - 1 = -(x + 1) by ring, ih, ih, ih]
    unfold R; congr 2; omega

theorem swap : ∀ t : ℕ, ∀ x y : ℤ, cell 533 t x y = cell 533 t y x := by
  intro t
  induction t with
  | zero => intro x y; show decide (x = 0 ∧ y = 0) = decide (y = 0 ∧ x = 0); simp [and_comm]
  | succ t ih =>
    intro x y
    rw [cell_succ, cell_succ, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y + 1), ih x (y - 1)]
    unfold R; congr 2; omega

theorem negy (t : ℕ) (x y : ℤ) : cell 533 t x (-y) = cell 533 t x y := by
  rw [swap, symm, swap]

/-- window coordinates: `u = x + t`. -/
def nb (t : ℕ) (u y : ℤ) : Bool := cell 533 t (u - t) y

theorem nb_succ (t : ℕ) (u y : ℤ) : nb (t + 1) u y = R (nb t (u - 1) y) (nb t u y) (nb t (u - 2) y)
    (nb t (u - 1) (y + 1)) (nb t (u - 1) (y - 1)) := by
  unfold nb
  rw [cell_succ]
  have e0 : u - ((t + 1 : ℕ) : ℤ) = (u - 1) - t := by push_cast; ring
  have e1 : u - ((t + 1 : ℕ) : ℤ) + 1 = u - t := by push_cast; ring
  have e2 : u - ((t + 1 : ℕ) : ℤ) - 1 = (u - 2) - t := by push_cast; ring
  rw [e1, e2, e0]

theorem nb_neg (t : ℕ) (u y : ℤ) (h : u < 0) : nb t u y = bg t := by
  unfold nb; apply cone; cases abs_cases (u - t) <;> cases abs_cases y <;> omega

def newRow (D : ℕ) (b : Bool) (rc ra rb : ℕ) : ℕ :=
  let M := 2 ^ (D + 1) - 1
  let f1 := if b then 1 else 0
  let f2 := if b then 3 else 0
  let c := ((rc <<< 1) ||| f1) &&& M
  let r := rc &&& M
  let l := ((rc <<< 2) ||| f2) &&& M
  let u := ((ra <<< 1) ||| f1) &&& M
  let d := ((rb <<< 1) ||| f1) &&& M
  let al := r &&& l &&& u &&& d
  let a3 := (r &&& l &&& (u ||| d)) ||| (u &&& d &&& (r ||| l))
  (c &&& al) ||| ((M ^^^ c) &&& (M ^^^ a3))

theorem R_formula (c r l u d : Bool) :
    ((c && (r && l && u && d)) || ((true ^^ c) && (true ^^ ((r && l && (u || d)) || (u && d && (r || l)))))) =
      R c r l u d := by
  cases c <;> cases r <;> cases l <;> cases u <;> cases d <;> decide

theorem newRow_bit (D : ℕ) (b : Bool) (rc ra rb k : ℕ) (hk : k ≤ D) :
    (newRow D b rc ra rb).testBit k = R (if 1 ≤ k then rc.testBit (k - 1) else b) (rc.testBit k)
      (if 2 ≤ k then rc.testBit (k - 2) else b) (if 1 ≤ k then ra.testBit (k - 1) else b)
      (if 1 ≤ k then rb.testBit (k - 1) else b) := by
  have hM : (2 ^ (D + 1) - 1 : ℕ).testBit k = true := by
    rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true (by omega)
  have h1 : (if b then 1 else 0 : ℕ).testBit k = (decide (k = 0) && b) := by
    cases b
    · simp
    · rw [if_pos rfl, show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]; simp [eq_comm]
  have h3 : (if b then 3 else 0 : ℕ).testBit k = (decide (k < 2) && b) := by
    cases b
    · simp
    · rw [if_pos rfl, show (3 : ℕ) = 2 ^ 2 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp
  simp only [newRow, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, hM, h1, h3,
    Bool.and_true]
  rw [← R_formula]
  rcases k with _ | _ | k <;> simp

def step (D : ℕ) (b : Bool) (w : List ℕ) : List ℕ :=
  (List.range (2 * D + 1)).map fun yi =>
    newRow D b (w.getD yi 0) (w.getD (yi + 1) 0) (if yi = 0 then 0 else w.getD (yi - 1) 0)

def Wst (D : ℕ) : ℕ → List ℕ
  | 0 => (List.range (2 * D + 1)).map fun yi => if yi = D then 1 else 0
  | t + 1 => step D (bg t) (Wst D t)

def SV (D t : ℕ) (u y : ℤ) : Bool := ((Wst D t).getD (y + D).toNat 0).testBit u.toNat

theorem getD_mapRange {α : Type} (n i : ℕ) (f : ℕ → α) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp

theorem correct (D : ℕ) : ∀ t : ℕ, ∀ u y : ℤ, 0 ≤ u → |y| ≤ D - u → nb t u y = SV D t u y := by
  intro t
  induction t with
  | zero =>
    intro u y hu hy
    unfold SV
    rw [show Wst D 0 = (List.range (2 * D + 1)).map fun yi => if yi = D then 1 else 0 from rfl,
      getD_mapRange _ (y + D).toNat _ _ (by cases abs_cases y <;> omega)]
    show decide (u - ((0 : ℕ) : ℤ) = 0 ∧ y = 0) = _
    by_cases h : y = 0
    · subst h
      rw [if_pos (by omega), show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
      simp only [Nat.cast_zero, sub_zero, and_true, decide_eq_decide]
      omega
    · rw [if_neg (show ¬ (y + (D : ℤ)).toNat = D by cases abs_cases y <;> omega)]; simp [h]
  | succ t ih =>
    intro u y hu hy
    have hy' : -(D : ℤ) ≤ y ∧ y ≤ D := by cases abs_cases y <;> constructor <;> omega
    have key : ∀ u' y' : ℤ, (u' < 0 ∨ (0 ≤ u' ∧ |y'| ≤ D - u')) →
        nb t u' y' = (if 0 ≤ u' then SV D t u' y' else bg t) := by
      intro u' y' h
      rcases h with h | ⟨h1, h2⟩
      · rw [nb_neg t u' y' h, if_neg (by omega)]
      · rw [ih u' y' h1 h2, if_pos h1]
    rw [nb_succ]
    unfold SV
    rw [show Wst D (t + 1) = step D (bg t) (Wst D t) from rfl]
    unfold step
    rw [getD_mapRange _ (y + D).toNat _ _ (by omega), newRow_bit _ _ _ _ _ u.toNat (by cases abs_cases y <;> omega)]
    rw [key (u - 1) y (by cases abs_cases y <;> omega), key u y (Or.inr ⟨hu, hy⟩),
      key (u - 2) y (by cases abs_cases y <;> omega),
      key (u - 1) (y + 1) (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega),
      key (u - 1) (y - 1) (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)]
    unfold SV
    have e1 : (y + D).toNat + 1 = (y + 1 + D).toNat := by omega
    have hn : ((u - 1).toNat) = u.toNat - 1 := by omega
    have hn2 : ((u - 2).toNat) = u.toNat - 2 := by omega
    rw [e1, hn, hn2, if_pos hu]
    by_cases h0 : u = 0
    · subst h0; simp
    · have e2 : (if (y + D).toNat = 0 then 0 else (Wst D t).getD ((y + D).toNat - 1) 0) =
          (Wst D t).getD (y - 1 + D).toNat 0 := by
        rw [if_neg (by cases abs_cases y <;> omega)]; congr 1; omega
      rw [e2]
      simp only [show 1 ≤ u.toNat by omega, show 0 ≤ u - 1 by omega, if_true]
      by_cases h2 : u = 1
      · subst h2; simp
      · simp only [show 2 ≤ u.toNat by omega, show 0 ≤ u - 2 by omega, if_true]

def mk (yi : ℕ) : ℕ := 2 ^ (21 - (if yi ≤ 20 then 20 - yi else yi - 20)) - 1

def msk (w : List ℕ) : List ℕ := (List.range 41).map fun yi => w.getD yi 0 &&& mk yi

theorem perOK_t : msk (Wst 20 29) = msk (Wst 20 25) := by decide +kernel

theorem SV_per (u y : ℤ) (hu : 0 ≤ u) (hy : |y| ≤ 20 - u) : SV 20 29 u y = SV 20 25 u y := by
  have hy' : (y + 20).toNat < 41 := by cases abs_cases y <;> omega
  have h := congrArg (fun w => (w.getD (y + 20).toNat 0).testBit u.toNat) perOK_t
  simp only [msk] at h
  rw [getD_mapRange _ _ _ _ hy', getD_mapRange _ _ _ _ hy', Nat.testBit_and, Nat.testBit_and] at h
  have hm : (mk (y + 20).toNat).testBit u.toNat = true := by
    unfold mk; rw [Nat.testBit_two_pow_sub_one]; apply decide_eq_true
    split_ifs <;> cases abs_cases y <;> omega
  rw [hm, Bool.and_true, Bool.and_true] at h
  exact h

theorem per : ∀ t : ℕ, 25 ≤ t → ∀ u y : ℤ, 0 ≤ u → |y| ≤ 20 - u → nb (t + 4) u y = nb t u y := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro u y hu hy; rw [correct 20 29 u y hu hy, correct 20 25 u y hu hy]; exact SV_per u y hu hy
  | succ t ht ih =>
    intro u y hu hy
    have key : ∀ u' y' : ℤ, (u' < 0 ∨ (0 ≤ u' ∧ |y'| ≤ 20 - u')) → nb (t + 4) u' y' = nb t u' y' := by
      intro u' y' h
      rcases h with h | ⟨h1, h2⟩
      · rw [nb_neg _ _ _ h, nb_neg _ _ _ h]; simp [bg]; omega
      · exact ih u' y' h1 h2
    rw [show t + 1 + 4 = (t + 4) + 1 by omega, nb_succ (t + 4), nb_succ t,
      key (u - 1) y (by cases abs_cases y <;> omega), key u y (Or.inr ⟨hu, hy⟩),
      key (u - 2) y (by cases abs_cases y <;> omega),
      key (u - 1) (y + 1) (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega),
      key (u - 1) (y - 1) (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)]

theorem per_red (t : ℕ) (ht : 25 ≤ t) (u y : ℤ) (hu : 0 ≤ u) (hy : |y| ≤ 20 - u) :
    nb t u y = nb (25 + (t - 25) % 4) u y := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases h : t < 29
    · congr 1; omega
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 4 := ⟨t - 4, by omega⟩
      rw [per s (by omega) u y hu hy, ih s (by omega) (by omega)]
      congr 2; omega

def MtL : List (List ℕ) := [[14, 10, 14, 14], [17, 17, 17, 21], [14, 14, 14, 10], [17, 21, 17, 17]]

def RtL : List (List ℕ) := [[0, 10, 0, 31, 31, 0], [31, 21, 31, 0, 0, 31], [4, 0, 0, 31, 31, 0], [27, 31, 31, 0, 0, 31]]

/-- the predicted state of the strip `|y| ≤ 2` at a time `≡ r (mod 4)`, away from the left edge -/
def predR (r : ℕ) (x y : ℤ) : Bool :=
  if -5 ≤ x then ((RtL.getD r []).getD (-x).toNat 0).testBit (y + 2).toNat
  else ((MtL.getD r []).getD (x % 4).toNat 0).testBit (y + 2).toNat

theorem predR_mid (r : ℕ) (x x' : ℤ) (hx : x ≤ -6) (hx' : x' ≤ -6) (h : x % 4 = x' % 4) (y : ℤ) :
    predR r x y = predR r x' y := by
  unfold predR; rw [if_neg (by omega), if_neg (by omega), h]

def Phi (t : ℕ) : Prop :=
  ∀ x y : ℤ, 17 ≤ (t : ℤ) + x → x ≤ 0 → |y| ≤ 2 → cell 533 t x y = predR (t % 4) x y

def baseOK : Bool := (List.range 12).all fun i => (List.range 5).all fun j =>
  SV 36 28 ((i : ℤ) + 17) ((j : ℤ) - 2) == predR 0 ((i : ℤ) - 11) ((j : ℤ) - 2)

theorem baseOK_t : baseOK = true := by decide +kernel

theorem phi_base : Phi 28 := by
  intro x y h1 h2 hy
  have h := baseOK_t
  unfold baseOK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h (x + 11).toNat (by omega) (y + 2).toNat (by cases abs_cases y <;> omega)
  rw [show (((x + 11).toNat : ℕ) : ℤ) + 17 = x + 28 by omega, show (((x + 11).toNat : ℕ) : ℤ) - 11 = x by omega,
    show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by cases abs_cases y <;> omega] at this
  rw [← this, ← correct 36 28 (x + 28) y (by omega) (by cases abs_cases y <;> omega)]
  unfold nb; congr 1; push_cast; ring

def triOK : Bool := (List.range 4).all fun i => (List.range 2).all fun v => (List.range 5).all fun j =>
  SV 20 (25 + i) ((v : ℤ) + 17) ((j : ℤ) - 2) == predR ((25 + i) % 4) ((v : ℤ) + 17 - ((25 + i : ℕ) : ℤ)) ((j : ℤ) - 2)

theorem triOK_t : triOK = true := by decide +kernel

theorem tri_part (s : ℕ) (hs : 29 ≤ s) (u y : ℤ) (hu1 : 17 ≤ u) (hu2 : u ≤ 18) (hy : |y| ≤ 2) :
    cell 533 s (u - s) y = predR (s % 4) (u - s) y := by
  have h := triOK_t
  unfold triOK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h ((s - 25) % 4) (Nat.mod_lt _ (by norm_num)) (u - 17).toNat (by omega) (y + 2).toNat
    (by cases abs_cases y <;> omega)
  rw [show (((u - 17).toNat : ℕ) : ℤ) + 17 = u by omega,
    show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by cases abs_cases y <;> omega,
    show (25 + (s - 25) % 4) % 4 = s % 4 by omega] at this
  rw [show cell 533 s (u - s) y = nb s u y from rfl, per_red s (by omega) u y (by omega)
    (by cases abs_cases y <;> omega), correct 20 _ u y (by omega) (by cases abs_cases y <;> omega), this]
  apply predR_mid
  · push_cast; omega
  · omega
  · push_cast; omega

def stepF (r : ℕ) (x y : ℤ) (b : Bool) : Bool :=
  R (predR r x y) (if x = 0 then predR r (-1) y else predR r (x + 1) y) (predR r (x - 1) y)
    (if y + 1 ≤ 2 then predR r x (y + 1) else if -2 ≤ x then predR r (-3) x else b)
    (if -2 ≤ y - 1 then predR r x (y - 1) else if -2 ≤ x then predR r (-3) x else b) == predR ((r + 1) % 4) x y

def stepOK : Bool := (List.range 4).all fun r => (List.range 11).all fun i => (List.range 5).all fun j =>
  stepF r ((i : ℤ) - 10) ((j : ℤ) - 2) false && stepF r ((i : ℤ) - 10) ((j : ℤ) - 2) true

theorem stepOK_t : stepOK = true := by decide +kernel

theorem stepNear (r : ℕ) (hr : r < 4) (x y : ℤ) (h1 : -10 ≤ x) (h2 : x ≤ 0) (hy : |y| ≤ 2) (b : Bool) :
    stepF r x y b = true := by
  have h := stepOK_t
  unfold stepOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  have := h r hr (x + 10).toNat (by omega) (y + 2).toNat (by cases abs_cases y <;> omega)
  rw [show (((x + 10).toNat : ℕ) : ℤ) - 10 = x by omega,
    show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by cases abs_cases y <;> omega] at this
  cases b
  · exact this.1
  · exact this.2

theorem stepAll (r : ℕ) (hr : r < 4) (x y : ℤ) (h2 : x ≤ 0) (hy : |y| ≤ 2) (b : Bool) :
    stepF r x y b = true := by
  by_cases h1 : -10 ≤ x
  · exact stepNear r hr x y h1 h2 hy b
  · have e : stepF r x y b = stepF r (-10 + (x + 10) % 4) y b := by
      unfold stepF
      simp only [show ¬ x = 0 by omega, show ¬ (-10 + (x + 10) % 4 = 0) by omega, show ¬ (-2 ≤ x) by omega,
        show ¬ (-2 ≤ -10 + (x + 10) % 4) by omega, if_false,
        predR_mid r x (-10 + (x + 10) % 4) (by omega) (by omega) (by omega),
        predR_mid r (x + 1) (-10 + (x + 10) % 4 + 1) (by omega) (by omega) (by omega),
        predR_mid r (x - 1) (-10 + (x + 10) % 4 - 1) (by omega) (by omega) (by omega),
        predR_mid ((r + 1) % 4) x (-10 + (x + 10) % 4) (by omega) (by omega) (by omega)]
    rw [e]
    exact stepNear r hr _ y (by omega) (by omega) hy b

theorem phi_step (t : ℕ) (ht : 28 ≤ t) (H : Phi t) : Phi (t + 1) := by
  intro x y h1 h2 hy
  push_cast at h1
  by_cases hu : (t : ℤ) + 1 + x ≤ 18
  · have := tri_part (t + 1) (by omega) ((t : ℤ) + 1 + x) y (by omega) hu hy
    rw [show (t : ℤ) + 1 + x - ((t + 1 : ℕ) : ℤ) = x by push_cast; ring] at this
    exact this
  · have e0 : cell 533 t x y = predR (t % 4) x y := H x y (by omega) h2 hy
    have er : cell 533 t (x + 1) y = if x = 0 then predR (t % 4) (-1) y else predR (t % 4) (x + 1) y := by
      split_ifs with hx
      · subst hx; rw [show (0 : ℤ) + 1 = -(-1) by norm_num, symm]; exact H (-1) y (by omega) (by norm_num) hy
      · exact H (x + 1) y (by omega) (by omega) hy
    have el : cell 533 t (x - 1) y = predR (t % 4) (x - 1) y := H (x - 1) y (by omega) (by omega) hy
    have h3 : cell 533 t x 3 = cell 533 t x 3 := rfl
    have e3 : -2 ≤ x → cell 533 t x 3 = predR (t % 4) (-3) x := by
      intro hx
      rw [swap, show (3 : ℤ) = -(-3) by norm_num, symm]
      exact H (-3) x (by omega) (by norm_num) (by cases abs_cases x <;> omega)
    have eu : cell 533 t x (y + 1) = if y + 1 ≤ 2 then predR (t % 4) x (y + 1)
        else if -2 ≤ x then predR (t % 4) (-3) x else cell 533 t x 3 := by
      split_ifs with ha hb
      · exact H x (y + 1) (by omega) h2 (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega)
      · rw [show y + 1 = 3 by cases abs_cases y <;> omega]; exact e3 hb
      · rw [show y + 1 = 3 by cases abs_cases y <;> omega]
    have ed : cell 533 t x (y - 1) = if -2 ≤ y - 1 then predR (t % 4) x (y - 1)
        else if -2 ≤ x then predR (t % 4) (-3) x else cell 533 t x 3 := by
      split_ifs with ha hb
      · exact H x (y - 1) (by omega) h2 (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)
      · rw [show y - 1 = -3 by cases abs_cases y <;> omega, negy]; exact e3 hb
      · rw [show y - 1 = -3 by cases abs_cases y <;> omega, negy]
    have hs := stepAll (t % 4) (Nat.mod_lt _ (by norm_num)) x y h2 hy (cell 533 t x 3)
    unfold stepF at hs
    rw [beq_iff_eq] at hs
    rw [cell_succ, e0, er, el, eu, ed, hs]
    congr 1; omega

theorem phi_all : ∀ t : ℕ, 28 ≤ t → Phi t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact phi_base
  | succ t ht ih => exact phi_step t ht ih

theorem dig (n k : ℕ) (hn : 28 ≤ n) (hk : k ≤ n) :
    cell 533 n ((k : ℤ) - n) 0 = if k ≤ 18 then SV 20 (25 + (n - 25) % 4) k 0 else predR (n % 4) ((k : ℤ) - n) 0 := by
  split_ifs with h
  · rw [show cell 533 n ((k : ℤ) - n) 0 = nb n k 0 from rfl, per_red n (by omega) k 0 (by omega) (by simp; omega),
      correct 20 _ k 0 (by omega) (by simp; omega)]
  · exact phi_all n hn _ 0 (by omega) (by omega) (by norm_num)

theorem cell_shift (n k : ℕ) (hn : 28 ≤ n) (hk : k + 6 ≤ n) :
    cell 533 (n + 4) ((k : ℤ) - ((n + 4 : ℕ) : ℤ)) 0 = cell 533 n ((k : ℤ) - n) 0 := by
  rw [dig (n + 4) k (by omega) (by omega), dig n k hn (by omega), show (n + 4 - 25) % 4 = (n - 25) % 4 by omega,
    show (n + 4) % 4 = n % 4 by omega]
  split_ifs
  · rfl
  · apply predR_mid <;> push_cast <;> omega

def G1 (r : ℕ) : ℤ := ∑ i ∈ Finset.range 10, if predR r ((i : ℤ) - 9) 0 then (10 : ℤ) ^ (9 - i) else 0

def G2 (r : ℕ) : ℤ := ∑ i ∈ Finset.range 6, if predR r ((i : ℤ) - 5) 0 then (10 : ℤ) ^ (5 - i) else 0

theorem shift4 (n : ℕ) (hn : 28 ≤ n) : a (n + 4) = 10 ^ 4 * a n + (G1 (n % 4) - 10 ^ 4 * G2 (n % 4)) := by
  unfold a
  rw [show n + 4 + 1 = (n - 5) + 10 by omega, Finset.sum_range_add, show n + 1 = (n - 5) + 6 by omega,
    Finset.sum_range_add]
  have hh : ∑ k ∈ Finset.range (n - 5), (if cell 533 (n + 4) ((k : ℤ) - ((n + 4 : ℕ) : ℤ)) 0 then (10 : ℤ) ^ (n + 4 - k) else 0) =
      10 ^ 4 * ∑ k ∈ Finset.range (n - 5), (if cell 533 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [cell_shift n k hn (by omega), show n + 4 - k = 4 + (n - k) by omega, pow_add]
    split_ifs <;> simp
  have h1 : ∑ i ∈ Finset.range 10, (if cell 533 (n + 4) (((n - 5 + i : ℕ) : ℤ) - ((n + 4 : ℕ) : ℤ)) 0 then (10 : ℤ) ^ (n + 4 - (n - 5 + i)) else 0) =
      G1 (n % 4) := by
    unfold G1
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [dig (n + 4) (n - 5 + i) (by omega) (by omega), if_neg (show ¬ (n - 5 + i ≤ 18) by omega), show (n + 4) % 4 = n % 4 by omega,
      show ((n - 5 + i : ℕ) : ℤ) - ((n + 4 : ℕ) : ℤ) = (i : ℤ) - 9 by push_cast; omega,
      show n + 4 - (n - 5 + i) = 9 - i by omega]
  have h2 : ∑ i ∈ Finset.range 6, (if cell 533 n (((n - 5 + i : ℕ) : ℤ) - (n : ℤ)) 0 then (10 : ℤ) ^ (n - (n - 5 + i)) else 0) =
      G2 (n % 4) := by
    unfold G2
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [dig n (n - 5 + i) hn (by omega), if_neg (show ¬ (n - 5 + i ≤ 18) by omega),
      show ((n - 5 + i : ℕ) : ℤ) - (n : ℤ) = (i : ℤ) - 5 by push_cast; omega,
      show n - (n - 5 + i) = 5 - i by omega]
  rw [hh, h1, h2]; ring

theorem rec_big (n : ℕ) (hn : 36 ≤ n) : a n = 10001 * a (n - 4) - 10000 * a (n - 8) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 36 := ⟨n - 36, by omega⟩
  have e1 := shift4 (p + 32) (by omega)
  have e2 := shift4 (p + 28) (by omega)
  rw [show p + 32 + 4 = p + 36 by omega, show (p + 32) % 4 = p % 4 by omega] at e1
  rw [show p + 28 + 4 = p + 32 by omega, show (p + 28) % 4 = p % 4 by omega] at e2
  rw [show p + 36 - 4 = p + 32 by omega, show p + 36 - 8 = p + 28 by omega]
  linear_combination e1 - e2

def awZ (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), if ((Wst 36 n).getD 36 0).testBit k then (10 : ℤ) ^ (n - k) else 0

theorem a_aw (n : ℕ) (hn : n ≤ 36) : a n = awZ n := by
  unfold a awZ
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [show cell 533 n ((k : ℤ) - n) 0 = nb n k 0 from rfl, correct 36 n k 0 (by omega) (by simp; omega)]
  unfold SV
  rw [show ((0 : ℤ) + ((36 : ℕ) : ℤ)).toNat = 36 from rfl, show ((k : ℤ)).toNat = k by omega]

def smallOK : Bool := (List.range 11).all fun i => awZ (i + 25) == 10001 * awZ (i + 21) - 10000 * awZ (i + 17)

theorem smallOK_t : smallOK = true := by decide +kernel

theorem rec (n : ℕ) (hn : 25 ≤ n) : (a n : ℚ) = 10001 * a (n - 4) - 10000 * a (n - 8) := by
  have : a n = 10001 * a (n - 4) - 10000 * a (n - 8) := by
    by_cases h : 36 ≤ n
    · exact rec_big n h
    · have hs := smallOK_t
      unfold smallOK at hs
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hs
      have := hs (n - 25) (by omega)
      rw [show n - 25 + 25 = n by omega, show n - 25 + 21 = n - 4 by omega, show n - 25 + 17 = n - 8 by omega] at this
      rw [a_aw n (by omega), a_aw (n - 4) (by omega), a_aw (n - 8) (by omega)]
      exact this
  rw [this]; push_cast; ring

set_option maxHeartbeats 2000000 in
open PowerSeries in
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (10000 * X ^ 8 - 10001 * X ^ 4 + 1 : PowerSeries ℚ) = 990000000 * X ^ 24 - 991000000 * X ^ 23 + 1000000 * X ^ 22 + 110000000 * X ^ 21 - 9999000 * X ^ 20 - 900 * X ^ 19 - 100 * X ^ 18 - 111011000 * X ^ 17 + 11010000 * X ^ 16 + 1000 * X ^ 15 + 1100 * X ^ 13 - 1100 * X ^ 12 + 9 * X ^ 11 + 90 * X ^ 10 - 89 * X ^ 9 + 1090 * X ^ 8 - 1000 * X ^ 7 + 911 * X ^ 6 + 90 * X ^ 5 + 9 * X ^ 4 + 1001 * X ^ 3 + 100 * X ^ 2 + 10 * X + 1 := by
  have h0 : a 0 = 1 := by rw [a_aw 0 (by norm_num)]; decide +kernel
  have h1 : a 1 = 10 := by rw [a_aw 1 (by norm_num)]; decide +kernel
  have h2 : a 2 = 100 := by rw [a_aw 2 (by norm_num)]; decide +kernel
  have h3 : a 3 = 1001 := by rw [a_aw 3 (by norm_num)]; decide +kernel
  have h4 : a 4 = 10010 := by rw [a_aw 4 (by norm_num)]; decide +kernel
  have h5 : a 5 = 100100 := by rw [a_aw 5 (by norm_num)]; decide +kernel
  have h6 : a 6 = 1001011 := by rw [a_aw 6 (by norm_num)]; decide +kernel
  have h7 : a 7 = 10010001 := by rw [a_aw 7 (by norm_num)]; decide +kernel
  have h8 : a 8 = 100101100 := by rw [a_aw 8 (by norm_num)]; decide +kernel
  have h9 : a 9 = 1001000011 := by rw [a_aw 9 (by norm_num)]; decide +kernel
  have h10 : a 10 = 10010111101 := by rw [a_aw 10 (by norm_num)]; decide +kernel
  have h11 : a 11 = 100100010010 := by rw [a_aw 11 (by norm_num)]; decide +kernel
  have h12 : a 12 = 1001011000000 := by rw [a_aw 12 (by norm_num)]; decide +kernel
  have h13 : a 13 = 10010000111111 := by rw [a_aw 13 (by norm_num)]; decide +kernel
  have h14 : a 14 = 100101111011101 := by rw [a_aw 14 (by norm_num)]; decide +kernel
  have h15 : a 15 = 1001000100101010 := by rw [a_aw 15 (by norm_num)]; decide +kernel
  have h16 : a 16 = 10010110011010000 := by rw [a_aw 16 (by norm_num)]; decide +kernel
  have h17 : a 17 = 100100001000100111 := by rw [a_aw 17 (by norm_num)]; decide +kernel
  have h18 : a 18 = 1001011110111011001 := by rw [a_aw 18 (by norm_num)]; decide +kernel
  have h19 : a 19 = 10010001001010100110 := by rw [a_aw 19 (by norm_num)]; decide +kernel
  have h20 : a 20 = 100101100110101011000 := by rw [a_aw 20 (by norm_num)]; decide +kernel
  have h21 : a 21 = 1001000010001000100111 := by rw [a_aw 21 (by norm_num)]; decide +kernel
  have h22 : a 22 = 10010111101110111011001 := by rw [a_aw 22 (by norm_num)]; decide +kernel
  have h23 : a 23 = 100100010010100010100110 := by rw [a_aw 23 (by norm_num)]; decide +kernel
  have h24 : a 24 = 1001011001101011101011000 := by rw [a_aw 24 (by norm_num)]; decide +kernel
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, f = fun n => (a n : ℚ) := ⟨_, rfl⟩
  have g0 : f 0 = 1 := by simp only [hf, h0]; norm_num
  have g1 : f 1 = 10 := by simp only [hf, h1]; norm_num
  have g2 : f 2 = 100 := by simp only [hf, h2]; norm_num
  have g3 : f 3 = 1001 := by simp only [hf, h3]; norm_num
  have g4 : f 4 = 10010 := by simp only [hf, h4]; norm_num
  have g5 : f 5 = 100100 := by simp only [hf, h5]; norm_num
  have g6 : f 6 = 1001011 := by simp only [hf, h6]; norm_num
  have g7 : f 7 = 10010001 := by simp only [hf, h7]; norm_num
  have g8 : f 8 = 100101100 := by simp only [hf, h8]; norm_num
  have g9 : f 9 = 1001000011 := by simp only [hf, h9]; norm_num
  have g10 : f 10 = 10010111101 := by simp only [hf, h10]; norm_num
  have g11 : f 11 = 100100010010 := by simp only [hf, h11]; norm_num
  have g12 : f 12 = 1001011000000 := by simp only [hf, h12]; norm_num
  have g13 : f 13 = 10010000111111 := by simp only [hf, h13]; norm_num
  have g14 : f 14 = 100101111011101 := by simp only [hf, h14]; norm_num
  have g15 : f 15 = 1001000100101010 := by simp only [hf, h15]; norm_num
  have g16 : f 16 = 10010110011010000 := by simp only [hf, h16]; norm_num
  have g17 : f 17 = 100100001000100111 := by simp only [hf, h17]; norm_num
  have g18 : f 18 = 1001011110111011001 := by simp only [hf, h18]; norm_num
  have g19 : f 19 = 10010001001010100110 := by simp only [hf, h19]; norm_num
  have g20 : f 20 = 100101100110101011000 := by simp only [hf, h20]; norm_num
  have g21 : f 21 = 1001000010001000100111 := by simp only [hf, h21]; norm_num
  have g22 : f 22 = 10010111101110111011001 := by simp only [hf, h22]; norm_num
  have g23 : f 23 = 100100010010100010100110 := by simp only [hf, h23]; norm_num
  have g24 : f 24 = 1001011001101011101011000 := by simp only [hf, h24]; norm_num
  have grec : ∀ k, 25 ≤ k → f k = 10001 * f (k - 4) - 10000 * f (k - 8) := by
    intro k hk; simp only [hf]; exact rec k hk
  rw [← hf]
  clear hf h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24
  set A : PowerSeries ℚ := PowerSeries.mk f with hA
  have hD : A * (10000 * X ^ 8 - 10001 * X ^ 4 + 1 : PowerSeries ℚ) =
      C (10000 : ℚ) * (A * X ^ 8) - C (10001 : ℚ) * (A * X ^ 4) + A := by
    simp only [map_ofNat]; ring
  have hN : (990000000 * X ^ 24 - 991000000 * X ^ 23 + 1000000 * X ^ 22 + 110000000 * X ^ 21 - 9999000 * X ^ 20 - 900 * X ^ 19 - 100 * X ^ 18 - 111011000 * X ^ 17 + 11010000 * X ^ 16 + 1000 * X ^ 15 + 1100 * X ^ 13 - 1100 * X ^ 12 + 9 * X ^ 11 + 90 * X ^ 10 - 89 * X ^ 9 + 1090 * X ^ 8 - 1000 * X ^ 7 + 911 * X ^ 6 + 90 * X ^ 5 + 9 * X ^ 4 + 1001 * X ^ 3 + 100 * X ^ 2 + 10 * X + 1 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (10 : ℚ) * X ^ 1 + C (100 : ℚ) * X ^ 2 + C (1001 : ℚ) * X ^ 3 + C (9 : ℚ) * X ^ 4 + C (90 : ℚ) * X ^ 5 + C (911 : ℚ) * X ^ 6 - C (1000 : ℚ) * X ^ 7 + C (1090 : ℚ) * X ^ 8 - C (89 : ℚ) * X ^ 9 + C (90 : ℚ) * X ^ 10 + C (9 : ℚ) * X ^ 11 - C (1100 : ℚ) * X ^ 12 + C (1100 : ℚ) * X ^ 13 + C (1000 : ℚ) * X ^ 15 + C (11010000 : ℚ) * X ^ 16 - C (111011000 : ℚ) * X ^ 17 - C (100 : ℚ) * X ^ 18 - C (900 : ℚ) * X ^ 19 - C (9999000 : ℚ) * X ^ 20 + C (110000000 : ℚ) * X ^ 21 + C (1000000 : ℚ) * X ^ 22 - C (991000000 : ℚ) * X ^ 23 + C (990000000 : ℚ) * X ^ 24 := by
    simp only [map_ofNat, map_one]; ring
  rw [hD, hN]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_C]
  rcases Nat.lt_or_ge k 25 with h | h
  · interval_cases k <;> simp [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24] <;> norm_num
  · simp only [show 0 ≤ k by omega, show 1 ≤ k by omega, show 2 ≤ k by omega, show 3 ≤ k by omega, show 4 ≤ k by omega, show 5 ≤ k by omega, show 6 ≤ k by omega, show 7 ≤ k by omega, show 8 ≤ k by omega, show 9 ≤ k by omega, show 10 ≤ k by omega, show 11 ≤ k by omega, show 12 ≤ k by omega, show 13 ≤ k by omega, show 15 ≤ k by omega, show 16 ≤ k by omega, show 17 ≤ k by omega, show 18 ≤ k by omega, show 19 ≤ k by omega, show 20 ≤ k by omega, show 21 ≤ k by omega, show 22 ≤ k by omega, show 23 ≤ k by omega, show 24 ≤ k by omega, show k - 0 ≠ 0 by omega, show k - 1 ≠ 0 by omega, show k - 2 ≠ 0 by omega, show k - 3 ≠ 0 by omega, show k - 4 ≠ 0 by omega, show k - 5 ≠ 0 by omega, show k - 6 ≠ 0 by omega, show k - 7 ≠ 0 by omega, show k - 8 ≠ 0 by omega, show k - 9 ≠ 0 by omega, show k - 10 ≠ 0 by omega, show k - 11 ≠ 0 by omega, show k - 12 ≠ 0 by omega, show k - 13 ≠ 0 by omega, show k - 15 ≠ 0 by omega, show k - 16 ≠ 0 by omega, show k - 17 ≠ 0 by omega, show k - 18 ≠ 0 by omega, show k - 19 ≠ 0 by omega, show k - 20 ≠ 0 by omega, show k - 21 ≠ 0 by omega, show k - 22 ≠ 0 by omega, show k - 23 ≠ 0 by omega, show k - 24 ≠ 0 by omega, if_true, if_false]
    linear_combination grec k h

end OMA.Helpers_a282954

open OMA.Helpers_a282954 in
theorem OMA.solution : type_of% @OMA.S_oeis_a282954.main := ⟨rec, gf⟩
