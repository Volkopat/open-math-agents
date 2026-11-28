import OMAStatements.S_oeis_a281751
import Mathlib

namespace OMA.Helpers_a281751
open OMA.S_oeis_a281751

def R (c r l u d : Bool) : Bool := Nat.testBit 395 (c.toNat + 2 * (r.toNat + l.toNat + u.toNat + d.toNat))

theorem cell_succ (t : ℕ) (i j : ℤ) : cell 395 (t + 1) i j = R (cell 395 t i j) (cell 395 t (i + 1) j)
    (cell 395 t (i - 1) j) (cell 395 t i (j + 1)) (cell 395 t i (j - 1)) := rfl

def bg (t : ℕ) : Bool := decide (t % 2 = 1)

theorem cone : ∀ t : ℕ, ∀ x y : ℤ, (t : ℤ) < |x| + |y| → cell 395 t x y = bg t := by
  intro t
  induction t with
  | zero =>
    intro x y h
    show decide (x = 0 ∧ y = 0) = decide (0 % 2 = 1)
    simp only [Nat.zero_mod, zero_ne_one, decide_false, decide_eq_false_iff_not, not_and]
    intro hx hy; subst hx hy; simp at h
  | succ t ih =>
    intro x y h
    push_cast at h
    rw [cell_succ, ih x y (by omega),
      ih (x + 1) y (by cases abs_cases x <;> cases abs_cases (x + 1) <;> cases abs_cases y <;> omega),
      ih (x - 1) y (by cases abs_cases x <;> cases abs_cases (x - 1) <;> cases abs_cases y <;> omega),
      ih x (y + 1) (by cases abs_cases x <;> cases abs_cases (y + 1) <;> cases abs_cases y <;> omega),
      ih x (y - 1) (by cases abs_cases x <;> cases abs_cases (y - 1) <;> cases abs_cases y <;> omega)]
    have : bg (t + 1) = !bg t := by
      unfold bg; rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h, Nat.add_mod]
    rw [this]
    cases bg t <;> decide

theorem symm : ∀ t : ℕ, ∀ x y : ℤ, cell 395 t (-x) y = cell 395 t x y := by
  intro t
  induction t with
  | zero => intro x y; show decide (-x = 0 ∧ y = 0) = decide (x = 0 ∧ y = 0); simp
  | succ t ih =>
    intro x y
    rw [cell_succ, cell_succ, ih, show -x + 1 = -(x - 1) by ring, ih, show -x - 1 = -(x + 1) by ring, ih, ih, ih]
    unfold R; congr 2; omega

theorem swap : ∀ t : ℕ, ∀ x y : ℤ, cell 395 t x y = cell 395 t y x := by
  intro t
  induction t with
  | zero => intro x y; show decide (x = 0 ∧ y = 0) = decide (y = 0 ∧ x = 0); simp [and_comm]
  | succ t ih =>
    intro x y
    rw [cell_succ, cell_succ, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y + 1), ih x (y - 1)]
    unfold R; congr 2; omega

theorem negy (t : ℕ) (x y : ℤ) : cell 395 t x (-y) = cell 395 t x y := by
  rw [swap, symm, swap]

/-- window coordinates: `u = x + t`. -/
def nb (t : ℕ) (u y : ℤ) : Bool := cell 395 t (u - t) y

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
  let an := r ||| l ||| u ||| d
  let al := r &&& l &&& u &&& d
  let p := r ^^^ l ^^^ u ^^^ d
  ((M ^^^ c) &&& ((M ^^^ an) ||| al)) ||| (c &&& ((M ^^^ an) ||| p))

theorem R_formula (c r l u d : Bool) :
    (((true ^^ c) && ((true ^^ (r || l || u || d)) || (r && l && u && d))) ||
      (c && ((true ^^ (r || l || u || d)) || (r ^^ l ^^ u ^^ d)))) = R c r l u d := by
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

def mk (yi : ℕ) : ℕ := 2 ^ (13 - (if yi ≤ 12 then 12 - yi else yi - 12)) - 1

def msk (w : List ℕ) : List ℕ := (List.range 25).map fun yi => w.getD yi 0 &&& mk yi

theorem perOK_t : msk (Wst 12 21) = msk (Wst 12 13) := by decide +kernel

theorem SV_per (u y : ℤ) (hu : 0 ≤ u) (hy : |y| ≤ 12 - u) : SV 12 21 u y = SV 12 13 u y := by
  have hy' : (y + 12).toNat < 25 := by cases abs_cases y <;> omega
  have h := congrArg (fun w => (w.getD (y + 12).toNat 0).testBit u.toNat) perOK_t
  simp only [msk] at h
  rw [getD_mapRange _ _ _ _ hy', getD_mapRange _ _ _ _ hy', Nat.testBit_and, Nat.testBit_and] at h
  have hm : (mk (y + 12).toNat).testBit u.toNat = true := by
    unfold mk; rw [Nat.testBit_two_pow_sub_one]; apply decide_eq_true
    split_ifs <;> cases abs_cases y <;> omega
  rw [hm, Bool.and_true, Bool.and_true] at h
  exact h

theorem per : ∀ t : ℕ, 13 ≤ t → ∀ u y : ℤ, 0 ≤ u → |y| ≤ 12 - u → nb (t + 8) u y = nb t u y := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro u y hu hy; rw [correct 12 21 u y hu hy, correct 12 13 u y hu hy]; exact SV_per u y hu hy
  | succ t ht ih =>
    intro u y hu hy
    have key : ∀ u' y' : ℤ, (u' < 0 ∨ (0 ≤ u' ∧ |y'| ≤ 12 - u')) → nb (t + 8) u' y' = nb t u' y' := by
      intro u' y' h
      rcases h with h | ⟨h1, h2⟩
      · rw [nb_neg _ _ _ h, nb_neg _ _ _ h]; unfold bg; rw [show (t + 8) % 2 = t % 2 by omega]
      · exact ih u' y' h1 h2
    rw [show t + 1 + 8 = (t + 8) + 1 by omega, nb_succ (t + 8), nb_succ t,
      key (u - 1) y (by cases abs_cases y <;> omega), key u y (Or.inr ⟨hu, hy⟩),
      key (u - 2) y (by cases abs_cases y <;> omega),
      key (u - 1) (y + 1) (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega),
      key (u - 1) (y - 1) (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)]

theorem per_red (t : ℕ) (ht : 13 ≤ t) (u y : ℤ) (hu : 0 ≤ u) (hy : |y| ≤ 12 - u) :
    nb t u y = nb (13 + (t - 13) % 8) u y := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases h : t < 21
    · congr 1; omega
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 8 := ⟨t - 8, by omega⟩
      rw [per s (by omega) u y hu hy, ih s (by omega) (by omega)]
      congr 2; omega

def MtL : List (List ℕ) := [[4, 17, 4, 10, 4, 17, 4, 17], [4, 17, 4, 14, 4, 17, 4, 17], [4, 17, 4, 10, 4, 17, 4, 17], [4, 17, 4, 14, 4, 17, 4, 17], [4, 17, 4, 10, 4, 17, 4, 17], [4, 17, 4, 14, 4, 17, 4, 17]]

def RtL : List (List ℕ) := [[17, 0], [21, 10], [31, 14], [17, 0], [21, 10], [31, 14]]

/-- the predicted state of the strip `|y| ≤ 2` at a time `≡ r (mod 6)`, away from the left edge -/
def predR (r : ℕ) (x y : ℤ) : Bool :=
  if -1 ≤ x then ((RtL.getD r []).getD (-x).toNat 0).testBit (y + 2).toNat
  else ((MtL.getD r []).getD (x % 8).toNat 0).testBit (y + 2).toNat

theorem predR_mid (r : ℕ) (x x' : ℤ) (hx : x ≤ -2) (hx' : x' ≤ -2) (h : x % 8 = x' % 8) (y : ℤ) :
    predR r x y = predR r x' y := by
  unfold predR; rw [if_neg (by omega), if_neg (by omega), h]

def Phi (t : ℕ) : Prop :=
  ∀ x y : ℤ, 7 ≤ (t : ℤ) + x → x ≤ 0 → |y| ≤ 2 → cell 395 t x y = predR (t % 6) x y

def baseOK : Bool := (List.range 18).all fun i => (List.range 5).all fun j =>
  SV 26 24 ((i : ℤ) + 7) ((j : ℤ) - 2) == predR 0 ((i : ℤ) - 17) ((j : ℤ) - 2)

theorem baseOK_t : baseOK = true := by decide +kernel

theorem phi_base : Phi 24 := by
  intro x y h1 h2 hy
  have h := baseOK_t
  unfold baseOK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h (x + 17).toNat (by omega) (y + 2).toNat (by cases abs_cases y <;> omega)
  rw [show (((x + 17).toNat : ℕ) : ℤ) + 7 = x + 24 by omega, show (((x + 17).toNat : ℕ) : ℤ) - 17 = x by omega,
    show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by cases abs_cases y <;> omega] at this
  rw [← this, ← correct 26 24 (x + 24) y (by omega) (by cases abs_cases y <;> omega)]
  unfold nb; congr 1; push_cast; ring

def triOK : Bool := (List.range 24).all fun r => (List.range 2).all fun v => (List.range 5).all fun j =>
  SV 12 (13 + (24 + r - 13) % 8) ((v : ℤ) + 7) ((j : ℤ) - 2) ==
    predR ((24 + r) % 6) ((v : ℤ) + 7 - ((24 + r : ℕ) : ℤ)) ((j : ℤ) - 2)

theorem triOK_t : triOK = true := by decide +kernel

theorem tri_part (s : ℕ) (hs : 25 ≤ s) (u y : ℤ) (hu1 : 7 ≤ u) (hu2 : u ≤ 8) (hy : |y| ≤ 2) :
    cell 395 s (u - s) y = predR (s % 6) (u - s) y := by
  have h := triOK_t
  unfold triOK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h ((s - 24) % 24) (Nat.mod_lt _ (by norm_num)) (u - 7).toNat (by omega) (y + 2).toNat
    (by cases abs_cases y <;> omega)
  rw [show (((u - 7).toNat : ℕ) : ℤ) + 7 = u by omega,
    show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by cases abs_cases y <;> omega,
    show (24 + (s - 24) % 24 - 13) % 8 = (s - 13) % 8 by omega,
    show (24 + (s - 24) % 24) % 6 = s % 6 by omega] at this
  rw [show cell 395 s (u - s) y = nb s u y from rfl, per_red s (by omega) u y (by omega)
    (by cases abs_cases y <;> omega), correct 12 _ u y (by omega) (by cases abs_cases y <;> omega), this]
  apply predR_mid
  · push_cast; omega
  · omega
  · push_cast; omega

def stepF (r : ℕ) (x y : ℤ) (b : Bool) : Bool :=
  R (predR r x y) (if x = 0 then predR r (-1) y else predR r (x + 1) y) (predR r (x - 1) y)
    (if y + 1 ≤ 2 then predR r x (y + 1) else if -2 ≤ x then predR r (-3) x else b)
    (if -2 ≤ y - 1 then predR r x (y - 1) else if -2 ≤ x then predR r (-3) x else b) == predR ((r + 1) % 6) x y

def stepOK : Bool := (List.range 6).all fun r => (List.range 12).all fun i => (List.range 5).all fun j =>
  stepF r ((i : ℤ) - 11) ((j : ℤ) - 2) false && stepF r ((i : ℤ) - 11) ((j : ℤ) - 2) true

theorem stepOK_t : stepOK = true := by decide +kernel

theorem stepNear (r : ℕ) (hr : r < 6) (x y : ℤ) (h1 : -11 ≤ x) (h2 : x ≤ 0) (hy : |y| ≤ 2) (b : Bool) :
    stepF r x y b = true := by
  have h := stepOK_t
  unfold stepOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  have := h r hr (x + 11).toNat (by omega) (y + 2).toNat (by cases abs_cases y <;> omega)
  rw [show (((x + 11).toNat : ℕ) : ℤ) - 11 = x by omega,
    show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by cases abs_cases y <;> omega] at this
  cases b
  · exact this.1
  · exact this.2

theorem stepAll (r : ℕ) (hr : r < 6) (x y : ℤ) (h2 : x ≤ 0) (hy : |y| ≤ 2) (b : Bool) :
    stepF r x y b = true := by
  by_cases h1 : -11 ≤ x
  · exact stepNear r hr x y h1 h2 hy b
  · have e : stepF r x y b = stepF r (-11 + (x + 11) % 8) y b := by
      unfold stepF
      simp only [show ¬ x = 0 by omega, show ¬ (-11 + (x + 11) % 8 = 0) by omega, show ¬ (-2 ≤ x) by omega,
        show ¬ (-2 ≤ -11 + (x + 11) % 8) by omega, if_false,
        predR_mid r x (-11 + (x + 11) % 8) (by omega) (by omega) (by omega),
        predR_mid r (x + 1) (-11 + (x + 11) % 8 + 1) (by omega) (by omega) (by omega),
        predR_mid r (x - 1) (-11 + (x + 11) % 8 - 1) (by omega) (by omega) (by omega),
        predR_mid ((r + 1) % 6) x (-11 + (x + 11) % 8) (by omega) (by omega) (by omega)]
    rw [e]
    exact stepNear r hr _ y (by omega) (by omega) hy b

theorem phi_step (t : ℕ) (ht : 24 ≤ t) (H : Phi t) : Phi (t + 1) := by
  intro x y h1 h2 hy
  push_cast at h1
  by_cases hu : (t : ℤ) + 1 + x ≤ 8
  · have := tri_part (t + 1) (by omega) ((t : ℤ) + 1 + x) y (by omega) hu hy
    rw [show (t : ℤ) + 1 + x - ((t + 1 : ℕ) : ℤ) = x by push_cast; ring] at this
    exact this
  · have e0 : cell 395 t x y = predR (t % 6) x y := H x y (by omega) h2 hy
    have er : cell 395 t (x + 1) y = if x = 0 then predR (t % 6) (-1) y else predR (t % 6) (x + 1) y := by
      split_ifs with hx
      · subst hx; rw [show (0 : ℤ) + 1 = -(-1) by norm_num, symm]; exact H (-1) y (by omega) (by norm_num) hy
      · exact H (x + 1) y (by omega) (by omega) hy
    have el : cell 395 t (x - 1) y = predR (t % 6) (x - 1) y := H (x - 1) y (by omega) (by omega) hy
    have e3 : -2 ≤ x → cell 395 t x 3 = predR (t % 6) (-3) x := by
      intro hx
      rw [swap, show (3 : ℤ) = -(-3) by norm_num, symm]
      exact H (-3) x (by omega) (by norm_num) (by cases abs_cases x <;> omega)
    have eu : cell 395 t x (y + 1) = if y + 1 ≤ 2 then predR (t % 6) x (y + 1)
        else if -2 ≤ x then predR (t % 6) (-3) x else cell 395 t x 3 := by
      split_ifs with ha hb
      · exact H x (y + 1) (by omega) h2 (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega)
      · rw [show y + 1 = 3 by cases abs_cases y <;> omega]; exact e3 hb
      · rw [show y + 1 = 3 by cases abs_cases y <;> omega]
    have ed : cell 395 t x (y - 1) = if -2 ≤ y - 1 then predR (t % 6) x (y - 1)
        else if -2 ≤ x then predR (t % 6) (-3) x else cell 395 t x 3 := by
      split_ifs with ha hb
      · exact H x (y - 1) (by omega) h2 (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)
      · rw [show y - 1 = -3 by cases abs_cases y <;> omega, negy]; exact e3 hb
      · rw [show y - 1 = -3 by cases abs_cases y <;> omega, negy]
    have hs := stepAll (t % 6) (Nat.mod_lt _ (by norm_num)) x y h2 hy (cell 395 t x 3)
    unfold stepF at hs
    rw [beq_iff_eq] at hs
    rw [cell_succ, e0, er, el, eu, ed, hs]
    congr 1; omega

theorem phi_all : ∀ t : ℕ, 24 ≤ t → Phi t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact phi_base
  | succ t ht ih => exact phi_step t ht ih

theorem dig (n k : ℕ) (hn : 24 ≤ n) (hk : k ≤ n) :
    cell 395 n (k : ℤ) 0 = if n - k ≤ 8 then SV 12 (13 + (n - 13) % 8) ((n - k : ℕ) : ℤ) 0
      else predR (n % 6) (-(k : ℤ)) 0 := by
  rw [← symm]
  have e : cell 395 n (-(k : ℤ)) 0 = nb n ((n - k : ℕ) : ℤ) 0 := by
    unfold nb; congr 1; push_cast [Nat.cast_sub hk]; ring
  split_ifs with h
  · rw [e, per_red n (by omega) _ 0 (by omega) (by simp; omega), correct 12 _ _ 0 (by omega) (by simp; omega)]
  · exact phi_all n hn _ 0 (by omega) (by omega) (by norm_num)

def T1 (r : ℕ) : ℤ := ∑ i ∈ Finset.range 33,
  if (if 32 - i ≤ 8 then SV 12 (13 + (48 + r - 13) % 8) ((32 - i : ℕ) : ℤ) 0
      else predR ((48 + r) % 6) (-((48 + r - 8 + i : ℕ) : ℤ)) 0) then (2 : ℤ) ^ (32 - i) else 0

def T2 (r : ℕ) : ℤ := ∑ i ∈ Finset.range 9,
  if SV 12 (13 + (48 + r - 13) % 8) ((8 - i : ℕ) : ℤ) 0 then (2 : ℤ) ^ (8 - i) else 0

def K (r : ℕ) : ℤ := T1 r - 2 ^ 24 * T2 r

theorem shift (n : ℕ) (hn : 24 ≤ n) : a (n + 24) = 2 ^ 24 * a n + K (n % 24) := by
  unfold a K
  rw [show n + 24 + 1 = (n - 8) + 33 by omega, Finset.sum_range_add, show n + 1 = (n - 8) + 9 by omega,
    Finset.sum_range_add]
  have hh : ∑ k ∈ Finset.range (n - 8), (if cell 395 (n + 24) (k : ℤ) 0 then (2 : ℤ) ^ (n + 24 - k) else 0) =
      2 ^ 24 * ∑ k ∈ Finset.range (n - 8), (if cell 395 n (k : ℤ) 0 then (2 : ℤ) ^ (n - k) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [dig (n + 24) k (by omega) (by omega), dig n k hn (by omega), if_neg (show ¬ (n + 24 - k ≤ 8) by omega),
      if_neg (show ¬ (n - k ≤ 8) by omega), show (n + 24) % 6 = n % 6 by omega,
      show n + 24 - k = 24 + (n - k) by omega, pow_add]
    split_ifs <;> simp
  have h1 : ∑ i ∈ Finset.range 33, (if cell 395 (n + 24) ((n - 8 + i : ℕ) : ℤ) 0 then (2 : ℤ) ^ (n + 24 - (n - 8 + i)) else 0) =
      T1 (n % 24) := by
    unfold T1
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [dig (n + 24) (n - 8 + i) (by omega) (by omega), show n + 24 - (n - 8 + i) = 32 - i by omega,
      show (n + 24 - 13) % 8 = (48 + n % 24 - 13) % 8 by omega, show (n + 24) % 6 = (48 + n % 24) % 6 by omega]
    by_cases hi2 : 32 - i ≤ 8
    · rw [if_pos hi2, if_pos hi2]
    · rw [if_neg hi2, if_neg hi2, predR_mid _ (-((n - 8 + i : ℕ) : ℤ)) (-((48 + n % 24 - 8 + i : ℕ) : ℤ))
        (by omega) (by omega) (by omega)]
  have h2 : ∑ i ∈ Finset.range 9, (if cell 395 n ((n - 8 + i : ℕ) : ℤ) 0 then (2 : ℤ) ^ (n - (n - 8 + i)) else 0) =
      T2 (n % 24) := by
    unfold T2
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [dig n (n - 8 + i) hn (by omega), if_pos (show n - (n - 8 + i) ≤ 8 by omega),
      show n - (n - 8 + i) = 8 - i by omega, show (n - 13) % 8 = (48 + n % 24 - 13) % 8 by omega]
  rw [hh, h1, h2]; ring

def Kl : List ℤ := [-27962025, 12237498, -27962025, 15395562, -27962025, -240407622, -27962025, -995184918, -27962025, 12237498, -27962025, 15395562, -27962025, -240407622, -27962025, -995184918, -27962025, 12237498, -27962025, 15395562, -27962025, -240407622, -27962025, -995184918]

theorem Kc0 : ((List.range 6).all fun i => K (i + 0) == Kl.getD (i + 0) 0) = true := by decide +kernel

theorem Kc1 : ((List.range 6).all fun i => K (i + 6) == Kl.getD (i + 6) 0) = true := by decide +kernel

theorem Kc2 : ((List.range 6).all fun i => K (i + 12) == Kl.getD (i + 12) 0) = true := by decide +kernel

theorem Kc3 : ((List.range 6).all fun i => K (i + 18) == Kl.getD (i + 18) 0) = true := by decide +kernel

theorem K_eq (r : ℕ) (hr : r < 24) : K r = Kl.getD r 0 := by
  by_cases c0 : r < 6
  · have h := Kc0; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 0) (by omega); rwa [show r - 0 + 0 = r by omega] at this
  by_cases c1 : r < 12
  · have h := Kc1; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 6) (by omega); rwa [show r - 6 + 6 = r by omega] at this
  by_cases c2 : r < 18
  · have h := Kc2; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 12) (by omega); rwa [show r - 12 + 12 = r by omega] at this
  by_cases c3 : r < 24
  · have h := Kc3; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 18) (by omega); rwa [show r - 18 + 18 = r by omega] at this
  omega

def Lc (r : ℕ) : ℤ := Kl.getD r 0 + 2 * Kl.getD ((r + 23) % 24) 0 - 8 * Kl.getD ((r + 21) % 24) 0 -
  16 * Kl.getD ((r + 20) % 24) 0 - Kl.getD ((r + 16) % 24) 0 - 2 * Kl.getD ((r + 15) % 24) 0 +
  8 * Kl.getD ((r + 13) % 24) 0 + 16 * Kl.getD ((r + 12) % 24) 0

def LcOK : Bool := (List.range 24).all fun r => Lc r == 0

theorem LcOK_t : LcOK = true := by decide +kernel

def awZ (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), if ((Wst 26 n).getD 26 0).testBit (n - k) then (2 : ℤ) ^ (n - k) else 0

theorem a_aw (n : ℕ) (hn : n ≤ 26) : a n = awZ n := by
  unfold a awZ
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [← symm]
  have e : cell 395 n (-(k : ℤ)) 0 = nb n ((n - k : ℕ) : ℤ) 0 := by
    unfold nb; congr 1; push_cast [Nat.cast_sub (by omega : k ≤ n)]; ring
  rw [e, correct 26 n _ 0 (by omega) (by simp; omega)]
  unfold SV
  rw [show ((0 : ℤ) + ((26 : ℕ) : ℤ)).toNat = 26 from rfl, Int.toNat_natCast]

def aD (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1),
  if (if n - k ≤ 8 then SV 12 (13 + (n - 13) % 8) ((n - k : ℕ) : ℤ) 0 else predR (n % 6) (-(k : ℤ)) 0)
  then (2 : ℤ) ^ (n - k) else 0

theorem a_aD (n : ℕ) (hn : 24 ≤ n) : a n = aD n := by
  unfold a aD
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [dig n k hn (by omega)]

def av (n : ℕ) : ℤ := if n < 24 then awZ n else aD n

theorem a_av (n : ℕ) : a n = av n := by
  unfold av
  split_ifs with h
  · exact a_aw n (by omega)
  · exact a_aD n (by omega)

def Lz (n : ℕ) : ℤ := a n + 2 * a (n - 1) - 8 * a (n - 3) - 16 * a (n - 4) - a (n - 8) - 2 * a (n - 9) +
  8 * a (n - 11) + 16 * a (n - 12)

def Al : List ℤ := [1, 2, 7, 2, 23, 58, 23, 170, 471, 186, 1367, 3818, 1367, 11194, 30039, 12010, 87383, 244410, 87383, 715498, 1922391, 764858, 5592407, 15642346, 5592407, 45791930, 123032919, 48949994, 357913943, 1001106362, 357913943, 2930683626, 7874106711, 3132799674, 22906492247, 64070806250, 22906492247, 187563748282, 503942829399, 200499179242, 1466015503703, 4100531600058, 1466015503703, 12004079889130, 32252341081431, 12831947467706, 93824992236887, 262434022403818, 93824992236887, 768261112904378, 2064149829211479, 821244637932266, 6004799503160663, 16795777433840570, 6004799503160663, 49168711225880298, 132105589069534551, 52559656827665082, 384307168202282327, 1074929755765795562]

theorem Ac0 : ((List.range 5).all fun i => av (i + 0) == Al.getD (i + 0) 0) = true := by decide +kernel

theorem Ac1 : ((List.range 5).all fun i => av (i + 5) == Al.getD (i + 5) 0) = true := by decide +kernel

theorem Ac2 : ((List.range 5).all fun i => av (i + 10) == Al.getD (i + 10) 0) = true := by decide +kernel

theorem Ac3 : ((List.range 5).all fun i => av (i + 15) == Al.getD (i + 15) 0) = true := by decide +kernel

theorem Ac4 : ((List.range 5).all fun i => av (i + 20) == Al.getD (i + 20) 0) = true := by decide +kernel

theorem Ac5 : ((List.range 5).all fun i => av (i + 25) == Al.getD (i + 25) 0) = true := by decide +kernel

theorem Ac6 : ((List.range 5).all fun i => av (i + 30) == Al.getD (i + 30) 0) = true := by decide +kernel

theorem Ac7 : ((List.range 5).all fun i => av (i + 35) == Al.getD (i + 35) 0) = true := by decide +kernel

theorem Ac8 : ((List.range 5).all fun i => av (i + 40) == Al.getD (i + 40) 0) = true := by decide +kernel

theorem Ac9 : ((List.range 5).all fun i => av (i + 45) == Al.getD (i + 45) 0) = true := by decide +kernel

theorem Ac10 : ((List.range 5).all fun i => av (i + 50) == Al.getD (i + 50) 0) = true := by decide +kernel

theorem Ac11 : ((List.range 5).all fun i => av (i + 55) == Al.getD (i + 55) 0) = true := by decide +kernel

theorem a_Al (n : ℕ) (hn : n < 60) : a n = Al.getD n 0 := by
  rw [a_av]
  by_cases c0 : n < 5
  · have h := Ac0; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 0) (by omega); rwa [show n - 0 + 0 = n by omega] at this
  by_cases c1 : n < 10
  · have h := Ac1; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 5) (by omega); rwa [show n - 5 + 5 = n by omega] at this
  by_cases c2 : n < 15
  · have h := Ac2; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 10) (by omega); rwa [show n - 10 + 10 = n by omega] at this
  by_cases c3 : n < 20
  · have h := Ac3; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 15) (by omega); rwa [show n - 15 + 15 = n by omega] at this
  by_cases c4 : n < 25
  · have h := Ac4; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 20) (by omega); rwa [show n - 20 + 20 = n by omega] at this
  by_cases c5 : n < 30
  · have h := Ac5; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 25) (by omega); rwa [show n - 25 + 25 = n by omega] at this
  by_cases c6 : n < 35
  · have h := Ac6; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 30) (by omega); rwa [show n - 30 + 30 = n by omega] at this
  by_cases c7 : n < 40
  · have h := Ac7; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 35) (by omega); rwa [show n - 35 + 35 = n by omega] at this
  by_cases c8 : n < 45
  · have h := Ac8; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 40) (by omega); rwa [show n - 40 + 40 = n by omega] at this
  by_cases c9 : n < 50
  · have h := Ac9; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 45) (by omega); rwa [show n - 45 + 45 = n by omega] at this
  by_cases c10 : n < 55
  · have h := Ac10; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 50) (by omega); rwa [show n - 50 + 50 = n by omega] at this
  by_cases c11 : n < 60
  · have h := Ac11; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (n - 55) (by omega); rwa [show n - 55 + 55 = n by omega] at this
  omega

def smallOK : Bool := (List.range 40).all fun i =>
  Al.getD (i + 20) 0 + 2 * Al.getD (i + 19) 0 - 8 * Al.getD (i + 17) 0 - 16 * Al.getD (i + 16) 0 - Al.getD (i + 12) 0 -
    2 * Al.getD (i + 11) 0 + 8 * Al.getD (i + 9) 0 + 16 * Al.getD (i + 8) 0 == 0

theorem smallOK_t : smallOK = true := by decide +kernel

theorem Lz_zero : ∀ n : ℕ, 20 ≤ n → Lz n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : n < 60
    · have hs := smallOK_t
      unfold smallOK at hs
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hs
      have := hs (n - 20) (by omega)
      rw [show n - 20 + 20 = n by omega, show n - 20 + 19 = n - 1 by omega, show n - 20 + 17 = n - 3 by omega,
        show n - 20 + 16 = n - 4 by omega, show n - 20 + 12 = n - 8 by omega, show n - 20 + 11 = n - 9 by omega,
        show n - 20 + 9 = n - 11 by omega, show n - 20 + 8 = n - 12 by omega] at this
      unfold Lz
      rw [a_Al n (by omega), a_Al (n - 1) (by omega), a_Al (n - 3) (by omega), a_Al (n - 4) (by omega),
        a_Al (n - 8) (by omega), a_Al (n - 9) (by omega), a_Al (n - 11) (by omega), a_Al (n - 12) (by omega)]
      exact this
    · have hp := ih (n - 24) (by omega) (by omega)
      have hl := LcOK_t
      unfold LcOK at hl
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hl
      have hL := hl ((n - 24) % 24) (Nat.mod_lt _ (by norm_num))
      unfold Lc at hL
      rw [← K_eq _ (Nat.mod_lt _ (by norm_num)), ← K_eq _ (Nat.mod_lt _ (by norm_num)), ← K_eq _ (Nat.mod_lt _ (by norm_num)),
        ← K_eq _ (Nat.mod_lt _ (by norm_num)), ← K_eq _ (Nat.mod_lt _ (by norm_num)), ← K_eq _ (Nat.mod_lt _ (by norm_num)),
        ← K_eq _ (Nat.mod_lt _ (by norm_num)), ← K_eq _ (Nat.mod_lt _ (by norm_num))] at hL
      unfold Lz at hp ⊢
      have s0 := shift (n - 24) (by omega)
      have s1 := shift (n - 25) (by omega)
      have s3 := shift (n - 27) (by omega)
      have s4 := shift (n - 28) (by omega)
      have s8 := shift (n - 32) (by omega)
      have s9 := shift (n - 33) (by omega)
      have s11 := shift (n - 35) (by omega)
      have s12 := shift (n - 36) (by omega)
      rw [show n - 24 + 24 = n by omega] at s0
      rw [show n - 25 + 24 = n - 1 by omega, show (n - 25) % 24 = ((n - 24) % 24 + 23) % 24 by omega] at s1
      rw [show n - 27 + 24 = n - 3 by omega, show (n - 27) % 24 = ((n - 24) % 24 + 21) % 24 by omega] at s3
      rw [show n - 28 + 24 = n - 4 by omega, show (n - 28) % 24 = ((n - 24) % 24 + 20) % 24 by omega] at s4
      rw [show n - 32 + 24 = n - 8 by omega, show (n - 32) % 24 = ((n - 24) % 24 + 16) % 24 by omega] at s8
      rw [show n - 33 + 24 = n - 9 by omega, show (n - 33) % 24 = ((n - 24) % 24 + 15) % 24 by omega] at s9
      rw [show n - 35 + 24 = n - 11 by omega, show (n - 35) % 24 = ((n - 24) % 24 + 13) % 24 by omega] at s11
      rw [show n - 36 + 24 = n - 12 by omega, show (n - 36) % 24 = ((n - 24) % 24 + 12) % 24 by omega] at s12
      rw [show n - 24 - 1 = n - 25 by omega, show n - 24 - 3 = n - 27 by omega, show n - 24 - 4 = n - 28 by omega,
        show n - 24 - 8 = n - 32 by omega, show n - 24 - 9 = n - 33 by omega, show n - 24 - 11 = n - 35 by omega,
        show n - 24 - 12 = n - 36 by omega] at hp
      rw [s0, s1, s3, s4, s8, s9, s11, s12]
      linear_combination 2 ^ 24 * hp + hL

theorem rec (n : ℕ) (hn : 20 ≤ n) : (a n : ℚ) = -2 * a (n - 1) + 8 * a (n - 3) + 16 * a (n - 4) + a (n - 8) +
    2 * a (n - 9) - 8 * a (n - 11) - 16 * a (n - 12) := by
  have h := Lz_zero n hn
  unfold Lz at h
  have h' : ((a n + 2 * a (n - 1) - 8 * a (n - 3) - 16 * a (n - 4) - a (n - 8) - 2 * a (n - 9) +
    8 * a (n - 11) + 16 * a (n - 12) : ℤ) : ℚ) = 0 := by rw [h]; simp
  push_cast at h'
  linarith

set_option maxHeartbeats 2000000 in
open PowerSeries in
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (16 * X ^ 12 + 8 * X ^ 11 - 2 * X ^ 9 - X ^ 8 - 16 * X ^ 4 - 8 * X ^ 3 + 2 * X + 1 : PowerSeries ℚ) = -1024 * X ^ 19 - 512 * X ^ 18 - 256 * X ^ 17 + 64 * X ^ 15 - 16 * X ^ 12 + 56 * X ^ 11 + 12 * X ^ 9 - 22 * X ^ 8 + 11 * X ^ 6 + 16 * X ^ 5 - 5 * X ^ 4 + 8 * X ^ 3 + 11 * X ^ 2 + 4 * X + 1 := by
  have h0 : a 0 = 1 := by rw [a_aw 0 (by norm_num)]; decide +kernel
  have h1 : a 1 = 2 := by rw [a_aw 1 (by norm_num)]; decide +kernel
  have h2 : a 2 = 7 := by rw [a_aw 2 (by norm_num)]; decide +kernel
  have h3 : a 3 = 2 := by rw [a_aw 3 (by norm_num)]; decide +kernel
  have h4 : a 4 = 23 := by rw [a_aw 4 (by norm_num)]; decide +kernel
  have h5 : a 5 = 58 := by rw [a_aw 5 (by norm_num)]; decide +kernel
  have h6 : a 6 = 23 := by rw [a_aw 6 (by norm_num)]; decide +kernel
  have h7 : a 7 = 170 := by rw [a_aw 7 (by norm_num)]; decide +kernel
  have h8 : a 8 = 471 := by rw [a_aw 8 (by norm_num)]; decide +kernel
  have h9 : a 9 = 186 := by rw [a_aw 9 (by norm_num)]; decide +kernel
  have h10 : a 10 = 1367 := by rw [a_aw 10 (by norm_num)]; decide +kernel
  have h11 : a 11 = 3818 := by rw [a_aw 11 (by norm_num)]; decide +kernel
  have h12 : a 12 = 1367 := by rw [a_aw 12 (by norm_num)]; decide +kernel
  have h13 : a 13 = 11194 := by rw [a_aw 13 (by norm_num)]; decide +kernel
  have h14 : a 14 = 30039 := by rw [a_aw 14 (by norm_num)]; decide +kernel
  have h15 : a 15 = 12010 := by rw [a_aw 15 (by norm_num)]; decide +kernel
  have h16 : a 16 = 87383 := by rw [a_aw 16 (by norm_num)]; decide +kernel
  have h17 : a 17 = 244410 := by rw [a_aw 17 (by norm_num)]; decide +kernel
  have h18 : a 18 = 87383 := by rw [a_aw 18 (by norm_num)]; decide +kernel
  have h19 : a 19 = 715498 := by rw [a_aw 19 (by norm_num)]; decide +kernel
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, f = fun n => (a n : ℚ) := ⟨_, rfl⟩
  have g0 : f 0 = 1 := by simp only [hf, h0]; norm_num
  have g1 : f 1 = 2 := by simp only [hf, h1]; norm_num
  have g2 : f 2 = 7 := by simp only [hf, h2]; norm_num
  have g3 : f 3 = 2 := by simp only [hf, h3]; norm_num
  have g4 : f 4 = 23 := by simp only [hf, h4]; norm_num
  have g5 : f 5 = 58 := by simp only [hf, h5]; norm_num
  have g6 : f 6 = 23 := by simp only [hf, h6]; norm_num
  have g7 : f 7 = 170 := by simp only [hf, h7]; norm_num
  have g8 : f 8 = 471 := by simp only [hf, h8]; norm_num
  have g9 : f 9 = 186 := by simp only [hf, h9]; norm_num
  have g10 : f 10 = 1367 := by simp only [hf, h10]; norm_num
  have g11 : f 11 = 3818 := by simp only [hf, h11]; norm_num
  have g12 : f 12 = 1367 := by simp only [hf, h12]; norm_num
  have g13 : f 13 = 11194 := by simp only [hf, h13]; norm_num
  have g14 : f 14 = 30039 := by simp only [hf, h14]; norm_num
  have g15 : f 15 = 12010 := by simp only [hf, h15]; norm_num
  have g16 : f 16 = 87383 := by simp only [hf, h16]; norm_num
  have g17 : f 17 = 244410 := by simp only [hf, h17]; norm_num
  have g18 : f 18 = 87383 := by simp only [hf, h18]; norm_num
  have g19 : f 19 = 715498 := by simp only [hf, h19]; norm_num
  have grec : ∀ k, 20 ≤ k → f k = -2 * f (k - 1) + 8 * f (k - 3) + 16 * f (k - 4) + f (k - 8) +
      2 * f (k - 9) - 8 * f (k - 11) - 16 * f (k - 12) := by
    intro k hk; simp only [hf]; exact rec k hk
  rw [← hf]
  clear hf h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
  set A : PowerSeries ℚ := PowerSeries.mk f with hA
  have hD : A * (16 * X ^ 12 + 8 * X ^ 11 - 2 * X ^ 9 - X ^ 8 - 16 * X ^ 4 - 8 * X ^ 3 + 2 * X + 1 : PowerSeries ℚ) =
      C (16 : ℚ) * (A * X ^ 12) + C (8 : ℚ) * (A * X ^ 11) - C (2 : ℚ) * (A * X ^ 9) - A * X ^ 8
        - C (16 : ℚ) * (A * X ^ 4) - C (8 : ℚ) * (A * X ^ 3) + C (2 : ℚ) * (A * X ^ 1) + A := by
    simp only [map_ofNat]; ring
  have hN : (-1024 * X ^ 19 - 512 * X ^ 18 - 256 * X ^ 17 + 64 * X ^ 15 - 16 * X ^ 12 + 56 * X ^ 11 + 12 * X ^ 9 - 22 * X ^ 8 + 11 * X ^ 6 + 16 * X ^ 5 - 5 * X ^ 4 + 8 * X ^ 3 + 11 * X ^ 2 + 4 * X + 1 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (4 : ℚ) * X ^ 1 + C (11 : ℚ) * X ^ 2 + C (8 : ℚ) * X ^ 3 - C (5 : ℚ) * X ^ 4 + C (16 : ℚ) * X ^ 5 + C (11 : ℚ) * X ^ 6 - C (22 : ℚ) * X ^ 8 + C (12 : ℚ) * X ^ 9 + C (56 : ℚ) * X ^ 11 - C (16 : ℚ) * X ^ 12 + C (64 : ℚ) * X ^ 15 - C (256 : ℚ) * X ^ 17 - C (512 : ℚ) * X ^ 18 - C (1024 : ℚ) * X ^ 19 := by
    simp only [map_ofNat, map_one]; ring
  rw [hD, hN]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_C]
  rcases Nat.lt_or_ge k 20 with h | h
  · interval_cases k <;> simp [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19] <;> norm_num
  · simp only [show 0 ≤ k by omega, show 1 ≤ k by omega, show 2 ≤ k by omega, show 3 ≤ k by omega, show 4 ≤ k by omega, show 5 ≤ k by omega, show 6 ≤ k by omega, show 8 ≤ k by omega, show 9 ≤ k by omega, show 11 ≤ k by omega, show 12 ≤ k by omega, show 15 ≤ k by omega, show 17 ≤ k by omega, show 18 ≤ k by omega, show 19 ≤ k by omega, show k - 0 ≠ 0 by omega, show k - 1 ≠ 0 by omega, show k - 2 ≠ 0 by omega, show k - 3 ≠ 0 by omega, show k - 4 ≠ 0 by omega, show k - 5 ≠ 0 by omega, show k - 6 ≠ 0 by omega, show k - 8 ≠ 0 by omega, show k - 9 ≠ 0 by omega, show k - 11 ≠ 0 by omega, show k - 12 ≠ 0 by omega, show k - 15 ≠ 0 by omega, show k - 17 ≠ 0 by omega, show k - 18 ≠ 0 by omega, show k - 19 ≠ 0 by omega, if_true, if_false]
    linear_combination grec k h

end OMA.Helpers_a281751

open OMA.Helpers_a281751 in
theorem OMA.solution : type_of% @OMA.S_oeis_a281751.main := ⟨rec, gf⟩
