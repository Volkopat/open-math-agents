import OMAStatements.S_oeis_a281748
import Mathlib

namespace OMA.Helpers_oeis_a281748
open OMA.S_oeis_a281748

def cl : ℕ → ℤ → ℤ → Bool
  | 0 => fun i j => decide (i = 0 ∧ j = 0)
  | t + 1 => fun i j => Nat.testBit 395 ((cl t i j).toNat + 2 * ((cl t (i + 1) j).toNat +
      (cl t (i - 1) j).toNat + (cl t i (j + 1)).toNat + (cl t i (j - 1)).toNat))

def R (c r l u d : Bool) : Bool := Nat.testBit 395 (c.toNat + 2 * (r.toNat + l.toNat + u.toNat + d.toNat))

theorem cell_succ (t : ℕ) (i j : ℤ) : cl (t + 1) i j = R (cl t i j) (cl t (i + 1) j)
    (cl t (i - 1) j) (cl t i (j + 1)) (cl t i (j - 1)) := rfl

def bg (t : ℕ) : Bool := decide (t % 2 = 1)

theorem cone : ∀ t : ℕ, ∀ x y : ℤ, (t : ℤ) < |x| + |y| → cl t x y = bg t := by
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

theorem symm : ∀ t : ℕ, ∀ x y : ℤ, cl t (-x) y = cl t x y := by
  intro t
  induction t with
  | zero => intro x y; show decide (-x = 0 ∧ y = 0) = decide (x = 0 ∧ y = 0); simp
  | succ t ih =>
    intro x y
    rw [cell_succ, cell_succ, ih, show -x + 1 = -(x - 1) by ring, ih, show -x - 1 = -(x + 1) by ring, ih, ih, ih]
    unfold R; congr 2; omega

theorem swap : ∀ t : ℕ, ∀ x y : ℤ, cl t x y = cl t y x := by
  intro t
  induction t with
  | zero => intro x y; show decide (x = 0 ∧ y = 0) = decide (y = 0 ∧ x = 0); simp [and_comm]
  | succ t ih =>
    intro x y
    rw [cell_succ, cell_succ, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y + 1), ih x (y - 1)]
    unfold R; congr 2; omega

theorem negy (t : ℕ) (x y : ℤ) : cl t x (-y) = cl t x y := by
  rw [swap, symm, swap]

/-- window coordinates: `u = x + t`. -/
def nb (t : ℕ) (u y : ℤ) : Bool := cl t (u - t) y

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
  let s0 := r ^^^ l ^^^ u ^^^ d
  let a2 := (r &&& l) ||| (r &&& u) ||| (r &&& d) ||| (l &&& u) ||| (l &&& d) ||| (u &&& d)
  let a3 := (r &&& l &&& u) ||| (r &&& l &&& d) ||| (r &&& u &&& d) ||| (l &&& u &&& d)
  let e0 := M ^^^ (r ||| l ||| u ||| d)
  let e1 := s0 &&& (M ^^^ a2)
  let e2 := a2 &&& (M ^^^ a3)
  let e3 := s0 &&& a2
  let e4 := r &&& l &&& u &&& d
  let nc := M ^^^ c
  (nc &&& e0) ||| (c &&& e0) ||| (c &&& e1) ||| (c &&& e3) ||| (nc &&& e4)

theorem R_formula (c r l u d : Bool) :
    (((true ^^ c) && (true ^^ (r || l || u || d))) || (c && (true ^^ (r || l || u || d))) || (c && ((r ^^ l ^^ u ^^ d) && (true ^^ ((r && l) || (r && u) || (r && d) || (l && u) || (l && d) || (u && d))))) || (c && ((r ^^ l ^^ u ^^ d) && ((r && l) || (r && u) || (r && d) || (l && u) || (l && d) || (u && d)))) || ((true ^^ c) && (r && l && u && d))) = R c r l u d := by
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

def mk (yi : ℕ) : ℕ := 2 ^ (12 - (if yi ≤ 11 then 11 - yi else yi - 11)) - 1

def msk (w : List ℕ) : List ℕ := (List.range 23).map fun yi => w.getD yi 0 &&& mk yi

theorem perOK_t : msk (Wst 11 20) = msk (Wst 11 12) := by decide +kernel

theorem SV_per (u y : ℤ) (hu : 0 ≤ u) (hy : |y| ≤ 11 - u) : SV 11 20 u y = SV 11 12 u y := by
  have hy' : (y + 11).toNat < 23 := by cases abs_cases y <;> omega
  have h := congrArg (fun w => (w.getD (y + 11).toNat 0).testBit u.toNat) perOK_t
  simp only [msk] at h
  rw [getD_mapRange _ _ _ _ hy', getD_mapRange _ _ _ _ hy', Nat.testBit_and, Nat.testBit_and] at h
  have hm : (mk (y + 11).toNat).testBit u.toNat = true := by
    unfold mk; rw [Nat.testBit_two_pow_sub_one]; apply decide_eq_true
    split_ifs <;> cases abs_cases y <;> omega
  rw [hm, Bool.and_true, Bool.and_true] at h
  exact h

theorem per : ∀ t : ℕ, 12 ≤ t → ∀ u y : ℤ, 0 ≤ u → |y| ≤ 11 - u → nb (t + 8) u y = nb t u y := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro u y hu hy; rw [correct 11 20 u y hu hy, correct 11 12 u y hu hy]; exact SV_per u y hu hy
  | succ t ht ih =>
    intro u y hu hy
    have key : ∀ u' y' : ℤ, (u' < 0 ∨ (0 ≤ u' ∧ |y'| ≤ 11 - u')) → nb (t + 8) u' y' = nb t u' y' := by
      intro u' y' h
      rcases h with h | ⟨h1, h2⟩
      · rw [nb_neg _ _ _ h, nb_neg _ _ _ h]; unfold bg; rw [show (t + 8) % 2 = t % 2 by omega]
      · exact ih u' y' h1 h2
    rw [show t + 1 + 8 = (t + 8) + 1 by omega, nb_succ (t + 8), nb_succ t,
      key (u - 1) y (by cases abs_cases y <;> omega), key u y (Or.inr ⟨hu, hy⟩),
      key (u - 2) y (by cases abs_cases y <;> omega),
      key (u - 1) (y + 1) (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega),
      key (u - 1) (y - 1) (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)]

theorem per_red (t : ℕ) (ht : 12 ≤ t) (u y : ℤ) (hu : 0 ≤ u) (hy : |y| ≤ 11 - u) :
    nb t u y = nb (12 + (t - 12) % 8) u y := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases h : t < 20
    · congr 1; omega
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 8 := ⟨t - 8, by omega⟩
      rw [per s (by omega) u y hu hy, ih s (by omega) (by omega)]
      congr 2; omega

def MtL : List (List ℕ) := [[4, 17, 4, 10, 4, 17, 4, 17], [4, 17, 4, 14, 4, 17, 4, 17], [4, 17, 4, 10, 4, 17, 4, 17], [4, 17, 4, 14, 4, 17, 4, 17], [4, 17, 4, 10, 4, 17, 4, 17], [4, 17, 4, 14, 4, 17, 4, 17]]

def RtL : List (List ℕ) := [[17, 0], [21, 10], [31, 14], [17, 0], [21, 10], [31, 14]]

def predR (r : ℕ) (x y : ℤ) : Bool :=
  if -1 ≤ x then ((RtL.getD r []).getD (-x).toNat 0).testBit (y + 2).toNat
  else ((MtL.getD r []).getD (x % 8).toNat 0).testBit (y + 2).toNat

theorem predR_mid (r : ℕ) (x x' : ℤ) (hx : x ≤ -2) (hx' : x' ≤ -2) (h : x % 8 = x' % 8) (y : ℤ) :
    predR r x y = predR r x' y := by
  unfold predR; rw [if_neg (by omega), if_neg (by omega), h]

def Phi (t : ℕ) : Prop :=
  ∀ x y : ℤ, 7 ≤ (t : ℤ) + x → x ≤ 0 → |y| ≤ 2 → cl t x y = predR (t % 6) x y

def baseOK : Bool := (List.range 6).all fun i => (List.range 5).all fun j =>
  SV 16 12 ((i : ℤ) + 7) ((j : ℤ) - 2) == predR 0 ((i : ℤ) - 5) ((j : ℤ) - 2)

theorem baseOK_t : baseOK = true := by decide +kernel

theorem phi_base : Phi 12 := by
  intro x y h1 h2 hy
  have h := baseOK_t
  unfold baseOK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h (x + 5).toNat (by omega) (y + 2).toNat (by cases abs_cases y <;> omega)
  rw [show (((x + 5).toNat : ℕ) : ℤ) + 7 = x + 12 by omega, show (((x + 5).toNat : ℕ) : ℤ) - 5 = x by omega,
    show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by cases abs_cases y <;> omega] at this
  rw [show 12 % 6 = 0 from rfl, ← this, ← correct 16 12 (x + 12) y (by omega) (by cases abs_cases y <;> omega)]
  unfold nb; congr 1; push_cast; ring

def triOK : Bool := (List.range 24).all fun r => (List.range 2).all fun v => (List.range 5).all fun j =>
  SV 11 (12 + ((24 + r) - 12) % 8) ((v : ℤ) + 7) ((j : ℤ) - 2) ==
    predR ((24 + r) % 6) ((v : ℤ) + 7 - ((24 + r : ℕ) : ℤ)) ((j : ℤ) - 2)

theorem triOK_t : triOK = true := by decide +kernel

theorem tri_part (s : ℕ) (hs : 13 ≤ s) (u y : ℤ) (hu1 : 7 ≤ u) (hu2 : u ≤ 8) (hy : |y| ≤ 2) :
    cl s (u - s) y = predR (s % 6) (u - s) y := by
  have h := triOK_t
  unfold triOK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h (s % 24) (Nat.mod_lt _ (by norm_num)) (u - 7).toNat (by omega) (y + 2).toNat
    (by cases abs_cases y <;> omega)
  rw [show (((u - 7).toNat : ℕ) : ℤ) + 7 = u by omega,
    show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by cases abs_cases y <;> omega,
    show (24 + s % 24 - 12) % 8 = (s - 12) % 8 by omega,
    show (24 + s % 24) % 6 = s % 6 by omega] at this
  rw [show cl s (u - s) y = nb s u y from rfl, per_red s (by omega) u y (by omega)
    (by cases abs_cases y <;> omega), correct 11 _ u y (by omega) (by cases abs_cases y <;> omega), this]
  apply predR_mid
  · push_cast; omega
  · omega
  · push_cast; omega

def stepF (r : ℕ) (x y : ℤ) (b : Bool) : Bool :=
  R (predR r x y) (if x = 0 then predR r (-1) y else predR r (x + 1) y) (predR r (x - 1) y)
    (if y + 1 ≤ 2 then predR r x (y + 1) else if -2 ≤ x then predR r (-3) x else b)
    (if -2 ≤ y - 1 then predR r x (y - 1) else if -2 ≤ x then predR r (-3) x else b) == predR ((r + 1) % 6) x y

def stepOK : Bool := (List.range 6).all fun r => (List.range 14).all fun i => (List.range 5).all fun j =>
  stepF r ((i : ℤ) - 13) ((j : ℤ) - 2) false && stepF r ((i : ℤ) - 13) ((j : ℤ) - 2) true

theorem stepOK_t : stepOK = true := by decide +kernel

theorem stepNear (r : ℕ) (hr : r < 6) (x y : ℤ) (h1 : -13 ≤ x) (h2 : x ≤ 0) (hy : |y| ≤ 2) (b : Bool) :
    stepF r x y b = true := by
  have h := stepOK_t
  unfold stepOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  have := h r hr (x + 13).toNat (by omega) (y + 2).toNat (by cases abs_cases y <;> omega)
  rw [show (((x + 13).toNat : ℕ) : ℤ) - 13 = x by omega,
    show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by cases abs_cases y <;> omega] at this
  cases b
  · exact this.1
  · exact this.2

theorem stepAll (r : ℕ) (hr : r < 6) (x y : ℤ) (h2 : x ≤ 0) (hy : |y| ≤ 2) (b : Bool) :
    stepF r x y b = true := by
  by_cases h1 : -13 ≤ x
  · exact stepNear r hr x y h1 h2 hy b
  · have e : stepF r x y b = stepF r (-13 + (x + 13) % 8) y b := by
      unfold stepF
      simp only [show ¬ x = 0 by omega, show ¬ (-13 + (x + 13) % 8 = 0) by omega, show ¬ (-2 ≤ x) by omega,
        show ¬ (-2 ≤ -13 + (x + 13) % 8) by omega, if_false,
        predR_mid r x (-13 + (x + 13) % 8) (by omega) (by omega) (by omega),
        predR_mid r (x + 1) (-13 + (x + 13) % 8 + 1) (by omega) (by omega) (by omega),
        predR_mid r (x - 1) (-13 + (x + 13) % 8 - 1) (by omega) (by omega) (by omega),
        predR_mid ((r + 1) % 6) x (-13 + (x + 13) % 8) (by omega) (by omega) (by omega)]
    rw [e]
    exact stepNear r hr _ y (by omega) (by omega) hy b

theorem phi_step (t : ℕ) (ht : 12 ≤ t) (H : Phi t) : Phi (t + 1) := by
  intro x y h1 h2 hy
  push_cast at h1
  by_cases hu : (t : ℤ) + 1 + x ≤ 8
  · have := tri_part (t + 1) (by omega) ((t : ℤ) + 1 + x) y (by omega) hu hy
    rw [show (t : ℤ) + 1 + x - ((t + 1 : ℕ) : ℤ) = x by push_cast; ring] at this
    exact this
  · have e0 : cl t x y = predR (t % 6) x y := H x y (by omega) h2 hy
    have er : cl t (x + 1) y = if x = 0 then predR (t % 6) (-1) y else predR (t % 6) (x + 1) y := by
      split_ifs with hx
      · subst hx; rw [show (0 : ℤ) + 1 = -(-1) by norm_num, symm]; exact H (-1) y (by omega) (by norm_num) hy
      · exact H (x + 1) y (by omega) (by omega) hy
    have el : cl t (x - 1) y = predR (t % 6) (x - 1) y := H (x - 1) y (by omega) (by omega) hy
    have e3 : -2 ≤ x → cl t x 3 = predR (t % 6) (-3) x := by
      intro hx
      rw [swap, show (3 : ℤ) = -(-3) by norm_num, symm]
      exact H (-3) x (by omega) (by norm_num) (by cases abs_cases x <;> omega)
    have eu : cl t x (y + 1) = if y + 1 ≤ 2 then predR (t % 6) x (y + 1)
        else if -2 ≤ x then predR (t % 6) (-3) x else cl t x 3 := by
      split_ifs with ha hb
      · exact H x (y + 1) (by omega) h2 (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega)
      · rw [show y + 1 = 3 by cases abs_cases y <;> omega]; exact e3 hb
      · rw [show y + 1 = 3 by cases abs_cases y <;> omega]
    have ed : cl t x (y - 1) = if -2 ≤ y - 1 then predR (t % 6) x (y - 1)
        else if -2 ≤ x then predR (t % 6) (-3) x else cl t x 3 := by
      split_ifs with ha hb
      · exact H x (y - 1) (by omega) h2 (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)
      · rw [show y - 1 = -3 by cases abs_cases y <;> omega, negy]; exact e3 hb
      · rw [show y - 1 = -3 by cases abs_cases y <;> omega, negy]
    have hs := stepAll (t % 6) (Nat.mod_lt _ (by norm_num)) x y h2 hy (cl t x 3)
    unfold stepF at hs
    rw [beq_iff_eq] at hs
    rw [cell_succ, e0, er, el, eu, ed, hs]
    congr 1; omega

theorem phi_all : ∀ t : ℕ, 12 ≤ t → Phi t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact phi_base
  | succ t ht ih => exact phi_step t ht ih


def A (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), if cl n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0

theorem dig (n k : ℕ) (hn : 12 ≤ n) (hk : k ≤ n) :
    cl n ((k : ℤ) - n) 0 = if k ≤ 8 then SV 11 (12 + (n - 12) % 8) k 0 else predR (n % 6) ((k : ℤ) - n) 0 := by
  split_ifs with h
  · rw [show cl n ((k : ℤ) - n) 0 = nb n k 0 from rfl, per_red n (by omega) k 0 (by omega) (by simp; omega),
      correct 11 _ k 0 (by omega) (by simp; omega)]
  · exact phi_all n hn _ 0 (by omega) (by omega) (by norm_num)

def T1 (r : ℕ) : ℤ := ∑ i ∈ Finset.range 26, if predR (r % 6) ((i : ℤ) - 25) 0 then (10 : ℤ) ^ (25 - i) else 0

def T2 (r : ℕ) : ℤ := ∑ i ∈ Finset.range 2, if predR (r % 6) ((i : ℤ) - 1) 0 then (10 : ℤ) ^ (1 - i) else 0

def K (r : ℕ) : ℤ := T1 r - 10 ^ 24 * T2 r

theorem shift (n : ℕ) (hn : 12 ≤ n) : A (n + 24) = 10 ^ 24 * A n + K (n % 24) := by
  unfold A K
  rw [show n + 24 + 1 = (n - 1) + 26 by omega, Finset.sum_range_add, show n + 1 = (n - 1) + 2 by omega,
    Finset.sum_range_add]
  have hh : ∑ k ∈ Finset.range (n - 1), (if cl (n + 24) ((k : ℤ) - ((n + 24 : ℕ) : ℤ)) 0 then (10 : ℤ) ^ (n + 24 - k) else 0) =
      10 ^ 24 * ∑ k ∈ Finset.range (n - 1), (if cl n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [dig (n + 24) k (by omega) (by omega), dig n k hn (by omega), show (n + 24 - 12) % 8 = (n - 12) % 8 by omega,
      show (n + 24) % 6 = n % 6 by omega, predR_mid _ ((k : ℤ) - ((n + 24 : ℕ) : ℤ)) ((k : ℤ) - n) (by push_cast; omega) (by omega) (by push_cast; omega),
      show n + 24 - k = 24 + (n - k) by omega, pow_add]
    split_ifs <;> simp
  have h1 : ∑ i ∈ Finset.range 26, (if cl (n + 24) (((n - 1 + i : ℕ) : ℤ) - ((n + 24 : ℕ) : ℤ)) 0 then (10 : ℤ) ^ (n + 24 - (n - 1 + i)) else 0) =
      T1 (n % 24) := by
    unfold T1
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [dig (n + 24) (n - 1 + i) (by omega) (by omega), if_neg (show ¬ (n - 1 + i ≤ 8) by omega),
      show (n + 24) % 6 = n % 24 % 6 by omega,
      show ((n - 1 + i : ℕ) : ℤ) - ((n + 24 : ℕ) : ℤ) = (i : ℤ) - 25 by push_cast; omega,
      show n + 24 - (n - 1 + i) = 25 - i by omega]
  have h2 : ∑ i ∈ Finset.range 2, (if cl n (((n - 1 + i : ℕ) : ℤ) - (n : ℤ)) 0 then (10 : ℤ) ^ (n - (n - 1 + i)) else 0) =
      T2 (n % 24) := by
    unfold T2
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [dig n (n - 1 + i) hn (by omega), if_neg (show ¬ (n - 1 + i ≤ 8) by omega),
      show n % 6 = n % 24 % 6 by omega,
      show ((n - 1 + i : ℕ) : ℤ) - (n : ℤ) = (i : ℤ) - 1 by push_cast; omega,
      show n - (n - 1 + i) = 1 - i by omega]
  rw [hh, h1, h2]; ring

def aD (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1),
  if (if k ≤ 8 then SV 11 (12 + (n - 12) % 8) k 0 else predR (n % 6) ((k : ℤ) - n) 0) then (10 : ℤ) ^ (n - k) else 0

theorem A_aD (n : ℕ) (hn : 12 ≤ n) : A n = aD n := by
  unfold A aD
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [dig n k hn (by omega)]

def awZ (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), if ((Wst 16 n).getD 16 0).testBit k then (10 : ℤ) ^ (n - k) else 0

theorem A_aw (n : ℕ) (hn : n ≤ 16) : A n = awZ n := by
  unfold A awZ
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [show cl n ((k : ℤ) - n) 0 = nb n k 0 from rfl, correct 16 n k 0 (by omega) (by simp; omega)]
  unfold SV
  rw [show ((0 : ℤ) + ((16 : ℕ) : ℤ)).toNat = 16 from rfl, Int.toNat_natCast]


def av (n : ℕ) : ℤ := if n < 12 then awZ n else aD n

theorem A_av (n : ℕ) : A n = av n := by
  unfold av
  split_ifs with h
  · exact A_aw n (by omega)
  · exact A_aD n (by omega)

def Kl : List ℤ := [1010101010101010101010100, 11101010111010101110101, -9989898989898989898989889, 1011101010111010101110100, 10101010101010101010101, -9988898989888989898889889, 1010101010101010101010100, 11101010111010101110101, -9989898989898989898989889, 1011101010111010101110100, 10101010101010101010101, -9988898989888989898889889, 1010101010101010101010100, 11101010111010101110101, -9989898989898989898989889, 1011101010111010101110100, 10101010101010101010101, -9988898989888989898889889, 1010101010101010101010100, 11101010111010101110101, -9989898989898989898989889, 1011101010111010101110100, 10101010101010101010101, -9988898989888989898889889]

theorem Kqc0 : ((List.range 6).all fun i => K (i + 0) == Kl.getD (i + 0) 0) = true := by decide +kernel

theorem Kqc1 : ((List.range 6).all fun i => K (i + 6) == Kl.getD (i + 6) 0) = true := by decide +kernel

theorem Kqc2 : ((List.range 6).all fun i => K (i + 12) == Kl.getD (i + 12) 0) = true := by decide +kernel

theorem Kqc3 : ((List.range 6).all fun i => K (i + 18) == Kl.getD (i + 18) 0) = true := by decide +kernel

theorem Kq_eq (r : ℕ) (hr : r < 24) : K r = Kl.getD r 0 := by
  by_cases c0 : r < 6
  · have h := Kqc0; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 0) (by omega); rwa [show r - 0 + 0 = r by omega] at this
  by_cases c1 : r < 12
  · have h := Kqc1; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 6) (by omega); rwa [show r - 6 + 6 = r by omega] at this
  by_cases c2 : r < 18
  · have h := Kqc2; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 12) (by omega); rwa [show r - 12 + 12 = r by omega] at this
  by_cases c3 : r < 24
  · have h := Kqc3; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 18) (by omega); rwa [show r - 18 + 18 = r by omega] at this
  omega

def Al : List ℤ := [1, 1, 111, 100, 11101, 10111, 1110100, 1010101, 111010111, 101110100, 11101010101, 10101110111, 1110101010100, 1011101110101, 111010101010111, 101011101110100, 11101010101010101, 10111010101110111, 1110101010101010100, 1010111010101110101, 111010101010101010111, 101110111010101110100, 11101010101010101010101, 10101110111010101110111, 1110101010101010101010100, 1011101010111010101110101, 111010101010101010101010111, 101011101010111010101110100, 11101010101010101010101010101, 10111011101010111010101110111, 1110101010101010101010101010100, 1010111011101010111010101110101, 111010101010101010101010101010111, 101110101011101010111010101110100, 11101010101010101010101010101010101, 10101110101011101010111010101110111, 1110101010101010101010101010101010100, 1011101110101011101010111010101110101, 111010101010101010101010101010101010111, 101011101110101011101010111010101110100, 11101010101010101010101010101010101010101, 10111010101110101011101010111010101110111, 1110101010101010101010101010101010101010100, 1010111010101110101011101010111010101110101, 111010101010101010101010101010101010101010111, 101110111010101110101011101010111010101110100, 11101010101010101010101010101010101010101010101, 10101110111010101110101011101010111010101110111]

theorem Aqc0 : ((List.range 5).all fun i => av (i + 0) == Al.getD (i + 0) 0) = true := by decide +kernel

theorem Aqc1 : ((List.range 5).all fun i => av (i + 5) == Al.getD (i + 5) 0) = true := by decide +kernel

theorem Aqc2 : ((List.range 5).all fun i => av (i + 10) == Al.getD (i + 10) 0) = true := by decide +kernel

theorem Aqc3 : ((List.range 5).all fun i => av (i + 15) == Al.getD (i + 15) 0) = true := by decide +kernel

theorem Aqc4 : ((List.range 5).all fun i => av (i + 20) == Al.getD (i + 20) 0) = true := by decide +kernel

theorem Aqc5 : ((List.range 5).all fun i => av (i + 25) == Al.getD (i + 25) 0) = true := by decide +kernel

theorem Aqc6 : ((List.range 5).all fun i => av (i + 30) == Al.getD (i + 30) 0) = true := by decide +kernel

theorem Aqc7 : ((List.range 5).all fun i => av (i + 35) == Al.getD (i + 35) 0) = true := by decide +kernel

theorem Aqc8 : ((List.range 5).all fun i => av (i + 40) == Al.getD (i + 40) 0) = true := by decide +kernel

theorem Aqc9 : ((List.range 3).all fun i => av (i + 45) == Al.getD (i + 45) 0) = true := by decide +kernel

theorem Aq_eq (r : ℕ) (hr : r < 48) : av r = Al.getD r 0 := by
  by_cases c0 : r < 5
  · have h := Aqc0; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 0) (by omega); rwa [show r - 0 + 0 = r by omega] at this
  by_cases c1 : r < 10
  · have h := Aqc1; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 5) (by omega); rwa [show r - 5 + 5 = r by omega] at this
  by_cases c2 : r < 15
  · have h := Aqc2; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 10) (by omega); rwa [show r - 10 + 10 = r by omega] at this
  by_cases c3 : r < 20
  · have h := Aqc3; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 15) (by omega); rwa [show r - 15 + 15 = r by omega] at this
  by_cases c4 : r < 25
  · have h := Aqc4; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 20) (by omega); rwa [show r - 20 + 20 = r by omega] at this
  by_cases c5 : r < 30
  · have h := Aqc5; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 25) (by omega); rwa [show r - 25 + 25 = r by omega] at this
  by_cases c6 : r < 35
  · have h := Aqc6; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 30) (by omega); rwa [show r - 30 + 30 = r by omega] at this
  by_cases c7 : r < 40
  · have h := Aqc7; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 35) (by omega); rwa [show r - 35 + 35 = r by omega] at this
  by_cases c8 : r < 45
  · have h := Aqc8; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 40) (by omega); rwa [show r - 40 + 40 = r by omega] at this
  by_cases c9 : r < 48
  · have h := Aqc9; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 45) (by omega); rwa [show r - 45 + 45 = r by omega] at this
  omega

theorem A_Al (n : ℕ) (hn : n < 48) : A n = Al.getD n 0 := by rw [A_av]; exact Aq_eq n hn

def Lz0 (n : ℕ) : ℤ := A n - (-1) * A (n - 1) - (1) * A (n - 3) - (1) * A (n - 4) - (100000000) * A (n - 8) - (100000000) * A (n - 9) - (-100000000) * A (n - 11) - (-100000000) * A (n - 12)

def Lc0 (r : ℕ) : ℤ := Kl.getD r 0 - (-1) * Kl.getD ((r + 23) % 24) 0 - (1) * Kl.getD ((r + 21) % 24) 0 - (1) * Kl.getD ((r + 20) % 24) 0 - (100000000) * Kl.getD ((r + 16) % 24) 0 - (100000000) * Kl.getD ((r + 15) % 24) 0 - (-100000000) * Kl.getD ((r + 13) % 24) 0 - (-100000000) * Kl.getD ((r + 12) % 24) 0

theorem Lc0_t : ((List.range 24).all fun r => Lc0 r == 0) = true := by decide +kernel

def sm0 (i : ℕ) : ℤ := Al.getD (i + 20) 0 - (-1) * Al.getD (i + 20 - 1) 0 - (1) * Al.getD (i + 20 - 3) 0 - (1) * Al.getD (i + 20 - 4) 0 - (100000000) * Al.getD (i + 20 - 8) 0 - (100000000) * Al.getD (i + 20 - 9) 0 - (-100000000) * Al.getD (i + 20 - 11) 0 - (-100000000) * Al.getD (i + 20 - 12) 0

theorem sm0_t : ((List.range 28).all fun i => sm0 i == 0) = true := by decide +kernel

theorem Lz0_zero : ∀ n : ℕ, 20 ≤ n → Lz0 n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : n < 48
    · have hs := sm0_t
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hs
      have := hs (n - 20) (by omega)
      unfold sm0 at this
      unfold Lz0
      rw [show n - 20 + 20 = n by omega] at this
      rw [A_Al n (by omega), A_Al (n - 1) (by omega), A_Al (n - 3) (by omega), A_Al (n - 4) (by omega), A_Al (n - 8) (by omega), A_Al (n - 9) (by omega), A_Al (n - 11) (by omega), A_Al (n - 12) (by omega)]
      exact this
    · have hp := ih (n - 24) (by omega) (by omega)
      have hl := Lc0_t
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hl
      have hL := hl ((n - 24) % 24) (Nat.mod_lt _ (by norm_num))
      unfold Lc0 at hL
      rw [← Kq_eq _ (Nat.mod_lt _ (by norm_num)), ← Kq_eq _ (Nat.mod_lt _ (by norm_num)), ← Kq_eq _ (Nat.mod_lt _ (by norm_num)), ← Kq_eq _ (Nat.mod_lt _ (by norm_num)), ← Kq_eq _ (Nat.mod_lt _ (by norm_num)), ← Kq_eq _ (Nat.mod_lt _ (by norm_num)), ← Kq_eq _ (Nat.mod_lt _ (by norm_num)), ← Kq_eq _ (Nat.mod_lt _ (by norm_num))] at hL
      unfold Lz0 at hp ⊢
      have s0 := shift (n - 24) (by omega)
      have s1 := shift (n - 24 - 1) (by omega)
      have s3 := shift (n - 24 - 3) (by omega)
      have s4 := shift (n - 24 - 4) (by omega)
      have s8 := shift (n - 24 - 8) (by omega)
      have s9 := shift (n - 24 - 9) (by omega)
      have s11 := shift (n - 24 - 11) (by omega)
      have s12 := shift (n - 24 - 12) (by omega)
      rw [show n - 24 + 24 = n by omega] at s0
      rw [show n - 24 - 1 + 24 = n - 1 by omega, show (n - 24 - 1) % 24 = ((n - 24) % 24 + 23) % 24 by omega] at s1
      rw [show n - 24 - 3 + 24 = n - 3 by omega, show (n - 24 - 3) % 24 = ((n - 24) % 24 + 21) % 24 by omega] at s3
      rw [show n - 24 - 4 + 24 = n - 4 by omega, show (n - 24 - 4) % 24 = ((n - 24) % 24 + 20) % 24 by omega] at s4
      rw [show n - 24 - 8 + 24 = n - 8 by omega, show (n - 24 - 8) % 24 = ((n - 24) % 24 + 16) % 24 by omega] at s8
      rw [show n - 24 - 9 + 24 = n - 9 by omega, show (n - 24 - 9) % 24 = ((n - 24) % 24 + 15) % 24 by omega] at s9
      rw [show n - 24 - 11 + 24 = n - 11 by omega, show (n - 24 - 11) % 24 = ((n - 24) % 24 + 13) % 24 by omega] at s11
      rw [show n - 24 - 12 + 24 = n - 12 by omega, show (n - 24 - 12) % 24 = ((n - 24) % 24 + 12) % 24 by omega] at s12
      rw [s0, s1, s3, s4, s8, s9, s11, s12]
      linear_combination 10 ^ 24 * hp + hL

theorem bridge : ∀ t : ℕ, ∀ i j : ℤ, cell 395 t i j = cl t i j := by
  intro t
  induction t with
  | zero => intro i j; rfl
  | succ t ih =>
    intro i j
    show Nat.testBit 395 ((cell 395 t i j).toNat + 2 * ((cell 395 t (i + 1) j).toNat +
      (cell 395 t (i - 1) j).toNat + (cell 395 t i (j + 1)).toNat + (cell 395 t i (j - 1)).toNat)) = cl (t + 1) i j
    rw [ih, ih, ih, ih, ih]; rfl

theorem a_eq (n : ℕ) : a n = A n := by
  unfold a A; simp only [bridge]

theorem rec0 (n : ℕ) (hn : 20 ≤ n) : (a n : ℚ) = -a (n - 1) + a (n - 3) + a (n - 4) + 100000000 * a (n - 8) + 100000000 * a (n - 9) - 100000000 * a (n - 11) - 100000000 * a (n - 12) := by
  have h := Lz0_zero n (by omega)
  unfold Lz0 at h
  have h' := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at h'
  simp only [a_eq]
  push_cast
  linarith

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (100000000 * X ^ 12 + 100000000 * X ^ 11 - 100000000 * X ^ 9 - 100000000 * X ^ 8 - X ^ 4 - X ^ 3 + X + 1 : PowerSeries ℚ) = -1000000000 * X ^ 19 - 1000000000 * X ^ 18 - 1000000000 * X ^ 17 + 1000000000 * X ^ 15 + 90000000 * X ^ 12 + 90100000 * X ^ 11 + 11000000 * X ^ 9 + 11999000 * X ^ 8 + 2109000 * X ^ 7 + 1120000 * X ^ 6 + 21100 * X ^ 5 + 11199 * X ^ 4 + 210 * X ^ 3 + 112 * X ^ 2 + 2 * X + 1 := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, f = fun n => (a n : ℚ) := ⟨_, rfl⟩
  have g0 : f 0 = 1 := by simp only [hf, a_eq, A_Al 0 (by norm_num)]; norm_num [Al]
  have g1 : f 1 = 1 := by simp only [hf, a_eq, A_Al 1 (by norm_num)]; norm_num [Al]
  have g2 : f 2 = 111 := by simp only [hf, a_eq, A_Al 2 (by norm_num)]; norm_num [Al]
  have g3 : f 3 = 100 := by simp only [hf, a_eq, A_Al 3 (by norm_num)]; norm_num [Al]
  have g4 : f 4 = 11101 := by simp only [hf, a_eq, A_Al 4 (by norm_num)]; norm_num [Al]
  have g5 : f 5 = 10111 := by simp only [hf, a_eq, A_Al 5 (by norm_num)]; norm_num [Al]
  have g6 : f 6 = 1110100 := by simp only [hf, a_eq, A_Al 6 (by norm_num)]; norm_num [Al]
  have g7 : f 7 = 1010101 := by simp only [hf, a_eq, A_Al 7 (by norm_num)]; norm_num [Al]
  have g8 : f 8 = 111010111 := by simp only [hf, a_eq, A_Al 8 (by norm_num)]; norm_num [Al]
  have g9 : f 9 = 101110100 := by simp only [hf, a_eq, A_Al 9 (by norm_num)]; norm_num [Al]
  have g10 : f 10 = 11101010101 := by simp only [hf, a_eq, A_Al 10 (by norm_num)]; norm_num [Al]
  have g11 : f 11 = 10101110111 := by simp only [hf, a_eq, A_Al 11 (by norm_num)]; norm_num [Al]
  have g12 : f 12 = 1110101010100 := by simp only [hf, a_eq, A_Al 12 (by norm_num)]; norm_num [Al]
  have g13 : f 13 = 1011101110101 := by simp only [hf, a_eq, A_Al 13 (by norm_num)]; norm_num [Al]
  have g14 : f 14 = 111010101010111 := by simp only [hf, a_eq, A_Al 14 (by norm_num)]; norm_num [Al]
  have g15 : f 15 = 101011101110100 := by simp only [hf, a_eq, A_Al 15 (by norm_num)]; norm_num [Al]
  have g16 : f 16 = 11101010101010101 := by simp only [hf, a_eq, A_Al 16 (by norm_num)]; norm_num [Al]
  have g17 : f 17 = 10111010101110111 := by simp only [hf, a_eq, A_Al 17 (by norm_num)]; norm_num [Al]
  have g18 : f 18 = 1110101010101010100 := by simp only [hf, a_eq, A_Al 18 (by norm_num)]; norm_num [Al]
  have g19 : f 19 = 1010111010101110101 := by simp only [hf, a_eq, A_Al 19 (by norm_num)]; norm_num [Al]
  have grec : ∀ k, 20 ≤ k → f k = (-1) * f (k - 1) + (1) * f (k - 3) + (1) * f (k - 4) + (100000000) * f (k - 8) + (100000000) * f (k - 9) + (-100000000) * f (k - 11) + (-100000000) * f (k - 12) := by
    intro k hk; have h := Lz0_zero k hk; unfold Lz0 at h
    have h' := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at h'
    simp only [hf, a_eq]
    push_cast
    linarith
  rw [← hf]
  clear hf
  set F : PowerSeries ℚ := PowerSeries.mk f with hF
  have hD : F * (100000000 * X ^ 12 + 100000000 * X ^ 11 - 100000000 * X ^ 9 - 100000000 * X ^ 8 - X ^ 4 - X ^ 3 + X + 1 : PowerSeries ℚ) = C (1 : ℚ) * (F * X ^ 0) + C (1 : ℚ) * (F * X ^ 1) - C (1 : ℚ) * (F * X ^ 3) - C (1 : ℚ) * (F * X ^ 4) - C (100000000 : ℚ) * (F * X ^ 8) - C (100000000 : ℚ) * (F * X ^ 9) + C (100000000 : ℚ) * (F * X ^ 11) + C (100000000 : ℚ) * (F * X ^ 12) := by
    simp only [map_ofNat, map_one]; ring
  have hN : (-1000000000 * X ^ 19 - 1000000000 * X ^ 18 - 1000000000 * X ^ 17 + 1000000000 * X ^ 15 + 90000000 * X ^ 12 + 90100000 * X ^ 11 + 11000000 * X ^ 9 + 11999000 * X ^ 8 + 2109000 * X ^ 7 + 1120000 * X ^ 6 + 21100 * X ^ 5 + 11199 * X ^ 4 + 210 * X ^ 3 + 112 * X ^ 2 + 2 * X + 1 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (2 : ℚ) * X ^ 1 + C (112 : ℚ) * X ^ 2 + C (210 : ℚ) * X ^ 3 + C (11199 : ℚ) * X ^ 4 + C (21100 : ℚ) * X ^ 5 + C (1120000 : ℚ) * X ^ 6 + C (2109000 : ℚ) * X ^ 7 + C (11999000 : ℚ) * X ^ 8 + C (11000000 : ℚ) * X ^ 9 + C (90100000 : ℚ) * X ^ 11 + C (90000000 : ℚ) * X ^ 12 + C (1000000000 : ℚ) * X ^ 15 - C (1000000000 : ℚ) * X ^ 17 - C (1000000000 : ℚ) * X ^ 18 - C (1000000000 : ℚ) * X ^ 19 := by
    simp only [map_ofNat, map_one]; ring
  rw [hD, hN]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hF, coeff_mk, coeff_C, Nat.sub_zero]
  rcases Nat.lt_or_ge k 20 with h | h
  · interval_cases k <;> simp [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19] <;> norm_num
  · simp only [show 0 ≤ k by omega, show 1 ≤ k by omega, show 2 ≤ k by omega, show 3 ≤ k by omega, show 4 ≤ k by omega, show 5 ≤ k by omega, show 6 ≤ k by omega, show 7 ≤ k by omega, show 8 ≤ k by omega, show 9 ≤ k by omega, show 11 ≤ k by omega, show 12 ≤ k by omega, show 15 ≤ k by omega, show 17 ≤ k by omega, show 18 ≤ k by omega, show 19 ≤ k by omega, show k ≠ 0 by omega, show k - 1 ≠ 0 by omega, show k - 2 ≠ 0 by omega, show k - 3 ≠ 0 by omega, show k - 4 ≠ 0 by omega, show k - 5 ≠ 0 by omega, show k - 6 ≠ 0 by omega, show k - 7 ≠ 0 by omega, show k - 8 ≠ 0 by omega, show k - 9 ≠ 0 by omega, show k - 11 ≠ 0 by omega, show k - 12 ≠ 0 by omega, show k - 15 ≠ 0 by omega, show k - 17 ≠ 0 by omega, show k - 18 ≠ 0 by omega, show k - 19 ≠ 0 by omega, if_true, if_false]
    linear_combination (1) * grec k h

end OMA.Helpers_oeis_a281748

open OMA.Helpers_oeis_a281748 in
theorem OMA.solution : type_of% @OMA.S_oeis_a281748.main := ⟨rec0, gf⟩
