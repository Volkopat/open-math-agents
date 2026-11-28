import OMAStatements.S_oeis_a283588

-- Problem: A283588: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 654'
-- Solfanbtc established the Rule 654 moving-front invariant for A283586 in
-- Left to Solve PR 28068. The recurrence and generating function here are its
-- radix-two consequence. This implementation uses independently simulated
-- bit masks and a certified finite reduction of the space-time update.

open OMA.S_oeis_a283588

namespace Rule654

def update (c e w n s : Bool) : Bool :=
  (654 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat))

theorem cell_step (t : ℕ) (x y : ℤ) :
    cell 654 (t + 1) x y =
      update (cell 654 t x y) (cell 654 t (x + 1) y) (cell 654 t (x - 1) y)
        (cell 654 t x (y + 1)) (cell 654 t x (y - 1)) := rfl

theorem outside (t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| + |y|) :
    cell 654 t x y = false := by
  induction t generalizing x y with
  | zero =>
    simp only [cell, decide_eq_false_iff_not]
    rintro ⟨rfl, rfl⟩
    simp at h
  | succ t ih =>
    have hx₁ : |x| ≤ |x + 1| + 1 := by simpa using (abs_sub (x + 1) (1 : ℤ))
    have hx₂ : |x| ≤ |x - 1| + 1 := by simpa using (abs_add_le (x - 1) (1 : ℤ))
    have hy₁ : |y| ≤ |y + 1| + 1 := by simpa using (abs_sub (y + 1) (1 : ℤ))
    have hy₂ : |y| ≤ |y - 1| + 1 := by simpa using (abs_add_le (y - 1) (1 : ℤ))
    rw [cell_step, ih x y (by omega), ih (x + 1) y (by omega),
      ih (x - 1) y (by omega), ih x (y + 1) (by omega), ih x (y - 1) (by omega)]
    rfl

theorem reflectX (t : ℕ) (x y : ℤ) : cell 654 t (-x) y = cell 654 t x y := by
  induction t generalizing x y with
  | zero => simp [cell]
  | succ t ih =>
    rw [cell_step, cell_step, show -x + 1 = -(x - 1) by omega,
      show -x - 1 = -(x + 1) by omega, ih, ih, ih, ih, ih]
    unfold update
    congr 1; ring

theorem reflectY (t : ℕ) (x y : ℤ) : cell 654 t x (-y) = cell 654 t x y := by
  induction t generalizing x y with
  | zero => simp [cell]
  | succ t ih =>
    rw [cell_step, cell_step, show -y + 1 = -(y - 1) by omega,
      show -y - 1 = -(y + 1) by omega, ih, ih, ih, ih, ih]
    unfold update
    congr 1; ring

/-! ### Fast bit-packed simulation for t ≤ 20 -/

def packBits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => packBits f n + if f n then 2 ^ n else 0

theorem packBits_lt (f : ℕ → Bool) (n : ℕ) : packBits f n < 2 ^ n := by
  induction n with
  | zero => simp [packBits]
  | succ n ih =>
    simp only [packBits, pow_succ]
    cases f n <;> simp <;> omega

theorem testBit_packBits (f : ℕ → Bool) (n k : ℕ) :
    (packBits f n).testBit k = (decide (k < n) && f k) := by
  induction n with
  | zero => simp [packBits]
  | succ n ih =>
    simp only [packBits]
    by_cases hfn : f n
    · have hlt := packBits_lt f n
      have hadd : packBits f n + 2 ^ n = 2 ^ n + packBits f n := Nat.add_comm _ _
      rw [if_pos hfn]
      rcases lt_trichotomy k n with hk | rfl | hk
      · rw [hadd, Nat.testBit_two_pow_add_gt hk, ih]
        simp [hk, show k < n + 1 by omega]
      · rw [hadd, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        simp [hfn]
      · have hk1 : ¬ (k < n + 1) := by omega
        have hk2 : ¬ (k < n) := by omega
        have hsum : packBits f n + 2 ^ n < 2 ^ k := by
          have h1 : 2 ^ (n + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
          rw [pow_succ] at h1
          omega
        rw [Nat.testBit_lt_two_pow hsum]
        simp [hk1]
    · rw [if_neg hfn, Nat.add_zero, ih]
      by_cases hk : k = n
      · subst hk; simp [show f k = false from Bool.eq_false_iff.mpr hfn]
      · have : (k < n + 1) ↔ (k < n) := by omega
        simp [this]

def simCell (g : List ℕ) (x y : ℕ) : Bool :=
  (g.getD y 0).testBit x

def simStep (g : List ℕ) : List ℕ :=
  List.ofFn fun y : Fin 21 =>
    packBits (fun x =>
      let c := simCell g x y.1
      let e := simCell g (x + 1) y.1
      let w := simCell g (if x = 0 then 1 else x - 1) y.1
      let n := simCell g x (y.1 + 1)
      let s := simCell g x (if y.1 = 0 then 1 else y.1 - 1)
      update c e w n s) 21

def sim : ℕ → List ℕ
  | 0 => List.ofFn fun y : Fin 21 => if y.1 = 0 then 1 else 0
  | t + 1 => simStep (sim t)

theorem cell_eq_simCell (t : ℕ) (ht : t ≤ 20) (x y : ℕ) (hx : x ≤ 20) (hy : y ≤ 20) :
    cell 654 t (x : ℤ) (y : ℤ) = simCell (sim t) x y := by
  induction t generalizing x y with
  | zero =>
    simp only [cell, sim, simCell, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    have hy21 : y < 21 := by omega
    simp only [hy21, ↓reduceDIte]
    rcases eq_or_ne y 0 with rfl | hy0
    · rcases eq_or_ne x 0 with rfl | hx0
      · simp
      · simp [hx0, Bool.eq_false_iff, Nat.testBit_one_eq_true_iff_self_eq_zero]
    · simp [hy0]
  | succ t ih =>
    have ht20 : t ≤ 20 := by omega
    rw [cell_step]
    have hc : cell 654 t (x : ℤ) (y : ℤ) = simCell (sim t) x y := ih ht20 x y hx hy
    have he : cell 654 t ((x : ℤ) + 1) (y : ℤ) = simCell (sim t) (x + 1) y := by
      by_cases hx20 : x = 20
      · subst hx20
        change cell 654 t 21 (y : ℤ) = simCell (sim t) 21 y
        have h1 : cell 654 t 21 (y : ℤ) = false := by
          apply outside
          have := abs_nonneg (y : ℤ)
          norm_num
          omega
        have h2 : simCell (sim t) 21 y = false := by
          cases t with
          | zero =>
            simp only [sim, simCell, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            split_ifs <;> decide
          | succ t' =>
            simp only [sim, simStep, simCell, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            have hy21 : y < 21 := by omega
            simp [hy21, testBit_packBits]
        rw [h1, h2]
      · exact_mod_cast ih ht20 (x + 1) y (by omega) hy
    have hw : cell 654 t ((x : ℤ) - 1) (y : ℤ) = simCell (sim t) (if x = 0 then 1 else x - 1) y := by
      by_cases hx0 : x = 0
      · subst hx0
        change cell 654 t (-1) (y : ℤ) = simCell (sim t) 1 y
        rw [reflectX]
        exact ih ht20 1 y (by omega) hy
      · simp only [hx0, ↓reduceIte]
        rw [show (x : ℤ) - 1 = ((x - 1 : ℕ) : ℤ) by omega]
        exact ih ht20 (x - 1) y (by omega) hy
    have hn : cell 654 t (x : ℤ) ((y : ℤ) + 1) = simCell (sim t) x (y + 1) := by
      by_cases hy20 : y = 20
      · subst hy20
        change cell 654 t (x : ℤ) 21 = simCell (sim t) x 21
        have h1 : cell 654 t (x : ℤ) 21 = false := by
          apply outside
          have := abs_nonneg (x : ℤ)
          norm_num
          omega
        have h2 : simCell (sim t) x 21 = false := by
          simp only [simCell, List.getD_eq_getElem?_getD]
          have hlen : (sim t).length = 21 := by cases t <;> simp [sim, simStep]
          have hnone : (sim t)[21]? = none := List.getElem?_eq_none (by omega)
          simp [hnone]
        rw [h1, h2]
      · exact_mod_cast ih ht20 x (y + 1) hx (by omega)
    have hs : cell 654 t (x : ℤ) ((y : ℤ) - 1) = simCell (sim t) x (if y = 0 then 1 else y - 1) := by
      by_cases hy0 : y = 0
      · subst hy0
        change cell 654 t (x : ℤ) (-1) = simCell (sim t) x 1
        rw [reflectY]
        exact ih ht20 x 1 hx (by omega)
      · simp only [hy0, ↓reduceIte]
        rw [show (y : ℤ) - 1 = ((y - 1 : ℕ) : ℤ) by omega]
        exact ih ht20 x (y - 1) hx (by omega)
    rw [hc, he, hw, hn, hs]
    simp only [sim, simStep, simCell, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    have hy21 : y < 21 := by omega
    have hx21 : x < 21 := by omega
    simp [hy21, hx21, testBit_packBits]

-- Precomputed rows. Lean verifies every transition from the single live cell.
def seedGrid : ℕ → List ℕ
  | 0 => [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => [3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [7, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => [13, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => [29, 4, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 5 => [53, 20, 3, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 6 => [113, 20, 18, 0, 7, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 7 => [219, 69, 58, 21, 13, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 8 => [475, 69, 58, 21, 13, 4, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 9 => [859, 325, 58, 21, 13, 4, 3, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 10 => [1819, 325, 314, 21, 13, 4, 2, 0, 7, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 11 => [3515, 1093, 954, 277, 13, 5, 2, 5, 13, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 12 => [7595, 1093, 954, 277, 268, 5, 2, 5, 29, 4, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 13 => [13739, 5205, 954, 21, 910, 261, 2, 21, 53, 20, 3, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0]
  | 14 => [29099, 5205, 4794, 21, 1998, 261, 274, 21, 113, 20, 18, 0, 7, 1, 1, 0, 0, 0, 0, 0, 0]
  | 15 => [56235, 17749, 15034, 5461, 3438, 1109, 954, 325, 219, 69, 58, 21, 13, 4, 3, 1, 0, 0, 0, 0, 0]
  | 16 => [121771, 17749, 15034, 5461, 3438, 1109, 954, 325, 219, 69, 58, 21, 13, 4, 3, 1, 1, 0, 0, 0, 0]
  | 17 => [220075, 83285, 15034, 5461, 3438, 1109, 954, 325, 219, 69, 58, 21, 13, 4, 3, 0, 3, 1, 0, 0, 0]
  | 18 => [465835, 83285, 80570, 5461, 3438, 1109, 954, 325, 219, 69, 58, 21, 13, 4, 2, 0, 7, 1, 1, 0, 0]
  | 19 => [900011, 279893, 244410, 70997, 3438, 1109, 954, 325, 219, 69, 58, 21, 13, 5, 2, 5, 13, 4, 3, 1, 0]
  | 20 => [1944491, 279893, 244410, 70997, 68974, 1109, 954, 325, 219, 69, 58, 21, 12, 5, 2, 5, 29, 4, 3, 1, 1]
  | _ => []

theorem seedGrid_step : ∀ t : Fin 20, simStep (seedGrid t.1) = seedGrid (t.1 + 1) := by
  intro t
  fin_cases t <;> decide +kernel

theorem sim_eq_seedGrid (t : ℕ) (ht : t ≤ 20) : sim t = seedGrid t := by
  induction t with
  | zero => decide +kernel
  | succ t ih =>
    rw [sim, ih (by omega)]
    exact seedGrid_step ⟨t, by omega⟩

/-! ### Exact invariant for t ≥ 20 -/

def tab03 (m y k : ℕ) : Bool :=
  let mask : ℕ := match y, k with
    | 0, 0 => 255 | 0, 1 => 255 | 0, 2 => 85  | 0, 3 => 170 | 0, 4 => 153
    | 0, 5 => 51  | 0, 6 => 238 | 0, 7 => 221 | 0, 8 => 171
    | 1, 0 => 0   | 1, 1 => 170 | 1, 2 => 85  | 1, 3 => 34  | 1, 4 => 68
    | 1, 5 => 136 | 1, 6 => 17  | 1, 7 => 162 | 1, 8 => 69
    | 2, 0 => 0   | 2, 1 => 0   | 2, 2 => 204 | 2, 3 => 153 | 2, 4 => 187
    | 2, 5 => 119 | 2, 6 => 174 | 2, 7 => 93  | 2, 8 => 186
    | 3, 0 => 0   | 3, 1 => 0   | 3, 2 => 0   | 3, 3 => 136 | 3, 4 => 17
    | 3, 5 => 130 | 3, 6 => 5   | 3, 7 => 138 | 3, 8 => 21
    | _, _ => 0
  mask.testBit m

def p03 (t x y : ℕ) : Bool :=
  if t - x ≤ 8 then tab03 (t % 8) y (t - x)
  else match y with
    | 0 => (171 : ℕ).testBit (x % 8)
    | 1 => decide (x % 2 = 0)
    | 2 => (186 : ℕ).testBit (x % 8)
    | _ => decide (x % 2 = 0)

def coneMask (y k : ℕ) : ℕ :=
  match y, k with
  | 4, 4 => 61680  | 4, 5 => 57825  | 4, 6 => 25443  | 4, 7 => 50886  | 4, 8 => 19789
  | 4, 9 => 39578  | 4, 10 => 46517 | 4, 11 => 27499 | 4, 12 => 59094 | 4, 13 => 52653
  | 4, 14 => 47963 | 4, 15 => 30391 | 4, 16 => 60782 | 4, 17 => 56029 | 4, 18 => 46523
  | 4, 19 => 27511 | 4, 20 => 55022
  | 5, 5 => 41120  | 5, 6 => 16705  | 5, 7 => 514    | 5, 8 => 1028   | 5, 9 => 34952
  | 5, 10 => 4369  | 5, 11 => 43554 | 5, 12 => 21573 | 5, 13 => 43146 | 5, 14 => 20757
  | 5, 15 => 41514 | 5, 16 => 17493 | 5, 17 => 34986 | 5, 18 => 4437  | 5, 19 => 41642
  | 5, 20 => 17749
  | 6, 6 => 49344  | 6, 7 => 33153  | 6, 8 => 33667  | 6, 9 => 1799   | 6, 10 => 51726
  | 6, 11 => 37917 | 6, 12 => 43067 | 6, 13 => 20599 | 6, 14 => 41198 | 6, 15 => 16861
  | 6, 16 => 33722 | 6, 17 => 1909  | 6, 18 => 52970 | 6, 19 => 40405
  | 7, 7 => 32896  | 7, 8 => 257    | 7, 9 => 43010  | 7, 10 => 20485 | 7, 11 => 10250
  | 7, 12 => 20500 | 7, 13 => 43048 | 7, 14 => 20561 | 7, 15 => 41122 | 7, 16 => 16709
  | 7, 17 => 41610 | 7, 18 => 17685
  | 8, 8 => 65280  | 8, 9 => 65025  | 8, 10 => 22019 | 8, 11 => 44038 | 8, 12 => 37901
  | 8, 13 => 10267 | 8, 14 => 55350 | 8, 15 => 45165 | 8, 16 => 37083 | 8, 17 => 8631
  | 9, 9 => 43520  | 9, 10 => 21505 | 9, 11 => 8194  | 9, 12 => 16388 | 9, 13 => 34824
  | 9, 14 => 4113  | 9, 15 => 40994 | 9, 16 => 16453
  | 10, 10 => 52224 | 10, 11 => 38913 | 10, 12 => 47107 | 10, 13 => 28679 | 10, 14 => 40974
  | 10, 15 => 16413
  | 11, 11 => 34816 | 11, 12 => 4097 | 11, 13 => 32770 | 11, 14 => 5
  | 12, 12 => 61440 | 12, 13 => 57345
  | _, _ => 0

def inCone (y k : ℕ) : Bool :=
  decide (4 ≤ y ∧ y ≤ k ∧ k ≤ 20 ∧ y + k ≤ 25)

def aliveInfo (y xm : ℕ) : Option (Bool × ℕ) :=
  match y, xm with
  | 4, 0 => some (false, 12) | 4, 1 => some (true, 12) | 4, 2 => some (true, 4)
  | 4, 3 => some (true, 4)   | 4, 4 => some (false, 0) | 4, 5 => some (true, 10)
  | 4, 11 => some (true, 4)  | 4, 12 => some (false, 0) | 4, 13 => some (true, 10)
  | 4, 14 => some (true, 8)  | 4, 15 => some (true, 14)
  | 5, 0 => some (true, 11)  | 5, 1 => some (false, 0) | 5, 2 => some (true, 5)
  | 5, 3 => some (false, 0)  | 5, 4 => some (true, 11) | 5, 5 => some (false, 0)
  | 5, 11 => some (false, 0) | 5, 12 => some (true, 19) | 5, 13 => some (false, 0)
  | 5, 14 => some (true, 9)  | 5, 15 => some (false, 0)
  | 6, 0 => some (false, 10) | 6, 1 => some (true, 6)  | 6, 2 => some (false, 0)
  | 6, 14 => some (false, 0) | 6, 15 => some (true, 8)
  | _, _ => none

def invVal (t x y : ℕ) : Option Bool :=
  if t < x + y then some false
  else if y ≤ 3 then some (p03 t x y)
  else if inCone y (t - x) then some ((coneMask y (t - x)).testBit (t % 16))
  else if y < 7 then
    match aliveInfo y (x % 16) with
    | some (val, k0) => if k0 ≤ min (t - x) 21 then some val else none
    | none => none
  else none

def holds (t : ℕ) : Prop :=
  ∀ x y : ℕ, ∀ b : Bool, invVal t x y = some b → cell 654 t (x : ℤ) (y : ℤ) = b

theorem base_check :
    ∀ x : Fin 21, ∀ y : Fin 21, ∀ b : Bool,
      invVal 20 x.1 y.1 = some b → simCell (sim 20) x.1 y.1 = b := by
  rw [sim_eq_seedGrid 20 (by omega)]
  intro x
  fin_cases x <;> decide +kernel

theorem holds_20 : holds 20 := by
  intro x y b h
  by_cases hxy : 20 < x + y
  · have hinv : invVal 20 x y = some false := by simp [invVal, hxy]
    rw [hinv] at h
    injection h with hb
    subst hb
    apply outside
    rw [abs_of_nonneg (by omega : 0 ≤ (x : ℤ)), abs_of_nonneg (by omega : 0 ≤ (y : ℤ))]
    omega
  · have hx : x ≤ 20 := by omega
    have hy : y ≤ 20 := by omega
    rw [cell_eq_simCell 20 (by omega) x y hx hy]
    exact base_check ⟨x, by omega⟩ ⟨y, by omega⟩ b h

def optOk (o : Option Bool) (v : Bool) : Bool :=
  match o with
  | none => true
  | some w => decide (w = v)

def forced (oc oe ow on os : Option Bool) (b : Bool) : Bool :=
  [false, true].all fun c =>
    [false, true].all fun e =>
      [false, true].all fun w =>
        [false, true].all fun n =>
          [false, true].all fun s =>
            if optOk oc c && optOk oe e && optOk ow w && optOk on n && optOk os s
            then decide (update c e w n s = b)
            else true

theorem forced_sound {c e w n s b : Bool} {oc oe ow on os : Option Bool}
    (hc : ∀ v, oc = some v → c = v)
    (he : ∀ v, oe = some v → e = v)
    (hw : ∀ v, ow = some v → w = v)
    (hn : ∀ v, on = some v → n = v)
    (hs : ∀ v, os = some v → s = v)
    (hf : forced oc oe ow on os b = true) :
    update c e w n s = b := by
  have hok : ∀ (o : Option Bool) (v : Bool), (∀ u, o = some u → v = u) → optOk o v = true := by
    intro o v hv
    cases o with
    | none => rfl
    | some u => simp [optOk, hv u rfl]
  have h1 := hok oc c hc
  have h2 := hok oe e he
  have h3 := hok ow w hw
  have h4 := hok on n hn
  have h5 := hok os s hs
  have bool_mem (v : Bool) : v ∈ [false, true] := by cases v <;> simp
  unfold forced at hf
  have hc' := List.all_eq_true.mp hf c (bool_mem c)
  have he' := List.all_eq_true.mp hc' e (bool_mem e)
  have hw' := List.all_eq_true.mp he' w (bool_mem w)
  have hn' := List.all_eq_true.mp hw' n (bool_mem n)
  have hs' := List.all_eq_true.mp hn' s (bool_mem s)
  simpa [h1, h2, h3, h4, h5] using hs'

theorem step_front_check :
    ∀ m : Fin 16, ∀ k : Fin 21, ∀ y : Fin 13, ∀ b : Bool,
      let t := 32 + m.1
      let x := t + 1 - k.1
      invVal (t + 1) x y.1 = some b →
        forced (invVal t x y.1) (invVal t (x + 1) y.1) (invVal t (x - 1) y.1)
          (invVal t x (y.1 + 1)) (invVal t x (if y.1 = 0 then 1 else y.1 - 1)) b = true := by
  intro m
  fin_cases m <;> decide +kernel

theorem step_zero_base_check :
    ∀ d : Fin 2, ∀ y : Fin 7, ∀ b : Bool,
      let t := 20 + d.1
      invVal (t + 1) 0 y.1 = some b →
        forced (invVal t 0 y.1) (invVal t 1 y.1) (invVal t 1 y.1)
          (invVal t 0 (y.1 + 1)) (invVal t 0 (if y.1 = 0 then 1 else y.1 - 1)) b = true := by
  decide +kernel

theorem step_zero_gt_check :
    ∀ m : Fin 16, ∀ y : Fin 7, ∀ b : Bool,
      let t := 48 + m.1
      invVal (t + 1) 0 y.1 = some b →
        forced (invVal t 0 y.1) (invVal t 1 y.1) (invVal t 1 y.1)
          (invVal t 0 (y.1 + 1)) (invVal t 0 (if y.1 = 0 then 1 else y.1 - 1)) b = true := by
  decide +kernel

theorem step_int_boundary_check :
    ∀ m : Fin 16, ∀ d : Fin 2, ∀ y : Fin 7, ∀ b : Bool,
      let t := 48 + m.1
      let x := t - (20 + d.1)
      invVal (t + 1) x y.1 = some b →
        forced (invVal t x y.1) (invVal t (x + 1) y.1) (invVal t (x - 1) y.1)
          (invVal t x (y.1 + 1)) (invVal t x (if y.1 = 0 then 1 else y.1 - 1)) b = true := by
  intro m
  fin_cases m <;> decide +kernel

theorem step_int_gt_check :
    ∀ m : Fin 16, ∀ xm : Fin 16, ∀ y : Fin 7, ∀ b : Bool,
      let t := 64 + m.1
      let x := 16 + xm.1
      invVal (t + 1) x y.1 = some b →
        forced (invVal t x y.1) (invVal t (x + 1) y.1) (invVal t (x - 1) y.1)
          (invVal t x (y.1 + 1)) (invVal t x (if y.1 = 0 then 1 else y.1 - 1)) b = true := by
  intro m
  fin_cases m <;> decide +kernel

theorem p03_congr {t₁ t₂ x₁ x₂ y : ℕ}
    (ht8 : t₁ % 8 = t₂ % 8) (hx8 : x₁ % 8 = x₂ % 8) (hx2 : x₁ % 2 = x₂ % 2)
    (hk : min (t₁ - x₁) 9 = min (t₂ - x₂) 9) :
    p03 t₁ x₁ y = p03 t₂ x₂ y := by
  unfold p03
  have hle : (t₁ - x₁ ≤ 8) ↔ (t₂ - x₂ ≤ 8) := by omega
  by_cases h1 : t₁ - x₁ ≤ 8
  · have hkeq : t₁ - x₁ = t₂ - x₂ := by omega
    rw [if_pos h1, if_pos (hle.mp h1), ht8, hkeq]
  · have h2 : ¬ t₂ - x₂ ≤ 8 := fun h => h1 (hle.mpr h)
    rw [if_neg h1, if_neg h2]
    rcases y with _ | _ | _ | y <;> simp [hx8, hx2]

theorem invVal_congr {t₁ t₂ x₁ x₂ y : ℕ}
    (ht16 : t₁ % 16 = t₂ % 16) (hx16 : x₁ % 16 = x₂ % 16)
    (hk : min (t₁ - x₁) 21 = min (t₂ - x₂) 21)
    (hlt1 : (t₁ < x₁ + y) ↔ (t₂ < x₂ + y)) :
    invVal t₁ x₁ y = invVal t₂ x₂ y := by
  have ht8 : t₁ % 8 = t₂ % 8 := by omega
  have hx8 : x₁ % 8 = x₂ % 8 := by omega
  have hx2 : x₁ % 2 = x₂ % 2 := by omega
  unfold invVal
  by_cases h1 : t₁ < x₁ + y
  · rw [if_pos h1, if_pos (hlt1.mp h1)]
  · have h2 : ¬ t₂ < x₂ + y := fun h => h1 (hlt1.mpr h)
    rw [if_neg h1, if_neg h2]
    by_cases hy : y ≤ 3
    · simp only [if_pos hy, p03_congr ht8 hx8 hx2 (by omega)]
    · simp only [if_neg hy]
      have hcone : inCone y (t₁ - x₁) = inCone y (t₂ - x₂) := by
        simp only [inCone]
        by_cases h1c : t₁ - x₁ ≤ 20
        · have : t₁ - x₁ = t₂ - x₂ := by omega
          rw [this]
        · have h2c : ¬ (t₂ - x₂ ≤ 20) := by omega
          simp [h1c, h2c]
      rw [hcone]
      by_cases hc : inCone y (t₂ - x₂) = true
      · have hkeq : t₁ - x₁ = t₂ - x₂ := by
          simp only [inCone, decide_eq_true_eq] at hc
          omega
        simp only [if_pos hc, ht16, hkeq]
      · simp only [if_neg hc, hx16, hk]


set_option maxHeartbeats 2000000 in
theorem holds_succ (t : ℕ) (ht : 20 ≤ t) (ih : holds t) : holds (t + 1) := by
  intro x y b hb
  by_cases hxy : t + 1 < x + y
  · have hinv : invVal (t + 1) x y = some false := by simp [invVal, hxy]
    rw [hinv] at hb
    injection hb with hbf
    subst hbf
    apply outside
    rw [abs_of_nonneg (by omega : 0 ≤ (x : ℤ)), abs_of_nonneg (by omega : 0 ≤ (y : ℤ))]
    omega
  · have hxy_le : x + y ≤ t + 1 := by omega
    rw [cell_step]
    have hw_refl : cell 654 t ((x : ℤ) - 1) (y : ℤ) =
        cell 654 t ((if x = 0 then 1 else x - 1 : ℕ) : ℤ) (y : ℤ) := by
      by_cases hx0 : x = 0
      · subst hx0; simp [show (0 : ℤ) - 1 = -(1 : ℤ) by omega, reflectX]
      · simp [hx0, show (x : ℤ) - 1 = ((x - 1 : ℕ) : ℤ) by omega]
    have hs_refl : cell 654 t (x : ℤ) ((y : ℤ) - 1) =
        cell 654 t (x : ℤ) ((if y = 0 then 1 else y - 1 : ℕ) : ℤ) := by
      by_cases hy0 : y = 0
      · subst hy0; simp [show (0 : ℤ) - 1 = -(1 : ℤ) by omega, reflectY]
      · simp [hy0, show (y : ℤ) - 1 = ((y - 1 : ℕ) : ℤ) by omega]
    rw [hw_refl, hs_refl]
    apply forced_sound
      (ih x y)
      (by exact_mod_cast ih (x + 1) y)
      (ih (if x = 0 then 1 else x - 1) y)
      (by exact_mod_cast ih x (y + 1))
      (ih x (if y = 0 then 1 else y - 1))
    -- Reduce to one of the 5 finite check lemmas
    by_cases hk : t + 1 - x ≤ 20
    · have hy13 : y < 13 := by
        by_contra hy
        have h13 : 13 ≤ y := by omega
        have hinv : invVal (t + 1) x y = none := by
          simp only [invVal, show ¬ (t + 1 < x + y) by omega, ↓reduceIte,
            show ¬ (y ≤ 3) by omega]
          have hnc : inCone y (t + 1 - x) = false := by
            simp only [inCone, decide_eq_false_iff_not]; omega
          simp [hnc, show ¬ y < 7 by omega]
        rw [hinv] at hb; cases hb
      have hx1 : 1 ≤ x := by omega
      let m : Fin 16 := ⟨t % 16, Nat.mod_lt _ (by omega)⟩
      let k : Fin 21 := ⟨t + 1 - x, by omega⟩
      let yf : Fin 13 := ⟨y, hy13⟩
      have hm_eq : m.1 = t % 16 := rfl
      have hk_eq : k.1 = t + 1 - x := rfl
      have hy_eq : yf.1 = y := rfl
      set t₀ := 32 + m.1
      set x₀ := t₀ + 1 - k.1
      have ht16 : t % 16 = t₀ % 16 := by simp [t₀, hm_eq]; omega
      have ht1_16 : (t + 1) % 16 = (t₀ + 1) % 16 := by simp [t₀, hm_eq]; omega
      have hx16 : x % 16 = x₀ % 16 := by
        have hxt : x = t + 1 - k.1 := by omega
        have hx0t : x₀ = 32 + t % 16 + 1 - k.1 := by simp [x₀, t₀, hm_eq]
        rw [hxt, hx0t]; omega
      have hx1_16 : (x + 1) % 16 = (x₀ + 1) % 16 := by
        rw [Nat.add_mod, hx16, ← Nat.add_mod]
      have hxm1_16 : (x - 1) % 16 = (x₀ - 1) % 16 := by
        have hx0_1 : 1 ≤ x₀ := by simp [x₀, t₀]; omega
        have h1 : x = (x - 1) + 1 := by omega
        have h2 : x₀ = (x₀ - 1) + 1 := by omega
        omega
      have hmain : invVal (t + 1) x y = invVal (t₀ + 1) x₀ yf.1 :=
        invVal_congr ht1_16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
      have hc : invVal t x y = invVal t₀ x₀ yf.1 :=
        invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
      have he : invVal t (x + 1) y = invVal t₀ (x₀ + 1) yf.1 :=
        invVal_congr ht16 hx1_16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
      have hw : invVal t (if x = 0 then 1 else x - 1) y = invVal t₀ (x₀ - 1) yf.1 := by
        simp only [show x ≠ 0 by omega, ↓reduceIte]
        exact invVal_congr ht16 hxm1_16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
      have hn : invVal t x (y + 1) = invVal t₀ x₀ (yf.1 + 1) :=
        invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
      have hs : invVal t x (if y = 0 then 1 else y - 1) = invVal t₀ x₀ (if yf.1 = 0 then 1 else yf.1 - 1) := by
        by_cases hy0 : y = 0
        · subst hy0; simp only [hy_eq, ↓reduceIte]; exact invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
        · simp only [hy0, hy_eq, ↓reduceIte]; exact invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
      rw [hmain] at hb
      rw [hc, he, hw, hn, hs]
      exact step_front_check m k yf b hb
    · have hk21 : 21 ≤ t + 1 - x := by omega
      have hy7 : y < 7 := by
        by_contra hy
        have h7 : 7 ≤ y := by omega
        have hinv : invVal (t + 1) x y = none := by
          simp only [invVal, show ¬ (t + 1 < x + y) by omega, ↓reduceIte,
            show ¬ (y ≤ 3) by omega]
          have hnc : inCone y (t + 1 - x) = false := by
            simp only [inCone, decide_eq_false_iff_not]; omega
          simp [hnc, show ¬ y < 7 by omega]
        rw [hinv] at hb; cases hb
      let yf : Fin 7 := ⟨y, hy7⟩
      have hy_eq : yf.1 = y := rfl
      by_cases hx0 : x = 0
      · subst hx0
        by_cases ht21 : t ≤ 21
        · let d : Fin 2 := ⟨t - 20, by omega⟩
          have hdt : 20 + d.1 = t := by
            change 20 + (t - 20) = t
            omega
          have hb' : invVal (20 + d.1 + 1) 0 yf.1 = some b := by
            rw [hdt]
            exact hb
          have hchk : forced (invVal (20 + d.1) 0 y) (invVal (20 + d.1) 1 y)
              (invVal (20 + d.1) 1 y) (invVal (20 + d.1) 0 (y + 1))
              (invVal (20 + d.1) 0 (if y = 0 then 1 else y - 1)) b = true :=
            step_zero_base_check d yf b hb'
          rw [hdt] at hchk
          exact hchk
        · have ht22 : 22 ≤ t := by omega
          let m : Fin 16 := ⟨t % 16, Nat.mod_lt _ (by omega)⟩
          have hm_eq : m.1 = t % 16 := rfl
          set t₀ := 48 + m.1
          have ht16 : t % 16 = t₀ % 16 := by simp [t₀, hm_eq]; omega
          have ht1_16 : (t + 1) % 16 = (t₀ + 1) % 16 := by simp [t₀, hm_eq]; omega
          have hmain : invVal (t + 1) 0 y = invVal (t₀ + 1) 0 yf.1 :=
            invVal_congr ht1_16 rfl (by simp [t₀]; omega) (by simp [t₀]; omega)
          have hc : invVal t 0 y = invVal t₀ 0 yf.1 :=
            invVal_congr ht16 rfl (by simp [t₀]; omega) (by simp [t₀]; omega)
          have he : invVal t 1 y = invVal t₀ 1 yf.1 :=
            invVal_congr ht16 rfl (by simp [t₀]; omega) (by simp [t₀]; omega)
          have hw : invVal t (if (0 : ℕ) = 0 then 1 else 0 - 1) y = invVal t₀ 1 yf.1 := by
            simp only [↓reduceIte]; exact he
          have hn : invVal t 0 (y + 1) = invVal t₀ 0 (yf.1 + 1) :=
            invVal_congr ht16 rfl (by simp [t₀]; omega) (by simp [t₀]; omega)
          have hs : invVal t 0 (if y = 0 then 1 else y - 1) = invVal t₀ 0 (if yf.1 = 0 then 1 else yf.1 - 1) := by
            by_cases hy0 : y = 0
            · subst hy0; simp only [hy_eq, ↓reduceIte]; exact invVal_congr ht16 rfl (by simp [t₀]; omega) (by simp [t₀]; omega)
            · simp only [hy0, hy_eq, ↓reduceIte]; exact invVal_congr ht16 rfl (by simp [t₀]; omega) (by simp [t₀]; omega)
          rw [hmain] at hb
          rw [hc, he, hw, hn, hs]
          exact step_zero_gt_check m yf b hb
      · have hx1 : 1 ≤ x := by omega
        by_cases hkBoundary : t - x ≤ 21
        · let d : Fin 2 := ⟨t - x - 20, by omega⟩
          let m : Fin 16 := ⟨t % 16, Nat.mod_lt _ (by omega)⟩
          have hm_eq : m.1 = t % 16 := rfl
          have hd : 20 + d.1 = t - x := by
            change 20 + (t - x - 20) = t - x
            omega
          set t₀ := 48 + m.1
          set x₀ := t₀ - (20 + d.1)
          have hxt : x = t - (20 + d.1) := by rw [hd]; omega
          have ht16 : t % 16 = t₀ % 16 := by simp [t₀, hm_eq]; omega
          have ht1_16 : (t + 1) % 16 = (t₀ + 1) % 16 := by simp [t₀, hm_eq]; omega
          have hx16 : x % 16 = x₀ % 16 := by
            have hx0t : x₀ = 48 + t % 16 - (20 + d.1) := by simp [x₀, t₀, hm_eq]
            rw [hxt, hx0t]; omega
          have hx1_16 : (x + 1) % 16 = (x₀ + 1) % 16 := by rw [Nat.add_mod, hx16, ← Nat.add_mod]
          have hxm1_16 : (x - 1) % 16 = (x₀ - 1) % 16 := by
            have hx0_1 : 1 ≤ x₀ := by simp [x₀, t₀]; omega
            omega
          have hmain : invVal (t + 1) x y = invVal (t₀ + 1) x₀ yf.1 :=
            invVal_congr ht1_16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          have hc : invVal t x y = invVal t₀ x₀ yf.1 :=
            invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          have he : invVal t (x + 1) y = invVal t₀ (x₀ + 1) yf.1 :=
            invVal_congr ht16 hx1_16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          have hw : invVal t (if x = 0 then 1 else x - 1) y = invVal t₀ (x₀ - 1) yf.1 := by
            simp only [hx0, ↓reduceIte]
            exact invVal_congr ht16 hxm1_16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          have hn : invVal t x (y + 1) = invVal t₀ x₀ (yf.1 + 1) :=
            invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          have hs : invVal t x (if y = 0 then 1 else y - 1) = invVal t₀ x₀ (if yf.1 = 0 then 1 else yf.1 - 1) := by
            by_cases hy0 : y = 0
            · subst hy0; simp only [hy_eq, ↓reduceIte]; exact invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
            · simp only [hy0, hy_eq, ↓reduceIte]; exact invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          rw [hmain] at hb
          rw [hc, he, hw, hn, hs]
          exact step_int_boundary_check m d yf b hb
        · have hk22 : 22 ≤ t - x := by omega
          let m : Fin 16 := ⟨t % 16, Nat.mod_lt _ (by omega)⟩
          let xm : Fin 16 := ⟨x % 16, Nat.mod_lt _ (by omega)⟩
          have hm_eq : m.1 = t % 16 := rfl
          have hxm_eq : xm.1 = x % 16 := rfl
          set t₀ := 64 + m.1
          set x₀ := 16 + xm.1
          have ht16 : t % 16 = t₀ % 16 := by simp [t₀, hm_eq]; omega
          have ht1_16 : (t + 1) % 16 = (t₀ + 1) % 16 := by simp [t₀, hm_eq]; omega
          have hx16 : x % 16 = x₀ % 16 := by simp [x₀, hxm_eq]
          have hx1_16 : (x + 1) % 16 = (x₀ + 1) % 16 := by rw [Nat.add_mod, hx16, ← Nat.add_mod]
          have hxm1_16 : (x - 1) % 16 = (x₀ - 1) % 16 := by
            have hx0_1 : 1 ≤ x₀ := by simp [x₀]; omega
            omega
          have hmain : invVal (t + 1) x y = invVal (t₀ + 1) x₀ yf.1 :=
            invVal_congr ht1_16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          have hc : invVal t x y = invVal t₀ x₀ yf.1 :=
            invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          have he : invVal t (x + 1) y = invVal t₀ (x₀ + 1) yf.1 :=
            invVal_congr ht16 hx1_16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          have hw : invVal t (if x = 0 then 1 else x - 1) y = invVal t₀ (x₀ - 1) yf.1 := by
            simp only [hx0, ↓reduceIte]
            exact invVal_congr ht16 hxm1_16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          have hn : invVal t x (y + 1) = invVal t₀ x₀ (yf.1 + 1) :=
            invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          have hs : invVal t x (if y = 0 then 1 else y - 1) = invVal t₀ x₀ (if yf.1 = 0 then 1 else yf.1 - 1) := by
            by_cases hy0 : y = 0
            · subst hy0; simp only [hy_eq, ↓reduceIte]; exact invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
            · simp only [hy0, hy_eq, ↓reduceIte]; exact invVal_congr ht16 hx16 (by simp [t₀, x₀]; omega) (by simp [t₀, x₀]; omega)
          rw [hmain] at hb
          rw [hc, he, hw, hn, hs]
          exact step_int_gt_check m xm yf b hb

theorem holds_ge_20 (t : ℕ) (ht : 20 ≤ t) : holds t := by
  induction t, ht using Nat.le_induction with
  | base => exact holds_20
  | succ t ht ih => exact holds_succ t ht ih

theorem cell_y0_ge_20 (t x : ℕ) (ht : 20 ≤ t) (hx : x ≤ t) :
    cell 654 t (x : ℤ) 0 = p03 t x 0 := by
  have h := holds_ge_20 t ht x 0 (p03 t x 0) (by
    simp [invVal, Nat.not_lt.mpr hx])
  simpa only [Nat.cast_zero] using h

/-! ### Initial values, recurrence, and generating function -/

def aSim (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if simCell (seedGrid n) k 0 then (2 : ℤ) ^ (n - k) else 0

theorem a_eq_aSim (n : ℕ) (hn : n ≤ 20) : a n = aSim n := by
  unfold a aSim
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h : cell 654 n (k : ℤ) 0 = simCell (sim n) k 0 := by
    simpa only [Nat.cast_zero] using cell_eq_simCell n hn k 0 (by omega) (by omega)
  rw [h, sim_eq_seedGrid n hn]

def initTable (n : ℕ) : ℤ :=
  match n with
  | 0 => 1 | 1 => 3 | 2 => 7 | 3 => 11 | 4 => 23 | 5 => 43 | 6 => 71 | 7 => 219
  | 8 => 439 | 9 => 875 | 10 => 1735 | 11 => 3547 | 12 => 6839 | 13 => 13675
  | 14 => 27335 | 15 => 54747 | 16 => 109495 | 17 => 218987 | 18 => 437959
  | 19 => 875995 | 20 => 1751735 | _ => 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem aSim_eq_initTable : ∀ n : Fin 21, aSim n.1 = initTable n.1 := by
  intro n
  fin_cases n <;> decide +kernel

theorem a_init (n : ℕ) (hn : n ≤ 20) : a n = initTable n := by
  rw [a_eq_aSim n hn]
  exact aSim_eq_initTable ⟨n, by omega⟩

def delta (m : ℕ) : ℤ :=
  (if tab03 ((m + 1) % 8) 0 0 then (1 : ℤ) else 0) +
  ∑ j ∈ Finset.range 9,
    ((if p03 (24 + m + 1) (24 + m - j) 0 then (1 : ℤ) else 0) -
     (if p03 (24 + m) (24 + m - j) 0 then (1 : ℤ) else 0)) * (2 : ℤ) ^ (j + 1)

theorem a_succ_sub (n : ℕ) (hn : 20 ≤ n) :
    a (n + 1) - 2 * a n = delta (n % 8) := by
  have ha1 : a (n + 1) =
      (if p03 (n + 1) (n + 1) 0 then (1 : ℤ) else 0) +
      ∑ x ∈ Finset.range (n + 1),
        (if p03 (n + 1) x 0 then (1 : ℤ) else 0) * (2 : ℤ) ^ (n - x + 1) := by
    unfold a
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, add_comm]
    congr 1
    · rw [cell_y0_ge_20 (n + 1) (n + 1) (by omega) le_rfl]
    · apply Finset.sum_congr rfl
      intro x hx
      have hx_le : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      rw [cell_y0_ge_20 (n + 1) x (by omega) (by omega), show n + 1 - x = n - x + 1 by omega]
      split_ifs <;> simp
  have ha0 : 2 * a n =
      ∑ x ∈ Finset.range (n + 1),
        (if p03 n x 0 then (1 : ℤ) else 0) * (2 : ℤ) ^ (n - x + 1) := by
    unfold a
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hx_le : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
    rw [cell_y0_ge_20 n x hn hx_le, pow_succ']
    split_ifs <;> ring
  rw [ha1, ha0, add_sub_assoc, ← Finset.sum_sub_distrib]
  have hsplit : n + 1 = (n - 8) + 9 := by omega
  conv_lhs =>
    arg 2
    arg 1
    rw [hsplit]
  rw [Finset.sum_range_add]
  have hzero : ∑ x ∈ Finset.range (n - 8),
      ((if p03 (n + 1) x 0 then (1 : ℤ) else 0) * (2 : ℤ) ^ (n - x + 1) -
       (if p03 n x 0 then (1 : ℤ) else 0) * (2 : ℤ) ^ (n - x + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxn : x < n - 8 := Finset.mem_range.mp hx
    have h1 : p03 (n + 1) x 0 = (171 : ℕ).testBit (x % 8) := by
      simp [p03, show ¬ (n + 1 - x ≤ 8) by omega]
    have h2 : p03 n x 0 = (171 : ℕ).testBit (x % 8) := by
      simp [p03, show ¬ (n - x ≤ 8) by omega]
    rw [h1, h2, sub_self]
  rw [hzero, zero_add]
  unfold delta
  have htop : p03 (n + 1) (n + 1) 0 = tab03 ((n % 8 + 1) % 8) 0 0 := by
    unfold p03
    simp only [Nat.sub_self, show (0 : ℕ) ≤ 8 by omega, ↓reduceIte,
      show (n + 1) % 8 = (n % 8 + 1) % 8 by omega]
  rw [htop]
  congr 1
  -- Reindex Finset.range 9: x = (n - 8) + i = n - (8 - i), vs j = 8 - i
  rw [← Finset.sum_range_reflect (fun j =>
    ((if p03 (24 + n % 8 + 1) (24 + n % 8 - j) 0 then (1 : ℤ) else 0) -
     (if p03 (24 + n % 8) (24 + n % 8 - j) 0 then (1 : ℤ) else 0)) * (2 : ℤ) ^ (j + 1)) 9]
  apply Finset.sum_congr rfl
  intro i hi
  have hi9 : i < 9 := Finset.mem_range.mp hi
  have hpow : n - (n - 8 + i) + 1 = (8 - i) + 1 := by omega
  have hp1 : p03 (n + 1) (n - 8 + i) 0 = p03 (24 + n % 8 + 1) (24 + n % 8 - (8 - i)) 0 := by
    apply p03_congr <;> omega
  have hp0 : p03 n (n - 8 + i) 0 = p03 (24 + n % 8) (24 + n % 8 - (8 - i)) 0 := by
    apply p03_congr <;> omega
  rw [hpow, hp1, hp0]
  ring

def deltaVal (m : ℕ) : ℤ :=
  match m with
  | 0 => -3 | 1 => -15 | 2 => 77 | 3 => -255
  | 4 => -3 | 5 => -15 | 6 => 77 | 7 => 1
  | _ => 0

theorem delta_eq_deltaVal : ∀ m : Fin 8, delta m.1 = deltaVal m.1 := by decide

theorem recurrence (n : ℕ) (hn : 13 ≤ n) :
    (a n : ℚ) = 2 * a (n - 1) + a (n - 8) - 2 * a (n - 9) := by
  by_cases h21 : n < 21
  · interval_cases n <;> norm_num [a_init, initTable]
  · have hn21 : 21 ≤ n := by omega
    have h1 := a_succ_sub (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at h1
    have h2 : a (n - 8) - 2 * a (n - 9) = delta ((n - 1) % 8) := by
      by_cases h29 : n < 29
      · have hdelta : delta ((n - 1) % 8) = deltaVal ((n - 1) % 8) :=
          delta_eq_deltaVal ⟨(n - 1) % 8, Nat.mod_lt _ (by omega)⟩
        rw [hdelta]
        interval_cases n <;> norm_num [a_init, initTable, deltaVal]
      · have h29' : 29 ≤ n := by omega
        have hsub := a_succ_sub (n - 9) (by omega)
        rw [show n - 9 + 1 = n - 8 by omega,
          show (n - 9) % 8 = (n - 1) % 8 by omega] at hsub
        exact hsub
    have hid : a n = 2 * a (n - 1) + a (n - 8) - 2 * a (n - 9) := by linarith
    exact_mod_cast hid

open PowerSeries

def series : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

noncomputable def numerator : ℚ⟦X⟧ :=
  1 + X + X ^ 2 - 3 * X ^ 3 + X ^ 4 - 3 * X ^ 5 - 15 * X ^ 6 + 77 * X ^ 7 -
    4 * X ^ 9 - 16 * X ^ 10 + 80 * X ^ 11 - 256 * X ^ 12

theorem series_mul_coeff (n d : ℕ) (q : ℚ) :
    coeff n (series * (C q * X ^ d)) = if d ≤ n then (a (n - d) : ℚ) * q else 0 := by
  rw [← mul_assoc, PowerSeries.coeff_mul_X_pow']
  by_cases h : d ≤ n
  · simp [series, h, PowerSeries.coeff_mul_C]
  · simp [h]

theorem generating :
    series * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + X ^ 2) * (1 + X ^ 4) : ℚ⟦X⟧) = numerator := by
  have hd : ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + X ^ 2) * (1 + X ^ 4) : ℚ⟦X⟧) =
      C 1 * X ^ 0 - C 2 * X ^ 1 - C 1 * X ^ 8 + C 2 * X ^ 9 := by
    simp only [map_ofNat, map_one]
    ring
  have hnum : numerator =
      C 1 * X ^ 0 + C 1 * X ^ 1 + C 1 * X ^ 2 + C (-3) * X ^ 3 +
        C 1 * X ^ 4 + C (-3) * X ^ 5 + C (-15) * X ^ 6 + C 77 * X ^ 7 +
        C (-4) * X ^ 9 + C (-16) * X ^ 10 + C 80 * X ^ 11 + C (-256) * X ^ 12 := by
    unfold numerator
    simp only [map_ofNat, map_one, map_neg]
    ring
  rw [hd, hnum]
  ext n
  simp only [mul_add, mul_sub, map_add, map_sub, series_mul_coeff, PowerSeries.coeff_C_mul_X_pow]
  by_cases h : n < 13
  · interval_cases n <;> norm_num [a_init, initTable]
  · have hn : 13 ≤ n := by omega
    have hl (m : ℕ) (hm : m < 13) : n ≠ m := by omega
    simp only [if_pos (show 0 ≤ n by omega), if_pos (show 1 ≤ n by omega),
      if_pos (show 8 ≤ n by omega), if_pos (show 9 ≤ n by omega), Nat.sub_zero, mul_one,
      if_neg (hl 0 (by decide)), if_neg (hl 1 (by decide)), if_neg (hl 2 (by decide)),
      if_neg (hl 3 (by decide)), if_neg (hl 4 (by decide)), if_neg (hl 5 (by decide)),
      if_neg (hl 6 (by decide)), if_neg (hl 7 (by decide)), if_neg (hl 9 (by decide)),
      if_neg (hl 10 (by decide)), if_neg (hl 11 (by decide)), if_neg (hl 12 (by decide)),
      add_zero]
    linarith [recurrence n hn]

end Rule654

theorem OMA.solution : type_of% @OMA.S_oeis_a283588.main := by
  exact ⟨Rule654.generating, Rule654.recurrence⟩
