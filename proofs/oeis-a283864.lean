import OMAStatements.S_oeis_a283864
import Mathlib

namespace OMA.Helpers_a283864
open OMA.S_oeis_a283864

theorem cell_succ (t : ℕ) (i j : ℤ) : cell 734 (t + 1) i j = Nat.testBit 734 ((cell 734 t i j).toNat +
    2 * ((cell 734 t (i + 1) j).toNat + (cell 734 t (i - 1) j).toNat + (cell 734 t i (j + 1)).toNat +
      (cell 734 t i (j - 1)).toNat)) := rfl

theorem cone : ∀ t : ℕ, ∀ x y : ℤ, (t : ℤ) < |x| + |y| → cell 734 t x y = false := by
  intro t
  induction t with
  | zero =>
    intro x y h
    show decide (x = 0 ∧ y = 0) = false
    simp only [decide_eq_false_iff_not, not_and]
    intro hx hy; subst hx hy; simp at h
  | succ t ih =>
    intro x y h
    rw [cell_succ, ih x y (by push_cast at h; omega), ih (x + 1) y (by push_cast at h; cases abs_cases x <;> cases abs_cases (x+1) <;> cases abs_cases y <;> omega),
      ih (x - 1) y (by push_cast at h; cases abs_cases x <;> cases abs_cases (x-1) <;> cases abs_cases y <;> omega),
      ih x (y + 1) (by push_cast at h; cases abs_cases x <;> cases abs_cases (y+1) <;> cases abs_cases y <;> omega),
      ih x (y - 1) (by push_cast at h; cases abs_cases x <;> cases abs_cases (y-1) <;> cases abs_cases y <;> omega)]
    decide

theorem symm : ∀ t : ℕ, ∀ x y : ℤ, cell 734 t (-x) y = cell 734 t x y := by
  intro t
  induction t with
  | zero => intro x y; show decide (-x = 0 ∧ y = 0) = decide (x = 0 ∧ y = 0); simp
  | succ t ih =>
    intro x y
    rw [cell_succ, cell_succ, ih, show -x + 1 = -(x - 1) by ring, ih, show -x - 1 = -(x + 1) by ring, ih, ih, ih]
    congr 2; ring

/-- window coordinates: `u = x + t`. -/
def nb (t : ℕ) (u y : ℤ) : Bool := cell 734 t (u - t) y

theorem nb_succ (t : ℕ) (u y : ℤ) : nb (t + 1) u y = Nat.testBit 734 ((nb t (u - 1) y).toNat +
    2 * ((nb t u y).toNat + (nb t (u - 2) y).toNat + (nb t (u - 1) (y + 1)).toNat +
      (nb t (u - 1) (y - 1)).toNat)) := by
  unfold nb
  rw [cell_succ]
  have e0 : u - ((t + 1 : ℕ) : ℤ) = (u - 1) - t := by push_cast; ring
  have e1 : u - ((t + 1 : ℕ) : ℤ) + 1 = u - t := by push_cast; ring
  have e2 : u - ((t + 1 : ℕ) : ℤ) - 1 = (u - 2) - t := by push_cast; ring
  rw [e1, e2, e0]

theorem nb_neg (t : ℕ) (u y : ℤ) (h : u < 0) : nb t u y = false := by
  unfold nb; apply cone; cases abs_cases (u - t) <;> cases abs_cases y <;> omega


def R (c r l u d : Bool) : Bool := Nat.testBit 734 (c.toNat + 2 * (r.toNat + l.toNat + u.toNat + d.toNat))

def newRow (rc ra rb : ℕ) : ℕ :=
  let M := 2 ^ 23 - 1
  let c := (rc <<< 1) &&& M
  let r := rc &&& M
  let l := (rc <<< 2) &&& M
  let u := (ra <<< 1) &&& M
  let d := (rb <<< 1) &&& M
  let an := l ||| r ||| u ||| d
  let al := l &&& r &&& u &&& d
  let pa := l ^^^ r ^^^ u ^^^ d
  let s2 := (M ^^^ pa) &&& an &&& (M ^^^ al)
  ((M ^^^ c) &&& an &&& (M ^^^ al)) ||| (c &&& (M ^^^ s2))

theorem R_formula (c r l u d : Bool) :
    (((true ^^ c) && (l || r || u || d) && (true ^^ (l && r && u && d))) ||
      (c && (true ^^ ((true ^^ (l ^^ r ^^ u ^^ d)) && (l || r || u || d) && (true ^^ (l && r && u && d)))))) =
      R c r l u d := by
  cases c <;> cases r <;> cases l <;> cases u <;> cases d <;> decide

theorem newRow_bit (rc ra rb k : ℕ) (hk : k < 23) :
    (newRow rc ra rb).testBit k = R (decide (1 ≤ k) && rc.testBit (k - 1)) (rc.testBit k)
      (decide (2 ≤ k) && rc.testBit (k - 2)) (decide (1 ≤ k) && ra.testBit (k - 1))
      (decide (1 ≤ k) && rb.testBit (k - 1)) := by
  have hM : (2 ^ 23 - 1 : ℕ).testBit k = true := by
    rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
  have hM' : Nat.testBit 8388607 k = true := hM
  simp only [newRow, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, hM,
    Bool.and_true]
  rw [← R_formula]

def step (w : List ℕ) : List ℕ :=
  (List.range 45).map fun yi => newRow (w.getD yi 0) (w.getD (yi + 1) 0) (if yi = 0 then 0 else w.getD (yi - 1) 0)

def Wst : ℕ → List ℕ
  | 0 => (List.range 45).map fun yi => if yi = 22 then 1 else 0
  | t + 1 => step (Wst t)

def SV (t : ℕ) (u y : ℤ) : Bool := ((Wst t).getD (y + 22).toNat 0).testBit u.toNat

theorem getD_mapRange {α : Type} (n i : ℕ) (f : ℕ → α) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp

theorem getD_mapRange_out {α : Type} (n i : ℕ) (f : ℕ → α) (d : α) (h : n ≤ i) :
    ((List.range n).map f).getD i d = d := by
  rw [List.getD_eq_default _ _ (by simpa using h)]

theorem Wst_len (t : ℕ) : (Wst t).length = 45 := by
  cases t <;> simp [Wst, step]

theorem correct : ∀ t : ℕ, ∀ u y : ℤ, 0 ≤ u → |y| ≤ 22 - u → nb t u y = SV t u y := by
  intro t
  induction t with
  | zero =>
    intro u y hu hy
    have hy' : -22 ≤ y ∧ y ≤ 22 := by cases abs_cases y <;> constructor <;> omega
    unfold SV
    rw [show Wst 0 = (List.range 45).map fun yi => if yi = 22 then 1 else 0 from rfl,
      getD_mapRange _ _ _ _ (by omega)]
    show decide (u - ((0 : ℕ) : ℤ) = 0 ∧ y = 0) = _
    by_cases h : y = 0
    · subst h
      rw [if_pos (by omega), show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
      simp only [Nat.cast_zero, sub_zero, and_true, decide_eq_decide]
      omega
    · rw [if_neg (by omega)]; simp [h]
  | succ t ih =>
    intro u y hu hy
    have hy' : -22 ≤ y ∧ y ≤ 22 := by cases abs_cases y <;> constructor <;> omega
    have hu' : u ≤ 22 := by cases abs_cases y <;> omega
    have key : ∀ u' y' : ℤ, (u' < 0 ∨ (0 ≤ u' ∧ |y'| ≤ 22 - u')) →
        nb t u' y' = (decide (0 ≤ u') && SV t u' y') := by
      intro u' y' h
      rcases h with h | ⟨h1, h2⟩
      · rw [nb_neg t u' y' h]; simp; omega
      · rw [ih u' y' h1 h2]; simp [h1]
    rw [nb_succ]
    unfold SV
    rw [show Wst (t + 1) = step (Wst t) from rfl]
    unfold step
    rw [getD_mapRange _ _ _ _ (by omega), newRow_bit _ _ _ _ (by omega)]
    unfold R
    rw [key (u - 1) y (by cases abs_cases y <;> omega), key u y (Or.inr ⟨hu, hy⟩),
      key (u - 2) y (by cases abs_cases y <;> omega),
      key (u - 1) (y + 1) (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega),
      key (u - 1) (y - 1) (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)]
    unfold SV
    have e1 : (y + 22).toNat + 1 = (y + 1 + 22).toNat := by omega
    have hn : ((u - 1).toNat) = u.toNat - 1 := by omega
    have hn2 : ((u - 2).toNat) = u.toNat - 2 := by omega
    rw [e1, hn, hn2]
    by_cases h0 : u = 0
    · subst h0; simp
    · have h1 : decide (1 ≤ u.toNat) = true := by simp; omega
      have hu1 : decide (0 ≤ u - 1) = true := by simp; omega
      rw [h1, hu1, show decide (0 ≤ u) = true by simp; omega]
      have e2 : (if (y + 22).toNat = 0 then 0 else (Wst t).getD ((y + 22).toNat - 1) 0) =
          (Wst t).getD (y - 1 + 22).toNat 0 := by
        by_cases hy0 : (y + 22).toNat = 0
        · exfalso; cases abs_cases y <;> omega
        · rw [if_neg hy0]; congr 1; omega
      rw [e2]
      by_cases h2 : u = 1
      · subst h2; simp
      · rw [show decide (2 ≤ u.toNat) = true by simp; omega, show decide (0 ≤ u - 2) = true by simp; omega]
        simp

def mk (yi : ℕ) : ℕ := 2 ^ (23 - (if yi ≤ 22 then 22 - yi else yi - 22)) - 1

def msk (w : List ℕ) : List ℕ := (List.range 45).map fun yi => w.getD yi 0 &&& mk yi

theorem perOK_t : msk (Wst 46) = msk (Wst 38) := by decide +kernel

theorem SV_per (u y : ℤ) (hu : 0 ≤ u) (hy : |y| ≤ 22 - u) : SV 46 u y = SV 38 u y := by
  have hy' : (y + 22).toNat < 45 := by cases abs_cases y <;> omega
  have h := congrArg (fun w => (w.getD (y + 22).toNat 0).testBit u.toNat) perOK_t
  simp only [msk] at h
  rw [getD_mapRange _ _ _ _ hy', getD_mapRange _ _ _ _ hy', Nat.testBit_and, Nat.testBit_and] at h
  have hm : (mk (y + 22).toNat).testBit u.toNat = true := by
    unfold mk; rw [Nat.testBit_two_pow_sub_one]; apply decide_eq_true
    split_ifs <;> cases abs_cases y <;> omega
  rw [hm, Bool.and_true, Bool.and_true] at h
  exact h

theorem per : ∀ t : ℕ, 38 ≤ t → ∀ u y : ℤ, 0 ≤ u → |y| ≤ 22 - u → nb (t + 8) u y = nb t u y := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro u y hu hy; rw [correct 46 u y hu hy, correct 38 u y hu hy]; exact SV_per u y hu hy
  | succ t ht ih =>
    intro u y hu hy
    have key : ∀ u' y' : ℤ, (u' < 0 ∨ (0 ≤ u' ∧ |y'| ≤ 22 - u')) → nb (t + 8) u' y' = nb t u' y' := by
      intro u' y' h
      rcases h with h | ⟨h1, h2⟩
      · rw [nb_neg _ _ _ h, nb_neg _ _ _ h]
      · exact ih u' y' h1 h2
    rw [show t + 1 + 8 = (t + 8) + 1 by omega, nb_succ (t + 8), nb_succ t,
      key (u - 1) y (by cases abs_cases y <;> omega), key u y (Or.inr ⟨hu, hy⟩),
      key (u - 2) y (by cases abs_cases y <;> omega),
      key (u - 1) (y + 1) (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega),
      key (u - 1) (y - 1) (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)]

theorem per_red (t : ℕ) (ht : 38 ≤ t) (u y : ℤ) (hu : 0 ≤ u) (hy : |y| ≤ 22 - u) :
    nb t u y = nb (38 + (t - 38) % 8) u y := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases h : t < 46
    · congr 1; omega
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 8 := ⟨t - 8, by omega⟩
      rw [per s (by omega) u y hu hy, ih s (by omega) (by omega)]
      congr 2; omega

def Lv (t : ℕ) : ℕ := if t % 2 = 1 then 1023 else if t % 4 = 2 then 759 else 887

def winOK : Bool := (List.range 25).all fun i =>
  ((((Wst (i + 21)).getD 21 0 >>> 10) &&& 4095 == 4095) && (((Wst (i + 21)).getD 22 0 >>> 10) &&& 4095 == 4095)) &&
    ((((Wst (i + 21)).getD 23 0 >>> 10) &&& 4095 == 4095) && ((Wst (i + 21)).getD 22 0 &&& 1023 == Lv (i + 21)))

theorem winOK_t : winOK = true := by decide +kernel

theorem bitkey (x : ℕ) (hx : (x >>> 10) &&& 4095 = 4095) (v : ℕ) (h1 : 10 ≤ v) (h2 : v ≤ 21) :
    x.testBit v = true := by
  have := congrArg (fun z => z.testBit (v - 10)) hx
  simp only [Nat.testBit_and, Nat.testBit_shiftRight] at this
  rw [show 10 + (v - 10) = v by omega] at this
  have h4 : (4095 : ℕ).testBit (v - 10) = true := by
    rw [show (4095 : ℕ) = 2 ^ 12 - 1 from rfl, Nat.testBit_two_pow_sub_one]; apply decide_eq_true; omega
  rw [h4, Bool.and_true] at this; exact this

theorem win (t : ℕ) (h1 : 21 ≤ t) (h2 : t ≤ 45) :
    (∀ u : ℤ, 10 ≤ u → u ≤ 21 → ∀ y : ℤ, |y| ≤ 1 → nb t u y = true) ∧
      (∀ k : ℕ, k < 10 → nb t k 0 = (Lv t).testBit k) := by
  have h := winOK_t
  unfold winOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := h (t - 21) (by omega)
  rw [show t - 21 + 21 = t by omega] at a1 a2 a3 a4
  constructor
  · intro u hu1 hu2 y hy
    rw [correct t u y (by omega) (by cases abs_cases y <;> omega)]
    unfold SV
    have : y = -1 ∨ y = 0 ∨ y = 1 := by cases abs_cases y <;> omega
    rcases this with rfl | rfl | rfl
    · rw [show ((-1 : ℤ) + 22).toNat = 21 from rfl]; exact bitkey _ a1 _ (by omega) (by omega)
    · rw [show ((0 : ℤ) + 22).toNat = 22 from rfl]; exact bitkey _ a2 _ (by omega) (by omega)
    · rw [show ((1 : ℤ) + 22).toNat = 23 from rfl]; exact bitkey _ a3 _ (by omega) (by omega)
  · intro k hk
    rw [correct t k 0 (by omega) (by simp; omega)]
    unfold SV
    rw [show ((0 : ℤ) + 22).toNat = 22 from rfl, show ((k : ℤ)).toNat = k by omega, ← a4,
      Nat.testBit_and, show (1023 : ℕ) = 2 ^ 10 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp [hk]

theorem winAll (t : ℕ) (h1 : 21 ≤ t) :
    (∀ u : ℤ, 10 ≤ u → u ≤ 21 → ∀ y : ℤ, |y| ≤ 1 → nb t u y = true) ∧
      (∀ k : ℕ, k < 10 → nb t k 0 = (Lv t).testBit k) := by
  by_cases h2 : t ≤ 45
  · exact win t h1 h2
  · have hw := win (38 + (t - 38) % 8) (by omega) (by omega)
    have hL : Lv t = Lv (38 + (t - 38) % 8) := by
      unfold Lv
      rw [show (38 + (t - 38) % 8) % 2 = t % 2 by omega, show (38 + (t - 38) % 8) % 4 = t % 4 by omega]
    constructor
    · intro u hu1 hu2 y hy
      rw [per_red t (by omega) u y (by omega) (by cases abs_cases y <;> omega)]
      exact hw.1 u hu1 hu2 y hy
    · intro k hk
      rw [per_red t (by omega) k 0 (by omega) (by simp; omega), hL]
      exact hw.2 k hk

theorem band : ∀ t : ℕ, 21 ≤ t → ∀ u : ℤ, 10 ≤ u → u ≤ t → ∀ y : ℤ, |y| ≤ 1 → nb t u y = true := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro u h1 h2 y hy; exact (winAll 21 le_rfl).1 u h1 (by exact_mod_cast h2) y hy
  | succ t ht ih =>
    intro u h1 h2 y hy
    have h2' : u ≤ (t : ℤ) + 1 := by push_cast at h2; exact h2
    by_cases hu : u ≤ 21
    · exact (winAll (t + 1) (by omega)).1 u h1 hu y hy
    · rw [nb_succ]
      have c : nb t (u - 1) y = true := ih (u - 1) (by omega) (by omega) y hy
      have l : nb t (u - 2) y = true := ih (u - 2) (by omega) (by omega) y hy
      have r : nb t u y = true := by
        by_cases hut : u ≤ t
        · exact ih u (by omega) hut y hy
        · have e : u = (t : ℤ) + 1 := by omega
          unfold nb
          rw [e, show (t : ℤ) + 1 - t = -((t : ℤ) - 1 - t) by ring, symm]
          exact ih ((t : ℤ) - 1) (by omega) (by omega) y hy
      rw [c, l, r]
      have hy0 : y = -1 ∨ y = 0 ∨ y = 1 := by cases abs_cases y <;> omega
      rcases hy0 with rfl | rfl | rfl
      · rw [show (-1 : ℤ) + 1 = 0 by norm_num, ih (u - 1) (by omega) (by omega) 0 (by norm_num)]
        cases nb t (u - 1) (-1 - 1) <;> decide
      · rw [ih (u - 1) (by omega) (by omega) (0 + 1) (by norm_num),
          ih (u - 1) (by omega) (by omega) (0 - 1) (by norm_num)]
        decide
      · rw [show (1 : ℤ) - 1 = 0 by norm_num, ih (u - 1) (by omega) (by omega) 0 (by norm_num)]
        cases nb t (u - 1) (1 + 1) <;> decide

def Tc (n : ℕ) : ℕ := if n % 2 = 1 then 1023 else if n % 4 = 2 then 957 else 955

theorem aF (n : ℕ) (hn : 21 ≤ n) : a n = 2 ^ (n - 9) * ((Tc n : ℤ) + 1) - 1 := by
  have hb := winAll n hn
  unfold a
  rw [show n + 1 = 10 + (n - 9) by omega, Finset.sum_range_add]
  have s1 : ∀ k ∈ Finset.range 10, (if cell 734 n ((k : ℤ) - n) 0 then (2 : ℤ) ^ (n - k) else 0) =
      2 ^ (n - 9) * (if (Lv n).testBit k then 2 ^ (9 - k) else 0) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [show cell 734 n ((k : ℤ) - n) 0 = nb n k 0 from rfl, hb.2 k hk]
    split_ifs
    · rw [← pow_add]; congr 1; omega
    · simp
  have s2 : ∀ k ∈ Finset.range (n - 9), (if cell 734 n (((10 + k : ℕ) : ℤ) - n) 0 then (2 : ℤ) ^ (n - (10 + k)) else 0) =
      2 ^ ((n - 9) - 1 - k) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [show cell 734 n (((10 + k : ℕ) : ℤ) - n) 0 = nb n ((10 + k : ℕ) : ℤ) 0 from rfl,
      band n hn _ (by push_cast; omega) (by push_cast; omega) 0 (by norm_num), if_pos rfl]
    congr 1; omega
  rw [Finset.sum_congr rfl s1, Finset.sum_congr rfl s2, ← Finset.mul_sum]
  have hr := Finset.sum_range_reflect (fun j => (2 : ℤ) ^ j) (n - 9)
  rw [hr]
  have hg := geom_sum_mul (2 : ℤ) (n - 9)
  norm_num at hg
  rw [hg]
  have hT : (∑ k ∈ Finset.range 10, (if (Lv n).testBit k then (2 : ℤ) ^ (9 - k) else 0)) = (Tc n : ℤ) := by
    unfold Lv Tc
    split_ifs <;> decide +kernel
  rw [hT]; ring

theorem rec (n : ℕ) (hn : 26 ≤ n) : (a n : ℚ) = a (n - 1) + 16 * a (n - 4) - 16 * a (n - 5) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 26 := ⟨n - 26, by omega⟩
  rw [aF (q + 26) (by omega), aF (q + 26 - 1) (by omega), aF (q + 26 - 4) (by omega),
    aF (q + 26 - 5) (by omega)]
  have t1 : Tc (q + 26 - 4) = Tc (q + 26) := by
    unfold Tc; rw [show (q + 26 - 4) % 2 = (q + 26) % 2 by omega, show (q + 26 - 4) % 4 = (q + 26) % 4 by omega]
  have t2 : Tc (q + 26 - 5) = Tc (q + 26 - 1) := by
    unfold Tc; rw [show (q + 26 - 5) % 2 = (q + 26 - 1) % 2 by omega, show (q + 26 - 5) % 4 = (q + 26 - 1) % 4 by omega]
  rw [t1, t2, show q + 26 - 9 = q + 17 by omega, show q + 26 - 1 - 9 = q + 16 by omega,
    show q + 26 - 4 - 9 = q + 13 by omega, show q + 26 - 5 - 9 = q + 12 by omega]
  push_cast; ring

def awN (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), if ((Wst n).getD 22 0).testBit k then 2 ^ (n - k) else 0

theorem a_aw (n : ℕ) (hn : n ≤ 22) : a n = ((awN n : ℕ) : ℤ) := by
  unfold a awN
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [show cell 734 n ((k : ℤ) - n) 0 = nb n k 0 from rfl, correct n k 0 (by omega) (by simp; omega)]
  unfold SV
  rw [show ((0 : ℤ) + 22).toNat = 22 from rfl, show ((k : ℤ)).toNat = k by omega]

set_option maxHeartbeats 2000000 in
open PowerSeries in
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (16 * X ^ 5 - 16 * X ^ 4 - X + 1 : PowerSeries ℚ) = -4096 * X ^ 25 + 4096 * X ^ 24 - 2048 * X ^ 23 + 2048 * X ^ 22 + 256 * X ^ 21 - 256 * X ^ 20 - 64 * X ^ 16 + 72 * X ^ 15 - 8 * X ^ 14 + 4 * X ^ 12 - 4 * X ^ 10 + 2 * X ^ 9 - 2 * X ^ 8 + 8 * X ^ 7 - 8 * X ^ 6 + 2 * X ^ 5 - 2 * X ^ 4 + 8 * X ^ 3 + 4 * X ^ 2 + 2 * X + 1 := by
  have h0 : a 0 = 1 := by rw [a_aw 0 (by norm_num)]; decide +kernel
  have h1 : a 1 = 3 := by rw [a_aw 1 (by norm_num)]; decide +kernel
  have h2 : a 2 = 7 := by rw [a_aw 2 (by norm_num)]; decide +kernel
  have h3 : a 3 = 15 := by rw [a_aw 3 (by norm_num)]; decide +kernel
  have h4 : a 4 = 29 := by rw [a_aw 4 (by norm_num)]; decide +kernel
  have h5 : a 5 = 63 := by rw [a_aw 5 (by norm_num)]; decide +kernel
  have h6 : a 6 = 119 := by rw [a_aw 6 (by norm_num)]; decide +kernel
  have h7 : a 7 = 255 := by rw [a_aw 7 (by norm_num)]; decide +kernel
  have h8 : a 8 = 477 := by rw [a_aw 8 (by norm_num)]; decide +kernel
  have h9 : a 9 = 1023 := by rw [a_aw 9 (by norm_num)]; decide +kernel
  have h10 : a 10 = 1915 := by rw [a_aw 10 (by norm_num)]; decide +kernel
  have h11 : a 11 = 4091 := by rw [a_aw 11 (by norm_num)]; decide +kernel
  have h12 : a 12 = 7647 := by rw [a_aw 12 (by norm_num)]; decide +kernel
  have h13 : a 13 = 16383 := by rw [a_aw 13 (by norm_num)]; decide +kernel
  have h14 : a 14 = 30647 := by rw [a_aw 14 (by norm_num)]; decide +kernel
  have h15 : a 15 = 65535 := by rw [a_aw 15 (by norm_num)]; decide +kernel
  have h16 : a 16 = 122367 := by rw [a_aw 16 (by norm_num)]; decide +kernel
  have h17 : a 17 = 262143 := by rw [a_aw 17 (by norm_num)]; decide +kernel
  have h18 : a 18 = 490367 := by rw [a_aw 18 (by norm_num)]; decide +kernel
  have h19 : a 19 = 1048575 := by rw [a_aw 19 (by norm_num)]; decide +kernel
  have h20 : a 20 = 1957631 := by rw [a_aw 20 (by norm_num)]; decide +kernel
  have h21 : a 21 = 4194303 := by rw [aF 21 (by norm_num)]; decide +kernel
  have h22 : a 22 = 7847935 := by rw [aF 22 (by norm_num)]; decide +kernel
  have h23 : a 23 = 16777215 := by rw [aF 23 (by norm_num)]; decide +kernel
  have h24 : a 24 = 31326207 := by rw [aF 24 (by norm_num)]; decide +kernel
  have h25 : a 25 = 67108863 := by rw [aF 25 (by norm_num)]; decide +kernel
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, f = fun n => (a n : ℚ) := ⟨_, rfl⟩
  have g0 : f 0 = 1 := by simp only [hf, h0]; norm_num
  have g1 : f 1 = 3 := by simp only [hf, h1]; norm_num
  have g2 : f 2 = 7 := by simp only [hf, h2]; norm_num
  have g3 : f 3 = 15 := by simp only [hf, h3]; norm_num
  have g4 : f 4 = 29 := by simp only [hf, h4]; norm_num
  have g5 : f 5 = 63 := by simp only [hf, h5]; norm_num
  have g6 : f 6 = 119 := by simp only [hf, h6]; norm_num
  have g7 : f 7 = 255 := by simp only [hf, h7]; norm_num
  have g8 : f 8 = 477 := by simp only [hf, h8]; norm_num
  have g9 : f 9 = 1023 := by simp only [hf, h9]; norm_num
  have g10 : f 10 = 1915 := by simp only [hf, h10]; norm_num
  have g11 : f 11 = 4091 := by simp only [hf, h11]; norm_num
  have g12 : f 12 = 7647 := by simp only [hf, h12]; norm_num
  have g13 : f 13 = 16383 := by simp only [hf, h13]; norm_num
  have g14 : f 14 = 30647 := by simp only [hf, h14]; norm_num
  have g15 : f 15 = 65535 := by simp only [hf, h15]; norm_num
  have g16 : f 16 = 122367 := by simp only [hf, h16]; norm_num
  have g17 : f 17 = 262143 := by simp only [hf, h17]; norm_num
  have g18 : f 18 = 490367 := by simp only [hf, h18]; norm_num
  have g19 : f 19 = 1048575 := by simp only [hf, h19]; norm_num
  have g20 : f 20 = 1957631 := by simp only [hf, h20]; norm_num
  have g21 : f 21 = 4194303 := by simp only [hf, h21]; norm_num
  have g22 : f 22 = 7847935 := by simp only [hf, h22]; norm_num
  have g23 : f 23 = 16777215 := by simp only [hf, h23]; norm_num
  have g24 : f 24 = 31326207 := by simp only [hf, h24]; norm_num
  have g25 : f 25 = 67108863 := by simp only [hf, h25]; norm_num
  have grec : ∀ k, 26 ≤ k → f k = f (k - 1) + 16 * f (k - 4) - 16 * f (k - 5) := by intro k hk; simp only [hf]; exact rec k hk
  rw [← hf]
  clear hf h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
  set A : PowerSeries ℚ := PowerSeries.mk f with hA
  have hD : A * (16 * X ^ 5 - 16 * X ^ 4 - X + 1 : PowerSeries ℚ) =
      C (16 : ℚ) * (A * X ^ 5) - C (16 : ℚ) * (A * X ^ 4) - A * X ^ 1 + A := by
    simp only [map_ofNat]; ring
  have hN : (-4096 * X ^ 25 + 4096 * X ^ 24 - 2048 * X ^ 23 + 2048 * X ^ 22 + 256 * X ^ 21 - 256 * X ^ 20 - 64 * X ^ 16 + 72 * X ^ 15 - 8 * X ^ 14 + 4 * X ^ 12 - 4 * X ^ 10 + 2 * X ^ 9 - 2 * X ^ 8 + 8 * X ^ 7 - 8 * X ^ 6 + 2 * X ^ 5 - 2 * X ^ 4 + 8 * X ^ 3 + 4 * X ^ 2 + 2 * X + 1 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (2 : ℚ) * X ^ 1 + C (4 : ℚ) * X ^ 2 + C (8 : ℚ) * X ^ 3 - C (2 : ℚ) * X ^ 4 + C (2 : ℚ) * X ^ 5 - C (8 : ℚ) * X ^ 6 + C (8 : ℚ) * X ^ 7 - C (2 : ℚ) * X ^ 8 + C (2 : ℚ) * X ^ 9 - C (4 : ℚ) * X ^ 10 + C (4 : ℚ) * X ^ 12 - C (8 : ℚ) * X ^ 14 + C (72 : ℚ) * X ^ 15 - C (64 : ℚ) * X ^ 16 - C (256 : ℚ) * X ^ 20 + C (256 : ℚ) * X ^ 21 + C (2048 : ℚ) * X ^ 22 - C (2048 : ℚ) * X ^ 23 + C (4096 : ℚ) * X ^ 24 - C (4096 : ℚ) * X ^ 25 := by
    simp only [map_ofNat, map_one]; ring
  rw [hD, hN]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk]
  rcases Nat.lt_or_ge k 26 with h | h
  · interval_cases k <;> simp [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25] <;> norm_num
  · simp only [show 5 ≤ k by omega, show 4 ≤ k by omega, show 1 ≤ k by omega, if_true, show 0 ≤ k by omega, show 2 ≤ k by omega, show 3 ≤ k by omega, show 6 ≤ k by omega, show 7 ≤ k by omega, show 8 ≤ k by omega, show 9 ≤ k by omega, show 10 ≤ k by omega, show 12 ≤ k by omega, show 14 ≤ k by omega, show 15 ≤ k by omega, show 16 ≤ k by omega, show 20 ≤ k by omega, show 21 ≤ k by omega, show 22 ≤ k by omega, show 23 ≤ k by omega, show 24 ≤ k by omega, show 25 ≤ k by omega, coeff_C, show k - 0 ≠ 0 by omega, show k - 1 ≠ 0 by omega, show k - 2 ≠ 0 by omega, show k - 3 ≠ 0 by omega, show k - 4 ≠ 0 by omega, show k - 5 ≠ 0 by omega, show k - 6 ≠ 0 by omega, show k - 7 ≠ 0 by omega, show k - 8 ≠ 0 by omega, show k - 9 ≠ 0 by omega, show k - 10 ≠ 0 by omega, show k - 12 ≠ 0 by omega, show k - 14 ≠ 0 by omega, show k - 15 ≠ 0 by omega, show k - 16 ≠ 0 by omega, show k - 20 ≠ 0 by omega, show k - 21 ≠ 0 by omega, show k - 22 ≠ 0 by omega, show k - 23 ≠ 0 by omega, show k - 24 ≠ 0 by omega, show k - 25 ≠ 0 by omega, if_false]
    linear_combination grec k h

end OMA.Helpers_a283864

open OMA.Helpers_a283864 in
theorem OMA.solution : type_of% @OMA.S_oeis_a283864.main := ⟨rec, gf⟩
