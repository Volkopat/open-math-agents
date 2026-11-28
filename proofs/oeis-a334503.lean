import OMAStatements.S_oeis_a334503
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace A334503Proof

open OMA.S_oeis_a334503 PowerSeries

lemma row_add (n t s : ℕ) : row n (t + s) = step^[s] (row n t) := by
  unfold row
  rw [Nat.add_comm, Function.iterate_add_apply]

lemma row_succ (n t : ℕ) : row n (t + 1) = step (row n t) := by
  rw [row_add]
  rfl

lemma row_periodic_of_eq (n T p : ℕ) (h : row n (T + p) = row n T) :
    ∀ s : ℕ, row n (T + s + p) = row n (T + s) := by
  intro s
  have h1 : T + s + p = T + p + s := by omega
  rw [h1, row_add, h, ← row_add]

lemma row_periodic_mul (n T p : ℕ) (h : row n (T + p) = row n T) :
    ∀ m : ℕ, row n (T + m * p) = row n T := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : T + (m + 1) * p = (T + m * p) + p := by ring
    rw [h1, row_add, ih, ← row_add, h]

lemma a_eq_of_cycle {n T p : ℕ} (hn : n ≠ 0) (hp : 0 < p)
    (hcyc : row n (T + p) = row n T)
    (hmin : ∀ q : ℕ, 0 < q → q < p → row n (T + q) ≠ row n T) :
    a n = p := by
  unfold a
  rw [if_neg hn]
  have hmem : p ∈ {p : ℕ | 0 < p ∧ ∃ t : ℕ, row n (t + p) = row n t} := ⟨hp, T, hcyc⟩
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · apply le_csInf ⟨p, hmem⟩
    rintro q ⟨hq, t, ht⟩
    by_contra hlt
    have hqlt : q < p := Nat.lt_of_not_ge hlt
    have hge : ∀ s : ℕ, t ≤ s → row n (s + q) = row n s := by
      intro s hs
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
      exact row_periodic_of_eq n t q ht d
    have hts : t ≤ T + t * p := by
      have : t * 1 ≤ t * p := Nat.mul_le_mul_left t hp
      omega
    have h1 := hge (T + t * p) hts
    have h2 : T + t * p + q = (T + q) + t * p := by omega
    rw [row_periodic_mul n T p hcyc t] at h1
    have hcyc_q : row n ((T + q) + p) = row n (T + q) := row_periodic_of_eq n T p hcyc q
    rw [h2, row_periodic_mul n (T + q) p hcyc_q t] at h1
    exact hmin q hq hqlt h1

def rule131 (l c r : Bool) : Bool := (!l && !c) || (l && c && r)

def rule62 (l c r : Bool) : Bool := (!l && (c || r)) || (l && !c)

lemma not_rule131 (l c r : Bool) : (!(rule131 l c r)) = rule62 (!l) (!c) (!r) := by
  cases l <;> cases c <;> cases r <;> rfl

lemma step_getLsbD {n : ℕ} (hn : 0 < n) (w : BitVec n) (i : ℕ) (hi : i < n) :
    (step w).getLsbD i =
      rule131 (w.getLsbD ((i + n - 1) % n)) (w.getLsbD i) (w.getLsbD ((i + 1) % n)) := by
  unfold step rule131
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true,
    Bool.true_and, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight]
  have hL : (bif decide (i < 1 % n) then w.getLsbD (n - 1 % n + i)
      else w.getLsbD (i - 1 % n)) = w.getLsbD ((i + n - 1) % n) := by
    by_cases h1 : n = 1
    · subst h1
      have hi0 : i = 0 := by omega
      subst hi0
      simp
    · have hmod : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      by_cases hi0 : i = 0
      · subst hi0
        have heq : (0 + n - 1) % n = n - 1 := by
          rw [Nat.zero_add]
          exact Nat.mod_eq_of_lt (by omega)
        simp
      · have heq : (i + n - 1) % n = i - 1 := by
          have : i + n - 1 = (i - 1) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hnot : ¬ (i < 1) := by omega
        simp [hnot, heq]
  have hR : (bif decide (i < n - 1 % n) then w.getLsbD (1 % n + i)
      else w.getLsbD (i - (n - 1 % n))) = w.getLsbD ((i + 1) % n) := by
    by_cases h1 : n = 1
    · subst h1
      have hi0 : i = 0 := by omega
      subst hi0
      simp
    · have hmod : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      by_cases hil : i + 1 = n
      · have heq : (i + 1) % n = 0 := by rw [hil, Nat.mod_self]
        have hnot : ¬ (i < n - 1) := by omega
        have hsub : i - (n - 1) = 0 := by omega
        simp [hnot, hsub, heq]
      · have hlt : i < n - 1 := by omega
        have heq : (i + 1) % n = 1 + i := by
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        simp [hlt, heq]
  rw [hL, hR]

def MatchesRaw (n : ℕ) (w : BitVec n) (f : ℕ → Bool) : Prop :=
  ∀ i : ℕ, i < n → w.getLsbD i = f i

lemma matchesRaw_eq {n : ℕ} {w1 w2 : BitVec n} {f : ℕ → Bool}
    (h1 : MatchesRaw n w1 f) (h2 : MatchesRaw n w2 f) : w1 = w2 :=
  BitVec.eq_of_getLsbD_eq (fun i hi => (h1 i hi).trans (h2 i hi).symm)

lemma matchesRaw_step {n : ℕ} (hn : 0 < n) {w : BitVec n} {f g : ℕ → Bool}
    (hw : MatchesRaw n w f)
    (hstep : ∀ i : ℕ, i < n →
      rule131 (f ((i + n - 1) % n)) (f i) (f ((i + 1) % n)) = g i) :
    MatchesRaw n (step w) g := by
  intro i hi
  rw [step_getLsbD hn w i hi,
    hw ((i + n - 1) % n) (Nat.mod_lt _ hn),
    hw i hi,
    hw ((i + 1) % n) (Nat.mod_lt _ hn)]
  exact hstep i hi

def initList (n : ℕ) : List Bool := true :: List.replicate (n - 1) false

def stepList (L : List Bool) : List Bool :=
  let n := L.length
  (List.range n).map fun i =>
    rule131 (L.getD ((i + n - 1) % n) false) (L.getD i false) (L.getD ((i + 1) % n) false)

lemma initList_length {n : ℕ} (hn : 0 < n) : (initList n).length = n := by
  simp [initList]
  omega

lemma stepList_length (L : List Bool) : (stepList L).length = L.length := by
  simp [stepList]

lemma stepList_iter_length (n t : ℕ) (hn : 0 < n) :
    (stepList^[t] (initList n)).length = n := by
  induction t with
  | zero => exact initList_length hn
  | succ t ih =>
    rw [Function.iterate_succ_apply', stepList_length, ih]

lemma matchesRaw_initList {n : ℕ} (hn : 0 < n) :
    MatchesRaw n (row n 0) (fun i => (initList n).getD i false) := by
  intro i hi
  change (1#n).getLsbD i = (initList n).getD i false
  rw [BitVec.getLsbD_one]
  simp only [hn, decide_true, Bool.true_and, initList]
  cases i with
  | zero => rfl
  | succ k =>
    simp only [Nat.succ_ne_zero, decide_false, List.getD_eq_getElem?_getD,
      List.getElem?_cons_succ]
    have hk : k < n - 1 := by omega
    rw [List.getElem?_replicate]
    simp [hk]

lemma matchesRaw_stepList {n : ℕ} (hn : 0 < n) {w : BitVec n} {L : List Bool}
    (hlen : L.length = n) (hw : MatchesRaw n w (fun i => L.getD i false)) :
    MatchesRaw n (step w) (fun i => (stepList L).getD i false) := by
  apply matchesRaw_step hn hw
  intro i hi
  simp only [stepList, hlen, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

lemma matchesRaw_row_list {n : ℕ} (hn : 0 < n) (t : ℕ) :
    MatchesRaw n (row n t) (fun i => (stepList^[t] (initList n)).getD i false) := by
  induction t with
  | zero => exact matchesRaw_initList hn
  | succ t ih =>
    rw [row_succ, Function.iterate_succ_apply']
    exact matchesRaw_stepList hn (stepList_iter_length n t hn) ih

lemma row_eq_iff_list {n : ℕ} (hn : 0 < n) (t1 t2 : ℕ) :
    row n t1 = row n t2 ↔ stepList^[t1] (initList n) = stepList^[t2] (initList n) := by
  have h1 := matchesRaw_row_list hn t1
  have h2 := matchesRaw_row_list hn t2
  have hl1 := stepList_iter_length n t1 hn
  have hl2 := stepList_iter_length n t2 hn
  constructor
  · intro heq
    apply List.ext_getElem (hl1.trans hl2.symm)
    intro i hi1 hi2
    have hi : i < n := hl1 ▸ hi1
    have hb1 := h1 i hi
    have hb2 := h2 i hi
    rw [heq] at hb1
    have hget := hb1.symm.trans hb2
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1,
      List.getElem?_eq_getElem hi2, Option.getD_some] at hget
    exact hget
  · intro heq
    apply matchesRaw_eq h1
    rw [heq]
    exact h2

def checkCycleAux (target cur : List Bool) : ℕ → Bool
  | 0 => cur == target
  | k + 1 => if cur == target then false else checkCycleAux target (stepList cur) k

lemma checkCycleAux_spec (target : List Bool) :
    ∀ (k : ℕ) (cur : List Bool), checkCycleAux target cur k = true →
      stepList^[k] cur = target ∧ ∀ j : ℕ, j < k → stepList^[j] cur ≠ target := by
  intro k
  induction k with
  | zero =>
    intro cur h
    simp only [checkCycleAux, beq_iff_eq] at h
    exact ⟨h, fun j hj => by omega⟩
  | succ k ih =>
    intro cur h
    unfold checkCycleAux at h
    by_cases hEq : cur = target
    · simp [hEq] at h
    · have hbeq : (cur == target) = false := beq_false_of_ne hEq
      rw [hbeq] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hfin, hne⟩ := ih (stepList cur) h
      constructor
      · rw [Function.iterate_succ_apply]
        exact hfin
      · intro j hj
        cases j with
        | zero => exact hEq
        | succ j =>
          rw [Function.iterate_succ_apply]
          exact hne j (by omega)

def checkCycle (n T p : ℕ) : Bool :=
  let L0 := stepList^[T] (initList n)
  checkCycleAux L0 (stepList L0) (p - 1)

lemma a_eq_of_checkCycle {n T p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (h : checkCycle n T p = true) : a n = p := by
  unfold checkCycle at h
  obtain ⟨hfin, hne⟩ := checkCycleAux_spec (stepList^[T] (initList n)) (p - 1)
    (stepList (stepList^[T] (initList n))) h
  apply a_eq_of_cycle (T := T) (by omega) hp
  · rw [row_eq_iff_list hn]
    have hadd : T + p = (p - 1 + 1) + T := by omega
    rw [hadd, Function.iterate_add_apply, Function.iterate_succ_apply]
    exact hfin
  · intro q hq1 hq2 heq
    rw [row_eq_iff_list hn] at heq
    have hadd : T + q = (q - 1 + 1) + T := by omega
    rw [hadd, Function.iterate_add_apply, Function.iterate_succ_apply] at heq
    exact hne (q - 1) (by omega) heq

lemma a_0 : a 0 = 0 := by simp [a]
lemma a_1 : a 1 = 1 := a_eq_of_checkCycle (T := 0) (by decide) (by decide) (by decide)
lemma a_2 : a 2 = 1 := a_eq_of_checkCycle (T := 2) (by decide) (by decide) (by decide)
lemma a_3 : a 3 = 3 := a_eq_of_checkCycle (T := 0) (by decide) (by decide) (by decide)
lemma a_4 : a 4 = 8 := a_eq_of_checkCycle (T := 0) (by decide) (by decide) (by decide)
lemma a_5 : a 5 = 3 := a_eq_of_checkCycle (T := 0) (by decide) (by decide) (by decide)
lemma a_6 : a 6 = 3 := a_eq_of_checkCycle (T := 0) (by decide) (by decide) (by decide)
lemma a_7 : a 7 = 14 := a_eq_of_checkCycle (T := 3) (by decide) (by decide) (by decide)
lemma a_8 : a 8 = 16 := a_eq_of_checkCycle (T := 3) (by decide) (by decide) (by decide)
lemma a_9 : a 9 = 3 := a_eq_of_checkCycle (T := 5) (by decide) (by decide) (by decide)
set_option maxRecDepth 20000 in
lemma a_10 : a 10 = 20 := a_eq_of_checkCycle (T := 8) (by decide) (by decide) (by decide)
lemma a_11 : a 11 = 3 := a_eq_of_checkCycle (T := 5) (by decide) (by decide) (by decide)
set_option maxRecDepth 20000 in
lemma a_12 : a 12 = 3 := a_eq_of_checkCycle (T := 20) (by decide) (by decide) (by decide)
lemma a_13 : a 13 = 3 := a_eq_of_checkCycle (T := 5) (by decide) (by decide) (by decide)
lemma a_14 : a 14 = 3 := a_eq_of_checkCycle (T := 5) (by decide) (by decide) (by decide)
set_option maxRecDepth 30000 in
lemma a_15 : a 15 = 3 := a_eq_of_checkCycle (T := 29) (by decide) (by decide) (by decide)
set_option maxRecDepth 60000 in
lemma a_16 : a 16 = 32 := a_eq_of_checkCycle (T := 32) (by decide) (by decide) (by decide)

def rowM (n s : ℕ) : BitVec n := row n (s + 2)

lemma rowM_succ (n s : ℕ) : rowM n (s + 1) = step (rowM n s) := by
  unfold rowM
  have : s + 1 + 2 = s + 2 + 1 := by omega
  rw [this, row_succ]

lemma a_eq_of_cycleM {n T p : ℕ} (hn : n ≠ 0) (hp : 0 < p)
    (hcyc : rowM n (T + p) = rowM n T)
    (hmin : ∀ q : ℕ, 0 < q → q < p → rowM n (T + q) ≠ rowM n T) :
    a n = p := by
  apply a_eq_of_cycle (T := T + 2) hn hp
  · have h1 : T + 2 + p = T + p + 2 := by omega
    rw [h1]
    exact hcyc
  · intro q hq1 hq2
    have h1 : T + 2 + q = T + q + 2 := by omega
    rw [h1]
    exact hmin q hq1 hq2

def Matches (n : ℕ) (w : BitVec n) (f : ℕ → Bool) : Prop :=
  ∀ i : ℕ, i < n → (!(w.getLsbD ((i + 2) % n))) = f i

lemma matches_eq {n : ℕ} (hn : 2 ≤ n) {w1 w2 : BitVec n} {f : ℕ → Bool}
    (h1 : Matches n w1 f) (h2 : Matches n w2 f) : w1 = w2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i := (j + n - 2) % n
  have hi : i < n := Nat.mod_lt _ (by omega)
  have hmod_add : ∀ a b : ℕ, (a % n + b) % n = (a + b) % n := fun a b => by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hij : (i + 2) % n = j := by
    have h0 : (i + 2) % n = ((j + n - 2) % n + 2) % n := rfl
    rw [h0, hmod_add]
    have ha : j + n - 2 + 2 = j + n := by omega
    rw [ha, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  have hb1 := h1 i hi
  have hb2 := h2 i hi
  rw [hij] at hb1 hb2
  have hnot : (!(w1.getLsbD j)) = (!(w2.getLsbD j)) := hb1.trans hb2.symm
  cases h1' : w1.getLsbD j <;> cases h2' : w2.getLsbD j <;> simp_all

lemma matches_ne_of_bit {n : ℕ} {w1 w2 : BitVec n} {f1 f2 : ℕ → Bool}
    (h1 : Matches n w1 f1) (h2 : Matches n w2 f2) (i : ℕ) (hi : i < n)
    (hne : f1 i ≠ f2 i) : w1 ≠ w2 := by
  intro heq
  apply hne
  rw [← h1 i hi, ← h2 i hi, heq]

lemma matches_step {n : ℕ} (hn : 2 ≤ n) {w : BitVec n} {f g : ℕ → Bool}
    (hw : Matches n w f)
    (hstep : ∀ i : ℕ, i < n →
      rule62 (f ((i + n - 1) % n)) (f i) (f ((i + 1) % n)) = g i) :
    Matches n (step w) g := by
  intro i hi
  have hj : (i + 2) % n < n := Nat.mod_lt _ (by omega)
  rw [step_getLsbD (by omega) w ((i + 2) % n) hj, not_rule131]
  have hmod_add : ∀ a b : ℕ, (a % n + b) % n = (a + b) % n := fun a b => by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hL : ((i + 2) % n + n - 1) % n = ((i + n - 1) % n + 2) % n := by
    have h1 : (i + 2) % n + n - 1 = (i + 2) % n + (n - 1) := by omega
    rw [h1, hmod_add, hmod_add]
    congr 1
    omega
  have hR : ((i + 2) % n + 1) % n = ((i + 1) % n + 2) % n := by
    rw [hmod_add, hmod_add]
  rw [hL, hR,
    hw ((i + n - 1) % n) (Nat.mod_lt _ (by omega)),
    hw i hi,
    hw ((i + 1) % n) (Nat.mod_lt _ (by omega))]
  exact hstep i hi

lemma matches_congr {n : ℕ} {w : BitVec n} {f g : ℕ → Bool}
    (hw : Matches n w f) (hfg : ∀ i : ℕ, i < n → f i = g i) :
    Matches n w g :=
  fun i hi => (hw i hi).trans (hfg i hi)

def leftBlock (t i : ℕ) : Bool :=
  match (t + 2 * (i / 4)) % 3 with
  | 0 => true
  | 1 => decide (i % 4 = 0)
  | _ => decide (i % 4 = 1 ∨ i % 4 = 3)

def bg110 (p i : ℕ) : Bool := decide ((i + p) % 3 ≠ 2)

lemma bg110_eq_true {p i : ℕ} (h : (i + p) % 3 ≠ 2) : bg110 p i = true := by
  unfold bg110
  simp [h]

lemma bg110_eq_false {p i : ℕ} (h : (i + p) % 3 = 2) : bg110 p i = false := by
  unfold bg110
  simp [h]

lemma leftBlock_eq_zero {t i : ℕ} (h : (t + 2 * (i / 4)) % 3 = 0) : leftBlock t i = true := by
  unfold leftBlock
  rw [h]
  rfl

lemma leftBlock_eq_one {t i : ℕ} (h : (t + 2 * (i / 4)) % 3 = 1) :
    leftBlock t i = decide (i % 4 = 0) := by
  unfold leftBlock
  rw [h]
  rfl

lemma leftBlock_eq_two {t i : ℕ} (h : (t + 2 * (i / 4)) % 3 = 2) :
    leftBlock t i = decide (i % 4 = 1 ∨ i % 4 = 3) := by
  unfold leftBlock
  rw [h]
  rfl

lemma leftBlock_mod (t i : ℕ) : leftBlock t i = leftBlock (t % 3) (i % 12) := by
  unfold leftBlock
  have h1 : (t + 2 * (i / 4)) % 3 = (t % 3 + 2 * ((i % 12) / 4)) % 3 := by omega
  have h2 : i % 4 = (i % 12) % 4 := by omega
  rw [h1, h2]

lemma bg110_mod (p i : ℕ) : bg110 p i = bg110 (p % 3) (i % 3) := by
  unfold bg110
  have h : (i + p) % 3 = (i % 3 + p % 3) % 3 := by omega
  rw [h]

lemma rule62_leftBlock (t i : ℕ) (hi : 0 < i) :
    rule62 (leftBlock t (i - 1)) (leftBlock t i) (leftBlock t (i + 1)) = leftBlock (t + 1) i := by
  have hcheck : ∀ (a : Fin 3) (b : Fin 12),
      rule62 (leftBlock a.val ((b.val + 11) % 12)) (leftBlock a.val b.val)
        (leftBlock a.val ((b.val + 1) % 12)) = leftBlock ((a.val + 1) % 3) b.val := by
    decide
  rw [leftBlock_mod t (i - 1), leftBlock_mod t i, leftBlock_mod t (i + 1), leftBlock_mod (t + 1) i]
  have hm1 : (i - 1) % 12 = (i % 12 + 11) % 12 := by omega
  have hp1 : (i + 1) % 12 = (i % 12 + 1) % 12 := by omega
  have ht1 : (t + 1) % 3 = (t % 3 + 1) % 3 := by omega
  rw [hm1, hp1, ht1]
  exact hcheck ⟨t % 3, Nat.mod_lt _ (by decide)⟩ ⟨i % 12, Nat.mod_lt _ (by decide)⟩

lemma rule62_bg110 (p i : ℕ) (hi : 0 < i) :
    rule62 (bg110 p (i - 1)) (bg110 p i) (bg110 p (i + 1)) = bg110 (p + 1) i := by
  have hcheck : ∀ (a : Fin 3) (b : Fin 3),
      rule62 (bg110 a.val ((b.val + 2) % 3)) (bg110 a.val b.val)
        (bg110 a.val ((b.val + 1) % 3)) = bg110 ((a.val + 1) % 3) b.val := by
    decide
  rw [bg110_mod p (i - 1), bg110_mod p i, bg110_mod p (i + 1), bg110_mod (p + 1) i]
  have hm1 : (i - 1) % 3 = (i % 3 + 2) % 3 := by omega
  have hp1 : (i + 1) % 3 = (i % 3 + 1) % 3 := by omega
  have hp2 : (p + 1) % 3 = (p % 3 + 1) % 3 := by omega
  rw [hm1, hp1, hp2]
  exact hcheck ⟨p % 3, Nat.mod_lt _ (by decide)⟩ ⟨i % 3, Nat.mod_lt _ (by decide)⟩

lemma rule62_wrap_zero (n t p : ℕ) (hn : 1 < n) (hp : p % 3 = (t + 2 * n) % 3) :
    rule62 (bg110 p (n - 1)) (leftBlock t 0) (leftBlock t 1) = leftBlock (t + 1) 0 := by
  have hcheck : ∀ (a : Fin 3),
      rule62 (decide ((a.val + 2) % 3 ≠ 2)) (leftBlock a.val 0) (leftBlock a.val 1) =
        leftBlock ((a.val + 1) % 3) 0 := by
    decide
  have hbg : bg110 p (n - 1) = decide ((t % 3 + 2) % 3 ≠ 2) := by
    unfold bg110
    have : (n - 1 + p) % 3 = (t % 3 + 2) % 3 := by omega
    rw [this]
  rw [hbg, leftBlock_mod t 0, leftBlock_mod t 1, leftBlock_mod (t + 1) 0]
  have ht1 : (t + 1) % 3 = (t % 3 + 1) % 3 := by omega
  rw [ht1]
  exact hcheck ⟨t % 3, Nat.mod_lt _ (by decide)⟩

lemma rule62_wrap_last (n t p : ℕ) (hn : 1 < n) (hp : p % 3 = (t + 2 * n) % 3) :
    rule62 (bg110 p (n - 2)) (bg110 p (n - 1)) (leftBlock t 0) = bg110 (p + 1) (n - 1) := by
  have hcheck : ∀ (a : Fin 3),
      rule62 (decide ((a.val + 1) % 3 ≠ 2)) (decide ((a.val + 2) % 3 ≠ 2)) (leftBlock a.val 0) =
        decide ((a.val + 3) % 3 ≠ 2) := by
    decide
  have h1 : bg110 p (n - 2) = decide ((t % 3 + 1) % 3 ≠ 2) := by
    unfold bg110
    have : (n - 2 + p) % 3 = (t % 3 + 1) % 3 := by omega
    rw [this]
  have h2 : bg110 p (n - 1) = decide ((t % 3 + 2) % 3 ≠ 2) := by
    unfold bg110
    have : (n - 1 + p) % 3 = (t % 3 + 2) % 3 := by omega
    rw [this]
  have h3 : bg110 (p + 1) (n - 1) = decide ((t % 3 + 3) % 3 ≠ 2) := by
    unfold bg110
    have : (n - 1 + (p + 1)) % 3 = (t % 3 + 3) % 3 := by omega
    rw [this]
  rw [h1, h2, h3, leftBlock_mod t 0]
  exact hcheck ⟨t % 3, Nat.mod_lt _ (by decide)⟩

lemma rule62_seam_left (B t p : ℕ) (hB : 0 < B) (hrel : (p + 2 * t + 2 * B) % 3 = 0) :
    rule62 (leftBlock t (4 * B - 2)) (leftBlock t (4 * B - 1)) (bg110 p (4 * B)) =
      leftBlock (t + 1) (4 * B - 1) := by
  have hcheck : ∀ (a : Fin 3),
      rule62 (leftBlock a.val 2) (leftBlock a.val 3) (decide ((a.val + 2) % 3 ≠ 2)) =
        leftBlock ((a.val + 1) % 3) 3 := by
    decide
  let a := (t + 2 * (B - 1)) % 3
  have ha : a < 3 := Nat.mod_lt _ (by decide)
  have h1 : leftBlock t (4 * B - 2) = leftBlock a 2 := by
    unfold leftBlock
    have : (t + 2 * ((4 * B - 2) / 4)) % 3 = (a + 2 * (2 / 4)) % 3 := by omega
    have hm : (4 * B - 2) % 4 = 2 := by omega
    rw [this, hm]
  have h2 : leftBlock t (4 * B - 1) = leftBlock a 3 := by
    unfold leftBlock
    have : (t + 2 * ((4 * B - 1) / 4)) % 3 = (a + 2 * (3 / 4)) % 3 := by omega
    have hm : (4 * B - 1) % 4 = 3 := by omega
    rw [this, hm]
  have h3 : leftBlock (t + 1) (4 * B - 1) = leftBlock ((a + 1) % 3) 3 := by
    unfold leftBlock
    have : (t + 1 + 2 * ((4 * B - 1) / 4)) % 3 = ((a + 1) % 3 + 2 * (3 / 4)) % 3 := by omega
    have hm : (4 * B - 1) % 4 = 3 := by omega
    rw [this, hm]
  have h4 : bg110 p (4 * B) = decide ((a + 2) % 3 ≠ 2) := by
    unfold bg110
    have : (4 * B + p) % 3 = (a + 2) % 3 := by omega
    rw [this]
  rw [h1, h2, h3, h4]
  exact hcheck ⟨a, ha⟩

lemma rule62_seam_right (B t p : ℕ) (hB : 0 < B) (hrel : (p + 2 * t + 2 * B) % 3 = 0) :
    rule62 (leftBlock t (4 * B - 1)) (bg110 p (4 * B)) (bg110 p (4 * B + 1)) =
      bg110 (p + 1) (4 * B) := by
  have hcheck : ∀ (a : Fin 3),
      rule62 (leftBlock a.val 3) (decide ((a.val + 2) % 3 ≠ 2)) (decide ((a.val + 3) % 3 ≠ 2)) =
        decide ((a.val + 3) % 3 ≠ 2) := by
    decide
  let a := (t + 2 * (B - 1)) % 3
  have ha : a < 3 := Nat.mod_lt _ (by decide)
  have h1 : leftBlock t (4 * B - 1) = leftBlock a 3 := by
    unfold leftBlock
    have : (t + 2 * ((4 * B - 1) / 4)) % 3 = (a + 2 * (3 / 4)) % 3 := by omega
    have hm : (4 * B - 1) % 4 = 3 := by omega
    rw [this, hm]
  have h2 : bg110 p (4 * B) = decide ((a + 2) % 3 ≠ 2) := by
    unfold bg110
    have : (4 * B + p) % 3 = (a + 2) % 3 := by omega
    rw [this]
  have h3 : bg110 p (4 * B + 1) = decide ((a + 3) % 3 ≠ 2) := by
    unfold bg110
    have : (4 * B + 1 + p) % 3 = (a + 3) % 3 := by omega
    rw [this]
  have h4 : bg110 (p + 1) (4 * B) = decide ((a + 3) % 3 ≠ 2) := by
    unfold bg110
    have : (4 * B + (p + 1)) % 3 = (a + 3) % 3 := by omega
    rw [this]
  rw [h1, h2, h3, h4]
  exact hcheck ⟨a, ha⟩

def leftCone (t i : ℕ) : Bool :=
  if 4 * (i / 4) + 3 ≤ t then leftBlock t i
  else
    match t % 4 with
    | 0 => decide (i % 4 = 0)
    | 1 => decide (i % 4 ≤ 1)
    | _ => decide (i % 4 = 2)

def preBit (n t i : ℕ) : Bool :=
  if i ≤ t then leftCone t i
  else if n ≤ i + t + 3 then bg110 (t + 2 * n) i
  else false

def frontierVal (s d : ℕ) : Bool :=
  if d ≤ s then
    if s = 3 then true
    else match s with
      | 0 => decide (d = 0)
      | 1 => decide (d ≤ 1)
      | _ => decide (d = 2)
  else false

def frontierNext (s d : ℕ) : Bool :=
  if d ≤ s + 1 then
    if s = 2 then true
    else if s = 3 then
      if d < 4 then leftBlock 4 d else true
    else match s + 1 with
      | 1 => decide (d ≤ 1)
      | _ => decide (d = 2)
  else false

lemma leftCone_zero (t : ℕ) : leftCone t 0 = leftBlock t 0 := by
  unfold leftCone leftBlock
  by_cases h : 3 ≤ t
  · simp [h]
  · interval_cases t <;> decide

lemma preBit_frontier_val (n q s d : ℕ) (hs : s < 4) (hgap : 4 * q + d + (4 * q + s) + 3 < n) :
    preBit n (4 * q + s) (4 * q + d) = frontierVal s d := by
  unfold preBit frontierVal
  by_cases hds : d ≤ s
  · have hle : 4 * q + d ≤ 4 * q + s := by omega
    rw [if_pos hle, if_pos hds]
    unfold leftCone
    have hdiv : (4 * q + d) / 4 = q := by omega
    have hmod : (4 * q + d) % 4 = d := by omega
    have htm : (4 * q + s) % 4 = s := by omega
    rw [hdiv, hmod, htm]
    by_cases hs3 : s = 3
    · subst hs3
      rw [if_pos (by omega), if_pos rfl]
      exact leftBlock_eq_zero (by omega)
    · rw [if_neg (by omega), if_neg hs3]
  · rw [if_neg (by omega), if_neg (by omega), if_neg hds]

lemma preBit_frontier_next (n q s d : ℕ) (hs : s < 4) (hd : d ≤ 4)
    (hgap : 4 * q + d + (4 * q + s + 1) + 3 < n) :
    preBit n (4 * q + s + 1) (4 * q + d) = frontierNext s d := by
  by_cases hs3 : s = 3
  · subst hs3
    unfold frontierNext
    by_cases hd4 : d < 4
    · unfold preBit leftCone
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_neg (by decide), if_pos rfl, if_pos hd4]
      unfold leftBlock
      have h1 : (4 * q + 3 + 1 + 2 * ((4 * q + d) / 4)) % 3 = (4 + 2 * (d / 4)) % 3 := by omega
      have h2 : (4 * q + d) % 4 = d % 4 := by omega
      rw [h1, h2]
    · have hd_eq4 : d = 4 := by omega
      subst hd_eq4
      unfold preBit leftCone
      rw [if_pos (by omega), if_neg (by omega), if_pos (by omega),
        if_neg (by decide), if_pos rfl, if_neg (by decide)]
      have hm1 : (4 * q + 3 + 1) % 4 = 0 := by omega
      simp [hm1]
  · have hs1 : s + 1 < 4 := by omega
    have ha : 4 * q + s + 1 = 4 * q + (s + 1) := by omega
    rw [ha, preBit_frontier_val n q (s + 1) d hs1 (by omega)]
    unfold frontierVal frontierNext
    have hs_lt3 : s < 3 := by omega
    interval_cases s <;> simp

lemma preBit_prev_block (n q s : ℕ) (hq : 0 < q) (hs : s < 4) :
    preBit n (4 * q + s) (4 * q - 1) = leftBlock (s + 1) 3 ∧
    preBit n (4 * q + s) (4 * q - 2) = leftBlock (s + 1) 2 := by
  constructor
  · unfold preBit leftCone
    rw [if_pos (by omega), if_pos (by omega)]
    unfold leftBlock
    have : (4 * q + s + 2 * ((4 * q - 1) / 4)) % 3 = (s + 1 + 2 * (3 / 4)) % 3 := by omega
    have hm : (4 * q - 1) % 4 = 3 := by omega
    rw [this, hm]
  · unfold preBit leftCone
    rw [if_pos (by omega), if_pos (by omega)]
    unfold leftBlock
    have : (4 * q + s + 2 * ((4 * q - 2) / 4)) % 3 = (s + 1 + 2 * (2 / 4)) % 3 := by omega
    have hm : (4 * q - 2) % 4 = 2 := by omega
    rw [this, hm]

lemma preBit_step {n t : ℕ} (hgap : 2 * t + 7 ≤ n) :
    ∀ i : ℕ, i < n →
      rule62 (preBit n t ((i + n - 1) % n)) (preBit n t i) (preBit n t ((i + 1) % n)) =
        preBit n (t + 1) i := by
  have hn : 7 ≤ n := by omega
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0
    have hm : (0 + n - 1) % n = n - 1 := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hp : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm, hp]
    by_cases ht3 : 3 ≤ t
    · have hl : preBit n t (n - 1) = bg110 (t + 2 * n) (n - 1) := by
        unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
      have hc : preBit n t 0 = leftBlock t 0 := by
        unfold preBit; rw [if_pos (by omega)]; exact leftCone_zero t
      have hr : preBit n t 1 = leftBlock t 1 := by
        unfold preBit leftCone; rw [if_pos (by omega), if_pos (by omega)]
      have hg : preBit n (t + 1) 0 = leftBlock (t + 1) 0 := by
        unfold preBit; rw [if_pos (by omega)]; exact leftCone_zero (t + 1)
      rw [hl, hc, hr, hg]
      exact rule62_wrap_zero n t (t + 2 * n) (by omega) rfl
    · interval_cases t
      · have p1 : preBit n 0 (n - 1) = false := by
          unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
          exact bg110_eq_false (by omega)
        have p2 : preBit n 0 0 = true := by unfold preBit leftCone; simp
        have p3 : preBit n 0 1 = false := by unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
        have p4 : preBit n 1 0 = true := by unfold preBit leftCone; simp
        rw [p1, p2, p3, p4]; rfl
      · have p1 : preBit n 1 (n - 1) = true := by
          unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
          exact bg110_eq_true (by omega)
        have p2 : preBit n 1 0 = true := by unfold preBit leftCone; simp
        have p3 : preBit n 1 1 = true := by unfold preBit leftCone; simp
        have p4 : preBit n 2 0 = false := by unfold preBit leftCone; simp
        rw [p1, p2, p3, p4]; rfl
      · have p1 : preBit n 2 (n - 1) = true := by
          unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
          exact bg110_eq_true (by omega)
        have p2 : preBit n 2 0 = false := by unfold preBit leftCone; simp
        have p3 : preBit n 2 1 = false := by unfold preBit leftCone; simp
        have p4 : preBit n 3 0 = true := by
          unfold preBit leftCone; simp [leftBlock]
        rw [p1, p2, p3, p4]; rfl
  · by_cases hil : i = n - 1
    · subst hil
      have hL : (n - 1 + n - 1) % n = n - 2 := by
        have : n - 1 + n - 1 = (n - 2) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (n - 1 + 1) % n = 0 := by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
      rw [hL, hR]
      have h1 : preBit n t (n - 2) = bg110 (t + 2 * n) (n - 2) := by
        unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
      have h2 : preBit n t (n - 1) = bg110 (t + 2 * n) (n - 1) := by
        unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
      have h3 : preBit n t 0 = leftBlock t 0 := by
        unfold preBit; rw [if_pos (by omega)]; exact leftCone_zero t
      have h4 : preBit n (t + 1) (n - 1) = bg110 (t + 1 + 2 * n) (n - 1) := by
        unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
      rw [h1, h2, h3, h4]
      have hadd : t + 1 + 2 * n = (t + 2 * n) + 1 := by omega
      rw [hadd]
      exact rule62_wrap_last n t (t + 2 * n) (by omega) rfl
    · have hL : (i + n - 1) % n = i - 1 := by
        have : i + n - 1 = (i - 1) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hL, hR]
      obtain ⟨q, s, hs, htqs⟩ : ∃ q s, s < 4 ∧ t = 4 * q + s :=
        ⟨t / 4, t % 4, Nat.mod_lt _ (by decide), by omega⟩
      by_cases h1 : i + 1 < 4 * q
      · have hle_l : preBit n t (i - 1) = leftBlock t (i - 1) := by
          unfold preBit leftCone; rw [if_pos (by omega), if_pos (by omega)]
        have hle_c : preBit n t i = leftBlock t i := by
          unfold preBit leftCone; rw [if_pos (by omega), if_pos (by omega)]
        have hle_r : preBit n t (i + 1) = leftBlock t (i + 1) := by
          unfold preBit leftCone; rw [if_pos (by omega), if_pos (by omega)]
        have hle_g : preBit n (t + 1) i = leftBlock (t + 1) i := by
          unfold preBit leftCone; rw [if_pos (by omega), if_pos (by omega)]
        rw [hle_l, hle_c, hle_r, hle_g]
        exact rule62_leftBlock t i (by omega)
      · by_cases h2 : i ≤ t + 1
        · by_cases him : i + 1 = 4 * q
          · have hqpos : 0 < q := by omega
            have hi_eq : i = 4 * q - 1 := by omega
            have him1 : i - 1 = 4 * q - 2 := by omega
            have hip1 : i + 1 = 4 * q + 0 := by omega
            rw [him1, hip1, hi_eq, htqs]
            have hprev := preBit_prev_block n q s hqpos hs
            have hfr := preBit_frontier_val n q s 0 hs (by omega)
            have hnext : preBit n (4 * q + s + 1) (4 * q - 1) = leftBlock (s + 2) 3 := by
              unfold preBit leftCone
              rw [if_pos (by omega), if_pos (by omega)]
              unfold leftBlock
              have : (4 * q + s + 1 + 2 * ((4 * q - 1) / 4)) % 3 = (s + 2 + 2 * (3 / 4)) % 3 := by omega
              have hm : (4 * q - 1) % 4 = 3 := by omega
              rw [this, hm]
            rw [hprev.1, hprev.2, hfr, hnext]
            interval_cases s <;> decide
          · obtain ⟨d, hd_eq⟩ : ∃ d, i = 4 * q + d := ⟨i - 4 * q, by omega⟩
            have hd : d ≤ 4 := by omega
            rw [htqs, hd_eq]
            have hnext := preBit_frontier_next n q s d hs hd (by omega)
            have hrc := preBit_frontier_val n q s d hs (by omega)
            have hrr := preBit_frontier_val n q s (d + 1) hs (by omega)
            have hadd1 : 4 * q + d + 1 = 4 * q + (d + 1) := by omega
            rw [hadd1, hrc, hrr, hnext]
            by_cases hd0 : d = 0
            · subst hd0
              have hqpos : 0 < q := by omega
              have hprev := preBit_prev_block n q s hqpos hs
              have hsub : 4 * q + 0 - 1 = 4 * q - 1 := by omega
              rw [hsub, hprev.1]
              interval_cases s <;> decide
            · have hd1 : 1 ≤ d := by omega
              have hrl := preBit_frontier_val n q s (d - 1) hs (by omega)
              have hsub : 4 * q + d - 1 = 4 * q + (d - 1) := by omega
              rw [hsub, hrl]
              interval_cases s <;> interval_cases d <;> decide
        · by_cases h3 : i + t + 4 < n
          · have h1' : preBit n t (i - 1) = false := by
              unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
            have h2' : preBit n t i = false := by
              unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
            have h3' : preBit n t (i + 1) = false := by
              unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
            have h4' : preBit n (t + 1) i = false := by
              unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
            rw [h1', h2', h3', h4']
            rfl
          · by_cases h4 : i + t + 4 = n
            · have h1' : preBit n t (i - 1) = false := by
                unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
              have h2' : preBit n t i = false := by
                unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
              have h3' : preBit n t (i + 1) = true := by
                unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
                exact bg110_eq_true (by omega)
              have h4' : preBit n (t + 1) i = true := by
                unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
                exact bg110_eq_true (by omega)
              rw [h1', h2', h3', h4']
              rfl
            · by_cases h5 : i + t + 3 = n
              · have h1' : preBit n t (i - 1) = false := by
                  unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
                have h2' : preBit n t i = true := by
                  unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
                  exact bg110_eq_true (by omega)
                have h4' : preBit n (t + 1) i = true := by
                  unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
                  exact bg110_eq_true (by omega)
                rw [h1', h2', h4']
                cases preBit n t (i + 1) <;> rfl
              · have h1' : preBit n t (i - 1) = bg110 (t + 2 * n) (i - 1) := by
                  unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
                have h2' : preBit n t i = bg110 (t + 2 * n) i := by
                  unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
                have h3' : preBit n t (i + 1) = bg110 (t + 2 * n) (i + 1) := by
                  unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
                have h4' : preBit n (t + 1) i = bg110 (t + 1 + 2 * n) i := by
                  unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
                rw [h1', h2', h3', h4']
                have hadd : t + 1 + 2 * n = (t + 2 * n) + 1 := by omega
                rw [hadd]
                exact rule62_bg110 (t + 2 * n) i (by omega)

lemma matches_rowM_zero {n : ℕ} (hn : 5 ≤ n) :
    Matches n (rowM n 0) (preBit n 0) := by
  have hm0 : Matches n (row n 0) (fun i => decide (i ≠ n - 2)) := by
    intro i hi
    change (!((1#n).getLsbD ((i + 2) % n))) = decide (i ≠ n - 2)
    rw [BitVec.getLsbD_one]
    have hpos : 0 < n := by omega
    simp only [hpos, decide_true, Bool.true_and]
    by_cases hi2 : i = n - 2
    · subst hi2
      have h0 : (n - 2 + 2) % n = 0 := by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
      simp [h0]
    · have hne0 : (i + 2) % n ≠ 0 := by
        by_cases hi1 : i = n - 1
        · subst hi1
          have : (n - 1 + 2) % n = 1 := by
            have ha : n - 1 + 2 = 1 + n := by omega
            rw [ha, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          omega
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp [hi2, hne0]
  have hm1 : Matches n (row n 1) (fun i => decide (i = n - 2 ∨ i = n - 1)) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, row_succ]
    refine matches_step (by omega) hm0 ?_
    intro i hi
    by_cases hi2 : i = n - 2
    · subst hi2
      have hL : (n - 2 + n - 1) % n = n - 3 := by
        have : n - 2 + n - 1 = (n - 3) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (n - 2 + 1) % n = n - 1 := by
        have : n - 2 + 1 = n - 1 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      rw [hL, hR]
      simp [show n - 3 ≠ n - 2 by omega, show n - 1 ≠ n - 2 by omega]
      rfl
    · by_cases hi1 : i = n - 1
      · subst hi1
        have hL : (n - 1 + n - 1) % n = n - 2 := by
          have : n - 1 + n - 1 = (n - 2) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hR : (n - 1 + 1) % n = 0 := by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
        rw [hL, hR]
        simp [show n - 1 ≠ n - 2 by omega, show (0 : ℕ) ≠ n - 2 by omega]
        rfl
      · by_cases hi3 : i = n - 3
        · subst hi3
          have hL : (n - 3 + n - 1) % n = n - 4 := by
            have : n - 3 + n - 1 = (n - 4) + n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hR : (n - 3 + 1) % n = n - 2 := by
            have : n - 3 + 1 = n - 2 := by omega
            rw [this, Nat.mod_eq_of_lt (by omega)]
          rw [hL, hR]
          simp [show n - 4 ≠ n - 2 by omega, show n - 3 ≠ n - 2 by omega, show n - 3 ≠ n - 1 by omega]
          rfl
        · have hL : (i + n - 1) % n ≠ n - 2 := by
            by_cases hi0 : i = 0
            · subst hi0
              rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
            · have : i + n - 1 = (i - 1) + n := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
          have hR : (i + 1) % n ≠ n - 2 := by
            rw [Nat.mod_eq_of_lt (by omega)]; omega
          simp [hL, hi2, hR, hi1]
          rfl
  change Matches n (row n (1 + 1)) (preBit n 0)
  rw [row_succ]
  refine matches_step (by omega) hm1 ?_
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0
    have hL : (0 + n - 1) % n = n - 1 := by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    have hR : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hL, hR]
    have hpre : preBit n 0 0 = true := by unfold preBit leftCone; simp
    simp [hpre, show (0 : ℕ) ≠ n - 2 by omega, show (0 : ℕ) ≠ n - 1 by omega,
      show (1 : ℕ) ≠ n - 2 by omega, show (1 : ℕ) ≠ n - 1 by omega]
    rfl
  · by_cases hi3 : i = n - 3
    · subst hi3
      have hL : (n - 3 + n - 1) % n = n - 4 := by
        have : n - 3 + n - 1 = (n - 4) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (n - 3 + 1) % n = n - 2 := by
        have : n - 3 + 1 = n - 2 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      rw [hL, hR]
      have hpre : preBit n 0 (n - 3) = true := by
        unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
        exact bg110_eq_true (by omega)
      simp [hpre, show n - 4 ≠ n - 2 by omega, show n - 4 ≠ n - 1 by omega,
        show n - 3 ≠ n - 2 by omega, show n - 3 ≠ n - 1 by omega]
      rfl
    · by_cases hi2 : i = n - 2
      · subst hi2
        have hL : (n - 2 + n - 1) % n = n - 3 := by
          have : n - 2 + n - 1 = (n - 3) + n := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hR : (n - 2 + 1) % n = n - 1 := by
          have : n - 2 + 1 = n - 1 := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
        rw [hL, hR]
        have hpre : preBit n 0 (n - 2) = true := by
          unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
          exact bg110_eq_true (by omega)
        simp [hpre, show n - 3 ≠ n - 2 by omega, show n - 3 ≠ n - 1 by omega]
        rfl
      · by_cases hi1 : i = n - 1
        · subst hi1
          have hL : (n - 1 + n - 1) % n = n - 2 := by
            have : n - 1 + n - 1 = (n - 2) + n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hR : (n - 1 + 1) % n = 0 := by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
          rw [hL, hR]
          have hpre : preBit n 0 (n - 1) = false := by
            unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
            exact bg110_eq_false (by omega)
          simp [hpre, show (0 : ℕ) ≠ n - 2 by omega, show (0 : ℕ) ≠ n - 1 by omega]
          rfl
        · have hL : (i + n - 1) % n = i - 1 := by
            have : i + n - 1 = (i - 1) + n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hR : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hL, hR]
          have hpre : preBit n 0 i = false := by
            unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
          simp [hpre, show i - 1 ≠ n - 2 by omega, show i - 1 ≠ n - 1 by omega,
            hi2, hi1, show i + 1 ≠ n - 2 by omega, show i + 1 ≠ n - 1 by omega]
          rfl

lemma matches_preBit {n t : ℕ} (hgap : 2 * t + 5 ≤ n) :
    Matches n (rowM n t) (preBit n t) := by
  induction t with
  | zero => exact matches_rowM_zero (by omega)
  | succ t ih =>
    rw [rowM_succ]
    exact matches_step (by omega) (ih (by omega)) (preBit_step (by omega))

def baseBit (B t p i : ℕ) : Bool :=
  if i < 4 * B then leftBlock t i else bg110 p i

def wallBit (B m t p i : ℕ) : Bool :=
  if i < 4 * B then leftBlock t i
  else if i < m then bg110 (p + 1) i
  else bg110 p i

def wall2Bit (B m1 m2 t p i : ℕ) : Bool :=
  if i < 4 * B then leftBlock t i
  else if i < m1 then bg110 (p + 2) i
  else if i < m2 then bg110 (p + 1) i
  else bg110 p i

def patchAt (base : ℕ → Bool) (anchor : ℕ) : List (ℕ × Bool) → ℕ → Bool
  | [], i => base i
  | (d, b) :: rest, i => if i = anchor + d then b else patchAt base anchor rest i

def patchWrap (base : ℕ → Bool) (n : ℕ) (ovL ovR : List (ℕ × Bool)) (i : ℕ) : Bool :=
  match ovL.find? (fun p => p.1 == i) with
  | some (_, b) => b
  | none =>
    match ovR.find? (fun p => n - p.1 == i) with
    | some (_, b) => b
    | none => base i

lemma patchAt_outside (base : ℕ → Bool) (anchor : ℕ) (ov : List (ℕ × Bool)) (i : ℕ)
    (h : ∀ p ∈ ov, i ≠ anchor + p.1) : patchAt base anchor ov i = base i := by
  induction ov with
  | nil => rfl
  | cons hd tl ih =>
    unfold patchAt
    rw [if_neg (h hd (by simp))]
    exact ih (fun p hp => h p (by simp [hp]))

lemma patchWrap_outside (base : ℕ → Bool) (n : ℕ) (ovL ovR : List (ℕ × Bool)) (i : ℕ)
    (hL : ∀ p ∈ ovL, p.1 ≠ i) (hR : ∀ p ∈ ovR, n - p.1 ≠ i) :
    patchWrap base n ovL ovR i = base i := by
  unfold patchWrap
  have h1 : ovL.find? (fun p => p.1 == i) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp [hL p hp]
  have h2 : ovR.find? (fun p => n - p.1 == i) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp [hR p hp]
  rw [h1, h2]

def seamModel (tb pb : ℕ) (ov : List (ℕ × Bool)) (d : ℕ) : Bool :=
  patchAt (fun x => if x < 4 then leftBlock tb x else bg110 pb x) 0 ov d

def checkSeamWindow (lo hi tb pb : ℕ) (ov1 ov2 : List (ℕ × Bool)) : Bool :=
  (List.range (hi + 1 - lo)).all fun k =>
    let d := lo + k
    let l := if d = 0 then leftBlock ((tb + 1) % 3) 3 else seamModel tb pb ov1 (d - 1)
    let c := seamModel tb pb ov1 d
    let r := seamModel tb pb ov1 (d + 1)
    let g := seamModel ((tb + 1) % 3) ((pb + 1) % 3) ov2 d
    rule62 l c r == g

lemma seamModel_eq {B t p : ℕ} (hB : 0 < B) (ov : List (ℕ × Bool)) (d : ℕ) (hd : d < 12) :
    patchAt (baseBit B t p) (4 * B - 4) ov (4 * B - 4 + d) =
      seamModel ((t + 2 * (B - 1)) % 3) ((p + (4 * B - 4)) % 3) ov d := by
  induction ov with
  | nil =>
    unfold patchAt seamModel
    simp only [patchAt]
    unfold baseBit
    by_cases hd4 : d < 4
    · rw [if_pos (by omega), if_pos hd4]
      unfold leftBlock
      have h1 : (t + 2 * ((4 * B - 4 + d) / 4)) % 3 =
          ((t + 2 * (B - 1)) % 3 + 2 * (d / 4)) % 3 := by omega
      have h2 : (4 * B - 4 + d) % 4 = d % 4 := by omega
      rw [h1, h2]
    · rw [if_neg (by omega), if_neg hd4]
      unfold bg110
      have h1 : (4 * B - 4 + d + p) % 3 = (d + (p + (4 * B - 4)) % 3) % 3 := by omega
      rw [h1]
  | cons hd' tl ih =>
    unfold patchAt seamModel
    simp only [patchAt, Nat.zero_add]
    have hiff : (4 * B - 4 + d = 4 * B - 4 + hd'.1) ↔ (d = hd'.1) := by omega
    by_cases he : d = hd'.1
    · rw [if_pos (hiff.mpr he), if_pos he]
    · rw [if_neg (fun h => he (hiff.mp h)), if_neg he]
      exact ih

lemma step_seam {n B t p lo hi : ℕ} {ov1 ov2 : List (ℕ × Bool)}
    (hB : 0 < B) (hlo_B : lo = 0 → 2 ≤ B)
    (hlo_ov1 : ∀ q ∈ ov1, lo + 1 ≤ q.1 ∧ q.1 + 1 ≤ hi)
    (hlo_ov2 : ∀ q ∈ ov2, lo ≤ q.1 ∧ q.1 ≤ hi)
    (hhi : hi < 11) (hn : 4 * B - 4 + hi + 2 < n)
    (hseam_left : lo ≤ 3) (hseam_right : 4 ≤ hi)
    (hp : p % 3 = (t + 2 * n) % 3)
    (hcheck : checkSeamWindow lo hi ((t + 2 * (B - 1)) % 3) ((p + (4 * B - 4)) % 3) ov1 ov2 = true) :
    ∀ i : ℕ, i < n →
      rule62 (patchAt (baseBit B t p) (4 * B - 4) ov1 ((i + n - 1) % n))
        (patchAt (baseBit B t p) (4 * B - 4) ov1 i)
        (patchAt (baseBit B t p) (4 * B - 4) ov1 ((i + 1) % n)) =
        patchAt (baseBit B (t + 1) (p + 1)) (4 * B - 4) ov2 i := by
  let a := 4 * B - 4
  intro i hi_n
  have ha_pos : lo = 0 → 4 ≤ a := fun h0 => by have := hlo_B h0; omega
  by_cases hi0 : i = 0
  · subst hi0
    have hm : (0 + n - 1) % n = n - 1 := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hpl : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm, hpl]
    have h_out1 : ∀ q ∈ ov1, n - 1 ≠ a + q.1 := fun q hq => by have := hlo_ov1 q hq; omega
    have h_out2 : ∀ q ∈ ov1, 0 ≠ a + q.1 := fun q hq => by
      have := hlo_ov1 q hq
      by_cases h0 : lo = 0
      · have := ha_pos h0; omega
      · omega
    have h_out3 : ∀ q ∈ ov1, 1 ≠ a + q.1 := fun q hq => by
      have := hlo_ov1 q hq
      by_cases h0 : lo = 0
      · have := ha_pos h0; omega
      · omega
    have h_out4 : ∀ q ∈ ov2, 0 ≠ a + q.1 := fun q hq => by
      have := hlo_ov2 q hq
      by_cases h0 : lo = 0
      · have := ha_pos h0; omega
      · omega
    rw [patchAt_outside _ _ _ _ h_out1, patchAt_outside _ _ _ _ h_out2,
      patchAt_outside _ _ _ _ h_out3, patchAt_outside _ _ _ _ h_out4]
    unfold baseBit
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    exact rule62_wrap_zero n t p (by omega) hp
  · by_cases hil : i = n - 1
    · subst hil
      have hL : (n - 1 + n - 1) % n = n - 2 := by
        have : n - 1 + n - 1 = (n - 2) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (n - 1 + 1) % n = 0 := by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
      rw [hL, hR]
      have h_o1 : ∀ q ∈ ov1, n - 2 ≠ a + q.1 := fun q hq => by have := hlo_ov1 q hq; omega
      have h_o2 : ∀ q ∈ ov1, n - 1 ≠ a + q.1 := fun q hq => by have := hlo_ov1 q hq; omega
      have h_o3 : ∀ q ∈ ov1, 0 ≠ a + q.1 := fun q hq => by
        have := hlo_ov1 q hq
        by_cases h0 : lo = 0
        · have := ha_pos h0; omega
        · omega
      have h_o4 : ∀ q ∈ ov2, n - 1 ≠ a + q.1 := fun q hq => by have := hlo_ov2 q hq; omega
      rw [patchAt_outside _ _ _ _ h_o1, patchAt_outside _ _ _ _ h_o2,
        patchAt_outside _ _ _ _ h_o3, patchAt_outside _ _ _ _ h_o4]
      unfold baseBit
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
      exact rule62_wrap_last n t p (by omega) hp
    · have hL : (i + n - 1) % n = i - 1 := by
        have : i + n - 1 = (i - 1) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hL, hR]
      by_cases hwin : a + lo ≤ i ∧ i ≤ a + hi
      · obtain ⟨k, hk_eq⟩ : ∃ k, i = a + (lo + k) := ⟨i - a - lo, by omega⟩
        have hk_lt : k < hi + 1 - lo := by omega
        have hmem : k ∈ List.range (hi + 1 - lo) := List.mem_range.mpr hk_lt
        have hchk := (List.all_eq_true.mp hcheck) k hmem
        simp only [beq_iff_eq] at hchk
        have hd_lt : lo + k < 12 := by omega
        have hdr_lt : lo + k + 1 < 12 := by omega
        have hc_eq := seamModel_eq (B := B) (t := t) (p := p) hB ov1 (lo + k) hd_lt
        have hr_eq := seamModel_eq (B := B) (t := t) (p := p) hB ov1 (lo + k + 1) hdr_lt
        have hg_eq := seamModel_eq (B := B) (t := t + 1) (p := p + 1) hB ov2 (lo + k) hd_lt
        have htb1 : (t + 1 + 2 * (B - 1)) % 3 = ((t + 2 * (B - 1)) % 3 + 1) % 3 := by omega
        have hpb1 : (p + 1 + (4 * B - 4)) % 3 = ((p + (4 * B - 4)) % 3 + 1) % 3 := by omega
        rw [htb1, hpb1] at hg_eq
        have hl_eq : patchAt (baseBit B t p) (4 * B - 4) ov1 (i - 1) =
            if lo + k = 0 then leftBlock (((t + 2 * (B - 1)) % 3 + 1) % 3) 3
            else seamModel ((t + 2 * (B - 1)) % 3) ((p + (4 * B - 4)) % 3) ov1 (lo + k - 1) := by
          by_cases hlk0 : lo + k = 0
          · rw [if_pos hlk0]
            have hlo0 : lo = 0 := by omega
            have hB2 := hlo_B hlo0
            have h_out : ∀ q ∈ ov1, i - 1 ≠ a + q.1 := fun q hq => by have := hlo_ov1 q hq; omega
            rw [patchAt_outside _ _ _ _ h_out]
            unfold baseBit
            rw [if_pos (by omega)]
            unfold leftBlock
            have hdiv : (i - 1) / 4 = B - 2 := by omega
            have h2 : (i - 1) % 4 = 3 := by omega
            have h34 : 2 * (3 / 4) = 0 := rfl
            have h1 : (t + 2 * (B - 2)) % 3 = ((t + 2 * (B - 1)) % 3 + 1) % 3 := by omega
            have hmod : (((t + 2 * (B - 1)) % 3 + 1) % 3) % 3 = ((t + 2 * (B - 1)) % 3 + 1) % 3 :=
              Nat.mod_mod _ _
            have h3m : 3 % 4 = 3 := rfl
            rw [hdiv, h2, h34, Nat.add_zero, h1, hmod, h3m]
          · rw [if_neg hlk0]
            have his : i - 1 = 4 * B - 4 + (lo + k - 1) := by omega
            rw [his]
            exact seamModel_eq hB ov1 (lo + k - 1) (by omega)
        have his_r : i + 1 = 4 * B - 4 + (lo + k + 1) := by omega
        rw [hl_eq, his_r, hk_eq, hc_eq, hr_eq, hg_eq]
        exact hchk
      · have h_o1 : ∀ q ∈ ov1, i - 1 ≠ a + q.1 := fun q hq => by have := hlo_ov1 q hq; omega
        have h_o2 : ∀ q ∈ ov1, i ≠ a + q.1 := fun q hq => by have := hlo_ov1 q hq; omega
        have h_o3 : ∀ q ∈ ov1, i + 1 ≠ a + q.1 := fun q hq => by have := hlo_ov1 q hq; omega
        have h_o4 : ∀ q ∈ ov2, i ≠ a + q.1 := fun q hq => by have := hlo_ov2 q hq; omega
        rw [patchAt_outside _ _ _ _ h_o1, patchAt_outside _ _ _ _ h_o2,
          patchAt_outside _ _ _ _ h_o3, patchAt_outside _ _ _ _ h_o4]
        by_cases hlt : i < a + lo
        · unfold baseBit
          rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
          exact rule62_leftBlock t i (by omega)
        · unfold baseBit
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          exact rule62_bg110 p i (by omega)

def wrapModelL (tm : ℕ) (ovL : List (ℕ × Bool)) (i : ℕ) : Bool :=
  match ovL.find? (fun p => p.1 == i) with
  | some (_, b) => b
  | none => leftBlock tm i

def wrapModelR (pn : ℕ) (ovR : List (ℕ × Bool)) (d : ℕ) : Bool :=
  match ovR.find? (fun p => p.1 == d) with
  | some (_, b) => b
  | none => decide ((pn + 3 - d % 3) % 3 ≠ 2)

def checkWrapWindow (W tm pn : ℕ) (ovL1 ovR1 ovL2 ovR2 : List (ℕ × Bool)) : Bool :=
  let okL := (List.range W).all fun i =>
    let l := if i = 0 then wrapModelR pn ovR1 1 else wrapModelL tm ovL1 (i - 1)
    let c := wrapModelL tm ovL1 i
    let r := wrapModelL tm ovL1 (i + 1)
    let g := wrapModelL ((tm + 1) % 3) ovL2 i
    rule62 l c r == g
  let okR := [1, 2, 3].all fun d =>
    let l := wrapModelR pn ovR1 (d + 1)
    let c := wrapModelR pn ovR1 d
    let r := if d = 1 then wrapModelL tm ovL1 0 else wrapModelR pn ovR1 (d - 1)
    let g := wrapModelR ((pn + 1) % 3) ovR2 d
    rule62 l c r == g
  okL && okR

lemma patchWrap_eq_L {n B t p W : ℕ} {ovL ovR : List (ℕ × Bool)}
    (hW : W < 4 * B) (hBn : 4 * B + 4 ≤ n)
    (hovR : ∀ q ∈ ovR, 1 ≤ q.1 ∧ q.1 ≤ 2)
    (i : ℕ) (hi : i ≤ W) :
    patchWrap (baseBit B t p) n ovL ovR i = wrapModelL (t % 3) ovL i := by
  unfold patchWrap wrapModelL
  cases hfind : ovL.find? (fun q => q.1 == i) with
  | some v => rfl
  | none =>
    have hR : ovR.find? (fun q => n - q.1 == i) = none := by
      rw [List.find?_eq_none]
      intro q hq
      have := hovR q hq
      simp only [beq_iff_eq]
      omega
    rw [hR]
    unfold baseBit
    rw [if_pos (by omega)]
    rw [leftBlock_mod t i, leftBlock_mod (t % 3) i, Nat.mod_mod]

lemma patchWrap_eq_R {n B t p W : ℕ} {ovL ovR : List (ℕ × Bool)}
    (hW : W < 4 * B) (hBn : 4 * B + 4 ≤ n)
    (hovL : ∀ q ∈ ovL, q.1 < W)
    (hovR : ∀ q ∈ ovR, 1 ≤ q.1 ∧ q.1 ≤ 2)
    (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
    patchWrap (baseBit B t p) n ovL ovR (n - d) = wrapModelR ((p + n) % 3) ovR d := by
  unfold patchWrap wrapModelR
  have hL : ovL.find? (fun q => q.1 == n - d) = none := by
    rw [List.find?_eq_none]
    intro q hq
    have := hovL q hq
    simp only [beq_iff_eq]
    omega
  rw [hL]
  have hfeq : ovR.find? (fun q => n - q.1 == n - d) = ovR.find? (fun q => q.1 == d) := by
    clear hL
    induction ovR with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.find?_cons]
      have hhd := hovR hd (by simp)
      have hiff : (n - hd.1 == n - d) = (hd.1 == d) := by
        simp only [beq_eq_beq]
        omega
      rw [hiff]
      cases hd.1 == d with
      | true => rfl
      | false => exact ih (fun q hq => hovR q (by simp [hq]))
  rw [hfeq]
  cases ovR.find? (fun q => q.1 == d) with
  | some v => rfl
  | none =>
    unfold baseBit
    rw [if_neg (by omega)]
    unfold bg110
    have : (n - d + p) % 3 = ((p + n) % 3 + 3 - d % 3) % 3 := by omega
    rw [this]

lemma step_wrap {n B t p W : ℕ} {ovL1 ovR1 ovL2 ovR2 : List (ℕ × Bool)}
    (hB : 0 < B) (hW0 : 0 < W) (hW : W < 4 * B) (hBn : 4 * B + 4 ≤ n)
    (hrel : (p + 2 * t + 2 * B) % 3 = 0)
    (hovL1 : ∀ q ∈ ovL1, q.1 + 1 < W) (hovL2 : ∀ q ∈ ovL2, q.1 < W)
    (hovR1 : ∀ q ∈ ovR1, 1 ≤ q.1 ∧ q.1 ≤ 2) (hovR2 : ∀ q ∈ ovR2, 1 ≤ q.1 ∧ q.1 ≤ 2)
    (hcheck : checkWrapWindow W (t % 3) ((p + n) % 3) ovL1 ovR1 ovL2 ovR2 = true) :
    ∀ i : ℕ, i < n →
      rule62 (patchWrap (baseBit B t p) n ovL1 ovR1 ((i + n - 1) % n))
        (patchWrap (baseBit B t p) n ovL1 ovR1 i)
        (patchWrap (baseBit B t p) n ovL1 ovR1 ((i + 1) % n)) =
        patchWrap (baseBit B (t + 1) (p + 1)) n ovL2 ovR2 i := by
  have hovL1' : ∀ q ∈ ovL1, q.1 < W := fun q hq => by have := hovL1 q hq; omega
  have hchk := Bool.and_eq_true _ _ |>.mp hcheck
  intro i hi_n
  by_cases hltW : i < W
  · have hmem : i ∈ List.range W := List.mem_range.mpr hltW
    have hstep := List.all_eq_true.mp hchk.1 i hmem
    simp only [beq_iff_eq] at hstep
    have hR : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hR,
      patchWrap_eq_L hW hBn hovR1 i (by omega),
      patchWrap_eq_L hW hBn hovR1 (i + 1) (by omega),
      patchWrap_eq_L hW hBn hovR2 i (by omega)]
    have htm1 : (t + 1) % 3 = (t % 3 + 1) % 3 := by omega
    rw [htm1]
    by_cases hi0 : i = 0
    · subst hi0
      have hL : (0 + n - 1) % n = n - 1 := by
        rw [Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hL, patchWrap_eq_R hW hBn hovL1' hovR1 1 (by decide) (by decide)]
      simpa using hstep
    · have hL : (i + n - 1) % n = i - 1 := by
        have : i + n - 1 = (i - 1) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hL, patchWrap_eq_L hW hBn hovR1 (i - 1) (by omega)]
      simpa [hi0] using hstep
  · by_cases hhiR : n - 3 ≤ i
    · let d := n - i
      have hd1 : 1 ≤ d := by omega
      have hd3 : d ≤ 3 := by omega
      have hi_eq : i = n - d := by omega
      have hd_mem : d ∈ ([1, 2, 3] : List ℕ) := by
        have : d = 1 ∨ d = 2 ∨ d = 3 := by omega
        rcases this with h | h | h <;> simp [h]
      have hstep := List.all_eq_true.mp hchk.2 d hd_mem
      simp only [beq_iff_eq] at hstep
      have hL : (i + n - 1) % n = n - (d + 1) := by
        have : i + n - 1 = (n - (d + 1)) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hL, hi_eq,
        patchWrap_eq_R hW hBn hovL1' hovR1 (d + 1) (by omega) (by omega),
        patchWrap_eq_R hW hBn hovL1' hovR1 d hd1 (by omega),
        patchWrap_eq_R hW hBn hovL2 hovR2 d hd1 (by omega)]
      have hpn1 : (p + 1 + n) % 3 = ((p + n) % 3 + 1) % 3 := by omega
      rw [hpn1]
      by_cases hd_1 : d = 1
      · have hR : (n - d + 1) % n = 0 := by
          have : n - d + 1 = n := by omega
          rw [this, Nat.mod_self]
        rw [hR, patchWrap_eq_L hW hBn hovR1 0 (by omega)]
        simpa [hd_1] using hstep
      · have hR : (n - d + 1) % n = n - (d - 1) := by
          have : n - d + 1 = n - (d - 1) := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
        rw [hR, patchWrap_eq_R hW hBn hovL1' hovR1 (d - 1) (by omega) (by omega)]
        simpa [hd_1] using hstep
    · have hL : (i + n - 1) % n = i - 1 := by
        have : i + n - 1 = (i - 1) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hL, hR,
        patchWrap_outside _ _ _ _ _ (fun q hq => by have := hovL1 q hq; omega) (fun q hq => by have := hovR1 q hq; omega),
        patchWrap_outside _ _ _ _ _ (fun q hq => by have := hovL1 q hq; omega) (fun q hq => by have := hovR1 q hq; omega),
        patchWrap_outside _ _ _ _ _ (fun q hq => by have := hovL1 q hq; omega) (fun q hq => by have := hovR1 q hq; omega),
        patchWrap_outside _ _ _ _ _ (fun q hq => by have := hovL2 q hq; omega) (fun q hq => by have := hovR2 q hq; omega)]
      by_cases hlt1 : i + 1 < 4 * B
      · unfold baseBit
        rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
        exact rule62_leftBlock t i (by omega)
      · by_cases heq1 : i + 1 = 4 * B
        · have hi_eq : i = 4 * B - 1 := by omega
          subst hi_eq
          unfold baseBit
          rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
          have hsub : 4 * B - 1 - 1 = 4 * B - 2 := by omega
          have hadd : 4 * B - 1 + 1 = 4 * B := by omega
          rw [hsub, hadd]
          exact rule62_seam_left B t p hB hrel
        · by_cases heq2 : i = 4 * B
          · subst heq2
            unfold baseBit
            rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            exact rule62_seam_right B t p hB hrel
          · unfold baseBit
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            exact rule62_bg110 p i (by omega)

lemma wallBit_step {n B m t p : ℕ}
    (hB : 0 < B) (hBn : 4 * B + 2 ≤ n) (hBm : 4 * B ≤ m) (hmn : m < n)
    (hm_edge : m = 4 * B → (m + p) % 3 = 0)
    (hrel : (p + 2 * t + 2 * B + 1) % 3 = 0)
    (hp : p % 3 = (t + 2 * n) % 3)
    (hmp : (m + p) % 3 = 0 ∨ (m + p) % 3 = 2) :
    ∀ i : ℕ, i < n →
      rule62 (wallBit B m t p ((i + n - 1) % n)) (wallBit B m t p i) (wallBit B m t p ((i + 1) % n)) =
        wallBit B (if (m + p) % 3 = 0 then m + 1 else m) (t + 1) (p + 1) i := by
  intro i hi_n
  by_cases hi0 : i = 0
  · subst hi0
    have hL : (0 + n - 1) % n = n - 1 := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hR : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hL, hR]
    unfold wallBit
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    exact rule62_wrap_zero n t p (by omega) hp
  · by_cases hil : i = n - 1
    · subst hil
      have hL : (n - 1 + n - 1) % n = n - 2 := by
        have : n - 1 + n - 1 = (n - 2) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (n - 1 + 1) % n = 0 := by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
      rw [hL, hR]
      by_cases hmn1 : m = n - 1
      · subst hmn1
        rcases hmp with h0 | h2
        · have vL : wallBit B (n - 1) t p (n - 2) = true := by
            unfold wallBit; rw [if_neg (by omega), if_pos (by omega)]
            exact bg110_eq_true (by omega)
          have vC : wallBit B (n - 1) t p (n - 1) = true := by
            unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
            exact bg110_eq_true (by omega)
          have vR : wallBit B (n - 1) t p 0 = true := by
            unfold wallBit; rw [if_pos (by omega)]
            rw [leftBlock_eq_one (by omega)]; decide
          have vG : wallBit B (if (n - 1 + p) % 3 = 0 then n - 1 + 1 else n - 1) (t + 1) (p + 1) (n - 1) = false := by
            unfold wallBit; rw [if_pos h0, if_neg (by omega), if_pos (by omega)]
            exact bg110_eq_false (by omega)
          rw [vL, vC, vR, vG]; rfl
        · have hne0 : (n - 1 + p) % 3 ≠ 0 := by omega
          have vL : wallBit B (n - 1) t p (n - 2) = false := by
            unfold wallBit; rw [if_neg (by omega), if_pos (by omega)]
            exact bg110_eq_false (by omega)
          have vC : wallBit B (n - 1) t p (n - 1) = false := by
            unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
            exact bg110_eq_false (by omega)
          have vR : wallBit B (n - 1) t p 0 = true := by
            unfold wallBit; rw [if_pos (by omega)]
            exact leftBlock_eq_zero (by omega)
          have vG : wallBit B (if (n - 1 + p) % 3 = 0 then n - 1 + 1 else n - 1) (t + 1) (p + 1) (n - 1) = true := by
            unfold wallBit; rw [if_neg hne0, if_neg (by omega), if_neg (by omega)]
            exact bg110_eq_true (by omega)
          rw [vL, vC, vR, vG]; rfl
      · have vL : wallBit B m t p (n - 2) = bg110 p (n - 2) := by
          unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
        have vC : wallBit B m t p (n - 1) = bg110 p (n - 1) := by
          unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
        have vR : wallBit B m t p 0 = leftBlock t 0 := by
          unfold wallBit; rw [if_pos (by omega)]
        have vG : wallBit B (if (m + p) % 3 = 0 then m + 1 else m) (t + 1) (p + 1) (n - 1) = bg110 (p + 1) (n - 1) := by
          unfold wallBit
          have hnot : ¬ (n - 1 < if (m + p) % 3 = 0 then m + 1 else m) := by split <;> omega
          rw [if_neg (by omega), if_neg hnot]
        rw [vL, vC, vR, vG]
        exact rule62_wrap_last n t p (by omega) hp
    · have hL : (i + n - 1) % n = i - 1 := by
        have : i + n - 1 = (i - 1) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hL, hR]
      by_cases h1 : i + 1 < 4 * B
      · unfold wallBit
        rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
        exact rule62_leftBlock t i (by omega)
      · by_cases h2 : i + 1 = 4 * B
        · have hi_eq : i = 4 * B - 1 := by omega
          subst hi_eq
          have vL : wallBit B m t p (4 * B - 1 - 1) = leftBlock t (4 * B - 2) := by
            have : 4 * B - 1 - 1 = 4 * B - 2 := by omega
            rw [this]; unfold wallBit; rw [if_pos (by omega)]
          have vC : wallBit B m t p (4 * B - 1) = leftBlock t (4 * B - 1) := by
            unfold wallBit; rw [if_pos (by omega)]
          have vR : wallBit B m t p (4 * B - 1 + 1) = bg110 (p + 1) (4 * B) := by
            have : 4 * B - 1 + 1 = 4 * B := by omega
            rw [this]; unfold wallBit; rw [if_neg (by omega)]
            by_cases hmeq : 4 * B < m
            · rw [if_pos hmeq]
            · rw [if_neg hmeq]
              have h0 := hm_edge (by omega)
              rw [bg110_eq_true (by omega), bg110_eq_true (by omega)]
          have vG : wallBit B (if (m + p) % 3 = 0 then m + 1 else m) (t + 1) (p + 1) (4 * B - 1) =
              leftBlock (t + 1) (4 * B - 1) := by
            unfold wallBit; rw [if_pos (by omega)]
          rw [vL, vC, vR, vG]
          exact rule62_seam_left B t (p + 1) hB (by omega)
        · by_cases h3 : i = 4 * B
          · subst h3
            by_cases hmeq : 4 * B = m
            · subst hmeq
              have h0 := hm_edge rfl
              have vL : wallBit B (4 * B) t p (4 * B - 1) = true := by
                unfold wallBit; rw [if_pos (by omega)]
                rw [leftBlock_eq_two (by omega)]
                have hm4 : (4 * B - 1) % 4 = 3 := by omega
                simp [hm4]
              have vC : wallBit B (4 * B) t p (4 * B) = true := by
                unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
                exact bg110_eq_true (by omega)
              have vR : wallBit B (4 * B) t p (4 * B + 1) = true := by
                unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
                exact bg110_eq_true (by omega)
              have vG : wallBit B (if (4 * B + p) % 3 = 0 then 4 * B + 1 else 4 * B) (t + 1) (p + 1) (4 * B) = false := by
                unfold wallBit; rw [if_pos h0, if_neg (by omega), if_pos (by omega)]
                exact bg110_eq_false (by omega)
              rw [vL, vC, vR, vG]; rfl
            · by_cases hm1 : 4 * B + 1 = m
              · subst hm1
                have hlt_n : 4 * B < if (4 * B + 1 + p) % 3 = 0 then 4 * B + 1 + 1 else 4 * B + 1 := by split <;> omega
                rcases hmp with h0 | h2'
                · have vL : wallBit B (4 * B + 1) t p (4 * B - 1) = false := by
                    unfold wallBit; rw [if_pos (by omega)]
                    rw [leftBlock_eq_one (by omega)]
                    have hm4 : (4 * B - 1) % 4 = 3 := by omega
                    simp [hm4]
                  have vC : wallBit B (4 * B + 1) t p (4 * B) = true := by
                    unfold wallBit; rw [if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_true (by omega)
                  have vR : wallBit B (4 * B + 1) t p (4 * B + 1) = true := by
                    unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
                    exact bg110_eq_true (by omega)
                  have vG : wallBit B (if (4 * B + 1 + p) % 3 = 0 then 4 * B + 1 + 1 else 4 * B + 1) (t + 1) (p + 1) (4 * B) = true := by
                    unfold wallBit; rw [if_neg (by omega), if_pos hlt_n]
                    exact bg110_eq_true (by omega)
                  rw [vL, vC, vR, vG]; rfl
                · have vL : wallBit B (4 * B + 1) t p (4 * B - 1) = true := by
                    unfold wallBit; rw [if_pos (by omega)]
                    exact leftBlock_eq_zero (by omega)
                  have vC : wallBit B (4 * B + 1) t p (4 * B) = false := by
                    unfold wallBit; rw [if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_false (by omega)
                  have vR : wallBit B (4 * B + 1) t p (4 * B + 1) = false := by
                    unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
                    exact bg110_eq_false (by omega)
                  have vG : wallBit B (if (4 * B + 1 + p) % 3 = 0 then 4 * B + 1 + 1 else 4 * B + 1) (t + 1) (p + 1) (4 * B) = true := by
                    unfold wallBit; rw [if_neg (by omega), if_pos hlt_n]
                    exact bg110_eq_true (by omega)
                  rw [vL, vC, vR, vG]; rfl
              · have hlt_n : 4 * B < if (m + p) % 3 = 0 then m + 1 else m := by split <;> omega
                unfold wallBit
                rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
                  if_pos (by omega), if_neg (by omega), if_pos hlt_n]
                exact rule62_seam_right B t (p + 1) hB (by omega)
          · by_cases h4 : i + 1 < m
            · have hlt_n : i < if (m + p) % 3 = 0 then m + 1 else m := by split <;> omega
              unfold wallBit
              rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
                if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos hlt_n]
              exact rule62_bg110 (p + 1) i (by omega)
            · by_cases h5 : i + 1 = m
              · subst h5
                have hlt_n : i < if (i + 1 + p) % 3 = 0 then i + 1 + 1 else i + 1 := by split <;> omega
                rcases hmp with h0 | h2'
                · have vL : wallBit B (i + 1) t p (i - 1) = false := by
                    unfold wallBit; rw [if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_false (by omega)
                  have vC : wallBit B (i + 1) t p i = true := by
                    unfold wallBit; rw [if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_true (by omega)
                  have vR : wallBit B (i + 1) t p (i + 1) = true := by
                    unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
                    exact bg110_eq_true (by omega)
                  have vG : wallBit B (if (i + 1 + p) % 3 = 0 then i + 1 + 1 else i + 1) (t + 1) (p + 1) i = true := by
                    unfold wallBit; rw [if_neg (by omega), if_pos hlt_n]
                    exact bg110_eq_true (by omega)
                  rw [vL, vC, vR, vG]; rfl
                · have vL : wallBit B (i + 1) t p (i - 1) = true := by
                    unfold wallBit; rw [if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_true (by omega)
                  have vC : wallBit B (i + 1) t p i = false := by
                    unfold wallBit; rw [if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_false (by omega)
                  have vR : wallBit B (i + 1) t p (i + 1) = false := by
                    unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
                    exact bg110_eq_false (by omega)
                  have vG : wallBit B (if (i + 1 + p) % 3 = 0 then i + 1 + 1 else i + 1) (t + 1) (p + 1) i = true := by
                    unfold wallBit; rw [if_neg (by omega), if_pos hlt_n]
                    exact bg110_eq_true (by omega)
                  rw [vL, vC, vR, vG]; rfl
              · by_cases h6 : i = m
                · subst h6
                  rcases hmp with h0 | h2'
                  · have vL : wallBit B i t p (i - 1) = true := by
                      unfold wallBit; rw [if_neg (by omega), if_pos (by omega)]
                      exact bg110_eq_true (by omega)
                    have vC : wallBit B i t p i = true := by
                      unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
                      exact bg110_eq_true (by omega)
                    have vR : wallBit B i t p (i + 1) = true := by
                      unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
                      exact bg110_eq_true (by omega)
                    have vG : wallBit B (if (i + p) % 3 = 0 then i + 1 else i) (t + 1) (p + 1) i = false := by
                      unfold wallBit; rw [if_pos h0, if_neg (by omega), if_pos (by omega)]
                      exact bg110_eq_false (by omega)
                    rw [vL, vC, vR, vG]; rfl
                  · have hne0 : (i + p) % 3 ≠ 0 := by omega
                    have vL : wallBit B i t p (i - 1) = false := by
                      unfold wallBit; rw [if_neg (by omega), if_pos (by omega)]
                      exact bg110_eq_false (by omega)
                    have vC : wallBit B i t p i = false := by
                      unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
                      exact bg110_eq_false (by omega)
                    have vR : wallBit B i t p (i + 1) = true := by
                      unfold wallBit; rw [if_neg (by omega), if_neg (by omega)]
                      exact bg110_eq_true (by omega)
                    have vG : wallBit B (if (i + p) % 3 = 0 then i + 1 else i) (t + 1) (p + 1) i = true := by
                      unfold wallBit; rw [if_neg hne0, if_neg (by omega), if_neg (by omega)]
                      exact bg110_eq_true (by omega)
                    rw [vL, vC, vR, vG]; rfl
                · have hnot : ¬ (i < if (m + p) % 3 = 0 then m + 1 else m) := by split <;> omega
                  unfold wallBit
                  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
                    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hnot]
                  exact rule62_bg110 p i (by omega)

lemma wallBit_reach_end {n B : ℕ} (hB : 0 < B) (hBn : 4 * B + 2 ≤ n)
    (hrel : ∀ t : ℕ, (t + 2 * n + 2 * t + 2 * B + 1) % 3 = 0) :
    ∀ d m t : ℕ, 0 < d → m + d = n → 4 * B ≤ m → (m + t + 2 * n) % 3 = 0 →
      Matches n (rowM n t) (wallBit B m t (t + 2 * n)) →
      ∃ T : ℕ, T % 3 = 2 ∧ Matches n (rowM n T) (baseBit B T (T + 2 * n + 1)) := by
  intro d
  induction d with
  | zero => intro _ _ h; omega
  | succ d ih =>
    intro m t _ hmd hBm hmp hmatch
    by_cases hd0 : d = 0
    · subst hd0
      have h1 := matches_step (by omega) hmatch
        (wallBit_step hB hBn hBm (by omega) (fun _ => by omega) (hrel t) rfl (Or.inl (by omega)))
      rw [← rowM_succ, if_pos (by omega)] at h1
      refine ⟨t + 1, by omega, matches_congr h1 ?_⟩
      intro i hi
      unfold wallBit baseBit
      by_cases hlt : i < 4 * B
      · rw [if_pos hlt, if_pos hlt]
      · rw [if_neg hlt, if_neg hlt, if_pos (by omega)]
        have : t + 2 * n + 1 + 1 = t + 1 + 2 * n + 1 := by omega
        rw [this]
    · have h1 := matches_step (by omega) hmatch
        (wallBit_step hB hBn hBm (by omega) (fun _ => by omega) (hrel t) rfl (Or.inl (by omega)))
      rw [← rowM_succ, if_pos (by omega)] at h1
      have h1' : Matches n (rowM n (t + 1)) (wallBit B (m + 1) (t + 1) (t + 1 + 2 * n)) := by
        refine matches_congr h1 ?_
        intro i _
        have : t + 2 * n + 1 = t + 1 + 2 * n := by omega
        rw [this]
      have h2 := matches_step (by omega) h1'
        (wallBit_step hB hBn (by omega) (by omega) (fun _ => by omega) (hrel (t + 1)) rfl (Or.inr (by omega)))
      rw [← rowM_succ, if_neg (by omega)] at h2
      have h2' : Matches n (rowM n (t + 2)) (wallBit B (m + 1) (t + 2) (t + 2 + 2 * n)) := by
        refine matches_congr h2 ?_
        intro i _
        have : t + 1 + 2 * n + 1 = t + 2 + 2 * n := by omega
        rw [this]
      exact ih (m + 1) (t + 2) (by omega) (by omega) (by omega) (by omega) h2'

lemma wall2Bit_step {n B m1 m2 t p : ℕ}
    (hB : 0 < B) (hBn : 4 * B + 4 ≤ n) (hBm1 : 4 * B < m1) (hm12 : m1 + 2 ≤ m2) (hm2n : m2 < n)
    (hrel : (p + 2 * t + 2 * B + 2) % 3 = 0)
    (hp : p % 3 = (t + 2 * n) % 3)
    (h1p : (m1 + p + 1) % 3 = 0 ∨ (m1 + p + 1) % 3 = 2)
    (h2p : (m2 + p) % 3 = 0 ∨ (m2 + p) % 3 = 2) :
    ∀ i : ℕ, i < n →
      rule62 (wall2Bit B m1 m2 t p ((i + n - 1) % n))
        (wall2Bit B m1 m2 t p i)
        (wall2Bit B m1 m2 t p ((i + 1) % n)) =
        wall2Bit B (if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1)
          (if (m2 + p) % 3 = 0 then m2 + 1 else m2) (t + 1) (p + 1) i := by
  intro i hi_n
  by_cases hi0 : i = 0
  · subst hi0
    have hL : (0 + n - 1) % n = n - 1 := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hR : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hL, hR]
    unfold wall2Bit
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega)]
    exact rule62_wrap_zero n t p (by omega) hp
  · by_cases hil : i = n - 1
    · subst hil
      have hL : (n - 1 + n - 1) % n = n - 2 := by
        have : n - 1 + n - 1 = (n - 2) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (n - 1 + 1) % n = 0 := by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
      rw [hL, hR]
      by_cases hmn1 : m2 = n - 1
      · subst hmn1
        have hnot1 : ¬ (n - 1 < if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1) := by split <;> omega
        rcases h2p with h0 | h2
        · have vL : wall2Bit B m1 (n - 1) t p (n - 2) = true := by
            unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
            exact bg110_eq_true (by omega)
          have vC : wall2Bit B m1 (n - 1) t p (n - 1) = true := by
            unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            exact bg110_eq_true (by omega)
          have vR : wall2Bit B m1 (n - 1) t p 0 = true := by
            unfold wall2Bit; rw [if_pos (by omega)]
            rw [leftBlock_eq_one (by omega)]; decide
          have vG : wall2Bit B (if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1)
              (if (n - 1 + p) % 3 = 0 then n - 1 + 1 else n - 1) (t + 1) (p + 1) (n - 1) = false := by
            unfold wall2Bit; rw [if_pos h0, if_neg (by omega), if_neg hnot1, if_pos (by omega)]
            exact bg110_eq_false (by omega)
          rw [vL, vC, vR, vG]; rfl
        · have hne0 : (n - 1 + p) % 3 ≠ 0 := by omega
          have vL : wall2Bit B m1 (n - 1) t p (n - 2) = false := by
            unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
            exact bg110_eq_false (by omega)
          have vC : wall2Bit B m1 (n - 1) t p (n - 1) = false := by
            unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            exact bg110_eq_false (by omega)
          have vR : wall2Bit B m1 (n - 1) t p 0 = true := by
            unfold wall2Bit; rw [if_pos (by omega)]
            exact leftBlock_eq_zero (by omega)
          have vG : wall2Bit B (if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1)
              (if (n - 1 + p) % 3 = 0 then n - 1 + 1 else n - 1) (t + 1) (p + 1) (n - 1) = true := by
            unfold wall2Bit; rw [if_neg hne0, if_neg (by omega), if_neg hnot1, if_neg (by omega)]
            exact bg110_eq_true (by omega)
          rw [vL, vC, vR, vG]; rfl
      · have hnot1 : ¬ (n - 1 < if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1) := by split <;> omega
        have hnot2 : ¬ (n - 1 < if (m2 + p) % 3 = 0 then m2 + 1 else m2) := by split <;> omega
        have vL : wall2Bit B m1 m2 t p (n - 2) = bg110 p (n - 2) := by
          unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have vC : wall2Bit B m1 m2 t p (n - 1) = bg110 p (n - 1) := by
          unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have vR : wall2Bit B m1 m2 t p 0 = leftBlock t 0 := by
          unfold wall2Bit; rw [if_pos (by omega)]
        have vG : wall2Bit B (if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1)
            (if (m2 + p) % 3 = 0 then m2 + 1 else m2) (t + 1) (p + 1) (n - 1) = bg110 (p + 1) (n - 1) := by
          unfold wall2Bit; rw [if_neg (by omega), if_neg hnot1, if_neg hnot2]
        rw [vL, vC, vR, vG]
        exact rule62_wrap_last n t p (by omega) hp
    · have hL : (i + n - 1) % n = i - 1 := by
        have : i + n - 1 = (i - 1) + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hR : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hL, hR]
      by_cases h1 : i + 1 < 4 * B
      · unfold wall2Bit
        rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
        exact rule62_leftBlock t i (by omega)
      · by_cases h2 : i + 1 = 4 * B
        · have hi_eq : i = 4 * B - 1 := by omega
          subst hi_eq
          have hsub : 4 * B - 1 - 1 = 4 * B - 2 := by omega
          have hadd : 4 * B - 1 + 1 = 4 * B := by omega
          rw [hsub, hadd]
          unfold wall2Bit
          rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega)]
          exact rule62_seam_left B t (p + 2) hB (by omega)
        · by_cases h3 : i = 4 * B
          · subst h3
            by_cases hm1eq : 4 * B + 1 = m1
            · subst hm1eq
              have hlt1 : 4 * B < if (4 * B + 1 + p + 1) % 3 = 0 then 4 * B + 1 + 1 else 4 * B + 1 := by split <;> omega
              rcases h1p with h0 | h2'
              · have vL : wall2Bit B (4 * B + 1) m2 t p (4 * B - 1) = false := by
                  unfold wall2Bit; rw [if_pos (by omega), leftBlock_eq_one (by omega)]
                  have hm4 : (4 * B - 1) % 4 = 3 := by omega
                  simp [hm4]
                have vC : wall2Bit B (4 * B + 1) m2 t p (4 * B) = true := by
                  unfold wall2Bit; rw [if_neg (by omega), if_pos (by omega)]
                  exact bg110_eq_true (by omega)
                have vR : wall2Bit B (4 * B + 1) m2 t p (4 * B + 1) = true := by
                  unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                  exact bg110_eq_true (by omega)
                have vG : wall2Bit B (if (4 * B + 1 + p + 1) % 3 = 0 then 4 * B + 1 + 1 else 4 * B + 1)
                    (if (m2 + p) % 3 = 0 then m2 + 1 else m2) (t + 1) (p + 1) (4 * B) = true := by
                  unfold wall2Bit; rw [if_neg (by omega), if_pos hlt1]
                  exact bg110_eq_true (by omega)
                rw [vL, vC, vR, vG]; rfl
              · have vL : wall2Bit B (4 * B + 1) m2 t p (4 * B - 1) = true := by
                  unfold wall2Bit; rw [if_pos (by omega)]
                  exact leftBlock_eq_zero (by omega)
                have vC : wall2Bit B (4 * B + 1) m2 t p (4 * B) = false := by
                  unfold wall2Bit; rw [if_neg (by omega), if_pos (by omega)]
                  exact bg110_eq_false (by omega)
                have vR : wall2Bit B (4 * B + 1) m2 t p (4 * B + 1) = false := by
                  unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                  exact bg110_eq_false (by omega)
                have vG : wall2Bit B (if (4 * B + 1 + p + 1) % 3 = 0 then 4 * B + 1 + 1 else 4 * B + 1)
                    (if (m2 + p) % 3 = 0 then m2 + 1 else m2) (t + 1) (p + 1) (4 * B) = true := by
                  unfold wall2Bit; rw [if_neg (by omega), if_pos hlt1]
                  exact bg110_eq_true (by omega)
                rw [vL, vC, vR, vG]; rfl
            · have hlt1 : 4 * B < if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1 := by split <;> omega
              unfold wall2Bit
              rw [if_pos (by omega), if_neg (by omega), if_pos (by omega),
                if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos hlt1]
              have hadd : p + 1 + 2 = (p + 2) + 1 := by omega
              rw [hadd]
              exact rule62_seam_right B t (p + 2) hB (by omega)
          · by_cases h4 : i + 1 < m1
            · have hlt1 : i < if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1 := by split <;> omega
              unfold wall2Bit
              rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
                if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos hlt1]
              have hadd : p + 1 + 2 = (p + 2) + 1 := by omega
              rw [hadd]
              exact rule62_bg110 (p + 2) i (by omega)
            · by_cases h5 : i + 1 = m1
              · subst h5
                have hlt1 : i < if (i + 1 + p + 1) % 3 = 0 then i + 1 + 1 else i + 1 := by split <;> omega
                rcases h1p with h0 | h2'
                · have vL : wall2Bit B (i + 1) m2 t p (i - 1) = false := by
                    unfold wall2Bit; rw [if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_false (by omega)
                  have vC : wall2Bit B (i + 1) m2 t p i = true := by
                    unfold wall2Bit; rw [if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_true (by omega)
                  have vR : wall2Bit B (i + 1) m2 t p (i + 1) = true := by
                    unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_true (by omega)
                  have vG : wall2Bit B (if (i + 1 + p + 1) % 3 = 0 then i + 1 + 1 else i + 1)
                      (if (m2 + p) % 3 = 0 then m2 + 1 else m2) (t + 1) (p + 1) i = true := by
                    unfold wall2Bit; rw [if_neg (by omega), if_pos hlt1]
                    exact bg110_eq_true (by omega)
                  rw [vL, vC, vR, vG]; rfl
                · have vL : wall2Bit B (i + 1) m2 t p (i - 1) = true := by
                    unfold wall2Bit; rw [if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_true (by omega)
                  have vC : wall2Bit B (i + 1) m2 t p i = false := by
                    unfold wall2Bit; rw [if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_false (by omega)
                  have vR : wall2Bit B (i + 1) m2 t p (i + 1) = false := by
                    unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                    exact bg110_eq_false (by omega)
                  have vG : wall2Bit B (if (i + 1 + p + 1) % 3 = 0 then i + 1 + 1 else i + 1)
                      (if (m2 + p) % 3 = 0 then m2 + 1 else m2) (t + 1) (p + 1) i = true := by
                    unfold wall2Bit; rw [if_neg (by omega), if_pos hlt1]
                    exact bg110_eq_true (by omega)
                  rw [vL, vC, vR, vG]; rfl
              · by_cases h6 : i = m1
                · subst h6
                  rcases h1p with h0 | h2'
                  · have vL : wall2Bit B i m2 t p (i - 1) = true := by
                      unfold wall2Bit; rw [if_neg (by omega), if_pos (by omega)]
                      exact bg110_eq_true (by omega)
                    have vC : wall2Bit B i m2 t p i = true := by
                      unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                      exact bg110_eq_true (by omega)
                    have vR : wall2Bit B i m2 t p (i + 1) = true := by
                      unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                      exact bg110_eq_true (by omega)
                    have vG : wall2Bit B (if (i + p + 1) % 3 = 0 then i + 1 else i)
                        (if (m2 + p) % 3 = 0 then m2 + 1 else m2) (t + 1) (p + 1) i = false := by
                      unfold wall2Bit; rw [if_pos h0, if_neg (by omega), if_pos (by omega)]
                      exact bg110_eq_false (by omega)
                    rw [vL, vC, vR, vG]; rfl
                  · have hne0 : (i + p + 1) % 3 ≠ 0 := by omega
                    have hlt2 : i < if (m2 + p) % 3 = 0 then m2 + 1 else m2 := by split <;> omega
                    have vL : wall2Bit B i m2 t p (i - 1) = false := by
                      unfold wall2Bit; rw [if_neg (by omega), if_pos (by omega)]
                      exact bg110_eq_false (by omega)
                    have vC : wall2Bit B i m2 t p i = false := by
                      unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                      exact bg110_eq_false (by omega)
                    have vR : wall2Bit B i m2 t p (i + 1) = true := by
                      unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                      exact bg110_eq_true (by omega)
                    have vG : wall2Bit B (if (i + p + 1) % 3 = 0 then i + 1 else i)
                        (if (m2 + p) % 3 = 0 then m2 + 1 else m2) (t + 1) (p + 1) i = true := by
                      unfold wall2Bit; rw [if_neg hne0, if_neg (by omega), if_neg (by omega), if_pos hlt2]
                      exact bg110_eq_true (by omega)
                    rw [vL, vC, vR, vG]; rfl
                · by_cases h7 : i + 1 < m2
                  · have hnot1 : ¬ (i < if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1) := by split <;> omega
                    have hlt2 : i < if (m2 + p) % 3 = 0 then m2 + 1 else m2 := by split <;> omega
                    unfold wall2Bit
                    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
                      if_neg (by omega), if_neg (by omega), if_pos (by omega),
                      if_neg (by omega), if_neg (by omega), if_pos (by omega),
                      if_neg (by omega), if_neg hnot1, if_pos hlt2]
                    exact rule62_bg110 (p + 1) i (by omega)
                  · by_cases h8 : i + 1 = m2
                    · subst h8
                      have hnot1 : ¬ (i < if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1) := by
                        by_cases hm1i : m1 + 1 = i
                        · subst hm1i
                          have hne : ¬ ((m1 + p + 1) % 3 = 0) := by
                            rcases h1p with h0 | h2'
                            · rcases h2p with h20 | h22 <;> omega
                            · omega
                          rw [if_neg hne]; omega
                        · split <;> omega
                      have hlt2 : i < if (i + 1 + p) % 3 = 0 then i + 1 + 1 else i + 1 := by split <;> omega
                      rcases h2p with h0 | h2'
                      · have vL : wall2Bit B m1 (i + 1) t p (i - 1) = false := by
                          unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                          exact bg110_eq_false (by omega)
                        have vC : wall2Bit B m1 (i + 1) t p i = true := by
                          unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                          exact bg110_eq_true (by omega)
                        have vR : wall2Bit B m1 (i + 1) t p (i + 1) = true := by
                          unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                          exact bg110_eq_true (by omega)
                        have vG : wall2Bit B (if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1)
                            (if (i + 1 + p) % 3 = 0 then i + 1 + 1 else i + 1) (t + 1) (p + 1) i = true := by
                          unfold wall2Bit; rw [if_neg (by omega), if_neg hnot1, if_pos hlt2]
                          exact bg110_eq_true (by omega)
                        rw [vL, vC, vR, vG]; rfl
                      · have vL : wall2Bit B m1 (i + 1) t p (i - 1) = true := by
                          unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                          exact bg110_eq_true (by omega)
                        have vC : wall2Bit B m1 (i + 1) t p i = false := by
                          unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                          exact bg110_eq_false (by omega)
                        have vR : wall2Bit B m1 (i + 1) t p (i + 1) = false := by
                          unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                          exact bg110_eq_false (by omega)
                        have vG : wall2Bit B (if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1)
                            (if (i + 1 + p) % 3 = 0 then i + 1 + 1 else i + 1) (t + 1) (p + 1) i = true := by
                          unfold wall2Bit; rw [if_neg (by omega), if_neg hnot1, if_pos hlt2]
                          exact bg110_eq_true (by omega)
                        rw [vL, vC, vR, vG]; rfl
                    · by_cases h9 : i = m2
                      · subst h9
                        have hnot1 : ¬ (i < if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1) := by split <;> omega
                        rcases h2p with h0 | h2'
                        · have vL : wall2Bit B m1 i t p (i - 1) = true := by
                            unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                            exact bg110_eq_true (by omega)
                          have vC : wall2Bit B m1 i t p i = true := by
                            unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                            exact bg110_eq_true (by omega)
                          have vR : wall2Bit B m1 i t p (i + 1) = true := by
                            unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                            exact bg110_eq_true (by omega)
                          have vG : wall2Bit B (if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1)
                              (if (i + p) % 3 = 0 then i + 1 else i) (t + 1) (p + 1) i = false := by
                            unfold wall2Bit; rw [if_pos h0, if_neg (by omega), if_neg hnot1, if_pos (by omega)]
                            exact bg110_eq_false (by omega)
                          rw [vL, vC, vR, vG]; rfl
                        · have hne0 : (i + p) % 3 ≠ 0 := by omega
                          have vL : wall2Bit B m1 i t p (i - 1) = false := by
                            unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
                            exact bg110_eq_false (by omega)
                          have vC : wall2Bit B m1 i t p i = false := by
                            unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                            exact bg110_eq_false (by omega)
                          have vR : wall2Bit B m1 i t p (i + 1) = true := by
                            unfold wall2Bit; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                            exact bg110_eq_true (by omega)
                          have vG : wall2Bit B (if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1)
                              (if (i + p) % 3 = 0 then i + 1 else i) (t + 1) (p + 1) i = true := by
                            unfold wall2Bit; rw [if_neg hne0, if_neg (by omega), if_neg hnot1, if_neg (by omega)]
                            exact bg110_eq_true (by omega)
                          rw [vL, vC, vR, vG]; rfl
                      · have hnot1 : ¬ (i < if (m1 + p + 1) % 3 = 0 then m1 + 1 else m1) := by split <;> omega
                        have hnot2 : ¬ (i < if (m2 + p) % 3 = 0 then m2 + 1 else m2) := by split <;> omega
                        unfold wall2Bit
                        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
                          if_neg (by omega), if_neg (by omega), if_neg (by omega),
                          if_neg (by omega), if_neg (by omega), if_neg (by omega),
                          if_neg (by omega), if_neg hnot1, if_neg hnot2]
                        exact rule62_bg110 p i (by omega)

lemma wall2Bit_reach_end {n B : ℕ} (hB : 0 < B) (hBn : 4 * B + 4 ≤ n)
    (hrel : ∀ t : ℕ, (t + 2 * n + 2 * t + 2 * B + 2) % 3 = 0) :
    ∀ d m1 t : ℕ, 0 < d → m1 + 2 + d = n → 4 * B < m1 →
      (m1 + t + 2 * n + 1) % 3 = 2 → (m1 + 2 + t + 2 * n) % 3 = 0 →
      Matches n (rowM n t) (wall2Bit B m1 (m1 + 2) t (t + 2 * n)) →
      ∃ T : ℕ, T % 3 = 2 ∧
        Matches n (rowM n T) (patchWrap (baseBit B T (T + 2 * n + 2)) n [] [(2, true), (1, false)]) := by
  intro d
  induction d with
  | zero => intro _ _ h; omega
  | succ d ih =>
    intro m1 t _ hmd hBm1 h1p h2p hmatch
    by_cases hd0 : d = 0
    · subst hd0
      have h1 := matches_step (by omega) hmatch
        (wall2Bit_step hB hBn hBm1 (by omega) (by omega) (hrel t) rfl (Or.inr (by omega)) (Or.inl (by omega)))
      rw [← rowM_succ, if_neg (by omega), if_pos (by omega)] at h1
      refine ⟨t + 1, by omega, matches_congr h1 ?_⟩
      intro i hi
      unfold wall2Bit patchWrap baseBit
      simp only [List.find?_nil, List.find?_cons]
      by_cases hlt : i < 4 * B
      · rw [if_pos hlt]
        have hne2 : (n - 2 == i) = false := beq_false_of_ne (by omega)
        have hne1 : (n - 1 == i) = false := beq_false_of_ne (by omega)
        simp [hne2, hne1, hlt]
      · rw [if_neg hlt]
        by_cases hlt1 : i < m1
        · rw [if_pos hlt1]
          have hne2 : (n - 2 == i) = false := beq_false_of_ne (by omega)
          have hne1 : (n - 1 == i) = false := beq_false_of_ne (by omega)
          simp only [hne2, hne1, if_neg hlt]
          unfold bg110
          have : (i + (t + 2 * n + 1 + 2)) % 3 = (i + (t + 1 + 2 * n + 2)) % 3 := by omega
          rw [this]
        · rw [if_neg hlt1, if_pos (by omega)]
          by_cases hi2 : i = n - 2
          · subst hi2
            simp only [beq_self_eq_true]
            exact bg110_eq_true (by omega)
          · by_cases hi1 : i = n - 1
            · subst hi1
              have hne2 : (n - 2 == n - 1) = false := beq_false_of_ne (by omega)
              simp only [hne2, beq_self_eq_true]
              exact bg110_eq_false (by omega)
            · have hi3 : i = n - 3 := by omega
              subst hi3
              have hne2 : (n - 2 == n - 3) = false := beq_false_of_ne (by omega)
              have hne1 : (n - 1 == n - 3) = false := beq_false_of_ne (by omega)
              simp only [hne2, hne1, if_neg hlt]
              rw [bg110_eq_true (by omega), bg110_eq_true (by omega)]
    · have h1 := matches_step (by omega) hmatch
        (wall2Bit_step hB hBn hBm1 (by omega) (by omega) (hrel t) rfl (Or.inr (by omega)) (Or.inl (by omega)))
      rw [← rowM_succ, if_neg (by omega), if_pos (by omega)] at h1
      have h1' : Matches n (rowM n (t + 1)) (wall2Bit B m1 (m1 + 3) (t + 1) (t + 1 + 2 * n)) := by
        refine matches_congr h1 ?_
        intro i _
        have hm3 : m1 + 2 + 1 = m1 + 3 := by omega
        have hp1 : t + 2 * n + 1 = t + 1 + 2 * n := by omega
        rw [hm3, hp1]
      have h2 := matches_step (by omega) h1'
        (wall2Bit_step hB hBn hBm1 (by omega) (by omega) (hrel (t + 1)) rfl (Or.inl (by omega)) (Or.inr (by omega)))
      rw [← rowM_succ, if_pos (by omega), if_neg (by omega)] at h2
      have h2' : Matches n (rowM n (t + 2)) (wall2Bit B (m1 + 1) (m1 + 1 + 2) (t + 2) (t + 2 + 2 * n)) := by
        refine matches_congr h2 ?_
        intro i _
        have hm3 : m1 + 3 = m1 + 1 + 2 := by omega
        have hp2 : t + 1 + 2 * n + 1 = t + 2 + 2 * n := by omega
        rw [hm3, hp2]
      exact ih (m1 + 1) (t + 2) (by omega) (by omega) (by omega) (by omega) (by omega) h2'

def preWant (d : ℕ) : Bool := if d ≤ 2 then decide (d = 2) else false

def preBase (r d : ℕ) : Bool := if d < 4 then leftBlock 2 d else bg110 ((2 * r + 2) % 3) d

def prePatchItem (r j : ℕ) : Option (ℕ × Bool) :=
  if preWant (j + 1) == preBase r (j + 1) then none else some (j + 1, preWant (j + 1))

def prePatchList (r : ℕ) : List (ℕ × Bool) :=
  (List.range (r - 3)).filterMap (prePatchItem r)

lemma patchAt_filterMap_prePatchItem (base : ℕ → Bool) (anchor r j i : ℕ)
    (hi : i = anchor + (j + 1)) (hbase : base i = preBase r (j + 1)) :
    ∀ L : List ℕ, L.Nodup →
      patchAt base anchor (L.filterMap (prePatchItem r)) i =
        if j ∈ L then preWant (j + 1) else base i := by
  intro L hnd
  induction L with
  | nil => simp [patchAt]
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    rw [List.filterMap_cons]
    simp only [List.mem_cons]
    by_cases hxj : j = x
    · subst hxj
      rw [if_pos (Or.inl rfl)]
      by_cases heq : preWant (j + 1) = preBase r (j + 1)
      · have hitem : prePatchItem r j = none := by
          unfold prePatchItem; rw [if_pos (beq_iff_eq.mpr heq)]
        rw [hitem]
        dsimp only
        rw [ih hnd.2, if_neg hnd.1, hbase, heq]
      · have hitem : prePatchItem r j = some (j + 1, preWant (j + 1)) := by
          unfold prePatchItem; rw [if_neg (by simp [heq])]
        rw [hitem]
        dsimp only [patchAt]
        rw [if_pos hi]
    · simp only [hxj, false_or]
      by_cases heq : preWant (x + 1) = preBase r (x + 1)
      · have hitem : prePatchItem r x = none := by
          unfold prePatchItem; rw [if_pos (beq_iff_eq.mpr heq)]
        rw [hitem]
        exact ih hnd.2
      · have hitem : prePatchItem r x = some (x + 1, preWant (x + 1)) := by
          unfold prePatchItem; rw [if_neg (by simp [heq])]
        rw [hitem]
        dsimp only [patchAt]
        have hne : i ≠ anchor + (x + 1) := by omega
        rw [if_neg hne]
        exact ih hnd.2

lemma preBit_as_patch_B_succ {k r : ℕ} (hk : 1 ≤ k) (hr1 : 6 ≤ r) (hr2 : r ≤ 13) :
    let n := 8 * k + r + 3
    let B := k + 1
    let t := 4 * k + 2
    ∀ i : ℕ, i < n →
      preBit n t i = patchAt (baseBit B t (t + 2 * n)) (4 * B - 4) (prePatchList r) i := by
  intro n B t i hi
  have hanc : 4 * B - 4 = 4 * k := by omega
  have hov_range : ∀ q ∈ prePatchList r, 1 ≤ q.1 ∧ q.1 ≤ r - 3 := by
    intro q hq
    simp only [prePatchList, List.mem_filterMap, List.mem_range] at hq
    obtain ⟨j, hj, hres⟩ := hq
    unfold prePatchItem at hres
    by_cases heq : (preWant (j + 1) == preBase r (j + 1)) = true
    · rw [if_pos heq] at hres; simp at hres
    · rw [if_neg heq] at hres
      injection hres with hq_eq
      rw [← hq_eq]
      omega
  by_cases hlt : i ≤ 4 * k
  · have hout : ∀ q ∈ prePatchList r, i ≠ 4 * B - 4 + q.1 := fun q hq => by have := hov_range q hq; omega
    rw [patchAt_outside _ _ _ _ hout]
    by_cases hi4k : i = 4 * k
    · subst hi4k
      have hL : preBit n t (4 * k) = false := by
        unfold preBit leftCone
        rw [if_pos (by omega), if_neg (by omega)]
        have ht4 : (4 * k + 2) % 4 = 2 := by omega
        have hi4 : (4 * k) % 4 = 0 := by omega
        rw [ht4, hi4]; rfl
      have hR : baseBit B t (t + 2 * n) (4 * k) = false := by
        unfold baseBit
        rw [if_pos (by omega), leftBlock_eq_two (by omega)]
        have hi4 : (4 * k) % 4 = 0 := by omega
        rw [hi4]; rfl
      rw [hL, hR]
    · unfold preBit baseBit leftCone
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  · by_cases hgt : 4 * k + r - 3 < i
    · have hout : ∀ q ∈ prePatchList r, i ≠ 4 * B - 4 + q.1 := fun q hq => by have := hov_range q hq; omega
      rw [patchAt_outside _ _ _ _ hout]
      unfold preBit baseBit
      rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    · obtain ⟨j, hj_lt, hi_eq⟩ : ∃ j, j < r - 3 ∧ i = 4 * k + (j + 1) := ⟨i - 4 * k - 1, by omega, by omega⟩
      have hpre : preBit n t i = preWant (j + 1) := by
        subst hi_eq
        unfold preBit preWant
        by_cases hj2 : j + 1 ≤ 2
        · rw [if_pos (by omega), if_pos hj2]
          unfold leftCone
          rw [if_neg (by omega)]
          have ht4 : (4 * k + 2) % 4 = 2 := by omega
          have hm4 : (4 * k + (j + 1)) % 4 = j + 1 := by omega
          rw [ht4, hm4]; rfl
        · rw [if_neg (by omega), if_neg (by omega), if_neg hj2]
      have hbase : baseBit B t (t + 2 * n) i = preBase r (j + 1) := by
        subst hi_eq
        unfold baseBit preBase
        by_cases h4 : j + 1 < 4
        · rw [if_pos (by omega), if_pos h4]
          unfold leftBlock
          have h1 : (4 * k + 2 + 2 * ((4 * k + (j + 1)) / 4)) % 3 = (2 + 2 * ((j + 1) / 4)) % 3 := by omega
          have h2 : (4 * k + (j + 1)) % 4 = (j + 1) % 4 := by omega
          rw [h1, h2]
        · rw [if_neg (by omega), if_neg h4]
          unfold bg110
          have h1 : (4 * k + (j + 1) + (4 * k + 2 + 2 * (8 * k + r + 3))) % 3 =
              (j + 1 + (2 * r + 2) % 3) % 3 := by omega
          rw [h1]
      unfold prePatchList
      rw [patchAt_filterMap_prePatchItem (baseBit B t (t + 2 * n)) (4 * B - 4) r j i (by omega) hbase
        (List.range (r - 3)) List.nodup_range, if_pos (List.mem_range.mpr hj_lt), hpre]

lemma step_wrap_apply_gen {n B t t' c W : ℕ} {tm pn : ℕ} {ovL1 ovR1 ovL2 ovR2 : List (ℕ × Bool)}
    (ht' : t' = t + 1) (hB : 0 < B) (hW0 : 0 < W) (hW : W < 4 * B) (hBn : 4 * B + 4 ≤ n)
    (hrel : (t + 2 * n + c + 2 * t + 2 * B) % 3 = 0)
    (hovL1 : ∀ q ∈ ovL1, q.1 + 1 < W) (hovL2 : ∀ q ∈ ovL2, q.1 < W)
    (hovR1 : ∀ q ∈ ovR1, 1 ≤ q.1 ∧ q.1 ≤ 2) (hovR2 : ∀ q ∈ ovR2, 1 ≤ q.1 ∧ q.1 ≤ 2)
    (htm : t % 3 = tm) (hpn : (t + 2 * n + c + n) % 3 = pn)
    (hcheck : checkWrapWindow W tm pn ovL1 ovR1 ovL2 ovR2 = true)
    (hm : Matches n (rowM n t) (patchWrap (baseBit B t (t + 2 * n + c)) n ovL1 ovR1)) :
    Matches n (rowM n t') (patchWrap (baseBit B t' (t' + 2 * n + c)) n ovL2 ovR2) := by
  subst ht'
  rw [rowM_succ]
  have hchk' : checkWrapWindow W (t % 3) ((t + 2 * n + c + n) % 3) ovL1 ovR1 ovL2 ovR2 = true := by
    rw [htm, hpn]; exact hcheck
  have hs := matches_step (by omega) hm (step_wrap hB hW0 hW hBn hrel hovL1 hovL2 hovR1 hovR2 hchk')
  refine matches_congr hs ?_
  intro i _
  have : t + 2 * n + c + 1 = t + 1 + 2 * n + c := by omega
  rw [this]

lemma absorb_cycle_r7_9_12 {n B T : ℕ} (hB : 0 < B) (hBn : 4 * B + 4 ≤ n)
    (hT : T % 3 = 2) (hrel : ∀ t : ℕ, (t + 2 * n + 1 + 2 * t + 2 * B) % 3 = 0)
    (hmatch : Matches n (rowM n T) (baseBit B T (T + 2 * n + 1))) :
    a n = 3 := by
  have h1 : Matches n (rowM n T) (patchWrap (baseBit B T (T + 2 * n + 1)) n [] []) := hmatch
  have h2 := step_wrap_apply_gen (t' := T + 1) (W := 2) (tm := 2) (pn := 0) (ovL2 := []) (ovR2 := [])
    rfl hB (by decide) (by omega) hBn (hrel T) (by simp) (by simp) (by simp) (by simp)
    hT (by omega) (by decide) h1
  have h3 := step_wrap_apply_gen (t' := T + 2) (W := 2) (tm := 0) (pn := 1) (ovL2 := [(0, false)]) (ovR2 := [])
    (by omega) hB (by decide) (by omega) hBn (hrel (T + 1)) (by simp) (by simp) (by simp) (by simp)
    (by omega) (by omega) (by decide) h2
  have h4 := step_wrap_apply_gen (t' := T + 3) (W := 3) (tm := 1) (pn := 2) (ovL2 := [(0, true), (1, false)]) (ovR2 := [])
    (by omega) hB (by decide) (by omega) hBn (hrel (T + 2)) (by simp) (by simp) (by simp) (by simp)
    (by omega) (by omega) (by decide) h3
  have h5 := step_wrap_apply_gen (t' := T + 4) (W := 3) (tm := 2) (pn := 0) (ovL2 := []) (ovR2 := [])
    (by omega) hB (by decide) (by omega) hBn (hrel (T + 3)) (by simp) (by simp) (by simp) (by simp)
    (by omega) (by omega) (by decide) h4
  have h5' : Matches n (rowM n (T + 1 + 3)) (patchWrap (baseBit B (T + 1) (T + 1 + 2 * n + 1)) n [] []) := by
    have ht4 : T + 1 + 3 = T + 4 := by omega
    rw [ht4]
    refine matches_congr h5 ?_
    intro i hi
    unfold patchWrap baseBit leftBlock bg110
    simp only [List.find?_nil]
    by_cases hlt : i < 4 * B
    · rw [if_pos hlt, if_pos hlt]
      have : (T + 4 + 2 * (i / 4)) % 3 = (T + 1 + 2 * (i / 4)) % 3 := by omega
      rw [this]
    · rw [if_neg hlt, if_neg hlt]
      have : (i + (T + 4 + 2 * n + 1)) % 3 = (i + (T + 1 + 2 * n + 1)) % 3 := by omega
      rw [this]
  apply a_eq_of_cycleM (T := T + 1) (by omega) (by decide)
  · exact matches_eq (by omega) h5' h2
  · intro q hq1 hq2
    interval_cases q
    · exact matches_ne_of_bit h3 h2 0 (by omega) (by
        have v1 : patchWrap (baseBit B (T + 2) (T + 2 + 2 * n + 1)) n [(0, false)] [] 0 = false := rfl
        have v2 : patchWrap (baseBit B (T + 1) (T + 1 + 2 * n + 1)) n [] [] 0 = true := by
          unfold patchWrap baseBit
          simp only [List.find?_nil, if_pos (by omega : 0 < 4 * B)]
          exact leftBlock_eq_zero (by omega)
        rw [v1, v2]; decide)
    · exact matches_ne_of_bit h4 h2 1 (by omega) (by
        have v1 : patchWrap (baseBit B (T + 3) (T + 3 + 2 * n + 1)) n [(0, true), (1, false)] [] 1 = false := rfl
        have v2 : patchWrap (baseBit B (T + 1) (T + 1 + 2 * n + 1)) n [] [] 1 = true := by
          unfold patchWrap baseBit
          simp only [List.find?_nil, if_pos (by omega : 1 < 4 * B)]
          exact leftBlock_eq_zero (by omega)
        rw [v1, v2]; decide)

lemma step_seam_apply_gen {n B t t' lo hi tb pb : ℕ} {ov1 ov2 : List (ℕ × Bool)}
    (ht' : t' = t + 1) (hB : 0 < B) (hlo_B : lo = 0 → 2 ≤ B)
    (h1 : ∀ q ∈ ov1, lo + 1 ≤ q.1 ∧ q.1 + 1 ≤ hi)
    (h2 : ∀ q ∈ ov2, lo ≤ q.1 ∧ q.1 ≤ hi)
    (hhi : hi < 11) (hn : 4 * B - 4 + hi + 2 < n) (hsl : lo ≤ 3) (hsr : 4 ≤ hi)
    (htb : (t + 2 * (B - 1)) % 3 = tb) (hpb : (t + 2 * n + (4 * B - 4)) % 3 = pb)
    (hchk : checkSeamWindow lo hi tb pb ov1 ov2 = true)
    (hm : Matches n (rowM n t) (patchAt (baseBit B t (t + 2 * n)) (4 * B - 4) ov1)) :
    Matches n (rowM n t') (patchAt (baseBit B t' (t' + 2 * n)) (4 * B - 4) ov2) := by
  subst ht'
  rw [rowM_succ]
  have hchk' : checkSeamWindow lo hi ((t + 2 * (B - 1)) % 3) ((t + 2 * n + (4 * B - 4)) % 3) ov1 ov2 = true := by
    rw [htb, hpb]; exact hchk
  have hs := matches_step (by omega) hm (step_seam hB hlo_B h1 h2 hhi hn hsl hsr rfl hchk')
  refine matches_congr hs ?_
  intro i _
  have : t + 2 * n + 1 = t + 1 + 2 * n := by omega
  rw [this]

lemma a_eq_3_of_ge_17 {n : ℕ} (hn : 17 ≤ n) : a n = 3 := by
  let k := (n - 9) / 8
  let r := (n - 9) % 8 + 6
  have hk : 1 ≤ k := by omega
  have hr1 : 6 ≤ r := by omega
  have hr2 : r ≤ 13 := by omega
  have hnr : n = 8 * k + r + 3 := by omega
  have hpre := matches_preBit (n := n) (t := 4 * k + 2) (by omega)
  have hbase_period3 : ∀ (B t c : ℕ) (ov : List (ℕ × Bool)) (i : ℕ),
      patchAt (baseBit B (t + 3) (t + 3 + 2 * n + c)) (4 * B - 4) ov i =
      patchAt (baseBit B t (t + 2 * n + c)) (4 * B - 4) ov i := by
    intro B t c ov i
    induction ov with
    | nil =>
      unfold patchAt baseBit leftBlock bg110
      by_cases h : i < 4 * B
      · rw [if_pos h, if_pos h]
        have : (t + 3 + 2 * (i / 4)) % 3 = (t + 2 * (i / 4)) % 3 := by omega
        rw [this]
      · rw [if_neg h, if_neg h]
        have : (i + (t + 3 + 2 * n + c)) % 3 = (i + (t + 2 * n + c)) % 3 := by omega
        rw [this]
    | cons hd tl ih =>
      unfold patchAt
      split
      · rfl
      · exact ih
  have hwrap_period3 : ∀ (B t c : ℕ) (ovL ovR : List (ℕ × Bool)) (i : ℕ),
      patchWrap (baseBit B (t + 3) (t + 3 + 2 * n + c)) n ovL ovR i =
      patchWrap (baseBit B t (t + 2 * n + c)) n ovL ovR i := by
    intro B t c ovL ovR i
    unfold patchWrap
    cases ovL.find? (fun p => p.1 == i) with
    | some _ => rfl
    | none =>
      cases ovR.find? (fun p => n - p.1 == i) with
      | some _ => rfl
      | none =>
        unfold baseBit leftBlock bg110
        by_cases h : i < 4 * B
        · rw [if_pos h, if_pos h]
          have : (t + 3 + 2 * (i / 4)) % 3 = (t + 2 * (i / 4)) % 3 := by omega
          rw [this]
        · rw [if_neg h, if_neg h]
          have : (i + (t + 3 + 2 * n + c)) % 3 = (i + (t + 2 * n + c)) % 3 := by omega
          rw [this]
  have hcyc_seam_ne : ∀ (B T : ℕ) (ov0 ov1 ov2 : List (ℕ × Bool)),
      2 ≤ B → 4 * B + 4 ≤ n →
      (∀ q ∈ ov0, 1 ≤ q.1) → (∀ q ∈ ov1, 1 ≤ q.1) → (∀ q ∈ ov2, 1 ≤ q.1) →
      Matches n (rowM n T) (patchAt (baseBit B T (T + 2 * n)) (4 * B - 4) ov0) →
      Matches n (rowM n (T + 1)) (patchAt (baseBit B (T + 1) (T + 1 + 2 * n)) (4 * B - 4) ov1) →
      Matches n (rowM n (T + 2)) (patchAt (baseBit B (T + 2) (T + 2 + 2 * n)) (4 * B - 4) ov2) →
      Matches n (rowM n (T + 3)) (patchAt (baseBit B (T + 3) (T + 3 + 2 * n)) (4 * B - 4) ov0) →
      a n = 3 := by
    intro B T ov0 ov1 ov2 hB2 hBn ho0 ho1 ho2 hm0 hm1 hm2 hm3
    apply a_eq_of_cycleM (T := T) (by omega) (by decide)
    · exact matches_eq (by omega) hm3 (matches_congr hm0 (fun i _ => (hbase_period3 B T 0 ov0 i).symm))
    · intro q hq1 hq2
      have h0 : ∀ (t : ℕ) (ov : List (ℕ × Bool)), (∀ q ∈ ov, 1 ≤ q.1) →
          patchAt (baseBit B t (t + 2 * n)) (4 * B - 4) ov 0 = leftBlock t 0 := by
        intro t ov hov
        rw [patchAt_outside _ _ _ _ (fun p hp => by have := hov p hp; omega)]
        unfold baseBit; rw [if_pos (by omega)]
      have h1 : ∀ (t : ℕ) (ov : List (ℕ × Bool)), (∀ q ∈ ov, 1 ≤ q.1) →
          patchAt (baseBit B t (t + 2 * n)) (4 * B - 4) ov 1 = leftBlock t 1 := by
        intro t ov hov
        rw [patchAt_outside _ _ _ _ (fun p hp => by have := hov p hp; omega)]
        unfold baseBit; rw [if_pos (by omega)]
      have hdist : ∀ (t : ℕ), (leftBlock (t + 1) 0 ≠ leftBlock t 0 ∨ leftBlock (t + 1) 1 ≠ leftBlock t 1) ∧
          (leftBlock (t + 2) 0 ≠ leftBlock t 0 ∨ leftBlock (t + 2) 1 ≠ leftBlock t 1) := by
        intro t
        have hc : ∀ (a : Fin 3),
            (leftBlock ((a.val + 1) % 3) 0 ≠ leftBlock a.val 0 ∨ leftBlock ((a.val + 1) % 3) 1 ≠ leftBlock a.val 1) ∧
            (leftBlock ((a.val + 2) % 3) 0 ≠ leftBlock a.val 0 ∨ leftBlock ((a.val + 2) % 3) 1 ≠ leftBlock a.val 1) := by
          decide
        rw [leftBlock_mod (t + 1) 0, leftBlock_mod t 0, leftBlock_mod (t + 1) 1, leftBlock_mod t 1,
          leftBlock_mod (t + 2) 0, leftBlock_mod (t + 2) 1]
        have ha1 : (t + 1) % 3 = (t % 3 + 1) % 3 := by omega
        have ha2 : (t + 2) % 3 = (t % 3 + 2) % 3 := by omega
        rw [ha1, ha2]
        exact hc ⟨t % 3, Nat.mod_lt _ (by decide)⟩
      interval_cases q
      · rcases (hdist T).1 with hne | hne
        · exact matches_ne_of_bit hm1 hm0 0 (by omega) (by rw [h0 _ _ ho1, h0 _ _ ho0]; exact hne)
        · exact matches_ne_of_bit hm1 hm0 1 (by omega) (by rw [h1 _ _ ho1, h1 _ _ ho0]; exact hne)
      · rcases (hdist T).2 with hne | hne
        · exact matches_ne_of_bit hm2 hm0 0 (by omega) (by rw [h0 _ _ ho2, h0 _ _ ho0]; exact hne)
        · exact matches_ne_of_bit hm2 hm0 1 (by omega) (by rw [h1 _ _ ho2, h1 _ _ ho0]; exact hne)
  have hpre_init : ∀ (r0 : ℕ) (ov : List (ℕ × Bool)), r = r0 → prePatchList r0 = ov →
      Matches n (rowM n (4 * k + 2))
        (patchAt (baseBit (k + 1) (4 * k + 2) (4 * k + 2 + 2 * n)) (4 * (k + 1) - 4) ov) := by
    intro r0 ov hreq hov
    subst hreq
    refine matches_congr hpre ?_
    intro i hi
    have h := preBit_as_patch_B_succ (k := k) (r := r) hk hr1 hr2 i (by omega)
    rw [← hnr, hov] at h
    exact h
  have : r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 := by omega
  rcases this with hr | hr | hr | hr | hr | hr | hr | hr
  · have h0 := hpre_init 6 [(1, false), (2, true), (3, false)] hr (by decide)
    have h1 := step_seam_apply_gen (t' := 4 * k + 3) (lo := 0) (hi := 4) (tb := 2) (pb := 2) (ov2 := [])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h0
    have h2 := step_seam_apply_gen (t' := 4 * k + 4) (lo := 0) (hi := 4) (tb := 0) (pb := 0) (ov2 := [])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h1
    have h3 := step_seam_apply_gen (t' := 4 * k + 5) (lo := 0) (hi := 4) (tb := 1) (pb := 1) (ov2 := [(3, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h2
    have h4 := step_seam_apply_gen (t' := 4 * k + 6) (lo := 0) (hi := 4) (tb := 2) (pb := 2) (ov2 := [])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h3
    exact hcyc_seam_ne (k + 1) (4 * k + 3) [] [] [(3, false)] (by omega) (by omega)
      (by simp) (by simp) (by simp) h1 h2 h3 h4
  · have h0 : Matches n (rowM n (4 * k + 2))
        (patchAt (baseBit k (4 * k + 2) (4 * k + 2 + 2 * n)) (4 * k - 4) [(4, false), (7, false)]) := by
      refine matches_congr hpre ?_
      intro i hi
      by_cases hlt : i < 4 * k
      · have hL : preBit n (4 * k + 2) i = leftBlock (4 * k + 2) i := by
          unfold preBit leftCone; rw [if_pos (by omega), if_pos (by omega)]
        have hR : patchAt (baseBit k (4 * k + 2) (4 * k + 2 + 2 * n)) (4 * k - 4) [(4, false), (7, false)] i =
            leftBlock (4 * k + 2) i := by
          rw [patchAt_outside _ _ _ _ (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> omega)]
          unfold baseBit; rw [if_pos hlt]
        rw [hL, hR]
      · by_cases hi0 : i = 4 * k
        · subst hi0
          have hL : preBit n (4 * k + 2) (4 * k) = false := by
            unfold preBit leftCone; rw [if_pos (by omega), if_neg (by omega)]
            have a1 : (4 * k + 2) % 4 = 2 := by omega
            have a2 : (4 * k) % 4 = 0 := by omega
            rw [a1, a2]; rfl
          have hR : patchAt (baseBit k (4 * k + 2) (4 * k + 2 + 2 * n)) (4 * k - 4) [(4, false), (7, false)] (4 * k) = false := by
            unfold patchAt; rw [if_pos (by omega)]
          rw [hL, hR]
        · by_cases hi1 : i = 4 * k + 1
          · subst hi1
            have hL : preBit n (4 * k + 2) (4 * k + 1) = false := by
              unfold preBit leftCone; rw [if_pos (by omega), if_neg (by omega)]
              have a1 : (4 * k + 2) % 4 = 2 := by omega
              have a2 : (4 * k + 1) % 4 = 1 := by omega
              rw [a1, a2]; rfl
            have hR : patchAt (baseBit k (4 * k + 2) (4 * k + 2 + 2 * n)) (4 * k - 4) [(4, false), (7, false)] (4 * k + 1) = false := by
              rw [patchAt_outside _ _ _ _ (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> omega)]
              unfold baseBit; rw [if_neg (by omega)]
              exact bg110_eq_false (by omega)
            rw [hL, hR]
          · by_cases hi2 : i = 4 * k + 2
            · subst hi2
              have hL : preBit n (4 * k + 2) (4 * k + 2) = true := by
                unfold preBit leftCone; rw [if_pos (by omega), if_neg (by omega)]
                have a1 : (4 * k + 2) % 4 = 2 := by omega
                rw [a1]; rfl
              have hR : patchAt (baseBit k (4 * k + 2) (4 * k + 2 + 2 * n)) (4 * k - 4) [(4, false), (7, false)] (4 * k + 2) = true := by
                rw [patchAt_outside _ _ _ _ (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> omega)]
                unfold baseBit; rw [if_neg (by omega)]
                exact bg110_eq_true (by omega)
              rw [hL, hR]
            · by_cases hi3 : i = 4 * k + 3
              · subst hi3
                have hL : preBit n (4 * k + 2) (4 * k + 3) = false := by
                  unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
                have hR : patchAt (baseBit k (4 * k + 2) (4 * k + 2 + 2 * n)) (4 * k - 4) [(4, false), (7, false)] (4 * k + 3) = false := by
                  simp only [patchAt]; rw [if_neg (by omega), if_pos (by omega)]
                rw [hL, hR]
              · by_cases hi4 : i = 4 * k + 4
                · subst hi4
                  have hL : preBit n (4 * k + 2) (4 * k + 4) = false := by
                    unfold preBit; rw [if_neg (by omega), if_neg (by omega)]
                  have hR : patchAt (baseBit k (4 * k + 2) (4 * k + 2 + 2 * n)) (4 * k - 4) [(4, false), (7, false)] (4 * k + 4) = false := by
                    rw [patchAt_outside _ _ _ _ (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> omega)]
                    unfold baseBit; rw [if_neg (by omega)]
                    exact bg110_eq_false (by omega)
                  rw [hL, hR]
                · have hL : preBit n (4 * k + 2) i = bg110 (4 * k + 2 + 2 * n) i := by
                    unfold preBit; rw [if_neg (by omega), if_pos (by omega)]
                  have hR : patchAt (baseBit k (4 * k + 2) (4 * k + 2 + 2 * n)) (4 * k - 4) [(4, false), (7, false)] i =
                      bg110 (4 * k + 2 + 2 * n) i := by
                    rw [patchAt_outside _ _ _ _ (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> omega)]
                    unfold baseBit; rw [if_neg (by omega)]
                  rw [hL, hR]
    have h1 := step_seam_apply_gen (t' := 4 * k + 3) (lo := 3) (hi := 9) (tb := 0) (pb := 0) (ov2 := [(4, true), (7, true)])
      (by omega) (by omega) (by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h0
    have h2 := step_seam_apply_gen (t' := 4 * k + 4) (lo := 3) (hi := 9) (tb := 1) (pb := 1) (ov2 := [(5, false), (7, false), (8, false)])
      (by omega) (by omega) (by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h1
    have h3 := step_seam_apply_gen (t' := 4 * k + 5) (lo := 3) (hi := 9) (tb := 2) (pb := 2) (ov2 := [(4, false), (5, true), (6, false), (7, false)])
      (by omega) (by omega) (by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h2
    have h4 := step_seam_apply_gen (t' := 4 * k + 6) (lo := 3) (hi := 9) (tb := 0) (pb := 0) (ov2 := [(4, true)])
      (by omega) (by omega) (by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h3
    have hw : Matches n (rowM n (4 * k + 6)) (wallBit k (4 * k + 1) (4 * k + 6) (4 * k + 6 + 2 * n)) := by
      refine matches_congr h4 ?_
      intro i hi
      simp only [patchAt, baseBit, wallBit]
      by_cases hi4 : i = 4 * k
      · subst hi4
        rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        exact (bg110_eq_true (by omega)).symm
      · rw [if_neg (by omega)]
        by_cases hlt : i < 4 * k
        · rw [if_pos hlt, if_pos hlt]
        · rw [if_neg hlt, if_neg hlt, if_neg (by omega)]
    obtain ⟨T, hT, hTm⟩ := wallBit_reach_end (n := n) (B := k) (by omega) (by omega) (fun t => by omega)
      (4 * k + 9) (4 * k + 1) (4 * k + 6) (by omega) (by omega) (by omega) (by omega) hw
    exact absorb_cycle_r7_9_12 (by omega) (by omega) hT (fun t => by omega) hTm
  · have h0 := hpre_init 8 [(1, false), (2, true), (3, false), (4, false)] hr (by decide)
    have h1 := step_seam_apply_gen (t' := 4 * k + 3) (lo := 0) (hi := 6) (tb := 2) (pb := 0) (ov2 := [])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h0
    have h2 := step_seam_apply_gen (t' := 4 * k + 4) (lo := 0) (hi := 6) (tb := 0) (pb := 1) (ov2 := [])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h1
    have h3 := step_seam_apply_gen (t' := 4 * k + 5) (lo := 0) (hi := 6) (tb := 1) (pb := 2) (ov2 := [])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h2
    have h4 := step_seam_apply_gen (t' := 4 * k + 6) (lo := 0) (hi := 6) (tb := 2) (pb := 0) (ov2 := [])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h3
    exact hcyc_seam_ne (k + 1) (4 * k + 3) [] [] [] (by omega) (by omega)
      (by simp) (by simp) (by simp) h1 h2 h3 h4
  · have h0 := hpre_init 9 [(1, false), (2, true), (3, false), (4, false), (5, false)] hr (by decide)
    have h1 := step_seam_apply_gen (t' := 4 * k + 3) (lo := 0) (hi := 6) (tb := 2) (pb := 2) (ov2 := [(4, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h0
    have hw0 : Matches n (rowM n (4 * k + 3)) (wallBit (k + 1) (4 * (k + 1) + 1) (4 * k + 3) (4 * k + 3 + 2 * n)) := by
      refine matches_congr h1 ?_
      intro i hi
      simp only [patchAt, baseBit, wallBit]
      by_cases hi4 : i = 4 * (k + 1)
      · subst hi4
        rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        exact (bg110_eq_false (by omega)).symm
      · rw [if_neg (by omega)]
        by_cases hlt : i < 4 * (k + 1)
        · rw [if_pos hlt, if_pos hlt]
        · rw [if_neg hlt, if_neg hlt, if_neg (by omega)]
    have hw1 := matches_step (by omega) hw0
      (wallBit_step (by omega) (by omega) (by omega) (by omega) (fun _ => by omega) (by omega) rfl (Or.inr (by omega)))
    rw [← rowM_succ, if_neg (by omega)] at hw1
    have hw1' : Matches n (rowM n (4 * k + 4)) (wallBit (k + 1) (4 * (k + 1) + 1) (4 * k + 4) (4 * k + 4 + 2 * n)) := by
      refine matches_congr hw1 ?_; intro i _
      have : 4 * k + 3 + 2 * n + 1 = 4 * k + 4 + 2 * n := by omega
      rw [this]
    obtain ⟨T, hT, hTm⟩ := wallBit_reach_end (n := n) (B := k + 1) (by omega) (by omega) (fun t => by omega)
      (4 * k + 7) (4 * (k + 1) + 1) (4 * k + 4) (by omega) (by omega) (by omega) (by omega) hw1'
    exact absorb_cycle_r7_9_12 (by omega) (by omega) hT (fun t => by omega) hTm
  · have h0 := hpre_init 10 [(1, false), (2, true), (3, false), (5, false), (6, false)] hr (by decide)
    have h1 := step_seam_apply_gen (t' := 4 * k + 3) (lo := 0) (hi := 8) (tb := 2) (pb := 1) (ov2 := [(4, false), (5, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h0
    have h2 := step_seam_apply_gen (t' := 4 * k + 4) (lo := 0) (hi := 8) (tb := 0) (pb := 2) (ov2 := [])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h1
    have h3 := step_seam_apply_gen (t' := 4 * k + 5) (lo := 0) (hi := 8) (tb := 1) (pb := 0) (ov2 := [(4, true)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h2
    have h4 := step_seam_apply_gen (t' := 4 * k + 6) (lo := 0) (hi := 8) (tb := 2) (pb := 1) (ov2 := [(4, false), (5, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h3
    exact hcyc_seam_ne (k + 1) (4 * k + 3) [(4, false), (5, false)] [] [(4, true)] (by omega) (by omega)
      (by simp) (by simp) (by simp) h1 h2 h3 h4
  · have h0 := hpre_init 11 [(1, false), (2, true), (3, false), (4, false), (6, false), (7, false)] hr (by decide)
    have h1 := step_seam_apply_gen (t' := 4 * k + 3) (lo := 0) (hi := 8) (tb := 2) (pb := 0) (ov2 := [(5, false), (6, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h0
    have h2 := step_seam_apply_gen (t' := 4 * k + 4) (lo := 0) (hi := 8) (tb := 0) (pb := 1) (ov2 := [(5, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h1
    have h3 := step_seam_apply_gen (t' := 4 * k + 5) (lo := 0) (hi := 8) (tb := 1) (pb := 2) (ov2 := [(5, true)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h2
    have h4 := step_seam_apply_gen (t' := 4 * k + 6) (lo := 0) (hi := 8) (tb := 2) (pb := 0) (ov2 := [(5, false), (6, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h3
    exact hcyc_seam_ne (k + 1) (4 * k + 3) [(5, false), (6, false)] [(5, false)] [(5, true)] (by omega) (by omega)
      (by simp) (by simp) (by simp) h1 h2 h3 h4
  · have h0 := hpre_init 12 [(1, false), (2, true), (3, false), (4, false), (5, false), (7, false), (8, false)] hr (by decide)
    have h1 := step_seam_apply_gen (t' := 4 * k + 3) (lo := 0) (hi := 9) (tb := 2) (pb := 2) (ov2 := [(4, false), (6, false), (7, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h0
    have h2 := step_seam_apply_gen (t' := 4 * k + 4) (lo := 0) (hi := 9) (tb := 0) (pb := 0) (ov2 := [(4, true), (5, false), (6, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h1
    have h3 := step_seam_apply_gen (t' := 4 * k + 5) (lo := 0) (hi := 9) (tb := 1) (pb := 1) (ov2 := [])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h2
    have hw : Matches n (rowM n (4 * k + 5)) (wallBit (k + 1) (4 * (k + 1)) (4 * k + 5) (4 * k + 5 + 2 * n)) := by
      refine matches_congr h3 ?_
      intro i hi
      unfold patchAt baseBit wallBit
      by_cases hlt : i < 4 * (k + 1)
      · rw [if_pos hlt, if_pos hlt]
      · rw [if_neg hlt, if_neg hlt, if_neg hlt]
    obtain ⟨T, hT, hTm⟩ := wallBit_reach_end (n := n) (B := k + 1) (by omega) (by omega) (fun t => by omega)
      (4 * k + 11) (4 * (k + 1)) (4 * k + 5) (by omega) (by omega) (by omega) (by omega) hw
    exact absorb_cycle_r7_9_12 (by omega) (by omega) hT (fun t => by omega) hTm
  · have h0 := hpre_init 13 [(1, false), (2, true), (3, false), (5, false), (6, false), (8, false), (9, false)] hr (by decide)
    have h1 := step_seam_apply_gen (t' := 4 * k + 3) (lo := 0) (hi := 10) (tb := 2) (pb := 1) (ov2 := [(4, false), (5, false), (7, false), (8, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h0
    have h2 := step_seam_apply_gen (t' := 4 * k + 4) (lo := 0) (hi := 10) (tb := 0) (pb := 2) (ov2 := [(6, false), (7, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h1
    have h3 := step_seam_apply_gen (t' := 4 * k + 5) (lo := 0) (hi := 10) (tb := 1) (pb := 0) (ov2 := [(4, true), (6, false)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h2
    have h4 := step_seam_apply_gen (t' := 4 * k + 6) (lo := 0) (hi := 10) (tb := 2) (pb := 1) (ov2 := [(4, false), (5, false), (6, true)])
      (by omega) (by omega) (fun _ => by omega) (by simp) (by simp) (by decide) (by omega) (by decide) (by decide)
      (by omega) (by omega) (by decide) h3
    have hw : Matches n (rowM n (4 * k + 6))
        (wall2Bit (k + 1) (4 * (k + 1) + 1) (4 * (k + 1) + 3) (4 * k + 6) (4 * k + 6 + 2 * n)) := by
      refine matches_congr h4 ?_
      intro i hi
      simp only [patchAt, baseBit, wall2Bit]
      by_cases hi4 : i = 4 * (k + 1)
      · subst hi4; rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        exact (bg110_eq_false (by omega)).symm
      · by_cases hi5 : i = 4 * (k + 1) + 1
        · subst hi5; rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          exact (bg110_eq_false (by omega)).symm
        · by_cases hi6 : i = 4 * (k + 1) + 2
          · subst hi6; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
            exact (bg110_eq_true (by omega)).symm
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            by_cases hlt : i < 4 * (k + 1)
            · rw [if_pos hlt, if_pos hlt]
            · rw [if_neg hlt, if_neg hlt, if_neg (by omega), if_neg (by omega)]
    obtain ⟨T, hT, hm0⟩ := wall2Bit_reach_end (n := n) (B := k + 1) (by omega) (by omega) (fun t => by omega)
      (4 * k + 9) (4 * (k + 1) + 1) (4 * k + 6) (by omega) (by omega) (by omega) (by omega) (by omega) hw
    have s1 := step_wrap_apply_gen (t' := T + 1) (W := 7) (tm := 2) (pn := 1) (ovL2 := []) (ovR2 := [(2, false)])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) hT (by omega) (by decide) hm0
    have s2 := step_wrap_apply_gen (t' := T + 2) (W := 7) (tm := 0) (pn := 2) (ovL2 := [(0, false)]) (ovR2 := [(1, true)])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s1
    have s3 := step_wrap_apply_gen (t' := T + 3) (W := 7) (tm := 1) (pn := 0) (ovL2 := [(0, true), (1, false)]) (ovR2 := [(1, false)])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s2
    have s4 := step_wrap_apply_gen (t' := T + 4) (W := 7) (tm := 2) (pn := 1) (ovL2 := []) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s3
    have s5 := step_wrap_apply_gen (t' := T + 5) (W := 7) (tm := 0) (pn := 2) (ovL2 := [(0, false)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s4
    have s6 := step_wrap_apply_gen (t' := T + 6) (W := 7) (tm := 1) (pn := 0) (ovL2 := [(1, false)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s5
    have s7 := step_wrap_apply_gen (t' := T + 7) (W := 7) (tm := 2) (pn := 1) (ovL2 := [(1, false)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s6
    have s8 := step_wrap_apply_gen (t' := T + 8) (W := 7) (tm := 0) (pn := 2) (ovL2 := [(0, false), (1, true), (2, true)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s7
    have s9 := step_wrap_apply_gen (t' := T + 9) (W := 7) (tm := 1) (pn := 0) (ovL2 := [(0, true)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s8
    have s10 := step_wrap_apply_gen (t' := T + 10) (W := 7) (tm := 2) (pn := 1) (ovL2 := [(0, false), (1, false)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s9
    have s11 := step_wrap_apply_gen (t' := T + 11) (W := 7) (tm := 0) (pn := 2) (ovL2 := [(1, true), (2, true)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s10
    have s12 := step_wrap_apply_gen (t' := T + 12) (W := 7) (tm := 1) (pn := 0) (ovL2 := [(0, true), (1, false)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s11
    have s13 := step_wrap_apply_gen (t' := T + 13) (W := 7) (tm := 2) (pn := 1) (ovL2 := [(0, false)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s12
    have s14 := step_wrap_apply_gen (t' := T + 14) (W := 7) (tm := 0) (pn := 2) (ovL2 := [(1, true)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s13
    have s15 := step_wrap_apply_gen (t' := T + 15) (W := 7) (tm := 1) (pn := 0) (ovL2 := [(0, true), (1, false), (2, true)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s14
    have s16 := step_wrap_apply_gen (t' := T + 16) (W := 7) (tm := 2) (pn := 1) (ovL2 := [(0, false), (3, false)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s15
    have s17 := step_wrap_apply_gen (t' := T + 17) (W := 7) (tm := 0) (pn := 2) (ovL2 := [(1, true), (3, true)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s16
    have s18 := step_wrap_apply_gen (t' := T + 18) (W := 7) (tm := 1) (pn := 0) (ovL2 := [(0, true), (1, false), (2, true), (4, false)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s17
    have s19 := step_wrap_apply_gen (t' := T + 19) (W := 7) (tm := 2) (pn := 1) (ovL2 := [(0, false), (3, false), (4, true), (5, false)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s18
    have s20 := step_wrap_apply_gen (t' := T + 20) (W := 7) (tm := 0) (pn := 2) (ovL2 := [(1, true), (3, true)]) (ovR2 := [])
      (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
      (by simp) (by simp) (by simp) (by simp) (by omega) (by omega) (by decide) s19
    apply a_eq_of_cycleM (T := T + 17) (by omega) (by decide)
    · exact matches_eq (by omega) (show Matches n (rowM n (T + 17 + 3)) _ from s20)
        (matches_congr s17 (fun i _ => (hwrap_period3 (k + 1) (T + 17) 2 [(1, true), (3, true)] [] i).symm))
    · intro q hq1 hq2
      interval_cases q
      · exact matches_ne_of_bit s18 s17 1 (by omega) (by
          have v1 : patchWrap (baseBit (k + 1) (T + 18) (T + 18 + 2 * n + 2)) n [(0, true), (1, false), (2, true), (4, false)] [] 1 = false := rfl
          have v2 : patchWrap (baseBit (k + 1) (T + 17) (T + 17 + 2 * n + 2)) n [(1, true), (3, true)] [] 1 = true := rfl
          rw [v1, v2]; decide)
      · exact matches_ne_of_bit s19 s17 0 (by omega) (by
          have v1 : patchWrap (baseBit (k + 1) (T + 19) (T + 19 + 2 * n + 2)) n [(0, false), (3, false), (4, true), (5, false)] [] 0 = false := rfl
          have v2 : patchWrap (baseBit (k + 1) (T + 17) (T + 17 + 2 * n + 2)) n [(1, true), (3, true)] [] 0 = true := by
            unfold patchWrap baseBit
            simp only [List.find?_cons, List.find?_nil, if_pos (by omega : 0 < 4 * (k + 1))]
            have h1 : (1 == 0) = false := rfl
            have h3 : (3 == 0) = false := rfl
            rw [h1, h3]
            simp only
            rw [leftBlock_eq_one (by omega)]
            rfl
          rw [v1, v2]; decide)

lemma recurrence : ∀ n : ℕ, 17 < n → a n = a (n - 1) := by
  intro n hn
  rw [a_eq_3_of_ge_17 (by omega), a_eq_3_of_ge_17 (by omega)]

lemma gf_identity :
    let X : PowerSeries ℤ := PowerSeries.X
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) =
      X * (1 + 2 * X ^ 2 + 5 * X ^ 3 - 5 * X ^ 4 + 11 * X ^ 6 + 2 * X ^ 7 -
        13 * X ^ 8 + 17 * X ^ 9 - 17 * X ^ 10 + 29 * X ^ 15 - 29 * X ^ 16) := by
  dsimp only
  let F : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  have hlhs : F * (1 - (PowerSeries.X : PowerSeries ℤ)) = F - (PowerSeries.X : PowerSeries ℤ) ^ 1 * F := by ring
  have hrhs : (PowerSeries.X : PowerSeries ℤ) * (1 + 2 * (PowerSeries.X : PowerSeries ℤ) ^ 2 +
      5 * (PowerSeries.X : PowerSeries ℤ) ^ 3 - 5 * (PowerSeries.X : PowerSeries ℤ) ^ 4 +
      11 * (PowerSeries.X : PowerSeries ℤ) ^ 6 + 2 * (PowerSeries.X : PowerSeries ℤ) ^ 7 -
      13 * (PowerSeries.X : PowerSeries ℤ) ^ 8 + 17 * (PowerSeries.X : PowerSeries ℤ) ^ 9 -
      17 * (PowerSeries.X : PowerSeries ℤ) ^ 10 + 29 * (PowerSeries.X : PowerSeries ℤ) ^ 15 -
      29 * (PowerSeries.X : PowerSeries ℤ) ^ 16) =
      (PowerSeries.X : PowerSeries ℤ) ^ 1 + (2 : ℕ) • (PowerSeries.X : PowerSeries ℤ) ^ 3 +
        (5 : ℕ) • (PowerSeries.X : PowerSeries ℤ) ^ 4 - (5 : ℕ) • (PowerSeries.X : PowerSeries ℤ) ^ 5 +
        (11 : ℕ) • (PowerSeries.X : PowerSeries ℤ) ^ 7 + (2 : ℕ) • (PowerSeries.X : PowerSeries ℤ) ^ 8 -
        (13 : ℕ) • (PowerSeries.X : PowerSeries ℤ) ^ 9 + (17 : ℕ) • (PowerSeries.X : PowerSeries ℤ) ^ 10 -
        (17 : ℕ) • (PowerSeries.X : PowerSeries ℤ) ^ 11 + (29 : ℕ) • (PowerSeries.X : PowerSeries ℤ) ^ 16 -
        (29 : ℕ) • (PowerSeries.X : PowerSeries ℤ) ^ 17 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  change F * (1 - PowerSeries.X) = _
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, map_nsmul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow,
    PowerSeries.coeff_mk, F]
  by_cases hn : n ≤ 17
  · interval_cases n <;>
      simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12, a_13,
        a_14, a_15, a_16, a_eq_3_of_ge_17]
  · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [recurrence n (by omega)]
    simp

end A334503Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a334503.main :=
  ⟨A334503Proof.recurrence, A334503Proof.gf_identity⟩
