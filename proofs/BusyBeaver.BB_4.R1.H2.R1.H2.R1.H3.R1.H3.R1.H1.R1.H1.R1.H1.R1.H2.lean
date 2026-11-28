import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H1_R1
import Mathlib

namespace BlankTapeEncoding

open Turing Turing.BusyBeaver

def instructionCode (entry : Fin 4 × Stmt (Fin 2)) : ℕ :=
  4 * entry.1.val + 2 * entry.2.symbol.val + match entry.2.dir with
    | .left => 0
    | .right => 1

def instruction (a : ℕ) : Fin 4 × Stmt (Fin 2) :=
  (⟨a / 4 % 4, Nat.mod_lt _ (by decide)⟩,
    .write ⟨a / 2 % 2, Nat.mod_lt _ (by decide)⟩
      (if a % 2 = 0 then .left else .right))

theorem instructionCode_lt (p : Fin 4 × Stmt (Fin 2)) : instructionCode p < 16 := by
  obtain ⟨q, ⟨s,d⟩⟩ := p
  have hq := q.isLt
  have hs := s.isLt
  cases d <;> simp only [instructionCode] <;> omega

theorem instruction_roundtrip (p : Fin 4 × Stmt (Fin 2)) :
    instruction (instructionCode p) = p := by
  obtain ⟨q, ⟨s,d⟩⟩ := p
  have hq := q.isLt
  have hs := s.isLt
  cases d
  · have h1 : (4*q.val + 2*s.val)/4%4 = q.val := by omega
    have h2 : (4*q.val + 2*s.val)/2%2 = s.val := by omega
    have h3 : (4*q.val + 2*s.val)%2 = 0 := by omega
    simp [instructionCode, instruction, h1, h2, h3]
  · have h1 : (4*q.val + 2*s.val+1)/4%4 = q.val := by omega
    have h2 : (4*q.val + 2*s.val+1)/2%2 = s.val := by omega
    have h3 : (4*q.val + 2*s.val+1)%2 ≠ 0 := by omega
    simp [instructionCode, instruction, h1, h2, h3]

def machineCode (b c : Fin 2) (q : Fin 4) (u : Fin 4 → Fin 4 × Stmt (Fin 2)) : ℕ :=
  instructionCode (u 1) + 16*instructionCode (u 2) + 256*instructionCode (u 3) +
    4096*q.val + 16384*b.val + 32768*c.val

theorem machineCode_lt (b c : Fin 2) (q : Fin 4) (u : Fin 4 → Fin 4 × Stmt (Fin 2)) :
    machineCode b c q u < 65536 := by
  have hb := b.isLt
  have hc := c.isLt
  have hq := q.isLt
  have e1 := instructionCode_lt (u 1)
  have e2 := instructionCode_lt (u 2)
  have e3 := instructionCode_lt (u 3)
  unfold machineCode
  omega

def digit (key : ℕ) : ℕ → ℕ
  | 0 => 7
  | 1 => 16
  | 2 => 11
  | 3 => key % 16
  | 4 => 13+2*(key / 16384 % 2)
  | 5 => key / 16 % 16
  | 6 => 4*(key / 4096 % 4)+2*(key / 32768 % 2)
  | _ => key / 256 % 16

def action (i : ℕ) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
  if i = 16 then none else some (some (instruction i).1, (instruction i).2)

def machine (key : ℕ) : Machine (Fin 2) (Fin 4) :=
  fun r s => action (digit key (2*r.val+s.val))

theorem action_encode (p : Fin 4 × Stmt (Fin 2)) :
    action (instructionCode p) = some (some p.1, p.2) := by
  have h := instructionCode_lt p
  simp [action, instruction_roundtrip, show instructionCode p ≠ 16 by omega]

theorem machine_eq (b c : Fin 2) (q : Fin 4) (u : Fin 4 → Fin 4 × Stmt (Fin 2)) :
    machine (machineCode b c q u) =
      (fun r s =>
        let v : Fin 4 → Fin 4 × Stmt (Fin 2) :=
          ![(1,.write 1 .right),(2,.write 1 .right),(3,.write b .right),(q,.write c .left)]
        if s = 0 then some (some (v r).1, (v r).2)
        else if r = 0 then none else some (some (u r).1, (u r).2)) := by
  let k := machineCode b c q u
  have hb := b.isLt
  have hc := c.isLt
  have hq := q.isLt
  have e1 := instructionCode_lt (u 1)
  have e2 := instructionCode_lt (u 2)
  have e3 := instructionCode_lt (u 3)
  have h1 : k % 16 = instructionCode (u 1) := by dsimp [k, machineCode]; omega
  have h2 : k / 16 % 16 = instructionCode (u 2) := by dsimp [k, machineCode]; omega
  have h3 : k / 256 % 16 = instructionCode (u 3) := by dsimp [k, machineCode]; omega
  have h4 : k / 16384 % 2 = b.val := by dsimp [k, machineCode]; omega
  have h5 : k / 4096 % 4 = q.val := by dsimp [k, machineCode]; omega
  have h6 : k / 32768 % 2 = c.val := by dsimp [k, machineCode]; omega
  change machine k = _
  funext r s
  fin_cases r
  · fin_cases s
    · change action 7 = some (some 1, .write 1 .right)
      exact action_encode (1,.write 1 .right)
    · change action 16 = none
      exact if_pos rfl
  · fin_cases s
    · change action 11 = some (some 2, .write 1 .right)
      exact action_encode (2,.write 1 .right)
    · change action (k % 16) = some (some (u 1).1, (u 1).2)
      rw [h1, action_encode]
  · fin_cases s
    · change action (13+2*(k / 16384 % 2)) = some (some 3, .write b .right)
      rw [h4]
      have h : 13 + 2*b.val = instructionCode (3,.write b .right) := by
        change 13 + 2*b.val = 4*3 + 2*b.val + 1
        omega
      rw [h, action_encode]
    · change action (k / 16 % 16) = some (some (u 2).1, (u 2).2)
      rw [h2, action_encode]
  · fin_cases s
    · change action (4*(k / 4096 % 4)+2*(k / 32768 % 2)) = some (some q, .write c .left)
      rw [h5,h6]
      exact action_encode (q,.write c .left)
    · change action (k / 256 % 16) = some (some (u 3).1, (u 3).2)
      rw [h3, action_encode]

def hasHalted (key : ℕ) : Bool :=
  ((machine key).multiStep (Machine.init []) 107).isNone

end BlankTapeEncoding

namespace BlankTapeEncoding

open Turing Turing.BusyBeaver

structure Certificate where
  n : ℕ
  m : ℕ
  leftTable : ℕ
  rightTable : ℕ
  states : ℕ
  actions : ℕ

def each (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).all p

theorem each_of {n i : ℕ} {p : ℕ → Bool} (h : each n p = true) (hi : i < n) : p i = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr hi)

def get (w b i : ℕ) : ℕ := Nat.land (Nat.shiftRight w (b*i)) (2^b-1)

def leftNext (c : Certificate) (s i : ℕ) : ℕ := get c.leftTable 7 (s*c.n+i) % c.n
def rightNext (c : Certificate) (s j : ℕ) : ℕ := get c.rightTable 7 (s*c.m+j) % c.m

def safe (c : Certificate) (qa i j : ℕ) : Bool :=
  c.states.testBit (qa*c.n*c.m+i*c.m+j)

def permits (c : Certificate) (qa cmd : ℕ) : Bool :=
  c.actions.testBit (17*qa+cmd)

def successorOk (c : Certificate) (qa cmd s t i j : ℕ) : Bool :=
  let il := leftNext c s i
  let jr := rightNext c t j
  if safe c qa il jr then
    let w := cmd / 2 % 2
    let r := cmd / 4 % 4
    decide (cmd < 16) &&
      if cmd % 2 = 0 then safe c (2*r+s) i (rightNext c w jr)
      else safe c (2*r+t) (leftNext c w il) j
  else true

def transitionsOk (c : Certificate) : Bool :=
  each 8 fun qa => each 17 fun cmd => !(permits c qa cmd) ||
    (each 2 fun s => each 2 fun t => each c.n fun i => each c.m fun j =>
      successorOk c qa cmd s t i j)

def accepts (c : Certificate) (k : ℕ) : Bool :=
  each 8 fun qa => permits c qa (digit k qa)

def correct (c : Certificate) : Bool :=
  decide (0 < c.n ∧ 0 < c.m ∧ leftNext c 0 0 = 0 ∧ rightNext c 0 0 = 0) &&
    (safe c 0 0 0 && transitionsOk c)

theorem digit_bound (k qa : ℕ) : digit k qa < 17 := by
  fun_cases digit k qa <;> omega

def Certifies (N : Machine (Fin 2) (Fin 4)) : Prop :=
  ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : Fin 2 → Fin n → Fin n)
    (R : Fin 2 → Fin m → Fin m) (S : Fin 4 → Fin 2 → Fin n → Fin m → Bool),
    L 0 x = x ∧ R 0 y = y ∧ S 0 0 x y = true ∧
    ∀ q a s t i j, S q a (L s i) (R t j) = true →
      ∃ r w d, N q a = some (some r, Stmt.write w d) ∧
        (match d with
         | .left => S r s i (R w (R t j))
         | .right => S r t (L w (L s i)) j) = true

theorem soundCertificate (c : Certificate) (k : ℕ)
    (h : correct c = true) (allowed : accepts c k = true) : Certifies (machine k) := by
  unfold correct at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hn,hm,hl,hr⟩,hh,ht⟩ := h
  let L (s : Fin 2) (i : Fin c.n) : Fin c.n :=
    ⟨leftNext c s.val i.val, Nat.mod_lt _ hn⟩
  let R (t : Fin 2) (j : Fin c.m) : Fin c.m :=
    ⟨rightNext c t.val j.val, Nat.mod_lt _ hm⟩
  let S (q : Fin 4) (a : Fin 2) (i : Fin c.n) (j : Fin c.m) : Bool :=
    safe c (2*q.val+a.val) i.val j.val
  refine ⟨c.n,c.m,⟨0,hn⟩,⟨0,hm⟩,L,R,S,Fin.ext hl,Fin.ext hr,hh,?_⟩
  intro q a s t i j hsafe
  let qa := 2*q.val+a.val
  let cmd := digit k qa
  have hqa : qa < 8 := by
    have hq := q.isLt
    have ha := a.isLt
    dsimp [qa]
    omega
  have hpermit : permits c qa (digit k qa) = true :=
    each_of (p := fun d => permits c d (digit k d)) allowed hqa
  unfold transitionsOk at ht
  have htransition := each_of (each_of ht hqa) (digit_bound k qa)
  rw [hpermit, Bool.not_true, Bool.false_or] at htransition
  have hstep := each_of (each_of (each_of (each_of htransition s.isLt) t.isLt) i.isLt) j.isLt
  change safe c qa (leftNext c s.val i.val) (rightNext c t.val j.val) = true at hsafe
  unfold successorOk at hstep
  simp only [hsafe, if_true, Bool.and_eq_true, decide_eq_true_eq] at hstep
  have hcmd : cmd ≠ 16 := by omega
  refine ⟨(instruction cmd).1, (instruction cmd).2.symbol, (instruction cmd).2.dir, ?_, ?_⟩
  · change action cmd = _
    simp [action, hcmd]
  · change (match if cmd % 2 = 0 then Dir.left else Dir.right with
      | .left => safe c (2*(cmd/4%4)+s.val) i.val
          (rightNext c (cmd/2%2) (rightNext c t.val j.val))
      | .right => safe c (2*(cmd/4%4)+t.val)
          (leftNext c (cmd/2%2) (leftNext c s.val i.val)) j.val) = true
    by_cases d : digit k qa % 2 = 0
    · simpa only [cmd, if_pos d] using hstep.2
    · simpa only [cmd, if_neg d] using hstep.2

end BlankTapeEncoding

namespace KeyBitmap

def row (width : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 2^width-1 else 0) ||| (row width bs <<< width)

theorem row_bit {width : ℕ} (hw : 0 < width) (bs : List Bool) (k : ℕ) :
    (row width bs).testBit k = (bs[k/width]?).getD false := by
  induction bs generalizing k with
  | nil => simp [row]
  | cons b bs ih =>
    by_cases hk : k < width
    · have hm : k/width=0 := Nat.div_eq_of_lt hk
      cases b <;> simp [row, hm, hk, Nat.not_le_of_lt hk, Nat.testBit_shiftLeft]
    · have hle : width ≤ k := Nat.le_of_not_gt hk
      have ha : k-width+width=k := by omega
      have hd : k/width = (k-width)/width+1 := by
        calc
          k/width = (k-width+width)/width := by rw [ha]
          _ = _ := Nat.add_div_right _ hw
      cases b <;> simp [row, hd, hk, hle, ih, Nat.testBit_shiftLeft]

def repeatWord (width w : ℕ) : ℕ → ℕ
  | 0 => w
  | n+1 =>
    let lower := repeatWord width w n
    lower ||| (lower <<< (width*2^n))

theorem repeat_bound {width w : ℕ} (h : w < 2^width) (n : ℕ) :
    repeatWord width w n < 2^(width*2^n) := by
  induction n with
  | zero => simpa [repeatWord] using h
  | succ n ih =>
    let d := width*2^n
    have hs : width*2^(n+1) = d+d := by rw [pow_succ, ← Nat.mul_assoc]; dsimp [d]; omega
    rw [repeatWord, hs]
    have hlow : repeatWord width w n < 2^(d+d) := by
      apply lt_of_lt_of_le ih
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hhigh : repeatWord width w n <<< d < 2^(d+d) := by
      rw [Nat.shiftLeft_eq, pow_add]
      exact Nat.mul_lt_mul_of_pos_right ih (by positivity)
    exact Nat.or_lt_two_pow hlow hhigh

theorem repeat_bit {width w : ℕ} (h : w < 2^width) (n k : ℕ)
    (hk : k < width*2^n) : (repeatWord width w n).testBit k = w.testBit (k%width) := by
  induction n generalizing k with
  | zero =>
    simp only [pow_zero, Nat.mul_one] at hk
    rw [repeatWord, Nat.mod_eq_of_lt hk]
  | succ n ih =>
    let d := width*2^n
    have hs : width*2^(n+1) = d+d := by rw [pow_succ, ← Nat.mul_assoc]; dsimp [d]; omega
    rw [hs] at hk
    change (repeatWord width w n ||| repeatWord width w n <<< d).testBit k = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hkd : k < d
    · simp [Nat.not_le_of_lt hkd, ih k hkd]
    · have hd : d ≤ k := Nat.le_of_not_gt hkd
      have hx : k-d < d := by omega
      have hb : (repeatWord width w n).testBit k = false := by
        apply Nat.testBit_lt_two_pow
        exact (repeat_bound h n).trans_le (Nat.pow_le_pow_right (by decide) hd)
      have hp : d%width = 0 := Nat.mul_mod_right _ _
      have hmod : k%width = (k-d)%width := by
        have he : k=k-d+d := by omega
        calc
          k%width = (k-d+d)%width := congrArg (· % width) he
          _ = (k-d)%width := by simp [Nat.add_mod, hp]
      simp [hd, hmod, hb, ih _ hx]

def repeatFactor (width : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => repeatFactor width n * (1 + 2^(width*2^n))

theorem repeat_factor {width w : ℕ} (h : w < 2^width) (n : ℕ) :
    repeatWord width w n = w * repeatFactor width n := by
  induction n with
  | zero => simp [repeatWord, repeatFactor]
  | succ n ih =>
    let lower := repeatWord width w n
    let d := width*2^n
    have hl := repeat_bound h n
    have hor := Nat.shiftLeft_add_eq_or_of_lt hl lower
    change lower ||| (lower <<< d) = _
    rw [Nat.or_comm, ← hor, Nat.shiftLeft_eq,
      show lower * 2^d + lower = lower * (1+2^d) by ring]
    rw [repeatFactor, show lower = w*repeatFactor width n from ih, Nat.mul_assoc]


theorem row_bound {width : ℕ} (hw : 0 < width) (bs : List Bool) :
    row width bs < 2^(width*bs.length) := by
  by_contra! h
  obtain ⟨i,hi,hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow h
  have hn : bs.length ≤ i/width := (Nat.le_div_iff_mul_le hw).mpr (by simpa [Nat.mul_comm] using hi)
  have he : (bs[i/width]?) = none := List.getElem?_eq_none hn
  simp [row_bit hw, he] at hbit

def coordinate (width steps times : ℕ) (accept : ℕ → Bool) : ℕ :=
  row width ((List.range steps).map accept) * repeatFactor (width*steps) times

theorem coordinate_bit {width steps times k : ℕ} (hw : 0 < width) (hs : 0 < steps)
    (hk : k < width*steps*2^times) (accept : ℕ → Bool) :
    (coordinate width steps times accept).testBit k = accept (k/width%steps) := by
  have len : ((List.range steps).map accept).length = steps := by simp
  have hbound := row_bound hw ((List.range steps).map accept)
  rw [len] at hbound
  have hi : k%(width*steps)/width < steps := by
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa [Nat.mul_comm] using (Nat.mod_lt k (Nat.mul_pos hw hs))
  have rem : k%(width*steps)/width = k/width%steps := by
    exact (Nat.mod_mul_right_div_self k width steps)
  rw [coordinate, ← repeat_factor hbound times, repeat_bit hbound times k hk, row_bit hw]
  rw [List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, rem]

end KeyBitmap

namespace BlankTapeEncoding

open Turing Turing.BusyBeaver KeyBitmap

def permission (w q a : ℕ) : Bool := w.testBit (17*q+a)

def sharedAllowed (w k : ℕ) : Bool := each 8 fun qa => permission w qa (digit k qa)

def guardedTrace (w key : ℕ) (start : Cfg (Fin 2) (Fin 4)) :
    ℕ → Bool × Option (Cfg (Fin 2) (Fin 4))
  | 0 => (true, some start)
  | n+1 =>
    match guardedTrace w key start n with
    | (ok, none) => (ok,none)
    | (ok, some config@⟨none, _⟩) => (ok, (machine key).step config)
    | (ok, some config@⟨some q,t⟩) =>
      let qa := 2*q.val+t.1.val
      let exactRow := get w 17 qa == 2^(digit key qa)
      (ok && exactRow, (machine key).step config)

theorem exactPermission {w q a b : ℕ}
    (ha : a < 17) (h : get w 17 q = 2^b) (hw : permission w q a = true) : a = b := by
  have hb : (get w 17 q).testBit a = true := by
    change ((w >>> (17*q)) &&& (2^17-1)).testBit a = true
    simp only [ Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
      ha, decide_true, Bool.and_true]
    unfold permission at hw
    simpa only [Nat.add_comm] using hw
  rw [h, Nat.testBit_two_pow, decide_eq_true_eq] at hb
  exact hb.symm

theorem guardedTrace_sound (w rep k : ℕ) (cfg : Cfg (Fin 2) (Fin 4))
    (halves : sharedAllowed w k = true) (n : ℕ)
    (h : (guardedTrace w rep cfg n).1 = true) :
    (machine k).multiStep cfg n = (guardedTrace w rep cfg n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Machine.multiStep_succ]
    have g := h
    unfold guardedTrace at g ⊢
    generalize eq : guardedTrace w rep cfg n = step at g ⊢
    obtain ⟨ok, next⟩ := step
    cases next with
    | none =>
      have last := ih (by simpa [eq] using g)
      simp [eq] at last
      simp [last, Machine.step]
    | some current =>
      obtain ⟨q,t⟩ := current
      cases q with
      | none =>
        have last := ih (by simpa [eq] using g)
        simp [eq] at last
        simp [last, Machine.step]
      | some q =>
        let qa := 2*q.val+t.1.val
        change (ok && (get w 17 qa == 2^digit rep qa)) = true at g
        rw [Bool.and_eq_true_iff, beq_iff_eq] at g
        have last := ih (by simpa [eq] using g.1)
        simp [eq] at last
        have hi : qa < 8 := by
          have hq := q.isLt
          have ht := t.1.isLt
          dsimp [qa]
          omega
        have hp : permission w qa (digit k qa) = true := each_of (p := fun qa => permission w qa (digit k qa)) halves hi
        have hd := exactPermission (digit_bound k qa) g.2 hp
        rw [last]
        change (machine k).step ⟨some q,t⟩ = (machine rep).step ⟨some q,t⟩
        simp only [Machine.step, machine]
        exact congrArg (fun x => (action x).map _) hd

end BlankTapeEncoding

namespace BlankTapeEncoding

private theorem each_intro {n : ℕ} {p : ℕ → Bool} (h : ∀ i < n, p i = true) :
    each n p = true :=
  List.all_eq_true.mpr fun i hi => h i (List.mem_range.mp hi)

def transitionsFast (c : Certificate) : Bool :=
  each 8 fun qa => each 2 fun s => each 2 fun t => each c.n fun i => each c.m fun j =>
    let li := leftNext c s i
    let rj := rightNext c t j
    if safe c qa li rj then
      each 17 fun cmd =>
        let w := cmd/2%2
        let r := cmd/4%4
        !(permits c qa cmd) ||
          (decide (cmd < 16) &&
            if cmd%2 = 0 then safe c (2*r+s) i (rightNext c w rj)
            else safe c (2*r+t) (leftNext c w li) j)
    else true

theorem transitionsFast_sound (c : Certificate) (h : transitionsFast c = true) :
    transitionsOk c = true := by
  unfold transitionsOk
  apply each_intro
  intro qa hqa
  apply each_intro
  intro cmd hcmd
  by_cases hp : permits c qa cmd = true
  · rw [hp, Bool.not_true, Bool.false_or]
    apply each_intro
    intro s hs
    apply each_intro
    intro t ht
    apply each_intro
    intro i hi
    apply each_intro
    intro j hj
    unfold transitionsFast at h
    have hv := each_of (each_of (each_of (each_of (each_of h hqa) hs) ht) hi) hj
    by_cases safeNow : safe c qa (leftNext c s i) (rightNext c t j) = true
    · simp only [safeNow,if_true] at hv
      have actionSafe := each_of hv hcmd
      simp only [hp,Bool.not_true,Bool.false_or] at actionSafe
      simpa only [successorOk,safeNow,if_true] using actionSafe
    · simp only [successorOk,safeNow,Bool.false_eq_true,if_false]
  · have hh : permits c qa cmd = false := Bool.eq_false_iff.mpr hp
    simp [hh]

def correctFast (c : Certificate) : Bool :=
  decide (0 < c.n ∧ 0 < c.m ∧ leftNext c 0 0 = 0 ∧ rightNext c 0 0 = 0) &&
    (safe c 0 0 0 && transitionsFast c)

theorem correctFast_sound (c : Certificate) (h : correctFast c = true) :
    correct c = true := by
  simp only [correctFast, Bool.and_eq_true_iff] at h
  simp only [correct, Bool.and_eq_true_iff]
  exact ⟨h.1, h.2.1, transitionsFast_sound c h.2.2⟩

end BlankTapeEncoding

namespace BlankTapeEncoding

open Turing Turing.BusyBeaver

inductive Outcome where
  | invariance (c : Certificate)
  | halting (permissions representative time : ℕ)

def Outcome.permissions : Outcome → ℕ
  | .invariance c => c.actions
  | .halting a _ _ => a

def Outcome.valid : Outcome → Bool
  | .invariance c => correctFast c
  | .halting a rep n =>
      let (sound,last) := guardedTrace a rep (Machine.init []) n
      decide (n ≤ 107) && (sound && last.isNone)

theorem Outcome.sound (row : Outcome) (k : ℕ) (h : row.valid = true)
    (allowed : sharedAllowed row.permissions k = true)
    (alive : ∃ r T, (machine k).multiStep (Machine.init []) 107 = some ⟨some r,T⟩) :
    Certifies (machine k) := by
  cases row with
  | invariance c => exact soundCertificate c k (correctFast_sound c h) allowed
  | halting a rep n =>
    change (decide (n ≤ 107) && ((guardedTrace a rep (Machine.init []) n).1 &&
        (guardedTrace a rep (Machine.init []) n).2.isNone)) = true at h
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
    have eq := guardedTrace_sound a rep k (Machine.init []) allowed n h.2.1
    rw [Option.eq_none_of_isNone h.2.2] at eq
    have noneAt := Machine.multiStep_eq_none_mono eq h.1
    obtain ⟨r,t,hr⟩ := alive
    rw [noneAt] at hr
    exact False.elim (Option.some_ne_none _ hr.symm)

end BlankTapeEncoding

namespace BlankTapeEncoding

open Turing Turing.BusyBeaver KeyBitmap

def highAllowed (a h : ℕ) : Bool :=
  permission a 0 7 && permission a 1 16 && permission a 2 11 &&
    permission a 4 (13+2*(h/64%2)) &&
    permission a 6 (4*(h/16%4)+2*(h/128%2)) && permission a 7 (h%16)

def lowBitmap (a : ℕ) : ℕ :=
  coordinate 1 16 4 (permission a 3) &&& coordinate 16 16 0 (permission a 5)

theorem lowBitmap_bit (a l : ℕ) (hl : l < 256) :
    (lowBitmap a).testBit l = (permission a 3 (l%16) && permission a 5 (l/16%16)) := by
  have h1 : l < 1*16*2^4 := hl
  have h2 : l < 16*16*2^0 := hl
  rw [lowBitmap, Nat.testBit_and, coordinate_bit (by decide) (by decide) h1,
    coordinate_bit (by decide) (by decide) h2, Nat.div_one]

theorem combineByte (a k : ℕ) (high : highAllowed a (k/256) = true)
    (low : (lowBitmap a).testBit (k%256) = true) : sharedAllowed a k = true := by
  rw [lowBitmap_bit a _ (Nat.mod_lt _ (by decide : 0 < 256))] at low
  rw [Nat.mod_mod_of_dvd k (by decide : 16 ∣ 256),
    show k%256/16=k/16%16 from Nat.mod_mul_right_div_self k 16 16] at low
  simp only [Nat.mod_mod] at low
  simp only [highAllowed, Nat.div_div_eq_div_mul] at high
  unfold sharedAllowed each
  rw [show List.range 8 = [0,1,2,3,4,5,6,7] by decide]
  simp only [List.all_cons,List.all_nil,Bool.and_true,digit]
  have eq :
      (permission a 0 7 && (permission a 1 16 &&
        (permission a 2 11 && (permission a 3 (k%16) &&
          (permission a 4 (13+2*(k/16384%2)) && (permission a 5 (k/16%16) &&
            (permission a 6 (4*(k/4096%4)+2*(k/32768%2)) && permission a 7 (k/256%16))))))))
      = ((permission a 0 7 && permission a 1 16 && permission a 2 11 &&
          permission a 4 (13+2*(k/16384%2)) && permission a 6 (4*(k/4096%4)+2*(k/32768%2)) &&
          permission a 7 (k/256%16)) && (permission a 3 (k%16) && permission a 5 (k/16%16))) := by
    ac_rfl
  exact eq.trans (by rw [high,low]; rfl)

def lookupRow (rows : List (List Outcome)) (i : ℕ) : Option Outcome :=
  (rows[i/32]?.getD [])[i%32]?

theorem lookupRow_mem {rows : List (List Outcome)} {i : ℕ} {row : Outcome}
    (h : lookupRow rows i = some row) : ∃ g ∈ rows, row ∈ g := by
  unfold lookupRow at h
  generalize hr : rows[i/32]? = group at h
  cases group with
  | none => simp at h
  | some g =>
    exact ⟨g,List.mem_of_getElem? hr,List.mem_of_getElem? h⟩

def byteCover (rows : List (List Outcome)) (high : ℕ) : List ℕ → ℕ
  | [] => 0
  | i :: is =>
    match lookupRow rows i with
    | none => byteCover rows high is
    | some row =>
      let tail := byteCover rows high is
      let mask := row.permissions
      if highAllowed mask high then lowBitmap mask ||| tail else tail

theorem byteCover_sound (rows : List (List Outcome)) (h l : ℕ) (indices : List ℕ)
    (b : (byteCover rows h indices).testBit l = true) :
    ∃ g ∈ rows, ∃ row ∈ g, highAllowed row.permissions h = true ∧ (lowBitmap row.permissions).testBit l = true := by
  induction indices with
  | nil => simp [byteCover] at b
  | cons i rest ih =>
    rw [byteCover] at b
    generalize hg : lookupRow rows i = result at b
    cases result with
    | none => exact ih b
    | some row =>
      by_cases hallow : highAllowed row.permissions h = true
      · simp only [hallow, if_true, Nat.testBit_or, Bool.or_eq_true] at b
        rcases b with first | rest
        · obtain ⟨g,hg',hr⟩ := lookupRow_mem hg
          exact ⟨g,hg',row,hr,hallow,first⟩
        · exact ih rest
      · have hb : highAllowed row.permissions h = false := Bool.eq_false_iff.mpr hallow
        simp only [hb,Bool.false_eq_true,if_false] at b
        exact ih b

theorem byteCertificate (rows : List (List Outcome)) (indices : ℕ → List ℕ) (k : ℕ) (hk : k < 65536)
    (hcover : ∀ h < 256, byteCover rows h (indices h) = 2^256-1)
    (hvalid : rows.all (·.all Outcome.valid) = true)
    (alive : ∃ r T, (machine k).multiStep (Machine.init []) 107 = some ⟨some r,T⟩) :
    Certifies (machine k) := by
  have hh : k/256 < 256 := by omega
  have hl : k%256 < 256 := Nat.mod_lt _ (by decide)
  have test : (byteCover rows (k/256) (indices (k/256))).testBit (k%256) = true := by
    rw [hcover (k/256) hh, Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    exact hl
  obtain ⟨g,hg,row,hr,high,low⟩ := byteCover_sound rows _ _ _ test
  have valid := List.all_eq_true.mp (List.all_eq_true.mp hvalid g hg) row hr
  exact row.sound k valid (combineByte row.permissions k high low) alive

end BlankTapeEncoding

namespace BlankTapeEncoding

private def group0 : List Outcome := [
.invariance ⟨1,1,0x0,0x0,0xfd,0x7ff815541ffe0a0007ff80200200000080⟩,
.invariance ⟨2,2,0x204000,0x204080,0x1040405,0x7fff80005fffe20007fff8200200000080⟩,
.invariance ⟨1,2,0x0,0x204080,0x5151,0x5d5d04041fffea0005d5d0200200000080⟩,
.invariance ⟨1,2,0x0,0x204080,0x1511,0x7fff804015754a0007fff8200200000080⟩,
.invariance ⟨1,2,0x0,0x204000,0xff31,0x7f8015401fe00a00000078200200000080⟩,
.invariance ⟨2,1,0x204000,0x0,0x5ff3,0x17fa815545fe0200017f80200200000080⟩,
.invariance ⟨2,2,0x204000,0x204080,0x1040501,0x7fff80041fffe20002aa28200200000080⟩,
.invariance ⟨1,2,0x0,0x204080,0x1151,0x7fff80041fffea000555d0200200000080⟩,
.invariance ⟨2,2,0x204000,0x204080,0x1050401,0x7fff80400a8aa20007fff8200200000080⟩,
.invariance ⟨1,2,0x0,0x204080,0x5111,0x5d5504001fffea0007fff8200200000080⟩,
.invariance ⟨1,2,0x0,0x204080,0xf111,0x70001400001fea0007fff8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x1008208013,0x7fff80011fffe200014010200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4101a008001,0x44101000abfe20007fff8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x120801a001,0x7fff80100410420007aaf8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4101a008009,0x481001abfe20007fff8200200000080⟩,
.invariance ⟨1,3,0x0,0x1020208100,0x496c1,0x7fff801014234a00005500200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x100820801b,0x7fff80011fffe200000040200200000080⟩,
.invariance ⟨1,3,0x0,0x1020208100,0x253241,0x5f5d010014140a0005f5d0200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x120801a009,0x7fff80100001020007aaf8200200000080⟩,
.invariance ⟨1,3,0x0,0x1010208100,0x596c1,0x78054015c0a00005700200200000080⟩,
.invariance ⟨1,2,0x0,0x204080,0xb111,0x28001000001fea0007fff8200200000080⟩,
.invariance ⟨1,3,0x0,0x1020208100,0x25b041,0x55010001400a0007fff8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x1008608013,0x7fff80011fffe200000400200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x10086c9013,0x7fff80011fffe200000100200200000080⟩,
.invariance ⟨2,2,0x204000,0x204080,0x330e0401,0x12000100001fe20007fff8200200000080⟩,
.invariance ⟨1,2,0x0,0x204080,0x1551,0x7fff804415774a00055dd0200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x1008249013,0x6d7580011fffe200000080200200000080⟩,
.invariance ⟨1,2,0x0,0x204080,0x5511,0xd5044002154a0007fff8200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33ff0e01,0x17a0011005e00200000078200200000080⟩,
.invariance ⟨1,3,0x0,0x1020208100,0x2494c1,0x5df50010177d4a00055000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x1009208013,0x7fff80011ea36200001000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x204081000c100,0xf00000dd0ffd999000001,0x3fd780101fffe800000080200200000080⟩
]

private def group1 : List Outcome := [
.invariance ⟨1,3,0x0,0x810200100,0xfc7b41,0x780814040001ea0007d080200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x1c703a02d001,0x801001a1fe20007fff8200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x38dac008001,0x7f81000020080007fff8200200000080⟩,
.invariance ⟨2,2,0x204000,0x204080,0x330f0401,0x800100001fe20007fff8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x120801b001,0x7fff80100004020006a0f8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4101a009001,0x1001000abfe20006daf8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4101b008001,0x1000100001de20007fff8200200000080⟩,
.invariance ⟨4,1,0x60c081060c100,0x0,0x75333303,0x2a800010aaa020002aa00200200000080⟩,
.invariance ⟨2,1,0x204000,0x0,0xdfa3,0x17c0000145f00200028000200200000080⟩,
.invariance ⟨1,3,0x0,0x1020208100,0x253041,0x55010014000a0007fff8200200000080⟩,
.invariance ⟨1,3,0x0,0x1020208000,0x2cb6c3,0x25044400094a0005dd80200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x8008688001,0x7fff80100a80a800000400200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x80084c9001,0x7fff80100a80a800000100200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x160801a001,0x68570010010002000688f8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x16c901a001,0x68570010004002000688f8200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x7f6d01a001,0x68570010002002000680f8200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x88001208001,0x4010001fffe800005050200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x8281008001,0x2a81000100080007fff8200200000080⟩,
.invariance ⟨2,3,0x4000,0x1010208100,0x80c1008001,0x2a81000040080007fff8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x241008208013,0x44100011fffe200008000200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x88201008001,0x40010000001480007fff8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x488048008009,0x10010000001280007fff8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x488008048009,0x1010001fffe800000048200200000080⟩,
.invariance ⟨1,3,0x0,0x1010208100,0x6c1641,0x5010000001ea00050000200200000080⟩,
.invariance ⟨1,3,0x0,0x1010208100,0x4c1641,0x5010000001ea00000500200200000080⟩,
.invariance ⟨1,3,0x0,0x1020208000,0x2db2c3,0x205044417760a00002050200200000080⟩,
.invariance ⟨1,4,0x0,0x6041810604100,0x55235503,0x705010002020a00007050200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x1248208013,0x7fff800101104200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4101a208013,0x201001fffe200004010200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33ff0c05,0x1780810045e00200068078200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x88041008001,0x10010000010480007fff8200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x88001048001,0x1010001fffe800001010200200000080⟩
]

private def group2 : List Outcome := [
.invariance ⟨2,3,0x204000,0x1020208100,0x4121a01a001,0x2001000010420007fff8200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x16c969a013,0x6805000100480200001200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48008488009,0x480101ffde800010000200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c181060c100,0x3210003055540031,0x810001fffe800000040200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c181060c100,0x3210003055540003,0x810001fffe800000010200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48488008009,0x81000400080007fff8200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x30555432100031,0x7fff801000010800000800200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x30555432100003,0x7fff801000004800000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x8048488009,0x7fff801000002800001000200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3a43a005e04000028000001,0x8010000000220007fff8200200000080⟩,
.invariance ⟨1,3,0x0,0x810208100,0x4c1e41,0x5010000001ea00020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4121a01a009,0x2001000001020007fff8200200000080⟩,
.invariance ⟨1,4,0x0,0x60c181060c100,0x11235503,0x5858010000020a00000050200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4101a20801b,0x201001fffe200000040200200000080⟩,
.invariance ⟨1,3,0x0,0x1020208100,0x2496c1,0xd001002034a00050500200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x120825a009,0x7fff801000020200000040200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x120825a001,0x7fff801000020200000010200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810208100,0x120c2000008038008000013,0x200000011fffe200020000200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810208100,0x3f1c2000008038008000013,0x200000011fffe200008000200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810208100,0x361c4000008038008000013,0x80000011fffe200020000200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810208100,0x2d145000008038008000013,0x80000011fffe200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x241008209013,0x1000011fffe200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x24100820801b,0x400011fffe200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x124820801b,0x7fff800100010200000800200200000080⟩,
.invariance ⟨4,2,0x4081810208100,0x204080,0x545014100040001,0x8004000000220007fff8200200000080⟩,
.invariance ⟨4,2,0x4081810608100,0x204080,0x440004001040001,0x804001fffe200000008200200000080⟩,
.invariance ⟨1,3,0x0,0x1020208000,0x6cb2c3,0x5d8004408014a00020050200200000080⟩,
.invariance ⟨1,2,0x0,0x204080,0x5551,0x8d044402034a00008850200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x1c703af69013,0x20201011a00a200000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x10c9608013,0x6c75800100508200001000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c081060c100,0x554100000100320110000321,0x400101efbe800008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x24120801a001,0x4100100200020002aaf8200200000080⟩
]

private def group3 : List Outcome := [
.invariance ⟨3,4,0x1020200000,0x60c081060c100,0x445100000100230010000003,0x100101bfba800008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x8488048009,0x206f810000040800000048200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x208001088001,0x50500100880a800040000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x80c9688013,0x3ed7801000008800001000200200000080⟩,
.invariance ⟨1,4,0x0,0x60c081060c100,0x23553103,0xd0100000014a00000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0xc101a0c9001,0x1001000001e200012100200200000080⟩,
.invariance ⟨1,3,0x0,0x1020208100,0x25b241,0x8d010001540a00000850200200000080⟩,
.invariance ⟨1,3,0x0,0x810208100,0x1fd4c1,0x7801000200a00005a00200200000080⟩,
.invariance ⟨4,1,0x60c081060c100,0x0,0x75223303,0x2800010f1a0200028000200200000080⟩,
.invariance ⟨2,1,0x204000,0x0,0xdaf3,0x147800014a000200014780200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x8081048001,0x2022810000040800041410200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x48001088001,0x414100100880a800010000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x24120801a009,0x400100200020002aaf8200200000080⟩,
.invariance ⟨1,4,0x0,0x60c081060c100,0x3753301,0x7801000140a00000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x160869a013,0x6805000101100200000200200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33ff0d01,0x1788010405e00200000028200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x8081208001,0x2022810000100800000050200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x868869a001,0x2810000180800000600200200000080⟩,
.invariance ⟨1,4,0x0,0x60c081060c100,0x33553103,0x80100000014a00050000200200000080⟩,
.invariance ⟨1,4,0x0,0x60c081060c100,0x23453103,0x80100000014a00000500200200000080⟩,
.invariance ⟨3,2,0x1000208100,0x204080,0x203001084001,0x2010000001e200028000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x4bf0081c8001,0x1010000001ea00008000200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xb3cc0e01,0x1400001008000200000078200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x73cc0e01,0x1400001002000200000078200200000080⟩,
.invariance ⟨3,3,0x820200100,0x810200100,0xe381c71d2002a80001,0x20000100a000200000078200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x241009208013,0x10000011a0d6200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810204100,0x18e28fda001,0x7801400020800000200200200000080⟩,
.invariance ⟨1,3,0x0,0x810204100,0xfd4c1,0x7805000080a00005a00200200000080⟩,
.invariance ⟨2,1,0x204000,0x0,0xdaa3,0x144000014f10020003c400200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0xc101a608013,0x201001a01e200000400200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0xc101a6c9013,0x201001a01e200000100200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x1c71ffe28013,0x1382010100008200011000200200000080⟩
]

private def group4 : List Outcome := [
.invariance ⟨2,2,0x204000,0x204000,0x33cc0e05,0x20801045000200068078200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33ee0e05,0x20801040800200068078200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33ff0e05,0x20801040400200068078200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33dd0e05,0x20801040200200068078200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xe38038fed001,0x402800100000a800000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4101b208013,0x201001a016200001000200200000080⟩,
.invariance ⟨1,4,0x0,0x408101060c100,0x11e34501,0x5010000080a00005200200200000080⟩,
.invariance ⟨1,4,0x0,0x6041810604100,0x55335503,0x85010002020a00000850200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0x1c783bf6901b,0x202010100014200000080200200000080⟩,
.invariance ⟨3,1,0x820200100,0x0,0xa64485,0x10400001000a0200028000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x481008e08013,0x4000011005e200020000200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x810208100,0x1012440fc0200001,0x7801400100800002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x38f6dfda001,0x7800400280800000a00200200000080⟩,
.invariance ⟨3,2,0x1000208100,0x204080,0x303001084001,0x2004000001e200028000200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xbbcc3f05,0x41010000d040200000008200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x1c703df69013,0x8000011a00a200000080200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810200100,0x1d21c200003803c02c000013,0x800010044e200020000200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810200100,0x1ed1c1000038039029000013,0x800010044e200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x7b48e08013,0x6805000104000200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x1688608013,0x6805000101000200002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x16c9608013,0x6805000101400200005000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x14c9608013,0x6805000100400200002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x1249208013,0x6805000100400200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x7dace08013,0x6805000100200200002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x7b6de08013,0x6805000100200200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x7f6de9a013,0x6805000100200200000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x1488e08013,0x6805000100100200002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x7f6ce9a013,0x6805000100080200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x10c96c9013,0x6805000100040200001000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x1248209013,0x6805000100040200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x16086db013,0x6805000100040200000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x1249249013,0x6805000100020200000800200200000080⟩
]

private def group5 : List Outcome := [
.invariance ⟨2,3,0x204000,0x810208100,0x1e08fda013,0x6805000100020200000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x488208008001,0x400100000100800000078200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xeb81ff02d001,0x100100000020800000078200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x604181060c100,0x220100544100000330000001,0x80100000100800000078200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0xc8001208001,0x4010000001e800008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x488008249001,0x4010000001e800000080200200000080⟩,
.invariance ⟨3,3,0x20204080,0x810208100,0xe000c0040080200001,0x2010000001e800040000200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x1010208100,0x4810000406d1200001,0x2010000001e800000400200200000080⟩,
.invariance ⟨3,3,0x20204080,0x1010208100,0x4000c00400c0200001,0x2010000001e800000100200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x488008048001,0x1010000001e800004000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x68801a0c9001,0x1010000001e800002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x488008049001,0x1010000001e800000080200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c0810604100,0x554300320500000330000001,0x40010002000800000078200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xccec3f05,0x4610010000040800000008200200000080⟩,
.invariance ⟨2,3,0x4000,0x1010208100,0x80c1608001,0x2810000100800005000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810204100,0x18fac49a001,0x7810000080800000800200200000080⟩,
.invariance ⟨2,3,0x4000,0x810208100,0x8fc149a001,0x2810000080800005200200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x604181060c100,0x100220100544110000321,0x2022810000020800000040200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x604181060c100,0x100220100454010000003,0x2022810000020800000010200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x810200100,0xfd70001c0480a00001,0x400000100001e800020000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x6041810604100,0x544500000320220010000001,0x40000100001e800008000200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x810208100,0x491000040fc0200001,0x4000100001e800020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48008489001,0x1800100000a800010000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810204100,0x1892c488001,0x7801010000800000800200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x1010208100,0x101b440480200001,0x7801001000800002000200200000080⟩,
.invariance ⟨4,3,0x60c1010004000,0x810200100,0x3f0b80025d200082c000001,0x200100000020200000078200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x5d71ff02d001,0x100100000020200000078200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xfff1ffe28013,0x100100000008a00050000200200000080⟩,
.invariance ⟨4,3,0x60c1010604000,0x810200100,0x3a0bf0051ec000029000001,0x80100000020200000078200200000080⟩,
.invariance ⟨1,4,0x0,0x204081000c100,0x2f4df903,0x80100000014a00020000200200000080⟩,
.invariance ⟨2,4,0x204000,0x204081000c100,0x222f00d0fd990001,0x4010000001e200000080200200000080⟩,
.invariance ⟨3,3,0x20208000,0x810208100,0x1c3000040010200001,0x2010000001e200040000200200000080⟩
]

private def group6 : List Outcome := [
.invariance ⟨4,3,0x4081810008100,0x810204100,0x10403000a04002008000001,0x2010000001e200000800200200000080⟩,
.invariance ⟨4,3,0x8101000c000,0x1010208100,0x902800000400da048000001,0x2010000001e200000400200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x4d301a0c9001,0x1010000001e200002000200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x2323003003550001,0x1010000001e200000080200200000080⟩,
.invariance ⟨4,3,0x4081810008100,0x810208100,0x10407000a04004008000001,0x810000001e200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0xc101a6c9001,0x5001000001e200000500200200000080⟩,
.invariance ⟨1,4,0x0,0x4081810408100,0x1123b901,0x5010000080a00000500200200000080⟩,
.invariance ⟨1,4,0x0,0x608101060c100,0x11737701,0x5010000140a00000200200200000080⟩,
.invariance ⟨1,4,0x0,0x60c101060c100,0x11337701,0x5010000020a00000500200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810204100,0x120c203802800001a000001,0x2000001008000200000078200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810204100,0x3f1c203802800001a000001,0x2000001002000200000078200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810208100,0x3f0c203a08a00001a000001,0x2000001000800200000078200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810204100,0x361c603802800001a000001,0x800001008000200000078200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810204100,0x3f1c703802800001a000001,0x800001002000200000078200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810208100,0x3f14503a08a00001a000001,0x800001000800200000078200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x24120901a001,0x100001002000200000078200200000080⟩,
.invariance ⟨4,2,0x60c081060c100,0x204000,0x3a330d0d000e0001,0x80001008000200000078200200000080⟩,
.invariance ⟨4,2,0x60c081060c100,0x204000,0x35330d0d000e0001,0x80001002000200000078200200000080⟩,
.invariance ⟨4,1,0x20c081040c100,0x0,0xf5ba220b,0x40000010a000200002800200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x1c703ae28013,0x20201011a00a200010000200200000080⟩,
.invariance ⟨6,3,0xa1418406042850404100,0x810200100,0x71c01c71c0fc0e3f038fc0aaf00000061b,0x10200010a000200000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x810204100,0x18f68fdb001,0x7804000020800000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0xc96086db013,0x2001404040800010200200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3fe38002e02038028000003,0x200140000008200028000200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3fe3f005e05038028000003,0x80140000008200028000200200000080⟩,
.invariance ⟨4,3,0x4081810608100,0x810204100,0x38e00e00a00002018000005,0x2014000a000200000008200200000080⟩,
.invariance ⟨4,3,0x60c1010608000,0x1020208100,0x904900005a001009000001,0x804000001e200002000200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33cc0f01,0x28001405000200000078200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33ee0f01,0x28001400800200000078200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33ff0f01,0x28001400400200000078200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33dd0f01,0x28001400200200000078200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x488208009001,0x400100000040800000070200200000080⟩
]

private def group7 : List Outcome := [
.invariance ⟨2,3,0x204000,0x1020208100,0x488048009001,0x100100000040800000070200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x604181060c100,0x220100454110000013000001,0x80100000040800000070200200000080⟩,
.invariance ⟨3,4,0x20200000,0x60c181060c100,0x155101230332000013000001,0x10010002000800000070200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48488208013,0x2010004000800044010200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xe381ffea8013,0x4120001000008800001000200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0xe38838fed011,0x4028001000010800000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0xe38838fed003,0x4028001000004800000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4121a01b001,0x20010000040200000070200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x24120801b001,0x10001002000200000070200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4920869a013,0x2001010004a00010000200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x704203a00a03a00a000013,0x2000000100880200002200200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x5c7038e28013,0x100000010004a200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xbc7038e28013,0x100000010004a200008000200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x704503a00a03a00a000013,0x800000100880200002200200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x1c7038f69013,0x100200011a00a200000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x1fff6de9a013,0x2005000280800010000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xeb81ffe28013,0x100100000008800061000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x488048208013,0x100100000008800004010200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x810200100,0xe870001f8ffdb40001,0x2010000000a800000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x4b802d1c8001,0x1010000000a800000800200200000080⟩,
.invariance ⟨3,18,0x1020200000,0x1e4080d0e2088f0e3438a06203850604490223030b203858c16241060c10100,0x9159c0023290ec00059159c000006154185506154a43b290ec521f1cefc73bf0001645679159e45670000000000000073bf1cefc73bf,0x8100000014800000800200200000080⟩,
.invariance ⟨8,3,0xe1c3050c0c1810e143840a10100,0x810204100,0x71ff1c0e3f038fff028b6f0000030030db000000000005,0x2001000a000800000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xddee3f05,0x810010002040800000008200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48488009001,0x8010004000800000028200200000080⟩,
.invariance ⟨3,12,0x1020200000,0xe2c482122038404101010c1848a0814305000c000,0xd2bd2bcaf15f10bd2b15f15f00fcafcafc8744144144115f15f15f000000000d2bd2bd2b,0x8010002000800000050200200000080⟩,
.invariance ⟨3,4,0x20200000,0x60c181060c100,0x151001200322010010000003,0x1010002000800018000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x8488208001,0x2810000100800040000200200000080⟩,
.invariance ⟨2,3,0x4000,0x810208100,0x8081e08001,0x2810000100800002000200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x80c1208001,0x2810000100800000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x84886c9001,0x2810000100800000100200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x8488249001,0x2810000100800000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x86884db001,0x2810000080800000100200200000080⟩
]

private def group8 : List Outcome := [
.invariance ⟨2,3,0x204000,0x1010208100,0x86880c9001,0x2810000040800004000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x384ad1c8001,0x2810000040800000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x86880db001,0x2810000040800000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x84880c9001,0x2810000040800000100200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x8488049001,0x2810000040800000080200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x608081060c100,0x100320100554330000001,0x2810000020800000400200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x810204100,0x303f160ffa680001,0x2810000020800000200200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x608081060c100,0x100230110445013000001,0x2810000020800000100200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x204081000c100,0xf00220dd0ddd999000001,0x2810000020800000080200200000080⟩,
.invariance ⟨2,2,0x204000,0x204080,0xcc04a401,0x400000100000a800040000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48008488001,0x40000100000a800010000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x1f802d488001,0x8000100000a800010000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x608008688001,0x4000100000a800040000200200000080⟩,
.invariance ⟨2,2,0x4000,0x204080,0xcc012401,0x2000100000a800040000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x6080084c9001,0x1000100000a800040000200200000080⟩,
.invariance ⟨2,2,0x4000,0x204080,0xcc013401,0x800100000a800040000200200000080⟩,
.invariance ⟨3,4,0x20204080,0x60c181060c100,0x140001010100201012000201,0x4001001040800008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0xc960869a013,0x2001001100800010000200200000080⟩,
.invariance ⟨3,4,0x20200000,0x60c181060c100,0x41001111100210232000003,0x1001004004800008000200200000080⟩,
.invariance ⟨2,4,0x204000,0x204081000c100,0xf055d5bb990001,0x2801000020800000800200200000080⟩,
.invariance ⟨3,18,0x1020204000,0x20348111a1c8071e3868b14243850604711122068e0c2420d18101080c10100,0xa79be9e6f051284277000040000109dc0023022218cab022200888004540115004569e6fa79bc144a000000000000004277109dc4277,0x400100000020200000050200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x5d71ffe28013,0x100100000008200031000200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810408100,0x88120100010020010000001,0x40100000014200001000200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xbbee3f05,0x210100000840200000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xbbff3f05,0x110100000440200000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xbbdd3f05,0x90100000240200000008200200000080⟩,
.invariance ⟨3,15,0x810200100,0x585142c306141458a10181830214702162c68218144870a10100,0xc3e187c30fa091224e0001048a0914122052a8e5814a224e00008939127224e449c00000000000085410a8215,0x10100000014200000008200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x49702d1c8001,0x1010000000a200000800200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xffee3f05,0x5000010000040a00000008200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c181060c100,0x1011002322000454000001,0x4000010000020200000028200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x1c71ff02d001,0x100010000020200000028200200000080⟩,
.invariance ⟨11,3,0x50a12203090618283022840a081c4070410100,0x810200100,0x7000e38e38e3ffc0e07e3fe001c7e3f000e3f1f801516abc00000000000c361b,0x201000a000200000200200200000080⟩
]

private def group9 : List Outcome := [
.invariance ⟨2,3,0x204000,0x1020208100,0x4949a208013,0x2010004100200040000200200000080⟩,
.invariance ⟨8,3,0xe183850c141810e142070410100,0x810208100,0x7038fff1c0e3f140a2f0071ff0c061b00000004020b,0x2001000800200028000200200000080⟩,
.invariance ⟨2,3,0x4000,0x1010208100,0x16c941a001,0x5001001000200002000200200000080⟩,
.invariance ⟨2,3,0x4000,0x1010208100,0x16c141a001,0x5001000400200002000200200000080⟩,
.invariance ⟨2,3,0x4000,0x810208100,0x7fed41a001,0x5001000200200002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x124925b001,0x5001000020200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x810204100,0x3e28fda001,0x5001000020200000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x120825b001,0x5001000020200000080200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810208100,0x3a0c2012088038008000013,0x2000000118000200002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0x7c7838e2801b,0x1000000100014200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0xbc7838e2801b,0x1000000100014200008000200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810208100,0x3d145012088038008000013,0x800000112000200002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xfc74bae28013,0x200000110000200022000200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0x1c783be2801b,0x202010100014200010000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48104820801b,0x100000100012200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x5c793de28013,0x80000100014200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0x1c783df6901b,0x80000100014200000080200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x1204202d008038008000013,0x2040000108000200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0x1c7838f6d01b,0x8000100014200000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x1c7038f6d013,0x800010000a200000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0x1c7838f6901b,0x1002000100014200000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x201488208013,0x401000110000200002000200200000080⟩,
.invariance ⟨8,3,0xe1c3050c141810e183840c10100,0x1020204080,0x38e381c0e0700000600c33c0061fe001049000000000005,0x20140000008800002000200200000080⟩,
.invariance ⟨6,3,0x40828206042820808100,0x820204080,0x38038007000080220040c00008000000005,0x20140000008800000800200200000080⟩,
.invariance ⟨3,3,0x20204080,0x810208100,0xe00040040080200001,0x2004000000a800040000200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x1010208100,0x2410000406d1200001,0x2004000000a800000400200200000080⟩,
.invariance ⟨3,3,0x20204080,0x1010208100,0x2000400400c0200001,0x2004000000a800000100200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x810200100,0xf470001f8ffdb40001,0x2004000000a800000080200200000080⟩,
.invariance ⟨3,3,0x20204000,0x810208100,0x93040048fc0240001,0x4000040000a800020000200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x810208100,0x39012440fc0200093,0x2001404000800002000200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x1010208100,0x101b440240200001,0x2800401000800002000200200000080⟩,
.invariance ⟨4,3,0x60c1010004000,0x810200100,0x3f1780025d200082c000001,0x200040000020200000028200200000080⟩
]

private def group10 : List Outcome := [
.invariance ⟨4,2,0x60c1010604000,0x204080,0x515011500050001,0x80040000020200000028200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x1020208100,0x9209001201008008000003,0x80040000008200044000200200000080⟩,
.invariance ⟨3,3,0x20208000,0x810208100,0x1c1000040010200001,0x2004000000a200040000200200000080⟩,
.invariance ⟨4,3,0x4081810008100,0x810204100,0x38e07000a04002008000001,0x2004000000a200000800200200000080⟩,
.invariance ⟨4,3,0x8101000c000,0x1010208100,0x482400000400da048000001,0x2004000000a200000400200200000080⟩,
.invariance ⟨4,2,0x4081810008100,0x204080,0x441004101040001,0x804000000a200000800200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33df0d01,0x208010400200200000078200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33ee0d01,0x1608010400800200000078200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x488208248009,0x400100000020800000040200200000080⟩,
.invariance ⟨2,3,0x4000,0x1020208100,0x88201048001,0x400100000020800000010200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xff81ffe28013,0x100100000008800008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x4880c8608013,0x100100000008800000400200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x4880c86c9013,0x100100000008800000100200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xeb81fff69013,0x100100000008800000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48804820801b,0x100100000008800000040200200000080⟩,
.invariance ⟨4,22,0x20c1010000000,0xc1ca93265009020383871a2c38714203050604415083459324447871c3460c0e2c4870a10100,0x8000a0100020000000000003800400000000000000000380040032020001800000000000684414000200000000005068001004800000148000a01000210b006000280000000000000000000000038004003202000180e001,0x80100000020800000040200200000080⟩,
.invariance ⟨4,25,0xc1010000000,0x883224430e1618a8b220c8831c2430b120c086020c09024408182e28b14144c9101e3448c14203800a10100,0x4d169fa68b4fc000000000000f27c5b8000000000000000000f27c5bf93e2dfc9f16e000000000000037137c00809400000006c24a83612541b092a0d84950000000082029345a7e0a092e0000000000000000000000000706c5b0812008c1904de4f8b7,0x80100000020800000010200200000080⟩,
.invariance ⟨5,4,0x20406080840608080,0x204081000c100,0xfff0ffff000df00dff000090009d0000000001,0x80100000020800000008200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c181060c100,0x330100555100100110000331,0x80100000010800008000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c181060c100,0x220100444100100010000221,0x80100000010800004000200200000080⟩,
.invariance ⟨4,29,0x60c1010204000,0x490126c19b0e2438712603961234a030e4008d160c4870a0c09726708121a18d1732645172a44693244478e18281080c10100,0xabee69fd5f734fc201124e00000004814db38008051400000000000000b5320aada990556d4c82ab6a64155036635f81b31afc0808d76040002a4814db3a40a6d9d20014cc9000a667914dbbbc8a6ddde4536ee9029b6700000000000000000000000000000abee69fd5f734feafb9a7f42dcd3d,0x80100000010800001000200200000080⟩,
.invariance ⟨2,4,0x204000,0x204081000c100,0x22f044d4fd990021,0x80100000010800000080200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x604181060c100,0x220100444100500110000321,0x80100000010800000040200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x604181060c100,0x220100444100550010000223,0x80100000010800000010200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x204081000c100,0x22fff0444ddd0f0090000003,0x80100000004800008000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c181060c100,0x220100444100010010000003,0x80100000004800004000200200000080⟩,
.invariance ⟨5,47,0x183080c0820000100,0x1027403538d1a1c6972e5d3810e043a01a2500c180c6092e1c4970e0c08d200c3900234583121c283025499220b96ac2cad529509928608911a2427cf1d2470d9a32605162a50693244478e18281080c10100,0xa107d95b9a7f420fb2b734ffa1f52496db3d083ecadcd3f00000000000000ea2dd90557a1f52496db380000000000000000000000000000000000001d45bb20aa803a8b764155007516ec82aa00ea2dd9055401d45bb20aac769843cc6bf8ed308798d7e1c8df4411eee3b4c21e635f8001000002aae87d4925b6ce00000202699800000404d33743ea492db670000010134cdf4023eca6ddfe8047d94dbbfd008fb29b77fa011f6536eff4023eca6ddc00000000000000000000000000000000000000000000000000000000005002ec2dcd3da005d85b9a7b420fb2b734fe8017616e69ed083ecadcd3f,0x80100000004800001000200200000080⟩,
.invariance ⟨2,4,0x4000,0x204081000c100,0x22ff44ddfd990003,0x80100000004800000080200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x604181060c100,0x220100444100550110000303,0x80100000004800000040200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x604181060c100,0x220100444100050010000003,0x80100000004800000010200200000080⟩,
.invariance ⟨4,4,0x81810408100,0x20c0810404100,0xf0c4400f004010a080af001c0000a001,0x20100000010800008000200200000080⟩,
.invariance ⟨4,4,0x60c1010000000,0x60c081060c100,0x22001000555411003320101000003321,0x20100000010800000800200200000080⟩
]

private def group11 : List Outcome := [
.invariance ⟨3,3,0x1020200000,0x10200100,0xec70241f8ffdb40081,0x20100000010800000080200200000080⟩,
.invariance ⟨4,21,0xc1010000000,0x70b242c487241c28e1c38187160c4870a0c08f2848a0826488901a3c68c0c281080c10100,0x2c6bc00000b1055058d780000000000000005882aac4155620aab1055005112c41540015400000887998000001635e000000051100a89a21e6600a660000000000000000000000120a018838440280b1af,0x20100000004800008000200200000080⟩,
.invariance ⟨4,4,0x41810208100,0x60c081060c100,0x20000003050550000030001000000303,0x20100000004800000800200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x10200100,0xec70241f8ffdb40003,0x20100000004800000080200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xecee3f05,0x210100000840800000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xecff3f05,0x110100000440800000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xecdd3f05,0x90100000240800000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xeccc3f05,0x410100019040800000008200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48820805a009,0x10100000010800000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48820805a001,0x10100000004800000200200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c181060c100,0x3210103055740011,0x8100000010800000400200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c181060c100,0x3210103055570011,0x8100000010800000100200200000080⟩,
.invariance ⟨9,3,0x40610183860a0c08810184040c10100,0x1020204080,0x1873ce2070381c000003020c33c000c3fc00041240000000000005,0x8100000008800002000200200000080⟩,
.invariance ⟨7,3,0x202081820302182040a10100,0x820204080,0x62070001c0000400220040180000200000000005,0x8100000008800000800200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c181060c100,0x3210103055740001,0x8100000004800000400200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c181060c100,0x3210103055570001,0x8100000004800000100200200000080⟩,
.invariance ⟨11,4,0x4051020287101c28302205080e104870c10100,0x204081000c100,0xd0000fdfdff000ff0fffff0000000000902002d0d2ff0f00f000fdf0900900099d0000000000000000000001,0x8100000002800000800200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xccff3f05,0x100010000040800000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xccfc3f05,0x80010000040800000008200200000080⟩,
.invariance ⟨4,3,0x6081810408100,0x810204100,0x38620e12a02002018000005,0x20010000800800000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xeeee3f05,0x2010010008040800000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xccee3f05,0x10010000800800000008200200000080⟩,
.invariance ⟨8,4,0xe1c3860c101810e143870a08100,0x60c0810604100,0x55503003000005330300005505000000003000003330000000000000005,0x8010002000800000008200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c181060c100,0x444100220100100010000221,0x4010002000800040000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c181060c100,0x554101220322100110000321,0x4010002000800010000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c081060c100,0x554100220100300110000321,0x4010002000800008000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c081060c100,0x444100220100300110000221,0x4010002000800000400200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c081060c100,0x555100330100322332000331,0x4010002000800000200200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c081060c100,0x444100220110303011000221,0x4010002000800000100200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x204081000c100,0x444f00220d90fd9191000221,0x4010002000800000080200200000080⟩,
.invariance ⟨4,4,0x60c1010000000,0x60c081060c100,0x55541000220011003320101000003321,0x4010000080800008000200200000080⟩,
.invariance ⟨3,17,0x1020200000,0x810202478b062438b121c303020c090164040e1a0860614203050800100,0x89a844d4226a0daf089a844d41b5e0daf526ba935d49aec0e3132f8997c48ae0daf06d7836bc0000000000000997c4cbe265f,0x4010000020800008000200200000080⟩
]

private def group12 : List Outcome := [
.invariance ⟨2,4,0x204000,0x408101060c100,0x1010e230cc540011,0x4010000020800000200200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x81000c100,0xc00f00ff0dd0fddb99000601,0x4010000020800000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x1c8488e08013,0x2010004000800002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48489208013,0x2010004000800001000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0xc8488608013,0x2010004000800000400200200000080⟩,
.invariance ⟨2,4,0x204000,0x6041810408100,0xf10a210fa9800ab,0x2010004000800000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0xc84886c9013,0x2010004000800000100200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48488249013,0x2010004000800000080200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4848820801b,0x2010004000800000040200200000080⟩,
.invariance ⟨6,3,0x81028506040840810100,0x1020204080,0x1b800003e000240000e00028000000005,0x2010000080800020000200200000080⟩,
.invariance ⟨9,3,0x18408102060a0c08208203840810100,0x820204080,0x407a00000007400000240e40006140000a00000000000005,0x2010000080800008000200200000080⟩,
.invariance ⟨6,3,0x81028406040840810100,0x1020204080,0x1b8000039000200000e00028000000005,0x2010000020800020000200200000080⟩,
.invariance ⟨8,3,0xa1c2040a1018108083040810100,0x820204080,0x2038000e00c402002001c0030140028000000000005,0x2010000020800008000200200000080⟩,
.invariance ⟨3,4,0x20200000,0x60c181060c100,0x155101220322010010000003,0x1010002000800040000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c081060c100,0x444100220100330110000003,0x1010002000800000400200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c081060c100,0x555100330100032232000003,0x1010002000800000200200200000080⟩,
.invariance ⟨3,4,0x20200000,0x60c181060c100,0x155101220332010011000003,0x1010002000800000100200200000080⟩,
.invariance ⟨2,4,0x4000,0x6041810604100,0x5555223353550003,0x1010002000800000080200200000080⟩,
.invariance ⟨4,4,0xc1010000000,0x60c081060c100,0x51000020001000030001000000003,0x1010000080800008000200200000080⟩,
.invariance ⟨3,25,0x20200000,0x70e2c20b0e2c1878f1c3090e104070c0c20406020c08912604970e38a941e249910e2478d16284870a10100,0x10135a8809ad4404d6a0000000010428008214ac619e000000000801024644c022204091913d526bfea935fc00000016208d2b186784880100000000000000000002a000415092f7aa4d7f,0x1010000020800008000200200000080⟩,
.invariance ⟨2,4,0x204000,0x408101060c100,0x1010e230cc540001,0x1010000020800000200200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x81000c100,0xc00f00ff0dd0dfd9b9000007,0x1010000020800000080200200000080⟩,
.invariance ⟨5,3,0x1830808081060c100,0x810204100,0x7c0000e00140007000600000005,0x810000080800020000200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x310321022320055,0x810000080800010000200200000080⟩,
.invariance ⟨6,3,0x81028406040840810100,0x810204100,0xf800003d000a00000e00018000000005,0x810000020800020000200200000080⟩,
.invariance ⟨6,4,0x81028406040840810100,0x60c0810604100,0x3300000003500005000000050000030000000000005,0x810000020800008000200200000080⟩,
.invariance ⟨2,4,0x204000,0x208101020c000,0xfbf990f0f6b20071,0x4000001000010800008000200200000080⟩,
.invariance ⟨2,4,0x204000,0x208101020c000,0xfbf990f0f6b20007,0x4000001000004800008000200200000080⟩,
.invariance ⟨3,4,0x20204000,0x6081810408100,0x8b9011101102a0033000101,0x1000001000010800020000200200000080⟩,
.invariance ⟨3,4,0x20200000,0x4081810408100,0x83001111100200232000001,0x1000001000004800020000200200000080⟩,
.invariance ⟨4,8,0x60c1010000000,0x6180810c0418104143800a10100,0xffffb7dfff35ff3535353535ffffdbbfffffb7dfb7b7b72700000000dfdfdf9f,0x800001000010800008000200200000080⟩,
.invariance ⟨2,14,0x4000,0x22808a140c08a1004301060438a1a2860b00241870a10100,0xa6de99fa6de8b5a2d68b5836e99fa6de99fa6dc3a70000000617e99f,0x800001000004800008000200200000080⟩
]

private def group13 : List Outcome := [
.invariance ⟨9,3,0x4080e183070a0c0880c201020c10100,0x1020204080,0x7c07c38038000000c3004030c0381c7000240240000000024065,0x200001000008800020000200200000080⟩,
.invariance ⟨10,3,0x121c4870c2038506044890c241020c10100,0x1020204080,0xf80f80e00e0000000618104030c187038c00009009000000000024065,0x200001000008800008000200200000080⟩,
.invariance ⟨14,70,0x1a3468c163448d1034304060468d1a3450d1a346870a34100,0x7d01bb360b95838a1d82e56043a94d0df208070d0326405857cf1d0334dcb03661d82e121d583021d4874c911203c70d180e581930e4038d1624385060611d6cc97ad08d19445eb42001ca12a38504ebf325090f1411ebb3ae5c366ad19315eb560608a8017509d2a3427ce9b3230b95284888f1c305080c10100,0x8249244a288924444000000000000000000000000000000000000000000000000000000000000000000000338f2a9ea0ca2a8125000410400008100404000000000000000000a2840d00220401410380400012c800a401000000000000000003fffffffffffffffff000000000000000000000000000000000005aaddad6aaaadb555738f2a9ea0ca2a812500000000000000000338f2a9ea0ca2a81250000000000000000014a2422482088204040a2840d00220401410000000000000000001084028088880210444000004020002000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000052890892082208101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000010080008001100002000000120040000000000000000000000000000000000000000000000000000016ab76b5aaaab6d5550000000000000000000000000000000000008649645a699964c4c000000000000000001084028088880210440000000000000000010840280888802104414405494464050832000002002400160048801051810020d0121000000000000000000000000000000000005aaddad6aaaadb5557fffffffffffffffff00000000000000000000000000000000000a4502429451524888842100a022220084110510152511901420c8000000000000000000510152511901420cb38f2a9ea0ca2a8125200414604008340486000080000040802020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004104000081004040002a0000ca000124000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a450242945152488880000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000200000102008080000000000000000000400100044000282020080000590018803,0x100001000010800008000200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x810208100,0x491000e40fc0200093,0x100001000008800020000200200000080⟩,
.invariance ⟨3,50,0x1000200100,0x5c6980d1a4172d5848d0d324120d509cc1a1a9068d3c50c903c1ca0d3068c161a54a12201468b06243850604d314cbc91f343549156a868f52951a62e652a34031121407ce863834d992e2068d264478e18281080c10100,0x868684da12ddc9011836a8b67868684da12ddc00008002814500828442124dc000080028145008a2420b4554042990828155008a2420b4554511048d14e3b14441234538ed028a5119493f00828442124dd028a5119493f04440014118ec9011836a8b67868684da12ddca091830a8b67000000000000000000000000000000000000001156b8d8c63f0211863371a7c131eb458c7bf,0x100001000004800008000200200000080⟩,
.invariance ⟨4,4,0xc1010000000,0x204081000c100,0x20f00000040d000f00009000000021,0x80001000010800020000200200000080⟩,
.invariance ⟨3,18,0x1020200000,0xe2058722307110e3860a0620385060430f183c80c124078d16241060c10100,0xd98ff663f0001400050001580556015580556015601bb806ee01bb0b59c00230008c2d670b59c2d6700000000000003663fd98fd221f,0x80001000010800008000200200000080⟩,
.invariance ⟨3,15,0x20200000,0x4050c1418606183061018283021c7061c3460b14184870c10100,0x500aa014000000000010046008c0118022020401100220a06000000003060a060c18000000000006050c0f2805,0x80001000004800008000200200000080⟩,
.invariance ⟨6,4,0x40c28206041820808100,0x204081000c100,0xf00d0f0000000000900d00000f000090090000000020021,0x80001000002800008000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c101060c100,0x444100100100220330000101,0x40001000010800008000200200000080⟩,
.invariance ⟨3,4,0x20200000,0x60c101060c100,0x40001111100200232000001,0x40001000004800008000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x208101020c000,0xfb9f99990f80f66b32000701,0x20001000010800008000200200000080⟩,
.invariance ⟨3,14,0x1020200000,0x1420189120c5061420301060450d180c48216144870a10100,0x4055015c2d501540570b5c2d70b5c2d6193864e193241d95f241cd87361cd870000000000181f607d95f,0x20001000004800008000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c181060c100,0x444100010100220112000101,0x10001000010800008000200200000080⟩,
.invariance ⟨3,4,0x20200000,0x60c181060c100,0x40001111100200232000001,0x10001000004800008000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x208101020c000,0xfbbf11990fb0ff3b33000701,0x8001000010800008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xe381fffe8013,0x8001000008800001000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x208101020c000,0xfbbf11990fb0ff33b3000007,0x8001000004800008000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c101060c080,0x1102222100220554000011,0x4001004000800000800200200000080⟩,
.invariance ⟨4,4,0xc1010000000,0x204081000c100,0x4f00000200d000f00009000000021,0x4001002000800002000200200000080⟩,
.invariance ⟨4,34,0x20c1010000000,0x1c8470d1808f9d280ce9c020c61818506131830991183c70d162438506045860a643a03c40b9c266cd03325cb15282098c242080c1c305080c10100,0x5000001400ca0000100010140140000050009940004000000000000000000000000000994000400004c30460000030000000000040a00020ca0220128000000801028000a000002901150000200000000000000000a00000290115000021102c2806800000a4000000000000000000000000000000000000994000400004c3046000003002650001,0x4001002000800000800200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x5510301032320031,0x4001002000800000200200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x608101060c100,0x100100764320220110000101,0x4001001000800000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x20805a488009,0x4001000800800001000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x608181060c100,0x10100444102220110000101,0x4001000400800000800200200000080⟩,
.invariance ⟨4,23,0x40c1010000000,0x38514281830a1c51222141850a0c5030e0c2830234b022054a00084c0101e3868c16244000c10100,0x72968be76d51ca5a2f9db54fffffe000000000001e54eafffffe7953a8f2a75000420040941e7fddc10250000422fffffffffffdca5a2394b4497ee3a5936aa5fb8e924d08000000000000000000000007dbbdc7dd3edf6ef7197471,0x4001000020800002000200200000080⟩,
.invariance ⟨2,4,0x204000,0x81000c100,0xc0f0fdddffb90061,0x4001000020800000800200200000080⟩,
.invariance ⟨9,3,0x3070e203860a0c0870e141050a10100,0x1020204080,0x30c071b81801c01f9000208e001c7000204340000000020065,0x2001008000800002000200200000080⟩,
.invariance ⟨6,4,0xa141840604285040c100,0x6041810408100,0xa0a00f0ff0f0fff00505500a1ab001a1b000000009099,0x2001008000800001000200200000080⟩,
.invariance ⟨12,3,0x101c28810285080e14181102c2080a244850c10100,0x1020204080,0x30000186000e06e060001f803f0400002083c0040e7802004810d000000000008120065,0x2001008000800000800200200000080⟩,
.invariance ⟨4,3,0x6081810408100,0x810208100,0x220003820043a00a000003,0x2001008000800000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x1fff6ce9a013,0x2001004000800000800200200000080⟩
]

private def group14 : List Outcome := [
.invariance ⟨10,3,0xe20409122038506044080c081050c10100,0x820204080,0x2080e02e02007c00d88000208e00038e0004810d000000000120065,0x2001002000800002000200200000080⟩,
.invariance ⟨14,3,0x102c3870a2040b142038506044091a3420818244850c10100,0x820204080,0x400002080000e02e021c0007c00d8024000020823e001031c0102004810d000000000004008120065,0x2001002000800000800200200000080⟩,
.invariance ⟨4,3,0x6081810408100,0x810208100,0x520003820043a00a000003,0x2001002000800000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0xc96c969a013,0x2001000400800010000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810208100,0x1cfe08fda013,0x2001000020800010000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4920869a01b,0x2001000010800010000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c101060c080,0x1102222100220454000001,0x1001004000800000800200200000080⟩,
.invariance ⟨4,20,0xc1010000000,0x1a3430306201910c1468316181880c141811830793241c4901e3860214184870c10100,0x5091050910509105091c4615000000000000000c4615c4615c461500000209022599320902209021a5a71a5a70000000000080040a1261a5a70a12600000000000000000000402144083a40a3ec4615,0x1001002000800000800200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x5510301032320003,0x1001002000800000200200200000080⟩,
.invariance ⟨3,4,0x20204080,0x60c181060c100,0x1001050300200012000001,0x1001001000800000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x20805a488001,0x1001000800800001000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x608181060c100,0x10100444102220010000001,0x1001000400800000800200200000080⟩,
.invariance ⟨3,4,0x20200000,0x60c181060c100,0x45101111110230233000003,0x1001000040800008000200200000080⟩,
.invariance ⟨2,4,0x204000,0x81000c100,0xc0f0fdddffb90007,0x1001000020800000800200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x60c081060c100,0x3101332100220332000555,0x801004000800002000200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x333745422320055,0x801004000800000800200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x311301022320055,0x801004000800000200200200000080⟩,
.invariance ⟨6,3,0xa141840604285040c100,0x1020208100,0x10402090412402090114c028b000000209,0x801002000800001000200200000080⟩,
.invariance ⟨6,4,0x81028306041040610100,0x204081000c100,0x9f000f0000fd000d00d00f00f000990000000000221,0x801002000800000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020204080,0x4ec084ac009,0x801000020800010000200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810208100,0x88120020010010090000011,0x400100000100200000040200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810208100,0x88120020010010091000101,0x400100000100200000010200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810208100,0x88120022010101818000011,0x400100000040200000040200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810208100,0x88120022010101818000001,0x400100000040200000010200200000080⟩,
.invariance ⟨4,3,0x60c1010604000,0x810200100,0x3f0bf0021d21f8028000013,0x200100000008200010000200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3f438002e02038028000003,0x200100000008200022000200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3f438007e02038028000003,0x200100000008200000800200200000080⟩,
.invariance ⟨4,3,0x60c1010004080,0x1010208100,0x1b0980024da61b009000403,0x200100000008200000100200200000080⟩,
.invariance ⟨4,4,0x60c1010608100,0x204081000c100,0x2f0f2000020dd200fd009900000003,0x200100000008200000080200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810208100,0x88120222010011098000011,0x100100000100200000040200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810208100,0x88120222010011099000101,0x100100000100200000010200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810208100,0x88120222010101818000011,0x100100000040200000040200200000080⟩
]

private def group15 : List Outcome := [
.invariance ⟨3,4,0x10200100,0x4081810208100,0x88120222010101818000001,0x100100000040200000010200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xfd71ffe28013,0x100100000008200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x4930c8608013,0x100100000008200000400200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x4930c86c9013,0x100100000008200000100200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x5d71fff69013,0x100100000008200000080200200000080⟩,
.invariance ⟨4,4,0x4101000c000,0x4081810208100,0x801200020201000010009000000101,0x80100000100200000040200200000080⟩,
.invariance ⟨4,4,0x4101000c000,0x4081810208100,0x801200020201000010009000000001,0x80100000100200000010200200000080⟩,
.invariance ⟨4,4,0x8101000c000,0x4081810208100,0x8801200022201001001811800000011,0x80100000040200000040200200000080⟩,
.invariance ⟨4,4,0x101000c000,0x4081810208100,0x801200002201000001001800000001,0x80100000040200000010200200000080⟩,
.invariance ⟨4,12,0x4101000c000,0xa1428502202880a14181141c58a12142870c10100,0x8141100c00008100200000008105008105000020300000000000200000010000290500200000000000000441100c411,0x80100000010200008000200200000080⟩,
.invariance ⟨4,17,0x4101000c000,0x40a140c30d0c185010c20406020c08b202878e182c38a12183070a10100,0x442c184d00180000044288008000000000442c00c0110b003000000c84c00000000008008009830a2002008008009830a20020000000000000000040064184d00190613,0x80100000010200004000200200000080⟩,
.invariance ⟨4,19,0x101000c000,0x8d0a142830a34285140440502142830230392224078e182c10312142870c10100,0xc112221000000400000c112208008000000000c112382245040000040000000ca0c0000000000020008008008000100002000040071038200000000000000000000001080021000000438415,0x80100000010200001000200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0x5df93df69011,0x80100000010200000080200200000080⟩,
.invariance ⟨4,4,0x4081810208100,0x20c0810204100,0x222032000450040040001000000009,0x80100000008200040000200200000080⟩,
.invariance ⟨4,3,0x60c1010604000,0x810200100,0x3f0bf0051ed1f8028000013,0x80100000008200010000200200000080⟩,
.invariance ⟨4,4,0x4081810208100,0x6041810400100,0xfaa0fa0005f0040050005000000003,0x80100000008200004000200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3a43a007e04038028000003,0x80100000008200002000200200000080⟩,
.invariance ⟨4,4,0x60c1010604000,0x208101040c100,0x46067f000809dd0990001000000023,0x80100000008200001000200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3a43a005e04038028000003,0x80100000008200020800200200000080⟩,
.invariance ⟨4,4,0x60c1010608100,0x204081000c100,0x220f2200040dd400fd009900000003,0x80100000008200000080200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x10200100,0x4bb7e49ed1c0a00003,0x80100000004200008000200200000080⟩,
.invariance ⟨4,19,0x200101000c000,0x70e10203011c3870606043081018083023c911201420e1e3460b14184870a10100,0x3416b3b07e760f800003416b8f61c0000000003416a682d4d05a9a0b500000c1e4c000000000002040040b1ec380102002040040b1ec38010200000000000000000009d83e0203004064ec1f,0x80100000004200004000200200000080⟩,
.invariance ⟨4,18,0x101000c000,0x21428114142830a1408a0a202850604711203c70d0e3040b12242870c10100,0x983073819ce06400009830404020000000009830420509830660c100000c60300000000001008040201008040201008040265414040200000000000000000004030100c040333819,0x80100000004200001000200200000080⟩,
.invariance ⟨2,3,0x204000,0x10200100,0x5df93df69003,0x80100000004200000080200200000080⟩,
.invariance ⟨3,4,0x10200100,0x60c101060c100,0x44120010010020030000011,0x40100000010200008000200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810408100,0x88120010010020010000011,0x40100000010200004000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x4930c9608013,0x40100000008200001000200200000080⟩,
.invariance ⟨3,4,0x10200100,0x60c101060c100,0x44120010010020031000101,0x40100000004200008000200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810408100,0x88120010010020011000101,0x40100000004200004000200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810408100,0x88120100010020010000011,0x40100000002200001000200200000080⟩,
.invariance ⟨4,3,0x60c1010004000,0x810200100,0x3f0b8ffa5d20024ba000825,0x20100000800200000008200200000080⟩,
.invariance ⟨4,4,0x4081810608100,0x60c0810604100,0x203000300050000002003000000005,0x20100000400200000008200200000080⟩
]

private def group16 : List Outcome := [
.invariance ⟨4,4,0x4081810608100,0x204081000c100,0x20f00bf0d9d001000200b000000005,0x20100000200200000008200200000080⟩,
.invariance ⟨5,15,0x204020c0800400100,0x81020450a0a285050204283021c3001c2868c16244070c10100,0x3c9ef93df27a0000093793d024c0003c9ef93df27be4f7c9e8022a3e6008a8f98022000000000930000024c04980931ba7374e6e9c00000000000000000011142229e45488a7915,0x20100000040200000008200200000080⟩,
.invariance ⟨7,4,0x81020c08302183040a10100,0x6081810408100,0xb0a0bb0b00faba0b0a1101001998b8a900010100000000999b9b9,0x20100000008200001000200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xffcc3f05,0x10100014000a00000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xfbcc3f05,0x10100002000200000008200200000080⟩,
.invariance ⟨3,13,0x810200100,0x58b0c2050a1628406020c085162c60204144870a10100,0x30f987cc3e2150d3800042a21510a852a3b614a0d3800034e1a70d3869c000000000085442a215,0x10100000100200000008200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810408100,0x88120011010202010000011,0x10100000010200004000200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810408100,0x88120001010202010000011,0x10100000010200001000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x4930c96c8013,0x10100000008200001000200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810408100,0x88120011010202011000101,0x10100000004200004000200200000080⟩,
.invariance ⟨3,4,0x10200100,0x4081810408100,0x88120001010202010000001,0x10100000004200001000200200000080⟩,
.invariance ⟨3,4,0x810200100,0x4081810408100,0x888120001010202010000101,0x10100000002200001000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x4081810408100,0x1011002322220010000889,0x4000010000008200010000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x4081810408100,0x1011003323330010000aab,0x4000010000008200001000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x4081810408100,0x1011002322320110000889,0x4000010000008200000400200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x4081810408100,0x1011002332221011000889,0x4000010000008200000100200200000080⟩,
.invariance ⟨5,8,0x183080c0820400100,0x20408106041810c003860a10100,0xf50000ff00f500000000ff00f5d3d300d300f5ffd3f5d3454545454500000000001b1b131b13,0x4000010000008200000080200200000080⟩,
.invariance ⟨4,3,0x4081810608100,0x810200100,0xe17e02010e02004028000001,0x2000010000020200000008200200000080⟩,
.invariance ⟨4,3,0x4081810608100,0x810200100,0xe2fe05010e02004028000001,0x800010000020200000008200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4121a25a009,0x20010000020200000040200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4121a25a001,0x20010000020200000010200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4969a208013,0x2010001000200040000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x494db208013,0x2010000400200040000200200000080⟩,
.invariance ⟨3,8,0x1020200000,0x20408106041810c003860a10100,0xf5ff00f5fffff5d3d3d3f5f5004f4f4f000000373737,0x2010000200200040000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4949a248013,0x2010000040200040000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4125a20801b,0x2010000010200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4125a208013,0x2010000004200000800200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x3bee3f05,0x2000810000040200020008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x37ee3f05,0x800810000040200008008200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48120821a009,0x40001008000200000040200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48120821a001,0x40001008000200000010200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48120805a009,0x10001008000200000040200200000080⟩
]

private def group17 : List Outcome := [
.invariance ⟨2,3,0x204000,0x1020208100,0x48120805a001,0x10001008000200000010200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c181060c100,0x2301103054770031,0x8001008000200000040200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c181060c100,0x2301103054770003,0x8001008000200000010200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xbc7e3827f029,0x8001002000200000040200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xbc7e3827f005,0x8001002000200000010200200000080⟩,
.invariance ⟨3,4,0x800208100,0x60c181060c100,0x414001010001021012000021,0x4001010000200008000200200000080⟩,
.invariance ⟨5,17,0x204020c0820400100,0x7870a3c78306140870a0c0870a0c08e0c1080e1a3058a12201000c10100,0x21aa90d5486aa435521aaffffc86ab7f7721aa834cefeef7f770699834cc1a677d37be9b8d09efa6e3427ffffffffefa6f7f77be9bfd0ffe87f741ffa1fdd07c000000000000000000001d0ffe87ff41ffa1ffd07f,0x4001010000200000080200200000080⟩,
.invariance ⟨4,4,0x8101000c000,0x60c081060c100,0x5541000030001000320031000000321,0x4001000080200008000200200000080⟩,
.invariance ⟨4,4,0x6041810400100,0x81000c100,0xc000f00f0c0d0d0fdfdb9b900000061,0x4001000080200000080200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c101060c000,0x1113303033760031,0x4001000020200008000200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c101060c000,0x103323211770031,0x4001000020200002000200200000080⟩,
.invariance ⟨5,7,0x204020c0820400100,0x81020c08302002060a10100,0x3f80ebfc075fe03af5ea03adbb60ad82fffedf5b79f3e5cf94000000001f3e5cf97,0x2001010000200000080200200000080⟩,
.invariance ⟨3,4,0x800200100,0x60c181060c100,0x505001010001030212000003,0x1001010000200008000200200000080⟩,
.invariance ⟨5,17,0x204020c0820400100,0x605183038c06300870a0c0870a0c08f08407861c3458a12201000c10100,0x40aaa055502aa815540aaffffd02abef7740aa814cfdeefef770299814cc0a67ed37f69b8909fda6e2427fffffffffda6fef77f69bfd0ffe87fe41ffa1ff907c000000000000000000001b0ffd87fec1ff61ffb07f,0x1001010000200000080200200000080⟩,
.invariance ⟨4,4,0xc101000c000,0x60c081060c100,0x451000300001000230021000000003,0x1001000080200008000200200000080⟩,
.invariance ⟨4,4,0x6041810400100,0x81000c100,0xc000f00f0c0d0d0fdfdb9b900000007,0x1001000080200000080200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c101060c000,0x1113303033760003,0x1001000020200008000200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c101060c000,0x103323211770003,0x1001000020200002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4920849a009,0x801010000200010000200200000080⟩,
.invariance ⟨5,12,0x204020c0820400100,0x102040302180880c041810e2c58a00242070a10100,0x1a70001a7fff000eb51a7000eb5eb541500041589b89b00a89b00affffff89beb589b1a71a70a51a70a500000000000000055f55f51755f517,0x801010000200000080200200000080⟩,
.invariance ⟨4,4,0x60c081060c100,0x6041810408100,0xfa010800a0001000fa001800000029,0x2000000110000200000200200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x1204203800803a00a000013,0x2000000108000200000200200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810208100,0x3e1c6012088038008000013,0x2000000102000200002000200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x3f04702d008038008000013,0x2000000102000200000800200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x3f04203800803a00a000013,0x2000000102000200000200200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x704203f00a038008000013,0x2000000100800200000800200200000080⟩,
.invariance ⟨2,3,0x204000,0x800200100,0xfc7438e2801b,0x1000000110000200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x800200100,0xbc7438e2801b,0x1000000110000200018000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xfc74b8e28013,0x1000000110000200002000200200000080⟩,
.invariance ⟨2,4,0x204000,0x6041810000100,0xff0fa0f0fad800ab,0x1000000110000200000200200200000080⟩,
.invariance ⟨4,4,0x60c0810604100,0x2081810008100,0x29b0909002202900090009000000023,0x1000000108000200002000200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x241c6012008038008000013,0x1000000102000200002000200200000080⟩
]

private def group18 : List Outcome := [
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x2d1c702d008038008000013,0x1000000102000200000800200200000080⟩,
.invariance ⟨4,4,0x60c081060c100,0x6041810408100,0xf5010500a0001000fa001800000023,0x800000110000200000200200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x810208100,0x3f1c7012088038008000013,0x800000108000200002000200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x3604602d008038008000013,0x800000108000200000800200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x3604403800803a00a000013,0x800000108000200000200200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x2d04502d008038008000013,0x800000102000200000800200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x2d04503800803a00a000013,0x800000102000200000200200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x704503f00a038008000013,0x800000100800200000800200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x1204203800803a008000013,0x400000100080200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x481208209013,0x400000100040200020000200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x1204203800803d008000013,0x400000100020200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x48120820801b,0x400000100010200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x481208208013,0x400000100004200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x800200100,0xbc74bbe2801b,0x200000110000200018000200200000080⟩,
.invariance ⟨2,4,0x204000,0x6041810000100,0xff0faafafad800ab,0x200000110000200000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x201489208013,0x100000110000200002000200200000080⟩,
.invariance ⟨3,4,0x820200100,0x2081810408100,0x990001222101292898000203,0x100000110000200000200200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x120421ff00803a01a000013,0x100000100080200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x481048209013,0x100000100040200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x5c71ffe2d013,0x100000100020200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xbc71ffe2d013,0x100000100020200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x5c71ffe28013,0x100010100008200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xbc71ffe28013,0x100010100008200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x481048208013,0x100000100004200020000200200000080⟩,
.invariance ⟨4,4,0x6041810400100,0x604181060c100,0x20200100445410105000031200002021,0x80000100040200020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xbc727de2d013,0x80000100040200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x24124920801b,0x80000100010200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x241249208013,0x80000100004200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x601488608013,0x40000110000200002000200200000080⟩,
.invariance ⟨2,4,0x204000,0x6081810008100,0xba09a090ba9800ab,0x40000110000200000200200200000080⟩,
.invariance ⟨4,3,0x60c0810604100,0x1010208100,0x1a0c2012088018008000013,0x40000108000200002000200200000080⟩,
.invariance ⟨4,4,0x8101000c000,0x60c081060c100,0x5541000032001000300033000000201,0x40000102000200002000200200000080⟩
]

private def group19 : List Outcome := [
.invariance ⟨4,3,0x8101000c000,0x1020208100,0x49200048040040048000081,0x40000102000200000800200200000080⟩,
.invariance ⟨4,4,0x2081810008100,0x6041810408100,0xf00a000100a0100000f0801800002003,0x20000110000200020000200200000080⟩,
.invariance ⟨2,4,0x204000,0x6041810008100,0xfa09aa98fa9800ab,0x20000110000200002000200200000080⟩,
.invariance ⟨2,4,0x204000,0x6041810008100,0xfa09a090fa9800ab,0x20000110000200000200200200000080⟩,
.invariance ⟨3,2,0x820200100,0x204000,0x8c3ff332e023,0x20000100400200020000200200000080⟩,
.invariance ⟨3,2,0x820200100,0x204000,0x4c3ff332e023,0x20000100400200008000200200000080⟩,
.invariance ⟨4,4,0x60c081060c100,0x60c101060c000,0x1110301001000300032003200000073,0x20000100010200008000200200000080⟩,
.invariance ⟨3,4,0x820200100,0x60c101060c000,0x101003110300030232000707,0x20000100004200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1010208100,0x6c149a6c9013,0x10000110000200002000200200000080⟩,
.invariance ⟨4,2,0x41810400100,0x204000,0x3b30cceef30f0089,0x10000108000200002000200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x810208100,0x121c702d02d1ff008000013,0x10000108000200000800200200000080⟩,
.invariance ⟨4,2,0x41810400100,0x204000,0x3730cceec33f0089,0x10000102000200002000200200000080⟩,
.invariance ⟨4,3,0x20c081040c100,0x1020208100,0x249041209208008249000413,0x10000102000200000800200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x800200100,0x1fb1c201003803d02d000019,0x8000110000200020000200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x800200100,0x1ed1c101003803902900001b,0x8000110000200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xfc74baf6d013,0x8000110000200002000200200000080⟩,
.invariance ⟨3,4,0x1020200000,0x6041810000100,0xf0f00faa0ff0ffaddd000aab,0x8000110000200000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x800200100,0xbc7438f6d01b,0x8000110000200000080200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x10200100,0x1db1c302003803d02d00001b,0x8000100010200020000200200000080⟩,
.invariance ⟨4,3,0x60c081060c100,0x10200100,0x1ed1c102003803902900001b,0x8000100010200008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0x1c71ffe2d013,0x8000100008200001000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x20148820801b,0x4000110000200002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4148820801b,0x4000104000200002000200200000080⟩,
.invariance ⟨4,4,0x8101000c000,0x204081000c100,0x444f00002200d000f00009000000221,0x4000102000200002000200200000080⟩,
.invariance ⟨4,3,0x8101000c000,0x1020208100,0x492000480400400480000c9,0x4000102000200000800200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x5501301032320033,0x4000102000200000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4149a24801b,0x4000100040200002000200200000080⟩,
.invariance ⟨2,4,0x204000,0x6041810604100,0x505223254540033,0x4000100020200002000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x41488208013,0x1000104000200002000200200000080⟩,
.invariance ⟨4,3,0x208101000c000,0x1020208100,0x249200048040040008000281,0x1000102000200000800200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x5501301032320023,0x1000102000200000200200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4149a248013,0x1000100040200002000200200000080⟩
]

private def group20 : List Outcome := [
.invariance ⟨2,4,0x204000,0x6041810604100,0x505223254540023,0x1000100020200002000200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xdcee3f05,0x200040000040800000008200200000080⟩,
.invariance ⟨5,2,0x20406080840608080,0x204080,0x5457014150040500001,0x80040000020800000008200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x1020208100,0x241000240491200049,0x20040000002800001000200200000080⟩,
.invariance ⟨13,3,0x30b161860b161c4870a0c08b16285080e185080c10100,0x1020204080,0xc060073ce00123e2301c000000003000400d374000c00c3fc00000001200000000000000000005,0x8040000008800002000200200000080⟩,
.invariance ⟨19,3,0x88e1644611181c70b1c30587101c2830244911143840c203c40d0e284840c10100,0x810208100,0x400072081cf3f803920727f3fffc0000000000000e0a000a510a9aff2390401c0e08ff9048200201041340000000000000000000000000003,0x8040000008800000800200200000080⟩,
.invariance ⟨8,2,0xa182060a101010a18384040c080,0x204080,0x4150157000104154045404500000001,0x8040000002800000800200200000080⟩,
.invariance ⟨9,3,0x3870a1c285060c0860e203040808100,0x810204100,0x3fec0efbfc0e3fff8145b6f0000006000036c0000000000005,0x20004008000800000008200200000080⟩,
.invariance ⟨12,3,0x142448614243050c0c181142c48a0e203840a10100,0x810204100,0x71ff0c07dbeffa07a3dfffa05a2db6f0000000030000030db000000000000000005,0x20004002000800000008200200000080⟩,
.invariance ⟨4,3,0x6081810408100,0x810204100,0x38620e3aa02002018000005,0x20004000800800000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xeedd3f05,0x10004008000800000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xccfe3f05,0x10004000800800000008200200000080⟩,
.invariance ⟨6,2,0xa0c28304042830808080,0x204080,0x5055115115001005000001,0x8004002000800000008200200000080⟩,
.invariance ⟨8,3,0x8102040e1418102100840c10100,0x1020204080,0x6e70000000f80000200000038000028000000000005,0x2004000080800020000200200000080⟩,
.invariance ⟨10,3,0x6102040810385060410412200840c10100,0x820204080,0x80e7000000003a000000200e40000c28000028000000000000005,0x2004000080800008000200200000080⟩,
.invariance ⟨7,3,0x3060c1420302180860810100,0x1020204080,0x30e400001c80002400001c0000a00000000005,0x2004000020800020000200200000080⟩,
.invariance ⟨16,3,0xc2820c1e2018c14305080c101810c2820c142020e1a2c4870a08100,0x810208100,0x70000013f9249e08048001e49a08048001a49048e38208079048618208059000000000000000000000003,0x2004000020800008000200200000080⟩,
.invariance ⟨12,3,0x12144870a0c4870a0c181101048716284060808100,0x810204100,0x36c003befb1c0fc0fff140b40b6d0071c71ff0030c30db000000000000000005,0x804000080800020000200200000080⟩,
.invariance ⟨2,3,0x204000,0x1020208100,0x4824849a009,0x804000080800010000200200000080⟩,
.invariance ⟨14,3,0x182860a101820a101830406046090a2868c16243850a08100,0x810204100,0xc36001dbedba281e81fdf68a05a05b6d000e38e07fc00186180db000000000000000000005,0x804000020800020000200200000080⟩,
.invariance ⟨9,2,0x406080840608080880c101070a0c080,0x204080,0x40155050541415111144445000000001,0x804000020800008000200200000080⟩,
.invariance ⟨9,3,0x4080e183070a0c0880c201020c10100,0x1020204080,0x7c07c38039040000c3004030c0381c7000240240000000024065,0x200000400008800020000200200000080⟩,
.invariance ⟨16,3,0x163c30b161c60516305090e141811c2c406162c70d142c1080c10100,0x1020204080,0x3000003e03e206008e00c400000060001860400440013040401f0181e30000000008008000000000000020001024065,0x200000400008800008000200200000080⟩,
.invariance ⟨2,3,0x204000,0x810200100,0xeba1fff6c013,0x100000400008800020000200200000080⟩,
.invariance ⟨2,4,0x204000,0x6041810600100,0x7272057755540011,0x100000400002800020000200200000080⟩,
.invariance ⟨12,3,0x121830a0e1018704101010c205830e244060a0c000,0x1020208100,0x4800820924100904920100800140305024b001040249048008209000000000291018413,0x80000400008800008000200200000080⟩,
.invariance ⟨9,2,0x307081838208080840e201060a0c080,0x204080,0x411140515000041055041550445000000001,0x80000400002800008000200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x5510301033320031,0x4000402000800000200200200000080⟩,
.invariance ⟨4,3,0x6081810408100,0x810208100,0x220003820063a00a000003,0x2000408000800000200200200000080⟩,
.invariance ⟨8,4,0xe143860a101810e1c2020810100,0x204081000c100,0xf0f00f0fd0d000f00ff0d00d0d00f00f0f00009029b0000000000020123,0x2000402000800002000200200000080⟩,
.invariance ⟨12,3,0x61030a0e284070410101162830b0e241860a0c000,0x1020208100,0x20800800120900904920104020904000824904000824961105020b00000000060a088413,0x2000402000800000800200200000080⟩,
.invariance ⟨4,3,0x6081810408100,0x810208100,0x520003820063a00a000003,0x2000402000800000200200200000080⟩
]

private def group21 : List Outcome := [
.invariance ⟨2,4,0x204000,0x60c081060c100,0x5510301033320003,0x1000402000800000200200200000080⟩,
.invariance ⟨3,3,0x1020200000,0x1020208100,0x9012440241200049,0x800404000800002000200200000080⟩,
.invariance ⟨2,4,0x204000,0x60c081060c100,0x311301033330055,0x800404000800000200200200000080⟩,
.invariance ⟨8,2,0x81838604101010e18205040c080,0x204080,0x10115044540554055044500000001,0x800402000800000800200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x77ee3f05,0x200040000040200000008200200000080⟩,
.invariance ⟨4,3,0x60c1010604000,0x810200100,0x3f17f0021d21f8028000013,0x200040000008200010000200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3fa38002e02038028000003,0x20004000000820000a000200200000080⟩,
.invariance ⟨11,4,0x18306103030c18203022850804244070a08100,0x4081810408100,0x333f0300f1f001f01f1fff10100000103aabfabfbfff2233031133b11110100111000000000002222020022b,0x200040000008200001000200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3fa38007e02038028000003,0x200040000008200000800200200000080⟩,
.invariance ⟨4,3,0x60c1010004080,0x1010208100,0x1b0480024da61b009000403,0x200040000008200000100200200000080⟩,
.invariance ⟨4,4,0x60c1010608100,0x204081000c100,0xdf0fd000020dd200fd009900000003,0x200040000008200000080200200000080⟩,
.invariance ⟨4,3,0x60c1010604000,0x810200100,0x3f17f0051ed1f8028000013,0x80040000008200010000200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3da3d007e01038028000003,0x80040000008200002000200200000080⟩,
.invariance ⟨4,3,0x60c1010604000,0x1020208100,0x9049001049048008000013,0x80040000008200001000200200000080⟩,
.invariance ⟨4,3,0x4081810208100,0x810200100,0x3da3d005e01038028000003,0x80040000008200008800200200000080⟩,
.invariance ⟨4,3,0x60c1010604000,0x1010208100,0x90490010490db009000013,0x80040000008200000100200200000080⟩,
.invariance ⟨4,3,0x60c1010608080,0x1020208100,0x9049001049009009000003,0x80040000008200000080200200000080⟩,
.invariance ⟨8,3,0x41c1040a101010c18186060c000,0x1020208100,0x20820f00827f0402010186ff2492492082090000004d2693,0x80040000008200000010200200000080⟩,
.invariance ⟨4,4,0x4081810608100,0x60c181060c100,0x101000100010000002003000000005,0x20040004000200000008200200000080⟩,
.invariance ⟨4,3,0x60c1010004000,0x810200100,0x3f178ffa5d20024ba000825,0x20040000800200000008200200000080⟩,
.invariance ⟨4,4,0x4081810608100,0x60c081060c100,0x101000300010000002003000000005,0x20040000400200000008200200000080⟩,
.invariance ⟨4,4,0x4081810608100,0x204081000c100,0xd0f009f0d9d001000200b000000005,0x20040000200200000008200200000080⟩,
.invariance ⟨4,4,0x60c1010004080,0x6041810600100,0x550570555007700002227700004005,0x20040000040200000008200200000080⟩,
.invariance ⟨8,4,0x2042810a041810e1c3040410100,0x60c1810600100,0x110101110007575f111111112227777772070207776767770000000055454545,0x20040000004200000008200200000080⟩,
.invariance ⟨4,3,0x208101000c000,0x1020208100,0x48240201040492048000249,0x20040000002200001000200200000080⟩,
.invariance ⟨9,3,0x860614305020c0880e203840808100,0x1020208100,0x2080092000493c924924a0812db2402082d34936c0000001201041,0x8040000004200000200200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33ce3f05,0x1638811440040200000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0xb3cc3f05,0x10001448000200000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x73cc3f05,0x10001442000200000008200200000080⟩,
.invariance ⟨2,2,0x204000,0x204000,0x33ee3f05,0x10011440800200000008200200000080⟩,
.halting 0xffff80013fffe8000ffff8200200000080 49152 5,
.halting 0xffff80007fffe8000ffff8200200000080 16384 5
]

private def group22 : List Outcome := [
.halting 0x410003fffe8000ffff8200200000080 62208 6,
.halting 0x210003fffe8000ffff8200200000080 61952 6,
.halting 0x110003fffe8000ffff8200200000080 61696 6,
.halting 0x90003fffe8000ffff8200200000080 61440 6,
.halting 0x410003fffe2000ffff8200200000080 45824 7,
.halting 0x210003fffe2000ffff8200200000080 45568 7,
.halting 0x110003fffe2000ffff8200200000080 45312 7,
.halting 0x90003fffe2000ffff8200200000080 45056 7,
.halting 0x204003fffe8000ffff8200200000080 29184 6,
.halting 0x84003fffe8000ffff8200200000080 28672 6,
.halting 0x204003fffe2000ffff8200200000080 12800 7,
.halting 0x84003fffe2000ffff8200200000080 12288 7,
.halting 0xffff8100000108000ffff8200200000080 57392 6,
.halting 0xffff8100000088000ffff8200200000080 57376 6,
.halting 0xffff8100000048000ffff8200200000080 57360 6,
.halting 0xffff8100000028000ffff8200200000080 57344 6,
.halting 0xffff8010000082000ffff8200200000080 36896 7,
.halting 0xffff8010000022000ffff8200200000080 36864 7,
.halting 0xffff8040000088000ffff8200200000080 24608 6,
.halting 0xffff8040000028000ffff8200200000080 24576 6,
.halting 0xffff80103fffe800000040200200000080 53251 6,
.halting 0xffff80103fffe800000020200200000080 53250 6,
.halting 0xffff80103fffe800000010200200000080 53249 6,
.halting 0xffff80103fffe800000008200200000080 53248 6,
.halting 0xffff80013fffe200040000200200000080 32783 8,
.halting 0xffff80013fffe200000020200200000080 32770 7,
.halting 0xffff80013fffe200000008200200000080 32768 7,
.halting 0xffff80043fffe800000020200200000080 20482 6,
.halting 0xffff80043fffe800000008200200000080 20480 6,
.halting 0x4001000000088000ffff8200200000080 64288 7,
.halting 0x4001000000028000ffff8200200000080 64256 7,
.halting 0x2001000000108000ffff8200200000080 64048 7
]

private def group23 : List Outcome := [
.halting 0x2001000000088000ffff8200200000080 64032 7,
.halting 0x2001000000048000ffff8200200000080 64016 7,
.halting 0x2001000000028000ffff8200200000080 64000 7,
.halting 0x801000000088000ffff8200200000080 63520 7,
.halting 0x801000000028000ffff8200200000080 63488 7,
.halting 0x40100080008000ffff8200200000080 58336 7,
.halting 0x40100008008000ffff8200200000080 58272 10,
.halting 0x20100100008000ffff8200200000080 58096 7,
.halting 0x20100080008000ffff8200200000080 58080 7,
.halting 0x20100020008000ffff8200200000080 58048 7,
.halting 0x20100008008000ffff8200200000080 58016 10,
.halting 0x10100080008000ffff8200200000080 57824 7,
.halting 0x10100008008000ffff8200200000080 57760 10,
.halting 0x8100100008000ffff8200200000080 57584 7,
.halting 0x8100080008000ffff8200200000080 57568 7,
.halting 0x8100020008000ffff8200200000080 57536 7,
.halting 0x8100008008000ffff8200200000080 57504 10,
.halting 0x4001000000102000ffff8200200000080 47920 8,
.halting 0x4001000000082000ffff8200200000080 47904 8,
.halting 0x4001000000042000ffff8200200000080 47888 8,
.halting 0x4001000000022000ffff8200200000080 47872 8,
.halting 0x2001000000102000ffff8200200000080 47664 8,
.halting 0x2001000000042000ffff8200200000080 47632 8,
.halting 0x2001000000022000ffff8200200000080 47616 11,
.halting 0x1001000000102000ffff8200200000080 47408 8,
.halting 0x1001000000042000ffff8200200000080 47376 8,
.halting 0x1001000000022000ffff8200200000080 47360 11,
.halting 0x40000100000102000ffff8200200000080 44848 9,
.halting 0x40000100000042000ffff8200200000080 44816 9,
.halting 0x40000100000022000ffff8200200000080 44800 12,
.halting 0x20000100000102000ffff8200200000080 44592 9,
.halting 0x20000100000082000ffff8200200000080 44576 9
]

private def group24 : List Outcome := [
.halting 0x20000100000042000ffff8200200000080 44560 9,
.halting 0x20000100000022000ffff8200200000080 44544 9,
.halting 0x8000100000102000ffff8200200000080 44080 9,
.halting 0x8000100000082000ffff8200200000080 44064 9,
.halting 0x8000100000042000ffff8200200000080 44048 9,
.halting 0x8000100000022000ffff8200200000080 44032 9,
.halting 0x200100000082000ffff8200200000080 42528 9,
.halting 0x200100000022000ffff8200200000080 42496 9,
.halting 0x40010080002000ffff8200200000080 37856 8,
.halting 0x40010008002000ffff8200200000080 37792 12,
.halting 0x20010080002000ffff8200200000080 37600 8,
.halting 0x20010020002000ffff8200200000080 37568 8,
.halting 0x10010080002000ffff8200200000080 37344 8,
.halting 0x10010008002000ffff8200200000080 37280 12,
.halting 0x8010080002000ffff8200200000080 37088 8,
.halting 0x8010020002000ffff8200200000080 37056 8,
.halting 0x2000400000108000ffff8200200000080 31280 7,
.halting 0x2000400000088000ffff8200200000080 31264 7,
.halting 0x2000400000048000ffff8200200000080 31248 7,
.halting 0x2000400000028000ffff8200200000080 31232 7,
.halting 0x800400000088000ffff8200200000080 30752 7,
.halting 0x800400000028000ffff8200200000080 30720 7,
.halting 0x40040080008000ffff8200200000080 25568 7,
.halting 0x40040008008000ffff8200200000080 25504 10,
.halting 0x20040080008000ffff8200200000080 25312 7,
.halting 0x20040020008000ffff8200200000080 25280 7,
.halting 0x20040008008000ffff8200200000080 25248 10,
.halting 0x10040080008000ffff8200200000080 25056 7,
.halting 0x10040008008000ffff8200200000080 24992 10,
.halting 0x8040080008000ffff8200200000080 24800 7,
.halting 0x8040020008000ffff8200200000080 24768 7,
.halting 0x8040008008000ffff8200200000080 24736 10
]

private def group25 : List Outcome := [
.halting 0x2000400000102000ffff8200200000080 14896 8,
.halting 0x2000400000042000ffff8200200000080 14864 8,
.halting 0x2000400000022000ffff8200200000080 14848 11,
.halting 0x4010003fffe800000020200200000080 63234 7,
.halting 0x4010003fffe800000008200200000080 63232 7,
.halting 0x2010003fffe800000040200200000080 62979 7,
.halting 0x2010003fffe800000020200200000080 62978 7,
.halting 0x2010003fffe800000010200200000080 62977 7,
.halting 0x2010003fffe800000008200200000080 62976 7,
.halting 0x1010003fffe800000020200200000080 62722 9,
.halting 0x810003fffe800000020200200000080 62466 7,
.halting 0x810003fffe800000008200200000080 62464 7,
.halting 0x400103fffe800020000200200000080 54030 7,
.halting 0x200103fffe800040000200200000080 53775 7,
.halting 0x200103fffe800020000200200000080 53774 7,
.halting 0x200103fffe800008000200200000080 53772 7,
.halting 0x100103fffe800020000200200000080 53518 7,
.halting 0x80103fffe800040000200200000080 53263 7,
.halting 0x80103fffe800020000200200000080 53262 7,
.halting 0x80103fffe800008000200200000080 53260 7,
.halting 0x4010003fffe200000040200200000080 46851 8,
.halting 0x4010003fffe200000020200200000080 46850 8,
.halting 0x4010003fffe200000010200200000080 46849 8,
.halting 0x4010003fffe200000008200200000080 46848 8,
.halting 0x2010003fffe200000040200200000080 46595 8,
.halting 0x2010003fffe200000020200200000080 46594 10,
.halting 0x2010003fffe200000010200200000080 46593 8,
.halting 0x1010003fffe200000040200200000080 46339 8,
.halting 0x1010003fffe200000020200200000080 46338 10,
.halting 0x1010003fffe200000010200200000080 46337 8,
.halting 0x810003fffe200000040200200000080 46083 10,
.halting 0x810003fffe200000020200200000080 46082 10
]

private def group26 : List Outcome := [
.halting 0x810003fffe200000010200200000080 46081 10,
.halting 0x810003fffe200000008200200000080 46080 21,
.halting 0x201003fffe200020000200200000080 41486 10,
.halting 0x201003fffe200008000200200000080 41484 10,
.halting 0x201003fffe200000020200200000080 41474 9,
.halting 0x201003fffe200000008200200000080 41472 9,
.halting 0x400000013fffe200020000200200000080 36622 10,
.halting 0x400000013fffe200008000200200000080 36620 9,
.halting 0x1000013fffe200020000200200000080 34062 10,
.halting 0x400013fffe200020000200200000080 33550 8,
.halting 0x200013fffe200020000200200000080 33294 8,
.halting 0x200013fffe200008000200200000080 33292 8,
.halting 0x100013fffe200020000200200000080 33038 8,
.halting 0x80013fffe200020000200200000080 32782 8,
.halting 0x80013fffe200008000200200000080 32780 8,
.halting 0x2004003fffe800000040200200000080 30211 7,
.halting 0x2004003fffe800000020200200000080 30210 7,
.halting 0x2004003fffe800000010200200000080 30209 7,
.halting 0x2004003fffe800000008200200000080 30208 7,
.halting 0x804003fffe800000020200200000080 29698 7,
.halting 0x804003fffe800000008200200000080 29696 7,
.halting 0x400043fffe800020000200200000080 21262 7,
.halting 0x200043fffe800020000200200000080 21006 7,
.halting 0x200043fffe800008000200200000080 21004 7,
.halting 0x100043fffe800020000200200000080 20750 7,
.halting 0x80043fffe800020000200200000080 20494 7,
.halting 0x80043fffe800008000200200000080 20492 7,
.halting 0x2004003fffe200000040200200000080 13827 8,
.halting 0x2004003fffe200000020200200000080 13826 10,
.halting 0x2004003fffe200000010200200000080 13825 8,
.halting 0x804003fffe200000020200200000080 13314 10,
.halting 0xffff810000100800000020200200000080 57458 7
]

private def group27 : List Outcome := [
.halting 0xffff810000100800000008200200000080 57456 7,
.halting 0xffff810000080800000040200200000080 57443 7,
.halting 0xffff810000080800000020200200000080 57442 7,
.halting 0xffff810000080800000010200200000080 57441 7,
.halting 0xffff810000080800000008200200000080 57440 7,
.halting 0xffff810000040800000020200200000080 57426 9,
.halting 0xffff810000020800000020200200000080 57410 7,
.halting 0xffff810000020800000008200200000080 57408 7,
.halting 0xffff801000010800002000200200000080 53306 7,
.halting 0xffff801000010800000200200200000080 53302 10,
.halting 0xffff801000008800004000200200000080 53291 7,
.halting 0xffff801000008800002000200200000080 53290 7,
.halting 0xffff801000008800000800200200000080 53288 7,
.halting 0xffff801000008800000200200200000080 53286 10,
.halting 0xffff801000004800002000200200000080 53274 7,
.halting 0xffff801000004800000200200200000080 53270 10,
.halting 0xffff801000002800004000200200000080 53259 7,
.halting 0xffff801000002800002000200200000080 53258 7,
.halting 0xffff801000002800000800200200000080 53256 7,
.halting 0xffff801000002800000200200200000080 53254 10,
.halting 0xffff801010000200000040200200000080 37107 9,
.halting 0xffff801010000200000020200200000080 37106 9,
.halting 0xffff801010000200000010200200000080 37105 9,
.halting 0xffff801010000200000008200200000080 37104 9,
.halting 0xffff801000080200000040200200000080 36963 8,
.halting 0xffff801000080200000020200200000080 36962 8,
.halting 0xffff801000080200000010200200000080 36961 8,
.halting 0xffff801000080200000008200200000080 36960 8,
.halting 0xffff801000020200000020200200000080 36930 8,
.halting 0xffff801000020200000008200200000080 36928 8,
.halting 0xffff800110000200000800200200000080 33016 9,
.halting 0xffff800100010200002000200200000080 32826 8
]

private def group28 : List Outcome := [
.halting 0xffff800100010200000200200200000080 32822 12,
.halting 0xffff800100008200002000200200000080 32810 8,
.halting 0xffff800100008200000800200200000080 32808 8,
.halting 0xffff800100008200000200200200000080 32806 12,
.halting 0xffff800100004200002000200200000080 32794 8,
.halting 0xffff800100004200000200200200000080 32790 12,
.halting 0xffff800100002200002000200200000080 32778 8,
.halting 0xffff800100002200000800200200000080 32776 8,
.halting 0xffff800100002200000200200200000080 32774 12,
.halting 0xffff804000080800000040200200000080 24675 7,
.halting 0xffff804000080800000020200200000080 24674 7,
.halting 0xffff804000080800000010200200000080 24673 7,
.halting 0xffff804000080800000008200200000080 24672 7,
.halting 0xffff804000020800000020200200000080 24642 7,
.halting 0xffff804000020800000008200200000080 24640 7,
.halting 0xffff800400010800002000200200000080 20538 7,
.halting 0xffff800400010800000200200200000080 20534 10,
.halting 0xffff800400008800002000200200000080 20522 7,
.halting 0xffff800400008800000800200200000080 20520 7,
.halting 0xffff800400008800000200200200000080 20518 10,
.halting 0xffff800400004800002000200200000080 20506 7,
.halting 0xffff800400004800000200200200000080 20502 10,
.halting 0xffff800400002800002000200200000080 20490 7,
.halting 0xffff800400002800000800200200000080 20488 7,
.halting 0xffff800400002800000200200200000080 20486 10,
.halting 0x400100000080800000040200200000080 64355 8,
.halting 0x400100000080800000020200200000080 64354 8,
.halting 0x400100000080800000010200200000080 64353 8,
.halting 0x400100000080800000008200200000080 64352 8,
.halting 0x400100000020800000020200200000080 64322 8,
.halting 0x400100000020800000008200200000080 64320 8,
.halting 0x200100000100800000040200200000080 64115 8
]

private def group29 : List Outcome := [
.halting 0x200100000100800000020200200000080 64114 8,
.halting 0x200100000100800000010200200000080 64113 8,
.halting 0x200100000100800000008200200000080 64112 8,
.halting 0x200100000080800000040200200000080 64099 8,
.halting 0x200100000080800000020200200000080 64098 10,
.halting 0x200100000080800000010200200000080 64097 8,
.halting 0x200100000080800000008200200000080 64096 12,
.halting 0x200100000040800000040200200000080 64083 8,
.halting 0x200100000040800000020200200000080 64082 10,
.halting 0x200100000040800000010200200000080 64081 8,
.halting 0x200100000020800000040200200000080 64067 10,
.halting 0x200100000020800000020200200000080 64066 10,
.halting 0x200100000020800000010200200000080 64065 10,
.halting 0x200100000020800000008200200000080 64064 14,
.halting 0x100100000080800000040200200000080 63843 10,
.halting 0x100100000080800000020200200000080 63842 10,
.halting 0x100100000080800000010200200000080 63841 10,
.halting 0x100100000080800000008200200000080 63840 10,
.halting 0x100100000008800002000200200000080 63786 10,
.halting 0x100100000008800000800200200000080 63784 10,
.halting 0x100100000008800000200200200000080 63782 14,
.halting 0x100100000008800000020200200000080 63778 9,
.halting 0x100100000008800000008200200000080 63776 9,
.halting 0x80100000080800000040200200000080 63587 8,
.halting 0x80100000080800000020200200000080 63586 10,
.halting 0x80100000080800000010200200000080 63585 8,
.halting 0x80100000080800000008200200000080 63584 12,
.halting 0x80100000020800000020200200000080 63554 10,
.halting 0x80100000010800002000200200000080 63546 10,
.halting 0x80100000010800000200200200000080 63542 14,
.halting 0x80100000010800000020200200000080 63538 9,
.halting 0x80100000010800000008200200000080 63536 9
]

private def group30 : List Outcome := [
.halting 0x80100000004800002000200200000080 63514 10,
.halting 0x80100000004800000200200200000080 63510 12,
.halting 0x80100000004800000020200200000080 63506 9,
.halting 0x80100000004800000008200200000080 63504 9,
.halting 0x40100000010800002000200200000080 63290 8,
.halting 0x40100000010800000200200200000080 63286 12,
.halting 0x40100000008800002000200200000080 63274 8,
.halting 0x40100000008800000800200200000080 63272 8,
.halting 0x40100000008800000200200200000080 63270 12,
.halting 0x40100000004800002000200200000080 63258 8,
.halting 0x40100000004800000200200200000080 63254 12,
.halting 0x40100000002800002000200200000080 63242 8,
.halting 0x40100000002800000800200200000080 63240 8,
.halting 0x40100000002800000200200200000080 63238 12,
.halting 0x20100000010800020000200200000080 63038 10,
.halting 0x20100000010800010000200200000080 63037 10,
.halting 0x20100000010800004000200200000080 63035 8,
.halting 0x20100000010800002000200200000080 63034 8,
.halting 0x20100000010800001000200200000080 63033 8,
.halting 0x20100000010800000200200200000080 63030 10,
.halting 0x20100000008800020000200200000080 63022 10,
.halting 0x20100000008800010000200200000080 63021 10,
.halting 0x20100000008800008000200200000080 63020 10,
.halting 0x20100000008800004000200200000080 63019 8,
.halting 0x20100000008800001000200200000080 63017 18,
.halting 0x20100000008800000200200200000080 63014 10,
.halting 0x20100000004800020000200200000080 63006 10,
.halting 0x20100000004800010000200200000080 63005 10,
.halting 0x20100000004800004000200200000080 63003 8,
.halting 0x20100000004800002000200200000080 63002 8,
.halting 0x20100000004800001000200200000080 63001 8,
.halting 0x20100000004800000200200200000080 62998 10
]

private def group31 : List Outcome := [
.halting 0x20100000002800020000200200000080 62990 10,
.halting 0x20100000002800010000200200000080 62989 10,
.halting 0x20100000002800008000200200000080 62988 10,
.halting 0x20100000002800004000200200000080 62987 8,
.halting 0x20100000002800002000200200000080 62986 11,
.halting 0x20100000002800001000200200000080 62985 11,
.halting 0x20100000002800000800200200000080 62984 14,
.halting 0x20100000002800000200200200000080 62982 10,
.halting 0x10100000008800000200200200000080 62758 9,
.halting 0x10100000002800000200200200000080 62726 9,
.halting 0x8100000010800002000200200000080 62522 8,
.halting 0x8100000010800000200200200000080 62518 10,
.halting 0x8100000008800000400200200000080 62503 9,
.halting 0x8100000008800000200200200000080 62502 10,
.halting 0x8100000008800000100200200000080 62501 9,
.halting 0x8100000004800002000200200000080 62490 8,
.halting 0x8100000004800000200200200000080 62486 10,
.halting 0x8100000002800002000200200000080 62474 11,
.halting 0x8100000002800000400200200000080 62471 9,
.halting 0x8100000002800000200200200000080 62470 10,
.halting 0x8100000002800000100200200000080 62469 9,
.halting 0x40010008000800000040200200000080 59363 8,
.halting 0x40010008000800000020200200000080 59362 8,
.halting 0x40010008000800000010200200000080 59361 8,
.halting 0x40010008000800000008200200000080 59360 8,
.halting 0x40010000800800000040200200000080 59299 11,
.halting 0x40010000800800000020200200000080 59298 11,
.halting 0x40010000800800000010200200000080 59297 11,
.halting 0x40010000800800000008200200000080 59296 11,
.halting 0x20010010000800000040200200000080 59123 8,
.halting 0x20010010000800000020200200000080 59122 8,
.halting 0x20010010000800000010200200000080 59121 8
]

private def group32 : List Outcome := [
.halting 0x20010010000800000008200200000080 59120 8,
.halting 0x20010008000800000040200200000080 59107 8,
.halting 0x20010008000800000020200200000080 59106 10,
.halting 0x20010008000800000010200200000080 59105 8,
.halting 0x20010004000800000040200200000080 59091 13,
.halting 0x20010004000800000020200200000080 59090 13,
.halting 0x20010004000800000010200200000080 59089 13,
.halting 0x20010004000800000008200200000080 59088 13,
.halting 0x20010002000800000040200200000080 59075 8,
.halting 0x20010002000800000020200200000080 59074 10,
.halting 0x20010002000800000010200200000080 59073 8,
.halting 0x20010000800800000040200200000080 59043 11,
.halting 0x20010000800800000020200200000080 59042 13,
.halting 0x20010000800800000010200200000080 59041 11,
.halting 0x10010008000800000040200200000080 58851 8,
.halting 0x10010008000800000020200200000080 58850 10,
.halting 0x10010008000800000010200200000080 58849 8,
.halting 0x10010000800800000040200200000080 58787 11,
.halting 0x10010000800800000020200200000080 58786 13,
.halting 0x10010000800800000010200200000080 58785 11,
.halting 0x8010010000800000020200200000080 58610 8,
.halting 0x8010010000800000008200200000080 58608 8,
.halting 0x8010008000800000040200200000080 58595 10,
.halting 0x8010008000800000020200200000080 58594 10,
.halting 0x8010008000800000010200200000080 58593 10,
.halting 0x8010008000800000008200200000080 58592 13,
.halting 0x8010002000800000020200200000080 58562 10,
.halting 0x8010000800800000040200200000080 58531 13,
.halting 0x8010000800800000020200200000080 58530 13,
.halting 0x8010000800800000010200200000080 58529 13,
.halting 0x8010000800800000008200200000080 58528 16,
.halting 0x4010002000800020000200200000080 58318 10
]

private def group33 : List Outcome := [
.halting 0x4010002000800000020200200000080 58306 9,
.halting 0x4010002000800000008200200000080 58304 9,
.halting 0x4010000100800020000200200000080 58238 8,
.halting 0x4010000080800040000200200000080 58223 8,
.halting 0x4010000080800020000200200000080 58222 8,
.halting 0x4010000080800010000200200000080 58221 8,
.halting 0x4010000080800002000200200000080 58218 13,
.halting 0x4010000080800000080200200000080 58212 16,
.halting 0x4010000040800020000200200000080 58206 16,
.halting 0x4010000020800040000200200000080 58191 15,
.halting 0x4010000020800020000200200000080 58190 8,
.halting 0x4010000020800010000200200000080 58189 10,
.halting 0x2010004000800020000200200000080 58078 10,
.halting 0x2010004000800010000200200000080 58077 12,
.halting 0x2010004000800008000200200000080 58076 10,
.halting 0x2010004000800000800200200000080 58072 13,
.halting 0x2010004000800000020200200000080 58066 9,
.halting 0x2010004000800000008200200000080 58064 9,
.halting 0x2010000100800020000200200000080 57982 8,
.halting 0x2010000100800010000200200000080 57981 10,
.halting 0x2010000100800008000200200000080 57980 8,
.halting 0x2010000080800040000200200000080 57967 8,
.halting 0x2010000080800010000200200000080 57965 16,
.halting 0x2010000080800002000200200000080 57962 13,
.halting 0x2010000080800000080200200000080 57956 16,
.halting 0x2010000040800020000200200000080 57950 16,
.halting 0x2010000040800010000200200000080 57949 10,
.halting 0x2010000040800008000200200000080 57948 16,
.halting 0x2010000040800002000200200000080 57946 9,
.halting 0x2010000020800040000200200000080 57935 15,
.halting 0x2010000020800010000200200000080 57933 10,
.halting 0x2010000020800004000200200000080 57931 9
]

private def group34 : List Outcome := [
.halting 0x2010000020800002000200200000080 57930 11,
.halting 0x2010000020800001000200200000080 57929 9,
.halting 0x2010000020800000800200200000080 57928 19,
.halting 0x1010002000800020000200200000080 57806 10,
.halting 0x1010002000800000020200200000080 57794 9,
.halting 0x1010002000800000008200200000080 57792 9,
.halting 0x1010000100800020000200200000080 57726 8,
.halting 0x1010000080800040000200200000080 57711 8,
.halting 0x1010000080800020000200200000080 57710 8,
.halting 0x1010000080800010000200200000080 57709 8,
.halting 0x1010000080800002000200200000080 57706 13,
.halting 0x1010000080800000080200200000080 57700 16,
.halting 0x1010000040800020000200200000080 57694 16,
.halting 0x1010000020800040000200200000080 57679 15,
.halting 0x1010000020800020000200200000080 57678 8,
.halting 0x1010000020800010000200200000080 57677 10,
.halting 0x810000100800020000200200000080 57470 8,
.halting 0x810000100800010000200200000080 57469 10,
.halting 0x810000100800008000200200000080 57468 8,
.halting 0x810000080800040000200200000080 57455 8,
.halting 0x810000080800008000200200000080 57452 12,
.halting 0x810000080800002000200200000080 57450 13,
.halting 0x810000080800000080200200000080 57444 16,
.halting 0x810000040800020000200200000080 57438 16,
.halting 0x810000040800010000200200000080 57437 10,
.halting 0x810000040800008000200200000080 57436 16,
.halting 0x810000040800002000200200000080 57434 9,
.halting 0x810000020800040000200200000080 57423 15,
.halting 0x810000020800010000200200000080 57421 10,
.halting 0x810000020800004000200200000080 57419 9,
.halting 0x810000020800002000200200000080 57418 11,
.halting 0x810000020800001000200200000080 57417 9
]

private def group35 : List Outcome := [
.halting 0x810000020800000800200200000080 57416 19,
.halting 0x4000001000008800008000200200000080 57132 15,
.halting 0x4000001000002800008000200200000080 57100 15,
.halting 0x2000001000010800040000200200000080 56895 13,
.halting 0x2000001000010800020000200200000080 56894 11,
.halting 0x2000001000010800010000200200000080 56893 16,
.halting 0x2000001000010800008000200200000080 56892 11,
.halting 0x2000001000008800040000200200000080 56879 13,
.halting 0x2000001000008800020000200200000080 56878 11,
.halting 0x2000001000008800010000200200000080 56877 16,
.halting 0x2000001000008800008000200200000080 56876 11,
.halting 0x2000001000004800040000200200000080 56863 13,
.halting 0x2000001000004800020000200200000080 56862 11,
.halting 0x2000001000004800010000200200000080 56861 16,
.halting 0x2000001000004800008000200200000080 56860 11,
.halting 0x2000001000002800040000200200000080 56847 13,
.halting 0x2000001000002800020000200200000080 56846 11,
.halting 0x2000001000002800010000200200000080 56845 16,
.halting 0x2000001000002800008000200200000080 56844 11,
.halting 0x1000001000010800008000200200000080 56636 10,
.halting 0x1000001000008800040000200200000080 56623 10,
.halting 0x1000001000008800020000200200000080 56622 12,
.halting 0x1000001000008800010000200200000080 56621 10,
.halting 0x1000001000008800008000200200000080 56620 10,
.halting 0x1000001000004800008000200200000080 56604 10,
.halting 0x1000001000002800040000200200000080 56591 10,
.halting 0x1000001000002800020000200200000080 56590 12,
.halting 0x1000001000002800010000200200000080 56589 10,
.halting 0x1000001000002800008000200200000080 56588 10,
.halting 0x800001000010800020000200200000080 56382 14,
.halting 0x800001000008800040000200200000080 56367 13,
.halting 0x800001000008800020000200200000080 56366 11
]

private def group36 : List Outcome := [
.halting 0x800001000008800010000200200000080 56365 16,
.halting 0x800001000008800008000200200000080 56364 11,
.halting 0x800001000004800020000200200000080 56350 14,
.halting 0x800001000002800040000200200000080 56335 13,
.halting 0x800001000002800020000200200000080 56334 11,
.halting 0x800001000002800010000200200000080 56333 16,
.halting 0x800001000002800008000200200000080 56332 11,
.halting 0x400001000010800020000200200000080 56126 8,
.halting 0x400001000008800020000200200000080 56110 8,
.halting 0x400001000004800020000200200000080 56094 8,
.halting 0x400001000002800020000200200000080 56078 8,
.halting 0x200001000010800040000200200000080 55871 8,
.halting 0x200001000010800020000200200000080 55870 8,
.halting 0x200001000010800010000200200000080 55869 10,
.halting 0x200001000010800008000200200000080 55868 8,
.halting 0x200001000008800040000200200000080 55855 8,
.halting 0x200001000008800010000200200000080 55853 10,
.halting 0x200001000004800040000200200000080 55839 8,
.halting 0x200001000004800020000200200000080 55838 8,
.halting 0x200001000004800010000200200000080 55837 10,
.halting 0x200001000004800008000200200000080 55836 8,
.halting 0x200001000002800040000200200000080 55823 8,
.halting 0x200001000002800020000200200000080 55822 11,
.halting 0x200001000002800010000200200000080 55821 10,
.halting 0x200001000002800008000200200000080 55820 11,
.halting 0x100001000010800020000200200000080 55614 8,
.halting 0x100001000008800008000200200000080 55596 19,
.halting 0x100001000004800020000200200000080 55582 8,
.halting 0x100001000002800020000200200000080 55566 11,
.halting 0x100001000002800008000200200000080 55564 19,
.halting 0x80001000008800040000200200000080 55343 8,
.halting 0x80001000008800020000200200000080 55342 17
]

private def group37 : List Outcome := [
.halting 0x80001000008800008000200200000080 55340 17,
.halting 0x80001000004800020000200200000080 55326 17,
.halting 0x80001000002800040000200200000080 55311 8,
.halting 0x80001000002800020000200200000080 55310 13,
.halting 0x40001000008800008000200200000080 55084 9,
.halting 0x40001000002800008000200200000080 55052 9,
.halting 0x20001000010800020000200200000080 54846 11,
.halting 0x20001000008800020000200200000080 54830 11,
.halting 0x20001000008800010000200200000080 54829 9,
.halting 0x20001000008800008000200200000080 54828 11,
.halting 0x20001000004800020000200200000080 54814 11,
.halting 0x20001000002800020000200200000080 54798 11,
.halting 0x20001000002800010000200200000080 54797 9,
.halting 0x20001000002800008000200200000080 54796 11,
.halting 0x10001000010800020000200200000080 54590 13,
.halting 0x10001000008800020000200200000080 54574 13,
.halting 0x10001000008800008000200200000080 54572 9,
.halting 0x10001000004800020000200200000080 54558 13,
.halting 0x10001000002800020000200200000080 54542 13,
.halting 0x10001000002800008000200200000080 54540 9,
.halting 0x8001000010800020000200200000080 54334 11,
.halting 0x8001000008800020000200200000080 54318 11,
.halting 0x8001000008800008000200200000080 54316 11,
.halting 0x8001000004800020000200200000080 54302 11,
.halting 0x8001000002800020000200200000080 54286 11,
.halting 0x8001000002800008000200200000080 54284 11,
.halting 0x4001010000800002000200200000080 54266 8,
.halting 0x4001010000800000200200200000080 54262 11,
.halting 0x4001008000800004000200200000080 54251 8,
.halting 0x4001008000800002000200200000080 54250 8,
.halting 0x4001008000800001000200200000080 54249 17,
.halting 0x4001008000800000800200200000080 54248 8
]

private def group38 : List Outcome := [
.halting 0x4001008000800000200200200000080 54246 11,
.halting 0x4001004000800002000200200000080 54234 8,
.halting 0x4001004000800000200200200000080 54230 11,
.halting 0x4001000800800004000200200000080 54187 12,
.halting 0x4001000800800002000200200000080 54186 10,
.halting 0x4001000800800000800200200000080 54184 10,
.halting 0x4001000800800000200200200000080 54182 13,
.halting 0x4001000400800002000200200000080 54170 14,
.halting 0x4001000200800002000200200000080 54154 13,
.halting 0x4001000080800002000200200000080 54122 10,
.halting 0x4001000040800002000200200000080 54106 10,
.halting 0x2001010000800002000200200000080 54010 8,
.halting 0x2001010000800000200200200000080 54006 11,
.halting 0x2001008000800010000200200000080 53997 13,
.halting 0x2001008000800004000200200000080 53995 8,
.halting 0x2001002000800010000200200000080 53965 13,
.halting 0x2001002000800004000200200000080 53963 8,
.halting 0x2001002000800001000200200000080 53961 27,
.halting 0x2001001000800000800200200000080 53944 9,
.halting 0x2001000800800010000200200000080 53933 18,
.halting 0x2001000800800004000200200000080 53931 12,
.halting 0x2001000800800002000200200000080 53930 10,
.halting 0x2001000800800001000200200000080 53929 9,
.halting 0x2001000800800000800200200000080 53928 10,
.halting 0x2001000800800000200200200000080 53926 13,
.halting 0x2001000400800002000200200000080 53914 14,
.halting 0x2001000400800000800200200000080 53912 9,
.halting 0x2001000200800002000200200000080 53898 13,
.halting 0x2001000080800002000200200000080 53866 10,
.halting 0x2001000040800002000200200000080 53850 10,
.halting 0x2001000020800002000200200000080 53834 10,
.halting 0x2001000008800010000200200000080 53805 12
]

private def group39 : List Outcome := [
.halting 0x2001000002800010000200200000080 53773 12,
.halting 0x1001010000800002000200200000080 53754 8,
.halting 0x1001010000800000200200200000080 53750 11,
.halting 0x1001008000800004000200200000080 53739 8,
.halting 0x1001008000800002000200200000080 53738 8,
.halting 0x1001008000800001000200200000080 53737 17,
.halting 0x1001008000800000800200200000080 53736 8,
.halting 0x1001008000800000200200200000080 53734 11,
.halting 0x1001004000800002000200200000080 53722 8,
.halting 0x1001004000800000200200200000080 53718 11,
.halting 0x1001002000800002000200200000080 53706 26,
.halting 0x1001000800800004000200200000080 53675 12,
.halting 0x1001000800800002000200200000080 53674 10,
.halting 0x1001000800800000800200200000080 53672 10,
.halting 0x1001000800800000200200200000080 53670 13,
.halting 0x1001000400800002000200200000080 53658 14,
.halting 0x1001000200800002000200200000080 53642 13,
.halting 0x1001000080800002000200200000080 53610 10,
.halting 0x1001000040800002000200200000080 53594 10,
.halting 0x1001000020800002000200200000080 53578 16,
.halting 0x801010000800002000200200000080 53498 8,
.halting 0x801010000800000200200200000080 53494 11,
.halting 0x801008000800004000200200000080 53483 8,
.halting 0x801008000800002000200200000080 53482 12,
.halting 0x801008000800001000200200000080 53481 21,
.halting 0x801008000800000800200200000080 53480 12,
.halting 0x801008000800000200200200000080 53478 15,
.halting 0x801002000800004000200200000080 53451 8,
.halting 0x801002000800002000200200000080 53450 12,
.halting 0x801002000800000200200200000080 53446 15,
.halting 0x801001000800000800200200000080 53432 9,
.halting 0x801000800800004000200200000080 53419 12
]

private def group40 : List Outcome := [
.halting 0x801000800800002000200200000080 53418 10,
.halting 0x801000800800001000200200000080 53417 9,
.halting 0x801000800800000800200200000080 53416 10,
.halting 0x801000800800000200200200000080 53414 13,
.halting 0x801000400800002000200200000080 53402 14,
.halting 0x801000400800000800200200000080 53400 9,
.halting 0x801000200800002000200200000080 53386 13,
.halting 0x801000080800002000200200000080 53354 10,
.halting 0x801000040800002000200200000080 53338 10,
.halting 0x801000020800002000200200000080 53322 10,
.halting 0x400100000100200000020200200000080 47986 9,
.halting 0x400100000100200000008200200000080 47984 9,
.halting 0x400100000080200000040200200000080 47971 9,
.halting 0x400100000080200000020200200000080 47970 9,
.halting 0x400100000080200000010200200000080 47969 9,
.halting 0x400100000080200000008200200000080 47968 9,
.halting 0x400100000040200000020200200000080 47954 11,
.halting 0x400100000020200000020200200000080 47938 9,
.halting 0x400100000020200000008200200000080 47936 9,
.halting 0x200100000100200000040200200000080 47731 9,
.halting 0x200100000100200000020200200000080 47730 9,
.halting 0x200100000100200000010200200000080 47729 9,
.halting 0x200100000100200000008200200000080 47728 9,
.halting 0x200100000080200000040200200000080 47715 11,
.halting 0x200100000080200000020200200000080 47714 13,
.halting 0x200100000080200000010200200000080 47713 11,
.halting 0x200100000080200000008200200000080 47712 15,
.halting 0x200100000040200000040200200000080 47699 9,
.halting 0x200100000040200000020200200000080 47698 11,
.halting 0x200100000040200000010200200000080 47697 9,
.halting 0x200100000008200040000200200000080 47663 12,
.halting 0x200100000008200004000200200000080 47659 11
]

private def group41 : List Outcome := [
.halting 0x200100000008200001000200200000080 47657 25,
.halting 0x200100000008200000400200200000080 47655 19,
.halting 0x200100000008200000200200200000080 47654 13,
.halting 0x200100000008200000040200200000080 47651 10,
.halting 0x200100000008200000020200200000080 47650 10,
.halting 0x200100000008200000010200200000080 47649 10,
.halting 0x200100000008200000008200200000080 47648 10,
.halting 0x100100000100200000020200200000080 47474 9,
.halting 0x100100000100200000008200200000080 47472 9,
.halting 0x100100000080200000040200200000080 47459 11,
.halting 0x100100000080200000020200200000080 47458 11,
.halting 0x100100000080200000010200200000080 47457 11,
.halting 0x100100000080200000008200200000080 47456 11,
.halting 0x100100000040200000020200200000080 47442 11,
.halting 0x100100000008200004000200200000080 47403 11,
.halting 0x100100000008200002000200200000080 47402 11,
.halting 0x100100000008200000800200200000080 47400 11,
.halting 0x100100000008200000200200200000080 47398 14,
.halting 0x100100000008200000040200200000080 47395 10,
.halting 0x100100000008200000020200200000080 47394 10,
.halting 0x100100000008200000010200200000080 47393 10,
.halting 0x100100000008200000008200200000080 47392 10,
.halting 0x80100000100200000020200200000080 47218 11,
.halting 0x80100000100200000008200200000080 47216 11,
.halting 0x80100000080200000040200200000080 47203 11,
.halting 0x80100000080200000020200200000080 47202 13,
.halting 0x80100000080200000010200200000080 47201 11,
.halting 0x80100000080200000008200200000080 47200 15,
.halting 0x80100000040200000020200200000080 47186 13,
.halting 0x80100000010200002000200200000080 47162 11,
.halting 0x80100000010200000200200200000080 47158 14,
.halting 0x80100000010200000040200200000080 47155 10
]

private def group42 : List Outcome := [
.halting 0x80100000010200000020200200000080 47154 10,
.halting 0x80100000010200000010200200000080 47153 10,
.halting 0x80100000010200000008200200000080 47152 10,
.halting 0x80100000008200000400200200000080 47143 12,
.halting 0x80100000008200000200200200000080 47142 13,
.halting 0x80100000008200000100200200000080 47141 12,
.halting 0x80100000008200000040200200000080 47139 12,
.halting 0x80100000008200000020200200000080 47138 10,
.halting 0x80100000008200000010200200000080 47137 12,
.halting 0x80100000008200000008200200000080 47136 10,
.halting 0x80100000004200002000200200000080 47130 11,
.halting 0x80100000004200000200200200000080 47126 13,
.halting 0x80100000004200000040200200000080 47123 10,
.halting 0x80100000004200000020200200000080 47122 10,
.halting 0x80100000004200000010200200000080 47121 10,
.halting 0x80100000004200000008200200000080 47120 10,
.halting 0x40100000010200002000200200000080 46906 9,
.halting 0x40100000010200000200200200000080 46902 12,
.halting 0x40100000008200008000200200000080 46892 11,
.halting 0x40100000008200004000200200000080 46891 9,
.halting 0x40100000008200002000200200000080 46890 9,
.halting 0x40100000008200000800200200000080 46888 9,
.halting 0x40100000008200000200200200000080 46886 12,
.halting 0x40100000004200002000200200000080 46874 9,
.halting 0x40100000004200000200200200000080 46870 12,
.halting 0x40100000002200008000200200000080 46860 11,
.halting 0x40100000002200004000200200000080 46859 9,
.halting 0x40100000002200002000200200000080 46858 9,
.halting 0x40100000002200000800200200000080 46856 9,
.halting 0x40100000002200000200200200000080 46854 12,
.halting 0x20100010000200000008200200000080 46832 13,
.halting 0x20100004000200000008200200000080 46800 21
]

private def group43 : List Outcome := [
.halting 0x20100001000200000008200200000080 46768 18,
.halting 0x20100000100200000008200200000080 46704 12,
.halting 0x20100000080200000008200200000080 46688 12,
.halting 0x20100000020200000008200200000080 46656 12,
.halting 0x20100000010200010000200200000080 46653 11,
.halting 0x20100000010200004000200200000080 46651 9,
.halting 0x20100000010200002000200200000080 46650 12,
.halting 0x20100000010200001000200200000080 46649 9,
.halting 0x20100000010200000200200200000080 46646 10,
.halting 0x20100000010200000100200200000080 46645 18,
.halting 0x20100000010200000080200200000080 46644 13,
.halting 0x20100000010200000008200200000080 46640 11,
.halting 0x20100000008200010000200200000080 46637 11,
.halting 0x20100000008200004000200200000080 46635 9,
.halting 0x20100000008200002000200200000080 46634 12,
.halting 0x20100000008200000200200200000080 46630 10,
.halting 0x20100000008200000100200200000080 46629 18,
.halting 0x20100000008200000080200200000080 46628 13,
.halting 0x20100000008200000008200200000080 46624 11,
.halting 0x20100000004200010000200200000080 46621 11,
.halting 0x20100000004200004000200200000080 46619 9,
.halting 0x20100000004200002000200200000080 46618 12,
.halting 0x20100000004200001000200200000080 46617 9,
.halting 0x20100000004200000200200200000080 46614 10,
.halting 0x20100000004200000100200200000080 46613 18,
.halting 0x20100000004200000080200200000080 46612 13,
.halting 0x20100000004200000008200200000080 46608 11,
.halting 0x20100000002200010000200200000080 46605 11,
.halting 0x20100000002200004000200200000080 46603 9,
.halting 0x20100000002200002000200200000080 46602 12,
.halting 0x20100000002200001000200200000080 46601 12,
.halting 0x20100000002200000200200200000080 46598 10
]

private def group44 : List Outcome := [
.halting 0x20100000002200000100200200000080 46597 18,
.halting 0x20100000002200000080200200000080 46596 13,
.halting 0x20100000002200000008200200000080 46592 11,
.halting 0x10100000080200000008200200000080 46432 12,
.halting 0x10100000020200000008200200000080 46400 12,
.halting 0x10100000010200000200200200000080 46390 10,
.halting 0x10100000008200004000200200000080 46379 9,
.halting 0x10100000008200000200200200000080 46374 10,
.halting 0x10100000008200000008200200000080 46368 11,
.halting 0x10100000004200000200200200000080 46358 10,
.halting 0x10100000002200004000200200000080 46347 9,
.halting 0x10100000002200000200200200000080 46342 10,
.halting 0x10100000002200000008200200000080 46336 11,
.halting 0x8100000010200002000200200000080 46138 34,
.halting 0x8100000010200000400200200000080 46135 10,
.halting 0x8100000010200000200200200000080 46134 17,
.halting 0x8100000010200000100200200000080 46133 10,
.halting 0x8100000008200002000200200000080 46122 34,
.halting 0x8100000008200000400200200000080 46119 10,
.halting 0x8100000008200000200200200000080 46118 10,
.halting 0x8100000008200000100200200000080 46117 10,
.halting 0x8100000004200002000200200000080 46106 34,
.halting 0x8100000004200000400200200000080 46103 10,
.halting 0x8100000004200000200200200000080 46102 15,
.halting 0x8100000004200000100200200000080 46101 10,
.halting 0x8100000002200002000200200000080 46090 34,
.halting 0x8100000002200000400200200000080 46087 10,
.halting 0x8100000002200000200200200000080 46086 10,
.halting 0x8100000002200000100200200000080 46085 10,
.halting 0x4000010000100200000020200200000080 44914 10,
.halting 0x4000010000100200000008200200000080 44912 10,
.halting 0x4000010000080200000040200200000080 44899 12
]

private def group45 : List Outcome := [
.halting 0x4000010000080200000020200200000080 44898 12,
.halting 0x4000010000080200000010200200000080 44897 12,
.halting 0x4000010000080200000008200200000080 44896 12,
.halting 0x4000010000040200000020200200000080 44882 12,
.halting 0x4000010000008200040000200200000080 44847 14,
.halting 0x4000010000008200020000200200000080 44846 16,
.halting 0x4000010000008200008000200200000080 44844 14,
.halting 0x4000010000008200004000200200000080 44843 12,
.halting 0x4000010000008200002000200200000080 44842 12,
.halting 0x4000010000008200000800200200000080 44840 12,
.halting 0x4000010000008200000200200200000080 44838 16,
.halting 0x4000010000008200000040200200000080 44835 11,
.halting 0x4000010000008200000020200200000080 44834 11,
.halting 0x4000010000008200000010200200000080 44833 11,
.halting 0x4000010000008200000008200200000080 44832 11,
.halting 0x2000010000100200000040200200000080 44659 10,
.halting 0x2000010000100200000020200200000080 44658 10,
.halting 0x2000010000100200000010200200000080 44657 10,
.halting 0x2000010000100200000008200200000080 44656 10,
.halting 0x2000010000080200000040200200000080 44643 10,
.halting 0x2000010000080200000020200200000080 44642 12,
.halting 0x2000010000080200000010200200000080 44641 10,
.halting 0x2000010000080200000008200200000080 44640 14,
.halting 0x2000010000040200000040200200000080 44627 10,
.halting 0x2000010000040200000020200200000080 44626 12,
.halting 0x2000010000040200000010200200000080 44625 10,
.halting 0x2000010000020200000040200200000080 44611 12,
.halting 0x2000010000020200000020200200000080 44610 12,
.halting 0x2000010000020200000010200200000080 44609 12,
.halting 0x800010000100200000020200200000080 44146 10,
.halting 0x800010000100200000008200200000080 44144 10,
.halting 0x800010000080200000040200200000080 44131 10
]

private def group46 : List Outcome := [
.halting 0x800010000080200000020200200000080 44130 12,
.halting 0x800010000080200000010200200000080 44129 10,
.halting 0x800010000080200000008200200000080 44128 14,
.halting 0x800010000040200000020200200000080 44114 12,
.halting 0x800010000020200000020200200000080 44098 12,
.halting 0x20010010000200000040200200000080 42739 13,
.halting 0x20010010000200000020200200000080 42738 13,
.halting 0x20010010000200000010200200000080 42737 13,
.halting 0x20010010000200000008200200000080 42736 13,
.halting 0x20010008000200000040200200000080 42723 11,
.halting 0x20010008000200000020200200000080 42722 11,
.halting 0x20010008000200000010200200000080 42721 11,
.halting 0x20010008000200000008200200000080 42720 11,
.halting 0x20010002000200000040200200000080 42691 11,
.halting 0x20010002000200000020200200000080 42690 11,
.halting 0x20010002000200000010200200000080 42689 11,
.halting 0x20010002000200000008200200000080 42688 11,
.halting 0x20010000080200000040200200000080 42595 10,
.halting 0x20010000080200000020200200000080 42594 10,
.halting 0x20010000080200000010200200000080 42593 10,
.halting 0x20010000080200000008200200000080 42592 10,
.halting 0x20010000020200000020200200000080 42562 10,
.halting 0x20010000020200000008200200000080 42560 10,
.halting 0x2010010000200040000200200000080 41727 12,
.halting 0x2010010000200002000200200000080 41722 11,
.halting 0x2010010000200000800200200000080 41720 13,
.halting 0x2010010000200000200200200000080 41718 15,
.halting 0x2010008000200040000200200000080 41711 12,
.halting 0x2010008000200002000200200000080 41706 11,
.halting 0x2010008000200000800200200000080 41704 11,
.halting 0x2010002000200040000200200000080 41679 12,
.halting 0x2010002000200002000200200000080 41674 11
]

private def group47 : List Outcome := [
.halting 0x2010002000200000800200200000080 41672 11,
.halting 0x2010000800200040000200200000080 41647 19,
.halting 0x2010000080200040000200200000080 41583 13,
.halting 0x2010000020200040000200200000080 41551 26,
.halting 0x2010000010200040000200200000080 41535 11,
.halting 0x2010000010200002000200200000080 41530 10,
.halting 0x2010000010200000200200200000080 41526 14,
.halting 0x2010000008200040000200200000080 41519 11,
.halting 0x2010000008200002000200200000080 41514 10,
.halting 0x2010000008200000800200200000080 41512 10,
.halting 0x2010000008200000200200200000080 41510 14,
.halting 0x2010000004200040000200200000080 41503 11,
.halting 0x2010000004200002000200200000080 41498 10,
.halting 0x2010000004200000200200200000080 41494 14,
.halting 0x2010000002200040000200200000080 41487 11,
.halting 0x2010000002200002000200200000080 41482 10,
.halting 0x2010000002200000800200200000080 41480 10,
.halting 0x2010000002200000200200200000080 41478 14,
.halting 0x4000001008000200000040200200000080 40931 11,
.halting 0x4000001008000200000020200200000080 40930 11,
.halting 0x4000001008000200000010200200000080 40929 11,
.halting 0x4000001008000200000008200200000080 40928 11,
.halting 0x4000001002000200000040200200000080 40899 10,
.halting 0x4000001002000200000020200200000080 40898 10,
.halting 0x4000001002000200000010200200000080 40897 10,
.halting 0x4000001002000200000008200200000080 40896 10,
.halting 0x4000001000800200000040200200000080 40867 17,
.halting 0x4000001000800200000020200200000080 40866 17,
.halting 0x4000001000800200000010200200000080 40865 17,
.halting 0x4000001000800200000008200200000080 40864 17,
.halting 0x100001008000200000040200200000080 39395 11,
.halting 0x100001008000200000020200200000080 39394 11
]

private def group48 : List Outcome := [
.halting 0x100001008000200000010200200000080 39393 11,
.halting 0x100001008000200000008200200000080 39392 11,
.halting 0x40001008000200000020200200000080 38882 9,
.halting 0x40001008000200000008200200000080 38880 9,
.halting 0x40001000800200000040200200000080 38819 13,
.halting 0x40001000800200000020200200000080 38818 13,
.halting 0x40001000800200000010200200000080 38817 13,
.halting 0x40001000800200000008200200000080 38816 13,
.halting 0x20001008000200000040200200000080 38627 9,
.halting 0x20001008000200000020200200000080 38626 9,
.halting 0x20001008000200000010200200000080 38625 9,
.halting 0x20001008000200000008200200000080 38624 9,
.halting 0x20001002000200000040200200000080 38595 9,
.halting 0x20001002000200000020200200000080 38594 9,
.halting 0x20001002000200000010200200000080 38593 9,
.halting 0x20001002000200000008200200000080 38592 9,
.halting 0x10001008000200000020200200000080 38370 11,
.halting 0x10001000800200000040200200000080 38307 13,
.halting 0x10001000800200000020200200000080 38306 15,
.halting 0x10001000800200000010200200000080 38305 13,
.halting 0x8001008000200000020200200000080 38114 9,
.halting 0x8001008000200000008200200000080 38112 9,
.halting 0x8001002000200000020200200000080 38082 9,
.halting 0x8001002000200000008200200000080 38080 9,
.halting 0x4001010000200020000200200000080 37886 10,
.halting 0x4001010000200002000200200000080 37882 11,
.halting 0x4001010000200000800200200000080 37880 23,
.halting 0x4001010000200000200200200000080 37878 15,
.halting 0x4001000080200020000200200000080 37742 9,
.halting 0x4001000080200002000200200000080 37738 12,
.halting 0x4001000020200020000200200000080 37710 9,
.halting 0x2001010000200040000200200000080 37631 10
]

private def group49 : List Outcome := [
.halting 0x2001010000200020000200200000080 37630 10,
.halting 0x2001010000200008000200200000080 37628 10,
.halting 0x2001010000200002000200200000080 37626 11,
.halting 0x2001010000200000800200200000080 37624 23,
.halting 0x2001010000200000200200200000080 37622 15,
.halting 0x2001000800200040000200200000080 37551 15,
.halting 0x2001000800200000040200200000080 37539 14,
.halting 0x2001000800200000020200200000080 37538 14,
.halting 0x2001000800200000010200200000080 37537 14,
.halting 0x2001000800200000008200200000080 37536 14,
.halting 0x2001000080200040000200200000080 37487 9,
.halting 0x2001000080200020000200200000080 37486 9,
.halting 0x2001000080200008000200200000080 37484 9,
.halting 0x2001000020200040000200200000080 37455 11,
.halting 0x2001000020200020000200200000080 37454 9,
.halting 0x2001000020200008000200200000080 37452 9,
.halting 0x1001010000200020000200200000080 37374 10,
.halting 0x1001010000200002000200200000080 37370 11,
.halting 0x1001010000200000800200200000080 37368 23,
.halting 0x1001010000200000200200200000080 37366 15,
.halting 0x1001000080200020000200200000080 37230 9,
.halting 0x1001000080200002000200200000080 37226 12,
.halting 0x1001000020200020000200200000080 37198 9,
.halting 0x801010000200040000200200000080 37119 10,
.halting 0x801010000200020000200200000080 37118 10,
.halting 0x801010000200008000200200000080 37116 10,
.halting 0x801010000200002000200200000080 37114 11,
.halting 0x801010000200000800200200000080 37112 23,
.halting 0x801010000200000200200200000080 37110 15,
.halting 0x801000080200040000200200000080 36975 9,
.halting 0x801000080200020000200200000080 36974 9,
.halting 0x801000080200008000200200000080 36972 9
]

private def group50 : List Outcome := [
.halting 0x801000020200040000200200000080 36943 11,
.halting 0x801000020200020000200200000080 36942 9,
.halting 0x801000020200008000200200000080 36940 9,
.halting 0x4000000110000200002000200200000080 36858 10,
.halting 0x4000000110000200000200200200000080 36854 16,
.halting 0x4000000108000200002000200200000080 36842 12,
.halting 0x4000000108000200000800200200000080 36840 11,
.halting 0x4000000108000200000200200200000080 36838 18,
.halting 0x4000000104000200002000200200000080 36826 10,
.halting 0x4000000104000200000200200200000080 36822 16,
.halting 0x4000000102000200002000200200000080 36810 10,
.halting 0x4000000102000200000800200200000080 36808 10,
.halting 0x4000000102000200000200200200000080 36806 14,
.halting 0x4000000100800200002000200200000080 36778 16,
.halting 0x4000000100800200000800200200000080 36776 15,
.halting 0x4000000100800200000200200200000080 36774 20,
.halting 0x4000000100080200002000200200000080 36714 20,
.halting 0x4000000100040200002000200200000080 36698 12,
.halting 0x4000000100020200002000200200000080 36682 14,
.halting 0x2000000104000200002000200200000080 36570 10,
.halting 0x2000000104000200000200200200000080 36566 14,
.halting 0x2000000100040200002000200200000080 36442 12,
.halting 0x2000000100020200002000200200000080 36426 14,
.halting 0x1000000108000200000800200200000080 36328 15,
.halting 0x800000104000200002000200200000080 36058 10,
.halting 0x800000104000200000200200200000080 36054 14,
.halting 0x800000100040200002000200200000080 35930 12,
.halting 0x800000100020200002000200200000080 35914 14,
.halting 0x400000110000200020000200200000080 35838 10,
.halting 0x400000110000200000200200200000080 35830 34,
.halting 0x400000100008200020000200200000080 35630 9,
.halting 0x400000100002200020000200200000080 35598 9
]

private def group51 : List Outcome := [
.halting 0x200000100040200020000200200000080 35422 11,
.halting 0x200000100040200008000200200000080 35420 11,
.halting 0x200000100010200020000200200000080 35390 9,
.halting 0x200000100010200008000200200000080 35388 9,
.halting 0x200000100008200020000200200000080 35374 9,
.halting 0x200000100008200008000200200000080 35372 9,
.halting 0x200000100004200020000200200000080 35358 9,
.halting 0x200000100004200008000200200000080 35356 9,
.halting 0x200000100002200020000200200000080 35342 9,
.halting 0x200000100002200008000200200000080 35340 9,
.halting 0x100000110000200020000200200000080 35326 10,
.halting 0x100000108000200020000200200000080 35310 10,
.halting 0x100000108000200002000200200000080 35306 11,
.halting 0x100000108000200000800200200000080 35304 11,
.halting 0x100000102000200020000200200000080 35278 10,
.halting 0x100000102000200002000200200000080 35274 21,
.halting 0x100000102000200000800200200000080 35272 15,
.halting 0x80000110000200020000200200000080 35070 10,
.halting 0x80000110000200008000200200000080 35068 10,
.halting 0x80000110000200002000200200000080 35066 11,
.halting 0x80000110000200000200200200000080 35062 15,
.halting 0x80000100008200020000200200000080 34862 9,
.halting 0x80000100008200008000200200000080 34860 9,
.halting 0x80000100002200020000200200000080 34830 9,
.halting 0x80000100002200008000200200000080 34828 9,
.halting 0x20000110000200008000200200000080 34556 13,
.halting 0x20000100040200020000200200000080 34398 14,
.halting 0x20000100040200008000200200000080 34396 22,
.halting 0x20000100010200020000200200000080 34366 12,
.halting 0x20000100008200020000200200000080 34350 12,
.halting 0x20000100008200008000200200000080 34348 12,
.halting 0x20000100004200020000200200000080 34334 12
]

private def group52 : List Outcome := [
.halting 0x20000100002200020000200200000080 34318 12,
.halting 0x20000100002200008000200200000080 34316 12,
.halting 0x10000110000200000200200200000080 34294 31,
.halting 0x4000110000200000200200200000080 33782 13,
.halting 0x4000108000200002000200200000080 33770 9,
.halting 0x4000108000200000800200200000080 33768 9,
.halting 0x4000108000200000200200200000080 33766 13,
.halting 0x4000104000200000200200200000080 33750 13,
.halting 0x4000100800200002000200200000080 33706 12,
.halting 0x4000100800200000800200200000080 33704 12,
.halting 0x4000100800200000200200200000080 33702 15,
.halting 0x4000100080200002000200200000080 33642 15,
.halting 0x2000110000200002000200200000080 33530 9,
.halting 0x2000110000200000200200200000080 33526 13,
.halting 0x2000108000200002000200200000080 33514 9,
.halting 0x2000108000200000800200200000080 33512 9,
.halting 0x2000102000200002000200200000080 33482 9,
.halting 0x2000102000200000800200200000080 33480 9,
.halting 0x1000110000200000200200200000080 33270 13,
.halting 0x1000108000200002000200200000080 33258 9,
.halting 0x1000108000200000800200200000080 33256 9,
.halting 0x1000108000200000200200200000080 33254 13,
.halting 0x1000104000200000200200200000080 33238 13,
.halting 0x1000102000200002000200200000080 33226 13,
.halting 0x1000100800200002000200200000080 33194 12,
.halting 0x1000100800200000800200200000080 33192 12,
.halting 0x1000100800200000200200200000080 33190 15,
.halting 0x1000100080200002000200200000080 33130 15,
.halting 0x800110000200002000200200000080 33018 9,
.halting 0x800110000200000200200200000080 33014 13,
.halting 0x800108000200002000200200000080 33002 9,
.halting 0x800108000200000800200200000080 33000 9
]

private def group53 : List Outcome := [
.halting 0x800108000200000200200200000080 32998 17,
.halting 0x800102000200002000200200000080 32970 9,
.halting 0x800102000200000800200200000080 32968 9,
.halting 0x800102000200000200200200000080 32966 21,
.halting 0x200040000100800000020200200000080 31346 8,
.halting 0x200040000100800000008200200000080 31344 8,
.halting 0x200040000080800000040200200000080 31331 8,
.halting 0x200040000080800000020200200000080 31330 10,
.halting 0x200040000080800000010200200000080 31329 8,
.halting 0x200040000080800000008200200000080 31328 12,
.halting 0x200040000040800000020200200000080 31314 10,
.halting 0x200040000020800000020200200000080 31298 10,
.halting 0x200040000020800000008200200000080 31296 14,
.halting 0x80040000080800000040200200000080 30819 8,
.halting 0x80040000080800000020200200000080 30818 10,
.halting 0x80040000080800000010200200000080 30817 8,
.halting 0x80040000080800000008200200000080 30816 12,
.halting 0x80040000020800000020200200000080 30786 10,
.halting 0x20040000010800020000200200000080 30270 10,
.halting 0x20040000010800002000200200000080 30266 8,
.halting 0x20040000010800000200200200000080 30262 10,
.halting 0x20040000008800020000200200000080 30254 10,
.halting 0x20040000008800010000200200000080 30253 10,
.halting 0x20040000008800008000200200000080 30252 10,
.halting 0x20040000008800004000200200000080 30251 8,
.halting 0x20040000008800001000200200000080 30249 15,
.halting 0x20040000008800000200200200000080 30246 10,
.halting 0x20040000004800020000200200000080 30238 10,
.halting 0x20040000004800002000200200000080 30234 8,
.halting 0x20040000004800000200200200000080 30230 10,
.halting 0x20040000002800020000200200000080 30222 10,
.halting 0x20040000002800010000200200000080 30221 10
]

private def group54 : List Outcome := [
.halting 0x20040000002800008000200200000080 30220 10,
.halting 0x20040000002800004000200200000080 30219 8,
.halting 0x20040000002800002000200200000080 30218 11,
.halting 0x20040000002800000800200200000080 30216 14,
.halting 0x20040000002800000200200200000080 30214 10,
.halting 0x8040000010800002000200200000080 29754 8,
.halting 0x8040000010800000200200200000080 29750 10,
.halting 0x8040000008800000200200200000080 29734 10,
.halting 0x8040000004800002000200200000080 29722 8,
.halting 0x8040000004800000200200200000080 29718 10,
.halting 0x8040000002800002000200200000080 29706 11,
.halting 0x8040000002800000200200200000080 29702 10,
.halting 0x40004008000800000020200200000080 26594 8,
.halting 0x40004008000800000008200200000080 26592 8,
.halting 0x40004000800800000040200200000080 26531 11,
.halting 0x40004000800800000020200200000080 26530 11,
.halting 0x40004000800800000010200200000080 26529 11,
.halting 0x40004000800800000008200200000080 26528 11,
.halting 0x20004008000800000040200200000080 26339 8,
.halting 0x20004008000800000020200200000080 26338 10,
.halting 0x20004008000800000010200200000080 26337 8,
.halting 0x20004002000800000040200200000080 26307 8,
.halting 0x20004002000800000020200200000080 26306 10,
.halting 0x20004002000800000010200200000080 26305 8,
.halting 0x20004000800800000040200200000080 26275 11,
.halting 0x20004000800800000020200200000080 26274 13,
.halting 0x20004000800800000010200200000080 26273 11,
.halting 0x10004008000800000020200200000080 26082 10,
.halting 0x10004000800800000040200200000080 26019 11,
.halting 0x10004000800800000020200200000080 26018 13,
.halting 0x10004000800800000010200200000080 26017 11,
.halting 0x8004008000800000020200200000080 25826 10
]

private def group55 : List Outcome := [
.halting 0x8004008000800000008200200000080 25824 13,
.halting 0x8004002000800000020200200000080 25794 10,
.halting 0x8004000800800000040200200000080 25763 13,
.halting 0x8004000800800000020200200000080 25762 13,
.halting 0x8004000800800000010200200000080 25761 13,
.halting 0x8004000800800000008200200000080 25760 16,
.halting 0x4004000080800020000200200000080 25454 8,
.halting 0x4004000080800002000200200000080 25450 13,
.halting 0x4004000020800020000200200000080 25422 8,
.halting 0x2004000080800040000200200000080 25199 8,
.halting 0x2004000080800002000200200000080 25194 13,
.halting 0x2004000080800000080200200000080 25188 16,
.halting 0x2004000020800002000200200000080 25162 11,
.halting 0x1004000080800020000200200000080 24942 8,
.halting 0x1004000080800002000200200000080 24938 13,
.halting 0x1004000020800020000200200000080 24910 8,
.halting 0x804000080800040000200200000080 24687 8,
.halting 0x804000080800008000200200000080 24684 12,
.halting 0x804000080800002000200200000080 24682 13,
.halting 0x804000080800000080200200000080 24676 16,
.halting 0x804000020800002000200200000080 24650 11,
.halting 0x400000400008800020000200200000080 23342 8,
.halting 0x400000400002800020000200200000080 23310 8,
.halting 0x200000400010800020000200200000080 23102 8,
.halting 0x200000400010800008000200200000080 23100 8,
.halting 0x200000400004800020000200200000080 23070 8,
.halting 0x200000400004800008000200200000080 23068 8,
.halting 0x200000400002800020000200200000080 23054 11,
.halting 0x200000400002800008000200200000080 23052 11,
.halting 0x80000400008800020000200200000080 22574 19,
.halting 0x80000400002800020000200200000080 22542 13,
.halting 0x20000400010800020000200200000080 22078 16
]

private def group56 : List Outcome := [
.halting 0x20000400008800020000200200000080 22062 16,
.halting 0x20000400008800008000200200000080 22060 16,
.halting 0x20000400004800020000200200000080 22046 16,
.halting 0x20000400002800020000200200000080 22030 16,
.halting 0x20000400002800008000200200000080 22028 16,
.halting 0x10000400008800020000200200000080 21806 16,
.halting 0x10000400002800020000200200000080 21774 16,
.halting 0x4000410000800000200200200000080 21494 11,
.halting 0x4000408000800002000200200000080 21482 8,
.halting 0x4000408000800000800200200000080 21480 8,
.halting 0x4000408000800000200200200000080 21478 11,
.halting 0x4000404000800000200200200000080 21462 11,
.halting 0x4000400800800002000200200000080 21418 10,
.halting 0x4000400800800000800200200000080 21416 10,
.halting 0x4000400800800000200200200000080 21414 13,
.halting 0x4000400080800002000200200000080 21354 10,
.halting 0x2000410000800002000200200000080 21242 8,
.halting 0x2000410000800000200200200000080 21238 11,
.halting 0x2000408000800002000200200000080 21226 15,
.halting 0x2000408000800000800200200000080 21224 15,
.halting 0x2000400800800002000200200000080 21162 10,
.halting 0x2000400800800000800200200000080 21160 10,
.halting 0x2000400800800000200200200000080 21158 13,
.halting 0x2000400400800002000200200000080 21146 13,
.halting 0x2000400200800002000200200000080 21130 13,
.halting 0x2000400080800002000200200000080 21098 10,
.halting 0x2000400040800002000200200000080 21082 10,
.halting 0x2000400020800002000200200000080 21066 10,
.halting 0x1000410000800000200200200000080 20982 11,
.halting 0x1000408000800002000200200000080 20970 8,
.halting 0x1000408000800000800200200000080 20968 8,
.halting 0x1000408000800000200200200000080 20966 11
]

private def group57 : List Outcome := [
.halting 0x1000404000800000200200200000080 20950 11,
.halting 0x1000400800800002000200200000080 20906 10,
.halting 0x1000400800800000800200200000080 20904 10,
.halting 0x1000400800800000200200200000080 20902 13,
.halting 0x1000400080800002000200200000080 20842 10,
.halting 0x800410000800002000200200000080 20730 8,
.halting 0x800410000800000200200200000080 20726 11,
.halting 0x800408000800002000200200000080 20714 12,
.halting 0x800408000800000800200200000080 20712 12,
.halting 0x800408000800000200200200000080 20710 15,
.halting 0x800402000800002000200200000080 20682 12,
.halting 0x800402000800000200200200000080 20678 15,
.halting 0x800400800800002000200200000080 20650 10,
.halting 0x800400800800000800200200000080 20648 10,
.halting 0x800400800800000200200200000080 20646 13,
.halting 0x800400400800002000200200000080 20634 13,
.halting 0x800400200800002000200200000080 20618 13,
.halting 0x800400080800002000200200000080 20586 10,
.halting 0x800400040800002000200200000080 20570 10,
.halting 0x800400020800002000200200000080 20554 10,
.halting 0x200040000100200000020200200000080 14962 9,
.halting 0x200040000100200000008200200000080 14960 9,
.halting 0x200040000080200000040200200000080 14947 11,
.halting 0x200040000080200000020200200000080 14946 13,
.halting 0x200040000080200000010200200000080 14945 11,
.halting 0x200040000080200000008200200000080 14944 15,
.halting 0x200040000040200000020200200000080 14930 11,
.halting 0x200040000008200040000200200000080 14895 12,
.halting 0x200040000008200004000200200000080 14891 11,
.halting 0x200040000008200000400200200000080 14887 17,
.halting 0x200040000008200000200200200000080 14886 13,
.halting 0x200040000008200000040200200000080 14883 10
]

private def group58 : List Outcome := [
.halting 0x200040000008200000020200200000080 14882 10,
.halting 0x200040000008200000010200200000080 14881 10,
.halting 0x200040000008200000008200200000080 14880 10,
.halting 0x80040000080200000040200200000080 14435 11,
.halting 0x80040000080200000020200200000080 14434 13,
.halting 0x80040000080200000010200200000080 14433 11,
.halting 0x80040000080200000008200200000080 14432 15,
.halting 0x80040000008200000400200200000080 14375 16,
.halting 0x80040000008200000200200200000080 14374 13,
.halting 0x80040000008200000040200200000080 14371 17,
.halting 0x80040000008200000020200200000080 14370 10,
.halting 0x80040000008200000008200200000080 14368 10,
.halting 0x20040010000200000008200200000080 14064 14,
.halting 0x20040001000200000008200200000080 14000 16,
.halting 0x20040000100200000008200200000080 13936 17,
.halting 0x20040000080200000008200200000080 13920 12,
.halting 0x20040000020200000008200200000080 13888 12,
.halting 0x20040000010200002000200200000080 13882 12,
.halting 0x20040000010200000200200200000080 13878 10,
.halting 0x20040000010200000008200200000080 13872 18,
.halting 0x20040000008200010000200200000080 13869 11,
.halting 0x20040000008200004000200200000080 13867 9,
.halting 0x20040000008200002000200200000080 13866 12,
.halting 0x20040000008200001000200200000080 13865 18,
.halting 0x20040000008200000200200200000080 13862 10,
.halting 0x20040000008200000100200200000080 13861 16,
.halting 0x20040000008200000080200200000080 13860 13,
.halting 0x20040000008200000008200200000080 13856 11,
.halting 0x20040000004200002000200200000080 13850 12,
.halting 0x20040000004200000200200200000080 13846 10,
.halting 0x20040000002200010000200200000080 13837 11,
.halting 0x20040000002200004000200200000080 13835 9
]

private def group59 : List Outcome := [
.halting 0x20040000002200002000200200000080 13834 12,
.halting 0x20040000002200000200200200000080 13830 10,
.halting 0x20040000002200000100200200000080 13829 16,
.halting 0x20040000002200000080200200000080 13828 13,
.halting 0x20040000002200000008200200000080 13824 11,
.halting 0x8040000010200000200200200000080 13366 21,
.halting 0x8040000008200000200200200000080 13350 10,
.halting 0x8040000002200000200200200000080 13318 10
]

def rows : List (List Outcome) := [
  group0,group1,group2,group3,group4,group5,group6,group7,
  group8,group9,group10,group11,group12,group13,group14,group15,
  group16,group17,group18,group19,group20,group21,group22,group23,
  group24,group25,group26,group27,group28,group29,group30,group31,
  group32,group33,group34,group35,group36,group37,group38,group39,
  group40,group41,group42,group43,group44,group45,group46,group47,
  group48,group49,group50,group51,group52,group53,group54,group55,
  group56,group57,group58,group59
]

private def bytePage0 (h : ℕ) : List ℕ :=
  (bif Nat.ble h 15 then (bif Nat.ble h 7 then (bif Nat.ble h 3 then (bif Nat.ble h 1 then (bif Nat.ble h 0 then [1] else [1]) else (bif Nat.ble h 2 then [1] else [1])) else (bif Nat.ble h 5 then (bif Nat.ble h 4 then [1] else [1]) else (bif Nat.ble h 6 then [1] else [1]))) else (bif Nat.ble h 11 then (bif Nat.ble h 9 then (bif Nat.ble h 8 then [1] else [1]) else (bif Nat.ble h 10 then [1] else [1])) else (bif Nat.ble h 13 then (bif Nat.ble h 12 then [1] else [1]) else (bif Nat.ble h 14 then [1] else [1])))) else (bif Nat.ble h 23 then (bif Nat.ble h 19 then (bif Nat.ble h 17 then (bif Nat.ble h 16 then [7,6] else [2,6]) else (bif Nat.ble h 18 then [7,6] else [2,6])) else (bif Nat.ble h 21 then (bif Nat.ble h 20 then [2,6] else [2,6]) else (bif Nat.ble h 22 then [7,6] else [2,6]))) else (bif Nat.ble h 27 then (bif Nat.ble h 25 then (bif Nat.ble h 24 then [7,6] else [2,6]) else (bif Nat.ble h 26 then [7,6] else [2,6])) else (bif Nat.ble h 29 then (bif Nat.ble h 28 then [2,6] else [2,6]) else (bif Nat.ble h 30 then [7,6] else [2,6])))))

private def bytePage1 (h : ℕ) : List ℕ :=
  (bif Nat.ble h 47 then (bif Nat.ble h 39 then (bif Nat.ble h 35 then (bif Nat.ble h 33 then (bif Nat.ble h 32 then [3,8] else [3,8]) else (bif Nat.ble h 34 then [3,8] else [3,8])) else (bif Nat.ble h 37 then (bif Nat.ble h 36 then [3,8] else [3,8]) else (bif Nat.ble h 38 then [3,8] else [3,8]))) else (bif Nat.ble h 43 then (bif Nat.ble h 41 then (bif Nat.ble h 40 then [3,8] else [3,8]) else (bif Nat.ble h 42 then [3,8] else [3,8])) else (bif Nat.ble h 45 then (bif Nat.ble h 44 then [3,8] else [3,8]) else (bif Nat.ble h 46 then [3,8] else [3,8])))) else (bif Nat.ble h 55 then (bif Nat.ble h 51 then (bif Nat.ble h 49 then (bif Nat.ble h 48 then [715] else [9]) else (bif Nat.ble h 50 then [714] else [9])) else (bif Nat.ble h 53 then (bif Nat.ble h 52 then [2,0,862,89,218,32,325,91,1895,1894,1893,697] else [9]) else (bif Nat.ble h 54 then [0,42,861,860,859,141,324,323,322,217,1892,1891,1890,1889,1888,1887,1886,1885,1884,1883,1882,1881,1880,1879,1878,1877,1876,1875,1874,1873,1872,1871,1870,1869,1868,696,695,694,693,692,691,690] else [9]))) else (bif Nat.ble h 59 then (bif Nat.ble h 57 then (bif Nat.ble h 56 then [0,27,4,88,686,321,320,91,1867,1866,1865,1864,1863,1862,1861,1860,1859,689,688,687,685,684,683,216] else [9]) else (bif Nat.ble h 58 then [0,4,802,801,800,57,678,319,1858,1857,1856,1855,1854,1853,1852,1851,1850,1849,1848,1847,1846,1845,1844,682,681,680,679,677,676,215] else [9])) else (bif Nat.ble h 61 then (bif Nat.ble h 60 then [9] else [9]) else (bif Nat.ble h 62 then [0,10,4] else [9])))))

private def bytePage2 (h : ℕ) : List ℕ :=
  (bif Nat.ble h 79 then (bif Nat.ble h 71 then (bif Nat.ble h 67 then (bif Nat.ble h 65 then (bif Nat.ble h 64 then [703] else [703]) else (bif Nat.ble h 66 then [703] else [703])) else (bif Nat.ble h 69 then (bif Nat.ble h 68 then [703] else [703]) else (bif Nat.ble h 70 then [703] else [703]))) else (bif Nat.ble h 75 then (bif Nat.ble h 73 then (bif Nat.ble h 72 then [703] else [703]) else (bif Nat.ble h 74 then [703] else [703])) else (bif Nat.ble h 77 then (bif Nat.ble h 76 then [703] else [703]) else (bif Nat.ble h 78 then [703] else [703])))) else (bif Nat.ble h 87 then (bif Nat.ble h 83 then (bif Nat.ble h 81 then (bif Nat.ble h 80 then [7,858,857,732,731,25,19,140,1843,1842,1841,1840,1839,1838,1837,1836,1835,1834,1833,1832,1831,1830,1829,920,919,918,917,916,915,914,913,912,911,675,674,673,318,139,122] else [2,856,732,731,25,57,19,140,1828,1827,1826,1825,1824,1823,1822,1821,1820,920,919,918,917,916,915,914,913,912,911,672,122,91]) else (bif Nat.ble h 82 then [7,855,854,732,731,25,19,140,1819,1818,1817,1816,1815,1814,1813,1812,1811,1810,1809,1808,920,919,918,917,916,915,914,913,912,911,671,670,669,668,318,317,214,139,122] else [2,853,732,731,25,57,19,140,1807,1806,1805,1804,1803,1802,1801,1800,1799,920,919,918,917,916,915,914,913,912,911,667,122,91])) else (bif Nat.ble h 85 then (bif Nat.ble h 84 then [2,0,732,731,32,91,920,919,918,917,916,915,914,913,912,911] else [2,0,732,731,90,25,1798,1797,920,919,918,917,916,915,914,913,912,911]) else (bif Nat.ble h 86 then [7,0,732,731,42,1796,1795,1794,1793,1792,1791,920,919,918,917,916,915,914,913,912,911] else [2,0,732,731,316,90,25,920,919,918,917,916,915,914,913,912,911]))) else (bif Nat.ble h 91 then (bif Nat.ble h 89 then (bif Nat.ble h 88 then [7,0,732,731,91,90,1790,1789,920,919,918,917,916,915,914,913,912,911,666,665] else [2,0,732,731,90,25,920,919,918,917,916,915,914,913,912,911,664,663]) else (bif Nat.ble h 90 then [7,0,732,731,25,1788,1787,1786,1785,1784,1783,920,919,918,917,916,915,914,913,912,911,662,661] else [2,0,732,731,90,25,1782,1781,920,919,918,917,916,915,914,913,912,911])) else (bif Nat.ble h 93 then (bif Nat.ble h 92 then [2,0,732,731,32,25,920,919,918,917,916,915,914,913,912,911] else [2,0,732,731,32,25,920,919,918,917,916,915,914,913,912,911]) else (bif Nat.ble h 94 then [7,0,732,731,32,25,920,919,918,917,916,915,914,913,912,911] else [2,0,732,731,32,25,920,919,918,917,916,915,914,913,912,911])))))

private def bytePage3 (h : ℕ) : List ℕ :=
  (bif Nat.ble h 111 then (bif Nat.ble h 103 then (bif Nat.ble h 99 then (bif Nat.ble h 97 then (bif Nat.ble h 96 then [3,799,798,797,723,722,25,19,1780,1779,1778,1777,1776,910,909,908,907,906,905,660,659,658,657,213,123] else [3,796,795,723,722,27,25,42,1775,1774,1773,910,909,908,907,906,905,213,123,91,57]) else (bif Nat.ble h 98 then [3,794,793,792,723,722,25,19,1772,1771,1770,1769,910,909,908,907,906,905,656,655,654,653,239,213,123] else [3,791,790,723,722,27,25,42,1768,1767,1766,910,909,908,907,906,905,213,123,91,57])) else (bif Nat.ble h 101 then (bif Nat.ble h 100 then [3,0,723,722,91,90,1765,1764,1763,1762,1761,1760,1759,910,909,908,907,906,905,652] else [3,0,723,722,27,90,25,1758,1757,1756,1755,910,909,908,907,906,905,651,650]) else (bif Nat.ble h 102 then [3,0,723,722,25,1754,1753,1752,1751,1750,1749,1748,1747,1746,910,909,908,907,906,905,649,648,647] else [3,0,723,722,27,90,25,1745,1744,1743,1742,1741,1740,910,909,908,907,906,905]))) else (bif Nat.ble h 107 then (bif Nat.ble h 105 then (bif Nat.ble h 104 then [3,0,723,722,4,91,910,909,908,907,906,905] else [3,0,723,722,4,25,910,909,908,907,906,905]) else (bif Nat.ble h 106 then [3,0,723,722,4,57,910,909,908,907,906,905] else [3,0,723,722,4,25,910,909,908,907,906,905])) else (bif Nat.ble h 109 then (bif Nat.ble h 108 then [3,0,723,722,4,25,910,909,908,907,906,905] else [3,0,723,722,4,25,910,909,908,907,906,905]) else (bif Nat.ble h 110 then [3,0,723,722,4,25,910,909,908,907,906,905] else [3,0,723,722,4,25,910,909,908,907,906,905])))) else (bif Nat.ble h 119 then (bif Nat.ble h 115 then (bif Nat.ble h 113 then (bif Nat.ble h 112 then [713] else [9]) else (bif Nat.ble h 114 then [712] else [9])) else (bif Nat.ble h 117 then (bif Nat.ble h 116 then [2,0,852,851,32,91,1739,1738,1737,1736,1735,1734,1733,646,645,644] else [9]) else (bif Nat.ble h 118 then [0,42,850,849,848,847,315,314,313,312,1732,1731,1730,1729,1728,1727,1726,1725,1724,1723,1722,1721,1720,1719,1718,1717,1716,1715,1714,643,311,310] else [9]))) else (bif Nat.ble h 123 then (bif Nat.ble h 121 then (bif Nat.ble h 120 then [0,27,4,789,788,91,1713,1712,1711,1710,1709,642] else [9]) else (bif Nat.ble h 122 then [0,4,787,786,785,784,57,1708,1707,1706,1705,1704,1703,1702,1701,1700,641] else [9])) else (bif Nat.ble h 125 then (bif Nat.ble h 124 then [9] else [9]) else (bif Nat.ble h 126 then [0,10,4] else [9])))))

private def bytePage4 (h : ℕ) : List ℕ :=
  (bif Nat.ble h 143 then (bif Nat.ble h 135 then (bif Nat.ble h 131 then (bif Nat.ble h 129 then (bif Nat.ble h 128 then [5,11,846,845,730,729,728,16,26,23,22,30,1699,1698,1697,1696,1695,1694,1693,1692,904,903,902,901,900,899,898,897,896,895,894,93,87,59] else [11,844,730,729,728,51,26,23,22,16,30,65,59,110,93,1691,1690,1689,1688,1687,1686,1685,1684,1683,1682,904,903,902,901,900,899,898,897,896,895,894,640,639,638,637,636,309,160,159,158,157,156,155,154,153,152,151,150,149,148,147,146,87]) else (bif Nat.ble h 130 then [5,11,843,842,730,729,728,16,23,22,30,238,308,212,1681,1680,1679,1678,1677,1676,904,903,902,901,900,899,898,897,896,895,894,127,87,59] else [11,841,730,729,728,86,26,23,22,16,30,65,59,110,93,1675,1674,1673,1672,1671,1670,1669,1668,1667,904,903,902,901,900,899,898,897,896,895,894,635,634,633,632,631,630,629,160,159,158,157,156,155,154,153,152,151,150,149,148,147,146,87])) else (bif Nat.ble h 133 then (bif Nat.ble h 132 then [5,11,39,730,729,728,16,23,22,104,30,145,144,307,306,105,904,903,902,901,900,899,898,897,896,895,894,628,627,626,625,624,623,622,621,87,59] else [5,11,840,730,729,728,85,16,105,30,26,23,22,1666,904,903,902,901,900,899,898,897,896,895,894,620,619,618,617,616,93,87,59]) else (bif Nat.ble h 134 then [5,11,39,730,729,728,16,26,23,22,104,30,1665,1664,1663,1662,1661,1660,1659,1658,1657,904,903,902,901,900,899,898,897,896,895,894,615,614,613,612,611,610,609,93,87,59] else [5,11,730,729,728,51,16,105,138,40,30,26,23,22,137,124,904,903,902,901,900,899,898,897,896,895,894,608,607,606,605,604,305,93,87,59]))) else (bif Nat.ble h 139 then (bif Nat.ble h 137 then (bif Nat.ble h 136 then [5,11,39,730,729,728,16,40,23,22,30,143,304,303,1656,1655,1654,1653,1652,1651,1650,1649,904,903,902,901,900,899,898,897,896,895,894,603,602,601,600,127,87,59] else [5,11,730,729,728,16,40,121,26,23,22,30,302,212,1648,1647,1646,1645,1644,1643,1642,904,903,902,901,900,899,898,897,896,895,894,599,598,597,596,595,594,593,592,591,127,87,59]) else (bif Nat.ble h 138 then [5,11,39,730,729,728,16,40,23,22,30,92,300,136,1641,1640,1639,1638,1637,1636,1635,1634,1633,1632,904,903,902,901,900,899,898,897,896,895,894,590,589,127,87,59] else [5,11,730,729,728,51,16,105,40,30,26,23,22,210,124,1631,1630,1629,1628,904,903,902,901,900,899,898,897,896,895,894,588,587,586,585,584,309,93,87,59])) else (bif Nat.ble h 141 then (bif Nat.ble h 140 then [11,730,729,728,84,83,26,23,22,16,30,237,93,59,299,110,65,1627,1626,1625,1624,904,903,902,901,900,899,898,897,896,895,894,583,582,581,580,579,578,577,160,159,158,157,156,155,154,153,152,151,150,149,148,147,146,87] else [5,11,730,729,728,16,124,23,40,30,238,22,137,236,235,308,298,297,105,1623,904,903,902,901,900,899,898,897,896,895,894,576,575,574,573,572,571,570,127,87,59]) else (bif Nat.ble h 142 then [11,730,729,728,82,81,26,23,22,16,30,234,93,59,296,110,65,1622,1621,1620,1619,904,903,902,901,900,899,898,897,896,895,894,569,568,567,566,565,564,305,160,159,158,157,156,155,154,153,152,151,150,149,148,147,146,87] else [11,839,838,730,729,728,26,23,22,16,30,65,59,110,93,1618,1617,1616,1615,1614,1613,1612,1611,1610,1609,1608,1607,1606,1605,1604,1603,904,903,902,901,900,899,898,897,896,895,894,160,159,158,157,156,155,154,153,152,151,150,149,148,147,146,87])))) else (bif Nat.ble h 151 then (bif Nat.ble h 147 then (bif Nat.ble h 145 then (bif Nat.ble h 144 then [5,13,783,782,721,720,18,15,131,130,129,128,36,1602,1601,1600,1599,1598,1597,1596,1595,1594,1593,1592,1591,893,892,891,890,889,888,887,886,885,884,563,562,80,79] else [29,13,781,780,721,720,19,15,95,18,46,45,36,47,78,103,1590,1589,1588,1587,1586,1585,1584,893,892,891,890,889,888,887,886,885,884,561,560,559,558,557,556,295,294,293,292,291,290,123,109,80,79]) else (bif Nat.ble h 146 then [5,13,779,778,721,720,18,15,47,46,45,36,289,1583,1582,1581,1580,1579,1578,1577,1576,1575,1574,1573,1572,1571,1570,1569,1568,1567,893,892,891,890,889,888,887,886,885,884,555,233,80,79] else [29,13,777,776,721,720,19,15,108,18,46,45,36,47,78,103,1566,1565,1564,1563,1562,1561,1560,893,892,891,890,889,888,887,886,885,884,554,553,552,551,550,549,295,294,293,292,291,290,123,109,80,79])) else (bif Nat.ble h 149 then (bif Nat.ble h 148 then [0,13,721,720,18,15,222,221,220,219,36,1559,1558,1557,1556,893,892,891,890,889,888,887,886,885,884,548,547,546,545,80,79] else [0,13,721,720,18,15,47,46,45,36,232,1555,1554,1553,1552,893,892,891,890,889,888,887,886,885,884,701,700,699,544,543,80,79]) else (bif Nat.ble h 150 then [0,28,721,720,13,18,15,36,1551,1550,1549,1548,1547,1546,1545,1544,893,892,891,890,889,888,887,886,885,884,80,79] else [0,13,721,720,18,15,95,47,46,45,36,1543,1542,1541,1540,1539,1538,893,892,891,890,889,888,887,886,885,884,542,541,80,79]))) else (bif Nat.ble h 155 then (bif Nat.ble h 153 then (bif Nat.ble h 152 then [0,28,721,720,13,18,15,209,208,36,893,892,891,890,889,888,887,886,885,884,80,79] else [0,28,721,720,13,18,15,207,36,1537,1536,1535,1534,893,892,891,890,889,888,887,886,885,884,80,79]) else (bif Nat.ble h 154 then [0,28,721,720,13,18,120,15,36,893,892,891,890,889,888,887,886,885,884,80,79] else [0,28,721,720,13,18,15,119,118,36,893,892,891,890,889,888,887,886,885,884,80,79])) else (bif Nat.ble h 157 then (bif Nat.ble h 156 then [0,13,721,720,18,15,206,205,204,47,46,45,36,893,892,891,890,889,888,887,886,885,884,80,79] else [0,28,721,720,13,18,15,119,118,36,893,892,891,890,889,888,887,886,885,884,80,79]) else (bif Nat.ble h 158 then [0,13,721,720,18,15,203,202,201,47,46,45,36,893,892,891,890,889,888,887,886,885,884,80,79] else [0,13,721,720,18,15,47,46,45,36,1533,1532,1531,1530,1529,1528,1527,1526,1525,1524,1523,1522,893,892,891,890,889,888,887,886,885,884,80,79])))))

private def bytePage5 (h : ℕ) : List ℕ :=
  (bif Nat.ble h 175 then (bif Nat.ble h 167 then (bif Nat.ble h 163 then (bif Nat.ble h 161 then (bif Nat.ble h 160 then [14,5,61] else [12,41,21]) else (bif Nat.ble h 162 then [5,60,837,836,835,834,77,126,125,133,211,92,301,288,287,136,1521,1520,1519,1518,1517,1516,1515,1514,1513,1512,1511,1510,1509,1508,1507,1506,1505,1504,1503,1502,1501,1500,1499,1498,1497,1496,1495,538,537,536,535,534,533,127] else [14,21,41])) else (bif Nat.ble h 165 then (bif Nat.ble h 164 then [33,0,111,102,327,326,17] else [37,0,101,41,21,197]) else (bif Nat.ble h 166 then [0,64,28,775,774,75,231,1494,1493,1492,1491,1490,1489,1488,1487,1486,1485,1484,1483,1482,1481,1480,1479,1478,1477,698,532,531] else [12,0,41,21]))) else (bif Nat.ble h 171 then (bif Nat.ble h 169 then (bif Nat.ble h 168 then [0,35,4] else [0,38,4,286,58]) else (bif Nat.ble h 170 then [0,24,4] else [12,0,4])) else (bif Nat.ble h 173 then (bif Nat.ble h 172 then [0,4,773,772,771,770,17,76,1476,1475,1474,1473,1472,1471,1470,1469,540,530] else [0,24,4]) else (bif Nat.ble h 174 then [0,4,769,768,767,766,1468,1467,1466,1465,1464,1463,1462,1461,1460,1459,1458,1457,1456,1455,539,529] else [0,4,765,764,763,17,285,76,1454,1453,1452,1451,1450,1449,1448,1447,1446,1445,1444,1443,1442,1441,1440,1439,1438,1437,528,527,526,525,524,284])))) else (bif Nat.ble h 183 then (bif Nat.ble h 179 then (bif Nat.ble h 177 then (bif Nat.ble h 176 then [711] else [710]) else (bif Nat.ble h 178 then [709] else [708])) else (bif Nat.ble h 181 then (bif Nat.ble h 180 then [0,32,833,832,831,830,196,1436,1435,1434,1433,1432,1431,1430,1429,1428,1427,1426,1425,1424,1423,1422,1421] else [0,829,828,827,56,55,195,194,142,117,74,283,282,100,1420,1419,1418,1417,1416,1415,1414,1413,1412,1411,523,522,521,520,519,518,517,516,515,281,280,279]) else (bif Nat.ble h 182 then [0,826,825,824,116,193,192,191,217,1410,1409,1408,1407,1406,1405,1404,1403,1402,1401,1400,1399,1398,1397,1396,1395,1394,1393,1392,1391,1390,1389,1388,1387,1386,1385,1384,1383,1382,1381,1380,1379,1378,1377,1376,1375,1374,514,513,512,511,510] else [0,823,822,821,820,56,55,190,74,278,100,1373,1372,1371,1370,1369,1368,1367,1366,1365,1364,1363,1362,1361,1360,509,508,507,506,505,504]))) else (bif Nat.ble h 187 then (bif Nat.ble h 185 then (bif Nat.ble h 184 then [0,4,73,188,115,114,498,189,100,1359,1358,1357,1356,1355,1354,1353,1352,1351,1350,1349,1348,1347,1346,1345,1344,1343,1342,1341,1340,1339,1338,1337,1336,1335,1334,503,502,501,500,499,497,496,495,494,493,492,491,490,489,488,487,486,485,281,216] else [0,4,762,761,760,186,277,1333,1332,1331,1330,1329,1328,1327,1326,1325,1324,1323,1322,1321,1320,1319,484,483,482,481,480,479,478,477,280,187]) else (bif Nat.ble h 186 then [0,4,759,758,757,185,473,1318,1317,1316,1315,1314,1313,1312,1311,1310,1309,1308,1307,1306,1305,1304,1303,1302,1301,1300,1299,476,475,474,472,279,215] else [0,4,756,755,754,753,276,1298,1297,1296,1295,1294,1293,1292,1291,1290,471,470,469,468,142])) else (bif Nat.ble h 189 then (bif Nat.ble h 188 then [0,20,4] else [0,10,4]) else (bif Nat.ble h 190 then [0,20,4] else [0,10,4])))))

private def bytePage6 (h : ℕ) : List ℕ :=
  (bif Nat.ble h 207 then (bif Nat.ble h 199 then (bif Nat.ble h 195 then (bif Nat.ble h 193 then (bif Nat.ble h 192 then [702] else [702]) else (bif Nat.ble h 194 then [702] else [702])) else (bif Nat.ble h 197 then (bif Nat.ble h 196 then [702] else [702]) else (bif Nat.ble h 198 then [702] else [702]))) else (bif Nat.ble h 203 then (bif Nat.ble h 201 then (bif Nat.ble h 200 then [702] else [702]) else (bif Nat.ble h 202 then [702] else [702])) else (bif Nat.ble h 205 then (bif Nat.ble h 204 then [702] else [702]) else (bif Nat.ble h 206 then [702] else [702])))) else (bif Nat.ble h 215 then (bif Nat.ble h 211 then (bif Nat.ble h 209 then (bif Nat.ble h 208 then [19,15,819,818,817,727,726,725,724,31,66,44,43,109,103,1289,1288,1287,1286,1285,1284,1283,1282,1281,1280,1279,1278,1277,1276,1275,1274,1273,1272,1271,1270,1269,1268,883,882,881,880,879,878,877,876,875,874,873,872,467,466,465,464,463,462,275,184,183,139,123,122,99,72,71,70] else [29,816,727,726,725,724,31,19,15,96,44,43,107,98,274,109,103,78,1267,1266,1265,1264,1263,1262,1261,1260,1259,1258,1257,1256,1255,1254,1253,1252,1251,1250,1249,883,882,881,880,879,878,877,876,875,874,873,872,461,460,459,458,457,456,455,454,184,183,139,123,122,99,72,71,70]) else (bif Nat.ble h 210 then [19,15,815,814,813,727,726,725,724,31,44,43,214,273,239,233,109,103,1248,1247,1246,1245,1244,1243,1242,1241,1240,1239,1238,1237,1236,1235,1234,1233,1232,1231,1230,1229,1228,1227,883,882,881,880,879,878,877,876,875,874,873,872,453,452,451,450,449,448,447,446,445,444,443,317,275,184,183,139,123,122,99,72,71,70] else [29,812,727,726,725,724,31,19,94,15,44,43,98,66,272,109,103,78,1226,1225,1224,1223,1222,1221,1220,1219,1218,1217,1216,1215,1214,1213,1212,1211,1210,883,882,881,880,879,878,877,876,875,874,873,872,442,441,440,439,438,437,436,435,434,184,183,139,123,122,99,72,71,70])) else (bif Nat.ble h 213 then (bif Nat.ble h 212 then [0,727,726,725,724,78,15,271,182,132,44,43,1209,1208,1207,1206,1205,1204,883,882,881,880,879,878,877,876,875,874,873,872,433,432,431,230,229,72,71,70] else [0,727,726,725,724,29,31,15,270,182,44,43,1203,1202,1201,1200,1199,1198,883,882,881,880,879,878,877,876,875,874,873,872,430,429,99,72,71,70]) else (bif Nat.ble h 214 then [0,727,726,725,724,29,15,269,132,44,43,1197,1196,1195,1194,1193,1192,1191,1190,883,882,881,880,879,878,877,876,875,874,873,872,428,427,230,229,228,72,71,70] else [0,727,726,725,724,29,181,31,15,268,107,44,43,1189,1188,883,882,881,880,879,878,877,876,875,874,873,872,426,425,99,72,71,70]))) else (bif Nat.ble h 219 then (bif Nat.ble h 217 then (bif Nat.ble h 216 then [0,727,726,725,724,29,31,15,267,44,43,1187,1186,1185,1184,1183,1182,883,882,881,880,879,878,877,876,875,874,873,872,424,423,422,421,99,72,71,70] else [0,727,726,725,724,29,31,15,107,98,44,43,1181,1180,1179,1178,1177,883,882,881,880,879,878,877,876,875,874,873,872,420,419,418,228,72,71,70]) else (bif Nat.ble h 218 then [0,727,726,725,724,15,31,44,43,1176,1175,1174,1173,1172,1171,1170,1169,1168,1167,1166,1165,1164,1163,883,882,881,880,879,878,877,876,875,874,873,872,417,416,99,72,71,70] else [0,727,726,725,724,29,180,31,15,266,98,44,43,1162,1161,1160,1159,883,882,881,880,879,878,877,876,875,874,873,872,99,72,71,70])) else (bif Nat.ble h 221 then (bif Nat.ble h 220 then [0,727,726,725,724,29,31,15,44,43,1158,1157,1156,1155,1154,1153,1152,1151,1150,1149,883,882,881,880,879,878,877,876,875,874,873,872,415,414,99,72,71,70] else [0,727,726,725,724,29,31,15,44,43,1148,1147,1146,1145,1144,1143,1142,1141,1140,1139,883,882,881,880,879,878,877,876,875,874,873,872,413,412,99,72,71,70]) else (bif Nat.ble h 222 then [0,727,726,725,724,15,31,44,43,1138,1137,1136,1135,1134,1133,1132,1131,1130,1129,1128,1127,1126,1125,1124,1123,883,882,881,880,879,878,877,876,875,874,873,872,99,72,71,70] else [0,727,726,725,724,29,179,15,265,132,107,44,43,1122,1121,883,882,881,880,879,878,877,876,875,874,873,872,411,410,230,229,228,72,71,70])))))

private def bytePage7 (h : ℕ) : List ℕ :=
  (bif Nat.ble h 239 then (bif Nat.ble h 231 then (bif Nat.ble h 227 then (bif Nat.ble h 225 then (bif Nat.ble h 224 then [752,751,750,749,719,718,717,716,69,50,49,34,113,106,176,174,112,97,1120,1119,1118,1117,1116,1115,1114,1113,1112,1111,1110,1109,1108,1107,1106,1105,1104,871,870,869,868,867,866,865,864,863,409,408,407,406,264,263,262,261,260,259,258,257,256,255,254,253,252,251,250,178,177,175] else [17,21,748,747,719,718,717,716,34,58,41,134,249,200,199,198,135,102,1103,1102,1101,1100,1099,1098,1097,1096,1095,1094,1093,1092,1091,871,870,869,868,867,866,865,864,863,405,404,403,402,401,400,399,398,397,175,97]) else (bif Nat.ble h 226 then [746,745,744,743,719,718,717,716,50,49,34,113,106,227,176,174,112,97,1090,1089,1088,1087,1086,1085,1084,1083,1082,1081,1080,1079,1078,1077,1076,1075,1074,1073,1072,1071,1070,1069,1068,871,870,869,868,867,866,865,864,863,396,395,394,393,392,391,390,389,388,387,386,264,263,262,261,260,259,258,257,256,255,254,253,252,251,250,178,177,175] else [17,21,742,741,719,718,717,716,34,58,41,134,200,199,198,135,102,1067,1066,1065,1064,1063,1062,1061,1060,1059,1058,1057,1056,1055,871,870,869,868,867,866,865,864,863,385,384,383,382,381,380,379,378,377,376,375,175,97])) else (bif Nat.ble h 229 then (bif Nat.ble h 228 then [0,719,718,717,716,102,34,17,248,247,76,50,49,1054,1053,1052,1051,1050,1049,1048,1047,1046,1045,1044,871,870,869,868,867,866,865,864,863,374,97] else [0,719,718,717,716,41,21,34,17,226,372,76,1043,1042,1041,1040,1039,1038,871,870,869,868,867,866,865,864,863,373,246]) else (bif Nat.ble h 230 then [0,719,718,717,716,50,49,34,245,112,97,1037,1036,1035,1034,1033,1032,1031,1030,1029,1028,1027,1026,1025,1024,1023,1022,1021,871,870,869,868,867,866,865,864,863,371,178,177,106] else [0,719,718,717,716,41,21,172,34,17,76,1020,1019,1018,1017,1016,1015,1014,1013,871,870,869,868,867,866,865,864,863,97]))) else (bif Nat.ble h 235 then (bif Nat.ble h 233 then (bif Nat.ble h 232 then [0,4,719,718,717,716,102,135,871,870,869,868,867,866,865,864,863,370] else [0,4,719,718,717,716,17,58,871,870,869,868,867,866,865,864,863,369]) else (bif Nat.ble h 234 then [0,4,719,718,717,716,17,58,871,870,869,868,867,866,865,864,863,173] else [0,4,719,718,717,716,17,58,871,870,869,868,867,866,865,864,863,173])) else (bif Nat.ble h 237 then (bif Nat.ble h 236 then [0,4,719,718,717,716,17,76,871,870,869,868,867,866,865,864,863,246] else [0,4,719,718,717,716,17,76,871,870,869,868,867,866,865,864,863,284]) else (bif Nat.ble h 238 then [0,4,719,718,717,716,112,97,871,870,869,868,867,866,865,864,863,178,177,106] else [0,4,719,718,717,716,17,76,871,870,869,868,867,866,865,864,863,284])))) else (bif Nat.ble h 247 then (bif Nat.ble h 243 then (bif Nat.ble h 241 then (bif Nat.ble h 240 then [707] else [706]) else (bif Nat.ble h 242 then [705] else [704])) else (bif Nat.ble h 245 then (bif Nat.ble h 244 then [0,32,811,810,68,67,244,1012,1011,1010,1009,1008,1007,1006,1005,1004,1003,1002,368,367,366,365,364,363,362] else [0,54,63,809,56,55,171,170,169,117,74,243,100,1001,1000,361,360]) else (bif Nat.ble h 246 then [0,808,807,806,805,168,167,166,242,999,998,997,996,995,994,993,992,991,990,989,988,987,986,985,984,983,982,981,980,979,978,977,976,975,974,355,354,353,352,351,350,311,310] else [0,48,804,803,56,55,165,164,74,100,973,972,971,970,969,968,967,966,965,964]))) else (bif Nat.ble h 251 then (bif Nat.ble h 249 then (bif Nat.ble h 248 then [0,4,740,739,163,115,114,225,189,100,963,962,961,960,959,958,957,956,955,954,953,952,951,358,349,348,347,346,345,344,343,342,341,340,339,338,337,336,335] else [0,53,4,62,162,240,224,241,950,949,948,947,946,945,944,943,942,357,334,333,332,331,330,187]) else (bif Nat.ble h 250 then [0,4,738,737,736,735,941,940,939,938,937,936,935,934,933,932,931,930,929,928,927,356] else [0,52,4,734,733,161,223,926,925,924,923,922,921,359,329,328])) else (bif Nat.ble h 253 then (bif Nat.ble h 252 then [0,20,4] else [0,10,4]) else (bif Nat.ble h 254 then [0,20,4] else [0,10,4])))))

def byteRows (h : ℕ) : List ℕ :=
  (bif Nat.ble h 31 then bytePage0 h else (bif Nat.ble h 63 then bytePage1 h else (bif Nat.ble h 95 then bytePage2 h else (bif Nat.ble h 127 then bytePage3 h else (bif Nat.ble h 159 then bytePage4 h else (bif Nat.ble h 191 then bytePage5 h else (bif Nat.ble h 223 then bytePage6 h else (bif Nat.ble h 255 then bytePage7 h else []))))))))

private def byteOk (h : ℕ) : Bool := byteCover rows h (byteRows h) == 2^256-1

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid0 : group0.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid1 : group1.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid2 : group2.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid3 : group3.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid4 : group4.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid5 : group5.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid6 : group6.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid7 : group7.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid8 : group8.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid9 : group9.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid10 : group10.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid11 : group11.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid12 : group12.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid13 : group13.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid14 : group14.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid15 : group15.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid16 : group16.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid17 : group17.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid18 : group18.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid19 : group19.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid20 : group20.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid21 : group21.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid22 : group22.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid23 : group23.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid24 : group24.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid25 : group25.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid26 : group26.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid27 : group27.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid28 : group28.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid29 : group29.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid30 : group30.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid31 : group31.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid32 : group32.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid33 : group33.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid34 : group34.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid35 : group35.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid36 : group36.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid37 : group37.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid38 : group38.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid39 : group39.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid40 : group40.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid41 : group41.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid42 : group42.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid43 : group43.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid44 : group44.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid45 : group45.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid46 : group46.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid47 : group47.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid48 : group48.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid49 : group49.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid50 : group50.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid51 : group51.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid52 : group52.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid53 : group53.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid54 : group54.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid55 : group55.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid56 : group56.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid57 : group57.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid58 : group58.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem valid59 : group59.all Outcome.valid = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem allRowsValid : rows.all (·.all Outcome.valid) = true := by
  simp only [rows, List.all_cons, List.all_nil, valid0,valid1,valid2,valid3,valid4,valid5,valid6,valid7,valid8,valid9,valid10,valid11,valid12,valid13,valid14,valid15,valid16,valid17,valid18,valid19,valid20,valid21,valid22,valid23,valid24,valid25,valid26,valid27,valid28,valid29,valid30,valid31,valid32,valid33,valid34,valid35,valid36,valid37,valid38,valid39,valid40,valid41,valid42,valid43,valid44,valid45,valid46,valid47,valid48,valid49,valid50,valid51,valid52,valid53,valid54,valid55,valid56,valid57,valid58,valid59, Bool.and_self]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass0 : each 8 (fun j => byteOk (0+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass1 : each 8 (fun j => byteOk (8+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass2 : each 8 (fun j => byteOk (16+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass3 : each 8 (fun j => byteOk (24+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass4 : each 8 (fun j => byteOk (32+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass5 : each 8 (fun j => byteOk (40+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass6 : each 8 (fun j => byteOk (48+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass7 : each 8 (fun j => byteOk (56+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass8 : each 8 (fun j => byteOk (64+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass9 : each 8 (fun j => byteOk (72+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass10 : each 8 (fun j => byteOk (80+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass11 : each 8 (fun j => byteOk (88+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass12 : each 8 (fun j => byteOk (96+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass13 : each 8 (fun j => byteOk (104+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass14 : each 8 (fun j => byteOk (112+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass15 : each 8 (fun j => byteOk (120+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass16 : each 8 (fun j => byteOk (128+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass17 : each 8 (fun j => byteOk (136+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass18 : each 8 (fun j => byteOk (144+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass19 : each 8 (fun j => byteOk (152+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass20 : each 8 (fun j => byteOk (160+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass21 : each 8 (fun j => byteOk (168+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass22 : each 8 (fun j => byteOk (176+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass23 : each 8 (fun j => byteOk (184+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass24 : each 8 (fun j => byteOk (192+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass25 : each 8 (fun j => byteOk (200+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass26 : each 8 (fun j => byteOk (208+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass27 : each 8 (fun j => byteOk (216+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass28 : each 8 (fun j => byteOk (224+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass29 : each 8 (fun j => byteOk (232+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass30 : each 8 (fun j => byteOk (240+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem bytePass31 : each 8 (fun j => byteOk (248+j)) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem everyByte (h : ℕ) (hb : h < 256) : byteCover rows h (byteRows h) = 2^256-1 := by
  let q := h/8
  let r := h%8
  have hq : q<32 := by dsimp [q]; omega
  have hr : r<8 := Nat.mod_lt _ (by decide)
  have eq : h = 8*q+r := by dsimp [q,r]; omega
  have packet : each 8 (fun j => byteOk (8*q+j)) = true := by
    interval_cases q
    · exact bytePass0
    · exact bytePass1
    · exact bytePass2
    · exact bytePass3
    · exact bytePass4
    · exact bytePass5
    · exact bytePass6
    · exact bytePass7
    · exact bytePass8
    · exact bytePass9
    · exact bytePass10
    · exact bytePass11
    · exact bytePass12
    · exact bytePass13
    · exact bytePass14
    · exact bytePass15
    · exact bytePass16
    · exact bytePass17
    · exact bytePass18
    · exact bytePass19
    · exact bytePass20
    · exact bytePass21
    · exact bytePass22
    · exact bytePass23
    · exact bytePass24
    · exact bytePass25
    · exact bytePass26
    · exact bytePass27
    · exact bytePass28
    · exact bytePass29
    · exact bytePass30
    · exact bytePass31
  have bit := each_of (p := fun j => byteOk (8*q+j)) packet hr
  rw [eq]
  exact beq_iff_eq.mp bit

end BlankTapeEncoding

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1_H1_R1.H2 := by
  intro b c q u
  change
    let N : Turing.BusyBeaver.Machine (Fin 2) (Fin 4) := fun r s =>
      let v : Fin 4 → Fin 4 × Turing.BusyBeaver.Stmt (Fin 2) :=
        ![(1,.write 1 .right),(2,.write 1 .right),(3,.write b .right),(q,.write c .left)]
      if s = 0 then some (some (v r).1, (v r).2)
      else if r = 0 then none else some (some (u r).1, (u r).2)
    (∃ s T, N.multiStep (Turing.BusyBeaver.Machine.init []) 107 = some ⟨some s,T⟩) →
      BlankTapeEncoding.Certifies N
  dsimp only
  rw [← BlankTapeEncoding.machine_eq b c q u]
  exact BlankTapeEncoding.byteCertificate BlankTapeEncoding.rows BlankTapeEncoding.byteRows _
    (BlankTapeEncoding.machineCode_lt b c q u)
    BlankTapeEncoding.everyByte BlankTapeEncoding.allRowsValid