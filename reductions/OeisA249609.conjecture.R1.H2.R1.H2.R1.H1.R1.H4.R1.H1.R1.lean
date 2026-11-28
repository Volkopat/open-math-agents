import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H4_R1
import Mathlib.Tactic

/-!
Columns 18 and 19 certify 35 of the 45 lifts modulo 1890. Column 20
certifies 25 of the 50 lifts modulo 9450 left by those columns.
The periodicity lemma comes from the merged ancestor. The quotient's
binary digit sum is certified by xor-folding its base-`2^a` digits.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H4_R1_H1_R1
open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

private theorem weight_half (n : ℕ) :
    (Nat.digits 2 n).count 1 = (Nat.digits 2 (n/2)).count 1 + n%2 := by
  have hh := count_ones_append (n/2) 1 (n%2) (by simpa using Nat.mod_lt n (by decide : 0 < 2))
  rw [pow_one, Nat.div_add_mod'] at hh
  change (Nat.digits 2 n).count 1 = (Nat.digits 2 (n / 2)).count 1 + (Nat.digits 2 (n % 2)).count 1 at hh
  rw [hh]
  have h : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> rfl

private theorem xor_weight (a b : ℕ) : (Nat.digits 2 (a ^^^ b)).count 1 % 2 = ((Nat.digits 2 a).count 1 + (Nat.digits 2 b).count 1) % 2 := by
  induction h : a+b using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hzero : n = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a; subst b; rfl
    have half := ih (a/2+b/2) (by omega) (a/2) (b/2) rfl
    have ha := weight_half a
    have hb := weight_half b
    have hab := weight_half (a ^^^ b)
    rw [Nat.xor_div_two] at hab
    have hmod := Nat.xor_mod_two_eq (m := a) (n := b)
    omega

/-- Folding the two halves with xor preserves the parity and halves the bit width. -/
private theorem fold_certificate (i n : ℕ) (h :
    (Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := (1 : ℕ) <<< (8 * 2^j); f ((v / base) ^^^ (v % base))) i n) = 0) :
    (Nat.digits 2 n).count 1 % 2 = 0 := by
  let count := Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := (1 : ℕ) <<< (8 * 2^j); f ((v / base) ^^^ (v % base)))
  have spec (j v : ℕ) : count j v = (Nat.digits 2 v).count 1 % 2 := by
    induction j generalizing v with
    | zero => rfl
    | succ j ih =>
      let w := 8*2^j
      change count j ((v / (1 <<< w)) ^^^ (v % (1 <<< w))) = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      rw [ih,xor_weight]
      have hh := count_ones_append (v / 2^w) w (v%2^w) (Nat.mod_lt _ (by positivity))
      rw [Nat.div_add_mod'] at hh
      exact congrArg (· % 2) hh.symm
  exact (spec i n).symm.trans h


private def appendDigit (w t : ℕ) (s : Bool × ℕ) (v : ℕ) : ℕ :=
  (((v <<< w) + (if s.1 then (1 <<< w) - 1 else 0)) <<< t) + s.2

private def divisionStep (w t d : ℕ) (s : Bool × ℕ) (state : ℕ × ℕ) : ℕ × ℕ :=
  let v := appendDigit w t s state.1
  (v % d, state.2 ^^^ (v / d))

/-- Concatenating a digit adds the quotient parity from dividing that digit with
the incoming remainder. Accumulating the quotient blocks by xor makes the
final parity certificate use only one digit's width. -/
private theorem divisionFold (w t d : ℕ) (hd : 0 < d) (ds : List (Bool × ℕ))
    (hc : ∀ s ∈ ds, s.2 < 2^t) :
    let word := ds.foldr (appendDigit w t) 0
    let state := ds.foldr (divisionStep w t d) (0, 0)
    state.1 = word % d ∧
      (Nat.digits 2 state.2).count 1 % 2 = (Nat.digits 2 (word / d)).count 1 % 2 := by
  induction ds with
  | nil => simp [Nat.digits]
  | cons s ds ih =>
    obtain ⟨b, c⟩ := s
    have hsmall := hc (b, c) (by simp)
    have ⟨hrem, hpar⟩ := ih (fun s hs => hc s (List.mem_cons_of_mem _ hs))
    let word := ds.foldr (appendDigit w t) 0
    let state := ds.foldr (divisionStep w t d) (0, 0)
    change state.1 = word % d at hrem
    change (Nat.digits 2 state.2).count 1 % 2 = (Nat.digits 2 (word / d)).count 1 % 2 at hpar
    let fill : ℕ := if b then 2^w - 1 else 0
    let suffix := fill * 2^t + c
    have hf : fill < 2^w := by
      cases b
      · exact Nat.two_pow_pos w
      · exact Nat.sub_lt (Nat.two_pow_pos w) (by decide)
    have hsuffix : suffix < 2^(w+t) := by
      rw [pow_add]
      have hm := Nat.mul_le_mul_right (2^t) (Nat.succ_le_of_lt hf)
      rw [Nat.succ_mul] at hm
      dsimp only [suffix]
      omega
    have hjoin (v : ℕ) : appendDigit w t (b,c) v = v * 2^(w+t) + suffix := by
      simp only [appendDigit, Nat.shiftLeft_eq, Nat.one_mul, pow_add, fill, suffix,
        Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    let part := word % d * 2^(w+t) + suffix
    have hword : word * 2^(w+t) + suffix = part + (word/d * 2^(w+t))*d := by
      dsimp only [part]
      calc
        word * 2^(w+t) + suffix = (word%d+d*(word/d))*2^(w+t)+suffix := by
          rw [Nat.mod_add_div]
        _ = _ := by ring
    have hpart : part / d < 2^(w+t) := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      have hm := Nat.mul_le_mul_right (2^(w+t)) (Nat.succ_le_of_lt (Nat.mod_lt word hd))
      rw [Nat.succ_mul, Nat.mul_comm d] at hm
      dsimp only [part]
      omega
    change appendDigit w t (b,c) state.1 % d = appendDigit w t (b,c) word % d ∧
      (Nat.digits 2 (state.2 ^^^ (appendDigit w t (b,c) state.1 / d))).count 1 % 2 =
        (Nat.digits 2 (appendDigit w t (b,c) word / d)).count 1 % 2
    rw [hjoin word, hjoin state.1, hrem]
    change part % d = (word * 2^(w+t) + suffix) % d ∧
      (Nat.digits 2 (state.2 ^^^ (part / d))).count 1 % 2 =
        (Nat.digits 2 ((word * 2^(w+t) + suffix) / d)).count 1 % 2
    rw [hword, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hd, xor_weight]
    rw [Nat.add_comm (part / d), count_ones_append _ _ _ hpart]
    exact ⟨rfl, by omega⟩

private theorem divideCertificate {w t d k : ℕ} {ds : List (Bool × ℕ)}
    (hd : 0 < d) (hc : ∀ s ∈ ds, s.2 < 2^t)
    (hw : ds.foldr (fun s n => (n * 2^w + (if s.1 then 2^w-1 else 0))*2^t+s.2) 0 =
      (2^(w+t)).descFactorial k)
    (h : (Nat.digits 2 (ds.foldr (divisionStep w t d) (0, 0)).2).count 1 % 2 = 0) :
    (Nat.digits 2 ((2^(w+t)).descFactorial k / d)).count 1 % 2 = 0 := by
  have hp := (divisionFold w t d hd ds hc).2
  unfold appendDigit at hp
  simp only [Nat.shiftLeft_eq, Nat.one_mul, hw] at hp
  exact hp.symm.trans h

private theorem certifyColumn {q k t d z l m : ℕ} {ds : List (Bool × ℕ)} {rs : List ℕ}
    (ht : t ≤ 2801) (hd : 0 < d) (hm : 2^l%d=1%d) (hc : ∀ s ∈ ds, s.2 < 2^t)
    (hw : ∀ w : ℕ, ds.foldr (fun s n => (n * 2^w + (if s.1 then 2^w-1 else 0))*2^t+s.2) 0 =
      (2^(w+t)).descFactorial k)
    (hf : k.factorial = d * 2^z) (hperiod : l+l = 3240*m) (hpos : 0 < m) (hr : q%m ∈ rs)
    (hpar : ∀ r ∈ rs,
      (Nat.digits 2 (ds.foldr (divisionStep (3240*r+2801-t) t d) (0, 0)).2).count 1 % 2 = 0) :
    OeisA249609.isEvil ((2^(3240*q+2801)).choose k) = true := by
  apply (periodic_column (ds := ds) (by omega) hd hm hc hw hf).2
  rw [show (3240*q+2801-t)%(l+l) = 3240*(q%m)+2801-t by
    have hlt := Nat.mod_lt q hpos
    have hdecomp := Nat.mod_add_div q m
    have he : (3240*q+2801-t) = (3240*(q%m)+2801-t) + (l+l)*(q/m) := by
      rw [hperiod, mul_assoc]
      omega
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]]
  exact divideCertificate hd hc (hw _) (hpar _ hr)

private def digits18 : List (Bool × ℕ) :=
  [(false, 0), (true, 1896112385589248), (false, 1223405590579199),
   (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136),
   (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935),
   (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268),
   (false, 4853222763), (true, 2251799514034442), (false, 13896581),
   (true, 2251799813217068), (false, 10811), (true, 2251799813685095),
   (false, 0)]

private def residues18 : List ℕ :=
  [214, 274, 276, 437, 451, 486, 634, 647, 661,
   694, 696, 844, 857, 871, 904, 1067, 1081, 1116,
   1264, 1324, 1326, 1474, 1501, 1711, 1744]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem falling18 (x B : ℕ) (hx : 0 < x) (hB : B = 2251799813685248) :
    digits18.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 18 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 2251799813685095) 10811) 2251799813217068) 13896581) 2251799514034442) 4853222763) 2251739610991268) 577924894832) 2247491708383319) 24871845297935) 2141571347501048) 369012649234383) 1342499907841136) 1583313975727487) 430197369060608) 1223405590579199) 1896112385589248) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hit18 (q : ℕ) (hr : q % 1890 ∈ residues18) :
    OeisA249609.isEvil ((2^(3240*q+2801)).choose 18) = true := by
  refine certifyColumn (t:=51) (d:=97692469875) (l:=3061800) (z:=16) (ds:=digits18)
    (by decide) (by decide) (by decide +kernel) (by decide) ?_ (by decide) (by decide)
    (by decide) hr ?_
  · intro w
    rw [pow_add]
    exact falling18 (2^w) (2^51) (by positivity) (by decide)
  · intro r hrs
    simp only [residues18, List.mem_cons, List.not_mem_nil, or_false] at hrs
    rcases hrs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply fold_certificate 20 <;> decide +kernel

private def digits19 : List (Bool × ℕ) :=
  [(false, 0), (false, 6402373705728000), (true, 13651808960442368),
   (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503),
   (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920),
   (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472),
   (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686),
   (false, 22323821), (true, 36028797018301172), (false, 13565),
   (true, 36028797018963797), (false, 0)]

private def residues19 : List ℕ :=
  [4, 17, 31, 64, 66, 241, 484, 1291, 1534,
   1684]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem falling19 (x B : ℕ) (hx : 0 < x) (hB : B = 36028797018963968) :
    digits19.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 19 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 36028797018963797) 13565) 36028797018301172) 22323821) 36028796469174686) 10246937271) 36028649458260236) 1661573386472) 36014086265555045) 102417740732657) 35470875337416920) 2353125040549983) 28477269426900944) 17950712280921503) 5707543011244544) 34012249593822719) 13651808960442368) 6402373705728000) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hit19 (q : ℕ) (hr : q % 1890 ∈ residues19) :
    OeisA249609.isEvil ((2^(3240*q+2801)).choose 19) = true := by
  refine certifyColumn (t:=55) (d:=1856156927625) (l:=3061800) (z:=16) (ds:=digits19)
    (by decide) (by decide) (by decide +kernel) (by decide) ?_ (by decide) (by decide)
    (by decide) hr ?_
  · intro w
    rw [pow_add]
    exact falling19 (2^w) (2^55) (by positivity) (by decide)
  · intro r hrs
    simp only [residues19, List.mem_cons, List.not_mem_nil, or_false] at hrs
    rcases hrs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply fold_certificate 20 <;> decide +kernel

private def digits20 : List (Bool × ℕ) :=
  [(false, 0), (true, 1031276404198014976), (false, 431565146817638399),
   (true, 484311774265693696), (false, 610116075740491775), (true, 781536717261618976),
   (false, 161429736530118959), (true, 1100660601244334256), (false, 12953636989943895),
   (true, 1150417645851379426), (false, 381922055502194), (true, 1152875223959095066),
   (false, 4465226757380), (true, 1152921162354335076), (false, 20692933629),
   (true, 1152921503632905076), (false, 34916945), (true, 1152921504605926426),
   (false, 16814), (true, 1152921504606846786), (false, 0)]

private def residues20 : List ℕ :=
  [906, 1054, 1114, 1277, 1487, 1746, 2117, 2314, 3167,
   3426, 3636, 4686, 5267, 5526, 5897, 6094, 6947, 7206,
   7367, 7416, 7787, 7984, 9047, 9257, 9306]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem falling20 (x B : ℕ) (hx : 0 < x) (hB : B = 1152921504606846976) :
    digits20.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 20 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 1152921504606846786) 16814) 1152921504605926426) 34916945) 1152921503632905076) 20692933629) 1152921162354335076) 4465226757380) 1152875223959095066) 381922055502194) 1150417645851379426) 12953636989943895) 1100660601244334256) 161429736530118959) 781536717261618976) 610116075740491775) 484311774265693696) 431565146817638399) 1031276404198014976) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hit20 (q : ℕ) (hr : q % 9450 ∈ residues20) :
    OeisA249609.isEvil ((2^(3240*q+2801)).choose 20) = true := by
  refine certifyColumn (t:=60) (d:=9280784638125) (l:=15309000) (z:=18) (ds:=digits20)
    (by decide) (by decide) (by decide +kernel) (by decide) ?_ (by decide) (by decide)
    (by decide) hr ?_
  · intro w
    rw [pow_add]
    exact falling20 (2^w) (2^60) (by positivity) (by decide)
  · intro r hrs
    simp only [residues20, List.mem_cons, List.not_mem_nil, or_false] at hrs
    rcases hrs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply fold_certificate 22 <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem coverage (q : ℕ) (hq : q%210 ∈ ([4, 17, 31, 64, 66] : List ℕ)) :
    q%1890 ∈ residues18 ∨ q%1890 ∈ residues19 ∨ q%9450 ∈ residues20 ∨
      q%9450 ∈ ([227, 424, 1697, 2944, 3377, 3587, 4007, 4204, 4834,
   5057, 5477, 6724, 7157, 8614, 8837] : List ℕ) ∨
      q%9450 ∈ ([1536, 2796, 3004, 4894, 5316, 6576, 6784, 8466, 8674,
   9096] : List ℕ) := by
  have finite (r : Fin 45) :
      ∀ s ∈ ([4, 17, 31, 64, 66] : List ℕ),
        (s+210*r.val)%1890 ∈ residues18 ∨ (s+210*r.val)%1890 ∈ residues19 ∨
        (s+210*r.val)%9450 ∈ residues20 ∨
        (s+210*r.val)%9450 ∈ ([227, 424, 1697, 2944, 3377, 3587, 4007, 4204, 4834,
   5057, 5477, 6724, 7157, 8614, 8837] : List ℕ) ∨
        (s+210*r.val)%9450 ∈ ([1536, 2796, 3004, 4894, 5316, 6576, 6784, 8466, 8674,
   9096] : List ℕ) := by
    revert r
    decide +kernel
  have lift : q%210 + 210*((q/210)%45) = q%9450 := by omega
  have h := finite ⟨(q/210)%45, Nat.mod_lt _ (by decide)⟩ (q%210) hq
  dsimp only at h
  rw [lift, Nat.mod_mod_of_dvd q (by decide : 1890 ∣ 9450),
    Nat.mod_mod_of_dvd q (by decide : 9450 ∣ 9450)] at h
  exact h

def H1 : Prop :=
  ∀ q : ℕ, q % 9450 ∈ ([227, 424, 1697, 2944, 3377, 3587, 4007, 4204, 4834,
   5057, 5477, 6724, 7157, 8614, 8837] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2801)),
      OeisA249609.isEvil ((2 ^ (3240*q+2801)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 9450 ∈ ([1536, 2796, 3004, 4894, 5316, 6576, 6784, 8466, 8674,
   9096] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2801)),
      OeisA249609.isEvil ((2 ^ (3240*q+2801)).choose k) = true

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H4_R1.H1 := by
  intro h1 h2 q hq
  have hbig : 32 ≤ 2^(3240*q+2801) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 3240*q+2801 by omega)
  rcases coverage q hq with h | h | h | h | h
  · exact witness _ 18 (by decide) (by omega) (hit18 q h)
  · exact witness _ 19 (by decide) (by omega) (hit19 q h)
  · exact witness _ 20 (by decide) (by omega) (hit20 q h)
  · exact h1 q h
  · exact h2 q h

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H4_R1_H1_R1
