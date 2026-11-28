import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1
import Mathlib.Tactic

/-! Columns 18 and 19. Reuses PanPapag’s periodic_column and the xor-fold certificate of the merged ancestor (PR 8363). -/
namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R1
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem falling18 (x B : ℕ) (hx : 0 < x) (hB : B = 2251799813685248) :
    ([(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)] : List (Bool × ℕ)).foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
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
set_option maxHeartbeats 5000000 in
private theorem hit18 (a : ℕ) (ha : 51 ≤ a)
    (hr : (a-51)%6123600+51 ∈ ([25385, 705785, 1726385, 2066585, 2406785, 2746985, 3427385, 4107785, 4447985, 751145, 1771745, 2111945, 3812945, 4833545, 5173745] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 18) = true := by
  apply (periodic_column (a:=a) (k:=18) (t:=51) (l:=3061800) (d:=97692469875) (z:=16)
    (ds:=([(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)] : List (Bool × ℕ))) ha (by decide) (by decide +kernel) (by decide)
    (fun w => by rw [pow_add]; exact falling18 (2^w) (2^51) (by positivity) (by decide))
    (by decide)).2
  suffices cert : ∀ r : ℕ, r ∈ ([25385, 705785, 1726385, 2066585, 2406785, 2746985, 3427385, 4107785, 4447985, 751145, 1771745, 2111945, 3812945, 4833545, 5173745] : List ℕ) → (Nat.digits 2 ((2^r).descFactorial 18 / 97692469875)).count 1 % 2 = 0 by exact cert _ hr
  intro r hrs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrs
  rcases hrs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> apply fold_certificate 24 <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem falling19 (x B : ℕ) (hx : 0 < x) (hB : B = 36028797018963968) :
    ([(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)] : List (Bool × ℕ)).foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
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
set_option maxHeartbeats 5000000 in
private theorem hit19 (a : ℕ) (ha : 55 ≤ a)
    (hr : (a-55)%6123600+55 ∈ ([365585, 1045985, 1386185, 4788185, 5128385, 70745, 410945, 1431545, 2452145, 4153145, 5854145] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 19) = true := by
  apply (periodic_column (a:=a) (k:=19) (t:=55) (l:=3061800) (d:=1856156927625) (z:=16)
    (ds:=([(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)] : List (Bool × ℕ))) ha (by decide) (by decide +kernel) (by decide)
    (fun w => by rw [pow_add]; exact falling19 (2^w) (2^55) (by positivity) (by decide))
    (by decide)).2
  suffices cert : ∀ r : ℕ, r ∈ ([365585, 1045985, 1386185, 4788185, 5128385, 70745, 410945, 1431545, 2452145, 4153145, 5854145] : List ℕ) → (Nat.digits 2 ((2^r).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 by exact cert _ hr
  intro r hrs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrs
  rcases hrs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> apply fold_certificate 24 <;> decide +kernel

def H1 : Prop :=
  ∀ q : ℕ, q % 1890 ∈ ([952, 1162, 1687, 1792] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)), OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 1890 ∈ ([336, 861, 966, 1071, 1386, 1701] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)), OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

lemma quotient_cases (q : ℕ) : (q/105)%18 = 0 ∨ (q/105)%18 = 1 ∨ (q/105)%18 = 2 ∨ (q/105)%18 = 3 ∨ (q/105)%18 = 4 ∨ (q/105)%18 = 5 ∨ (q/105)%18 = 6 ∨ (q/105)%18 = 7 ∨ (q/105)%18 = 8 ∨ (q/105)%18 = 9 ∨ (q/105)%18 = 10 ∨ (q/105)%18 = 11 ∨ (q/105)%18 = 12 ∨ (q/105)%18 = 13 ∨ (q/105)%18 = 14 ∨ (q/105)%18 = 15 ∨ (q/105)%18 = 16 ∨ (q/105)%18 = 17 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1.H1 := by
  intro h1 h2 q hq
  have choose18 (hr : (3240*q+2705-51)%6123600+51 ∈ ([25385, 705785, 1726385, 2066585, 2406785, 2746985, 3427385, 4107785, 4447985, 751145, 1771745, 2111945, 3812945, 4833545, 5173745] : List ℕ)) : ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)), OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true := by
    refine ⟨18, List.mem_range'_1.mpr ⟨by decide, ?_⟩, hit18 _ (by omega) hr⟩
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 3240*q+2705 by omega)
    omega
  have choose19 (hr : (3240*q+2705-55)%6123600+55 ∈ ([365585, 1045985, 1386185, 4788185, 5128385, 70745, 410945, 1431545, 2452145, 4153145, 5854145] : List ℕ)) : ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)), OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true := by
    refine ⟨19, List.mem_range'_1.mpr ⟨by decide, ?_⟩, hit19 _ (by omega) hr⟩
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 3240*q+2705 by omega)
    omega
  have e := Nat.mod_add_div q 105
  have f := Nat.mod_add_div (q/105) 18
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  have cases18 := quotient_cases q
  rcases hq with hq|hq
  · rcases cases18 with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 25385 by omega]
      decide
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 365585 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 705785 by omega]
      decide
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 1045985 by omega]
      decide
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 1386185 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 1726385 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 2066585 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 2406785 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 2746985 by omega]
      decide
    · apply h1 q
      rw [show q%1890 = 952 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 3427385 by omega]
      decide
    · apply h1 q
      rw [show q%1890 = 1162 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 4107785 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 4447985 by omega]
      decide
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 4788185 by omega]
      decide
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 5128385 by omega]
      decide
    · apply h1 q
      rw [show q%1890 = 1687 by omega]
      decide
    · apply h1 q
      rw [show q%1890 = 1792 by omega]
      decide
  · rcases cases18 with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 70745 by omega]
      decide
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 410945 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 751145 by omega]
      decide
    · apply h2 q
      rw [show q%1890 = 336 by omega]
      decide
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 1431545 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 1771745 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 2111945 by omega]
      decide
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 2452145 by omega]
      decide
    · apply h2 q
      rw [show q%1890 = 861 by omega]
      decide
    · apply h2 q
      rw [show q%1890 = 966 by omega]
      decide
    · apply h2 q
      rw [show q%1890 = 1071 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 3812945 by omega]
      decide
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 4153145 by omega]
      decide
    · apply h2 q
      rw [show q%1890 = 1386 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 4833545 by omega]
      decide
    · apply choose18
      rw [show (3240*q+2705-51)%6123600+51 = 5173745 by omega]
      decide
    · apply h2 q
      rw [show q%1890 = 1701 by omega]
      decide
    · apply choose19
      rw [show (3240*q+2705-55)%6123600+55 = 5854145 by omega]
      decide

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R1
