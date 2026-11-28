import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1
import Mathlib.Tactic

/-!
Pascal rows indexed by powers of two in the four remaining classes
q = 0, 23, 30 or 84 modulo 105. Columns 18 and 19 settle 51 of
their 72 residue classes modulo 1890. The hypotheses concern the
remaining even and odd residues. They make no assertion about the
other rows of Pascal's triangle.

I use PanPapag's periodic_column from PR 5614 and the fixed-column
polynomial and xor-fold identities from the previously merged
column-18/19 proof (including the kernel-shift update by @FransDevelopment) for the separate exponent family 3240*q+2705.
The certificate residues below are for 3240*q+209.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1

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
private theorem hit18 (q : ℕ) (hq : q % 1890 ∈ ([30, 105, 128, 135, 233, 338, 345, 420, 504, 609, 630, 653, 660, 714, 765, 819, 975, 1050, 1073, 1080, 1178, 1283, 1290, 1365, 1449, 1554, 1575, 1598, 1605, 1659, 1710, 1764] : List ℕ)) :
    OeisA249609.isEvil ((2^(3240*q+209)).choose 18) = true := by
  apply (periodic_column (a:=(3240*q+209)) (k:=18) (t:=51) (l:=3061800) (d:=97692469875) (z:=16)
    (ds:=([(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)] : List (Bool × ℕ))) (by omega) (by decide) (by decide +kernel) (by decide)
    (fun w => by rw [pow_add]; exact falling18 (2^w) (2^51) (by positivity) (by decide))
    (by decide)).2
  rw [show ((3240*q+209)-51)%(3061800+3061800)+51 = 3240*(q%1890)+209 by omega]
  generalize q % 1890 = r at hq ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> apply fold_certificate 24 <;> decide +kernel

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
private theorem hit19 (q : ℕ) (hq : q % 1890 ∈ ([23, 84, 189, 315, 548, 555, 735, 758, 840, 863, 924, 945, 1029, 1134, 1155, 1388, 1470, 1500, 1869] : List ℕ)) :
    OeisA249609.isEvil ((2^(3240*q+209)).choose 19) = true := by
  apply (periodic_column (a:=(3240*q+209)) (k:=19) (t:=55) (l:=3061800) (d:=1856156927625) (z:=16)
    (ds:=([(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)] : List (Bool × ℕ))) (by omega) (by decide) (by decide +kernel) (by decide)
    (fun w => by rw [pow_add]; exact falling19 (2^w) (2^55) (by positivity) (by decide))
    (by decide)).2
  rw [show ((3240*q+209)-55)%(3061800+3061800)+55 = 3240*(q%1890)+209 by omega]
  generalize q % 1890 = r at hq ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> apply fold_certificate 24 <;> decide +kernel

def H1 : Prop := ∀ q : ℕ, q % 1890 ∈ ([0, 210, 240, 294, 450, 870, 968, 1260, 1344, 1680, 1808] : List ℕ) →
  ∃ k ∈ List.range' 1 (2 ^ (3240*q+209)),
    OeisA249609.isEvil ((2 ^ (3240*q+209)).choose k) = true

def H2 : Prop := ∀ q : ℕ, q % 1890 ∈ ([399, 443, 525, 1185, 1239, 1395, 1493, 1703, 1785, 1815] : List ℕ) →
  ∃ k ∈ List.range' 1 (2 ^ (3240*q+209)),
    OeisA249609.isEvil ((2 ^ (3240*q+209)).choose k) = true

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1.H1 := by
  intro heven hodd q hq
  have cover : ∀ i : Fin 1890, i.val % 105 ∈ ([0, 23, 30, 84] : List ℕ) →
      i.val ∈ ([0, 210, 240, 294, 450, 870, 968, 1260, 1344, 1680, 1808] : List ℕ) ∨
      i.val ∈ ([399, 443, 525, 1185, 1239, 1395, 1493, 1703, 1785, 1815] : List ℕ) ∨
      i.val ∈ ([30, 105, 128, 135, 233, 338, 345, 420, 504, 609, 630, 653, 660, 714, 765, 819, 975, 1050, 1073, 1080, 1178, 1283, 1290, 1365, 1449, 1554, 1575, 1598, 1605, 1659, 1710, 1764] : List ℕ) ∨
      i.val ∈ ([23, 84, 189, 315, 548, 555, 735, 758, 840, 863, 924, 945, 1029, 1134, 1155, 1388, 1470, 1500, 1869] : List ℕ) := by
    set_option maxRecDepth 8000 in decide +kernel
  have hm : (q%1890)%105 = q%105 := Nat.mod_mod_of_dvd q (by decide)
  rcases cover ⟨q%1890, Nat.mod_lt _ (by decide)⟩ (hm ▸ hq) with h|h|h|h
  · exact heven q h
  · exact hodd q h
  · refine ⟨18, List.mem_range'_1.mpr ⟨by decide, ?_⟩, hit18 q h⟩
    have ht := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 3240*q+209 by omega)
    omega
  · refine ⟨19, List.mem_range'_1.mpr ⟨by decide, ?_⟩, hit19 q h⟩
    have ht := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 3240*q+209 by omega)
    omega

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1
