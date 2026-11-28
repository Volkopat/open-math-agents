import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1

-- Reduction OeisA249609.conjecture.R1.H2.R1.H2.R1.H1.R1.H3.R1.H2.R1 of step OeisA249609.conjecture.R1.H2.R1.H2.R1.H1.R1.H3.R1.H2
-- Credit: @ehsanmok

/-!
# Columns 17, 18 and 19 for the exponent classes q = 33, 54, 68, 96 mod 105 of A249609

Here a = 3240*q+2705. Column 17 has period 680400 in a and is evil on both lifts of
the class q = 96 mod 105, which closes it. Columns 18 and 19 have period
6123600 = 2*ord(2 mod d), d the odd part of 18! or 19!. For q = 33, 54 and 68 mod 105,
these columns are evil on 15, 13 and 13 of the 18 lifts modulo 6123600. The lifts left
(q mod 1890) form the three hypotheses, one per class. The periodicity theorem is
PanPapag's from PR 5614; the fold by xor follows PR 8363, with the fold bases built
by repeated squaring.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H2_R1
open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

private def wt (n : ℕ) := (Nat.digits 2 n).count 1

private lemma half (n : ℕ) : wt n = wt (n/2) + n%2 := by
  have h := count_ones_append (n/2) 1 (n%2) (by simpa using Nat.mod_lt n (by decide : 0 < 2))
  rw [pow_one, Nat.div_add_mod'] at h
  change wt n = wt (n/2) + wt (n%2) at h
  rw [h]
  rcases (show n%2 = 0 ∨ n%2 = 1 by omega) with e|e <;> rw [e] <;> rfl

private lemma xorParity (a b : ℕ) : wt (a ^^^ b) % 2 = (wt a+wt b) % 2 := by
  induction h : a+b using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n = 0
    · have ha : a=0 := by omega
      have hb : b=0 := by omega
      subst_vars; rfl
    have hh := ih (a/2+b/2) (by omega) (a/2) (b/2) rfl
    have ha := half a
    have hb := half b
    have hab := half (a ^^^ b)
    rw [Nat.xor_div_two] at hab
    have hm := Nat.xor_mod_two_eq (m:=a) (n:=b)
    omega

/-- Fold bases 2^(8*2^j) built by repeated squaring, so the kernel never evaluates a huge power. -/
private def sqB : ℕ → ℕ
  | 0 => 256
  | j+1 => sqB j * sqB j

private lemma sqB_eq (j : ℕ) : sqB j = 2^(8*2^j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show sqB (j+1) = sqB j * sqB j from rfl, ih, ← pow_add, pow_succ]
    congr 1
    ring

private def foldB : ℕ → ℕ → ℕ
  | 0, n => wt n % 2
  | j+1, n => let base := sqB j; foldB j ((n/base) ^^^ (n%base))

private theorem foldB_exact (j n : ℕ) : foldB j n = wt n % 2 := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    simp only [foldB, ih, xorParity, sqB_eq]
    have h := count_ones_append (n/2^(8*2^j)) (8*2^j) (n%2^(8*2^j)) (Nat.mod_lt _ (by positivity))
    rw [Nat.div_add_mod'] at h
    exact congrArg (· % 2) h.symm

private def word17 : List (Bool × ℕ) := [(false, 0), (false, 20922789888000), (true, 70003205961728), (false, 102992244837119), (true, 53659739479424), (false, 48366009233423), (true, 121875921296448), (false, 5374523477959), (true, 139590587071800), (false, 185953177552), (true, 140714431195488), (false, 2185031419), (true, 140737331402896), (false, 8394021), (true, 140737488031648), (false, 8499), (true, 140737488355192), (false, 0)]

set_option maxHeartbeats 4000000 in
private theorem falling17 (x B : ℕ) (hx : 0 < x) (hB : B = 140737488355328) :
    word17.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 17 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 140737488355192) 8499) 140737488031648) 8394021) 140737331402896) 2185031419) 140714431195488) 185953177552) 139590587071800) 5374523477959) 121875921296448) 48366009233423) 53659739479424) 102992244837119) 70003205961728) 20922789888000) 0) := rfl
    _ = _ := by
      dsimp only [low,high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private def word18 : List (Bool × ℕ) := [(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)]

set_option maxHeartbeats 4000000 in
private theorem falling18 (x B : ℕ) (hx : 0 < x) (hB : B = 2251799813685248) :
    word18.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 18 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 2251799813685095) 10811) 2251799813217068) 13896581) 2251799514034442) 4853222763) 2251739610991268) 577924894832) 2247491708383319) 24871845297935) 2141571347501048) 369012649234383) 1342499907841136) 1583313975727487) 430197369060608) 1223405590579199) 1896112385589248) 0) := rfl
    _ = _ := by
      dsimp only [low,high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private def word19 : List (Bool × ℕ) := [(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)]

set_option maxHeartbeats 4000000 in
private theorem falling19 (x B : ℕ) (hx : 0 < x) (hB : B = 36028797018963968) :
    word19.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 19 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 36028797018963797) 13565) 36028797018301172) 22323821) 36028796469174686) 10246937271) 36028649458260236) 1661573386472) 36014086265555045) 102417740732657) 35470875337416920) 2353125040549983) 28477269426900944) 17950712280921503) 5707543011244544) 34012249593822719) 13651808960442368) 6402373705728000) 0) := rfl
    _ = _ := by
      dsimp only [low,high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cert18_33 (r : ℕ) (hr : r ∈ ([1130225, 1470425, 2150825, 2491025, 2831225, 3171425, 3511625, 3851825, 4872425] : List ℕ)) :
    (Nat.digits 2 ((2^r).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  change wt _ % 2 = 0
  rw [← foldB_exact 24]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem hit18_33 (t : ℕ) (ht : 51 ≤ t) (hr : (t-51)%6123600+51 ∈ ([1130225, 1470425, 2150825, 2491025, 2831225, 3171425, 3511625, 3851825, 4872425] : List ℕ)) :
    OeisA249609.isEvil ((2^t).choose 18) = true := by
  apply (periodic_column (a:=t) (k:=18) (t:=51) (l:=3061800) (d:=97692469875) (z:=16)
    (ds:=word18) ht (by decide) (by decide +kernel) (by dsimp only [word18]; decide)
    (fun e => by rw [pow_add]; exact falling18 (2^e) (2^51) (by positivity) (by decide))
    (by decide)).2
  exact cert18_33 _ hr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cert19_33 (r : ℕ) (hr : r ∈ ([449825, 790025, 1810625, 4192025, 5212625, 5552825] : List ℕ)) :
    (Nat.digits 2 ((2^r).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  change wt _ % 2 = 0
  rw [← foldB_exact 24]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem hit19_33 (t : ℕ) (ht : 55 ≤ t) (hr : (t-55)%6123600+55 ∈ ([449825, 790025, 1810625, 4192025, 5212625, 5552825] : List ℕ)) :
    OeisA249609.isEvil ((2^t).choose 19) = true := by
  apply (periodic_column (a:=t) (k:=19) (t:=55) (l:=3061800) (d:=1856156927625) (z:=16)
    (ds:=word19) ht (by decide) (by decide +kernel) (by dsimp only [word19]; decide)
    (fun e => by rw [pow_add]; exact falling19 (2^e) (2^55) (by positivity) (by decide))
    (by decide)).2
  exact cert19_33 _ hr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cert18_54 (r : ℕ) (hr : r ∈ ([1198265, 1878665, 3239465, 3579665, 3919865, 4600265, 5280665, 5620865, 5961065] : List ℕ)) :
    (Nat.digits 2 ((2^r).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  change wt _ % 2 = 0
  rw [← foldB_exact 24]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem hit18_54 (t : ℕ) (ht : 51 ≤ t) (hr : (t-51)%6123600+51 ∈ ([1198265, 1878665, 3239465, 3579665, 3919865, 4600265, 5280665, 5620865, 5961065] : List ℕ)) :
    OeisA249609.isEvil ((2^t).choose 18) = true := by
  apply (periodic_column (a:=t) (k:=18) (t:=51) (l:=3061800) (d:=97692469875) (z:=16)
    (ds:=word18) ht (by decide) (by decide +kernel) (by dsimp only [word18]; decide)
    (fun e => by rw [pow_add]; exact falling18 (2^e) (2^51) (by positivity) (by decide))
    (by decide)).2
  exact cert18_54 _ hr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cert19_54 (r : ℕ) (hr : r ∈ ([517865, 2218865, 4260065, 4940465] : List ℕ)) :
    (Nat.digits 2 ((2^r).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  change wt _ % 2 = 0
  rw [← foldB_exact 24]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem hit19_54 (t : ℕ) (ht : 55 ≤ t) (hr : (t-55)%6123600+55 ∈ ([517865, 2218865, 4260065, 4940465] : List ℕ)) :
    OeisA249609.isEvil ((2^t).choose 19) = true := by
  apply (periodic_column (a:=t) (k:=19) (t:=55) (l:=3061800) (d:=1856156927625) (z:=16)
    (ds:=word19) ht (by decide) (by decide +kernel) (by dsimp only [word19]; decide)
    (fun e => by rw [pow_add]; exact falling19 (2^e) (2^55) (by positivity) (by decide))
    (by decide)).2
  exact cert19_54 _ hr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cert18_68 (r : ℕ) (hr : r ∈ ([223025, 1583825, 1924025, 2604425, 2944625, 3625025, 3965225, 4305425, 5326025] : List ℕ)) :
    (Nat.digits 2 ((2^r).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  change wt _ % 2 = 0
  rw [← foldB_exact 24]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem hit18_68 (t : ℕ) (ht : 51 ≤ t) (hr : (t-51)%6123600+51 ∈ ([223025, 1583825, 1924025, 2604425, 2944625, 3625025, 3965225, 4305425, 5326025] : List ℕ)) :
    OeisA249609.isEvil ((2^t).choose 18) = true := by
  apply (periodic_column (a:=t) (k:=18) (t:=51) (l:=3061800) (d:=97692469875) (z:=16)
    (ds:=word18) ht (by decide) (by decide +kernel) (by dsimp only [word18]; decide)
    (fun e => by rw [pow_add]; exact falling18 (2^e) (2^51) (by positivity) (by decide))
    (by decide)).2
  exact cert18_68 _ hr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cert19_68 (r : ℕ) (hr : r ∈ ([1243625, 2264225, 3284825, 4645625] : List ℕ)) :
    (Nat.digits 2 ((2^r).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  change wt _ % 2 = 0
  rw [← foldB_exact 24]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem hit19_68 (t : ℕ) (ht : 55 ≤ t) (hr : (t-55)%6123600+55 ∈ ([1243625, 2264225, 3284825, 4645625] : List ℕ)) :
    OeisA249609.isEvil ((2^t).choose 19) = true := by
  apply (periodic_column (a:=t) (k:=19) (t:=55) (l:=3061800) (d:=1856156927625) (z:=16)
    (ds:=word19) ht (by decide) (by decide +kernel) (by dsimp only [word19]; decide)
    (fun e => by rw [pow_add]; exact falling19 (2^e) (2^55) (by positivity) (by decide))
    (by decide)).2
  exact cert19_68 _ hr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cert17_96 (r : ℕ) (hr : r ∈ ([313745, 653945] : List ℕ)) :
    (Nat.digits 2 ((2^r).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  change wt _ % 2 = 0
  rw [← foldB_exact 21]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem hit17_96 (t : ℕ) (ht : 47 ≤ t) (hr : (t-47)%680400+47 ∈ ([313745, 653945] : List ℕ)) :
    OeisA249609.isEvil ((2^t).choose 17) = true := by
  apply (periodic_column (a:=t) (k:=17) (t:=47) (l:=340200) (d:=10854718875) (z:=15)
    (ds:=word17) ht (by decide) (by decide +kernel) (by dsimp only [word17]; decide)
    (fun e => by rw [pow_add]; exact falling17 (2^e) (2^47) (by positivity) (by decide))
    (by decide)).2
  exact cert17_96 _ hr

private theorem case33
    (h : ∀ q : ℕ, q % 1890 ∈ ([33, 1398, 1818] : List ℕ) →
      ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
        OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true)
    (q : ℕ) (hq : q % 105 = 33) :
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true := by
  have hbig : 19 ≤ 2^(3240*q+2705) :=
    le_trans (by decide : 19 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
  have hm : q % 1890 = 33 + 105 * (q / 105 % 18) := by omega
  have hlt : q / 105 % 18 < 18 := Nat.mod_lt _ (by decide)
  have k18 : (3240*q+2705-51) % 6123600 + 51 = 109625 + 340200 * (q / 105 % 18) := by omega
  have k19 : (3240*q+2705-55) % 6123600 + 55 = 109625 + 340200 * (q / 105 % 18) := by omega
  generalize q / 105 % 18 = m at hm hlt k18 k19
  interval_cases m
  · exact h q (by rw [hm]; decide)
  · exact witness _ 19 (by decide) hbig (hit19_33 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_33 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_33 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_33 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_33 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_33 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_33 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_33 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_33 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_33 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_33 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_33 _ (by omega) (by rw [k19]; decide))
  · exact h q (by rw [hm]; decide)
  · exact witness _ 18 (by decide) (by omega) (hit18_33 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_33 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_33 _ (by omega) (by rw [k19]; decide))
  · exact h q (by rw [hm]; decide)

private theorem case54
    (h : ∀ q : ℕ, q % 1890 ∈ ([54, 264, 474, 789, 894] : List ℕ) →
      ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
        OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true)
    (q : ℕ) (hq : q % 105 = 54) :
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true := by
  have hbig : 19 ≤ 2^(3240*q+2705) :=
    le_trans (by decide : 19 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
  have hm : q % 1890 = 54 + 105 * (q / 105 % 18) := by omega
  have hlt : q / 105 % 18 < 18 := Nat.mod_lt _ (by decide)
  have k18 : (3240*q+2705-51) % 6123600 + 51 = 177665 + 340200 * (q / 105 % 18) := by omega
  have k19 : (3240*q+2705-55) % 6123600 + 55 = 177665 + 340200 * (q / 105 % 18) := by omega
  generalize q / 105 % 18 = m at hm hlt k18 k19
  interval_cases m
  · exact h q (by rw [hm]; decide)
  · exact witness _ 19 (by decide) hbig (hit19_54 _ (by omega) (by rw [k19]; decide))
  · exact h q (by rw [hm]; decide)
  · exact witness _ 18 (by decide) (by omega) (hit18_54 _ (by omega) (by rw [k18]; decide))
  · exact h q (by rw [hm]; decide)
  · exact witness _ 18 (by decide) (by omega) (hit18_54 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_54 _ (by omega) (by rw [k19]; decide))
  · exact h q (by rw [hm]; decide)
  · exact h q (by rw [hm]; decide)
  · exact witness _ 18 (by decide) (by omega) (hit18_54 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_54 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_54 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_54 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_54 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_54 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_54 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_54 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_54 _ (by omega) (by rw [k18]; decide))

private theorem case68
    (h : ∀ q : ℕ, q % 1890 ∈ ([173, 278, 1538, 1748, 1853] : List ℕ) →
      ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
        OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true)
    (q : ℕ) (hq : q % 105 = 68) :
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true := by
  have hbig : 19 ≤ 2^(3240*q+2705) :=
    le_trans (by decide : 19 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
  have hm : q % 1890 = 68 + 105 * (q / 105 % 18) := by omega
  have hlt : q / 105 % 18 < 18 := Nat.mod_lt _ (by decide)
  have k18 : (3240*q+2705-51) % 6123600 + 51 = 223025 + 340200 * (q / 105 % 18) := by omega
  have k19 : (3240*q+2705-55) % 6123600 + 55 = 223025 + 340200 * (q / 105 % 18) := by omega
  generalize q / 105 % 18 = m at hm hlt k18 k19
  interval_cases m
  · exact witness _ 18 (by decide) (by omega) (hit18_68 _ (by omega) (by rw [k18]; decide))
  · exact h q (by rw [hm]; decide)
  · exact h q (by rw [hm]; decide)
  · exact witness _ 19 (by decide) hbig (hit19_68 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_68 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_68 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_68 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_68 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_68 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_68 _ (by omega) (by rw [k19]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_68 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_68 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 18 (by decide) (by omega) (hit18_68 _ (by omega) (by rw [k18]; decide))
  · exact witness _ 19 (by decide) hbig (hit19_68 _ (by omega) (by rw [k19]; decide))
  · exact h q (by rw [hm]; decide)
  · exact witness _ 18 (by decide) (by omega) (hit18_68 _ (by omega) (by rw [k18]; decide))
  · exact h q (by rw [hm]; decide)
  · exact h q (by rw [hm]; decide)

private theorem case96 (q : ℕ) (hq : q % 105 = 96) :
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true :=
  witness _ 17 (by decide)
    (le_trans (by decide : 17 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega)))
    (hit17_96 _ (by omega) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega))

def H1 : Prop :=
  ∀ q : ℕ, q % 1890 ∈ ([33, 1398, 1818] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 1890 ∈ ([54, 264, 474, 789, 894] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H3 : Prop :=
  ∀ q : ℕ, q % 1890 ∈ ([173, 278, 1538, 1748, 1853] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

theorem main : H1 → H2 → H3 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1.H2 := by
  intro h1 h2 h3 q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq|hq|hq|hq
  · exact case33 h1 q hq
  · exact case54 h2 q hq
  · exact case68 h3 q hq
  · exact case96 q hq

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H2_R1
