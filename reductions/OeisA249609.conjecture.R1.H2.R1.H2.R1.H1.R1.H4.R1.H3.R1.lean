import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H4_R1
import Mathlib.Tactic

/-!
For the exponent `3240*q + 2801`, columns 18 and 19 cover 29 of the 36
relevant classes modulo 1890, including every lift of class 141 modulo 210.
The seven remaining lifts lie over classes 157, 200, and 206.

Uses PanPapag's periodic_column (PR 5614), the falling-factorial words
from PR 19959, and the XOR-fold parity argument from PR 8363.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H4_R1_H3_R1

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


/-- Assemble the fixed-width pieces of a falling factorial using shifts.
Each entry contributes a run of identical bits followed by its fixed low bits. -/
private def word (ds : List (Bool × ℕ)) (w t : ℕ) : ℕ :=
  ds.foldr (fun s v => (((v <<< w) + (if s.1 then (1 <<< w)-1 else 0)) <<< t) + s.2) 0

/-- Discard the high half after XORing it into the low half. Subtracting the
shifted high part also works when the split lies above the leading bit. -/
private def parity : ℕ → ℕ → ℕ
  | 0, n => (Nat.digits 2 n).count 1 % 2
  | j+1, n =>
    let width := 8*2^j
    let high := n >>> width
    parity j (high ^^^ (n - (high <<< width)))

private theorem parity_eq (j n : ℕ) : parity j n = (Nat.digits 2 n).count 1 % 2 := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    let w := 8*2^j
    have splitLow : n - ((n >>> w) <<< w) = n % 2^w := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mul_comm]
      have h := Nat.mod_add_div n (2^w)
      omega
    change parity j ((n >>> w) ^^^ (n - ((n >>> w) <<< w))) = _
    rw [splitLow, Nat.shiftRight_eq_div_pow, ih, xor_weight]
    have h := count_ones_append (n/2^w) w (n%2^w) (Nat.mod_lt _ (by positivity))
    rw [Nat.div_add_mod'] at h
    exact congrArg (· % 2) h.symm

/-- Reduce a column to the binary parity at its representative exponent. -/
private theorem checked_column {a k t d z l : ℕ} {ds : List (Bool × ℕ)}
    (ha : t ≤ a) (hd : 0 < d) (order : 2^l%d = 1%d)
    (digits : ∀ s ∈ ds, s.2 < 2^t)
    (assemble : ∀ w, word ds w t = (2^(w+t)).descFactorial k)
    (fac : k.factorial = d*2^z) (r : ℕ)
    (hr : r = (a-t)%(l+l)+t) (check : (Nat.digits 2 (word ds (r-t) t / d)).count 1 % 2 = 0) :
    OeisA249609.isEvil ((2^a).choose k) = true := by
  apply (periodic_column ha hd order digits (fun w => by
    simpa only [word, Nat.shiftLeft_eq, Nat.one_mul] using assemble w) fac).2
  rw [← hr]
  rw [assemble] at check
  have rt : r-t+t = r := by omega
  simpa only [rt] using check

private lemma extend_pow_mod {n r d m s : ℕ} (b : ℕ) (h : 2^n ≡ r [MOD d])
    (hm : n+n+b = m) (hs : (r*r*2^b)%d = s) : 2^m ≡ s [MOD d] := by
  subst m s
  rw [pow_add, pow_add]
  exact ((h.mul h).mul (Nat.ModEq.refl _)).trans (Nat.mod_modEq _ _).symm


private def ds18 : List (Bool × ℕ) := [(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608),
  (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true,
  2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832),
  (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581),
  (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)]

set_option maxHeartbeats 8000000 in
private theorem falling18 (x B : ℕ) (hx : 0 < x) (hB : B = 2251799813685248) :
    ds18.foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 18 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 2251799813685095) 10811) 2251799813217068) 13896581) 2251799514034442) 4853222763) 2251739610991268) 577924894832) 2247491708383319) 24871845297935) 2141571347501048) 369012649234383) 1342499907841136) 1583313975727487) 430197369060608) 1223405590579199) 1896112385589248) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem modular_order18 : (2:ℕ)^3061800 % 97692469875 = 1 % 97692469875 := by
  have h0 : (2:ℕ)^0 ≡ 1 [MOD 97692469875] := by decide
  have h1 : (2:ℕ)^1 ≡ 2 [MOD 97692469875] :=
    extend_pow_mod (n := 0) (r := 1) (d := 97692469875) (m := 1) (s := 2) 1 h0 (by decide) (by decide)
  have h2 : (2:ℕ)^2 ≡ 4 [MOD 97692469875] :=
    extend_pow_mod (n := 1) (r := 2) (d := 97692469875) (m := 2) (s := 4) 0 h1 (by decide) (by decide)
  have h5 : (2:ℕ)^5 ≡ 32 [MOD 97692469875] :=
    extend_pow_mod (n := 2) (r := 4) (d := 97692469875) (m := 5) (s := 32) 1 h2 (by decide) (by decide)
  have h11 : (2:ℕ)^11 ≡ 2048 [MOD 97692469875] :=
    extend_pow_mod (n := 5) (r := 32) (d := 97692469875) (m := 11) (s := 2048) 1 h5 (by decide) (by decide)
  have h23 : (2:ℕ)^23 ≡ 8388608 [MOD 97692469875] :=
    extend_pow_mod (n := 11) (r := 2048) (d := 97692469875) (m := 23) (s := 8388608) 1 h11 (by decide) (by decide)
  have h46 : (2:ℕ)^46 ≡ 30165867664 [MOD 97692469875] :=
    extend_pow_mod (n := 23) (r := 8388608) (d := 97692469875) (m := 46) (s := 30165867664) 0 h23 (by decide) (by decide)
  have h93 : (2:ℕ)^93 ≡ 71361718667 [MOD 97692469875] :=
    extend_pow_mod (n := 46) (r := 30165867664) (d := 97692469875) (m := 93) (s := 71361718667) 1 h46 (by decide) (by decide)
  have h186 : (2:ℕ)^186 ≡ 78850596889 [MOD 97692469875] :=
    extend_pow_mod (n := 93) (r := 71361718667) (d := 97692469875) (m := 186) (s := 78850596889) 0 h93 (by decide) (by decide)
  have h373 : (2:ℕ)^373 ≡ 85367490392 [MOD 97692469875] :=
    extend_pow_mod (n := 186) (r := 78850596889) (d := 97692469875) (m := 373) (s := 85367490392) 1 h186 (by decide) (by decide)
  have h747 : (2:ℕ)^747 ≡ 39027422078 [MOD 97692469875] :=
    extend_pow_mod (n := 373) (r := 85367490392) (d := 97692469875) (m := 747) (s := 39027422078) 1 h373 (by decide) (by decide)
  have h1495 : (2:ℕ)^1495 ≡ 89023383668 [MOD 97692469875] :=
    extend_pow_mod (n := 747) (r := 39027422078) (d := 97692469875) (m := 1495) (s := 89023383668) 1 h747 (by decide) (by decide)
  have h2990 : (2:ℕ)^2990 ≡ 82484462974 [MOD 97692469875] :=
    extend_pow_mod (n := 1495) (r := 89023383668) (d := 97692469875) (m := 2990) (s := 82484462974) 0 h1495 (by decide) (by decide)
  have h5980 : (2:ℕ)^5980 ≡ 15987711301 [MOD 97692469875] :=
    extend_pow_mod (n := 2990) (r := 82484462974) (d := 97692469875) (m := 5980) (s := 15987711301) 0 h2990 (by decide) (by decide)
  have h11960 : (2:ℕ)^11960 ≡ 43669698601 [MOD 97692469875] :=
    extend_pow_mod (n := 5980) (r := 15987711301) (d := 97692469875) (m := 11960) (s := 43669698601) 0 h5980 (by decide) (by decide)
  have h23920 : (2:ℕ)^23920 ≡ 90133808326 [MOD 97692469875] :=
    extend_pow_mod (n := 11960) (r := 43669698601) (d := 97692469875) (m := 23920) (s := 90133808326) 0 h11960 (by decide) (by decide)
  have h47840 : (2:ℕ)^47840 ≡ 54769462276 [MOD 97692469875] :=
    extend_pow_mod (n := 23920) (r := 90133808326) (d := 97692469875) (m := 47840) (s := 54769462276) 0 h23920 (by decide) (by decide)
  have h95681 : (2:ℕ)^95681 ≡ 16302014852 [MOD 97692469875] :=
    extend_pow_mod (n := 47840) (r := 54769462276) (d := 97692469875) (m := 95681) (s := 16302014852) 1 h47840 (by decide) (by decide)
  have h191362 : (2:ℕ)^191362 ≡ 44498744404 [MOD 97692469875] :=
    extend_pow_mod (n := 95681) (r := 16302014852) (d := 97692469875) (m := 191362) (s := 44498744404) 0 h95681 (by decide) (by decide)
  have h382725 : (2:ℕ)^382725 ≡ 15094420307 [MOD 97692469875] :=
    extend_pow_mod (n := 191362) (r := 44498744404) (d := 97692469875) (m := 382725) (s := 15094420307) 1 h191362 (by decide) (by decide)
  have h765450 : (2:ℕ)^765450 ≡ 73599119749 [MOD 97692469875] :=
    extend_pow_mod (n := 382725) (r := 15094420307) (d := 97692469875) (m := 765450) (s := 73599119749) 0 h382725 (by decide) (by decide)
  have h1530900 : (2:ℕ)^1530900 ≡ 11493231751 [MOD 97692469875] :=
    extend_pow_mod (n := 765450) (r := 73599119749) (d := 97692469875) (m := 1530900) (s := 11493231751) 0 h765450 (by decide) (by decide)
  have h3061800 : (2:ℕ)^3061800 ≡ 1 [MOD 97692469875] :=
    extend_pow_mod (n := 1530900) (r := 11493231751) (d := 97692469875) (m := 3061800) (s := 1) 0 h1530900 (by decide) (by decide)
  exact h3061800

private theorem assemble18 (w : ℕ) : word ds18 w 51 = (2^(w+51)).descFactorial 18 := by
  rw [pow_add]
  simpa only [word, ds18, Nat.shiftLeft_eq, Nat.one_mul] using
    falling18 (2^w) (2^51) (Nat.two_pow_pos _) rfl

private def residues18 : List ℕ :=
  [141, 200, 351, 367, 410, 416, 620, 771, 830, 836, 981, 1191, 1256, 1611, 1676, 1821, 1837,
  1880]

private def ds19 : List (Bool × ℕ) := [(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719),
  (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false,
  2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true,
  36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271),
  (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565),
  (true, 36028797018963797), (false, 0)]

set_option maxHeartbeats 8000000 in
private theorem falling19 (x B : ℕ) (hx : 0 < x) (hB : B = 36028797018963968) :
    ds19.foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 19 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 36028797018963797) 13565) 36028797018301172) 22323821) 36028796469174686) 10246937271) 36028649458260236) 1661573386472) 36014086265555045) 102417740732657) 35470875337416920) 2353125040549983) 28477269426900944) 17950712280921503) 5707543011244544) 34012249593822719) 13651808960442368) 6402373705728000) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem modular_order19 : (2:ℕ)^3061800 % 1856156927625 = 1 % 1856156927625 := by
  have h0 : (2:ℕ)^0 ≡ 1 [MOD 1856156927625] := by decide
  have h1 : (2:ℕ)^1 ≡ 2 [MOD 1856156927625] :=
    extend_pow_mod (n := 0) (r := 1) (d := 1856156927625) (m := 1) (s := 2) 1 h0 (by decide) (by decide)
  have h2 : (2:ℕ)^2 ≡ 4 [MOD 1856156927625] :=
    extend_pow_mod (n := 1) (r := 2) (d := 1856156927625) (m := 2) (s := 4) 0 h1 (by decide) (by decide)
  have h5 : (2:ℕ)^5 ≡ 32 [MOD 1856156927625] :=
    extend_pow_mod (n := 2) (r := 4) (d := 1856156927625) (m := 5) (s := 32) 1 h2 (by decide) (by decide)
  have h11 : (2:ℕ)^11 ≡ 2048 [MOD 1856156927625] :=
    extend_pow_mod (n := 5) (r := 32) (d := 1856156927625) (m := 11) (s := 2048) 1 h5 (by decide) (by decide)
  have h23 : (2:ℕ)^23 ≡ 8388608 [MOD 1856156927625] :=
    extend_pow_mod (n := 11) (r := 2048) (d := 1856156927625) (m := 23) (s := 8388608) 1 h11 (by decide) (by decide)
  have h46 : (2:ℕ)^46 ≡ 1690937855539 [MOD 1856156927625] :=
    extend_pow_mod (n := 23) (r := 8388608) (d := 1856156927625) (m := 46) (s := 1690937855539) 0 h23 (by decide) (by decide)
  have h93 : (2:ℕ)^93 ≡ 266746658417 [MOD 1856156927625] :=
    extend_pow_mod (n := 46) (r := 1690937855539) (d := 1856156927625) (m := 93) (s := 266746658417) 1 h46 (by decide) (by decide)
  have h186 : (2:ℕ)^186 ≡ 469620476389 [MOD 1856156927625] :=
    extend_pow_mod (n := 93) (r := 266746658417) (d := 1856156927625) (m := 186) (s := 469620476389) 0 h93 (by decide) (by decide)
  have h373 : (2:ℕ)^373 ≡ 1453062068642 [MOD 1856156927625] :=
    extend_pow_mod (n := 186) (r := 469620476389) (d := 1856156927625) (m := 373) (s := 1453062068642) 1 h186 (by decide) (by decide)
  have h747 : (2:ℕ)^747 ≡ 625182241328 [MOD 1856156927625] :=
    extend_pow_mod (n := 373) (r := 1453062068642) (d := 1856156927625) (m := 747) (s := 625182241328) 1 h373 (by decide) (by decide)
  have h1495 : (2:ℕ)^1495 ≡ 1749795371543 [MOD 1856156927625] :=
    extend_pow_mod (n := 747) (r := 625182241328) (d := 1856156927625) (m := 1495) (s := 1749795371543) 1 h747 (by decide) (by decide)
  have h2990 : (2:ℕ)^2990 ≡ 1352486571349 [MOD 1856156927625] :=
    extend_pow_mod (n := 1495) (r := 1749795371543) (d := 1856156927625) (m := 2990) (s := 1352486571349) 0 h1495 (by decide) (by decide)
  have h5980 : (2:ℕ)^5980 ≡ 797527470301 [MOD 1856156927625] :=
    extend_pow_mod (n := 2990) (r := 1352486571349) (d := 1856156927625) (m := 5980) (s := 797527470301) 0 h2990 (by decide) (by decide)
  have h11960 : (2:ℕ)^11960 ≡ 532132047976 [MOD 1856156927625] :=
    extend_pow_mod (n := 5980) (r := 797527470301) (d := 1856156927625) (m := 11960) (s := 532132047976) 0 h5980 (by decide) (by decide)
  have h23920 : (2:ℕ)^23920 ≡ 773981097451 [MOD 1856156927625] :=
    extend_pow_mod (n := 11960) (r := 532132047976) (d := 1856156927625) (m := 23920) (s := 773981097451) 0 h11960 (by decide) (by decide)
  have h47840 : (2:ℕ)^47840 ≡ 1617848980276 [MOD 1856156927625] :=
    extend_pow_mod (n := 23920) (r := 773981097451) (d := 1856156927625) (m := 47840) (s := 1617848980276) 0 h23920 (by decide) (by decide)
  have h95681 : (2:ℕ)^95681 ≡ 895534243727 [MOD 1856156927625] :=
    extend_pow_mod (n := 47840) (r := 1617848980276) (d := 1856156927625) (m := 95681) (s := 895534243727) 1 h47840 (by decide) (by decide)
  have h191362 : (2:ℕ)^191362 ≡ 1119115913029 [MOD 1856156927625] :=
    extend_pow_mod (n := 95681) (r := 895534243727) (d := 1856156927625) (m := 191362) (s := 1119115913029) 0 h95681 (by decide) (by decide)
  have h382725 : (2:ℕ)^382725 ≡ 992019119057 [MOD 1856156927625] :=
    extend_pow_mod (n := 191362) (r := 1119115913029) (d := 1856156927625) (m := 382725) (s := 992019119057) 1 h191362 (by decide) (by decide)
  have h765450 : (2:ℕ)^765450 ≡ 757446408874 [MOD 1856156927625] :=
    extend_pow_mod (n := 382725) (r := 992019119057) (d := 1856156927625) (m := 765450) (s := 757446408874) 0 h382725 (by decide) (by decide)
  have h1530900 : (2:ℕ)^1530900 ≡ 109185701626 [MOD 1856156927625] :=
    extend_pow_mod (n := 765450) (r := 757446408874) (d := 1856156927625) (m := 1530900) (s := 109185701626) 0 h765450 (by decide) (by decide)
  have h3061800 : (2:ℕ)^3061800 ≡ 1 [MOD 1856156927625] :=
    extend_pow_mod (n := 1530900) (r := 109185701626) (d := 1856156927625) (m := 3061800) (s := 1) 0 h1530900 (by decide) (by decide)
  exact h3061800

private theorem assemble19 (w : ℕ) : word ds19 w 55 = (2^(w+55)).descFactorial 19 := by
  rw [pow_add]
  simpa only [word, ds19, Nat.shiftLeft_eq, Nat.one_mul] using
    falling19 (2^w) (2^55) (Nat.two_pow_pos _) rfl

private def residues19 : List ℕ :=
  [157, 206, 561, 787, 997, 1040, 1250, 1401, 1417, 1627, 1670]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 30000000 in
private theorem column_parities :
    (∀ r ∈ residues18,
      (Nat.digits 2 (word ds18 (3240*r+2801-51) 51 / 97692469875)).count 1 % 2 = 0) ∧
    (∀ r ∈ residues19,
      (Nat.digits 2 (word ds19 (3240*r+2801-55) 55 / 1856156927625)).count 1 % 2 = 0) := by
  constructor
  · intro r hr
    simp only [residues18, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← parity_eq 20]
      decide +kernel
    · rw [← parity_eq 21]
      decide +kernel
    · rw [← parity_eq 22]
      decide +kernel
    · rw [← parity_eq 22]
      decide +kernel
    · rw [← parity_eq 22]
      decide +kernel
    · rw [← parity_eq 22]
      decide +kernel
    · rw [← parity_eq 23]
      decide +kernel
    · rw [← parity_eq 23]
      decide +kernel
    · rw [← parity_eq 23]
      decide +kernel
    · rw [← parity_eq 23]
      decide +kernel
    · rw [← parity_eq 23]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
  · intro r hr
    simp only [residues19, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← parity_eq 21]
      decide +kernel
    · rw [← parity_eq 21]
      decide +kernel
    · rw [← parity_eq 23]
      decide +kernel
    · rw [← parity_eq 23]
      decide +kernel
    · rw [← parity_eq 23]
      decide +kernel
    · rw [← parity_eq 23]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel
    · rw [← parity_eq 24]
      decide +kernel

private theorem column18 (q : ℕ) (hq : q % 1890 ∈ residues18) :
    OeisA249609.isEvil ((2^(3240*q+2801)).choose 18) = true := by
  apply checked_column (ds := ds18) (z := 16) (l := 3061800) (by omega) (by decide)
    modular_order18 (by decide) assemble18 (by decide) (3240*(q%1890)+2801) (by omega)
  exact column_parities.1 _ hq

private theorem column19 (q : ℕ) (hq : q % 1890 ∈ residues19) :
    OeisA249609.isEvil ((2^(3240*q+2801)).choose 19) = true := by
  apply checked_column (ds := ds19) (z := 16) (l := 3061800) (by omega) (by decide)
    modular_order19 (by decide) assemble19 (by decide) (3240*(q%1890)+2801) (by omega)
  exact column_parities.2 _ hq

private def remaining1 : List ℕ := [577, 1207]
private def remaining2 : List ℕ := [1460]
private def remaining3 : List ℕ := [626, 1046, 1466, 1886]

private def originalClass (i : Fin 4) : ℕ := ([141, 157, 200, 206] : List ℕ)[i.val]!

/-- Each original class has nine lifts in the common period of both columns. -/
private theorem cover : ∀ (i : Fin 4) (j : Fin 9),
    let r := 210*j.val + originalClass i
    r ∈ residues18 ∨ r ∈ residues19 ∨
      r ∈ remaining1 ∨ r ∈ remaining2 ∨ r ∈ remaining3 := by
  decide +kernel

private theorem witness {q k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 32)
    (h : OeisA249609.isEvil ((2^(3240*q+2801)).choose k) = true) :
    ∃ j ∈ List.range' 1 (2^(3240*q+2801)),
      OeisA249609.isEvil ((2^(3240*q+2801)).choose j) = true := by
  have bound := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 3240*q+2801 by omega)
  exact ⟨k, List.mem_range'_1.mpr ⟨hk, by omega⟩, h⟩

/-- The surviving lifts of class 157 modulo 210. -/
def H1 : Prop :=
  ∀ q : ℕ, q % 1890 ∈ ([577, 1207] : List ℕ) →
    ∃ k ∈ List.range' 1 (2^(3240*q+2801)),
      OeisA249609.isEvil ((2^(3240*q+2801)).choose k) = true

/-- The surviving lifts of class 200 modulo 210. -/
def H2 : Prop :=
  ∀ q : ℕ, q % 1890 ∈ ([1460] : List ℕ) →
    ∃ k ∈ List.range' 1 (2^(3240*q+2801)),
      OeisA249609.isEvil ((2^(3240*q+2801)).choose k) = true

/-- The surviving lifts of class 206 modulo 210. -/
def H3 : Prop :=
  ∀ q : ℕ, q % 1890 ∈ ([626, 1046, 1466, 1886] : List ℕ) →
    ∃ k ∈ List.range' 1 (2^(3240*q+2801)),
      OeisA249609.isEvil ((2^(3240*q+2801)).choose k) = true

theorem main : H1 → H2 → H3 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H4_R1.H3 := by
  intro h157 h200 h206 q hq
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, q % 210 = originalClass i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  let j : Fin 9 := ⟨(q/210)%9, Nat.mod_lt _ (by decide)⟩
  have he : 210*j.val + originalClass i = q % 1890 := by
    dsimp only [j]
    rw [← hi]
    have h := Nat.mod_add_div q 210
    have h' := Nat.mod_add_div (q/210) 9
    omega
  have h := cover i j
  dsimp only at h
  rw [he] at h
  rcases h with h | h | h | h | h
  · exact witness (by decide) (by decide) (column18 q h)
  · exact witness (by decide) (by decide) (column19 q h)
  · exact h157 q h
  · exact h200 q h
  · exact h206 q h

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H4_R1_H3_R1
