import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1

-- Reduction OeisA249609.conjecture.R1.H2.R1.H2.R1.H1.R1.H1.R1.H3.R1 of step OeisA249609.conjecture.R1.H2.R1.H2.R1.H1.R1.H1.R1.H3
-- Credit: @wtho704

/-!
# Even binary digit sums in binomial rows with exponent 3240q + 209

In the three classes 29, 42 and 52 modulo 105, columns 18 and 19 cover 46 of
the 54 lifts modulo 1890. Column 20 covers another 27 of the 40 remaining
lifts modulo 9450. The two hypotheses list the thirteen survivors. The whole
class 52 modulo 105 is proved below without either hypothesis.

The periodicity theorem is PanPapag's (PR 5614). The falling-factorial words
and modular-order certificates are adapted from connoranderson (PR 17944).
The XOR parity argument goes back to the merged reduction in PR 8363.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1

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

/-- Append a single base-2^(w+t) digit to the prefix. Its first w bits all
have the same value, and its last t bits are fixed. -/
private def appendDigit (w t : ℕ) (s : Bool × ℕ) (n : ℕ) : ℕ :=
  (((n <<< w) + (if s.1 then (1 <<< w)-1 else 0)) <<< t) + s.2

private theorem append_size (w t : ℕ) (s : Bool × ℕ) (hs : s.2 < 2^t) :
    appendDigit w t s 0 < 2^(w+t) := by
  let f := if s.1 then (1 <<< w)-1 else 0
  have hf : f < 2^w := by
    have hp := Nat.two_pow_pos w
    cases e : s.1 <;> simp [f, e, Nat.shiftLeft_eq] <;> omega
  have h := Nat.mul_le_mul_right (2^t) (Nat.succ_le_of_lt hf)
  rw [Nat.succ_mul] at h
  change ((0 <<< w) + f) <<< t + s.2 < _
  simp only [Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_add, pow_add]
  omega

private theorem append_split (w t : ℕ) (s : Bool × ℕ) (n : ℕ) :
    appendDigit w t s n = n*2^(w+t) + appendDigit w t s 0 := by
  simp only [appendDigit, Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_add, pow_add]
  ring

/-- A state packs the remainder and the parity of the quotient of the prefix.
A single step only divides a number with at most w+t plus the width of d bits. -/
private def advance (w t d st : ℕ) (s : Bool × ℕ) : ℕ :=
  let v := appendDigit w t s (st/2)
  2*(v%d) + ((st%2 + parity 22 (v/d))%2)

private def goodState (d st n : ℕ) : Prop :=
  st/2 = n%d ∧ st%2 = (Nat.digits 2 (n/d)).count 1 % 2

private theorem advance_good (w t d st n : ℕ) (hd : 0 < d) (s : Bool × ℕ)
    (hc : s.2 < 2^t) (hg : goodState d st n) :
    goodState d (advance w t d st s) (appendDigit w t s n) := by
  obtain ⟨hr,hp⟩ := hg
  let B := 2^(w+t)
  let c := appendDigit w t s 0
  let v := (n%d)*B+c
  have hv : v/d < B := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    have e := Nat.mul_le_mul_right B (Nat.succ_le_of_lt (Nat.mod_lt n hd))
    rw [Nat.succ_mul] at e
    have small : c < B := append_size w t s hc
    dsimp only [v]
    rw [Nat.mul_comm B d]
    omega
  have splitNum : appendDigit w t s n = v + (n/d*B)*d := by
    rw [append_split]
    change n*B+c = ((n%d)*B+c) + (n/d*B)*d
    conv_lhs => rw [← Nat.mod_add_div n d]
    ring
  have key : appendDigit w t s (st/2) = v := by rw [hr,append_split]
  have remEq : (appendDigit w t s n)%d = v%d := by rw [splitNum, Nat.add_mul_mod_self_right]
  have quotEq : (appendDigit w t s n)/d = n/d*B + v/d := by
    rw [splitNum,Nat.add_mul_div_right _ _ hd,Nat.add_comm]
  have digits := count_ones_append (n/d) (w+t) (v/d) hv
  simp only [goodState, advance, key, remEq, quotEq, parity_eq, B, digits] at *
  omega

private def follows (w t d : ℕ) : List (Bool × ℕ) → List ℕ → ℕ → Bool
  | [], [], st => st%2 == 0
  | s::xs, y::ys, st => (advance w t d st s == y) && follows w t d xs ys y
  | _, _, _ => false

private theorem follows_sound (w t d : ℕ) (hd : 0 < d) (xs : List (Bool × ℕ)) (ys : List ℕ)
    (st n : ℕ) (hg : goodState d st n) (hc : ∀ s ∈ xs, s.2 < 2^t)
    (ok : follows w t d xs ys st = true) :
    (Nat.digits 2 ((xs.foldl (fun m s => appendDigit w t s m) n)/d)).count 1 % 2 = 0 := by
  induction xs generalizing ys st n with
  | nil =>
    cases ys with
    | nil =>
      have he : st%2 = 0 := by simpa [follows] using ok
      exact hg.2.symm.trans he
    | cons => simp [follows] at ok
  | cons s xs ih =>
    cases ys with
    | nil => simp [follows] at ok
    | cons y ys =>
      simp only [follows,Bool.and_eq_true,beq_iff_eq] at ok
      have h := advance_good w t d st n hd s (hc _ List.mem_cons_self) hg
      rw [ok.1] at h
      exact ih ys y _ h (fun a ha => hc a (List.mem_cons_of_mem _ ha)) ok.2

private theorem digit_certificate (ds : List (Bool × ℕ)) (w t d : ℕ) (hd : 0 < d)
    (hc : ∀ s ∈ ds, s.2 < 2^t) (ys : List ℕ) (ok : follows w t d ds.reverse ys 0 = true) :
    (Nat.digits 2 (word ds w t / d)).count 1 % 2 = 0 := by
  have h := follows_sound w t d hd ds.reverse ys 0 0 (by simp [goodState]) (by simpa using hc) ok
  simpa only [List.foldl_reverse, word, appendDigit] using h

private lemma extend_pow_mod {n r d m s : ℕ} (b : ℕ) (h : 2^n ≡ r [MOD d])
    (hm : n+n+b = m) (hs : (r*r*2^b)%d = s) : 2^m ≡ s [MOD d] := by
  subst m s
  rw [pow_add, pow_add]
  exact ((h.mul h).mul (Nat.ModEq.refl _)).trans (Nat.mod_modEq _ _).symm


private def ds18 : List (Bool × ℕ) := [(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)]

set_option maxHeartbeats 8000000 in
private theorem falling18 (x B : ℕ) (hx : 0 < x) (hB : B = 2251799813685248) :
    ([(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)] : List (Bool × ℕ)).foldr
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

private def residues18 : List ℕ := [94169, 136289, 168689, 508889, 816689, 1156889, 1497089, 1529489, 1795169, 1837289, 2177489, 2475569, 2550089, 3155969, 3230489, 3538289, 3570689, 4591289, 4856969, 5537369, 5579489, 5611889, 5919689]

private theorem parity18_94169 : (Nat.digits 2 (word ds18 (94169-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (94169-51) 51 97692469875 (by decide) (by decide) [0, 62453409869, 166625187138, 2996089570, 51577683252, 36661009487, 80096477559, 29535208010, 29047887284, 125768661525, 127113748209, 27850657370, 104364910456, 178415288623, 70747800838, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_136289 : (Nat.digits 2 (word ds18 (136289-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (136289-51) 51 97692469875 (by decide) (by decide) [0, 93673648918, 58284754938, 169848625420, 132005981203, 87316364237, 68311354208, 56620316060, 41866793384, 153060526125, 189347469758, 35500649721, 41097406156, 63045133723, 98659935089, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_168689 : (Nat.digits 2 (word ds18 (168689-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (168689-51) 51 97692469875 (by decide) (by decide) [0, 27511552919, 20034793189, 42693347170, 58607405953, 51133967986, 164453149958, 17336571561, 36697879634, 53817382125, 116982677259, 161622145220, 22489316657, 109565357472, 14923532339, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_508889 : (Nat.digits 2 (word ds18 (508889-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (508889-51) 51 97692469875 (by decide) (by decide) [0, 114349303918, 106872544188, 172949973670, 167154594702, 159681156737, 99324836709, 191012073560, 80116755134, 184074008625, 138692115009, 118203269721, 22489316656, 109565357473, 14923532338, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_816689 : (Nat.digits 2 (word ds18 (816689-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (816689-51) 51 97692469875 (by decide) (by decide) [0, 71964211169, 36575317188, 39591998920, 153715418953, 109025801986, 133439667458, 13201440560, 128704544384, 22803899624, 37381405508, 144047838470, 41097406156, 63045133723, 98659935089, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_1156889 : (Nat.digits 2 (word ds18 (1156889-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (1156889-51) 51 97692469875 (by decide) (by decide) [0, 158801962168, 123413068189, 169848625421, 66877667953, 22188050987, 68311354209, 186876942560, 172123419885, 153060526124, 59090843258, 100628962971, 41097406157, 63045133722, 98659935088, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_1497089 : (Nat.digits 2 (word ds18 (1497089-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (1497089-51) 51 97692469875 (by decide) (by decide) [0, 50254773418, 14865879439, 104720312170, 175424856702, 130735239736, 3183040958, 165167504811, 20157355635, 87932212874, 80800281008, 57210087471, 41097406156, 63045133723, 98659935089, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_1529489 : (Nat.digits 2 (word ds18 (1529489-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (1529489-51) 51 97692469875 (by decide) (by decide) [0, 179477617169, 172000857439, 172949973670, 102026281453, 94552843487, 99324836708, 125883760311, 14988441884, 184074008625, 8435488509, 183331582970, 22489316657, 109565357472, 14923532339, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_1795169 : (Nat.digits 2 (word ds18 (1795169-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (1795169-51) 51 97692469875 (by decide) (by decide) [0, 105872285369, 14659122888, 68124402820, 8158807752, 188627073737, 145224790808, 116372959011, 50757325035, 190896974775, 40275997209, 6141219621, 104364910457, 178415288622, 70747800839, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_1837289 : (Nat.digits 2 (word ds18 (1837289-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (1837289-51) 51 97692469875 (by decide) (by decide) [0, 137092524419, 101703630439, 39591998920, 88587105703, 43897488737, 133439667459, 143458067060, 63576231135, 22803899624, 102509718758, 13791211971, 41097406157, 63045133722, 98659935088, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_2177489 : (Nat.digits 2 (word ds18 (2177489-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (2177489-51) 51 97692469875 (by decide) (by decide) [0, 28545335668, 188541381438, 169848625420, 1749354703, 152444677486, 68311354209, 121748629310, 106995106635, 153060526124, 124219156508, 165757276221, 41097406156, 63045133723, 98659935089, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_2475569 : (Nat.digits 2 (word ds18 (2475569-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (2475569-51) 51 97692469875 (by decide) (by decide) [0, 84162847619, 188334624889, 133252716070, 29868245502, 14951571737, 14968164308, 72954083511, 137595076034, 60640348274, 83694872709, 114688408370, 104364910457, 178415288622, 70747800839, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_2550089 : (Nat.digits 2 (word ds18 (2550089-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (2550089-51) 51 97692469875 (by decide) (by decide) [0, 49220990669, 41744230939, 172949973670, 36897968202, 29424530237, 99324836708, 60755447061, 145245068385, 184074008625, 73563801758, 53074956470, 22489316656, 109565357473, 14923532338, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_3155969 : (Nat.digits 2 (word ds18 (3155969-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (3155969-51) 51 97692469875 (by decide) (by decide) [0, 62453409868, 166625187138, 2996089571, 51577683253, 36661009487, 80096477558, 29535208011, 29047887284, 125768661524, 127113748208, 27850657371, 104364910457, 178415288622, 70747800839, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_3230489 : (Nat.digits 2 (word ds18 (3230489-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (3230489-51) 51 97692469875 (by decide) (by decide) [0, 27511552918, 20034793189, 42693347171, 58607405953, 51133967987, 164453149958, 17336571561, 36697879634, 53817382124, 116982677258, 161622145220, 22489316656, 109565357473, 14923532338, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_3538289 : (Nat.digits 2 (word ds18 (3538289-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (3538289-51) 51 97692469875 (by decide) (by decide) [0, 180511399918, 145122505939, 104720312171, 45168230203, 478613237, 3183040958, 34910878310, 85285668885, 87932212875, 15671967759, 187466713970, 41097406156, 63045133723, 98659935089, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_3570689 : (Nat.digits 2 (word ds18 (3570689-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (3570689-51) 51 97692469875 (by decide) (by decide) [0, 114349303919, 106872544188, 172949973671, 167154594702, 159681156736, 99324836709, 191012073560, 80116755134, 184074008624, 138692115008, 118203269721, 22489316657, 109565357472, 14923532339, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_4591289 : (Nat.digits 2 (word ds18 (4591289-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (4591289-51) 51 97692469875 (by decide) (by decide) [0, 179477617168, 172000857439, 172949973671, 102026281453, 94552843486, 99324836708, 125883760311, 14988441884, 184074008624, 8435488508, 183331582970, 22489316656, 109565357473, 14923532338, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_4856969 : (Nat.digits 2 (word ds18 (4856969-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (4856969-51) 51 97692469875 (by decide) (by decide) [0, 105872285368, 14659122888, 68124402821, 8158807753, 188627073737, 145224790809, 116372959010, 50757325035, 190896974774, 40275997208, 6141219620, 104364910456, 178415288623, 70747800838, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_5537369 : (Nat.digits 2 (word ds18 (5537369-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (5537369-51) 51 97692469875 (by decide) (by decide) [0, 84162847618, 188334624889, 133252716071, 29868245503, 14951571737, 14968164309, 72954083510, 137595076034, 60640348275, 83694872708, 114688408371, 104364910456, 178415288623, 70747800838, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_5579489 : (Nat.digits 2 (word ds18 (5579489-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (5579489-51) 51 97692469875 (by decide) (by decide) [0, 115383086668, 79994192688, 104720312170, 110296543452, 65606926486, 3183040958, 100039191561, 150413982135, 87932212875, 145928594259, 122338400720, 41097406156, 63045133723, 98659935089, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_5611889 : (Nat.digits 2 (word ds18 (5611889-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (5611889-51) 51 97692469875 (by decide) (by decide) [0, 49220990668, 41744230939, 172949973671, 36897968202, 29424530236, 99324836708, 60755447061, 145245068385, 184074008624, 73563801759, 53074956470, 22489316657, 109565357472, 14923532339, 122474494801, 151966064248, 0, 0]
  decide +kernel
private theorem parity18_5919689 : (Nat.digits 2 (word ds18 (5919689-51) 51 / 97692469875)).count 1 % 2 = 0 := by
  apply digit_certificate ds18 (5919689-51) 51 97692469875 (by decide) (by decide) [0, 6835897918, 166831943689, 39591998920, 23458792453, 174154115236, 133439667458, 78329753811, 193832857635, 22803899625, 167638032008, 78919525220, 41097406157, 63045133722, 98659935088, 122474494801, 151966064248, 0, 0]
  decide +kernel

private theorem column18 (a : ℕ) (ha : 51 ≤ a)
    (hr : (a-51)%6123600+51 ∈ residues18) :
    OeisA249609.isEvil ((2^a).choose 18) = true := by
  apply checked_column (ds := ds18) (z := 16) (l := 3061800) ha (by decide) modular_order18
    (by decide) assemble18 (by decide) ((a-51)%6123600+51) rfl
  generalize (a-51)%6123600+51 = r at hr ⊢
  simp only [residues18, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact parity18_94169
  · exact parity18_136289
  · exact parity18_168689
  · exact parity18_508889
  · exact parity18_816689
  · exact parity18_1156889
  · exact parity18_1497089
  · exact parity18_1529489
  · exact parity18_1795169
  · exact parity18_1837289
  · exact parity18_2177489
  · exact parity18_2475569
  · exact parity18_2550089
  · exact parity18_3155969
  · exact parity18_3230489
  · exact parity18_3538289
  · exact parity18_3570689
  · exact parity18_4591289
  · exact parity18_4856969
  · exact parity18_5537369
  · exact parity18_5579489
  · exact parity18_5611889
  · exact parity18_5919689

private def ds19 : List (Bool × ℕ) := [(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)]

set_option maxHeartbeats 8000000 in
private theorem falling19 (x B : ℕ) (hx : 0 < x) (hB : B = 36028797018963968) :
    ([(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)] : List (Bool × ℕ)).foldr
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

private def residues19 : List ℕ := [476489, 849089, 1114769, 1189289, 1869689, 2135369, 2209889, 2517689, 2815769, 2890289, 3198089, 3878489, 3910889, 4176569, 4218689, 4251089, 4558889, 4899089, 4931489, 5197169, 5271689, 5877569, 5952089]

private theorem parity19_476489 : (Nat.digits 2 (word ds19 (476489-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (476489-55) 55 1856156927625 (by decide) (by decide) [0, 2134360797382, 803616102414, 2377138699000, 1090976707392, 2899764324814, 3120727038710, 954540839781, 3364588654305, 897409449927, 1168281292526, 100756234040, 3309784506196, 3230990617879, 2480776443592, 1081984819681, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_849089 : (Nat.digits 2 (word ds19 (849089-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (849089-55) 55 1856156927625 (by decide) (by decide) [0, 2350421392133, 2433891499165, 137965262501, 874916112642, 385604676814, 2826098954961, 2093769430280, 202247222054, 2193773018427, 559383252777, 3439874516541, 2779453955446, 1463222115379, 1950445892843, 1612315370431, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_1114769 : (Nat.digits 2 (word ds19 (1114769-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (1114769-55) 55 1856156927625 (by decide) (by decide) [0, 2472201000083, 3015290917765, 3060675853301, 1495599275742, 2950833192664, 3132512162061, 1453444394931, 3144599685105, 2924450666127, 1836104949027, 2689554996590, 2143057294546, 1816775815879, 571586460893, 21323718181, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_1189289 : (Nat.digits 2 (word ds19 (1189289-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (1189289-55) 55 1856156927625 (by decide) (by decide) [0, 288024805882, 371494912914, 2612841166000, 2937312698893, 2448001263065, 1588661003211, 1681290113030, 1027205856554, 956335066677, 971862570026, 2614915882041, 2779453955446, 1463222115379, 1950445892842, 1612315370431, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_1869689 : (Nat.digits 2 (word ds19 (1869689-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (1869689-55) 55 1856156927625 (by decide) (by decide) [0, 3587859343882, 3671329450914, 137965262501, 3349792016143, 2860480580314, 2826098954960, 856331478531, 2677123125554, 2193773018426, 1796821204526, 964998613040, 2779453955446, 1463222115379, 1950445892842, 1612315370431, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_2135369 : (Nat.digits 2 (word ds19 (2135369-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (2135369-55) 55 1856156927625 (by decide) (by decide) [0, 3709638951833, 540415014264, 3060675853301, 258161323992, 1713395240915, 3132512162060, 216006443180, 1907161733355, 2924450666127, 3073542900777, 214679093091, 2143057294546, 1816775815879, 571586460892, 21323718181, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_2209889 : (Nat.digits 2 (word ds19 (2209889-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (2209889-55) 55 1856156927625 (by decide) (by decide) [0, 1525462757633, 1608932864665, 2612841166000, 1699874747143, 1210563311315, 1588661003211, 443852161281, 3502081760055, 956335066677, 2209300521776, 140039978541, 2779453955446, 1463222115379, 1950445892843, 1612315370431, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_2517689 : (Nat.digits 2 (word ds19 (2517689-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (2517689-55) 55 1856156927625 (by decide) (by decide) [0, 896922845632, 3278492005914, 2377138699001, 2328414659143, 424888421315, 3120727038710, 2191978791530, 889712750805, 897409449926, 3643157196026, 2575632137541, 3309784506196, 3230990617879, 2480776443592, 1081984819681, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_2815769 : (Nat.digits 2 (word ds19 (2815769-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (2815769-55) 55 1856156927625 (by decide) (by decide) [0, 3297159634583, 127935697015, 585799949800, 670640641242, 2125874558165, 657636258560, 3103361663930, 3557079002355, 449574762626, 186187680026, 2277075679341, 2143057294546, 1816775815879, 571586460892, 21323718181, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_2890289 : (Nat.digits 2 (word ds19 (2890289-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (2890289-55) 55 1856156927625 (by decide) (by decide) [0, 1112983440383, 1196453547414, 137965262501, 2112354064393, 1623042628565, 2826098954961, 3331207382030, 1439685173804, 2193773018427, 3034259156276, 2202436564790, 2779453955446, 1463222115379, 1950445892843, 1612315370431, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_3198089 : (Nat.digits 2 (word ds19 (3198089-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (3198089-55) 55 1856156927625 (by decide) (by decide) [0, 484443528383, 2866012688665, 3614576650751, 2740893976393, 837367738564, 645851135211, 1367020157030, 2539630019804, 2134847401676, 755801975276, 925714868540, 3309784506196, 3230990617879, 2480776443592, 1081984819681, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_3878489 : (Nat.digits 2 (word ds19 (3878489-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (3878489-55) 55 1856156927625 (by decide) (by decide) [0, 71964211132, 2453533371414, 1139700747250, 3153373293642, 1249847055814, 1883289086960, 542061522531, 477233433554, 3372285353427, 1580760609776, 2988111454790, 3309784506196, 3230990617879, 2480776443592, 1081984819681, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_3910889 : (Nat.digits 2 (word ds19 (3910889-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (3910889-55) 55 1856156927625 (by decide) (by decide) [0, 2350421392132, 2433891499164, 137965262500, 874916112642, 385604676815, 2826098954960, 2093769430280, 202247222054, 2193773018426, 559383252776, 3439874516541, 2779453955446, 1463222115379, 1950445892842, 1612315370431, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_4176569 : (Nat.digits 2 (word ds19 (4176569-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (4176569-55) 55 1856156927625 (by decide) (by decide) [0, 2472201000082, 3015290917764, 3060675853300, 1495599275742, 2950833192664, 3132512162061, 1453444394930, 3144599685104, 2924450666127, 1836104949027, 2689554996591, 2143057294546, 1816775815879, 571586460892, 21323718181, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_4218689 : (Nat.digits 2 (word ds19 (4218689-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (4218689-55) 55 1856156927625 (by decide) (by decide) [0, 1721881480132, 391136785164, 3614576650750, 1503456024643, 3312243642064, 645851135210, 129582205281, 1302192068054, 2134847401676, 1993239927026, 2163152820290, 3309784506196, 3230990617879, 2480776443593, 1081984819681, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_4251089 : (Nat.digits 2 (word ds19 (4251089-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (4251089-55) 55 1856156927625 (by decide) (by decide) [0, 288024805883, 371494912915, 2612841166001, 2937312698893, 2448001263064, 1588661003210, 1681290113030, 1027205856554, 956335066676, 971862570027, 2614915882041, 2779453955446, 1463222115379, 1950445892843, 1612315370431, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_4558889 : (Nat.digits 2 (word ds19 (4558889-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (4558889-55) 55 1856156927625 (by decide) (by decide) [0, 3371798749132, 2041054054165, 2377138699001, 3565852610893, 1662326373065, 3120727038711, 3429416743281, 2127150702555, 897409449926, 2405719244276, 1338194185791, 3309784506196, 3230990617879, 2480776443592, 1081984819681, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_4899089 : (Nat.digits 2 (word ds19 (4899089-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (4899089-55) 55 1856156927625 (by decide) (by decide) [0, 1309402162883, 3690971323165, 1139700747250, 1915935341893, 12409104065, 1883289086960, 3016937426031, 2952109337055, 3372285353426, 2818198561526, 513235551291, 3309784506196, 3230990617879, 2480776443593, 1081984819681, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_4931489 : (Nat.digits 2 (word ds19 (4931489-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (4931489-55) 55 1856156927625 (by decide) (by decide) [0, 3587859343883, 3671329450915, 137965262500, 3349792016143, 2860480580315, 2826098954961, 856331478531, 2677123125554, 2193773018427, 1796821204527, 964998613040, 2779453955446, 1463222115379, 1950445892843, 1612315370431, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_5197169 : (Nat.digits 2 (word ds19 (5197169-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (5197169-55) 55 1856156927625 (by decide) (by decide) [0, 3709638951832, 540415014265, 3060675853300, 258161323992, 1713395240915, 3132512162060, 216006443181, 1907161733354, 2924450666127, 3073542900777, 214679093090, 2143057294546, 1816775815879, 571586460893, 21323718181, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_5271689 : (Nat.digits 2 (word ds19 (5271689-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (5271689-55) 55 1856156927625 (by decide) (by decide) [0, 1525462757632, 1608932864664, 2612841166001, 1699874747143, 1210563311314, 1588661003210, 443852161281, 3502081760055, 956335066676, 2209300521777, 140039978541, 2779453955446, 1463222115379, 1950445892842, 1612315370431, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_5877569 : (Nat.digits 2 (word ds19 (5877569-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (5877569-55) 55 1856156927625 (by decide) (by decide) [0, 3297159634582, 127935697014, 585799949801, 670640641242, 2125874558165, 657636258560, 3103361663931, 3557079002354, 449574762626, 186187680026, 2277075679340, 2143057294546, 1816775815879, 571586460893, 21323718181, 3222818531099, 1172309638500, 0, 0]
  decide +kernel
private theorem parity19_5952089 : (Nat.digits 2 (word ds19 (5952089-55) 55 / 1856156927625)).count 1 % 2 = 0 := by
  apply digit_certificate ds19 (5952089-55) 55 1856156927625 (by decide) (by decide) [0, 1112983440382, 1196453547415, 137965262500, 2112354064393, 1623042628564, 2826098954960, 3331207382030, 1439685173804, 2193773018426, 3034259156277, 2202436564790, 2779453955446, 1463222115379, 1950445892842, 1612315370431, 3222818531099, 1172309638500, 0, 0]
  decide +kernel

private theorem column19 (a : ℕ) (ha : 55 ≤ a)
    (hr : (a-55)%6123600+55 ∈ residues19) :
    OeisA249609.isEvil ((2^a).choose 19) = true := by
  apply checked_column (ds := ds19) (z := 16) (l := 3061800) ha (by decide) modular_order19
    (by decide) assemble19 (by decide) ((a-55)%6123600+55) rfl
  generalize (a-55)%6123600+55 = r at hr ⊢
  simp only [residues19, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact parity19_476489
  · exact parity19_849089
  · exact parity19_1114769
  · exact parity19_1189289
  · exact parity19_1869689
  · exact parity19_2135369
  · exact parity19_2209889
  · exact parity19_2517689
  · exact parity19_2815769
  · exact parity19_2890289
  · exact parity19_3198089
  · exact parity19_3878489
  · exact parity19_3910889
  · exact parity19_4176569
  · exact parity19_4218689
  · exact parity19_4251089
  · exact parity19_4558889
  · exact parity19_4899089
  · exact parity19_4931489
  · exact parity19_5197169
  · exact parity19_5271689
  · exact parity19_5877569
  · exact parity19_5952089

private def ds20 : List (Bool × ℕ) := [(false, 0), (true, 1031276404198014976), (false, 431565146817638399), (true, 484311774265693696), (false, 610116075740491775), (true, 781536717261618976), (false, 161429736530118959), (true, 1100660601244334256), (false, 12953636989943895), (true, 1150417645851379426), (false, 381922055502194), (true, 1152875223959095066), (false, 4465226757380), (true, 1152921162354335076), (false, 20692933629), (true, 1152921503632905076), (false, 34916945), (true, 1152921504605926426), (false, 16814), (true, 1152921504606846786), (false, 0)]

set_option maxHeartbeats 8000000 in
private theorem falling20 (x B : ℕ) (hx : 0 < x) (hB : B = 1152921504606846976) :
    ([(false, 0), (true, 1031276404198014976), (false, 431565146817638399), (true, 484311774265693696), (false, 610116075740491775), (true, 781536717261618976), (false, 161429736530118959), (true, 1100660601244334256), (false, 12953636989943895), (true, 1150417645851379426), (false, 381922055502194), (true, 1152875223959095066), (false, 4465226757380), (true, 1152921162354335076), (false, 20692933629), (true, 1152921503632905076), (false, 34916945), (true, 1152921504605926426), (false, 16814), (true, 1152921504606846786), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 20 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 1152921504606846786) 16814) 1152921504605926426) 34916945) 1152921503632905076) 20692933629) 1152921162354335076) 4465226757380) 1152875223959095066) 381922055502194) 1150417645851379426) 12953636989943895) 1100660601244334256) 161429736530118959) 781536717261618976) 610116075740491775) 484311774265693696) 431565146817638399) 1031276404198014976) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem modular_order20 : (2:ℕ)^15309000 % 9280784638125 = 1 % 9280784638125 := by
  have h0 : (2:ℕ)^0 ≡ 1 [MOD 9280784638125] := by decide
  have h1 : (2:ℕ)^1 ≡ 2 [MOD 9280784638125] :=
    extend_pow_mod (n := 0) (r := 1) (d := 9280784638125) (m := 1) (s := 2) 1 h0 (by decide) (by decide)
  have h3 : (2:ℕ)^3 ≡ 8 [MOD 9280784638125] :=
    extend_pow_mod (n := 1) (r := 2) (d := 9280784638125) (m := 3) (s := 8) 1 h1 (by decide) (by decide)
  have h7 : (2:ℕ)^7 ≡ 128 [MOD 9280784638125] :=
    extend_pow_mod (n := 3) (r := 8) (d := 9280784638125) (m := 7) (s := 128) 1 h3 (by decide) (by decide)
  have h14 : (2:ℕ)^14 ≡ 16384 [MOD 9280784638125] :=
    extend_pow_mod (n := 7) (r := 128) (d := 9280784638125) (m := 14) (s := 16384) 0 h7 (by decide) (by decide)
  have h29 : (2:ℕ)^29 ≡ 536870912 [MOD 9280784638125] :=
    extend_pow_mod (n := 14) (r := 16384) (d := 9280784638125) (m := 29) (s := 536870912) 1 h14 (by decide) (by decide)
  have h58 : (2:ℕ)^58 ≡ 6328430101744 [MOD 9280784638125] :=
    extend_pow_mod (n := 29) (r := 536870912) (d := 9280784638125) (m := 58) (s := 6328430101744) 0 h29 (by decide) (by decide)
  have h116 : (2:ℕ)^116 ≡ 6278007334036 [MOD 9280784638125] :=
    extend_pow_mod (n := 58) (r := 6328430101744) (d := 9280784638125) (m := 116) (s := 6278007334036) 0 h58 (by decide) (by decide)
  have h233 : (2:ℕ)^233 ≡ 6344777226092 [MOD 9280784638125] :=
    extend_pow_mod (n := 116) (r := 6278007334036) (d := 9280784638125) (m := 233) (s := 6344777226092) 1 h116 (by decide) (by decide)
  have h467 : (2:ℕ)^467 ≡ 7981151742428 [MOD 9280784638125] :=
    extend_pow_mod (n := 233) (r := 6344777226092) (d := 9280784638125) (m := 467) (s := 7981151742428) 1 h233 (by decide) (by decide)
  have h934 : (2:ℕ)^934 ≡ 4972644508309 [MOD 9280784638125] :=
    extend_pow_mod (n := 467) (r := 7981151742428) (d := 9280784638125) (m := 934) (s := 4972644508309) 0 h467 (by decide) (by decide)
  have h1868 : (2:ℕ)^1868 ≡ 1799872299481 [MOD 9280784638125] :=
    extend_pow_mod (n := 934) (r := 4972644508309) (d := 9280784638125) (m := 1868) (s := 1799872299481) 0 h934 (by decide) (by decide)
  have h3737 : (2:ℕ)^3737 ≡ 3279875004347 [MOD 9280784638125] :=
    extend_pow_mod (n := 1868) (r := 1799872299481) (d := 9280784638125) (m := 3737) (s := 3279875004347) 1 h1868 (by decide) (by decide)
  have h7475 : (2:ℕ)^7475 ≡ 2914118570318 [MOD 9280784638125] :=
    extend_pow_mod (n := 3737) (r := 3279875004347) (d := 9280784638125) (m := 7475) (s := 2914118570318) 1 h3737 (by decide) (by decide)
  have h14950 : (2:ℕ)^14950 ≡ 3566129542999 [MOD 9280784638125] :=
    extend_pow_mod (n := 7475) (r := 2914118570318) (d := 9280784638125) (m := 14950) (s := 3566129542999) 0 h7475 (by decide) (by decide)
  have h29900 : (2:ℕ)^29900 ≡ 1942800457126 [MOD 9280784638125] :=
    extend_pow_mod (n := 14950) (r := 3566129542999) (d := 9280784638125) (m := 29900) (s := 1942800457126) 0 h14950 (by decide) (by decide)
  have h59800 : (2:ℕ)^59800 ≡ 9093535390501 [MOD 9280784638125] :=
    extend_pow_mod (n := 29900) (r := 1942800457126) (d := 9280784638125) (m := 59800) (s := 9093535390501) 0 h29900 (by decide) (by decide)
  have h119601 : (2:ℕ)^119601 ≡ 8135774592002 [MOD 9280784638125] :=
    extend_pow_mod (n := 59800) (r := 9093535390501) (d := 9280784638125) (m := 119601) (s := 8135774592002) 1 h59800 (by decide) (by decide)
  have h239203 : (2:ℕ)^239203 ≡ 6908995359758 [MOD 9280784638125] :=
    extend_pow_mod (n := 119601) (r := 8135774592002) (d := 9280784638125) (m := 239203) (s := 6908995359758) 1 h119601 (by decide) (by decide)
  have h478406 : (2:ℕ)^478406 ≡ 1146199296064 [MOD 9280784638125] :=
    extend_pow_mod (n := 239203) (r := 6908995359758) (d := 9280784638125) (m := 478406) (s := 1146199296064) 0 h239203 (by decide) (by decide)
  have h956812 : (2:ℕ)^956812 ≡ 9260472164596 [MOD 9280784638125] :=
    extend_pow_mod (n := 478406) (r := 1146199296064) (d := 9280784638125) (m := 956812) (s := 9260472164596) 0 h478406 (by decide) (by decide)
  have h1913625 : (2:ℕ)^1913625 ≡ 773647715807 [MOD 9280784638125] :=
    extend_pow_mod (n := 956812) (r := 9260472164596) (d := 9280784638125) (m := 1913625) (s := 773647715807) 1 h956812 (by decide) (by decide)
  have h3827250 : (2:ℕ)^3827250 ≡ 8182074119374 [MOD 9280784638125] :=
    extend_pow_mod (n := 1913625) (r := 773647715807) (d := 9280784638125) (m := 3827250) (s := 8182074119374) 0 h1913625 (by decide) (by decide)
  have h7654500 : (2:ℕ)^7654500 ≡ 3821499556876 [MOD 9280784638125] :=
    extend_pow_mod (n := 3827250) (r := 8182074119374) (d := 9280784638125) (m := 7654500) (s := 3821499556876) 0 h3827250 (by decide) (by decide)
  have h15309000 : (2:ℕ)^15309000 ≡ 1 [MOD 9280784638125] :=
    extend_pow_mod (n := 7654500) (r := 3821499556876) (d := 9280784638125) (m := 15309000) (s := 1) 0 h7654500 (by decide) (by decide)
  exact h15309000

private theorem assemble20 (w : ℕ) : word ds20 w 60 = (2^(w+60)).descFactorial 20 := by
  rw [pow_add]
  simpa only [word, ds20, Nat.shiftLeft_eq, Nat.one_mul] using
    falling20 (2^w) (2^60) (Nat.two_pow_pos _) rfl

private def residues20 : List ℕ := [434369, 1454969, 2857889, 3836369, 6557969, 6898169, 7578569, 8981489, 9619769, 9959969, 10640369, 13021769, 13702169, 15105089, 15743369, 16763969, 19145369, 21866969, 22207169, 22887569, 24928769, 25268969, 25949369, 27352289, 28330769, 29011169, 29733689]

private theorem parity20_434369 : (Nat.digits 2 (word ds20 (434369-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (434369-60) 60 9280784638125 (by decide) (by decide) [0, 6596994172545, 591238179206, 7229566685996, 18413993802543, 4232957795529, 16775686116695, 18244387007003, 10177418830434, 14123499216113, 6081043293882, 3689261565809, 5076302919087, 5646453482467, 6888298366960, 7722750237444, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_1454969 : (Nat.digits 2 (word ds20 (1454969-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (1454969-60) 60 9280784638125 (by decide) (by decide) [0, 4122118269045, 15440493600207, 2279814878996, 13464241995543, 7945271650779, 14300810213194, 5870007489502, 13889732685684, 7936309457363, 3606167390382, 18538516986809, 126551112086, 16783395048216, 3175984511711, 4010436382195, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_2857889 : (Nat.digits 2 (word ds20 (2857889-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (2857889-60) 60 9280784638125 (by decide) (by decide) [0, 2546840114595, 4798527215156, 7732398615596, 16147321744892, 11869717726328, 17734209482494, 10544773085003, 16164261492234, 492039874613, 14228491903182, 2652170711009, 7170126500937, 10879048249867, 7913604098411, 2207312509644, 16075931654428, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_3836369 : (Nat.digits 2 (word ds20 (3836369-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (3836369-60) 60 9280784638125 (by decide) (by decide) [0, 4534597586295, 591238179206, 15479153030996, 14289200630042, 4232957795529, 2338910012944, 7932404075753, 3990229071685, 12061102629863, 4018646707632, 9876451324558, 13325889264086, 5646453482467, 6888298366960, 7722750237444, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_6557969 : (Nat.digits 2 (word ds20 (6557969-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (6557969-60) 60 9280784638125 (by decide) (by decide) [0, 10309308027794, 15440493600207, 14654194396496, 7277052236793, 7945271650778, 1926430695694, 18244387007002, 13889732685684, 14123499216112, 9793357149132, 18538516986809, 12500930629587, 16783395048217, 3175984511710, 4010436382194, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_6898169 : (Nat.digits 2 (word ds20 (6898169-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (6898169-60) 60 9280784638125 (by decide) (by decide) [0, 15671539152044, 8015865889707, 629897609996, 18001514485292, 15369899361278, 13475851578694, 7932404075752, 15127170637434, 12061102629862, 15155588273382, 17301079035058, 17038203119336, 1934139627216, 14312926077461, 15147377947945, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_7578569 : (Nat.digits 2 (word ds20 (7578569-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (7578569-60) 60 9280784638125 (by decide) (by decide) [0, 7834432124295, 11728179744956, 9704442589497, 2327300429792, 11657585506028, 18013124068445, 5870007489503, 17602046540935, 7936309457362, 7318481245633, 14826203131558, 7551178822587, 9358767337716, 18025239932711, 298122526945, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_8981489 : (Nat.digits 2 (word ds20 (8981489-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (8981489-60) 60 9280784638125 (by decide) (by decide) [0, 6259153969844, 1086213359907, 15157026326096, 5010380179143, 15582031581578, 2884954061494, 10544773085003, 1315006071235, 492039874612, 17940805758432, 17501426132008, 14594754211436, 3454420539366, 4201290243160, 17056567930644, 16075931654428, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_9619769 : (Nat.digits 2 (word ds20 (9619769-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (9619769-60) 60 9280784638125 (by decide) (by decide) [0, 2884680317295, 4303552034456, 18366508251746, 10989366092042, 520643940279, 13063372261444, 18244387007003, 6465104975184, 14123499216113, 2368729438632, 7401575421058, 16213244484836, 13071081192966, 10600612222211, 11435064092695, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_9959969 : (Nat.digits 2 (word ds20 (9959969-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (9959969-60) 60 9280784638125 (by decide) (by decide) [0, 8246911441544, 15440493600207, 4342211465246, 3152259064293, 7945271650779, 6051223868194, 7932404075753, 7702542926934, 12061102629862, 7730960562882, 6164137469309, 2188947698336, 16783395048217, 3175984511710, 4010436382194, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_10640369 : (Nat.digits 2 (word ds20 (10640369-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (10640369-60) 60 9280784638125 (by decide) (by decide) [0, 409804413794, 591238179207, 13416756444746, 6039614285042, 4232957795528, 10588496357944, 5870007489503, 10177418830434, 7936309457362, 18455422811382, 3689261565808, 11263492677837, 5646453482467, 6888298366960, 7722750237444, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_13021769 : (Nat.digits 2 (word ds20 (13021769-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (13021769-60) 60 9280784638125 (by decide) (by decide) [0, 822283731045, 4303552034456, 8054525320496, 6864572919542, 520643940279, 17188165433944, 7932404075753, 277915216434, 12061102629862, 306332852383, 13588765179808, 5901261553586, 13071081192966, 10600612222211, 11435064092695, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_13702169 : (Nat.digits 2 (word ds20 (13702169-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (13702169-60) 60 9280784638125 (by decide) (by decide) [0, 11546745979544, 8015865889706, 17129070299996, 9751928140292, 15369899361279, 3163868647445, 5870007489502, 2752791119934, 7936309457362, 11030795100882, 11113889276309, 14975806533086, 1934139627216, 14312926077461, 15147377947945, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_15105089 : (Nat.digits 2 (word ds20 (15105089-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (15105089-60) 60 9280784638125 (by decide) (by decide) [0, 9971467825095, 15935468780906, 4020084760346, 12435007889643, 732776160579, 6597267916745, 10544773085003, 5027319926485, 492039874612, 3091550337432, 13789112276758, 3457812645686, 14591362105117, 488976387911, 13344254075394, 16075931654428, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_15743369 : (Nat.digits 2 (word ds20 (15743369-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (15743369-60) 60 9280784638125 (by decide) (by decide) [0, 6596994172544, 591238179207, 7229566685997, 18413993802542, 4232957795528, 16775686116694, 18244387007002, 10177418830435, 14123499216112, 6081043293883, 3689261565808, 5076302919086, 5646453482466, 6888298366961, 7722750237445, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_16763969 : (Nat.digits 2 (word ds20 (16763969-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (16763969-60) 60 9280784638125 (by decide) (by decide) [0, 4122118269044, 15440493600206, 2279814878997, 13464241995542, 7945271650778, 14300810213195, 5870007489503, 13889732685685, 7936309457362, 3606167390383, 18538516986808, 126551112087, 16783395048217, 3175984511710, 4010436382194, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_19145369 : (Nat.digits 2 (word ds20 (19145369-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (19145369-60) 60 9280784638125 (by decide) (by decide) [0, 4534597586294, 591238179207, 15479153030997, 14289200630043, 4232957795528, 2338910012945, 7932404075752, 3990229071684, 12061102629862, 4018646707633, 9876451324559, 13325889264087, 5646453482466, 6888298366961, 7722750237445, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_21866969 : (Nat.digits 2 (word ds20 (21866969-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (21866969-60) 60 9280784638125 (by decide) (by decide) [0, 10309308027795, 15440493600206, 14654194396497, 7277052236792, 7945271650779, 1926430695695, 18244387007003, 13889732685685, 14123499216113, 9793357149133, 18538516986808, 12500930629586, 16783395048216, 3175984511711, 4010436382195, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_22207169 : (Nat.digits 2 (word ds20 (22207169-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (22207169-60) 60 9280784638125 (by decide) (by decide) [0, 15671539152045, 8015865889706, 629897609997, 18001514485293, 15369899361279, 13475851578695, 7932404075753, 15127170637435, 12061102629863, 15155588273383, 17301079035059, 17038203119337, 1934139627217, 14312926077460, 15147377947944, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_22887569 : (Nat.digits 2 (word ds20 (22887569-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (22887569-60) 60 9280784638125 (by decide) (by decide) [0, 7834432124294, 11728179744957, 9704442589496, 2327300429793, 11657585506029, 18013124068444, 5870007489502, 17602046540934, 7936309457363, 7318481245632, 14826203131559, 7551178822586, 9358767337717, 18025239932710, 298122526944, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_24928769 : (Nat.digits 2 (word ds20 (24928769-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (24928769-60) 60 9280784638125 (by decide) (by decide) [0, 2884680317294, 4303552034457, 18366508251747, 10989366092043, 520643940278, 13063372261445, 18244387007002, 6465104975185, 14123499216112, 2368729438633, 7401575421059, 16213244484837, 13071081192967, 10600612222210, 11435064092694, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_25268969 : (Nat.digits 2 (word ds20 (25268969-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (25268969-60) 60 9280784638125 (by decide) (by decide) [0, 8246911441545, 15440493600206, 4342211465247, 3152259064292, 7945271650778, 6051223868195, 7932404075752, 7702542926935, 12061102629863, 7730960562883, 6164137469308, 2188947698337, 16783395048216, 3175984511711, 4010436382195, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_25949369 : (Nat.digits 2 (word ds20 (25949369-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (25949369-60) 60 9280784638125 (by decide) (by decide) [0, 409804413795, 591238179206, 13416756444747, 6039614285043, 4232957795529, 10588496357945, 5870007489502, 10177418830435, 7936309457363, 18455422811383, 3689261565809, 11263492677836, 5646453482466, 6888298366961, 7722750237445, 17666923306678, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_27352289 : (Nat.digits 2 (word ds20 (27352289-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (27352289-60) 60 9280784638125 (by decide) (by decide) [0, 17396095535595, 8510841070406, 307770905096, 8722694034392, 8157403871079, 14021895627244, 10544773085002, 12451947636985, 492039874612, 10516178047933, 6364484566258, 18307068066687, 18303675960366, 11625917953661, 5919626364894, 16075931654428, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_28330769 : (Nat.digits 2 (word ds20 (28330769-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (28330769-60) 60 9280784638125 (by decide) (by decide) [0, 822283731044, 4303552034457, 8054525320497, 6864572919543, 520643940278, 17188165433945, 7932404075752, 277915216435, 12061102629863, 306332852382, 13588765179809, 5901261553587, 13071081192967, 10600612222210, 11435064092694, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_29011169 : (Nat.digits 2 (word ds20 (29011169-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (29011169-60) 60 9280784638125 (by decide) (by decide) [0, 11546745979545, 8015865889707, 17129070299997, 9751928140293, 15369899361278, 3163868647444, 5870007489503, 2752791119935, 7936309457363, 11030795100883, 11113889276308, 14975806533087, 1934139627217, 14312926077460, 15147377947944, 17666923306679, 6760406942101, 11136941565749, 0, 0]
  decide +kernel
private theorem parity20_29733689 : (Nat.digits 2 (word ds20 (29733689-60) 60 / 9280784638125)).count 1 % 2 = 0 := by
  apply digit_certificate ds20 (29733689-60) 60 9280784638125 (by decide) (by decide) [0, 17808574852845, 12223154925657, 13507109057097, 9547652668892, 4445090015828, 2059995426995, 12607169671253, 2552444022984, 4616833047113, 10928657365183, 16263988180258, 12944836942436, 7166734394616, 15338231808910, 9631940220144, 16075931654429, 6760406942101, 11136941565749, 0, 0]
  decide +kernel

private theorem column20 (a : ℕ) (ha : 60 ≤ a)
    (hr : (a-60)%30618000+60 ∈ residues20) :
    OeisA249609.isEvil ((2^a).choose 20) = true := by
  apply checked_column (ds := ds20) (z := 18) (l := 15309000) ha (by decide) modular_order20
    (by decide) assemble20 (by decide) ((a-60)%30618000+60) rfl
  generalize (a-60)%30618000+60 = r at hr ⊢
  simp only [residues20, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact parity20_434369
  · exact parity20_1454969
  · exact parity20_2857889
  · exact parity20_3836369
  · exact parity20_6557969
  · exact parity20_6898169
  · exact parity20_7578569
  · exact parity20_8981489
  · exact parity20_9619769
  · exact parity20_9959969
  · exact parity20_10640369
  · exact parity20_13021769
  · exact parity20_13702169
  · exact parity20_15105089
  · exact parity20_15743369
  · exact parity20_16763969
  · exact parity20_19145369
  · exact parity20_21866969
  · exact parity20_22207169
  · exact parity20_22887569
  · exact parity20_24928769
  · exact parity20_25268969
  · exact parity20_25949369
  · exact parity20_27352289
  · exact parity20_28330769
  · exact parity20_29011169
  · exact parity20_29733689

private def left29 : List ℕ := [239, 1079, 1394, 3914, 4964, 5804, 6119, 8639]
private def left42 : List ℕ := [1617, 3507, 5397, 6552, 7287]

private def branch (s : Fin 3) : ℕ := ([29, 42, 52] : List ℕ)[s.val]!

/-- There are ninety lifts of each original class in the common period of the
three columns. Each covered lift points to a certified representative. -/
private theorem cover : ∀ (s : Fin 3) (t : Fin 90),
    let u := 105*t.val + branch s
    (3240*u+158)%6123600+51 ∈ residues18 ∨
    (3240*u+154)%6123600+55 ∈ residues19 ∨
    (3240*u+149)%30618000+60 ∈ residues20 ∨
    u ∈ left29 ∨ u ∈ left42 := by decide +kernel

private def Witness (q : ℕ) : Prop :=
  ∃ k ∈ List.range' 1 (2^(3240*q+209)), OeisA249609.isEvil ((2^(3240*q+209)).choose k) = true

private theorem witness {q k : ℕ} (hpos : 0 < k) (hk : k ≤ 32)
    (h : OeisA249609.isEvil ((2^(3240*q+209)).choose k) = true) : Witness q := by
  refine ⟨k, List.mem_range'_1.mpr ⟨hpos, ?_⟩, h⟩
  have bound : 32 ≤ 2^(3240*q+209) := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 3240*q+209 by omega)
  omega

private theorem classify (q : ℕ) (hq : q%105 ∈ ([29,42,52] : List ℕ)) :
    Witness q ∨ q%9450 ∈ left29 ∨ q%9450 ∈ left42 := by
  obtain ⟨s, hs⟩ : ∃ s : Fin 3, q%105 = branch s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h|h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  let t : Fin 90 := ⟨(q/105)%90, Nat.mod_lt _ (by decide)⟩
  have hq' : 105*t.val + branch s = q%9450 := by
    dsimp only [t]
    rw [← hs]
    have a := Nat.mod_add_div q 105
    have b := Nat.mod_add_div (q/105) 90
    omega
  have h := cover s t
  dsimp only at h
  rw [hq'] at h
  have periodic (c : ℕ) (m j : ℕ) (hm : m*j = 30618000) :
      (3240*(q%9450)+c)%m = (3240*q+c)%m := by
    have eq : 3240*q+c = 3240*(q%9450)+c + 30618000*(q/9450) := by
      have z := Nat.mod_add_div q 9450
      omega
    rw [eq, ← hm, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  rw [periodic 158 6123600 5 (by decide), periodic 154 6123600 5 (by decide),
      periodic 149 30618000 1 (by decide)] at h
  rcases h with h|h|h|h|h
  · exact Or.inl (witness (k:=18) (by decide) (by decide) (column18 _ (by omega)
      (by simpa only [show 3240*q+209-51 = 3240*q+158 by omega] using h)))
  · exact Or.inl (witness (k:=19) (by decide) (by decide) (column19 _ (by omega)
      (by simpa only [show 3240*q+209-55 = 3240*q+154 by omega] using h)))
  · exact Or.inl (witness (k:=20) (by decide) (by decide) (column20 _ (by omega)
      (by simpa only [show 3240*q+209-60 = 3240*q+149 by omega] using h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Every exponent with q in class 52 modulo 105 already has a witness. -/
theorem class52 (q : ℕ) (hq : q%105 = 52) :
    ∃ k ∈ List.range' 1 (2^(3240*q+209)), OeisA249609.isEvil ((2^(3240*q+209)).choose k) = true := by
  rcases classify q (by rw [hq]; decide) with h|h|h
  · exact h
  · have f : ∀ r ∈ left29, r%105 = 29 := by decide
    have bad := f _ h
    rw [Nat.mod_mod_of_dvd q (by decide : 105 ∣ 9450), hq] at bad
    contradiction
  · have f : ∀ r ∈ left42, r%105 = 42 := by decide
    have bad := f _ h
    rw [Nat.mod_mod_of_dvd q (by decide : 105 ∣ 9450), hq] at bad
    contradiction

/-- Eight lifts of the original class 29 remain. -/
def H1 : Prop :=
  ∀ q : ℕ, q%9450 ∈ ([239, 1079, 1394, 3914, 4964, 5804, 6119, 8639] : List ℕ) →
    ∃ k ∈ List.range' 1 (2^(3240*q+209)), OeisA249609.isEvil ((2^(3240*q+209)).choose k) = true

/-- Five lifts of the original class 42 remain. -/
def H2 : Prop :=
  ∀ q : ℕ, q%9450 ∈ ([1617, 3507, 5397, 6552, 7287] : List ℕ) →
    ∃ k ∈ List.range' 1 (2^(3240*q+209)), OeisA249609.isEvil ((2^(3240*q+209)).choose k) = true

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1.H3 := by
  intro h29 h42 q hq
  rcases classify q hq with h|h|h
  · exact h
  · exact h29 q h
  · exact h42 q h

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1
