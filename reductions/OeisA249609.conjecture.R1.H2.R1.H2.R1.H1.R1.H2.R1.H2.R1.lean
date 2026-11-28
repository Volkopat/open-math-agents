import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1

import Mathlib.Tactic

/-!
Columns 18, 19 and 20 cover 85, 60 and 12 of the 180 classes modulo 9450
above 37 and 38 modulo 105, respectively. H1 and H2 contain the remaining
lifts of 37 and 38.

The binary block certificates use the periodicity theorem of the common
ancestor and the kernel-checked block division method of sibling PR 34517.
The falling factorial is expanded into runs of repeated bits with fixed
suffixes. Long division tracks the remainder and the parity of the quotient.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1

open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ q : ℕ, q % 9450 ∈ ([247, 1402, 2137, 3292, 4027, 5182, 5917, 7072, 8962] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+545)),
      OeisA249609.isEvil ((2 ^ (3240*q+545)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 9450 ∈ ([38, 773, 2663, 2873, 3608, 3818, 4553, 4763, 5498, 7388, 7598, 8333, 8543, 9278] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+545)),
      OeisA249609.isEvil ((2 ^ (3240*q+545)).choose k) = true

section Certificates

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

private def folded : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun n => (Nat.digits 2 n).count 1 % 2)
    (fun j f n =>
      let w := 8 * 2^j
      f ((n >>> w) ^^^ (n &&& ((1 <<< w) - 1))))

private theorem folded_eq (i n : ℕ) : folded i n = (Nat.digits 2 n).count 1 % 2 := by
  induction i generalizing n with
  | zero => rfl
  | succ j ih =>
    let w := 8 * 2^j
    change folded j ((n >>> w) ^^^ (n &&& ((1 <<< w) - 1))) = _
    rw [ih, xor_weight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.and_two_pow_sub_one_eq_mod]
    have h := count_ones_append (n / 2^w) w (n % 2^w) (Nat.mod_lt _ (by positivity))
    rw [Nat.div_add_mod'] at h
    exact congrArg (· % 2) h.symm

/-- Remainder and parity of the quotient after a prefix of the dividend. -/
private def state (d x : ℕ) : ℕ × ℕ :=
  (x % d, (Nat.digits 2 (x / d)).count 1 % 2)

private def appendBlock (d w c : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  let u := (st.1 <<< w) + c
  (u % d, (st.2 + folded ((w / 8).log2 + 1) (u / d)) % 2)

private theorem appendBlock_state (d x w c : ℕ) (hd : 0 < d) (hc : c < 2^w) :
    appendBlock d w c (state d x) = state d (x * 2^w + c) := by
  have he : x*2^w+c = (x%d * 2^w+c) + (x/d * 2^w)*d := by
    calc
      x*2^w+c = (x%d+d*(x/d))*2^w+c := by rw [Nat.mod_add_div]
      _ = _ := by ring
  have hv : (x%d * 2^w+c)/d < 2^w := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    have h := Nat.mul_le_mul_right (2^w) (Nat.succ_le_of_lt (Nat.mod_lt x hd))
    rw [Nat.succ_mul] at h
    nlinarith only [h,hc]
  simp only [appendBlock, state, Nat.shiftLeft_eq, folded_eq]
  rw [he, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hd,
    Nat.add_comm ((x % d * 2^w+c) / d), count_ones_append _ _ _ hv]
  simp [Nat.add_mod]

private def readBlocks (d w t : ℕ) (ds : List (Bool × ℕ)) : ℕ × ℕ :=
  ds.foldr (fun s st => appendBlock d t s.2
    (appendBlock d w (if s.1 then (1 <<< w) - 1 else 0) st)) (0, 0)

private theorem readBlocks_state (d w t : ℕ) (ds : List (Bool × ℕ))
    (hd : 0 < d) (hc : ∀ s ∈ ds, s.2 < 2^t) :
    readBlocks d w t ds = state d (ds.foldr
      (fun s n => (n*2^w + (if s.1 then 2^w-1 else 0))*2^t + s.2) 0) := by
  induction ds with
  | nil => simp [readBlocks, state]
  | cons s ds ih =>
    have hs := hc s (by simp)
    have hf : (if s.1 then 2^w-1 else 0) < 2^w := by
      have hp : 0 < 2^w := by positivity
      split <;> omega
    change appendBlock d t s.2 (appendBlock d w _ (readBlocks d w t ds)) = _
    rw [ih (fun b hb => hc b (by simp [hb])), Nat.shiftLeft_eq, Nat.one_mul,
      appendBlock_state _ _ _ _ hd hf, appendBlock_state _ _ _ _ hd hs]
    rfl

private theorem column_of_blocks {a k t d z l w : ℕ} {ds : List (Bool × ℕ)}
    (ht : t ≤ a) (hd : 0 < d) (hm : 2^l % d = 1 % d) (hc : ∀ s ∈ ds, s.2 < 2^t)
    (hw : ∀ u : ℕ, ds.foldr (fun s n => (n*2^u + (if s.1 then 2^u-1 else 0))*2^t + s.2) 0 =
      (2^(u+t)).descFactorial k) (hf : k.factorial = d * 2^z)
    (hr : (a-t)%(l+l) = w) (h : (readBlocks d w t ds).2 = 0) :
    OeisA249609.isEvil ((2^a).choose k) = true := by
  apply (periodic_column ht hd hm hc hw hf).2
  rw [hr, ← hw]
  rw [readBlocks_state _ _ _ _ hd hc] at h
  exact h

private def blocks18 : List (Bool × ℕ) :=
  [(false, 0), (true, 1896112385589248),
   (false, 1223405590579199), (true, 430197369060608),
   (false, 1583313975727487), (true, 1342499907841136),
   (false, 369012649234383), (true, 2141571347501048),
   (false, 24871845297935), (true, 2247491708383319),
   (false, 577924894832), (true, 2251739610991268),
   (false, 4853222763), (true, 2251799514034442),
   (false, 13896581), (true, 2251799813217068),
   (false, 10811), (true, 2251799813685095),
   (false, 0)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem falling18 (x B : ℕ) (hx : 0 < x) (hB : B = 2251799813685248) :
    blocks18.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
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

private def residues18 : List ℕ :=
  [37, 142, 143, 248, 352, 457, 458, 562, 667, 877, 878, 1088, 1192, 1193, 1403, 1717, 1823]

private theorem certified18 (r : ℕ) (hr : r ∈ residues18) :
    (readBlocks 97692469875 (3240*r+494) 51 blocks18).2 = 0 := by
  simp only [residues18, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem column18 (q : ℕ) (hr : q % 1890 ∈ residues18) :
    OeisA249609.isEvil ((2^(3240*q+545)).choose 18) = true := by
  refine column_of_blocks (t := 51) (l := 3061800) (d := 97692469875) (z := 16)
    (ds := blocks18) (by omega) (by decide) (by decide +kernel) (by decide) ?_ (by decide)
    ?_ (certified18 _ hr)
  · intro u
    rw [pow_add]
    exact falling18 (2^u) (2^51) (by positivity) (by decide)
  · omega

private def blocks19 : List (Bool × ℕ) :=
  [(false, 0), (false, 6402373705728000),
   (true, 13651808960442368), (false, 34012249593822719),
   (true, 5707543011244544), (false, 17950712280921503),
   (true, 28477269426900944), (false, 2353125040549983),
   (true, 35470875337416920), (false, 102417740732657),
   (true, 36014086265555045), (false, 1661573386472),
   (true, 36028649458260236), (false, 10246937271),
   (true, 36028796469174686), (false, 22323821),
   (true, 36028797018301172), (false, 13565),
   (true, 36028797018963797), (false, 0)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem falling19 (x B : ℕ) (hx : 0 < x) (hB : B = 36028797018963968) :
    blocks19.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
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

private def residues19 : List ℕ :=
  [353, 563, 668, 772, 1087, 1297, 1298, 1507, 1508, 1612, 1613, 1822]

private theorem certified19 (r : ℕ) (hr : r ∈ residues19) :
    (readBlocks 1856156927625 (3240*r+490) 55 blocks19).2 = 0 := by
  simp only [residues19, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem column19 (q : ℕ) (hr : q % 1890 ∈ residues19) :
    OeisA249609.isEvil ((2^(3240*q+545)).choose 19) = true := by
  refine column_of_blocks (t := 55) (l := 3061800) (d := 1856156927625) (z := 16)
    (ds := blocks19) (by omega) (by decide) (by decide +kernel) (by decide) ?_ (by decide)
    ?_ (certified19 _ hr)
  · intro u
    rw [pow_add]
    exact falling19 (2^u) (2^55) (by positivity) (by decide)
  · omega

private def blocks20 : List (Bool × ℕ) :=
  [(false, 0), (true, 1031276404198014976),
   (false, 431565146817638399), (true, 484311774265693696),
   (false, 610116075740491775), (true, 781536717261618976),
   (false, 161429736530118959), (true, 1100660601244334256),
   (false, 12953636989943895), (true, 1150417645851379426),
   (false, 381922055502194), (true, 1152875223959095066),
   (false, 4465226757380), (true, 1152921162354335076),
   (false, 20692933629), (true, 1152921503632905076),
   (false, 34916945), (true, 1152921504605926426),
   (false, 16814), (true, 1152921504606846786),
   (false, 0)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem falling20 (x B : ℕ) (hx : 0 < x) (hB : B = 1152921504606846976) :
    blocks20.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
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

private def residues20 : List ℕ :=
  [982, 983, 1718, 1928, 2872, 4762, 5708, 6443, 6652, 6653, 7807, 8542]

private theorem certified20 (r : ℕ) (hr : r ∈ residues20) :
    (readBlocks 9280784638125 (3240*r+485) 60 blocks20).2 = 0 := by
  simp only [residues20, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem column20 (q : ℕ) (hr : q % 9450 ∈ residues20) :
    OeisA249609.isEvil ((2^(3240*q+545)).choose 20) = true := by
  refine column_of_blocks (t := 60) (l := 15309000) (d := 9280784638125) (z := 18)
    (ds := blocks20) (by omega) (by decide) (by decide +kernel) (by decide) ?_ (by decide)
    ?_ (certified20 _ hr)
  · intro u
    rw [pow_add]
    exact falling20 (2^u) (2^60) (by positivity) (by decide)
  · omega

end Certificates

private theorem cover : ∀ j : Fin 90, ∀ b : Fin 2,
    let r := 105*j.val + (37+b.val)
    r % 1890 ∈ residues18 ∨ r % 1890 ∈ residues19 ∨ r ∈ residues20 ∨
    r ∈ ([247, 1402, 2137, 3292, 4027, 5182, 5917, 7072, 8962] : List ℕ) ∨
    r ∈ ([38, 773, 2663, 2873, 3608, 3818, 4553, 4763, 5498, 7388, 7598, 8333, 8543, 9278] : List ℕ) := by decide +kernel

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro h1 h2 q hq
  have hbase : q%105 = 37 ∨ q%105 = 38 := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hq
  let j : Fin 90 := ⟨(q/105)%90, Nat.mod_lt _ (by decide)⟩
  let b : Fin 2 := ⟨q%105-37, by omega⟩
  have he : 105*j.val + (37+b.val) = q%9450 := by
    dsimp [j, b]
    omega
  have h := cover j b
  dsimp only at h
  rw [he, Nat.mod_mod_of_dvd q (by decide : 1890 ∣ 9450)] at h
  have hb : 32 ≤ 2^(3240*q+545) :=
    le_trans (by decide : 32 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
  rcases h with h | h | h | h | h
  · exact witness _ 18 (by decide) (by omega) (column18 q h)
  · exact witness _ 19 (by decide) (by omega) (column19 q h)
  · exact witness _ 20 (by decide) (by omega) (column20 q h)
  · exact h1 q h
  · exact h2 q h

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1
