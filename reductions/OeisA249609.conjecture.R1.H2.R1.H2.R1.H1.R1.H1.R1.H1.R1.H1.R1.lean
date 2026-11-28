import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1
import Mathlib.Tactic

/-!
Column 20 settles 32 of the 55 lifts modulo 9450 for the exponents
`3240*q + 209`. Column 21 settles 151 of the remaining 483 lifts modulo
198450 with representatives below 120000. Together these columns settle
823 of the 1155 lifts. The three hypotheses partition the remaining 332 lifts
according to their residue classes modulo 1890.

The long-division certificate uses the periodic-column lemma from PR 5614
and the xor folding from the sibling reductions.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1

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

/-- Fold the halves with xor until only one byte remains. -/
private def foldParity : ℕ → ℕ → ℕ
  | 0, v => (Nat.digits 2 v).count 1 % 2
  | j+1, v =>
    let w := 8 * 2^j
    foldParity j ((v >>> w) ^^^ (v &&& ((1 <<< w)-1)))

private theorem foldParity_eq (j v : ℕ) :
    foldParity j v = (Nat.digits 2 v).count 1 % 2 := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
    change foldParity j ((v >>> (8 * 2^j)) ^^^ (v &&& ((1 <<< (8 * 2^j))-1))) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow,
      Nat.and_two_pow_sub_one_eq_mod, ih, xor_weight]
    have h := count_ones_append (v / 2^(8*2^j)) (8*2^j) (v % 2^(8*2^j))
      (Nat.mod_lt _ (by positivity))
    rw [Nat.div_add_mod'] at h
    exact congrArg (· % 2) h.symm

private def appendDigit (w t : ℕ) (s : Bool × ℕ) (v : ℕ) : ℕ :=
  (((v <<< w) + (if s.1 then (1 <<< w) - 1 else 0)) <<< t) + s.2

private def divisionStep (w t d : ℕ) (s : Bool × ℕ) (state : ℕ × ℕ) : ℕ × ℕ :=
  let stem : ℕ := (((1 : ℕ) <<< w) - 1) <<< t
  let scale := state.1 + (if s.1 then 1 else 0)
  let small := scale * (stem % d) + (state.1 <<< t) + s.2
  (small % d, state.2 ^^^ (scale * (stem / d) + small / d))

/-- Factor out the repeated bit block before dividing. Its quotient and
remainder only depend on the width and the divisor. -/
private theorem divisionStep_eq (w t d : ℕ) (hd : 0 < d) (s : Bool × ℕ)
    (state : ℕ × ℕ) :
    divisionStep w t d s state =
      let v := appendDigit w t s state.1
      (v % d, state.2 ^^^ (v / d)) := by
  obtain ⟨b, c⟩ := s
  let stem : ℕ := (((1 : ℕ) <<< w) - 1) <<< t
  let scale := state.1 + (if b then 1 else 0)
  let small := scale * (stem % d) + (state.1 <<< t) + c
  have hjoin : appendDigit w t (b, c) state.1 = scale * stem + (state.1 <<< t) + c := by
    simp only [appendDigit, stem, scale, Nat.shiftLeft_eq, Nat.one_mul]
    have hs := Nat.sub_add_cancel (Nat.one_le_two_pow (n := w))
    conv_lhs => rw [show state.1 * 2^w = state.1 * ((2^w - 1) + 1) by rw [hs]]
    cases b <;> simp <;> ring
  have he : appendDigit w t (b, c) state.1 = small + (scale * (stem / d)) * d := by
    rw [hjoin]
    dsimp only [small]
    calc
      _ = scale * (stem % d + d * (stem / d)) + (state.1 <<< t) + c := by
        rw [Nat.mod_add_div]
      _ = _ := by ring
  change (small % d, state.2 ^^^ (scale * (stem / d) + small / d)) = _
  dsimp only
  rw [he, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hd,
    Nat.add_comm (small / d)]

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
    change (divisionStep w t d (b,c) state).1 = appendDigit w t (b,c) word % d ∧
      (Nat.digits 2 (divisionStep w t d (b,c) state).2).count 1 % 2 =
        (Nat.digits 2 (appendDigit w t (b,c) word / d)).count 1 % 2
    rw [divisionStep_eq w t d hd]
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
    (ht : t ≤ 209) (hd : 0 < d) (hm : 2^l%d=1%d) (hc : ∀ s ∈ ds, s.2 < 2^t)
    (hw : ∀ w : ℕ, ds.foldr (fun s n => (n * 2^w + (if s.1 then 2^w-1 else 0))*2^t+s.2) 0 =
      (2^(w+t)).descFactorial k)
    (hf : k.factorial = d * 2^z) (hperiod : l+l = 3240*m) (hpos : 0 < m) (hr : q%m ∈ rs)
    (hpar : ∀ r ∈ rs,
      (Nat.digits 2 (ds.foldr (divisionStep (3240*r+209-t) t d) (0, 0)).2).count 1 % 2 = 0) :
    OeisA249609.isEvil ((2^(3240*q+209)).choose k) = true := by
  apply (periodic_column (ds := ds) (by omega) hd hm hc hw hf).2
  rw [show (3240*q+209-t)%(l+l) = 3240*(q%m)+209-t by
    have hlt := Nat.mod_lt q hpos
    have hdecomp := Nat.mod_add_div q m
    have he : (3240*q+209-t) = (3240*(q%m)+209-t) + (l+l)*(q/m) := by
      rw [hperiod, mul_assoc]
      omega
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]]
  exact divideCertificate hd hc (hw _) (hpar _ hr)

private def digits20 : List (Bool × ℕ) :=
  [(false, 0), (true, 1031276404198014976), (false, 431565146817638399),
   (true, 484311774265693696), (false, 610116075740491775), (true, 781536717261618976),
   (false, 161429736530118959), (true, 1100660601244334256), (false, 12953636989943895),
   (true, 1150417645851379426), (false, 381922055502194), (true, 1152875223959095066),
   (false, 4465226757380), (true, 1152921162354335076), (false, 20692933629),
   (true, 1152921503632905076), (false, 34916945), (true, 1152921504605926426),
   (false, 16814), (true, 1152921504606846786), (false, 0)]

private def residues20 : List ℕ :=
  [210, 240, 968, 1260, 1680, 1808, 2130, 2184, 2340, 3150, 3234, 3570, 3698, 3990, 4230,
   4650, 5124, 5460, 5588, 5670, 5880, 5910, 6120, 6638, 7014, 7560, 7770, 7854, 8430, 8528,
   8820, 9240]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem falling20 (x B : ℕ) (hx : 0 < x) (hB : B = 1152921504606846976) :
    digits20.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 20 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high
        (low (high (low (high (low 0 0) 1152921504606846786) 16814) 1152921504605926426) 34916945)
        1152921503632905076) 20692933629) 1152921162354335076) 4465226757380) 1152875223959095066)
        381922055502194) 1150417645851379426) 12953636989943895) 1100660601244334256)
        161429736530118959) 781536717261618976) 610116075740491775) 484311774265693696)
        431565146817638399) 1031276404198014976) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

-- This Boolean checker is evaluated only on explicit, bounded lists of residues.
private def checkResidues (j t d : ℕ) (digits : List (Bool × ℕ)) (rs : List ℕ) : Bool :=
  rs.all fun r => foldParity j (digits.foldr (divisionStep (3240*r+209-t) t d) (0, 0)).2 == 0

private theorem checkResidues_sound {j t d : ℕ} {digits : List (Bool × ℕ)} {rs : List ℕ}
    (h : checkResidues j t d digits rs = true) (r : ℕ) (hr : r ∈ rs) :
    (Nat.digits 2 (digits.foldr (divisionStep (3240*r+209-t) t d) (0, 0)).2).count 1 % 2 = 0 := by
  have hf := List.all_eq_true.mp h r hr
  exact (foldParity_eq _ _).symm.trans (beq_iff_eq.mp hf)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem hit20 (q : ℕ) (hr : q % 9450 ∈ residues20) :
    OeisA249609.isEvil ((2^(3240*q+209)).choose 20) = true := by
  refine certifyColumn (t:=60) (d:=9280784638125) (l:=15309000) (z:=18) (ds:=digits20)
    (by decide) (by decide) (by decide +kernel) (by decide) ?_ (by decide) (by decide)
    (by decide) hr (checkResidues_sound (j:=22) ?_)
  · intro w
    rw [pow_add]
    exact falling20 (2^w) (2^60) (by positivity) (by decide)
  · decide +kernel
private def remaining1 : List ℕ :=
  [0, 294, 450, 870, 1344, 1890, 2100, 2760]

private def remaining2 : List ℕ :=
  [2858, 3780, 4020, 4074, 4748, 5040, 5964, 6540]

private def remaining3 : List ℕ :=
  [6930, 7350, 7478, 7800, 8010, 8904, 9368]

private theorem coverage20 (q : ℕ)
    (hq : q % 1890 ∈ ([0, 210, 240, 294, 450, 870, 968, 1260, 1344, 1680, 1808] : List ℕ)) :
    q % 9450 ∈ residues20 ∨ q % 9450 ∈ remaining1 ∨
      q % 9450 ∈ remaining2 ∨ q % 9450 ∈ remaining3 := by
  have finite : ∀ i : Fin 5, ∀ s ∈ ([0, 210, 240, 294, 450, 870, 968, 1260, 1344, 1680, 1808] : List ℕ),
      s + 1890*i.val ∈ residues20 ∨ s + 1890*i.val ∈ remaining1 ∨
        s + 1890*i.val ∈ remaining2 ∨ s + 1890*i.val ∈ remaining3 := by decide +kernel
  have h := finite ⟨(q/1890)%5, Nat.mod_lt _ (by decide)⟩ (q%1890) hq
  dsimp only at h
  rwa [show q%1890 + 1890*((q/1890)%5) = q%9450 by omega] at h

def H1 : Prop :=
  ∀ q : ℕ, q % 9450 ∈ remaining1 →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+209)),
      OeisA249609.isEvil ((2 ^ (3240*q+209)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 9450 ∈ remaining2 →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+209)),
      OeisA249609.isEvil ((2 ^ (3240*q+209)).choose k) = true

def H3 : Prop :=
  ∀ q : ℕ, q % 9450 ∈ remaining3 →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+209)),
      OeisA249609.isEvil ((2 ^ (3240*q+209)).choose k) = true

theorem main : H1 → H2 → H3 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro h1 h2 h3 q hq
  have hb := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 3240*q+209 by omega)
  rcases coverage20 q hq with h | h | h | h
  · exact witness _ 20 (by decide) (by omega) (hit20 q h)
  · exact h1 q h
  · exact h2 q h
  · exact h3 q h

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1
