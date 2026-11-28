import OMAReductions.R_Erdos982_erdos_982_R1_H1_R1

/-! Dihedral orbit representatives for subsets of two or three vertices of a decagon. -/

namespace Erdos982Orbits

private def move (r : Nat) (reverse : Bool) (i : Nat) : Nat :=
  if reverse then (r + 10 - i) % 10 else (r + i) % 10

private def two : List Nat := [3, 5, 9, 17, 33]
private def three : List Nat := [515, 832, 19, 42, 35, 74, 69, 290]

private def encode (a : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => encode a n ||| (if a n then 1 <<< n else 0)

private theorem encode_bound (a : Nat → Bool) (n : Nat) : encode a n < 2^n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    simp only [encode]
    have h : 2^n < 2^(n+1) := by simp [Nat.pow_succ]
    apply Nat.or_lt_two_pow (ih.trans h)
    cases a n <;> simp [Nat.shiftLeft_eq, h]

private theorem encode_test (a : Nat → Bool) (n i : Nat) (hi : i < n) :
    (encode a n).testBit i = a i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      have below := Nat.testBit_lt_two_pow (encode_bound a n)
      cases ha : a n <;> simp [encode, below, ha, Nat.shiftLeft_eq]
    · have smaller : i < n := by omega
      have inner := ih smaller
      cases ha : a n <;> simp [encode, ha, inner, Nat.shiftLeft_eq, Ne.symm he]

private def count (a : Nat → Bool) : Nat := ((List.range 10).filter a).length

private def samePositions (bits target shift : Nat) (reverse : Bool) : Bool :=
  (List.range 10).all fun i => bits.testBit (move shift reverse i) == target.testBit i

private def applies (bits : Nat) (targets : List Nat) : Bool :=
  targets.any fun mask => (List.range 10).any fun r =>
    samePositions bits mask r false || samePositions bits mask r true

private def rule (bits : Nat) : Bool :=
  match count bits.testBit with
  | 2 => applies bits two
  | 3 => applies bits three
  | _ => true

private def verified (start : Nat) : Bool :=
  (List.range' start 64).all rule

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 70000 in
private theorem allRanges : ∀ x : Fin 16, verified (64*x.val) = true := by
  intro x
  fin_cases x <;> decide +kernel

private theorem allRules (b : Nat) (hb : b < 1024) : rule b = true := by
  let major : Fin 16 := ⟨b / 64, by omega⟩
  have he := allRanges major
  have hblock : b ∈ List.range' (64*major.val) 64 := by
    apply List.mem_range'_1.mpr
    dsimp [major]
    omega
  exact List.all_eq_true.mp he b hblock

theorem normalize (a : Nat → Bool) (card : Nat) (lo : 2 ≤ card) (hi : card ≤ 3)
    (hcount : ((List.range 10).filter a).length = card) :
    ∃ mask ∈ (if card = 2 then two else three), ∃ r < 10, ∃ reverse,
      ∀ i < 10, a (move r reverse i) = mask.testBit i := by
  let bits := encode a 10
  have hbits : bits < 1024 := encode_bound a 10
  have total := allRules bits hbits
  have count_eq : count bits.testBit = card := by
    unfold count
    rw [← hcount]
    apply congrArg List.length
    apply List.filter_congr
    intro i hi
    exact encode_test a 10 i (List.mem_range.mp hi)
  have found : applies bits (if card = 2 then two else three) = true := by
    unfold rule at total
    rw [count_eq] at total
    interval_cases card <;> exact total
  obtain ⟨mask,hm,someMatch⟩ := List.any_eq_true.mp found
  obtain ⟨r,hr,oneDirection⟩ := List.any_eq_true.mp someMatch
  have hrot : r < 10 := List.mem_range.mp hr
  obtain fwd | bwd := Bool.or_eq_true_iff.mp oneDirection
  · refine ⟨mask, hm, r, hrot, false, ?_⟩
    intro i hi
    have he := List.all_eq_true.mp fwd i (List.mem_range.mpr hi)
    have hmove : move r false i < 10 := Nat.mod_lt _ (by decide)
    have hbit : bits.testBit (move r false i) = a (move r false i) := encode_test a 10 _ hmove
    simpa [hbit] using he
  · refine ⟨mask, hm, r, hrot, true, ?_⟩
    intro i hi
    have he := List.all_eq_true.mp bwd i (List.mem_range.mpr hi)
    have hmove : move r true i < 10 := Nat.mod_lt _ (by decide)
    have hbit : bits.testBit (move r true i) = a (move r true i) := encode_test a 10 _ hmove
    simpa [hbit] using he

end Erdos982Orbits

open Std.Sat

namespace OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1

private structure FinitePair (P : Prop) where
  small : CNF Nat
  large : CNF Nat
  eq : P = (small.Unsat ∧ large.Unsat)

private def finitePair : FinitePair OMA.R_Erdos982_erdos_982_R1.H1 := by
  unfold OMA.R_Erdos982_erdos_982_R1.H1
  exact ⟨_, _, rfl⟩

private def normalized (masks : List Nat) : Prop :=
  ∀ mask ∈ masks, ∀ r < 10, ∀ reverse : Bool, ∀ a : Nat → Bool,
    (∀ i < 10, a (20000 + Erdos982Orbits.move r reverse i) = mask.testBit i) →
    finitePair.large.eval a = false

private lemma count_eq (a : Nat → Bool) :
    ((List.finRange 10).filter (fun i => a (20000+i.val))).length =
      ((List.range 10).filter (fun i => a (20000+i))).length := by
  have values : (List.finRange 10).map Fin.val = List.range 10 := by decide +kernel
  simp only [← values, List.filter_map, List.length_map]
  rfl

def H1 : Prop := normalized [3, 5]

def H2 : Prop := normalized [9, 17, 33]

def H3 : Prop := normalized [515, 832, 19, 42]

def H4 : Prop := normalized [35, 74, 69, 290]

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos982_erdos_982_R1_H1_R1.H2 := by
  intro smallTwo largeTwo smallThree largeThree a
  dsimp only
  intro low high
  change 2 ≤ ((List.finRange 10).filter (fun i => a (20000+i.val))).length at low
  change ((List.finRange 10).filter (fun i => a (20000+i.val))).length ≤ 3 at high
  change finitePair.large.eval a = false
  rw [count_eq] at low high
  set n := ((List.range 10).filter (fun i => a (20000+i))).length with hn
  obtain ⟨mask, member, r, hr, reverse, hm⟩ :=
    Erdos982Orbits.normalize (fun i => a (20000+i)) n low high hn.symm
  by_cases isTwo : n = 2
  · rw [if_pos isTwo, show Erdos982Orbits.two = [3, 5] ++ [9, 17, 33] from rfl] at member
    rcases List.mem_append.mp member with hl | hh
    · exact smallTwo mask hl r hr reverse a hm
    · exact largeTwo mask hh r hr reverse a hm
  · rw [if_neg isTwo, show Erdos982Orbits.three = [515, 832, 19, 42] ++ [35, 74, 69, 290] from rfl] at member
    rcases List.mem_append.mp member with hl | hh
    · exact smallThree mask hl r hr reverse a hm
    · exact largeThree mask hh r hr reverse a hm

end OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1