import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases

-- Credit: @avivorly

namespace WeightSixteenCubicGeometry

open Finset

def together (A : Fin 8 → Fin 111 → Bool) (p : Fin 111) (a b : Fin 8) : Prop :=
  A a p = true ∧ A b p = true

noncomputable def outer (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a : Fin 8) :
    Finset (Fin 8) := by
  classical
  exact Finset.univ.filter fun b => b ≠ a ∧ ∃ p ∉ S, together A p a b

noncomputable def inner (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a : Fin 8) :
    Finset (Fin 8) := by
  classical
  exact Finset.univ.filter fun b => b ≠ a ∧ ∃ p ∈ S, together A p a b

lemma mem_outer (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a b : Fin 8) :
    b ∈ outer A S a ↔ b ≠ a ∧ ∃ p ∉ S, together A p a b := by
  classical
  simp [outer]

lemma mem_inner (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a b : Fin 8) :
    b ∈ inner A S a ↔ b ≠ a ∧ ∃ p ∈ S, together A p a b := by
  classical
  simp [inner]

theorem outer_symm (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a b : Fin 8) :
    b ∈ outer A S a ↔ a ∈ outer A S b := by
  rw [mem_outer, mem_outer]
  constructor <;> rintro ⟨different, p, outside, on_a, on_b⟩
  · exact ⟨different.symm,p,outside,on_b,on_a⟩
  · exact ⟨different.symm,p,outside,on_b,on_a⟩

theorem outer_irrefl (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a : Fin 8) :
    a ∉ outer A S a := by simp [mem_outer]

lemma second_row (A : Fin 8 → Fin 111 → Bool) (p : Fin 111)
    (rows : (Finset.univ.filter fun l => A l p = true).card = 2)
    (a : Fin 8) (on_a : A a p = true) : ∃! b, b ≠ a ∧ A b p = true := by
  let here : Finset (Fin 8) := Finset.univ.filter fun r => A r p = true
  have contains_a : a ∈ here := Finset.mem_filter.mpr ⟨Finset.mem_univ _,on_a⟩
  have residual : (here.erase a).card = 1 := by
    rw [Finset.card_erase_of_mem contains_a]
    exact Nat.sub_eq_of_eq_add rows
  obtain ⟨b, represented⟩ := Finset.card_eq_one.mp residual
  have iff_mem (r : Fin 8) : r ∈ here.erase a ↔ r ≠ a ∧ A r p = true := by
    simp [here, Finset.mem_erase, Finset.mem_filter]
  have hb : b ∈ here.erase a := by rw [represented]; exact Finset.mem_singleton_self b
  refine ⟨b,(iff_mem b).mp hb,fun r hr => ?_⟩
  have h := (iff_mem r).mpr hr
  rw [represented] at h
  exact Finset.mem_singleton.mp h

lemma cardinal_inner (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (share : ∀ a b, a ≠ b → ∃! p, together A p a b)
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (a : Fin 8) (line_four : (S.filter fun p => A a p = true).card = 4) :
    (inner A S a).card = 4 := by
  classical
  let on_line := S.filter fun p => A a p = true
  have second (p : Fin 111) (hp : p ∈ on_line) : ∃! b, b ≠ a ∧ A b p = true := by
    obtain ⟨inS, onA⟩ := Finset.mem_filter.mp hp
    exact second_row A p (degree_two p inS) a onA
  let other (p : Fin 111) (hp : p ∈ on_line) := Classical.choose (second p hp)
  have other_good (p : Fin 111) (hp : p ∈ on_line) :
      (other p hp ≠ a ∧ A (other p hp) p = true) ∧
      ∀ b, b ≠ a ∧ A b p = true → b = other p hp := Classical.choose_spec (second p hp)
  have bij : on_line.card = (inner A S a).card := by
    apply Finset.card_bij other
    · intro p hp
      obtain ⟨inS, onA⟩ := Finset.mem_filter.mp hp
      obtain ⟨different, onB⟩ := (other_good p hp).1
      exact (mem_inner A S a _).mpr ⟨different,p,inS,onA,onB⟩
    · intro p hp q hq eq
      obtain ⟨_, _, unique⟩ := share a (other p hp) ((other_good p hp).1.1.symm)
      have one : together A p a (other p hp) :=
        ⟨(Finset.mem_filter.mp hp).2,(other_good p hp).1.2⟩
      have two : together A q a (other p hp) :=
        ⟨(Finset.mem_filter.mp hq).2,eq.symm ▸ (other_good q hq).1.2⟩
      exact (unique p one).trans (unique q two).symm
    · intro b hb
      obtain ⟨different,p,inS,onA,onB⟩ := (mem_inner A S a b).mp hb
      have hp : p ∈ on_line := Finset.mem_filter.mpr ⟨inS,onA⟩
      exact ⟨p,hp,((other_good p hp).2 b ⟨different,onB⟩).symm⟩
  exact bij.symm.trans line_four

theorem exterior_cubic (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (share : ∀ a b, a ≠ b → ∃! p, together A p a b)
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (line_four : ∀ a, (S.filter fun p => A a p = true).card = 4)
    (a : Fin 8) : (outer A S a).card = 3 := by
  classical
  have inner_four := cardinal_inner A S share degree_two a (line_four a)
  have separated : Disjoint (inner A S a) (outer A S a) := by
    rw [Finset.disjoint_left]
    intro b hb hc
    obtain ⟨different,p,inside,hp⟩ := (mem_inner A S a b).mp hb
    obtain ⟨_,q,outside,hq⟩ := (mem_outer A S a b).mp hc
    obtain ⟨_, _, unique⟩ := share a b different.symm
    have same := (unique p hp).trans (unique q hq).symm
    exact outside (same ▸ inside)
  have total : inner A S a ∪ outer A S a = Finset.univ.erase a := by
    ext b
    simp only [Finset.mem_union, mem_inner, mem_outer, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (⟨different,_⟩ | ⟨different,_⟩) <;> exact different
    · intro different
      obtain ⟨p,on_rows,_⟩ := share a b different.symm
      by_cases inside : p ∈ S
      · exact Or.inl ⟨different,p,inside,on_rows⟩
      · exact Or.inr ⟨different,p,inside,on_rows⟩
  have count := Finset.card_union_of_disjoint separated
  rw [total, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin, inner_four] at count
  omega

theorem normalize_first_neighbors (neighbors : Finset (Fin 8)) (size : neighbors.card = 3)
    (zero_outside : 0 ∉ neighbors) :
    ∃ e : Equiv.Perm (Fin 8), e 0 = 0 ∧
      ∀ j, e j ∈ neighbors ↔ j = 1 ∨ j = 2 ∨ j = 3 := by
  let wanted : Finset (Fin 8) := {1, 2, 3}
  have wanted_size : wanted.card = 3 := by decide
  have zero_missing : 0 ∉ wanted := by decide
  let ew : ↥wanted ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using wanted_size)
  let en : ↥neighbors ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using size)
  let adjust : ↥wanted ≃ ↥neighbors := ew.trans en.symm
  let initial : Equiv.Perm (Fin 8) := adjust.extendSubtype
  have image_eq (j : Fin 8) : initial j ∈ neighbors ↔ j ∈ wanted := by
    by_cases inside : j ∈ wanted
    · exact iff_of_true (Equiv.extendSubtype_mem adjust _ inside) inside
    · exact iff_of_false (Equiv.extendSubtype_not_mem adjust _ inside) inside
  have initialZero : initial 0 ∉ neighbors := fun inside => zero_missing ((image_eq 0).mp inside)
  let restore := Equiv.swap (initial 0) 0
  have restore_mem (j : Fin 8) : restore j ∈ neighbors ↔ j ∈ neighbors := by
    by_cases first : j = initial 0
    · subst j
      simpa only [restore, Equiv.swap_apply_left] using iff_of_false zero_outside initialZero
    by_cases second : j = 0
    · subst j
      simpa only [restore, Equiv.swap_apply_right] using iff_of_false initialZero zero_outside
    rw [show restore j = j from Equiv.swap_apply_of_ne_of_ne first second]
  refine ⟨initial.trans restore, Equiv.swap_apply_left _ _, ?_⟩
  intro j
  change restore (initial j) ∈ neighbors ↔ _
  rw [restore_mem, image_eq]
  simp [wanted]

end WeightSixteenCubicGeometry

namespace WeightSixteenTripleProjection

open Finset
open WeightSixteenCubicGeometry

theorem free_internal_neighbors (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (T : Finset (Fin 8)) (degree : ∀ p ∈ S, (Finset.univ.filter fun a => A a p = true).card = 2)
    (rowPairs : ∀ a b, a ≠ b → ∃! p, A a p = true ∧ A b p = true)
    (a : Fin 8) (outsideT : a ∉ T) :
    (S.filter fun p => A a p = true ∧ ∀ b ∈ T, A b p = false).card =
    (Finset.univ.filter fun b => b ≠ a ∧ b ∉ T ∧ ¬ (∃ p ∉ S, A a p = true ∧ A b p = true)).card := by
  classical
  let free := S.filter fun p => A a p = true ∧ ∀ b ∈ T, A b p = false
  let candidates := Finset.univ.filter
    fun b => b ≠ a ∧ b ∉ T ∧ ¬ (∃ p ∉ S, A a p = true ∧ A b p = true)
  have picked (p : Fin 111) (hp : p ∈ free) : ∃! b, b ≠ a ∧ A b p = true :=
    second_row A p (degree p (Finset.mem_filter.mp hp).1) a (Finset.mem_filter.mp hp).2.1
  let other (p : Fin 111) (hp : p ∈ free) := Classical.choose (picked p hp)
  have spec (p : Fin 111) (hp : p ∈ free) :
      (other p hp ≠ a ∧ A (other p hp) p = true) ∧
      ∀ b, b ≠ a ∧ A b p = true → b = other p hp :=
    Classical.choose_spec (picked p hp)
  change free.card = candidates.card
  apply Finset.card_bij other
  · intro p hp
    obtain ⟨inS,ona,off⟩ := Finset.mem_filter.mp hp
    obtain ⟨ne,onb⟩ := (spec p hp).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne,?_,?_⟩
    · intro insideT
      have notOn := off _ insideT
      rw [notOn] at onb
      contradiction
    · rintro ⟨r,outside,hr⟩
      obtain ⟨_,_,unique⟩ := rowPairs a _ ne.symm
      have eq := (unique p ⟨ona,onb⟩).trans (unique r hr).symm
      exact outside (eq ▸ inS)
  · intro p hp q hq equal
    obtain ⟨ne,onb⟩ := (spec p hp).1
    have onq := (spec q hq).1.2
    rw [← equal] at onq
    obtain ⟨_,_,unique⟩ := rowPairs a _ ne.symm
    exact (unique p ⟨(Finset.mem_filter.mp hp).2.1,onb⟩).trans
      (unique q ⟨(Finset.mem_filter.mp hq).2.1,onq⟩).symm
  · intro b hb
    obtain ⟨_,ne,outB,noOuter⟩ := Finset.mem_filter.mp hb
    obtain ⟨p,onBoth,_⟩ := rowPairs a b ne.symm
    have inS : p ∈ S := by
      by_contra outside
      exact noOuter ⟨p,outside,onBoth⟩
    obtain ⟨d,_,unique⟩ := second_row A p (degree p inS) a onBoth.1
    have bd : b = d := unique b ⟨ne,onBoth.2⟩
    have not_in (c : Fin 8) (hc : c ∈ T) : A c p = false := by
      cases val : A c p with
      | false => rfl
      | true =>
        have ca : c ≠ a := fun same => outsideT (same ▸ hc)
        have cb := (unique c ⟨ca,val⟩).trans bd.symm
        exact False.elim (outB (cb ▸ hc))
    have hp : p ∈ free := Finset.mem_filter.mpr ⟨inS,onBoth.1,not_in⟩
    exact ⟨p,hp,((spec p hp).2 b ⟨ne,onBoth.2⟩).symm⟩

end WeightSixteenTripleProjection

namespace FiniteSearchMasks

variable {α : Type}

def bitMask (xs : List α) (chosen : α → Bool) : Nat :=
  (xs.zipIdx.map fun (x, i) => if chosen x then 2^i else 0).foldr Nat.lor 0

lemma foldr_or_testBit (words : List Nat) (i : Nat) :
    (words.foldr Nat.lor 0).testBit i = true ↔ ∃ n ∈ words, n.testBit i = true := by
  induction words with
  | nil => simp
  | cons word words ih =>
      change (word ||| words.foldr Nat.lor 0).testBit i = true ↔ _
      simp only [Nat.testBit_lor, Bool.or_eq_true, ih, List.mem_cons]
      constructor
      · intro h
        rcases h with bit | ⟨n, hn, bit⟩
        · exact ⟨word, Or.inl rfl, bit⟩
        · exact ⟨n, Or.inr hn, bit⟩
      · rintro ⟨n, h, bit⟩
        rcases h with rfl | mem
        · exact Or.inl bit
        · exact Or.inr ⟨n, mem, bit⟩

theorem bitMask_testBit (xs : List α) (chosen : α → Bool) (i : Nat) :
    (bitMask xs chosen).testBit i = true ↔ ∃ x, xs[i]? = some x ∧ chosen x = true := by
  rw [bitMask, foldr_or_testBit]
  constructor
  · rintro ⟨n, member, set⟩
    obtain ⟨⟨x,j⟩, hxj, rfl⟩ := List.mem_map.mp member
    cases hx : chosen x with
    | false => simp [hx] at set
    | true =>
      have ji : j = i := by simpa [hx, Nat.testBit_two_pow] using set
      subst j
      exact ⟨x, List.mk_mem_zipIdx_iff_getElem?.mp hxj, hx⟩
  · rintro ⟨x, hx, chosen_x⟩
    refine ⟨2^i, ?_, Nat.testBit_two_pow_self⟩
    apply List.mem_map.mpr
    exact ⟨(x,i), List.mk_mem_zipIdx_iff_getElem?.mpr hx, by simp [chosen_x]⟩

lemma bitMask_getElem_testBit (xs : List α) (chosen : α → Bool) (i : ℕ) (in_list : i < xs.length) :
    (bitMask xs chosen).testBit i = chosen xs[i] := by
  apply Bool.eq_iff_iff.mpr
  rw [bitMask_testBit]
  simp [List.getElem?_eq_getElem in_list]

end FiniteSearchMasks


namespace WeightSixteenCubicGraphs

open Finset FiniteSearchMasks

def rowMasks : List Nat := [0x7f, 0x1f81, 0x3e082, 0x3c2104, 0x1c44208, 0x6488410, 0xa910820, 0xd221040]

def rowMask (v : Nat) : Nat := rowMasks[v]?.getD 0

def offset (v : Fin 7) : Nat := ([0,7,13,18,22,25,27] : List Nat)[v.val]?.getD 0

def width (v : Fin 7) : Nat := 7-v.val

def countBits : Nat → Nat → Nat
  | 0, _ => 0
  | steps+1, word => if word = 0 then 0 else
    1 + countBits steps (word ^^^ 2^word.log2)

def degree (code v : Nat) : Nat := countBits 7 (code &&& rowMask v)

def edgeIndex (i j : Nat) : Nat :=
  let a := min i j
  let b := max i j
  a * (15-a)/2 + (b-a-1)


lemma countBits_correct (steps w : Nat) (S : Finset Nat) (size : S.card ≤ steps)
    (agreement : ∀ i, w.testBit i = true ↔ i ∈ S) : countBits steps w = S.card := by
  induction steps generalizing w S with
  | zero =>
    have empty : S.card = 0 := by omega
    exact empty.symm
  | succ n ih =>
    by_cases zero : w = 0
    · have none : S = ∅ := by
        ext i
        rw [← agreement i, zero]
        simp
      simp [countBits, zero, none]
    · let i := w.log2
      have chosen : i ∈ S := (agreement i).mp (Nat.testBit_log2 zero)
      have bit : w.testBit i = true := Nat.testBit_log2 zero
      have size' : (S.erase i).card ≤ n := by
        rw [Finset.card_erase_of_mem chosen]
        omega
      have reduced (j : Nat) :
          (w ^^^ 2^i).testBit j = true ↔ j ∈ S.erase i := by
        by_cases same : j = i
        · subst j
          simp [Nat.testBit_xor, Nat.testBit_two_pow_self, bit]
        · simp only [Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm same, decide_false,
            Bool.xor_false, Finset.mem_erase]
          exact (agreement j).trans ⟨fun hit => ⟨same,hit⟩, fun hit => hit.2⟩
      simp only [countBits, if_neg zero]
      change 1 + countBits n (w ^^^ 2^i) = _
      rw [ih _ _ size' reduced, Finset.card_erase_of_mem chosen]
      have positive := Finset.card_pos.mpr ⟨i, chosen⟩
      omega

def pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]

lemma pairs_size : pairs.length = 28 := rfl

def pairOf (i : Fin 28) : Fin 8 × Fin 8 := pairs[i.val]'(by simpa only [pairs_size] using i.isLt)

def neighbor (v : Fin 8) (i : Fin 28) : Fin 8 :=
  if (pairOf i).1 = v then (pairOf i).2 else (pairOf i).1

def encode (g : Fin 8 → Fin 8 → Bool) : Nat :=
  bitMask pairs (fun (v,w) => g v w)

lemma encode_bit (g : Fin 8 → Fin 8 → Bool) (i : Fin 28) :
    (encode g).testBit i.val = g (pairOf i).1 (pairOf i).2 := by
  unfold encode pairOf
  exact bitMask_getElem_testBit _ _ _ (by simpa only [pairs_size] using i.isLt)

lemma encode_off (g : Fin 8 → Fin 8 → Bool) (i : Nat) (outside : 28 ≤ i) :
    (encode g).testBit i = false := by
  by_contra on
  have yes : (encode g).testBit i = true := Bool.eq_true_of_not_eq_false on
  obtain ⟨edge, found, _⟩ := (bitMask_testBit _ _ _).mp yes
  rw [List.getElem?_eq_none (by simpa only [pairs_size] using outside)] at found
  contradiction

lemma encode_bound (g : Fin 8 → Fin 8 → Bool) : encode g < 2^28 := by
  by_cases empty : encode g = 0
  · simp [empty]
  · apply (Nat.log2_lt empty).mp
    by_contra outside
    exact Bool.false_ne_true ((encode_off g _ (Nat.le_of_not_gt outside)).symm.trans (Nat.testBit_log2 empty))

lemma row_bit : ∀ (v : Fin 8) (i : Fin 28),
    (rowMask v.val).testBit i.val = decide ((pairOf i).1 = v ∨ (pairOf i).2 = v) := by decide +kernel

lemma index_of_pair (v : Fin 8) (i : Fin 28)
    (joined : (pairOf i).1 = v ∨ (pairOf i).2 = v) :
    edgeIndex v.val (neighbor v i).val = i.val := by
  have Numeric : ∀ v : Fin 8, ∀ i : Fin 28, (pairOf i).1 = v ∨ (pairOf i).2 = v →
      edgeIndex v.val (neighbor v i).val = i.val := by decide +kernel
  exact Numeric v i joined

lemma neighbor_different (v : Fin 8) (i : Fin 28) : neighbor v i ≠ v := by
  have Numeric : ∀ v : Fin 8, ∀ i : Fin 28, neighbor v i ≠ v := by decide +kernel
  exact Numeric v i

lemma ordered_pair_exists (v w : Fin 8) (different : v ≠ w) :
    ∃ i : Fin 28, pairOf i = (v,w) ∨ pairOf i = (w,v) := by
  have Numeric : ∀ v w : Fin 8, v ≠ w →
      ∃ i : Fin 28, pairOf i = (v,w) ∨ pairOf i = (w,v) := by decide +kernel
  exact Numeric v w different

lemma relevant_bit (g : Fin 8 → Fin 8 → Bool) (symm : ∀ x y, g x y = g y x)
    (v : Fin 8) (i : Fin 28) :
    (encode g &&& rowMask v.val).testBit i.val = true ↔
      ((pairOf i).1 = v ∨ (pairOf i).2 = v) ∧ g v (neighbor v i) = true := by
  rw [Nat.testBit_land, encode_bit, row_bit, Bool.and_eq_true, decide_eq_true_eq, and_comm]
  by_cases first : (pairOf i).1 = v
  · simp [first, neighbor]
  by_cases second : (pairOf i).2 = v
  · simp [first, second, neighbor, symm (pairOf i).1 v]
  · simp [first, second]

theorem degree_encode (g : Fin 8 → Fin 8 → Bool) (symm : ∀ x y, g x y = g y x)
    (loopfree : ∀ x, g x x = false) (v : Fin 8) :
    degree (encode g) v.val = (Finset.univ.filter fun w => g v w = true).card := by
  classical
  let bs : Finset (Fin 28) := Finset.univ.filter fun i => (encode g &&& rowMask v.val).testBit i.val = true
  let ns : Finset (Fin 8) := Finset.univ.filter fun w => g v w = true
  have chosen (i : Fin 28) : i ∈ bs ↔
      ((pairOf i).1 = v ∨ (pairOf i).2 = v) ∧ g v (neighbor v i) = true := by
    simpa only [bs, Finset.mem_filter, Finset.mem_univ, true_and] using relevant_bit g symm v i
  have card_eq : bs.card = ns.card := by
    apply Finset.card_bij (fun i _ => neighbor v i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((chosen i).mp hi).2⟩
    · intro i hi j hj eq
      apply Fin.ext
      have left := index_of_pair v i ((chosen i).mp hi).1
      have right := index_of_pair v j ((chosen j).mp hj).1
      rw [eq] at left
      exact left.symm.trans right
    · intro w hw
      have active := (Finset.mem_filter.mp hw).2
      have different : v ≠ w := by intro same; subst w; simp [loopfree] at active
      obtain ⟨i, orientation⟩ := ordered_pair_exists v w different
      obtain first | second := orientation
      · have pick : neighbor v i = w := by simp [neighbor, first]
        exact ⟨i,(chosen i).mpr ⟨Or.inl (by rw [first]), by rwa [pick]⟩,pick⟩
      · have pick : neighbor v i = w := by simp [neighbor, second, different.symm]
        exact ⟨i,(chosen i).mpr ⟨Or.inr (by rw [second]), by rwa [pick]⟩,pick⟩
  let selected := bs.image Fin.val
  have count_selected : selected.card = bs.card := Finset.card_image_of_injective bs Fin.val_injective
  have bounded : ns.card ≤ 7 := by
    have inside : ns ⊆ Finset.univ.erase v := by
      intro w hw
      refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
      intro same
      subst w
      have active := (Finset.mem_filter.mp hw).2
      simp [loopfree] at active
    have count := Finset.card_le_card inside
    rwa [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin] at count
  have agreement (i : Nat) :
      (encode g &&& rowMask v.val).testBit i = true ↔ i ∈ selected := by
    by_cases within : i < 28
    · constructor
      · intro hit
        exact Finset.mem_image.mpr ⟨⟨i,within⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩, rfl⟩
      · intro hi
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hj).2
    · have bit := encode_off g i (Nat.le_of_not_gt within)
      have absent : i ∉ selected := by
        intro hi
        obtain ⟨j,_,same⟩ := Finset.mem_image.mp hi
        exact within (same ▸ j.isLt)
      simp [bit, absent]
  have values := countBits_correct 7 (encode g &&& rowMask v.val) selected
    (count_selected.trans card_eq ▸ bounded) agreement
  change countBits 7 (encode g &&& rowMask v.val) = ns.card
  exact values.trans (count_selected.trans card_eq)

end WeightSixteenCubicGraphs

namespace WeightSixteenCubicGraphs

open Finset WeightSixteenCubicGeometry

lemma first_pairs : ∀ i : Fin 7,
    (pairOf ⟨i.val, by omega⟩).1 = 0 ∧
    ((7 : Nat).testBit i.val = true ↔
      (pairOf ⟨i.val, by omega⟩).2 = 1 ∨
      (pairOf ⟨i.val, by omega⟩).2 = 2 ∨
      (pairOf ⟨i.val, by omega⟩).2 = 3) := by decide +kernel

lemma first_row_encoding (g : Fin 8 → Fin 8 → Bool)
    (row : ∀ j, g 0 j = true ↔ j = 1 ∨ j = 2 ∨ j = 3) :
    encode g &&& (2^7-1) = 7 := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases within : j < 7
  · let i : Fin 7 := ⟨j,within⟩
    let k : Fin 28 := ⟨j,by omega⟩
    rw [Nat.testBit_land, Nat.testBit_two_pow_sub_one, decide_eq_true within, Bool.and_true]
    change (encode g).testBit k.val = (7:Nat).testBit i.val
    rw [encode_bit, (first_pairs i).1]
    exact Bool.eq_iff_iff.mpr ((row (pairOf k).2).trans (first_pairs i).2.symm)
  · have zero := Nat.testBit_lt_two_pow ((show 7 < 2^7 by decide).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt within)))
    simp only [Nat.testBit_land, Nat.testBit_two_pow_sub_one, decide_eq_false within,
      Bool.and_false, zero]

noncomputable def exteriorGraph
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (e : Equiv.Perm (Fin 8))
    (a b : Fin 8) : Bool :=
  decide (e b ∈ outer A S (e a))

lemma exteriorGraph_symm
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (e : Equiv.Perm (Fin 8)) :
    ∀ a b, exteriorGraph A S e a b = exteriorGraph A S e b a := by
  intro a b
  apply Bool.eq_iff_iff.mpr
  simpa only [exteriorGraph, decide_eq_true_eq] using outer_symm A S (e a) (e b)

lemma exteriorGraph_loopfree
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (e : Equiv.Perm (Fin 8)) :
    ∀ a, exteriorGraph A S e a a = false := by
  intro a
  exact decide_eq_false (outer_irrefl A S (e a))

lemma exteriorGraph_degree
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (e : Equiv.Perm (Fin 8)) (a : Fin 8) :
    (Finset.univ.filter fun b => exteriorGraph A S e a b = true).card =
      (outer A S (e a)).card := by
  apply Finset.card_bij (fun b _ => e b)
  · intro b hb
    exact of_decide_eq_true (Finset.mem_filter.mp hb).2
  · intro b _ c _ equal
    exact e.injective equal
  · intro b hb
    refine ⟨e.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,e.apply_symm_apply b⟩
    simp [exteriorGraph, hb]

theorem encode_exterior_normalized
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (share : ∀ a b, a ≠ b → ∃! p, together A p a b)
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (line_four : ∀ a, (S.filter fun p => A a p = true).card = 4) :
    ∃ e : Equiv.Perm (Fin 8), e 0 = 0 ∧
      (encode (exteriorGraph A S e) &&& (2^7-1) = 7) ∧
      ∀ v < 8, degree (encode (exteriorGraph A S e)) v = 3 := by
  have actual := exterior_cubic A S share degree_two line_four
  obtain ⟨e, fixed, across⟩ := normalize_first_neighbors (outer A S 0) (actual 0) (outer_irrefl A S 0)
  have row (j : Fin 8) : exteriorGraph A S e 0 j = true ↔ j = 1 ∨ j = 2 ∨ j = 3 := by
    simpa only [exteriorGraph, decide_eq_true_eq, fixed] using across j
  refine ⟨e,fixed,first_row_encoding _ row,?_⟩
  intro v small
  let j : Fin 8 := ⟨v,small⟩
  change degree (encode (exteriorGraph A S e)) j.val = 3
  rw [degree_encode _ (exteriorGraph_symm A S e) (exteriorGraph_loopfree A S e),
    exteriorGraph_degree]
  exact actual (e j)

end WeightSixteenCubicGraphs

namespace WeightSixteenCubicGraphs

lemma edgeIndex_comm (a b : Nat) : edgeIndex a b = edgeIndex b a := by
  simp [edgeIndex, min_comm a b, max_comm a b]

lemma index_pairOf : ∀ i : Fin 28, edgeIndex (pairOf i).1.val (pairOf i).2.val = i.val := by
  decide +kernel

end WeightSixteenCubicGraphs

namespace WeightSixteenTripleNumerics

open Finset
open WeightSixteenCubicGraphs

def adj (r : Nat) (a b : Fin 8) : Bool :=
  decide (a ≠ b) && r.testBit (edgeIndex a.val b.val)

def CanHold (G : Fin 8 → Fin 8 → Bool) (T : Finset (Fin 8)) : Prop :=
  T.card = 3 ∧
    (∀ a ∈ T, ∀ b ∈ T, a ≠ b → G a b = true) ∧
    ∀ a ∉ T, (Finset.univ.filter fun b => b ≠ a ∧ b ∉ T ∧ G a b = false).card ≤ 2

instance (G : Fin 8 → Fin 8 → Bool) (T : Finset (Fin 8)) : Decidable (CanHold G T) := by
  unfold CanHold
  infer_instance

lemma recover_adjacency (G : Fin 8 → Fin 8 → Bool) (symm : ∀ a b, G a b = G b a)
    (loop : ∀ a, G a a = false) : adj (encode G) = G := by
  funext a b
  by_cases equal : a = b
  · subst b
    simp [adj,loop a]
  obtain ⟨x,shape⟩ := ordered_pair_exists a b equal
  have bit := encode_bit G x
  have at_index := index_pairOf x
  have index : edgeIndex a.val b.val = x.val := by
    rcases shape with ab | ba
    · simpa only [ab] using at_index
    · rw [edgeIndex_comm]
      simpa only [ba] using at_index
  change (decide (a ≠ b) && (encode G).testBit (edgeIndex a.val b.val)) = G a b
  rw [index]
  simp only [equal,ne_eq,not_false_eq_true,decide_true,Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  rw [bit]
  rcases shape with ab | ba
  · simp [ab]
  · simpa only [ba] using (show G b a = true ↔ G a b = true by rw [symm b a])

end WeightSixteenTripleNumerics

namespace WeightSixteenSaturatedColumn

open Finset
open scoped BigOperators

theorem saturated_column {R P : Type} [Fintype R] [Fintype P] [DecidableEq R] [DecidableEq P]
    (M : R → P → Bool) (pointCount : Fintype.card P = 111)
    (rowSize : ∀ l, (Finset.univ.filter fun q => M l q = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (p : P) (onSize : (Finset.univ.filter fun l => M l p = true).card = 11) :
    ∀ q, p ≠ q → ∃! l, M l p = true ∧ M l q = true := by
  let on := Finset.univ.filter fun l => M l p = true
  let ray (l : R) := (Finset.univ.filter fun q => M l q = true).erase p
  let covered := on.biUnion ray
  let other : Finset P := Finset.univ.erase p
  have rays_disjoint : (on : Set R).PairwiseDisjoint ray := by
    intro a ha b hb different
    change Disjoint (ray a) (ray b)
    rw [Finset.disjoint_left]
    intro q qa qb
    obtain ⟨ne,in_a⟩ := Finset.mem_erase.mp qa
    obtain ⟨_,in_b⟩ := Finset.mem_erase.mp qb
    exact different (columnPairs p q ne.symm a b
      (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2 (Finset.mem_filter.mp in_a).2
      (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2 (Finset.mem_filter.mp in_b).2)
  have ray_size (l : R) (hl : l ∈ on) : (ray l).card = 10 := by
    change ((Finset.univ.filter fun q => M l q = true).erase p).card = 10
    have on_l : p ∈ Finset.univ.filter (fun q => M l q = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    rw [Finset.card_erase_of_mem on_l,rowSize]
  have matched : covered.card = 110 := by
    change (on.biUnion ray).card = 110
    rw [Finset.card_biUnion rays_disjoint,Finset.sum_congr rfl ray_size,Finset.sum_const,Nat.nsmul_eq_mul]
    change (Finset.univ.filter fun l => M l p = true).card * 10 = 110
    rw [onSize]
  have other_size : other.card = 110 := by
    change ((Finset.univ : Finset P).erase p).card = 110
    rw [Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,pointCount]
  have subset : covered ⊆ other := by
    intro q hq
    obtain ⟨l,_,loc⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp loc).1,Finset.mem_univ _⟩
  have full : covered = other := by
    apply Finset.eq_of_subset_of_card_le subset
    rw [other_size,matched]
  intro q ne
  have elsewhere : q ∈ other := Finset.mem_erase.mpr ⟨ne.symm,Finset.mem_univ _⟩
  have some_ray : q ∈ covered := full.symm ▸ elsewhere
  obtain ⟨l,hl,present⟩ := Finset.mem_biUnion.mp some_ray
  have lp := (Finset.mem_filter.mp hl).2
  have lq := (Finset.mem_filter.mp (Finset.mem_erase.mp present).2).2
  exact ⟨l,⟨lp,lq⟩,fun m hm => columnPairs p q ne m l hm.1 hm.2 lp lq⟩

lemma count_incidence_sum {X Y : Type} [Fintype X] [Fintype Y]
    (P : X ⊕ Y → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter fun x => P (.inl x)).card +
      (Finset.univ.filter fun y => P (.inr y)).card := by
  have same : Finset.univ.filter P = (Finset.univ.filter fun x => P (.inl x)).disjSum
      (Finset.univ.filter fun y => P (.inr y)) := by
    ext l
    cases l <;> simp [Finset.mem_filter]
  rw [same,Finset.card_disjSum]

theorem free_points_on_heavy_line
    (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111))
    (rows : ∀ l, (Finset.univ.filter fun p => M l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (inside : ∀ p ∈ S, (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card = 2 ∧
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card = 9)
    (q : Fin 111) (hq : q ∉ S) (a : Fin 8) :
    let onQ := Finset.univ.filter fun b : Fin 8 => M (.inl b) q = true
    let free := S.filter fun p => M (.inl a) p = true ∧ ∀ b ∈ onQ, M (.inl b) p = false
    free.card ≤ (Finset.univ.filter fun b : Fin 72 => M (.inr b) q = true).card := by
  classical
  let onQ := Finset.univ.filter fun b : Fin 8 => M (.inl b) q = true
  let free := S.filter fun p => M (.inl a) p = true ∧ ∀ b ∈ onQ, M (.inl b) p = false
  let B := Finset.univ.filter fun b : Fin 72 => M (.inr b) q = true
  have exists_line (p : Fin 111) (hp : p ∈ free) : ∃ b ∈ B, M (.inr b) p = true := by
    obtain ⟨inS,_,off⟩ := Finset.mem_filter.mp hp
    have degree : (Finset.univ.filter fun l => M l p = true).card = 11 := by
      rw [count_incidence_sum, (inside p inS).1, (inside p inS).2]
    have ne : p ≠ q := fun equal => hq (equal ▸ inS)
    obtain ⟨l,left,_⟩ := saturated_column M (Fintype.card_fin 111) rows columnPairs p degree q ne
    cases l with
    | inl b =>
      have found : b ∈ onQ := Finset.mem_filter.mpr ⟨Finset.mem_univ _,left.2⟩
      exact False.elim (Bool.noConfusion ((off b found).symm.trans left.1))
    | inr b =>
      exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,left.2⟩,left.1⟩
  let f (p : ↥free) : ↥B := ⟨Classical.choose (exists_line p.val p.property),
    (Classical.choose_spec (exists_line p.val p.property)).1⟩
  have known (p : ↥free) : M (.inr (f p).val) p.val = true :=
    (Classical.choose_spec (exists_line p.val p.property)).2
  have injective : Function.Injective f := by
    intro p t equality
    apply Subtype.ext
    by_contra ne
    have ap := ((Finset.mem_filter.mp p.property).2).1
    have at' := ((Finset.mem_filter.mp t.property).2).1
    have bp := known p
    have bt := known t
    rw [← equality] at bt
    have wrong := columnPairs p.val t.val ne (.inl a) (.inr (f p).val) ap at' bp bt
    cases wrong
  exact Finset.card_le_card_of_injective injective

end WeightSixteenSaturatedColumn

namespace WeightSixteenTripleNumerics

open Finset WeightSixteenCubicGraphs

lemma cardinal_relabel {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x => P (e x)).card = (Finset.univ.filter P).card := by
  have mapped := Finset.filter_map (s := Finset.univ) (p := P) (f := e.toEmbedding)
  rw [Finset.map_univ_equiv] at mapped
  rw [mapped, Finset.card_map]
  rfl

theorem geometry_allows_triangle (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111))
    (rows : ∀ l, (Finset.univ.filter fun p => M l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (cols : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (inside : ∀ p ∈ S, (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card = 2 ∧
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card = 9)
    (outside : ∀ p ∉ S, 2 * (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card +
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card = 8)
    (e : Equiv.Perm (Fin 8)) (q : Fin 111) (hq : q ∉ S)
    (triple : (Finset.univ.filter fun a : Fin 8 => M (.inl a) q = true).card = 3) :
    CanHold (exteriorGraph (fun a p => M (.inl a) p) S e)
      (Finset.univ.filter fun a => M (.inl (e a)) q = true) := by
  classical
  let A (a : Fin 8) (p : Fin 111) := M (.inl a) p
  let R (a : Fin 8) (p : Fin 111) := A (e a) p
  let T := Finset.univ.filter fun a => R a q = true
  let original := Finset.univ.filter fun a => A a q = true
  let G := exteriorGraph A S e
  have T_iff (a : Fin 8) : a ∈ T ↔ R a q = true := by simp [T]
  have orig_iff (a : Fin 8) : a ∈ original ↔ A a q = true := by simp [original]
  have lead (a b : Fin 8) (ne : a ≠ b) :
      G a b = true ↔ ∃ p ∉ S, R a p = true ∧ R b p = true := by
    have distinct : e b ≠ e a := fun same => ne (e.injective same).symm
    simp [G,exteriorGraph,WeightSixteenCubicGeometry.mem_outer,distinct,R,
      WeightSixteenCubicGeometry.together]
  have B_count : (Finset.univ.filter fun b : Fin 72 => M (.inr b) q = true).card = 2 := by
    have count := outside q hq
    rw [triple] at count
    omega
  refine ⟨(cardinal_relabel e (fun a => A a q = true)).trans triple,?_,?_⟩
  · intro a ha b hb distinct
    exact (lead a b distinct).mpr ⟨q,hq,(T_iff a).mp ha,(T_iff b).mp hb⟩
  · intro a ha
    have degree (p : Fin 111) (hp : p ∈ S) : (Finset.univ.filter fun a => R a p = true).card = 2 :=
      (cardinal_relabel e (fun b => A b p = true)).trans (inside p hp).1
    have shares (a b : Fin 8) (distinct : a ≠ b) : ∃! p, R a p = true ∧ R b p = true :=
      rowPairs (.inl (e a)) (.inl (e b)) (fun same => distinct (e.injective (Sum.inl.inj same)))
    have count := WeightSixteenTripleProjection.free_internal_neighbors R S T degree shares a ha
    have same_candidates :
        (Finset.univ.filter fun b => b ≠ a ∧ b ∉ T ∧ G a b = false) =
        Finset.univ.filter fun b => b ≠ a ∧ b ∉ T ∧ ¬ (∃ p ∉ S, R a p = true ∧ R b p = true) := by
      ext b
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      apply and_congr_right
      intro ne
      apply and_congr_right
      intro _
      cases value : G a b with
      | false => simp [← lead a b (Ne.symm ne),value]
      | true => simp [← lead a b (Ne.symm ne),value]
    rw [same_candidates,← count]
    have free :
        (S.filter fun p => R a p = true ∧ ∀ b ∈ T, R b p = false) =
        S.filter fun p => A (e a) p = true ∧ ∀ b ∈ original, A b p = false := by
      ext p
      simp only [Finset.mem_filter]
      apply and_congr_right
      intro _
      apply and_congr_right
      intro _
      constructor
      · intro prop b hb
        obtain ⟨c,rfl⟩ := e.surjective b
        exact prop c ((T_iff c).mpr ((orig_iff (e c)).mp hb))
      · intro prop b hb
        exact prop (e b) ((orig_iff (e b)).mpr ((T_iff b).mp hb))
    rw [free,← B_count]
    exact WeightSixteenSaturatedColumn.free_points_on_heavy_line M S rows cols inside q hq (e a)

end WeightSixteenTripleNumerics

namespace WeightSixteenTripleNumerics

open Finset WeightSixteenCubicGraphs

lemma word_model_syntax (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111))
    (e : Equiv.Perm (Fin 8)) :
    encode (fun a b => decide (b ≠ a ∧ ∃ p ∉ S, M (.inl (e a)) p = true ∧ M (.inl (e b)) p = true)) =
      encode (exteriorGraph (fun a p => M (.inl a) p) S e) := by
  congr 1
  funext a b
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,exteriorGraph,WeightSixteenCubicGeometry.mem_outer,
    WeightSixteenCubicGeometry.together]
  exact and_congr (not_congr e.injective.eq_iff.symm) Iff.rfl

end WeightSixteenTripleNumerics

namespace WeightSixteenTripleTriangleObstruction

open Finset WeightSixteenSaturatedColumn
open WeightSixteenCubicGraphs WeightSixteenTripleNumerics

abbrev Lines := Fin 8 ⊕ Fin 72
abbrev Points := Fin 111

def heavyAt (M : Lines → Points → Bool) (p : Points) : Finset (Fin 8) :=
  univ.filter fun a => M (.inl a) p = true

def lightAt (M : Lines → Points → Bool) (p : Points) : Finset (Fin 72) :=
  univ.filter fun b => M (.inr b) p = true

lemma mem_heavyAt {M : Lines → Points → Bool} {p : Points} {a : Fin 8} :
    a ∈ heavyAt M p ↔ M (.inl a) p = true := by simp [heavyAt]

theorem free_points_count (M : Lines → Points → Bool) (S : Finset Points)
    (rows : ∀ l, (univ.filter fun p => M l p = true).card = 11)
    (unique : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (inside : ∀ p ∈ S, (heavyAt M p).card = 2 ∧ (lightAt M p).card = 9)
    (q : Points) (external : q ∉ S) (T : Finset Points) (in_code : T ⊆ S)
    (off_heavy : ∀ p ∈ T, Disjoint (heavyAt M p) (heavyAt M q))
    (pair_heavy : ∀ p ∈ T, ∀ r ∈ T, p ≠ r →
      ∃ a, a ∈ heavyAt M p ∧ a ∈ heavyAt M r) :
    T.card ≤ (lightAt M q).card := by
  classical
  have neighbor (p : Points) (hp : p ∈ T) : ∃ b ∈ lightAt M q, M (.inr b) p = true := by
    have degree : (univ.filter fun l => M l p = true).card = 11 := by
      rw [count_incidence_sum]
      change (heavyAt M p).card + (lightAt M p).card = 11
      rw [(inside p (in_code hp)).1,(inside p (in_code hp)).2]
    have different : p ≠ q := fun equal => external (equal ▸ in_code hp)
    obtain ⟨l,⟨throughP,throughQ⟩,_⟩ :=
      saturated_column M (Fintype.card_fin 111) rows unique p degree q different
    cases l with
    | inl a =>
      exact (Finset.disjoint_left.mp (off_heavy p hp) (mem_heavyAt.mpr throughP)
        (mem_heavyAt.mpr throughQ)).elim
    | inr b => exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,throughQ⟩,throughP⟩
  let f (p : ↥T) : ↥(lightAt M q) :=
    ⟨Classical.choose (neighbor p.val p.property),(Classical.choose_spec (neighbor p.val p.property)).1⟩
  have at_point (p : ↥T) : M (.inr (f p).val) p.val = true :=
    (Classical.choose_spec (neighbor p.val p.property)).2
  have injective : Function.Injective f := by
    intro p r equal
    apply Subtype.ext
    by_contra different
    obtain ⟨a,hp,hr⟩ := pair_heavy p.val p.property r.val r.property different
    have hit := at_point r
    rw [← equal] at hit
    have equ := unique p.val r.val different (.inl a) (.inr (f p).val)
      (mem_heavyAt.mp hp) (mem_heavyAt.mp hr) (at_point p) hit
    cases equ
  exact Finset.card_le_card_of_injective injective

set_option maxHeartbeats 15000000 in
set_option maxRecDepth 6000 in
private lemma only_external_triple : ∀ T : Finset (Fin 8),
    CanHold (adj 0x2e69807) T → T = {4,5,6} := by decide +kernel

/-- The three internal intersections of heavy rows 1, 2, 3 require distinct
two-secants through the exterior triple, which only has room for two. -/
theorem graph_2e69807_excluded
    (M : Lines → Points → Bool) (S : Finset Points)
    (rows : ∀ l, (univ.filter fun p => M l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (unique : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (inside : ∀ p ∈ S, (heavyAt M p).card = 2 ∧ (lightAt M p).card = 9)
    (outside : ∀ p ∉ S, 2 * (heavyAt M p).card + (lightAt M p).card = 8)
    (e : Equiv.Perm (Fin 8))
    (shape : encode (exteriorGraph (fun a p => M (.inl a) p) S e) = 0x2e69807)
    (q : Points) (external : q ∉ S) (triple : (heavyAt M q).card = 3) : False := by
  let A (a : Fin 8) (p : Points) := M (.inl a) p
  let g := exteriorGraph A S e
  let support (p : Points) := univ.filter fun a : Fin 8 => A (e a) p = true
  have support_mem {p : Points} {a : Fin 8} : a ∈ support p ↔ A (e a) p = true := by
    simp [support]
  have graph : g = adj 0x2e69807 := by
    have recovered := recover_adjacency g (exteriorGraph_symm A S e) (exteriorGraph_loopfree A S e)
    rw [show encode g = 0x2e69807 from shape] at recovered
    exact recovered.symm
  have triangle : support q = {4,5,6} := by
    have valid := geometry_allows_triangle M S rows rowPairs unique inside outside e q external triple
    change CanHold g (support q) at valid
    rw [graph] at valid
    exact only_external_triple _ valid
  have locate (a b : Fin 8) (different : a ≠ b) (notEdge : adj 0x2e69807 a b = false) :
      ∃ p ∈ S, support p = {a,b} := by
    obtain ⟨p,⟨ha,hb⟩,_⟩ := rowPairs (.inl (e a)) (.inl (e b))
      (fun same => different (e.injective (Sum.inl.inj same)))
    have code : p ∈ S := by
      by_contra off
      have apart : e b ≠ e a := fun same => different (e.injective same).symm
      have present : g a b = true := by
        simp only [g,exteriorGraph,decide_eq_true_eq,WeightSixteenCubicGeometry.mem_outer,
          WeightSixteenCubicGeometry.together]
        exact ⟨apart,p,off,ha,hb⟩
      rw [graph,notEdge] at present
      cases present
    have two : (support p).card = 2 :=
      (cardinal_relabel e (fun a => A a p = true)).trans (inside p code).1
    have included : ({a,b} : Finset (Fin 8)) ⊆ support p := by
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | memberB
      · exact support_mem.mpr ha
      · obtain rfl := Finset.mem_singleton.mp memberB
        exact support_mem.mpr hb
    refine ⟨p,code,(Finset.eq_of_subset_of_card_le included ?_).symm⟩
    rw [two,Finset.card_pair different]
  obtain ⟨p12,h12,e12⟩ := locate 1 2 (by decide) (by decide)
  obtain ⟨p13,h13,e13⟩ := locate 1 3 (by decide) (by decide)
  obtain ⟨p23,h23,e23⟩ := locate 2 3 (by decide) (by decide)
  have d12_13 : p12 ≠ p13 := by
    intro same
    exact (by decide : ({1,2} : Finset (Fin 8)) ≠ {1,3}) (e12.symm.trans ((congrArg support same).trans e13))
  have d12_23 : p12 ≠ p23 := by
    intro same
    exact (by decide : ({1,2} : Finset (Fin 8)) ≠ {2,3}) (e12.symm.trans ((congrArg support same).trans e23))
  have d13_23 : p13 ≠ p23 := by
    intro same
    exact (by decide : ({1,3} : Finset (Fin 8)) ≠ {2,3}) (e13.symm.trans ((congrArg support same).trans e23))
  let T : Finset Points := {p12,p13,p23}
  have in_code : T ⊆ S := by
    intro p hp
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have contained {p : Points} (hp : p ∈ T) : support p ⊆ ({1,2,3} : Finset (Fin 8)) := by
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · rw [e12]; decide
    · rw [e13]; decide
    · rw [e23]; decide
  have off (p : Points) (hp : p ∈ T) : Disjoint (heavyAt M p) (heavyAt M q) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨b,rfl⟩ := e.surjective a
    have hp' := contained hp (support_mem.mpr (mem_heavyAt.mp ha))
    have hq' : b ∈ ({4,5,6} : Finset (Fin 8)) := triangle ▸ support_mem.mpr (mem_heavyAt.mp hb)
    exact (Finset.disjoint_left.mp (by decide : Disjoint ({1,2,3} : Finset (Fin 8)) {4,5,6}) hp' hq')
  have shared (p : Points) (hp : p ∈ T) (r : Points) (hr : r ∈ T) (_ : p ≠ r) :
      ∃ a, a ∈ heavyAt M p ∧ a ∈ heavyAt M r := by
    have intersect : ¬ Disjoint (support p) (support r) := by
      intro disjoint
      have together : support p ∪ support r ⊆ ({1,2,3} : Finset (Fin 8)) := union_subset (contained hp) (contained hr)
      have card := Finset.card_le_card together
      rw [Finset.card_union_of_disjoint disjoint] at card
      have size (b : Points) (hb : b ∈ T) : (support b).card = 2 :=
        (cardinal_relabel e (fun a => A a b = true)).trans (inside b (in_code hb)).1
      rw [size p hp,size r hr] at card
      exact (by decide : ¬ (2 + 2 ≤ ({1,2,3} : Finset (Fin 8)).card)) card
    obtain ⟨a,ha,hb⟩ := Finset.not_disjoint_iff.mp intersect
    exact ⟨e a,mem_heavyAt.mpr (support_mem.mp ha),mem_heavyAt.mpr (support_mem.mp hb)⟩
  have count := free_points_count M S rows unique inside q external T in_code off shared
  have size : T.card = 3 := by simp [T,d12_13,d12_23,d13_23]
  rw [size] at count
  have light := outside q external
  rw [triple] at light
  omega

end WeightSixteenTripleTriangleObstruction

namespace WeightSixteenTripleSymmetry

open Finset WeightSixteenCubicGraphs WeightSixteenTripleNumerics
open WeightSixteenTripleTriangleObstruction (Lines Points heavyAt lightAt)

def exchange : Equiv.Perm (Fin 8) :=
  (Equiv.swap 2 3).trans ((Equiv.swap 4 5).trans (Equiv.swap 6 7))

private lemma preserves_edges (a b : Fin 8) :
    adj 0x35a5807 (exchange a) (exchange b) = adj 0x35a5807 a b := by
  revert a b
  decide +kernel

private lemma moves_triangle (a : Fin 8) :
    exchange a ∈ ({3,5,6} : Finset (Fin 8)) ↔ a ∈ ({2,4,7} : Finset (Fin 8)) := by
  revert a
  decide +kernel

set_option maxHeartbeats 15000000 in
set_option maxRecDepth 6000 in
private lemma two_triangles : ∀ T : Finset (Fin 8),
    CanHold (adj 0x35a5807) T → T = {2,4,7} ∨ T = {3,5,6} := by decide +kernel

theorem normalize (M : Lines → Points → Bool) (S : Finset Points)
    (rows : ∀ l, (univ.filter fun p => M l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (unique : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (inside : ∀ p ∈ S, (heavyAt M p).card = 2 ∧ (lightAt M p).card = 9)
    (outside : ∀ p ∉ S, 2 * (heavyAt M p).card + (lightAt M p).card = 8)
    (e : Equiv.Perm (Fin 8))
    (shape : encode (exteriorGraph (fun a p => M (.inl a) p) S e) = 0x35a5807)
    (q : Points) (external : q ∉ S) (triple : (heavyAt M q).card = 3) :
    ∃ f : Equiv.Perm (Fin 8),
      encode (exteriorGraph (fun a p => M (.inl a) p) S f) = 0x35a5807 ∧
      (univ.filter fun a => M (.inl (f a)) q = true) = {2,4,7} := by
  let A (a : Fin 8) (p : Points) := M (.inl a) p
  let support (f : Equiv.Perm (Fin 8)) := univ.filter fun a => A (f a) q = true
  have graph : exteriorGraph A S e = adj 0x35a5807 := by
    have recovered := recover_adjacency (exteriorGraph A S e)
      (exteriorGraph_symm A S e) (exteriorGraph_loopfree A S e)
    change encode (exteriorGraph A S e) = 0x35a5807 at shape
    rw [shape] at recovered
    exact recovered.symm
  have valid : CanHold (exteriorGraph A S e) (support e) :=
    geometry_allows_triangle M S rows rowPairs unique inside outside e q external triple
  rw [graph] at valid
  rcases two_triangles _ valid with first | second
  · exact ⟨e, shape, first⟩
  · let f := exchange.trans e
    have same : exteriorGraph A S f = exteriorGraph A S e := by
      funext a b
      calc
        exteriorGraph A S f a b = exteriorGraph A S e (exchange a) (exchange b) := rfl
        _ = adj 0x35a5807 (exchange a) (exchange b) := by rw [graph]
        _ = adj 0x35a5807 a b := preserves_edges a b
        _ = exteriorGraph A S e a b := by rw [graph]
    refine ⟨f, ?_, ?_⟩
    · change encode (exteriorGraph A S f) = 0x35a5807
      rw [same, shape]
    · change support f = {2,4,7}
      ext a
      have relabel : a ∈ support f ↔ exchange a ∈ support e := by
        constructor <;> intro present
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp present).2⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp present).2⟩
      rw [relabel, second]
      exact moves_triangle a

end WeightSixteenTripleSymmetry

namespace WeightSixteenSecantIndexGeneric

open Finset

variable {P : Type} [DecidableEq P]

def insideRow {X : Type} (internal : Finset P) (M : X → P → Bool) (x : X) : Finset P :=
  internal.filter fun p => M x p = true

def freePairs (internal : Finset P) (A : Fin 8 → P → Bool) : Finset (Finset P) :=
  internal.powersetCard 2 \
    (Finset.univ : Finset (Fin 8)).biUnion (fun a => (insideRow internal A a).powersetCard 2)

lemma row_mem {X : Type} (internal : Finset P) (M : X → P → Bool) (x : X) (p : P) :
    p ∈ insideRow internal M x ↔ p ∈ internal ∧ M x p = true := by
  simp [insideRow]

lemma shared_pair_eq (internal : Finset P) (M : Fin 8 ⊕ Fin 72 → P → Bool)
    (col_pair : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (t : Finset P) (pairs : t.card = 2)
    (l m : Fin 8 ⊕ Fin 72) (on_l : t ⊆ insideRow internal M l) (on_m : t ⊆ insideRow internal M m) :
    l = m := by
  obtain ⟨p,q,ne,eq⟩ := Finset.card_eq_two.mp pairs
  have hp : p ∈ t := eq ▸ Finset.mem_insert_self _ _
  have hq : q ∈ t := eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact col_pair p q ne l m ((row_mem internal M l p).mp (on_l hp) |>.2) ((row_mem internal M l q).mp (on_l hq) |>.2)
    ((row_mem internal M m p).mp (on_m hp) |>.2) ((row_mem internal M m q).mp (on_m hq) |>.2)

theorem secant_index (internal : Finset P) (cardS : internal.card = 16)
    (A : Fin 8 → P → Bool) (B : Fin 72 → P → Bool)
    (four : ∀ a, (insideRow internal A a).card = 4)
    (two : ∀ b, (insideRow internal B b).card = 2)
    (col_pair : ∀ p q, p ≠ q → ∀ l m : Fin 8 ⊕ Fin 72,
      Sum.elim A B l p = true → Sum.elim A B l q = true →
      Sum.elim A B m p = true → Sum.elim A B m q = true → l = m) :
    ∃ e : Fin 72 ≃ ↥(freePairs internal A), ∀ b, (e b).val = insideRow internal B b := by
  let by_row (a : Fin 8) := (insideRow internal A a).powersetCard 2
  let used := (Finset.univ : Finset (Fin 8)).biUnion by_row
  let possible := internal.powersetCard 2
  have unique := shared_pair_eq internal (Sum.elim A B) col_pair
  have by_row_disjoint : (↑(Finset.univ : Finset (Fin 8)) : Set (Fin 8)).PairwiseDisjoint by_row := by
    intro a _ b _ ne
    change Disjoint (by_row a) (by_row b)
    rw [Finset.disjoint_left]
    intro t ht hq
    obtain ⟨at_a,size⟩ := Finset.mem_powersetCard.mp ht
    obtain ⟨at_b,_⟩ := Finset.mem_powersetCard.mp hq
    exact ne (Sum.inl.inj (unique t size (.inl a) (.inl b) at_a at_b))
  have fact (a : Fin 8) : (by_row a).card = 6 := by
    change ((insideRow internal A a).powersetCard 2).card = 6
    rw [Finset.card_powersetCard,four]
    decide
  have used_count : used.card = 48 := by
    change ((Finset.univ : Finset (Fin 8)).biUnion by_row).card = 48
    rw [Finset.card_biUnion by_row_disjoint]
    simp [fact]
  have possible_count : possible.card = 120 := by
    change (internal.powersetCard 2).card = 120
    rw [Finset.card_powersetCard,cardS]
    decide
  have use_possible : used ⊆ possible := by
    intro t ht
    obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp ht
    exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_powersetCard.mp ha).1.trans (Finset.filter_subset _ _),
      (Finset.mem_powersetCard.mp ha).2⟩
  have free_count : (freePairs internal A).card = 72 := by
    change (possible \ used).card = 72
    rw [Finset.card_sdiff_of_subset use_possible,possible_count,used_count]
  have free (b : Fin 72) : insideRow internal B b ∈ freePairs internal A := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _,two b⟩,?_⟩
    intro clash
    obtain ⟨a,_,inA⟩ := Finset.mem_biUnion.mp clash
    have at_a := (Finset.mem_powersetCard.mp inA).1
    have on_b : insideRow internal B b ⊆ insideRow internal B b := Finset.Subset.rfl
    have same := unique (insideRow internal B b) (two b) (.inl a) (.inr b) at_a on_b
    cases same
  let f (b : Fin 72) : ↥(freePairs internal A) := ⟨insideRow internal B b,free b⟩
  have one_to_one : Function.Injective f := by
    intro b c same
    have sameRows : insideRow internal B b = insideRow internal B c := congrArg Subtype.val same
    have here : insideRow internal B b ⊆ insideRow internal B b := Finset.Subset.rfl
    have there : insideRow internal B b ⊆ insideRow internal B c := sameRows ▸ here
    exact Sum.inr.inj (unique _ (two b) (.inr b) (.inr c) here there)
  have cardinal : Fintype.card (Fin 72) = Fintype.card ↥(freePairs internal A) := by
    rw [Fintype.card_fin,Fintype.card_coe,free_count]
  have both := (Fintype.bijective_iff_injective_and_card f).mpr ⟨one_to_one,cardinal⟩
  exact ⟨Equiv.ofBijective f both,fun _ => rfl⟩

end WeightSixteenSecantIndexGeneric

namespace WeightSixteenExteriorMatching

open Finset WeightSixteenSaturatedColumn WeightSixteenSecantIndexGeneric WeightSixteenCubicGraphs
open WeightSixteenTripleTriangleObstruction (Lines Points heavyAt lightAt)

abbrev Matrix := Lines → Points → Bool

def freeAt (M : Matrix) (p q : Points) : Prop :=
  Disjoint (heavyAt M p) (heavyAt M q)

def internalLabels (G : Fin 8 → Fin 8 → Bool) : Finset (Finset (Fin 8)) :=
  univ.filter fun t => t.card = 2 ∧ ∀ a ∈ t, ∀ b ∈ t, a ≠ b → G a b = false

theorem code_points_by_heavy_pair (A : Fin 8 → Points → Bool) (S : Finset Points)
    (rowPairs : ∀ a b, a ≠ b → ∃! p, A a p = true ∧ A b p = true)
    (degree : ∀ p ∈ S, (univ.filter fun a => A a p = true).card = 2) :
    ∃ label : ↥S ≃ ↥(internalLabels (exteriorGraph A S (Equiv.refl _))),
      ∀ (p : ↥S) (a : Fin 8), a ∈ (label p).val ↔ A a p.val = true := by
  let G := exteriorGraph A S (Equiv.refl _)
  let support (p : Points) := (univ.filter fun a => A a p = true : Finset (Fin 8))
  have on {p : Points} {a : Fin 8} : a ∈ support p ↔ A a p = true := by
    simp [support]
  have edge {a b : Fin 8} (different : a ≠ b) :
      G a b = true ↔ ∃ q ∉ S, A a q = true ∧ A b q = true := by
    simp [G, exteriorGraph, WeightSixteenCubicGeometry.mem_outer,
      WeightSixteenCubicGeometry.together, different.symm]
  have label_exists (p : ↥S) : support p.val ∈ internalLabels G := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, degree p.val p.property, ?_⟩
    intro a ha b hb different
    cases decision : G a b with
    | false => rfl
    | true =>
      obtain ⟨q, outside, atQ⟩ := (edge different).mp decision
      obtain ⟨_, _, alone⟩ := rowPairs a b different
      have same := (alone p.val ⟨on.mp ha, on.mp hb⟩).trans (alone q atQ).symm
      exact (outside (same ▸ p.property)).elim
  let f (p : ↥S) : ↥(internalLabels G) := ⟨support p.val, label_exists p⟩
  have injective : Function.Injective f := by
    intro p q eq
    have same : support p.val = support q.val := congrArg Subtype.val eq
    obtain ⟨a, b, different, shape⟩ := Finset.card_eq_two.mp (degree p.val p.property)
    change support p.val = {a,b} at shape
    have ha : a ∈ support p.val := by rw [shape]; exact Finset.mem_insert_self _ _
    have hb : b ∈ support p.val := by
      rw [shape]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨_, _, alone⟩ := rowPairs a b different
    exact Subtype.ext ((alone p.val ⟨on.mp ha, on.mp hb⟩).trans
      (alone q.val ⟨on.mp (same ▸ ha), on.mp (same ▸ hb)⟩).symm)
  have surjective : Function.Surjective f := by
    intro t
    obtain ⟨_, size, nonedges⟩ := Finset.mem_filter.mp t.property
    obtain ⟨a, b, different, shape⟩ := Finset.card_eq_two.mp size
    have ha : a ∈ t.val := shape ▸ Finset.mem_insert_self _ _
    have hb : b ∈ t.val := shape ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨p, ⟨atA, atB⟩, _⟩ := rowPairs a b different
    have internal : p ∈ S := by
      by_contra outside
      have present := (edge different).mpr ⟨p, outside, atA, atB⟩
      rw [nonedges a ha b hb different] at present
      cases present
    have subset : t.val ⊆ support p := by
      rw [shape]
      exact Finset.insert_subset (on.mpr atA) (Finset.singleton_subset_iff.mpr (on.mpr atB))
    have equal := Finset.eq_of_subset_of_card_le subset ((degree p internal).trans size.symm).le
    exact ⟨⟨p, internal⟩, Subtype.ext equal.symm⟩
  exact ⟨Equiv.ofBijective f ⟨injective, surjective⟩, fun p a => on⟩

theorem exterior_matching (M : Matrix) (S : Finset Points)
    (rows : ∀ l, (univ.filter fun p => M l p = true).card = 11)
    (unique : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (inside : ∀ p ∈ S, (heavyAt M p).card = 2 ∧ (lightAt M p).card = 9)
    {p q : Points} (hp : p ∈ S) (hq : q ∉ S) :
    (freeAt M p q → ∃! b : Fin 72, M (.inr b) p = true ∧ M (.inr b) q = true) ∧
    (∀ b : Fin 72, M (.inr b) p = true → M (.inr b) q = true → freeAt M p q) := by
  have different : p ≠ q := fun eq => hq (eq ▸ hp)
  have degree : (univ.filter fun l => M l p = true).card = 11 := by
    rw [count_incidence_sum]
    change (heavyAt M p).card + (lightAt M p).card = 11
    rw [(inside p hp).1, (inside p hp).2]
  constructor
  · intro free
    obtain ⟨l, ⟨atP, atQ⟩, _⟩ :=
      saturated_column M (Fintype.card_fin 111) rows unique p degree q different
    cases l with
    | inl a =>
      exact (Finset.disjoint_left.mp free
        (WeightSixteenTripleTriangleObstruction.mem_heavyAt.mpr atP)
        (WeightSixteenTripleTriangleObstruction.mem_heavyAt.mpr atQ)).elim
    | inr b =>
      refine ⟨b, ⟨atP, atQ⟩, ?_⟩
      intro c hc
      exact Sum.inr.inj (unique p q different (.inr c) (.inr b) hc.1 hc.2 atP atQ)
  · intro b atP atQ
    refine Finset.disjoint_left.mpr ?_
    intro a haP haQ
    have equal := unique p q different (.inl a) (.inr b)
      (WeightSixteenTripleTriangleObstruction.mem_heavyAt.mp haP)
      (WeightSixteenTripleTriangleObstruction.mem_heavyAt.mp haQ) atP atQ
    cases equal

theorem exterior_partitions_rows (M : Matrix) (S : Finset Points)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (a : Fin 8) (b : Fin 72) :
    (∀ p ∈ insideRow S M (.inr b), M (.inl a) p = false) ↔
      ∃! q, q ∉ S ∧ M (.inl a) q = true ∧ M (.inr b) q = true := by
  have different : (Sum.inl a : Lines) ≠ Sum.inr b := by simp
  obtain ⟨q, ⟨atA, atB⟩, alone⟩ := rowPairs (.inl a) (.inr b) different
  constructor
  · intro free
    have exterior : q ∉ S := by
      intro hq
      have absent := free q ((row_mem S M (.inr b) q).mpr ⟨hq, atB⟩)
      rw [atA] at absent
      cases absent
    exact ⟨q, ⟨exterior, atA, atB⟩, fun r hr => alone r hr.2⟩
  · rintro ⟨r, ⟨exterior, rowA, rowB⟩, _⟩ p hp
    have same := alone r ⟨rowA, rowB⟩
    obtain ⟨hp, onB⟩ := (row_mem S M (.inr b) p).mp hp
    cases onA : M (.inl a) p with
    | false => rfl
    | true =>
      have equal := alone p ⟨onA, onB⟩
      exact (exterior (same.symm ▸ equal ▸ hp)).elim

theorem exterior_columns_share_at_most_one (M : Matrix)
    (unique : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    {p q : Points} (different : p ≠ q) : ((lightAt M p) ∩ (lightAt M q)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb c hc
  have at_pq (d : Fin 72) (hd : d ∈ lightAt M p ∩ lightAt M q) :
      M (.inr d) p = true ∧ M (.inr d) q = true := by
    simpa only [lightAt, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] using hd
  exact Sum.inr.inj (unique p q different (.inr b) (.inr c)
    (at_pq b hb).1 (at_pq b hb).2 (at_pq c hc).1 (at_pq c hc).2)

theorem remaining_pair_has_hidden_meeting (M : Matrix) (S : Finset Points)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (b c : Fin 72) (different : b ≠ c)
    (insideDisjoint : Disjoint (insideRow S M (.inr b)) (insideRow S M (.inr c)))
    (unused : ∀ q ∉ S, (heavyAt M q).Nonempty →
      ¬ (M (.inr b) q = true ∧ M (.inr c) q = true)) :
    ∃ q ∉ S, heavyAt M q = ∅ ∧ M (.inr b) q = true ∧ M (.inr c) q = true := by
  obtain ⟨q, ⟨atB, atC⟩, _⟩ := rowPairs (.inr b) (.inr c) (fun eq => different (Sum.inr.inj eq))
  have exterior : q ∉ S := by
    intro hq
    exact (Finset.disjoint_left.mp insideDisjoint
      ((row_mem S M (.inr b) q).mpr ⟨hq, atB⟩)
      ((row_mem S M (.inr c) q).mpr ⟨hq, atC⟩))
  have hidden : heavyAt M q = ∅ := by
    by_contra nonempty
    exact unused q exterior (Finset.nonempty_iff_ne_empty.mpr nonempty) ⟨atB, atC⟩
  exact ⟨q, exterior, hidden, atB, atC⟩

theorem covering_pair_has_hidden_meeting (M : Matrix) (S : Finset Points)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (unique : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (b c : Fin 72) (different : b ≠ c)
    (insideDisjoint : Disjoint (insideRow S M (.inr b)) (insideRow S M (.inr c)))
    (cover : ∀ a : Fin 8, ∃ p ∈ S, M (.inl a) p = true ∧
      (M (.inr b) p = true ∨ M (.inr c) p = true)) :
    ∃ q ∉ S, heavyAt M q = ∅ ∧ M (.inr b) q = true ∧ M (.inr c) q = true := by
  apply remaining_pair_has_hidden_meeting M S rowPairs b c different insideDisjoint
  rintro q exterior ⟨a, ha⟩ ⟨atB, atC⟩
  have atA := WeightSixteenTripleTriangleObstruction.mem_heavyAt.mp ha
  obtain ⟨p, internal, heavy, atP⟩ := cover a
  have apart : p ≠ q := fun eq => exterior (eq ▸ internal)
  rcases atP with here | here
  · cases unique p q apart (.inl a) (.inr b) heavy atA here atB
  · cases unique p q apart (.inl a) (.inr c) heavy atA here atC

end WeightSixteenExteriorMatching

namespace WeightSixteenTripleColumnData

open Finset WeightSixteenCubicGraphs WeightSixteenExteriorMatching WeightSixteenTripleNumerics

def codeLabelTable : List (Finset (Fin 8)) :=
  [{0,4},{0,5},{0,6},{0,7},{1,2},{1,3},{1,4},{1,5},
    {2,3},{2,5},{2,6},{3,4},{3,7},{4,6},{5,7},{6,7}]

def codeLabel (i : Fin 16) : Finset (Fin 8) := codeLabelTable.get (i.cast (by decide))

private lemma code_label_injective : Function.Injective codeLabel := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 15000000 in
private lemma code_labels : ∀ s : Finset (Fin 8),
    s ∈ internalLabels (adj 0x35a5807) ↔ ∃ i : Fin 16, codeLabel i = s := by decide +kernel

noncomputable def codeIndex : Fin 16 ≃ ↥(internalLabels (adj 0x35a5807)) := by
  let f (i : Fin 16) : ↥(internalLabels (adj 0x35a5807)) :=
    ⟨codeLabel i, (code_labels _).mpr ⟨i,rfl⟩⟩
  refine Equiv.ofBijective f ⟨fun _ _ same => code_label_injective (congrArg Subtype.val same), ?_⟩
  intro s
  obtain ⟨i,same⟩ := (code_labels _).mp s.property
  exact ⟨i, Subtype.ext same⟩

def rowTable : List (Fin 16 × Fin 16) :=
  (List.finRange 16).flatMap fun a => (List.finRange 16).filterMap fun b =>
    if a < b ∧ Disjoint (codeLabel a) (codeLabel b) then some (a,b) else none

lemma rowTable_length : rowTable.length = 72 := by decide +kernel

def rowEndpoints (r : Fin 72) : Fin 16 × Fin 16 := rowTable.get (r.cast rowTable_length.symm)

set_option maxHeartbeats 10000000 in
lemma rowTable_nodup : rowTable.Nodup := by decide +kernel

def rowCover (r : Fin 72) : Finset (Fin 8) :=
  codeLabel (rowEndpoints r).1 ∪ codeLabel (rowEndpoints r).2

def oneTripleSupports : List (Finset (Fin 8)) :=
  [{2,4,7},{0,1},{0,2},{0,3},{1,6},{1,7},{3,5},{3,6},{4,5},{5,6}]

def twoTripleSupports : List (Finset (Fin 8)) :=
  [{2,4,7},{3,5,6},{0,1},{0,2},{0,3},{1,6},{1,7},{4,5}]

def tripleSupports (two : Bool) : List (Finset (Fin 8)) :=
  if two then [{2,4,7},{3,5,6}] else [{2,4,7}]

def exteriorSupports (two : Bool) : List (Finset (Fin 8)) :=
  if two then twoTripleSupports else oneTripleSupports

set_option maxRecDepth 8000 in
private lemma triples_are_included : ∀ (two : Bool) (T : Finset (Fin 8)),
    T ∈ tripleSupports two → T ∈ exteriorSupports two := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 25000000 in
private lemma listed_pairs : ∀ (two : Bool) (a b : Fin 8), a ≠ b → adj 0x35a5807 a b = true →
    (∀ T ∈ tripleSupports two, ¬ ({a,b} : Finset (Fin 8)) ⊆ T) →
    ({a,b} : Finset (Fin 8)) ∈ exteriorSupports two := by decide +kernel

theorem exterior_supports_listed (A : Fin 8 → WeightSixteenTripleTriangleObstruction.Points → Bool)
    (S : Finset WeightSixteenTripleTriangleObstruction.Points) (two : Bool)
    (rowPairs : ∀ a b, a ≠ b → ∃! p, A a p = true ∧ A b p = true)
    (graph : exteriorGraph A S (Equiv.refl _) = adj 0x35a5807)
    (maxSupport : ∀ q ∉ S, (univ.filter fun a => A a q = true).card ≤ 3)
    (triples : ∀ q ∉ S, (univ.filter fun a => A a q = true).card = 3 →
      (univ.filter fun a => A a q = true) ∈ tripleSupports two)
    (present : ∀ T ∈ tripleSupports two, ∃ q ∉ S, (univ.filter fun a => A a q = true) = T)
    (q : WeightSixteenTripleTriangleObstruction.Points) (outside : q ∉ S)
    (many : 2 ≤ (univ.filter fun a => A a q = true).card) :
    (univ.filter fun a => A a q = true) ∈ exteriorSupports two := by
  let T := univ.filter fun a => A a q = true
  have max : T.card ≤ 3 := maxSupport q outside
  change 2 ≤ T.card at many
  by_cases triple : T.card = 3
  · exact triples_are_included two _ (triples q outside triple)
  have size : T.card = 2 := by omega
  obtain ⟨a,b,ne,form⟩ := Finset.card_eq_two.mp size
  have atA : A a q = true := (Finset.mem_filter.mp (form ▸ Finset.mem_insert_self a {b} : a ∈ T)).2
  have atB : A b q = true := (Finset.mem_filter.mp
    (form ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b) : b ∈ T)).2
  have edge : adj 0x35a5807 a b = true := by
    rw [← graph]
    simp only [exteriorGraph, Equiv.refl_apply, decide_eq_true_eq, WeightSixteenCubicGeometry.mem_outer,
      WeightSixteenCubicGeometry.together]
    exact ⟨ne.symm,q,outside,atA,atB⟩
  have distinct_from_triples (U : Finset (Fin 8)) (allowed : U ∈ tripleSupports two) :
      ¬ ({a,b} : Finset (Fin 8)) ⊆ U := by
    intro contained
    obtain ⟨r, _, atR⟩ := present U allowed
    have a_r : A a r = true := (Finset.mem_filter.mp (atR ▸ contained (Finset.mem_insert_self a {b}) :
      a ∈ (univ.filter fun d => A d r = true))).2
    have b_r : A b r = true := (Finset.mem_filter.mp (atR ▸ contained
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)) :
      b ∈ (univ.filter fun d => A d r = true))).2
    obtain ⟨_, _, alone⟩ := rowPairs a b ne
    have equal := (alone q ⟨atA,atB⟩).trans (alone r ⟨a_r,b_r⟩).symm
    have three_count (U : Finset (Fin 8)) (known : U ∈ tripleSupports two) : U.card = 3 := by
      cases two
      · have same : U = ({2,4,7} : Finset (Fin 8)) := by simpa [tripleSupports] using known
        rw [same]
        decide
      · have same : U = ({2,4,7} : Finset (Fin 8)) ∨ U = {3,5,6} := by simpa [tripleSupports] using known
        rcases same with rfl | rfl <;> decide
    have r_size : (univ.filter fun d => A d r = true).card = 3 := by rw [atR, three_count U allowed]
    have contradict : (univ.filter fun d => A d r = true).card = 2 := equal ▸ size
    omega
  change T ∈ exteriorSupports two
  rw [form]
  exact listed_pairs two a b ne edge distinct_from_triples

set_option maxHeartbeats 20000000 in
theorem one_triple_anchors : ∀ r ∈ ([17,26,41,52] : List (Fin 72)),
    ∀ T ∈ oneTripleSupports, ¬ Disjoint (rowCover r) T := by decide +kernel

set_option maxHeartbeats 20000000 in
theorem two_triple_anchors : ∀ r ∈ ([1,2,8] : List (Fin 72)),
    (rowEndpoints r).1 = 0 ∧ ∀ T ∈ twoTripleSupports, ¬ Disjoint (rowCover r) T := by decide +kernel

end WeightSixteenTripleColumnData

namespace WeightSixteenDenseMatchings

open Finset WeightSixteenTripleColumnData

abbrev Edge := Fin 16 × Fin 16

def freePoints (support : Finset (Fin 8)) : Finset (Fin 16) :=
  univ.filter fun p => Disjoint (codeLabel p) support

def allowedEdges (support : Finset (Fin 8)) : Finset Edge :=
  univ.filter fun e => e.1 < e.2 ∧ Disjoint (codeLabel e.1) (codeLabel e.2) ∧
    e.1 ∈ freePoints support ∧ e.2 ∈ freePoints support

def matchings (support : Finset (Fin 8)) (size : Nat) : Finset (Finset Edge) :=
  ((allowedEdges support).powersetCard size).filter fun column =>
    ∀ p ∈ freePoints support, (column.filter fun e => e.1 = p ∨ e.2 = p).card = 1

theorem listed {T : Finset (Fin 8)} {column : Finset Edge} {n : Nat}
    (eligible : column ⊆ allowedEdges T) (size : column.card = n)
    (exactlyOnce : ∀ p ∈ freePoints T, (column.filter fun e => e.1 = p ∨ e.2 = p).card = 1) :
    column ∈ matchings T n :=
  Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨eligible, size⟩, exactlyOnce⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem pair_35_matchings : matchings {3,5} 4 =
    ({{(0,10),(2,4),(3,13),(6,15)}, {(0,10),(2,6),(3,13),(4,15)},
      {(0,15),(2,4),(3,13),(6,10)}, {(0,15),(2,6),(3,10),(4,13)}} : Finset (Finset Edge)) := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
theorem first_triple_matching :
    matchings {2,4,7} 2 = ({{(1,5),(2,7)}} : Finset (Finset Edge)) := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
theorem second_triple_matching :
    matchings {3,5,6} 2 = ({{(0,4),(3,6)}} : Finset (Finset Edge)) := by decide +kernel

end WeightSixteenDenseMatchings

namespace WeightSixteenDenseColumnProjection

open Finset WeightSixteenExteriorMatching WeightSixteenSecantIndexGeneric
open WeightSixteenCubicGraphs WeightSixteenTripleNumerics
open WeightSixteenTripleTriangleObstruction WeightSixteenTripleColumnData WeightSixteenDenseMatchings

theorem label_code_points (M : Matrix) (S : Finset Points)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (inside : ∀ p ∈ S, (heavyAt M p).card = 2)
    (shape : exteriorGraph (fun a p => M (.inl a) p) S (Equiv.refl _) = adj 0x35a5807) :
    ∃ points : Fin 16 ≃ ↥S, ∀ i, heavyAt M (points i).val = codeLabel i := by
  let A (a : Fin 8) (p : Points) := M (.inl a) p
  have meet (a b : Fin 8) (ne : a ≠ b) : ∃! p, A a p = true ∧ A b p = true :=
    rowPairs (.inl a) (.inl b) (fun eq => ne (Sum.inl.inj eq))
  have degrees (p : Points) (hp : p ∈ S) : (univ.filter fun a => A a p = true).card = 2 := inside p hp
  have labels : ∃ e : ↥S ≃ ↥(internalLabels (adj 0x35a5807)),
      ∀ (p : ↥S) (a : Fin 8), a ∈ (e p).val ↔ A a p.val = true := by
    have recovered := code_points_by_heavy_pair A S meet degrees
    change exteriorGraph A S (Equiv.refl _) = adj 0x35a5807 at shape
    rw [shape] at recovered
    exact recovered
  obtain ⟨e, membership⟩ := labels
  let points := codeIndex.trans e.symm
  refine ⟨points, ?_⟩
  intro i
  apply Finset.ext
  intro a
  rw [mem_heavyAt, ← membership (points i) a]
  have equal : e (points i) = codeIndex i := e.apply_symm_apply _
  rw [equal] <;> rfl

theorem label_secants (M : Matrix) (S : Finset Points) (points : Fin 16 ≃ ↥S)
    (two : ∀ b : Fin 72, (insideRow S M (.inr b)).card = 2)
    (unique : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) :
    ∃ label : Fin 72 → Edge, Function.Injective label ∧
      (∀ b, (label b).1 < (label b).2) ∧
      (∀ b i, M (.inr b) (points i).val = true ↔ i = (label b).1 ∨ i = (label b).2) := by
  let through (b : Fin 72) := univ.filter fun i : Fin 16 => M (.inr b) (points i).val = true
  have cardinal (b : Fin 72) : (through b).card = 2 := by
    rw [← two b]
    apply Finset.card_bij (fun i _ => (points i).val)
    · intro i hit
      exact (row_mem S M _ _).mpr ⟨(points i).property, (Finset.mem_filter.mp hit).2⟩
    · intro i _ j _ same
      exact points.injective (Subtype.ext same)
    · intro p hit
      obtain ⟨inside, incident⟩ := (row_mem S M _ _).mp hit
      let i := points.symm ⟨p, inside⟩
      have equal : (points i).val = p := congrArg Subtype.val (points.apply_symm_apply ⟨p, inside⟩)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, equal.symm ▸ incident⟩, equal⟩
  have sorted (b : Fin 72) : ∃ e : Edge, e.1 < e.2 ∧ through b = {e.1, e.2} := by
    obtain ⟨i, j, apart, equal⟩ := Finset.card_eq_two.mp (cardinal b)
    rcases lt_or_gt_of_ne apart with less | greater
    · exact ⟨(i,j), less, equal⟩
    · exact ⟨(j,i), greater, equal.trans (Finset.pair_comm i j)⟩
  choose label ordered given using sorted
  have membership (b : Fin 72) (i : Fin 16) :
      M (.inr b) (points i).val = true ↔ i = (label b).1 ∨ i = (label b).2 := by
    have hit : i ∈ through b ↔ M (.inr b) (points i).val = true := by simp [through]
    rw [← hit, given b, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨label, ?_, ordered, membership⟩
  intro b c equal
  let i := (label b).1
  let j := (label b).2
  have apart : (points i).val ≠ (points j).val :=
    fun eq => (ne_of_lt (ordered b)) (points.injective (Subtype.ext eq))
  exact Sum.inr.inj (unique _ _ apart (.inr b) (.inr c)
    ((membership b i).mpr (Or.inl rfl)) ((membership b j).mpr (Or.inr rfl))
    ((membership c i).mpr (Or.inl (congrArg Prod.fst equal)))
    ((membership c j).mpr (Or.inr (congrArg Prod.snd equal))))

theorem exterior_column_projects (M : Matrix) (S : Finset Points) (points : Fin 16 ≃ ↥S)
    (heavyLabel : ∀ i, heavyAt M (points i).val = codeLabel i)
    (rows : ∀ l, (univ.filter fun p => M l p = true).card = 11)
    (two : ∀ b : Fin 72, (insideRow S M (.inr b)).card = 2)
    (inside : ∀ p ∈ S, (heavyAt M p).card = 2 ∧ (lightAt M p).card = 9)
    (unique : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (q : Points) (outside : q ∉ S) :
    ∃ label : Fin 72 → Edge, Function.Injective label ∧
      (∀ b i, M (.inr b) (points i).val = true ↔ i = (label b).1 ∨ i = (label b).2) ∧
      (lightAt M q).image label ∈ matchings (heavyAt M q) (lightAt M q).card := by
  obtain ⟨label, injective, order, membership⟩ := label_secants M S points two unique
  have at_q (b : Fin 72) : b ∈ lightAt M q ↔ M (.inr b) q = true := by simp [lightAt]
  have free_iff (i : Fin 16) : i ∈ freePoints (heavyAt M q) ↔ freeAt M (points i).val q := by
    simp [freePoints, freeAt, heavyLabel]
  let column := (lightAt M q).image label
  refine ⟨label, injective, membership, listed ?_ (Finset.card_image_of_injective _ injective) ?_⟩
  · intro e member
    obtain ⟨b, on_q, rfl⟩ := Finset.mem_image.mp member
    let i := (label b).1
    let j := (label b).2
    have at_i := (membership b i).mpr (Or.inl rfl)
    have at_j := (membership b j).mpr (Or.inr rfl)
    have apart : (points i).val ≠ (points j).val :=
      fun eq => (ne_of_lt (order b)) (points.injective (Subtype.ext eq))
    have disjoint : Disjoint (codeLabel i) (codeLabel j) := by
      rw [← heavyLabel i, ← heavyLabel j, Finset.disjoint_left]
      intro a h_i h_j
      have equal := unique _ _ apart (.inl a) (.inr b) (mem_heavyAt.mp h_i) (mem_heavyAt.mp h_j) at_i at_j
      cases equal
    have free_i := (exterior_matching M S rows unique inside (points i).property outside).2 b at_i ((at_q b).mp on_q)
    have free_j := (exterior_matching M S rows unique inside (points j).property outside).2 b at_j ((at_q b).mp on_q)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, order b, disjoint,
      (free_iff i).mpr free_i, (free_iff j).mpr free_j⟩
  · intro i free
    obtain ⟨b, ⟨at_i, on_q⟩, only⟩ :=
      (exterior_matching M S rows unique inside (points i).property outside).1 ((free_iff i).mp free)
    have one : column.filter (fun e => e.1 = i ∨ e.2 = i) = {label b} := by
      apply Finset.ext
      intro e
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨in_column, contains⟩
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp in_column
        have at_i' := (membership c i).mpr (contains.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm))
        exact congrArg label (only c ⟨at_i', (at_q c).mp hc⟩)
      · rintro rfl
        have ends := (membership b i).mp at_i
        exact ⟨Finset.mem_image.mpr ⟨b, (at_q b).mpr on_q, rfl⟩,
          ends.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
    change (column.filter fun e => e.1 = i ∨ e.2 = i).card = 1
    rw [one, Finset.card_singleton]

end WeightSixteenDenseColumnProjection

namespace WeightSixteenColumn35Geometry

open Finset WeightSixteenCubicGraphs WeightSixteenTripleNumerics
open WeightSixteenTripleTriangleObstruction WeightSixteenExteriorMatching
open WeightSixteenSecantIndexGeneric WeightSixteenDenseMatchings WeightSixteenDenseColumnProjection
open WeightSixteenTripleColumnData (codeLabel)

theorem column_35_cases (M : Matrix) (S : Finset Points)
    (shape : exteriorGraph (fun a p => M (.inl a) p) S (Equiv.refl _) = adj 0x35a5807)
    (rows : ∀ l, (univ.filter fun p => M l p = true).card = 11)
    (two : ∀ b : Fin 72, (insideRow S M (.inr b)).card = 2)
    (inside : ∀ p ∈ S, (heavyAt M p).card = 2 ∧ (lightAt M p).card = 9)
    (outside : ∀ p ∉ S, 2 * (heavyAt M p).card + (lightAt M p).card = 8)
    (max : ∀ p ∉ S, (heavyAt M p).card ≤ 3)
    (triple : ∀ p ∉ S, (heavyAt M p).card = 3 → heavyAt M p = {2,4,7})
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (unique : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) :
    ∃ (points : Fin 16 ≃ ↥S) (label : Fin 72 → Edge) (q : Points),
      Function.Injective label ∧
      (∀ i, heavyAt M (points i).val = codeLabel i) ∧
      (∀ b i, M (.inr b) (points i).val = true ↔ i = (label b).1 ∨ i = (label b).2) ∧
      q ∉ S ∧ heavyAt M q = {3,5} ∧
      (lightAt M q).image label ∈
        ({{(0,10),(2,4),(3,13),(6,15)}, {(0,10),(2,6),(3,13),(4,15)},
          {(0,15),(2,4),(3,13),(6,10)}, {(0,15),(2,6),(3,10),(4,13)}} : Finset (Finset Edge)) := by
  have edge : exteriorGraph (fun a p => M (.inl a) p) S (Equiv.refl _) 3 5 = true := by
    rw [shape] <;> decide
  simp only [exteriorGraph, Equiv.refl_apply, decide_eq_true_eq,
    WeightSixteenCubicGeometry.mem_outer, WeightSixteenCubicGeometry.together] at edge
  obtain ⟨_, q, external, meetThree, meetFive⟩ := edge
  have onThree : (3 : Fin 8) ∈ heavyAt M q := mem_heavyAt.mpr meetThree
  have onFive : (5 : Fin 8) ∈ heavyAt M q := mem_heavyAt.mpr meetFive
  have contained : ({3,5} : Finset (Fin 8)) ⊆ heavyAt M q :=
    Finset.insert_subset onThree (Finset.singleton_subset_iff.mpr onFive)
  have pairCard : ({3,5} : Finset (Fin 8)).card = 2 := by decide
  have lower := Finset.card_le_card contained
  rw [pairCard] at lower
  have upper := max q external
  have notTriple : (heavyAt M q).card ≠ 3 := by
    intro count
    rw [triple q external count] at onThree
    exact (by decide : (3 : Fin 8) ∉ ({2,4,7} : Finset (Fin 8))) onThree
  have exactCard : (heavyAt M q).card = 2 := by omega
  have support : heavyAt M q = {3,5} :=
    (Finset.eq_of_subset_of_card_le contained (by rw [exactCard, pairCard] <;> omega)).symm
  have light := outside q external
  rw [exactCard] at light
  have size : (lightAt M q).card = 4 := by omega
  obtain ⟨points, heavyLabel⟩ := label_code_points M S rowPairs (fun p hp => (inside p hp).1) shape
  obtain ⟨label, injective, membership, projected⟩ :=
    exterior_column_projects M S points heavyLabel rows two inside unique q external
  rw [support, size, pair_35_matchings] at projected
  exact ⟨points, label, q, injective, heavyLabel, membership, external, support, projected⟩

end WeightSixteenColumn35Geometry

namespace WeightSixteenColumn35Reduction

open Finset WeightSixteenTripleTriangleObstruction WeightSixteenExteriorMatching
open WeightSixteenCubicGraphs WeightSixteenTripleNumerics
open WeightSixteenDenseMatchings WeightSixteenTripleColumnData

structure Geometry (M : Matrix) (S : Finset Points) : Prop where
  size : S.card = 16
  rowSize : ∀ l, (univ.filter fun p => M l p = true).card = 11
  heavyRows : ∀ a : Fin 8, (S.filter fun p => M (.inl a) p = true).card = 4
  lightRows : ∀ b : Fin 72, (S.filter fun p => M (.inr b) p = true).card = 2
  inside : ∀ p ∈ S, (heavyAt M p).card = 2 ∧ (lightAt M p).card = 9
  outside : ∀ p ∉ S, 2 * (heavyAt M p).card + (lightAt M p).card = 8
  rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true
  colPairs : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
    M m p = true → M m q = true → l = m
  maxSupport : ∀ p ∉ S, (heavyAt M p).card ≤ 3
  tripleCount : (univ.filter fun p => p ∉ S ∧ (heavyAt M p).card = 3).card = 1
  graph : exteriorGraph (fun a p => M (.inl a) p) S (Equiv.refl _) = adj 0x35a5807
  triple : ∀ p ∉ S, (heavyAt M p).card = 3 → heavyAt M p = {2,4,7}

def NoLayout (column : Finset Edge) : Prop :=
  ¬ ∃ (M : Matrix) (S : Finset Points) (points : Fin 16 ≃ ↥S) (label : Fin 72 → Edge) (q : Points),
    Geometry M S ∧ Function.Injective label ∧
    (∀ i, heavyAt M (points i).val = codeLabel i) ∧
    (∀ b i, M (.inr b) (points i).val = true ↔ i = (label b).1 ∨ i = (label b).2) ∧
    q ∉ S ∧ heavyAt M q = {3,5} ∧ (lightAt M q).image label = column

def H1 : Prop := NoLayout {(0,10),(2,4),(3,13),(6,15)}
def H2 : Prop := NoLayout {(0,10),(2,6),(3,13),(4,15)}
def H3 : Prop := NoLayout {(0,15),(2,4),(3,13),(6,10)}
def H4 : Prop := NoLayout {(0,15),(2,6),(3,10),(4,13)}

private def rowPermutation (f : Equiv.Perm (Fin 8)) : Equiv.Perm Lines :=
  Equiv.sumCongr f (Equiv.refl _)

private def relabelHeavy (M : Matrix) (f : Equiv.Perm (Fin 8)) : Matrix :=
  fun l p => M (rowPermutation f l) p

private lemma relabel_heavy_card (M : Matrix) (f : Equiv.Perm (Fin 8)) (p : Points) :
    (heavyAt (relabelHeavy M f) p).card = (heavyAt M p).card := by
  have same : heavyAt (relabelHeavy M f) p = (heavyAt M p).map f.symm.toEmbedding := by
    apply Finset.ext
    intro a
    rw [Finset.mem_map]
    constructor
    · intro onA
      have present : relabelHeavy M f (.inl a) p = true := mem_heavyAt.mp onA
      change M (.inl (f a)) p = true at present
      exact ⟨f a, mem_heavyAt.mpr present, f.symm_apply_apply a⟩
    · rintro ⟨b, onB, equal⟩
      apply mem_heavyAt.mpr
      change M (.inl (f a)) p = true
      change f.symm b = a at equal
      rw [← equal, f.apply_symm_apply]
      exact mem_heavyAt.mp onB
  rw [same, Finset.card_map]

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1.H2 := by
  classical
  intro first second third fourth
  rintro ⟨M,S,size,rows,heavyRows,lightRows,inside,outside,rowPairs,cols,maxTriple,tripleCount,e,word⟩
  let triples := univ.filter fun p : Points => p ∉ S ∧ (heavyAt M p).card = 3
  have count : triples.card = 1 := tripleCount
  obtain ⟨q, singleton⟩ := Finset.card_eq_one.mp count
  have belongs : q ∈ triples := singleton ▸ Finset.mem_singleton_self q
  obtain ⟨_, external, three⟩ := Finset.mem_filter.mp belongs
  have shape : encode (exteriorGraph (fun a p => M (.inl a) p) S e) = 0x35a5807 := by
    rw [← word_model_syntax]
    exact word
  obtain ⟨f, renamedWord, chosen⟩ :=
    WeightSixteenTripleSymmetry.normalize M S rows rowPairs cols inside outside e shape q external three
  let N := relabelHeavy M f
  have heavyCount (p : Points) : (heavyAt N p).card = (heavyAt M p).card := relabel_heavy_card M f p
  have lightCount (p : Points) : lightAt N p = lightAt M p := rfl
  have geometry : Geometry N S := by
    refine ⟨size, ?_, ?_, lightRows, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l
      exact rows (rowPermutation f l)
    · intro a
      exact heavyRows (f a)
    · intro p hp
      rw [heavyCount, lightCount]
      exact inside p hp
    · intro p hp
      rw [heavyCount, lightCount]
      exact outside p hp
    · intro l m ne
      exact rowPairs (rowPermutation f l) (rowPermutation f m)
        (fun equal => ne ((rowPermutation f).injective equal))
    · intro p t different l m atL atT atM atMT
      exact (rowPermutation f).injective (cols p t different _ _ atL atT atM atMT)
    · intro p hp
      rw [heavyCount]
      exact maxTriple p hp
    · have same : (univ.filter fun p => p ∉ S ∧ (heavyAt N p).card = 3) = triples := by
        apply Finset.ext
        intro p
        simp [triples, heavyCount]
      rw [same, count]
    · let G := exteriorGraph (fun a p => M (.inl a) p) S f
      have recovered := recover_adjacency G (exteriorGraph_symm _ _ _) (exteriorGraph_loopfree _ _ _)
      change encode G = 0x35a5807 at renamedWord
      rw [renamedWord] at recovered
      calc
        _ = G := by
          funext a b
          apply Bool.eq_iff_iff.mpr
          simp [G, exteriorGraph, WeightSixteenCubicGeometry.mem_outer,
            WeightSixteenCubicGeometry.together, N, relabelHeavy, rowPermutation]
        _ = _ := recovered.symm
    · intro p hp degree
      rw [heavyCount] at degree
      have inTriples : p ∈ triples := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, degree⟩
      have same : p = q := Finset.mem_singleton.mp (singleton ▸ inTriples)
      rw [same]
      exact chosen
  obtain ⟨points,label,p,injective,heavyMembership,lightMembership,out,support,cases⟩ :=
    WeightSixteenColumn35Geometry.column_35_cases N S geometry.graph geometry.rowSize geometry.lightRows
      geometry.inside geometry.outside geometry.maxSupport geometry.triple geometry.rowPairs geometry.colPairs
  simp only [Finset.mem_insert, Finset.mem_singleton] at cases
  rcases cases with hit | hit | hit | hit
  · exact first ⟨N,S,points,label,p,geometry,injective,heavyMembership,lightMembership,out,support,hit⟩
  · exact second ⟨N,S,points,label,p,geometry,injective,heavyMembership,lightMembership,out,support,hit⟩
  · exact third ⟨N,S,points,label,p,geometry,injective,heavyMembership,lightMembership,out,support,hit⟩
  · exact fourth ⟨N,S,points,label,p,geometry,injective,heavyMembership,lightMembership,out,support,hit⟩

end WeightSixteenColumn35Reduction


namespace WeightSixteenPublicColumn35

open Finset WeightSixteenCubicGraphs WeightSixteenTripleNumerics
open WeightSixteenColumn35Reduction WeightSixteenDenseMatchings WeightSixteenTripleColumnData

private def numberedPairs : List (Fin 8 × Fin 8) :=
  (List.finRange 8).flatMap fun a => ((List.finRange 8).filter (a < ·)).map fun b => (a,b)

private def numberedCode : List (Fin 8 × Fin 8) :=
  (numberedPairs.zipIdx.filter fun x => !(0x35a5807 : Nat).testBit x.2).map Prod.fst

private lemma code_agrees : ∀ i : Fin 16,
    codeLabel i = {numberedCode[i.val]!.1, numberedCode[i.val]!.2} := by decide +kernel

end WeightSixteenPublicColumn35

open Finset WeightSixteenCubicGraphs WeightSixteenTripleNumerics WeightSixteenTripleTriangleObstruction
open WeightSixteenColumn35Reduction WeightSixteenDenseMatchings WeightSixteenPublicColumn35

set_option maxRecDepth 12000 in
theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1.H1 := by
  classical
  intro given
  by_contra missing
  have exclude (column : Finset Edge)
      (allowed : column ∈ ({{(0,10),(2,4),(3,13),(6,15)}, {(0,10),(2,6),(3,13),(4,15)},
        {(0,15),(2,4),(3,13),(6,10)}, {(0,15),(2,6),(3,10),(4,13)}} : Finset (Finset Edge))) :
      NoLayout column := by
    rintro ⟨M,S,points,label,q,geometry,_,heavyLabel,lightLabel,out,support,asColumn⟩
    apply missing
    refine ⟨M,S,⟨geometry.size,geometry.rowSize,geometry.heavyRows,geometry.lightRows,
      geometry.inside,geometry.outside,geometry.rowPairs,geometry.colPairs,geometry.maxSupport,
      geometry.tripleCount⟩,?_,geometry.triple,points,label,q,?_,lightLabel,out,support,?_⟩
    · have graphWord : encode (exteriorGraph (fun a p => M (.inl a) p) S (Equiv.refl _)) = 0x35a5807 := by
        rw [geometry.graph]
        decide +kernel
      rw [← word_model_syntax] at graphWord
      exact graphWord
    · intro i
      exact (heavyLabel i).trans (WeightSixteenPublicColumn35.code_agrees i)
    · change (lightAt M q).image label ∈ _
      rw [asColumn]
      exact allowed
  have refuse := WeightSixteenColumn35Reduction.main
    (exclude _ (by decide)) (exclude _ (by decide)) (exclude _ (by decide)) (exclude _ (by decide))
  obtain ⟨M,S,⟨size,rows,heavy,light,inside,outside,rowPairs,colPairs,maxSupport,tripleCount⟩,e,word⟩ := given
  exact refuse ⟨M,S,size,rows,heavy,light,inside,outside,rowPairs,colPairs,maxSupport,tripleCount,e,word⟩
