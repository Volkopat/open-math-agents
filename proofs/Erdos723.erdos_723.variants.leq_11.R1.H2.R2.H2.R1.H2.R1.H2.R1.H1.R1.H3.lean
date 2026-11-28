import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise

/-! The group-zero key interval is refuted by exact-cover searches on three pairs of groups. -/

-- The star enumeration and its connection to the source order are adapted from
-- @avivorly's merged sibling proof ending in R1.H2.R1.H2.
namespace Erdos723Interval

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

namespace WeightFifteenLargeCatalog

def vertexMask (g : Fin 15) : Nat :=
  ([32760, 32711, 32319, 29183, 4095, 28095, 23543, 16239,
      30431, 14334, 24317, 31611, 28635, 32237, 32694] : List Nat)[g.val]'g.isLt

def endpointMask (g : Fin 60) : Nat :=
  ([17, 33, 129, 257, 513, 1025, 4097, 8193,
      10, 34, 66, 130, 1026, 2050, 4098, 16386,
      12, 20, 68, 260, 516, 2052, 8196, 16388,
      136, 264, 520, 2056, 4104, 16392, 80, 272,
      1040, 2064, 4112, 8208, 96, 160, 544, 1056,
      8224, 16416, 1088, 2112, 8256, 16448, 640, 2176,
      4224, 8320, 768, 1280, 4352, 16640, 8704, 16896,
      5120, 17408, 6144, 10240] : List Nat)[g.val]'g.isLt

def eligibleMask (g : Fin 15) : Nat :=
  ([1152921504590069760, 1152917106576915708, 1134911294713099251, 14411560693780431, 3603047246675775, 732542662748126127, 339435142697119327, 962677200052385786,
      271188003732839925, 98892265553878784, 540976176994648183, 933436301946972123, 787844113021058493, 1097681697835385070, 1152855463058668032] : List Nat)[g.val]'g.isLt


end WeightFifteenLargeCatalog

namespace FiniteMaskCoverEnumeration

abbrev Allowed := Nat × Nat

def enumerate (options : List Allowed) : Nat → Nat → List (Finset Nat)
  | 0, remaining => if remaining == 0 then [∅] else []
  | fuel + 1, remaining =>
      if remaining == 0 then [∅]
      else options.flatMap fun pair =>
        if pair.1.testBit remaining.log2 && (pair.1 &&& remaining == pair.1) then
          (enumerate options fuel (remaining ^^^ pair.1)).map (insert pair.2)
        else []

def covers (options : List Allowed) (remaining : Nat) (picked : Finset Allowed) : Prop :=
  (∀ a ∈ picked, a ∈ options) ∧
  (∀ a ∈ picked, ∀ i, a.1.testBit i = true → remaining.testBit i = true) ∧
  (∀ a ∈ picked, ∀ b ∈ picked, a ≠ b → ∀ i, a.1.testBit i = true → b.1.testBit i = false) ∧
  ∀ i, remaining.testBit i = true → ∃ a ∈ picked, a.1.testBit i = true

lemma cover_empty (options : List Allowed) (nonempty : ∀ a ∈ options, a.1 ≠ 0)
    (picked : Finset Allowed) (valid : covers options 0 picked) :
    picked = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have ne := nonempty a (valid.1 a ha)
  have bit := Nat.testBit_log2 ne
  have impossible := valid.2.1 a ha a.1.log2 bit
  simp at impossible

lemma cover_erase (options : List Allowed) (remaining : Nat) (picked : Finset Allowed)
    (valid : covers options remaining picked) (first : Allowed) (selected : first ∈ picked) :
    covers options (remaining ^^^ first.1) (picked.erase first) := by
  obtain ⟨members, inside, separated, covering⟩ := valid
  refine ⟨?_,?_,?_,?_⟩
  · intro a ha
    exact members a (Finset.mem_of_mem_erase ha)
  · intro a ha i bit
    obtain ⟨unequal, member⟩ := Finset.mem_erase.mp ha
    have old := inside a member i bit
    have not_first := separated a member first selected unequal i bit
    simp [Nat.testBit_xor, old, not_first]
  · intro a ha b hb
    exact separated a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  · intro i bit
    have avoid : first.1.testBit i = false := by
      cases at_i : first.1.testBit i
      · rfl
      · have old := inside first selected i at_i
        simp [Nat.testBit_xor, at_i, old] at bit
    have old : remaining.testBit i = true := by simpa [Nat.testBit_xor, avoid] using bit
    obtain ⟨a, ha, covers_i⟩ := covering i old
    have other : a ≠ first := by
      intro same
      rw [same, avoid] at covers_i
      contradiction
    exact ⟨a, Finset.mem_erase.mpr ⟨other, ha⟩, covers_i⟩

theorem enumerate_complete (options : List Allowed) (nonempty : ∀ a ∈ options, a.1 ≠ 0)
    (fuel remaining : Nat) (picked : Finset Allowed) (room : picked.card ≤ fuel)
    (valid : covers options remaining picked) :
    picked.image Prod.snd ∈ enumerate options fuel remaining := by
  induction fuel generalizing remaining picked with
  | zero =>
      have empty : picked = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero room)
      have rem : remaining = 0 := by
        by_contra nonzero
        have covered := valid.2.2.2 remaining.log2 (Nat.testBit_log2 nonzero)
        simp [empty] at covered
      simp [enumerate, rem, empty]
  | succ fuel ih =>
      by_cases empty : remaining = 0
      · subst remaining
        simp [enumerate, cover_empty options nonempty picked valid]
      · obtain ⟨first, selected, bit_pivot⟩ :=
          valid.2.2.2 remaining.log2 (Nat.testBit_log2 empty)
        have in_options := valid.1 first selected
        have subset : first.1 &&& remaining = first.1 := by
          apply Nat.eq_of_testBit_eq
          intro i
          cases bit : first.1.testBit i
          · simp [bit]
          · simp [bit, valid.2.1 first selected i bit]
        have mask_ok : (first.1.testBit remaining.log2 && (first.1 &&& remaining == first.1)) = true := by
          simp [bit_pivot, subset]
        have less : (picked.erase first).card ≤ fuel := by
          rw [Finset.card_erase_of_mem selected]
          omega
        have step := ih (remaining ^^^ first.1) (picked.erase first) less
          (cover_erase options remaining picked valid first selected)
        simp only [enumerate, beq_iff_eq, if_neg empty, List.mem_flatMap]
        refine ⟨first, in_options, ?_⟩
        rw [if_pos mask_ok, List.mem_map]
        refine ⟨(picked.erase first).image Prod.snd, step, ?_⟩
        rw [← Finset.image_insert, Finset.insert_erase selected]

end FiniteMaskCoverEnumeration
namespace WeightFifteenIndexedSearch

open Finset FiniteMaskCoverEnumeration FiniteSearchMasks
open WeightFifteenLargeCatalog (vertexMask endpointMask eligibleMask)

def indexOptions (g : Fin 15) : List Allowed :=
  (List.finRange 60).filterMap fun p =>
    if (eligibleMask g).testBit p.val then some (endpointMask p, p.val) else none

def pack (bits : Finset Nat) : Nat := bitMask (List.range 60) fun p => decide (p ∈ bits)

def numericCatalog (g : Fin 15) : List Nat :=
  ((enumerate (indexOptions g) 60 (vertexMask g)).map pack).mergeSort

lemma vertex_bound : ∀ g : Fin 15, vertexMask g < 2^15 := by decide +kernel
lemma endpoint_bound : ∀ p : Fin 60, endpointMask p < 2^15 := by decide +kernel
lemma endpoint_positive : ∀ p : Fin 60, endpointMask p ≠ 0 := by decide +kernel
lemma eligible_bound : ∀ g : Fin 15, eligibleMask g < 2^60 := by decide +kernel

lemma endpoint_subset : ∀ (g : Fin 15) (p : Fin 60),
    (eligibleMask g).testBit p.val = true → (endpointMask p &&& vertexMask g) = endpointMask p :=
  by decide +kernel

lemma read_indexOptions (g : Fin 15) (q : Allowed) (mem : q ∈ indexOptions g) :
    ∃ p : Fin 60, ((eligibleMask g).testBit p.val = true) ∧ (endpointMask p, p.val) = q := by
  obtain ⟨p, hp, value⟩ := List.mem_filterMap.mp mem
  by_cases avail : (eligibleMask g).testBit p.val = true
  · exact ⟨p, avail, by simpa [avail] using value⟩
  · simp [avail] at value

lemma pack_testBit (b : Finset Nat) (i : Nat) :
    (pack b).testBit i = true ↔ i < 60 ∧ i ∈ b := by
  rw [pack, bitMask_testBit]
  by_cases lt : i < 60
  · have inside : i < (List.range 60).length := by simpa using lt
    rw [List.getElem?_eq_getElem inside, List.getElem_range]
    simp [lt]
  · have outside : (List.range 60).length ≤ i := by simpa using Nat.le_of_not_gt lt
    rw [List.getElem?_eq_none outside]
    simp [lt]

theorem indexed_star_in_catalog (g : Fin 15) (star : Finset (Fin 60))
    (uses : ∀ p ∈ star, (eligibleMask g).testBit p.val = true)
    (exactCover : ∀ m : Fin 15, (vertexMask g).testBit m.val = true →
      ∃! p : Fin 60, p ∈ star ∧ (endpointMask p).testBit m.val = true) :
    pack (star.image Fin.val) ∈ numericCatalog g := by
  let selected := star.image fun p => (endpointMask p, p.val)
  have allowed_nonempty : ∀ a ∈ indexOptions g, a.1 ≠ 0 := by
    intro q hq
    obtain ⟨p, _, rfl⟩ := read_indexOptions g q hq
    exact endpoint_positive p
  have room : selected.card ≤ 60 := by
    exact Finset.card_image_le.trans (by simpa using Finset.card_le_univ star)
  have within (p : Fin 60) (hp : p ∈ star) (b : Nat) (bit : (endpointMask p).testBit b = true) :
      (vertexMask g).testBit b = true := by
    have eq := congrArg (fun m => m.testBit b) (endpoint_subset g p (uses p hp))
    simpa only [Nat.testBit_land, bit, Bool.true_and] using eq
  have chosen : covers (indexOptions g) (vertexMask g) selected := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      exact List.mem_filterMap.mpr ⟨p, List.mem_finRange p, by simp [uses p hp]⟩
    · intro q hq b bit
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      exact within p hp b bit
    · intro a ha b hb distinct i on_a
      obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hb
      have here : i < 15 := by
        by_contra outside
        have less : endpointMask p < 2^i :=
          (endpoint_bound p).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt outside))
        exact Bool.false_ne_true ((Nat.testBit_lt_two_pow less).symm.trans on_a)
      cases there : (endpointMask q).testBit i
      · rfl
      · obtain ⟨_, _, unique⟩ := exactCover ⟨i,here⟩ (within p hp i on_a)
        have same := (unique p ⟨hp, on_a⟩).trans (unique q ⟨hq, there⟩).symm
        exact (distinct (congrArg (fun w : Fin 60 => (endpointMask w, w.val)) same)).elim
    · intro i required
      have here : i < 15 := by
        by_contra outside
        have less : vertexMask g < 2^i :=
          (vertex_bound g).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt outside))
        exact Bool.false_ne_true ((Nat.testBit_lt_two_pow less).symm.trans required)
      obtain ⟨p, ⟨hp, bit⟩, _⟩ := exactCover ⟨i,here⟩ required
      exact ⟨(endpointMask p,p.val), mem_image_of_mem _ hp, bit⟩
  have member := enumerate_complete _ allowed_nonempty 60 _ selected room chosen
  unfold numericCatalog
  rw [List.mem_mergeSort]
  apply List.mem_map.mpr
  refine ⟨_, member, ?_⟩
  rw [show selected.image Prod.snd = star.image Fin.val by
    unfold selected
    rw [Finset.image_image]
    rfl]

end WeightFifteenIndexedSearch

namespace WeightFifteenIndexedSearch

open Finset FiniteMaskCoverEnumeration FiniteSearchMasks
open WeightFifteenLargeCatalog (vertexMask endpointMask eligibleMask)

def enumerateMasks (options : List Allowed) : Nat → Nat → List Nat
  | 0, remaining => if remaining == 0 then [0] else []
  | fuel + 1, remaining =>
      if remaining == 0 then [0]
      else options.flatMap fun pair =>
        if pair.1.testBit remaining.log2 && (pair.1 &&& remaining == pair.1) then
          (enumerateMasks options fuel (remaining ^^^ pair.1)).map (fun m => 2^pair.2 ||| m)
        else []

lemma pack_empty : pack ∅ = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases b : (pack ∅).testBit i with
  | false => simp
  | true => simpa using ((pack_testBit _ _).mp b).2

lemma pack_insert (p : Nat) (lt : p < 60) (b : Finset Nat) :
    pack (insert p b) = 2^p ||| pack b := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  by_cases equal : p = i
  · subst i
    simp [pack_testBit, lt]
  · simp [pack_testBit, equal, Ne.symm equal]

lemma enumerateMasks_correct (options : List Allowed) (labels : ∀ a ∈ options, a.2 < 60)
    (fuel remaining : Nat) :
    enumerateMasks options fuel remaining = (enumerate options fuel remaining).map pack := by
  induction fuel generalizing remaining with
  | zero =>
    by_cases empty : remaining = 0 <;> simp [enumerateMasks, enumerate, empty, pack_empty]
  | succ fuel ih =>
    by_cases empty : remaining = 0
    · simp [enumerateMasks, enumerate, empty, pack_empty]
    · simp only [enumerateMasks, enumerate, beq_iff_eq, if_neg empty, List.map_flatMap]
      apply List.flatMap_congr
      intro a ha
      by_cases good : (a.1.testBit remaining.log2 && (a.1 &&& remaining == a.1)) = true
      · simp only [if_pos good, ih, List.map_map, Function.comp_def, pack_insert a.2 (labels a ha)]
      · simp [good]


def directCatalog (g : Fin 15) : List Nat :=
  enumerateMasks (indexOptions g) 60 (vertexMask g)

theorem directCatalog_mem (g : Fin 15) (x : Nat) :
    x ∈ directCatalog g ↔ x ∈ numericCatalog g := by
  unfold directCatalog numericCatalog
  rw [List.mem_mergeSort, enumerateMasks_correct]
  intro a ha
  obtain ⟨p, _, rfl⟩ := read_indexOptions g a ha
  exact p.isLt

lemma star_mask_bit (star : Finset (Fin 60)) (b : Nat) :
    (pack (star.image Fin.val)).testBit b = true ↔ ∃ p ∈ star, p.val = b := by
  rw [pack_testBit]
  constructor
  · exact fun h => Finset.mem_image.mp h.2
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.isLt, Finset.mem_image_of_mem _ hp⟩


end WeightFifteenIndexedSearch

namespace WeightFifteenIndexedSymmetry

open Finset WeightFifteenLargeCatalog

def IsCover (s : Fin 15 → Fin 6 → Finset (Fin 60)) : Prop :=
  (∀ g i p, p ∈ s g i → (eligibleMask g).testBit p.val = true) ∧
  (∀ g i (m : Fin 15), (vertexMask g).testBit m.val = true →
    ∃! p : Fin 60, p ∈ s g i ∧ (endpointMask p).testBit m.val = true) ∧
  (∀ g p, (eligibleMask g).testBit p.val = true → ∃! i, p ∈ s g i) ∧
  ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1

end WeightFifteenIndexedSymmetry


namespace WeightFifteenRankAgreement

open Finset FiniteSearchMasks WeightFifteenLargeCatalog
open WeightFifteenIndexedSearch

def recurse (endpoint : Fin 60 → Nat) (options : List (Fin 60)) (fuel remaining : Nat) :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun w => if w=0 then [0] else [])
    (fun _ next w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoint p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else [])
    fuel remaining

lemma recurse_eq (endpoint : Fin 60 → Nat) (options : List (Fin 60)) (fuel remaining : Nat) :
    recurse endpoint options fuel remaining =
      enumerateMasks (options.map fun p => (endpoint p, p.val)) fuel remaining := by
  induction fuel generalizing remaining with
  | zero => simp [recurse, enumerateMasks]
  | succ fuel ih =>
    by_cases empty : remaining = 0
    · simp [recurse, enumerateMasks, empty]
    · change (if remaining = 0 then [0] else options.flatMap fun p =>
        if (endpoint p).testBit remaining.log2 && (endpoint p &&& remaining == endpoint p) then
          (recurse endpoint options fuel (remaining ^^^ endpoint p)).map (fun u => 2^p.val ||| u) else []) = _
      simp only [if_neg empty, enumerateMasks, beq_iff_eq, List.flatMap_map]
      apply List.flatMap_congr
      intro p _
      rw [ih]

lemma option_rows (options : List (Fin 60)) (eligible : Fin 60 → Bool) (endpoint : Fin 60 → Nat) :
    (options.filter eligible).map (fun p => (endpoint p, p.val)) =
      options.filterMap (fun p => if eligible p then some (endpoint p, p.val) else none) := by
  induction options with
  | nil => rfl
  | cons p rest ih => cases ok : eligible p <;> simp [ok, ih]

lemma word_from_fins (star : Finset (Fin 60)) :
    (((List.finRange 60).map fun p => if p∈star then 2^p.val else 0).foldr Nat.lor 0) =
      pack (star.image Fin.val) := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [foldr_or_testBit, star_mask_bit]
  constructor
  · rintro ⟨mask, member, bit⟩
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
    by_cases present : p ∈ star
    · exact ⟨p, present, by simpa [present, Nat.testBit_two_pow] using bit⟩
    · simp [present] at bit
  · rintro ⟨p, present, rfl⟩
    exact ⟨_, List.mem_map_of_mem (List.mem_finRange p), by simp [present]⟩

end WeightFifteenRankAgreement

namespace WeightFifteenLargeCatalog

lemma row_testBit (packed width base index : Nat) (within : index < width) :
    (((packed >>> (width * base)) &&& (2^width-1)).testBit index) =
      packed.testBit (width * base + index) := by
  simp only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    decide_eq_true within, Bool.and_true, Nat.add_comm]


set_option maxRecDepth 10000 in
lemma row_eligible : ∀ g : Fin 15,
    ((0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000 : Nat) >>> (60 * g.val)) &&& (2^60-1) = eligibleMask g := by decide +kernel

lemma packed_eligible (g : Fin 15) (p : Fin 60) :
    (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000 : Nat).testBit (60*g.val+p.val) = (eligibleMask g).testBit p.val := by
  rw [← row_testBit _ _ _ _ p.isLt, row_eligible]

set_option maxRecDepth 10000 in
lemma row_vertex : ∀ g : Fin 15,
    ((0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8 : Nat) >>> (15 * g.val)) &&& (2^15-1) = vertexMask g := by decide +kernel

lemma packed_vertex (g : Fin 15) (m : Fin 15) :
    (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8 : Nat).testBit (15*g.val+m.val) = (vertexMask g).testBit m.val := by
  rw [← row_testBit _ _ _ _ m.isLt, row_vertex]

set_option maxRecDepth 10000 in
lemma row_endpoint : ∀ p : Fin 60,
    ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011 : Nat) >>> (15 * p.val)) &&& (2^15-1) = endpointMask p := by decide +kernel

lemma packed_endpoint (p : Fin 60) (m : Fin 15) :
    (0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011 : Nat).testBit (15*p.val+m.val) = (endpointMask p).testBit m.val := by
  rw [← row_testBit _ _ _ _ m.isLt, row_endpoint]

end WeightFifteenLargeCatalog

namespace WeightFifteenRankAgreement

open WeightFifteenLargeCatalog WeightFifteenIndexedSearch WeightFifteenIndexedSymmetry

def sourceAllowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val)
def sourceRequired (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val)
def sourceEndpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767

def sourceValid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → sourceAllowed g p = true) ∧
    (∀ g i m, sourceRequired g m = true → ∃! p, p∈s g i ∧ (sourceEndpoints p).testBit m.val = true) ∧
    (∀ g p, sourceAllowed g p = true → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1

def sourceCatalogue : List Nat := recurse sourceEndpoints
  ((List.finRange 60).filter fun p => decide (sourceAllowed 0 p = true)) 60 32760

def sourceRank (s : Fin 15 → Fin 6 → Finset (Fin 60)) : Nat :=
  let word (star : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈star then 2^p.val else 0).foldr Nat.lor 0
  ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => sourceCatalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0

lemma sourceEndpoints_eq (p : Fin 60) : sourceEndpoints p = endpointMask p := row_endpoint p

lemma sourceValid_eq (s : Fin 15 → Fin 6 → Finset (Fin 60)) : sourceValid s ↔ IsCover s := by
  unfold sourceValid IsCover sourceAllowed sourceRequired
  simp only [packed_eligible, packed_vertex, sourceEndpoints_eq]

lemma sourceCatalogue_eq : sourceCatalogue = directCatalog 0 := by
  unfold sourceCatalogue directCatalog indexOptions
  rw [recurse_eq, option_rows]
  unfold sourceAllowed
  simp only [packed_eligible, sourceEndpoints_eq, Bool.decide_eq_true]
  rfl

end WeightFifteenRankAgreement

open Finset FiniteMaskCoverEnumeration
open WeightFifteenLargeCatalog WeightFifteenIndexedSearch
open WeightFifteenIndexedSymmetry (IsCover)
open WeightFifteenRankAgreement

def word (s : Finset (Fin 60)) : Nat := pack (s.image Fin.val)

theorem star_catalogue (s : Fin 15 → Fin 6 → Finset (Fin 60)) (h : IsCover s)
    (g : Fin 15) (i : Fin 6) : word (s g i) ∈ directCatalog g :=
  (directCatalog_mem g _).mpr (indexed_star_in_catalog g _ (h.1 g i) (h.2.1 g i))

theorem group_cover (s : Fin 15 → Fin 6 → Finset (Fin 60)) (h : IsCover s)
    (g : Fin 15) (tag : Nat → Nat) (options : List Allowed)
    (catalogued : ∀ i, (word (s g i), tag (word (s g i))) ∈ options) :
    covers options (eligibleMask g)
      (Finset.univ.image fun i => (word (s g i), tag (word (s g i)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact catalogued i
  · intro a ha b bit
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨p, hp, rfl⟩ := (star_mask_bit _ b).mp bit
    exact h.1 g i p hp
  · intro a ha b hb different bit on_a
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨p, hp, place⟩ := (star_mask_bit _ bit).mp on_a
    cases on_b : (word (s g j)).testBit bit with
    | false => rfl
    | true =>
      obtain ⟨q, hq, place'⟩ := (star_mask_bit _ bit).mp on_b
      have eq : p = q := Fin.ext (place.trans place'.symm)
      subst q
      obtain ⟨_, _, unique⟩ := h.2.2.1 g p (h.1 g i p hp)
      have same := (unique i hp).trans (unique j hq).symm
      exact (different (by rw [same])).elim
  · intro b needed
    have inside : b < 60 := by
      by_contra outside
      have bounded : eligibleMask g < 2^b :=
        (eligible_bound g).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt outside))
      exact Bool.false_ne_true ((Nat.testBit_lt_two_pow bounded).symm.trans needed)
    obtain ⟨i, member, _⟩ := h.2.2.1 g ⟨b, inside⟩ needed
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ i), (star_mask_bit _ b).mpr ⟨_, member, rfl⟩⟩

end Erdos723Interval

namespace Erdos723Interval

open Finset FiniteMaskCoverEnumeration
open WeightFifteenLargeCatalog WeightFifteenIndexedSearch
open WeightFifteenIndexedSymmetry (IsCover)

def compatible (a b : Nat) : Bool :=
  let w := a &&& b
  (w &&& (w - 1)) == 0

lemma compatible_comm (a b : Nat) : compatible a b = compatible b a := by
  unfold compatible
  rw [Nat.and_comm]

lemma compatible_of_inter (a b : Finset (Fin 60)) (small : (a ∩ b).card ≤ 1) :
    compatible (word a) (word b) = true := by
  have intersection : word a &&& word b = word (a ∩ b) := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    simp only [Nat.testBit_land, Bool.and_eq_true, word, star_mask_bit, Finset.mem_inter]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, ⟨q, hq, eq⟩⟩
      have same : q = p := Fin.ext eq
      exact ⟨p, ⟨hp, same ▸ hq⟩, rfl⟩
    · rintro ⟨p, ⟨ha, hb⟩, eq⟩
      exact ⟨⟨p, ha, eq⟩, ⟨p, hb, eq⟩⟩
  unfold compatible
  rw [intersection]
  by_cases h : a ∩ b = ∅
  · simp [h, word, pack_empty]
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr h
    have singleton : a ∩ b = {p} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨hp, fun q hq => Finset.card_le_one.mp small q hq p hp⟩
    rw [singleton]
    have power : word {p} = 2 ^ p.val := by
      simpa [word, pack_empty] using pack_insert p.val p.isLt (∅ : Finset Nat)
    simp [power, Nat.and_two_pow_sub_one_eq_mod]

lemma disjoint_masks {opts : List Allowed} {r : Nat} {p : Finset Allowed}
    (valid : covers opts r p) {a b : Allowed} (ha : a ∈ p) (hb : b ∈ p)
    (distinct : a ≠ b) : a.1 &&& b.1 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases bit : a.1.testBit i
  · simp [bit]
  · simp [bit, valid.2.2.1 a ha b hb distinct i bit]

structure Row where
  remaining : Nat
  options : List Allowed

def select (r : Row) (a : Allowed) : Row :=
  ⟨r.remaining ^^^ a.1, r.options.filter fun b => (a.1 &&& b.1) == 0⟩

def restrict (r : Row) (a : Allowed) : Row :=
  ⟨r.remaining, r.options.filter fun b => compatible a.1 b.1⟩

def Joint (left right : Row) : Prop :=
  ∃ p q : Finset Allowed, covers left.options left.remaining p ∧
    covers right.options right.remaining q ∧
    ∀ a ∈ p, ∀ b ∈ q, compatible a.1 b.1 = true

lemma joint_swap {l r : Row} (ok : Joint l r) : Joint r l := by
  obtain ⟨p, q, hp, hq, hc⟩ := ok
  exact ⟨q, p, hq, hp, fun b hb a ha => compatible_comm a.1 b.1 ▸ hc a ha b hb⟩

lemma narrow_cover {opts : List Allowed} {r : Nat} {p : Finset Allowed}
    (valid : covers opts r p) (f : Allowed → Bool) (ok : ∀ a ∈ p, f a = true) :
    covers (opts.filter f) r p :=
  ⟨fun a ha => List.mem_filter.mpr ⟨valid.1 a ha, ok a ha⟩, valid.2⟩

lemma joint_step {l r : Row} (ok : Joint l r) {pivot : Nat}
    (bit : l.remaining.testBit pivot = true) :
    ∃ a ∈ l.options.filter (fun a => a.1.testBit pivot), Joint (select l a) (restrict r a) := by
  obtain ⟨p, q, hp, hq, hc⟩ := ok
  obtain ⟨a, ap, at_pivot⟩ := hp.2.2.2 pivot bit
  refine ⟨a, List.mem_filter.mpr ⟨hp.1 a ap, at_pivot⟩, p.erase a, q, ?_, ?_, ?_⟩
  · apply narrow_cover (cover_erase _ _ _ hp a ap)
    intro b hb
    have mem := Finset.mem_erase.mp hb
    exact beq_iff_eq.mpr (disjoint_masks hp ap mem.2 (Ne.symm mem.1))
  · exact narrow_cover hq _ (hc a ap)
  · exact fun b hb c hcp => hc b (Finset.mem_of_mem_erase hb) c hcp

-- Each trace entry chooses an uncovered line. Entries at least 60 choose the
-- second row. The checker verifies every available branch at that line.
def replay : Nat → Row → Row → List Nat → Option (List Nat)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | fuel + 1, left, right, k :: trace =>
      let (a, b, pivot) := if k < 60 then (left, right, k) else (right, left, k - 60)
      if a.remaining.testBit pivot then
        (a.options.filter fun w => w.1.testBit pivot).foldlM
          (fun rest w => replay fuel (select a w) (restrict b w) rest) trace
      else none

lemma foldlM_branch {α β : Type} (f : β → α → Option β) (opts : List α)
    {before after : β} (ok : opts.foldlM f before = some after) {a : α} (mem : a ∈ opts) :
    ∃ u v, f u a = some v := by
  induction opts generalizing before with
  | nil => simp at mem
  | cons x xs ih =>
    cases hx : f before x with
    | none => simp [List.foldlM, hx] at ok
    | some next =>
      rcases List.mem_cons.mp mem with rfl | mem
      · exact ⟨before, next, hx⟩
      · exact ih (by simpa [List.foldlM, hx] using ok) mem

lemma replay_refutes {fuel : Nat} {l r : Row} {before after : List Nat}
    (checked : replay fuel l r before = some after) : ¬ Joint l r := by
  induction fuel generalizing l r before after with
  | zero => simp [replay] at checked
  | succ fuel ih =>
    cases before with
    | nil => simp [replay] at checked
    | cons k trace =>
      intro valid
      by_cases side : k < 60
      · simp only [replay, if_pos side] at checked
        split at checked
        next bit =>
          obtain ⟨a, ha, step⟩ := joint_step valid (by simpa using bit)
          obtain ⟨u, v, branch⟩ := foldlM_branch _ _ checked ha
          exact ih branch step
        next => contradiction
      · simp only [replay, if_neg side] at checked
        split at checked
        next bit =>
          obtain ⟨a, ha, step⟩ := joint_step (joint_swap valid) (by simpa using bit)
          obtain ⟨u, v, branch⟩ := foldlM_branch _ _ checked ha
          exact ih branch step
        next => contradiction

def allowedOptions (cat : List Nat) (seed : List Nat) : List Allowed :=
  (cat.filter fun w => seed.all (compatible w)).map fun w => (w, 0)

lemma joint_of_cover {s : Fin 15 → Fin 6 → Finset (Fin 60)} (h : IsCover s)
    {g j : Fin 15} (diff : g ≠ j) (hg : g ≠ 0) (hj : j ≠ 0)
    (seed : List Nat) (seedStars : ∀ w ∈ seed, ∃ i, w = word (s 0 i)) :
    Joint ⟨eligibleMask g, allowedOptions (directCatalog g) seed⟩
      ⟨eligibleMask j, allowedOptions (directCatalog j) seed⟩ := by
  have present (a : Fin 15) (ha : a ≠ 0) (i : Fin 6) :
      (word (s a i), 0) ∈ allowedOptions (directCatalog a) seed := by
    apply List.mem_map_of_mem
    refine List.mem_filter.mpr ⟨star_catalogue s h a i, List.all_eq_true.mpr ?_⟩
    intro w hw
    obtain ⟨k, rfl⟩ := seedStars w hw
    exact compatible_of_inter _ _ (h.2.2.2 a 0 i k ha)
  refine ⟨_, _, group_cover s h g (fun _ => 0) _ (present g hg),
    group_cover s h j (fun _ => 0) _ (present j hj), ?_⟩
  intro a ha b hb
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hb
  exact compatible_of_inter _ _ (h.2.2.2 g j i k diff)

end Erdos723Interval

namespace Erdos723Interval

open Finset FiniteMaskCoverEnumeration FiniteSearchMasks
open WeightFifteenLargeCatalog WeightFifteenIndexedSearch
open WeightFifteenIndexedSymmetry (IsCover)
open WeightFifteenRankAgreement

def lower : Nat := 0x1000000008000000000000020000000000004000000000010000000000400000000000000
def upper : Nat := 0x1000040000000000000000002000004000000000000000400000000000000000000400000

def seedKey (indices : List Nat) : Nat := (indices.map (fun i => 2^i)).foldr Nat.lor 0

lemma seedKey_bit (p : List Nat) (b : Nat) : (seedKey p).testBit b = true ↔ b ∈ p := by
  simp only [seedKey, foldr_or_testBit, List.mem_map]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, bit⟩
    have : j = b := by simpa [Nat.testBit_two_pow] using bit
    exact this ▸ hj
  · intro hb
    exact ⟨_, ⟨b, hb, rfl⟩, Nat.testBit_two_pow_self⟩

def rankWith (cat : List Nat) (s : Fin 15 → Fin 6 → Finset (Fin 60)) : Nat :=
  ((List.range 344).map fun b =>
    if (List.finRange 6).any (fun i => cat.idxOf (word (s 0 i)) == b) then 2^b else 0).foldr Nat.lor 0

lemma sourceRank_agree (s : Fin 15 → Fin 6 → Finset (Fin 60)) :
    sourceRank s = rankWith (directCatalog 0) s := by
  unfold sourceRank rankWith
  simp only [sourceCatalogue_eq, word_from_fins, word]
  rfl

lemma rankWith_bit (cat : List Nat) (s : Fin 15 → Fin 6 → Finset (Fin 60)) (b : Nat) :
    (rankWith cat s).testBit b = true ↔ b < 344 ∧ ∃ i, cat.idxOf (word (s 0 i)) = b := by
  unfold rankWith
  rw [foldr_or_testBit]
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, bit⟩
    split at bit
    next chosen =>
      have eq : j = b := by simpa [Nat.testBit_two_pow] using bit
      subst j
      obtain ⟨i, _, hi⟩ := List.any_eq_true.mp chosen
      exact ⟨List.mem_range.mp hj, i, beq_iff_eq.mp hi⟩
    next => simp at bit
  · rintro ⟨bound, i, hi⟩
    have chosen : ((List.finRange 6).any fun j => cat.idxOf (word (s 0 j)) == b) = true :=
      List.any_eq_true.mpr ⟨i, List.mem_finRange i, beq_iff_eq.mpr hi⟩
    exact ⟨2^b, ⟨b, List.mem_range.mpr bound, if_pos chosen⟩, Nat.testBit_two_pow_self⟩

lemma interval_top {k : Nat} (lo : lower < k) (hi : k ≤ upper) :
    k.testBit 288 = true ∧ k < 2^289 := by
  have lowBase : 2^288 ≤ lower := by decide +kernel
  have low : 2^288 ≤ k := lowBase.trans lo.le
  have highBase : upper < 2^289 := by decide +kernel
  have high : k < 2^289 := hi.trans_lt highBase
  have positive : k ≠ 0 := Nat.ne_of_gt ((Nat.zero_le lower).trans_lt lo)
  have a := (Nat.le_log2 positive).mpr low
  have b := (Nat.log2_lt positive).mpr high
  have eq : k.log2 = 288 := by omega
  exact ⟨eq ▸ Nat.testBit_log2 positive, high⟩

def enumerateLists : Nat → List Allowed → Nat → List (List Nat)
  | 0, _, remaining => if remaining == 0 then [[]] else []
  | fuel + 1, options, remaining =>
      if remaining == 0 then [[]]
      else options.flatMap fun pair =>
        if pair.1.testBit remaining.log2 && (pair.1 &&& remaining == pair.1) then
          let next := options.filter fun a => (pair.1 &&& a.1) == 0
          (enumerateLists fuel next (remaining ^^^ pair.1)).map (List.cons pair.2)
        else []

lemma enumerateLists_complete (fuel : Nat) (options : List Allowed)
    (nonempty : ∀ a ∈ options, a.1 ≠ 0) (remaining : Nat) (picked : Finset Allowed)
    (room : picked.card ≤ fuel) (valid : covers options remaining picked) :
    ∃ p ∈ enumerateLists fuel options remaining, p.toFinset = picked.image Prod.snd := by
  induction fuel generalizing options remaining picked with
  | zero =>
    have empty : picked = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero room)
    have rem : remaining = 0 := by
      by_contra nonzero
      have covered := valid.2.2.2 remaining.log2 (Nat.testBit_log2 nonzero)
      simp [empty] at covered
    exact ⟨[], by simp [enumerateLists, rem], by simp [empty]⟩
  | succ fuel ih =>
    by_cases empty : remaining = 0
    · subst remaining
      exact ⟨[], by simp [enumerateLists], by simp [cover_empty options nonempty picked valid]⟩
    · obtain ⟨first, selected, bit_pivot⟩ :=
        valid.2.2.2 remaining.log2 (Nat.testBit_log2 empty)
      have subset : first.1 &&& remaining = first.1 := by
        apply Nat.eq_of_testBit_eq
        intro i
        cases bit : first.1.testBit i
        · simp [bit]
        · simp [bit, valid.2.1 first selected i bit]
      have mask_ok : (first.1.testBit remaining.log2 && (first.1 &&& remaining == first.1)) = true := by
        simp [bit_pivot, subset]
      have less : (picked.erase first).card ≤ fuel := by
        rw [Finset.card_erase_of_mem selected]
        omega
      let next := options.filter fun a => (first.1 &&& a.1) == 0
      have tailCover : covers next (remaining ^^^ first.1) (picked.erase first) := by
        apply narrow_cover (cover_erase options remaining picked valid first selected)
        intro a ha
        obtain ⟨ne, mem⟩ := Finset.mem_erase.mp ha
        exact beq_iff_eq.mpr (disjoint_masks valid selected mem (Ne.symm ne))
      obtain ⟨tail, tailMem, tailSet⟩ := ih next
        (fun a h => nonempty a (List.mem_filter.mp h).1) _ _ less tailCover
      refine ⟨first.2 :: tail, ?_, ?_⟩
      · simp only [enumerateLists, beq_iff_eq, if_neg empty, List.mem_flatMap]
        refine ⟨first, valid.1 first selected, ?_⟩
        rw [if_pos mask_ok, List.mem_map]
        exact ⟨tail, tailMem, rfl⟩
      · rw [List.toFinset_cons, tailSet, ← Finset.image_insert, Finset.insert_erase selected]

def headPair (cat : List Nat) : Allowed := (cat[288]?.getD 0, 288)

def remainingOptions (cat : List Nat) : List Allowed :=
  cat.zipIdx.filter fun a => (a.2 < 288) && ((headPair cat).1 &&& a.1 == 0)

def intervalSeeds (cat : List Nat) : List (List Nat) :=
  (((enumerateLists 5 (remainingOptions cat) (eligibleMask 0 ^^^ (headPair cat).1)).map
    (List.cons 288)).filter fun p => (lower < seedKey p) && (seedKey p ≤ upper))

def seedWords (cat : List Nat) (p : List Nat) : List Nat := p.map fun i => cat[i]?.getD 0

lemma enumerateMasks_nonzero {options : List Allowed} {fuel remaining mask : Nat}
    (required : remaining ≠ 0) (listed : mask ∈ enumerateMasks options fuel remaining) : mask ≠ 0 := by
  cases fuel with
  | zero => simp [enumerateMasks, required] at listed
  | succ fuel =>
    simp only [enumerateMasks, beq_iff_eq, if_neg required, List.mem_flatMap] at listed
    obtain ⟨pair, _, next⟩ := listed
    split at next
    · obtain ⟨tail, _, rfl⟩ := List.mem_map.mp next
      have bit : (2 ^ pair.2 ||| tail).testBit pair.2 = true := by
        simp
      intro empty
      simp [empty] at bit
    · simp at next


theorem interval_seed_complete
    (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s)
    (cat : List Nat) (length : cat.length = 344) (nonzero_cat : ∀ a ∈ cat, a ≠ 0)
    (mem_cat : ∀ i, word (s 0 i) ∈ cat)
    (lo : lower < rankWith cat s) (hi : rankWith cat s ≤ upper) :
    ∃ p ∈ intervalSeeds cat,
      ∀ w ∈ seedWords cat p, ∃ i, w = word (s 0 i) := by
  let chosen := fun i : Fin 6 => (word (s 0 i), cat.idxOf (word (s 0 i)))
  let picked := Finset.univ.image chosen
  have found (i : Fin 6) : cat[(chosen i).2]? = some (chosen i).1 :=
    List.getElem?_idxOf (mem_cat i)
  have bound (i : Fin 6) : (chosen i).2 < 344 := by
    rw [← length]
    exact List.idxOf_lt_length_of_mem (mem_cat i)
  have at_key (i : Fin 6) : (rankWith cat s).testBit (chosen i).2 = true :=
    (rankWith_bit cat s _).mpr ⟨bound i, i, rfl⟩
  obtain ⟨top_bit, below⟩ := interval_top lo hi
  have index_le (i : Fin 6) : (chosen i).2 ≤ 288 := by
    by_contra bad
    have exponent : 289 ≤ (chosen i).2 := Nat.succ_le_of_lt (Nat.lt_of_not_ge bad)
    have lt : rankWith cat s < 2^(chosen i).2 := below.trans_le
      (Nat.pow_le_pow_right (Nat.zero_lt_succ 1) exponent)
    exact Bool.false_ne_true ((Nat.testBit_lt_two_pow lt).symm.trans (at_key i))
  obtain ⟨_, i, hit⟩ := (rankWith_bit cat s 288).mp top_bit
  have head_eq : headPair cat = chosen i := by
    change (chosen i).2 = 288 at hit
    apply Prod.ext
    · change cat[288]?.getD 0 = _
      rw [← hit, found i]
      rfl
    · exact hit.symm
  have head_mem : headPair cat ∈ picked := by
    rw [head_eq]
    exact Finset.mem_image_of_mem chosen (Finset.mem_univ i)
  have whole : covers cat.zipIdx (eligibleMask 0) picked :=
    group_cover s valid 0 (fun w => cat.idxOf w) _ (fun k => List.mk_mem_zipIdx_iff_getElem?.mpr (found k))
  have sub := cover_erase _ _ _ whole (headPair cat) head_mem
  have restricted : covers (remainingOptions cat) (eligibleMask 0 ^^^ (headPair cat).1)
      (picked.erase (headPair cat)) := by
    apply narrow_cover sub
    intro a ha
    obtain ⟨ne, hm⟩ := Finset.mem_erase.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm
    have lt : (chosen j).2 < 288 := by
      refine lt_of_le_of_ne (index_le j) ?_
      intro eq
      apply ne
      apply Prod.ext
      · change _ = cat[288]?.getD 0
        rw [← eq, found j]
        rfl
      · exact eq
    exact Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true lt, beq_iff_eq.mpr (disjoint_masks whole head_mem hm (Ne.symm ne))⟩
  have nonzero : ∀ a ∈ remainingOptions cat, a.1 ≠ 0 := by
    intro a ha
    exact nonzero_cat _ (List.fst_mem_of_mem_zipIdx (List.mem_filter.mp ha).1)
  have total : picked.card ≤ 6 := Finset.card_image_le.trans (by simp)
  have room : (picked.erase (headPair cat)).card ≤ 5 := by
    rw [Finset.card_erase_of_mem head_mem]
    omega
  obtain ⟨rest, computed, rest_eq⟩ :=
    enumerateLists_complete 5 _ nonzero _ _ room restricted
  let p := 288 :: rest
  have p_eq : p.toFinset = picked.image Prod.snd := by
    change (288 :: rest).toFinset = _
    rw [List.toFinset_cons, rest_eq]
    change insert (headPair cat).2 ((picked.erase (headPair cat)).image Prod.snd) = _
    rw [← Finset.image_insert, Finset.insert_erase head_mem]
  have on_seed (b : Nat) : b ∈ p ↔ ∃ j, (chosen j).2 = b := by
    rw [← List.mem_toFinset, p_eq]
    simp [picked, Finset.image_image, Finset.mem_image]
  have key_eq : seedKey p = rankWith cat s := by
    apply Nat.eq_of_testBit_eq
    intro b
    apply Bool.eq_iff_iff.mpr
    rw [seedKey_bit, on_seed, rankWith_bit]
    constructor
    · rintro ⟨j, h⟩
      exact ⟨h ▸ bound j, j, h⟩
    · exact And.right
  refine ⟨p, List.mem_filter.mpr ⟨List.mem_map_of_mem computed, ?_⟩, ?_⟩
  · simp [key_eq, lo, hi]
  · intro w hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    obtain ⟨j, hj⟩ := (on_seed b).mp hb
    exact ⟨j, by rw [← hj, found j]; rfl⟩

end Erdos723Interval

namespace Erdos723Interval

open FiniteMaskCoverEnumeration WeightFifteenIndexedSearch WeightFifteenLargeCatalog
open WeightFifteenIndexedSymmetry (IsCover)
open WeightFifteenRankAgreement

def catalog0 : List Nat :=
  [1416755628998656, 2542380657934336, 4583349116993536, 4649044936753152, 73192462373355520, 73324335049211904,
  289360846440628224, 290552648325660672, 2332081879252992, 1272152670076928, 1412881568497664, 1417275320041472,
  4579475056492544, 4583868808036352, 72137861071110144, 73325332555366400, 288306245138382848, 290553645831815168,
  1284797053796352, 2410422082732032, 1425525952217088, 2551150981152768, 4592119440211968, 4662209011515392,
  73201232696573952, 72216201274589184, 289374010515390464, 288318889522102272, 1698213425840128, 2823838454775808,
  5071231632015360, 5075625383559168, 73746521744474112, 72629617646632960, 289919299563290624, 289919777378402304,
  288798001713905664, 291045402407337984, 20275149571883008, 20407022247739392, 20547751146160128, 18305222019383296,
  22522542749122560, 22526936500666368, 22658809176522752, 22659286991634432, 90080928763740160, 90212801439596544,
  306249312831012864, 308496713524445184, 577591205412470784, 578783007297503232, 577868200738291712, 577868678553403392,
  576746902888906752, 578994303582339072, 581034794226286592, 581035272041398272, 648588786489360384, 649644385297760256,
  2333198302314496, 1273269093138432, 1414006447276032, 2544304333520896, 4580599935270912, 4650968612339712,
  72138992291676160, 73194523437563904, 288307376358948864, 289362907504836608, 2341968625532928, 1286433167900672,
  2341977081249792, 2412345758318592, 1427170522038272, 2553074656739328, 4593764010033152, 4664132687101952,
  72147756273106944, 72147762614894592, 73203293760782336, 72218124950175744, 288320540433711104, 289376071579598848,
  1695455788400640, 1699849539944448, 1695464244117504, 2825762130362368, 5073155307601920, 5077549059145728,
  73748644129406976, 72631541322219520, 288799925389492224, 291047326082924544, 18161735483523072, 20409136176955392,
  20277210636091392, 18161750281027584, 18302472837660672, 20549873531092992, 18302479179448320, 18306872930992128,
  22524603813330944, 22528997564874752, 90082989827948544, 90214930166317056, 306251373895221248, 308498774588653568,
  576537720533286912, 578785121226719232, 576537735330791424, 577593266476679168, 576748826564493312, 578996227257925632,
  648590915216080896, 649646446361968640, 1302406151274496, 2428031180210176, 1443143505412096, 2568768534347776,
  4609736993406976, 4680105670475776, 73218850249768960, 72233825169571840, 288336513417084928, 289392044562972672,
  290517532203286528, 290517669591908352, 2358461299949568, 1302925842317312, 2358469755666432, 2428838432735232,
  1443663196454912, 2569567331155968, 4610256684449792, 4680625361518592, 72164248947523584, 72164255289311232,
  73219786435198976, 72234617624592384, 288337033108127744, 289392564254015488, 1724592846536704, 2850217875472384,
  1724601302253568, 2850226331189248, 5102013259972608, 5102292365737984, 72656005523046400, 72656011864834048,
  288828789683650560, 288829062447628288, 20301528992579584, 18190872541659136, 20301537448296448, 18190887339163648,
  18331609895796736, 18331616237584384, 22553324377079808, 22553740871467008, 90107316640153600, 90107322981941248,
  306280100800757760, 306280510953357312, 577621978584711168, 576566857591422976, 576566872388927488, 577622403534815232,
  578747891175129088, 578748028563750912, 576777690858651648, 576777963622629376, 580999678103912448, 580999815492534272,
  648553670366986240, 648553807755608064, 9086948475928576, 9152644295688192, 9293381649825792, 9298054507134976,
  81135265250279424, 81073761251491840, 81073898640113664, 81205633927348224, 297242145318764544, 297242282707386368,
  9083074415427584, 9087468166971392, 9083082871144448, 9153451548213248, 9294180446633984, 9298574198177792,
  81136262756433920, 81206631433502720, 9095718799147008, 9165808370450432, 9095727254863872, 9166095931932672,
  9306545724588032, 9306824830353408, 81082531574710272, 81082668963332096, 297255309393526784, 297255446782148608,
  9574830990950400, 9579224742494208, 9574839446667264, 9579512303976448, 81628019331956736, 81627820622610432,
  297800598441426944, 297801076256538624, 27026142108057600, 27030535859601408, 27162408535457792, 27162886350569472,
  27026150563774464, 27030960809705472, 27303145889595392, 27303623704707072, 99079330449063936, 99079269128339456,
  315252046947155968, 315252524762267648, 585538393585221632, 585538871400333312, 585472504290607104, 585472641679228928,
  585749499616428032, 585749977431539712, 657525684175896576, 657525821564518400, 38289564992798720, 38421437668655104,
  38562175022792704, 36319652237803520, 40536966625755136, 40541776871686144, 108095358982160384, 108227231658016768,
  324263743049433088, 326511076080353280, 36175034481377280, 38422435174809600, 38290509633945600, 36175049278881792,
  36315771835514880, 38563172528947200, 36315778177302528, 36320171928846336, 40537902811185152, 40542296562728960,
  108096288825802752, 108228229164171264, 324264672893075456, 326512073586507776, 38298335316017152, 36187678865096704,
  38298343771734016, 36187693662601216, 36328416219234304, 36328422561021952, 40550130700517376, 40550547194904576,
  108104122963591168, 108104129305378816, 324276907124195328, 324277317276794880, 38843624363917312, 36601095237140480,
  38843632819634176, 36601110034644992, 41095419748417536, 41095897563529216, 108649412011491328, 108649418353278976,
  324822196172095488, 324822673987207168, 612494087223771136, 614741487917203456, 612494102021275648, 614741435052195840,
  612771097347096576, 612771575162208256, 616993221980979200, 616993699796090880, 684547281906565120, 684547214244052992,
  145250056142848000, 145381928818704384, 145522666172841984, 144405768416788480, 148689259660836864, 148627755662049280,
  148627893050671104, 148759628337905664, 432416036084514816, 433471567230402560, 144195454840602624, 145382926324858880,
  144195469638107136, 145251000783994880, 145523663678996480, 144406560871809024, 148690257166991360, 148760625844060160,
  432417033590669312, 433472564736557056, 145258826466066432, 144273795044081664, 145258834921783296, 144273809841586176,
  144414532398219264, 144414538740006912, 148636525985267712, 148636663373889536, 432363296067158016, 432363433455779840,
  145804115513966592, 144687211416125440, 145804123969683456, 144687226213629952, 149182013742514176, 149181815033167872,
  432908585115058176, 432908790166192128, 162138522533232640, 162270395209089024, 162138537330737152, 162270410006593536,
  162411132563226624, 162411138905014272, 166633324859621376, 166633263538896896, 450360101283299328, 450360033620787200,
  720646380258852864, 721701979067252736, 720646395056357376, 721701926202245120, 720857486290059264, 720857691341193216,
  725079678586454016, 725079815975075840]

def lineOptions0 : List Allowed :=
  [
  (136, 24), (264, 25), (520, 26), (2056, 27), (4104, 28), (16392, 29), (80, 30), (272, 31),
  (1040, 32), (2064, 33), (4112, 34), (8208, 35), (96, 36), (160, 37), (544, 38), (1056, 39),
  (8224, 40), (16416, 41), (1088, 42), (2112, 43), (8256, 44), (16448, 45), (640, 46), (2176, 47),
  (4224, 48), (8320, 49), (768, 50), (1280, 51), (4352, 52), (16640, 53), (8704, 54), (16896, 55),
  (5120, 56), (17408, 57), (6144, 58), (10240, 59)]

set_option maxRecDepth 20000 in
lemma lineOptions0_eq : indexOptions 0 = lineOptions0 := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma catalog0_arithmetic : enumerateMasks lineOptions0 60 32760 = catalog0 := by decide +kernel

lemma catalog0_eq : directCatalog 0 = catalog0 := by
  unfold directCatalog
  rw [lineOptions0_eq]
  exact catalog0_arithmetic

def catalog9 : List Nat :=
  [70441796386816, 1125972942274560, 70919611498496, 1126450757386240, 4537704267776, 4675092889600,
  2251938397700096, 2252075786321920, 70439883771904, 1126038692171776, 1125973193918464, 1126041913394176,
  70920920105984, 1126451009030144, 4675344533504, 74769210802688, 2252076037965824, 2322169904235008,
  70454681276416, 1125985827164160, 70935717610496, 1126466863498240, 4690142038016, 74784008307200,
  1130315154194944, 1130452576370944, 2251885784336384, 2251954503812096, 2252091892433920, 2322254461403392,
  281545914978304, 281750966112256, 281754187334656, 1407447902191872, 282026951312384, 1407925717303552,
  285875242009088, 286150052806912, 2533275935441408, 2533550746239232, 4503738211373056, 4503875599994880,
  4503672713119744, 4503741432595456, 4503878821217280, 4574041390186752, 4504150528231424, 4574519205298432,
  72057664976193536, 72057733695669248, 72057870027327488, 72057871084291072, 72127963893596672, 72128033653260544,
  73183495039484416, 73183632461660416, 70952893562880, 1126484039450624, 4569879822336, 4569912852480,
  4707301474304, 1130469752127488, 2251902910742528, 2251971679764480, 2252109068386304, 2322271637159936,
  70472092356608, 1126071974236160, 70953128690688, 1126484291094528, 4707553118208, 74801419387392,
  2251903162386432, 2251971881862144, 2252109320030208, 2322203186299392, 281578090532864, 281578123563008,
  281784248176640, 1407477962838016, 282059126866944, 282059159897088, 1407958999172096, 1407958999367936,
  285907417563648, 285907450593792, 286182261391616, 1411807289868800, 2533377870659840, 2533309217505792,
  2533584028107776, 2533584028303616, 4503702724415488, 4503771493437440, 4503908882059264, 4574071450832896,
  4504183760749568, 4504183810295808, 4574552487166976, 4574552487362816, 4508032051446272, 4508169473622272,
  4508306911594496, 4578400777863680, 72057697151748096, 72057765871223808, 72057697184778240, 72057765904253952,
  72057903292875776, 72057903309391872, 72128065861845248, 72127997175661056, 73183597024053248, 73183528321548800,
  73183665743528960, 73183665743724800, 71472584605696, 1127003730493440, 5499723464704, 75866336018432,
  75868449882112, 1131397481906176, 2252900416897024, 2323269143314432, 71469598511104, 71470671990784,
  71472819733504, 1127003982137344, 5499975108608, 1131397733550080, 2252900668540928, 2323268338058240,
  71485469495296, 1127016615383040, 5514772613120, 5514805643264, 75883482710272, 1131414644918272,
  2252916523009024, 2252916572555264, 2323285249426432, 2323285249622272, 282575596687360, 282575629717504,
  282576703197184, 1408475468992512, 282578817909760, 282578850939904, 1408478690214912, 1408478690410752,
  286974683382016, 1412872441823488, 2534375376814336, 2534374369264640, 4504700230569984, 4575068956987392,
  4504703451792384, 4504703501338624, 4575072178209792, 4575072178405632, 4509097252751360, 4579465929818368,
  72058694657902592, 72058695714866176, 72058694690932736, 72058695764412416, 72129063367999744, 72129062327419904,
  72129064441283584, 72129064441479424, 73184594530207744, 73184593473307648, 17733954584576, 17733987614720,
  17871376236544, 1143633826889728, 18144107184128, 88510719737856, 88512833601536, 1144041865625600,
  2269529505939456, 2269666894561280, 17732041969664, 1143629800411136, 17871627880448, 87965494149632,
  18144358828032, 1144042117269504, 2269667146205184, 2339761012474368, 17746839474176, 17746872504320,
  17884261126144, 1143646711779328, 18159156332544, 18159189362688, 88527866429696, 1144059028637696,
  2269409197425152, 2269546619601152, 2269684057573376, 2339777923842560, 299342074351616, 299344188215296,
  299071492325888, 299071525356032, 299346336153856, 1424971364631040, 299619067101440, 1425516825542912,
  2550867043680768, 2551141854478592, 4521329319612416, 4521466708234240, 4521196126208512, 4521333548384512,
  4521470986356736, 4591564852625920, 4521741636470784, 4592110313537792, 72075188389282304, 72075325811458304,
  72075461135566848, 72075463249430528, 72145555001836032, 72145557115699712, 73201086147723776, 73201223569899776,
  563023002484736, 563023035514880, 563229160128512, 1688922874789888, 563500817596416, 563500850626560,
  563501924106240, 1689400689901568, 567622911541248, 567625025404928, 2814818553839616, 2815025718837248,
  563021089869824, 563226174033920, 563227247513600, 1688918848311296, 563229395256320, 1688854423929344,
  563502126203904, 1689399884645376, 567350416900608, 1693248175342080, 2814751110332928, 2815024913581056,
  563035887374336, 563035920404480, 563242045018112, 1688935759679488, 563516923708416, 563516956738560,
  1689416796013568, 1689416796209408, 567365214405120, 567365247435264, 567640058233088, 1693265086710272,
  2814835667501312, 2814767014347264, 2815041824949248, 2815041825145088, 5066618367512576, 5066825532510208,
  5066622596284672, 5066553943130624, 5066828753732608, 5066828753928448, 5067100411396352, 5067099403846656,
  5070947694543360, 5071222505341184, 72620545099694592, 72620614859358464, 72620545132724736, 72620546206204416,
  72620819943522560, 72620818902942720, 72620821016806400, 72620821017002240, 73746444971999744, 73746512617799936,
  18014471541243904, 18014540277235712, 18014949356355584, 18014950429835264, 18018934028648448, 18018936142512128,
  20266267059568640, 20266336835944448, 18014537291141120, 18014538364620800, 18014471792887808, 18014540512363520,
  18014949607999488, 18014950681479168, 20266267311212544, 20266336030688256, 18014484426133504, 18014553162125312,
  18014965462467584, 18014965478983680, 18018813753164288, 18018951175340288, 20266284222580736, 20266215520076288,
  20266352942056448, 20266352942252288, 18295942239358976, 18295944353222656, 18295946501161216, 18295877814977024,
  18296424316272896, 18296423275693056, 18296425389556736, 18296425389752576, 18300271566389760, 18300273680253440,
  20547674373685760, 20547742019485952, 22518066873241600, 22518136649617408, 22518071151364096, 22518002448859648,
  22518139870839808, 22518139871035648, 22518548966475776, 22518547909575680, 22522396200272384, 22522533622448384,
  90071993638453760, 90072131060629760, 90072061300574208, 90072130020049920, 90072063414437888, 90071994711933440,
  90072132133913600, 90072132134109440]

def lineOptions9 : List Allowed :=
  [
  (10, 8), (34, 9), (66, 10), (130, 11), (1026, 12), (4098, 14), (12, 16), (20, 17),
  (68, 18), (260, 19), (516, 20), (8196, 22), (136, 24), (264, 25), (520, 26), (4104, 28),
  (80, 30), (272, 31), (1040, 32), (4112, 34), (8208, 35), (96, 36), (160, 37), (544, 38),
  (1056, 39), (8224, 40), (1088, 42), (8256, 44), (640, 46), (4224, 48), (8320, 49), (768, 50),
  (1280, 51), (4352, 52), (8704, 54), (5120, 56)]

set_option maxRecDepth 20000 in
lemma lineOptions9_eq : indexOptions 9 = lineOptions9 := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma catalog9_arithmetic : enumerateMasks lineOptions9 60 14334 = catalog9 := by decide +kernel

lemma catalog9_eq : directCatalog 9 = catalog9 := by
  unfold directCatalog
  rw [lineOptions9_eq]
  exact catalog9_arithmetic

def catalog14 : List Nat :=
  [1267204335108096, 2392829364043776, 1407933233528832, 2533558262464512, 4574526721523712, 4644616292827136,
  73183639977885696, 72198608555900928, 289356417796702208, 288301296803414016, 1407959001235456, 2533584030171136,
  4574552489230336, 4644921232359424, 73183665745592320, 72198640764485632, 288301329011998720, 290482347765170176,
  2323285251489792, 2393653994618880, 1408478692278272, 2534382893039616, 4575072180273152, 4645440923402240,
  72129064443346944, 72129070884225024, 72199433186476032, 73325330944917504, 288301848703041536, 290553644221366272,
  1689416798076928, 2815041827012608, 5066828755795968, 5067107927621632, 72620821018869760, 72620827459747840,
  288793605278564352, 288793878009511936, 289919775767953408, 291045400796889088, 20266352944119808, 18155702934077440,
  18296425391620096, 18296431832498176, 22518139872903168, 22659285381185536, 90072132135976960, 90072138576855040,
  306244916395671552, 308496711913996288, 576531687983841280, 578712706737012736, 576742506453565440, 576742779184513024,
  577868676942954496, 578994301971890176, 580964493665796096, 581035270430949376, 648518485928869888, 649644383687311360,
  1267221519155200, 2392846548090880, 1407959007502336, 2533584036438016, 4574552495497216, 4644646361763840,
  73183665751859200, 73324265801253376, 289356447865638912, 289356860182497280, 290482485211432960, 290552579077702144,
  2323276667830272, 1267741210198016, 2323285257756672, 1267754095087616, 1408478698545152, 1408482993508352,
  4575072186540032, 4575076481503232, 72129064449613824, 73184602054723584, 288301846563393536, 289357379873540096,
  1689408214417408, 2815033243353088, 1689416804343808, 2815041833279488, 5066828762062848, 5066833057026048,
  72620821025136640, 73746452496515584, 288793603138916352, 289919230315332096, 20266344360460288, 18155687909539840,
  20266352950386688, 20406952999780864, 18296425397886976, 20547681898201600, 22518139879170048, 22518144174133248,
  22518556490991616, 22658739928564224, 90072132142243840, 90212732191638016, 306244914256023552, 306245326572881920,
  577586793952591872, 576531672959303680, 577586806837481472, 577587219154339840, 578712844183275520, 578782938049544704,
  576742504313917440, 577868131490333184, 580964631112058880, 581034724978328064, 648518623375132672, 648588717241401856,
  2324376175263744, 1268840717631488, 2324384765190144, 1268853602521088, 1409578205978624, 1409582500941824,
  4576171693973504, 4576175988936704, 72130163957047296, 73185701562157056, 288302946070827008, 289358479380973568,
  2324401942970368, 2394770686099456, 2535508174446592, 1409608268648448, 4576201756643328, 4646570499772416,
  72130196165632000, 73185727329863680, 288302978279411712, 290484409349441536, 1691053180600320, 2816957381361664,
  2816965971288064, 1691066065489920, 5068752900071424, 5068757195034624, 72622745163145216, 73748642921586688,
  288795527276924928, 289921425035366400, 18157339316600832, 20409134834925568, 20268414528391168, 18157352201490432,
  18298076804947968, 20549872323272704, 18298074659033088, 18298081099911168, 22520201457174528, 22660934648598528,
  90074193720248320, 90074200161126400, 306246977979942912, 308498773498267648, 576533324366364672, 578785119884689408,
  576533337251254272, 578714768321284096, 576744428451926016, 577870326210367488, 581036919698362368, 580966555250067456,
  648520547513141248, 649646445271582720, 9078126348877824, 9148215920181248, 9078134938804224, 9148228805070848,
  9288953408528384, 9288957703491584, 81065076764706816, 81135170630976000, 297237854583523328, 297307948449792512,
  9078152116584448, 9148520859713536, 9289258348060672, 9288983471198208, 81064965092417536, 81065102532413440,
  81135196398682624, 81205565141811712, 297237747206197248, 297238159523055616, 9078671807627264, 9149040550756352,
  9078684692516864, 9149053435645952, 9289778039103488, 9289782334066688, 81136261548613632, 81065901395281920,
  297309043662393344, 297238679214098432, 9570428383150080, 9570707554975744, 9570716144902144, 9570441268039680,
  81628018124136448, 81627751837073920, 297800800237916160, 297800529655890432, 27021739500257280, 27162885008539648,
  27021752385146880, 27022164702005248, 27303622496886784, 27303077037998592, 99079329241243648, 99219929290637824,
  315252111355023360, 315252523671881728, 585468093293150208, 585538870058303488, 585468106178039808, 585468518494898176,
  585749701412917248, 585749430830891520, 657525820474132480, 657595914340401664, 38280742865747968, 36170086414827520,
  38280751455674368, 38421351505068544, 36310823903174656, 38562080403489280, 40532538384457728, 40532542679420928,
  40532954996279296, 40673138433851904, 108086530647531520, 108227130696925696, 324259312761311232, 324259725078169600,
  38280768633454592, 36170118623412224, 36310856111759360, 38562106171195904, 40532568447127552, 40532980763985920,
  108086562856116224, 108227162905510400, 324259344969895936, 324259757286754304, 36170638314455040, 38422433832779776,
  38281713526245376, 36170651199344640, 36311375802802176, 38563171321126912, 36311373656887296, 36311380097765376,
  40533500455028736, 40674233646452736, 108087492718102528, 108087499158980608, 324260276977797120, 326512072496121856,
  36592298877796352, 36592305318674432, 36592313908600832, 38843563968037376, 41095896355708928, 41095350896820736,
  108649343159894528, 108649349600772608, 324822127419589120, 327073922937913856, 612489691056848896, 614741486575173632,
  612489703941738496, 612490116258596864, 612771028594590208, 615022824112914944, 616993286388846592, 616993698705704960,
  145241234015797248, 144256202593812480, 145241242605723648, 145381842655117824, 144396940082159616, 145522571553538560,
  148619071175264256, 148689165041533440, 432345841257154560, 432415935123423744, 145241259783503872, 144256234802397184,
  144396972290744320, 145522597321245184, 148618959502974976, 148619096942970880, 148689190809240064, 148759559552369152,
  432345873465739264, 432415967332008448, 144186658481258496, 144186664922136576, 144257027224387584, 145382924982829056,
  144186673512062976, 145242204676294656, 144397764712734720, 145523662471176192, 148690255959171072, 148619895805839360,
  432346665887729664, 433472563646171136, 144678415056781312, 144678421497659392, 144678430087585792, 145804055118086656,
  149182012534693888, 149181746247631360, 432908516329521664, 434034414087963136, 162129726173888512, 162129732614766592,
  162129741204692992, 162270341254087168, 162411063711629824, 162411070152507904, 166633323651801088, 166773923701195264,
  720576079966781440, 721701977725222912, 720576232437581824, 720646326303851008, 720857417504522752, 721983315262964224,
  725079814884689920, 725149908750959104]

def lineOptions14 : List Allowed :=
  [
  (34, 9), (130, 11), (1026, 12), (2050, 13), (4098, 14), (16386, 15), (20, 17), (260, 19),
  (516, 20), (2052, 21), (8196, 22), (16388, 23), (272, 31), (1040, 32), (2064, 33), (4112, 34),
  (8208, 35), (160, 37), (544, 38), (1056, 39), (8224, 40), (16416, 41), (640, 46), (2176, 47),
  (4224, 48), (8320, 49), (768, 50), (1280, 51), (4352, 52), (16640, 53), (8704, 54), (16896, 55),
  (5120, 56), (17408, 57), (6144, 58), (10240, 59)]

set_option maxRecDepth 20000 in
lemma lineOptions14_eq : indexOptions 14 = lineOptions14 := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma catalog14_arithmetic : enumerateMasks lineOptions14 60 32694 = catalog14 := by decide +kernel

lemma catalog14_eq : directCatalog 14 = catalog14 := by
  unfold directCatalog
  rw [lineOptions14_eq]
  exact catalog14_arithmetic

def catalog10 : List Nat :=
  [70441901228096, 70919716339776, 4544150896704, 4681539518528, 8937902440512, 9075291062336,
  140810578296896, 141288393408576, 70446330413088, 4544352223248, 4681791176708, 74775657447426,
  8938103767056, 9075542720516, 79169408991234, 79714869837825, 141013716828192, 140810779623440,
  141288594735120, 145410689597441, 70454786129952, 4552807940112, 4690246893572, 74784113164290,
  8950787342368, 9088175964192, 9363053871120, 9363104202756, 140823463198752, 145152790233090,
  281751070965792, 281548133761040, 282025948872720, 286148043735041, 281552361619488, 285881688653826,
  290275440197634, 290820901044225, 72057732693229584, 72057870132183044, 72127963998453762, 72128031644188673,
  72057671372505104, 72057671422836740, 72066527645401089, 72066665034022913, 72198332675522562, 72198400321257473,
  288230514739904544, 288230652128526368, 288230449191321616, 288230449241653252, 288230927006433296, 288230927056764932,
  288234911712673793, 288235049101295617, 70442297589824, 70920112701504, 70927627059264, 4544613318720,
  8938364862528, 79715130015808, 140811040718912, 141017198362688, 141288855830592, 145410949775424,
  70455182491680, 4553204301840, 4690643255300, 74784509526018, 8951249764384, 9363566624772,
  140823925620768, 141030083264544, 141304961171472, 145153252655106, 281751467327520, 281548530122768,
  282026345234448, 286148440096769, 281552824041504, 281758981685280, 282033859592208, 285882151075842,
  290546484641824, 290275902619650, 290821362548752, 290821363466241, 72057733089591312, 72057870528544772,
  72127964394815490, 72128032040550401, 72057740603949072, 72057671885258756, 72057878042902532, 72127971909173250,
  72066528106905616, 72066528107823105, 72066665545859076, 72136759412129794, 72198400782762000, 72198333137944578,
  72198400783679489, 72198606941323265, 288230515202326560, 288300814152368160, 288230518422765584, 288230449704075268,
  288230655861719044, 288300749727989762, 288230927519186948, 288301295188836353, 288234912174178320, 288234912175095809,
  288235049613131780, 288305143479402498, 72572196880448, 76965948293184, 6605677527104, 76974403944512,
  10999429070912, 81368155488320, 142940873949248, 147334625361984, 72569111707680, 76966084476929,
  72576626065440, 6605929185284, 81364129021984, 10999680729092, 142937854836768, 142941075275792,
  147334826688528, 147334827606017, 6614268510224, 6614318841860, 72585081782304, 6614384902148,
  11012313972768, 81381040390176, 142953758851104, 147351738056720, 283675142914080, 288072115683329,
  283675208974368, 283678429413392, 288072180826128, 288072181743617, 283682657271840, 288080636477456,
  292470160228384, 292474388021264, 72059794153799696, 72059794204131332, 72059794270191620, 72130161939841025,
  72059801668157456, 72059801718489092, 72068589171114000, 72068589172031489, 72068589221445636, 72138957898448897,
  72200531623346192, 72200530616909825, 288232576266534944, 288302944992952352, 288232579486973968, 288232579537305604,
  288236973238386704, 288236973239304193, 288236973288718340, 288307341965721601, 35326175215680, 35463563837504,
  35326241275968, 106103006429248, 35742735663168, 106111462080576, 176201033384000, 176471683498048,
  35326376542224, 35463815495684, 105557681766402, 106103142612993, 35330670460960, 35742987321348,
  176197006917664, 175926424895490, 176471884824592, 176471885742081, 35339060117536, 35476448739360,
  35751326646288, 35751376977924, 35339126177824, 35751443038212, 176213918285856, 176488796192784,
  316663712972802, 317209173819393, 316934361055264, 316663779033090, 317209238962192, 317209239879681,
  316942816706592, 317217694613520, 72092915918176257, 72093053306798081, 72092915983319056, 72092915984236545,
  72093053422272516, 72163147288543234, 72092924438970384, 72092787017777154, 72093061877923844, 72163155744194562,
  72233515965612034, 72233790776344577, 288265698029994016, 288265835418615840, 288265702257786896, 288265564836593666,
  288265839696740356, 288335933563011074, 288266110296522768, 288266110297440257, 288266110346854404, 288336479023857665,
  36028870052282432, 36029347867394112, 36028938887364672, 36033332638777408, 36029355381751872, 36033341094428736,
  36037734845972544, 36038142884708416, 36169607521828928, 36170085336940608, 36028935802191904, 36028870303940612,
  36029348119052292, 36033332774961153, 36028943316549664, 36029355633410052, 36037730819506208, 36038143136366596,
  36169603495362592, 36169539070984194, 36170084531830785, 36173932822396930, 36028882937184288, 36033212264218626,
  36028951772266528, 36029364089126916, 36037747730874400, 36038160047734788, 36169620406730784, 36173949733765122,
  36310340849500192, 36310276425121794, 36310821885968385, 36314670176534530, 36310349305151520, 36314678632185858,
  36319072383729666, 36319617844576257, 108086392149508098, 108086459795243009, 108086459910717444, 108086528630325249,
  108086468366368772, 108086399663865858, 108095187166822402, 108095324588933121, 108227129619054594, 108227197264789505,
  324259241907060768, 324259311683436576, 324259246185185284, 324259177482682370, 324259724000296964, 324259722943528961,
  324263571234095106, 324263708656205825, 144115326657757248, 144115464046379072, 144115326723817536, 144185625673859136,
  144115265403093056, 144115334172115008, 144115471560736832, 144185634129510464, 144124121675071552, 144124259063693376,
  144255994350927936, 144256201515925568, 144115326859083792, 144115464298037252, 144185558164307970, 144185625810042881,
  144115334373441552, 144115265654751236, 144115471812395012, 144185565678665730, 144124121876398096, 144124121877315585,
  144124259315351556, 144194353181622274, 144255994552254480, 144255926907437058, 144255994553171969, 144256200710815745,
  144115273994076176, 144115274044407812, 144115342829158416, 144115274110468100, 144115480268111876, 144185574134382594,
  144124138787766288, 144124001366573058, 144124276226719748, 144194370092990466, 144256011463622672, 144255942811451394,
  144396664195514370, 144396731841249281, 144396731906392080, 144396664261574658, 144396731907309569, 144396938064953345,
  144396740362043408, 144396671709872130, 144405459212828674, 144405734023561217, 432345632963952656, 432345702740328464,
  432345565319135234, 432345632964870145, 432345633014284292, 432345701733892097, 432345840179281924, 432345839122513921,
  432415934045552642, 432416001691287553]

def lineOptions10 : List Allowed :=
  [
  (17, 0), (33, 1), (129, 2), (513, 4), (1025, 5), (4097, 6), (12, 16), (20, 17),
  (68, 18), (516, 20), (2052, 21), (16388, 23), (136, 24), (520, 26), (2056, 27), (4104, 28),
  (16392, 29), (80, 30), (1040, 32), (2064, 33), (4112, 34), (96, 36), (160, 37), (544, 38),
  (1056, 39), (16416, 41), (1088, 42), (2112, 43), (16448, 45), (640, 46), (2176, 47), (4224, 48),
  (16896, 55), (5120, 56), (17408, 57), (6144, 58)]

set_option maxRecDepth 20000 in
lemma lineOptions10_eq : indexOptions 10 = lineOptions10 := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma catalog10_arithmetic : enumerateMasks lineOptions10 60 24317 = catalog10 := by decide +kernel

lemma catalog10_eq : directCatalog 10 = catalog10 := by
  unfold directCatalog
  rw [lineOptions10_eq]
  exact catalog10_arithmetic

def catalog13 : List Nat :=
  [2260733622485120, 2392606298341504, 2533343652479104, 290820867489920, 4508135255441536, 4512945501372544,
  72066527611846784, 72198400287703168, 288234911679119488, 290482244710039680, 2261695443501120, 146235088437312,
  2261695695159300, 146235323318280, 286972677455880, 291370623303712, 4509097328115716, 4513495257186336,
  72067489667743752, 72067489684520964, 288235873735016456, 288235873751793668, 2269529581289536, 158879472156736,
  158879707037704, 2410129764909058, 299617061175304, 2550867119046658, 4521329394974752, 4521741711835140,
  72075323805532168, 72215923754270722, 288248105818652704, 288248518118735880, 288248518135513092, 290499768176607234,
  2814818629189696, 572295844200512, 572296079081480, 2823546136952834, 5066618442874912, 5070947769909250,
  72620612853432328, 72629340126314498, 288793394866552864, 288797724193587202, 576465287830831168, 578712620861751360,
  576465288065712136, 578712621113409540, 576742296041553952, 576746625368588290, 580964420675436576, 580968750002470914,
  648518415085993992, 648518415102771204, 2533344048840832, 290821362942080, 4508135651803264, 4644887408672896,
  72066528107298944, 72198400783155328, 288234912174571648, 290482313941483648, 2260733886726208, 2392606562582592,
  290821366611976, 2542071424483330, 4512533700411424, 4512946017271812, 4644406376267808, 4648735703302146,
  72066528110968840, 72198400786825224, 288234912178241544, 290482245225938948, 146235583889472, 2393637350801472,
  286973073817608, 291371118755872, 4509097724477444, 4645437164486688, 72067490179973124, 72199431575044104,
  288235874247245828, 290483276014157828, 2269529977651264, 158879967608896, 299617457537032, 2550867515408386,
  4521329791336480, 4521742108196868, 72075324201893896, 72215924249722882, 288248106314104864, 288248518630965252,
  2814819025551424, 572296339652672, 5066618839236640, 5070948166270978, 72620613249794056, 72629340621766658,
  288793395362005024, 288793876398080008, 288797724689039362, 291045126455951362, 576465288326283328, 578712690093195328,
  576742296537006112, 576742777573081096, 576746625864040450, 578994027630952450, 580964489906880544, 580964902223740932,
  648518484317437960, 648518415598223364, 147334827081856, 2394736593993856, 288072082129024, 288072181219456,
  2535473948131456, 2544269906739328, 4510196716011648, 4650934185558144, 72068589171507328, 72200530583355520,
  288236973238780032, 290484375005692032, 2262794950934592, 147334595870784, 2262795202592772, 147334830751752,
  288072184889352, 292470130737184, 4510196835549188, 4514594764619808, 72068589175177224, 72068589191954436,
  288236973242449928, 288236973259227140, 2271591041859648, 2412328511406144, 2271591293517828, 160528966615072,
  301266221662240, 301266320752672, 4523390855544864, 4664128325091360, 72077385266102280, 72077385282879492,
  72077385381969924, 72218122735648776, 288250167378313248, 290501967174762500, 569547058839616, 569547157930048,
  2816948924842048, 2825744883449920, 569547293720584, 573945338658848, 5068748738527264, 5077544697135136,
  72622743149084680, 72631539107692552, 288795525162205216, 288799923174965256, 576467349390491712, 578714751157403712,
  576467349642149892, 578714751409061892, 576744426337206304, 576748824349966344, 580966550971088928, 580970949000626180,
  648520545381646344, 648520545398423556, 2287121895260288, 176471885217920, 317209140265088, 317209239355520,
  4539333774147712, 4680071243694208, 72092915884621952, 72092915983712384, 288266110296916096, 290517497776504960,
  2287121763139648, 176471654006848, 176471888887816, 2427721946759170, 317209243025416, 2568459300896770,
  4538921576824864, 4539333893685252, 72092915987382280, 72233515936120834, 288265698000502816, 288266110300585992,
  288266110317363204, 290517360358457346, 2288083716276288, 2428821185822784, 2288083967934468, 177021641031712,
  317758896078880, 317758995169312, 4539883529961504, 4680620999508000, 72093877940518920, 72093877957296132,
  72093878056386564, 72234615410065416, 288266660052729888, 290518459849179140, 598684116975680, 598684216066112,
  598684351856648, 2849934409728002, 72655728399089666, 72655728498180098, 288829060233101320, 291080310290972674,
  576496486448627776, 578747873928216640, 576496074383425568, 576496486700285956, 576777961408102408, 579029211465973762,
  580999673741901856, 581000086058762244, 648553668152459272, 648553530730741762, 9011735010738304, 9148486767607936,
  9289224121745536, 9298020080353408, 81064862031020160, 81064930866102400, 81073726824710272, 81205599500566656,
  297238125179306112, 297242110891982976, 9011734878617664, 9016545124548672, 9016133059346464, 9016545376206852,
  9148005735202848, 9152335062237186, 9288743089340448, 9293072416374786, 81064862150557700, 81073589406662658,
  297237644146901024, 297241973473935362, 9012696831754304, 9153434301300800, 9012697083412484, 9149036523421728,
  9289773877559328, 9298569836167200, 81065892938776580, 81074688897384452, 297238674935119904, 297243072964657156,
  9025341215473728, 9166078685020224, 9024929150271520, 9025341467131908, 81082385497587714, 81223122967134210,
  297255305031516192, 297255717348376580, 9570699098456128, 9579495057064000, 9570218198171680, 9574547525206018,
  81627743380570114, 81636539339177986, 297800594079416352, 297804923406450690, 585468501331017792, 585472487043694656,
  585468089265815584, 585468501582675972, 585749495254417440, 585753824581451778, 657525614315634692, 657525545613131778,
  144124121876791424, 144255994552647808, 144396731807694976, 144396731906785408, 148618856441577600, 148618925276659840,
  148627721235267712, 148759593911124096, 432345632964345984, 432345701700337792, 144124121645580352, 144255994321436736,
  144124121880461320, 144255994556317704, 144396731910455304, 144405459183337474, 148618856561115140, 148627583817220098,
  432345632968015880, 432345632984793092, 144125083697807424, 144257025109655616, 144125083949465604, 144257025344536584,
  144397762698674184, 144406558657282056, 148619887349334020, 148628683307941892, 432346663756234760, 432346663773011972,
  144132917736505408, 144132917835595840, 144132917971386376, 144273518019215362, 144414255274262530, 144414255373352962,
  148636379908145154, 148777117377691650, 432363293852631048, 432363156430913538, 144678206784405568, 144678206883496000,
  144678207019286536, 144686934391259138, 149181737791127554, 149190533749735426, 432908582900531208, 432908514214805506,
  720576009116057664, 720576077852049472, 720576078086930440, 720576009367715844, 720857484075532296, 720857415389806594,
  725079608726192132, 725079540023689218]

def lineOptions13 : List Allowed :=
  [
  (33, 1), (129, 2), (257, 3), (1025, 5), (4097, 6), (8193, 7), (12, 16), (68, 18),
  (260, 19), (2052, 21), (8196, 22), (16388, 23), (136, 24), (264, 25), (2056, 27), (4104, 28),
  (16392, 29), (96, 36), (160, 37), (1056, 39), (8224, 40), (16416, 41), (1088, 42), (2112, 43),
  (8256, 44), (16448, 45), (2176, 47), (4224, 48), (8320, 49), (1280, 51), (4352, 52), (16640, 53),
  (5120, 56), (17408, 57), (6144, 58), (10240, 59)]

set_option maxRecDepth 20000 in
lemma lineOptions13_eq : indexOptions 13 = lineOptions13 := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma catalog13_arithmetic : enumerateMasks lineOptions13 60 32237 = catalog13 := by decide +kernel

lemma catalog13_eq : directCatalog 13 = catalog13 := by
  unfold directCatalog
  rw [lineOptions13_eq]
  exact catalog13_arithmetic

def catalog11 : List Nat :=
  [1125977484722304, 9073386881152, 1125985940439168, 9088184385664, 4503875713269888, 4503677003923584,
  288230447085813888, 288230652136947840, 1126003120308288, 9105364254784, 9105599135752, 1134730628071426,
  4503702840836112, 4512430147272706, 288230479264514064, 288230479298068488, 1127000626462784, 9897819275328,
  9898020601872, 1135795779960833, 9912818106384, 9912851660808, 4504700346990608, 4513495299162113,
  288231476770668560, 288231476804222984, 17869345685568, 17875687473216, 17875922354184, 1143500951289858,
  17884378071048, 1143509407006722, 4521466825572353, 4521200470491138, 288247970552381442, 288248243249250305,
  18014469510692928, 18014475852480576, 18014476087361544, 18023197018456066, 18014484543078408, 18023211815960578,
  22517999344844802, 22518066990579713, 306244775768522754, 306244843414257665, 576460823237525568, 576461028288659520,
  576460823438852112, 576461028523540488, 577586653552476162, 577586721198211073, 576460838236356624, 576460838269911048,
  580964353071677442, 580964420717412353, 1125977753141376, 9073655300224, 1125986343067776, 1134713716605568,
  4503876115898496, 4503883632084096, 288230653713974400, 289356277669167744, 1126003522936896, 1134730896474688,
  9105867554824, 1134730896490498, 4503703243464720, 4512430617002512, 288230685926229000, 289356310955164674,
  1127001029091392, 1127008545276992, 9898289020944, 1135796048379905, 4504700749619216, 4504708265804816,
  288231478347695120, 289357376107054081, 17869748314176, 1143501219693120, 17876190773256, 1143501219708930,
  17884780699656, 1143509809635330, 4521467228200961, 4521200940220944, 288247971022111248, 289373868781470209,
  18014469913321536, 18023197286859328, 18014476355780616, 18023197286875138, 18014484945707016, 18023212319244808,
  22517999747473410, 22518067393208321, 22518007263659010, 22526794766746113, 306244776271806984, 306244777345549314,
  576461029865686080, 577586653820879424, 576460823707271184, 576461028791959560, 577586653820895234, 577586721466630145,
  576461044898071560, 577586669927007234, 580964353541407248, 580964627345572865, 1128100138074240, 10997330886784,
  1128100272283776, 1128107788469376, 1128116244186240, 1136912202989952, 4505799791485056, 4505807307670656,
  288232577389560960, 289358476155552128, 1128133424055360, 1136929382859072, 11029509586960, 11029543141384,
  4505833144583184, 4514629103386896, 288232609568261136, 288232609601815560, 19793423900736, 1145699706077504,
  19793491017744, 1145691250376705, 19799832805392, 19799866359816, 19793625227280, 1145691384586241,
  19808422731792, 19808456286216, 4523390903787521, 4523399426605328, 288250169508495632, 289376067267854593,
  18016598640042048, 18016599814440000, 18016606156227648, 18025395773243712, 18016598740713480, 18025393659330561,
  18016598874923016, 18016606391108616, 18016614846825480, 18025410805629192, 22520197294326785, 22528993253130497,
  306246974758191368, 306246973718004737, 576462953541272640, 577588852307263808, 576462952433991696, 576462952467546120,
  576462953742599184, 577588851501958145, 576462968540103696, 576462968573658120, 580966552027791632, 580966551021159425,
  35461531713664, 35467873501312, 35461665923200, 1161093137302144, 35476463427712, 1161101593019008,
  4538792656503424, 4539067467301248, 288265562738393728, 288265837549191552, 35493643296832, 1161118772888128,
  35493743968264, 1161118772903938, 35493878177800, 1161118907113474, 4538818426314754, 4538818493415952,
  288265594917093904, 288265594950648328, 288265869761446152, 289391494790381826, 36286098317376, 1162192380494144,
  36286165434384, 1162183924793345, 36292507222032, 36292540776456, 36286299643920, 1162184059002881,
  36301097148432, 36301130702856, 4539883578204161, 4539892101021968, 288266662182912272, 289392559942271233,
  18049585163272768, 18049591505060416, 18049585163288578, 18049591505076226, 18049585297498114, 18049591739941384,
  18049600095002626, 18049600195658248, 22553182643159553, 22553191098876162, 306279959066837505, 306279961180766466,
  576495938890105408, 576496213700903232, 576495938890121218, 576496211586990081, 576495939091431952, 577621836850790913,
  576495953888936464, 576495953922490888, 576496228733288712, 577621853762224386, 580999536369992193, 580999811180790017,
  9007475340624000, 9007276631277696, 9007475474833536, 9007482991019136, 9007285221204096, 9007491446736000,
  9016012594741888, 9016287405539712, 297237576547304064, 297237851358101888, 9007302401073216, 9007508626605120,
  9016029774611008, 9016304585408832, 9007302468190224, 9016029774626818, 9007302602399760, 9016029975937552,
  297237678485668112, 297237609833300994, 9008299907227712, 9008307423413312, 9008299974344720, 9017094926516225,
  9008300108554256, 9008307624739856, 9008316080456720, 9017112039260432, 297238675991822608, 297238674985190401,
  9024800097829440, 9025074908627264, 9025066452926465, 9024800097845250, 9025066587136001, 9024800299155984,
  9024808687771650, 9024808754872848, 297255167659606529, 297255442470404353, 27021598972183104, 27021675073634624,
  27021598972198914, 27021666617933825, 27021599106408450, 27021666752143361, 27021606622594050, 27030394125681153,
  27021615078310914, 27030411037114626, 315251974989676802, 315252042635411713, 585467952699015744, 585468227509813568,
  585467952699031554, 585468020344766465, 585467952900342288, 585468226704507905, 585468037457510672, 585467968805143554,
  36028868020158592, 36028874361946240, 36028868154368128, 36037595527905920, 36028882951872640, 36037610325410432,
  40532397854294656, 40532473955746176, 324259174277972608, 324259244037636480, 36028900131741760, 36037627505279552,
  36028900232413192, 36037627505295362, 36028900366622728, 36037627740160520, 40532431140291586, 40541227099095298,
  324259276249891080, 324259207563969538, 36029897637896256, 36029898812294208, 36029905154081856, 36038694771097920,
  36029897738567688, 36038692657184769, 36029897872777224, 36029905388962824, 36029913844679688, 36038709803483400,
  40533496292180993, 40542292250984705, 324260273756045576, 324260272715858945, 36046391486710336, 36046397828497984,
  36046391486726146, 36046397828513794, 36046391620935682, 36046398063378952, 36046406418440194, 36046406519095816,
  40549988966597121, 40549997422313730, 324276765390275073, 324276767504204034, 612489550429684288, 612489620189348160,
  612489550429700098, 612489618075435009, 612489550664565256, 612489551738307586, 612489635221733640, 612489566535812098,
  616993150023500034, 616993217669234945]

def lineOptions11 : List Allowed :=
  [
  (17, 0), (33, 1), (257, 3), (513, 4), (4097, 6), (8193, 7), (10, 8), (34, 9),
  (66, 10), (2050, 13), (4098, 14), (16386, 15), (264, 25), (520, 26), (2056, 27), (4104, 28),
  (16392, 29), (80, 30), (272, 31), (2064, 33), (4112, 34), (8208, 35), (96, 36), (544, 38),
  (8224, 40), (16416, 41), (2112, 43), (8256, 44), (16448, 45), (768, 50), (4352, 52), (16640, 53),
  (8704, 54), (16896, 55), (6144, 58), (10240, 59)]

set_option maxRecDepth 20000 in
lemma lineOptions11_eq : indexOptions 11 = lineOptions11 := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma catalog11_arithmetic : enumerateMasks lineOptions11 60 31611 = catalog11 := by decide +kernel

lemma catalog11_eq : directCatalog 11 = catalog11 := by
  unfold directCatalog
  rw [lineOptions11_eq]
  exact catalog11_arithmetic

def catalog12 : List Nat :=
  [74769072423040, 2322169765855360, 74775414210688, 1130306560098432, 79169165754496, 1134700311642240,
  145137749491840, 2392538442924160, 74801284677640, 1130332447342596, 79199230525472, 1134730376413216,
  2260630283255824, 2260630333587460, 145169928192016, 145169961746440, 87963211956256, 87965359439880,
  1143496522104836, 2339760878157825, 87969553743904, 1143500699631648, 2269400606474256, 2269400656805892,
  158331889025056, 158334002954256, 158334036508680, 2410129555226625, 1688851068256288, 567350281666576,
  1693248041025537, 2814750975098896, 567356623454224, 567356657008648, 571748261068832, 571750374998032,
  571750408552456, 2823545927270401, 18018798837727236, 20266199531159556, 18018805162737672, 18018805179514884,
  18023196766797856, 18023198914281480, 18023198931058692, 20274994432999425, 18155137105166368, 18159534077935617,
  576531122154930208, 577586653300817952, 576465152514228240, 576465152564559876, 576535519127699457, 577591050273587201,
  578712553207660560, 578712553257992196, 74769475051648, 2322170168483968, 1130307080161408, 2322177684669568,
  79167521558656, 1134700831705216, 1266639005814912, 1266642227037312, 74801687306248, 1130332849971204,
  1134730896476192, 79199733813256, 1134730896478212, 2260630803318800, 1266672291808288, 2392572198650896,
  87963614584864, 87965762068488, 1143496924733444, 2339761280786433, 1143501219694624, 87970057031688,
  1143501219696644, 2269401126537232, 158332358758416, 1284230118117377, 1688851470884896, 567350684295184,
  1693248443654145, 2814751377727504, 1688858987070496, 2814758893913104, 571748730802192, 1697646490161153,
  18018799240355844, 20266199933788164, 18018805682800648, 20266207449973764, 18023197286860832, 18023197286862852,
  18023199434344456, 20274994953062401, 18155138682192928, 18155137608454152, 18155140829676552, 20406936348394497,
  576531123731956768, 577586653820880928, 576531122658217992, 577586653820882948, 576531125879440392, 577586657042105348,
  576465153034291216, 577591050793650177, 578712553727723536, 578782921398158337, 105557444796544, 1161088590684288,
  105555397972096, 1161088708118656, 105561739759744, 1161092885647488, 2286992842819712, 2357361519886720,
  175924075040896, 1301826062254464, 105587509567520, 1161118655455264, 2287018562297872, 2287018612629508,
  1161118772889632, 105587610226696, 1161118772891652, 2287018679732240, 1301856127025440, 175956253741072,
  175956287295496, 2427756033868048, 598136540110880, 598138654040080, 598138687594504, 2849934206312449,
  598136607215632, 1724034366574593, 1724042822287648, 598142949003280, 598142982557704, 2849942729130256,
  18049585045839904, 18049587193323528, 18049587210100740, 20301382712041473, 18049585163274272, 18049585163276292,
  18049587310757896, 20301382829475841, 18049591505061920, 18049591488286728, 18049591505063940, 20301391285190916,
  18190322517410080, 18190320403484673, 18190324664893704, 20442120183611649, 576495938890106912, 576566307567173920,
  576495938839777296, 576495938890108932, 576566305453248513, 577621836599136257, 576495941004036112, 576495941037590536,
  576566309714657544, 577621840877322500, 578747736556308481, 578818105233375489, 9077569206882432, 9077572428104832,
  9011605958297728, 9081974635364736, 9015999709841536, 9086368386908544, 9147937883951232, 9147941105173632,
  9011631677775888, 9011631728107524, 9077602492875808, 9011631795210256, 9016029774612512, 9086398451679520,
  9016029724282896, 9016029774614532, 9147971169944608, 9152369149346064, 9024795752538128, 9024795802869764,
  9095160319184897, 9024795869972496, 9024800097830944, 9095168774897952, 9024800047501328, 9024800097832964,
  9165528996253697, 9165533224108304, 9570150349021216, 9574547321790465, 9570150416125968, 9570153637348368,
  9570157865206816, 9574555844608272, 9578945368297473, 9578949596152080, 27021598854750240, 27025995827519489,
  27021598972184608, 27021598972186628, 27021602193409028, 27025995944953857, 27021606370935840, 27026004400668932,
  27030393874026497, 27030398152212740, 27162336326320416, 27166733299089665, 585467952699017248, 585538321376084256,
  585467952648687632, 585467952699019268, 585467955869910032, 585467955920241668, 585472349671786497, 585542718348853505,
  36033197229744256, 38280597923176576, 36033197347178624, 38280598040610944, 36033203688966272, 38280605439362176,
  36037595276251264, 36037597440510080, 36169535614619776, 36169538835842176, 36173934701314432, 38421335394746752,
  36033229441998856, 36033229458776068, 36033229559433224, 38280631326606340, 36037627505281056, 36037627488505864,
  36037627505283076, 38289427285410052, 36169568900613152, 36173966913569032, 36046391369277472, 36046393516761096,
  36046393533538308, 38298189035479041, 36046391486711840, 36046391486713860, 36046393634195464, 38298189152913409,
  36046397828499488, 36046397811724296, 36046397828501508, 38298197608628484, 36187128840847648, 36187126726922241,
  36187130988331272, 38438926507049217, 36591748079689760, 36596145052459009, 36591749254087712, 36591748180348936,
  36591751401571336, 38843546920289281, 36591755595875360, 36596153608831240, 36600545212891424, 36600543098966017,
  36600547360375048, 38852342879092993, 612489550429685792, 612489551486649376, 612489550412910600, 612489550429687812,
  612489553634133000, 612489553650910212, 612493947402455041, 612493949516382468, 614741350209814788, 614741349152850945,
  144185557927338112, 145241089073225856, 144185559101736064, 145241089190660224, 144185565443523712, 145241096589411456,
  144123986383472768, 144194355060539776, 144255927778804864, 145381826544796032, 144185591313990664, 145241122476655620,
  144124018562172944, 144124018595727368, 144194387272794376, 145249918435459332, 144255959957505040, 144255959991059464,
  144132782426169360, 144132782476500996, 144203149039640577, 145258680185528321, 144132782543603728, 145258680302962689,
  144132788885391376, 144132788918945800, 144203157596012808, 145258688758677764, 144273519897739536, 145399417657098497,
  144678139136581648, 144678139170136072, 144678140310979600, 145804038070338561, 144678146652767248, 144678146686321672,
  144686936269783312, 145812834029142273, 162129587675865096, 162129587692642308, 162129587793299464, 162129588867040260,
  162129595192050696, 162129595208827908, 162138382711916545, 162138384825843972, 162270325147435272, 162270324107248641,
  720575941486577680, 720575942543541264, 720575941520132104, 720575942593872900, 720646310197199112, 720646309157012481,
  721701841359864068, 721701840302900225]

def lineOptions12 : List Allowed :=
  [
  (17, 0), (129, 2), (257, 3), (513, 4), (1025, 5), (8193, 7), (10, 8), (66, 10),
  (130, 11), (1026, 12), (2050, 13), (16386, 15), (136, 24), (264, 25), (520, 26), (2056, 27),
  (16392, 29), (80, 30), (272, 31), (1040, 32), (2064, 33), (8208, 35), (1088, 42), (2112, 43),
  (8256, 44), (16448, 45), (640, 46), (2176, 47), (8320, 49), (768, 50), (1280, 51), (16640, 53),
  (8704, 54), (16896, 55), (17408, 57), (10240, 59)]

set_option maxRecDepth 20000 in
lemma lineOptions12_eq : indexOptions 12 = lineOptions12 := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma catalog12_arithmetic : enumerateMasks lineOptions12 60 28635 = catalog12 := by decide +kernel

lemma catalog12_eq : directCatalog 12 = catalog12 := by
  unfold directCatalog
  rw [lineOptions12_eq]
  exact catalog12_arithmetic

def checkBatch (g h : Fin 15) (cg ch : List Nat) (batch : List (List Nat × List Nat)) : Bool :=
  batch.all fun (p, trace) =>
    let seed := seedWords catalog0 p
    replay 13 ⟨eligibleMask g, allowedOptions cg seed⟩
      ⟨eligibleMask h, allowedOptions ch seed⟩ trace == some []

lemma checked_survivor {before after : List (List Nat)} {g h : Fin 15} {cg ch : List Nat}
    {batches : List (List (List Nat × List Nat))}
    (coverage : before.filter (fun p => !after.contains p) = batches.flatten.map Prod.fst)
    (checked : ∀ batch ∈ batches, checkBatch g h cg ch batch = true)
    {p : List Nat} (in_before : p ∈ before)
    (joint : Joint ⟨eligibleMask g, allowedOptions cg (seedWords catalog0 p)⟩
      ⟨eligibleMask h, allowedOptions ch (seedWords catalog0 p)⟩) : p ∈ after := by
  by_contra missing
  have rejected : (!after.contains p) = true := by
    cases present : after.contains p
    · rfl
    · exact (missing (List.contains_iff_mem.mp present)).elim
  have eliminated : p ∈ before.filter (fun q => !after.contains q) :=
    List.mem_filter.mpr ⟨in_before, rejected⟩
  rw [coverage] at eliminated
  obtain ⟨⟨_, trace⟩, entry, rfl⟩ := List.mem_map.mp eliminated
  obtain ⟨batch, present, in_batch⟩ := List.mem_flatten.mp entry
  have replayed := List.all_eq_true.mp (checked batch present) _ in_batch
  exact replay_refutes (beq_iff_eq.mp replayed) joint

def batch1_0 : List (List Nat × List Nat) :=
  [
  ([288, 51, 106, 193, 261, 146], [115, 33, 14, 19, 91, 37, 8, 72, 9, 69, 23, 20, 12, 98, 38, 9, 12, 12, 56, 17, 22, 34, 17, 34, 15, 9, 19, 14, 13, 9, 12, 112, 97, 54, 69, 33, 14, 9, 15, 102, 49, 34, 109, 14, 50, 17, 15, 11, 13, 12, 14, 77, 19, 52, 15, 35, 23, 13, 69, 31, 51, 9, 22, 56, 32, 11, 13, 14, 86, 14, 71, 19, 20, 49, 9, 20]),
  ([288, 51, 106, 208, 261, 135], [77, 11, 19, 12, 13, 14, 86, 12, 32, 49, 20, 34, 22, 32, 55, 34, 15, 11, 49, 31, 9, 34, 32, 11, 56, 97, 54, 38, 15, 38, 100, 22, 9, 12, 74, 11, 13, 19, 94, 12, 13, 14, 35, 15, 48, 9, 11, 15, 13, 14, 86, 14, 85, 56, 11, 31, 20, 22, 11, 15, 14, 14, 11, 12, 20, 48, 39, 23]),
  ([288, 51, 150, 193, 260, 102], [69, 13, 22, 19, 59, 21, 11, 15, 69, 32, 35, 14, 22, 38, 33, 33, 34, 34, 15, 51, 31, 11, 33, 12, 57, 19, 92, 46, 54, 71, 31, 8, 36, 34, 46, 54, 71, 31, 35, 31, 12, 8, 94, 40, 9, 12, 16, 25, 9, 46, 20, 38, 10, 94, 19, 51, 34, 41, 11, 14, 12, 69, 18, 12, 37, 31, 13, 11, 15, 69, 17, 15, 11, 15, 17, 19, 14, 11, 11, 15, 12, 13, 69, 25, 17, 12, 20, 49, 53, 17, 13, 15, 79, 8, 15, 13, 23, 11, 23, 11, 35, 11, 12, 13, 79, 15, 12]),
  ([288, 51, 150, 193, 263, 98], [109, 33, 47, 11, 31, 17, 9, 11, 102, 11, 56, 114, 34, 49, 32, 34, 14, 22, 13, 14, 11, 13, 15, 78, 15, 11, 13, 98, 15, 12, 13, 14, 106, 56, 22, 9, 91, 100, 46, 94, 49, 12, 9, 8, 12, 28, 37, 11, 12, 9, 15, 12, 14, 114, 46, 12, 80, 49, 8, 49, 44, 49, 9, 11, 14, 12, 10, 14, 91, 91, 49, 56, 117, 12, 32])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_0_ok : checkBatch 9 14 catalog9 catalog14 batch1_0 = true := by decide +kernel

def batch1_1 : List (List Nat × List Nat) :=
  [
  ([288, 51, 267, 105, 190, 146], [79, 17, 9, 47, 9, 11, 14, 13, 69, 10, 11, 11, 50, 48, 9, 13, 12, 94, 13, 109, 55, 13, 12, 14, 88, 52, 21, 92, 11, 17, 25, 10, 37, 9, 117, 59, 13, 11, 12, 84, 109, 21, 11, 17, 8, 35, 97, 9, 17, 11, 94, 17, 20, 22, 13, 58, 11, 52, 15, 12, 98, 17, 17, 15, 12, 52, 14, 12, 77, 15, 17, 20, 11, 31, 56, 57, 57, 31, 13, 12, 71]),
  ([288, 51, 267, 193, 100, 146], [71, 98, 100, 32, 37, 52, 11, 32, 10, 8, 77, 21, 9, 116, 20, 10, 8, 20, 28, 34, 34, 32, 34, 32, 31, 11, 10, 49, 19, 46, 19, 47, 34, 59, 38, 13, 9, 14, 15, 68, 10, 32, 46, 13, 40, 9, 49, 109, 11, 12, 22, 12, 47, 12, 14, 15, 70, 18, 49, 12, 109, 15, 9, 13, 14, 12, 92, 12, 12, 13, 14, 77, 9, 12, 14, 13, 70, 55, 38, 9, 38, 22, 15, 108]),
  ([288, 51, 267, 208, 100, 135], [17, 49, 34, 46, 109, 22, 100, 56, 38, 34, 14, 32, 48, 9, 11, 98, 28, 32, 34, 54, 38, 8, 9, 111, 80, 9, 30, 11, 38, 47, 38, 59, 37, 10, 8, 11, 11, 28, 11, 10, 14, 81, 51, 98, 51, 13, 21, 51, 55, 17, 78, 24, 10, 94, 13, 15, 78, 94, 10, 8, 52, 31, 18, 8, 94, 32, 12, 116, 109, 22, 19, 77, 12, 34, 12, 111, 35, 8, 10, 72]),
  ([288, 54, 93, 221, 259, 134], [71, 21, 57, 13, 15, 52, 15, 22, 13, 12, 20, 40, 32, 39, 31, 31, 13, 15, 21, 9, 58, 51, 17, 22, 20, 49, 40, 56, 21, 9, 15]),
  ([288, 54, 107, 209, 259, 134], [71, 17, 13, 41, 35, 22, 88, 35, 8, 11, 53, 13, 20, 9, 12, 15, 70, 12, 17, 38, 40, 47, 39, 13, 15, 21, 46, 91, 14, 12, 80, 91, 11, 20, 11, 11, 40, 13, 35, 31, 47, 15, 12, 14, 74, 14, 74, 24, 56, 13, 49, 9, 12, 14, 74, 38, 23, 9])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_1_ok : checkBatch 9 14 catalog9 catalog14 batch1_1 = true := by decide +kernel

def batch1_2 : List (List Nat × List Nat) :=
  [
  ([288, 54, 210, 105, 263, 130], [11, 26, 36, 36, 54, 18, 10, 46, 17, 14, 8, 9, 74, 57, 32, 10, 8, 12, 81, 37, 77, 31, 11, 18, 20, 12, 8, 79, 12, 10, 17, 20, 14, 8, 9, 30, 16, 9, 18, 8, 25, 10, 17, 12, 9, 74, 38, 9, 12, 14, 38, 31, 14, 19, 46]),
  ([288, 54, 255, 209, 155, 76], [14, 9, 34, 17, 10, 12, 114, 48, 11, 10, 8, 12, 114, 18, 10, 9, 11, 12, 77, 22, 25, 8, 9, 11, 9, 22, 11, 10, 18, 37, 50, 11, 12, 28, 35, 22, 10, 28, 22, 17, 37, 10, 118, 42, 106, 47, 42, 32, 28, 54, 48, 34, 11, 12, 10, 9, 106, 12, 12, 9, 10, 69, 38, 11, 22, 98, 14, 11, 114, 11, 9, 32, 55, 11, 76, 9, 14, 14, 12, 13, 15, 90, 14, 15, 13, 12, 90, 22, 8, 9, 10, 11, 72, 34, 8, 38, 17, 9, 12, 71, 41, 28, 12, 48, 20, 35, 42]),
  ([288, 55, 92, 221, 259, 134], [69, 106, 71, 37, 12, 13, 14, 15, 74, 38, 94, 49, 99, 34, 40, 13, 15, 11, 14, 80, 37, 12, 35, 23, 11, 100, 14, 13, 11, 14, 88, 15, 12, 11, 13, 15, 15, 38, 106, 97, 11, 94, 8, 32, 73, 14, 21, 15, 12, 71, 34, 22, 8, 116]),
  ([288, 55, 106, 209, 259, 134], [71, 17, 48, 21, 20, 40, 13, 12, 9, 15, 22, 39, 9, 17, 13, 21, 80, 39, 8, 11, 10, 9, 100, 16, 9, 11, 20, 17, 80, 8, 31, 56, 9, 93, 17, 9, 16, 26, 82, 14, 12, 20, 11, 12, 14, 97, 100, 51, 9, 11, 20, 22, 16, 14, 9, 42, 40, 13, 12, 37, 9, 12, 74, 9, 19, 31, 35, 47, 13])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_2_ok : checkBatch 9 14 catalog9 catalog14 batch1_2 = true := by decide +kernel

def batch1_3 : List (List Nat × List Nat) :=
  [
  ([288, 55, 210, 136, 259, 102], [71, 21, 22, 12, 9, 96, 12, 9, 13, 72, 31, 50, 17, 20, 34, 31, 15, 72, 31, 22, 12, 14, 9, 39, 12, 34, 49, 47, 12, 9, 15, 70, 14, 15, 49, 31, 13, 47, 19, 31, 17, 9, 17, 38, 33, 51, 12, 104, 37, 12, 9, 20, 9, 13, 13, 14, 86, 9, 40, 55, 47, 12, 15, 69, 14, 15, 17, 14, 19, 20, 13, 14, 12, 15, 92, 12, 17, 13, 14, 69, 17]),
  ([288, 55, 210, 136, 263, 97], [8, 12, 11, 10, 14, 97, 46, 34, 12, 14, 9, 10, 22, 11, 12, 54, 22, 9, 16, 14, 9, 34, 14, 32, 17, 11, 12, 9, 91, 40, 17, 40, 56, 12, 69, 22, 28, 30, 31, 19, 9, 10, 14, 72, 28, 17, 9, 10, 115, 16, 14, 32, 12, 40, 19, 17, 11, 22, 16, 11, 49]),
  ([288, 55, 222, 136, 259, 88], [116, 49, 11, 11, 12, 100, 13, 100, 12, 34, 17, 31, 116, 25, 28, 94, 14, 12, 17, 19, 28, 42, 17, 11, 9, 10, 12, 49, 13, 15, 35, 34, 20, 50, 12, 13, 100, 9, 14, 97, 28, 9, 13, 14, 74, 17, 37, 9, 14, 78, 9, 13, 111, 14, 9, 15, 40, 12, 13, 111, 34, 12, 14, 72, 14, 57, 49, 11, 23, 41, 23, 11, 22, 12, 57, 31]),
  ([288, 55, 267, 209, 97, 134], [100, 35, 11, 12, 13, 14, 76, 9, 11, 12, 13, 68, 16, 12, 11, 13, 68, 9, 10, 32, 59, 9, 13, 14, 86, 51, 11, 31, 32, 23, 52, 17, 22, 35, 31, 15, 32, 13, 11, 15, 68, 9, 17, 12, 21, 9, 12, 57, 12, 14, 106, 13, 17, 52, 34, 22, 34, 38, 9, 9, 17, 56, 9, 11, 14, 11, 12, 70, 34, 34, 39, 38, 17])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_3_ok : checkBatch 9 14 catalog9 catalog14 batch1_3 = true := by decide +kernel

def batch1_4 : List (List Nat × List Nat) :=
  [
  ([288, 56, 106, 193, 261, 145], [32, 34, 38, 28, 38, 25, 19, 42, 22, 18, 14, 8, 83, 34, 19, 20, 11, 112, 10, 9, 14, 115, 19, 14, 11, 9, 99, 14, 9, 12, 68, 52, 38, 77, 20, 11, 109, 48, 37, 11, 26, 11, 8, 10, 81, 12, 16, 18, 22, 31, 34, 10, 9, 10, 12, 9, 14, 97, 11, 19, 9, 8, 10, 8, 10, 12, 77, 23, 10, 12, 97, 42]),
  ([288, 56, 106, 208, 259, 133], [79, 9, 23, 17, 38, 12, 11, 14, 33, 17, 55, 11, 22, 21, 11, 14, 15, 68, 55, 15, 31, 12, 14, 9, 76, 56, 9, 38, 92, 42, 9, 110, 19, 34, 9, 10, 9, 8, 17, 114, 13, 12, 108, 50, 86, 9, 11, 31, 17, 21, 11, 15, 12, 86, 55, 54, 9, 14, 15, 71, 8, 37, 14, 15, 77, 15, 102, 13, 14, 15, 102, 48, 40, 12, 13, 14, 111, 14, 15, 68, 48]),
  ([288, 56, 106, 208, 261, 131], [32, 92, 17, 51, 13, 13, 31, 19, 94, 19, 30, 38, 8, 12, 8, 8, 17, 10, 11, 75, 8, 12, 14, 92, 74, 19, 38, 16, 19, 50, 17, 13, 15, 71, 40, 22, 30, 31, 8, 31, 9, 11, 8, 77, 13, 42, 8, 12, 38, 28, 112, 35, 11, 9, 12, 10, 77, 13, 49, 37, 8, 8, 18, 10, 42, 34, 35, 48, 8, 9, 18, 9, 10, 12, 72, 37, 23, 9, 10, 14, 109, 26, 8, 20, 14, 8, 11, 20, 16, 98, 11, 28, 16, 12]),
  ([288, 56, 107, 139, 261, 206], [32, 92, 14, 76, 19, 79, 23, 11, 71, 79, 16, 11, 91, 17, 97, 19, 14, 22, 8, 115, 16, 42, 11, 10, 12, 112, 12, 10, 17, 8, 9, 11, 98, 16, 30, 9, 34, 8, 10, 77, 38, 42, 16, 8, 16, 28, 34, 11, 10, 9, 12, 74, 11, 20, 9, 31, 17, 20, 9, 12, 77, 12, 15, 22, 37, 115, 14, 8, 11, 31, 19, 12, 8, 9, 10, 111, 31])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_4_ok : checkBatch 9 14 catalog9 catalog14 batch1_4 = true := by decide +kernel

def batch1_5 : List (List Nat × List Nat) :=
  [
  ([288, 56, 107, 148, 259, 190], [73, 59, 19, 15, 33, 15, 19, 55, 14, 46, 17, 35, 15, 12, 55, 34, 21, 17, 12, 12, 22, 14, 49, 12, 22, 20, 55, 19, 12, 14, 92, 14, 104, 22, 50, 31, 91, 34, 30, 10, 16, 10, 17, 11, 15, 9, 32, 11, 91]),
  ([288, 56, 107, 148, 261, 189], [32, 19, 49, 10, 11, 77, 16, 20, 12, 31, 30, 8, 11, 12, 73, 12, 14, 11, 46, 35, 12, 8, 73, 31, 30, 16, 12, 9, 36, 38, 17, 22, 18, 22, 9, 11, 22, 11, 9, 40, 8, 38, 42, 26, 8, 10, 112, 8, 11, 12, 75, 20, 28, 37, 8, 11, 115, 51, 22, 114, 40, 22, 14, 34, 9, 8, 12, 93, 46, 31, 9, 8, 30, 114, 112, 31, 37, 38, 19, 9, 10, 11, 98]),
  ([288, 56, 107, 149, 260, 189], [77, 20, 9, 31, 11, 116, 14, 34, 109, 59, 14, 9, 13, 82, 37, 19, 12, 41, 19, 11, 9, 99, 33, 21, 34, 41, 56, 32, 20, 34, 38, 32, 14, 13, 15, 77, 52, 34, 15, 38, 12, 13, 14, 12, 114, 119, 37, 8, 11, 12, 50, 52, 54, 22, 15, 20, 14, 9, 13, 76, 15, 9, 13, 76, 19, 11, 12, 9, 13, 79, 47, 22, 12, 11, 12, 112, 20, 13, 15, 88, 17, 37, 19, 20, 21, 31, 14, 12, 13, 79, 13, 49, 22]),
  ([288, 56, 255, 81, 157, 206], [32, 14, 8, 16, 22, 17, 8, 91, 34, 8, 97, 48, 17, 14, 22, 17, 8, 91, 28, 39, 14, 10, 11, 9, 12, 91, 11, 12, 12, 10, 30, 9, 8, 10, 11, 98, 50, 18, 10, 12, 119, 20, 11, 10, 97, 109, 47, 25, 10, 20, 25, 31, 25, 17, 18, 14, 12, 10, 12, 82, 12, 8, 10, 9, 77, 55, 9, 18, 24, 28, 24, 30, 30, 11, 116, 14, 10, 11, 9, 73, 11, 22, 9, 14, 28, 24, 8, 11, 81, 11, 8, 92, 22, 8, 11, 10])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_5_ok : checkBatch 9 14 catalog9 catalog14 batch1_5 = true := by decide +kernel

def batch1_6 : List (List Nat × List Nat) :=
  [
  ([288, 56, 255, 148, 97, 199], [32, 35, 44, 17, 40, 8, 56, 14, 39, 8, 12, 17, 11, 14, 92, 50, 14, 12, 9, 69, 35, 12, 11, 9, 14, 77, 32, 20, 12, 31, 49, 25, 14, 37, 10, 56, 30, 37, 9, 12, 11, 9, 10, 8, 11, 114, 57, 11, 72, 23, 97, 86, 56, 37, 40, 14, 12, 10, 12, 82, 53, 14, 9, 22, 8]),
  ([288, 56, 255, 148, 100, 197], [37, 30, 12, 10, 11, 11, 9, 10, 92, 52, 8, 9, 10, 81, 23, 10, 107, 9, 8, 10, 69, 12, 10, 9, 49, 10, 20, 116, 12, 14, 10, 11, 9, 14, 95, 9, 11, 14, 94, 56, 38, 97, 54, 9, 13, 97, 54, 9, 13, 97, 54, 52, 32, 11, 22, 22, 11, 14]),
  ([288, 56, 255, 149, 98, 197], [69, 54, 59, 13, 14, 11, 90, 12, 15, 19, 12, 11, 13, 114, 51, 20, 17, 109, 10, 9, 8, 20, 9, 11, 12, 83, 9, 31, 10, 11, 99, 25, 11, 8, 106, 19, 10, 9, 20, 32, 8, 11, 116, 22, 20, 49, 22, 31, 32, 52, 14, 13, 13, 11, 15, 74, 31, 78, 31, 22, 12, 15, 68, 23, 14, 12, 15, 76, 19, 38, 12, 11, 13, 14, 19, 47, 11, 12, 15, 90, 12, 21, 11, 114, 49, 11, 37, 14, 76, 14, 19, 14, 15, 33, 19, 14, 15, 88, 36]),
  ([288, 56, 267, 105, 190, 145], [73, 19, 14, 21, 17, 19, 57, 14, 11, 15, 70, 49, 23, 14, 11, 15, 68, 54, 17, 31, 46, 9, 14, 47, 32, 11, 38, 35, 14, 15, 56, 52, 11, 15, 11, 14, 97, 20, 41, 34, 82, 77, 52, 41, 94, 40, 9, 10, 16, 56, 32, 8, 10])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_6_ok : checkBatch 9 14 catalog9 catalog14 batch1_6 = true := by decide +kernel

def batch1_7 : List (List Nat × List Nat) :=
  [
  ([288, 56, 267, 149, 99, 189], [109, 32, 11, 55, 12, 9, 14, 68, 17, 33, 20, 22, 11, 11, 9, 15, 41, 9, 22, 11, 13, 12, 14, 15, 68, 47, 40, 17, 22, 19, 15, 11, 9, 13, 69, 52, 11, 53, 59, 17, 19, 11, 14, 79, 19, 13, 15, 32, 34, 11, 9, 14, 68, 16, 15, 9, 57, 9, 11, 15, 68, 9, 21, 41, 13, 13, 19, 14, 19, 17, 12, 13, 15, 76, 12, 8, 20, 46, 106, 8, 16, 36, 10, 99, 11, 17, 49, 30, 101]),
  ([288, 56, 267, 193, 100, 145], [10, 30, 11, 9, 8, 12, 81, 12, 94, 52, 37, 31, 32, 8, 11, 8, 16, 8, 16, 9, 34, 14, 25, 11, 9, 14, 115, 9, 12, 38, 14, 25, 34, 14, 8, 11, 80, 32, 34, 8, 11, 14, 92, 8, 12, 14, 92, 12, 14, 28, 97, 92, 12, 34, 11, 11, 30, 16, 12, 35, 8, 12, 101, 52, 20, 38, 9, 12, 91, 17, 12, 73, 56, 8, 9, 12, 97, 11, 20, 17, 12, 8, 12, 14, 118, 14, 12, 69, 13]),
  ([288, 56, 267, 208, 97, 133], [32, 35, 9, 16, 56, 14, 11, 39, 9, 14, 92, 55, 9, 38, 94, 14, 39, 58, 58, 11, 13, 68, 40, 9, 51, 8, 11, 10, 12, 79, 10, 35, 17, 51, 9, 18, 8, 9, 11, 98, 40, 9, 12, 10, 8, 12, 109, 9, 17, 26, 8, 10, 10, 34, 20, 14, 8, 75, 8, 8, 28, 14, 12, 10, 109, 109, 72, 17, 10, 73, 28, 14, 34, 51, 97, 80, 35, 10, 14, 77, 54, 17, 11, 9, 12, 115, 14, 9, 12, 109, 8, 25, 17, 54, 12, 112, 11, 10])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_7_ok : checkBatch 9 14 catalog9 catalog14 batch1_7 = true := by decide +kernel

def batch1_8 : List (List Nat × List Nat) :=
  [
  ([288, 56, 267, 208, 100, 131], [8, 10, 16, 9, 9, 12, 11, 12, 40, 18, 19, 16, 25, 32, 111, 12, 9, 94, 111, 12, 9, 23, 9, 92, 17, 12, 9, 111, 19, 22, 12, 11, 34, 17, 15, 116, 19, 40, 31, 9, 108, 31, 13, 11, 14, 108, 46, 18, 51, 10, 9, 12, 73, 98, 52, 10, 109, 48, 11, 12, 14, 75, 37, 11, 10, 75, 32, 92, 55, 109, 34, 39, 17, 72, 30, 11, 19, 10, 92, 14, 10, 48, 14, 9, 10, 111, 34, 14, 10, 12]),
  ([288, 58, 107, 259, 190, 146], [109, 11, 19, 12, 14, 9, 97, 9, 34, 33, 9, 47, 9, 12, 74, 40, 9, 12, 13, 80, 18, 56, 20, 13, 21, 41, 47, 13, 11, 15, 68, 37, 9, 11, 15, 92, 41, 39, 39, 22, 11, 13, 9, 15, 14, 106, 23, 20, 14, 40, 22, 13, 9, 14, 79, 25, 9, 14, 97, 11, 32, 47, 11, 20, 79, 56, 9, 12, 97, 9, 11, 12, 15, 76, 20, 12, 15, 71, 20, 11, 12, 48, 17, 13, 11, 12, 14, 92, 13, 11, 12, 112, 32, 15, 106, 19, 11, 21, 55, 17, 34]),
  ([288, 58, 107, 261, 189, 146], [31, 11, 37, 17, 8, 9, 12, 92, 34, 37, 9, 10, 17, 35, 54, 8, 12, 10, 19, 8, 32, 18, 44, 8, 12, 82, 11, 14, 18, 10, 12, 14, 9, 115, 18, 22, 20, 10, 8, 9, 77, 55, 37, 11, 9, 12, 99, 12, 8, 9, 8, 46, 11, 12, 11, 12, 8, 14, 79, 40, 11, 17, 16, 14, 8, 12, 116, 54, 12, 10, 11, 93, 34, 16, 14, 19, 8, 106, 114, 112, 22, 26, 92, 17, 12, 109, 31, 14, 11, 85, 25, 22, 46, 28, 25, 52, 14, 8, 11, 12, 71, 49, 8, 8, 11, 12, 14, 109, 57, 56])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_8_ok : checkBatch 9 14 catalog9 catalog14 batch1_8 = true := by decide +kernel

def batch1_9 : List (List Nat × List Nat) :=
  [
  ([288, 58, 107, 261, 206, 135], [101, 23, 17, 11, 21, 15, 49, 13, 11, 38, 39, 21, 12, 13, 11, 49, 14, 21, 11, 51, 12, 49, 17, 32, 32, 14, 13, 15, 85, 112, 109, 11, 13, 13, 14, 97, 11, 19, 13, 14, 77, 33, 13, 14, 91, 37, 31, 20, 100, 19, 25, 23, 39, 9, 11, 48, 9, 11, 12, 69, 14, 48, 17, 22, 11, 40, 37, 9, 14, 15, 112, 50, 55, 12, 19, 11, 9, 14, 69, 14, 9, 14, 11, 70, 12, 11, 15, 11, 9, 9, 32, 13, 23, 15, 39, 9, 11, 88, 37]),
  ([288, 58, 150, 263, 99, 189], [109, 56, 14, 12, 9, 9, 12, 13, 95, 22, 33, 51, 106, 51, 31, 12, 9, 12, 14, 15, 77, 9, 47, 15, 39, 13, 41, 15, 11, 12, 68, 16, 22, 20, 13, 15, 9, 14, 80, 33, 17, 23, 33, 14, 9, 11, 15, 68, 12, 116, 28, 20, 17, 12, 100, 42, 49, 99, 57, 41, 13, 15, 15, 11, 15, 11, 21, 13, 11, 14, 90, 17, 14, 15, 13, 33, 23, 17, 12, 41, 11, 13, 13, 12, 15, 68, 22]),
  ([288, 58, 255, 97, 198, 147], [69, 54, 35, 11, 48, 116, 15, 56, 14, 31, 14, 12, 11, 85, 13, 13, 11, 35, 11, 13, 70, 12, 13, 76, 12, 11, 15, 14, 85, 9, 11, 14, 15, 106, 11, 14, 15, 69, 16, 116, 9, 12, 69, 35, 40, 10, 14, 20, 26, 11, 10, 8, 12, 108, 10, 35, 22, 35, 8, 40, 14, 21, 11, 15, 17, 11, 13, 12, 78, 48, 15, 11, 13, 12, 71, 10, 19, 21, 20, 13, 35, 13, 46, 20, 116, 35, 42, 49, 35, 40, 32, 38, 11, 12, 11, 13, 12, 13, 15, 100, 21, 12, 13, 14, 15, 85, 14, 49, 12, 14, 14, 15, 22, 33, 15, 56, 55, 12, 11, 14, 86, 10, 11, 14, 85, 22, 35])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_9_ok : checkBatch 9 14 catalog9 catalog14 batch1_9 = true := by decide +kernel

def batch1_10 : List (List Nat × List Nat) :=
  [
  ([288, 58, 255, 97, 199, 146], [37, 30, 12, 11, 8, 10, 91, 19, 10, 91, 19, 39, 34, 10, 8, 11, 73, 21, 17, 46, 49, 12, 10, 9, 83, 44, 56, 12, 8, 14, 69, 12, 9, 16, 28, 56, 14, 16, 14, 8, 10, 9, 98, 11, 9, 9, 10, 72, 15, 9, 34, 16, 8, 31, 40, 40, 22, 10, 8, 9, 81, 9, 26, 28, 11, 12, 10, 116, 12, 114, 12, 37, 52, 12, 22, 22, 114, 38, 9, 19, 49, 38, 40, 13, 12, 14, 92]),
  ([288, 58, 255, 155, 198, 88], [69, 15, 22, 19, 11, 13, 69, 12, 42, 116, 12, 92, 71, 56, 56, 14, 11, 12, 13, 82, 41, 11, 33, 21, 51, 46, 58, 94, 12, 39, 11, 12, 13, 15, 76, 18, 31, 22, 56, 17, 40, 17, 12, 14, 15, 70, 50, 39, 37, 13, 14, 15, 68, 17, 48, 11, 14, 15, 68, 14, 15, 71, 116, 71, 14, 17, 15, 12, 97, 109, 11, 12, 11, 38, 12, 38, 13, 21, 49, 33, 41, 69, 12, 14, 15, 86, 56, 32, 12, 11, 14, 78, 20, 10]),
  ([288, 58, 255, 157, 206, 77], [28, 22, 34, 9, 8, 12, 109, 48, 16, 26, 8, 11, 72, 15, 18, 8, 14, 20, 8, 11, 12, 73, 11, 11, 114, 16, 17, 25, 25, 8, 22, 9, 10, 72, 13, 9, 32, 9, 10, 114, 10, 22, 9, 8, 91, 9, 10, 8, 14, 9, 12, 14, 81, 34, 8, 9, 14, 92, 9, 14, 69, 14, 18, 34, 12, 9, 14, 81, 25, 8, 12, 14, 81, 11, 34, 35, 10, 19, 8, 12, 14, 91, 30, 14, 12, 19, 8, 11, 44, 56, 25, 8, 109, 14, 34, 42, 10, 12, 39, 8, 12, 14, 79, 21, 37, 44, 10, 9, 91, 24, 9, 8])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_10_ok : checkBatch 9 14 catalog9 catalog14 batch1_10 = true := by decide +kernel

def batch1_11 : List (List Nat × List Nat) :=
  [
  ([288, 110, 37, 139, 263, 218], [109, 19, 14, 20, 37, 17, 11, 23, 9, 11, 31, 32, 9, 21, 12, 14, 15, 85, 14, 12, 57, 11, 12, 15, 14, 12, 59, 11, 12, 12, 32, 35, 20, 17, 11, 12, 15, 9, 114, 50, 19, 37, 92, 22, 19, 11, 92, 12, 11, 98, 11, 14, 74, 82, 14, 33, 21, 9, 11, 12, 76, 50, 21, 12, 9, 11, 15, 21, 9, 20, 11, 12, 74, 32, 21, 35, 31, 15, 11, 35, 21, 37, 57]),
  ([288, 110, 37, 221, 260, 135], [17, 56, 34, 48, 116, 21, 17, 56, 9, 34, 14, 9, 14, 49, 22, 9, 25, 36, 110, 19, 11, 8, 10, 79, 14, 13, 8, 26, 110, 9, 26, 11, 12, 98, 32, 11, 28, 30, 39, 25, 42, 32, 18, 14, 31, 8, 77, 12, 21, 9, 108, 11, 116, 21, 23, 13, 108, 25, 116, 38]),
  ([288, 110, 255, 25, 218, 147], [115, 35, 9, 12, 17, 19, 11, 59, 35, 11, 23, 35, 41, 11, 9, 14, 77, 14, 9, 12, 14, 85, 40, 11, 41, 12, 85, 14, 15, 59, 35, 35, 13, 54, 114, 19, 26, 8, 15, 11, 12, 79, 9, 13, 59, 11, 9, 12, 14, 74, 9, 12, 14, 70, 8, 15, 14, 15, 12, 9, 14, 100, 74, 18, 8, 11, 19, 32, 37, 11, 9, 82, 9, 12, 81, 54, 11, 9, 82, 9, 12, 81, 32, 28, 42, 37, 11, 71, 13, 20, 21, 85, 21, 48, 21, 11, 23, 22, 33, 14, 15, 77, 18, 48]),
  ([288, 110, 255, 47, 198, 147], [115, 9, 17, 14, 12, 85, 33, 19, 17, 54, 34, 9, 14, 15, 78, 9, 41, 59, 35, 35, 59, 21, 22, 17, 71, 24, 33, 13, 15, 59, 51, 15, 12, 85, 21, 47, 48, 52, 15, 13, 48, 40, 54, 38, 19, 9, 23, 15, 15, 21])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_11_ok : checkBatch 9 14 catalog9 catalog14 batch1_11 = true := by decide +kernel

def batch1_12 : List (List Nat × List Nat) :=
  [
  ([288, 110, 255, 47, 199, 146], [56, 14, 12, 37, 44, 9, 12, 11, 12, 22, 44, 20, 69, 11, 13, 40, 20, 32, 10, 12, 9, 14, 36, 19, 14, 8, 12, 69, 14, 14, 19, 116, 9, 100, 38, 14, 8, 100, 98, 26, 18, 11, 44, 19, 12, 8, 14, 81, 11, 18, 12, 19, 11, 17, 12, 8, 44, 31, 18, 114, 14, 10, 12, 97, 17, 22, 19, 8, 14, 77, 19, 18, 19, 11, 12, 14, 111, 14]),
  ([288, 110, 255, 148, 44, 199], [56, 30, 38, 28, 17, 42, 9, 12, 20, 28, 9, 39, 12, 20, 18, 32, 26, 30, 11, 8, 12, 14, 75, 9, 12, 38, 14, 14, 18, 44, 9, 14, 8, 14, 79, 50]),
  ([288, 110, 255, 209, 156, 23], [25, 32, 36, 18, 17, 28, 20, 26, 9, 8, 116, 10, 116, 31, 32, 35, 8, 17, 10, 12, 114, 39, 14, 12, 114, 12, 10, 114, 32, 56, 11, 14, 71, 32, 10, 9, 19, 36, 22, 8, 9, 111, 15, 17, 22, 31, 40, 9, 20, 9, 12, 14, 10, 69, 19, 46, 17, 10, 12, 69, 42, 9, 10, 12, 69, 56, 14, 12, 8, 11, 69, 14, 19, 22, 8, 11, 115, 54, 9, 114, 11, 46, 10, 8, 114, 9, 10, 12, 52, 37, 114, 19, 11, 14, 15, 11, 38, 11, 13, 70, 14, 11, 15, 13, 44, 30, 32])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_12_ok : checkBatch 9 14 catalog9 catalog14 batch1_12 = true := by decide +kernel

def batch1_13 : List (List Nat × List Nat) :=
  [
  ([288, 110, 267, 193, 40, 146], [98, 35, 40, 12, 11, 9, 13, 76, 9, 11, 13, 90, 12, 18, 20, 9, 11, 12, 14, 90, 9, 12, 34, 56, 17, 9, 39, 11, 32, 15, 9, 12, 13, 71, 17, 10, 9, 12, 13, 76, 9, 40, 71, 91, 12, 38, 56, 16, 35, 38, 28, 10, 12, 72, 37, 17, 20, 9, 14, 90, 16, 11, 14, 19, 11, 13, 15, 72, 17, 50, 71, 95, 39, 19, 68, 46, 56, 56, 28, 25, 10, 14, 115, 12, 9, 79, 77, 19, 21, 9, 20, 51, 13, 11, 14, 74, 30, 11, 14, 74, 8, 12, 46, 37, 19, 52, 31, 14, 20, 19, 11, 32, 9, 15, 76, 51, 9, 11, 14, 15, 71, 51, 14, 20, 33, 37, 11, 59, 13, 21, 41, 46, 56, 40, 11, 12, 14, 76, 11, 14, 90, 20, 51, 20, 11, 12, 14, 88, 9, 46, 23, 59]),
  ([288, 110, 267, 208, 40, 135], [72, 13, 9, 15, 11, 13, 50, 13, 35, 110, 49, 40, 9, 11, 8, 83, 44, 49, 19, 18, 40, 17, 14, 11, 49, 17, 22, 11, 11, 13, 35, 13, 13, 21, 9, 14, 74, 17, 15, 9, 14, 74, 17, 17, 35, 20, 32, 15, 31, 114, 17, 16, 8, 9, 9, 10, 16, 18, 8, 71, 112, 31, 11, 14, 17, 38, 49, 34, 48, 49, 51, 9, 11, 14, 95, 8, 9, 20, 11, 14, 15, 85, 24, 56, 56, 32]),
  ([288, 110, 267, 208, 44, 133], [79, 50, 35, 53, 49, 37, 55, 20, 12, 11, 14, 12, 13, 109, 11, 92, 91, 50, 33, 11, 12, 50, 14, 48, 10, 11, 28, 36, 37, 12, 9, 38, 9, 31, 9, 12, 96, 48, 9, 15, 14, 78, 36, 15, 14, 20, 59, 13, 22, 59, 14, 17, 23, 15, 38, 13, 14, 14, 9, 99, 56, 41, 9, 13, 99, 15, 20, 14, 92, 98, 74, 9, 69, 74, 38, 38, 98, 14, 25, 34, 25, 111, 92, 117, 56, 98, 42, 22, 12, 15, 48, 10, 11, 9, 50])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_13_ok : checkBatch 9 14 catalog9 catalog14 batch1_13 = true := by decide +kernel

def batch1_14 : List (List Nat × List Nat) :=
  [
  ([288, 112, 17, 221, 259, 146], [40, 92, 102, 54, 40, 34, 32, 31, 19, 30, 32, 9, 20, 17, 31, 10, 52, 19, 8, 9, 95, 19, 17, 100, 32, 31, 9, 106, 11, 12, 91, 11, 8, 79, 8, 46, 11, 8, 9, 14, 71, 13, 9, 24, 11, 24, 8, 79, 25, 19, 14, 19, 11, 10, 92, 50, 13, 20]),
  ([288, 112, 37, 221, 259, 134], [83, 53, 19, 13, 9, 49, 13, 47, 32, 9, 12, 46, 9, 11, 12, 15, 77, 37, 59, 32, 12, 9, 9, 20, 11, 34, 52, 53, 19, 14, 57, 12, 13, 70, 15, 12, 13, 14, 106, 49, 51, 51, 9, 8]),
  ([288, 112, 140, 208, 263, 39], [40, 9, 11, 31, 31, 28, 34, 34, 11, 8, 10, 82, 28, 11, 9, 56, 12, 8, 98, 22, 12, 10, 8, 9, 109, 100, 33, 21, 13, 11, 20, 98, 95, 14, 9, 49, 30, 11, 8, 10, 72, 9, 11, 19, 22, 24, 9, 28, 24, 34, 9, 11, 8, 83, 9, 17, 35, 17, 14, 25, 24, 39, 100, 31, 9, 13, 69, 9, 34, 9, 33, 49, 14, 34, 8, 11, 12, 109, 23, 17, 8, 11, 8, 9]),
  ([288, 112, 150, 192, 263, 39], [40, 9, 26, 8, 10, 100, 20, 10, 11, 91, 11, 12, 22, 36, 10, 69, 11, 22, 16, 8, 12, 9, 34, 48, 9, 32, 11, 8, 109, 26, 8, 109, 14, 8, 39, 8, 14, 9, 17, 39, 10, 14, 82, 31, 35, 31, 8, 10, 28, 110, 69, 49, 20, 8, 14, 95, 14, 10, 8, 82, 40, 35, 38, 11, 46, 14, 12, 9, 34, 24, 11, 12, 8, 91, 8, 17, 100, 57, 48, 12, 104, 31, 14, 13, 99, 49, 55, 38, 9, 15, 15, 11, 13, 94, 80, 17, 39, 12, 19, 9, 12, 8, 8, 16, 14]),
  ([288, 113, 16, 221, 259, 146], [94, 9, 12, 11, 14, 13, 38, 19, 21, 9, 21, 9, 17, 77, 46, 33, 106, 11, 98, 10, 11, 33, 17, 14, 9, 37, 77, 37, 11, 98, 26, 17, 21, 23])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_14_ok : checkBatch 9 14 catalog9 catalog14 batch1_14 = true := by decide +kernel

def batch1_15 : List (List Nat × List Nat) :=
  [
  ([288, 113, 36, 221, 259, 134], [69, 106, 35, 38, 18, 10, 8, 79, 9, 8, 93, 79, 71, 99, 17, 57, 40, 34, 40, 59, 12, 11, 15, 68, 10, 34, 52, 51, 23, 106, 97, 11, 94, 17, 32, 114, 11, 71, 15, 34, 9, 10, 114]),
  ([288, 113, 140, 47, 263, 206], [19, 28, 40, 17, 14, 40, 22, 98, 52, 38, 9, 10, 117, 8, 26, 8, 30, 40, 9, 8, 75, 46, 18, 52, 11, 83, 11, 51, 11, 10, 14, 12, 16, 114, 19, 15, 35, 17, 10, 20, 52, 31, 18, 24, 8, 28, 9, 56, 14, 8, 9, 109, 8]),
  ([288, 113, 150, 47, 263, 188], [40, 56, 28, 8, 36, 12, 10, 11, 35, 30, 35, 11, 8, 8, 12, 9, 69, 12, 56, 31, 17, 11, 12, 10, 11, 116, 19, 48, 22, 54, 12, 22, 17, 28, 91, 19, 9, 15, 13, 35, 22, 35, 31, 18, 10, 12, 82, 116, 23, 9, 11, 17, 12, 23, 35, 23, 21, 14, 97, 9, 28, 12, 30, 11, 48]),
  ([288, 113, 222, 136, 259, 30], [94, 55, 23, 11, 9, 14, 116, 14, 9, 55, 32, 9, 11, 15, 82, 116, 11, 82, 15, 9, 11, 116, 48, 14, 40, 19, 13, 15, 9, 11, 14, 116, 14, 9, 9, 13, 15, 70, 14, 72, 20, 36, 11, 106, 91, 56, 9, 14, 46, 55, 56, 17, 39, 12, 51, 13, 13, 15, 74, 12, 74]),
  ([288, 113, 222, 148, 259, 12], [94, 55, 11, 9, 9, 12, 14, 80, 22, 17, 19, 9, 17, 9, 11, 56, 22, 17, 57, 32, 14, 15, 96, 11, 14, 13, 15, 79, 13, 14, 15, 116, 9, 12, 38, 14, 9, 11, 13, 68, 31, 38, 13, 21, 46, 56, 9, 12, 12, 13, 14, 79, 18, 14, 20, 17, 52, 40, 56, 11, 12, 17])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_15_ok : checkBatch 9 14 catalog9 catalog14 batch1_15 = true := by decide +kernel

def batch1_16 : List (List Nat × List Nat) :=
  [
  ([288, 113, 267, 137, 44, 206], [11, 19, 16, 17, 8, 12, 98, 12, 14, 109, 28, 38, 12, 8, 9, 14, 73, 15, 32, 25, 10, 9, 73, 28, 38, 32, 92, 10, 8, 12, 14, 91, 11, 31, 14, 22, 10, 18, 8, 100, 10, 25, 8, 9, 12, 69, 33, 9, 35, 28, 10, 14, 98, 18, 22, 38, 39, 71, 32, 19, 49, 38, 13, 49, 94, 51, 26, 77, 19, 34, 26, 49, 22, 14, 12, 52, 26, 10, 9, 10, 49, 30, 19]),
  ([288, 113, 267, 149, 44, 188], [40, 92, 14, 11, 14, 48, 9, 98, 40, 14, 34, 41, 100, 20, 20, 54, 38, 88, 44, 92, 14, 48, 20, 9, 88, 44, 9, 12, 40, 50, 15, 13, 40, 17, 11, 9, 31, 11, 71, 25, 24, 17, 10, 12, 109, 51, 10, 9, 11, 73, 11, 9, 49, 18, 22, 18, 14, 109, 12, 11, 17, 28, 42, 35, 32, 22, 49, 9, 10, 114, 18, 8, 17, 112, 14, 9, 10, 73, 8, 12, 9, 14, 71, 14, 10, 12, 19, 12, 14, 73, 30, 18, 26, 18, 14, 18, 26, 18]),
  ([288, 114, 36, 263, 218, 131], [11, 98, 54, 9, 11, 22, 50, 11, 9, 19, 9, 17, 20, 18, 12, 8, 14, 73, 94, 15, 28, 52, 39, 31, 9, 9, 10, 51, 9, 9, 10, 10, 8, 69, 18, 12, 14, 8, 9, 48, 12, 94, 41, 35, 36, 31, 9, 17, 8, 12, 14, 79, 11, 22, 25, 26, 19, 8, 10, 12, 14, 109, 9, 10, 30, 8, 9, 12, 93, 49, 12, 38, 42, 20]),
  ([288, 114, 163, 270, 190, 23], [32, 40, 56, 48, 9, 9, 35, 56, 26, 11, 19, 10, 11, 12, 116, 46, 14, 17, 8, 12, 114, 16, 19, 51, 26, 9, 36, 9, 38, 8, 8, 9, 11, 9, 11, 14, 71, 37, 9, 11, 8, 71, 8, 14, 97, 26, 34, 14, 8, 9, 14, 71, 55, 34, 44, 8, 10, 114, 17, 12, 26, 34, 40, 9, 25, 40, 26, 25, 35, 12, 40, 24, 14, 9, 50, 18, 9, 14, 75, 11, 9, 11, 9, 9, 8, 17, 20, 34, 16])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_16_ok : checkBatch 9 14 catalog9 catalog14 batch1_16 = true := by decide +kernel

def batch1_17 : List (List Nat × List Nat) :=
  [
  ([288, 114, 267, 39, 190, 146], [40, 8, 11, 16, 25, 19, 9, 98, 109, 32, 51, 9, 10, 11, 12, 93, 10, 10, 11, 12, 112, 44, 19, 12, 32, 12, 11, 8, 10, 109, 11, 9, 8, 10, 93, 11, 8, 56, 52, 32, 10, 109, 22, 98, 36, 9, 11, 14, 71, 17, 14, 34, 9, 100, 91, 9, 19, 32, 31, 20, 19, 14, 34, 15, 53, 19, 52, 38, 12, 11, 13, 17, 22, 9, 8, 10, 12, 73, 58, 19, 49, 18, 12, 14, 12, 38, 24, 8, 14, 9, 14, 73, 56, 34, 9, 11, 8, 71, 40, 9, 11, 12, 77, 8, 9, 11, 14, 73, 9, 36, 49, 19, 10, 8, 109, 34, 15, 9, 35, 11, 8, 9, 14, 97, 38, 11, 10, 9, 14, 97, 38, 22, 14, 8, 98, 8, 11, 16, 12, 36, 9, 11, 14, 111, 9, 16, 12, 18]),
  ([288, 114, 267, 40, 189, 146], [56, 19, 52, 114, 47, 13, 9, 94, 98, 31, 48, 12, 78, 56, 22, 74, 16, 51, 9, 12, 77, 17, 8, 10, 114, 8, 17, 32, 11, 12, 73, 41, 19, 14, 11, 9, 12, 107, 54, 12, 38, 17, 12, 9, 10, 109, 10, 71, 13, 39, 8, 9, 109, 17, 9, 10, 12, 14, 72, 19, 31, 12, 14, 72, 17, 35, 52, 11, 8, 14, 9, 12, 75, 37, 9, 12, 75, 9, 22, 8, 26, 8, 25, 9, 69, 22, 8, 35, 9, 11, 14, 119, 41, 54, 9, 11, 12, 14, 71, 53, 16, 54, 11, 12, 9, 118, 32, 42, 10, 9, 11, 106, 12, 69, 41, 13, 14, 9, 69, 10, 12, 12, 9, 114, 18, 11, 8, 54, 10, 114, 10, 11, 12, 14, 79, 13, 52, 14, 72, 15, 17, 19, 20, 109, 94, 20, 14, 10, 16, 21, 22, 11, 12, 59, 56, 11, 31, 35, 76, 17, 19, 46, 11, 20, 8, 14, 75, 21, 14, 75, 8, 19, 8, 17, 11, 14, 106, 69, 19, 9, 22, 10, 9, 92, 13, 14, 11, 14, 10, 12, 81, 13, 23, 12, 75, 34, 19])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_17_ok : checkBatch 9 14 catalog9 catalog14 batch1_17 = true := by decide +kernel

def batch1_18 : List (List Nat × List Nat) :=
  [
  ([288, 114, 267, 40, 206, 135], [81, 38, 14, 51, 51, 12, 20, 9, 82, 11, 38, 13, 14, 17, 94, 17, 32, 41, 13, 14, 9, 70, 16, 9, 14, 68, 25, 12, 55, 32, 57, 13, 12, 14, 70, 16, 39, 11, 12, 9, 13, 110, 56, 9, 12, 13, 112, 9, 38, 9, 23, 15, 11, 12, 70, 32, 17, 52, 40, 51, 20, 12, 13, 9, 13, 15, 15, 11, 9, 9, 13, 15, 82, 14, 59, 11, 15, 19, 13, 14, 17, 22, 20, 20, 12, 13, 70, 38, 39, 9, 39, 13, 20, 9, 109, 9, 12, 15, 70, 8, 15, 84, 37]),
  ([288, 114, 267, 44, 190, 145], [34, 38, 8, 10, 9, 14, 79, 14, 10, 9, 73, 15, 40, 25, 97, 16, 40, 18, 14, 17, 10, 8, 11, 71, 46, 56, 14, 11, 94, 11, 40, 21, 12, 14, 12, 50, 13, 50, 13, 14, 33, 15, 77, 8, 14, 10, 82, 12, 13, 14, 77, 13, 9, 14, 111, 32, 8, 10, 24, 18, 36, 17, 30, 72, 37, 11, 54, 13, 11, 14, 100, 23, 11, 16, 8, 9, 10, 12, 80, 11, 12, 8, 10, 14, 99, 32, 40, 33, 8, 10, 14, 12, 69, 32, 11, 14, 14, 38, 56, 49, 10, 9, 12, 77, 9, 38, 50]),
  ([288, 114, 267, 44, 206, 133], [49, 11, 56, 32, 109, 39, 21, 32, 70, 36, 34, 11, 8, 75, 11, 8, 9, 97, 12, 77, 39, 21, 56, 26, 40, 22, 14, 36, 11, 8, 10, 14, 16, 8, 12, 14, 73, 19, 14, 72, 8, 14, 11, 10, 16, 9, 12, 14, 75, 13, 10, 37, 9, 12, 79, 21, 13, 9, 12, 114, 35, 9, 10, 12, 99, 19, 56, 40, 40, 109, 11, 31, 109, 69, 10, 12, 50, 26, 10, 11, 71, 14, 13, 42, 52, 36, 50, 10, 11, 14, 71, 16, 20, 109, 56, 35, 59, 13, 11, 17, 9, 46, 17, 13, 82, 35, 31, 46, 11, 40, 17, 15, 17, 11, 13])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_18_ok : checkBatch 9 14 catalog9 catalog14 batch1_18 = true := by decide +kernel

def batch1_19 : List (List Nat × List Nat) :=
  [
  ([288, 114, 267, 218, 30, 131], [109, 53, 11, 109, 25, 19, 12, 9, 13, 82, 32, 11, 41, 53, 53, 58, 11, 14, 9, 109, 12, 21, 41, 53, 40, 11, 14, 13, 15, 31, 22, 54, 20, 12, 31, 12, 11, 77, 23, 47, 11, 12, 69, 14, 17, 22, 12, 71, 12, 14, 11, 53, 19, 19, 15, 9, 13, 71, 50, 32, 17, 34, 57, 14, 11, 110, 110, 17, 25, 20, 49, 34, 100, 40, 13, 116, 15, 116, 109, 34, 42, 8, 25, 11, 34, 14, 11, 9, 112, 9, 14, 12, 10, 95]),
  ([288, 166, 255, 25, 218, 88], [11, 56, 37, 10, 8, 12, 75, 17, 17, 44, 14, 8, 12, 73, 50, 17, 49, 39, 9, 8, 69, 8, 12, 75, 30, 18, 52, 38, 42, 92, 9, 31, 22, 14, 8, 10, 83, 21, 14, 26, 116, 69, 12, 17, 8, 14, 97, 100, 9, 12, 9, 46, 10, 18, 14, 36, 8, 22, 19, 9, 10, 71, 58, 14, 116, 56, 14, 94, 69, 56, 34, 14, 9, 12, 81, 20, 13, 40, 30, 24, 71, 14, 12, 8, 115, 56, 12, 9, 10, 98, 24, 9]),
  ([288, 166, 255, 47, 198, 88], [44, 9, 17, 28, 17, 11, 35, 9, 40, 11, 56, 12, 10, 94, 20, 25, 38, 19, 34, 8, 69, 10, 69, 10, 32, 25, 31, 18, 20, 11, 48, 26, 25, 14, 8, 22, 30, 40, 12, 80, 40, 22, 19, 116, 34, 10, 11, 14, 71, 20, 26, 18, 51, 36, 97, 34, 17, 50, 9, 11, 32, 19, 25, 14, 10, 8, 35, 8, 12, 30, 16])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_19_ok : checkBatch 9 14 catalog9 catalog14 batch1_19 = true := by decide +kernel

def batch1_20 : List (List Nat × List Nat) :=
  [
  ([288, 166, 255, 81, 218, 30], [79, 53, 17, 9, 11, 12, 13, 70, 14, 22, 9, 12, 70, 17, 34, 34, 9, 11, 49, 13, 9, 15, 33, 9, 11, 13, 116, 49, 12, 11, 9, 38, 116, 21, 37, 51, 49, 17, 11, 14, 20, 9, 12, 14, 68, 9, 10, 12, 15, 15, 52, 51, 49, 34, 12, 97, 32, 23, 11, 85, 17, 9, 11, 13, 68, 9, 12, 15, 11, 78, 46, 56, 48, 15, 98, 8, 12, 9, 15, 78, 12, 21, 23, 37, 58, 14, 14, 12, 11, 15, 68, 14, 11, 15, 90, 17, 31, 32]),
  ([288, 166, 255, 209, 98, 23], [25, 49, 18, 14, 8, 20, 14, 111, 14, 10, 49, 50, 9, 14, 12, 69, 8, 14, 32, 31, 22, 9, 10, 10, 14, 8, 11, 10, 106, 11, 40, 9, 14, 11, 75, 9, 14, 10, 9, 31, 19, 54, 9, 8, 16, 19, 31, 9, 14, 24, 14, 49, 8, 11, 9, 50, 32, 108, 46, 11, 8, 10, 69, 19, 35, 8, 28, 18, 10, 8, 69, 30, 11, 10, 9, 12, 97, 12, 97, 12, 12, 22, 11, 11, 12, 9, 10, 111, 11, 19, 12, 9, 10, 71, 9, 44, 22, 18, 30]),
  ([288, 169, 92, 192, 261, 44], [22, 40, 8, 16, 17, 8, 11, 12, 83, 12, 32, 49, 8, 94, 40, 13, 12, 10, 11, 106, 17, 17, 44, 51, 8, 10, 54, 10, 18, 30, 9, 32, 14, 32, 17, 8, 18, 49, 11, 8, 9, 10, 69, 12, 11, 8, 9, 100, 9, 14, 100, 17, 19, 10, 14, 28, 14, 9, 10, 111, 12, 17, 56, 11, 14, 28, 24, 46, 28, 106, 24, 12, 10, 11, 106, 46, 10, 39, 9, 31, 10, 8, 11, 72, 14, 19, 11, 12, 94, 40, 31, 14, 8, 111])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_20_ok : checkBatch 9 14 catalog9 catalog14 batch1_20 = true := by decide +kernel

def batch1_21 : List (List Nat × List Nat) :=
  [
  ([288, 169, 210, 105, 260, 12], [11, 19, 9, 18, 69, 22, 21, 36, 25, 99, 9, 10, 54, 34, 114, 13, 11, 35, 19, 22, 34, 14, 44, 50, 24, 26, 8, 71, 95, 28, 14, 12, 97, 12, 13, 110, 35, 15, 31, 20, 95, 13, 18, 34, 99, 19, 37, 8, 10, 111, 46, 9, 54, 49, 12, 12, 46, 37, 18, 8, 22]),
  ([288, 170, 27, 193, 270, 102], [69, 38, 46, 19, 11, 15, 13, 11, 80, 38, 15, 13, 95, 8, 38, 54, 22, 11, 15, 15, 92, 34, 17, 72, 46, 42, 8, 12, 79, 9, 10, 17, 38, 17, 35, 9, 8, 12, 34, 8, 14, 12, 75, 17, 53, 22, 12, 14, 15, 70, 15, 12, 50, 37, 15, 20, 14, 37, 13, 17, 12, 22, 40, 92, 50, 46, 33, 11, 12, 13, 70, 54, 8, 36, 13, 70, 34, 17, 20, 54, 54, 106, 10, 25, 48, 14, 9, 8, 16, 111, 17, 72, 9, 28, 17]),
  ([288, 170, 92, 192, 263, 39], [20, 31, 9, 19, 8, 40, 51, 17, 9, 10, 14, 26, 8, 82, 12, 8, 10, 69, 14, 12, 10, 80, 18, 14, 12, 10, 69, 14, 10, 9, 14, 8, 109, 12, 9, 10, 14, 95, 14, 26, 46, 54, 9, 10, 11, 26, 8, 54, 10, 18, 28, 19, 9, 8, 11, 71, 38, 36, 19, 40, 48, 11, 10, 8, 82, 55, 44, 17, 11, 11, 10, 12, 10, 82, 74, 14, 97, 94, 35, 33, 33, 53, 21, 57, 9, 15, 13, 49, 50, 12, 35, 9, 11, 9, 10]),
  ([288, 170, 93, 47, 263, 188], [17, 9, 19, 18, 14, 11, 12, 22, 16, 38, 12, 8, 14, 81, 13, 20, 46, 56, 14, 16, 10, 56, 42, 11, 8, 12, 73, 21, 8, 12, 69, 69, 32, 12, 13, 70, 11, 14, 8, 12, 97, 12, 10, 69, 69, 40, 20, 42, 26, 19, 12, 8, 30, 11, 14, 92, 11, 50, 39, 20, 32, 10, 11, 91, 18, 16, 9, 11, 9, 34, 46, 52, 44, 11, 14, 12, 10, 71, 12, 10, 119, 20, 12, 81])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_21_ok : checkBatch 9 14 catalog9 catalog14 batch1_21 = true := by decide +kernel

def batch1_22 : List (List Nat × List Nat) :=
  [
  ([288, 170, 106, 193, 270, 22], [20, 32, 42, 10, 9, 11, 97, 31, 9, 34, 8, 9, 14, 75, 44, 8, 9, 10, 72, 46, 24, 9, 10, 75, 17, 9, 9, 10, 39, 12, 8, 10, 81, 22, 10, 8, 12, 81, 11, 46, 38, 42, 35, 8, 11, 50, 8, 11, 12, 92, 17, 56, 9, 11, 14, 81, 13, 46, 11, 10, 14, 81, 16, 56, 17, 34, 11, 9, 12, 75, 9, 12, 75, 25, 9, 14, 12, 82, 40, 16, 9, 24, 8, 10, 97, 17, 22, 8, 10, 11, 71, 19, 51, 8, 11, 18, 25, 16, 9, 11, 12, 14, 93, 40, 14, 12, 97, 11, 14, 11, 25]),
  ([288, 170, 267, 192, 39, 88], [82, 13, 9, 14, 11, 116, 12, 40, 9, 11, 14, 9, 69, 20, 9, 14, 11, 12, 70, 33, 13, 9, 14, 57, 11, 13, 14, 68, 12, 17, 14, 11, 13, 78, 14, 11, 49, 40, 9, 15, 69, 19, 52, 14, 51, 12, 40, 9, 9, 12, 9, 23, 40, 35, 9, 17, 41, 53, 9, 15, 74, 9, 12, 9, 13, 9, 11, 57, 56, 12, 100, 56, 12, 12, 11, 14, 102, 40, 47, 9, 14, 11, 15, 71, 17, 9, 11, 12, 15, 68, 44, 14, 11, 13, 15, 114, 17, 11, 23, 13, 13, 40, 56, 12, 12, 34, 9, 15, 85]),
  ([288, 171, 255, 79, 44, 206], [9, 11, 12, 8, 10, 14, 109, 10, 14, 91, 53, 14, 109, 10, 14, 14, 8, 10, 12, 71, 30, 40, 52, 31, 30, 11, 12, 69, 49, 49, 56, 12, 22, 8, 10, 73, 12, 8, 73, 14, 10, 40, 31, 19, 25, 54, 14, 17, 12, 8, 71, 12, 42, 22, 10, 12, 72, 40, 92, 11, 32, 12, 8, 12, 10, 71, 12, 14, 10, 37, 31, 11, 25, 10, 11, 8, 110, 36, 10, 40, 8, 22, 16, 14, 31, 116, 31, 11, 17, 9, 53, 102])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_22_ok : checkBatch 9 14 catalog9 catalog14 batch1_22 = true := by decide +kernel

def batch1_23 : List (List Nat × List Nat) :=
  [
  ([288, 173, 16, 209, 259, 99], [71, 49, 13, 12, 19, 14, 9, 35, 22, 12, 112, 13, 14, 40, 17, 20, 13, 14, 96, 47, 13, 9, 106, 13, 9, 58, 9, 40, 31, 17, 32, 19, 9, 12, 97, 31, 14, 12, 9, 20, 33, 12, 13, 14, 106, 20, 38, 40, 13, 92, 48, 12, 22, 34, 13, 14]),
  ([288, 173, 17, 209, 259, 98], [20, 18, 34, 46, 32, 8, 42, 31, 10, 38, 11, 34, 31, 32, 100, 32, 39, 12, 57, 91, 35, 14, 8, 11, 116, 57, 31, 106, 50, 12, 107, 20, 40, 14, 50, 37, 46, 28, 40, 12, 8, 10, 82, 15, 36, 10, 8, 11, 73, 51, 25, 12, 9, 10, 10, 49, 10, 9, 10, 28, 46, 16, 12, 8, 9, 69, 11, 11, 9, 8, 69, 11, 11, 42, 8, 9, 92, 8, 9, 14, 106, 20, 11, 48, 116, 38, 14, 31, 38, 9, 11, 14, 112, 24, 9, 10, 83, 28, 35, 10, 11, 14, 116]),
  ([288, 173, 17, 209, 260, 97], [71, 46, 57, 12, 9, 37, 17, 32, 49, 14, 9, 13, 99, 9, 17, 12, 13, 9, 53, 9, 13, 15, 68, 16, 13, 15, 70, 8, 9, 12, 17, 34, 14, 9, 19, 19, 92, 37, 22, 19, 14, 9, 40, 100, 25, 19, 20, 34, 12, 15, 70, 19, 33, 34, 12, 15, 70, 12, 11, 17, 32, 32, 92, 112, 119, 21, 23, 52, 112, 36, 9, 9, 47, 31, 13, 14, 76, 14, 20, 12, 31, 13, 14, 76, 17, 13, 14, 32, 46, 92, 39, 9, 10, 12, 46, 14, 9, 112, 56, 19, 49, 39, 9, 37, 46, 20, 47, 13, 19, 31, 9, 13, 14, 70, 18, 9, 13, 12, 86, 12, 100, 22, 14, 15, 12, 70, 34, 15]),
  ([288, 173, 27, 105, 270, 190], [54, 97, 17, 54, 54, 15, 9, 12, 39, 8, 10, 72, 37, 14, 8, 10, 73, 40, 8, 10, 73, 49, 48, 31, 8, 42, 50, 25, 9, 35, 50, 25, 11, 10, 32, 114, 19, 34, 13, 104, 8, 35, 35, 12, 9, 14, 10, 72, 25, 18, 44, 35, 10, 114, 10, 18])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_23_ok : checkBatch 9 14 catalog9 catalog14 batch1_23 = true := by decide +kernel

def batch1_24 : List (List Nat × List Nat) :=
  [
  ([288, 173, 92, 192, 259, 40], [115, 21, 56, 13, 11, 14, 68, 20, 11, 19, 17, 19, 9, 11, 91, 10, 9, 37, 46, 30, 8, 9, 69, 46, 50, 9, 21, 22, 15, 11, 12, 76, 11, 12, 86, 16, 31, 20, 31, 9, 106, 37, 53, 35, 13, 9, 50, 37, 34, 9, 91, 13, 9, 13, 12, 15, 96, 15, 17, 14, 15, 53, 34, 32, 23, 9, 15, 12, 68, 19, 12, 102, 100, 72, 50, 22, 12, 104, 50, 13, 15, 57, 51, 12, 13, 100, 12, 13, 112, 100, 15, 14, 92, 14, 92, 32, 59, 15, 11, 54, 11, 12, 112, 13, 12, 100]),
  ([288, 173, 92, 192, 261, 39], [20, 31, 9, 16, 8, 32, 35, 9, 12, 14, 82, 9, 9, 50, 17, 10, 12, 14, 118, 19, 91, 9, 37, 9, 52, 20, 9, 49, 20, 17, 32, 18, 32, 32, 9, 19, 40, 9, 111, 17, 9, 10, 69, 31, 22, 10, 44, 40, 17, 19, 40, 12, 34, 24, 32, 10, 22, 9, 28]),
  ([288, 173, 93, 47, 261, 188], [40, 8, 19, 28, 9, 19, 114, 19, 36, 10, 8, 11, 8, 92, 55, 31, 9, 97, 17, 18, 36, 9, 11, 56, 92, 79, 17, 12, 20, 51, 17, 52, 9, 10, 8, 106, 9, 14, 10, 52, 9, 8, 106, 9, 14, 22, 24, 69, 52, 9, 8, 14, 72, 31, 77, 11, 114, 9, 15, 23, 15, 15, 23, 12, 11, 9, 69, 15]),
  ([288, 175, 17, 259, 218, 88], [117, 11, 19, 12, 9, 100, 35, 22, 11, 9, 15, 35, 15, 9, 106, 31, 11, 14, 9, 15, 78, 25, 15, 77, 40, 41, 9, 15, 69, 17, 12, 14, 15, 9, 92, 15, 48, 23, 11, 9, 14, 85, 15, 53, 19, 34, 11, 12, 116, 41, 56, 31, 21, 32, 39, 23, 15, 13, 54, 14, 11, 21, 12, 53, 31, 15, 13, 114, 39, 13, 22])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_24_ok : checkBatch 9 14 catalog9 catalog14 batch1_24 = true := by decide +kernel

def batch1_25 : List (List Nat × List Nat) :=
  [
  ([288, 175, 82, 270, 45, 190], [18, 8, 51, 11, 26, 9, 14, 111, 77, 16, 74, 16, 16, 100, 94, 51, 32, 15, 11, 12, 97, 80, 16, 16, 69, 15, 20, 11, 14, 49, 16, 30, 8, 9, 71, 19, 35, 8, 111, 10, 8, 71, 94, 40, 22, 21, 9, 12, 17, 11, 12, 32, 99, 16, 8, 81, 40, 22, 37, 9, 16, 44, 24, 31, 12, 8, 69, 8, 11, 69, 14, 35, 10, 10, 11, 8, 111, 9, 10, 24, 12, 40, 14, 19, 10, 10, 11, 50, 14, 10, 12, 73, 15, 12, 82, 26, 19, 9, 10, 111, 16, 22, 40, 8, 72, 42, 20, 10, 91]),
  ([288, 175, 93, 259, 218, 12], [40, 52, 16, 8, 25, 19, 19, 9, 10, 71, 10, 30, 36, 56, 10, 8, 36, 11, 50, 12, 11, 46, 11, 12, 14, 91, 11, 20, 12, 14, 91, 50, 17, 10, 8, 14, 35, 22, 91, 40, 11, 90, 40, 20, 13, 82, 9, 100, 31, 39, 11, 95, 91, 25, 8, 11, 99, 53, 71, 40, 33, 22, 71, 40, 50, 15, 17, 47, 31, 50, 15, 9, 96]),
  ([288, 175, 93, 261, 44, 188], [17, 20, 19, 14, 14, 32, 56, 9, 10, 14, 92, 8, 26, 12, 10, 10, 12, 42, 10, 14, 42, 36, 25, 28, 8, 9, 56, 10, 8, 79, 37, 11, 10, 12, 79, 17, 20, 20, 9, 11, 12, 10, 69, 10, 9, 14, 10, 79, 12, 10, 14, 79, 18, 16, 14, 25, 14, 9, 56, 34, 38, 36, 8, 106, 114, 40, 14, 12, 100, 15, 91, 19, 49, 15, 17, 22]),
  ([288, 175, 210, 259, 99, 12], [71, 22, 49, 39, 33, 40, 22, 17, 9, 12, 96, 20, 9, 14, 58, 9, 38, 14, 39, 47, 40, 39, 9, 22, 31, 100, 16, 8, 20, 11, 8, 36, 106, 20, 16, 31, 39, 12, 11, 9, 94, 11, 44, 108, 39, 15, 13])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_25_ok : checkBatch 9 14 catalog9 catalog14 batch1_25 = true := by decide +kernel

def batch1_26 : List (List Nat × List Nat) :=
  [
  ([288, 227, 93, 136, 261, 44], [40, 92, 106, 9, 17, 22, 34, 9, 24, 92, 112, 22, 17, 9, 8, 14, 14, 8, 92, 14, 8, 11, 95, 22, 12, 10, 9, 11, 95, 26, 19, 17, 22, 16, 18, 10, 22, 54, 50, 46, 8, 10, 11, 72, 15, 32, 56, 12, 31, 30]),
  ([288, 228, 16, 105, 263, 145], [11, 98, 35, 40, 100, 69, 13, 11, 12, 15, 79, 85, 12, 15, 79, 108, 17, 32, 44, 8, 9, 14, 73, 12, 26, 98, 32, 11, 13, 114, 97, 34, 9, 92, 17, 114, 8, 9, 69, 28, 26, 32, 51, 52, 16]),
  ([288, 228, 17, 148, 259, 102], [117, 11, 48, 12, 111, 19, 12, 15, 9, 13, 116, 23, 15, 19, 55, 11, 50, 22, 12, 11, 15, 69, 31, 19, 11, 12, 13, 38, 11, 15, 102, 53, 13, 20, 12, 14, 15, 100, 21, 14, 12, 15, 92, 31, 15, 31, 23, 69, 14, 32, 12, 10, 8, 12, 11, 97, 26, 11, 32, 19, 16, 15, 40, 31, 12, 31, 13, 23, 19, 22, 56, 22, 20]),
  ([288, 228, 17, 148, 263, 97], [32, 49, 8, 11, 9, 12, 116, 19, 10, 12, 11, 10, 8, 72, 13, 10, 74, 98, 91, 20, 47, 9, 56, 17, 52, 10, 8, 72, 8, 14, 72, 10, 48, 14, 56, 38, 26, 11, 12, 26, 24, 9, 82, 13, 11, 116, 8, 9, 11, 116, 39, 12, 26, 9, 12, 10, 11, 12, 116, 16]),
  ([288, 228, 36, 105, 263, 130], [32, 11, 17, 77, 30, 98, 38, 9, 30, 106, 13, 9, 17, 12, 9, 17, 18, 16, 106, 55, 11, 37, 37, 77, 19, 18, 11, 18, 11, 14, 9, 12, 10, 46])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_26_ok : checkBatch 9 14 catalog9 catalog14 batch1_26 = true := by decide +kernel

def batch1_27 : List (List Nat × List Nat) :=
  [
  ([288, 228, 37, 136, 259, 102], [117, 32, 39, 40, 13, 100, 20, 39, 12, 48, 9, 12, 15, 69, 23, 13, 11, 94, 33, 23, 9, 11, 41, 12, 15, 70, 8, 19, 15, 12, 15, 14, 69, 9, 17, 11, 15, 12, 70, 47, 11, 37, 34, 11, 15, 69, 56, 49, 53, 12, 11, 14, 15, 68, 14, 51, 15, 11, 12, 70, 8, 9, 58, 17, 32, 92, 17, 15, 9, 14, 69, 30, 31, 54, 32, 13, 15, 74, 32, 21, 12, 20, 15, 13, 11, 17, 15, 38, 13, 31, 15, 21, 12, 15, 12, 106, 17, 9, 12, 94, 10, 25, 12, 94]),
  ([288, 228, 37, 136, 263, 97], [32, 56, 28, 34, 8, 12, 107, 8, 19, 10, 9, 79, 12, 116, 11, 14, 22, 17, 46, 12, 9, 10, 11, 75, 31, 46, 10, 18, 38, 56, 17, 9, 14, 56, 51, 38, 20, 17, 11, 14, 12, 10, 14, 79, 20, 22, 19, 9, 11, 11, 17, 26, 9, 11, 11, 12, 14, 80, 22, 17]),
  ([288, 228, 107, 136, 259, 30], [28, 71, 12, 14, 13, 32, 34, 19, 20, 15, 14, 9, 86, 55, 9, 10, 31, 16, 20, 18, 8, 12, 14, 94, 14, 8, 109, 31, 8, 19, 56, 22, 20, 22, 8, 49, 31, 10, 16, 14, 31, 9, 19, 39, 14, 112, 14, 8, 10, 116, 16, 8, 19, 22, 8, 9, 14, 71, 31, 9, 50, 26, 19, 9, 14, 10, 46, 8, 9, 118, 25]),
  ([288, 228, 107, 148, 259, 12], [28, 34, 16, 10, 8, 9, 72, 30, 39, 8, 11, 71, 10, 109, 20, 39, 8, 25, 9, 16, 11, 17, 8, 8, 14, 73, 36, 32, 8, 9, 71, 9, 26, 56, 11, 9, 24, 8, 14, 72, 13, 19, 14, 8, 12, 71, 8, 18, 17, 8, 8, 10, 9, 46, 14, 20, 42, 54, 34, 8, 10, 72, 34, 31, 17, 34, 94, 17, 8, 11, 12, 69, 23, 98, 17, 11, 14, 92, 13, 14, 92, 34, 10, 18, 14, 8, 14, 8, 31, 40, 52, 8, 9, 14, 73, 14, 21, 25, 14, 8, 9, 12, 72, 15])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_27_ok : checkBatch 9 14 catalog9 catalog14 batch1_27 = true := by decide +kernel

def batch1_28 : List (List Nat × List Nat) :=
  [
  ([288, 228, 255, 78, 155, 30], [28, 31, 39, 16, 8, 9, 9, 11, 12, 74, 9, 24, 11, 8, 71, 17, 12, 8, 11, 77, 49, 11, 81, 53, 14, 8, 12, 11, 94, 8, 25, 19, 24, 9, 8, 10, 113, 24, 56, 10, 18, 12, 12, 8, 54, 25, 24, 31, 8, 10, 74, 10, 22, 48, 9, 19, 14, 10, 11, 109, 35, 22, 9, 11, 8, 35, 8, 11, 98, 31, 34, 48, 18, 16, 8]),
  ([288, 228, 255, 148, 97, 22], [56, 14, 26, 35, 32, 10, 8, 28, 40, 9, 16, 24, 16, 40, 9, 14, 10, 12, 112, 14, 109, 9, 20, 8, 49, 32, 12, 14, 72, 14, 14, 10, 112, 14, 11, 10, 12, 72, 17, 11, 10, 112, 37, 11, 12, 81, 10, 11, 12, 97, 50, 109, 12, 10, 50, 9, 22, 14, 31, 28, 116, 17, 11, 12, 9, 49, 109, 22, 14, 92, 17, 57, 58, 19, 32, 17, 31]),
  ([288, 228, 267, 105, 12, 145], [16, 25, 19, 10, 11, 25, 11, 37, 8, 77, 17, 9, 34, 28, 98, 40, 52, 52, 11, 15, 40, 10, 36, 9, 32, 51, 25, 19, 12, 28, 14, 8, 10, 73, 8, 14, 10, 12, 44, 11, 20, 34, 14, 8]),
  ([288, 228, 267, 105, 30, 130], [109, 53, 19, 12, 19, 9, 13, 94, 50, 10, 20, 38, 31, 11, 31, 9, 12, 98, 9, 11, 11, 12, 15, 69, 10, 13, 15, 11, 95, 51, 19, 19, 17, 34, 11, 20, 17, 31, 94, 40, 28, 114, 11, 34, 19, 33, 31, 109, 91, 9, 15, 12, 95, 34, 11, 98, 9, 14, 31]),
  ([288, 231, 92, 259, 40, 134], [46, 56, 14, 11, 9, 113, 51, 30, 24, 32, 11, 14, 9, 12, 92, 9, 12, 92, 20, 14, 34, 39, 11, 36, 39, 38, 40, 17, 82, 56, 52, 12, 9, 88, 46, 31, 56, 15, 56, 32, 49, 31, 32, 17, 42, 9, 10, 12, 69, 49, 9, 31, 32, 10, 31, 8, 10, 42, 11, 118, 19, 30, 34, 28, 26, 8, 118, 20, 11, 8, 14, 69, 14, 42, 14, 11, 118, 26, 8, 12, 14, 109])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_28_ok : checkBatch 9 14 catalog9 catalog14 batch1_28 = true := by decide +kernel

def batch1_29 : List (List Nat × List Nat) :=
  [
  ([288, 231, 92, 261, 39, 134], [100, 9, 39, 55, 35, 13, 55, 55, 12, 9, 41, 32, 13, 22, 49, 9, 13, 9, 37, 9, 47, 9, 15, 15, 112, 9, 14, 97, 100, 17, 97, 97, 14, 51, 51, 55, 52, 53, 32, 15, 13, 9, 38, 22, 15, 11]),
  ([288, 231, 92, 261, 44, 130], [40, 92, 69, 22, 8, 10, 10, 32, 10, 8, 9, 106, 12, 97, 54, 15, 10, 11, 8, 111, 22, 114, 68, 34, 11, 8, 111, 32, 11, 22, 8, 9, 49, 9, 34, 20, 92, 106, 31, 38, 9, 12, 72, 14, 9, 9, 8, 11, 14, 97, 49, 14, 12, 14, 24, 9, 20, 38, 11, 94, 69, 31, 22]),
  ([288, 231, 140, 260, 39, 88], [69, 12, 11, 13, 15, 14, 11, 13, 70, 114, 24, 22, 33, 13, 22, 11, 12, 37, 57, 13, 12, 15, 11, 78, 15, 12, 11, 76, 15, 50, 14, 11, 12, 71, 40, 57, 14, 12, 13, 15, 85, 31, 100, 12, 13, 12, 51, 41, 57, 53, 11, 13, 15, 69, 38, 11, 47, 13, 12, 22, 13, 14, 74, 34, 14, 31, 12, 32, 11, 21, 20, 49, 11, 116, 35, 12, 11, 116, 11, 55, 12, 11, 12, 15, 38, 13, 14, 69])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch1_29_ok : checkBatch 9 14 catalog9 catalog14 batch1_29 = true := by decide +kernel

def batches1 : List (List (List Nat × List Nat)) := [batch1_0, batch1_1, batch1_2, batch1_3, batch1_4, batch1_5, batch1_6, batch1_7, batch1_8, batch1_9, batch1_10, batch1_11, batch1_12, batch1_13, batch1_14, batch1_15, batch1_16, batch1_17, batch1_18, batch1_19, batch1_20, batch1_21, batch1_22, batch1_23, batch1_24, batch1_25, batch1_26, batch1_27, batch1_28, batch1_29]

def survivors1 : List (List Nat) := [[288, 54, 82, 193, 270, 159], [288, 56, 267, 105, 206, 133], [288, 114, 222, 260, 30, 131], [288, 227, 93, 47, 261, 134], [288, 227, 93, 137, 260, 44]]

lemma batches1_ok : ∀ b ∈ batches1, checkBatch 9 14 catalog9 catalog14 b = true := by
  apply List.all_eq_true.mp
  simp only [batches1, List.all_cons, List.all_nil, batch1_0_ok, batch1_1_ok, batch1_2_ok, batch1_3_ok, batch1_4_ok, batch1_5_ok, batch1_6_ok, batch1_7_ok, batch1_8_ok, batch1_9_ok, batch1_10_ok, batch1_11_ok, batch1_12_ok, batch1_13_ok, batch1_14_ok, batch1_15_ok, batch1_16_ok, batch1_17_ok, batch1_18_ok, batch1_19_ok, batch1_20_ok, batch1_21_ok, batch1_22_ok, batch1_23_ok, batch1_24_ok, batch1_25_ok, batch1_26_ok, batch1_27_ok, batch1_28_ok, batch1_29_ok, Bool.and_true]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma coverage1 :
    (intervalSeeds catalog0).filter (fun p => !survivors1.contains p) = batches1.flatten.map Prod.fst := by decide +kernel

def batch2_0 : List (List Nat × List Nat) :=
  [
  ([288, 54, 82, 193, 270, 159], [18, 28, 41, 17, 55, 6, 27, 0, 6, 79, 46, 23, 1, 5, 61, 6, 46, 89, 76, 5, 27, 43, 0, 6, 34, 21, 28, 21, 2, 5, 85, 28, 0, 34, 0, 1, 4, 6, 66, 16, 21, 23, 2, 5, 111, 88, 42, 42, 5, 2, 6, 62, 5, 88, 6, 27, 0, 4, 5, 82, 1, 16, 29, 23, 2, 62, 42, 88, 29, 4, 5, 6, 116, 36, 21, 2, 0, 107, 46, 2, 4, 5, 6, 61, 18, 16, 55, 5, 6, 1, 63, 21, 4, 47, 2, 5, 61]),
  ([288, 114, 222, 260, 30, 131], [18, 6, 2, 5, 1, 4, 5, 65, 22, 20, 1, 4, 5, 78, 6, 28, 48, 1, 6, 0, 2, 62, 27, 6, 42, 33, 2, 42, 17, 32, 46, 30, 36, 17, 6, 29, 5, 4, 0, 2, 62, 1, 3, 0, 4, 108, 48, 41, 5, 2, 0, 6, 0, 4, 67, 59, 6, 5, 0, 4, 87, 3, 6, 5, 0, 4, 102, 28, 6, 0, 4, 63, 19, 32, 17, 21, 16, 23, 16, 21, 32, 24, 6, 6, 28, 4, 2, 4, 32, 2, 41, 6])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch2_0_ok : checkBatch 10 13 catalog10 catalog13 batch2_0 = true := by decide +kernel

def batch2_1 : List (List Nat × List Nat) :=
  [
  ([288, 227, 93, 47, 261, 134], [26, 21, 27, 96, 1, 38, 2, 5, 4, 5, 0, 4, 84, 1, 3, 4, 84, 1, 3, 0, 4, 5, 79, 45, 88, 6, 5, 5, 6, 0, 4, 61, 21, 34, 16, 0, 4, 87, 4, 87, 0, 4, 5, 88, 29, 34, 33, 30, 23, 0, 39, 88, 16, 23, 23, 1, 4, 6, 61, 30, 88, 1, 16, 88, 45, 18, 1, 3, 27, 103, 29, 0, 6, 67, 6, 107, 4, 0, 6, 67, 0, 6, 82, 117, 4, 0, 38, 1, 41, 107, 0, 6, 107, 5, 1, 4, 4, 0, 88, 3, 2, 6, 16, 29, 27, 4, 38, 34, 6, 1, 107, 4, 5, 88, 24, 117, 27, 1, 5, 87, 29, 5, 24, 16, 28, 2, 6, 27, 24, 16, 4, 5, 88, 27, 1, 96, 87, 38, 1, 0, 0, 4, 103, 16, 1, 24, 5, 88, 6, 98, 27, 111, 58, 33, 1, 4, 88, 88, 28, 2, 6, 0, 5, 6, 0, 4, 84, 1, 27, 2, 28, 0, 29, 0, 4, 6, 88, 22, 24, 7, 25, 96, 83, 45, 1, 2, 6, 87, 25]),
  ([288, 227, 93, 137, 260, 44], [18, 23, 88, 48, 39, 30, 103, 2, 44, 39, 4, 0, 108, 55, 107, 1, 5, 34, 23, 1, 88, 18, 36, 2, 5, 1, 4, 107, 1, 5, 96, 88, 16, 28, 28, 1, 23, 1, 0, 2, 88, 0, 1, 5, 88, 43, 2, 6, 28, 105, 105, 117, 30, 88, 43, 27, 2, 30, 0, 4, 88, 0, 6, 5, 4, 16, 5, 6, 66, 88, 57, 39, 57, 117, 36, 36, 6, 0, 2, 4, 88, 2, 23, 5, 43, 0, 2, 6, 78, 23, 33, 0, 5, 39, 36, 6, 0, 2, 4, 83, 2, 6, 4, 5, 79, 5, 16, 34, 6])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch2_1_ok : checkBatch 10 13 catalog10 catalog13 batch2_1 = true := by decide +kernel

def batches2 : List (List (List Nat × List Nat)) := [batch2_0, batch2_1]

def survivors2 : List (List Nat) := [[288, 56, 267, 105, 206, 133]]

lemma batches2_ok : ∀ b ∈ batches2, checkBatch 10 13 catalog10 catalog13 b = true := by
  apply List.all_eq_true.mp
  simp only [batches2, List.all_cons, List.all_nil, batch2_0_ok, batch2_1_ok, Bool.and_true]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma coverage2 :
    (survivors1).filter (fun p => !survivors2.contains p) = batches2.flatten.map Prod.fst := by decide +kernel

def batch3_0 : List (List Nat × List Nat) :=
  [
  ([288, 56, 267, 105, 206, 133], [95, 59, 13, 5, 2, 7, 68, 2, 13, 0, 13, 5, 63, 4, 5, 7, 63, 50, 8, 2, 30, 7, 0, 3, 61, 7, 27, 33, 13, 7, 2, 5, 73, 27, 5, 73, 27, 13, 27, 27, 7, 3, 0, 4, 98, 1, 14, 4, 2, 49, 11, 0, 3, 60, 3, 4, 60, 7, 9, 26, 3, 8, 57, 5, 0, 7, 66, 54, 0, 5, 4, 15, 4, 5, 2, 7, 103, 0, 57, 86, 64, 2, 3, 7, 73, 29, 3, 0, 7, 89, 3, 93, 115, 4, 49, 8, 0, 8, 3, 5, 67, 6, 5, 75, 3, 0, 0, 96, 0, 3, 5, 8, 0, 29, 3, 4, 98, 4, 5, 98, 11, 0, 12, 7, 3, 5, 86, 7, 1, 47, 11, 0, 7, 25, 2, 5, 61, 3, 5, 61, 3, 2, 4, 7, 2, 5, 95, 95, 10, 29, 5, 27, 2, 4, 7, 61, 15, 2, 4, 5, 7, 61, 15, 5, 4, 7, 61, 3, 26, 4, 5, 93, 5, 7, 75, 6, 51, 10, 2, 7, 73])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma batch3_0_ok : checkBatch 11 12 catalog11 catalog12 batch3_0 = true := by decide +kernel

def batches3 : List (List (List Nat × List Nat)) := [batch3_0]

def survivors3 : List (List Nat) := []

lemma batches3_ok : ∀ b ∈ batches3, checkBatch 11 12 catalog11 catalog12 b = true := by
  apply List.all_eq_true.mp
  simp only [batches3, List.all_cons, List.all_nil, batch3_0_ok, Bool.and_true]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma coverage3 :
    (survivors2).filter (fun p => !survivors3.contains p) = batches3.flatten.map Prod.fst := by decide +kernel

set_option maxRecDepth 12000 in
theorem no_cover_in_interval (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s)
    (lo : lower < sourceRank s) (hi : sourceRank s ≤ upper) : False := by
  rw [sourceRank_agree, catalog0_eq] at lo hi
  have nonzero : ∀ a ∈ catalog0, a ≠ 0 := by
    rw [← catalog0_eq]
    intro a ha
    exact enumerateMasks_nonzero (by decide : vertexMask 0 ≠ 0) ha
  have theStars (i : Fin 6) : word (s 0 i) ∈ catalog0 := by
    rw [← catalog0_eq]
    exact star_catalogue s valid 0 i
  obtain ⟨p, in_seeds, seedStars⟩ :=
    interval_seed_complete s valid catalog0 rfl nonzero theStars lo hi
  have h1 := joint_of_cover valid (g := 9) (j := 14)
    (by decide) (by decide) (by decide) _ seedStars
  have h2 := joint_of_cover valid (g := 10) (j := 13)
    (by decide) (by decide) (by decide) _ seedStars
  have h3 := joint_of_cover valid (g := 11) (j := 12)
    (by decide) (by decide) (by decide) _ seedStars
  rw [catalog9_eq, catalog14_eq] at h1
  rw [catalog10_eq, catalog13_eq] at h2
  rw [catalog11_eq, catalog12_eq] at h3
  have p1 := checked_survivor coverage1 batches1_ok in_seeds h1
  have p2 := checked_survivor coverage2 batches2_ok p1 h2
  have p3 := checked_survivor coverage3 batches3_ok p2 h3
  simp [survivors3] at p3

end Erdos723Interval

-- Credit: @MrSeizy
open Erdos723Interval Erdos723Interval.WeightFifteenRankAgreement in
set_option maxRecDepth 12000 in
theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1_H1_R1.H3 := by
  change ¬ ∃ s, sourceValid s ∧ (∀ t, sourceValid t → sourceRank s ≤ sourceRank t) ∧
    lower < sourceRank s ∧ sourceRank s ≤ upper
  rintro ⟨s, valid, _, lo, hi⟩
  exact Erdos723Interval.no_cover_in_interval s
    ((Erdos723Interval.WeightFifteenRankAgreement.sourceValid_eq s).mp valid) lo hi
