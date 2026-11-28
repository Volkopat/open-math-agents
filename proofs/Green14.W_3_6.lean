import FormalConjectures.GreensOpenProblems.«14»

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-! Exact mixed van der Waerden numbers as tabulated by Ahmed, Kullmann and Snevily,
https://arxiv.org/abs/1102.5433, Appendix A.
The order and certificate bridge below are adapted from Dominic
Dabish’s Apache-2.0 Green14 proofs, revision 013a0f04de0057d2bd1034c7cc4caf10ac8dc2cf
of https://github.com/DomTheDeveloper/formal-conjectures. Credit: @Deldor14. -/

open Set
open scoped Classical

namespace Green14

theorem mixedMonoAPGuaranteeSet_upward (k r : ℕ) {M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ mixedMonoAPGuaranteeSet k r) :
    N ∈ mixedMonoAPGuaranteeSet k r := by
  intro coloring
  let emb : Icc 1 M ↪ Icc 1 N :=
    ⟨fun x ↦ ⟨x, x.2.1, x.2.2.trans hMN⟩, by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Icc 1 N ↦ (z : Nat)) h⟩
  let restricted : Icc 1 M → Fin 2 := fun x ↦ coloring (emb x)
  rcases hM restricted with hzero | hone
  · left
    rcases hzero with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy
  · right
    rcases hone with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy

/-- One bad coloring of `{1, ..., N}` proves the numerical lower bound
`W(k,r) ≥ N+1`. -/
theorem W_ge_succ_of_not_mem (k r N : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r)
    (hne : (mixedMonoAPGuaranteeSet k r).Nonempty) (hbad : N ∉ mixedMonoAPGuaranteeSet k r) :
    N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf hne
  intro b hb
  by_contra hle
  have hbN : b ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle)
  exact hbad (mixedMonoAPGuaranteeSet_upward k r hbN hb)

end Green14

open Set
open scoped Classical

namespace Green14.FunctionCertificateBridge

/-- Bit i of starts m d j records that i through i+j*d all belong to m. -/
private def starts (m d : Nat) : Nat → Nat
  | 0 => m
  | j+1 => starts m d j &&& (m >>> ((j+1)*d))

private theorem start_bit {m d a j : Nat}
    (h : ∀ i ≤ j, m.testBit (a + i*d) = true) :
    (starts m d j).testBit a = true := by
  induction j with
  | zero => simpa [starts] using h 0 le_rfl
  | succ j ih =>
    simp only [starts, Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true]
    exact ⟨ih fun i hi => h i (Nat.le_succ_of_le hi), by simpa [Nat.add_comm] using h (j+1) le_rfl⟩

private def clear (N k m : Nat) : Bool :=
  (List.range ((N-1)/(k-1))).all fun d => starts m (d+1) (k-1) == 0

private lemma mismatch {N k m : Nat} (hk : 2 ≤ k) (hc : clear N k m = true)
    {a d : Nat} (hd : 0 < d) (he : a + (k-1)*d < N) :
    ∃ i < k, m.testBit (a+i*d) = false := by
  by_contra! h
  have hmul : d*(k-1) ≤ N-1 := by rw [Nat.mul_comm]; omega
  have hle := (Nat.le_div_iff_mul_le (show 0 < k-1 by omega)).mpr hmul
  have hz := List.all_eq_true.mp hc (d-1) (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq, Nat.sub_add_cancel (show 1 ≤ d by omega)] at hz
  have H := start_bit (a := a) (j := k-1) (m := m) (d := d) (by
    intro i hi
    simpa using h i (by omega))
  simp [hz] at H

def boolColor : Bool → Fin 2
  | false => 0
  | true => 1

lemma boolColor_injective : Function.Injective boolColor := by
  intro x y h
  cases x <;> cases y <;> simp_all [boolColor]

def certificateColoring (N : Nat) (coloring : Nat → Bool) : Icc 1 N → Fin 2 :=
  fun x => boolColor (coloring (x.1 - 1))

private lemma mem_coe_finset_set_iff {N : Nat} {s : Finset (Icc 1 N)} {z : Nat} :
    z ∈ ({(x : Nat) | x ∈ s} : Set Nat) ↔ ∃ x ∈ s, (x : Nat) = z := by
  simp

lemma no_monoAP_of_hasAP_eq_false
    {N k mask : Nat} {coloring : Nat → Bool} {color : Bool}
    (hk : 2 ≤ k) (hcheck : clear N k mask = true)
    (hmask : ∀ i < N, coloring i = color → mask.testBit i = true) :
    ¬ ∃ s : Finset (Icc 1 N),
        ({(x : Nat) | x ∈ s}).IsAPOfLength k ∧
          ∀ x ∈ s, certificateColoring N coloring x = boolColor color := by
  rintro ⟨s, hAP, hmono⟩
  rcases hAP with ⟨start, step, hWith⟩
  let T : Set Nat := {(x : Nat) | x ∈ s}
  have hT : T.IsAPOfLengthWith k start step := hWith
  have term_mem (i : Nat) (hi : i < k) : start + i * step ∈ T := by
    rw [hT.2]
    refine ⟨i, ?_, ?_⟩
    · exact_mod_cast hi
    · simp
  have start_mem : start ∈ T := by simpa using term_mem 0 (by omega)
  have last_mem : start + (k - 1) * step ∈ T := term_mem (k - 1) (by omega)
  rcases (mem_coe_finset_set_iff.mp start_mem) with ⟨x0, hx0s, hx0⟩
  rcases (mem_coe_finset_set_iff.mp last_mem) with ⟨xlast, hxlasts, hxlast⟩
  have hstart_lo : 1 ≤ start := by simpa [hx0] using x0.2.1
  have hstart_hi : start ≤ N := by simpa [hx0] using x0.2.2
  have hlast_hi : start + (k - 1) * step ≤ N := by simpa [hxlast] using xlast.2.2
  have hstep_pos : 0 < step := by
    by_contra hnot
    have hstep : step = 0 := Nat.eq_zero_of_not_pos hnot
    have hTsingle : T = {start} := by
      rw [hT.2]
      ext z
      constructor
      · rintro ⟨i, hi, rfl⟩
        simp [hstep]
      · intro hz
        have hz' : z = start := by simpa using hz
        subst z
        refine ⟨0, ?_, by simp [hstep]⟩
        exact_mod_cast (show 0 < k by omega)
    have hcard : (k : ℕ∞) = 1 := by
      rw [← hT.1, hTsingle]
      simp
    have : k = 1 := by exact_mod_cast hcard
    omega
  have hend0 : start - 1 + (k - 1) * step < N := by omega
  obtain ⟨i, hi, hmismatch⟩ :=
    mismatch hk hcheck hstep_pos hend0
  have hiterm : start + i * step ∈ T := term_mem i hi
  rcases (mem_coe_finset_set_iff.mp hiterm) with ⟨x, hxs, hx⟩
  have hxindex : x.1 - 1 = start - 1 + i * step := by
    have hxval : x.1 = start + i * step := hx
    omega
  have hcolor := hmono x hxs
  have hbool : coloring (start - 1 + i * step) = color := by
    apply boolColor_injective
    simpa [certificateColoring, hxindex] using hcolor
  have hbound := Nat.mul_le_mul_right step (show i ≤ k-1 by omega)
  have ht := hmask _ (by omega) hbool
  simp_all

end Green14.FunctionCertificateBridge

open Green14.FunctionCertificateBridge
namespace OMA.VDW
open Set Green14
private lemma progression_at {N k a d : Nat} (hd : 0 < d)
    (c : Icc 1 N → Fin 2) (color : Fin 2)
    (bound : ∀ i : Fin k, a+i.val*d < N)
    (mono : ∀ (i : Fin k) (hi : a+i.val*d < N), c ⟨a+i.val*d+1, by constructor <;> omega⟩ = color) :
    ∃ s : Finset (Icc 1 N), ({(z : Nat) | z ∈ s}).IsAPOfLength k ∧
      ∀ z ∈ s, c z = color := by
  classical
  let value (i : Fin k) := a + i.val*d + 1
  have inj : Function.Injective value := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (by simpa [value] using h)
  let point : Fin k ↪ Icc 1 N := ⟨fun i => ⟨value i, by
    have := bound i
    dsimp [value]
    constructor <;> omega⟩, fun i j h => inj (congrArg Subtype.val h)⟩
  let s := Finset.univ.map point
  have eqs : ({(z : Nat) | z ∈ s} : Set Nat) = range value := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨point i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩,rfl⟩
  refine ⟨s, ?_, ?_⟩
  · rw [eqs]
    refine ⟨a+1,d,?_,?_⟩
    · rw [ENat.card_coe_set_eq, ← Set.image_univ, inj.encard_image]
      simp
    · ext z
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨i.val,by exact_mod_cast i.isLt,by simp [value]; omega⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,by exact_mod_cast hi⟩,by simp [value]; omega⟩
  · intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hz
    exact mono i (bound i)

private def clauses (N k : Nat) (b : Bool) : List (Std.Sat.CNF.Clause Nat) :=
  (List.range N).flatMap fun j =>
    (List.range (N-(k-1)*(j+1))).map fun a =>
      (List.range k).map fun i => (a+i*(j+1),b)

private def formula (N r : Nat) : Std.Sat.CNF Nat :=
  ⟨(clauses N 3 true ++ clauses N r false).toArray⟩

private lemma block_forces {N k : Nat} (c : Icc 1 N → Fin 2) (b : Bool) (v : Fin 2)
    (bits : Nat → Bool)
    (hc : ∀ i (hi : i < N), bits i ≠ b → c ⟨i+1,by constructor <;> omega⟩ = v)
    (bad : ¬ ∃ s : Finset (Icc 1 N), ({(z : Nat) | z ∈ s}).IsAPOfLength k ∧
      ∀ z ∈ s, c z = v) :
    ∀ C ∈ clauses N k b, Std.Sat.CNF.Clause.eval bits C = true := by
  intro C hC
  obtain ⟨j,_,a,ha,rfl⟩ := (by simpa [clauses] using hC :
    ∃ j < N, ∃ a < N-(k-1)*(j+1), (List.range k).map (fun i => (a+i*(j+1),b)) = C)
  by_contra h
  apply bad
  apply progression_at (d := j+1) (a := a) (by omega) c v
  · intro i
    have hle := Nat.mul_le_mul_right (j+1) (show i.val ≤ k-1 by omega)
    omega
  · intro i hi
    apply hc _ hi
    intro heq
    apply h
    apply List.any_eq_true.mpr
    exact ⟨_,List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩,by simpa using heq⟩

private theorem of_unsat {N r : Nat} (hu : (formula N r).Unsat) :
    N ∈ Green14.mixedMonoAPGuaranteeSet 3 r := by
  intro c
  by_contra h
  rw [not_or] at h
  let bits (i : Nat) := if hi : i < N then decide (c ⟨i+1,by constructor <;> omega⟩ = 1) else false
  have hb (i : Nat) (hi : i < N) : bits i = decide (c ⟨i+1,by constructor <;> omega⟩ = 1) := by simp [bits,hi]
  have hval : (formula N r).eval bits = true := by
    apply Array.all_eq_true'.mpr
    intro C hC
    have hmem : C ∈ clauses N 3 true ∨ C ∈ clauses N r false := by simpa [formula] using hC
    rcases hmem with hr | hb'
    · apply block_forces c true 0 bits ?_ h.1 C hr
      intro i hi hn
      rw [hb i hi] at hn
      have hne : c ⟨i+1,by constructor <;> omega⟩ ≠ 1 := by simpa using hn
      exact (show ∀ x : Fin 2, x ≠ 1 → x = 0 by decide) _ hne
    · apply block_forces c false 1 bits ?_ h.2 C hb'
      intro i hi hn
      rw [hb i hi] at hn
      simpa using hn
  simpa [hu bits] using hval

end OMA.VDW

namespace OMA.VDW
open Std.Sat

/-- The positive and negative literals of a clause are two bit sets. -/
private abbrev Masks := Nat × Nat
private def holds (v : Nat → Bool) (c : Masks) : Prop :=
  ∃ i, (if v i then c.1 else c.2).testBit i = true

private def masks : CNF.Clause Nat → Masks
  | [] => (0,0)
  | (i,s)::xs =>
    let c := masks xs
    if s then (c.1 ||| 2^i,c.2) else (c.1,c.2 ||| 2^i)

private lemma literal_in_masks {x : Nat × Bool} {C : CNF.Clause Nat} (hx : x ∈ C) :
    (if x.2 then (masks C).1 else (masks C).2).testBit x.1 = true := by
  induction C with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | ht
    · cases x with | mk i b => cases b <;> simp [masks,Nat.testBit_two_pow]
    · have hh := ih ht
      obtain ⟨i,b⟩ := y
      obtain ⟨j,c⟩ := x
      cases b <;> cases c <;> simp_all [masks]

private def eraseBit (m j : Nat) := m ^^^ (m &&& 2^j)
private def resolve (p q : Masks) (j : Nat) : Masks :=
  (eraseBit p.1 j ||| q.1, p.2 ||| eraseBit q.2 j)

private lemma resolve_sound {v : Nat → Bool} {p q : Masks}
    (hp : holds v p) (hq : holds v q) (j : Nat) : holds v (resolve p q j) := by
  cases hj : v j with
  | false =>
    obtain ⟨i,hi⟩ := hp
    refine ⟨i,?_⟩
    cases hv : v i with
    | false => simpa [resolve,hv,show p.2.testBit i = true by simpa [hv] using hi]
    | true =>
      have hne : j ≠ i := by rintro rfl; simp_all
      simp_all [resolve,eraseBit,Nat.testBit_two_pow]
  | true =>
    obtain ⟨i,hi⟩ := hq
    refine ⟨i,?_⟩
    cases hv : v i with
    | true => simpa [resolve,hv,show q.1.testBit i = true by simpa [hv] using hi]
    | false =>
      have hne : j ≠ i := by rintro rfl; simp_all
      simp_all [resolve,eraseBit,Nat.testBit_two_pow]

private def resolveRow (get : Nat → Masks) (w : Nat) : Nat → Nat → Masks → Masks
  | 0, _, c => c
  | fuel+1, x, c =>
    let p := get (x % 2^w)
    let j := ((c.1 &&& p.2) ||| (p.1 &&& c.2)).log2
    let next := if c.1.testBit j then resolve c p j else resolve p c j
    resolveRow get w fuel (x / 2^w) next

private lemma row_sound {v : Nat → Bool} {get : Nat → Masks} (hget : ∀ i, holds v (get i))
    (w fuel x : Nat) (c : Masks) (h : holds v c) : holds v (resolveRow get w fuel x c) := by
  induction fuel generalizing x c with
  | zero => exact h
  | succ t ih =>
    apply ih
    split <;> apply resolve_sound <;> first | exact h | apply hget

private def checkedRow (tab : Nat → Masks) (w idx x : Nat) : Bool :=
  let get (j : Nat) := if j < idx then tab j else (1,1)
  resolveRow get w (x.log2 / w - 1) (x / 2^w) (get (x % 2^w)) == tab idx

private lemma row_entails {v : Nat → Bool} {tab : Nat → Masks} {w idx x : Nat}
    (h : checkedRow tab w idx x = true) (prev : ∀ j < idx, holds v (tab j)) :
    holds v (tab idx) := by
  let get (j : Nat) := if j < idx then tab j else (1,1)
  have hg (j : Nat) : holds v (get j) := by
    unfold get
    split
    · apply prev; assumption
    · exact ⟨0,by cases v 0 <;> decide⟩
  have he := beq_iff_eq.mp h
  rw [← he]
  exact row_sound hg _ _ _ _ (hg _)

private theorem refutation {N r count base last : Nat} (w : Nat) (tab : Nat → Masks)
    (steps : Nat → Nat) (hbase : base = (formula N r).clauses.size)
    (hinit : ∀ j : Fin (formula N r).clauses.size, tab j = masks ((formula N r).clauses[j]))
    (hsteps : ∀ i : Fin count, checkedRow tab w (base+i.val) (steps i.val) = true)
    (hlast : last < base+count) (empty : tab last = (0,0)) : (formula N r).Unsat := by
  intro v
  by_contra hv
  have H : (formula N r).eval v = true := by simpa using hv
  have all (i : Nat) (hi : i < base+count) : holds v (tab i) := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      by_cases h : i < base
      · have hj : i < (formula N r).clauses.size := hbase ▸ h
        rw [hinit ⟨i,hj⟩]
        have ht := (Array.all_eq_true.mp H) i hj
        obtain ⟨⟨j,b⟩,hm,he⟩ := List.any_eq_true.mp ht
        have hb : v j = b := by simpa using he
        refine ⟨j,?_⟩
        rw [hb]
        exact literal_in_masks hm
      · have hh := hsteps ⟨i-base,by omega⟩
        rw [show base+(i-base) = i by omega] at hh
        exact row_entails hh (fun j hj => ih j hj (by omega))
  obtain ⟨i,hi⟩ := all last hlast
  rw [empty] at hi
  cases v i <;> simp_all

end OMA.VDW

namespace OMA.VDW
/-- A word holds 32 consecutive entries of the indicated width. -/
private def field (words : Array Nat) (width i : Nat) : Nat :=
  (words[i/32]! >>> ((i%32)*width)) % 2^width

private def literalSets : Array Nat := #[
  0x1004000008010000f000000060000000060400000000200000080080808000000021000000008000c0140000e41100000008200000220000201000000000400000010000080000000400000000400000200000000080000000080000008200000004000001000000000200000020000080000000001000000200000000000000,
  0x181000004c4500001000000000404000084040004444000008510000741000000c400000080104000640000002200000018400000400010004200000042040000008800000a20000820000008028000080082000800920000042000080080000800900002002000082080000c0318000c414000020010000e000000010100000,
  0x4400000a24000002400000180000001a4000000001000010200008091000080a8000000280000402000000282000082292000802b00008221000080002000600800002208000020080000c1008000c000000040000000c0020000200500000204000020040000401480001400800010010000e4000000e400800000300000,
  0x62000000842000001454000fa000000ba2000000500000000240400048300002226000005800000b2600000fb0000009240000000060000db7400007900000004c000001110000000428000fb800000318800000460800051000000046800004117d0009b4000000842100000880080000408000002400000c2000001820000,
  0x2f51000600400000c01000042640040007c0000400400400011040042448420040100000c41000004418000f80000007801000078030000492f0000d840000006000000007400200400c10041740000040180009840000088220800040410009841000098411000117918000404000018611000060c000000017c0088400000,
  0x5445600074000000000022000011400054402000001102000010030005e21024081002003000000021263200401400000841400074500000245600000900000008050000b00100000c04000022e20a00000c0000f0040000501500005017000004480000904500000c000000000198000c100000004500000c08800000057c00,
  0xe4510000845100001804400085f1050008040000e4514000000141400106000064554000b450400009040000241040000b04000094510000090040003411000008400000001f00002011220000172200082040002011000008c00000b401000008504000f0400000f0400200100421000a0040009041200000144000d4416200,
  0x14050000e4040000003c9000e4044000a418c0100021040080088000012104006414000010018000e40100008569a000054100000810800044458000446580004065800018104000600100001850000010508200cc010000cc4100001010800010300000847d000011080000ac5100002c50000010240000e4150000e4350000,
  0x20800441544000004804000020c004005800030080000885c800088088000202100008415000030008000d0140000445c00000101800004008000d055000040d4000040151000e00080000015800004401000a011000014040000a91194000111010004048000e00400002108400004208000e02400004010000014010000,
  0x88288800c231800048318000204c000049918000004c0000822bc0800222800021400000d6510000803100002c0400005015800004600000c814000010200000c05400002401000024410000980c8000214100004010840028010000c45400001414000020090000c41500005f04800041048000004a0000c41d000054158000,
  0x20188000c00a0000c00080004900800000500000000b8000281000004102800020180000c0088000c0808000c020000020118000c0028000c0100000c0300000823800008228200040300000200d000000022288c0110000c01900008021080003008000c2190000c01180008349200040118000202c0000c3710000c0398000,
  0x8029200020192010802b2000000402002020000000ba200020002000003a00004080200080a008008220000020100200800021008000b000000a2800400012008000230000000f00001820000212000002520000005200006088000010d4210000f80000204200002003000080dc800020120000128000004052000040010000,
  0x820200008202400081025000820240208180000000000080080940002490000000050000898400008904108082900000041100008081000084810000811100008011000000204000009f1000400020008018200048030000800a2000801a00008482000000600000004b2000005b2000015b3000015370000011500041020000,
  0x1100000081000000120400000824000083000000004200000048000000c80000004c000022080000024800001808000218a0800003400000086000002600000021000000202000011a4000002060000021600000124020000020008000400200010020000200800004020000080800002080000088000001200000028000000,
  0x400800004100000c4000000804000008042001009200000092000008440000000000801004000010060000022400000012000002260000122000001660000210000000090100000920000008280000124000020400000]

private def learned : Array Nat := #[
  0x3e000f67a3c9e0ee763a8cce800399c8e20a381bcdc6d36000d66a349a0ce32330c4ca30,
  0x498d5243548805208f47235188b4506d12884386d0c1b42a110682408c9007f3f0c0fa34,
  0x5503552375429d4ca55228d44a1500353e094f27538364d8d934994c25c389605a552800,
  0x5f8097c1e5eaf176ba1d2e570b75b0e56a021c07968b35907962b01c2bc3a0d572b558ab,
  0xe801acd56a34da4d16833d9c0e668ed98cb653243a026431d8c026280988c3613058002,
  0xa001cc3d1d395c81f71b88280c70831c00c0a0f0280e6f839bcdd6e36db40e6cb61ae0e,
  0x21008820220901ea007a07de6f2788fde03f77bb9daec07badd420748807c201bba07ce7,
  0x8407e0f061080a0a028240e04021083e0300013fc84007f001fa437e001f6fa7cbe1eef6,
  0x8dc6846438c88a31170a85a2d158a05a27120ac46200d879104200871121a008642e1509,
  0x978008b2e22cb44600964ae5529940024f2692802480991c8a42009047e3c05118f63b1c,
  0xa080280009f918480c9f0327b3c9dce8480e9c81e71379b0026b340a8002a0499cca6330,
  0x2485ea417a8802a000a79229c48a6d329647a50029200a451e8c00a28028846a1d084800,
  0xb15849600b057ebc00ae8009800ae56eb559ac55c9805ab016aa042583ea80f2483c9553,
  0x1936dd6db613ed64fb55a4064e0c13ad04d018985026b39284f66128984b65b20884b63,
  0x182c077b0188af41c01de6f177bb02eea0b2882c061128044a174b9846e411b8dc2de11,
  0x150030a55c21570604c10105405150a70380bf802fc5429800a2292980afa00295f0a401,
  0x13808500a16000580516004ae002b8385600058e7160015814ad8a158131204c405f0f86,
  0xca83c300dca0000793c900322002c00320012c01b1e0d01810078e0185c5000138031b8c,
  0x680001c018005a00cf8033c00ce803385a168185a590c0003001cd8073599cc65f2c01,
  0x36b015ab031535408006a401a80006401a70069801a50069000590068c00310068801a1,
  0x380401b62e8076a01030040c472e00768012e0d367b21980763b02d804b7af036bb5a29,
  0x40ec1004056f41040de0100bbb0401c105f1701cbc072f6e85db9176e025b7000042c01,
  0xe38002407e30038bc404000100ce1803840ce0f00100630818c3bf096f8101030040c03c,
  0x9f4827d1e802b9fce00734000602800c400310680a0602f300bcb090039400097279000,
  0xc82cac0b0481c13d51781c12630c98c5fd4000680e1a0004c00100d0402610e9840265f,
  0x34000c2d000000a0001000160001c1200048105e000483c120a0c800ba0a32000c804,
  0x0]

/-- Each starting progression is encoded by its difference and its first term. -/
private def coordinates : Array Nat := #[
  0x209007a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a24118884220,
  0x32990c66230980b65a2c960ae562a950a652289409e4e26930964a249208e46229108642,
  0x45a29128843a190a8441a0902803c9e0ee763a9d0e672389c0de6e369b0d66a349a0ce66,
  0x59ac962b057ab95aac55aa952a853a994aa451a8942a04ba592a9449a49229047a391a8c,
  0x74ba1cee672b91c6e270b81a6d268b419ece66b3196ca64b218ec662b1186c260b016ab4,
  0x93c9a4b2491c8a432087c3a1b0c85c2a130883c1a0b0481c0a030078bc1deee76bb1d6ea,
  0xc1e0b0380b4da2cf66b2d92c762b0d82974aa4d228f46a2d128742a0d025b2c95caa5328,
  0x178b85a2c158a85228138984a24118884220f0f8387c2e0f034ba4d1e8b43a0c3e1b0b84,
  0x2a14ca4512813c9c4d2612c94492411c8c452210c8441200e872381b8d86a34198c86230,
  0x50a81168a44a210e8642a11068240a00e06f371b4d86b351a4d06733194c86331184c055,
  0x30580a652a9146a2]

private def inputMask (i : Nat) : Masks :=
  let u := field coordinates 9 i
  let d := u / 32
  let positive := i < 240
  let k := if positive then 3 else 6
  let bits := (((1 <<< (k*d))-1) / ((1 <<< d)-1)) <<< (u%32)
  if positive then (bits, 0) else (0, bits)

/-- Input clauses are the progressions themselves. Both signs of a learned
clause index the same dictionary of literal sets. -/
private def table (i : Nat) : Masks :=
  if i < 327 then inputMask i
  else
    let j := 2*(i-327)
    (field literalSets 32 (field learned 9 j), field literalSets 32 (field learned 9 (j+1)))

private def rows0 : Array Nat := #[
  0x49d37940,
  0x47c4c4130bca24e94745c491d0fc,
  0x5153f02439145,
  0x4141987c0bca24e89e52475274ae10912514e4,
  0x4141987c22c9e35936508bb03141,
  0x1429201f148198145294b3fc783013a,
  0x12787803d3a,
  0x44e054664c0633594d4009f03942,
  0x53018d014c40f,
  0x41104131,
  0x50a5304e5394853c795413b27d3118ca21d4fc,
  0x479239504ec9f4c4631e8fc,
  0x44e0d1011e8a245c4727d3b,
  0x13008d03c9f331273d873,
  0x4344804e54953281544c47a28915,
  0x50a544345544c1f13104c7a28917,
  0x4654647b04cfe,
  0x47c275472882803128,
  0x4180cc651f15855c49284b24f48f288fa,
  0x13ecf93589701d22,
  0x12c8a10608f044124e95a354de1d54001896484cb25d33,
  0x12c9034e879301164a0af,
  0x1285590615b5704e1ed3d,
  0x4b228559574462893d1e5164a073,
  0x4462893d45879,
  0x559284b2578100b0bf57d40260f93dc74,
  0x13300e03d012886317d454a4a8,
  0x1034c025d014cc75,
  0x106159581301eccb35961464d5035624d941288282bd25,
  0x5304007b,
  0x10614e1984d5901452cff,
  0x466061651e0c01952d4e87b,
  0x14295606163199662fccc1f130278cb358f33d085,
  0x11288c0d0cc278d60390f50843,
  0x11f0d70647d2304a5a11a50c4e,
  0x47c3314319090181344a898,
  0x11906031945,
  0x44435d024049f234cd2650e,
  0x135d6b5b0672cd042c0a01e926,
  0x419330d71f1695b56a0380f4d0984ec4728d01,
  0x50445c7a,
  0x144d5a,
  0x12cca219c192456f240a35c076,
  0x49028cfb,
  0x4194c467288b35c57245d6f1e89d394750bd3a448ad1bd0c,
  0x10d0a25293a279494a875,
  0x47d5d1003fc91,
  0x5670656e5cc7d5d414240a33f53b2787610d13,
  0x1049044ec7a1d129,
  0x419199503053119ca22cc125dc4c2453a1d0fc4489d,
  0x56706576198b2305505e02c0b8cc35c7c50d3b118d61d10f,
  0x1304100b12f1e4354ec151311f,
  0x44f404671e92f,
  0x15e8d747cb05eca03340f4f1430a8452c4f7,
  0x44a230d70382a2b9430d4bf35535490d2108702610b,
  0x57a5f07d1297d4bc9f0d4150593b508bc,
  0x53b4a87b,
  0x42e180a31907d128145fc9f4609e37d41,
  0x4a34147b460b31d5233e808,
  0x48a0213c,
  0x42e1809f261825043d5ad0d4e070,
  0x42e18064038484a87704d14,
  0x15f86428c600b98060d844f0861d9424a813,
  0x53c1d8c63f4a012c995042609145]
private def rows1 : Array Nat := #[
  0x1618124c4a11ecfb4508819544,
  0x4480485e4c5282847b27516,
  0x43535541,
  0x159ca35e58561c48229886253b4b813,
  0x56728d796158a30582619891d52e,
  0x4140c07d28cae3948a511892cd3b51825,
  0x159d79614a362c7d0c014630fd1ec9e1d93b44c43,
  0x11f4670d415400c11e53b,
  0x491274ff448b3,
  0x11887d63d004ec4d,
  0x5003fc91,
  0x47d6392f188ae395912cc7a1d53f640910313a4906f,
  0x113ce53287a4c43535502238a14fcbe4d40625932,
  0x1238c10d4a14bca0334f93dc74,
  0x44f651505492f,
  0x5675e5856359247d936557b4f0a0,
  0x146d7b4f0a0,
  0x48e28111,
  0x1659971f8c13392f334d80459840d42194911849a519354401f,
  0x130503414b323d443e088,
  0x4ea2907e3385e6688e32932,
  0x596664a466d1b5ecd811544,
  0x5966707d6392f188a42b991510b3,
  0x5961419d188a42b920510161153040063,
  0x5961419d480164c063400d823544,
  0x16799d6599f0552f1e0d80bc6145499281453486c4f49e22d364383e,
  0x1675961419e6807e339204bc4c12478185363ec9a,
  0x11f84c291064bc65,
  0x47e339a2480a1510883612f3a85e4c8201c0ca500f840c89,
  0x4c21e93c,
  0x502404d823544,
  0x16599d685a346da4694a445d3c0980a280ff49871,
  0x4682901355d3c4187612cfe,
  0x12d0681ece64184b2bd40,
  0x16a06869d30,
  0x11a1a86a47e0493d418a1,
  0x12d0686a830051302787644cae3a945,
  0x4302d09e3987644cae1c10d,
  0x4a32d0681407d0c0144edac3f4ae3a945,
  0x12d0684a8a33a8481d5454605a0d52b,
  0x128cb41a12a6b93c3ec09,
  0x128cb41a1af2913c3f0c636145,
  0x4a31ec911d9054ac67,
  0x11f905460a136144,
  0x1659a61a0b46aca36b5b16c0c1049b2290fb5089a,
  0x5b30b864658e0248a41dc134f1425ac9f261823613d48cd7,
  0x5b30b9962d064249b44c12a35c9f26105604b1,
  0x1659b32482e6d40e1d93c,
  0x4e0248e60380f4f12f3087127d01508772c123,
  0x4771104f2813d4509f,
  0x4776e14227d3d4bccd26535,
  0x5966cdb66dce02493c309b94056c28130,
  0x1249024049f36127,
  0x5b66cd966ddba0a8a46ec7a1d52a,
  0x1659b36d9bc1f8100b12f,
  0x11f0e0330920d87e2c8ce0b10343ca2,
  0x47c24836069be4c161,
  0x1659bd0d81a1f1bf138b40b9204b47b,
  0x16f44e65836069204c07b,
  0x4d622d42,
  0x5962d1bd2404e70036069c1050137093d3f8ba36134514c6,
  0x1701bd658902d1c3198b2338124449c3612b3f07b,
  0x44635936,
  0x13387e4d89a4f4114a4a41c1203e08f]
private def rows2 : Array Nat := #[
  0x10d81a1987e2c8ce715c6289034f55902d2b,
  0x4a21e0ff,
  0x5966f5c0711c70d81a4c0a44641572115308ff4f4d834945,
  0x1398d60d81a4d89e30117500ea01945,
  0x1659bd0d9c0711c7724d6728a210d422900d0a10049473,
  0x4366fdca464a229102,
  0x172c515cd634c47f52104,
  0x5cb29451731cd1f1614087f,
  0x10380f2c13c404711dd26,
  0x1739cb2951d1fdcf4c46905d02,
  0x13aca546c7f69469290b55191716c732bd2c,
  0x5cb294eb739d0399d1380e70380f4f0c21c5013c47709126,
  0x12d4774f49327d14,
  0x174d0240493,
  0x172c1b748927507f309304f0a4,
  0x41b1fd30290b50bcfd,
  0x12640a02524,
  0x5d272c1b755d63fcd8384934f44575d3c50c50,
  0x53c45478,
  0x445764a0029d74e824,
  0x1761d272cff24dda4f4371f531,
  0x42f1f530,
  0x53041c31,
  0x5d8749cb76c7f33d1f135dc774672cd2c2b9442d58f,
  0x44a1fd1d,
  0x172dd8779df749d44743735c4f50d6c,
  0x43735d43,
  0x139c162c1412d53d1c80b09d27,
  0x5d272dd8779df7808c785e24c1d3,
  0x47c0d08c4c1e1,
  0x451330e71f1e4408a233d24,
  0x172dd278de57341b0d9194c0a4,
  0x178dcb749e5799c8145d6290ff4f515361d7,
  0x1720345293a3fcc0,
  0x1799cb749e3795e806de7,
  0x172dd278de5798347a53006975,
  0x43706c51199044c47f,
  0x172d1f4c47f,
  0x47f0591a,
  0x51a1e4fc518d3,
  0x5cb7a8d906c377adec1887d7b8b319d2c,
  0x44d044621992c41c9a348ce3093250c9b,
  0x11887f33c11135f01e4fc4dc9b,
  0x172dea7bdf1188d97b8e124d434e4aa2649a348f03c86d,
  0x17bdea72df17c8a14f4931e516,
  0x14f4931e516,
  0x5f37bdea72df4285311f91a410e128143,
  0x17a9cb4107e145ec,
  0x172dea365f37d47f33c117d8a123d12,
  0x4b51a44c364cf044314489a2ccc77c106488b2,
  0x14c52b06c7e2c906,
  0x172dea365f7130692d5f8518c77e462054fb4d4bb,
  0x172dfa3aca57a849365f6519310d8be0a544,
  0x4182f944,
  0x172dfa295ea125fb285fc40c7e1451f,
  0x17a9cb7e849294eb7f47f33c117d88f32d33,
  0x12850e448cb,
  0x1040e73644a1fccf11dff4107e1451f,
  0x42c040e7365463ad16460722689f34d214dc6c2a10f,
  0x10b010804741e51a4a429,
  0x17a9fe041cb39cd9802020dca17d046294eb32d4043098,
  0x172dea365fe0402c80c7c2d4771252c4489f,
  0x60404c1472cb51f0c3451d360c1b,
  0x18102e1f014814760393c]
private def rows3 : Array Nat := #[
  0x10b860190a51d80e4f0d63310f514a8,
  0x5cb812070b860190c3819304a8a333d16,
  0x60872e0481c2e180644c12a0dca3334a933d46,
  0x172e0430ce7192078204b824691f01404d064d4cd,
  0x1829cb810c31a41404d314f41b,
  0x18104b829cb30d3d06c371f531,
  0x60a811cb12e0b83011759dc4c1730dd05,
  0x4cf048134c12a0dca326d37,
  0x4c306c3728d2e45814,
  0x43005130,
  0x60a72e0430e0d83a0f4f44e6ae104c469591f4,
  0x60a72e0430e111a07f0ca0c83d314f417,
  0x1812121d9cb2947b829314ac1b6acb547051,
  0x4762947b30c7f0481318d05288905c09c39145,
  0x5cb8120a8487b294768512b84c2b,
  0x11a8321f507,
  0x4938541c30e164c4e703d354f4cd,
  0x615071027507c1491d,
  0x61724e150701003e181a87d41de2,
  0x4933861507217865311a8a51f53d41cd22813e,
  0x61a2c615200690dc93294b61e13d285154a8a0,
  0x50240c94,
  0x124e15868371a4802c61c2947886d3d39c101c924,
  0x615070938747f33c110b42f4a8a21e11d41480,
  0x11fd1d504a239d3a,
  0x123c4d854800dcda33e1e0721f36560285ff4b0d5,
  0x6153687f070692004d880a61453a46c8828544,
  0x4da33c7f070a60c4514e91b26cd31e533,
  0x1368cf1fc1c889042d4c487d3a364491dd12,
  0x4da33c7f072232d84a4e8c426d264dc0b,
  0x489270f6,
  0x61e854cf36a21890c334013895373e09b,
  0x1854d030c8089a1e071143e0a518131,
  0x4c410d16,
  0x615340c3202268781c458fa0509d4c54674ce5,
  0x4c38548089a1e072278a229294eb4c5463b00e08d23,
  0x62a30e1520226878078a1468a4eb,
  0x615340c3202268781c8a88a8ad143e4a517131,
  0x62687a15200c38b09c28cb5470a613944,
  0x62d89a1e8541c4c500294b6365ee,
  0x62d89a1e8562e2991a870a5,
  0x18bc378b6268553d870a5,
  0x4a61e500,
  0x62d89a1e8541c2d62f0de3187230294a102d007892d,
  0x518870a5,
  0x18ca2d89a1e854a68cc7c1dd2c038b60b218,
  0x18d23289a1e8541c1a4c44c4a52d8fc,
  0x18561e89a2d8ca348d62f8cd00144e228544,
  0x185480400e2285440e06a06560,
  0x18de36854943051c1f9314206a,
  0x636856374ee38400d04acb63f84327913,
  0x18e636854d012d2b4807d,
  0x18da151a87d4808d05944420d8,
  0x18e6158ea3b871312343836144,
  0x4b105c8d508d52f50e1cc962bd3648406,
  0x636856393a23c200b18f61c2d8785089428115,
  0x49428115,
  0x18f865854e8312362d8148fd424d8a901d46,
  0x18fa36854e8196404c52b0e0a4280d046d42305a3,
  0x5193f049,
  0x6422909d4e9282105e50191,
  0x131243148943fd173b89d3293250084,
  0x1910803412b,
  0x18da158fa419146a2d8140552f]
private def rows4 : Array Nat := #[
  0x636854b60512f,
  0x1854a61f2471dd2c038a40b13d47452,
  0x6461dc7c854c429a479208034064418913e89d39546,
  0x615918a61de491940f4f4d733546440a9,
  0x1040a63b0521f61c200d0121054d0cc,
  0x192a15918a68d81003e4b4813d200b11ca1c49c78,
  0x646854a692a4c4600e8d92f8706a,
  0x124980,
  0x636856463b0a692a4c4600e93480340640b92093934414cc,
  0x64f8da1528e1c1a8b61f52f,
  0x193e3685650480808706a2d8bc4bc2b174784f5422863f49c72,
  0x64f94479854a68d8170d6373a02b1752d5080c,
  0x65293e511e61529a3b12d310e1a5,
  0x64f85651298c91e6538c49c139440a40b09d24,
  0x193e5418615310a6054790cd310e0a445cfe28da8,
  0x6559524f85480050a34c4381a106,
  0x13fc290352c45c6a,
  0x65593e54186153123695a57250744e8382912f,
  0x61593e54186559607c922472006428d06,
  0x6590c42f04e3611c7c1dd2f0389d1d512,
  0x65a96413854c4368a41e93a,
  0x18565936a36310130bc3196a5b4bc381a93a45c94,
  0x65c8565936a360e0a24e85206155,
  0x65d972598da15148941e9204bc4d23ce82c42d8fca026c73489384406d,
  0x65d972598544d46ce228544,
  0x65c966368565d97a5f481042ccb61f52c,
  0x1966369721598080480b328c52048d036905510b61f5134ec40,
  0x65c9663685660200d00492028cb3984a224170,
  0x4cc9644a854ec3401224134,
  0x6599884a972368552041052,
  0x6599884a854ec9703828a63990bf06019501600b52d,
  0x19644a854ec971404b42d,
  0x1988bf8548099659128ec8d91d30a660a92f4d0d8,
  0x4100b12f,
  0x135cb311c0e1d510,
  0x63698a65854809a0bf9644a3b11d99cc29a52f4d0d8,
  0x1996599884712a153b236200bf9a26a1e92f2c42d281341c8f94409b,
  0x65c966368566212a659ad2041452,
  0x19647a9b063854a612e3f2809b3713e,
  0x19666c19c63854a6368941e8169b4fd224d45009b02d23,
  0x19ba599b06718e15298da8d8a2420c22d07e4f926464d2,
  0x19666c19c63854a69712d3f079,
  0x66e9667026e6f,
  0x66e9666c19c63972369c4754ec0c1e52d,
  0x18566c29a5c9666e9ca3b12c119751b,
  0x6159b0a69cc8005e5f,
  0x19d01d,
  0x19d039,
  0x19d053,
  0x19d06b,
  0x19d081,
  0x19d095,
  0x19d0a7,
  0x19d0b7,
  0x19d0c5,
  0x19d0d1,
  0x19d0db,
  0x19d0e3,
  0x19d0e9,
  0x19d0ed,
  0x12344b9e27ca092d4c0d31cc782990c464bd,
  0x12c4659ea779f09312c8da0e81040798f5103a03e1ccf83e4c01891f,
  0x4a1042829e87b121351ccfb1d09c10511,
  0x6841967a9dc102868540e7d18878534fb]
private def rows5 : Array Nat := #[
  0x6829f47d1e1414b49e,
  0x19ea77194b1a1286a1d032007b1212a4c0ac9d942,
  0x6889e8801ed184c0a3,
  0x6889ea8940d009f5182940e5a12f,
  0x19fa799ea779f4144b09d355355049e,
  0x1a227a9de8a9e67ea2d1d9fc7b450a34e49d2fd57,
  0x4499fc2e450a31d09c4e49d10542444ac,
  0x1a30a1a227a9e4691268d4b09d35535,
  0x1a3a8c286889e9189f4dd1d1039fc2e28c9c4e53f3644124111508ac,
  0x1a227aa32812868ea3c7b40c6227926,
  0x1a40339f2889e87928516,
  0x67aa22909f2780ce914c08029900,
  0x69205e7b9e9189f5019fc64270fe49c0c,
  0x1a48170627b9ea931ed02400a50392f,
  0x67ea48170627b22ccb1ed2c274d50350e,
  0x1a48179ee7aa527e13e954e49d2fcfe,
  0x1a58a1a484ca04179ee7a460d43747448cd5329353c096,
  0x67aa4a7b06017a584c238a1a5cbe1ed2c0b0621780d3293f4a09725932,
  0x698a042c1885e0352b4dc75,
  0x1a629911a810485f4992c1d09e2c904568b0,
  0x698a669a472763053b0a47428d29,
  0x698a6d1a04a809f47441129238d42cd40,
  0x1a629b46812a069c4dccf2e12f4f8b2,
  0x1a629b46812a74621e904,
  0x1a629e130499fa792909d0b107305121d00c28d3a,
  0x1a629e9e67e1329f4b0130528d41a76,
  0x104e7f9f89128d14,
  0x6989fa79a812c04c14a8506190683f92e1d8be35134,
  0x698a889d9fa7904c14a85064e4ca1907603525,
  0x1a609d2927e9e47a13d390340e4b8a52d909,
  0x698a8279a88a4a8ea441d1d9d8b664985,
  0x6982da7da96a09d93b9fc754017d,
  0x698a96a09f4b6a991c4c0752953b,
  0x1a62a5a9d0441490,
  0x698a96a0aa07a4691c0340ea992b40076,
  0x6989fe7628d3b,
  0x1a62a9a96a09fc68aa91ca007f4ec9c35134500d028909,
  0x6a9a96a0aad011fd2f2883645c472c129504ab,
  0x698aa6a5ab0320d12f295ed,
  0x19d67629530,
  0x1a627daa6a5a811a3f44a,
  0x1a62adaa6a5a81049f6ae4bd3babcd62796810d36,
  0x698ac27fab6a5a827dab93b,
  0x1a62a0a96a9ab6b09feaa47280ac5052892a1d85f3e4f7270e436945,
  0x6989e04e2d108,
  0x6b29e27c4c12d9d4a6acd0146ca2,
  0x1a62b29f2811e5379fcb84f85e2a80902123,
  0x1ad6b29e27c4c2b429a7d2d8fd,
  0x1a62b2ad816ad67c3f49f1913b4047f,
  0x6b2ad816ad44719101,
  0x1a62b2ad816ad6789f2b7324d4ae0fea007f5015334cdc02c9b4fcf048c22,
  0x698aca7cad6b605ab92f47a4067f4dc0c27127,
  0x1ae89dac8159e00c35140,
  0x1a62b2ae8150c67e9f0a4274bdaed104b89f,
  0x6b2ae8150c67e9e67c132bc3f8a627d3c45044,
  0x698af6b2ae8319e6789f0b51e5083f8e027d42,
  0x698acaba054319fa7caf91427cfd4b87e,
  0x1a62b29f278aea799f831056bdafca4422752d51f4527f,
  0x1b027b,
  0x1b0282,
  0x1a607e1892e,
  0x6c0a62c124e784212e1a94e,
  0x1b02c19e27c114a927ec3b10a4361304fc38,
  0x6c0b0698114489f0bdb15101cc9d2592a4f85e]
private def rows6 : Array Nat := #[
  0x1b02980405e1892b,
  0x1b0298b0448412792911d,
  0x1b06c011448b1ac7b207d1e0b62b9453a89653539,
  0x6c0b0ac1116c9a00750442d0bd0e4a89b,
  0x6c0a62c1122ca9f4610345d031044a879,
  0x1b02c1a602b174619f411a0d2a414a2,
  0x1b06c0b0acc0ac5d186834a87302d35,
  0x6c0b06989f461176ccb36811e47440d05270a32c91e3d4d9,
  0x1b02cea62c2040731e1284b80a1f935,
  0x1b3ac2b0298b049a2367e04281494aa2c8f2414d81f507,
  0x6cbb049ab402536542,
  0x6c0b3acbb4410b3cfb,
  0x1b0298b48499f0cd3651e,
  0x1b3ac2b0698a06d1b4a7c126d343a7f30504478a5,
  0x1b06c0a62ce24e769d6d4ab93040c0f1d92b,
  0x6c0b06989d893b56799f9064e4a5,
  0x6c1a62ceb0ac0b2ed49e67e4d40f2448b4190e050781c515,
  0x1b0698b02c2b3ad6b52d74787d414c006941,
  0x6c0b2ec112e789f2834b49f1e119,
  0x6c0a62cbb06d4b5ad89e04bb667905508464e027d42,
  0x1b02ceb2ec1b68739f093234fb3e89f21942,
  0x6c0b0698b3acbb6eda33473b500f4b6799f9063e88c,
  0x1b02ceb2ec1b72da33473b50fb4b67e,
  0x1b0298b3acbb06dab745bb6ccd1ce7922d063e4a50f942,
  0x1b0298b68cdb6edeb551e,
  0x6dfb0011,
  0x6dfb002d,
  0x6dfb002f,
  0x6e2b82d9,
  0x1b82e1b02e3b8ac1a612d4a87d9fd04,
  0x6e4b0078,
  0x6e4b7ca2,
  0x6e6b96e2b8e98b0505]
private def segments : Array (Array Nat) := #[rows0, rows1, rows2, rows3, rows4, rows5, rows6]
private def step (i : Nat) := (segments[i/64]!).getD (i%64) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem forced : 32 ∈ Green14.mixedMonoAPGuaranteeSet 3 6 :=
  of_unsat (refutation (count := 417) (base := 327) (last := 743) 10 table step
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide +kernel))
end OMA.VDW

namespace OMA.GreenCertificate
private def red : Nat := 0x30620d0
private def blue : Nat := (2^31-1) ^^^ red
private def coloring (i : Nat) : Bool := !(red.testBit i)
end OMA.GreenCertificate

open OMA.GreenCertificate in
theorem OMA.solution : type_of% @Green14.W_3_6 := by
  apply le_antisymm (Nat.sInf_le OMA.VDW.forced)
  apply Green14.W_ge_succ_of_not_mem 3 6 31 (by decide) (by decide) ⟨_,OMA.VDW.forced⟩
  intro h
  rcases h (certificateColoring 31 coloring) with hr | hb
  · apply no_monoAP_of_hasAP_eq_false (k := 3) (color := false) (mask := red)
      (by decide) (by decide +kernel) ?_ hr
    intro i _ hi
    simpa [coloring] using hi
  · apply no_monoAP_of_hasAP_eq_false (k := 6) (color := true) (mask := blue)
      (by decide) (by decide +kernel) ?_ hb
    intro i hi hc
    change (((2^_ - 1 : Nat) ^^^ red).testBit i) = true
    rw [Nat.testBit_xor,Nat.testBit_two_pow_sub_one,decide_eq_true hi] <;> first | simpa [coloring] using hc | assumption
