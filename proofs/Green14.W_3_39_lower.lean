import FormalConjectures.GreensOpenProblems.«14»
import Mathlib.Combinatorics.HalesJewett

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


/-! Certificate formalization for the bounds of Ahmed, Kullmann and Snevily,
https://arxiv.org/abs/1102.5433, Appendix A.
The finite-existence and certificate bridge below are adapted from Dominic
Dabish’s Apache-2.0 Green14 proofs, revision 013a0f04de0057d2bd1034c7cc4caf10ac8dc2cf
of https://github.com/DomTheDeveloper/formal-conjectures. Credit: @Deldor14. -/

open Set
open scoped Classical

namespace Green14

/-- Project a Hales-Jewett line to the sums of its coordinates. Each moving
coordinate contributes one to the common positive difference. -/
theorem mixedMonoAPGuaranteeSet_nonempty (k r : ℕ) (_hk : 1 ≤ k) (_hr : 1 ≤ r) :
    (mixedMonoAPGuaranteeSet k r).Nonempty := by
  classical
  let m := max k r
  obtain ⟨ι,instι,hι⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin m) (Fin 2)
  let _ : Fintype ι := instι
  let N := Fintype.card ι*(m-1)+1
  let wordPoint (v : ι → Fin m) : Icc 1 N :=
    ⟨1+∑ i, (v i : ℕ), by
      have bound : ∑ i, (v i : ℕ) ≤ ∑ _i : ι, (m-1) :=
        Finset.sum_le_sum fun i _ => Nat.le_pred_of_lt (v i).isLt
      rw [show (∑ _i : ι, (m-1)) = Fintype.card ι*(m-1) by simp] at bound
      dsimp [N]
      constructor <;> omega⟩
  refine ⟨N,?_⟩
  intro coloring
  obtain ⟨line,color,mono⟩ := hι (fun v => coloring (wordPoint v))
  let d : ℕ := ∑ i, if line.idxFun i=none then 1 else 0
  let b : ℕ := ∑ i, ((line.idxFun i).map Fin.val).getD 0
  have pos : 0<d := by
    obtain ⟨i,hi⟩ := line.proper
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i,Finset.mem_univ _,by simp [hi]⟩
  have linear (x : Fin m) : ∑ i, (line x i : ℕ) = b+(x:ℕ)*d := by
    dsimp only [b,d]
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases h : line.idxFun i <;> simp [Combinatorics.Line.coe_apply,h]
  have build (q : ℕ) (hq : q ≤ m) : ∃ s : Finset (Icc 1 N),
      ({(z : ℕ) | z ∈ s}).IsAPOfLength q ∧ ∀ z ∈ s, coloring z=color := by
    let point (i : Fin q) := wordPoint (line (Fin.castLE hq i))
    let value (i : Fin q) := 1+b+i.val*d
    have val (i : Fin q) : (point i : ℕ)=value i := by
      change 1+(∑ j, (line (Fin.castLE hq i) j : ℕ))=1+b+i.val*d
      rw [linear]
      simp [Nat.add_assoc]
    have inj : Function.Injective value := by
      intro i j hij
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right pos (by simpa [value] using hij))
    let s := Finset.univ.image point
    have es : ({(z : ℕ) | z ∈ s} : Set ℕ)=Set.range value := by
      ext z
      constructor
      · rintro ⟨y,hy,rfl⟩
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
        exact ⟨i,(val i).symm⟩
      · rintro ⟨i,rfl⟩
        exact ⟨point i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,val i⟩
    refine ⟨s,?_,?_⟩
    · rw [es]
      refine ⟨1+b,d,?_,?_⟩
      · rw [ENat.card_coe_set_eq,←Set.image_univ,inj.encard_image]
        simp
      · ext z
        constructor
        · rintro ⟨i,rfl⟩
          exact ⟨i.val,by exact_mod_cast i.isLt,by simp [value]⟩
        · rintro ⟨i,hi,rfl⟩
          exact ⟨⟨i,by exact_mod_cast hi⟩,by simp [value]⟩
    · intro z hz
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
      exact mono (Fin.castLE hq i)
  fin_cases color
  · exact Or.inl (build k (le_max_left k r))
  · exact Or.inr (build r (le_max_right k r))

end Green14

/- Intersect shifted color masks to check all starts with a common difference.
Every shorter interval inherits the same certificate. -/
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

private lemma clear_prefix {M N k mask : Nat} (bound : M ≤ N) (h : clear N k mask=true) :
    clear M k mask=true := by
  apply List.all_eq_true.mpr
  intro d hd
  apply List.all_eq_true.mp h d
  apply List.mem_range.mpr
  exact (List.mem_range.mp hd).trans_le (Nat.div_le_div_right (Nat.sub_le_sub_right bound 1))

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

private lemma excludes_progression
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

namespace OMA.GreenCertificate

private def red : Nat := 0x800400000002100000201000000042021000120c80000000460c0000001020000001000000800c00000800000000680002008940000004000400000240040401100010000824080000000040000008000000014001020001008000004000000002102200000482002000101100004000000800010242400000030800000108000410000000204040040000800000082001000000806400002000000001202000020000080000500000000200084
private def blue : Nat := (2^1418-1) ^^^ red
private def coloring (i : Nat) : Bool := !(red.testBit i)

end OMA.GreenCertificate

open Green14.FunctionCertificateBridge OMA.GreenCertificate in
theorem OMA.solution : type_of% @Green14.W_3_39_lower := by
  apply le_csInf (Green14.mixedMonoAPGuaranteeSet_nonempty 3 39 (by decide) (by decide))
  intro M hM
  by_contra! h
  have bound : M ≤ 1418 := by omega
  rcases hM (certificateColoring M coloring) with hr | hb
  · apply excludes_progression (k:=3) (color:=false) (mask:=red) (by decide)
      (clear_prefix bound (by decide +kernel)) ?_ hr
    intro i _ hi
    simpa [coloring] using hi
  · apply excludes_progression (k:=39) (color:=true) (mask:=blue) (by decide)
      (clear_prefix bound (by decide +kernel)) ?_ hb
    intro i hi hc
    have hmax : i < 1418 := hi.trans_le bound
    change (((2^1418-1:Nat) ^^^ red).testBit i)=true
    rw [Nat.testBit_xor,Nat.testBit_two_pow_sub_one,decide_eq_true hmax]
    simpa [coloring] using hc
