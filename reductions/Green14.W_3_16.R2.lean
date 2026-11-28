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

/-!
# Palindromic obstructions for W(3,16)

Ahmed, Kullmann and Snevily, *On the van der Waerden numbers w(2;3,t)*,
Table 6, give the palindromic breakpoint pair (232,237). The odd lengths
admit an avoiding palindrome through 231, the even lengths through 236.
H1 and H2 ask for these two complete parity statements independently.

The union of the red set with its reflection forces a triple across the
two sets. Their intersection forces a sixteen-term progression across the
two blue sets. H3 is the remaining asymmetric upper-bound problem with
these constraints in every window of length 233 or 238.

The 237-position lower coloring is Tanbir Ahmed's, Table 4.3 of
*An Implementation of the DPLL Algorithm*, in the representation checked
by @MrSeizy in registry PR 1639. The interval arguments adapt work by
NickLeko, Halldon and Dominic Dabish under Apache License 2.0.
-/

-- Credit: @KoaOkano

open Set Green14
open scoped Classical

namespace OMA.R_Green14_W_3_16_R2

/-- Complete spectrum of reflection-symmetric avoiding colorings at odd lengths. -/
def H1 : Prop := ∀ (n : Nat) (_ : n % 2 = 1),
  (∃ c : Nat → Bool, (∀ x < n, c (n-1-x)=c x) ∧
    ∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 16 else 3)-1)*d<n →
      ∃ t < (if b then 16 else 3), c (a+t*d)=b) ↔ n ≤ 231

/-- Complete spectrum of reflection-symmetric avoiding colorings at even lengths. -/
def H2 : Prop := ∀ (n : Nat) (_ : n % 2 = 0),
  (∃ c : Nat → Bool, (∀ x < n, c (n-1-x)=c x) ∧
    ∀ (b : Bool) (a d : Nat), 0 < d → a+((if b then 16 else 3)-1)*d<n →
      ∃ t < (if b then 16 else 3), c (a+t*d)=b) ↔ n ≤ 236

def H3 : Prop :=
  ∀ c : Nat → Bool,
    (∀ n o : Nat, n = 233 ∨ n = 238 → o+n ≤ 238 →
      (∃ a d : Nat, 0 < d ∧ a+2*d < n ∧ ∀ t ≤ 2,
        c (o+(a+t*d)) = true ∨ c (o+(n-1-(a+t*d))) = true) ∧
      (∃ a d : Nat, 0 < d ∧ a+15*d < n ∧ ∀ t ≤ 15,
        c (o+(a+t*d)) = false ∨ c (o+(n-1-(a+t*d))) = false)) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 15)*d < 238 ∧
      ∀ t ≤ (if b then 2 else 15), c (a+t*d) = b

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
private theorem W_ge_succ_of_not_mem (k r N : ℕ)
    (hne : (mixedMonoAPGuaranteeSet k r).Nonempty) (hbad : N ∉ mixedMonoAPGuaranteeSet k r) :
    N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf hne
  intro b hb
  by_contra hle
  have hbN : b ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle)
  exact hbad (mixedMonoAPGuaranteeSet_upward k r hbN hb)

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


private lemma extract_progression {N k : ℕ} (hk : 2 ≤ k) (q : ℕ → Fin 2) (col : Fin 2)
    (h : ∃ s : Finset (Icc 1 N), ({(x : ℕ) | x ∈ s}).IsAPOfLength k ∧
      ∀ x ∈ s, q (x.val-1) = col) :
    ∃ a d : Fin N, 0 < d.val ∧ a.val + (k-1)*d.val < N ∧
      ∀ i : Fin k, q (a.val + i.val*d.val) = col := by
  obtain ⟨s,⟨a,d,hcard,hset⟩,hc⟩ := h
  have term (i : ℕ) (hi : i < k) :
      ∃ x ∈ s, (x : ℕ) = a + i*d := by
    change a + i*d ∈ ({(x : ℕ) | x ∈ s} : Set ℕ)
    rw [hset]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  obtain ⟨x₀, -, hx₀⟩ := term 0 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero] at hx₀
  obtain ⟨x₁, -, hx₁⟩ := term (k-1) (by omega)
  have ha : 1 ≤ a := hx₀ ▸ x₀.property.1
  have hb : a + (k-1)*d ≤ N := hx₁ ▸ x₁.property.2
  have hpos : 0 < d := by
    by_contra! hz
    have hd : d = 0 := by omega
    have heq : ({(x : ℕ) | x ∈ s} : Set ℕ) = {a} := by
      rw [hset]
      ext z
      simp only [hd, nsmul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,hi,rfl⟩
        rfl
      · rintro rfl
        exact ⟨0, by exact_mod_cast (show 0 < k by omega), rfl⟩
    have hone : (k : ℕ∞) = 1 := by rw [← hcard, heq]; simp
    have : k = 1 := by exact_mod_cast hone
    omega
  have hd' : d ≤ (k-1)*d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k-1 by omega)
  refine ⟨⟨a-1,by omega⟩,⟨d,by omega⟩,hpos,by change a-1+(k-1)*d < N; omega,?_⟩
  intro i
  obtain ⟨x,hx,hval⟩ := term i.val i.isLt
  have he := hc x hx
  change q (a - 1 + i.val*d) = col
  convert he using 2 <;> omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem lower_witness : 237 ∉ mixedMonoAPGuaranteeSet 3 16 := by
  let q (i : ℕ) : Fin 2 := if (0x20041822001012000b04800202401100080029001608000c801400080 : ℕ).testBit i then 0 else 1
  have red : ∀ a d : Fin 237, 0 < d.val → a.val + 2*d.val < 237 →
      ¬ ∀ i : Fin 3, q (a.val + i.val*d.val) = 0 := by decide +kernel
  have blue : ∀ a d : Fin 237, 0 < d.val → a.val + 15*d.val < 237 →
      ¬ ∀ i : Fin 16, q (a.val + i.val*d.val) = 1 := by decide +kernel
  intro h
  rcases h (fun x => q (x.val-1)) with hr | hb
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 3) q 0 hr
    exact red a d hd hbound hc
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 16) q 1 hb
    exact blue a d hd hbound hc

private lemma idx_val (i : ℕ) (hi : i < 238) : (Fin.ofNat 238 i).val = i :=
  Nat.mod_eq_of_lt hi


private theorem boundary (odd : H1) (even : H2) (n : Nat) (hn : n=233 ∨ n=238)
    (c : Nat → Bool) (hp : ∀ x < n, c (n-1-x)=c x) :
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a+(if b then 2 else 15)*d<n ∧
      ∀ t ≤ (if b then 2 else 15), c (a+t*d)=b := by
  classical
  by_contra bad
  have ha (b : Bool) (a d : Nat) (hd : 0<d) (he : a+((if b then 16 else 3)-1)*d<n) :
      ∃ t < (if b then 16 else 3), c (a+t*d)=b := by
    by_contra! fails
    apply bad
    cases b
    · refine ⟨true,a,d,hd,he,?_⟩
      intro t ht
      exact Bool.ne_false_iff.mp (fails t (by change t<3; change t≤2 at ht; omega))
    · refine ⟨false,a,d,hd,he,?_⟩
      intro t ht
      exact Bool.eq_false_iff.mpr (fails t (by change t<16; change t≤15 at ht; omega))
  rcases hn with rfl | rfl
  · exact (by decide : ¬233≤231) ((odd 233 (by decide)).mp ⟨c,hp,ha⟩)
  · exact (by decide : ¬238≤236) ((even 238 (by decide)).mp ⟨c,hp,ha⟩)

private lemma some_progression (h₁ : H1) (h₂ : H2) (h₃ : H3) (r : Fin 238 → Bool) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 15)*d < 238 ∧
      ∀ t ≤ (if b then 2 else 15), r (Fin.ofNat 238 (a+t*d)) = b := by
  let c (x : Nat) := r (Fin.ofNat 238 x)
  change ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 15)*d < 238 ∧
    ∀ t ≤ (if b then 2 else 15), c (a+t*d) = b
  by_contra bad
  apply bad
  apply h₃ c
  intro n o hn ho
  let p (x : Nat) := c (o+x)
  have avoid (b : Bool) (a d : Nat) (hd : 0 < d)
      (he : a + (if b then 2 else 15)*d < n)
      (hm : ∀ t ≤ (if b then 2 else 15), p (a+t*d) = b) : False := by
    apply bad
    refine ⟨b, o+a, d, hd, by omega, ?_⟩
    intro t ht
    simpa only [p, Nat.add_assoc] using hm t ht
  constructor
  · let cover (x : Nat) := p x || p (n-1-x)
    have symm (x : Nat) (hx : x < n) : cover (n-1-x) = cover x := by
      simp only [cover, show n-1-(n-1-x)=x by omega, Bool.or_comm (p (n-1-x)) (p x)]
    obtain ⟨b, a, d, hd, he, hm⟩ := boundary h₁ h₂ n hn cover symm
    cases b
    · exfalso
      apply avoid false a d hd he
      intro t ht
      exact (Bool.or_eq_false_iff.mp (hm t ht)).1
    · exact ⟨a, d, hd, he, fun t ht => by simpa only [cover, p, Bool.or_eq_true] using hm t ht⟩
  · let core (x : Nat) := p x && p (n-1-x)
    have symm (x : Nat) (hx : x < n) : core (n-1-x) = core x := by
      simp only [core, show n-1-(n-1-x)=x by omega, Bool.and_comm (p (n-1-x)) (p x)]
    obtain ⟨b, a, d, hd, he, hm⟩ := boundary h₁ h₂ n hn core symm
    cases b
    · exact ⟨a, d, hd, he, fun t ht => Bool.and_eq_false_iff.mp (hm t ht)⟩
    · exfalso
      apply avoid true a d hd he
      intro t ht
      exact (Bool.and_eq_true_iff.mp (hm t ht)).1

theorem main : H1 → H2 → H3 → type_of% @Green14.W_3_16 := by
  intro h₁ h₂ h₃
  have upper : 238 ∈ mixedMonoAPGuaranteeSet 3 16 := by
    intro c
    let r (i : Fin 238) := decide (c ⟨i.val+1, by constructor <;> omega⟩ = 0)
    obtain ⟨b,a,d,hd,he,hm⟩ := some_progression h₁ h₂ h₃ r
    cases b
    · right
      apply progression_at (a := a) hd c 1
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 15 by omega)
        simp only [Bool.false_eq_true,if_false] at he
        omega
      · intro i hi
        have hh := hm i.val (by change i.val ≤ 15; omega)
        have hx : Fin.ofNat 238 (a+i.val*d) = ⟨a+i.val*d,hi⟩ := Fin.ext (idx_val _ hi)
        rw [hx] at hh
        dsimp only [r] at hh
        have hv : c ⟨a+i.val*d+1,by constructor <;> omega⟩ ≠ 0 := of_decide_eq_false hh
        exact (show ∀ x : Fin 2, x ≠ 0 → x = 1 by decide) _ hv
    · left
      apply progression_at (a := a) hd c 0
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ 2 by omega)
        simp only [if_true] at he
        omega
      · intro i hi
        have hh := hm i.val (by change i.val ≤ 2; omega)
        have hx : Fin.ofNat 238 (a+i.val*d) = ⟨a+i.val*d,hi⟩ := Fin.ext (idx_val _ hi)
        rw [hx] at hh
        dsimp only [r] at hh
        exact of_decide_eq_true hh
  exact le_antisymm (Nat.sInf_le upper)
    (W_ge_succ_of_not_mem 3 16 237 ⟨238,upper⟩ lower_witness)

end OMA.R_Green14_W_3_16_R2
